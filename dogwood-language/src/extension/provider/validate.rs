//! Schema-aware validation of `provider { … }` invocations.
//!
//! The provider dialect's contribution to `validate_source`: each hoisted
//! invocation must name a declared provider, supply the declared number of
//! arguments, and pass directly-typed literal/set arguments matching the
//! declared `argumentTypes`. Field-path arguments (`context.input.X`,
//! `principal.<attr>`, `resource.<attr>`) are resolved against the schema here
//! — the same resolution the temporal dialect uses — and checked for existence
//! and type on every action the rule's scope reaches. Provider output/projection
//! typing is checked by Cedar over the augmented schema (the comparison was
//! lowered to native Cedar), so it is not re-checked here.

use crate::api::{ActionRef, ProviderField, ScopeConstraint};
use crate::error::{Span, ValidationError, ValidationWarning};
use crate::extension::dialect::{DogwoodDialect, Rendered, ValidationCtx};
use crate::extension::provider::ast::Arg;
use crate::extension::provider::declarations::ParamType;
use crate::conformance::CType;
use crate::extension::temporal::schema_info::{ActionHandle, PathResolution, SchemaInfo, ScopePath};
use cedar_policy_core::ast::EntityType;

/// One provider validation finding, with its span already rebased into the
/// `.dw` source.
pub struct ProviderFinding {
    pub message: String,
    pub span: Span,
    /// Rendered as a warning instead of an error.
    pub warning: bool,
}

/// The provider dialect. Owns its leaf type — the public [`ProviderField`],
/// which carries its resolved declaration and the block-body base for span
/// rebasing. `validate` calls it by name.
pub struct ProviderDialect;

impl DogwoodDialect for ProviderDialect {
    type Leaf = ProviderField;
    type Finding = ProviderFinding;

    fn marker(&self) -> &'static str {
        "provider"
    }

    fn validate(&self, leaves: &[ProviderField], ctx: &ValidationCtx<'_>) -> Vec<ProviderFinding> {
        let mut findings = Vec::new();
        // Cedar's typed view of the augmented schema — used to resolve each
        // field-path argument's `context.<path>` against the actions the rule
        // scope reaches (mirrors the temporal dialect's use of the same
        // projection). `cedar_policy::Schema` is a transparent newtype over a
        // `ValidatorSchema`, so `as_ref()` avoids re-parsing a schema string.
        let info = SchemaInfo::from_validator_schema(ctx.schema.as_ref());
        // Fallback warnings already reported, so a provider called several
        // times warns once, at its first call.
        let mut warned = std::collections::BTreeSet::new();
        for field in leaves {
            let key = field.invocation.key();
            // The invocation's span is relative to the `provider { … }` block
            // body; `field.body_base` is that body's offset in the `.dw`
            // source.
            let span = field.invocation.span.rebased(field.body_base);

            let Some(decl) = field.declaration.as_ref() else {
                // An invocation of a provider that isn't declared (its
                // declaration did not resolve at parse time). The lowering
                // defaults its output to a permissive type and raises nothing,
                // so this is the only layer that catches it.
                findings.push(ProviderFinding {
                    message: format!(
                        "provider `{key}` is not present in the provider declarations"
                    ),
                    span,
                    warning: false,
                });
                continue;
            };

            // ── Deprecated `String` fallback ────────────────────────────
            // An unknown `paramType` in a type this call uses loads and is
            // typed `String`; warn, so a typo (`decimel`) doesn't pass
            // silently. Becomes an error in the next major version.
            let mut fallbacks = Vec::new();
            decl.collect_fallback_warnings(
                &key,
                field.methods.iter().map(|m| m.name.as_str()),
                &mut fallbacks,
            );
            for message in fallbacks {
                if warned.insert(message.clone()) {
                    findings.push(ProviderFinding {
                        message,
                        span,
                        warning: true,
                    });
                }
            }

            // ── Entity types ────────────────────────────────────────────
            // Every entity type the call's types name must exist — in the
            // policy schema (an app enum used as an argument) or among the
            // injected provider enums — and must be an enum: a provider sees
            // an entity as its bare id, which only identifies an enum value.
            let methods = field.methods.iter().map(|m| m.name.as_str());
            for name in decl.referenced_entity_types(methods) {
                // A provider enum is in the schema under its exported name.
                let in_schema = field.entity_type_names.get(&name).unwrap_or(&name);
                match info.entity_type(None, in_schema) {
                    None => findings.push(ProviderFinding {
                        message: format!(
                            "provider `{key}`: entityType `{name}` is not declared in the \
                             policy schema or the provider declarations' `entityTypes`"
                        ),
                        span,
                        warning: false,
                    }),
                    Some(handle) if handle.enum_eids().is_none() => {
                        findings.push(ProviderFinding {
                            message: format!(
                                "provider `{key}`: entityType `{name}` is not an enum entity \
                                 type; provider values may only be enum entities"
                            ),
                            span,
                            warning: false,
                        })
                    }
                    Some(_) => {}
                }
            }

            let expected = &decl.argument_types;
            let got = &field.invocation.args;
            if expected.len() != got.len() {
                findings.push(ProviderFinding {
                    message: format!(
                        "provider `{key}` expects {} argument(s) but got {}",
                        expected.len(),
                        got.len()
                    ),
                    span,
                    warning: false,
                });
                continue;
            }

            for (arg, param) in got.iter().zip(expected) {
                if let Some(actual) = arg_kind(arg)
                    && !param_type_accepts(&param.param_type, actual)
                {
                    findings.push(ProviderFinding {
                        message: format!(
                            "provider `{key}`: argument of type `{actual}` does not match the \
                             declared `{}`",
                            display_param(param)
                        ),
                        span,
                        warning: false,
                    });
                }
            }

            // ── Field-path argument existence ────────────────────────────
            // A context-rooted field-path argument (`context.input.x`) must
            // resolve on every action the rule's scope reaches. A DEFINITELY
            // MISSING field (undeclared on that action) is an error — the same
            // "the field must exist on every scoped action" rule Cedar and the
            // temporal dialect enforce. Before this, a provider argument was the
            // one dereference in the language exempt from that check (the arg is
            // hoisted out of Cedar's view), so `Ns::Fn(context.input.typo)`
            // validated cleanly where a bare `context.input.typo` would not —
            // an invisible asymmetry keyed only on the call being a provider.
            check_field_path_args(
                &key,
                &field.invocation.args,
                &info,
                &field.target_actions,
                &field.principal,
                &field.resource,
                span,
                &mut findings,
            );
            for method in &field.methods {
                let m_span = method.span.rebased(field.body_base);
                check_field_path_args(
                    &key,
                    &method.args,
                    &info,
                    &field.target_actions,
                    &field.principal,
                    &field.resource,
                    m_span,
                    &mut findings,
                );
            }

            // ── Argument TYPES ───────────────────────────────────────────
            // Every argument has its declared Cedar type exactly (the type
            // `ParamType::to_cedar_type_with` gives the hoisted field), in every
            // request environment the rule decides: every action its scope
            // reaches, and every principal and resource type it admits there —
            // as Cedar type-checks per request environment. A set's elements
            // each have the declared element type; a record has the declared
            // attributes, and an entity the declared entity type. A path that
            // does not resolve is the existence pass's finding; a top-level
            // literal is the literal pass's. Positional: invocation args map to
            // the provider's `argumentTypes`, method args to the method's.
            let envs = request_envs(&info, &field.target_actions, &field.principal, &field.resource);
            let names = &field.entity_type_names;
            let typing = ArgTyping {
                key: &key,
                names,
                envs: &envs,
                principal: &field.principal,
                resource: &field.resource,
            };
            for (arg, param) in field.invocation.args.iter().zip(&decl.argument_types) {
                typing.check(arg, param, true, span, &mut findings);
            }
            for method in &field.methods {
                let Some(mdecl) = decl.methods.get(&method.name) else {
                    continue;
                };
                let m_span = method.span.rebased(field.body_base);
                for (arg, param) in method.args.iter().zip(&mdecl.argument_types) {
                    typing.check(arg, param, true, m_span, &mut findings);
                }
            }

            // ── Method chain ────────────────────────────────────────────
            // Each method must be declared on the provider, must not shadow a
            // Cedar extension-method name (which would be ambiguous with the
            // native comparison forms), must be given the declared number and
            // types of arguments, and — when `inputType` is declared — must be
            // fed a compatible value by the preceding pipeline stage. The
            // pipeline's running type starts at the provider's `outputType`.
            // The running type of the pipeline, compared by kind AND (for an
            // `entity`) by entity type: two different enums are different types.
            let mut pipeline_type: &ParamType = &decl.output_type;
            for method in &field.methods {
                let m_span = method.span.rebased(field.body_base);

                if is_cedar_extension_method(&method.name) {
                    findings.push(ProviderFinding {
                        message: format!(
                            "provider `{key}`: method `{}` collides with a built-in Cedar \
                             extension method; rename the declared method",
                            method.name
                        ),
                        span: m_span,
                        warning: false,
                    });
                    continue;
                }

                let Some(mdecl) = decl.methods.get(&method.name) else {
                    let available = if decl.methods.is_empty() {
                        format!("provider `{key}` declares no methods")
                    } else {
                        format!(
                            "declared methods on `{key}` are: {}",
                            decl.methods.keys().cloned().collect::<Vec<_>>().join(", ")
                        )
                    };
                    findings.push(ProviderFinding {
                        message: format!(
                            "provider `{key}`: method `{}` is not declared ({available})",
                            method.name
                        ),
                        span: m_span,
                        warning: false,
                    });
                    // Unknown method breaks the pipeline type; stop checking
                    // the rest of this chain.
                    break;
                };

                // Optional receiver-type check: the previous stage's output
                // type must be the Cedar type this method expects to receive —
                // the types the declarations convert to, not their tokens, so a
                // `set` of `string` is not a `set` of `long`, and `integer` is
                // `long`.
                if let Some(input) = mdecl.input_type.as_ref()
                    && CType::from_param(input, &field.entity_type_names)
                        != CType::from_param(pipeline_type, &field.entity_type_names)
                {
                    findings.push(ProviderFinding {
                        message: format!(
                            "provider `{key}`: method `{}` expects an input of type `{}` but the \
                             preceding stage produces `{}`",
                            method.name,
                            display_param(input),
                            display_param(pipeline_type)
                        ),
                        span: m_span,
                        warning: false,
                    });
                }

                // Method argument count + directly-typed argument types.
                if mdecl.argument_types.len() != method.args.len() {
                    findings.push(ProviderFinding {
                        message: format!(
                            "provider `{key}`: method `{}` expects {} argument(s) but got {}",
                            method.name,
                            mdecl.argument_types.len(),
                            method.args.len()
                        ),
                        span: m_span,
                        warning: false,
                    });
                } else {
                    for (arg, param) in method.args.iter().zip(&mdecl.argument_types) {
                        if let Some(actual) = arg_kind(arg)
                            && !param_type_accepts(&param.param_type, actual)
                        {
                            findings.push(ProviderFinding {
                                message: format!(
                                    "provider `{key}`: method `{}` argument of type `{actual}` \
                                     does not match the declared `{}`",
                                    method.name,
                                    display_param(param)
                                ),
                                span: m_span,
                                warning: false,
                            });
                        }
                    }
                }

                // This method re-types the pipeline for the next stage.
                pipeline_type = &mdecl.output_type;
            }
        }
        findings
    }

    fn render(&self, finding: ProviderFinding, src: &std::sync::Arc<str>) -> Rendered {
        let help = derive_provider_help(&finding.message);
        if finding.warning {
            return Rendered::Warning(ValidationWarning::Extension {
                code: self.marker(),
                message: finding.message,
                span: finding.span.into(),
                label: None,
                help,
                src: src.clone(),
                source: None,
            });
        }
        Rendered::Error(ValidationError::Extension {
            code: self.marker(),
            message: finding.message,
            span: finding.span.into(),
            label: None,
            help,
            src: src.clone(),
            source: None,
        })
    }
}

/// Derive actionable help text from a provider validation finding's message.
fn derive_provider_help(message: &str) -> Option<String> {
    if message.contains("falling back to String") {
        Some(
            "the known paramTypes are string, integer/long, bool/boolean, decimal, set, \
             record and entity; fix the declaration in providers.json"
                .to_string(),
        )
    } else if message.contains("is not present in the provider declarations") {
        Some("check the `availableProviders` in your provider declarations JSON".to_string())
    } else if message.contains("expects") && message.contains("argument(s) but got") {
        Some("check the `argumentTypes` array in the provider declaration".to_string())
    } else if message.contains("does not match the declared") {
        Some(
            "provider arguments are typed: string, integer, decimal, bool, or set; \
             field-path arguments (context.input.X) are resolved and type-checked \
             against each scoped action's schema"
                .to_string(),
        )
    } else if message.contains("is not declared") && message.contains("method") {
        Some("check the `availableMethods` in the provider declaration".to_string())
    } else if message.contains("collides with a built-in Cedar extension method") {
        Some(
            "Cedar extension methods (contains, lessThan, isIpv4, etc.) cannot be \
             shadowed by provider methods; rename the method in the declaration"
                .to_string(),
        )
    } else if message.contains("expects an input of type") {
        Some(
            "each method's `inputType` constrains what the preceding pipeline stage must produce"
                .to_string(),
        )
    } else if message.contains("is not present in the context of action") {
        Some(
            "a provider's context field-path argument must be declared on every action \
             the rule is scoped to; scope the rule to actions that declare the field, \
             or reference a field they all share. (A present-but-optional field is \
             accepted — only a flatly-undeclared field is rejected.)"
                .to_string(),
        )
    } else if message.contains("is not present on the") {
        Some(
            "a provider's principal/resource field-path argument must be an attribute of \
             every entity type the rule's scope admits; narrow the rule (`principal is \
             <type>`) to the types that declare the attribute, or reference one they \
             all share"
                .to_string(),
        )
    } else if message.contains("declares argument type") {
        Some(
            "a provider's context field-path argument must have the declared type on \
             every action the rule is scoped to; a field typed differently on one \
             action (e.g. Long on one, String on another) does not match a scalar \
             argument type"
                .to_string(),
        )
    } else {
        None
    }
}

/// Check every field-path argument in `args` (recursing into sets) for a path
/// that is definitely missing on some scoped action.
///
/// Provider counterpart of the temporal dialect's `check_context_fields` and
/// scope-path checks. Dispatches on the path root. A `context.<path>` argument
/// must resolve on every action the rule's scope reaches (via
/// `resolve_context_path`); a present-but-OPTIONAL field resolves and is
/// accepted (the Null-tolerant sentinel contract), so only a flatly-undeclared
/// field is rejected. A `principal.<attr>` / `resource.<attr>` argument must
/// resolve on the entity types the rule's scope admits (via
/// `resolve_scope_path`, narrowed by the rule's own `principal`/`resource`
/// constraint so a rule scoped to a type that HAS the attribute is not judged
/// against sibling types it excludes). A bare `principal` / `resource` (no
/// attribute tail) always resolves.
#[allow(clippy::too_many_arguments)]
fn check_field_path_args(
    key: &str,
    args: &[Arg],
    info: &SchemaInfo,
    target_actions: &[ActionRef],
    principal: &ScopeConstraint,
    resource: &ScopeConstraint,
    span: Span,
    findings: &mut Vec<ProviderFinding>,
) {
    for arg in args {
        match arg {
            Arg::Set(items) => check_field_path_args(
                key,
                items,
                info,
                target_actions,
                principal,
                resource,
                span,
                findings,
            ),
            Arg::Field(path) => check_one_field_path(
                key,
                path,
                info,
                target_actions,
                principal,
                resource,
                span,
                findings,
            ),
            _ => {}
        }
    }
}

/// Resolve one field-path argument's EXISTENCE against each target action,
/// emitting an error for the FIRST action on which it is definitely missing
/// ("missing from any", matching Cedar/temporal's conjunctive-over-environments
/// rule). Dispatches on the path root.
#[allow(clippy::too_many_arguments)]
fn check_one_field_path(
    key: &str,
    path: &[String],
    info: &SchemaInfo,
    target_actions: &[ActionRef],
    principal: &ScopeConstraint,
    resource: &ScopeConstraint,
    span: Span,
    findings: &mut Vec<ProviderFinding>,
) {
    let Some(root) = path.first().map(String::as_str) else {
        return;
    };
    // A bare `principal` / `resource` (no tail) always resolves, to the
    // request's entity. The whole request `context` is not an argument: it has
    // no type a declaration can name.
    if path.len() < 2 {
        if root == "context" {
            findings.push(ProviderFinding {
                message: format!(
                    "provider `{key}`: argument `context` is the whole request context, which \
                     is not an argument; pass one of its attributes"
                ),
                span,
                warning: false,
            });
        }
        return;
    }
    let rest = &path[1..];
    for action in target_actions {
        let Some(handle) = info.action(action.namespace.as_deref(), &action.id) else {
            // Not in the projection; Cedar's own validator owns unknown-action.
            continue;
        };
        // Skip an action the rule's scope can never reach: under the rule's own
        // `principal is` / `resource is` narrowing there is no request
        // environment with this (principal-type, action, resource-type). Cedar
        // and the temporal dialect do not check an infeasible environment (see
        // `admits_any_env`); the provider must not either, or it would reject a
        // `context.*` argument on an action the rule can never fire on. (The
        // `principal`/`resource` roots are separately narrowed by
        // `resolve_scope_path`; gating here keeps every root consistent.)
        if !handle.admits_any_env(Some(principal), Some(resource)) {
            continue;
        }
        match root {
            // `resolve_context_path` resolves against the action's context
            // RECORD, i.e. the path WITHOUT the leading `context` root.
            "context" => {
                let missing = matches!(
                    handle.resolve_context_path(rest),
                    PathResolution::HeadMissing
                        | PathResolution::NestedMissing(_)
                        | PathResolution::NonRecord(_)
                );
                if missing {
                    findings.push(ProviderFinding {
                        message: format!(
                            "provider `{key}`: argument `{}` is not present in the \
                             context of action `{}`",
                            crate::field_path::join_under("context", rest),
                            action_display(action),
                        ),
                        span,
                        warning: false,
                    });
                    return;
                }
            }
            // `resolve_scope_path` resolves the attribute tail against the entity
            // types the action's principal/resource admits, narrowed by the
            // rule's own scope constraint. Resolved / Unknown (scope pins nothing)
            // / Ambiguous (exists on every admitted type, just differently) all
            // EXIST — accepted here; the type pass owns a scalar mismatch.
            "principal" | "resource" => {
                let narrow = if root == "principal" {
                    principal
                } else {
                    resource
                };
                if let ScopePath::Missing { segment, .. } | ScopePath::NonRecord { segment } =
                    handle.resolve_scope_path(root, rest, Some(narrow))
                {
                    findings.push(ProviderFinding {
                        message: format!(
                            "provider `{key}`: argument `{}` is not present on the `{root}` \
                             of action `{}` (no attribute `{segment}`)",
                            crate::field_path::join(path),
                            action_display(action),
                        ),
                        span,
                        warning: false,
                    });
                    return;
                }
            }
            _ => {}
        }
    }
}

/// Render an action reference as its predicate form for a diagnostic.
fn action_display(action: &ActionRef) -> String {
    let id = cedar_policy_core::ast::Eid::new(action.id.as_str()).escaped();
    match &action.namespace {
        Some(ns) => format!("{ns}::Action::\"{id}\""),
        None => format!("Action::\"{id}\""),
    }
}

/// One request environment a provider leaf's rule decides: an action its scope
/// reaches, and a principal and a resource type the action admits and the rule's
/// scope narrows to.
struct RequestEnv<'h> {
    action: &'h ActionRef,
    handle: ActionHandle<'h>,
    principal: EntityType,
    resource: EntityType,
}

/// Every request environment of the rule: each target action in the schema,
/// with each principal and resource type the rule's scope admits for it.
fn request_envs<'h>(
    info: &'h SchemaInfo,
    target_actions: &'h [ActionRef],
    principal: &ScopeConstraint,
    resource: &ScopeConstraint,
) -> Vec<RequestEnv<'h>> {
    let mut envs = Vec::new();
    for action in target_actions {
        let Some(handle) = info.action(action.namespace.as_deref(), &action.id) else {
            // Not in the projection; Cedar's own validator owns unknown-action.
            continue;
        };
        let principals: Vec<EntityType> = handle
            .admitted_types("principal", Some(principal))
            .into_iter()
            .cloned()
            .collect();
        let resources: Vec<EntityType> = handle
            .admitted_types("resource", Some(resource))
            .into_iter()
            .cloned()
            .collect();
        for p in &principals {
            for r in &resources {
                envs.push(RequestEnv {
                    action,
                    handle,
                    principal: p.clone(),
                    resource: r.clone(),
                });
            }
        }
    }
    envs
}

/// The Cedar type an argument other than a set has in the request environment
/// `env`, as the specification types it (`Provider.Arg.typeIn?`): a literal's
/// type; a `context.<path>` or `principal.<path>` / `resource.<path>` path its
/// declared type — an optional attribute along it need not be present, since an
/// absent one resolves to an absent argument, which the provider contract
/// tolerates (`id` and `type` are attributes like any other); a bare
/// `principal` / `resource` its entity type. `None` for a bare `context` and
/// for a path that does not resolve.
fn arg_type(arg: &Arg, env: &RequestEnv<'_>) -> Option<CType> {
    match arg {
        Arg::String(_) => Some(CType::String),
        Arg::Integer(_) => Some(CType::Long),
        Arg::Decimal(_) => Some(CType::Decimal),
        Arg::Bool(_) => Some(CType::Bool),
        Arg::Set(_) => None,
        Arg::Field(path) => {
            let (root, rest) = path.split_first()?;
            let ety = match root.as_str() {
                "context" => {
                    return env.handle.context_path_cedar_type(rest).map(CType::from_type);
                }
                "principal" => &env.principal,
                "resource" => &env.resource,
                _ => return None,
            };
            match rest {
                [] => Some(CType::Entity(vec![ety.to_string()])),
                _ => env
                    .handle
                    .scope_attribute_cedar_type(ety, rest)
                    .map(CType::from_type),
            }
        }
    }
}

/// What typing one provider leaf's arguments needs: the provider's name, the
/// exported names of the enums its types name, the rule's request
/// environments, and its scope narrowing.
struct ArgTyping<'a> {
    key: &'a str,
    names: &'a std::collections::BTreeMap<String, String>,
    envs: &'a [RequestEnv<'a>],
    principal: &'a ScopeConstraint,
    resource: &'a ScopeConstraint,
}

impl ArgTyping<'_> {
    /// Type-check one argument against its declared `paramType`
    /// (`Provider.Arg.hasTypeIn`), in every request environment of the rule,
    /// reporting the first environment in which it does not have the declared
    /// type. A set has each element checked against the declared element type.
    /// At the top level (`top`), a literal, and a set where no set is declared,
    /// are the literal pass's finding; a bare `context`, and a path that does
    /// not resolve, are the existence pass's.
    fn check(
        &self,
        arg: &Arg,
        declared: &ParamType,
        top: bool,
        span: Span,
        findings: &mut Vec<ProviderFinding>,
    ) {
        let declared_ty = CType::from_param(declared, self.names);
        match arg {
            Arg::String(_) | Arg::Integer(_) | Arg::Decimal(_) | Arg::Bool(_) if top => {}
            Arg::Set(items) => match &declared_ty {
                CType::Set(_) => {
                    // A set with no declared element type holds strings, as
                    // `to_cedar_type_with` types it.
                    let element = declared.items.as_deref().cloned().unwrap_or_else(|| ParamType {
                        param_type: "string".to_string(),
                        ..Default::default()
                    });
                    for item in items {
                        self.check(item, &element, false, span, findings);
                    }
                }
                _ if top => {}
                _ => {
                    if let Some(env) = self.envs.first() {
                        self.report(arg, "Set".to_string(), declared, &declared_ty, env, span, findings);
                    }
                }
            },
            Arg::Field(path) if path.len() < 2 && path.first().is_some_and(|r| r == "context") => {}
            _ => {
                if self.ambiguous(arg, declared, span, findings) {
                    return;
                }
                for env in self.envs {
                    // A path that does not resolve is the existence pass's finding.
                    let Some(ty) = arg_type(arg, env) else {
                        continue;
                    };
                    if ty != declared_ty {
                        self.report(arg, display_ctype(&ty), declared, &declared_ty, env, span, findings);
                        return;
                    }
                }
            }
        }
    }

    /// A `principal.<attr>` / `resource.<attr>` argument whose attribute has a
    /// different type on the entity types the rule admits cannot have one
    /// declared type in every environment: report it as such.
    fn ambiguous(
        &self,
        arg: &Arg,
        declared: &ParamType,
        span: Span,
        findings: &mut Vec<ProviderFinding>,
    ) -> bool {
        let Arg::Field(path) = arg else {
            return false;
        };
        let Some((root, rest)) = path.split_first() else {
            return false;
        };
        let narrow = match root.as_str() {
            "principal" => self.principal,
            "resource" => self.resource,
            _ => return false,
        };
        if rest.is_empty() {
            return false;
        }
        for env in self.envs {
            if let ScopePath::Ambiguous { types } = env.handle.resolve_scope_path(root, rest, Some(narrow)) {
                findings.push(ProviderFinding {
                    message: format!(
                        "provider `{}`: argument `{}` has a different type on each `{root}` type \
                         the rule admits (`{}`), so it cannot match the declared argument type `{}`",
                        self.key,
                        crate::field_path::join(path),
                        types.join("`, `"),
                        display_param(declared),
                    ),
                    span,
                    warning: false,
                });
                return true;
            }
        }
        false
    }

    #[allow(clippy::too_many_arguments)]
    fn report(
        &self,
        arg: &Arg,
        shown: String,
        declared: &ParamType,
        declared_ty: &CType,
        env: &RequestEnv<'_>,
        span: Span,
        findings: &mut Vec<ProviderFinding>,
    ) {
        // A declared set by its element type; two records of different shapes
        // render alike, so by their attributes then.
        let wanted = match declared_ty {
            CType::Set(_) => display_ctype(declared_ty),
            _ => display_param(declared),
        };
        let (shown, wanted) = if shown == wanted {
            (shown_full(arg, env).unwrap_or(shown), declared_ty.render())
        } else {
            (shown, wanted)
        };
        let reads_scope =
            |root: &str| matches!(arg, Arg::Field(p) if p.first().is_some_and(|r| r == root));
        let scope = if reads_scope("principal") {
            format!(" when the principal is a `{}`", env.principal)
        } else if reads_scope("resource") {
            format!(" when the resource is a `{}`", env.resource)
        } else {
            String::new()
        };
        findings.push(ProviderFinding {
            message: format!(
                "provider `{}`: argument `{}` has type `{shown}` on action `{}`{scope} but the \
                 provider declares argument type `{wanted}`",
                self.key,
                render_arg(arg),
                action_display(env.action),
            ),
            span,
            warning: false,
        });
    }
}

/// An argument's type in full (a record with its attributes), for a diagnostic.
fn shown_full(arg: &Arg, env: &RequestEnv<'_>) -> Option<String> {
    arg_type(arg, env).map(|ty| ty.render())
}

/// An argument as written, for a diagnostic.
fn render_arg(arg: &Arg) -> String {
    match arg {
        Arg::Field(path) => crate::field_path::join(path),
        Arg::String(s) => format!("{s:?}"),
        Arg::Integer(i) => i.to_string(),
        Arg::Decimal(d) => format!("decimal({d:?})"),
        Arg::Bool(b) => b.to_string(),
        Arg::Set(items) => format!(
            "[{}]",
            items.iter().map(render_arg).collect::<Vec<_>>().join(", ")
        ),
    }
}

/// A declared type as shown in diagnostics: an `entity` type by its entity
/// type's name (`Drupe::AlertLevel`), anything else by its `paramType`.
fn display_param(ty: &ParamType) -> String {
    match (ty.param_type.as_str(), ty.entity_type.as_deref()) {
        ("entity", Some(name)) => name.to_string(),
        (kind, _) => kind.to_string(),
    }
}

/// A Cedar type in Cedar-familiar form for diagnostics (`Set<String>`, a
/// `record`, an entity as `entity:Ns::Type`).
fn display_ctype(ty: &CType) -> String {
    match ty {
        CType::Entity(names) if names.len() == 1 => format!("entity:{}", names[0]),
        CType::Set(inner) => format!("Set<{}>", display_ctype(inner)),
        CType::Record { .. } => "record".to_string(),
        other => other.render(),
    }
}

/// The declared `paramType` token a directly-typed argument satisfies, or
/// `None` for a field path (deferred to schema validation).
fn arg_kind(arg: &Arg) -> Option<&'static str> {
    match arg {
        Arg::String(_) => Some("string"),
        Arg::Integer(_) => Some("integer"),
        Arg::Decimal(_) => Some("decimal"),
        Arg::Bool(_) => Some("bool"),
        Arg::Set(_) => Some("set"),
        Arg::Field(_) => None,
    }
}

/// Whether a declared `paramType` accepts an argument of the given kind.
/// `integer`/`long` and `bool`/`boolean` are accepted as synonyms.
fn param_type_accepts(declared: &str, actual: &str) -> bool {
    match actual {
        "string" => declared == "string",
        "integer" => declared == "integer" || declared == "long",
        "decimal" => declared == "decimal",
        "bool" => declared == "bool" || declared == "boolean",
        "set" => declared == "set",
        _ => false,
    }
}

/// The Cedar extension-method / built-in names a provider method may not
/// shadow. The decimal comparison methods (`lessThan`, …) are the terminal
/// comparison form of the provider grammar (`method_cmp`), and the rest are
/// Cedar's native set / entity-tag / IP / datetime methods; a declared
/// provider method sharing one of these names would be ambiguous, so it is
/// rejected. This mirrors the exclusion list the grammar uses to keep
/// `.lessThan(…)` a comparison rather than a projection method.
fn is_cedar_extension_method(name: &str) -> bool {
    matches!(
        name,
        "lessThan"
            | "lessThanOrEqual"
            | "greaterThan"
            | "greaterThanOrEqual"
            | "contains"
            | "containsAll"
            | "containsAny"
            | "isEmpty"
            | "hasTag"
            | "getTag"
            | "isIpv4"
            | "isIpv6"
            | "isLoopback"
            | "isMulticast"
            | "isInRange"
            | "offset"
            | "durationSince"
            | "toDate"
            | "toTime"
            | "toMilliseconds"
            | "toSeconds"
            | "toMinutes"
            | "toHours"
            | "toDays"
    )
}
