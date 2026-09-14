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
use crate::error::{Span, ValidationError};
use crate::extension::dialect::{DogwoodDialect, Rendered, ValidationCtx};
use crate::extension::provider::ast::Arg;
use crate::extension::provider::declarations::ParamType;
use crate::extension::temporal::schema_info::{
    ArrayElem, PathResolution, RichType, SchemaInfo, ScopePath,
};

/// One provider validation finding, with its span already rebased into the
/// `.dw` source.
pub struct ProviderFinding {
    pub message: String,
    pub span: Span,
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
                });
                continue;
            };

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
                            param.param_type
                        ),
                        span,
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

            // ── Field-path argument TYPE (axis C) ────────────────────────
            // A field-path argument's resolved schema type must match the
            // declared `paramType` for its position — on every scoped action,
            // just as Cedar type-checks per request environment and the
            // temporal dialect per action. The resolution reuses the same
            // `resolve_context_path` as the existence check; only a clear
            // SCALAR-vs-scalar mismatch is rejected (set/record/entity and
            // non-scalar resolved types are left lenient for now — see
            // `check_field_path_type`). Positional: invocation args map to the
            // provider's `argumentTypes`, method args to the method's.
            for (arg, param) in field.invocation.args.iter().zip(&decl.argument_types) {
                check_arg_type(
                    &key,
                    arg,
                    param,
                    &info,
                    &field.target_actions,
                    &field.principal,
                    &field.resource,
                    span,
                    &mut findings,
                );
            }
            for method in &field.methods {
                let Some(mdecl) = decl.methods.get(&method.name) else {
                    continue;
                };
                let m_span = method.span.rebased(field.body_base);
                for (arg, param) in method.args.iter().zip(&mdecl.argument_types) {
                    check_arg_type(
                        &key,
                        arg,
                        param,
                        &info,
                        &field.target_actions,
                        &field.principal,
                        &field.resource,
                        m_span,
                        &mut findings,
                    );
                }
            }

            // ── Method chain ────────────────────────────────────────────
            // Each method must be declared on the provider, must not shadow a
            // Cedar extension-method name (which would be ambiguous with the
            // native comparison forms), must be given the declared number and
            // types of arguments, and — when `inputType` is declared — must be
            // fed a compatible value by the preceding pipeline stage. The
            // pipeline's running type starts at the provider's `outputType`.
            let mut pipeline_type = decl.output_type.param_type.clone();
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
                    });
                    // Unknown method breaks the pipeline type; stop checking
                    // the rest of this chain.
                    break;
                };

                // Optional receiver-type check: the previous stage's output
                // type must match what this method expects to receive.
                if let Some(input) = mdecl.input_type.as_ref()
                    && input.param_type != pipeline_type
                {
                    findings.push(ProviderFinding {
                        message: format!(
                            "provider `{key}`: method `{}` expects an input of type `{}` but the \
                             preceding stage produces `{}`",
                            method.name, input.param_type, pipeline_type
                        ),
                        span: m_span,
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
                                    method.name, param.param_type
                                ),
                                span: m_span,
                            });
                        }
                    }
                }

                // This method re-types the pipeline for the next stage.
                pipeline_type = mdecl.output_type.param_type.clone();
            }
        }
        findings
    }

    fn render(&self, finding: ProviderFinding, src: &std::sync::Arc<str>) -> Rendered {
        let help = derive_provider_help(&finding.message);
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
    if message.contains("is not present in the provider declarations") {
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
    // A bare `context` / `principal` / `resource` (no tail) always resolves.
    if path.len() < 2 {
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
                            "provider `{key}`: argument `context.{}` is not present in the \
                             context of action `{}`",
                            rest.join("."),
                            action_display(action),
                        ),
                        span,
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
                            path.join("."),
                            action_display(action),
                        ),
                        span,
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

/// Type-check one provider ARGUMENT against its declared `paramType`, recursing
/// into a set-literal argument (`[a, b]`) so each element field-path is checked
/// against the declared set's ELEMENT type — mirroring the existence pass
/// (`check_field_path_args`), which also recurses into `Arg::Set`. A field-path
/// argument dispatches to `check_field_path_type`; a set literal recurses per
/// element (only when the declared arg is a set with a known element type);
/// other literal args are owned by the scalar/literal arg-type check.
#[allow(clippy::too_many_arguments)]
fn check_arg_type(
    key: &str,
    arg: &Arg,
    declared: &ParamType,
    info: &SchemaInfo,
    target_actions: &[ActionRef],
    principal: &ScopeConstraint,
    resource: &ScopeConstraint,
    span: Span,
    findings: &mut Vec<ProviderFinding>,
) {
    match arg {
        Arg::Field(path) => check_field_path_type(
            key,
            path,
            declared,
            info,
            target_actions,
            principal,
            resource,
            span,
            findings,
        ),
        Arg::Set(items) => {
            if let Some(item) = declared.items.as_deref() {
                for it in items {
                    check_arg_type(
                        key,
                        it,
                        item,
                        info,
                        target_actions,
                        principal,
                        resource,
                        span,
                        findings,
                    );
                }
            }
        }
        _ => {}
    }
}

/// Type-check one field-path argument against its declared `paramType`, per
/// scoped action.
///
/// Resolution reuses `resolve_context_path` / `resolve_scope_path` (whichever
/// the root selects); this compares the resolved rich type against the declared
/// `paramType` by CATEGORY (`param_matches_rich`). Scalars must match exactly
/// (`string`/`Long`/`Bool`/`decimal`). A `set` must be an array, and when both
/// element types are known the element types must match too (Cedar's set
/// element-type check, #2). A `record` need only be an object — its FIELDS are
/// not compared (Cedar records are invariant, but exact field matching needs
/// structured types and is the deferred boundary #3). A mismatch is reported on
/// the first scoped action where it occurs ("wrong on any"). An unknown declared
/// `paramType`, or a resolved type this cannot classify, is left lenient;
/// missing fields are owned by the existence pass.
#[allow(clippy::too_many_arguments)]
fn check_field_path_type(
    key: &str,
    path: &[String],
    declared: &ParamType,
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
    if path.len() < 2 {
        return;
    }
    let rest = &path[1..];
    for action in target_actions {
        let Some(handle) = info.action(action.namespace.as_deref(), &action.id) else {
            continue;
        };
        // Skip an action the rule's scope can never reach (see the existence
        // pass and `admits_any_env`): an infeasible request environment must not
        // be type-checked, matching Cedar and the temporal dialect.
        if !handle.admits_any_env(Some(principal), Some(resource)) {
            continue;
        }
        // The resolved rich type on this action, for whichever root — `context`
        // via `resolve_context_path`, `principal`/`resource` via
        // `resolve_scope_path` (narrowed). Only a `Resolved` single type is
        // compared; `Ambiguous`/`Unknown`/missing are left to the existence
        // pass.
        let resolved_rich = match root {
            "context" => match handle.resolve_context_path(rest) {
                PathResolution::Resolved(rich) => Some(rich),
                _ => None,
            },
            "principal" | "resource" => {
                let narrow = if root == "principal" {
                    principal
                } else {
                    resource
                };
                match handle.resolve_scope_path(root, rest, Some(narrow)) {
                    ScopePath::Resolved(rich) => Some(rich),
                    // Exists on every admitted type but at DIFFERENT types, so no
                    // single declared arg type can match in every request
                    // environment. Cedar rejects such a use (it accepts only
                    // `has` / a use valid in every env); mirror that here in the
                    // TYPE pass. The existence pass treats an ambiguous attribute
                    // as present, so the diagnosis is a type mismatch, not
                    // "not present".
                    ScopePath::Ambiguous { types } => {
                        findings.push(ProviderFinding {
                            message: format!(
                                "provider `{key}`: argument `{}` has a different type on each \
                                 `{root}` type the rule admits (`{}`), so it cannot match the \
                                 declared argument type `{}`",
                                path.join("."),
                                types.join("`, `"),
                                declared.param_type,
                            ),
                            span,
                        });
                        return;
                    }
                    _ => None,
                }
            }
            _ => None,
        };
        if let Some(rich) = resolved_rich
            && !param_matches_rich(declared, &rich)
        {
            findings.push(ProviderFinding {
                message: format!(
                    "provider `{key}`: argument `{}` has type `{}` on action `{}` but the \
                     provider declares argument type `{}`",
                    path.join("."),
                    display_rich(&rich),
                    action_display(action),
                    declared.param_type,
                ),
                span,
            });
            return;
        }
    }
}

/// Whether a resolved rich type is compatible with a declared `paramType`, by
/// CATEGORY (#1) plus set element type (#2). Scalars must match exactly; a
/// `set` must be an array whose element type (when both are known) matches the
/// declared `items`; a `record` need only be an object (fields deferred, #3).
/// An unknown declared `paramType`, or a rich type this does not recognize, is
/// treated as compatible (lenient) rather than risk a false rejection.
fn param_matches_rich(declared: &ParamType, rich: &RichType) -> bool {
    match declared.param_type.as_str() {
        "string" => matches!(rich, RichType::String),
        "integer" | "long" => matches!(rich, RichType::Long),
        "bool" | "boolean" => matches!(rich, RichType::Bool),
        "decimal" => matches!(rich, RichType::Decimal),
        "set" => match rich {
            // #1: must be an array. #2: if both element types are known, check
            // them. A bare array (element unknown), or a declared set with no
            // `items`, leaves the element unknown -> accept.
            RichType::Array(ArrayElem::Unknown) => true,
            RichType::Array(ArrayElem::Of(elem)) => match declared.items.as_deref() {
                Some(item_decl) => param_matches_rich(item_decl, elem),
                None => true,
            },
            // A mixed-element array matches only a set with no declared element.
            RichType::Array(ArrayElem::Mixed) => declared.items.is_none(),
            _ => false,
        },
        "record" => matches!(rich, RichType::Record),
        // Unknown declared type: lenient.
        _ => true,
    }
}

/// A user-facing name for a resolved rich type, rendering non-scalars in
/// Cedar-familiar form (`array<string>` -> `Set<String>`, `object` -> `record`).
fn display_rich(rich: &RichType) -> String {
    match rich {
        RichType::Long => "Long".to_string(),
        RichType::String => "String".to_string(),
        RichType::Bool => "Bool".to_string(),
        RichType::Decimal => "decimal".to_string(),
        RichType::Timepoint => "timepoint".to_string(),
        RichType::Record => "record".to_string(),
        RichType::Array(ArrayElem::Unknown) => "Set".to_string(),
        RichType::Array(ArrayElem::Mixed) => "Set<?>".to_string(),
        RichType::Array(ArrayElem::Of(elem)) => format!("Set<{}>", display_rich(elem)),
        RichType::Entity(Some(name)) => format!("entity:{name}"),
        RichType::Entity(None) => "entity".to_string(),
        RichType::Never => "never".to_string(),
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
