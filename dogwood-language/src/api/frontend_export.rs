//! A JSON export of the frontend's inputs and of its observables at every
//! stage boundary, for differential testing of an independent implementation
//! of the stages after the parsers.
//!
//! Behind the off-by-default feature `frontend-export`, and not part of the
//! public API. [`export`] takes the sources of one bundle (the policy text,
//! the service schema's macros, event-schema DSL and provider declarations,
//! and the action schema) and returns one JSON object:
//!
//! * `inputs`: what the parsers produce, as the frontend receives it: the
//!   surface policy set before the macro library is merged and macros are
//!   expanded (with the source spans the macro expander reads), the macro
//!   library's definitions, the event-schema DSL, the provider declarations
//!   as deserialized (before their consistency check), and the action schema
//!   as a Cedar schema fragment. Each is `{"ok": v}` or `{"error": e}`;
//! * `stages`: the result of each stage, run on the observables of the stages
//!   it depends on, in the order the lowering runs them. A stage is absent
//!   when an input it needs is unavailable (an earlier stage failed, or a
//!   parser rejected its source);
//! * `outcome`: what the public pipeline (parse, then lower) does with the
//!   same sources: the rejection, or the rule ids, revisions and hashes of the
//!   lowered set, with `mismatches` listing every component on which the
//!   stages above disagree with it (empty when the stages reproduce the
//!   pipeline).
//!
//! The encoding is a constructor-tagged one: a variant without fields is its
//! name (`"any"`), a variant with fields is a one-key object holding them by
//! name (`{"eq": {"entity": …}}`), a struct is an object, an optional value is
//! `null` when absent, and a map is an array of `[key, value]` pairs in the
//! map's iteration order. An error is `{"stage", "category", "message",
//! "span"}`, `category` being the lowering error's kind (`parse`, `macro`,
//! `cedarify`, `policySet`, `cedarSchema`, `eventSchema`, `providers`).

use std::collections::{BTreeMap, BTreeSet};
use std::sync::Arc;

use cedar_policy_core::ast as cedar_ast;
use cedar_policy_core::validator::RawName;
use cedar_policy_core::validator::json_schema;
use serde_json::{Map, Value as Json, json};

use super::{Error, Parsed};
use crate::ast::{
    BinOp, CondKeyword, Effect, Expr, ExprKind, MacroBody, MacroDef, Policy, PolicySet, UnOp,
};
use crate::cedarify::{ContextField, ProviderField, ScopeConstraint, ScopedAction};
use crate::error::Span;
use crate::event_schema::ast as dsl;
use crate::event_schema::derive::{DerivedEvent, DerivedEventSchema, DerivedFieldNode, FieldType};
use crate::extension::Extension;
use crate::extension::provider::ast::{Arg, Invocation, MethodCall};
use crate::extension::provider::declarations::{
    EntityTypeDecl, Implementation, MethodDecl, ParamType, ProviderDecl, ProviderDeclarations,
};
use crate::extension::temporal::Temporal;
use crate::extension::temporal::ast::{
    AggExpr, AggExprKind, ArithOp, BinderSlot, Call, CallArg, CmpOp, Condition, ConditionKind,
    Interval, NamedArg, Predicate, Sigil, Term, TimeUnit, Type, TypedBinder, WithinSpec,
};
use crate::service_schema::{DEFAULT_EVENT_SCHEMA, DEFAULT_MACROS, ServiceSchema};

/// The sources of one bundle.
#[derive(Debug, Clone, Copy)]
pub struct BundleSources<'a> {
    /// The policy text (`.dw`).
    pub policy: &'a str,
    /// The event-schema DSL (`.dwschema`); `None` for the default schema.
    pub event_schema: Option<&'a str>,
    /// The provider declarations (`providers.json`); `None` when there are none.
    pub providers: Option<&'a str>,
    /// The macro library; `None` for the default library.
    pub macros: Option<&'a str>,
    /// The action schema (`.cedarschema`).
    pub action_schema: &'a str,
    /// The stable-id source the public pipeline assigns ids with
    /// (`ParsedPolicySet::with_ids`); `None` for positional ids.
    pub ids: Option<&'a crate::IdSource>,
    /// The distincter the public pipeline lowers under
    /// (`lower_with_distincter`); `None` for `lower`.
    pub distincter: Option<&'a str>,
}

// ─── The inputs alone ───────────────────────────────────────────────────

/// The parsed inputs of one bundle, exactly as the Lean frontend's entry points
/// take them (the `lowerAll` input of the frontend's FFI format), and as
/// [`export`] records them under `inputs`: the policy set as the parser produced
/// it, the macro library's definitions, the event-schema DSL, the provider
/// declarations, the action schema, the distincter and the id source.
///
/// Only the parsers run: no frontend stage (the macro library's merge, macro
/// expansion, the provider declarations' check, stable ids, derivation,
/// lowering, augmentation, validation) and no public pipeline. A parser's
/// rejection is the value `{"error": …}` of its key, which the Lean frontend
/// reports where the crate's pipeline reports it. The crate's own Lean frontend
/// (feature `lean-frontend`) sends the same JSON, built by the same encoders,
/// for a bundle it lowers.
pub fn inputs(b: &BundleSources<'_>) -> Json {
    let shared = SharedParses::parse(b.event_schema, b.providers, b.macros, b.action_schema);
    let policy = parse_policy(b.policy);
    single_inputs(
        &shared.inputs(),
        entry_inputs(policy.as_ref(), b.distincter, b.ids),
    )
}

/// The parsed inputs of several policy sets lowered together, exactly as the
/// Lean frontend's entry points take them (the `lowerManyAll` input), and as
/// [`export_many`] records them under `inputs`: the shared inputs, and each
/// entry's policy set, distincter and id source. Only the parsers run, as in
/// [`inputs`].
pub fn inputs_many(m: &ManySources<'_>) -> Json {
    let shared = SharedParses::parse(m.event_schema, m.providers, m.macros, m.action_schema);
    many_inputs(&shared.inputs(), m.entries.iter().map(|e| {
        let policy = parse_policy(e.policy);
        entry_inputs(policy.as_ref(), Some(e.distincter), e.ids)
    }))
}

// ─── Temporal leaves alone ──────────────────────────────────────────────

/// One temporal leaf of a policy set lowered elsewhere, as a caller that sends
/// temporal fields alone has it: its id, its rule's action scope, and its
/// authored condition (after macro expansion, before pin injection), parsed
/// ([`crate::temporal_ast::parse_condition`]).
#[derive(Debug, Clone, Copy)]
pub struct LeafInput<'a> {
    /// The leaf's id: the `context.<id>` its rule reads.
    pub id: &'a str,
    /// Its rule's action scope.
    pub action: &'a super::ActionScope,
    /// Its authored condition.
    pub condition: &'a Condition,
}

/// **The parsed inputs of temporal leaves**, for an implementation of the
/// frontend's stages in another language that lowers the leaves as lowering
/// lowers a policy set's (pins injected from the derived event schema, the
/// action schema augmented with each leaf's `context.<id>`): the inputs every
/// entry of [`inputs`] shares, without a macro library or provider
/// declarations (`library` and `providers` are `null`), and `leaves`, each
/// leaf's `id`, `action` (its scope as lowering records it: `"unconstrained"`,
/// `{"concrete": {"ns", "id"}}` or `{"list": {"actions"}}`, a namespace being
/// its text, `""` at the root) and `condition` (in the encoding of a policy's
/// temporal condition), in order. Only the parsers of the schemas run.
pub fn leaf_inputs(
    event_schema: Option<&str>,
    action_schema: &str,
    leaves: &[LeafInput<'_>],
) -> Json {
    let shared = SharedParses::parse(event_schema, None, Some(""), action_schema);
    let mut m = shared.inputs();
    let scope = |a: &super::ActionScope| {
        let pair = |r: &super::ActionRef| (r.namespace.clone().unwrap_or_default(), r.id.clone());
        scoped_action(&match a {
            super::ActionScope::Concrete(r) => ScopedAction::Concrete(pair(r)),
            super::ActionScope::List(rs) => ScopedAction::List(rs.iter().map(pair).collect()),
            super::ActionScope::Unconstrained => ScopedAction::Unconstrained,
        })
    };
    m.insert(
        "leaves".into(),
        Json::Array(
            leaves
                .iter()
                .map(|l| {
                    json!({"id": l.id, "action": scope(l.action), "condition": condition(l.condition)})
                })
                .collect(),
        ),
    );
    Json::Object(m)
}

// ─── Cedar's part of a lowered set, from its JSON ────────────────────────

/// The Cedar policy set of a lowered set's `policies` (`[{"id", "est", …}]`, in
/// rule order: the `policies` of the Lean frontend's lowered set, or of
/// `lowered_record`), with each rule's id and the annotations of its policy
/// JSON. Each policy is built from Cedar's policy JSON (`est`) with Cedar's own
/// constructors, as the crate builds the policies of a set its Lean frontend
/// lowers (and as its Rust frontend builds them): a core policy set, then the
/// public one. A rule's `text` is not read: its policy JSON is the policy.
///
/// The error names the first rule whose JSON is not a static Cedar policy, or an
/// id two rules share.
pub fn cedar_policy_set(policies: &Json) -> Result<cedar_policy::PolicySet, String> {
    cedar_policies(policies).map(|(set, _)| set)
}

/// The augmented schema of a lowered set, from its JSON (`augmentedSchema`:
/// Cedar's JSON schema form, `SchemaFragment::to_json_value`), and compiled by
/// Cedar, as the crate builds the schema of a set its Lean frontend lowers.
pub fn cedar_schema(
    augmented_schema: &Json,
) -> Result<(cedar_policy::SchemaFragment, cedar_policy::Schema), String> {
    let fragment = cedar_policy::SchemaFragment::from_json_value(augmented_schema.clone())
        .map_err(|e| e.to_string())?;
    let schema = fragment
        .clone()
        .try_into()
        .map_err(|e: cedar_policy::SchemaError| e.to_string())?;
    Ok((fragment, schema))
}

/// [`cedar_policy_set`], with the rules' ids in rule order.
pub(crate) fn cedar_policies(
    policies: &Json,
) -> Result<(cedar_policy::PolicySet, Vec<String>), String> {
    fn field<'a>(p: &'a Json, key: &str) -> Result<&'a Json, String> {
        p.get(key).ok_or_else(|| format!("a rule has no `{key}`"))
    }
    let mut set = cedar_ast::PolicySet::new();
    let mut ids = Vec::new();
    let items = policies.as_array().ok_or("`policies` is not an array")?;
    for p in items {
        let id = field(p, "id")?
            .as_str()
            .ok_or("a rule's `id` is not a string")?
            .to_owned();
        let est: cedar_policy_core::est::Policy = serde_json::from_value(field(p, "est")?.clone())
            .map_err(|e| format!("rule `{id}`: not Cedar's policy JSON: {e}"))?;
        let policy = est
            .try_into_ast_policy(Some(cedar_ast::PolicyID::from_string(&id)))
            .map_err(|e| format!("rule `{id}`: {e}"))?;
        let policy = cedar_ast::StaticPolicy::try_from(policy.template().clone())
            .map_err(|e| format!("rule `{id}`: not a static policy: {e}"))?;
        set.add_static(policy)
            .map_err(|e| format!("rule `{id}`: {e}"))?;
        ids.push(id);
    }
    let set = cedar_policy::PolicySet::from(set);
    Ok((set, ids))
}

/// What the parsers produce from the sources every entry shares: the macro
/// library (`None` for a blank one), the event-schema DSL, the provider
/// declarations as deserialized (`None` when there are none), and the action
/// schema; each failure is its error record.
pub(crate) struct SharedParses {
    pub(crate) library: Option<Result<PolicySet, Json>>,
    pub(crate) event_schema: Result<dsl::EventSchema, Json>,
    pub(crate) providers: Option<Result<ProviderDeclarations, Json>>,
    pub(crate) fragment: Result<json_schema::Fragment<RawName>, Json>,
}

impl SharedParses {
    /// Parse the shared sources: `None` for the default event schema, no
    /// providers, the default macro library.
    pub(crate) fn parse(
        event_schema: Option<&str>,
        providers: Option<&str>,
        macros: Option<&str>,
        action_schema: &str,
    ) -> SharedParses {
        let macros_src = macros.unwrap_or(DEFAULT_MACROS);
        let event_src = event_schema.unwrap_or(DEFAULT_EVENT_SCHEMA);
        SharedParses {
            library: (!macros_src.trim().is_empty()).then(|| {
                crate::parser::parse_policies_with(macros_src, &dogwood_syntax::ParseOptions::default())
                    .map_err(|errs| parse_error("library", &errs))
            }),
            event_schema: if event_src.trim().is_empty() {
                Err(err("eventSchema", "eventSchema", "empty event schema", None))
            } else {
                crate::event_schema::parse::parse_event_schema(event_src)
                    .map_err(|m| err("eventSchema", "eventSchema", &m, None))
            },
            providers: providers.map(|text| {
                serde_json::from_str::<ProviderDeclarations>(strip_bom(text)).map_err(|e| {
                    err("providers", "providers", &format!("providers.json: {e}"), None)
                })
            }),
            fragment: parse_action_schema(strip_bom(action_schema)),
        }
    }

    /// The shared inputs, encoded ([`shared_inputs`]).
    pub(crate) fn inputs(&self) -> Map<String, Json> {
        shared_inputs(
            self.library.as_ref().map(Result::as_ref),
            self.event_schema.as_ref(),
            self.providers.as_ref().map(Result::as_ref),
            Some(self.fragment.as_ref()),
        )
    }
}

/// The parser's output for a policy text, or its error record.
pub(crate) fn parse_policy(src: &str) -> Result<PolicySet, Json> {
    crate::parser::parse_policies_with(src, &dogwood_syntax::ParseOptions::default()).map_err(|errs| parse_error("policy", &errs))
}

/// The action schema as a Cedar schema fragment, or its error record.
pub(crate) fn parse_action_schema(src: &str) -> Result<json_schema::Fragment<RawName>, Json> {
    crate::cedarify::parse_base_schema(src)
        .map_err(|e| err("actionSchema", "cedarify", &e.message, e.span))
}

/// The inputs every entry shares, encoded: `library` (`null` for none, else the
/// library's definitions and its policy count), `eventSchema`, `providers`
/// (`null` for none) and `actionSchema` (an empty schema for `None`: the parse
/// phase reads none), each `{"ok": v}` or `{"error": e}`.
pub(crate) fn shared_inputs(
    library: Option<Result<&PolicySet, &Json>>,
    event_schema: Result<&dsl::EventSchema, &Json>,
    providers: Option<Result<&ProviderDeclarations, &Json>>,
    action_schema: Option<Result<&json_schema::Fragment<RawName>, &Json>>,
) -> Map<String, Json> {
    let mut m = Map::new();
    m.insert(
        "library".into(),
        match library {
            None => Json::Null,
            Some(l) => result(l, |ps| {
                json!({"defs": ps.defs.iter().map(macro_def).collect::<Vec<_>>(),
                       "policies": ps.policies.len()})
            }),
        },
    );
    m.insert("eventSchema".into(), result(event_schema, dsl_schema));
    m.insert(
        "providers".into(),
        match providers {
            None => Json::Null,
            Some(p) => result(p, declarations),
        },
    );
    m.insert(
        "actionSchema".into(),
        match action_schema {
            None => json!({"ok": []}),
            Some(f) => result(f, schema_fragment),
        },
    );
    m
}

/// One entry's own inputs, encoded: `policy` (the parser's output), `distincter`
/// (`null` for none) and `ids` (`null` for none, else the id source).
pub(crate) fn entry_inputs(
    policy: Result<&PolicySet, &Json>,
    distincter: Option<&str>,
    ids: Option<&crate::IdSource>,
) -> Map<String, Json> {
    let mut m = Map::new();
    m.insert("policy".into(), result(policy, policy_set));
    m.insert("distincter".into(), json!(distincter));
    m.insert("ids".into(), ids.map(id_source).unwrap_or(Json::Null));
    m
}

/// The input of one policy set: its policy, the shared inputs, its distincter and
/// its ids, in that order.
pub(crate) fn single_inputs(shared: &Map<String, Json>, mut entry: Map<String, Json>) -> Json {
    let mut m = Map::new();
    m.insert("policy".into(), entry.remove("policy").unwrap_or(Json::Null));
    m.extend(shared.iter().map(|(k, v)| (k.clone(), v.clone())));
    m.extend(entry);
    Json::Object(m)
}

/// The input of several policy sets lowered together: the shared inputs, and the
/// entries.
pub(crate) fn many_inputs(
    shared: &Map<String, Json>,
    entries: impl Iterator<Item = Map<String, Json>>,
) -> Json {
    let mut m = shared.clone();
    m.insert(
        "entries".into(),
        Json::Array(entries.map(Json::Object).collect()),
    );
    Json::Object(m)
}

/// Export one bundle: its parsed inputs, every stage's observable, and the
/// outcome of the public pipeline (see the module documentation).
pub fn export(b: &BundleSources<'_>) -> Json {
    let dw_src: Arc<str> = Arc::from(b.policy);
    let action_src = strip_bom(b.action_schema);
    let macros_src = b.macros.unwrap_or(DEFAULT_MACROS);

    // ─── Inputs ──────────────────────────────────────────────────────
    let shared = SharedParses::parse(b.event_schema, b.providers, b.macros, b.action_schema);
    let policy = parse_policy(b.policy);
    let inputs = single_inputs(
        &shared.inputs(),
        entry_inputs(policy.as_ref(), b.distincter, b.ids),
    );
    let SharedParses {
        library,
        event_schema,
        providers,
        fragment,
    } = shared;

    // ─── Stages, in the order the lowering runs them ─────────────────
    let mut stages = Map::new();
    let mut put = |name: &str, v: Json| {
        stages.insert(name.to_string(), v);
    };

    // The provider declarations' consistency check.
    let decls: Option<Option<&ProviderDeclarations>> = match &providers {
        None => Some(None),
        Some(Ok(d)) => {
            let checked = d.check();
            put("providerCheck", unit_result(&checked, "providerCheck", "providers"));
            checked.is_ok().then_some(Some(d))
        }
        Some(Err(_)) => None,
    };

    // The macro library merged into the policy set's own definitions.
    let merged: Option<PolicySet> = match (&policy, &library) {
        (Ok(p), None) => {
            put("mergeLibrary", json!({"ok": {"defs": defs(&p.defs)}}));
            Some(p.clone())
        }
        (Ok(p), Some(Ok(lib))) => match crate::macros::check_defs(&lib.defs) {
            Err(e) => {
                put("mergeLibrary", json!({"error": err("mergeLibrary", "macro", &e.message, Some(e.span))}));
                None
            }
            Ok(()) => {
                let mut m = p.clone();
                match super::merge_macro_library(&mut m, macros_src, &dogwood_syntax::ParseOptions::default()) {
                    Ok(()) => {
                        put("mergeLibrary", json!({"ok": {"defs": defs(&m.defs)}}));
                        Some(m)
                    }
                    Err(e) => {
                        put("mergeLibrary", json!({"error": api_error("mergeLibrary", &e)}));
                        None
                    }
                }
            }
        },
        _ => None,
    };

    // Macro expansion.
    let expanded: Option<PolicySet> = merged.and_then(|mut m| match crate::macros::expand(&mut m, &dogwood_syntax::ParseOptions::default()) {
        Ok(()) => {
            put("expand", json!({"ok": policy_set(&m)}));
            Some(m)
        }
        Err(e) => {
            put("expand", json!({"error": err("expand", "macro", &e.message, Some(e.span))}));
            None
        }
    });

    // Stable-id assignment (`ParsedPolicySet::with_ids`) on the expanded set:
    // from the `@id` annotations, and from the bundle's explicit ids if any.
    if let Some(e) = &expanded {
        let parsed = Parsed {
            surface: e.clone(),
            service_schema: ServiceSchema::defaults(),
            dw_src: dw_src.clone(),
            ids: None,
            options: dogwood_syntax::ParseOptions::default(),
            #[cfg(feature = "lean-frontend")]
            raw: None,
            #[cfg(feature = "lean-frontend")]
            id_source: None,
        };
        let assigned = |source: crate::IdSource| {
            match crate::policy_set::assign_ids(&parsed, source) {
                Ok(ids) => json!({"ok": ids}),
                Err(e) => json!({"error": api_error("assignIds", &e)}),
            }
        };
        let explicit = match b.ids {
            Some(crate::IdSource::Explicit(ids)) => assigned(crate::IdSource::Explicit(ids.clone())),
            _ => Json::Null,
        };
        put(
            "assignIds",
            json!({"ok": {"annotation": assigned(crate::IdSource::Annotation), "explicit": explicit}}),
        );
    }

    // Event-schema derivation, and what is read off the derived schema.
    let derived: Option<DerivedEventSchema> = match (&event_schema, &fragment) {
        (Ok(es), Ok(_)) => match crate::event_schema::derive::derive(es, action_src) {
            Ok(d) => {
                put("derive", json!({"ok": derived_schema(&d)}));
                Some(d)
            }
            Err(m) => {
                put("derive", json!({"error": err("derive", "eventSchema", &m, None)}));
                None
            }
        },
        _ => None,
    };
    let universal = derived.as_ref().map(crate::event_schema::relativize::universal_pins);
    if let (Some(d), Some(u)) = (&derived, &universal) {
        put(
            "signatures",
            json!({"ok": d.events.iter().map(signature).collect::<Vec<_>>()}),
        );
        put(
            "universalPins",
            json!({"ok": u.iter().map(|p| pin_parts(&p.field_path, &p.context_path, p.root)).collect::<Vec<_>>()}),
        );
        put(
            "decisionKinds",
            json!({"ok": d.decision_kinds().into_iter().collect::<Vec<_>>()}),
        );
    }

    // The array check, cedarify, and pin injection (`lower_entry`).
    let arrays_ok = expanded.as_ref().map(|e| {
        let parsed = Parsed {
            surface: e.clone(),
            service_schema: ServiceSchema::defaults(),
            dw_src: dw_src.clone(),
            ids: None,
            options: dogwood_syntax::ParseOptions::default(),
            #[cfg(feature = "lean-frontend")]
            raw: None,
            #[cfg(feature = "lean-frontend")]
            id_source: None,
        };
        let r = super::reject_temporal_arrays(&parsed);
        put(
            "rejectArrays",
            match &r {
                Ok(()) => json!({"ok": null}),
                Err(e) => json!({"error": api_error("rejectArrays", e)}),
            },
        );
        r.is_ok()
    });
    let cedarified = match (&expanded, arrays_ok, &fragment, decls) {
        (Some(e), Some(true), Ok(frag), Some(decls)) => {
            match cedarify_stage(e, frag, decls, &dw_src) {
                Ok((obs, c)) => {
                    put("cedarify", json!({"ok": obs}));
                    Some(c)
                }
                Err(e) => {
                    put("cedarify", json!({"error": e}));
                    None
                }
            }
        }
        _ => None,
    };
    let pinned: Option<Vec<ContextField>> = match (&cedarified, &derived) {
        (Some(c), Some(d)) => {
            let mut fields = c.context_fields.clone();
            for f in fields.iter_mut() {
                crate::event_schema::pin::inject_pins(&mut f.temporal.condition, d);
            }
            put(
                "injectPins",
                json!({"ok": fields.iter().map(|f| condition(&f.temporal.condition)).collect::<Vec<_>>()}),
            );
            Some(fields)
        }
        _ => None,
    };

    // Rule identity: the canonical form, the leaf encodings and the revisions.
    let revisions: Option<Vec<String>> = match (&cedarified, &pinned) {
        (Some(c), Some(pinned)) => {
            let leaves = identity_leaves(c, pinned);
            let revisions: Vec<String> = c
                .rule_canonical
                .iter()
                .zip(&leaves)
                .map(|(cedar, leaves)| crate::identity::rule_revision(cedar, leaves))
                .collect();
            put(
                "identity",
                json!({"ok": {
                    "ruleCanonical": c.rule_canonical,
                    "leaves": leaves.iter().map(|ls| ls.iter().map(|(n, e)| json!([n, e])).collect::<Vec<_>>()).collect::<Vec<_>>(),
                    "ruleRevisions": revisions,
                }}),
            );
            Some(revisions)
        }
        _ => None,
    };

    // Schema augmentation (`merge`), the provider fields' declarations, and the
    // compiled schema.
    let mut augmented_json: Option<Json> = None;
    if let (Some(c), Some(pinned), Ok(frag), Some(decls)) = (&cedarified, &pinned, &fragment, decls) {
        match crate::cedarify::augment_schema(
            frag.clone(),
            decls,
            &c.referenced_enums,
            pinned,
            &c.provider_fields,
        ) {
            Ok(sf) => match sf.clone().to_json_value().ok().and_then(|v| {
                json_schema::Fragment::<RawName>::from_json_value(v.clone()).ok().map(|f| (v, f))
            }) {
                Some((v, f)) => {
                    put("augment", json!({"ok": schema_fragment(&f)}));
                    // Cedar's own JSON form of the augmented fragment, which the
                    // version hash serializes.
                    put("augmentJson", json!({"ok": v.clone()}));
                    augmented_json = Some(v);
                    let compiled: Result<cedar_policy::Schema, cedar_policy::SchemaError> = sf.try_into();
                    put(
                        "compileSchema",
                        match compiled {
                            Ok(_) => json!({"ok": null}),
                            Err(e) => json!({"error": err("compileSchema", "cedarSchema", &e.to_string(), None)}),
                        },
                    );
                }
                None => put(
                    "augment",
                    json!({"error": err("augment", "export", "the augmented fragment does not round-trip through JSON", None)}),
                ),
            },
            Err(e) => put("augment", json!({"error": err("augment", "cedarify", &e.message, e.span)})),
        }
    }
    let resolved: Option<Vec<Json>> = match (&cedarified, decls) {
        (Some(c), Some(decls)) => {
            let r: Vec<Json> = c
                .provider_fields
                .iter()
                .map(|f| resolve_provider(f, decls, &c.enum_names))
                .collect();
            put("resolveProviders", json!({"ok": r}));
            Some(r)
        }
        _ => None,
    };

    // The executable leaves, and their relativization.
    let executable: Option<Vec<Condition>> = pinned.as_ref().map(|fields| {
        fields
            .iter()
            .map(|f| crate::extension::temporal::timepoints::unorder_timepoints(&f.temporal.condition))
            .collect()
    });
    if let Some(ex) = &executable {
        put("unorder", json!({"ok": ex.iter().map(condition).collect::<Vec<_>>()}));
    }
    let rewritten: Option<Vec<Condition>> = match (&executable, &derived, &universal) {
        (Some(ex), Some(d), Some(u)) => {
            // One node budget for the set's leaves, as `merge` gives an entry.
            let mut budget = dogwood_syntax::NodeBudget::new(dogwood_syntax::DEFAULT_MAX_NODES);
            let r: Result<Vec<Condition>, _> = ex
                .iter()
                .map(|c| {
                    crate::event_schema::relativize::relativize_condition(c, d, u, &mut budget)
                })
                .collect();
            match r {
                Ok(r) => {
                    put("relativize", json!({"ok": r.iter().map(condition).collect::<Vec<_>>()}));
                    Some(r)
                }
                Err(e) => {
                    let m = format!("lowering exceeds the node budget of {}", e.max_nodes);
                    put("relativize", json!({"error": err("relativize", "cedarify", &m, None)}));
                    None
                }
            }
        }
        _ => None,
    };

    // ─── The public pipeline, and its agreement with the stages ──────
    let staged = Staged {
        cedarified: cedarified.as_ref(),
        pinned: pinned.as_deref(),
        executable: executable.as_deref(),
        rewritten: rewritten.as_deref(),
        resolved: resolved.as_deref(),
        augmented: augmented_json.as_ref(),
        revisions: revisions.as_deref(),
        derived: derived.as_ref(),
    };
    let outcome = outcome(b, &providers, &staged);

    json!({"inputs": inputs, "stages": stages, "outcome": outcome})
}

// ─── Stage helpers ──────────────────────────────────────────────────────

/// The observables of cedarify, from one lowering of the expanded set.
struct Cedarified {
    rule_ids: Vec<String>,
    rule_keys: Vec<String>,
    rule_canonical: Vec<String>,
    temporal_rules: Vec<usize>,
    provider_rules: Vec<usize>,
    referenced_enums: BTreeSet<String>,
    enum_names: BTreeMap<String, String>,
    context_fields: Vec<ContextField>,
    provider_fields: Vec<ProviderField>,
    /// Each rule's Cedar text, in rule order.
    policy_texts: Vec<String>,
}

fn cedarify_stage(
    expanded: &PolicySet,
    fragment: &crate::cedarify::Fragment,
    decls: Option<&ProviderDeclarations>,
    dw_src: &Arc<str>,
) -> Result<(Json, Cedarified), Json> {
    let mut c = crate::cedarify::cedarify_with_providers(expanded, fragment, decls, None, None, dw_src)
        .map_err(|e| err("cedarify", "cedarify", &e.message, e.span))?;
    let context_fields = c.hoisted.take_leaves::<ContextField>();
    let provider_fields = c.hoisted.take_leaves::<ProviderField>();
    let policies = cedar_policy::PolicySet::from(c.policy_set);
    let mut policy_json = Vec::new();
    let mut policy_texts = Vec::new();
    for id in &c.rule_ids {
        let p = policies
            .policy(&cedar_policy::PolicyId::new(id))
            .ok_or_else(|| err("cedarify", "export", &format!("rule `{id}` is not in the policy set"), None))?;
        let est = p
            .to_json()
            .map_err(|e| err("cedarify", "export", &format!("rule `{id}`: {e}"), None))?;
        policy_texts.push(p.to_string());
        policy_json.push(json!({"id": id, "est": est, "text": p.to_string()}));
    }
    let obs = json!({
        "policies": policy_json,
        "contextFields": context_fields.iter().map(context_field).collect::<Vec<_>>(),
        "providerFields": provider_fields.iter().map(provider_field).collect::<Vec<_>>(),
        "ruleIds": c.rule_ids,
        "ruleKeys": c.rule_keys,
        "temporalRules": c.temporal_rules,
        "providerRules": c.provider_rules,
        "referencedEnums": c.referenced_enums,
        "enumNames": pairs(&c.enum_names),
    });
    Ok((
        obs,
        Cedarified {
            rule_ids: c.rule_ids,
            rule_keys: c.rule_keys,
            rule_canonical: c.rule_canonical,
            temporal_rules: c.temporal_rules,
            provider_rules: c.provider_rules,
            referenced_enums: c.referenced_enums,
            enum_names: c.enum_names,
            context_fields,
            provider_fields,
            policy_texts,
        },
    ))
}

/// Each rule's hoisted leaves as `(canonical field name, encoding)`, as
/// `lower_entry` computes them for the revisions.
fn identity_leaves(c: &Cedarified, pinned: &[ContextField]) -> Vec<Vec<(String, String)>> {
    let mut leaves: Vec<Vec<(String, String)>> = vec![Vec::new(); c.rule_ids.len()];
    for (leaf, &k) in pinned.iter().zip(&c.temporal_rules) {
        leaves[k].push((
            crate::identity::canonical_field_name(&c.rule_keys[k], &leaf.field_name),
            crate::identity::canonical_context_field(leaf),
        ));
    }
    for (leaf, &k) in c.provider_fields.iter().zip(&c.provider_rules) {
        leaves[k].push((
            crate::identity::canonical_field_name(&c.rule_keys[k], &leaf.field_name),
            crate::identity::canonical_provider_field(leaf),
        ));
    }
    leaves
}

/// A provider field's declaration, its referenced enum declarations, and their
/// exported names, as `merge` resolves them.
fn resolve_provider(
    f: &ProviderField,
    decls: Option<&ProviderDeclarations>,
    enum_names: &BTreeMap<String, String>,
) -> Json {
    let declaration = decls.and_then(|d| d.get(&f.invocation.key()));
    let entity_types: BTreeMap<String, EntityTypeDecl> = match (decls, declaration) {
        (Some(decls), Some(decl)) => decl
            .referenced_entity_types(f.methods.iter().map(|m| m.name.as_str()))
            .into_iter()
            .filter_map(|name| Some((name.clone(), decls.entity_type_decls.get(&name)?.clone())))
            .collect(),
        _ => BTreeMap::new(),
    };
    let names: BTreeMap<String, String> = entity_types
        .keys()
        .filter_map(|name| Some((name.clone(), enum_names.get(name)?.clone())))
        .collect();
    json!({
        "id": f.field_name,
        "declaration": declaration.map(provider_decl),
        "entityTypes": entity_types.iter().map(|(k, v)| json!([k, entity_type_decl(v)])).collect::<Vec<_>>(),
        "entityTypeNames": pairs(&names),
    })
}

/// What the stages computed, for the comparison with the public pipeline.
struct Staged<'a> {
    cedarified: Option<&'a Cedarified>,
    pinned: Option<&'a [ContextField]>,
    executable: Option<&'a [Condition]>,
    rewritten: Option<&'a [Condition]>,
    resolved: Option<&'a [Json]>,
    augmented: Option<&'a Json>,
    revisions: Option<&'a [String]>,
    derived: Option<&'a DerivedEventSchema>,
}

/// The outcome of the public pipeline on the bundle's sources: the error it
/// rejects them with, or the lowered set's identity and the components on
/// which the stages disagree with it.
fn outcome(
    b: &BundleSources<'_>,
    providers: &Option<Result<ProviderDeclarations, Json>>,
    staged: &Staged<'_>,
) -> Json {
    // The export records the Rust frontend's pipeline, whatever `DOGWOOD_FRONTEND` says.
    let mut builder = ServiceSchema::builder().frontend(crate::Frontend::Rust);
    if let Some(src) = b.event_schema {
        builder = builder.event_schema_str(src);
    }
    if let Some(src) = b.macros {
        builder = builder.macros_str(src);
    }
    match providers {
        Some(Ok(d)) => builder = builder.providers(d.clone()),
        Some(Err(e)) => return json!({"rejected": e}),
        None => {}
    }
    let lowered = builder.build().and_then(|service| {
        let mut parsed = super::parse(b.policy, &service, &dogwood_syntax::ParseOptions::default())?;
        if let Some(source) = b.ids {
            let ids = crate::policy_set::assign_ids(&parsed, source.clone())?;
            parsed.set_ids(ids);
        }
        let schema = crate::PolicySchema::from_cedarschema_str(b.action_schema)?;
        let distincter = b
            .distincter
            .map(str::parse::<crate::policy_set::Distincter>)
            .transpose()?;
        super::lower(&parsed, &schema, distincter.as_ref())
    });
    let (lowered, identity) = match lowered {
        Ok(l) => l,
        Err(e) => return json!({"rejected": api_error("pipeline", &e)}),
    };
    let full = lowered_record(&lowered, &identity);
    // The stages lower without stable ids or a distincter; compare them with
    // the pipeline only when it does too.
    if b.ids.is_some() || b.distincter.is_some() {
        let revisions: Vec<&str> = (0..lowered.rule_ids.len()).map(|k| identity.revision(k)).collect();
        return json!({"lowered": {
            "ruleIds": lowered.rule_ids,
            "ruleRevisions": revisions,
            "contentHashes": lowered.temporal.iter().map(|f| f.content_hash()).collect::<Vec<_>>(),
            "versionHash": identity.version_hash(&lowered),
            "mismatches": Vec::<String>::new(),
            "full": full,
        }});
    }

    let mut mismatches: Vec<String> = Vec::new();
    let mut check = |what: &str, ok: Option<bool>| match ok {
        Some(true) => {}
        Some(false) => mismatches.push(what.to_string()),
        None => mismatches.push(format!("{what} (not staged)")),
    };
    check(
        "ruleIds",
        staged.cedarified.map(|c| c.rule_ids == lowered.rule_ids),
    );
    check(
        "policies",
        staged.cedarified.map(|c| {
            c.rule_ids.iter().zip(&c.policy_texts).all(|(id, text)| {
                lowered
                    .policies
                    .policy(&cedar_policy::PolicyId::new(id))
                    .is_some_and(|p| &p.to_string() == text)
            }) && c.rule_ids.len() == lowered.policies.policies().count()
        }),
    );
    check(
        "temporal",
        staged.pinned.map(|fields| {
            fields.len() == lowered.temporal.len()
                && fields.iter().zip(&lowered.temporal).all(|(f, t)| {
                    f.field_name == t.id && f.temporal == t.condition
                })
        }),
    );
    check(
        "temporalExecutable",
        staged.executable.map(|ex| {
            ex.len() == lowered.temporal_executable.len()
                && ex.iter().zip(&lowered.temporal_executable).all(|(c, t)| *c == t.condition.condition)
        }),
    );
    check(
        "temporalRewritten",
        staged.rewritten.map(|rw| {
            rw.len() == lowered.temporal_rewritten.len()
                && rw.iter().zip(&lowered.temporal_rewritten).all(|(c, t)| *c == t.condition.condition)
        }),
    );
    check(
        "providers",
        staged.resolved.map(|r| {
            r.len() == lowered.providers.len()
                && r.iter().zip(&lowered.providers).all(|(j, p)| {
                    j["id"] == json!(p.id)
                        && j["declaration"] == p.declaration.as_ref().map(provider_decl).unwrap_or(Json::Null)
                        && j["entityTypeNames"] == pairs(&p.entity_type_names)
                })
        }),
    );
    check(
        "augmentedSchema",
        staged
            .augmented
            .map(|a| lowered.augmented_schema_fragment.clone().to_json_value().ok().as_ref() == Some(a)),
    );
    check(
        "ruleRevisions",
        staged.revisions.map(|r| {
            r.len() == lowered.rule_ids.len()
                && r.iter().enumerate().all(|(k, rev)| rev.as_str() == identity.revision(k))
        }),
    );
    check(
        "decisionKinds",
        staged.derived.map(|d| {
            d.decision_kinds().into_iter().map(str::to_string).collect::<BTreeSet<_>>()
                == lowered.decision_kinds
        }),
    );
    let content_hashes: Vec<String> = lowered.temporal.iter().map(|f| f.content_hash()).collect();
    let revisions: Vec<&str> = (0..lowered.rule_ids.len()).map(|k| identity.revision(k)).collect();
    json!({"lowered": {
        "ruleIds": lowered.rule_ids,
        "ruleRevisions": revisions,
        "contentHashes": content_hashes,
        "versionHash": identity.version_hash(&lowered),
        "mismatches": mismatches,
        "full": full,
    }})
}

// ─── The lowered set, whole ─────────────────────────────────────────────

/// Every component of a lowered set and of its identity, in the export's
/// encoding: what an independent implementation of the frontend must produce
/// for the set to be rebuilt from it.
pub(crate) fn lowered_record(l: &super::Lowered, identity: &crate::identity::SetIdentity) -> Json {
    let policies: Vec<Json> = l
        .rule_ids
        .iter()
        .map(|id| match l.policies.policy(&cedar_policy::PolicyId::new(id)) {
            Some(p) => json!({"id": id, "est": p.to_json().unwrap_or(Json::Null), "text": p.to_string()}),
            None => json!({"id": id, "est": null, "text": null}),
        })
        .collect();
    let revisions: Vec<&str> = (0..l.rule_ids.len()).map(|k| identity.revision(k)).collect();
    let fields = |fs: &[super::TemporalField]| fs.iter().map(temporal_field).collect::<Vec<_>>();
    json!({
        "policies": policies,
        "ruleIds": l.rule_ids,
        "ruleSpans": l.rule_locs.iter().map(|loc| span(loc_span(loc))).collect::<Vec<_>>(),
        "ruleSources": l.rule_sources,
        "ruleRevisions": revisions,
        "stableIds": identity.stable(),
        "versionHash": identity.version_hash(l),
        "augmentedSchema": l.augmented_schema_fragment.clone().to_json_value().unwrap_or(Json::Null),
        "temporal": fields(&l.temporal),
        "temporalExecutable": fields(&l.temporal_executable),
        "temporalRewritten": fields(&l.temporal_rewritten),
        "partitionKeys": l.partition_keys.iter().map(|k| json!({
            "fieldPath": k.field_path,
            "contextPath": k.context_path,
            "root": match k.root {
                super::EventPinRoot::Scope => "scope",
                super::EventPinRoot::Context => "context",
            },
        })).collect::<Vec<_>>(),
        "providers": l.providers.iter().map(lowered_provider_field).collect::<Vec<_>>(),
        "temporalRules": l.temporal_rules,
        "providerRules": l.provider_rules,
        "eventSchema": derived_schema(&l.event_schema),
        "decisionKinds": l.decision_kinds,
        "enumNames": pairs(&l.enum_names),
        "contextReads": l.context_reads.iter().map(|r| json!({
            "rule": r.rule, "span": span(r.span), "message": r.message, "whole": r.whole,
        })).collect::<Vec<_>>(),
        "contentHashes": l.temporal.iter().map(|f| f.content_hash()).collect::<Vec<_>>(),
    })
}

fn action_ref_pair(r: &super::ActionRef) -> Json {
    json!([r.namespace.clone().unwrap_or_default(), r.id])
}

fn action_scope(a: &super::ActionScope) -> Json {
    match a {
        super::ActionScope::Concrete(r) => {
            ctor("concrete", json!({"ns": r.namespace.clone().unwrap_or_default(), "id": r.id}))
        }
        super::ActionScope::List(v) => {
            ctor("list", json!({"actions": v.iter().map(action_ref_pair).collect::<Vec<_>>()}))
        }
        super::ActionScope::Unconstrained => json!("unconstrained"),
    }
}

fn temporal_field(f: &super::TemporalField) -> Json {
    json!({
        "id": f.id, "action": action_scope(&f.action),
        "targetActions": f.target_actions.iter().map(action_ref_pair).collect::<Vec<_>>(),
        "principal": scope_constraint(&f.principal), "resource": scope_constraint(&f.resource),
        "condition": temporal(&f.condition),
    })
}

fn lowered_provider_field(f: &super::ProviderField) -> Json {
    json!({
        "id": f.id, "action": action_scope(&f.action),
        "targetActions": f.target_actions.iter().map(action_ref_pair).collect::<Vec<_>>(),
        "principal": scope_constraint(&f.principal), "resource": scope_constraint(&f.resource),
        "invocation": invocation(&f.invocation),
        "methods": f.methods.iter().map(method_call).collect::<Vec<_>>(),
        "bodyBase": f.body_base,
        "declaration": f.declaration.as_ref().map(provider_decl),
        "entityTypes": f.entity_types.iter().map(|(k, v)| json!([k, entity_type_decl(v)])).collect::<Vec<_>>(),
        "entityTypeNames": pairs(&f.entity_type_names),
    })
}

// ─── Several policy sets, lowered together ──────────────────────────────

/// One entry of a [`ManySources`]: a policy text, its distincter, and the
/// stable-id source it is given before lowering (`None` for positional ids).
#[derive(Debug, Clone, Copy)]
pub struct ManyEntry<'a> {
    pub policy: &'a str,
    pub distincter: &'a str,
    pub ids: Option<&'a crate::IdSource>,
}

/// The sources of several policy sets lowered together (`lower_many`): one
/// service schema and one action schema, shared, and the entries.
#[derive(Debug, Clone, Copy)]
pub struct ManySources<'a> {
    pub entries: &'a [ManyEntry<'a>],
    /// The event-schema DSL; `None` for the default schema.
    pub event_schema: Option<&'a str>,
    /// The provider declarations; `None` when there are none.
    pub providers: Option<&'a str>,
    /// The macro library; `None` for the default library.
    pub macros: Option<&'a str>,
    pub action_schema: &'a str,
}

/// Export several policy sets lowered together: the parsers' outputs (the
/// shared inputs, and each entry's policy set, distincter and id source), and
/// what the public pipeline does with them (each entry parsed, given its ids,
/// then `lower_many`): the rejection, with the entry it belongs to, or the
/// whole lowered set ([`lowered_record`]).
pub fn export_many(m: &ManySources<'_>) -> Json {
    let shared = SharedParses::parse(m.event_schema, m.providers, m.macros, m.action_schema);
    let inputs = many_inputs(
        &shared.inputs(),
        m.entries.iter().map(|e| {
            let policy = parse_policy(e.policy);
            entry_inputs(policy.as_ref(), Some(e.distincter), e.ids)
        }),
    );
    let providers = shared.providers;

    let outcome = match many_outcome(m, &providers) {
        Ok((l, identity)) => json!({"lowered": {"full": lowered_record(&l, &identity)}}),
        Err((entry, e)) => {
            let mut j = api_error("pipeline", &e);
            j["entry"] = json!(entry);
            json!({"rejected": j})
        }
    };
    json!({"inputs": inputs, "outcome": outcome})
}

pub(crate) fn id_source(s: &crate::IdSource) -> Json {
    match s {
        crate::IdSource::Annotation => json!("annotation"),
        crate::IdSource::Explicit(ids) => json!({"explicit": ids}),
        _ => json!("positional"),
    }
}

/// A lowered set and its identity, as `LoweredPolicySet` holds them.
type LoweredParts = (Arc<super::Lowered>, Arc<crate::identity::SetIdentity>);

/// The public pipeline on several policy sets, and on a rejection the entry it
/// belongs to (`None` for the shared inputs and the merge).
fn many_outcome(
    m: &ManySources<'_>,
    providers: &Option<Result<ProviderDeclarations, Json>>,
) -> Result<LoweredParts, (Option<usize>, Error)> {
    let shared = |e: Error| (None, e);
    // The export records the Rust frontend's pipeline, whatever `DOGWOOD_FRONTEND` says.
    let mut builder = ServiceSchema::builder().frontend(crate::Frontend::Rust);
    if let Some(src) = m.event_schema {
        builder = builder.event_schema_str(src);
    }
    if let Some(src) = m.macros {
        builder = builder.macros_str(src);
    }
    match providers {
        Some(Ok(d)) => builder = builder.providers(d.clone()),
        Some(Err(e)) => {
            let message = e["message"].as_str().unwrap_or_default().to_string();
            return Err((None, Error::Providers(message)));
        }
        None => {}
    }
    let service = builder.build().map_err(shared)?;
    let mut parsed = Vec::with_capacity(m.entries.len());
    for (i, e) in m.entries.iter().enumerate() {
        let mut p = crate::ParsedPolicySet::parse(e.policy, &service).map_err(|err| (Some(i), err))?;
        if let Some(source) = e.ids {
            p = p.with_ids(source.clone()).map_err(|err| (Some(i), err))?;
        }
        parsed.push(p);
    }
    let schema = crate::PolicySchema::from_cedarschema_str(m.action_schema).map_err(shared)?;
    let mut distincters = Vec::with_capacity(m.entries.len());
    for (i, e) in m.entries.iter().enumerate() {
        distincters.push(e.distincter.parse::<crate::policy_set::Distincter>().map_err(|err| (Some(i), err))?);
    }
    let pairs: Vec<(&crate::ParsedPolicySet, crate::policy_set::Distincter)> =
        parsed.iter().zip(distincters.iter().cloned()).collect();
    match crate::policy_set::lower_many(&pairs, &schema) {
        Ok(set) => Ok(set.into_parts()),
        Err(e) => {
            // The entry an error belongs to: the first whose own lowering fails
            // (as `lower_many` lowers them in order), unless the error is of
            // the shared inputs or of the merge.
            let entry = match &e {
                Error::DuplicateDistincter(_) | Error::NoPolicies | Error::MismatchedServiceSchema(_) => None,
                _ => super::Base::derive(&service, &schema).ok().and_then(|base| {
                    pairs.iter().position(|(p, d)| super::lower_entry(&p.parsed, &base, Some(d)).is_err())
                }),
            };
            Err((entry, e))
        }
    }
}

// ─── Errors and results ─────────────────────────────────────────────────

fn strip_bom(s: &str) -> &str {
    s.strip_prefix('\u{FEFF}').unwrap_or(s)
}

pub(crate) fn span(s: Span) -> Json {
    json!({"start": s.start, "end": s.end})
}

fn opt_span(s: Option<Span>) -> Json {
    s.map(span).unwrap_or(Json::Null)
}

fn err(stage: &str, category: &str, message: &str, at: Option<Span>) -> Json {
    json!({"stage": stage, "category": category, "message": message, "span": opt_span(at)})
}

fn parse_error(stage: &str, errs: &[crate::error::RawParseError]) -> Json {
    let message = errs.iter().map(|e| e.message.as_str()).collect::<Vec<_>>().join("\n");
    err(stage, "parse", &message, errs.first().map(|e| e.span))
}

fn loc_span(loc: &crate::error::SourceLoc) -> Span {
    let s = loc.span();
    Span::new(s.offset(), s.offset() + s.len())
}

/// A lowering error, by its kind, with its raw message (the variant's payload,
/// before `Error`'s `Display` adds a prefix), its `Display` (`display`), its
/// location, and, for a stable-id error, its kind, policy and id.
fn api_error(stage: &str, e: &Error) -> Json {
    let (category, at) = match e {
        Error::Parse(_) => ("parse", None),
        Error::Macro(m) => ("macro", Some(loc_span(m.location()))),
        Error::Cedarify(c) => ("cedarify", c.location().map(loc_span)),
        Error::PolicySet(_) => ("policySet", None),
        Error::CedarSchema(_) => ("cedarSchema", None),
        Error::EventSchema(_) => ("eventSchema", None),
        Error::Providers(_) => ("providers", None),
        Error::PolicyId(p) => ("policyId", p.location().map(loc_span)),
        Error::InvalidDistincter(_) => ("invalidDistincter", None),
        Error::DuplicateDistincter(_) => ("duplicateDistincter", None),
        Error::NoPolicies => ("noPolicies", None),
        _ => ("other", None),
    };
    let raw = match e {
        Error::EventSchema(m)
        | Error::Providers(m)
        | Error::InvalidDistincter(m)
        | Error::DuplicateDistincter(m) => m.clone(),
        Error::NoPolicies => String::new(),
        _ => e.to_string(),
    };
    let mut j = err(stage, category, &raw, at);
    j["display"] = json!(e.to_string());
    if let Error::PolicyId(p) = e {
        use crate::error::PolicyIdErrorKind as K;
        let kind = match p.kind() {
            K::Missing => "missing",
            K::Duplicate => "duplicate",
            K::Invalid => "invalid",
            K::CountMismatch => "countMismatch",
            K::RepeatedAnnotation => "repeatedAnnotation",
        };
        j["policyId"] = json!({"kind": kind, "policy": p.policy_index(), "id": p.id()});
    }
    j
}

/// `{"ok": f(v)}` or `{"error": e}`.
fn result<T: ?Sized>(r: Result<&T, &Json>, f: impl FnOnce(&T) -> Json) -> Json {
    match r {
        Ok(v) => json!({"ok": f(v)}),
        Err(e) => json!({"error": e}),
    }
}

fn unit_result(r: &Result<(), String>, stage: &str, category: &str) -> Json {
    match r {
        Ok(()) => json!({"ok": null}),
        Err(m) => json!({"error": err(stage, category, m, None)}),
    }
}

pub(crate) fn pairs(m: &BTreeMap<String, String>) -> Json {
    Json::Array(m.iter().map(|(k, v)| json!([k, v])).collect())
}

fn ctor(name: &str, args: Json) -> Json {
    let mut m = Map::new();
    m.insert(name.to_string(), args);
    Json::Object(m)
}

// ─── Cedar names ────────────────────────────────────────────────────────

/// A Cedar name `A::B::C` as `{"id": "C", "path": ["A", "B"]}`.
fn name_parts(text: &str) -> Json {
    let mut segs: Vec<&str> = text.split("::").collect();
    let id = segs.pop().unwrap_or_default();
    json!({"id": id, "path": segs})
}

pub(crate) fn entity_type(t: &cedar_ast::EntityType) -> Json {
    name_parts(&t.to_string())
}

pub(crate) fn entity_uid(u: &cedar_ast::EntityUID) -> Json {
    json!({"ty": entity_type(u.entity_type()), "eid": u.eid().as_ref()})
}

// ─── The surface policy set ─────────────────────────────────────────────

pub(crate) fn policy_set(ps: &PolicySet) -> Json {
    json!({"policies": ps.policies.iter().map(policy).collect::<Vec<_>>(), "defs": defs(&ps.defs)})
}

pub(crate) fn defs(ds: &[MacroDef]) -> Json {
    Json::Array(ds.iter().map(macro_def).collect())
}

pub(crate) fn macro_def(d: &MacroDef) -> Json {
    let body = match &d.body {
        MacroBody::Cedar(e) => ctor("cedar", json!({"e": expr(e)})),
        MacroBody::TemporalCondition(c) => ctor("condition", json!({"c": condition(c)})),
        MacroBody::TemporalValue(t) => ctor("value", json!({"t": term(t)})),
    };
    json!({
        "span": span(d.span), "name": d.name,
        "params": d.params.iter().map(|p| json!({"span": span(p.span), "name": p.name})).collect::<Vec<_>>(),
        "body": body,
    })
}

pub(crate) fn policy(p: &Policy) -> Json {
    json!({
        "span": span(p.span),
        "annotations": p.annotations.iter().map(|a| json!({"key": a.key, "value": a.value})).collect::<Vec<_>>(),
        "effect": match p.effect { Effect::Permit => "permit", Effect::Forbid => "forbid" },
        "scope": {
            "span": span(p.scope.span),
            "principal": scope_template(p.scope.principal.as_inner(), "?principal"),
            "action": action_constraint(&p.scope.action),
            "resource": scope_template(p.scope.resource.as_inner(), "?resource"),
        },
        "conditions": p.conditions.iter().map(|c| json!({
            "span": span(c.span),
            "keyword": match c.keyword { CondKeyword::When => "when", CondKeyword::Unless => "unless" },
            "body": expr(&c.body),
        })).collect::<Vec<_>>(),
    })
}

/// A principal or resource constraint, as cedar-lean's `ScopeTemplate`; a slot
/// is named `slot` (`?principal` or `?resource`).
fn scope_template(c: &cedar_ast::PrincipalOrResourceConstraint, slot: &str) -> Json {
    use cedar_ast::PrincipalOrResourceConstraint as P;
    let reference = |r: &cedar_ast::EntityReference| match r {
        cedar_ast::EntityReference::EUID(u) => ctor("entityUID", json!({"entity": entity_uid(u)})),
        cedar_ast::EntityReference::Slot(_) => ctor("slot", json!({"id": slot})),
    };
    match c {
        P::Any => json!("any"),
        P::Eq(r) => ctor("eq", json!({"entityOrSlot": reference(r)})),
        P::In(r) => ctor("mem", json!({"entityOrSlot": reference(r)})),
        P::Is(t) => ctor("is", json!({"ety": entity_type(t)})),
        P::IsIn(t, r) => ctor("isMem", json!({"ety": entity_type(t), "entityOrSlot": reference(r)})),
    }
}

fn action_constraint(a: &cedar_ast::ActionConstraint) -> Json {
    match a {
        cedar_ast::ActionConstraint::Eq(u) => ctor("eq", json!({"entity": entity_uid(u)})),
        cedar_ast::ActionConstraint::In(us) => {
            ctor("in", json!({"entities": us.iter().map(|u| entity_uid(u)).collect::<Vec<_>>()}))
        }
        #[allow(unreachable_patterns)]
        _ => json!("any"),
    }
}

fn literal(l: &cedar_ast::Literal) -> Json {
    match l {
        cedar_ast::Literal::Bool(b) => json!(b),
        cedar_ast::Literal::Long(i) => json!(i),
        cedar_ast::Literal::String(s) => json!(s.as_str()),
        cedar_ast::Literal::EntityUID(u) => json!({"entity": entity_uid(u)}),
    }
}

fn var(v: &cedar_ast::Var) -> &'static str {
    match v {
        cedar_ast::Var::Principal => "principal",
        cedar_ast::Var::Action => "action",
        cedar_ast::Var::Resource => "resource",
        cedar_ast::Var::Context => "context",
    }
}

fn unop(op: UnOp) -> &'static str {
    match op {
        UnOp::Not => "not",
        UnOp::Neg => "neg",
        UnOp::IsEmpty => "isEmpty",
        UnOp::Decimal => "decimal",
        UnOp::Datetime => "datetime",
        UnOp::Duration => "duration",
        UnOp::Ip => "ip",
        UnOp::IsIpv4 => "isIpv4",
        UnOp::IsIpv6 => "isIpv6",
        UnOp::IsLoopback => "isLoopback",
        UnOp::IsMulticast => "isMulticast",
        UnOp::ToDate => "toDate",
        UnOp::ToTime => "toTime",
        UnOp::ToMilliseconds => "toMilliseconds",
        UnOp::ToSeconds => "toSeconds",
        UnOp::ToMinutes => "toMinutes",
        UnOp::ToHours => "toHours",
        UnOp::ToDays => "toDays",
    }
}

fn binop(op: BinOp) -> &'static str {
    match op {
        BinOp::Eq => "eq",
        BinOp::NotEq => "notEq",
        BinOp::Less => "less",
        BinOp::LessEq => "lessEq",
        BinOp::Greater => "greater",
        BinOp::GreaterEq => "greaterEq",
        BinOp::And => "and",
        BinOp::Or => "or",
        BinOp::Add => "add",
        BinOp::Sub => "sub",
        BinOp::Mul => "mul",
        BinOp::In => "in",
        BinOp::Contains => "contains",
        BinOp::ContainsAll => "containsAll",
        BinOp::ContainsAny => "containsAny",
        BinOp::GetTag => "getTag",
        BinOp::HasTag => "hasTag",
        BinOp::IsInRange => "isInRange",
        BinOp::Offset => "offset",
        BinOp::DurationSince => "durationSince",
        BinOp::DecimalLessThan => "decimalLessThan",
        BinOp::DecimalLessEq => "decimalLessEq",
        BinOp::DecimalGreater => "decimalGreater",
        BinOp::DecimalGreaterEq => "decimalGreaterEq",
    }
}

fn expr(e: &Expr) -> Json {
    let kind = match &e.kind {
        ExprKind::Lit(l) => ctor("lit", json!({"l": literal(l)})),
        ExprKind::Var(v) => ctor("var", json!({"v": var(v)})),
        ExprKind::Slot(s) => ctor("slot", json!({"id": if s.is_principal() { "?principal" } else { "?resource" }})),
        ExprKind::Extension(Extension::Temporal(t)) => ctor("extension", json!({"t": temporal(t)})),
        ExprKind::UnaryApp { op, expr: x } => ctor("unaryApp", json!({"op": unop(*op), "expr": expr(x)})),
        ExprKind::BinaryApp { op, left, right } => {
            ctor("binaryApp", json!({"op": binop(*op), "left": expr(left), "right": expr(right)}))
        }
        ExprKind::GetAttr { expr: x, attr } => ctor("getAttr", json!({"expr": expr(x), "attr": attr})),
        ExprKind::HasAttr { expr: x, attrs } => ctor("hasAttr", json!({"expr": expr(x), "attrs": attrs})),
        ExprKind::Like { expr: x, pattern } => {
            let pattern: Vec<Json> = pattern
                .iter()
                .map(|p| match p {
                    cedar_ast::PatternElem::Char(c) => ctor("justChar", json!({"c": c.to_string()})),
                    cedar_ast::PatternElem::Wildcard => json!("star"),
                })
                .collect();
            ctor("like", json!({"expr": expr(x), "pattern": pattern}))
        }
        ExprKind::Is { expr: x, entity_type: t, in_expr } => ctor(
            "is",
            json!({"expr": expr(x), "entityType": entity_type(t), "inExpr": in_expr.as_deref().map(expr)}),
        ),
        ExprKind::IfThenElse { cond, then_expr, else_expr } => ctor(
            "ite",
            json!({"cond": expr(cond), "thenExpr": expr(then_expr), "elseExpr": expr(else_expr)}),
        ),
        ExprKind::Set(xs) => ctor("set", json!({"items": xs.iter().map(expr).collect::<Vec<_>>()})),
        ExprKind::Record(m) => ctor(
            "record",
            json!({"entries": m.iter().map(|(k, v)| json!([k, expr(v)])).collect::<Vec<_>>()}),
        ),
        ExprKind::Call { name, args } => {
            ctor("call", json!({"name": name, "args": args.iter().map(expr).collect::<Vec<_>>()}))
        }
        ExprKind::MethodCall { receiver, method, args } => ctor(
            "methodCall",
            json!({"receiver": expr(receiver), "method": method, "args": args.iter().map(expr).collect::<Vec<_>>()}),
        ),
        ExprKind::ParamRef { name } => ctor("paramRef", json!({"name": name})),
    };
    json!({"kind": kind, "span": span(e.span)})
}

// ─── The temporal AST ───────────────────────────────────────────────────

pub(crate) fn temporal(t: &Temporal) -> Json {
    json!({"condition": condition(&t.condition), "span": span(t.span)})
}

pub(crate) fn interval(i: &Interval) -> Json {
    let unit = match i.unit {
        TimeUnit::Seconds => "seconds",
        TimeUnit::Minutes => "minutes",
        TimeUnit::Hours => "hours",
        TimeUnit::Days => "days",
    };
    json!({"amount": i.amount, "unit": unit})
}

fn within(w: &WithinSpec) -> Json {
    match w {
        WithinSpec::Concrete(i) => ctor("concrete", json!({"i": interval(i)})),
        WithinSpec::ParamRef(p) => ctor("paramRef", json!({"name": p})),
    }
}

fn binder_slot(s: &BinderSlot) -> Json {
    match s {
        BinderSlot::Name(n) => ctor("name", json!({"n": n})),
        BinderSlot::ParamRef(p) => ctor("paramRef", json!({"name": p})),
        BinderSlot::BinderRef(b) => ctor("binderRef", json!({"name": b})),
    }
}

fn typed_binder(b: &TypedBinder) -> Json {
    let ty = match &b.ty {
        Type::Timepoint => json!("timepoint"),
        Type::Named(path) => ctor("named", json!({"path": path})),
    };
    json!({"slot": binder_slot(&b.slot), "ty": ty})
}

fn cmp_op(op: CmpOp) -> &'static str {
    match op {
        CmpOp::Eq => "eq",
        CmpOp::NotEq => "ne",
        CmpOp::Lt => "lt",
        CmpOp::Le => "le",
        CmpOp::Gt => "gt",
        CmpOp::Ge => "ge",
    }
}

fn arith_op(op: ArithOp) -> &'static str {
    match op {
        ArithOp::Add => "add",
        ArithOp::Sub => "sub",
        ArithOp::Mul => "mul",
    }
}

fn named_arg(a: &NamedArg) -> Json {
    json!({"name": a.name, "value": term(&a.value)})
}

fn predicate(p: &Predicate) -> Json {
    json!({
        "span": span(p.span), "namespace": p.namespace, "action": p.action, "kind": p.kind,
        "args": p.args.iter().map(named_arg).collect::<Vec<_>>(),
    })
}

fn call(c: &Call) -> Json {
    let args: Vec<Json> = c
        .args
        .iter()
        .map(|a| match a {
            CallArg::Condition(x) => ctor("condition", json!({"c": condition(x)})),
            CallArg::Within(i) => ctor("within", json!({"i": interval(i)})),
            CallArg::Term(t) => ctor("term", json!({"t": term(t)})),
        })
        .collect();
    json!({"span": span(c.span), "name": c.name, "args": args})
}

/// A temporal condition, in the encoding the module documentation describes: one leaf as a
/// temporal engine receives it (the `condition` of a
/// [`TemporalField`](crate::TemporalField)'s temporal block), in the form the Lean frontend's
/// decoder (`Dogwood.Frontend.Surface.Temporal.conditionOfJson`) reads.
#[doc(hidden)]
pub fn condition(c: &Condition) -> Json {
    let kind = match &c.kind {
        ConditionKind::And { left, right } => ctor("and", json!({"left": condition(left), "right": condition(right)})),
        ConditionKind::Or { left, right } => ctor("or", json!({"left": condition(left), "right": condition(right)})),
        ConditionKind::Not { inner } => ctor("not", json!({"inner": condition(inner)})),
        ConditionKind::Formerly { within: w, body } => {
            ctor("formerly", json!({"within": within(w), "body": condition(body)}))
        }
        ConditionKind::Previous { within: w, body } => {
            ctor("previous", json!({"within": within(w), "body": condition(body)}))
        }
        ConditionKind::Since { left, within: w, right } => ctor(
            "since",
            json!({"left": condition(left), "within": within(w), "right": condition(right)}),
        ),
        ConditionKind::Predicate(p) => ctor("predicate", json!({"p": predicate(p)})),
        ConditionKind::Comparison { op, left, right } => {
            ctor("comparison", json!({"op": cmp_op(*op), "left": term(left), "right": term(right)}))
        }
        ConditionKind::Exists { var, body } => {
            ctor("exists", json!({"var": typed_binder(var), "body": condition(body)}))
        }
        ConditionKind::Tp { var } => ctor("tp", json!({"var": binder_slot(var)})),
        ConditionKind::Call(c) => ctor("call", json!({"c": call(c)})),
        ConditionKind::SigilRef { sigil, name } => ctor(
            "sigilRef",
            json!({"sigil": match sigil { Sigil::Param => "param", Sigil::Binder => "binder" }, "name": name}),
        ),
        ConditionKind::Refine { base, fields, span: s } => ctor(
            "refine",
            json!({"base": condition(base), "fields": fields.iter().map(named_arg).collect::<Vec<_>>(), "span": span(*s)}),
        ),
    };
    json!({"span": span(c.span), "kind": kind})
}

pub(crate) fn term(t: &Term) -> Json {
    match t {
        Term::Entity { ty, id } => ctor("entity", json!({"ty": ty, "id": id})),
        Term::Integer(i) => ctor("integer", json!({"i": i})),
        Term::Decimal(s) => ctor("decimal", json!({"text": s})),
        Term::String(s) => ctor("string", json!({"s": s})),
        Term::Bool(b) => ctor("bool", json!({"b": b})),
        Term::ContextField(p) => ctor("contextField", json!({"path": p})),
        Term::ScopeField(p) => ctor("scopeField", json!({"path": p})),
        Term::Var(x) => ctor("var", json!({"x": x})),
        Term::Wildcard => json!("wildcard"),
        Term::Array(xs) => ctor("array", json!({"items": xs.iter().map(term).collect::<Vec<_>>()})),
        Term::Agg(a) => ctor("agg", json!({"a": agg(a)})),
        Term::Arith { op, left, right } => {
            ctor("arith", json!({"op": arith_op(*op), "left": term(left), "right": term(right)}))
        }
        Term::ParamRef(p) => ctor("paramRef", json!({"name": p})),
        Term::BinderRef(b) => ctor("binderRef", json!({"name": b})),
    }
}

fn agg(a: &AggExpr) -> Json {
    let binders = |vs: &[TypedBinder]| vs.iter().map(typed_binder).collect::<Vec<_>>();
    let kind = match &a.kind {
        AggExprKind::Sum { bound_var, for_vars, body } => ctor(
            "sum",
            json!({"boundVar": binder_slot(bound_var), "forVars": binders(for_vars), "body": condition(body)}),
        ),
        AggExprKind::Count { for_vars, body } => {
            ctor("count", json!({"forVars": binders(for_vars), "body": condition(body)}))
        }
        AggExprKind::Call(c) => ctor("call", json!({"c": call(c)})),
    };
    json!({"span": span(a.span), "kind": kind})
}

// ─── One event, as a timepoint of the specification ─────────────────────

/// One event as a timepoint of the Lean specification (`Dogwood.Spec.TimePoint`), in the
/// encoding `Dogwood.Conformance.Json` decodes: `{"ts": T, "event": {"action", "kind",
/// "principal", "resource", "logged", "context", "entities"}}`, as the conformance bridge writes
/// a trace's events.
///
/// * The values are canonical in the specification's sense: a `null` is absent (a record member
///   or a set element whose value is `null` is left out), an array is a set (the decoder sorts
///   and deduplicates it), a decimal is `{"decimal": text}` (the decoder reads Cedar's decimal), and
///   an `ipaddr`, `datetime` or `duration` value is `{"extension": {"fn": F, "arg": A}}`.
/// * `principal` and `resource` are the scope's entity uids, `null` when absent.
/// * `entities` holds each supplied entity, with its attributes and its ancestors, closed
///   transitively as Cedar's are. An entity whose key is not a uid Cedar reads is left out: no
///   term of a condition can name it.
#[doc(hidden)]
pub fn event(e: &crate::Event) -> Json {
    let data = e.data();
    let action = uid_json(&e.namespace().join("::"), e.action());
    let keyed: Vec<(&String, (String, String))> = data
        .entities
        .keys()
        .filter_map(|u| split_uid(u).map(|key| (u, key)))
        .collect();
    let parents: BTreeMap<&(String, String), Vec<(String, String)>> = keyed
        .iter()
        .map(|(u, key)| {
            let ps = data.entities[*u]
                .parents
                .iter()
                .filter_map(|p| match p {
                    crate::Value::Entity { ty, id } => Some((ty.clone(), id.clone())),
                    _ => None,
                })
                .collect();
            (key, ps)
        })
        .collect();
    let entities: Vec<Json> = keyed
        .iter()
        .map(|(u, key)| {
            let mut seen = BTreeSet::new();
            let mut todo: Vec<(String, String)> = parents.get(key).cloned().unwrap_or_default();
            while let Some(parent) = todo.pop() {
                if seen.insert(parent.clone()) {
                    todo.extend(parents.get(&parent).cloned().unwrap_or_default());
                }
            }
            let ancestors: Vec<Json> = seen.iter().map(|(t, i)| uid_json(t, i)).collect();
            json!([
                uid_json(&key.0, &key.1),
                {"attrs": record_json(data.entities[*u].attrs.iter()), "ancestors": ancestors, "tags": []}
            ])
        })
        .collect();
    let scope = |v: &Option<crate::Value>| match v {
        Some(crate::Value::Entity { ty, id }) => uid_json(ty, id),
        _ => Json::Null,
    };
    json!({"ts": e.timestamp(), "event": {
        "action": action, "kind": e.kind(),
        "principal": scope(&e.scope().principal), "resource": scope(&e.scope().resource),
        "logged": record_json(data.logged.iter()),
        "context": record_json(data.request_context.iter()),
        "entities": entities,
    }})
}

/// One value in the encoding of [`event`]; `None` for `null`, which is absent.
#[doc(hidden)]
pub fn value(v: &crate::Value) -> Option<Json> {
    use crate::Value;
    Some(match v {
        Value::Null => return None,
        Value::Bool(b) => json!(b),
        Value::Int(i) => json!(i),
        Value::Decimal(s) => json!({"decimal": s}),
        Value::String(s) => json!(s),
        Value::Entity { ty, id } => json!({"entity": uid_json(ty, id)}),
        Value::Array(xs) => json!({"set": xs.iter().filter_map(value).collect::<Vec<_>>()}),
        Value::Object(m) => match extension_parts(m) {
            Some((f, arg)) => json!({"extension": {"fn": f, "arg": arg}}),
            None => json!({"record": record_json(m.iter())}),
        },
    })
}

/// A record as `[key, value]` pairs, its `null` members left out.
fn record_json<'a>(fields: impl Iterator<Item = (&'a String, &'a crate::Value)>) -> Json {
    Json::Array(fields.filter_map(|(k, v)| value(v).map(|v| json!([k, v]))).collect())
}

/// An entity uid of type `ty` (`A::B::C`) and id `id`, as the specification's `EntityUID`.
fn uid_json(ty: &str, id: &str) -> Json {
    let mut path: Vec<&str> = ty.split("::").collect();
    let last = path.pop().unwrap_or_default();
    json!({"ty": {"id": last, "path": path}, "eid": id})
}

/// The constructor and argument of Cedar's JSON escape for an extension value,
/// `{"__extn": {"fn": F, "arg": A}}` (`Value::extension`), its `null` members absent.
fn extension_parts(m: &BTreeMap<String, crate::Value>) -> Option<(&str, &str)> {
    use crate::Value;
    let present = |m: &BTreeMap<String, Value>| m.values().filter(|v| !v.is_null()).count();
    if present(m) != 1 {
        return None;
    }
    let Value::Object(inner) = m.get("__extn")? else {
        return None;
    };
    match (present(inner), inner.get("fn")?, inner.get("arg")?) {
        (2, Value::String(f), Value::String(arg)) => Some((f, arg)),
        _ => None,
    }
}

/// An entity store key, `Ns::Type::"id"`, as its type and its id; `None` when Cedar does not read
/// it as a uid. The key is Cedar's rendering of the uid, which Cedar's parser inverts.
fn split_uid(u: &str) -> Option<(String, String)> {
    let uid: cedar_policy::EntityUid = u.parse().ok()?;
    Some((uid.type_name().to_string(), uid.id().unescaped().to_string()))
}

// ─── The event-schema DSL and the derived schema ────────────────────────

pub(crate) fn dsl_schema(s: &dsl::EventSchema) -> Json {
    json!({
        "maxWindow": s.max_window.as_ref().map(interval),
        "maxHorizon": s.max_horizon.as_ref().map(interval),
        "decls": s.decls.iter().map(|d| json!({
            "span": span(d.span), "decision": d.decision, "binder": d.binder, "kind": d.kind,
            "fields": d.fields.iter().map(field_spec).collect::<Vec<_>>(),
        })).collect::<Vec<_>>(),
    })
}

fn selector(s: dsl::Selector) -> &'static str {
    s.as_str()
}

fn pin_root(r: dsl::PinRoot) -> &'static str {
    match r {
        dsl::PinRoot::Scope => "scope",
        dsl::PinRoot::Context => "context",
    }
}

fn field_spec(f: &dsl::FieldSpec) -> Json {
    match f {
        dsl::FieldSpec::Spread { selector: s, span: sp } => {
            ctor("spread", json!({"selector": selector(*s), "span": span(*sp)}))
        }
        dsl::FieldSpec::Named { name, ty, pin, span: sp } => {
            let ty = match ty {
                dsl::TypeExpr::Selector(s) => ctor("selector", json!({"s": selector(*s)})),
                dsl::TypeExpr::Concrete(path) => ctor("concrete", json!({"path": path})),
                dsl::TypeExpr::Record(fields) => {
                    ctor("record", json!({"fields": fields.iter().map(field_spec).collect::<Vec<_>>()}))
                }
            };
            let pin = pin.as_ref().map(|p| {
                json!({"contextPath": p.context_path, "root": pin_root(p.root), "span": span(p.span)})
            });
            ctor("named", json!({"name": name, "ty": ty, "pin": pin, "span": span(*sp)}))
        }
    }
}

pub(crate) fn pin_parts(field_path: &[String], context_path: &[String], root: dsl::PinRoot) -> Json {
    json!({"fieldPath": field_path, "contextPath": context_path, "root": pin_root(root)})
}

pub(crate) fn field_type(t: &FieldType) -> Json {
    match t {
        FieldType::Cedar(s) => ctor("cedar", json!({"text": s})),
        FieldType::EntityTypes(v) => ctor("entityTypes", json!({"names": v})),
    }
}

pub(crate) fn field_nodes(m: &BTreeMap<String, DerivedFieldNode>) -> Json {
    Json::Array(
        m.iter()
            .map(|(k, n)| {
                let node = match n {
                    DerivedFieldNode::Leaf(t) => ctor("leaf", json!({"ty": field_type(t)})),
                    DerivedFieldNode::Group(g) => ctor("group", json!({"members": field_nodes(g)})),
                };
                json!([k, node])
            })
            .collect(),
    )
}

pub(crate) fn derived_event(e: &DerivedEvent) -> Json {
    json!({
        "namespace": e.namespace, "action": e.action, "kind": e.kind, "decision": e.decision,
        "fields": field_nodes(&e.fields),
        "pins": e.pins.iter().map(|p| pin_parts(&p.field_path, &p.context_path, p.root)).collect::<Vec<_>>(),
    })
}

pub(crate) fn derived_schema(d: &DerivedEventSchema) -> Json {
    json!({
        "events": d.events.iter().map(derived_event).collect::<Vec<_>>(),
        "maxWindow": interval(&d.max_window),
        "maxHorizon": d.max_horizon.as_ref().map(interval),
    })
}

/// A derived event as the public event signature lists it: its leaf fields,
/// sorted by their path's text.
fn signature(e: &DerivedEvent) -> Json {
    json!({
        "namespace": e.namespace, "action": e.action, "kind": e.kind, "decision": e.decision,
        "fields": e.leaf_fields().iter().map(|(p, t)| json!([p, field_type(t)])).collect::<Vec<_>>(),
        "pins": e.pins.iter().map(|p| pin_parts(&p.field_path, &p.context_path, p.root)).collect::<Vec<_>>(),
    })
}

// ─── Provider declarations and hoisted fields ───────────────────────────

pub(crate) fn param_type(p: &ParamType) -> Json {
    json!({
        "paramType": p.param_type,
        "fields": p.fields.iter().map(|(k, v)| json!([k, param_type(v)])).collect::<Vec<_>>(),
        "items": p.items.as_deref().map(param_type),
        "required": p.required,
        "entityType": p.entity_type,
    })
}

pub(crate) fn method_decl(m: &MethodDecl) -> Json {
    json!({
        "argumentTypes": m.argument_types.iter().map(param_type).collect::<Vec<_>>(),
        "outputType": param_type(&m.output_type),
        "inputType": m.input_type.as_ref().map(param_type),
    })
}

pub(crate) fn provider_decl(d: &ProviderDecl) -> Json {
    json!({
        "argumentTypes": d.argument_types.iter().map(param_type).collect::<Vec<_>>(),
        "outputType": param_type(&d.output_type),
        "methods": d.methods.iter().map(|(k, m)| json!([k, method_decl(m)])).collect::<Vec<_>>(),
        "implementation": d.implementation.as_ref().map(|i| match i {
            Implementation::Rhai { script, script_file } => {
                ctor("rhai", json!({"script": script, "scriptFile": script_file}))
            }
        }),
    })
}

pub(crate) fn entity_type_decl(d: &EntityTypeDecl) -> Json {
    json!({"values": d.values, "annotations": pairs(&d.annotations)})
}

pub(crate) fn declarations(d: &ProviderDeclarations) -> Json {
    json!({
        "available": d.available.iter().map(|(k, v)| json!([k, provider_decl(v)])).collect::<Vec<_>>(),
        "entityTypeDecls": d.entity_type_decls.iter().map(|(k, v)| json!([k, entity_type_decl(v)])).collect::<Vec<_>>(),
    })
}

pub(crate) fn scoped_action(a: &ScopedAction) -> Json {
    match a {
        ScopedAction::Concrete((ns, id)) => ctor("concrete", json!({"ns": ns, "id": id})),
        ScopedAction::List(v) => ctor("list", json!({"actions": v})),
        ScopedAction::Unconstrained => json!("unconstrained"),
    }
}

pub(crate) fn scope_constraint(c: &ScopeConstraint) -> Json {
    match c {
        ScopeConstraint::Any => json!("any"),
        ScopeConstraint::IsType(t) => ctor("isType", json!({"t": t})),
        ScopeConstraint::Uid { entity_type, membership } => {
            ctor("uid", json!({"entityType": entity_type, "membership": membership}))
        }
    }
}

pub(crate) fn provider_arg(a: &Arg) -> Json {
    match a {
        Arg::Field(p) => ctor("field", json!({"path": p})),
        Arg::String(s) => ctor("string", json!({"s": s})),
        Arg::Integer(i) => ctor("integer", json!({"i": i})),
        Arg::Decimal(t) => ctor("decimal", json!({"text": t})),
        Arg::Bool(b) => ctor("bool", json!({"b": b})),
        Arg::Set(xs) => ctor("set", json!({"items": xs.iter().map(provider_arg).collect::<Vec<_>>()})),
    }
}

pub(crate) fn invocation(i: &Invocation) -> Json {
    json!({"span": span(i.span), "function": i.function, "args": i.args.iter().map(provider_arg).collect::<Vec<_>>()})
}

pub(crate) fn method_call(m: &MethodCall) -> Json {
    json!({"span": span(m.span), "name": m.name, "args": m.args.iter().map(provider_arg).collect::<Vec<_>>()})
}

pub(crate) fn context_field(f: &ContextField) -> Json {
    json!({
        "action": scoped_action(&f.action), "fieldName": f.field_name, "temporal": temporal(&f.temporal),
        "targetActions": f.target_actions, "principal": scope_constraint(&f.principal),
        "resource": scope_constraint(&f.resource),
    })
}

pub(crate) fn provider_field(f: &ProviderField) -> Json {
    json!({
        "action": scoped_action(&f.action), "targetActions": f.target_actions, "fieldName": f.field_name,
        "cedarType": f.cedar_type, "bodyBase": f.body_base, "invocation": invocation(&f.invocation),
        "methods": f.methods.iter().map(method_call).collect::<Vec<_>>(),
        "principal": scope_constraint(&f.principal), "resource": scope_constraint(&f.resource),
    })
}

// ─── Cedar schema fragments ─────────────────────────────────────────────

/// Schema annotations, as `[key, value]` pairs; the value is `null` for an
/// annotation written without one.
pub(crate) fn annotations(a: &cedar_policy_core::est::Annotations) -> Json {
    Json::Array(
        a.0.iter()
            .map(|(k, v)| json!([k.to_string(), v.as_ref().map(|v| v.val.as_str())]))
            .collect(),
    )
}

pub(crate) fn schema_type(t: &json_schema::Type<RawName>) -> Json {
    use json_schema::TypeVariant as V;
    match t {
        json_schema::Type::CommonTypeRef { type_name, .. } => ctor("commonRef", json!({"name": type_name.to_string()})),
        json_schema::Type::Type { ty, .. } => match ty {
            V::String => json!("string"),
            V::Long => json!("long"),
            V::Boolean => json!("boolean"),
            V::Set { element } => ctor("set", json!({"element": schema_type(element)})),
            V::Record(r) => ctor(
                "record",
                json!({
                    "attributes": r.attributes.iter().map(|(k, a)| json!([k.as_str(), {
                        "ty": schema_type(&a.ty), "required": a.required, "annotations": annotations(&a.annotations),
                    }])).collect::<Vec<_>>(),
                    "additionalAttributes": r.additional_attributes,
                }),
            ),
            V::Entity { name } => ctor("entity", json!({"name": name.to_string()})),
            V::EntityOrCommon { type_name } => ctor("entityOrCommon", json!({"name": type_name.to_string()})),
            V::Extension { name } => ctor("extension", json!({"name": name.to_string()})),
        },
    }
}

/// A Cedar schema fragment, its namespaces in the fragment's own order (the
/// order of Cedar's `Name`: basename first, then the namespace path).
pub(crate) fn schema_fragment(f: &json_schema::Fragment<RawName>) -> Json {
    Json::Array(
        f.0.iter()
            .map(|(ns, def)| {
                let common: Vec<Json> = def
                    .common_types
                    .iter()
                    .map(|(id, ct)| json!([id.to_string(), {"ty": schema_type(&ct.ty), "annotations": annotations(&ct.annotations)}]))
                    .collect();
                let entities: Vec<Json> = def
                    .entity_types
                    .iter()
                    .map(|(id, et)| {
                        let kind = match &et.kind {
                            json_schema::EntityTypeKind::Standard(s) => ctor(
                                "standard",
                                json!({
                                    "memberOfTypes": s.member_of_types.iter().map(|n| n.to_string()).collect::<Vec<_>>(),
                                    "shape": schema_type(&s.shape.0),
                                    "tags": s.tags.as_ref().map(schema_type),
                                }),
                            ),
                            json_schema::EntityTypeKind::Enum { choices } => ctor(
                                "enum",
                                json!({"choices": choices.iter().map(|c| c.as_ref().to_string()).collect::<Vec<_>>()}),
                            ),
                        };
                        // `external` (Cedar 4.14, RFC 116): declared here, defined in another
                        // fragment, so a `standard` kind carries its parents only.
                        json!([id.to_string(), {"kind": kind, "external": et.external, "annotations": annotations(&et.annotations)}])
                    })
                    .collect();
                let actions: Vec<Json> = def
                    .actions
                    .iter()
                    .map(|(id, a)| {
                        // The deprecated action attributes, as compact JSON text.
                        let attributes = a.attributes.as_ref().map(|m| {
                            let sorted: BTreeMap<&str, _> = m.iter().map(|(k, v)| (k.as_str(), v)).collect();
                            serde_json::to_string(&sorted).unwrap_or_default()
                        });
                        json!([id.as_str(), {
                            "attributes": attributes,
                            "appliesTo": a.applies_to.as_ref().map(|s| json!({
                                "principalTypes": s.principal_types.iter().map(|n| n.to_string()).collect::<Vec<_>>(),
                                "resourceTypes": s.resource_types.iter().map(|n| n.to_string()).collect::<Vec<_>>(),
                                "context": schema_type(&s.context.0),
                            })),
                            "memberOf": a.member_of.as_ref().map(|ms| ms.iter().map(|m| json!({
                                "id": m.id.as_str(), "ty": m.ty.as_ref().map(|t| t.to_string()),
                            })).collect::<Vec<_>>()),
                            // An `external` action has no `appliesTo`.
                            "external": a.external,
                            "annotations": annotations(&a.annotations),
                        }])
                    })
                    .collect();
                json!([ns.as_ref().map(|n| n.to_string()), {
                    "commonTypes": common, "entityTypes": entities, "actions": actions,
                    "annotations": annotations(&def.annotations),
                }])
            })
            .collect(),
    )
}

/// The sources of corpus bundles, read as the conformance bridge reads them
/// (tests only).
#[cfg(test)]
pub(crate) mod test_bundles {
    use std::path::{Path, PathBuf};

    use super::BundleSources;

    /// One bundle's sources.
    pub(crate) struct Bundle {
        pub(crate) dir: PathBuf,
        pub(crate) policy: String,
        pub(crate) event_schema: String,
        pub(crate) providers: Option<String>,
        pub(crate) macros: Option<String>,
        pub(crate) action_schema: String,
    }

    impl Bundle {
        pub(crate) fn sources(&self) -> BundleSources<'_> {
            BundleSources {
                policy: &self.policy,
                event_schema: Some(&self.event_schema),
                providers: self.providers.as_deref(),
                macros: self.macros.as_deref(),
                action_schema: &self.action_schema,
                ids: None,
                distincter: None,
            }
        }
    }

    /// Every `step`-th bundle of the corpus directory `group` (under `tests/`),
    /// whose action schema is the bundle's own or the group's `shared` one.
    pub(crate) fn read(group: &str, shared: Option<&str>, step: usize) -> Vec<Bundle> {
        let manifest = Path::new(env!("CARGO_MANIFEST_DIR"));
        let root = manifest.join("tests").join(group);
        let read = |p: PathBuf| std::fs::read_to_string(p).ok();
        let shared = shared.and_then(|f| read(root.join(f))).unwrap_or_default();
        let events = read(manifest.join("tests/fixtures/request_response.dwschema")).unwrap();
        let mut dirs: Vec<_> = std::fs::read_dir(root.join("corpus"))
            .unwrap()
            .filter_map(|e| e.ok().map(|e| e.path()))
            .filter(|p| p.is_dir())
            .collect();
        dirs.sort();
        dirs.into_iter()
            .step_by(step)
            .map(|dir| {
                let policy = read(dir.join("policy.dw")).unwrap_or_else(|| {
                    let mut parts: Vec<_> = std::fs::read_dir(&dir)
                        .unwrap()
                        .filter_map(|e| e.ok().map(|e| e.path()))
                        .filter(|p| {
                            p.extension().is_some_and(|e| e == "dw")
                                && p.file_name()
                                    .and_then(|n| n.to_str())
                                    .is_some_and(|n| n.starts_with("policy_"))
                        })
                        .collect();
                    parts.sort();
                    parts.into_iter().filter_map(read).collect::<Vec<_>>().join("\n")
                });
                Bundle {
                    action_schema: read(dir.join("schema.cedarschema"))
                        .unwrap_or_else(|| shared.clone()),
                    event_schema: read(dir.join("event.dwschema"))
                        .or_else(|| read(dir.join("events.dwschema")))
                        .unwrap_or_else(|| events.clone()),
                    providers: read(dir.join("providers.json")),
                    macros: read(dir.join("macros.dw")),
                    policy,
                    dir,
                }
            })
            .collect()
    }

    /// The corpus groups the tests sample, with their shared action schemas.
    pub(crate) const GROUPS: [(&str, Option<&str>); 4] = [
        ("passing/temporal_only", Some("shared_schema.cedarschema")),
        ("passing/provider_only", Some("shared_schema.cedarschema")),
        ("passing/macros", None),
        ("passing/mixed", None),
    ];
}

#[cfg(test)]
mod tests {
    use super::*;

    const SCHEMA: &str = r#"
        namespace Drupe {
            entity User;
            entity Doc;
            type ReadInput = { user: String };
            action Login appliesTo { principal: User, resource: Doc, context: { input: { user: String } } };
            action Read appliesTo { principal: User, resource: Doc, context: { input: ReadInput } };
        }
    "#;

    const POLICY: &str = r#"
        permit (principal, action == Drupe::Action::"Read", resource)
        when temporal {
            formerly within 1h Drupe::Action::"Login"::response{ input.user: context.input.user }
        };
    "#;

    fn sources<'a>(policy: &'a str, schema: &'a str) -> BundleSources<'a> {
        BundleSources {
            policy,
            event_schema: None,
            providers: None,
            macros: None,
            action_schema: schema,
            ids: None,
            distincter: None,
        }
    }

    #[test]
    fn a_lowering_bundle_exports_every_stage_and_agrees_with_the_pipeline() {
        let out = export(&sources(POLICY, SCHEMA));
        for stage in [
            "mergeLibrary", "expand", "derive", "signatures", "universalPins", "decisionKinds",
            "rejectArrays", "cedarify", "injectPins", "identity", "augment", "compileSchema",
            "resolveProviders", "unorder", "relativize",
        ] {
            assert!(out["stages"][stage].get("ok").is_some(), "stage {stage}: {}", out["stages"][stage]);
        }
        let lowered = &out["outcome"]["lowered"];
        assert_eq!(lowered["mismatches"], json!([]), "{lowered}");
        assert_eq!(lowered["ruleIds"], json!(["policy_0"]));
        assert_eq!(out["stages"]["cedarify"]["ok"]["contextFields"][0]["fieldName"], json!("policy_0__temporal_0"));
        assert_eq!(out["stages"]["decisionKinds"]["ok"], json!(["request"]));
        // The default library is merged before expansion, and expansion clears it.
        assert!(!out["stages"]["mergeLibrary"]["ok"]["defs"].as_array().unwrap().is_empty());
        assert_eq!(out["stages"]["expand"]["ok"]["defs"], json!([]));
        // The pinned leaf carries the default schema's pin on `callerPrincipal`.
        let pinned = out["stages"]["injectPins"]["ok"][0].to_string();
        assert!(pinned.contains("callerPrincipal"), "{pinned}");
    }

    /// `condition` writes each leaf a temporal engine receives (the pin-injected authored leaves
    /// of the lowered set) as the export's `injectPins` stage writes it.
    #[test]
    fn condition_writes_each_leaf_as_the_export_does() {
        let service = ServiceSchema::builder().frontend(crate::Frontend::Rust).build().unwrap();
        let schema = crate::PolicySchema::from_cedarschema_str(SCHEMA).unwrap();
        let parsed = crate::ParsedPolicySet::parse(POLICY, &service).unwrap();
        let (lowered, _) = super::super::lower(&parsed.parsed, &schema, None).unwrap();
        let leaves: Vec<Json> =
            lowered.temporal.iter().map(|f| condition(&f.condition.condition)).collect();
        assert_eq!(leaves.len(), 1);
        let out = export(&sources(POLICY, SCHEMA));
        assert_eq!(Json::Array(leaves), out["stages"]["injectPins"]["ok"]);
    }

    /// `event` writes an event as a timepoint of the specification: no `null`, an array as a set,
    /// a decimal by its text, an extension value by its constructor and argument, the scope's
    /// uids, and the entities with their ancestors closed transitively.
    #[test]
    fn event_writes_a_timepoint_of_the_specification() {
        use crate::Value;
        let user = || Value::Entity { ty: "Drupe::User".into(), id: "alice".into() };
        let ev = crate::Event::builder("Drupe::Action::Read", "request")
            .timestamp(42)
            .principal_for("Drupe::User", "alice")
            .field("input", "user", Value::String("alice".into()))
            .field("input", "gone", Value::Null)
            .logged_field("tags", Value::Array(vec![Value::Int(2), Value::Null, Value::Int(1)]))
            .logged_field("amount", Value::Decimal("02.50".into()))
            .logged_field("addr", Value::extension("ip", "10.0.0.1"))
            .logged_field("nothing", Value::Null)
            .logged_field("callerPrincipal", user())
            .request_context("input", "user", Value::String("alice".into()))
            .entity_for("Drupe::User", "alice", [("dept", Value::String("eng".into()))])
            .parents_for("Drupe::User", "alice", [("Drupe::Group", "g1")])
            .parents_for("Drupe::Group", "g1", [("Drupe::Group", "g0")])
            .build();
        let uid = |ty: &str, id: &str| json!({"ty": {"id": ty, "path": ["Drupe"]}, "eid": id});
        assert_eq!(
            event(&ev),
            json!({"ts": 42, "event": {
                "action": uid("Action", "Read"),
                "kind": "request",
                "principal": uid("User", "alice"),
                "resource": null,
                "logged": [
                    ["addr", {"extension": {"fn": "ip", "arg": "10.0.0.1"}}],
                    ["amount", {"decimal": "02.50"}],
                    ["callerPrincipal", {"entity": uid("User", "alice")}],
                    ["input", {"record": [["user", "alice"]]}],
                    ["tags", {"set": [2, 1]}],
                ],
                "context": [["input", {"record": [["user", "alice"]]}]],
                "entities": [
                    [uid("Group", "g1"), {"attrs": [], "ancestors": [uid("Group", "g0")], "tags": []}],
                    [uid("User", "alice"), {"attrs": [["dept", "eng"]],
                        "ancestors": [uid("Group", "g0"), uid("Group", "g1")], "tags": []}],
                ],
            }})
        );
        assert_eq!(value(&Value::Null), None);
        assert_eq!(value(&user()), Some(json!({"entity": uid("User", "alice")})));
    }

    #[test]
    fn a_rejected_bundle_records_the_failing_stage() {
        let bad = "permit (principal, action, resource) when { undefined_macro(1) };";
        let out = export(&sources(bad, SCHEMA));
        assert_eq!(out["stages"]["expand"]["error"]["category"], json!("macro"));
        assert!(out["stages"].get("cedarify").is_none());
        assert_eq!(out["outcome"]["rejected"]["category"], json!("macro"));
        // Derivation does not depend on the policy, so it still runs.
        assert!(out["stages"]["derive"].get("ok").is_some());
    }

    /// Every sampled bundle of a corpus directory that lowers: the stages
    /// reproduce the public pipeline on it. A bundle's files are read as the conformance
    /// bridge reads them.
    fn check_corpus(group: &str, shared: Option<&str>) -> usize {
        let mut lowered = 0;
        // A sample of the corpus, to keep the test quick in a debug build; the
        // conformance bridge runs the export over every bundle.
        for b in super::test_bundles::read(group, shared, 8) {
            let out = export(&b.sources());
            if let Some(l) = out["outcome"].get("lowered") {
                lowered += 1;
                assert_eq!(l["mismatches"], json!([]), "{}", b.dir.display());
            }
        }
        lowered
    }

    #[test]
    fn stable_ids_and_a_distincter_reach_the_whole_lowered_set() {
        let policy = format!("@id(\"read\")\n{POLICY}");
        let ids = crate::IdSource::Annotation;
        let out = export(&BundleSources {
            ids: Some(&ids),
            distincter: Some("usr"),
            ..sources(&policy, SCHEMA)
        });
        assert_eq!(out["stages"]["assignIds"]["ok"]["annotation"]["ok"], json!(["read"]));
        let full = &out["outcome"]["lowered"]["full"];
        assert_eq!(full["ruleIds"], json!(["usr/read"]), "{full}");
        assert_eq!(full["stableIds"], json!(true));
        assert_eq!(full["temporal"][0]["id"], json!("usr_0__temporal_0"));
    }

    #[test]
    fn several_policy_sets_are_lowered_together() {
        let entries = [
            ManyEntry { policy: POLICY, distincter: "a", ids: None },
            ManyEntry { policy: POLICY, distincter: "b", ids: None },
        ];
        let many = |entries: &[ManyEntry<'_>]| {
            export_many(&ManySources {
                entries,
                event_schema: None,
                providers: None,
                macros: None,
                action_schema: SCHEMA,
            })
        };
        let full = &many(&entries)["outcome"]["lowered"]["full"];
        assert_eq!(full["ruleIds"], json!(["a_0", "b_0"]), "{full}");
        assert_eq!(full["ruleSources"], json!([0, 1]));
        let repeated = [entries[0], ManyEntry { distincter: "a", ..entries[1] }];
        let out = many(&repeated);
        assert_eq!(out["outcome"]["rejected"]["category"], json!("duplicateDistincter"), "{out}");
        assert_eq!(out["outcome"]["rejected"]["message"], json!("a"));
    }

    #[test]
    fn the_stages_reproduce_the_pipeline_on_the_corpora() {
        assert!(check_corpus("passing/temporal_only", Some("shared_schema.cedarschema")) > 50);
        assert!(check_corpus("passing/provider_only", Some("shared_schema.cedarschema")) > 5);
        assert!(check_corpus("passing/macros", None) > 10);
    }

    /// The frontend stages that ran since the last call, on this thread.
    fn stages() -> Vec<&'static str> {
        crate::api::stage_probe::take()
    }

    #[test]
    fn the_inputs_are_the_exports_and_run_only_the_parsers() {
        let annotated = format!("@id(\"read\")\n{POLICY}");
        let ids = crate::IdSource::Annotation;
        let explicit = crate::IdSource::Explicit(vec!["r".into()]);
        let mut bundles: Vec<BundleSources<'_>> = vec![
            sources(POLICY, SCHEMA),
            sources("permit (principal, action, resource) when { undefined_macro(1) };", SCHEMA),
            sources("permit (principal", SCHEMA),
            sources(POLICY, "namespace {"),
            BundleSources { ids: Some(&ids), distincter: Some("usr"), ..sources(&annotated, SCHEMA) },
            BundleSources { ids: Some(&explicit), ..sources(POLICY, SCHEMA) },
            BundleSources { providers: Some("{not json"), ..sources(POLICY, SCHEMA) },
            BundleSources { event_schema: Some(""), macros: Some(""), ..sources(POLICY, SCHEMA) },
        ];
        let corpus: Vec<_> = super::test_bundles::GROUPS
            .iter()
            .flat_map(|(g, shared)| super::test_bundles::read(g, *shared, 8))
            .collect();
        bundles.extend(corpus.iter().map(|b| b.sources()));
        let mut lowered = 0;
        for b in &bundles {
            stages();
            let inputs = inputs(b);
            assert_eq!(stages(), Vec::<&str>::new(), "inputs ran a stage on\n{}", b.policy);
            let exported = export(b);
            let ran = stages();
            if exported["outcome"].get("lowered").is_some() {
                lowered += 1;
                // The probe sees the stages the export runs.
                for stage in ["parse", "expand", "derive", "cedarify", "lowerEntry", "merge"] {
                    assert!(ran.contains(&stage), "export ran {ran:?}");
                }
            }
            // The same JSON, key for key and in the same order.
            assert_eq!(
                serde_json::to_string(&inputs).unwrap(),
                serde_json::to_string(&exported["inputs"]).unwrap(),
                "{}",
                b.policy
            );
        }
        assert!(lowered > 50, "only {lowered} bundles lowered");
    }

    #[test]
    fn the_inputs_of_several_sets_are_the_exports() {
        let bad = "permit (principal";
        for entries in [
            vec![
                ManyEntry { policy: POLICY, distincter: "a", ids: None },
                ManyEntry { policy: POLICY, distincter: "b", ids: Some(&crate::IdSource::Positional) },
            ],
            vec![ManyEntry { policy: bad, distincter: "a", ids: None }],
            vec![],
        ] {
            let m = ManySources {
                entries: &entries,
                event_schema: None,
                providers: None,
                macros: None,
                action_schema: SCHEMA,
            };
            stages();
            let inputs = inputs_many(&m);
            assert_eq!(stages(), Vec::<&str>::new());
            let exported = export_many(&m);
            assert_eq!(
                serde_json::to_string(&inputs).unwrap(),
                serde_json::to_string(&exported["inputs"]).unwrap()
            );
        }
    }

    /// `cedar_policy_set` and `cedar_schema` rebuild, from a lowered set's JSON, its
    /// Cedar policies (ids, annotations, policy JSON and text) and its augmented
    /// schema.
    #[test]
    fn the_cedar_part_is_rebuilt_from_its_json() {
        let annotated = format!("@id(\"read\")\n@note(\"why\")\n{POLICY}");
        let service = ServiceSchema::builder().frontend(crate::Frontend::Rust).build().unwrap();
        let schema = crate::PolicySchema::from_cedarschema_str(SCHEMA).unwrap();
        let parsed = crate::ParsedPolicySet::parse(&annotated, &service)
            .unwrap()
            .with_ids(crate::IdSource::Annotation)
            .unwrap();
        let mut sets = vec![super::super::lower(&parsed.parsed, &schema, None).unwrap()];
        let corpus = super::test_bundles::GROUPS
            .iter()
            .flat_map(|(g, shared)| super::test_bundles::read(g, *shared, 8));
        for b in corpus {
            let mut builder = ServiceSchema::builder()
                .frontend(crate::Frontend::Rust)
                .event_schema_str(&b.event_schema);
            if let Some(m) = &b.macros {
                builder = builder.macros_str(m);
            }
            if let Some(p) = &b.providers {
                builder = builder.providers(crate::ProviderDeclarations::from_json(p).unwrap());
            }
            let (Ok(service), Ok(schema)) =
                (builder.build(), crate::PolicySchema::from_cedarschema_str(&b.action_schema))
            else {
                continue;
            };
            let Ok(parsed) = super::super::parse(&b.policy, &service, &dogwood_syntax::ParseOptions::default()) else { continue };
            if let Ok(l) = super::super::lower(&parsed, &schema, None) {
                sets.push(l);
            }
        }
        assert!(sets.len() > 10, "only {} sets", sets.len());
        for (l, identity) in &sets {
            let record = lowered_record(l, identity);
            let rebuilt = cedar_policy_set(&record["policies"]).unwrap();
            let mut ids: Vec<String> = rebuilt.policies().map(|p| p.id().to_string()).collect();
            let mut expected = l.rule_ids.clone();
            ids.sort();
            expected.sort();
            assert_eq!(ids, expected);
            for p in l.policies.policies() {
                let q = rebuilt.policy(p.id()).unwrap();
                assert_eq!(q.to_string(), p.to_string());
                assert_eq!(q.to_json().unwrap(), p.to_json().unwrap());
                assert_eq!(
                    q.annotations().collect::<Vec<_>>(),
                    p.annotations().collect::<Vec<_>>()
                );
            }
            let (fragment, _) = cedar_schema(&record["augmentedSchema"]).unwrap();
            assert_eq!(
                fragment.to_json_value().unwrap(),
                l.augmented_schema_fragment.clone().to_json_value().unwrap()
            );
        }
        let first = &sets[0].0;
        let read = first.policies.policies().next().unwrap();
        assert_eq!(read.id().to_string(), "read");
        assert_eq!(read.annotation("note"), Some("why"));
        // A rule that is not Cedar's policy JSON is named.
        let bad = json!([{"id": "x", "est": {"effect": "permit"}}]);
        assert!(cedar_policy_set(&bad).unwrap_err().contains("rule `x`"));
    }
}
