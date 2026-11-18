//! Decoding the Lean frontend's results into the crate's own types: the lowered
//! set (`Lowered` and `SetIdentity`), the validator's findings, and the errors.
//!
//! Every value is in the encoding of the crate's frontend export
//! (`api::frontend_export`): a constructor without fields is its name, one with
//! fields a one-key object holding them by name, a struct an object, an absent
//! optional value `null`, a pair a two-element array, and a map an array of
//! `[key, value]` pairs. Each decoder here inverts the export's encoder of the
//! same name; [`lowered`] inverts `lowered_record`.
//!
//! The lowered set's Cedar policies arrive as Cedar's policy JSON (`est`), and
//! its augmented schema as Cedar's JSON schema; both are rebuilt with Cedar's own
//! constructors, as the Rust frontend builds them: a core `ast::PolicySet`, then
//! `cedar_policy::PolicySet::from`; `SchemaFragment::from_json_value`, then
//! the compilation into a `Schema` (`frontend_export::cedar_policy_set` and
//! `cedar_schema`, which a dependent crate calls on what its own Lean code
//! lowered). Each rule's printed text (`text`) is not re-parsed: the policy JSON
//! is the policy. Shadow mode checks that both printers of the Lean frontend
//! print as Cedar does.

use std::collections::{BTreeMap, BTreeSet};
use std::sync::Arc;

use serde_json::Value as Json;

use crate::api::{ActionRef, EventPinRoot, Lowered, ProviderField, TemporalField};
use crate::cedarify::{ContextRead, ScopeConstraint, ScopedAction};
use crate::error::{SourceLoc, Span};
use crate::event_schema::ast::PinRoot;
use crate::event_schema::derive::{
    DerivedEvent, DerivedEventSchema, DerivedFieldNode, FieldType, Pin,
};
use crate::extension::provider::ast::{Arg, Invocation, MethodCall};
use crate::extension::provider::declarations::{
    EntityTypeDecl, Implementation, MethodDecl, ParamType, ProviderDecl,
};
use crate::extension::temporal::Temporal;
use crate::extension::temporal::ast::{
    AggExpr, AggExprKind, ArithOp, BinderSlot, Call, CallArg, CmpOp, Condition, ConditionKind,
    Interval, NamedArg, Predicate, Sigil, Term, TimeUnit, Type, TypedBinder, WithinSpec,
};

/// A decoding result: the value, or why the JSON is not one.
pub(crate) type R<T> = Result<T, String>;

// ─── JSON accessors ─────────────────────────────────────────────────────

pub(crate) fn get<'a>(j: &'a Json, key: &str) -> R<&'a Json> {
    j.get(key)
        .ok_or_else(|| format!("no key `{key}` in {}", short(j)))
}

/// `j[key]`, or `None` when the key is absent or `null`.
pub(crate) fn opt<'a>(j: &'a Json, key: &str) -> Option<&'a Json> {
    j.get(key).filter(|v| !v.is_null())
}

pub(crate) fn string(j: &Json) -> R<String> {
    j.as_str()
        .map(str::to_owned)
        .ok_or_else(|| format!("not a string: {}", short(j)))
}

pub(crate) fn str_at(j: &Json, key: &str) -> R<String> {
    string(get(j, key)?).map_err(|e| format!("`{key}`: {e}"))
}

fn bool_at(j: &Json, key: &str) -> R<bool> {
    get(j, key)?
        .as_bool()
        .ok_or_else(|| format!("`{key}` is not a boolean"))
}

fn i64_of(j: &Json) -> R<i64> {
    j.as_i64()
        .ok_or_else(|| format!("not a 64-bit integer: {}", short(j)))
}

pub(crate) fn usize_of(j: &Json) -> R<usize> {
    j.as_u64()
        .and_then(|n| usize::try_from(n).ok())
        .ok_or_else(|| format!("not a natural number: {}", short(j)))
}

pub(crate) fn usize_at(j: &Json, key: &str) -> R<usize> {
    usize_of(get(j, key)?).map_err(|e| format!("`{key}`: {e}"))
}

pub(crate) fn list<'a, T>(j: &'a Json, f: impl Fn(&'a Json) -> R<T>) -> R<Vec<T>> {
    j.as_array()
        .ok_or_else(|| format!("not an array: {}", short(j)))?
        .iter()
        .enumerate()
        .map(|(i, x)| f(x).map_err(|e| format!("[{i}]: {e}")))
        .collect()
}

pub(crate) fn list_at<'a, T>(j: &'a Json, key: &str, f: impl Fn(&'a Json) -> R<T>) -> R<Vec<T>> {
    list(get(j, key)?, f).map_err(|e| format!("`{key}`{e}"))
}

fn strings(j: &Json) -> R<Vec<String>> {
    list(j, string)
}

fn strings_at(j: &Json, key: &str) -> R<Vec<String>> {
    list_at(j, key, string)
}

/// A `[key, value]` pair.
fn pair(j: &Json) -> R<(&Json, &Json)> {
    match j.as_array().map(Vec::as_slice) {
        Some([a, b]) => Ok((a, b)),
        _ => Err(format!("not a pair: {}", short(j))),
    }
}

/// A map, as an array of `[key, value]` pairs with string keys.
fn map_at<'a, T>(j: &'a Json, key: &str, f: impl Fn(&'a Json) -> R<T>) -> R<BTreeMap<String, T>> {
    let items = list_at(j, key, |p| {
        let (k, v) = pair(p)?;
        Ok((string(k)?, f(v)?))
    })?;
    Ok(items.into_iter().collect())
}

/// A constructor: its name, and its fields (`null` for a constructor without any).
pub(crate) fn ctor(j: &Json) -> R<(&str, &Json)> {
    match j {
        Json::String(s) => Ok((s.as_str(), &Json::Null)),
        Json::Object(m) if m.len() == 1 => {
            let (k, v) = m.iter().next().expect("one entry");
            Ok((k.as_str(), v))
        }
        _ => Err(format!("not a constructor: {}", short(j))),
    }
}

/// `j` printed, cut to a length that keeps a message readable.
pub(crate) fn short(j: &Json) -> String {
    let s = j.to_string();
    if s.len() <= 120 {
        s
    } else {
        let mut cut = 117;
        while !s.is_char_boundary(cut) {
            cut -= 1;
        }
        format!("{}...", &s[..cut])
    }
}

// ─── Spans, scopes, actions ─────────────────────────────────────────────

pub(crate) fn span(j: &Json) -> R<Span> {
    Ok(Span::new(usize_at(j, "start")?, usize_at(j, "end")?))
}

fn span_at(j: &Json, key: &str) -> R<Span> {
    span(get(j, key)?).map_err(|e| format!("`{key}`: {e}"))
}

fn scoped_action(j: &Json) -> R<ScopedAction> {
    match ctor(j)? {
        ("unconstrained", _) => Ok(ScopedAction::Unconstrained),
        ("concrete", a) => Ok(ScopedAction::Concrete((str_at(a, "ns")?, str_at(a, "id")?))),
        ("list", a) => Ok(ScopedAction::List(list_at(a, "actions", action_pair)?)),
        (c, _) => Err(format!("unknown action scope `{c}`")),
    }
}

/// An action `[namespace, id]`, the namespace `""` at the root.
fn action_pair(j: &Json) -> R<(String, String)> {
    let (ns, id) = pair(j)?;
    Ok((string(ns)?, string(id)?))
}

fn scope_constraint(j: &Json) -> R<ScopeConstraint> {
    match ctor(j)? {
        ("any", _) => Ok(ScopeConstraint::Any),
        ("isType", a) => Ok(ScopeConstraint::IsType(str_at(a, "t")?)),
        ("uid", a) => Ok(ScopeConstraint::Uid {
            entity_type: str_at(a, "entityType")?,
            membership: bool_at(a, "membership")?,
        }),
        (c, _) => Err(format!("unknown scope constraint `{c}`")),
    }
}

fn action_refs(actions: &[(String, String)]) -> Vec<ActionRef> {
    actions
        .iter()
        .map(|(ns, id)| crate::api::action_ref(ns.clone(), id.clone()))
        .collect()
}

// ─── The temporal AST ───────────────────────────────────────────────────

fn interval(j: &Json) -> R<Interval> {
    let unit = match str_at(j, "unit")?.as_str() {
        "seconds" => TimeUnit::Seconds,
        "minutes" => TimeUnit::Minutes,
        "hours" => TimeUnit::Hours,
        "days" => TimeUnit::Days,
        u => return Err(format!("unknown time unit `{u}`")),
    };
    Ok(Interval {
        amount: i64_of(get(j, "amount")?)?,
        unit,
    })
}

fn within(j: &Json) -> R<WithinSpec> {
    match ctor(j)? {
        ("concrete", a) => Ok(WithinSpec::Concrete(interval(get(a, "i")?)?)),
        ("paramRef", a) => Ok(WithinSpec::ParamRef(str_at(a, "name")?)),
        (c, _) => Err(format!("unknown window `{c}`")),
    }
}

fn binder_slot(j: &Json) -> R<BinderSlot> {
    match ctor(j)? {
        ("name", a) => Ok(BinderSlot::Name(str_at(a, "n")?)),
        ("paramRef", a) => Ok(BinderSlot::ParamRef(str_at(a, "name")?)),
        ("binderRef", a) => Ok(BinderSlot::BinderRef(str_at(a, "name")?)),
        (c, _) => Err(format!("unknown binder `{c}`")),
    }
}

fn typed_binder(j: &Json) -> R<TypedBinder> {
    let ty = match ctor(get(j, "ty")?)? {
        ("timepoint", _) => Type::Timepoint,
        ("named", a) => Type::Named(strings_at(a, "path")?),
        (c, _) => return Err(format!("unknown binder type `{c}`")),
    };
    Ok(TypedBinder {
        slot: binder_slot(get(j, "slot")?)?,
        ty,
    })
}

fn cmp_op(s: &str) -> R<CmpOp> {
    Ok(match s {
        "eq" => CmpOp::Eq,
        "ne" => CmpOp::NotEq,
        "lt" => CmpOp::Lt,
        "le" => CmpOp::Le,
        "gt" => CmpOp::Gt,
        "ge" => CmpOp::Ge,
        _ => return Err(format!("unknown comparison `{s}`")),
    })
}

fn arith_op(s: &str) -> R<ArithOp> {
    Ok(match s {
        "add" => ArithOp::Add,
        "sub" => ArithOp::Sub,
        "mul" => ArithOp::Mul,
        _ => return Err(format!("unknown arithmetic operator `{s}`")),
    })
}

fn named_arg(j: &Json) -> R<NamedArg> {
    Ok(NamedArg {
        name: str_at(j, "name")?,
        value: term(get(j, "value")?)?,
    })
}

fn call(j: &Json) -> R<Call> {
    Ok(Call {
        span: span_at(j, "span")?,
        name: str_at(j, "name")?,
        args: list_at(j, "args", |a| match ctor(a)? {
            ("condition", x) => Ok(CallArg::Condition(condition(get(x, "c")?)?)),
            ("within", x) => Ok(CallArg::Within(interval(get(x, "i")?)?)),
            ("term", x) => Ok(CallArg::Term(term(get(x, "t")?)?)),
            (c, _) => Err(format!("unknown call argument `{c}`")),
        })?,
    })
}

fn boxed(j: &Json, key: &str) -> R<Box<Condition>> {
    condition(get(j, key)?)
        .map(Box::new)
        .map_err(|e| format!("`{key}`: {e}"))
}

/// A temporal condition (inverse of the export's `condition`).
pub(crate) fn condition(j: &Json) -> R<Condition> {
    let (c, a) = ctor(get(j, "kind")?)?;
    let kind = match c {
        "and" => ConditionKind::And {
            left: boxed(a, "left")?,
            right: boxed(a, "right")?,
        },
        "or" => ConditionKind::Or {
            left: boxed(a, "left")?,
            right: boxed(a, "right")?,
        },
        "not" => ConditionKind::Not {
            inner: boxed(a, "inner")?,
        },
        "formerly" => ConditionKind::Formerly {
            within: within(get(a, "within")?)?,
            body: boxed(a, "body")?,
        },
        "previous" => ConditionKind::Previous {
            within: within(get(a, "within")?)?,
            body: boxed(a, "body")?,
        },
        "since" => ConditionKind::Since {
            left: boxed(a, "left")?,
            within: within(get(a, "within")?)?,
            right: boxed(a, "right")?,
        },
        "predicate" => {
            let p = get(a, "p")?;
            ConditionKind::Predicate(Predicate {
                span: span_at(p, "span")?,
                namespace: strings_at(p, "namespace")?,
                action: str_at(p, "action")?,
                kind: str_at(p, "kind")?,
                args: list_at(p, "args", named_arg)?,
            })
        }
        "comparison" => ConditionKind::Comparison {
            op: cmp_op(&str_at(a, "op")?)?,
            left: term(get(a, "left")?)?,
            right: term(get(a, "right")?)?,
        },
        "exists" => ConditionKind::Exists {
            var: typed_binder(get(a, "var")?)?,
            body: boxed(a, "body")?,
        },
        "tp" => ConditionKind::Tp {
            var: binder_slot(get(a, "var")?)?,
        },
        "call" => ConditionKind::Call(call(get(a, "c")?)?),
        "sigilRef" => ConditionKind::SigilRef {
            sigil: match str_at(a, "sigil")?.as_str() {
                "param" => Sigil::Param,
                "binder" => Sigil::Binder,
                s => return Err(format!("unknown sigil `{s}`")),
            },
            name: str_at(a, "name")?,
        },
        "refine" => ConditionKind::Refine {
            base: boxed(a, "base")?,
            fields: list_at(a, "fields", named_arg)?,
            span: span_at(a, "span")?,
        },
        _ => return Err(format!("unknown condition `{c}`")),
    };
    Ok(Condition {
        span: span_at(j, "span")?,
        kind,
    })
}

/// A temporal term (inverse of the export's `term`).
pub(crate) fn term(j: &Json) -> R<Term> {
    let (c, a) = ctor(j)?;
    Ok(match c {
        "entity" => Term::Entity {
            ty: str_at(a, "ty")?,
            id: str_at(a, "id")?,
        },
        "integer" => Term::Integer(i64_of(get(a, "i")?)?),
        "decimal" => Term::Decimal(str_at(a, "text")?),
        "string" => Term::String(str_at(a, "s")?),
        "bool" => Term::Bool(bool_at(a, "b")?),
        "contextField" => Term::ContextField(strings_at(a, "path")?),
        "scopeField" => Term::ScopeField(strings_at(a, "path")?),
        "var" => Term::Var(str_at(a, "x")?),
        "wildcard" => Term::Wildcard,
        "array" => Term::Array(list_at(a, "items", term)?),
        "agg" => {
            let x = get(a, "a")?;
            let (k, b) = ctor(get(x, "kind")?)?;
            let kind = match k {
                "sum" => AggExprKind::Sum {
                    bound_var: binder_slot(get(b, "boundVar")?)?,
                    for_vars: list_at(b, "forVars", typed_binder)?,
                    body: boxed(b, "body")?,
                },
                "count" => AggExprKind::Count {
                    for_vars: list_at(b, "forVars", typed_binder)?,
                    body: boxed(b, "body")?,
                },
                "call" => AggExprKind::Call(call(get(b, "c")?)?),
                _ => return Err(format!("unknown aggregation `{k}`")),
            };
            Term::Agg(Box::new(AggExpr {
                span: span_at(x, "span")?,
                kind,
            }))
        }
        "arith" => Term::Arith {
            op: arith_op(&str_at(a, "op")?)?,
            left: Box::new(term(get(a, "left")?)?),
            right: Box::new(term(get(a, "right")?)?),
        },
        "paramRef" => Term::ParamRef(str_at(a, "name")?),
        "binderRef" => Term::BinderRef(str_at(a, "name")?),
        _ => return Err(format!("unknown term `{c}`")),
    })
}

fn temporal(j: &Json) -> R<Temporal> {
    Ok(Temporal {
        condition: condition(get(j, "condition")?).map_err(|e| format!("`condition`: {e}"))?,
        span: span_at(j, "span")?,
    })
}

// ─── Hoisted leaves ─────────────────────────────────────────────────────

fn temporal_field(j: &Json) -> R<TemporalField> {
    let action = scoped_action(get(j, "action")?)?;
    Ok(TemporalField {
        id: str_at(j, "id")?,
        action: crate::api::action_scope(&action),
        target_actions: action_refs(&list_at(j, "targetActions", action_pair)?),
        principal: scope_constraint(get(j, "principal")?)?,
        resource: scope_constraint(get(j, "resource")?)?,
        condition: temporal(get(j, "condition")?).map_err(|e| format!("`condition`: {e}"))?,
    })
}

fn provider_arg(j: &Json) -> R<Arg> {
    let (c, a) = ctor(j)?;
    Ok(match c {
        "field" => Arg::Field(strings_at(a, "path")?),
        "string" => Arg::String(str_at(a, "s")?),
        "integer" => Arg::Integer(i64_of(get(a, "i")?)?),
        "decimal" => Arg::Decimal(str_at(a, "text")?),
        "bool" => Arg::Bool(bool_at(a, "b")?),
        "set" => Arg::Set(list_at(a, "items", provider_arg)?),
        _ => return Err(format!("unknown provider argument `{c}`")),
    })
}

fn param_type(j: &Json) -> R<ParamType> {
    Ok(ParamType {
        param_type: str_at(j, "paramType")?,
        fields: map_at(j, "fields", param_type)?,
        items: opt(j, "items").map(param_type).transpose()?.map(Box::new),
        required: strings_at(j, "required")?,
        entity_type: opt(j, "entityType").map(string).transpose()?,
    })
}

fn method_decl(j: &Json) -> R<MethodDecl> {
    Ok(MethodDecl {
        argument_types: list_at(j, "argumentTypes", param_type)?,
        output_type: param_type(get(j, "outputType")?)?,
        input_type: opt(j, "inputType").map(param_type).transpose()?,
    })
}

fn provider_decl(j: &Json) -> R<ProviderDecl> {
    let implementation = match opt(j, "implementation") {
        None => None,
        Some(i) => match ctor(i)? {
            ("rhai", a) => Some(Implementation::Rhai {
                script: opt(a, "script").map(string).transpose()?,
                script_file: opt(a, "scriptFile").map(string).transpose()?,
            }),
            (c, _) => return Err(format!("unknown implementation `{c}`")),
        },
    };
    Ok(ProviderDecl {
        argument_types: list_at(j, "argumentTypes", param_type)?,
        output_type: param_type(get(j, "outputType")?)?,
        methods: map_at(j, "methods", method_decl)?,
        implementation,
    })
}

fn entity_type_decl(j: &Json) -> R<EntityTypeDecl> {
    Ok(EntityTypeDecl {
        values: strings_at(j, "values")?,
        annotations: map_at(j, "annotations", string)?,
    })
}

fn provider_field(j: &Json) -> R<ProviderField> {
    let action = scoped_action(get(j, "action")?)?;
    let inv = get(j, "invocation")?;
    Ok(ProviderField {
        id: str_at(j, "id")?,
        action: crate::api::action_scope(&action),
        target_actions: action_refs(&list_at(j, "targetActions", action_pair)?),
        principal: scope_constraint(get(j, "principal")?)?,
        resource: scope_constraint(get(j, "resource")?)?,
        invocation: Invocation {
            span: span_at(inv, "span")?,
            function: strings_at(inv, "function")?,
            args: list_at(inv, "args", provider_arg)?,
        },
        methods: list_at(j, "methods", |m| {
            Ok(MethodCall {
                span: span_at(m, "span")?,
                name: str_at(m, "name")?,
                args: list_at(m, "args", provider_arg)?,
            })
        })?,
        body_base: usize_at(j, "bodyBase")?,
        declaration: opt(j, "declaration").map(provider_decl).transpose()?,
        entity_types: map_at(j, "entityTypes", entity_type_decl)?,
        entity_type_names: map_at(j, "entityTypeNames", string)?,
    })
}

// ─── The derived event schema ───────────────────────────────────────────

fn pin_root(s: &str) -> R<PinRoot> {
    match s {
        "scope" => Ok(PinRoot::Scope),
        "context" => Ok(PinRoot::Context),
        _ => Err(format!("unknown pin root `{s}`")),
    }
}

fn pin(j: &Json) -> R<Pin> {
    Ok(Pin {
        field_path: strings_at(j, "fieldPath")?,
        context_path: strings_at(j, "contextPath")?,
        root: pin_root(&str_at(j, "root")?)?,
    })
}

fn field_type(j: &Json) -> R<FieldType> {
    match ctor(j)? {
        ("cedar", a) => Ok(FieldType::Cedar(str_at(a, "text")?)),
        ("entityTypes", a) => Ok(FieldType::EntityTypes(strings_at(a, "names")?)),
        (c, _) => Err(format!("unknown field type `{c}`")),
    }
}

fn field_node(j: &Json) -> R<DerivedFieldNode> {
    match ctor(j)? {
        ("leaf", a) => Ok(DerivedFieldNode::Leaf(field_type(get(a, "ty")?)?)),
        ("group", a) => Ok(DerivedFieldNode::Group(map_at(a, "members", field_node)?)),
        (c, _) => Err(format!("unknown field node `{c}`")),
    }
}

fn derived_schema(j: &Json) -> R<DerivedEventSchema> {
    Ok(DerivedEventSchema {
        events: list_at(j, "events", |e| {
            Ok(DerivedEvent {
                namespace: strings_at(e, "namespace")?,
                action: str_at(e, "action")?,
                kind: str_at(e, "kind")?,
                decision: bool_at(e, "decision")?,
                fields: map_at(e, "fields", field_node)?,
                pins: list_at(e, "pins", pin)?,
            })
        })?,
        max_window: interval(get(j, "maxWindow")?)?,
        max_horizon: match j.get("maxHorizon") {
            None | Some(Json::Null) => None,
            Some(h) => Some(interval(h)?),
        },
    })
}

// ─── The lowered set ────────────────────────────────────────────────────

/// The policy source of each entry of the request, in entry order: the rules'
/// spans index into them.
pub(crate) struct Sources<'a> {
    pub(crate) entries: Vec<&'a Arc<str>>,
}

/// The lowered set and its identity, from the payload's `lowered`.
pub(crate) fn lowered(
    j: &Json,
    sources: &Sources<'_>,
) -> R<(Lowered, crate::identity::SetIdentity)> {
    let field = |key: &str| get(j, key).map_err(|e| format!("lowered: {e}"));
    let in_field = |key: &str, e: String| {
        format!(
            "lowered.{key}{}{e}",
            if e.starts_with('[') { "" } else { ": " }
        )
    };

    let rule_ids = strings(field("ruleIds")?).map_err(|e| in_field("ruleIds", e))?;
    let rule_sources =
        list(field("ruleSources")?, usize_of).map_err(|e| in_field("ruleSources", e))?;
    let rule_spans = list(field("ruleSpans")?, span).map_err(|e| in_field("ruleSpans", e))?;
    if rule_sources.len() != rule_ids.len() || rule_spans.len() != rule_ids.len() {
        return Err("lowered: `ruleSources`, `ruleSpans` and `ruleIds` differ in length".into());
    }
    let rule_locs = rule_spans
        .iter()
        .zip(&rule_sources)
        .map(|(s, &e)| {
            let src = sources
                .entries
                .get(e)
                .ok_or_else(|| format!("lowered: rule source {e} is not an entry"))?;
            Ok(SourceLoc::new(*s, Arc::clone(src)))
        })
        .collect::<R<Vec<_>>>()?;

    let (policies, policy_ids) = crate::api::frontend_export::cedar_policies(field("policies")?)
        .map_err(|e| in_field("policies", e))?;
    if policy_ids != rule_ids {
        return Err("lowered: the policies' ids are not `ruleIds`".into());
    }

    let (augmented_schema_fragment, augmented_schema) =
        crate::api::frontend_export::cedar_schema(field("augmentedSchema")?)
            .map_err(|e| in_field("augmentedSchema", e))?;

    let temporal = list(field("temporal")?, temporal_field).map_err(|e| in_field("temporal", e))?;
    let temporal_executable = list(field("temporalExecutable")?, temporal_field)
        .map_err(|e| in_field("temporalExecutable", e))?;
    let temporal_rewritten = list(field("temporalRewritten")?, temporal_field)
        .map_err(|e| in_field("temporalRewritten", e))?;
    let partition_keys = list(field("partitionKeys")?, |p| {
        let p = pin(p)?;
        Ok(crate::engine::PartitionKey {
            field_path: p.field_path,
            root: match p.root {
                PinRoot::Scope => EventPinRoot::Scope,
                PinRoot::Context => EventPinRoot::Context,
            },
            context_path: p.context_path,
        })
    })
    .map_err(|e| in_field("partitionKeys", e))?;
    let providers =
        list(field("providers")?, provider_field).map_err(|e| in_field("providers", e))?;
    let temporal_rules =
        list(field("temporalRules")?, usize_of).map_err(|e| in_field("temporalRules", e))?;
    let provider_rules =
        list(field("providerRules")?, usize_of).map_err(|e| in_field("providerRules", e))?;
    let event_schema =
        derived_schema(field("eventSchema")?).map_err(|e| in_field("eventSchema", e))?;
    let decision_kinds: BTreeSet<String> = strings(field("decisionKinds")?)
        .map_err(|e| in_field("decisionKinds", e))?
        .into_iter()
        .collect();
    let enum_names: BTreeMap<String, String> = list(field("enumNames")?, |p| {
        let (k, v) = pair(p)?;
        Ok((string(k)?, string(v)?))
    })
    .map_err(|e| in_field("enumNames", e))?
    .into_iter()
    .collect();
    let context_reads = list(field("contextReads")?, |r| {
        Ok(ContextRead {
            rule: usize_at(r, "rule")?,
            span: span_at(r, "span")?,
            message: str_at(r, "message")?,
            whole: bool_at(r, "whole")?,
        })
    })
    .map_err(|e| in_field("contextReads", e))?;
    if temporal_rules.len() != temporal.len()
        || temporal_executable.len() != temporal.len()
        || temporal_rewritten.len() != temporal.len()
        || provider_rules.len() != providers.len()
        || temporal_rules
            .iter()
            .chain(&provider_rules)
            .any(|&k| k >= rule_ids.len())
        || context_reads.iter().any(|r| r.rule >= rule_ids.len())
    {
        return Err("lowered: the leaves and their rules do not line up".into());
    }

    let mut rule_index = std::collections::HashMap::with_capacity(rule_ids.len());
    for (k, id) in rule_ids.iter().enumerate() {
        rule_index.entry(id.clone()).or_insert(k);
    }

    let revisions = strings(field("ruleRevisions")?).map_err(|e| in_field("ruleRevisions", e))?;
    if revisions.len() != rule_ids.len() {
        return Err("lowered: `ruleRevisions` and `ruleIds` differ in length".into());
    }
    let stable = field("stableIds")?
        .as_bool()
        .ok_or("lowered: `stableIds` is not a boolean")?;
    let identity = match opt(j, "versionHash") {
        Some(v) => crate::identity::SetIdentity::with_version_hash(
            revisions,
            stable,
            string(v).map_err(|e| in_field("versionHash", e))?,
        ),
        // Computed by the crate from the decoded set, on first use.
        None => crate::identity::SetIdentity::new(revisions, stable),
    };

    Ok((
        Lowered {
            policies,
            augmented_schema,
            augmented_schema_fragment,
            temporal,
            temporal_executable,
            temporal_rewritten,
            partition_keys,
            providers,
            rule_ids,
            rule_index,
            rule_locs,
            rule_sources,
            temporal_rules,
            provider_rules,
            event_schema,
            decision_kinds,
            enum_names,
            context_reads,
            checks: Default::default(),
            lean: None,
        },
        identity,
    ))
}
