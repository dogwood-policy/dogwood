//! Runtime conformance: what an [`Authorizer`](crate::Authorizer) checks of the
//! data a decision reads before it decides.
//!
//! Validation makes a policy set's leaves well-typed against its schemas. At
//! runtime the data a decision reads must conform to the same schemas, and a
//! decision fails closed on each kind of nonconforming data. The rules follow
//! the formal specification (`dogwood-lean`, `Dogwood.Spec.Conformance`):
//!
//! * **An event** conforms when the event schema declares a signature for its
//!   action and kind, and its logged record is an instance of that signature:
//!   every logged declared field has its declared type, every required field
//!   and every pinned field is logged, and every logged field that mirrors the
//!   request holds the request's value. The mirrored fields are the fields of
//!   the symmetric pins, and `callerPrincipal` and `callerResource` when no pin
//!   names them. A field spliced from the action's `context.input` /
//!   `context.output` record has the type the context declares at its path,
//!   and is required when every attribute along the path is required; any
//!   other declared field has the type the event schema names, and is
//!   optional.
//! * **A request** conforms when its action is declared, its principal and its
//!   resource are of types the action applies to, and its context is an
//!   instance of the action's context record type: it has no undeclared
//!   attribute, and every required attribute is present. The context record
//!   type is the one the action schema declares, without the attributes
//!   lowering hoists (`context.<id>` for each temporal leaf, and
//!   `context.providers`): the decision supplies those itself.
//! * **A provider output** conforms when it is a value of the provider's
//!   declared output type: the type of the last method of its output-method
//!   chain, or the provider's own output type when the chain is empty.
//!
//! The entity store is checked by Cedar itself (`Entities::from_entities` with
//! the schema), in `api::build_entities`.
//!
//! A value of [`Value::Null`] stands for an absent value: a logged field, a
//! context attribute, or a record attribute whose value is `Null` is absent.
//! [`Value`] carries a value of Cedar's `ipaddr`, `datetime`, and `duration`
//! extension types as Cedar's JSON escape `{"__extn": {"fn": F, "arg": A}}`; it
//! conforms when `F` is the type's constructor and Cedar accepts `A`.

//!
//! ## The pin rules and the mirror rule
//!
//! The pin rules of an event's conformance: the **mirror rule**, and the rule
//! that every pinned field is logged.
//!
//! A logged field that *mirrors* the request must hold the request's value.
//! This is what lets a pin isolate a key: an event cannot log one principal as
//! its caller while it carries another, or none. The mirrored fields are the
//! fields of the symmetric pins, and the caller fields `callerPrincipal` /
//! `callerResource` when the signature declares them and no pin names them. A
//! pin is symmetric when it is pinned to the request's principal, its
//! resource, or a context attribute (`pin f = principal`, `pin f = resource`,
//! `pin f = context.<path>`), whatever the field is called. A pin to an
//! attribute of the principal or resource (`pin dept = principal.dept`) is not
//! symmetric, and its field need only be logged.
//!
//! The specification states the rule as `Mirrored` (`dogwood-lean`,
//! `Dogwood.Spec.Conformance`), checked by `Event.Conforms` before an event is
//! logged (`Log.submit` rejects a nonconforming event). Its **strict** form, the
//! default here ([`MirrorRule::Strict`]), has no vacuous case:
//!
//! * when the event's request side resolves (it has a principal, a resource, or
//!   the pinned context path), the logged field holds that value;
//! * when it does not, the logged field is **absent**.
//!
//! The earlier form ([`MirrorRule::Current`]) accepted any logged value when the
//! request side did not resolve. A scope-less event could then log
//! `callerPrincipal: alice` and count as Alice's history under a pin that is not
//! universal, so forged history reached Alice's decisions (semantics review
//! F1.2, critical). Under the strict rule such an event is rejected.
//!
//! **What the strict rule costs** (semantics review F1.4): an event that reports
//! on a key must carry that key's scope. Under a universal pin
//! (`pin callerPrincipal = principal` on every kind, the default schema), a
//! history event without a principal can no longer log a caller: it is
//! rejected. Report history events with the principal (and resource) of the
//! request they report on.
//!
//! A [`Value::Null`] is an absent value on both sides.
//!
//! There is one conformance check, [`RuntimeChecks::event_nonconformance`]
//! (the specification's `Event.Conforms`, with its strict mirror rule), which
//! every ingested event goes through, and which
//! [`LoweredPolicySet::check_event_conformance`](crate::LoweredPolicySet::check_event_conformance)
//! runs without ingesting (both through `Lowered::check_event_conformance`).
//! Its pin clauses are one function
//! (`pin_nonconformance`), which [`EventSignature::check_pins`] and
//! [`LoweredPolicySet::check_event`](crate::LoweredPolicySet::check_event)
//! also run; [`MirrorRule`] is an option over it: `Current` drops the strict
//! case (a mirrored field logged by an event with no request-side value for
//! it), `Unchecked` drops the pin clauses (1.1's ingestion).

use std::collections::{BTreeMap, BTreeSet};

use cedar_policy::RestrictedExpression;
use cedar_policy_core::ast::{Eid, EntityType, EntityUID};
use cedar_policy_core::validator::types::{Attributes, EntityKind, OpenTag, Type};
use cedar_policy_core::validator::{ValidatorEntityTypeKind, ValidatorSchema};

use crate::api::{EventPinRoot, EventSignature, Lowered};
use crate::event_schema::ast::PinRoot;
use crate::event_schema::derive::{DerivedEvent, FieldType};
use crate::extension::provider::declarations::ParamType;
use crate::interpreter::value::{
    Event, EventData, Value, cedar_decimal_value, entity_uid_string, extension_escape,
};

// ─── Types ───────────────────────────────────────────────────────────

/// A type a runtime value is checked against: Cedar's schema types, in a form
/// built once from the schemas a policy set was lowered against.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum CType {
    Bool,
    Long,
    String,
    Decimal,
    /// One of Cedar's `ipaddr`, `datetime`, and `duration` extension types, by
    /// name. [`Value`] carries a value of one as Cedar's JSON escape
    /// (`interpreter::value::extension_escape`).
    Extension(String),
    Set(Box<CType>),
    /// A record type: each attribute's type, and whether it is required. A
    /// closed record (every schema record is closed) admits no other attribute.
    Record {
        attrs: BTreeMap<String, (CType, bool)>,
        open: bool,
    },
    /// An entity of one of these types, by fully qualified name.
    Entity(Vec<String>),
    /// An entity of any type.
    AnyEntity,
    /// A type the schemas do not determine: every value is an instance.
    Any,
    /// The empty type: no value is an instance.
    Never,
}

impl CType {
    /// The type of a Cedar schema [`Type`].
    pub(crate) fn from_type(ty: &Type) -> CType {
        match ty {
            Type::Never => CType::Never,
            Type::Bool(_) => CType::Bool,
            Type::Long => CType::Long,
            Type::String => CType::String,
            Type::Set {
                element_type: Some(inner),
            } => CType::Set(Box::new(CType::from_type(inner))),
            Type::Set { element_type: None } => CType::Set(Box::new(CType::Any)),
            Type::Entity(EntityKind::Entity(lub)) => match lub.get_single_entity() {
                Some(ety) => CType::Entity(vec![ety.to_string()]),
                // A schema names one entity type per position; a least upper
                // bound of several only arises from type inference.
                None => CType::AnyEntity,
            },
            Type::Entity(EntityKind::AnyEntity) => CType::AnyEntity,
            Type::Record {
                attrs,
                open_attributes,
            } => CType::from_attributes(attrs, *open_attributes == OpenTag::OpenAttributes),
            Type::ExtensionType { name } => match name.basename().as_ref() {
                "decimal" => CType::Decimal,
                other => CType::Extension(other.to_string()),
            },
        }
    }

    fn from_attributes(attrs: &Attributes, open: bool) -> CType {
        CType::Record {
            attrs: attrs
                .iter()
                .map(|(k, a)| {
                    (
                        k.to_string(),
                        (CType::from_type(&a.attr_type), a.is_required()),
                    )
                })
                .collect(),
            open,
        }
    }

    /// The type an information provider's declaration gives its output, as the
    /// augmented schema types the hoisted `context.providers.<id>` field
    /// (`ParamType::to_cedar_type_with`): `names` maps a provider enum's
    /// declared name to the name it is exported under.
    pub(crate) fn from_param(ty: &ParamType, names: &BTreeMap<String, String>) -> CType {
        match ty.param_type.as_str() {
            "string" => CType::String,
            "integer" | "long" => CType::Long,
            "bool" | "boolean" => CType::Bool,
            "decimal" => CType::Decimal,
            "set" => CType::Set(Box::new(match ty.items.as_deref() {
                Some(items) => CType::from_param(items, names),
                None => CType::String,
            })),
            "record" => CType::Record {
                attrs: ty
                    .fields
                    .iter()
                    .map(|(name, field)| {
                        (
                            name.clone(),
                            (CType::from_param(field, names), ty.required.contains(name)),
                        )
                    })
                    .collect(),
                open: false,
            },
            "entity" => match ty.entity_type.as_deref() {
                Some(declared) => CType::Entity(vec![
                    names
                        .get(declared)
                        .cloned()
                        .unwrap_or_else(|| declared.to_string()),
                ]),
                None => CType::String,
            },
            // The deprecated fallback of `to_cedar_type_with`: an unknown kind
            // is typed `String`.
            _ => CType::String,
        }
    }

    /// The type the event schema names for a field in text (`String`, `Long`,
    /// `Set < String >`, an entity type), for an event of an action in the
    /// namespace `ns`. An entity type is resolved in the action's namespace
    /// first, then as written. A name the schema does not declare gives
    /// [`CType::Any`]: the event-schema derivation already accepted it.
    fn from_text(text: &str, ns: &[String], schema: &ValidatorSchema) -> CType {
        let t = text.trim();
        match t {
            "String" => CType::String,
            "Long" => CType::Long,
            "Bool" | "Boolean" => CType::Bool,
            "decimal" => CType::Decimal,
            "ipaddr" | "datetime" | "duration" => CType::Extension(t.to_string()),
            _ => {
                if let Some(inner) = t
                    .strip_prefix("Set")
                    .map(str::trim)
                    .and_then(|rest| rest.strip_prefix('<'))
                    .and_then(|rest| rest.strip_suffix('>'))
                {
                    return CType::Set(Box::new(CType::from_text(inner, ns, schema)));
                }
                match resolve_entity_type(t, ns, schema) {
                    Some(name) => CType::Entity(vec![name]),
                    None => CType::Any,
                }
            }
        }
    }

    /// The type rendered for a diagnostic.
    pub(crate) fn render(&self) -> String {
        match self {
            CType::Bool => "Bool".to_string(),
            CType::Long => "Long".to_string(),
            CType::String => "String".to_string(),
            CType::Decimal => "decimal".to_string(),
            CType::Extension(name) => name.clone(),
            CType::Set(inner) => format!("Set<{}>", inner.render()),
            CType::Record { attrs, .. } => {
                let attrs: Vec<String> = attrs
                    .iter()
                    .map(|(k, (t, required))| {
                        format!("{k}{}: {}", if *required { "" } else { "?" }, t.render())
                    })
                    .collect();
                format!("{{ {} }}", attrs.join(", "))
            }
            CType::Entity(names) => names.join(" | "),
            CType::AnyEntity => "an entity".to_string(),
            CType::Any => "any value".to_string(),
            CType::Never => "no value".to_string(),
        }
    }
}

/// An entity type named in the event schema or the action schema, resolved to
/// a declared type: qualified by the action's namespace `ns` (the action type
/// path, ending in `Action`), or as written.
fn resolve_entity_type(name: &str, ns: &[String], schema: &ValidatorSchema) -> Option<String> {
    let home = &ns[..ns.len().saturating_sub(1)];
    let qualified = if home.is_empty() {
        name.to_string()
    } else {
        format!("{}::{name}", home.join("::"))
    };
    [qualified, name.to_string()].into_iter().find(|candidate| {
        candidate
            .parse::<EntityType>()
            .is_ok_and(|ety| schema.get_entity_type(&ety).is_some())
    })
}

// ─── Values against types ────────────────────────────────────────────

/// How a value fails to be an instance of a type: the attribute path inside the
/// value where it fails (empty at the value itself), and the problem there.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct Mismatch {
    pub(crate) path: Vec<String>,
    pub(crate) problem: String,
}

impl Mismatch {
    fn at(problem: String) -> Self {
        Mismatch {
            path: Vec::new(),
            problem,
        }
    }

    fn inside(mut self, attr: &str) -> Self {
        self.path.insert(0, attr.to_string());
        self
    }

    /// The mismatch, phrased about `subject` (e.g. "the logged field
    /// `input`"), with the path inside it.
    pub(crate) fn describe(&self, subject: &str) -> String {
        if self.path.is_empty() {
            format!("{subject} {}", self.problem)
        } else {
            format!(
                "{subject}: `{}` {}",
                crate::field_path::join(&self.path),
                self.problem
            )
        }
    }
}

/// A short description of a value's kind, for diagnostics.
fn value_kind(value: &Value) -> String {
    match value {
        Value::Null => "no value".to_string(),
        Value::Bool(_) => "a Bool".to_string(),
        Value::Int(_) => "a Long".to_string(),
        Value::Decimal(text) => format!("the decimal text `{text}`"),
        Value::String(_) => "a String".to_string(),
        Value::Entity { ty, .. } => format!("an entity of type `{ty}`"),
        Value::Array(_) => "a set".to_string(),
        Value::Object(_) => match extension_escape(value) {
            Some((function, arg)) => format!("`{function}(\"{arg}\")`"),
            None => "a record".to_string(),
        },
    }
}

/// Whether `ty::"id"` is a valid entity uid of the schema: an entity of a
/// declared type, whose id is one of the type's ids when the type is an
/// enumeration, or a declared action (Cedar's `instanceOfEntityType`).
fn valid_entity(ty: &str, id: &str, schema: &ValidatorSchema) -> bool {
    let Ok(ety) = ty.parse::<EntityType>() else {
        return false;
    };
    match schema.get_entity_type(&ety) {
        Some(declared) => match &declared.kind {
            ValidatorEntityTypeKind::Enum(choices) => choices.iter().any(|c| c.as_ref() == id),
            // Cedar 4.14 admits any id of an `external` type in a request.
            ValidatorEntityTypeKind::Standard(_) | ValidatorEntityTypeKind::External => true,
        },
        None => schema
            .get_action_id(&EntityUID::from_components(ety, Eid::new(id), None))
            .is_some(),
    }
}

/// Check that `value` is an instance of `ty`, as Cedar's `instanceOfType`
/// decides it, with `Null` record attributes read as absent.
pub(crate) fn check_value(
    value: &Value,
    ty: &CType,
    schema: &ValidatorSchema,
) -> Result<(), Mismatch> {
    let mismatch = || {
        Mismatch::at(format!(
            "is {}, but its declared type is `{}`",
            value_kind(value),
            ty.render()
        ))
    };
    match (ty, value) {
        (CType::Any, _) => Ok(()),
        (_, Value::Null) => Err(mismatch()),
        (CType::Bool, Value::Bool(_))
        | (CType::Long, Value::Int(_))
        | (CType::String, Value::String(_)) => Ok(()),
        (CType::Decimal, Value::Decimal(text)) => {
            if cedar_decimal_value(text).is_some() {
                Ok(())
            } else {
                Err(Mismatch::at(format!(
                    "is the text `{text}`, which is not a `decimal` Cedar accepts"
                )))
            }
        }
        (CType::Extension(name), value) if let Some((function, arg)) = extension_escape(value) => {
            let (constructor, expr) = match name.as_str() {
                "ipaddr" => ("ip", RestrictedExpression::new_ip(arg)),
                "datetime" => ("datetime", RestrictedExpression::new_datetime(arg)),
                "duration" => ("duration", RestrictedExpression::new_duration(arg)),
                _ => return Err(mismatch()),
            };
            if function != constructor {
                return Err(mismatch());
            }
            // Cedar evaluates the constructor when it builds a context, which is
            // where an argument it does not accept is reported.
            match cedar_policy::Context::from_pairs([("value".to_string(), expr)]) {
                Ok(_) => Ok(()),
                Err(_) => Err(Mismatch::at(format!(
                    "is `{function}(\"{arg}\")`, which is not a `{name}` Cedar accepts"
                ))),
            }
        }
        (CType::Set(inner), Value::Array(items)) => {
            for (i, item) in items.iter().enumerate() {
                check_value(item, inner, schema).map_err(|m| m.inside(&format!("[{i}]")))?;
            }
            Ok(())
        }
        (CType::Record { attrs, open }, Value::Object(fields)) => {
            for (name, field) in fields {
                if matches!(field, Value::Null) {
                    continue;
                }
                match attrs.get(name) {
                    Some((field_ty, _)) => {
                        check_value(field, field_ty, schema).map_err(|m| m.inside(name))?
                    }
                    None if *open => {}
                    None => {
                        return Err(Mismatch::at(format!(
                            "has the attribute `{name}`, which its type `{}` does not declare",
                            ty.render()
                        )));
                    }
                }
            }
            for (name, (_, required)) in attrs {
                if *required && fields.get(name).is_none_or(|v| matches!(v, Value::Null)) {
                    return Err(Mismatch::at(format!(
                        "lacks the attribute `{name}`, which its type `{}` requires",
                        ty.render()
                    )));
                }
            }
            Ok(())
        }
        (CType::Entity(names), Value::Entity { ty: ety, id }) => {
            if !names.iter().any(|n| n == ety) {
                return Err(mismatch());
            }
            if valid_entity(ety, id, schema) {
                Ok(())
            } else {
                Err(Mismatch::at(format!(
                    "is the entity `{}`, which is not a valid entity of its type",
                    entity_uid_string(ety, id)
                )))
            }
        }
        (CType::AnyEntity, Value::Entity { ty: ety, id }) => {
            if valid_entity(ety, id, schema) {
                Ok(())
            } else {
                Err(Mismatch::at(format!(
                    "is the entity `{}`, which is not a valid entity of the schema",
                    entity_uid_string(ety, id)
                )))
            }
        }
        _ => Err(mismatch()),
    }
}

/// The value at a non-empty `path` of a record, descending records, with a
/// `Null` read as absent.
fn record_path<'a>(record: &'a BTreeMap<String, Value>, path: &[String]) -> Option<&'a Value> {
    let (head, rest) = path.split_first()?;
    let mut current = record.get(head)?;
    for segment in rest {
        match current {
            Value::Object(members) => current = members.get(segment)?,
            _ => return None,
        }
    }
    (!matches!(current, Value::Null)).then_some(current)
}

/// The pin clauses of event conformance, under the mirror rule `rule` (the
/// specification's `EventSignature.Admits.pinned` and `.mirrored`): every pinned
/// field is logged, and every logged field that mirrors the request holds the
/// request's value when the event carries one, and (strict, the
/// specification's rule) is absent when it does not. [`MirrorRule::Current`]
/// accepts a mirrored field when the event carries no request-side value for
/// it; [`MirrorRule::Unchecked`] checks no pin clause. The one implementation:
/// [`RuntimeChecks::event_nonconformance`], which every ingested event goes
/// through, and [`EventSignature::check_pins`] call it. `head` names the event.
fn pin_nonconformance(
    head: &str,
    event: &Event,
    pinned: &[Vec<String>],
    mirrors: &[(Vec<String>, MirrorSource)],
    rule: MirrorRule,
) -> Option<String> {
    if rule == MirrorRule::Unchecked {
        return None;
    }
    let data = event.data();
    for pinned in pinned {
        if record_path(&data.logged, pinned).is_none() {
            return Some(format!(
                "`{head}`: the pinned field `{}` is not logged",
                crate::field_path::join(pinned)
            ));
        }
    }
    for (field, source) in mirrors {
        let (request_side, what) = match source {
            MirrorSource::Principal => (
                event
                    .scope()
                    .principal
                    .as_ref()
                    .filter(|v| !matches!(v, Value::Null)),
                "the request's principal".to_string(),
            ),
            MirrorSource::Resource => (
                event
                    .scope()
                    .resource
                    .as_ref()
                    .filter(|v| !matches!(v, Value::Null)),
                "the request's resource".to_string(),
            ),
            MirrorSource::Context(path) => (
                record_path(&data.request_context, path),
                format!(
                    "the request's `{}`",
                    crate::field_path::join_under("context", path)
                ),
            ),
        };
        let field_name = crate::field_path::join(field);
        match (request_side, record_path(&data.logged, field)) {
            (Some(expected), Some(logged)) if logged.dom_eq(expected) => {}
            (Some(expected), Some(logged)) => {
                return Some(format!(
                    "`{head}` logs `{field_name}` as {}, but {what} is {}",
                    render_value(logged),
                    render_value(expected)
                ));
            }
            (Some(expected), None) => {
                return Some(format!(
                    "`{head}` does not log `{field_name}`, which must hold {what}, {}",
                    render_value(expected)
                ));
            }
            (None, Some(logged)) if rule == MirrorRule::Strict => {
                return Some(format!(
                    "`{head}` logs `{field_name}` as {}, but has no value for {what} for it to \
                     mirror: an event that reports on a key must carry that key's scope",
                    render_value(logged)
                ));
            }
            (None, _) => {}
        }
    }
    None
}

// ─── The checks of one policy set ────────────────────────────────────

/// One declared field of an event signature.
#[derive(Debug, Clone)]
struct FieldCheck {
    path: Vec<String>,
    ty: CType,
    required: bool,
}

/// Where the request-side value a mirrored field must hold comes from.
#[derive(Debug, Clone)]
enum MirrorSource {
    Principal,
    Resource,
    Context(Vec<String>),
}

/// Where a pin's request-side value comes from, if the pin is symmetric. It is
/// the request's principal (`target` is `["principal"]` under a scope root),
/// its resource (`["resource"]`), or the context attribute at `target` (under a
/// context root). `None` for a pin to an attribute of the principal or
/// resource (`["principal", "dept"]`), which is not symmetric. The pinned
/// field's name plays no part.
fn mirror_source(scope_root: bool, target: &[String]) -> Option<MirrorSource> {
    if !scope_root {
        return Some(MirrorSource::Context(target.to_vec()));
    }
    match target {
        [root] if root == "principal" => Some(MirrorSource::Principal),
        [root] if root == "resource" => Some(MirrorSource::Resource),
        _ => None,
    }
}

/// The caller fields, which mirror the request's principal and resource when
/// the signature declares them and no pin names them. The event builder fills
/// them from the request's scope.
fn caller_fields() -> [(Vec<String>, MirrorSource); 2] {
    [
        (vec!["callerPrincipal".to_string()], MirrorSource::Principal),
        (vec!["callerResource".to_string()], MirrorSource::Resource),
    ]
}

/// The checks of one derived event signature.
#[derive(Debug, Clone)]
struct SignatureCheck {
    fields: Vec<FieldCheck>,
    /// The paths of the pinned fields, which every event must log.
    pinned: Vec<Vec<String>>,
    /// The logged fields that mirror the request, and where their value comes
    /// from.
    mirrors: Vec<(Vec<String>, MirrorSource)>,
}

/// The checks of one declared action's requests.
#[derive(Debug, Clone)]
struct ActionCheck {
    principals: Vec<String>,
    resources: Vec<String>,
    /// The action's context record type, without the hoisted attributes;
    /// `None` for an `external` action, for which no request is valid.
    context: Option<CType>,
}

/// The runtime conformance checks of a lowered policy set, built once per set
/// ([`RuntimeChecksCache`]).
#[derive(Debug, Clone)]
pub(crate) struct RuntimeChecks {
    schema: ValidatorSchema,
    /// Keyed by `(action namespace, action id, kind)`.
    signatures: BTreeMap<(Vec<String>, String, String), SignatureCheck>,
    /// Keyed by `(action namespace, action id)`.
    actions: BTreeMap<(Vec<String>, String), ActionCheck>,
    /// The declared output type of each hoisted provider field, by id; `None`
    /// when the provider, or the last method of its chain, is undeclared.
    provider_types: BTreeMap<String, Option<CType>>,
}

/// The [`RuntimeChecks`] of one lowered policy set, built on first use and kept
/// with the set: every clone of the [`LoweredPolicySet`](crate::LoweredPolicySet),
/// every [`Authorizer`](crate::Authorizer) built from it, and
/// [`LoweredPolicySet::check_event_conformance`](crate::LoweredPolicySet::check_event_conformance)
/// use the one set of checks, so building them (which clones the validator
/// schema) happens once per set.
#[derive(Default)]
pub(crate) struct RuntimeChecksCache(std::sync::OnceLock<RuntimeChecks>);

impl RuntimeChecksCache {
    /// The checks of `lowered`, the set this cache belongs to, built on the
    /// first call.
    pub(crate) fn get_or_build(&self, lowered: &Lowered) -> &RuntimeChecks {
        self.0.get_or_init(|| RuntimeChecks::new(lowered))
    }
}

// The checks are derived from the rest of the lowered set and hold a copy of
// its schema, so `Debug` names the cache without printing them; the output is
// the same whether or not they have been built.
impl std::fmt::Debug for RuntimeChecksCache {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str("RuntimeChecksCache")
    }
}

impl RuntimeChecks {
    pub(crate) fn new(lowered: &Lowered) -> Self {
        let schema: ValidatorSchema = lowered.augmented_schema.as_ref().clone();

        // The attributes lowering hoists into every context: the decision
        // supplies them, so a request context is checked without them.
        let mut hoisted: BTreeSet<String> = lowered.temporal.iter().map(|f| f.id.clone()).collect();
        if !lowered.providers.is_empty() {
            hoisted.insert("providers".to_string());
        }

        let mut actions = BTreeMap::new();
        for action in schema.action_ids() {
            let name = action.name();
            let namespace: Vec<String> = name
                .entity_type()
                .to_string()
                .split("::")
                .map(str::to_string)
                .collect();
            let context = action.context_type().map(|ty| match CType::from_type(ty) {
                CType::Record { mut attrs, open } => {
                    attrs.retain(|k, _| !hoisted.contains(k));
                    CType::Record { attrs, open }
                }
                other => other,
            });
            actions.insert(
                (namespace, name.eid().as_ref().to_string()),
                ActionCheck {
                    principals: action
                        .applies_to_principals()
                        .map(ToString::to_string)
                        .collect(),
                    resources: action
                        .applies_to_resources()
                        .map(ToString::to_string)
                        .collect(),
                    context,
                },
            );
        }

        let mut signatures = BTreeMap::new();
        for event in &lowered.event_schema.events {
            signatures.insert(
                (
                    event.namespace.clone(),
                    event.action.clone(),
                    event.kind.clone(),
                ),
                signature_check(event, &schema),
            );
        }

        let provider_types = lowered
            .providers
            .iter()
            .map(|field| {
                let ty = field.declaration.as_ref().and_then(|decl| {
                    let declared = match field.methods.last() {
                        Some(last) => &decl.methods.get(&last.name)?.output_type,
                        None => &decl.output_type,
                    };
                    Some(CType::from_param(declared, &field.entity_type_names))
                });
                (field.id.clone(), ty)
            })
            .collect();

        RuntimeChecks {
            schema,
            signatures,
            actions,
            provider_types,
        }
    }

    /// Why `event` does not conform to the event schema, if it does not
    /// (`Event.Conforms`). Its pin clauses (every pinned field is logged, every
    /// mirrored field holds the request's value) are checked unless `mirror`
    /// is [`MirrorRule::Unchecked`], which ingests every event as
    /// Dogwood_Language 1.1 did; the strict rule's extra case is
    /// [`EventSignature::check_pins`]'s.
    pub(crate) fn event_nonconformance(&self, event: &Event, mirror: MirrorRule) -> Option<String> {
        let data = event.data();
        let head = event_head(data);
        let Some(sig) = self.signatures.get(&(
            data.namespace.clone(),
            data.action.clone(),
            data.kind.clone(),
        )) else {
            return Some(format!("the event schema declares no event `{head}`"));
        };
        for field in &sig.fields {
            let path = crate::field_path::join(&field.path);
            match record_path(&data.logged, &field.path) {
                Some(value) => {
                    if let Err(m) = check_value(value, &field.ty, &self.schema) {
                        return Some(
                            m.describe(&format!("`{head}` logs the field `{path}`, which")),
                        );
                    }
                }
                None if field.required => {
                    return Some(format!(
                        "`{head}` does not log the field `{path}`, which its signature requires"
                    ));
                }
                None => {}
            }
        }
        pin_nonconformance(&head, event, &sig.pinned, &sig.mirrors, mirror)
    }

    /// Why the request of the decision event `event`, whose principal and
    /// resource are present, does not conform to the action schema, if it does
    /// not (Cedar's `validateRequest`).
    pub(crate) fn request_nonconformance(&self, event: &Event) -> Option<String> {
        let data = event.data();
        let action = action_display(data);
        let Some(check) = self
            .actions
            .get(&(data.namespace.clone(), data.action.clone()))
        else {
            return Some(format!("the action schema declares no action `{action}`"));
        };
        // Cedar's `validateRequest` rejects an `external` action before its scope.
        let Some(context_ty) = &check.context else {
            return Some(format!(
                "the action schema declares `{action}` `external`, so no request is valid for it"
            ));
        };
        for (root, value, admitted) in [
            (
                "principal",
                event.scope().principal.as_ref(),
                &check.principals,
            ),
            (
                "resource",
                event.scope().resource.as_ref(),
                &check.resources,
            ),
        ] {
            let Some(Value::Entity { ty, id }) = value else {
                return Some(format!("the request's {root} is not an entity"));
            };
            if !admitted.iter().any(|t| t == ty) {
                return Some(format!(
                    "`{action}` does not apply to a {root} of type `{ty}` (it applies to `{}`)",
                    admitted.join("`, `")
                ));
            }
            if !valid_entity(ty, id, &self.schema) {
                return Some(format!(
                    "the request's {root} `{}` is not a valid entity of its type",
                    entity_uid_string(ty, id)
                ));
            }
        }
        let context = Value::Object(data.request_context.clone());
        match check_value(&context, context_ty, &self.schema) {
            Ok(()) => None,
            Err(m) => Some(m.describe(&format!("the context of `{action}`"))),
        }
    }

    /// Why the output `value` of the hoisted provider field `id` is not a value
    /// of its declared type, if it is not (`Provider.Output.Conforms`).
    pub(crate) fn provider_output_nonconformance(
        &self,
        id: &str,
        key: &str,
        value: &Value,
    ) -> Option<String> {
        match self.provider_types.get(id) {
            Some(Some(ty)) => check_value(value, ty, &self.schema)
                .err()
                .map(|m| m.describe(&format!("the output of `{key}`"))),
            // An output without a declared type has no conforming value.
            Some(None) | None => Some(format!(
                "`{key}` has no declared output type, so its output cannot be checked"
            )),
        }
    }
}

/// The declared leaf fields of a derived event signature, each with its type
/// and whether every event of the signature must log it, against the augmented
/// schema. A field spliced from the action's `context.input` or
/// `context.output` record has the type the context declares at its path, and
/// is required when every attribute along the path is; any other field has the
/// type the event schema names, and is optional.
pub(crate) fn event_fields(
    event: &DerivedEvent,
    schema: &ValidatorSchema,
) -> Vec<(Vec<String>, CType, bool)> {
    let action_uid = event
        .namespace
        .join("::")
        .parse::<EntityType>()
        .ok()
        .map(|ety| EntityUID::from_components(ety, Eid::new(event.action.as_str()), None));
    let context = action_uid
        .as_ref()
        .and_then(|uid| schema.get_action_id(uid))
        .and_then(|action| action.context_type());
    let context_attrs = match context {
        Some(Type::Record { attrs, .. }) => Some(attrs),
        _ => None,
    };
    event
        .leaf_fields()
        .into_iter()
        .map(|(path, ty)| {
            let spliced = matches!(path.first().map(String::as_str), Some("input" | "output"));
            match (spliced, context_attrs.and_then(|a| path_type(a, &path))) {
                (true, Some((ty, required))) => (path, CType::from_type(ty), required),
                _ => {
                    let ty = match &ty {
                        FieldType::Cedar(text) => CType::from_text(text, &event.namespace, schema),
                        FieldType::EntityTypes(names) => CType::Entity(
                            names
                                .iter()
                                .filter_map(|n| resolve_entity_type(n, &event.namespace, schema))
                                .collect(),
                        ),
                    };
                    (path, ty, false)
                }
            }
        })
        .collect()
}

/// The checks of one derived event signature, against the augmented schema.
fn signature_check(event: &DerivedEvent, schema: &ValidatorSchema) -> SignatureCheck {
    let fields = event_fields(event, schema)
        .into_iter()
        .map(|(path, ty, required)| FieldCheck { path, ty, required })
        .collect::<Vec<_>>();
    let declared: BTreeSet<&[String]> = fields.iter().map(|f| f.path.as_slice()).collect();
    let pinned: Vec<Vec<String>> = event.pins.iter().map(|p| p.field_path.clone()).collect();
    let mut mirrors: Vec<(Vec<String>, MirrorSource)> = event
        .pins
        .iter()
        .filter_map(|pin| {
            mirror_source(pin.root == PinRoot::Scope, &pin.context_path)
                .map(|source| (pin.field_path.clone(), source))
        })
        .collect();
    for (path, source) in caller_fields() {
        if declared.contains(path.as_slice()) && !pinned.contains(&path) {
            mirrors.push((path, source));
        }
    }

    SignatureCheck {
        fields,
        pinned,
        mirrors,
    }
}

/// The type at `path` in a record type, and whether every attribute along the
/// path is required.
fn path_type<'a>(mut attrs: &'a Attributes, path: &[String]) -> Option<(&'a Type, bool)> {
    let (last, init) = path.split_last()?;
    let mut required = true;
    for segment in init {
        let attr = attrs.get_attr(segment)?;
        required &= attr.is_required();
        match attr.attr_type.as_ref() {
            Type::Record { attrs: inner, .. } => attrs = inner,
            _ => return None,
        }
    }
    let attr = attrs.get_attr(last)?;
    Some((attr.attr_type.as_ref(), required && attr.is_required()))
}

/// `Ns::Action::"Id"::kind`, for diagnostics.
fn event_head(data: &EventData) -> String {
    format!("{}::{}", action_display(data), data.kind)
}

/// `Ns::Action::"Id"`, for diagnostics.
fn action_display(data: &EventData) -> String {
    crate::api::qualified_action_uid(&data.namespace, &data.action)
}

/// A value, rendered for a diagnostic.
fn render_value(value: &Value) -> String {
    match value {
        Value::Entity { ty, id } => format!("`{}`", entity_uid_string(ty, id)),
        Value::String(s) => format!("`{s:?}`"),
        Value::Int(n) => format!("`{n}`"),
        Value::Decimal(d) => format!("`{d}`"),
        Value::Bool(b) => format!("`{b}`"),
        other => value_kind(other),
    }
}

// ─── The pin rules: the mirror rule and the rejection ────────────────
/// Which form of the **mirror rule** an [`Authorizer`](crate::Authorizer)
/// checks before it ingests an event.
///
/// A logged field that *mirrors* the request must hold the request's value.
/// The mirrored fields are the fields of the symmetric pins (see
/// [`EventPin::is_symmetric`](crate::api::EventPin::is_symmetric)), and
/// `callerPrincipal` / `callerResource` when the signature declares them and no
/// pin names them. This is what lets a pin isolate a key: an event cannot log
/// one principal as its caller while it carries another, or none. Every pinned
/// field must also be logged. The specification states the rule as `Mirrored`,
/// checked by `Event.Conforms` before an event is logged (`dogwood-lean`,
/// `Dogwood.Spec.Conformance`).
///
/// Under the default, [`Strict`](MirrorRule::Strict), **an event that reports on
/// a key must carry that key's scope**. With the default event schema (the
/// universal pin `callerPrincipal = principal`), a history event logs its
/// caller and carries the same principal; one that logs a caller and carries no
/// principal is rejected (semantics review F1.4). A `null` is absent on both
/// sides.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default, Hash)]
#[non_exhaustive]
pub enum MirrorRule {
    /// The specification's strict rule (the default): a mirrored field holds
    /// the request's value when the request side resolves, and is absent when
    /// it does not. Every pinned field must be logged.
    #[default]
    Strict,
    /// The earlier rule: a mirrored field holds the request's value when the
    /// request side resolves; when it does not, any logged value is accepted.
    /// Every pinned field must be logged. Leaves forged history open under a
    /// pin that is not universal (semantics review F1.2).
    Current,
    /// No pin check at all: every event is ingested, as Dogwood_Language 1.1
    /// did.
    Unchecked,
}

impl MirrorRule {
    /// The rule's name as an option value: `strict`, `current`, or `unchecked`.
    pub fn as_str(self) -> &'static str {
        match self {
            MirrorRule::Strict => "strict",
            MirrorRule::Current => "current",
            MirrorRule::Unchecked => "unchecked",
        }
    }
}

impl std::fmt::Display for MirrorRule {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(self.as_str())
    }
}

impl std::str::FromStr for MirrorRule {
    type Err = String;

    /// Parse `strict`, `current`, or `unchecked` (the [`as_str`](Self::as_str)
    /// names).
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        match s {
            "strict" => Ok(MirrorRule::Strict),
            "current" => Ok(MirrorRule::Current),
            "unchecked" | "off" => Ok(MirrorRule::Unchecked),
            other => Err(format!(
                "unknown mirror rule `{other}` (expected strict, current or unchecked)"
            )),
        }
    }
}

/// Why an event was rejected at ingestion, returned by
/// [`Authorizer::submit`](crate::Authorizer::submit),
/// [`LoweredPolicySet::check_event`](crate::LoweredPolicySet::check_event) and
/// [`EventSignature::check_pins`].
///
/// A rejected event is not ingested: the temporal engine never observes it, so
/// no later decision sees it. It is not a decision either, in particular not a
/// `Deny`. The specification states the rule as ingestion's
/// `Rejection.nonconforming` (`dogwood-lean`, `Dogwood.Spec.Ingest`): a logged
/// event is history for every later decision, so checking it once, at
/// ingestion, is what keeps a badly logged event from failing every later
/// decision closed, or from being silently dropped as a `forbid`'s evidence. A
/// decision event that does not conform is not ingested, and its decision
/// fails closed.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub enum Rejection {
    /// The event does not conform to the event schema: the schema declares no
    /// event of its action and kind, or its logged record is not an instance
    /// of the event's signature (a declared field of the wrong type, a
    /// required or pinned field not logged, or a field that mirrors the
    /// request and holds another value, or, under the strict mirror rule, is
    /// logged by an event without a request-side value for it).
    Nonconforming {
        /// What does not conform.
        reason: String,
    },
    /// The temporal engine did not record the event, or cannot say that it did
    /// ([`TemporalEngine::try_observe`](crate::TemporalEngine::try_observe)
    /// failed): no later decision can rely on it. The specification's
    /// `Rejection.unavailable`. When the reason says the outcome of the write is
    /// unknown (an ambiguous commit), the event may be in the history after all.
    Unavailable {
        /// Why the engine did not record it.
        reason: String,
    },
}

impl std::fmt::Display for Rejection {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Rejection::Nonconforming { reason } => write!(f, "nonconforming event: {reason}"),
            Rejection::Unavailable { reason } => write!(f, "event not recorded: {reason}"),
        }
    }
}

impl std::error::Error for Rejection {}

impl EventSignature {
    /// The logged fields of an event of this signature that mirror its
    /// request, with where each one's value comes from: the fields of its
    /// symmetric pins, and `callerPrincipal` / `callerResource` when the
    /// signature declares them and no pin names them (the specification's
    /// `EventSignature.mirrors`).
    fn mirrors(&self) -> Vec<(Vec<String>, MirrorSource)> {
        let mut out: Vec<(Vec<String>, MirrorSource)> = self
            .pins
            .iter()
            .filter_map(|pin| {
                mirror_source(pin.root == EventPinRoot::Scope, &pin.target_path)
                    .map(|source| (pin.field_path.clone(), source))
            })
            .collect();
        for (path, source) in caller_fields() {
            if self.fields.iter().any(|f| f.path == path)
                && !self.pins.iter().any(|p| p.field_path == path)
            {
                out.push((path, source));
            }
        }
        out
    }

    /// Check `event`, an event of this signature, against the signature's pin
    /// rules: every pinned field is logged, and every mirrored field obeys
    /// `rule` (see [`MirrorRule`]). A logged or request-side `null` is absent.
    /// [`MirrorRule::Unchecked`] accepts every event. These are the pin clauses
    /// of the one conformance check every ingested event goes through (the
    /// authorizer's also checks the fields' types and the required fields).
    ///
    /// The event's action and kind are not checked against the signature; use
    /// [`LoweredPolicySet::check_event`](crate::LoweredPolicySet::check_event)
    /// to look the signature up.
    pub fn check_pins(&self, event: &Event, rule: MirrorRule) -> Result<(), Rejection> {
        let pinned: Vec<Vec<String>> = self.pins.iter().map(|p| p.field_path.clone()).collect();
        match pin_nonconformance(
            &event_head(event.data()),
            event,
            &pinned,
            &self.mirrors(),
            rule,
        ) {
            Some(reason) => Err(Rejection::Nonconforming { reason }),
            None => Ok(()),
        }
    }
}

impl crate::api::EventPin {
    /// Whether the pin is symmetric, that is, pinned to the request's
    /// principal, its resource, or a context attribute (`pin f = principal`,
    /// `pin f = resource`, `pin f = context.<path>`), whatever the pinned field
    /// is called. A pin to an attribute of the principal or resource
    /// (`pin dept = principal.dept`) is not symmetric.
    pub fn is_symmetric(&self) -> bool {
        mirror_source(self.root == EventPinRoot::Scope, &self.target_path).is_some()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn schema() -> ValidatorSchema {
        let src = r#"
            namespace Drupe {
              entity OAuthUser = { id: String };
              entity Gateway;
              entity Level enum ["low", "high"];
              action "Read" appliesTo {
                principal: [OAuthUser],
                resource: [Gateway],
                context: { input: { user: String, note?: String } }
              };
            }
        "#;
        let (schema, _) = cedar_policy::Schema::from_cedarschema_str(src).expect("schema");
        schema.as_ref().clone()
    }

    fn record(pairs: &[(&str, Value)]) -> Value {
        Value::Object(
            pairs
                .iter()
                .map(|(k, v)| (k.to_string(), v.clone()))
                .collect(),
        )
    }

    fn input_type() -> CType {
        CType::Record {
            attrs: BTreeMap::from([
                ("user".to_string(), (CType::String, true)),
                ("note".to_string(), (CType::String, false)),
            ]),
            open: false,
        }
    }

    #[test]
    fn a_record_needs_its_required_attributes_and_no_others() {
        let s = schema();
        let ty = input_type();
        assert!(check_value(&record(&[("user", Value::String("a".into()))]), &ty, &s).is_ok());
        let missing = check_value(&record(&[("note", Value::String("n".into()))]), &ty, &s);
        assert!(
            missing
                .unwrap_err()
                .problem
                .contains("lacks the attribute `user`")
        );
        let extra = check_value(
            &record(&[("user", Value::String("a".into())), ("x", Value::Int(1))]),
            &ty,
            &s,
        );
        assert!(extra.unwrap_err().problem.contains("has the attribute `x`"));
    }

    #[test]
    fn a_null_attribute_is_absent() {
        let s = schema();
        let ty = input_type();
        let value = record(&[("user", Value::String("a".into())), ("note", Value::Null)]);
        assert!(check_value(&value, &ty, &s).is_ok());
        let value = record(&[("user", Value::Null)]);
        assert!(check_value(&value, &ty, &s).is_err());
    }

    #[test]
    fn a_wrong_type_is_reported_at_its_path() {
        let s = schema();
        let err = check_value(&record(&[("user", Value::Int(3))]), &input_type(), &s).unwrap_err();
        assert_eq!(err.path, vec!["user".to_string()]);
        assert!(err.problem.contains("is a Long"));
    }

    #[test]
    fn decimals_must_be_text_cedar_accepts() {
        let s = schema();
        assert!(check_value(&Value::Decimal("1.5".into()), &CType::Decimal, &s).is_ok());
        assert!(check_value(&Value::Decimal("1".into()), &CType::Decimal, &s).is_err());
        assert!(check_value(&Value::Int(1), &CType::Decimal, &s).is_err());
    }

    #[test]
    fn entities_must_be_of_a_listed_type_and_valid() {
        let s = schema();
        let user = Value::Entity {
            ty: "Drupe::OAuthUser".into(),
            id: "alice".into(),
        };
        let ty = CType::Entity(vec!["Drupe::OAuthUser".into()]);
        assert!(check_value(&user, &ty, &s).is_ok());
        let gw = CType::Entity(vec!["Drupe::Gateway".into()]);
        assert!(check_value(&user, &gw, &s).is_err());
        let level = CType::Entity(vec!["Drupe::Level".into()]);
        let high = Value::Entity {
            ty: "Drupe::Level".into(),
            id: "high".into(),
        };
        let bad = Value::Entity {
            ty: "Drupe::Level".into(),
            id: "medium".into(),
        };
        assert!(check_value(&high, &level, &s).is_ok());
        assert!(check_value(&bad, &level, &s).is_err());
    }

    #[test]
    fn extension_values_are_cedar_escapes_cedar_accepts() {
        let s = schema();
        let ty = CType::Extension("datetime".into());
        let now = Value::extension("datetime", "2024-01-01T00:00:00Z");
        assert!(check_value(&now, &ty, &s).is_ok());
        let bad = Value::extension("datetime", "yesterday");
        assert!(
            check_value(&bad, &ty, &s)
                .unwrap_err()
                .problem
                .contains("Cedar accepts")
        );
        let ip = Value::extension("ip", "10.0.0.1");
        assert!(
            check_value(&ip, &ty, &s).is_err(),
            "an `ipaddr` is not a `datetime`"
        );
        assert!(check_value(&ip, &CType::Extension("ipaddr".into()), &s).is_ok());
        assert!(check_value(&Value::String("2024-01-01T00:00:00Z".into()), &ty, &s).is_err());
    }

    #[test]
    fn provider_types_follow_the_augmented_schema() {
        let mut names = BTreeMap::new();
        names.insert(
            "Vendor::Severity".to_string(),
            "Drupe::Vendor_Severity".to_string(),
        );
        let decl: ParamType = serde_json::from_str(
            r#"{"paramType": "record", "required": ["level"],
                "fields": {"level": {"paramType": "entity", "entityType": "Vendor::Severity"},
                           "tags": {"paramType": "set"}}}"#,
        )
        .expect("param type");
        assert_eq!(
            CType::from_param(&decl, &names),
            CType::Record {
                attrs: BTreeMap::from([
                    (
                        "level".to_string(),
                        (CType::Entity(vec!["Drupe::Vendor_Severity".into()]), true)
                    ),
                    (
                        "tags".to_string(),
                        (CType::Set(Box::new(CType::String)), false)
                    ),
                ]),
                open: false,
            }
        );
    }
}
