//! The typed event signatures of the formal specification (`dogwood-lean`,
//! `Dogwood.Spec.EventSchema`): each declared leaf field of an event signature with
//! the Cedar type the specification gives it and whether every event of the
//! signature must log it, and the action schema's entity types and actions, as the
//! specification's `Cedar.Validation.Schema` holds them.
//!
//! These are computed exactly as the specification's conformance bridge computes
//! them (`dogwood-lean/bridge/src/schema.rs`: `signature`, `path_type`, `text_type`,
//! `resolve_entity_type`, `ty`, `action_schema`), from the Cedar schema the policy
//! set was lowered against ([`LoweredPolicySet::cedar_schema`](crate::LoweredPolicySet::cedar_schema)):
//!
//! * a field of the spliced `input` / `output` group has the type the action's
//!   context declares at its path (resolved by Cedar: common types, namespaces), and
//!   is required when every attribute along the path is required;
//! * a `principalType(A)` / `resourceType(A)` field admits entities of the listed
//!   types, each resolved in the action's namespace first, then as written;
//! * any other field has the type the event schema names (`String`, `Long`, `Bool`,
//!   `Boolean`, `decimal`, `ipaddr`, `datetime`, `duration`, `Set<…>`, or a declared
//!   entity type by its full name);
//! * only a spliced field can be required (a pinned field must be logged all the same,
//!   the specification's `EventSignature.Admits.pinned`).
//!
//! A type the specification cannot represent (an open record, a singleton boolean
//! type, a name the schema does not declare) is an `Err` with the reason: the
//! bridge rejects the bundle there.
//!
//! Additive.

use cedar_policy_core::validator::types::{Attributes, BoolType, EntityKind, OpenTag, Type};
use cedar_policy_core::validator::{ValidatorEntityTypeKind, ValidatorSchema};

use crate::api::{EventFieldType, EventSignature};

/// A Cedar type, as the specification's `Cedar.Validation.CedarType` (with Cedar's
/// boolean type always `AnyBool`).
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SpecCedarType {
    Bool,
    Long,
    String,
    /// An extension type, by name: `decimal`, `ipaddr`, `datetime`, `duration`.
    Extension(String),
    Set(Box<SpecCedarType>),
    /// A closed record type: each attribute, its type, and whether it is required.
    Record(Vec<(String, SpecCedarType, bool)>),
    /// An entity type, by its full name (`Ns::Type`).
    Entity(String),
}

/// A field type, as the specification's `FieldTy`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SpecFieldType {
    /// A value of a Cedar type (`FieldTy.cedar`).
    Cedar(SpecCedarType),
    /// An entity of one of these types, by full name (`FieldTy.entities`).
    EntityTypes(Vec<String>),
}

/// A declared leaf field, as the specification's `FieldDecl`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SpecField {
    /// The field's path (`input.user` is `["input", "user"]`).
    pub path: Vec<String>,
    /// Its type, or why the specification cannot represent it.
    pub ty: Result<SpecFieldType, String>,
    /// Whether every event of the signature must log it.
    pub required: bool,
}

/// An entity type of the schema: its full name, and its ids when it is an enumeration.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SpecEntityType {
    pub name: String,
    pub enum_ids: Option<Vec<String>>,
}

/// The action schema's entity types and actions (`Cedar.Validation.Schema`'s `ets`
/// and the uids of its `acts`), as `(type, id)`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SpecEntities {
    pub entity_types: Vec<SpecEntityType>,
    pub actions: Vec<(String, String)>,
}

/// A validator type, as a [`SpecCedarType`] (the bridge's `ty`).
fn spec_type(t: &Type) -> Result<SpecCedarType, String> {
    Ok(match t {
        Type::Bool(BoolType::AnyBool) => SpecCedarType::Bool,
        Type::Bool(b) => return Err(format!("singleton boolean type {b:?} in a schema")),
        Type::Long => SpecCedarType::Long,
        Type::String => SpecCedarType::String,
        Type::Set {
            element_type: Some(e),
        } => SpecCedarType::Set(Box::new(spec_type(e)?)),
        Type::Set { element_type: None } => return Err("a set type without an element type".into()),
        Type::Entity(EntityKind::Entity(lub)) => match lub.get_single_entity() {
            Some(e) => SpecCedarType::Entity(e.to_string()),
            None => return Err("a non-singleton entity type in a schema".into()),
        },
        Type::Entity(EntityKind::AnyEntity) => return Err("the any-entity type in a schema".into()),
        Type::Record {
            attrs,
            open_attributes,
        } => {
            if *open_attributes != OpenTag::ClosedAttributes {
                return Err("an open record type in a schema".into());
            }
            let mut out = Vec::new();
            for (k, a) in attrs.iter() {
                out.push((k.to_string(), spec_type(&a.attr_type)?, a.is_required()));
            }
            SpecCedarType::Record(out)
        }
        Type::ExtensionType { name } => SpecCedarType::Extension(name.to_string()),
        Type::Never => return Err("the never type in a schema".into()),
    })
}

/// The type at `path` in a record type, and whether every attribute along the path is
/// required (the bridge's `path_type`).
fn path_type<'a>(mut attrs: &'a Attributes, path: &[String]) -> Option<(&'a Type, bool)> {
    let mut required = true;
    let (last, init) = path.split_last()?;
    for seg in init {
        let a = attrs.get_attr(seg)?;
        required &= a.is_required();
        match a.attr_type.as_ref() {
            Type::Record { attrs: inner, .. } => attrs = inner,
            _ => return None,
        }
    }
    let a = attrs.get_attr(last)?;
    Some((a.attr_type.as_ref(), required && a.is_required()))
}

/// A field type the event schema declares in text, as a Cedar type (the bridge's
/// `text_type`).
fn text_type(text: &str, schema: &ValidatorSchema) -> Result<SpecCedarType, String> {
    let t = text.trim();
    Ok(match t {
        "String" => SpecCedarType::String,
        "Long" => SpecCedarType::Long,
        "Bool" | "Boolean" => SpecCedarType::Bool,
        "decimal" | "ipaddr" | "datetime" | "duration" => SpecCedarType::Extension(t.to_string()),
        _ => {
            if let Some(inner) = t
                .strip_prefix("Set")
                .map(str::trim)
                .and_then(|r| r.strip_prefix('<'))
            {
                let inner = inner
                    .strip_suffix('>')
                    .ok_or_else(|| format!("field type `{t}`"))?;
                return Ok(SpecCedarType::Set(Box::new(text_type(inner, schema)?)));
            }
            match schema.entity_types().find(|e| e.name().to_string() == t) {
                Some(e) => SpecCedarType::Entity(e.name().to_string()),
                None => return Err(format!("field type `{t}`")),
            }
        }
    })
}

/// An entity type the event schema names, resolved against the action schema: in the
/// namespace of the event's action first, then as written (the bridge's
/// `resolve_entity_type`).
fn resolve_entity_type(
    name: &str,
    namespace: &[String],
    schema: &ValidatorSchema,
) -> Result<String, String> {
    let ns = &namespace[..namespace.len().saturating_sub(1)];
    let qualified = if ns.is_empty() {
        name.to_string()
    } else {
        format!("{}::{name}", ns.join("::"))
    };
    schema
        .entity_types()
        .find(|e| e.name().to_string() == qualified)
        .or_else(|| schema.entity_types().find(|e| e.name().to_string() == name))
        .map(|e| e.name().to_string())
        .ok_or_else(|| format!("entity type `{name}` of an event field"))
}

impl EventSignature {
    /// The signature's fields as the specification types them (the specification's
    /// conformance bridge's `signature`: see [`SpecField`]), against the Cedar schema the
    /// policy set was lowered against. Additive.
    pub fn spec_fields(&self, schema: &cedar_policy::Schema) -> Vec<SpecField> {
        let schema: &ValidatorSchema = schema.as_ref();
        let context = schema
            .action_ids()
            .find(|a| {
                let name = a.name();
                name.eid().as_ref() == self.action
                    && name.entity_type().to_string() == self.namespace.join("::")
            })
            .and_then(|a| a.context_type());
        let context_attrs = match context {
            Some(Type::Record { attrs, .. }) => Some(attrs),
            _ => None,
        };
        let mut out = Vec::new();
        for f in &self.fields {
            let path = f.path();
            let spliced = matches!(path.first().map(String::as_str), Some("input" | "output"));
            let (ty, required) = match (spliced, context_attrs.and_then(|a| path_type(a, path))) {
                (true, Some((t, required))) => (spec_type(t).map(SpecFieldType::Cedar), required),
                _ => match f.field_type() {
                    EventFieldType::EntityTypes(names) => (
                        names
                            .iter()
                            .map(|n| resolve_entity_type(n, &self.namespace, schema))
                            .collect::<Result<Vec<_>, _>>()
                            .map(SpecFieldType::EntityTypes),
                        false,
                    ),
                    EventFieldType::Cedar(text) => {
                        (text_type(text, schema).map(SpecFieldType::Cedar), false)
                    }
                },
            };
            out.push(SpecField {
                path: path.to_vec(),
                ty,
                required,
            });
        }
        out
    }
}

/// The action schema's entity types (with an enumeration's ids) and actions, as the
/// specification's schema holds them (the bridge's `action_schema`). Additive.
pub fn spec_entities(schema: &cedar_policy::Schema) -> SpecEntities {
    let schema: &ValidatorSchema = schema.as_ref();
    let entity_types = schema
        .entity_types()
        .map(|e| SpecEntityType {
            name: e.name().to_string(),
            enum_ids: match &e.kind {
                ValidatorEntityTypeKind::Enum(choices) => {
                    Some(choices.iter().map(|c| c.as_ref().to_string()).collect())
                }
                ValidatorEntityTypeKind::Standard(_) | ValidatorEntityTypeKind::External => None,
            },
        })
        .collect();
    let actions = schema
        .action_ids()
        .map(|a| {
            (
                a.name().entity_type().to_string(),
                a.name().eid().as_ref().to_string(),
            )
        })
        .collect();
    SpecEntities {
        entity_types,
        actions,
    }
}
