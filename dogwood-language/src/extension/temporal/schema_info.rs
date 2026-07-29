//! Schema lookups for the temporal validator, served directly from
//! `cedar_policy_core`'s [`ValidatorSchema`].
//!
//! The temporal checks need three things from the (augmented) schema: an
//! action's declared `input` record, the type of a field within it, and
//! whether an entity type is declared (and, for an enum entity, its
//! permitted eids). Cedar already computes all of this — a `ValidatorSchema`
//! exposes each action's fully-typed `context` and the declared entity
//! types — so this is a thin adapter over it rather than a reconstructed
//! schema projection. Field/operand types are rendered to the "rich"
//! comparison strings the checks use (`"int"`, `"string"`, `"entity:User"`,
//! `"array<int>"`, …) straight from Cedar's [`Type`].

use cedar_policy_core::ast::{EntityType, EntityUID};
use cedar_policy_core::validator::types::{Attributes, EntityKind, Type};
use cedar_policy_core::validator::{
    ValidatorActionId, ValidatorEntityType, ValidatorEntityTypeKind, ValidatorSchema,
};

/// A thin handle over a [`ValidatorSchema`] exposing just the lookups the
/// temporal validator needs.
pub struct SchemaInfo {
    schema: ValidatorSchema,
}

impl SchemaInfo {
    /// Build directly from an already-parsed [`ValidatorSchema`]. The public
    /// `cedar_policy::Schema` is a transparent newtype over a `ValidatorSchema`
    /// and exposes it via `AsRef`, so a caller that already holds the augmented
    /// schema (e.g. `validate`) builds a `SchemaInfo` without re-parsing the
    /// source text.
    pub fn from_validator_schema(schema: &ValidatorSchema) -> SchemaInfo {
        SchemaInfo {
            schema: schema.clone(),
        }
    }

    /// The action with the given namespace path + id, if declared. The
    /// predicate's `namespace` is the qualified path with the trailing
    /// `Action` segment already stripped by the caller; we reattach the
    /// Cedar `Action` type to form the action's entity uid.
    pub fn action(&self, namespace: Option<&str>, id: &str) -> Option<ActionHandle<'_>> {
        let type_name = match namespace {
            Some(ns) if !ns.is_empty() => format!("{ns}::Action"),
            _ => "Action".to_string(),
        };
        let uid: EntityUID = format!("{type_name}::\"{id}\"").parse().ok()?;
        self.schema
            .get_action_id(&uid)
            .map(|action| ActionHandle { action })
    }

    /// The declared entity type `(namespace, name)`, if any.
    pub fn entity_type(&self, namespace: Option<&str>, name: &str) -> Option<EntityTypeHandle<'_>> {
        let qualified = match namespace {
            Some(ns) if !ns.is_empty() => format!("{ns}::{name}"),
            _ => name.to_string(),
        };
        let et: EntityType = qualified.parse().ok()?;
        self.schema
            .get_entity_type(&et)
            .map(|ety| EntityTypeHandle { ety })
    }

    /// The refs of every declared entity type, for diagnostics.
    pub fn known_entity_refs(&self) -> Vec<String> {
        self.schema
            .entity_types()
            .map(|e| e.name().to_string())
            .collect()
    }
}

/// A declared action and its Cedar-typed context.
pub struct ActionHandle<'a> {
    action: &'a ValidatorActionId,
}

impl ActionHandle<'_> {
    /// The predicate reference form used in diagnostics (`Ns::id`).
    pub fn predicate_ref(&self) -> String {
        predicate_ref(self.action)
    }

    /// The rich type of the named `input` field, or `None` if absent.
    pub fn input_field_type(&self, name: &str) -> Option<String> {
        input_attrs(self.action)?
            .get_attr(name)
            .map(|at| rich_type(&at.attr_type))
    }

    /// Every declared input field name, for diagnostics.
    pub fn input_field_names(&self) -> Vec<String> {
        input_attrs(self.action)
            .map(|attrs| attrs.iter().map(|(k, _)| k.to_string()).collect())
            .unwrap_or_default()
    }

    /// Resolve a `context.<seg0>.<seg1>…` field path against the scoped
    /// action's **full** declared context record — Cedar's `context` variable,
    /// which is a record whose members (`input`, `system`, `output`, …) are the
    /// declared context fields. Not limited to the `input` sub-record:
    /// `context.system.now` resolves against `system`, `context.input.user`
    /// against `input`, and `context.principal` resolves only if the context
    /// record actually declares a `principal` field (matching Cedar, where
    /// `context.principal` is a plain field access, not the request scope).
    pub fn resolve_context_path(&self, path: &[String]) -> PathResolution {
        let Some(head) = path.first() else {
            return PathResolution::HeadMissing;
        };
        let Some(attrs) = record_attrs(self.action.context()) else {
            return PathResolution::HeadMissing;
        };
        resolve_in(attrs, head, &path[1..])
    }

    /// The scoped action's principal entity type as a rich `entity:<Name>`
    /// string, if it declares exactly one principal type. `None` when the
    /// action admits several (a LUB the coarse projection does not model) or
    /// none — the bare `principal` term is then left untyped.
    pub fn principal_type(&self) -> Option<String> {
        single_entity_rich(self.action.applies_to_principals())
    }

    /// The scoped action's resource entity type, mirroring
    /// [`principal_type`](ActionHandle::principal_type).
    pub fn resource_type(&self) -> Option<String> {
        single_entity_rich(self.action.applies_to_resources())
    }
}

/// Render the single entity type of an applies-to iterator as
/// `entity:<basename>`, or `None` if there is not exactly one.
fn single_entity_rich<'a>(
    mut tys: impl Iterator<Item = &'a cedar_policy_core::ast::EntityType>,
) -> Option<String> {
    let first = tys.next()?;
    if tys.next().is_some() {
        return None;
    }
    Some(format!("entity:{}", first.name().basename()))
}

/// Resolve `head` then the remaining `rest` segments within a record's
/// `attrs`, descending nested records. Shared by the `input`-rooted and
/// full-context path resolvers.
fn resolve_in(attrs: &Attributes, head: &str, rest: &[String]) -> PathResolution {
    let Some(at) = attrs.get_attr(head) else {
        return PathResolution::HeadMissing;
    };
    let mut current = at.attr_type.as_ref();
    for seg in rest {
        match record_attrs(current) {
            Some(rec) => match rec.get_attr(seg) {
                Some(at) => current = at.attr_type.as_ref(),
                None => return PathResolution::NestedMissing(seg.clone()),
            },
            None => return PathResolution::NonRecord(seg.clone()),
        }
    }
    PathResolution::Resolved(rich_type(current))
}

/// The outcome of resolving a `context.input` field path.
pub enum PathResolution {
    /// The full path resolved; carries the leaf's rich type.
    Resolved(String),
    /// The head (`input.<head>`) field is not declared on the action.
    HeadMissing,
    /// A nested segment is not a field of its (record) parent.
    NestedMissing(String),
    /// A nested segment tried to traverse into a non-record type.
    NonRecord(String),
}

/// A declared entity type.
pub struct EntityTypeHandle<'a> {
    ety: &'a ValidatorEntityType,
}

impl EntityTypeHandle<'_> {
    /// The permitted eids if this is an enum entity type; `None` for a
    /// standard entity type.
    pub fn enum_eids(&self) -> Option<Vec<String>> {
        match &self.ety.kind {
            ValidatorEntityTypeKind::Enum(eids) => {
                Some(eids.iter().map(|e| e.escaped().to_string()).collect())
            }
            ValidatorEntityTypeKind::Standard(_) => None,
        }
    }
}

/// The `input` record's attributes of an action's context, if the context is
/// a record carrying an `input` record attribute (the MCP convention).
fn input_attrs(action: &ValidatorActionId) -> Option<&Attributes> {
    let input_ty = record_attrs(action.context())?
        .get_attr("input")?
        .attr_type
        .as_ref();
    record_attrs(input_ty)
}

/// The attributes of a record [`Type`], if it is one.
fn record_attrs(ty: &Type) -> Option<&Attributes> {
    match ty {
        Type::Record { attrs, .. } => Some(attrs),
        _ => None,
    }
}

/// The predicate reference form (`Ns::id`) for an action. The action's
/// entity type renders as `Ns::Action` (or bare `Action`); the predicate
/// form is that namespace (the path minus the trailing `Action` segment)
/// joined with the action eid.
fn predicate_ref(action: &ValidatorActionId) -> String {
    let uid = action.name();
    let eid = uid.eid().escaped();
    let action_ty = uid.entity_type().to_string();
    match action_ty
        .strip_suffix("::Action")
        .filter(|ns| !ns.is_empty())
    {
        Some(ns) => format!("{ns}::{eid}"),
        // Top-level `Action` (no namespace) or an unexpected shape: just the
        // eid.
        None => eid.to_string(),
    }
}

/// Render a Cedar [`Type`] as the "rich" comparison string the temporal
/// checks use.
pub fn rich_type(ty: &Type) -> String {
    match ty {
        Type::Long => "int".to_string(),
        Type::String => "string".to_string(),
        Type::Bool(_) => "boolean".to_string(),
        // `decimal` is comparison-relevant; `datetime`/`ipaddr` (and any
        // other extension) collapse to `string`, matching the prior
        // hand-rolled projection's coarse mapping. (A finer extension-type
        // treatment would be a deliberate behavior change, not this dedup.)
        Type::ExtensionType { name } => match name.basename().as_ref() {
            "decimal" => "decimal".to_string(),
            _ => "string".to_string(),
        },
        Type::Set {
            element_type: Some(inner),
        } => format!("array<{}>", rich_type(inner)),
        Type::Set { element_type: None } => "array".to_string(),
        Type::Record { .. } => "object".to_string(),
        Type::Entity(EntityKind::Entity(lub)) => match lub.get_single_entity() {
            Some(et) => format!("entity:{}", et.name().basename()),
            None => "entity".to_string(),
        },
        Type::Entity(EntityKind::AnyEntity) => "entity".to_string(),
        Type::Never => "never".to_string(),
    }
}
