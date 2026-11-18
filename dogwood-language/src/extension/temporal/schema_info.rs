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

use cedar_policy_core::ast::{Eid, EntityType, EntityUID};
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
    /// The schema this handle reads.
    pub(crate) fn validator_schema(&self) -> &ValidatorSchema {
        &self.schema
    }

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
        let entity_type: EntityType = type_name.parse().ok()?;
        let uid = EntityUID::from_components(entity_type, Eid::new(id), None);
        self.schema.get_action_id(&uid).map(|action| ActionHandle {
            action,
            schema: &self.schema,
        })
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

    /// The refs of every declared entity type, for diagnostics, sorted (the
    /// schema holds them in a hash map, whose order varies from run to run).
    pub fn known_entity_refs(&self) -> Vec<String> {
        let mut known: Vec<String> = self
            .schema
            .entity_types()
            .map(|e| e.name().to_string())
            .collect();
        known.sort();
        known
    }
}

/// A declared action and its Cedar-typed context.
#[derive(Clone, Copy)]
pub struct ActionHandle<'a> {
    action: &'a ValidatorActionId,
    /// Kept so a scope entity's ATTRIBUTES can be resolved, not just its type
    /// name: `applies_to_principals` yields an entity type, and turning that
    /// into attribute types needs another lookup in the same schema.
    schema: &'a ValidatorSchema,
}

impl ActionHandle<'_> {
    /// The predicate reference form used in diagnostics (`Ns::id`).
    pub fn predicate_ref(&self) -> String {
        predicate_ref(self.action)
    }

    /// The rich type of the named `input` field, or `None` if absent.
    pub fn input_field_type(&self, name: &str) -> Option<RichType> {
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

    /// The Cedar type of the `context.<path>` field, when every attribute along
    /// it is declared (an optional one need not be present). `None` when the
    /// path does not resolve, or runs through an attribute lowering hoisted
    /// (see [`resolve_context_path`](ActionHandle::resolve_context_path)).
    pub(crate) fn context_path_cedar_type(&self, path: &[String]) -> Option<&Type> {
        let (head, rest) = path.split_first()?;
        if crate::api::is_hoisted_name(head) {
            return None;
        }
        // `context()` is `None` for an `external` action (Cedar 4.14, RFC 116).
        let mut current = record_attrs(self.action.context()?)?
            .get_attr(head)?
            .attr_type
            .as_ref();
        for seg in rest {
            current = record_attrs(current)?.get_attr(seg)?.attr_type.as_ref();
        }
        Some(current)
    }

    /// The Cedar type of the attribute `path` of the entity type `ety`, when
    /// every attribute along it is declared. `id` and `type` are attributes
    /// like any other, as in Cedar.
    pub(crate) fn scope_attribute_cedar_type(
        &self,
        ety: &EntityType,
        path: &[String],
    ) -> Option<&Type> {
        let (first, rest) = path.split_first()?;
        let mut current = self.schema.get_entity_type(ety)?.attr(first)?.attr_type.as_ref();
        for seg in rest {
            current = record_attrs(current)?.get_attr(seg)?.attr_type.as_ref();
        }
        Some(current)
    }

    /// Resolve a `context.<seg0>.<seg1>…` field path against the scoped
    /// action's **full** declared context record — Cedar's `context` variable,
    /// which is a record whose members (`input`, `system`, `output`, …) are the
    /// declared context fields. Not limited to the `input` sub-record:
    /// `context.system.now` resolves against `system`, `context.input.user`
    /// against `input`, and `context.principal` resolves only if the context
    /// record actually declares a `principal` field (matching Cedar, where
    /// `context.principal` is a plain field access, not the request scope).
    ///
    /// The attributes lowering hoists into the context (`<rule>__temporal_<n>`,
    /// `providers`) are not part of the request a caller supplies, so a path
    /// through one does not resolve.
    pub fn resolve_context_path(&self, path: &[String]) -> PathResolution {
        let Some(head) = path.first() else {
            return PathResolution::HeadMissing;
        };
        if crate::api::is_hoisted_name(head) {
            return PathResolution::HeadMissing;
        }
        // An `external` action's context is unknown, so no head resolves.
        let Some(attrs) = self.action.context().and_then(record_attrs) else {
            return PathResolution::HeadMissing;
        };
        resolve_in(attrs, head, &path[1..])
    }

    /// The action's uid, as Cedar renders it (`Ns::Action::"Id"`).
    pub(crate) fn uid(&self) -> String {
        self.action.name().to_string()
    }

    /// The action's full declared context record type; `None` for an
    /// `external` action, whose context is unknown.
    pub(crate) fn context_type(&self) -> Option<&Type> {
        self.action.context_type()
    }

    /// The entity types the action admits for `scope` (`"principal"` or
    /// `"resource"`) that the rule's scope narrowing admits too: the scope
    /// types of the request environments the rule decides, in the order of
    /// their names (Cedar's order of entity types).
    pub(crate) fn admitted_types(
        &self,
        scope: &str,
        narrow: Option<&crate::api::ScopeConstraint>,
    ) -> Vec<&EntityType> {
        let mut types: Vec<&EntityType> = match scope {
            "principal" => self.action.applies_to_principals().collect(),
            "resource" => self.action.applies_to_resources().collect(),
            _ => Vec::new(),
        };
        // The applies-to spec is a hash set, whose order varies from run to run;
        // the request environments are visited in this order, and a check reports
        // the first environment that fails, so it is sorted.
        types.sort();
        types
            .into_iter()
            .filter(|ety| narrow.is_none_or(|n| self.admits(n, ety)))
            .collect()
    }

    /// The declared attributes of the entity type `ety`, when it is declared.
    pub(crate) fn entity_attributes(&self, ety: &EntityType) -> Option<&Attributes> {
        self.schema.get_entity_type(ety).map(|e| e.attributes())
    }

    /// The declared type at attribute `path` of the entity type `ety`, one of this
    /// action's scope types: its type in one request environment. `None` when the
    /// path does not resolve there, which the path checks report.
    pub(crate) fn scope_attribute_type_of(
        &self,
        ety: &EntityType,
        path: &[String],
    ) -> Option<RichType> {
        let (first, rest) = path.split_first()?;
        let declared = self.schema.get_entity_type(ety)?;
        resolve_one(declared, first, rest).ok()
    }

    /// Whether this action admits ANY request environment under `principal` / `resource`
    /// narrowing — i.e. some permitted principal type AND some permitted resource type
    /// survive it.
    ///
    /// Cedar filters whole (principal, action, resource) triples by the policy scope and
    /// never typechecks an action for which no triple survives. Narrowing the types
    /// WITHIN an action is not enough: `principal is Staff` must also remove an action
    /// whose principals are `[Bot]` entirely, or that action's resource types and context
    /// record get held against a condition the rule can never evaluate there.
    pub fn admits_any_env(
        &self,
        principal: Option<&crate::api::ScopeConstraint>,
        resource: Option<&crate::api::ScopeConstraint>,
    ) -> bool {
        let ok = |narrow: Option<&crate::api::ScopeConstraint>,
                  mut tys: Box<dyn Iterator<Item = &EntityType> + '_>| match narrow
        {
            None => true,
            Some(n) => tys.any(|ety| self.admits(n, ety)),
        };
        ok(principal, Box::new(self.action.applies_to_principals()))
            && ok(resource, Box::new(self.action.applies_to_resources()))
    }

    /// Whether `narrowing` admits entity type `ety`.
    ///
    /// `in G` admits `G`'s own type and any type that can be a MEMBER of it, which is
    /// static even though membership is not: it comes from the schema's declared
    /// hierarchy, via Cedar's own `ancestors` relation rather than a hand-rolled walk.
    fn admits(&self, narrowing: &crate::api::ScopeConstraint, ety: &EntityType) -> bool {
        use crate::api::ScopeConstraint as S;
        match narrowing {
            S::Any => true,
            S::IsType(ty) => ety.to_string() == *ty,
            S::Uid {
                entity_type,
                membership,
            } => {
                if ety.to_string() == *entity_type {
                    return true;
                }
                if !*membership {
                    return false;
                }
                self.schema
                    .ancestors(ety)
                    .is_some_and(|mut a| a.any(|p| p.to_string() == *entity_type))
            }
        }
    }

    /// Resolve attribute `path` under this action's `scope` entity, explaining any
    /// failure so it can be reported rather than silently ignored.
    ///
    /// `path` is the tail after the scope root, so `principal.profile.team` passes
    /// `["profile", "team"]`. Each segment after the first descends through a
    /// record-typed attribute, mirroring how a context path resolves.
    ///
    /// A scope may permit SEVERAL entity types. The path is resolved against every
    /// one of them, because the condition is evaluated whichever entity the request
    /// carries. A path that resolves to different types is
    /// [`Ambiguous`](ScopePath::Ambiguous) rather than silently one of them: a
    /// provider argument needs one type, and the temporal validator types the path
    /// in each request environment instead, as Cedar does.
    pub fn resolve_scope_path(
        &self,
        scope: &str,
        path: &[String],
        narrow: Option<&crate::api::ScopeConstraint>,
    ) -> ScopePath {
        let Some((first, rest)) = path.split_first() else {
            return ScopePath::Unknown;
        };
        let mut etys: Vec<_> = match scope {
            "principal" => self.action.applies_to_principals().collect(),
            "resource" => self.action.applies_to_resources().collect(),
            _ => return ScopePath::Unknown,
        };
        // Narrow by the RULE's scope. The action says which types it accepts; the
        // rule's `principal is T` / `== T::"x"` / `in G` says which of those the rule
        // itself can see. Without this, a rule narrowed to a type that declares the
        // attribute is judged against types it can never receive.
        if let Some(narrowing) = narrow {
            etys.retain(|ety| self.admits(narrowing, ety));
        }
        if etys.is_empty() {
            // The scope pins no entity type, so there is nothing to resolve
            // against and nothing to report.
            return ScopePath::Unknown;
        }

        // Resolve against EVERY permitted entity type, then decide from the whole
        // picture. Deciding on the first failure would be nondeterministic: the
        // applies-to spec is a hash set, so its iteration order is not stable across
        // schema builds, and the reported entity would vary run to run.
        let mut resolved: Vec<(String, RichType)> = Vec::new();
        let mut failed: Vec<(String, ScopePathFailure)> = Vec::new();
        for ety in etys {
            let entity = ety.to_string();
            let Some(declared) = self.schema.get_entity_type(ety) else {
                // Not in the projection; Cedar's own validator owns that.
                return ScopePath::Unknown;
            };
            match resolve_one(declared, first, rest) {
                Ok(ty) => resolved.push((entity, ty)),
                Err(f) => failed.push((entity, f)),
            }
        }
        resolved.sort();
        failed.sort_by(|a, b| a.0.cmp(&b.0));

        // Reject when the path fails on ANY admitted entity type. The condition is
        // evaluated whichever type the request carries, so a read that cannot resolve
        // for one of them is dead for those requests — Cedar's own answer. An author
        // who means only one type says so in the rule scope (`principal is T`), which
        // the narrowing above honours, so this tightens rather than removing a
        // capability.
        if !failed.is_empty() {
            // Report only the entities that failed the SAME WAY as the first. Listing
            // every failure against one entity's segment misattributes it: two entities
            // can fail at different segments of the same path. Sorted above, so which
            // failure leads does not depend on the schema's hash iteration order.
            let failure = failed[0].1.clone();
            let entities: Vec<String> = failed
                .iter()
                .filter(|(_, f)| match (f, &failure) {
                    (ScopePathFailure::Missing(a), ScopePathFailure::Missing(b)) => a == b,
                    (ScopePathFailure::NonRecord(a), ScopePathFailure::NonRecord(b)) => a == b,
                    _ => false,
                })
                .map(|(e, _)| e.clone())
                .collect();
            return match failure {
                ScopePathFailure::Missing(segment) => ScopePath::Missing { entities, segment },
                ScopePathFailure::NonRecord(segment) => ScopePath::NonRecord { segment },
            };
        }

        // Type it only when every permitted entity type agrees. Compare the QUALIFIED
        // entity types' resolved types as rendered; a disagreement is reported as
        // `Ambiguous` rather than silently resolved to one side. A provider argument
        // rejects it; the temporal validator types the path in each request
        // environment instead.
        let mut types: Vec<RichType> = resolved.iter().map(|(_, t)| t.clone()).collect();
        types.sort();
        types.dedup();
        if types.len() > 1 {
            // Render, then sort the STRINGS: the ambiguous diagnostic's type list
            // must be lexicographic by rendered name (as the pre-enum, stringly
            // typed projection produced), not the `RichType` enum's declaration
            // order — otherwise pairs like {`boolean`, `int`} would print in a
            // different order than before. Error path only; the list is tiny.
            let mut rendered: Vec<String> = types.iter().map(RichType::render).collect();
            rendered.sort();
            return ScopePath::Ambiguous { types: rendered };
        }
        ScopePath::Resolved
    }
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

/// Why resolving a scope path against ONE entity type failed.
#[derive(Clone)]
enum ScopePathFailure {
    Missing(String),
    NonRecord(String),
}

/// Resolve `first` (then `rest`) against one entity type's declared attributes.
/// `id` and `type` are attributes like any other, as in Cedar.
fn resolve_one(
    declared: &ValidatorEntityType,
    first: &str,
    rest: &[String],
) -> Result<RichType, ScopePathFailure> {
    let Some(attr) = declared.attr(first) else {
        return Err(ScopePathFailure::Missing(first.to_string()));
    };
    let mut ty = &attr.attr_type;
    for segment in rest {
        let Some(attrs) = record_attrs(ty) else {
            return Err(ScopePathFailure::NonRecord(segment.clone()));
        };
        let Some(next) = attrs.get_attr(segment) else {
            return Err(ScopePathFailure::Missing(segment.clone()));
        };
        ty = &next.attr_type;
    }
    Ok(rich_type(ty))
}

/// The outcome of resolving a scope attribute path
/// ([`resolve_scope_path`](ActionHandle::resolve_scope_path)).
///
/// Separate from [`PathResolution`] because a scope path has a failure mode a
/// context path does not: the scope may permit several entity types, which can
/// declare the same attribute differently.
pub enum ScopePath {
    /// The full path resolved on every permitted entity type, to one type.
    Resolved,
    /// A segment is declared on NONE of the permitted entity types, listed in
    /// sorted order so the diagnostic does not depend on hash iteration order.
    Missing {
        entities: Vec<String>,
        segment: String,
    },
    /// A segment tried to traverse into a non-record type.
    NonRecord { segment: String },
    /// The path resolved on every permitted entity type but to different types,
    /// so it has no single type: a provider argument, which needs one, rejects
    /// it, and the temporal validator types it in each request environment. The
    /// types are the rendered rich-type names, for the diagnostic.
    Ambiguous { types: Vec<String> },
    /// Nothing to resolve against, and nothing to report: no attribute tail, an
    /// unrecognized root, or a scope pinning no entity type in the projection.
    Unknown,
}

/// The outcome of resolving a `context.input` field path.
pub enum PathResolution {
    /// The full path resolved; carries the leaf's rich type.
    Resolved(RichType),
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
    /// standard or `external` (Cedar 4.14, RFC 116) entity type.
    pub fn enum_eids(&self) -> Option<Vec<String>> {
        match &self.ety.kind {
            ValidatorEntityTypeKind::Enum(eids) => {
                Some(eids.iter().map(|e| e.as_ref().to_string()).collect())
            }
            ValidatorEntityTypeKind::Standard(_) | ValidatorEntityTypeKind::External => None,
        }
    }
}

/// The `input` record's attributes of an action's context, if the context is
/// a record carrying an `input` record attribute (the MCP convention).
fn input_attrs(action: &ValidatorActionId) -> Option<&Attributes> {
    let input_ty = record_attrs(action.context()?)?
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

/// The element type of an array/set in [`RichType`]: a known element type, or
/// one of two "unknown" states that behave differently in comparisons.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum ArrayElem {
    /// A bare array with no element-type information (e.g. an empty set literal,
    /// or a schema `Set` with no declared element). Pairs with any array.
    Unknown,
    /// A heterogeneous / unclassifiable element (a mixed-type array literal).
    /// Never matches a different array — the conservative direction.
    Mixed,
    /// A known element type.
    Of(Box<RichType>),
}

/// The "rich" type vocabulary the temporal checkers compare against — a
/// projection of Cedar's `Type` that the dialects own (insulating them from
/// Cedar's internal type representation). It is exact for the types a schema
/// declares: an entity type by its qualified name, a record with its
/// attributes, and each extension type by its name, so two operands have equal
/// rich types exactly when they have equal Cedar types. [`RichType::render`]
/// reproduces the former stringly-typed projection's strings for diagnostics.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum RichType {
    /// Cedar `Long` (rendered `"int"`).
    Long,
    String,
    Decimal,
    Bool,
    /// A timepoint index (a `tp` binder); distinct from `Long` so a timepoint is
    /// not silently comparable to an integer.
    Timepoint,
    /// A Cedar extension type other than `decimal` (`datetime`, `ipaddr`,
    /// `duration`), by name.
    Extension(String),
    /// An array/set, with its element state.
    Array(ArrayElem),
    /// A record (rendered `"object"`): each attribute's name, whether it is
    /// required, and its type, in name order.
    Record(Vec<(String, bool, RichType)>),
    /// An entity: `Some(name)` is a single known type, by its qualified name
    /// (`"entity:Ns::Name"`); `None` is an untagged entity — Cedar's `AnyEntity`,
    /// which no declared type is (`"entity"`).
    Entity(Option<String>),
    Never,
}

impl std::fmt::Display for RichType {
    /// The wire-identical rendering of the former rich-type strings — used in
    /// diagnostics and as the stable projection identity.
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            RichType::Long => f.write_str("int"),
            RichType::String => f.write_str("string"),
            RichType::Decimal => f.write_str("decimal"),
            RichType::Bool => f.write_str("boolean"),
            RichType::Timepoint => f.write_str("timepoint"),
            RichType::Extension(name) => f.write_str(name),
            RichType::Array(ArrayElem::Unknown) => f.write_str("array"),
            RichType::Array(ArrayElem::Mixed) => f.write_str("array<?>"),
            RichType::Array(ArrayElem::Of(inner)) => write!(f, "array<{inner}>"),
            RichType::Record(_) => f.write_str("object"),
            RichType::Entity(None) => f.write_str("entity"),
            RichType::Entity(Some(name)) => write!(f, "entity:{name}"),
            RichType::Never => f.write_str("never"),
        }
    }
}

impl RichType {
    /// The wire-identical rich-type string (an alias for the `Display` form).
    pub fn render(&self) -> String {
        self.to_string()
    }

    /// Whether this is a numeric type (only `Long`, matching the former
    /// `is_numeric`; Dogwood arithmetic/ordering operates on `Long`).
    pub fn is_numeric(&self) -> bool {
        matches!(self, RichType::Long)
    }

    /// Whether an `actual` value is acceptable where `self` is the DECLARED
    /// (expected) type — the former `param_accepts`: the two types are equal.
    /// A field of one entity type holds no entity of another, a field of one
    /// record shape no record of another, and a `datetime` field no string.
    pub fn accepts(&self, actual: &RichType) -> bool {
        self == actual
    }

    /// Whether two operands are comparable with `==` — the former
    /// `types_compatible`: equal types, or two entities of any types, when the
    /// equality does not have the shape of one that can bind a variable
    /// (`binding` is false; `check::eq_restricted_var`). An equality that binds
    /// a variable gives it the other side's value, so an equality of that shape
    /// needs equal types, whether or not it binds: a `User` variable cannot hold
    /// a `Gateway`.
    pub fn compatible(&self, other: &RichType, binding: bool) -> bool {
        self == other
            || (!binding && matches!((self, other), (RichType::Entity(_), RichType::Entity(_))))
    }

    /// User-facing rendering for diagnostics — the former `display_type`:
    /// `array<?>` reads as "mixed-type array", an entity shows just its
    /// qualified type, a record its attributes, and a known array element is
    /// rendered recursively.
    pub fn display(&self) -> String {
        match self {
            RichType::Array(ArrayElem::Mixed) => "mixed-type array".to_string(),
            RichType::Array(ArrayElem::Of(inner)) => format!("array<{}>", inner.display()),
            RichType::Entity(Some(tag)) => tag.clone(),
            RichType::Record(attrs) => {
                let attrs: Vec<String> = attrs
                    .iter()
                    .map(|(name, required, ty)| {
                        format!("{name}{}: {}", if *required { "" } else { "?" }, ty.display())
                    })
                    .collect();
                format!("{{ {} }}", attrs.join(", "))
            }
            // Scalars, `array` (Unknown), `entity` (untagged), `never`.
            _ => self.render(),
        }
    }
}

/// What a temporal finding says of a binder or a term of one of Cedar's
/// extension types other than `decimal`: temporal conditions do not support
/// them (the specification's `CedarType.temporalSupported`).
pub(crate) const UNSUPPORTED_EXTENSION: &str =
    "temporal conditions do not support Cedar's `datetime`, `duration`, and `ipaddr` types";

impl RichType {
    /// Whether the type is, or holds as a set element or record attribute, one
    /// of Cedar's extension types other than `decimal`, which temporal
    /// conditions do not support (`UNSUPPORTED_EXTENSION`).
    pub fn holds_unsupported_extension(&self) -> bool {
        match self {
            RichType::Extension(_) => true,
            RichType::Array(ArrayElem::Of(inner)) => inner.holds_unsupported_extension(),
            RichType::Record(attrs) => attrs
                .iter()
                .any(|(_, _, t)| t.holds_unsupported_extension()),
            _ => false,
        }
    }
}

/// Project a Cedar [`Type`] into the [`RichType`] comparison vocabulary.
pub fn rich_type(ty: &Type) -> RichType {
    match ty {
        Type::Long => RichType::Long,
        Type::String => RichType::String,
        Type::Bool(_) => RichType::Bool,
        Type::ExtensionType { name } => match name.basename().as_ref() {
            "decimal" => RichType::Decimal,
            other => RichType::Extension(other.to_string()),
        },
        Type::Set {
            element_type: Some(inner),
        } => RichType::Array(ArrayElem::Of(Box::new(rich_type(inner)))),
        Type::Set { element_type: None } => RichType::Array(ArrayElem::Unknown),
        Type::Record { attrs, .. } => RichType::Record(
            attrs
                .iter()
                .map(|(name, attr)| {
                    (
                        name.to_string(),
                        attr.is_required(),
                        rich_type(&attr.attr_type),
                    )
                })
                .collect(),
        ),
        Type::Entity(EntityKind::Entity(lub)) => match lub.get_single_entity() {
            Some(et) => RichType::Entity(Some(et.to_string())),
            None => RichType::Entity(None),
        },
        Type::Entity(EntityKind::AnyEntity) => RichType::Entity(None),
        Type::Never => RichType::Never,
    }
}

#[cfg(test)]
mod tests {
    use std::collections::BTreeSet;

    use super::{PathResolution, RichType, SchemaInfo};

    struct ActionIdCase {
        label: &'static str,
        source: &'static str,
        decoded: &'static str,
    }

    const ACTION_IDS: &[ActionIdCase] = &[
        ActionIdCase {
            label: "plain",
            source: "plain",
            decoded: "plain",
        },
        ActionIdCase {
            label: "empty",
            source: "",
            decoded: "",
        },
        ActionIdCase {
            label: "quote",
            source: r#"a\"b"#,
            decoded: "a\"b",
        },
        ActionIdCase {
            label: "backslash",
            source: r#"a\\b"#,
            decoded: "a\\b",
        },
        ActionIdCase {
            label: "hex_quote",
            source: r#"hex\x22quote"#,
            decoded: "hex\"quote",
        },
        ActionIdCase {
            label: "hex_backslash",
            source: r#"hex\x5cslash"#,
            decoded: "hex\\slash",
        },
        ActionIdCase {
            label: "hex_delete",
            source: r#"hex\x7fdelete"#,
            decoded: "hex\u{7f}delete",
        },
        ActionIdCase {
            label: "escaped_single_quote",
            source: r#"single\'quote"#,
            decoded: "single'quote",
        },
        ActionIdCase {
            label: "newline",
            source: r#"a\nb"#,
            decoded: "a\nb",
        },
        ActionIdCase {
            label: "carriage_return",
            source: r#"a\rb"#,
            decoded: "a\rb",
        },
        ActionIdCase {
            label: "tab",
            source: r#"a\tb"#,
            decoded: "a\tb",
        },
        ActionIdCase {
            label: "nul",
            source: r#"a\0b"#,
            decoded: "a\0b",
        },
        ActionIdCase {
            label: "unicode_escape",
            source: r#"\u{e}"#,
            decoded: "\u{e}",
        },
        ActionIdCase {
            label: "underscored_unicode",
            source: r#"u\u{0_1_2_3}"#,
            decoded: "u\u{123}",
        },
        ActionIdCase {
            label: "underscored_unicode_quote",
            source: r#"u\u{0_0_2_2}q"#,
            decoded: "u\"q",
        },
        ActionIdCase {
            label: "literal_escape_text",
            source: r#"\\u{e}"#,
            decoded: r"\u{e}",
        },
        ActionIdCase {
            label: "literal_hex_escape_text",
            source: r#"\\x22"#,
            decoded: r"\x22",
        },
        ActionIdCase {
            label: "punctuation",
            source: "symbols::{}[]",
            decoded: "symbols::{}[]",
        },
        ActionIdCase {
            label: "printable_unicode",
            source: "犬",
            decoded: "犬",
        },
    ];

    fn schema_info(namespaced: bool) -> SchemaInfo {
        fn actions(principal: &str, resource: &str) -> String {
            ACTION_IDS
                .iter()
                .enumerate()
                .map(|(index, case)| {
                    format!(
                        r#"action "{}" appliesTo {{
                            principal: [{principal}],
                            resource: [{resource}],
                            context: {{ input: {{ marker_{index}: String }} }}
                        }};"#,
                        case.source
                    )
                })
                .collect::<Vec<_>>()
                .join("\n")
        }

        let schema_source = if namespaced {
            format!(
                r#"
                namespace Escaped {{
                    entity User;
                    entity Doc;
                    {}
                }}
            "#,
                actions("User", "Doc")
            )
        } else {
            format!(
                r#"
                entity RootUser;
                entity RootDoc;
                {}
            "#,
                actions("RootUser", "RootDoc")
            )
        };
        let schema = cedar_policy::Schema::from_cedarschema_str(&schema_source)
            .unwrap_or_else(|e| {
                panic!("lookup fixture schema should parse: {e:?}\n{schema_source}")
            })
            .0;
        SchemaInfo::from_validator_schema(schema.as_ref())
    }

    #[test]
    fn action_resolves_decoded_ids_for_every_escape_class_and_namespace_shape() {
        for (info, namespaces) in [
            (schema_info(false), vec![None, Some("")]),
            (schema_info(true), vec![Some("Escaped")]),
        ] {
            for namespace in namespaces {
                for (index, case) in ACTION_IDS.iter().enumerate() {
                    let handle = info.action(namespace, case.decoded).unwrap_or_else(|| {
                        panic!("{} should resolve in {namespace:?}", case.label)
                    });
                    assert_eq!(
                        handle.input_field_type(&format!("marker_{index}")),
                        Some(RichType::String),
                        "{} resolved the wrong action in {namespace:?}",
                        case.label
                    );
                }
            }
        }
    }

    #[test]
    fn escaped_text_and_the_character_it_spells_are_distinct_action_ids() {
        let info = schema_info(true);

        let control = info
            .action(Some("Escaped"), "\u{e}")
            .expect("U+000E action");
        let literal = info
            .action(Some("Escaped"), r"\u{e}")
            .expect("literal escape-text action");

        let control_index = ACTION_IDS
            .iter()
            .position(|case| case.label == "unicode_escape")
            .unwrap();
        let literal_index = ACTION_IDS
            .iter()
            .position(|case| case.label == "literal_escape_text")
            .unwrap();
        assert_eq!(
            control.input_field_type(&format!("marker_{control_index}")),
            Some(RichType::String)
        );
        assert_eq!(
            literal.input_field_type(&format!("marker_{literal_index}")),
            Some(RichType::String)
        );
    }

    #[test]
    fn action_returns_none_only_for_an_undeclared_id() {
        let info = schema_info(true);
        assert!(info.action(Some("Escaped"), "not-declared").is_none());
    }

    #[test]
    fn enum_eids_are_decoded_for_semantic_comparison_in_every_namespace_shape() {
        let cases = [
            ("plain", "plain"),
            (r#"quote\x22id"#, "quote\"id"),
            (r#"slash\x5cid"#, "slash\\id"),
            (r#"line\nbreak"#, "line\nbreak"),
            (r#"carriage\rreturn"#, "carriage\rreturn"),
            (r#"tab\tid"#, "tab\tid"),
            (r#"nul\0id"#, "nul\0id"),
            (r#"control\u{e}"#, "control\u{e}"),
            (r#"unicode\u{0_1_2_3}"#, "unicode\u{123}"),
            (r#"unicode\u{0_0_2_2}quote"#, "unicode\"quote"),
            (r#"literal\\u{e}"#, r"literal\u{e}"),
            (r#"literal\\x22"#, r"literal\x22"),
            (r#"single\'quote"#, "single'quote"),
            ("犬", "犬"),
        ];
        let members = cases
            .iter()
            .map(|(source, _)| format!(r#""{source}""#))
            .collect::<Vec<_>>()
            .join(", ");
        let expected: BTreeSet<_> = cases
            .iter()
            .map(|(_, decoded)| decoded.to_string())
            .collect();

        for (namespace, schema_source) in [
            (
                None,
                format!(
                    r#"
                    entity Mode enum [{members}];
                    entity User;
                    "#
                ),
            ),
            (
                Some("Outer::Inner"),
                format!(
                    r#"
                    namespace Outer::Inner {{
                        entity Mode enum [{members}];
                        entity User;
                    }}
                    "#
                ),
            ),
        ] {
            let schema = cedar_policy::Schema::from_cedarschema_str(&schema_source)
                .unwrap_or_else(|error| panic!("{error:?}\n{schema_source}"))
                .0;
            let info = SchemaInfo::from_validator_schema(schema.as_ref());
            let actual: BTreeSet<_> = info
                .entity_type(namespace, "Mode")
                .expect("enum entity type")
                .enum_eids()
                .expect("enum IDs")
                .into_iter()
                .collect();
            assert_eq!(actual, expected, "namespace {namespace:?}");
            assert!(
                info.entity_type(namespace, "User")
                    .expect("standard entity type")
                    .enum_eids()
                    .is_none()
            );
        }
    }

    /// A schema with Cedar 4.14 (RFC 116) `external` declarations next to
    /// their normal counterparts, so each external assertion has a control.
    fn external_schema_info() -> SchemaInfo {
        let schema_source = r#"
            namespace Ext {
                entity User;
                entity Mode enum ["on", "off"];
                external entity Remote;
                action "Normal" appliesTo {
                    principal: [User],
                    resource: [User],
                    context: { input: { owner: User } }
                };
                external action "Outside";
            }
        "#;
        let schema = cedar_policy::Schema::from_cedarschema_str(schema_source)
            .unwrap_or_else(|e| panic!("external fixture schema should parse: {e:?}"))
            .0;
        SchemaInfo::from_validator_schema(schema.as_ref())
    }

    #[test]
    fn external_action_has_no_context_and_input_helpers_are_empty() {
        let info = external_schema_info();
        let path = ["input".to_string(), "owner".to_string()];

        // Control: the normal action's input field resolves.
        let normal = info.action(Some("Ext"), "Normal").expect("normal action");
        assert_eq!(
            normal.input_field_type("owner"),
            Some(RichType::Entity(Some("Ext::User".to_string())))
        );
        assert_eq!(normal.input_field_names(), vec!["owner".to_string()]);
        assert!(matches!(
            normal.resolve_context_path(&path),
            PathResolution::Resolved(RichType::Entity(Some(_)))
        ));
        assert_eq!(
            normal
                .context_path_cedar_type(&path)
                .map(ToString::to_string)
                .as_deref(),
            Some("Ext::User")
        );

        // The external action is declared, but its context is unknown.
        let external = info
            .action(Some("Ext"), "Outside")
            .expect("external action");
        assert!(matches!(
            external.resolve_context_path(&path),
            PathResolution::HeadMissing
        ));
        assert!(external.context_path_cedar_type(&path).is_none());
        assert_eq!(external.input_field_type("owner"), None);
        assert!(external.input_field_names().is_empty());
    }

    #[test]
    fn external_entity_has_no_enum_eids_while_enum_entity_does() {
        let info = external_schema_info();
        let remote = info
            .entity_type(Some("Ext"), "Remote")
            .expect("external entity type is declared");
        assert!(remote.enum_eids().is_none());

        let modes: BTreeSet<_> = info
            .entity_type(Some("Ext"), "Mode")
            .expect("enum entity type")
            .enum_eids()
            .expect("enum IDs")
            .into_iter()
            .collect();
        assert_eq!(modes, BTreeSet::from(["on".to_string(), "off".to_string()]));
    }
}
