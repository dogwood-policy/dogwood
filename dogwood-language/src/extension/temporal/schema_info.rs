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
    /// The scope entity's type, narrowed by `narrow` when given.
    ///
    /// Exactly one candidate yields the TAGGED type (`entity:Staff`). Several yield the
    /// UNTAGGED `entity`, which is the honest answer — the arriving entity is some one of
    /// them and the tag is not statically known, but it IS an entity. Returning `None`
    /// there was fail-open: every comparison check is guarded on both operands having a
    /// type, so an entity compared against a STRING or an INT — a genuine type error
    /// Cedar rejects — went unreported whenever an action permitted more than one type.
    fn scope_entity_type<'t>(
        &self,
        tys: impl Iterator<Item = &'t EntityType>,
        narrow: Option<&crate::api::ScopeConstraint>,
    ) -> Option<String> {
        let mut admitted = tys.filter(|ety| narrow.is_none_or(|n| self.admits(n, ety)));
        let first = admitted.next()?;
        if admitted.next().is_some() {
            return Some("entity".to_string());
        }
        Some(format!("entity:{}", first.name().basename()))
    }

    /// [`principal_type`](ActionHandle::principal_type), narrowed by the rule's scope.
    pub fn principal_type_narrowed(
        &self,
        narrow: Option<&crate::api::ScopeConstraint>,
    ) -> Option<String> {
        self.scope_entity_type(self.action.applies_to_principals(), narrow)
    }

    /// [`resource_type`](ActionHandle::resource_type), narrowed by the rule's scope.
    pub fn resource_type_narrowed(
        &self,
        narrow: Option<&crate::api::ScopeConstraint>,
    ) -> Option<String> {
        self.scope_entity_type(self.action.applies_to_resources(), narrow)
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

    /// The declared type at attribute `path` under this action's `scope` entity
    /// (`"principal"` or `"resource"`), or `None` when it does not resolve.
    ///
    /// Typing only: a caller wanting to know WHY a path did not resolve, so it can
    /// say so, uses [`resolve_scope_path`](ActionHandle::resolve_scope_path).
    pub fn scope_attribute_type(
        &self,
        scope: &str,
        path: &[String],
        narrow: Option<&crate::api::ScopeConstraint>,
    ) -> Option<String> {
        match self.resolve_scope_path(scope, path, narrow) {
            ScopePath::Resolved(ty) => Some(ty),
            _ => None,
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
    /// one of them and must resolve the same way for all, because the condition is
    /// evaluated whichever entity the request carries — the same rule context paths
    /// follow across the actions a hoisted leaf attaches to. A path that resolves to
    /// different types is therefore [`Ambiguous`](ScopePath::Ambiguous) rather than
    /// silently one of them.
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
        let mut resolved: Vec<(String, String)> = Vec::new();
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
        // entity types' resolved types as rendered; a disagreement means the
        // comparison is a mismatch for at least one admissible request, which is
        // reported rather than silently resolved to one side.
        let mut types: Vec<String> = resolved.iter().map(|(_, t)| t.clone()).collect();
        types.sort();
        types.dedup();
        if types.len() > 1 {
            return ScopePath::Ambiguous { types };
        }
        ScopePath::Resolved(types.remove(0))
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
///
/// `.id` / `.type` project the entity uid when no attribute of that name is declared,
/// and the uid's parts are strings. A DECLARED attribute shadows the projection, which
/// the attribute lookup below already handles by running first — matching the
/// interpreter, which looks a supplied attribute up before falling back to the uid.
fn resolve_one(
    declared: &ValidatorEntityType,
    first: &str,
    rest: &[String],
) -> Result<String, ScopePathFailure> {
    let Some(attr) = declared.attr(first) else {
        if matches!(first, "id" | "type") {
            return match rest.first() {
                None => Ok("string".to_string()),
                // The projection is a string, so it has no fields.
                Some(segment) => Err(ScopePathFailure::NonRecord(segment.clone())),
            };
        }
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
    /// The full path resolved on every permitted entity type, to this type.
    Resolved(String),
    /// A segment is declared on NONE of the permitted entity types, listed in
    /// sorted order so the diagnostic does not depend on hash iteration order.
    Missing {
        entities: Vec<String>,
        segment: String,
    },
    /// A segment tried to traverse into a non-record type.
    NonRecord { segment: String },
    /// The path resolved on every permitted entity type but to different types,
    /// so there is no single type the condition can be checked against.
    Ambiguous { types: Vec<String> },
    /// Nothing to resolve against, and nothing to report: no attribute tail, an
    /// unrecognized root, or a scope pinning no entity type in the projection.
    Unknown,
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
