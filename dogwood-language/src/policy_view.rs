//! Read-only, Dogwood-owned **views** into a parsed policy's scope, exposed by
//! [`ParsedPolicy`](crate::policy_set::ParsedPolicy) before the action schema
//! is applied.
//!
//! A parsed policy's head (`principal, action, resource`) is stored internally
//! as `cedar_policy_core::ast` scope constraints (see `crate::ast::Scope`),
//! but `cedar-policy-core` is a lower-level crate Dogwood deliberately keeps
//! *out* of its public surface — only the high-level `cedar-policy` crate is
//! re-exported (see the [`cedar`](crate::cedar) module). So rather than leak
//! the internal constraint types, these views mirror the **public** shapes
//! `cedar_policy` itself uses for a template's scope
//! (`TemplatePrincipalConstraint` / `ActionConstraint` /
//! `TemplateResourceConstraint`): the entity leaves are
//! [`cedar_policy::EntityUid`] / [`cedar_policy::EntityTypeName`], and a
//! template slot (`?principal` / `?resource`) is modeled as `None`.
//!
//! These types own their data (a cheap projection of the parsed scope), carry
//! no source spans, and are produced only by Dogwood — a consumer matches on
//! them to read a policy's head without depending on `cedar-policy-core` or on
//! Dogwood's internal AST.

use cedar_policy::{EntityTypeName, EntityUid};
use cedar_policy_core::ast as cedar_ast;

use crate::ast::Scope;

/// A parsed policy's scope (`principal, action, resource`) as a Dogwood-owned
/// projection — the pre-lowering analog of reading a `cedar_policy` policy's
/// three scope constraints.
///
/// Produced by [`ParsedPolicy::scope`](crate::policy_set::ParsedPolicy::scope).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PolicyScope {
    principal: PrincipalConstraint,
    action: ActionConstraint,
    resource: ResourceConstraint,
}

impl PolicyScope {
    /// The principal constraint (`principal`, `principal == …`,
    /// `principal in …`, `principal is …`, `principal is … in …`).
    pub fn principal(&self) -> &PrincipalConstraint {
        &self.principal
    }

    /// The action constraint (`action`, `action == …`, `action in […]`).
    pub fn action(&self) -> &ActionConstraint {
        &self.action
    }

    /// The resource constraint (same shapes as the principal constraint).
    pub fn resource(&self) -> &ResourceConstraint {
        &self.resource
    }

    /// Project the internal [`Scope`] into this owned view.
    pub(crate) fn from_scope(scope: &Scope) -> PolicyScope {
        PolicyScope {
            principal: PrincipalConstraint::from_inner(scope.principal.as_inner()),
            action: ActionConstraint::from_inner(&scope.action),
            resource: ResourceConstraint::from_inner(scope.resource.as_inner()),
        }
    }
}

/// The principal scope constraint. Mirrors `cedar_policy`'s
/// `TemplatePrincipalConstraint`: a template slot (`?principal`) appears as
/// `None` in the [`In`](PrincipalConstraint::In) /
/// [`Eq`](PrincipalConstraint::Eq) / [`IsIn`](PrincipalConstraint::IsIn)
/// payload (a slot is never `Any` or bare `Is`).
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum PrincipalConstraint {
    /// Unconstrained (`principal`).
    Any,
    /// `principal in <euid>` — or `principal in ?principal` (slot) when `None`.
    In(Option<EntityUid>),
    /// `principal == <euid>` — or `principal == ?principal` (slot) when `None`.
    Eq(Option<EntityUid>),
    /// `principal is <Type>`.
    Is(EntityTypeName),
    /// `principal is <Type> in <euid>` — the `in` target is a slot when `None`.
    IsIn(EntityTypeName, Option<EntityUid>),
}

/// The resource scope constraint — same shapes as [`PrincipalConstraint`],
/// mirroring `cedar_policy`'s `TemplateResourceConstraint`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ResourceConstraint {
    /// Unconstrained (`resource`).
    Any,
    /// `resource in <euid>` — or a slot (`?resource`) when `None`.
    In(Option<EntityUid>),
    /// `resource == <euid>` — or a slot (`?resource`) when `None`.
    Eq(Option<EntityUid>),
    /// `resource is <Type>`.
    Is(EntityTypeName),
    /// `resource is <Type> in <euid>` — the `in` target is a slot when `None`.
    IsIn(EntityTypeName, Option<EntityUid>),
}

/// The action scope constraint. Mirrors `cedar_policy`'s `ActionConstraint`:
/// actions never take an `is` constraint and carry no slots, but may be
/// compared against a *list* (`action in [ … ]`).
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ActionConstraint {
    /// Unconstrained (`action`).
    Any,
    /// `action in [ <euid>, … ]`.
    In(Vec<EntityUid>),
    /// `action == <euid>`.
    Eq(EntityUid),
}

impl PrincipalConstraint {
    fn from_inner(inner: &cedar_ast::PrincipalOrResourceConstraint) -> PrincipalConstraint {
        match project_por(inner) {
            Por::Any => PrincipalConstraint::Any,
            Por::In(o) => PrincipalConstraint::In(o),
            Por::Eq(o) => PrincipalConstraint::Eq(o),
            Por::Is(t) => PrincipalConstraint::Is(t),
            Por::IsIn(t, o) => PrincipalConstraint::IsIn(t, o),
        }
    }
}

impl ResourceConstraint {
    fn from_inner(inner: &cedar_ast::PrincipalOrResourceConstraint) -> ResourceConstraint {
        match project_por(inner) {
            Por::Any => ResourceConstraint::Any,
            Por::In(o) => ResourceConstraint::In(o),
            Por::Eq(o) => ResourceConstraint::Eq(o),
            Por::Is(t) => ResourceConstraint::Is(t),
            Por::IsIn(t, o) => ResourceConstraint::IsIn(t, o),
        }
    }
}

impl ActionConstraint {
    fn from_inner(inner: &cedar_ast::ActionConstraint) -> ActionConstraint {
        match inner {
            cedar_ast::ActionConstraint::Any => ActionConstraint::Any,
            cedar_ast::ActionConstraint::Eq(euid) => {
                ActionConstraint::Eq(to_public_uid(euid.as_ref()))
            }
            cedar_ast::ActionConstraint::In(euids) => {
                ActionConstraint::In(euids.iter().map(|e| to_public_uid(e.as_ref())).collect())
            }
            // `tolerant-ast` is off in Dogwood's build, so `ErrorConstraint`
            // never occurs; treat any future non-exhaustive variant as `Any`
            // rather than panic.
            #[allow(unreachable_patterns)]
            _ => ActionConstraint::Any,
        }
    }
}

/// The principal/resource shape, projected once so the two identical mappings
/// (principal, resource) share a single conversion.
enum Por {
    Any,
    In(Option<EntityUid>),
    Eq(Option<EntityUid>),
    Is(EntityTypeName),
    IsIn(EntityTypeName, Option<EntityUid>),
}

fn project_por(inner: &cedar_ast::PrincipalOrResourceConstraint) -> Por {
    use cedar_ast::PrincipalOrResourceConstraint as C;
    match inner {
        C::Any => Por::Any,
        C::In(r) => Por::In(entity_ref_to_public(r)),
        C::Eq(r) => Por::Eq(entity_ref_to_public(r)),
        C::Is(t) => Por::Is(to_public_type(t.as_ref())),
        C::IsIn(t, r) => Por::IsIn(to_public_type(t.as_ref()), entity_ref_to_public(r)),
    }
}

/// A core [`EntityReference`](cedar_ast::EntityReference) as an optional public
/// [`EntityUid`] — `Some(uid)` for a literal reference, `None` for a template
/// slot (`?principal` / `?resource`).
fn entity_ref_to_public(r: &cedar_ast::EntityReference) -> Option<EntityUid> {
    match r {
        cedar_ast::EntityReference::EUID(euid) => Some(to_public_uid(euid.as_ref())),
        cedar_ast::EntityReference::Slot(_) => None,
    }
}

/// Convert a core `EntityUID` to the public [`EntityUid`] via `cedar_policy`'s
/// own `From` bridge. The `.dw` source `Loc` the parser stamped onto the euid
/// is dropped — this is a data view, not a diagnostic surface.
fn to_public_uid(euid: &cedar_ast::EntityUID) -> EntityUid {
    EntityUid::from(euid.clone())
}

/// Convert a core `EntityType` to the public [`EntityTypeName`] via
/// `cedar_policy`'s own `From` bridge.
fn to_public_type(ty: &cedar_ast::EntityType) -> EntityTypeName {
    EntityTypeName::from(ty.clone())
}
