import Dogwood.Frontend.Validate.Assumptions

/-!
# What the validator's completeness assumes of the earlier stages

The validator's completeness (`Dogwood.Thm.Frontend.validate_complete`) takes the guarantees its
soundness takes (`Validate.assumptions`), and six more, each a property of the lowered set the
stages before validation give by construction:

* `scopesExact`: a leaf's target actions and narrowing admit only request environments its rule's
  scope admits (the converse of `scopesCovered`), so the crate checks a leaf only where the
  specification types it;
* `providersResolved`: a provider leaf whose provider the projection declares has the crate's
  declaration (resolution found it);
* `derivedFieldsResolve`: each leaf field of a derived event is found by its path (the fields of a
  derived event's groups have distinct names);
* `leafIdsDistinct`: the temporal leaves have distinct ids, and so do the provider leaves (the
  projection finds each leaf by its id);
* `leavesGrafted`: augmentation declares each leaf's attribute, required, on every target action
  of its rule (`context.<id>` of a temporal leaf, `context.providers.<id>` of a provider leaf);
* `actionsApart`: the schema's actions are its uids of a type named `Action` (Cedar's schema
  constructor names each action `Action::"<id>"` in its namespace, and no entity type `Action`).

It holds up to the crate's stricter rules (`Dogwood.Thm.Frontend.StrictRules`): what the crate
rejects and the specification's validity accepts.
-/

namespace Dogwood.Frontend.Validate

open Dogwood.Spec (Policy)

/-- A leaf's target actions and narrowing admit only request environments of the action schema
that its rule's scope admits. -/
def withinScope (l : Lowered) (q : Policy) (targets : List (String × String))
    (p r : ScopeConstraint) : Bool :=
  let A := specActionSchema l
  A.environments.all fun env => q.admits A env ||
    !(targets.any (fun (ns, id) => actionUidOf ns id == env.reqty.action) &&
      constraintAdmits l.schema p env.reqty.principal &&
      constraintAdmits l.schema r env.reqty.resource)

/-- Every leaf's metadata stays within its rule's scope. -/
def scopesExact (l : Lowered) : Bool :=
  (l.temporal.zip l.temporalRules).all (fun (f, k) => match l.policies[k]? with
    | some q => withinScope l q f.targetActions f.principal f.resource
    | none => false) &&
  (l.providers.zip l.providerRules).all (fun (g, k) => match l.policies[k]? with
    | some q => withinScope l q g.targetActions g.principal g.resource
    | none => false)

/-- A provider leaf whose provider the projection declares has a declaration. -/
def providersResolved (l : Lowered) : Bool :=
  l.providers.all fun g => match g.toCall with
    | .ok c => !((providerDeclsToSpec l.declarations l.schema).1.find? c.function).isSome ||
        g.declaration.isSome
    | .error _ => true

/-- Every leaf field of a derived event is found by its path. -/
def derivedFieldsResolve (l : Lowered) : Bool :=
  l.eventSchema.events.all fun ev => ev.leafFields.all fun x => lookupPath ev x.1 == .leaf

/-- The temporal leaves have distinct ids, and so do the provider leaves. -/
def leafIdsDistinct (l : Lowered) : Bool :=
  decide (l.temporal.map (·.id)).Nodup && decide (l.providers.map (·.id)).Nodup

/-- The record type declares `a` as a required attribute. -/
def requiredIn (C : Cedar.Validation.RecordType) (a : String) : Bool :=
  match C.find? a with
  | some (.required _) => true
  | _ => false

/-- The record type declares `providers` as a required record, which declares `a`, required. -/
def providerRequiredIn (C : Cedar.Validation.RecordType) (a : String) : Bool :=
  match C.find? "providers" with
  | some (.required (.record R)) => requiredIn R a
  | _ => false

/-- Augmentation declares each leaf's attribute, required, on every target action of its rule. -/
def leavesGrafted (l : Lowered) : Bool :=
  l.temporal.all (fun f => f.targetActions.all fun (ns, id) =>
    match action? l.schema ns id with
    | some (_, entry) => requiredIn entry.context f.id
    | none => true) &&
  l.providers.all (fun g => g.targetActions.all fun (ns, id) =>
    match action? l.schema ns id with
    | some (_, entry) => providerRequiredIn entry.context g.id
    | none => true)

/-- The schema's actions are its uids of a type named `Action`: every action's type is named
`Action`, and no entity type is. -/
def actionsApart (S : Cedar.Validation.Schema) : Bool :=
  S.acts.toList.all (·.1.ty.id == "Action") && S.ets.toList.all (·.1.id != "Action")

/-- Every assumption of completeness beyond soundness's, decided. -/
def converseAssumptions (l : Lowered) : List (String × Bool) :=
  [("scopesExact", scopesExact l), ("providersResolved", providersResolved l),
   ("derivedFieldsResolve", derivedFieldsResolve l), ("leafIdsDistinct", leafIdsDistinct l),
   ("leavesGrafted", leavesGrafted l), ("actionsApart", actionsApart l.schema)]

end Dogwood.Frontend.Validate
