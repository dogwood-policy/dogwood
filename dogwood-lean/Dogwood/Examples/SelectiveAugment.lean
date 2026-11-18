import Dogwood.Examples.ReadAfterLogin

/-!
# Worked example: the augmented schema is action-selective

The rule of `read_after_login` is scoped to `action == Drupe::Action::"Read"`. Lowering hoists its
temporal leaf into the request-context attribute `leafAttr 0`, and the augmented schema adds that
attribute to the context of the actions the rule's action scope admits (`actionScopeAdmits`), as
the crate does (`scope_target_actions`): `Read`'s context gains it, and `Login`'s is left as the
action schema declares it. The schema that adds every attribute to every action
(`PolicySet.allAugmentedSchema`) gives `Login` the attribute too.

The same rule under the other scopes the crate resolves:

* `action in [Drupe::Action::"Reads"]`, an action group with `Read` as a member: the group's
  members gain the attribute (`descendentOf`), and `Login` does not;
* an unconstrained `action`: every action gains it.
-/

namespace Dogwood.Examples.SelectiveAugment

open Dogwood.Spec Dogwood.Examples Dogwood.Examples.ReadAfterLogin

/-- The context `Read` has in the augmented schema: its declared context, with the leaf's
attribute. -/
theorem read_context_augmented :
    ((policySet.augmentedSchema.acts.find? read).map (·.context)).map (·.find? (leafAttr 0)) =
      some (some (.required (.bool .anyBool))) := by
  decide +kernel

/-- **`Login`'s context is unchanged**: no rule of the set can apply to `Login`, so the
augmented schema adds nothing to it. -/
theorem login_context_unchanged :
    (policySet.augmentedSchema.acts.find? login).map (·.context) =
      (policySet.actionSchema.acts.find? login).map (·.context) := by
  decide +kernel

/-- **The all-action schema adds the attribute to `Login` too.** -/
theorem login_context_all :
    ((policySet.allAugmentedSchema.acts.find? login).map (·.context)).map (·.find? (leafAttr 0)) =
      some (some (.required (.bool .anyBool))) := by
  decide +kernel

/-! ## Other action scopes -/

/-- The action group `Reads`. -/
def readsGroup : Cedar.Spec.EntityUID := action "Reads"

/-- An action entry of the examples' schema, with the given ancestors. -/
def entryWith (anc : List Cedar.Spec.EntityUID) : Cedar.Validation.ActionSchemaEntry where
  appliesToPrincipal := Cedar.Data.Set.make [oauthUserType]
  appliesToResource := Cedar.Data.Set.make [gatewayType]
  ancestors := Cedar.Data.Set.make anc
  context := Cedar.Data.Map.make [("input",
    .required (.record (Cedar.Data.Map.make [("user", .required .string)])))]

/-- The examples' schema, with `Read` a member of the pure action group `Reads` (which applies to
no principal and no resource). -/
def groupedSchema : Cedar.Validation.Schema :=
  { actionSchema actions with
    acts := Cedar.Data.Map.make [
      (login, entryWith []),
      (read, entryWith [readsGroup]),
      (readsGroup, { entryWith [] with
        appliesToPrincipal := Cedar.Data.Set.empty, appliesToResource := Cedar.Data.Set.empty })] }

/-- `policySet`'s rule with the action scope `scope`, over `groupedSchema`. -/
def withScope (scope : Cedar.Spec.ActionScope) : PolicySet :=
  { policySet with
    policies := [{ temporalPermit read φ with actionScope := scope }]
    actionSchema := groupedSchema }

/-- The context an action has in `withScope scope`'s augmented schema, at the leaf's attribute. -/
def leafAt (scope : Cedar.Spec.ActionScope) (act : Cedar.Spec.EntityUID) :
    Option (Option Cedar.Validation.QualifiedType) :=
  (((withScope scope).augmentedSchema.acts.find? act).map (·.context)).map (·.find? (leafAttr 0))

/-- **`action in [Reads]`**: the group's member `Read` gains the attribute; `Login` does not. -/
theorem in_group_selective :
    leafAt (.actionInAny [readsGroup]) read = some (some (.required (.bool .anyBool))) ∧
      leafAt (.actionInAny [readsGroup]) login = some none := by
  decide +kernel

/-- **An unconstrained `action`**: every action gains the attribute. -/
theorem unconstrained_all :
    leafAt (.actionScope .any) read = some (some (.required (.bool .anyBool))) ∧
      leafAt (.actionScope .any) login = some (some (.required (.bool .anyBool))) := by
  decide +kernel

end Dogwood.Examples.SelectiveAugment
