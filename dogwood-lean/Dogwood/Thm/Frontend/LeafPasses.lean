import Dogwood.Thm.Frontend.LeafPasses.Conservative
import Dogwood.Thm.Frontend.LeafPasses.Pins
import Dogwood.Thm.Frontend.LeafPasses.Unorder
import Dogwood.Thm.Frontend.LeafPasses.Relativize
import Dogwood.Frontend.Identity

/-!
# Theorems about the frontend: pin injection, the executable form of a leaf, its relativization, and rule identity (WP5)

The passes over each temporal leaf (`Dogwood.Frontend.LeafPasses`) and the extended relation
that gives the relativized leaves a meaning (`Dogwood.Frontend.LeafPasses.Semantics`):

* `LeafPasses.Conservative`: the extended relation `XSat`, with timepoints unordered and binders
  ranging over every value, is the specification's `Sat` (`xsat_iff_sat`);
* `LeafPasses.Pins`: pin injection commutes with the projection to the specification's formulas
  and the specification's pin injection (`injectCond_toFormula`, `injectCond_toFormula_of_agrees`);
* `LeafPasses.Unorder`: the executable form is the identity on a leaf that orders no timepoint
  (`unorderCond_eq_self`), and means the authored leaf under the sorted reading
  (`xsat_unorder`); two counterexamples show what the sorted reading is needed for;
* `LeafPasses.Relativize`: relativization is the identity without universal pins
  (`relativize_of_universalPins_nil`), keeps whether a condition implies mine
  (`impliesMine_relCond`), and its μ is the specification's visibility (`xsat_mu_iff_visible`).

The relativization theorem itself is stated as `LeafPasses.RelativizationTheorem`, and proved in
`Dogwood.Thm.Frontend.Relativization`. This module adds the shape of the rule identity's leaf
encodings (`leaves_length`).
-/

namespace Dogwood.Thm.Frontend

open Dogwood.Frontend RuleIdentity

theorem length_pushAt {α : Type} (acc : List (List α)) (k : Nat) (x : α) :
    (pushAt acc k x).length = acc.length := by
  simp [pushAt]

theorem length_foldl_pushAt {α β : Type} (g : β → Nat × α) :
    (xs : List β) → (acc : List (List α)) →
    (xs.foldl (fun acc b => pushAt acc (g b).1 (g b).2) acc).length = acc.length
  | [], _ => rfl
  | b :: xs, acc => by
    rw [List.foldl_cons, length_foldl_pushAt g xs, length_pushAt]

/-- **One list of leaf encodings per rule.** -/
theorem leaves_length {c : Cedarified} {pinned : List ContextField}
    {ls : List (List (String × String))} (h : leaves c pinned = .ok ls) :
    ls.length = c.ruleIds.length := by
  simp only [leaves, pure, Except.pure, Except.ok.injEq] at h
  subst h
  have h₁ := length_foldl_pushAt
    (fun (x : ProviderField × Nat) => (x.2, (canonicalFieldName (c.ruleKeys.getD x.2 "") x.1.fieldName,
      canonicalProviderField x.1))) (c.providerFields.zip c.providerRules)
  have h₂ := length_foldl_pushAt
    (fun (x : ContextField × Nat) => (x.2, (canonicalFieldName (c.ruleKeys.getD x.2 "") x.1.fieldName,
      canonicalContextField x.1))) (pinned.zip c.temporalRules)
  simp only at h₁ h₂
  rw [h₁, h₂, List.length_replicate]

end Dogwood.Thm.Frontend
