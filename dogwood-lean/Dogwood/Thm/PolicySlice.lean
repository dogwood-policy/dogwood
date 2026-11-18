import Dogwood.Thm.DecisionSoundness
import Dogwood.Thm.Implementation
import Cedar.Thm.Authorization.Authorizer
import Cedar.Thm.Data.Set

/-!
# Policy slicing

cedar-lean proves that authorizing with a sound slice of the policies, and in particular with the
policies whose scope holds, gives the same response as authorizing with all of them
(`Cedar.Thm.isAuthorized_eq_for_sound_policy_slice`,
`Cedar.Thm.isAuthorized_eq_for_scope_based_policy_slice`). The same holds of Dogwood, in three
layers:

* **At one decision, at every leaf valuation** (`isAuthorized_eq_for_sound_policy_slice`,
  `isAuthorized_eq_for_scope_slice`). A rule whose scope does not hold evaluates to `false`
  before it reaches a leaf (`evaluate_toExpr_of_not_scopeHolds`), so it is neither satisfied nor
  erring, whatever its leaves' values.
* **Over a trace, slicing the response** (`authorize_eq_response_slice`). The decision's checks
  read every rule, its response only a slice that keeps the rules whose scope holds. The checks
  include the providers' (checks 7 and 8): a failing provider of a rule outside the slice still
  fails the decision closed.
* **An implementation's leaves** (`authorizeWithEach_eq`, `authorizeWith_eq_of_scope`, and
  `authorize_eq_each_of_scope` under every reading). An implementation must compute the temporal
  leaves of the rules whose scope holds, where their facts hold; any other leaf may take any
  value, `false` say. Leaf values are given rule by rule, as an implementation that keys a leaf by
  its rule gives them, so the same condition may be computed for one rule and not for another.
  They are not given occurrence by occurrence: two occurrences of one condition in one rule take
  the same value, and so do two equal rules. An implementation that computes all of a rule's
  leaves or none of them, as the crate's `DecisionLeafMap` does, is covered; one that computes
  some occurrences of a condition in a rule and not others is not.

Slicing selects which leaves are computed, not which events they see: every leaf that is
computed must hold as over the whole trace (`PolicySet.LeafHolds`).
-/

namespace Dogwood.Thm

open Dogwood.Spec Dogwood.Spec.Temporal
open Cedar.Spec (Request Entities EntityUID Response)
open Cedar.Data

/-! ## At one decision -/

private theorem evaluate_and_of_false {θ : Leaves} {req : Request} {es : Entities} {a b : Expr}
    (h : evaluate θ a req es = .ok (.prim (.bool false))) :
    evaluate θ (.and a b) req es = .ok (.prim (.bool false)) := by
  simp [evaluate, h, Cedar.Spec.Result.as, Coe.coe, Cedar.Spec.Value.asBool]

private theorem evaluate_and_of_true {θ : Leaves} {req : Request} {es : Entities} {a b : Expr}
    (ha : evaluate θ a req es = .ok (.prim (.bool true)))
    (hb : evaluate θ b req es = .ok (.prim (.bool false))) :
    evaluate θ (.and a b) req es = .ok (.prim (.bool false)) := by
  simp [evaluate, ha, hb, Cedar.Spec.Result.as, Coe.coe, Cedar.Spec.Value.asBool]

private theorem bool_of_producesBool {e : Cedar.Spec.Expr} {req : Request} {es : Entities}
    (h : Cedar.Thm.producesBool e req es) :
    ∃ b, Cedar.Spec.evaluate e req es = .ok (.prim (.bool b)) := by
  unfold Cedar.Thm.producesBool at h
  split at h
  · next b heq => exact ⟨b, heq⟩
  · simp at h

/-- **A rule whose scope does not hold evaluates to `false`**, at every leaf valuation: the scope
constraints come first, never err, and short-circuit before the conditions. -/
theorem evaluate_toExpr_of_not_scopeHolds (θ : Leaves) {p : Policy} {req : Request}
    {es : Entities} (h : ¬ p.ScopeHolds req es) :
    evaluate θ p.toExpr req es = .ok (.prim (.bool false)) := by
  let cp : Cedar.Spec.Policy := ⟨p.id, p.effect, p.principalScope, p.actionScope,
    p.resourceScope, []⟩
  obtain ⟨b₁, h₁⟩ := bool_of_producesBool (Cedar.Thm.principal_scope_produces_boolean cp req es)
  obtain ⟨b₂, h₂⟩ := bool_of_producesBool (Cedar.Thm.action_scope_produces_boolean cp req es)
  obtain ⟨b₃, h₃⟩ := bool_of_producesBool (Cedar.Thm.resource_scope_produces_boolean cp req es)
  have e₁ := (evaluate_ofCedar θ p.principalScope.toExpr req es).trans h₁
  have e₂ := (evaluate_ofCedar θ p.actionScope.toExpr req es).trans h₂
  have e₃ := (evaluate_ofCedar θ p.resourceScope.toExpr req es).trans h₃
  unfold Policy.toExpr
  cases b₁
  · exact evaluate_and_of_false e₁
  cases b₂
  · exact evaluate_and_of_true e₁ (evaluate_and_of_false e₂)
  cases b₃
  · exact evaluate_and_of_true e₁ (evaluate_and_of_true e₂ (evaluate_and_of_false e₃))
  exact absurd ⟨h₁, h₂, h₃⟩ h

/-- A rule whose scope does not hold is neither satisfied nor erring, whatever its leaves. -/
theorem satisfied_hasError_of_not_scopeHolds {θ : Leaves} {p : Policy} {req : Request}
    {es : Entities} (h : ¬ p.ScopeHolds req es) :
    satisfied θ p req es = false ∧ hasError θ p req es = false := by
  have he := evaluate_toExpr_of_not_scopeHolds θ h
  constructor
  · simp [satisfied, he]
  · simp [hasError, he]

/-- **A sound slice** of `policies` at a request, under the leaf valuation `θ`: a sublist that
keeps every rule that is satisfied or errs there (Cedar's `IsSoundPolicySlice`). -/
def IsSoundPolicySlice (θ : Leaves) (req : Request) (es : Entities) (slice policies : Policies) :
    Prop :=
  slice ⊆ policies ∧
  ∀ p ∈ policies, p ∉ slice → satisfied θ p req es = false ∧ hasError θ p req es = false

private theorem filterMap_slice_equiv {α : Type} {f : Policy → Option α} {slice policies : Policies}
    (hsub : slice ⊆ policies) (hnone : ∀ p ∈ policies, p ∉ slice → f p = none) :
    slice.filterMap f ≡ policies.filterMap f := by
  constructor
  · intro x hx
    obtain ⟨a, ha, hfa⟩ := List.mem_filterMap.mp hx
    exact List.mem_filterMap.mpr ⟨a, hsub ha, hfa⟩
  · intro x hx
    obtain ⟨a, ha, hfa⟩ := List.mem_filterMap.mp hx
    by_cases has : a ∈ slice
    · exact List.mem_filterMap.mpr ⟨a, has, hfa⟩
    · rw [hnone a ha has] at hfa
      cases hfa

/-- **Policy slicing.** A sound slice decides as the policies do: the same decision, determining
policies, and erroring policies. -/
theorem isAuthorized_eq_for_sound_policy_slice {θ : Leaves} {req : Request} {es : Entities}
    {slice policies : Policies} (h : IsSoundPolicySlice θ req es slice policies) :
    isAuthorized θ req es slice = isAuthorized θ req es policies := by
  have hs : ∀ eff, satisfiedPolicies θ eff slice req es = satisfiedPolicies θ eff policies req es :=
    fun eff => by
      unfold satisfiedPolicies
      rw [Set.make_make_eqv]
      exact filterMap_slice_equiv h.1 fun p hp hn => by
        simp [satisfiedWithEffect, (h.2 p hp hn).1]
  have he : errorPolicies θ slice req es = errorPolicies θ policies req es := by
    unfold errorPolicies
    rw [Set.make_make_eqv]
    exact filterMap_slice_equiv h.1 fun p hp hn => by simp [errored, (h.2 p hp hn).2]
  simp only [isAuthorized, hs, he]

/-- A sublist that keeps every rule whose scope holds, such as the rules whose action scope
admits the request's action, is a sound slice at every leaf valuation. -/
theorem isSoundPolicySlice_of_scope {θ : Leaves} {req : Request} {es : Entities}
    {slice policies : Policies} (hsub : slice ⊆ policies)
    (hkeep : ∀ p ∈ policies, p.ScopeHolds req es → p ∈ slice) :
    IsSoundPolicySlice θ req es slice policies :=
  ⟨hsub, fun p hp hn => satisfied_hasError_of_not_scopeHolds fun hs => hn (hkeep p hp hs)⟩

/-- The rules whose scope holds at the request. -/
def scopeSlice (policies : Policies) (req : Request) (es : Entities) : Policies :=
  policies.filter (·.scopeHolds req es)

/-- **Slicing by scope.** At every leaf valuation, the rules whose scope holds decide as all the
rules do (Cedar's `isAuthorized_eq_for_scope_based_policy_slice`). -/
theorem isAuthorized_eq_for_scope_slice (θ : Leaves) (req : Request) (es : Entities)
    (policies : Policies) :
    isAuthorized θ req es (scopeSlice policies req es) = isAuthorized θ req es policies :=
  isAuthorized_eq_for_sound_policy_slice (isSoundPolicySlice_of_scope
    (fun _ hx => (List.mem_filter.mp hx).1)
    fun _ hp hs => List.mem_filter.mpr ⟨hp, scopeHolds_iff.mpr hs⟩)

/-! ## Over a trace: slicing the response -/

variable {ι : ImplChoices} {P : PolicySet} {ω : Provider.Providers} {σ : Trace} {n : Nat}

/-- A slicer picks, at each decision event and its principal and resource, a sublist of the
rules that keeps every rule whose scope holds there. -/
def SoundScopeSlicer (P : PolicySet) (slice : Event → EntityUID → EntityUID → Policies) : Prop :=
  ∀ e pr rs, slice e pr rs ⊆ P.policies ∧
    ∀ q ∈ P.policies, q.ScopeHolds (e.request pr rs) (P.decisionEntities e) → q ∈ slice e pr rs

/-- **Slicing the response, over a trace, under every reading.** The decision is the one whose
checks read every rule and whose response, under every completion of the reading, reads only the
slice. The checks still read every rule's providers: a failing provider of a rule outside the
slice still fails the decision closed. -/
theorem authorize_eq_response_slice {slice : Event → EntityUID → EntityUID → Policies}
    (hs : SoundScopeSlicer P slice) :
    P.authorize ι ω σ n =
      P.decideWith P.policies ω σ n fun e pr rs =>
        ι.supervaluate fun ι' =>
          isAuthorized (P.leaves ι' ω σ n e) (e.request pr rs) (P.decisionEntities e)
            (slice e pr rs) := by
  unfold PolicySet.authorize
  refine decideWith_congr rfl fun p pr rs _ _ => ?_
  simp only [PolicySet.respond]
  exact supervaluate_congr fun ι' _ =>
    (isAuthorized_eq_for_sound_policy_slice
      (isSoundPolicySlice_of_scope (hs _ _ _).1 (hs _ _ _).2)).symm

/-! ## An implementation's leaves -/

/-- **An implementation that computes the leaves of the rules whose scope holds decides as the
specification does**, under a total reading. At each admitted decision event, the value the
implementation gives a temporal leaf of a rule whose scope holds, at a position whose facts hold
(`Expr.leafFacts`), must be whether the leaf holds over the whole trace (`PolicySet.LeafHolds`);
every other leaf may take any value. The values are given rule by rule, so the same condition may
be computed for one rule and given any value for another. -/
theorem authorizeWithEach_eq {temporal : Event → Policy → Formula → Bool} (hι : ι.Total)
    (htemp : ∀ p pr rs, σ[n]? = some p → P.Admits P.policies ω p pr rs →
      ∀ q ∈ P.policies, q.ScopeHolds (p.event.request pr rs) (P.decisionEntities p.event) →
      ∀ φ F, (Sum.inl φ, F) ∈ q.toExpr.leafFacts [] →
      (∀ g ∈ F, g.HoldsIn (p.event.request pr rs) (P.decisionEntities p.event)) →
      (temporal p.event q φ = true ↔ P.LeafHolds ι σ n φ)) :
    P.authorizeWithEach ω σ n temporal = P.authorize ι ω σ n := by
  unfold PolicySet.authorizeWithEach PolicySet.authorize
  refine decideWith_congr rfl fun p pr rs hσ ha => ?_
  rw [respond_total hι, Option.some.injEq, isAuthorizedEach_eq (θ₀ := P.leaves ι ω σ n p.event)]
  · simp [List.map_map, Function.comp_def]
  · intro r hr
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hr
    apply evaluate_toExpr_congr
    intro hs l F hlF hF
    cases l with
    | inl φ =>
      show temporal p.event q φ = @decide (P.LeafHolds ι σ n φ) (Classical.propDecidable _)
      rw [Bool.eq_iff_iff]
      simp only [decide_eq_true_eq]
      exact htemp p pr rs hσ ha q hq hs φ F hlF hF
    | inr c => rfl

/-- **Per-rule leaf values, under every reading.** Under each completion of the reading, give each
rule a leaf valuation of its own that agrees with the specification's at that completion on the
leaves of the rules whose scope holds, where their facts hold. The decision supervaluated over
these per-rule valuations is the specification's. This joins the two slicings above: rules outside
the slice, and leaves outside the rules whose scope holds, are left free. -/
theorem authorize_eq_each_of_scope {θ : ImplChoices → Event → Policy → Leaves}
    (h : ∀ p pr rs, σ[n]? = some p → P.Admits P.policies ω p pr rs → ∀ ι', ι'.Completes ι →
      ∀ q ∈ P.policies, q.ScopeHolds (p.event.request pr rs) (P.decisionEntities p.event) →
      ∀ l F, (l, F) ∈ q.toExpr.leafFacts [] →
      (∀ g ∈ F, g.HoldsIn (p.event.request pr rs) (P.decisionEntities p.event)) →
      LeafAgree (θ ι' p.event q) (P.leaves ι' ω σ n p.event) l) :
    P.decideWith P.policies ω σ n (fun e pr rs => ι.supervaluate fun ι' =>
      isAuthorizedEach (e.request pr rs) (P.decisionEntities e)
        (P.policies.map fun q => (q, θ ι' e q))) = P.authorize ι ω σ n := by
  unfold PolicySet.authorize
  refine decideWith_congr rfl fun p pr rs hσ ha => ?_
  simp only [PolicySet.respond]
  refine supervaluate_congr fun ι' hc => ?_
  rw [isAuthorizedEach_eq (θ₀ := P.leaves ι' ω σ n p.event)]
  · simp [List.map_map, Function.comp_def]
  · intro r hr
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hr
    exact evaluate_toExpr_congr q fun hs l F hlF hF => h p pr rs hσ ha ι' hc q hq hs l F hlF hF

/-- An implementation that gives every rule the same leaf values decides as `authorizeWith`. -/
theorem authorizeWith_eq_authorizeWithEach (temporal : Event → Formula → Bool) :
    P.authorizeWith ω σ n temporal = P.authorizeWithEach ω σ n (fun e _ φ => temporal e φ) := by
  unfold PolicySet.authorizeWith PolicySet.authorizeWithEach
  simp only [isAuthorizedEach_const]

/-- **`authorizeWith_eq`, for the leaves of the rules whose scope holds only.** An implementation
that values each leaf by its condition decides as the specification does, under a total reading,
when it computes the temporal leaves of the rules whose scope holds, where their facts hold. -/
theorem authorizeWith_eq_of_scope {temporal : Event → Formula → Bool} (hι : ι.Total)
    (htemp : ∀ p pr rs, σ[n]? = some p → P.Admits P.policies ω p pr rs →
      ∀ q ∈ P.policies, q.ScopeHolds (p.event.request pr rs) (P.decisionEntities p.event) →
      ∀ φ F, (Sum.inl φ, F) ∈ q.toExpr.leafFacts [] →
      (∀ g ∈ F, g.HoldsIn (p.event.request pr rs) (P.decisionEntities p.event)) →
      (temporal p.event φ = true ↔ P.LeafHolds ι σ n φ)) :
    P.authorizeWith ω σ n temporal = P.authorize ι ω σ n := by
  rw [authorizeWith_eq_authorizeWithEach]
  exact authorizeWithEach_eq hι htemp

end Dogwood.Thm
