import Dogwood.Thm.Decision
import Cedar.Thm.Data.Set
import Cedar.Thm.Data.List

/-!
# Properties of authorization

Dogwood's per-request authorizer has the properties cedar-lean proves of Cedar's
(`Cedar.Thm.Authorization`), at every leaf valuation, and they carry over to
decisions over a trace:

* **Forbid overrides permit** (`forbid_overrides_permit`,
  `authorize_forbid_denies`): a satisfied `forbid` denies.
* **Deny by default** (`allowed_only_if_explicitly_permitted`, `default_deny`,
  `authorize_allow`): a request is allowed only when some `permit` is
  satisfied. With `allowed_iff_explicitly_permitted_and_not_forbidden`, a
  request is allowed exactly when some `permit` and no `forbid` is satisfied.
* **Order and duplicate independence** (`order_and_dup_independent`,
  `authorize_order_and_dup_independent`): two policy lists with the same
  members decide alike, so neither the order of the policies nor a repeated
  policy changes a decision (`dup_independent`).
* **Adding a `forbid` keeps a deny** (`unchanged_deny_when_add_forbid`,
  `authorize_unchanged_deny_when_add_forbid`): over a trace, unless the deny is a fail-closed for
  a temporal error and the added rule shares an id with another rule; so always under a total
  reading (`authorize_unchanged_deny_when_add_forbid_of_total`). A failed-closed decision stays a
  deny, since an added rule only adds checks that can fail.

These are properties of the policies at one decision. They are not properties
of the trace: ingesting the same event twice can change a decision, because a
denied request is still history that a later condition (a `count`, say) sees,
and reordering events can change a decision too.
-/

namespace Dogwood.Thm

open Dogwood.Spec
open Cedar.Spec (Request Entities Effect Decision EntityUID)
open Cedar.Data

/-! ## At one decision, for every leaf valuation -/

section

variable (θ : Leaves)

/-- Some policy of `policies` with effect `effect` is satisfied. -/
def HasSatisfiedEffect (effect : Effect) (req : Request) (es : Entities) (policies : Policies) :
    Prop :=
  ∃ p ∈ policies, p.effect = effect ∧ satisfied θ p req es = true

/-- Some `forbid` is satisfied. -/
def IsExplicitlyForbidden : Request → Entities → Policies → Prop :=
  HasSatisfiedEffect θ .forbid

/-- Some `permit` is satisfied. A `forbid` may still be satisfied too. -/
def IsExplicitlyPermitted : Request → Entities → Policies → Prop :=
  HasSatisfiedEffect θ .permit

variable {θ}

theorem satisfied_iff_satisfiedPolicies_nonempty {effect : Effect} {req : Request}
    {es : Entities} {policies : Policies} :
    HasSatisfiedEffect θ effect req es policies ↔
      (satisfiedPolicies θ effect policies req es).isEmpty = false := by
  simp [HasSatisfiedEffect, satisfiedPolicies, satisfiedWithEffect]

/-- **Forbid overrides permit.** -/
theorem forbid_overrides_permit (req : Request) (es : Entities) (policies : Policies)
    (h : IsExplicitlyForbidden θ req es policies) :
    (isAuthorized θ req es policies).decision = .deny := by
  unfold isAuthorized
  rw [IsExplicitlyForbidden, satisfied_iff_satisfiedPolicies_nonempty] at h
  simp [h]

theorem allowed_only_if_explicitly_permitted (req : Request) (es : Entities) (policies : Policies)
    (h : (isAuthorized θ req es policies).decision = .allow) :
    IsExplicitlyPermitted θ req es policies := by
  unfold isAuthorized at h
  rw [IsExplicitlyPermitted, satisfied_iff_satisfiedPolicies_nonempty]
  cases hp : (satisfiedPolicies θ .permit policies req es).isEmpty
  · rfl
  · simp [hp] at h

/-- **Deny by default.** -/
theorem default_deny (req : Request) (es : Entities) (policies : Policies)
    (h : ¬ IsExplicitlyPermitted θ req es policies) :
    (isAuthorized θ req es policies).decision = .deny := by
  cases hd : (isAuthorized θ req es policies).decision
  · exact absurd (allowed_only_if_explicitly_permitted req es policies hd) h
  · rfl

theorem allowed_iff_explicitly_permitted_and_not_forbidden (req : Request) (es : Entities)
    (policies : Policies) :
    (isAuthorized θ req es policies).decision = .allow ↔
      IsExplicitlyPermitted θ req es policies ∧ ¬ IsExplicitlyForbidden θ req es policies := by
  constructor
  · intro h
    refine ⟨allowed_only_if_explicitly_permitted req es policies h, fun hf => ?_⟩
    rw [forbid_overrides_permit req es policies hf] at h
    cases h
  · rintro ⟨hp, hf⟩
    rw [IsExplicitlyPermitted, satisfied_iff_satisfiedPolicies_nonempty] at hp
    rw [IsExplicitlyForbidden, satisfied_iff_satisfiedPolicies_nonempty] at hf
    unfold isAuthorized
    simp [hp, hf]

theorem satisfiedPolicies_order_and_dup_independent {policies₁ policies₂ : Policies}
    (effect : Effect) (req : Request) (es : Entities) (h : policies₁ ≡ policies₂) :
    satisfiedPolicies θ effect policies₁ req es = satisfiedPolicies θ effect policies₂ req es := by
  unfold satisfiedPolicies
  rw [Set.make_make_eqv]
  exact List.filterMap_equiv (satisfiedWithEffect θ effect · req es) policies₁ policies₂ h

theorem errorPolicies_order_and_dup_independent {policies₁ policies₂ : Policies}
    (req : Request) (es : Entities) (h : policies₁ ≡ policies₂) :
    errorPolicies θ policies₁ req es = errorPolicies θ policies₂ req es := by
  unfold errorPolicies
  rw [Set.make_make_eqv]
  exact List.filterMap_equiv (errored θ · req es) policies₁ policies₂ h

/-- **Order and duplicate independence.** Two policy lists with the same members
decide alike: the same decision, determining policies, and erroring policies. -/
theorem order_and_dup_independent (req : Request) (es : Entities) {policies₁ policies₂ : Policies}
    (h : policies₁ ≡ policies₂) :
    isAuthorized θ req es policies₁ = isAuthorized θ req es policies₂ := by
  simp [isAuthorized, satisfiedPolicies_order_and_dup_independent _ req es h,
    errorPolicies_order_and_dup_independent req es h]

/-- A repeated policy list decides as the list does. -/
theorem dup_independent (req : Request) (es : Entities) (policies : Policies) :
    isAuthorized θ req es (policies ++ policies) = isAuthorized θ req es policies :=
  order_and_dup_independent req es ⟨fun _ h => by simpa using h, fun _ h => by simp [h]⟩

/-- With a `forbid` added, an allow is an allow without it. -/
theorem allow_of_allow_add_forbid (req : Request) (es : Entities) (policies : Policies)
    {q : Policy} (hq : q.effect = .forbid)
    (h : (isAuthorized θ req es (q :: policies)).decision = .allow) :
    (isAuthorized θ req es policies).decision = .allow := by
  obtain ⟨hp, hf⟩ := (allowed_iff_explicitly_permitted_and_not_forbidden req es _).mp h
  refine (allowed_iff_explicitly_permitted_and_not_forbidden req es _).mpr ⟨?_, ?_⟩
  · obtain ⟨p, hmem, heff, hsat⟩ := hp
    rcases List.mem_cons.mp hmem with rfl | hmem
    · rw [hq] at heff; cases heff
    · exact ⟨p, hmem, heff, hsat⟩
  · rintro ⟨p, hmem, heff, hsat⟩
    exact hf ⟨p, List.mem_cons_of_mem _ hmem, heff, hsat⟩

/-- **Adding a `forbid` keeps a deny.** -/
theorem unchanged_deny_when_add_forbid (req : Request) (es : Entities) (policies : Policies)
    {q : Policy} (hq : q.effect = .forbid)
    (h : (isAuthorized θ req es policies).decision = .deny) :
    (isAuthorized θ req es (q :: policies)).decision = .deny := by
  cases hd : (isAuthorized θ req es (q :: policies)).decision with
  | deny => rfl
  | allow =>
    rw [allow_of_allow_add_forbid req es policies hq hd] at h
    cases h

/-- The determining policies of an allow are the satisfied `permit`s. -/
theorem isAuthorized_determiningPolicies_of_allow {req : Request} {es : Entities}
    {policies : Policies}
    (h : (isAuthorized θ req es policies).decision = .allow) :
    (isAuthorized θ req es policies).determiningPolicies =
      satisfiedPolicies θ .permit policies req es := by
  unfold isAuthorized at h ⊢
  dsimp only at h ⊢
  split
  · rfl
  · rename_i hc
    simp [hc] at h

/-- The erroring policies of a response are the rules that err, whatever the decision. -/
theorem isAuthorized_erroringPolicies (req : Request) (es : Entities) (policies : Policies) :
    (isAuthorized θ req es policies).erroringPolicies = errorPolicies θ policies req es := by
  unfold isAuthorized
  dsimp only
  split <;> rfl

/-- A `forbid` is never a satisfied `permit`. -/
theorem satisfiedPolicies_permit_cons_forbid (req : Request) (es : Entities) (policies : Policies)
    {q : Policy} (hq : q.effect = .forbid) :
    satisfiedPolicies θ .permit (q :: policies) req es = satisfiedPolicies θ .permit policies req es := by
  simp [satisfiedPolicies, satisfiedWithEffect, hq]

/-- The ids of the rules that err are ids of the rules. -/
theorem mem_errored_ids {req : Request} {es : Entities} {policies : Policies} {x : Cedar.Spec.PolicyID}
    (h : x ∈ policies.filterMap (errored θ · req es)) : ∃ p ∈ policies, p.id = x := by
  obtain ⟨p, hp, he⟩ := List.mem_filterMap.mp h
  unfold errored at he
  split at he
  · exact ⟨p, hp, Option.some.inj he⟩
  · cases he

end

/-- **An added `forbid` with a fresh id loses no information about an allow.** Two leaf valuations
that allow alike with a `forbid` added, whose id no other rule has, allow alike without it: the
added rule changes neither the decision nor the determining policies, and its id can be taken back
out of the erroring policies. -/
theorem isAuthorized_eq_of_add_forbid {θ₁ θ₂ : Leaves} {req : Request} {es : Entities}
    {policies : Policies} {q : Policy} (hq : q.effect = .forbid)
    (hfresh : ∀ p ∈ policies, p.id ≠ q.id)
    (heq : isAuthorized θ₁ req es (q :: policies) = isAuthorized θ₂ req es (q :: policies))
    (ha : (isAuthorized θ₁ req es (q :: policies)).decision = .allow) :
    isAuthorized θ₁ req es policies = isAuthorized θ₂ req es policies := by
  have ha₂ : (isAuthorized θ₂ req es (q :: policies)).decision = .allow := heq ▸ ha
  have hd₁ := allow_of_allow_add_forbid req es policies hq ha
  have hd₂ := allow_of_allow_add_forbid req es policies hq ha₂
  have hdet : (isAuthorized θ₁ req es policies).determiningPolicies =
      (isAuthorized θ₂ req es policies).determiningPolicies := by
    rw [isAuthorized_determiningPolicies_of_allow hd₁, isAuthorized_determiningPolicies_of_allow hd₂,
      ← satisfiedPolicies_permit_cons_forbid req es policies hq,
      ← satisfiedPolicies_permit_cons_forbid req es policies hq,
      ← isAuthorized_determiningPolicies_of_allow ha, ← isAuthorized_determiningPolicies_of_allow ha₂, heq]
  have herr : (isAuthorized θ₁ req es policies).erroringPolicies =
      (isAuthorized θ₂ req es policies).erroringPolicies := by
    have hc := congrArg Cedar.Spec.Response.erroringPolicies heq
    rw [isAuthorized_erroringPolicies, isAuthorized_erroringPolicies] at hc ⊢
    unfold errorPolicies at hc ⊢
    rw [Set.make_make_eqv] at hc ⊢
    -- An id of a rule of `policies` is not `q`'s, so it errs with `q` added exactly as without.
    have key : ∀ {θ θ' : Leaves},
        (q :: policies).filterMap (errored θ · req es) ⊆
          (q :: policies).filterMap (errored θ' · req es) →
        policies.filterMap (errored θ · req es) ⊆ policies.filterMap (errored θ' · req es) := by
      intro θ θ' hsub x hx
      obtain ⟨p, hp, hpx⟩ := mem_errored_ids hx
      have hx' := hsub (List.mem_filterMap.mpr (by
        obtain ⟨a, ha, he⟩ := List.mem_filterMap.mp hx
        exact ⟨a, List.mem_cons_of_mem _ ha, he⟩))
      obtain ⟨a, ha, he⟩ := List.mem_filterMap.mp hx'
      rcases List.mem_cons.mp ha with rfl | ha
      · unfold errored at he
        split at he
        · exact absurd (hpx.trans (Option.some.inj he).symm) (hfresh p hp)
        · cases he
      · exact List.mem_filterMap.mpr ⟨a, ha, he⟩
    exact ⟨key hc.1, key hc.2⟩
  have hdec := hd₁.trans hd₂.symm
  revert hdec hdet herr
  cases isAuthorized θ₁ req es policies
  cases isAuthorized θ₂ req es policies
  intro h₁ h₂ h₃
  congr

/-! ## Over a trace -/

variable {ι : Temporal.ImplChoices} {P : PolicySet} {ω : Provider.Providers} {σ : Trace} {n : Nat}

/-- **Deny by default, over a trace.** An event the policy set allows is a decision event
with a principal and a resource, every check of which passes, at whose leaf valuation under every
completion of the reading some `permit` and no `forbid` is satisfied. A history-only event decides
nothing, and a failed-closed decision denies. -/
theorem authorize_allow (h : (P.authorize ι ω σ n).decision? = some .allow) :
    ∃ p pr rs, σ[n]? = some p ∧ P.Admits P.policies ω p pr rs ∧
      ∀ ι', ι'.Completes ι →
        IsExplicitlyPermitted (P.leaves ι' ω σ n p.event) (p.event.request pr rs)
          (P.decisionEntities p.event) P.policies ∧
        ¬ IsExplicitlyForbidden (P.leaves ι' ω σ n p.event) (p.event.request pr rs)
          (P.decisionEntities p.event) P.policies := by
  obtain ⟨p, pr, rs, r, hσ, ha, hr, hd⟩ := decideWith_decision?_allow h
  have hall := supervaluate_eq_some_iff.mp hr
  refine ⟨p, pr, rs, hσ, ha, fun ι' hc => ?_⟩
  apply (allowed_iff_explicitly_permitted_and_not_forbidden _ _ _).mp
  rw [hall ι' hc]
  exact hd

/-- **Forbid overrides permit, over a trace.** At a decision event with a principal and a
resource, a `forbid` satisfied at the leaf valuation of some completion of the reading denies. -/
theorem authorize_forbid_denies {p : TimePoint} {pr rs : EntityUID} (hσ : σ[n]? = some p)
    (hk : P.schema.isDecisionKind p.event.kind = true) (hpr : p.event.principal = some pr)
    (hrs : p.event.resource = some rs)
    (hf : ∃ ι', ι'.Completes ι ∧ IsExplicitlyForbidden (P.leaves ι' ω σ n p.event)
      (p.event.request pr rs) (P.decisionEntities p.event) P.policies) :
    (P.authorize ι ω σ n).decision? = some .deny := by
  have hsome : (P.authorize ι ω σ n).decision?.isSome = true :=
    decideWith_decision?_isSome hσ hk
  cases hd : (P.authorize ι ω σ n).decision? with
  | none => simp [hd] at hsome
  | some d =>
    cases d with
    | deny => rfl
    | allow =>
      obtain ⟨p', pr', rs', hσ', ha, hall⟩ := authorize_allow hd
      rw [hσ] at hσ'
      cases hσ'
      have hpr' : pr = pr' := Option.some.inj (hpr.symm.trans ha.principal)
      have hrs' : rs = rs' := Option.some.inj (hrs.symm.trans ha.resource)
      subst hpr' hrs'
      obtain ⟨ι', hc, hf⟩ := hf
      exact absurd hf (hall ι' hc).2

/-- Two policy lists with the same members fail on the same events. -/
theorem providersFail_equiv {policies₁ policies₂ : Policies} (h : policies₁ ≡ policies₂)
    (ω : Provider.Providers) (e : Event) :
    policies₁.providersFail ω e = policies₂.providersFail ω e := by
  have key : ∀ {a b : Policies}, a ⊆ b → a.providersFail ω e = true →
      b.providersFail ω e = true := by
    intro a b hab ha
    rw [providersFail_iff] at ha ⊢
    obtain ⟨c, hc, he⟩ := ha
    refine ⟨c, ?_, he⟩
    simp only [Policies.providerCalls, List.mem_flatMap] at hc ⊢
    obtain ⟨p, hp, hc⟩ := hc
    exact ⟨p, hab hp, hc⟩
  cases h1 : policies₁.providersFail ω e <;> cases h2 : policies₂.providersFail ω e
  · rfl
  · exact absurd (key h.2 h2) (by simp [h1])
  · exact absurd (key h.1 h1) (by simp [h2])
  · rfl

/-- Two policy lists with the same members have the same provider invocations. -/
theorem mem_providerCalls_equiv {policies₁ policies₂ : Policies} (h : policies₁ ≡ policies₂)
    (c : Provider.Call) : c ∈ policies₁.providerCalls ↔ c ∈ policies₂.providerCalls := by
  simp only [Policies.providerCalls, List.mem_flatMap]
  exact ⟨fun ⟨p, hp, hc⟩ => ⟨p, h.1 hp, hc⟩, fun ⟨p, hp, hc⟩ => ⟨p, h.2 hp, hc⟩⟩

/-- Two policy lists with the same members have conforming provider outputs on the same
events. -/
theorem providerOutputsConform_equiv {policies₁ policies₂ : Policies} (h : policies₁ ≡ policies₂)
    (P : PolicySet) (ω : Provider.Providers) (e : Event) :
    P.providerOutputsConform policies₁ ω e = P.providerOutputsConform policies₂ ω e := by
  unfold PolicySet.providerOutputsConform
  rw [Bool.eq_iff_iff, List.all_eq_true, List.all_eq_true]
  exact ⟨fun h' c hc => h' c ((mem_providerCalls_equiv h c).mpr hc),
    fun h' c hc => h' c ((mem_providerCalls_equiv h c).mp hc)⟩

/-- Two policy lists with the same members read the same scope entities. -/
theorem scopeEntitiesSupplied_equiv {policies₁ policies₂ : Policies} (h : policies₁ ≡ policies₂)
    (P : PolicySet) (e : Event) (pr rs : EntityUID) :
    P.scopeEntitiesSupplied policies₁ e pr rs = P.scopeEntitiesSupplied policies₂ e pr rs := by
  unfold PolicySet.scopeEntitiesSupplied
  rw [Bool.eq_iff_iff, List.all_eq_true, List.all_eq_true]
  exact ⟨fun h' q hq => h' q (h.2 hq), fun h' q hq => h' q (h.1 hq)⟩

/-- The outcome depends on the rules only through their provider invocations, the scope entities
they read, and the response. -/
theorem decideWith_rules_congr {rules₁ rules₂ : Policies}
    {respond : Event → EntityUID → EntityUID → Option Cedar.Spec.Response}
    (h₁ : ∀ e, rules₁.providersFail ω e = rules₂.providersFail ω e)
    (h₂ : ∀ e, P.providerOutputsConform rules₁ ω e = P.providerOutputsConform rules₂ ω e)
    (h₃ : ∀ e pr rs, P.scopeEntitiesSupplied rules₁ e pr rs = P.scopeEntitiesSupplied rules₂ e pr rs) :
    P.decideWith rules₁ ω σ n respond = P.decideWith rules₂ ω σ n respond := by
  simp only [PolicySet.decideWith, h₁, h₂, h₃]

/-- **Order and duplicate independence, over a trace.** Replacing a policy set's policies by a
list with the same members changes no outcome, at any timepoint of any trace. -/
theorem authorize_order_and_dup_independent {policies₁ policies₂ : Policies}
    (h : policies₁ ≡ policies₂) :
    ({ P with policies := policies₁ } : PolicySet).authorize ι ω σ n =
      ({ P with policies := policies₂ } : PolicySet).authorize ι ω σ n := by
  unfold PolicySet.authorize
  have hP : ∀ ps rules respond, ({ P with policies := ps } : PolicySet).decideWith rules ω σ n
      respond = P.decideWith rules ω σ n respond := fun _ _ _ => rfl
  dsimp only
  rw [hP policies₁, hP policies₂,
    decideWith_rules_congr (providersFail_equiv h ω) (providerOutputsConform_equiv h P ω)
      (scopeEntitiesSupplied_equiv h P)]
  refine decideWith_congr rfl fun p pr rs _ _ => ?_
  simp only [PolicySet.respond]
  exact supervaluate_congr fun ι' _ => order_and_dup_independent _ _ h

/-- An event every check of which passes for a list of rules passes them without its first rule,
under the same schemas, whatever the policy set's own rules. -/
theorem _root_.Dogwood.Spec.PolicySet.Admits.of_cons {q : Policy} {ps policies : Policies} {p : TimePoint} {pr rs : EntityUID}
    (h : ({ P with policies } : PolicySet).Admits (q :: ps) ω p pr rs) : P.Admits ps ω p pr rs where
  kind := h.kind
  principal := h.principal
  resource := h.resource
  event := h.event
  request := h.request
  entities := h.entities
  scopes := by
    have hs := h.scopes
    unfold PolicySet.scopeEntitiesSupplied at hs ⊢
    rw [List.all_cons, Bool.and_eq_true] at hs
    exact hs.2
  providers := by
    have hω := h.providers
    simp only [Policies.providersFail, Policies.providerCalls, List.flatMap_cons, List.any_append,
      Bool.or_eq_false_iff] at hω ⊢
    exact hω.2
  outputs := by
    have ho := h.outputs
    simp only [PolicySet.providerOutputsConform, Policies.providerCalls, List.flatMap_cons,
      List.all_append, Bool.and_eq_true] at ho ⊢
    exact ho.2

/-- A policy set and the same policy set with other rules decide nothing at the same events. -/
theorem authorize_decision?_none_iff {policies : Policies} :
    (({ P with policies } : PolicySet).authorize ι ω σ n).decision? = none ↔
      (P.authorize ι ω σ n).decision? = none := by
  have key : ∀ (Q : PolicySet), Q.schema = P.schema →
      ((Q.authorize ι ω σ n).decision? = none ↔
        ∀ p, σ[n]? = some p → P.schema.isDecisionKind p.event.kind = false) := by
    intro Q hQ
    constructor
    · intro hd p hσ
      cases hk : P.schema.isDecisionKind p.event.kind
      · rfl
      · have := decideWith_decision?_isSome (P := Q) (rules := Q.policies) (ω := ω)
          (respond := Q.respond ι ω σ n) hσ (hQ ▸ hk)
        unfold PolicySet.authorize at hd
        rw [hd] at this
        cases this
    · intro hk
      unfold PolicySet.authorize
      cases hσ : σ[n]? with
      | none => simp [PolicySet.decideWith, hσ, Outcome.decision?]
      | some p => rw [decideWith_history_only hσ (hQ ▸ hk p hσ)]; rfl
  exact (key ({ P with policies } : PolicySet) rfl).trans (key P rfl).symm

/-- Under a total reading, no decision fails closed for a temporal error. -/
theorem authorize_ne_temporalError_of_total (hι : ι.Total) :
    P.authorize ι ω σ n ≠ .failClosed .temporalError := by
  intro h
  obtain ⟨p, pr, rs, _, _, hr⟩ := decideWith_eq_temporalError h
  rw [respond_total hι] at hr
  cases hr

/-- **Adding a `forbid` keeps a deny, over a trace.** A policy set that denies the event at
timepoint `n`, by failing closed or by its response, still denies it once a `forbid` is added to
its rules, unless its deny is a fail-closed for a temporal error and the added rule shares an id
with one of its rules.

That exception is real. Under a reading that reports errors, the response is supervaluated: it is
the response every completion of the reading gives, erroring policies included, and the decision
fails closed when they differ. Completions that allow alike, and differ only in whether a rule
errs, can be made to agree by an added `forbid` that has that rule's id and errs where it does
not. With the id fresh, completions that agree with the `forbid` added on an allow agree without
it (`isAuthorized_eq_of_add_forbid`).

The rules here observe the whole trace. A rule deployed while events flow is decided by
`PolicySet.authorizeDeployed`. -/
theorem authorize_unchanged_deny_when_add_forbid {q : Policy} (hq : q.effect = .forbid)
    (hP : P.authorize ι ω σ n ≠ .failClosed .temporalError ∨ ∀ p ∈ P.policies, p.id ≠ q.id)
    (h : (P.authorize ι ω σ n).decision? = some .deny) :
    (({ P with policies := q :: P.policies } : PolicySet).authorize ι ω σ n).decision? =
      some .deny := by
  cases hd : (({ P with policies := q :: P.policies } : PolicySet).authorize ι ω σ n).decision? with
  | none =>
    rw [authorize_decision?_none_iff.mp hd] at h
    cases h
  | some d =>
    cases d with
    | deny => rfl
    | allow =>
      obtain ⟨p, pr, rs, r, hσ, ha, hr, hra⟩ := decideWith_decision?_allow hd
      have hall := supervaluate_eq_some_iff.mp hr
      have haP : P.Admits P.policies ω p pr rs := ha.of_cons
      -- Under every completion, the rules allow with the `forbid` added, and so without it.
      have hallow : ∀ ι', ι'.Completes ι →
          (isAuthorized (P.leaves ι' ω σ n p.event) (p.event.request pr rs)
            (P.decisionEntities p.event) (q :: P.policies)).decision = .allow := by
        intro ι' hc
        rw [show isAuthorized (P.leaves ι' ω σ n p.event) (p.event.request pr rs)
            (P.decisionEntities p.event) (q :: P.policies) = r from hall ι' hc]
        exact hra
      obtain ⟨ι₀, hc₀⟩ := exists_completes ι
      cases hresp : P.respond ι ω σ n p.event pr rs with
      | some rP =>
        -- The policy set's response is its response under every completion: an allow.
        rw [authorize_of_admits hσ haP, hresp] at h
        have hallow₀ := allow_of_allow_add_forbid _ _ _ hq (hallow ι₀ hc₀)
        rw [supervaluate_eq_some_iff.mp hresp ι₀ hc₀] at hallow₀
        simp [Outcome.decision?, hallow₀] at h
      | none =>
        rcases hP with hP | hfresh
        · exact absurd (by rw [authorize_of_admits hσ haP, hresp]) hP
        · -- With the id fresh, the completions agree without the `forbid` too.
          have hsome : P.respond ι ω σ n p.event pr rs =
              some (isAuthorized (P.leaves ι₀ ω σ n p.event) (p.event.request pr rs)
                (P.decisionEntities p.event) P.policies) := by
            apply supervaluate_eq_some_iff.mpr
            intro ι' hc
            exact isAuthorized_eq_of_add_forbid hq hfresh ((hall ι' hc).trans (hall ι₀ hc₀).symm)
              (hallow ι' hc)
          rw [hresp] at hsome
          cases hsome

/-- **Adding a `forbid` keeps a deny, over a trace**, under a total reading, whatever the ids. -/
theorem authorize_unchanged_deny_when_add_forbid_of_total (hι : ι.Total) {q : Policy}
    (hq : q.effect = .forbid) (h : (P.authorize ι ω σ n).decision? = some .deny) :
    (({ P with policies := q :: P.policies } : PolicySet).authorize ι ω σ n).decision? =
      some .deny :=
  authorize_unchanged_deny_when_add_forbid hq (.inl (authorize_ne_temporalError_of_total hι)) h

end Dogwood.Thm
