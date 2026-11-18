import Dogwood.Thm.Temporal
import Dogwood.Spec.Decision
import Dogwood.Thm.Leaves
import Dogwood.Thm.Readings

/-!
# Properties of decisions

Every decision is the skeleton `PolicySet.decideWith` with a response of its own. The lemmas
about the skeleton therefore hold of `authorize`, `authorizeWith`, `authorizeDeployed`, and the
evaluator's `Eval.authorize` alike.

* A history-only event decides nothing (`decideWith_history_only`).
* A decision event fails closed, with a reason of its own, when it has no principal or no
  resource, when its logged record does not conform, when its request context or its entity
  store does not conform, when a rule whose scope holds reads an attribute of a scope entity the
  event does not supply, when a provider fails, and when a provider's output does not conform
  (`decideWith_no_principal` … `decideWith_nonconformingProviderOutput`). A failed-closed
  decision denies (`decision?_failClosed`).
* When every check passes (`PolicySet.Admits`), the outcome is the response, or a temporal
  error when the response is `none` (`decideWith_of_admits`), and it depends on the response
  only at that event (`decideWith_congr`).
* **Readings.** Under a total reading, an admitted event is decided at the reading's leaf
  valuation (`authorize_decided`). Under any reading, the outcome fails closed for a temporal
  error or is the outcome under every completion of the reading (`authorize_dichotomy`); so the
  erroring reading allows only what every total admissible reading allows (`authorize_error`,
  `authorize_error_allow`). When every result is in range, every reading decides alike
  (`authorize_readings_agree`) and none fails closed for a temporal error
  (`authorize_ne_temporalError`).
* **Past-only decisions** (`authorize_append`): the outcome at a timepoint depends only on the
  history up to and including it. The same holds of `authorizeDeployed`
  (`authorizeDeployed_append`).
* Rules that all observe the trace from its first timepoint decide as `authorize` does
  (`authorize_eq_authorizeDeployed`).
-/

namespace Dogwood.Thm

open Dogwood.Spec Dogwood.Spec.Temporal
open Cedar.Spec (EntityUID Response)

variable {ι : ImplChoices} {P : PolicySet} {rules : Policies} {ω : Provider.Providers}
  {σ : Trace} {n : Nat} {p : TimePoint} {respond : Event → EntityUID → EntityUID → Option Response}

theorem mem_temporalLeaves {P : PolicySet} {p : Policy} {φ : Formula} (hp : p ∈ P.policies)
    (hl : Sum.inl φ ∈ p.toExpr.leaves) : φ ∈ P.temporalLeaves := by
  simp only [PolicySet.temporalLeaves, List.mem_flatMap, List.mem_filterMap]
  exact ⟨p, hp, .inl φ, hl, rfl⟩

/-! ## The skeleton -/

/-- Every check a decision makes passes at the event `p`: it is a decision event with the
principal `pr` and the resource `rs`, its logged record, request, and entity store conform, it
supplies the scope entities whose attributes the rules that apply to it read, and its providers
produce conforming values. -/
structure _root_.Dogwood.Spec.PolicySet.Admits (P : PolicySet) (rules : Policies) (ω : Provider.Providers)
    (p : TimePoint) (pr rs : EntityUID) : Prop where
  kind : P.schema.isDecisionKind p.event.kind = true
  principal : p.event.principal = some pr
  resource : p.event.resource = some rs
  event : p.event.Conforms P.actionSchema P.schema
  request : succeeds (Cedar.Validation.validateRequest P.actionSchema (p.event.request pr rs)) = true
  entities : succeeds (Cedar.Validation.validateEntities P.actionSchema (P.decisionEntities p.event)) =
    true
  scopes : P.scopeEntitiesSupplied rules p.event pr rs = true
  providers : rules.providersFail ω p.event = false
  outputs : P.providerOutputsConform rules ω p.event = true

theorem decideWith_history_only (hσ : σ[n]? = some p)
    (hk : P.schema.isDecisionKind p.event.kind = false) :
    P.decideWith rules ω σ n respond = .noDecision := by
  simp [PolicySet.decideWith, hσ, hk]

theorem decideWith_no_principal (hσ : σ[n]? = some p)
    (hk : P.schema.isDecisionKind p.event.kind = true) (hpr : p.event.principal = none) :
    P.decideWith rules ω σ n respond = .failClosed .noPrincipal := by
  simp [PolicySet.decideWith, hσ, hk, hpr]

theorem decideWith_no_resource (hσ : σ[n]? = some p)
    (hk : P.schema.isDecisionKind p.event.kind = true) {pr : EntityUID}
    (hpr : p.event.principal = some pr) (hrs : p.event.resource = none) :
    P.decideWith rules ω σ n respond = .failClosed .noResource := by
  simp [PolicySet.decideWith, hσ, hk, hpr, hrs]

/-- **A nonconforming decision event fails closed.** -/
theorem decideWith_nonconformingEvent (hσ : σ[n]? = some p)
    (hk : P.schema.isDecisionKind p.event.kind = true) {pr rs : EntityUID}
    (hpr : p.event.principal = some pr) (hrs : p.event.resource = some rs)
    (he : ¬ p.event.Conforms P.actionSchema P.schema) :
    P.decideWith rules ω σ n respond = .failClosed .nonconformingEvent := by
  simp [PolicySet.decideWith, hσ, hk, hpr, hrs, he]

/-- **A nonconforming request context fails closed.** -/
theorem decideWith_nonconformingContext (hσ : σ[n]? = some p)
    (hk : P.schema.isDecisionKind p.event.kind = true) {pr rs : EntityUID}
    (hpr : p.event.principal = some pr) (hrs : p.event.resource = some rs)
    (he : p.event.Conforms P.actionSchema P.schema)
    (hreq : succeeds (Cedar.Validation.validateRequest P.actionSchema (p.event.request pr rs)) =
      false) :
    P.decideWith rules ω σ n respond = .failClosed .nonconformingContext := by
  simp [PolicySet.decideWith, hσ, hk, hpr, hrs, he, hreq]

/-- **A nonconforming entity store fails closed.** -/
theorem decideWith_nonconformingEntities (hσ : σ[n]? = some p)
    (hk : P.schema.isDecisionKind p.event.kind = true) {pr rs : EntityUID}
    (hpr : p.event.principal = some pr) (hrs : p.event.resource = some rs)
    (he : p.event.Conforms P.actionSchema P.schema)
    (hreq : succeeds (Cedar.Validation.validateRequest P.actionSchema (p.event.request pr rs)) = true)
    (hes : succeeds (Cedar.Validation.validateEntities P.actionSchema (P.decisionEntities p.event)) =
      false) :
    P.decideWith rules ω σ n respond = .failClosed .nonconformingEntities := by
  simp [PolicySet.decideWith, hσ, hk, hpr, hrs, he, hreq, hes]

/-- **A rule that reads an absent scope entity fails the decision closed**, on conforming data:
some rule whose scope holds at the request has a temporal leaf that reads an attribute of a scope
entity the event does not supply. -/
theorem decideWith_missingScopeEntity (hσ : σ[n]? = some p)
    (hk : P.schema.isDecisionKind p.event.kind = true) {pr rs : EntityUID}
    (hpr : p.event.principal = some pr) (hrs : p.event.resource = some rs)
    (he : p.event.Conforms P.actionSchema P.schema)
    (hreq : succeeds (Cedar.Validation.validateRequest P.actionSchema (p.event.request pr rs)) = true)
    (hes : succeeds (Cedar.Validation.validateEntities P.actionSchema (P.decisionEntities p.event)) =
      true)
    (hsc : P.scopeEntitiesSupplied rules p.event pr rs = false) :
    P.decideWith rules ω σ n respond = .failClosed .missingScopeEntity := by
  simp [PolicySet.decideWith, hσ, hk, hpr, hrs, he, hreq, hes, hsc]

/-- **A failing provider fails the decision closed**, on conforming data. -/
theorem decideWith_providerError (hσ : σ[n]? = some p)
    (hk : P.schema.isDecisionKind p.event.kind = true) {pr rs : EntityUID}
    (hpr : p.event.principal = some pr) (hrs : p.event.resource = some rs)
    (he : p.event.Conforms P.actionSchema P.schema)
    (hreq : succeeds (Cedar.Validation.validateRequest P.actionSchema (p.event.request pr rs)) = true)
    (hes : succeeds (Cedar.Validation.validateEntities P.actionSchema (P.decisionEntities p.event)) =
      true)
    (hsc : P.scopeEntitiesSupplied rules p.event pr rs = true)
    (hω : rules.providersFail ω p.event = true) :
    P.decideWith rules ω σ n respond = .failClosed .providerError := by
  simp [PolicySet.decideWith, hσ, hk, hpr, hrs, he, hreq, hes, hsc, hω]

/-- **A nonconforming provider output fails the decision closed.** -/
theorem decideWith_nonconformingProviderOutput (hσ : σ[n]? = some p)
    (hk : P.schema.isDecisionKind p.event.kind = true) {pr rs : EntityUID}
    (hpr : p.event.principal = some pr) (hrs : p.event.resource = some rs)
    (he : p.event.Conforms P.actionSchema P.schema)
    (hreq : succeeds (Cedar.Validation.validateRequest P.actionSchema (p.event.request pr rs)) = true)
    (hes : succeeds (Cedar.Validation.validateEntities P.actionSchema (P.decisionEntities p.event)) =
      true)
    (hsc : P.scopeEntitiesSupplied rules p.event pr rs = true)
    (hω : rules.providersFail ω p.event = false)
    (ho : P.providerOutputsConform rules ω p.event = false) :
    P.decideWith rules ω σ n respond = .failClosed .nonconformingProviderOutput := by
  simp [PolicySet.decideWith, hσ, hk, hpr, hrs, he, hreq, hes, hsc, hω, ho]

/-- When every check passes, the outcome is the response, or a temporal error. -/
theorem decideWith_of_admits (hσ : σ[n]? = some p) {pr rs : EntityUID}
    (h : P.Admits rules ω p pr rs) :
    P.decideWith rules ω σ n respond =
      match respond p.event pr rs with
      | some r => .decided r
      | none => .failClosed .temporalError := by
  unfold PolicySet.decideWith
  simp only [hσ, h.kind, h.principal, h.resource, h.event, h.request, h.entities, h.scopes,
    h.providers, h.outputs, decide_true, Bool.not_true, Bool.false_eq_true, if_false]
  cases respond p.event pr rs <;> rfl

/-- **A decided outcome passed every check.** An outcome the response decides was decided at a
decision event every check of which passes, by the response there. -/
theorem decideWith_eq_decided {r : Response} (h : P.decideWith rules ω σ n respond = .decided r) :
    ∃ p pr rs, σ[n]? = some p ∧ P.Admits rules ω p pr rs ∧ respond p.event pr rs = some r := by
  unfold PolicySet.decideWith at h
  split at h
  · cases h
  rename_i p hσ
  simp only at h
  split at h
  · cases h
  rename_i hk
  simp only [Bool.not_eq_true', Bool.not_eq_false] at hk
  split at h
  · cases h
  · cases h
  rename_i pr rs hpr hrs
  split at h
  · cases h
  rename_i he
  split at h
  · cases h
  rename_i hreq
  split at h
  · cases h
  rename_i hes
  split at h
  · cases h
  rename_i hsc
  split at h
  · cases h
  rename_i hω
  split at h
  · cases h
  rename_i ho
  split at h
  · rename_i r' hr
    cases h
    refine ⟨p, pr, rs, hσ, ⟨hk, hpr, hrs, ?_, ?_, ?_, ?_, ?_, ?_⟩, hr⟩
    · simpa using he
    · simpa using hreq
    · simpa using hes
    · simpa using hsc
    · simpa using hω
    · simpa using ho
  · cases h

/-- A decision fails closed for a temporal error only at a decision event every check of which
passes, where the response is `none`. -/
theorem decideWith_eq_temporalError
    (h : P.decideWith rules ω σ n respond = .failClosed .temporalError) :
    ∃ p pr rs, σ[n]? = some p ∧ P.Admits rules ω p pr rs ∧ respond p.event pr rs = none := by
  unfold PolicySet.decideWith at h
  split at h
  · cases h
  rename_i p hσ
  simp only at h
  split at h
  · cases h
  rename_i hk
  simp only [Bool.not_eq_true', Bool.not_eq_false] at hk
  split at h
  · cases h
  · cases h
  rename_i pr rs hpr hrs
  split at h
  · cases h
  rename_i he
  split at h
  · cases h
  rename_i hreq
  split at h
  · cases h
  rename_i hes
  split at h
  · cases h
  rename_i hsc
  split at h
  · cases h
  rename_i hω
  split at h
  · cases h
  rename_i ho
  split at h
  · cases h
  · rename_i hr
    refine ⟨p, pr, rs, hσ, ⟨hk, hpr, hrs, ?_, ?_, ?_, ?_, ?_, ?_⟩, hr⟩
    · simpa using he
    · simpa using hreq
    · simpa using hes
    · simpa using hsc
    · simpa using hω
    · simpa using ho

/-- **An allow passed every check.** An allowed outcome was decided by the response, as an
allow, at a decision event every check of which passes. -/
theorem decideWith_decision?_allow (h : (P.decideWith rules ω σ n respond).decision? = some .allow) :
    ∃ p pr rs r, σ[n]? = some p ∧ P.Admits rules ω p pr rs ∧ respond p.event pr rs = some r ∧
      r.decision = .allow := by
  cases hd : P.decideWith rules ω σ n respond with
  | noDecision => simp [hd, Outcome.decision?] at h
  | failClosed _ => simp [hd, Outcome.decision?] at h
  | decided r =>
    obtain ⟨p, pr, rs, hσ, ha, hr⟩ := decideWith_eq_decided hd
    rw [hd] at h
    exact ⟨p, pr, rs, r, hσ, ha, hr, by simpa [Outcome.decision?] using h⟩

/-- A decision event decides: its outcome is an allow or a deny. -/
theorem decideWith_decision?_isSome (hσ : σ[n]? = some p)
    (hk : P.schema.isDecisionKind p.event.kind = true) :
    (P.decideWith rules ω σ n respond).decision?.isSome = true := by
  unfold PolicySet.decideWith
  simp only [hσ, hk, Bool.not_true, Bool.false_eq_true, if_false]
  split
  · rfl
  · rfl
  · split
    · rfl
    · split
      · rfl
      · split
        · rfl
        · split
          · rfl
          · split
            · rfl
            · split
              · rfl
              · split <;> rfl

/-- **The outcome depends on the response only at an admitted event.** -/
theorem decideWith_congr {σ₁ σ₂ : Trace} {n₁ n₂ : Nat} {respond₁ respond₂ : Event → EntityUID →
      EntityUID → Option Response} (hn : σ₁[n₁]? = σ₂[n₂]?)
    (h : ∀ p pr rs, σ₁[n₁]? = some p → P.Admits rules ω p pr rs →
      respond₁ p.event pr rs = respond₂ p.event pr rs) :
    P.decideWith rules ω σ₁ n₁ respond₁ = P.decideWith rules ω σ₂ n₂ respond₂ := by
  unfold PolicySet.decideWith
  rw [← hn]
  cases hσ : σ₁[n₁]? with
  | none => rfl
  | some p =>
    simp only
    by_cases hk : P.schema.isDecisionKind p.event.kind = true
    · simp only [hk, Bool.not_true, Bool.false_eq_true, if_false]
      cases hpr : p.event.principal with
      | none => rfl
      | some pr =>
        cases hrs : p.event.resource with
        | none => rfl
        | some rs =>
          simp only
          by_cases he : p.event.Conforms P.actionSchema P.schema
          · by_cases hreq : succeeds (Cedar.Validation.validateRequest P.actionSchema
                (p.event.request pr rs)) = true
            · by_cases hes : succeeds (Cedar.Validation.validateEntities P.actionSchema
                  (P.decisionEntities p.event)) = true
              · cases hsc : P.scopeEntitiesSupplied rules p.event pr rs
                · simp [he, hreq, hes]
                · cases hω : rules.providersFail ω p.event
                  · cases ho : P.providerOutputsConform rules ω p.event
                    · simp [he, hreq, hes]
                    · simp only [he, decide_true, Bool.not_true, Bool.false_eq_true, if_false, hreq,
                        hes]
                      rw [h p pr rs hσ ⟨hk, hpr, hrs, he, hreq, hes, hsc, hω, ho⟩]
                  · simp [he, hreq, hes]
              · simp only [Bool.not_eq_true] at hes
                simp [he, hreq, hes]
            · simp only [Bool.not_eq_true] at hreq
              simp [he, hreq]
          · simp [he]
    · simp only [Bool.not_eq_true] at hk
      simp [hk]

/-! ## `authorize` -/

theorem authorize_history_only (hσ : σ[n]? = some p)
    (hk : P.schema.isDecisionKind p.event.kind = false) :
    P.authorize ι ω σ n = .noDecision :=
  decideWith_history_only hσ hk

theorem authorize_no_principal (hσ : σ[n]? = some p)
    (hk : P.schema.isDecisionKind p.event.kind = true) (hpr : p.event.principal = none) :
    P.authorize ι ω σ n = .failClosed .noPrincipal :=
  decideWith_no_principal hσ hk hpr

theorem authorize_no_resource (hσ : σ[n]? = some p)
    (hk : P.schema.isDecisionKind p.event.kind = true) {pr : EntityUID}
    (hpr : p.event.principal = some pr) (hrs : p.event.resource = none) :
    P.authorize ι ω σ n = .failClosed .noResource :=
  decideWith_no_resource hσ hk hpr hrs

/-- A decision event at which a provider invocation of the policy set fails fails closed, when
its data conform. -/
theorem authorize_providerError (hσ : σ[n]? = some p)
    (hk : P.schema.isDecisionKind p.event.kind = true) {pr rs : EntityUID}
    (hpr : p.event.principal = some pr) (hrs : p.event.resource = some rs)
    (he : p.event.Conforms P.actionSchema P.schema)
    (hreq : succeeds (Cedar.Validation.validateRequest P.actionSchema (p.event.request pr rs)) = true)
    (hes : succeeds (Cedar.Validation.validateEntities P.actionSchema (P.decisionEntities p.event)) =
      true)
    (hsc : P.scopeEntitiesSupplied P.policies p.event pr rs = true)
    (hω : P.policies.providersFail ω p.event = true) :
    P.authorize ι ω σ n = .failClosed .providerError :=
  decideWith_providerError hσ hk hpr hrs he hreq hes hsc hω

/-- **A nonconforming decision event fails `authorize` closed.** -/
theorem authorize_nonconformingEvent (hσ : σ[n]? = some p)
    (hk : P.schema.isDecisionKind p.event.kind = true) {pr rs : EntityUID}
    (hpr : p.event.principal = some pr) (hrs : p.event.resource = some rs)
    (he : ¬ p.event.Conforms P.actionSchema P.schema) :
    P.authorize ι ω σ n = .failClosed .nonconformingEvent :=
  decideWith_nonconformingEvent hσ hk hpr hrs he

/-- **A nonconforming request context fails `authorize` closed.** -/
theorem authorize_nonconformingContext (hσ : σ[n]? = some p)
    (hk : P.schema.isDecisionKind p.event.kind = true) {pr rs : EntityUID}
    (hpr : p.event.principal = some pr) (hrs : p.event.resource = some rs)
    (he : p.event.Conforms P.actionSchema P.schema)
    (hreq : succeeds (Cedar.Validation.validateRequest P.actionSchema (p.event.request pr rs)) =
      false) :
    P.authorize ι ω σ n = .failClosed .nonconformingContext :=
  decideWith_nonconformingContext hσ hk hpr hrs he hreq

/-- **A nonconforming entity store fails `authorize` closed.** -/
theorem authorize_nonconformingEntities (hσ : σ[n]? = some p)
    (hk : P.schema.isDecisionKind p.event.kind = true) {pr rs : EntityUID}
    (hpr : p.event.principal = some pr) (hrs : p.event.resource = some rs)
    (he : p.event.Conforms P.actionSchema P.schema)
    (hreq : succeeds (Cedar.Validation.validateRequest P.actionSchema (p.event.request pr rs)) = true)
    (hes : succeeds (Cedar.Validation.validateEntities P.actionSchema (P.decisionEntities p.event)) =
      false) :
    P.authorize ι ω σ n = .failClosed .nonconformingEntities :=
  decideWith_nonconformingEntities hσ hk hpr hrs he hreq hes

/-- **A rule that reads an absent scope entity fails `authorize` closed.** -/
theorem authorize_missingScopeEntity (hσ : σ[n]? = some p)
    (hk : P.schema.isDecisionKind p.event.kind = true) {pr rs : EntityUID}
    (hpr : p.event.principal = some pr) (hrs : p.event.resource = some rs)
    (he : p.event.Conforms P.actionSchema P.schema)
    (hreq : succeeds (Cedar.Validation.validateRequest P.actionSchema (p.event.request pr rs)) = true)
    (hes : succeeds (Cedar.Validation.validateEntities P.actionSchema (P.decisionEntities p.event)) =
      true)
    (hsc : P.scopeEntitiesSupplied P.policies p.event pr rs = false) :
    P.authorize ι ω σ n = .failClosed .missingScopeEntity :=
  decideWith_missingScopeEntity hσ hk hpr hrs he hreq hes hsc

/-- **A nonconforming provider output fails `authorize` closed.** -/
theorem authorize_nonconformingProviderOutput (hσ : σ[n]? = some p)
    (hk : P.schema.isDecisionKind p.event.kind = true) {pr rs : EntityUID}
    (hpr : p.event.principal = some pr) (hrs : p.event.resource = some rs)
    (he : p.event.Conforms P.actionSchema P.schema)
    (hreq : succeeds (Cedar.Validation.validateRequest P.actionSchema (p.event.request pr rs)) = true)
    (hes : succeeds (Cedar.Validation.validateEntities P.actionSchema (P.decisionEntities p.event)) =
      true)
    (hsc : P.scopeEntitiesSupplied P.policies p.event pr rs = true)
    (hω : P.policies.providersFail ω p.event = false)
    (ho : P.providerOutputsConform P.policies ω p.event = false) :
    P.authorize ι ω σ n = .failClosed .nonconformingProviderOutput :=
  decideWith_nonconformingProviderOutput hσ hk hpr hrs he hreq hes hsc hω ho

/-- Under a total reading, the response is the per-request authorizer's at the reading's own
leaf valuation. -/
theorem respond_total (hι : ι.Total) (e : Event) (pr rs : EntityUID) :
    P.respond ι ω σ n e pr rs = some (isAuthorized (P.leaves ι ω σ n e) (e.request pr rs)
      (P.decisionEntities e) P.policies) :=
  supervaluate_total hι

/-- An admitted decision event is decided by the response, or fails closed for a temporal
error. -/
theorem authorize_of_admits (hσ : σ[n]? = some p) {pr rs : EntityUID}
    (h : P.Admits P.policies ω p pr rs) :
    P.authorize ι ω σ n = match P.respond ι ω σ n p.event pr rs with
      | some r => .decided r
      | none => .failClosed .temporalError :=
  decideWith_of_admits hσ h

/-- **Under a total reading, an admitted decision event is decided** by the per-request
authorizer at the reading's leaf valuation. -/
theorem authorize_decided (hι : ι.Total) (hσ : σ[n]? = some p) {pr rs : EntityUID}
    (h : P.Admits P.policies ω p pr rs) :
    P.authorize ι ω σ n = .decided (isAuthorized (P.leaves ι ω σ n p.event)
      (p.event.request pr rs) (P.decisionEntities p.event) P.policies) := by
  rw [authorize_of_admits hσ h, respond_total hι]

/-- **A decided outcome is the response of every completion of the reading.** -/
theorem authorize_eq_decided {r : Response} (h : P.authorize ι ω σ n = .decided r) :
    ∃ p pr rs, σ[n]? = some p ∧ P.Admits P.policies ω p pr rs ∧
      ∀ ι', ι'.Completes ι → isAuthorized (P.leaves ι' ω σ n p.event) (p.event.request pr rs)
        (P.decisionEntities p.event) P.policies = r := by
  obtain ⟨p, pr, rs, hσ, ha, hr⟩ := decideWith_eq_decided h
  exact ⟨p, pr, rs, hσ, ha, supervaluate_eq_some_iff.mp hr⟩

/-- **An erroring reading fails closed, or decides as every completion does.** At every
timepoint, the outcome under the reading `ι` fails closed for a temporal error, or it is the
outcome under every completion of `ι`. -/
theorem authorize_dichotomy :
    P.authorize ι ω σ n = .failClosed .temporalError ∨
      ∀ ι', ι'.Completes ι → P.authorize ι ω σ n = P.authorize ι' ω σ n := by
  by_cases hfail : P.authorize ι ω σ n = .failClosed .temporalError
  · exact .inl hfail
  · refine .inr fun ι' hc => ?_
    have hι' : ι'.Total := hc.total
    have hrespond : ∀ p pr rs, σ[n]? = some p → P.Admits P.policies ω p pr rs →
        P.respond ι ω σ n p.event pr rs = P.respond ι' ω σ n p.event pr rs := by
      intro p pr rs hσ ha
      rw [respond_total hι']
      cases hr : P.respond ι ω σ n p.event pr rs with
      | some r => rw [supervaluate_eq_some_iff.mp hr ι' hc]
      | none =>
        exfalso
        apply hfail
        rw [authorize_of_admits hσ ha, hr]
    unfold PolicySet.authorize
    exact decideWith_congr rfl hrespond

/-- **The erroring reading fails closed, or decides as every total admissible reading does.** -/
theorem authorize_error :
    P.authorize .error ω σ n = .failClosed .temporalError ∨
      ∀ ι', ι'.Total → ι'.Admissible → P.authorize .error ω σ n = P.authorize ι' ω σ n := by
  rcases authorize_dichotomy (P := P) (ι := .error) (ω := ω) (σ := σ) (n := n) with h | h
  · exact .inl h
  · exact .inr fun ι' ht ha => h ι' (completes_error_iff.mpr ⟨ht, ha⟩)

/-- **The erroring reading allows only what every admissible reading allows.** An allow under
the erroring reading is an allow under every total admissible reading: no out-of-range result
that the erroring reading reports an error for causes an allow. -/
theorem authorize_error_allow (h : (P.authorize .error ω σ n).decision? = some .allow)
    {ι' : ImplChoices} (ht : ι'.Total) (ha : ι'.Admissible) :
    (P.authorize ι' ω σ n).decision? = some .allow := by
  rcases authorize_error (P := P) (ω := ω) (σ := σ) (n := n) with hf | hall
  · rw [hf] at h; cases h
  · rw [← hall ι' ht ha]; exact h

/-- In range, a leaf holds alike under every reading. -/
theorem leafHolds_readings_agree (h : P.InRange ι σ n) {φ : Formula} (hφ : φ ∈ P.temporalLeaves)
    (ι' : ImplChoices) : P.LeafHolds ι' σ n φ ↔ P.LeafHolds ι σ n φ := by
  unfold PolicySet.LeafHolds
  refine exists_congr fun p => ⟨fun ⟨hp, hs⟩ => ⟨hp, ?_⟩, fun ⟨hp, hs⟩ => ⟨hp, ?_⟩⟩
  · exact (sat_readings_agree ι ι' _ _ _ (h p hp φ hφ)).mp hs
  · exact (sat_readings_agree ι ι' _ _ _ (h p hp φ hφ)).mpr hs

/-- In range, every reading responds as `ι` does. -/
theorem respond_readings_agree (h : P.InRange ι σ n) (ι₁ : ImplChoices) (p : TimePoint)
    (pr rs : EntityUID) :
    P.respond ι₁ ω σ n p.event pr rs = some (isAuthorized (P.leaves ι ω σ n p.event)
      (p.event.request pr rs) (P.decisionEntities p.event) P.policies) := by
  unfold PolicySet.respond
  rw [supervaluate_congr (g := fun _ => isAuthorized (P.leaves ι ω σ n p.event)
    (p.event.request pr rs) (P.decisionEntities p.event) P.policies) fun ι' _ => ?_]
  · exact supervaluate_const _
  apply isAuthorized_congr
  intro q hq l hl
  cases l with
  | inl φ =>
    show @decide _ (Classical.propDecidable _) = @decide _ (Classical.propDecidable _)
    exact decide_eq_decide.mpr (leafHolds_readings_agree h (mem_temporalLeaves hq hl) ι')
  | inr c => rfl

/-- **In range, the readings agree.** When every result the policy set's temporal leaves compute
at a decision is in range, every reading, erroring or not, decides alike there. -/
theorem authorize_readings_agree (h : P.InRange ι σ n) (ι₁ ι₂ : ImplChoices) :
    P.authorize ι₁ ω σ n = P.authorize ι₂ ω σ n := by
  unfold PolicySet.authorize
  refine decideWith_congr rfl fun p pr rs _ _ => ?_
  rw [respond_readings_agree h ι₁ p, respond_readings_agree h ι₂ p]

/-- In range, no decision fails closed for a temporal error. -/
theorem authorize_ne_temporalError (h : P.InRange ι σ n) (ι₁ : ImplChoices) :
    P.authorize ι₁ ω σ n ≠ .failClosed .temporalError := by
  intro hf
  obtain ⟨p, pr, rs, _, _, hr⟩ := decideWith_eq_temporalError hf
  rw [respond_readings_agree h ι₁ p] at hr
  cases hr

/-! ## Information providers -/

/-- Providers that never fail make no decision fail closed. -/
theorem providersFail_total (ps : Policies) (f : Provider.ResolvedCall → Cedar.Spec.Value)
    (e : Event) : ps.providersFail (Provider.total f) e = false := by
  simp [Policies.providersFail, Provider.total, Provider.Output.isError]

/-- Rules without provider invocations make no decision fail closed, whatever the providers. -/
theorem providersFail_of_providerCalls_nil {ps : Policies} (h : ps.providerCalls = [])
    (ω : Provider.Providers) (e : Event) : ps.providersFail ω e = false := by
  simp [Policies.providersFail, h]

/-- Rules without provider invocations have conforming provider outputs, whatever the
providers. -/
theorem providerOutputsConform_of_providerCalls_nil {ps : Policies} (h : ps.providerCalls = [])
    (P : PolicySet) (ω : Provider.Providers) (e : Event) : P.providerOutputsConform ps ω e = true := by
  simp [PolicySet.providerOutputsConform, h]

theorem providersFail_iff {ps : Policies} {ω : Provider.Providers} {e : Event} :
    ps.providersFail ω e = true ↔ ∃ c ∈ ps.providerCalls, ω (c.resolve e) = .error := by
  simp only [Policies.providersFail, List.any_eq_true]
  refine exists_congr fun c => and_congr_right fun _ => ?_
  cases ω (c.resolve e) <;> simp [Provider.Output.isError]

/-! ## Scope entities -/

/-- Rules whose temporal leaves read no attribute of a scope entity pass the check of the scope
entities, whatever the event supplies. -/
theorem scopeEntitiesSupplied_of_scopeReads_nil
    (h : ∀ q ∈ rules, ∀ φ, Sum.inl φ ∈ q.toExpr.leaves → (φ.injectPins P.schema).scopeReads = [])
    (e : Event) (pr rs : EntityUID) : P.scopeEntitiesSupplied rules e pr rs = true := by
  unfold PolicySet.scopeEntitiesSupplied
  refine List.all_eq_true.mpr fun q hq => ?_
  rw [Bool.or_eq_true]
  refine .inr (List.all_eq_true.mpr fun l hl => ?_)
  cases l with
  | inl φ =>
    show (φ.injectPins P.schema).scopeReads.all e.supplies = true
    rw [h q hq φ hl]
    rfl
  | inr _ => rfl

/-- Rules without temporal leaves pass the check of the scope entities. -/
theorem scopeEntitiesSupplied_of_temporal_nil
    (h : ∀ q ∈ rules, ∀ φ, Sum.inl φ ∉ q.toExpr.leaves) (e : Event) (pr rs : EntityUID) :
    P.scopeEntitiesSupplied rules e pr rs = true :=
  scopeEntitiesSupplied_of_scopeReads_nil (fun q hq φ hφ => absurd hφ (h q hq φ)) e pr rs

theorem decision?_failClosed (r : FailClosed) : (Outcome.failClosed r).decision? = some .deny :=
  rfl

/-! ## Past-only decisions -/

theorem leafHolds_append (τ : Trace) (φ : Formula) (hn : n < σ.length) :
    P.LeafHolds ι (σ ++ τ) n φ ↔ P.LeafHolds ι σ n φ := by
  have hget : ∀ k ≤ n, (σ ++ τ)[k]? = σ[k]? :=
    fun k hk => List.getElem?_append_left (Nat.lt_of_le_of_lt hk hn)
  simp only [PolicySet.LeafHolds, hget n (Nat.le_refl n)]
  refine exists_congr fun p => and_congr_right fun _ => ?_
  apply sat_congr
  intro k hk
  refine ⟨hget k hk, ?_⟩
  simp only [EventSchema.Visible, hget k hk]

/-- **Past-only decisions.** -/
theorem authorize_append (τ : Trace) (hn : n < σ.length) :
    P.authorize ι ω (σ ++ τ) n = P.authorize ι ω σ n := by
  have hget : (σ ++ τ)[n]? = σ[n]? := List.getElem?_append_left hn
  have hleaves : ∀ ι' e, P.leaves ι' ω (σ ++ τ) n e = P.leaves ι' ω σ n e := by
    intro ι' e
    simp only [PolicySet.leaves, Leaves.mk.injEq, and_true]
    funext φ
    exact decide_eq_decide.mpr (leafHolds_append τ φ hn)
  unfold PolicySet.authorize
  exact decideWith_congr hget fun _ _ _ _ _ => by simp only [PolicySet.respond, hleaves]

/-! ## Rules that observe the trace from a timepoint of their own -/

/-- Observing the trace from its first timepoint is observing all of it. -/
theorem leafHoldsFrom_zero (φ : Formula) :
    P.LeafHoldsFrom ι σ 0 n φ ↔ P.LeafHolds ι σ n φ := by
  unfold PolicySet.LeafHoldsFrom PolicySet.LeafHolds
  refine exists_congr fun p => and_congr_right fun _ => ?_
  exact sat_congr _ _ n fun k _ => ⟨rfl, ⟨fun h => h.2, fun h => ⟨Nat.zero_le k, h⟩⟩⟩

theorem leavesFrom_zero (e : Event) : P.leavesFrom ι ω σ 0 n e = P.leaves ι ω σ n e := by
  simp only [PolicySet.leavesFrom, PolicySet.leaves, Leaves.mk.injEq, and_true]
  funext φ
  exact decide_eq_decide.mpr (leafHoldsFrom_zero φ)

/-- `authorize` is `authorizeDeployed` with the policy set's rules, each observing the trace from
its first timepoint. -/
theorem authorize_eq_authorizeDeployed :
    P.authorize ι ω σ n = P.authorizeDeployed ι ω σ n (P.policies.map fun q => (q, 0)) := by
  have hmap : (P.policies.map fun q => (q, 0)).map (·.1) = P.policies := by
    simp [List.map_map, Function.comp_def]
  unfold PolicySet.authorize PolicySet.authorizeDeployed
  rw [hmap]
  refine decideWith_congr rfl fun p pr rs _ _ => ?_
  simp only [PolicySet.respond]
  refine supervaluate_congr fun ι' _ => ?_
  simp only [List.map_map, Function.comp_def, leavesFrom_zero]
  exact (isAuthorizedEach_const _ _ _ _).symm

theorem leafHoldsFrom_append (τ : Trace) (start : Nat) (φ : Formula) (hn : n < σ.length) :
    P.LeafHoldsFrom ι (σ ++ τ) start n φ ↔ P.LeafHoldsFrom ι σ start n φ := by
  have hget : ∀ k ≤ n, (σ ++ τ)[k]? = σ[k]? :=
    fun k hk => List.getElem?_append_left (Nat.lt_of_le_of_lt hk hn)
  simp only [PolicySet.LeafHoldsFrom, hget n (Nat.le_refl n)]
  refine exists_congr fun p => and_congr_right fun _ => ?_
  apply sat_congr
  intro k hk
  refine ⟨hget k hk, ?_⟩
  simp only [EventSchema.Visible, hget k hk]

/-- **Past-only decisions, for rules with starts of their own.** -/
theorem authorizeDeployed_append (τ : Trace) (rules : List (Policy × Nat)) (hn : n < σ.length) :
    P.authorizeDeployed ι ω (σ ++ τ) n rules = P.authorizeDeployed ι ω σ n rules := by
  have hget : (σ ++ τ)[n]? = σ[n]? := List.getElem?_append_left hn
  have hleaves : ∀ ι' start e,
      P.leavesFrom ι' ω (σ ++ τ) start n e = P.leavesFrom ι' ω σ start n e := by
    intro ι' start e
    simp only [PolicySet.leavesFrom, Leaves.mk.injEq, and_true]
    funext φ
    exact decide_eq_decide.mpr (leafHoldsFrom_append τ start φ hn)
  unfold PolicySet.authorizeDeployed
  exact decideWith_congr hget fun _ _ _ _ _ => by simp only [hleaves]

end Dogwood.Thm
