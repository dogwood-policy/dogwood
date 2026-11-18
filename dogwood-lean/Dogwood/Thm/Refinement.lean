import Dogwood.Thm.Authorization
import Dogwood.Thm.Conservative
import Dogwood.Thm.DecisionSoundness
import Dogwood.Thm.Log
import Dogwood.Thm.TemporalLaws

/-!
# Refinement: making the rules stricter makes the decisions stricter

* **The general form** (`authorize_allow_of_refines`): replace a policy set's rules by rules
  whose checks pass only where the old rules' do, and that, at the leaf valuations of the
  decision, allow only requests the old rules allow. Then an event the new rules allow, the old
  rules allow, unless the old decision fails closed for a temporal error. The exception is of the
  same kind as `authorize_unchanged_deny_when_add_forbid`'s, but arises with distinct policy ids:
  under a reading that reports errors the response is supervaluated, and completions that differ
  in which policies determine it fail it closed. Under a total reading there is no exception
  (`authorize_allow_of_refines_of_total`). `authorize_allow_of_refines_of_forall` asks the
  refinement at every leaf valuation instead.
* **Strengthening a `permit`** (`authorize_allow_of_replace_permit`): replacing a `permit` by one
  satisfied only where it is never creates an allow, when the old `permit` passes its own checks
  wherever the new one does, as it does when its checks are among the new one's
  (`PolicySet.ChecksWithin`, `authorize_allow_of_replace_permit_of_checksWithin`). Instances:
  adding a condition (`authorize_allow_of_strengthen_permit`), tightening the windows of a
  temporal condition anywhere among the conditions (`Condition.Tightens`,
  `authorize_allow_of_tighten_permit_window`), and narrowing the scope of a `permit` whose
  temporal leaves read no scope entity (`authorize_allow_of_narrow_permit_scope`).
* **Weakening a `forbid`** (`authorize_allow_of_replace_forbid`): replacing a `forbid` by one
  satisfied wherever it is never creates an allow, when the old `forbid` passes its own checks
  wherever the new one does, as it does when its checks are among the new one's
  (`authorize_allow_of_replace_forbid_of_checksWithin`). Instances: removing a condition
  (`authorize_allow_of_weaken_forbid`, `authorize_allow_of_weaken_forbid_of_leaves`), loosening
  the windows of a temporal condition (`authorize_allow_of_loosen_forbid_window`), and widening
  the scope (`authorize_allow_of_widen_forbid_scope`).
* **Removing a `permit`** (`authorize_allow_of_remove_permit`): never creates an allow, when the
  `permit` passes its own checks at the event, as one without leaves always does
  (`authorize_allow_of_remove_permit_of_leaves_nil`). **Removing a `forbid`**
  (`authorize_unchanged_allow_when_remove_forbid`) keeps an allow, unless the decision without it
  fails closed for a temporal error.

The side conditions on the checks are needed. The decision fails closed when a provider of any
rule fails (check 7), or a temporal leaf of a rule whose scope holds reads a scope entity the event
does not supply (check 6). So removing a rule, or a condition, whose provider fails turns a
failed-closed deny into a decision, which can be an allow: removing a broken part removes its
failure. For the same reason narrowing the scope of a `permit` whose temporal leaves read scope
entities can create an allow: where the old scope holds and the new one does not, the old rule's
temporal leaves were checked and the new rule's are not. The general form states what is needed in
each case.

* **Adding a `permit`** (`rulePasses_of_authorize_add_permit`,
  `authorize_unchanged_allow_when_add_permit`, and under a total reading
  `authorize_unchanged_allow_when_add_permit_iff`): an allow stays an allow exactly when the added
  rule passes the checks (`PolicySet.RulePasses`): its providers do not fail and produce
  conforming outputs, and its temporal leaves, if its scope holds, read only supplied scope
  entities. This holds under every reading unless the new decision fails closed for a temporal
  error. Unlike Cedar's `unchanged_allow_when_add_permit`, adding a `permit` can turn an allow
  into a deny, and this says exactly when.
* **Deployments** (`authorizeDeployed_allow_of_replace_permit`,
  `authorizeDeployed_allow_of_strengthen_permit`): of two deployments that differ in a `permit`
  whose monitor starts at the same timepoint, the one with the stricter `permit` allows only what
  the other allows. Under the retrospective reading every rule observes the whole trace, so
  refinement carries over to two logs with the same trace that decide the same event
  (`decide_retrospective_allow_of_refines`, `decide_retrospective_allow_of_strengthen_permit`).
  Under the prospective reading it does not apply to deploying a strengthened rule: a rule whose
  content changes is a new rule, and gets a new monitor instance
  (`Dogwood.Spec.Log.InstancesStable`), which observes the trace only from the deployment on.
  Adding `when { count … < 3 }` to a `permit … when { count … < 5 }` that had seen seven events,
  and so denied, restarts the count at zero, and the stricter rule allows.
-/

/-! ## Window widening commutes with the leaf passes -/

namespace Dogwood.Spec.Temporal

/-- Pin injection keeps a widening a widening: it changes no window. -/
theorem Formula.Widens.injectPins {rate : TickRate} {S : EventSchema} {φ φ' : Formula}
    (h : Formula.Widens rate φ φ') :
    Formula.Widens rate (φ.injectPins S) (φ'.injectPins S) := by
  induction h with
  | refl => exact .refl _
  | and _ _ ih₁ ih₂ => exact .and ih₁ ih₂
  | exist x _ ih => exact .exist x ih
  | formerly hw _ ih => exact .formerly hw ih
  | previous hw _ ih => exact .previous hw ih
  | since hw _ _ ih₁ ih₂ => exact .since hw ih₁ ih₂

/-- A widening reads the same scope entities: windows are not read. -/
theorem Formula.Widens.scopeReads_eq {rate : TickRate} {φ φ' : Formula}
    (h : Formula.Widens rate φ φ') : φ.scopeReads = φ'.scopeReads := by
  induction h with
  | refl => rfl
  | and _ _ ih₁ ih₂ => simp only [Formula.scopeReads, ih₁, ih₂]
  | exist x _ ih => simp only [Formula.scopeReads, ih]
  | formerly _ _ ih => simp only [Formula.scopeReads, ih]
  | previous _ _ ih => simp only [Formula.scopeReads, ih]
  | since _ _ _ ih₁ ih₂ => simp only [Formula.scopeReads, ih₁, ih₂]

end Dogwood.Spec.Temporal

namespace Dogwood.Thm

open Dogwood.Spec Dogwood.Spec.Temporal
open Cedar.Spec (Request Entities EntityUID Effect Decision Response)

/-! ## Conditions -/

/-- A rule with one more condition, checked after the others. -/
def _root_.Dogwood.Spec.Policy.addCondition (q : Policy) (c : Condition) : Policy :=
  { q with condition := q.condition ++ [c] }

/-- A rule with the condition between `pre` and `post` replaced by `c`. -/
def _root_.Dogwood.Spec.Policy.withCondition (q : Policy) (pre : Conditions) (c : Condition)
    (post : Conditions) : Policy :=
  { q with condition := pre ++ c :: post }

theorem evaluate_and_true_iff {θ : Leaves} {req : Request} {es : Entities} {a b : Expr} :
    evaluate θ (.and a b) req es = .ok (.prim (.bool true)) ↔
      evaluate θ a req es = .ok (.prim (.bool true)) ∧
        evaluate θ b req es = .ok (.prim (.bool true)) := by
  constructor
  · intro h
    simp only [evaluate] at h
    cases ha : (evaluate θ a req es).as Bool with
    | error e => rw [ha] at h; cases h
    | ok b₁ =>
      rw [ha] at h
      cases b₁ with
      | false => simp at h
      | true =>
        simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, Except.bind_ok] at h
        cases hb : (evaluate θ b req es).as Bool with
        | error e => rw [hb] at h; cases h
        | ok b₂ =>
          rw [hb] at h
          have hb₂ : b₂ = true := by simpa [pure, Except.pure] using h
          subst hb₂
          exact ⟨as_bool_true ha, as_bool_true hb⟩
  · rintro ⟨ha, hb⟩
    simp [evaluate, ha, hb, Cedar.Spec.Result.as, Coe.coe, Cedar.Spec.Value.asBool]

private theorem foldl_true_iff {θ : Leaves} {req : Request} {es : Entities} :
    (xs : List Condition) → (acc : Expr) →
    (evaluate θ (xs.foldl (fun expr c => .and c.toExpr expr) acc) req es =
        .ok (.prim (.bool true)) ↔
      evaluate θ acc req es = .ok (.prim (.bool true)) ∧
        ∀ x ∈ xs, evaluate θ x.toExpr req es = .ok (.prim (.bool true)))
  | [], acc => by simp
  | x :: xs, acc => by
    simp only [List.foldl_cons, foldl_true_iff xs, evaluate_and_true_iff, List.forall_mem_cons]
    constructor
    · rintro ⟨⟨h₁, h₂⟩, h₃⟩
      exact ⟨h₂, h₁, h₃⟩
    · rintro ⟨h₂, h₁, h₃⟩
      exact ⟨⟨h₁, h₂⟩, h₃⟩

/-- A rule's conditions hold exactly when each does. -/
theorem conditions_toExpr_true_iff {θ : Leaves} {req : Request} {es : Entities}
    (cs : Conditions) :
    evaluate θ (Conditions.toExpr cs) req es = .ok (.prim (.bool true)) ↔
      ∀ c ∈ cs, evaluate θ c.toExpr req es = .ok (.prim (.bool true)) := by
  unfold Conditions.toExpr
  have hm : ∀ c, c ∈ cs ↔ c ∈ cs.reverse := fun c => List.mem_reverse.symm
  simp only [hm]
  cases cs.reverse with
  | nil => simp [evaluate]
  | cons d ds => simp only [foldl_true_iff, List.forall_mem_cons]

/-- A rule is satisfied exactly when its scope holds and each of its conditions does. -/
theorem satisfied_iff {θ : Leaves} {q : Policy} {req : Request} {es : Entities} :
    satisfied θ q req es = true ↔
      q.ScopeHolds req es ∧ ∀ c ∈ q.condition, evaluate θ c.toExpr req es = .ok (.prim (.bool true))
    := by
  simp only [satisfied, decide_eq_true_eq, Policy.toExpr, evaluate_and_true_iff, evaluate_ofCedar,
    conditions_toExpr_true_iff, Policy.ScopeHolds, and_assoc]

/-- A rule with a condition added is satisfied only where the rule is. -/
theorem satisfied_of_addCondition {θ : Leaves} {q : Policy} {c : Condition} {req : Request}
    {es : Entities} (h : satisfied θ (q.addCondition c) req es = true) :
    satisfied θ q req es = true := by
  rw [satisfied_iff] at h ⊢
  exact ⟨h.1, fun d hd => h.2 d (List.mem_append_left _ hd)⟩

/-- A rule with a condition replaced by one that holds only where it does is satisfied only where
the rule is. -/
theorem satisfied_withCondition_mono {θ : Leaves} {q : Policy} {pre post : Conditions}
    {c c' : Condition} {req : Request} {es : Entities}
    (hc : evaluate θ c'.toExpr req es = .ok (.prim (.bool true)) →
      evaluate θ c.toExpr req es = .ok (.prim (.bool true)))
    (h : satisfied θ (q.withCondition pre c' post) req es = true) :
    satisfied θ (q.withCondition pre c post) req es = true := by
  rw [satisfied_iff] at h ⊢
  simp only [Policy.withCondition, List.mem_append, List.mem_cons] at h ⊢
  refine ⟨h.1, fun d hd => ?_⟩
  rcases hd with hd | rfl | hd
  · exact h.2 d (.inl hd)
  · exact hc (h.2 _ (.inr (.inl rfl)))
  · exact h.2 d (.inr (.inr hd))

private theorem mem_leaves_foldl {l : Leaf} : (xs : List Condition) → (acc : Expr) →
    (l ∈ (xs.foldl (fun expr c => .and c.toExpr expr) acc).leaves ↔
      l ∈ acc.leaves ∨ ∃ x ∈ xs, l ∈ x.toExpr.leaves)
  | [], acc => by simp
  | x :: xs, acc => by
    simp only [List.foldl_cons, mem_leaves_foldl xs, Expr.leaves, List.mem_append,
      List.mem_cons, exists_eq_or_imp]
    constructor
    · rintro ((h | h) | h)
      · exact .inr (.inl h)
      · exact .inl h
      · exact .inr (.inr h)
    · rintro (h | h | h)
      · exact .inl (.inr h)
      · exact .inl (.inl h)
      · exact .inr h

/-- The leaves of a rule are those of its conditions: its scope has none. -/
theorem mem_leaves_toExpr {q : Policy} {l : Leaf} :
    l ∈ q.toExpr.leaves ↔ ∃ c ∈ q.condition, l ∈ c.toExpr.leaves := by
  simp only [Policy.toExpr, Expr.leaves, leaves_ofCedar, List.nil_append]
  unfold Conditions.toExpr
  have hm : ∀ c, c ∈ q.condition ↔ c ∈ q.condition.reverse := fun c => List.mem_reverse.symm
  simp only [hm]
  cases q.condition.reverse with
  | nil => simp [Expr.leaves]
  | cons d ds => simp only [mem_leaves_foldl, List.mem_cons, exists_eq_or_imp]

/-- The leaves of a rule with a condition added are the rule's and the condition's. -/
theorem mem_leaves_addCondition {q : Policy} {c : Condition} {l : Leaf} :
    l ∈ (q.addCondition c).toExpr.leaves ↔ l ∈ q.toExpr.leaves ∨ l ∈ c.toExpr.leaves := by
  simp only [mem_leaves_toExpr, Policy.addCondition, List.mem_append, List.mem_singleton]
  constructor
  · rintro ⟨d, hd | rfl, hl⟩
    · exact .inl ⟨d, hd, hl⟩
    · exact .inr hl
  · rintro (⟨d, hd, hl⟩ | hl)
    · exact ⟨d, .inl hd, hl⟩
    · exact ⟨c, .inr rfl, hl⟩

/-! ## The checks -/

/-- The checks a rule makes on its own at a decision event: its providers do not fail and produce
conforming outputs, and, if its scope holds, its temporal leaves read only supplied scope
entities. -/
def _root_.Dogwood.Spec.PolicySet.RulePasses (P : PolicySet) (q : Policy)
    (ω : Provider.Providers) (e : Event) (pr rs : EntityUID) : Prop :=
  Policies.providersFail [q] ω e = false ∧ P.providerOutputsConform [q] ω e = true ∧
    P.scopeEntitiesSupplied [q] e pr rs = true

/-- The checks of `q` are among those of `q₀`: the provider calls of `q` are among those of `q₀`,
and every scope entity a temporal leaf of `q` reads, after pin injection, a temporal leaf of `q₀`
reads, and where the scope of `q` holds, the scope of `q₀` does. The scope matters only for scope
reads: check 6 looks at the rules whose scope holds, checks 7 and 8 at every rule. -/
def _root_.Dogwood.Spec.PolicySet.ChecksWithin (P : PolicySet) (q q₀ : Policy) : Prop :=
  (∀ c, Sum.inr c ∈ q.toExpr.leaves → Sum.inr c ∈ q₀.toExpr.leaves) ∧
  ∀ φ, Sum.inl φ ∈ q.toExpr.leaves → ∀ r ∈ (φ.injectPins P.schema).scopeReads,
    (∀ req es, q.scopeHolds req es = true → q₀.scopeHolds req es = true) ∧
    ∃ φ₀, Sum.inl φ₀ ∈ q₀.toExpr.leaves ∧ r ∈ (φ₀.injectPins P.schema).scopeReads

/-- A rule whose leaves are among another's, with a scope that holds only where the other's does,
has its checks among the other's. -/
theorem checksWithin_of_leaves {P : PolicySet} {q q₀ : Policy}
    (hscope : ∀ req es, q.scopeHolds req es = true → q₀.scopeHolds req es = true)
    (hl : ∀ l ∈ q.toExpr.leaves, l ∈ q₀.toExpr.leaves) : P.ChecksWithin q q₀ :=
  ⟨fun _ h => hl _ h, fun φ h _ hr => ⟨hscope, φ, hl _ h, hr⟩⟩

/-- A rule whose leaves are among another's and read no scope entity has its checks among the
other's, whatever the two scopes. -/
theorem checksWithin_of_noScopeReads {P : PolicySet} {q q₀ : Policy}
    (hl : ∀ l ∈ q.toExpr.leaves, l ∈ q₀.toExpr.leaves)
    (hnr : ∀ φ, Sum.inl φ ∈ q.toExpr.leaves → (φ.injectPins P.schema).scopeReads = []) :
    P.ChecksWithin q q₀ :=
  ⟨fun _ h => hl _ h, fun φ h r hr => by simp [hnr φ h] at hr⟩

/-- Replacing a condition by one with the same provider calls, whose temporal leaves read what the
old one's do, keeps the checks among the old rule's. -/
theorem checksWithin_withCondition {P : PolicySet} {q : Policy} {pre post : Conditions}
    {c c' : Condition}
    (hcalls : ∀ x, Sum.inr x ∈ c.toExpr.leaves → Sum.inr x ∈ c'.toExpr.leaves)
    (hreads : ∀ φ, Sum.inl φ ∈ c.toExpr.leaves → ∀ r ∈ (φ.injectPins P.schema).scopeReads,
      ∃ φ', Sum.inl φ' ∈ c'.toExpr.leaves ∧ r ∈ (φ'.injectPins P.schema).scopeReads) :
    P.ChecksWithin (q.withCondition pre c post) (q.withCondition pre c' post) := by
  have hmem : ∀ {l : Leaf}, l ∈ (q.withCondition pre c post).toExpr.leaves →
      l ∈ c.toExpr.leaves ∨ l ∈ (q.withCondition pre c' post).toExpr.leaves := by
    intro l hl
    simp only [mem_leaves_toExpr, Policy.withCondition, List.mem_append, List.mem_cons] at hl ⊢
    obtain ⟨d, hd | rfl | hd, hl⟩ := hl
    · exact .inr ⟨d, .inl hd, hl⟩
    · exact .inl hl
    · exact .inr ⟨d, .inr (.inr hd), hl⟩
  have hin : ∀ {l : Leaf}, l ∈ c'.toExpr.leaves →
      l ∈ (q.withCondition pre c' post).toExpr.leaves := fun hl =>
    mem_leaves_toExpr.mpr ⟨c', by simp [Policy.withCondition], hl⟩
  refine ⟨fun x hx => ?_, fun φ hφ r hr => ⟨fun _ _ h => h, ?_⟩⟩
  · rcases hmem hx with hx | hx
    · exact hin (hcalls x hx)
    · exact hx
  · rcases hmem hφ with hφ | hφ
    · obtain ⟨φ', hφ', hr'⟩ := hreads φ hφ r hr
      exact ⟨φ', hin hφ', hr'⟩
    · exact ⟨φ, hφ, hr⟩

/-- The checks of a list of rules with one more are those of the list and of the rule. -/
theorem _root_.Dogwood.Spec.PolicySet.Admits.cons_iff {P : PolicySet} {q : Policy} {ps : Policies}
    {ω : Provider.Providers} {p : TimePoint} {pr rs : EntityUID} :
    P.Admits (q :: ps) ω p pr rs ↔ P.Admits ps ω p pr rs ∧ P.RulePasses q ω p.event pr rs := by
  have hfail : Policies.providersFail (q :: ps) ω p.event =
      (Policies.providersFail [q] ω p.event || Policies.providersFail ps ω p.event) := by
    simp [Policies.providersFail, Policies.providerCalls, List.flatMap_cons, List.any_append]
  have hout : P.providerOutputsConform (q :: ps) ω p.event =
      (P.providerOutputsConform [q] ω p.event && P.providerOutputsConform ps ω p.event) := by
    simp [PolicySet.providerOutputsConform, Policies.providerCalls, List.flatMap_cons,
      List.all_append]
  have hsc : P.scopeEntitiesSupplied (q :: ps) p.event pr rs =
      (P.scopeEntitiesSupplied [q] p.event pr rs && P.scopeEntitiesSupplied ps p.event pr rs) := by
    simp [PolicySet.scopeEntitiesSupplied, List.all_cons]
  constructor
  · intro h
    have hp := h.providers
    have ho := h.outputs
    have hs := h.scopes
    rw [hfail, Bool.or_eq_false_iff] at hp
    rw [hout, Bool.and_eq_true] at ho
    rw [hsc, Bool.and_eq_true] at hs
    exact ⟨⟨h.kind, h.principal, h.resource, h.event, h.request, h.entities, hs.2, hp.2, ho.2⟩,
      hp.1, ho.1, hs.1⟩
  · rintro ⟨h, hp, ho, hs⟩
    refine ⟨h.kind, h.principal, h.resource, h.event, h.request, h.entities, ?_, ?_, ?_⟩
    · rw [hsc, Bool.and_eq_true]
      exact ⟨hs, h.scopes⟩
    · rw [hfail, Bool.or_eq_false_iff]
      exact ⟨hp, h.providers⟩
    · rw [hout, Bool.and_eq_true]
      exact ⟨ho, h.outputs⟩

/-- An event passes a rule's checks when they are among another's whose checks it passes. -/
theorem rulePasses_of_checksWithin {P : PolicySet} {q q₀ : Policy} {ω : Provider.Providers}
    {e : Event} {pr rs : EntityUID} (hw : P.ChecksWithin q q₀) (h : P.RulePasses q₀ ω e pr rs) :
    P.RulePasses q ω e pr rs := by
  obtain ⟨hcalls', hreads⟩ := hw
  obtain ⟨hp, ho, hs⟩ := h
  have hcalls : ∀ c ∈ Policies.providerCalls [q], c ∈ Policies.providerCalls [q₀] := by
    intro c hc
    simp only [Policies.providerCalls, List.flatMap_cons, List.flatMap_nil, List.append_nil,
      List.mem_filterMap] at hc ⊢
    obtain ⟨l, hl, hlc⟩ := hc
    cases l with
    | inl _ => cases hlc
    | inr c' =>
      simp only [Option.some.injEq] at hlc
      subst hlc
      exact ⟨.inr _, hcalls' _ hl, rfl⟩
  refine ⟨?_, ?_, ?_⟩
  · rw [Policies.providersFail, List.any_eq_false] at hp ⊢
    exact fun c hc => hp c (hcalls c hc)
  · simp only [PolicySet.providerOutputsConform, List.all_eq_true] at ho ⊢
    exact fun c hc => ho c (hcalls c hc)
  · simp only [PolicySet.scopeEntitiesSupplied, List.all_cons, List.all_nil, Bool.and_true,
      Bool.or_eq_true, Bool.not_eq_true', List.all_eq_true] at hs ⊢
    cases hq : q.scopeHolds (e.request pr rs) (P.decisionEntities e) with
    | false => exact .inl rfl
    | true =>
      refine .inr fun l hl => ?_
      cases l with
      | inr _ => rfl
      | inl φ =>
        simp only [List.all_eq_true]
        intro r hr
        obtain ⟨hscope, φ₀, hφ₀, hr₀⟩ := hreads φ hl r hr
        rcases hs with hs | hs
        · rw [hscope _ _ hq] at hs
          cases hs
        have := hs _ hφ₀
        simp only [List.all_eq_true] at this
        exact this r hr₀

/-- An event passes a rule's checks when the rule's leaves are among another's whose checks it
passes, and the rule's scope holds only where the other's does. -/
theorem rulePasses_of_leaves {P : PolicySet} {q q₀ : Policy} {ω : Provider.Providers} {e : Event}
    {pr rs : EntityUID}
    (hscope : ∀ req es, q.scopeHolds req es = true → q₀.scopeHolds req es = true)
    (hl : ∀ l ∈ q.toExpr.leaves, l ∈ q₀.toExpr.leaves) (h : P.RulePasses q₀ ω e pr rs) :
    P.RulePasses q ω e pr rs :=
  rulePasses_of_checksWithin (checksWithin_of_leaves hscope hl) h

/-- A rule with no leaves passes every check. -/
theorem rulePasses_of_leaves_nil {P : PolicySet} {q : Policy} {ω : Provider.Providers}
    {e : Event} {pr rs : EntityUID} (h : q.toExpr.leaves = []) : P.RulePasses q ω e pr rs := by
  refine ⟨?_, ?_, ?_⟩
  · simp [Policies.providersFail, Policies.providerCalls, h]
  · simp [PolicySet.providerOutputsConform, Policies.providerCalls, h]
  · simp [PolicySet.scopeEntitiesSupplied, h]

/-! ## Temporal conditions with stricter windows -/

end Dogwood.Thm

namespace Dogwood.Spec

open Dogwood.Spec.Temporal

/-- The temporal condition `c'` is `c` with stricter windows: under `when`, the windows of its
formula narrowed in positive positions; under `unless`, widened. -/
inductive Condition.Tightens (rate : TickRate) : Condition → Condition → Prop
  | whenCond {φ φ' : Formula} : Formula.Widens rate φ' φ →
      Condition.Tightens rate ⟨.when, .temporal φ⟩ ⟨.when, .temporal φ'⟩
  | unlessCond {φ φ' : Formula} : Formula.Widens rate φ φ' →
      Condition.Tightens rate ⟨.unless, .temporal φ⟩ ⟨.unless, .temporal φ'⟩

end Dogwood.Spec

namespace Dogwood.Thm

open Dogwood.Spec Dogwood.Spec.Temporal
open Cedar.Spec (Request Entities EntityUID Effect Decision Response)

/-- A condition with stricter windows holds, at the leaf valuation of a decision, only where the
condition does. -/
theorem _root_.Dogwood.Spec.Condition.Tightens.evaluate {ι : ImplChoices} {P : PolicySet}
    {ω : Provider.Providers}
    {σ : Trace} {n : Nat} {e : Event} {req : Request} {es : Entities} {c c' : Condition}
    (ht : Condition.Tightens P.tickRate c c')
    (h : Dogwood.Spec.evaluate (P.leaves ι ω σ n e) c'.toExpr req es = .ok (.prim (.bool true))) :
    Dogwood.Spec.evaluate (P.leaves ι ω σ n e) c.toExpr req es = .ok (.prim (.bool true)) := by
  cases ht with
  | whenCond hW =>
    simp only [Condition.toExpr, Dogwood.Spec.evaluate, PolicySet.leaves, Except.ok.injEq,
      Cedar.Spec.Value.prim.injEq, Cedar.Spec.Prim.bool.injEq, decide_eq_true_eq] at h ⊢
    obtain ⟨p, hσ, hs⟩ := h
    exact ⟨p, hσ, hW.injectPins.sat hs⟩
  | unlessCond hW =>
    have hb : ∀ φ₀, Dogwood.Spec.evaluate (P.leaves ι ω σ n e)
        (Condition.toExpr ⟨.unless, .temporal φ₀⟩) req es = .ok (.prim (.bool true)) ↔
        ¬ P.LeafHolds ι σ n φ₀ := by
      intro φ₀
      simp [Condition.toExpr, Dogwood.Spec.evaluate, PolicySet.leaves, Cedar.Spec.apply₁]
    rw [hb] at h ⊢
    rintro ⟨p, hσ, hs⟩
    exact h ⟨p, hσ, hW.injectPins.sat hs⟩

/-- A condition with stricter windows has the leaf of the condition, up to windows. -/
private theorem _root_.Dogwood.Spec.Condition.Tightens.leaves {rate : TickRate} {c c' : Condition}
    (ht : Condition.Tightens rate c c') :
    ∃ φ φ', c.toExpr.leaves = [.inl φ] ∧ c'.toExpr.leaves = [.inl φ'] ∧
      (Formula.Widens rate φ φ' ∨ Formula.Widens rate φ' φ) := by
  cases ht with
  | whenCond hW => exact ⟨_, _, rfl, rfl, .inr hW⟩
  | unlessCond hW => exact ⟨_, _, rfl, rfl, .inl hW⟩

/-- Tightening or loosening the windows of a condition keeps the checks. -/
theorem checksWithin_tightens {P : PolicySet} {q : Policy} {pre post : Conditions}
    {c c' : Condition}
    (ht : Condition.Tightens P.tickRate c c' ∨ Condition.Tightens P.tickRate c' c) :
    P.ChecksWithin (q.withCondition pre c post) (q.withCondition pre c' post) := by
  have : ∃ φ φ', c.toExpr.leaves = [.inl φ] ∧ c'.toExpr.leaves = [.inl φ'] ∧
      (φ.injectPins P.schema).scopeReads = (φ'.injectPins P.schema).scopeReads := by
    rcases ht with ht | ht
    · obtain ⟨φ, φ', h, h', hW⟩ := ht.leaves
      refine ⟨φ, φ', h, h', ?_⟩
      rcases hW with hW | hW
      · exact hW.injectPins.scopeReads_eq
      · exact hW.injectPins.scopeReads_eq.symm
    · obtain ⟨φ', φ, h', h, hW⟩ := ht.leaves
      refine ⟨φ, φ', h, h', ?_⟩
      rcases hW with hW | hW
      · exact hW.injectPins.scopeReads_eq.symm
      · exact hW.injectPins.scopeReads_eq
  obtain ⟨φ, φ', h, h', hr⟩ := this
  refine checksWithin_withCondition (fun x hx => ?_) (fun ψ hψ r hr' => ?_)
  · rw [h] at hx
    simp at hx
  · rw [h, List.mem_singleton, Sum.inl.injEq] at hψ
    subst hψ
    exact ⟨φ', by rw [h']; exact List.mem_singleton_self _, hr ▸ hr'⟩

/-! ## The general form -/

variable {ι : ImplChoices} {P : PolicySet} {ω : Provider.Providers} {σ : Trace} {n : Nat}

/-- The checks of a policy set read its rules, not its own policy list. -/
theorem _root_.Dogwood.Spec.PolicySet.Admits.with_iff {ps rules : Policies} {p : TimePoint}
    {pr rs : EntityUID} :
    ({ P with policies := ps } : PolicySet).Admits rules ω p pr rs ↔
      P.Admits rules ω p pr rs :=
  ⟨fun h => ⟨h.kind, h.principal, h.resource, h.event, h.request, h.entities, h.scopes,
    h.providers, h.outputs⟩,
   fun h => ⟨h.kind, h.principal, h.resource, h.event, h.request, h.entities, h.scopes,
    h.providers, h.outputs⟩⟩

/-- **Refinement, in general.** If every event that passes the checks of the new rules `ps'`
passes the old rules', and there, at the leaf valuation of every completion of the reading, the
new rules allow only what the policy set's rules allow, then an event the new rules allow, the
policy set allows, unless its decision fails closed for a temporal error. (The proof uses the
refinement at one completion only.)

The exception is needed, even with distinct policy ids. Take as the old rules an unconditional
`permit`, and a `permit` with another id whose temporal condition holds under one completion of
the reading and not under another; the old decision fails closed, since the completions disagree
on the policies that determine it. Adding `when { false }` to the second `permit` makes the
completions agree, and the new rules allow. -/
theorem authorize_allow_of_refines {ps' : Policies}
    (hcheck : ∀ p pr rs, σ[n]? = some p → P.Admits ps' ω p pr rs →
      P.Admits P.policies ω p pr rs)
    (hreq : ∀ p pr rs, σ[n]? = some p → P.Admits ps' ω p pr rs → ∀ ι', ι'.Completes ι →
      (isAuthorized (P.leaves ι' ω σ n p.event) (p.event.request pr rs)
        (P.decisionEntities p.event) ps').decision = .allow →
      (isAuthorized (P.leaves ι' ω σ n p.event) (p.event.request pr rs)
        (P.decisionEntities p.event) P.policies).decision = .allow)
    (hP : P.authorize ι ω σ n ≠ .failClosed .temporalError)
    (h : (({ P with policies := ps' } : PolicySet).authorize ι ω σ n).decision? = some .allow) :
    (P.authorize ι ω σ n).decision? = some .allow := by
  obtain ⟨p, pr, rs, r, hσ, ha', hr, hra⟩ := decideWith_decision?_allow h
  have ha := PolicySet.Admits.with_iff.mp ha'
  have hA := authorize_of_admits (ι := ι) hσ (hcheck p pr rs hσ ha)
  obtain ⟨ι₀, hc₀⟩ := exists_completes ι
  cases hresp : P.respond ι ω σ n p.event pr rs with
  | none => exact absurd (by rw [hA, hresp]) hP
  | some rP =>
    rw [hA, hresp]
    have h₁ := supervaluate_eq_some_iff.mp hresp ι₀ hc₀
    have h₂ := supervaluate_eq_some_iff.mp hr ι₀ hc₀
    have hallow : (isAuthorized (P.leaves ι₀ ω σ n p.event) (p.event.request pr rs)
        (P.decisionEntities p.event) ps').decision = .allow := by
      rw [show isAuthorized (P.leaves ι₀ ω σ n p.event) (p.event.request pr rs)
          (P.decisionEntities p.event) ps' = r from h₂]
      exact hra
    have := hreq p pr rs hσ ha ι₀ hc₀ hallow
    simp only [Outcome.decision?, Option.some.injEq]
    rw [← h₁]
    exact this

/-- **Refinement, at every leaf valuation.** -/
theorem authorize_allow_of_refines_of_forall {ps' : Policies}
    (hcheck : ∀ p pr rs, σ[n]? = some p → P.Admits ps' ω p pr rs →
      P.Admits P.policies ω p pr rs)
    (hreq : ∀ θ req es, (isAuthorized θ req es ps').decision = .allow →
      (isAuthorized θ req es P.policies).decision = .allow)
    (hP : P.authorize ι ω σ n ≠ .failClosed .temporalError)
    (h : (({ P with policies := ps' } : PolicySet).authorize ι ω σ n).decision? = some .allow) :
    (P.authorize ι ω σ n).decision? = some .allow :=
  authorize_allow_of_refines hcheck (fun _ _ _ _ _ _ _ => hreq _ _ _) hP h

/-- **Refinement, in general, under a total reading.** -/
theorem authorize_allow_of_refines_of_total (hι : ι.Total) {ps' : Policies}
    (hcheck : ∀ p pr rs, σ[n]? = some p → P.Admits ps' ω p pr rs →
      P.Admits P.policies ω p pr rs)
    (hreq : ∀ p pr rs, σ[n]? = some p → P.Admits ps' ω p pr rs → ∀ ι', ι'.Completes ι →
      (isAuthorized (P.leaves ι' ω σ n p.event) (p.event.request pr rs)
        (P.decisionEntities p.event) ps').decision = .allow →
      (isAuthorized (P.leaves ι' ω σ n p.event) (p.event.request pr rs)
        (P.decisionEntities p.event) P.policies).decision = .allow)
    (h : (({ P with policies := ps' } : PolicySet).authorize ι ω σ n).decision? = some .allow) :
    (P.authorize ι ω σ n).decision? = some .allow :=
  authorize_allow_of_refines hcheck hreq (authorize_ne_temporalError_of_total hι) h

/-! ## Per request -/

section

variable {θ : Leaves} {req : Request} {es : Entities} {q q' : Policy} {ps : Policies}

/-- Replacing a `permit` by one satisfied only where it is allows only what the `permit`
allows. -/
theorem allow_of_replace_permit (hq : q.effect = .permit) (hq' : q'.effect = .permit)
    (hs : satisfied θ q' req es = true → satisfied θ q req es = true)
    (h : (isAuthorized θ req es (q' :: ps)).decision = .allow) :
    (isAuthorized θ req es (q :: ps)).decision = .allow := by
  obtain ⟨⟨p, hp, he, hsp⟩, hf⟩ := (allowed_iff_explicitly_permitted_and_not_forbidden _ _ _).mp h
  refine (allowed_iff_explicitly_permitted_and_not_forbidden _ _ _).mpr ⟨?_, ?_⟩
  · rcases List.mem_cons.mp hp with rfl | hp
    · exact ⟨q, List.mem_cons_self .., hq, hs hsp⟩
    · exact ⟨p, List.mem_cons_of_mem _ hp, he, hsp⟩
  · rintro ⟨p, hp, he, hsp⟩
    rcases List.mem_cons.mp hp with rfl | hp
    · rw [hq] at he
      cases he
    · exact hf ⟨p, List.mem_cons_of_mem _ hp, he, hsp⟩

/-- Replacing a `forbid` by one satisfied wherever it is allows only what the `forbid`
allows. -/
theorem allow_of_replace_forbid (hq : q.effect = .forbid) (hq' : q'.effect = .forbid)
    (hs : satisfied θ q req es = true → satisfied θ q' req es = true)
    (h : (isAuthorized θ req es (q' :: ps)).decision = .allow) :
    (isAuthorized θ req es (q :: ps)).decision = .allow := by
  obtain ⟨⟨p, hp, he, hsp⟩, hf⟩ := (allowed_iff_explicitly_permitted_and_not_forbidden _ _ _).mp h
  refine (allowed_iff_explicitly_permitted_and_not_forbidden _ _ _).mpr ⟨?_, ?_⟩
  · rcases List.mem_cons.mp hp with rfl | hp
    · rw [hq'] at he
      cases he
    · exact ⟨p, List.mem_cons_of_mem _ hp, he, hsp⟩
  · rintro ⟨p, hp, he, hsp⟩
    rcases List.mem_cons.mp hp with rfl | hp
    · exact hf ⟨q', List.mem_cons_self .., hq', hs hsp⟩
    · exact hf ⟨p, List.mem_cons_of_mem _ hp, he, hsp⟩

/-- Strengthening a `permit` allows only what the `permit` allows. -/
theorem allow_of_strengthen_permit (hq : q.effect = .permit) (c : Condition)
    (h : (isAuthorized θ req es (q.addCondition c :: ps)).decision = .allow) :
    (isAuthorized θ req es (q :: ps)).decision = .allow :=
  allow_of_replace_permit (q' := q.addCondition c) hq hq satisfied_of_addCondition h

/-- Weakening a `forbid` allows only what the `forbid` allows. -/
theorem allow_of_weaken_forbid (hq : q.effect = .forbid) (c : Condition)
    (h : (isAuthorized θ req es (q :: ps)).decision = .allow) :
    (isAuthorized θ req es (q.addCondition c :: ps)).decision = .allow :=
  allow_of_replace_forbid (q := q.addCondition c) (q' := q) hq hq satisfied_of_addCondition h

/-- Adding a `permit` keeps an allow, per request. -/
theorem allow_of_add_permit (hq : q.effect = .permit)
    (h : (isAuthorized θ req es ps).decision = .allow) :
    (isAuthorized θ req es (q :: ps)).decision = .allow := by
  obtain ⟨⟨p, hp, he, hs⟩, hf⟩ := (allowed_iff_explicitly_permitted_and_not_forbidden _ _ _).mp h
  refine (allowed_iff_explicitly_permitted_and_not_forbidden _ _ _).mpr
    ⟨⟨p, List.mem_cons_of_mem _ hp, he, hs⟩, ?_⟩
  rintro ⟨p, hp, he, hs⟩
  rcases List.mem_cons.mp hp with rfl | hp
  · rw [hq] at he
    cases he
  · exact hf ⟨p, hp, he, hs⟩

/-- Removing a `forbid` keeps an allow, per request. -/
theorem allow_of_remove_forbid (hq : q.effect = .forbid)
    (h : (isAuthorized θ req es (q :: ps)).decision = .allow) :
    (isAuthorized θ req es ps).decision = .allow := by
  obtain ⟨⟨p, hp, he, hs⟩, hf⟩ := (allowed_iff_explicitly_permitted_and_not_forbidden _ _ _).mp h
  refine (allowed_iff_explicitly_permitted_and_not_forbidden _ _ _).mpr ⟨?_, fun ⟨p, hp, he, hs⟩ =>
    hf ⟨p, List.mem_cons_of_mem _ hp, he, hs⟩⟩
  rcases List.mem_cons.mp hp with rfl | hp
  · rw [hq] at he
    cases he
  · exact ⟨p, hp, he, hs⟩

/-- `isAuthorizedEach` allows exactly when some rule is a satisfied `permit` and none a satisfied
`forbid`, each under its own valuation. -/
theorem isAuthorizedEach_allow_iff {rules : List (Policy × Leaves)} :
    (isAuthorizedEach req es rules).decision = .allow ↔
      (∃ r ∈ rules, satisfiedWithEffect r.2 .permit r.1 req es ≠ none) ∧
        ∀ r ∈ rules, satisfiedWithEffect r.2 .forbid r.1 req es = none := by
  unfold isAuthorizedEach
  dsimp only
  split
  · rename_i hc
    simp only [Bool.and_eq_true, Bool.not_eq_true', Cedar.Data.Set.isEmpty_make,
      Cedar.Data.Set.isEmpty_make_eq_false, ne_eq, List.filterMap_eq_nil_iff] at hc
    simp only [true_iff]
    refine ⟨?_, hc.1⟩
    by_contra hne
    simp only [not_exists, not_and, Decidable.not_not] at hne
    exact hc.2 hne
  · rename_i hc
    simp only [reduceCtorEq, false_iff, not_and]
    intro ⟨r, hr, hs⟩ hf
    apply hc
    simp only [Bool.and_eq_true, Bool.not_eq_true', Cedar.Data.Set.isEmpty_make,
      Cedar.Data.Set.isEmpty_make_eq_false, ne_eq, List.filterMap_eq_nil_iff]
    refine ⟨hf, fun hnil => hs ?_⟩
    exact hnil r hr

end

/-! ## Strengthening a `permit` over a trace -/

/-- **Strengthening a `permit` never creates an allow**: replacing a `permit` by one that, at the
leaf valuations of the decision, is satisfied only where it is, when the old `permit` passes its
own checks wherever the new one does, unless the policy set's decision fails closed for a temporal
error. -/
theorem authorize_allow_of_replace_permit {q q' : Policy} {ps : Policies}
    (hq : q.effect = .permit) (hq' : q'.effect = .permit) (hps : P.policies = q :: ps)
    (hsat : ∀ p pr rs, σ[n]? = some p → P.Admits (q' :: ps) ω p pr rs → ∀ ι', ι'.Completes ι →
      satisfied (P.leaves ι' ω σ n p.event) q' (p.event.request pr rs)
        (P.decisionEntities p.event) = true →
      satisfied (P.leaves ι' ω σ n p.event) q (p.event.request pr rs)
        (P.decisionEntities p.event) = true)
    (hpass : ∀ p pr rs, σ[n]? = some p → P.Admits (q' :: ps) ω p pr rs →
      P.RulePasses q ω p.event pr rs)
    (hP : P.authorize ι ω σ n ≠ .failClosed .temporalError)
    (h : (({ P with policies := q' :: ps } : PolicySet).authorize ι ω σ n).decision? =
      some .allow) :
    (P.authorize ι ω σ n).decision? = some .allow := by
  refine authorize_allow_of_refines (fun p pr rs hσ ha => ?_)
    (fun p pr rs hσ ha ι' hc ha' => ?_) hP h
  · rw [hps]
    exact PolicySet.Admits.cons_iff.mpr ⟨(PolicySet.Admits.cons_iff.mp ha).1, hpass p pr rs hσ ha⟩
  · rw [hps]
    exact allow_of_replace_permit hq hq' (hsat p pr rs hσ ha ι' hc) ha'

/-- **Strengthening a `permit` whose checks are among the new one's never creates an allow.** -/
theorem authorize_allow_of_replace_permit_of_checksWithin {q q' : Policy} {ps : Policies}
    (hq : q.effect = .permit) (hq' : q'.effect = .permit) (hps : P.policies = q :: ps)
    (hsat : ∀ p pr rs, σ[n]? = some p → P.Admits (q' :: ps) ω p pr rs → ∀ ι', ι'.Completes ι →
      satisfied (P.leaves ι' ω σ n p.event) q' (p.event.request pr rs)
        (P.decisionEntities p.event) = true →
      satisfied (P.leaves ι' ω σ n p.event) q (p.event.request pr rs)
        (P.decisionEntities p.event) = true)
    (hw : P.ChecksWithin q q')
    (hP : P.authorize ι ω σ n ≠ .failClosed .temporalError)
    (h : (({ P with policies := q' :: ps } : PolicySet).authorize ι ω σ n).decision? =
      some .allow) :
    (P.authorize ι ω σ n).decision? = some .allow :=
  authorize_allow_of_replace_permit hq hq' hps hsat
    (fun _ _ _ _ ha => rulePasses_of_checksWithin hw (PolicySet.Admits.cons_iff.mp ha).2) hP h

/-- **Adding a condition to a `permit` never creates an allow**, unless the policy set's decision
fails closed for a temporal error. The added condition can only add provider calls and scope
reads, so the checks only get stricter. The exception is needed: the counterexample of
`authorize_allow_of_refines` adds a condition to a `permit`. -/
theorem authorize_allow_of_strengthen_permit {q : Policy} {ps : Policies} (c : Condition)
    (hq : q.effect = .permit) (hps : P.policies = q :: ps)
    (hP : P.authorize ι ω σ n ≠ .failClosed .temporalError)
    (h : (({ P with policies := q.addCondition c :: ps } : PolicySet).authorize ι ω σ n).decision? =
      some .allow) :
    (P.authorize ι ω σ n).decision? = some .allow :=
  authorize_allow_of_replace_permit_of_checksWithin (q' := q.addCondition c) hq hq hps
    (fun _ _ _ _ _ _ _ => satisfied_of_addCondition)
    (checksWithin_of_leaves (fun _ _ h => h) fun _ hl => mem_leaves_addCondition.mpr (.inl hl)) hP h

/-- **Tightening the windows of a `permit`'s temporal condition never creates an allow**: replacing
a condition `when { φ }` of a `permit` by `when { φ' }` with windows narrowed in positive positions
(`φ` widens `φ'`, `Formula.Widens`), or `unless { φ }` by `unless { φ' }` with windows widened,
unless the policy set's decision fails closed for a temporal error. The new condition holds only
where the old one does, and reads the same scope entities. -/
theorem authorize_allow_of_tighten_permit_window {q : Policy} {pre post : Conditions}
    {ps : Policies} {c c' : Condition} (hq : q.effect = .permit)
    (ht : Condition.Tightens P.tickRate c c') (hps : P.policies = q.withCondition pre c post :: ps)
    (hP : P.authorize ι ω σ n ≠ .failClosed .temporalError)
    (h : (({ P with policies := q.withCondition pre c' post :: ps } : PolicySet).authorize
      ι ω σ n).decision? = some .allow) :
    (P.authorize ι ω σ n).decision? = some .allow :=
  authorize_allow_of_replace_permit_of_checksWithin (q := q.withCondition pre c post)
    (q' := q.withCondition pre c' post) hq hq hps
    (fun _ _ _ _ _ _ _ => satisfied_withCondition_mono ht.evaluate)
    (checksWithin_tightens (.inl ht)) hP h

/-- **Narrowing the scope of a `permit` whose temporal leaves read no scope entity never creates
an allow**: replacing a `permit` by one with the same conditions whose scope constraints each hold
only where the old ones do, unless the policy set's decision fails closed for a temporal error.
Without the hypothesis on scope reads it can: where the old scope holds and the new one does not,
the old rule's temporal leaves were checked (check 6) and the new rule's are not. -/
theorem authorize_allow_of_narrow_permit_scope {q q' : Policy} {ps : Policies}
    (hq : q.effect = .permit) (hq' : q'.effect = .permit) (hc : q'.condition = q.condition)
    (hscope : ∀ req es, q'.ScopeHolds req es → q.ScopeHolds req es)
    (hnr : ∀ φ, Sum.inl φ ∈ q.toExpr.leaves → (φ.injectPins P.schema).scopeReads = [])
    (hps : P.policies = q :: ps)
    (hP : P.authorize ι ω σ n ≠ .failClosed .temporalError)
    (h : (({ P with policies := q' :: ps } : PolicySet).authorize ι ω σ n).decision? =
      some .allow) :
    (P.authorize ι ω σ n).decision? = some .allow := by
  refine authorize_allow_of_replace_permit_of_checksWithin hq hq' hps
    (fun _ _ _ _ _ _ _ hs => ?_) (checksWithin_of_noScopeReads (fun l hl => ?_) hnr) hP h
  · rw [satisfied_iff] at hs ⊢
    exact ⟨hscope _ _ hs.1, hc ▸ hs.2⟩
  · rw [mem_leaves_toExpr] at hl ⊢
    rw [hc]
    exact hl

/-! ## Weakening a `forbid` over a trace -/

/-- **Weakening a `forbid` never creates an allow**: replacing a `forbid` by one that, at the leaf
valuations of the decision, is satisfied wherever it is, when the old `forbid` passes its own
checks wherever the new one does, unless the policy set's decision fails closed for a temporal
error. A `forbid` that fails them, say through a provider that fails, was failing the old decision
closed, and replacing it can create an allow. -/
theorem authorize_allow_of_replace_forbid {q q' : Policy} {ps : Policies}
    (hq : q.effect = .forbid) (hq' : q'.effect = .forbid) (hps : P.policies = q :: ps)
    (hsat : ∀ p pr rs, σ[n]? = some p → P.Admits (q' :: ps) ω p pr rs → ∀ ι', ι'.Completes ι →
      satisfied (P.leaves ι' ω σ n p.event) q (p.event.request pr rs)
        (P.decisionEntities p.event) = true →
      satisfied (P.leaves ι' ω σ n p.event) q' (p.event.request pr rs)
        (P.decisionEntities p.event) = true)
    (hpass : ∀ p pr rs, σ[n]? = some p → P.Admits (q' :: ps) ω p pr rs →
      P.RulePasses q ω p.event pr rs)
    (hP : P.authorize ι ω σ n ≠ .failClosed .temporalError)
    (h : (({ P with policies := q' :: ps } : PolicySet).authorize ι ω σ n).decision? =
      some .allow) :
    (P.authorize ι ω σ n).decision? = some .allow := by
  refine authorize_allow_of_refines (fun p pr rs hσ ha => ?_)
    (fun p pr rs hσ ha ι' hc ha' => ?_) hP h
  · rw [hps]
    exact PolicySet.Admits.cons_iff.mpr ⟨(PolicySet.Admits.cons_iff.mp ha).1, hpass p pr rs hσ ha⟩
  · rw [hps]
    exact allow_of_replace_forbid hq hq' (hsat p pr rs hσ ha ι' hc) ha'

/-- **Weakening a `forbid` whose checks are among the new one's never creates an allow.** -/
theorem authorize_allow_of_replace_forbid_of_checksWithin {q q' : Policy} {ps : Policies}
    (hq : q.effect = .forbid) (hq' : q'.effect = .forbid) (hps : P.policies = q :: ps)
    (hsat : ∀ p pr rs, σ[n]? = some p → P.Admits (q' :: ps) ω p pr rs → ∀ ι', ι'.Completes ι →
      satisfied (P.leaves ι' ω σ n p.event) q (p.event.request pr rs)
        (P.decisionEntities p.event) = true →
      satisfied (P.leaves ι' ω σ n p.event) q' (p.event.request pr rs)
        (P.decisionEntities p.event) = true)
    (hw : P.ChecksWithin q q')
    (hP : P.authorize ι ω σ n ≠ .failClosed .temporalError)
    (h : (({ P with policies := q' :: ps } : PolicySet).authorize ι ω σ n).decision? =
      some .allow) :
    (P.authorize ι ω σ n).decision? = some .allow :=
  authorize_allow_of_replace_forbid hq hq' hps hsat
    (fun _ _ _ _ ha => rulePasses_of_checksWithin hw (PolicySet.Admits.cons_iff.mp ha).2) hP h

/-- **Removing a condition from a `forbid` never creates an allow**, when the `forbid` with its
condition passes its own checks at the event (`PolicySet.RulePasses`), unless the policy set's
decision fails closed for a temporal error. -/
theorem authorize_allow_of_weaken_forbid {q : Policy} {ps : Policies} {c : Condition}
    (hq : q.effect = .forbid) (hps : P.policies = q.addCondition c :: ps)
    (hpass : ∀ p pr rs, σ[n]? = some p → P.Admits (q :: ps) ω p pr rs →
      P.RulePasses (q.addCondition c) ω p.event pr rs)
    (hP : P.authorize ι ω σ n ≠ .failClosed .temporalError)
    (h : (({ P with policies := q :: ps } : PolicySet).authorize ι ω σ n).decision? =
      some .allow) :
    (P.authorize ι ω σ n).decision? = some .allow :=
  authorize_allow_of_replace_forbid (q := q.addCondition c) (q' := q) hq hq hps
    (fun _ _ _ _ _ _ _ => satisfied_of_addCondition) hpass hP h

/-- **Removing a condition from a `forbid` never creates an allow** when the removed condition's
leaves are among the rest of the rule's: the `forbid` with the condition then passes the checks
the `forbid` without it does. -/
theorem authorize_allow_of_weaken_forbid_of_leaves {q : Policy} {ps : Policies} {c : Condition}
    (hq : q.effect = .forbid) (hps : P.policies = q.addCondition c :: ps)
    (hc : ∀ l ∈ c.toExpr.leaves, l ∈ q.toExpr.leaves)
    (hP : P.authorize ι ω σ n ≠ .failClosed .temporalError)
    (h : (({ P with policies := q :: ps } : PolicySet).authorize ι ω σ n).decision? =
      some .allow) :
    (P.authorize ι ω σ n).decision? = some .allow := by
  refine authorize_allow_of_replace_forbid_of_checksWithin (q := q.addCondition c) (q' := q)
    hq hq hps (fun _ _ _ _ _ _ _ => satisfied_of_addCondition)
    (checksWithin_of_leaves (fun _ _ h => h) fun l hl => ?_) hP h
  rcases mem_leaves_addCondition.mp hl with hl | hl
  · exact hl
  · exact hc l hl

/-- **Loosening the windows of a `forbid`'s temporal condition never creates an allow**: replacing
a condition `when { φ }` of a `forbid` by `when { φ' }` with windows widened in positive positions,
or `unless { φ }` by `unless { φ' }` with windows narrowed, unless the policy set's decision fails
closed for a temporal error. -/
theorem authorize_allow_of_loosen_forbid_window {q : Policy} {pre post : Conditions}
    {ps : Policies} {c c' : Condition} (hq : q.effect = .forbid)
    (ht : Condition.Tightens P.tickRate c' c) (hps : P.policies = q.withCondition pre c post :: ps)
    (hP : P.authorize ι ω σ n ≠ .failClosed .temporalError)
    (h : (({ P with policies := q.withCondition pre c' post :: ps } : PolicySet).authorize
      ι ω σ n).decision? = some .allow) :
    (P.authorize ι ω σ n).decision? = some .allow :=
  authorize_allow_of_replace_forbid_of_checksWithin (q := q.withCondition pre c post)
    (q' := q.withCondition pre c' post) hq hq hps
    (fun _ _ _ _ _ _ _ => satisfied_withCondition_mono ht.evaluate)
    (checksWithin_tightens (.inr ht)) hP h

/-- **Widening the scope of a `forbid` never creates an allow**: replacing a `forbid` by one with
the same conditions whose scope holds wherever the old one does, unless the policy set's decision
fails closed for a temporal error. -/
theorem authorize_allow_of_widen_forbid_scope {q q' : Policy} {ps : Policies}
    (hq : q.effect = .forbid) (hq' : q'.effect = .forbid) (hc : q'.condition = q.condition)
    (hscope : ∀ req es, q.ScopeHolds req es → q'.ScopeHolds req es)
    (hps : P.policies = q :: ps)
    (hP : P.authorize ι ω σ n ≠ .failClosed .temporalError)
    (h : (({ P with policies := q' :: ps } : PolicySet).authorize ι ω σ n).decision? =
      some .allow) :
    (P.authorize ι ω σ n).decision? = some .allow := by
  refine authorize_allow_of_replace_forbid_of_checksWithin hq hq' hps
    (fun _ _ _ _ _ _ _ hs => ?_) ?_ hP h
  · rw [satisfied_iff] at hs ⊢
    exact ⟨hscope _ _ hs.1, hc ▸ hs.2⟩
  · refine checksWithin_of_leaves (fun req es hs => ?_) fun l hl => ?_
    · rw [scopeHolds_iff] at hs ⊢
      exact hscope _ _ hs
    · rw [mem_leaves_toExpr] at hl ⊢
      rw [hc]
      exact hl

/-! ## Removing and adding rules over a trace -/

/-- **Removing a `permit` never creates an allow** when the `permit` passes its own checks at the
event (`PolicySet.RulePasses`: its providers do not fail and produce conforming outputs, and its
temporal leaves read only supplied scope entities), unless the policy set's decision fails closed
for a temporal error. Removing it can then only turn an allow into a deny. A `permit` that fails
its checks was failing the old decision closed, and removing it can create an allow. This is
`authorize_unchanged_allow_when_add_permit` read backwards. -/
theorem authorize_allow_of_remove_permit {q : Policy} {ps : Policies}
    (hq : q.effect = .permit) (hps : P.policies = q :: ps)
    (hpass : ∀ p pr rs, σ[n]? = some p → P.Admits ps ω p pr rs → P.RulePasses q ω p.event pr rs)
    (hP : P.authorize ι ω σ n ≠ .failClosed .temporalError)
    (h : (({ P with policies := ps } : PolicySet).authorize ι ω σ n).decision? = some .allow) :
    (P.authorize ι ω σ n).decision? = some .allow := by
  refine authorize_allow_of_refines_of_forall (fun p pr rs hσ ha => ?_)
    (fun θ req es ha => ?_) hP h
  · rw [hps]
    exact PolicySet.Admits.cons_iff.mpr ⟨ha, hpass p pr rs hσ ha⟩
  · rw [hps]
    exact allow_of_add_permit hq ha

/-- **Removing a `permit` without leaves never creates an allow**: it passes every check. -/
theorem authorize_allow_of_remove_permit_of_leaves_nil {q : Policy} {ps : Policies}
    (hq : q.effect = .permit) (hps : P.policies = q :: ps) (hl : q.toExpr.leaves = [])
    (hP : P.authorize ι ω σ n ≠ .failClosed .temporalError)
    (h : (({ P with policies := ps } : PolicySet).authorize ι ω σ n).decision? = some .allow) :
    (P.authorize ι ω σ n).decision? = some .allow :=
  authorize_allow_of_remove_permit hq hps (fun _ _ _ _ _ => rulePasses_of_leaves_nil hl) hP h

/-- **Removing a `forbid` keeps an allow**, unless the decision without it fails closed for a
temporal error. The removed rule's checks only go away. -/
theorem authorize_unchanged_allow_when_remove_forbid {q : Policy} (hq : q.effect = .forbid)
    (hP : P.authorize ι ω σ n ≠ .failClosed .temporalError)
    (h : (({ P with policies := q :: P.policies } : PolicySet).authorize ι ω σ n).decision? =
      some .allow) :
    (P.authorize ι ω σ n).decision? = some .allow :=
  authorize_allow_of_refines_of_forall (fun _ _ _ _ ha => (PolicySet.Admits.cons_iff.mp ha).1)
    (fun _ _ _ ha => allow_of_remove_forbid hq ha) hP h

/-- **An allow with a `permit` added means the `permit` passes the checks**, under every reading:
where the policy set allows, the new rule's providers do not fail and produce conforming outputs,
and its temporal leaves read only supplied scope entities. -/
theorem rulePasses_of_authorize_add_permit {q : Policy}
    (h' : (({ P with policies := q :: P.policies } : PolicySet).authorize ι ω σ n).decision? =
      some .allow) :
    ∀ p pr rs, σ[n]? = some p → P.Admits P.policies ω p pr rs →
      P.RulePasses q ω p.event pr rs := by
  intro p pr rs hσ ha
  obtain ⟨p', pr', rs', r, hσ', ha', _, _⟩ := decideWith_decision?_allow h'
  rw [hσ] at hσ'
  cases hσ'
  have ha'' := PolicySet.Admits.with_iff.mp ha'
  have hpr : pr = pr' := Option.some.inj (ha.principal.symm.trans ha''.principal)
  have hrs : rs = rs' := Option.some.inj (ha.resource.symm.trans ha''.resource)
  subst hpr hrs
  exact (PolicySet.Admits.cons_iff.mp ha'').2

/-- **Adding a `permit` that passes the checks keeps an allow**, under every reading, unless the
new decision fails closed for a temporal error: the new rule's leaves may depend on how an
out-of-range result is read, and the completions of the reading may then disagree. Read backwards,
this is `authorize_allow_of_remove_permit`. -/
theorem authorize_unchanged_allow_when_add_permit {q : Policy} (hq : q.effect = .permit)
    (h : (P.authorize ι ω σ n).decision? = some .allow)
    (hpass : ∀ p pr rs, σ[n]? = some p → P.Admits P.policies ω p pr rs →
      P.RulePasses q ω p.event pr rs)
    (hP' : ({ P with policies := q :: P.policies } : PolicySet).authorize ι ω σ n ≠
      .failClosed .temporalError) :
    (({ P with policies := q :: P.policies } : PolicySet).authorize ι ω σ n).decision? =
      some .allow := by
  obtain ⟨p, pr, rs, r, hσ, ha, hr, hra⟩ := decideWith_decision?_allow h
  have ha' : ({ P with policies := q :: P.policies } : PolicySet).Admits
      ({ P with policies := q :: P.policies } : PolicySet).policies ω p pr rs :=
    PolicySet.Admits.with_iff.mpr (PolicySet.Admits.cons_iff.mpr ⟨ha, hpass p pr rs hσ ha⟩)
  have hA := authorize_of_admits (ι := ι) hσ ha'
  obtain ⟨ι₀, hc₀⟩ := exists_completes ι
  cases hresp :
      ({ P with policies := q :: P.policies } : PolicySet).respond ι ω σ n p.event pr rs with
  | none => exact absurd (by rw [hA, hresp]) hP'
  | some r' =>
    rw [hA, hresp]
    simp only [Outcome.decision?, Option.some.injEq]
    have h₁ := supervaluate_eq_some_iff.mp hresp ι₀ hc₀
    have h₂ := supervaluate_eq_some_iff.mp hr ι₀ hc₀
    rw [← h₁]
    rw [← h₂] at hra
    exact allow_of_add_permit hq hra

/-- **Adding a `permit` keeps an allow exactly when the `permit` passes the checks**, under a total
reading. Adding a `permit` can turn an allow into a deny: a failing provider of the new rule, or a
scope entity its temporal leaves read and the event does not supply, fails the decision closed. -/
theorem authorize_unchanged_allow_when_add_permit_iff (hι : ι.Total) {q : Policy}
    (hq : q.effect = .permit) (h : (P.authorize ι ω σ n).decision? = some .allow) :
    (({ P with policies := q :: P.policies } : PolicySet).authorize ι ω σ n).decision? =
        some .allow ↔
      ∀ p pr rs, σ[n]? = some p → P.Admits P.policies ω p pr rs →
        P.RulePasses q ω p.event pr rs :=
  ⟨rulePasses_of_authorize_add_permit, fun H =>
    authorize_unchanged_allow_when_add_permit hq h H (authorize_ne_temporalError_of_total hι)⟩

/-! ## Deployments -/

private theorem satisfiedWithEffect_mono {θ θ' : Leaves} {q q' : Policy} {req : Request}
    {es : Entities} {eff : Effect} (he : q'.effect = q.effect)
    (hs : satisfied θ' q' req es = true → satisfied θ q req es = true)
    (h : satisfiedWithEffect θ' eff q' req es ≠ none) :
    satisfiedWithEffect θ eff q req es ≠ none := by
  unfold satisfiedWithEffect at h ⊢
  intro h'
  apply h
  split at h'
  · cases h'
  · rename_i hc
    have : ¬ (q'.effect == eff && satisfied θ' q' req es) = true :=
      fun h'' => hc (by
        simp only [Bool.and_eq_true] at h'' ⊢
        exact ⟨he ▸ h''.1, hs h''.2⟩)
    simp only [Bool.eq_false_iff.mpr this, Bool.false_eq_true, ↓reduceIte]

/-- **Of two deployments that differ in a `permit`, the one with the stricter `permit` allows only
what the other allows**, when the `permit`'s monitor starts at the same timepoint `s` in both, the
stricter one is satisfied, at the leaf valuations of the decision, only where the other is, and
the other passes its own checks wherever the stricter does, unless the other's decision fails
closed for a temporal error. This does not compare a deployment with its update under the
prospective reading: there a rule whose content changes gets a new monitor instance
(`Dogwood.Spec.Log.InstancesStable`), which starts at the update. -/
theorem authorizeDeployed_allow_of_replace_permit {q q' : Policy} {s : Nat}
    {rest : List (Policy × Nat)} (hq : q.effect = .permit) (hq' : q'.effect = .permit)
    (hsat : ∀ p pr rs ι', σ[n]? = some p → ι'.Completes ι →
      satisfied (P.leavesFrom ι' ω σ s n p.event) q' (p.event.request pr rs)
        (P.decisionEntities p.event) = true →
      satisfied (P.leavesFrom ι' ω σ s n p.event) q (p.event.request pr rs)
        (P.decisionEntities p.event) = true)
    (hpass : ∀ p pr rs, σ[n]? = some p → P.Admits (q' :: rest.map (·.1)) ω p pr rs →
      P.RulePasses q ω p.event pr rs)
    (hP : P.authorizeDeployed ι ω σ n ((q, s) :: rest) ≠ .failClosed .temporalError)
    (h : (P.authorizeDeployed ι ω σ n ((q', s) :: rest)).decision? = some .allow) :
    (P.authorizeDeployed ι ω σ n ((q, s) :: rest)).decision? = some .allow := by
  unfold PolicySet.authorizeDeployed at h hP ⊢
  obtain ⟨p, pr, rs, r, hσ, ha', hr, hra⟩ := decideWith_decision?_allow h
  simp only [List.map_cons] at ha' hP ⊢
  have ha : P.Admits (q :: rest.map (·.1)) ω p pr rs :=
    PolicySet.Admits.cons_iff.mpr ⟨(PolicySet.Admits.cons_iff.mp ha').1, hpass p pr rs hσ ha'⟩
  rw [decideWith_of_admits hσ ha] at hP ⊢
  obtain ⟨ι₀, hc₀⟩ := exists_completes ι
  split at hP
  · rename_i rP hresp
    simp only [Outcome.decision?, Option.some.injEq]
    have h₁ := supervaluate_eq_some_iff.mp hresp ι₀ hc₀
    have h₂ := supervaluate_eq_some_iff.mp hr ι₀ hc₀
    simp only [List.map_cons] at h₁ h₂
    rw [← h₁]
    rw [← h₂] at hra
    obtain ⟨⟨r', hr', hs⟩, hf⟩ := isAuthorizedEach_allow_iff.mp hra
    refine isAuthorizedEach_allow_iff.mpr ⟨?_, fun r'' hr'' => ?_⟩
    · rcases List.mem_cons.mp hr' with rfl | hr'
      · exact ⟨_, List.mem_cons_self .., satisfiedWithEffect_mono (hq'.trans hq.symm)
          (hsat p pr rs ι₀ hσ hc₀) hs⟩
      · exact ⟨r', List.mem_cons_of_mem _ hr', hs⟩
    · rcases List.mem_cons.mp hr'' with rfl | hr''
      · simp [satisfiedWithEffect, hq]
      · exact hf r'' (List.mem_cons_of_mem _ hr'')
  · exact absurd rfl hP

/-- **Of two deployments that differ in a condition added to a `permit`, the stricter allows only
what the other allows**, when the `permit`'s monitor starts at the same timepoint in both, unless
the other's decision fails closed for a temporal error. -/
theorem authorizeDeployed_allow_of_strengthen_permit {q : Policy} {s : Nat}
    {rest : List (Policy × Nat)} (c : Condition) (hq : q.effect = .permit)
    (hP : P.authorizeDeployed ι ω σ n ((q, s) :: rest) ≠ .failClosed .temporalError)
    (h : (P.authorizeDeployed ι ω σ n ((q.addCondition c, s) :: rest)).decision? = some .allow) :
    (P.authorizeDeployed ι ω σ n ((q, s) :: rest)).decision? = some .allow :=
  authorizeDeployed_allow_of_replace_permit (q' := q.addCondition c) hq hq
    (fun _ _ _ _ _ _ => satisfied_of_addCondition)
    (fun _ _ _ _ ha => rulePasses_of_leaves (q₀ := q.addCondition c) (fun _ _ h => h)
      (fun _ hl => mem_leaves_addCondition.mpr (.inl hl)) (PolicySet.Admits.cons_iff.mp ha).2)
    hP h

/-- **Refinement over a log, under the retrospective reading**: of two logs with the same trace
that decide an event at the same number of events, one with the rules `ps` in force and the other
with `ps'`, the second allows only what the first does, when `ps'` refines `ps` as in
`authorize_allow_of_refines`, unless the first's decision fails closed for a temporal error. -/
theorem decide_retrospective_allow_of_refines {log log' : Log} {i i' : Nat} {p p' : TimePoint}
    {ps ps' : Policies} (hi : log[i]? = some (.event p)) (hi' : log'[i']? = some (.event p'))
    (htrace : log'.trace = log.trace)
    (hevents : (Log.state P (log'.take i')).events = (Log.state P (log.take i)).events)
    (hrules : (Log.state P (log.take i)).rules.map (·.1.policy) = ps)
    (hrules' : (Log.state P (log'.take i')).rules.map (·.1.policy) = ps')
    (hcheck : ∀ p pr rs, log.trace[(Log.state P (log.take i)).events]? = some p →
      P.Admits ps' ω p pr rs → P.Admits ps ω p pr rs)
    (hreq : ∀ p pr rs, log.trace[(Log.state P (log.take i)).events]? = some p →
      P.Admits ps' ω p pr rs → ∀ ι', ι'.Completes ι →
      (isAuthorized (P.leaves ι' ω log.trace (Log.state P (log.take i)).events p.event)
        (p.event.request pr rs) (P.decisionEntities p.event) ps').decision = .allow →
      (isAuthorized (P.leaves ι' ω log.trace (Log.state P (log.take i)).events p.event)
        (p.event.request pr rs) (P.decisionEntities p.event) ps).decision = .allow)
    (hP : Log.decide .retrospective ι P ω log i ≠ .failClosed .temporalError)
    (h : (Log.decide .retrospective ι P ω log' i').decision? = some .allow) :
    (Log.decide .retrospective ι P ω log i).decision? = some .allow := by
  rw [decide_retrospective hi, hrules] at hP ⊢
  rw [decide_retrospective hi', hrules', htrace, hevents] at h
  exact authorize_allow_of_refines (P := { P with policies := ps })
    (fun p pr rs hσ ha => PolicySet.Admits.with_iff.mpr
      (hcheck p pr rs hσ (PolicySet.Admits.with_iff.mp ha)))
    (fun p pr rs hσ ha => hreq p pr rs hσ (PolicySet.Admits.with_iff.mp ha)) hP h

/-- **Under the retrospective reading, strengthening a `permit` never creates an allow**: of two
logs with the same trace that decide an event at the same number of events, one with the rules
`q :: ps` in force and the other with a condition added to the `permit` `q`, the second allows
only what the first does, unless the first's decision fails closed for a temporal error. -/
theorem decide_retrospective_allow_of_strengthen_permit {log log' : Log} {i i' : Nat}
    {p p' : TimePoint} {q : Policy} {ps : Policies} (c : Condition) (hq : q.effect = .permit)
    (hi : log[i]? = some (.event p)) (hi' : log'[i']? = some (.event p'))
    (htrace : log'.trace = log.trace)
    (hevents : (Log.state P (log'.take i')).events = (Log.state P (log.take i)).events)
    (hrules : (Log.state P (log.take i)).rules.map (·.1.policy) = q :: ps)
    (hrules' : (Log.state P (log'.take i')).rules.map (·.1.policy) = q.addCondition c :: ps)
    (hP : Log.decide .retrospective ι P ω log i ≠ .failClosed .temporalError)
    (h : (Log.decide .retrospective ι P ω log' i').decision? = some .allow) :
    (Log.decide .retrospective ι P ω log i).decision? = some .allow := by
  rw [decide_retrospective hi, hrules] at hP ⊢
  rw [decide_retrospective hi', hrules', htrace, hevents] at h
  exact authorize_allow_of_strengthen_permit (P := { P with policies := q :: ps }) c hq rfl hP h

end Dogwood.Thm
