import Dogwood.Thm.TemporalEmbeddingOriginal

/-!
# Hoisting a timepoint-independent condition out of a temporal operator

A condition that does not vary with the timepoint (`Formula.Varies`: no predicate, `tp`,
temporal operator, `exists`, or aggregate) reads only the decision event and the valuation, so it
holds alike at every timepoint (`sat_not_varies`). A Cedar condition written as a leaf is such a
condition (`toTemporal_not_varies`). It comes out of a past operator as a conjunct:

* `formerly within w (φ && c)` holds exactly when `c && formerly within w φ` does
  (`sat_formerly_hoist`);
* likewise `previous` (`sat_previous_hoist`), and the anchor of `since`:
  `φ since within w (ψ && c)` is `c && φ since within w ψ` (`sat_since_anchor_hoist`).

The left side of `since` is the exception (`sat_since_left_hoist`): `(φ && c) since within w ψ`
asks `c` only at the visible timepoints after the anchor, and there may be none. When `ψ` holds
at the decision timepoint itself, the `since` holds whatever `c` and `φ` are
(`sat_since_now`), so it holds where `c && φ since within w ψ` does not
(`since_left_not_hoist`).

In a rule (`authorize_hoist_of_valid`): for a valid policy set, a condition
`when temporal { formerly within w (ψ && c) }`, `c` the translation of a Cedar expression `e`, can
be replaced by `when { e }` and `when temporal { formerly within w ψ }`, with the same outcome
under every reading, given what the embedding itself needs (`authorize_toTemporal_of_valid`): the
decision event supplies the scope entities `c` reads, and Cedar's arithmetic does not overflow.
Likewise `previous` and the anchor of `since` (`Hoists`). Only a `when` condition splits: an
`unless` of a conjunction is not two `unless` conditions.
-/

namespace Dogwood.Thm

open Dogwood.Spec Dogwood.Spec.Temporal

section

variable {ι : ImplChoices} {rate : TickRate} {σ : Trace} {e : Event} {vis : Nat → Prop}

/-- A term that does not vary denotes alike at every timepoint. -/
theorem denotes_not_varies {E : List VarName} {v : Valuation} :
    (t : Term) → ¬ t.Varies E → ∀ j k c,
      Denotes ι rate σ e vis v j t c ↔ Denotes ι rate σ e vis v k t c
  | .agg _, h, _, _, _ => absurd trivial h
  | .arith op l r, h, j, k, c => by
    simp only [Term.Varies, not_or] at h
    simp only [Denotes]
    constructor
    · rintro ⟨m, n, hl, hr, hc⟩
      exact ⟨m, n, (denotes_not_varies l h.1 j k _).mp hl, (denotes_not_varies r h.2 j k _).mp hr,
        hc⟩
    · rintro ⟨m, n, hl, hr, hc⟩
      exact ⟨m, n, (denotes_not_varies l h.1 j k _).mpr hl,
        (denotes_not_varies r h.2 j k _).mpr hr, hc⟩
  | .entity _, _, _, _, _ | .long _, _, _, _, _ | .decimal _, _, _, _, _
  | .string _, _, _, _, _ | .bool _, _, _, _, _ | .context _, _, _, _, _
  | .scope _ _, _, _, _, _ | .var _, _, _, _, _ | .wildcard, _, _, _, _ => by
    simp only [Denotes]

/-- **A condition that does not vary holds alike at every timepoint.** -/
theorem sat_not_varies {E : List VarName} :
    (φ : Formula) → ¬ φ.Varies E → ∀ v j k,
      Sat ι rate σ e vis v j φ ↔ Sat ι rate σ e vis v k φ
  | .cmp op l r, h, v, j, k => by
    simp only [Formula.Varies, not_or] at h
    simp only [Sat]
    constructor
    · rintro ⟨a, b, ha, hb, hab⟩
      exact ⟨a, b, (denotes_not_varies l h.1 j k a).mp ha, (denotes_not_varies r h.2 j k b).mp hb,
        hab⟩
    · rintro ⟨a, b, ha, hb, hab⟩
      exact ⟨a, b, (denotes_not_varies l h.1 j k a).mpr ha,
        (denotes_not_varies r h.2 j k b).mpr hb, hab⟩
  | .not φ, h, v, j, k => by
    simp only [Formula.Varies] at h
    simp only [Sat, sat_not_varies φ h v j k]
  | .and φ ψ, h, v, j, k => by
    simp only [Formula.Varies, not_or] at h
    simp only [Sat, sat_not_varies φ h.1 v j k, sat_not_varies ψ h.2 v j k]
  | .pred .., h, _, _, _ | .tp _, h, _, _, _ | .formerly .., h, _, _, _
  | .previous .., h, _, _, _ | .since .., h, _, _, _ | .exist .., h, _, _, _ =>
    absurd trivial h

variable {E : List VarName} {c : Formula} (hc : ¬ c.Varies E) {v : Valuation} {j : Nat}
  {w : Window}
include hc

/-- **`formerly` hoists a timepoint-independent conjunct.** -/
theorem sat_formerly_hoist (φ : Formula) :
    Sat ι rate σ e vis v j (.formerly w (.and φ c)) ↔
      Sat ι rate σ e vis v j c ∧ Sat ι rate σ e vis v j (.formerly w φ) := by
  simp only [Sat]
  constructor
  · rintro ⟨k, hk, hv, hw, hφ, hck⟩
    exact ⟨(sat_not_varies c hc v k j).mp hck, k, hk, hv, hw, hφ⟩
  · rintro ⟨hcj, k, hk, hv, hw, hφ⟩
    exact ⟨k, hk, hv, hw, hφ, (sat_not_varies c hc v j k).mp hcj⟩

/-- **`previous` hoists a timepoint-independent conjunct.** -/
theorem sat_previous_hoist (φ : Formula) :
    Sat ι rate σ e vis v j (.previous w (.and φ c)) ↔
      Sat ι rate σ e vis v j c ∧ Sat ι rate σ e vis v j (.previous w φ) := by
  simp only [Sat]
  constructor
  · rintro ⟨k, hk, hv, hlast, hw, hφ, hck⟩
    exact ⟨(sat_not_varies c hc v k j).mp hck, k, hk, hv, hlast, hw, hφ⟩
  · rintro ⟨hcj, k, hk, hv, hlast, hw, hφ⟩
    exact ⟨k, hk, hv, hlast, hw, hφ, (sat_not_varies c hc v j k).mp hcj⟩

/-- **`since` hoists a timepoint-independent conjunct of its anchor.** -/
theorem sat_since_anchor_hoist (φ ψ : Formula) :
    Sat ι rate σ e vis v j (.since φ w (.and ψ c)) ↔
      Sat ι rate σ e vis v j c ∧ Sat ι rate σ e vis v j (.since φ w ψ) := by
  simp only [Sat]
  constructor
  · rintro ⟨k, hk, hv, hw, ⟨hψ, hck⟩, hall⟩
    exact ⟨(sat_not_varies c hc v k j).mp hck, k, hk, hv, hw, hψ, hall⟩
  · rintro ⟨hcj, k, hk, hv, hw, hψ, hall⟩
    exact ⟨k, hk, hv, hw, ⟨hψ, (sat_not_varies c hc v j k).mp hcj⟩, hall⟩

/-- **`since` does not hoist a conjunct of its left side**: `(φ && c) since ψ` holds exactly when
`c` and `φ since ψ` do, or when `ψ` held at a visible timepoint in the window with no visible
timepoint after it, through `j`, whatever `c`. -/
theorem sat_since_left_hoist (φ ψ : Formula) :
    Sat ι rate σ e vis v j (.since (.and φ c) w ψ) ↔
      (Sat ι rate σ e vis v j c ∧ Sat ι rate σ e vis v j (.since φ w ψ)) ∨
        ∃ k, k ≤ j ∧ vis k ∧ InWindow rate σ j k w ∧ Sat ι rate σ e vis v k ψ ∧
          ∀ k', k < k' → k' ≤ j → ¬ vis k' := by
  simp only [Sat]
  constructor
  · rintro ⟨k, hk, hv, hw, hψ, hall⟩
    by_cases htail : ∃ k', k < k' ∧ k' ≤ j ∧ vis k'
    · obtain ⟨k', hk', hk'j, hvk'⟩ := htail
      refine .inl ⟨(sat_not_varies c hc v k' j).mp (hall k' hk' hk'j hvk').2, k, hk, hv, hw, hψ,
        fun k'' h₁ h₂ h₃ => (hall k'' h₁ h₂ h₃).1⟩
    · refine .inr ⟨k, hk, hv, hw, hψ, fun k' h₁ h₂ h₃ => htail ⟨k', h₁, h₂, h₃⟩⟩
  · rintro (⟨hcj, k, hk, hv, hw, hψ, hall⟩ | ⟨k, hk, hv, hw, hψ, hnone⟩)
    · exact ⟨k, hk, hv, hw, hψ, fun k' h₁ h₂ h₃ =>
        ⟨hall k' h₁ h₂ h₃, (sat_not_varies c hc v j k').mp hcj⟩⟩
    · exact ⟨k, hk, hv, hw, hψ, fun k' h₁ h₂ h₃ => absurd h₃ (hnone k' h₁ h₂)⟩

omit hc in
/-- **A `since` whose anchor holds now holds**, whatever its left side: there is no timepoint
after the anchor. -/
theorem sat_since_now {p : TimePoint} (hvis : vis j) (hσ : σ[j]? = some p)
    (hw : 0 ≤ w.ticks rate) (φ : Formula) {ψ : Formula} (hψ : Sat ι rate σ e vis v j ψ) :
    Sat ι rate σ e vis v j (.since φ w ψ) :=
  ⟨j, Nat.le_refl j, hvis, ⟨p, p, hσ, hσ, by simp, by simpa using hw⟩, hψ,
    fun _ h₁ h₂ _ => absurd (Nat.lt_of_lt_of_le h₁ h₂) (Nat.lt_irrefl _)⟩

omit hc in
/-- **Hoisting from the left of `since` is unsound**: when the anchor holds now and `c` does not,
`(φ && c) since within w ψ` holds and `c && φ since within w ψ` does not. -/
theorem since_left_not_hoist {p : TimePoint} (hvis : vis j) (hσ : σ[j]? = some p)
    (hw : 0 ≤ w.ticks rate) (φ : Formula) {ψ : Formula} (hψ : Sat ι rate σ e vis v j ψ)
    (hnc : ¬ Sat ι rate σ e vis v j c) :
    Sat ι rate σ e vis v j (.since (.and φ c) w ψ) ∧
      ¬ (Sat ι rate σ e vis v j c ∧ Sat ι rate σ e vis v j (.since φ w ψ)) :=
  ⟨sat_since_now hvis hσ hw _ hψ, fun h => hnc h.1⟩

end

/-! ## Hoisting in a rule -/

section

open Cedar.Spec (Request Entities EntityUID)

variable {θ : Leaves} {req : Request} {es : Entities}

/-- `&&` is associative, errors included. -/
theorem evaluate_and_assoc (a b r : Expr) :
    evaluate θ (.and (.and a b) r) req es = evaluate θ (.and a (.and b r)) req es := by
  simp only [evaluate]
  cases ha : (evaluate θ a req es).as Bool with
  | error e => rfl
  | ok b₁ =>
    cases b₁ with
    | false => rfl
    | true =>
      simp only [Except.bind_ok, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      cases hb : (evaluate θ b req es).as Bool with
      | error e => rfl
      | ok b₂ =>
        cases b₂ with
        | false => rfl
        | true =>
          cases hr : (evaluate θ r req es).as Bool with
          | error e =>
            simp [Cedar.Spec.Result.as, Coe.coe, Cedar.Spec.Value.asBool]
          | ok b₃ =>
            cases b₃ <;>
              simp [Cedar.Spec.Result.as, Coe.coe, Cedar.Spec.Value.asBool]

/-- A condition can be split in two that evaluate, in turn, as it does, where the conditions
before it hold. -/
theorem evaluate_conditions_split {c c₁ c₂ : Condition} {post : Conditions} :
    (pre : Conditions) → ((∀ g ∈ condFacts pre, g.HoldsIn req es) →
      evaluate θ c.toExpr req es = evaluate θ (.and c₁.toExpr c₂.toExpr) req es) →
    evaluate θ (Conditions.toExpr (pre ++ c :: post)) req es =
      evaluate θ (Conditions.toExpr (pre ++ c₁ :: c₂ :: post)) req es
  | [], h => by
    have h' := h (by simp [condFacts])
    cases post with
    | nil => exact h'
    | cons d ds =>
      simp only [List.nil_append]
      rw [conditions_toExpr_cons c (d :: ds) (by simp),
        conditions_toExpr_cons c₁ (c₂ :: d :: ds) (by simp),
        conditions_toExpr_cons c₂ (d :: ds) (by simp), ← evaluate_and_assoc]
      simp only [evaluate, h']
  | d :: pre, h => by
    simp only [List.cons_append]
    rw [conditions_toExpr_cons _ _ (by simp), conditions_toExpr_cons _ _ (by simp)]
    refine evaluate_and_congr_right fun hd => evaluate_conditions_split pre fun hF => h ?_
    intro g hg
    simp only [condFacts, List.flatMap_cons, List.mem_append] at hg
    rcases hg with hg | hg
    · exact facts_hold _ hd g hg
    · exact hF g (by simpa [condFacts] using hg)

/-- **A rule's condition can be split in two** that evaluate, in turn, as it does, where the
rule's scope holds and the conditions before it hold. -/
theorem evaluate_withCondition_split {q : Policy} {pre post : Conditions} {c c₁ c₂ : Condition}
    (h : q.ScopeHolds req es → (∀ g ∈ condFacts pre, g.HoldsIn req es) →
      evaluate θ c.toExpr req es = evaluate θ (.and c₁.toExpr c₂.toExpr) req es) :
    evaluate θ (q.withCondition pre c post).toExpr req es =
      evaluate θ (q.withCondition pre c₁ (c₂ :: post)).toExpr req es := by
  simp only [Policy.withCondition, Policy.toExpr]
  refine evaluate_and_congr_right fun h₁ => evaluate_and_congr_right fun h₂ =>
    evaluate_and_congr_right fun h₃ => evaluate_conditions_split pre (h ?_)
  rw [evaluate_ofCedar] at h₁ h₂ h₃
  exact ⟨h₁, h₂, h₃⟩

end

section

open Cedar.Spec (Request Entities EntityUID)

variable {ι : ImplChoices} {P : PolicySet} {ω : Provider.Providers} {σ : Trace} {n : Nat}

/-- **The leaf `F₁` hoists `c`, leaving `F₂`**: after pin injection, `F₁` holds exactly when `c`
and `F₂` do, it reads the scope entities `F₂` and `c` read, and typing it types `c`. -/
structure Hoists (S : EventSchema) (c F₁ F₂ : Formula) : Prop where
  sat : ∀ (ι : ImplChoices) rate σ e vis v j, Sat ι rate σ e vis v j (F₁.injectPins S) ↔
    Sat ι rate σ e vis v j c ∧ Sat ι rate σ e vis v j (F₂.injectPins S)
  reads : (F₁.injectPins S).scopeReads = (F₂.injectPins S).scopeReads ++ c.scopeReads
  typed : ∀ C, F₁.WellTyped C [] → c.WellTyped C []

/-- `formerly within w (ψ && c)` hoists a translation `c`, leaving `formerly within w ψ`. -/
theorem hoists_formerly {S : EventSchema} {e : Cedar.Spec.Expr} {c : Formula}
    (hφ : toTemporal e = some c) (w : Window) (ψ : Formula) :
    Hoists S c (.formerly w (.and ψ c)) (.formerly w ψ) where
  sat _ _ _ _ _ _ _ := by
    simp only [Formula.injectPins, toTemporal_injectPins e c hφ]
    exact sat_formerly_hoist (toTemporal_not_varies (E := []) e c hφ) _
  reads := by simp [Formula.injectPins, toTemporal_injectPins e c hφ, Formula.scopeReads]
  typed _ h := by
    cases h with
    | formerly _ h => cases h with
      | and _ h => exact h

/-- `previous within w (ψ && c)` hoists a translation `c`, leaving `previous within w ψ`. -/
theorem hoists_previous {S : EventSchema} {e : Cedar.Spec.Expr} {c : Formula}
    (hφ : toTemporal e = some c) (w : Window) (ψ : Formula) :
    Hoists S c (.previous w (.and ψ c)) (.previous w ψ) where
  sat _ _ _ _ _ _ _ := by
    simp only [Formula.injectPins, toTemporal_injectPins e c hφ]
    exact sat_previous_hoist (toTemporal_not_varies (E := []) e c hφ) _
  reads := by simp [Formula.injectPins, toTemporal_injectPins e c hφ, Formula.scopeReads]
  typed _ h := by
    cases h with
    | previous _ h => cases h with
      | and _ h => exact h

/-- `φ since within w (ψ && c)` hoists a translation `c`, leaving `φ since within w ψ`. -/
theorem hoists_since_anchor {S : EventSchema} {e : Cedar.Spec.Expr} {c : Formula}
    (hφ : toTemporal e = some c) (φ : Formula) (w : Window) (ψ : Formula) :
    Hoists S c (.since φ w (.and ψ c)) (.since φ w ψ) where
  sat _ _ _ _ _ _ _ := by
    simp only [Formula.injectPins, toTemporal_injectPins e c hφ]
    exact sat_since_anchor_hoist (toTemporal_not_varies (E := []) e c hφ) _ _
  reads := by simp [Formula.injectPins, toTemporal_injectPins e c hφ, Formula.scopeReads]
  typed _ h := by
    cases h with
    | since _ _ h => cases h with
      | and _ h => exact h

/-- **The value of a leaf that hoists a translation `c` is the value of `c` and of what it
leaves.** -/
theorem leaves_hoist {p : TimePoint} (hp : σ[n]? = some p) {e : Cedar.Spec.Expr} {c F₁ F₂ : Formula}
    (hφ : toTemporal e = some c) (hh : Hoists P.schema c F₁ F₂) :
    (P.leaves ι ω σ n p.event).temporal F₁ =
      ((P.leaves ι ω σ n p.event).temporal c && (P.leaves ι ω σ n p.event).temporal F₂) := by
  have hinj := toTemporal_injectPins (S := P.schema) e c hφ
  have key : P.LeafHolds ι σ n F₁ ↔ P.LeafHolds ι σ n c ∧ P.LeafHolds ι σ n F₂ := by
    simp only [PolicySet.LeafHolds, hp, Option.some.injEq, exists_eq_left', hinj]
    exact hh.sat _ _ _ _ _ _ _
  simp only [PolicySet.leaves]
  rw [Bool.eq_iff_iff, Bool.and_eq_true]
  simp only [decide_eq_true_eq]
  exact key

/-- The leaves of a rule with the condition `ofCedar e` then `temporal { φ }` in place of one
condition `temporal { φ' }`. -/
theorem mem_leaves_split {q : Policy} {pre post : Conditions} {e : Cedar.Spec.Expr}
    {φ : Formula} {l : Leaf} :
    l ∈ (q.withCondition pre ⟨.when, Expr.ofCedar e⟩
        (⟨.when, .temporal φ⟩ :: post)).toExpr.leaves ↔
      (∃ d ∈ pre ++ post, l ∈ d.toExpr.leaves) ∨ l = .inl φ := by
  have h₀ : (Condition.toExpr ⟨.when, Expr.ofCedar e⟩).leaves = [] := by
    simp [Condition.toExpr, leaves_ofCedar]
  have h₁ : (Condition.toExpr ⟨.when, .temporal φ⟩).leaves = [.inl φ] := by
    simp [Condition.toExpr, Expr.leaves]
  simp only [mem_leaves_toExpr, Policy.withCondition, List.mem_append, List.mem_cons]
  constructor
  · rintro ⟨d, hd | rfl | rfl | hd, hl⟩
    · exact .inl ⟨d, .inl hd, hl⟩
    · rw [h₀] at hl; cases hl
    · rw [h₁] at hl; exact .inr (List.mem_singleton.mp hl)
    · exact .inl ⟨d, .inr hd, hl⟩
  · rintro (⟨d, hd | hd, hl⟩ | rfl)
    · exact ⟨d, .inl hd, hl⟩
    · exact ⟨d, .inr (.inr (.inr hd)), hl⟩
    · exact ⟨_, .inr (.inr (.inl rfl)), by rw [h₁]; simp⟩

theorem mem_leaves_one {q : Policy} {pre post : Conditions} {φ : Formula} {l : Leaf} :
    l ∈ (q.withCondition pre ⟨.when, .temporal φ⟩ post).toExpr.leaves ↔
      (∃ d ∈ pre ++ post, l ∈ d.toExpr.leaves) ∨ l = .inl φ := by
  have h₁ : (Condition.toExpr ⟨.when, .temporal φ⟩).leaves = [.inl φ] := by
    simp [Condition.toExpr, Expr.leaves]
  simp only [mem_leaves_toExpr, Policy.withCondition, List.mem_append, List.mem_cons]
  constructor
  · rintro ⟨d, hd | rfl | hd, hl⟩
    · exact .inl ⟨d, .inl hd, hl⟩
    · rw [h₁] at hl; exact .inr (List.mem_singleton.mp hl)
    · exact .inl ⟨d, .inr hd, hl⟩
  · rintro (⟨d, hd | hd, hl⟩ | rfl)
    · exact ⟨d, .inl hd, hl⟩
    · exact ⟨d, .inr (.inr hd), hl⟩
    · exact ⟨_, .inr (.inl rfl), by rw [h₁]; simp⟩

theorem calls_mem_iff_hoist {qs₁ qs₂ : Policies} {q : Policy} {pre post : Conditions}
    {e : Cedar.Spec.Expr} {φ φ' : Formula} (c : Provider.Call) :
    c ∈ Policies.providerCalls (qs₁ ++ q.withCondition pre ⟨.when, Expr.ofCedar e⟩
        (⟨.when, .temporal φ⟩ :: post) :: qs₂) ↔
      c ∈ Policies.providerCalls
        (qs₁ ++ q.withCondition pre ⟨.when, .temporal φ'⟩ post :: qs₂) := by
  rw [mem_providerCalls', mem_providerCalls']
  simp only [List.mem_append, List.mem_cons]
  constructor
  · rintro ⟨p, hp | rfl | hp, hl⟩
    · exact ⟨p, .inl hp, hl⟩
    · rcases (mem_leaves_split (φ := φ)).mp hl with h | h
      · exact ⟨_, .inr (.inl rfl), (mem_leaves_one (φ := φ')).mpr (.inl h)⟩
      · cases h
    · exact ⟨p, .inr (.inr hp), hl⟩
  · rintro ⟨p, hp | rfl | hp, hl⟩
    · exact ⟨p, .inl hp, hl⟩
    · rcases (mem_leaves_one (φ := φ')).mp hl with h | h
      · exact ⟨_, .inr (.inl rfl), (mem_leaves_split (φ := φ)).mpr (.inl h)⟩
      · cases h
    · exact ⟨p, .inr (.inr hp), hl⟩

/-- **Hoisting a Cedar condition out of a leaf changes no decision.** Replacing a rule's
condition `when temporal { F₁ }`, where `F₁` hoists `c`, the translation of the Cedar expression
`e`, leaving `F₂` (`Hoists`: `formerly within w (ψ && c)` leaving `formerly within w ψ`, and
likewise `previous` and the anchor of `since`), by the two conditions `when { e }` and
`when temporal { F₂ }` gives the same outcome at a timepoint of a trace, under every reading,
where every admitted decision event at which the condition is evaluated (the rule's scope holds,
and the facts of the conditions before it) evaluates `e` to a `Bool` within the temporal
sub-language (`Fits`), and where the decision event supplies the scope entities whose attributes
`c` reads when the rule's scope holds. -/
theorem authorize_hoist {qs₁ qs₂ : Policies} {q : Policy} {pre post : Conditions}
    {e : Cedar.Spec.Expr} {c F₁ F₂ : Formula}
    (hφ : toTemporal e = some c) (hh : Hoists P.schema c F₁ F₂)
    (hps : P.policies = qs₁ ++ q.withCondition pre ⟨.when, .temporal F₁⟩
      post :: qs₂)
    (hsup : ∀ p pr rs, σ[n]? = some p → p.event.principal = some pr →
      p.event.resource = some rs →
      q.ScopeHolds (p.event.request pr rs) (P.decisionEntities p.event) →
      ∀ r ∈ c.scopeReads, p.event.supplies r = true)
    (hok : ∀ p pr rs, σ[n]? = some p → P.Admits P.policies ω p pr rs →
      q.ScopeHolds (p.event.request pr rs) (P.decisionEntities p.event) →
      (∀ g ∈ condFacts pre, g.HoldsIn (p.event.request pr rs) (P.decisionEntities p.event)) →
      Fits (p.event.request pr rs) (P.decisionEntities p.event) e ∧
        ∃ b, Cedar.Spec.evaluate e (p.event.request pr rs) (P.decisionEntities p.event) =
          .ok (.prim (.bool b))) :
    ({ P with policies := (qs₁ ++ q.withCondition pre ⟨.when, Expr.ofCedar e⟩
        (⟨.when, .temporal F₂⟩ :: post) :: qs₂) } : PolicySet).authorize ι ω σ n =
      P.authorize ι ω σ n := by
  have hinj := toTemporal_injectPins (S := P.schema) e c hφ
  unfold PolicySet.authorize
  show P.decideWith (qs₁ ++ q.withCondition pre ⟨.when, Expr.ofCedar e⟩
      (⟨.when, .temporal F₂⟩ :: post) :: qs₂) ω σ n _ =
    P.decideWith P.policies ω σ n _
  rw [hps]
  rw [decideWith_rules_congr_at
    (rules₂ := qs₁ ++ q.withCondition pre ⟨.when, .temporal F₁⟩ post :: qs₂)
    (fun ev => ?_) (fun ev => ?_) (fun p pr rs hσ hpr hrs => ?_)]
  · refine decideWith_congr rfl fun p pr rs hσ ha => ?_
    simp only [PolicySet.respond]
    refine supervaluate_congr fun ι' _ => ?_
    have hL : ∀ X, ({ P with policies := X } : PolicySet).leaves ι' ω σ n p.event =
        P.leaves ι' ω σ n p.event := fun _ => rfl
    have hD : ∀ X, ({ P with policies := X } : PolicySet).decisionEntities p.event =
        P.decisionEntities p.event := fun _ => rfl
    rw [hL, hD, hps]
    apply isAuthorized_congr_evaluate
    refine forall₂_append' ?_ (.cons ?_ ?_)
    · exact forall₂_refl' (fun _ => ⟨rfl, rfl, rfl⟩) _
    rotate_left
    · exact forall₂_refl' (fun _ => ⟨rfl, rfl, rfl⟩) _
    refine ⟨rfl, rfl, (evaluate_withCondition_split fun hs hpre => ?_).symm⟩
    obtain ⟨hfit, b, he⟩ := hok p pr rs hσ (hps ▸ ha) hs hpre
    have hb := leaves_toTemporal (ι := ι') (P := P) (ω := ω) hσ ha.principal ha.resource hφ hfit he
    simp only [Condition.toExpr]
    simp only [evaluate, evaluate_ofCedar, leaves_hoist hσ hφ hh, hb, he]
    cases b <;> simp [Cedar.Spec.Result.as, Coe.coe, Cedar.Spec.Value.asBool]
  · unfold Policies.providersFail
    exact any_congr_mem _ (calls_mem_iff_hoist (e := e))
  · unfold PolicySet.providerOutputsConform
    exact all_congr_mem _ (calls_mem_iff_hoist (e := e))
  · simp only [PolicySet.scopeEntitiesSupplied, List.all_append, List.all_cons]
    congr 2
    have hscope : (q.withCondition pre ⟨.when, Expr.ofCedar e⟩
          (⟨.when, .temporal F₂⟩ :: post)).scopeHolds =
        (q.withCondition pre ⟨.when, .temporal F₁⟩ post).scopeHolds := rfl
    rw [hscope]
    cases hsh : (q.withCondition pre ⟨.when, .temporal F₁⟩ post).scopeHolds
      (p.event.request pr rs) (P.decisionEntities p.event) with
    | false => rfl
    | true =>
      simp only [Bool.not_true, Bool.false_or]
      have hc : c.scopeReads.all p.event.supplies = true := by
        rw [List.all_eq_true]
        exact hsup p pr rs hσ hpr hrs (scopeHolds_iff.mp hsh)
      rw [Bool.eq_iff_iff, List.all_eq_true, List.all_eq_true]
      constructor
      · intro h l hl
        rcases mem_leaves_one.mp hl with hl | rfl
        · exact h l (mem_leaves_split.mpr (.inl hl))
        · have := h _ (mem_leaves_split.mpr (.inr rfl))
          simp only [hh.reads, List.all_append, Bool.and_eq_true] at this ⊢
          exact ⟨this, hc⟩
      · intro h l hl
        rcases mem_leaves_split.mp hl with hl | rfl
        · exact h l (mem_leaves_one.mpr (.inl hl))
        · have := h _ (mem_leaves_one.mpr (.inr rfl))
          simp only [hh.reads, List.all_append, Bool.and_eq_true] at this ⊢
          exact this.1

/-- **For a valid policy set, hoisting a Cedar condition out of a leaf changes no decision.**
For a valid policy set with a rule's condition `when temporal { F₁ }`, where `F₁` hoists `c`, the
translation of the Cedar expression `e`, leaving `F₂` (`hoists_formerly`, `hoists_previous`,
`hoists_since_anchor`), replacing it by `when { e }` and `when temporal { F₂ }` gives the same
outcome at a timepoint of a trace, under every reading, where the decision event supplies the
scope entities whose attributes `c` reads when the rule's scope holds, and where Cedar's
arithmetic does not overflow. Validity types `c`
at the leaf's position, which is what makes Cedar evaluate `e` to a `Bool` that fits there
(`fits_of_wellTyped`). -/
theorem authorize_hoist_of_valid {qs₁ qs₂ : Policies} {q : Policy}
    {pre post : Conditions} {e : Cedar.Spec.Expr} {c F₁ F₂ : Formula}
    (hφ : toTemporal e = some c) (hh : Hoists P.schema c F₁ F₂)
    (hps : P.policies = qs₁ ++ q.withCondition pre ⟨.when, .temporal F₁⟩
      post :: qs₂)
    (hv : P.Valid)
    (hsup : ∀ p pr rs, σ[n]? = some p → p.event.principal = some pr →
      p.event.resource = some rs →
      q.ScopeHolds (p.event.request pr rs) (P.decisionEntities p.event) →
      ∀ r ∈ c.scopeReads, p.event.supplies r = true)
    (hnov : ∀ p pr rs, σ[n]? = some p → P.Admits P.policies ω p pr rs →
      q.ScopeHolds (p.event.request pr rs) (P.decisionEntities p.event) →
      (∀ g ∈ condFacts pre, g.HoldsIn (p.event.request pr rs) (P.decisionEntities p.event)) →
      Cedar.Spec.evaluate e (p.event.request pr rs) (P.decisionEntities p.event) ≠
        .error .arithBoundsError) :
    ({ P with policies := (qs₁ ++ q.withCondition pre ⟨.when, Expr.ofCedar e⟩
        (⟨.when, .temporal F₂⟩ :: post) :: qs₂) } : PolicySet).authorize ι ω σ n =
      P.authorize ι ω σ n := by
  have hq'mem : q.withCondition pre ⟨.when, .temporal F₁⟩ post ∈
      P.policies := by rw [hps]; simp
  refine authorize_hoist hφ hh hps hsup fun p pr rs hσ ha hs hpre => ?_
  obtain ⟨env, henv, hreq⟩ := request_instance ha.request
  have henvq : env ∈ P.envsOf q :=
    admits_of_scopeHolds (q := q) henv hreq (instanceOfSchema_of_admits ha henv) hs
  obtain ⟨F, hmem, hF⟩ := mem_leafFacts_withCondition (q := q) (pre := pre) (post := post)
    (k := .when) (φ := F₁)
  have hfacts : ∀ g ∈ F, g.Holds p.event := fun g hg =>
    holds_of_holdsIn (P := P) ha.principal ha.resource (by
      rcases hF g hg with hg | hg
      · exact scopeFacts_hold (P.leaves ι ω σ n p.event) hs g hg
      · exact hpre g hg)
  have hsupp : ∀ r ∈ c.scopeReads, p.event.Supplies env r := fun r hr =>
    supplies_of_admits hv ha henv (hsup p pr rs hσ ha.principal ha.resource hs r hr)
  have hc := hh.typed _ ((hv.temporal _ hq'mem _ F hmem).wellTyped env henvq)
  obtain ⟨hfit, hb⟩ := fits_of_wellTyped (C := P.typingCtx env F)
    (req := p.event.request pr rs) (es := P.decisionEntities p.event) rfl ha.principal
    ha.resource (instanceOf_of_admits ha hreq) hfacts
    (storeReads_decisionEntities hv henv p.event) e c hφ hc hsupp
  rcases hb with hb | hb
  · exact ⟨hfit, hb⟩
  · exact absurd hb (hnov p pr rs hσ ha hs hpre)

end

end Dogwood.Thm
