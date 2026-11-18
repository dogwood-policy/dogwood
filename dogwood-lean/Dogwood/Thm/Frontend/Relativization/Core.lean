import Dogwood.Thm.Frontend.Relativization.Encodings
import Dogwood.Thm.Frontend.Relativization.Mine

/-!
# The rewrite with every timepoint visible is the leaf with the key's timepoints visible

`rsat_relCond`: on a trace whose timestamps never decrease, and which is not longer than the
largest `Long`, the relativization rewrite of a condition (`LeafPasses.relCond`), read under
`RSat` with every timepoint visible, holds exactly when the condition does with the visible
timepoints of the specification (`EventSchema.Visible`), under every valuation. It assumes that μ
holds exactly at the visible timepoints (`xsat_mu_iff_visible`), that the condition projects to a
formula whose predicates are pinned (`Formula.Pinned`), and that it uses no fresh name.

The induction is on the condition. Its cases:

* a guarded body (`formerly`, the anchor of `since`) holds at the visible timepoints at which the
  body holds: the guard μ is visibility, and a body that implies mine holds only at visible
  timepoints (`rsat_guard`);
* `previous` and the general `since`: their encodings (`rsat_encodePrevious`,
  `rsat_encodeSince`) quantify over the visible timepoints *in the window*, and the
  specification over all visible ones. On a trace whose timestamps never decrease, every
  timepoint between a timepoint in the window and the window's end is in the window
  (`inWindow_between`), so the two agree;
* the negated-left idiom `!x since a` with an `x` that implies mine: `x` fails at every
  timepoint that is not visible, so `!x` holds there, and the native `since` over every timepoint
  is the specification's over the visible ones;
* every other form is rewritten pointwise, and a predicate, a term and `tp` do not consult
  visibility.
-/

namespace Dogwood.Thm.Frontend

open Dogwood.Frontend Dogwood.Frontend.LeafPasses Surface.Temporal
open Dogwood.Spec (Event Trace TickRate EventSchema)
open Dogwood.Spec.Temporal (Valuation ImplChoices CVal TVal Formula Aggregate InWindow Window)

/-! ## The rewrite's steps -/

theorem run_relKind_previous (pre : String) (μ : Span → Condition) (sp : Span) (w : WithinSpec)
    (c : Condition) (n : Nat) :
    ((relKind pre μ sp (.previous w c)).run n).1 =
      encodePrevious μ sp w (guardMine μ ((relCond pre μ c).run n).1)
        (freshName pre "ti" ((relCond pre μ c).run n).2)
        (freshName pre "tj" (((relCond pre μ c).run n).2 + 1))
        (freshName pre "tk" (((relCond pre μ c).run n).2 + 2)) := by
  have : ((relKind pre μ sp (.previous w c)).run n).1 =
      encodePrevious μ sp w (guardMine μ ((relCond pre μ c).run n).1)
        ((fresh pre "ti").run ((relCond pre μ c).run n).2).1
        ((fresh pre "tj").run ((fresh pre "ti").run ((relCond pre μ c).run n).2).2).1
        ((fresh pre "tk").run ((fresh pre "tj").run ((fresh pre "ti").run
          ((relCond pre μ c).run n).2).2).2).1 := rfl
  rw [this, fresh_run, fresh_run, fresh_run]

theorem run_relSinceGeneral (pre : String) (μ : Span → Condition) (sp : Span)
    (left' : StateM Nat Condition) (w : WithinSpec) (a : Condition) (n : Nat) :
    ((relSinceGeneral pre μ sp left' w a).run n).1 = encodeSince μ sp (left'.run n).1 w a
      (freshName pre "ti" (left'.run n).2) (freshName pre "tj" ((left'.run n).2 + 1))
      (freshName pre "tk_all" ((left'.run n).2 + 2)) (freshName pre "tk_left" ((left'.run n).2 + 3))
      (freshName pre "n" ((left'.run n).2 + 4)) (freshName pre "n" ((left'.run n).2 + 5)) := by
  have : ((relSinceGeneral pre μ sp left' w a).run n).1 = encodeSince μ sp (left'.run n).1 w a
      ((fresh pre "ti").run (left'.run n).2).1
      ((fresh pre "tj").run ((fresh pre "ti").run (left'.run n).2).2).1
      ((fresh pre "tk_all").run ((fresh pre "tj").run ((fresh pre "ti").run
        (left'.run n).2).2).2).1
      ((fresh pre "tk_left").run ((fresh pre "tk_all").run ((fresh pre "tj").run
        ((fresh pre "ti").run (left'.run n).2).2).2).2).1
      ((fresh pre "n").run ((fresh pre "tk_left").run ((fresh pre "tk_all").run
        ((fresh pre "tj").run ((fresh pre "ti").run (left'.run n).2).2).2).2).2).1
      ((fresh pre "n").run ((fresh pre "n").run ((fresh pre "tk_left").run
        ((fresh pre "tk_all").run ((fresh pre "tj").run ((fresh pre "ti").run
          (left'.run n).2).2).2).2).2).2).1 := rfl
  simp only [this, fresh_run]

/-- The rewrite of `l since a` when `l` is not a negation: the general encoding. -/
theorem relKind_since_general (pre : String) (μ : Span → Condition) (sp : Span) (l : Condition)
    (w : WithinSpec) (r : Condition) (h : ∀ lsp x, l ≠ ⟨lsp, .not x⟩) :
    relKind pre μ sp (.since l w r) = (do
      let a ← relCond pre μ r
      relSinceGeneral pre μ sp (relCond pre μ l) w (guardMine μ a)) := by
  rcases l with ⟨lsp, lk⟩
  cases lk <;> first | rfl | exact absurd rfl (h _ _)

/-- The rewrite of `!x since a`: the native `since` when `x` implies mine, the general encoding
otherwise. -/
theorem relKind_since_not (pre : String) (μ : Span → Condition) (sp lsp : Span) (x : Condition)
    (w : WithinSpec) (r : Condition) :
    relKind pre μ sp (.since ⟨lsp, .not x⟩ w r) = (do
      let a ← relCond pre μ r
      let a := guardMine μ a
      if impliesMine x then (do let x' ← relCond pre μ x; return ⟨sp, .since (mkNot sp x') w a⟩)
      else relSinceGeneral pre μ sp (relCond pre μ ⟨lsp, .not x⟩) w a) := rfl

/-! ## Distinct fresh names -/

theorem freshName_ti_tj {pre : String} (a b : Nat) : freshName pre "ti" a ≠ freshName pre "tj" b :=
  freshName_ne_of_get 1 (by decide) (by decide) (by decide) a b
theorem freshName_ti_tk {pre : String} (a b : Nat) : freshName pre "ti" a ≠ freshName pre "tk" b :=
  freshName_ne_of_get 1 (by decide) (by decide) (by decide) a b
theorem freshName_tj_tk {pre : String} (a b : Nat) : freshName pre "tj" a ≠ freshName pre "tk" b :=
  freshName_ne_of_get 1 (by decide) (by decide) (by decide) a b
theorem freshName_ti_n {pre : String} (a b : Nat) : freshName pre "ti" a ≠ freshName pre "n" b :=
  freshName_ne_of_get 0 (by decide) (by decide) (by decide) a b
theorem freshName_tj_n {pre : String} (a b : Nat) : freshName pre "tj" a ≠ freshName pre "n" b :=
  freshName_ne_of_get 0 (by decide) (by decide) (by decide) a b
theorem freshName_tkAll_ti {pre : String} (a b : Nat) :
    freshName pre "tk_all" a ≠ freshName pre "ti" b :=
  freshName_ne_of_get 1 (by decide) (by decide) (by decide) a b
theorem freshName_tkAll_tj {pre : String} (a b : Nat) :
    freshName pre "tk_all" a ≠ freshName pre "tj" b :=
  freshName_ne_of_get 1 (by decide) (by decide) (by decide) a b
theorem freshName_tkLeft_ti {pre : String} (a b : Nat) :
    freshName pre "tk_left" a ≠ freshName pre "ti" b :=
  freshName_ne_of_get 1 (by decide) (by decide) (by decide) a b
theorem freshName_tkLeft_tj {pre : String} (a b : Nat) :
    freshName pre "tk_left" a ≠ freshName pre "tj" b :=
  freshName_ne_of_get 1 (by decide) (by decide) (by decide) a b
theorem freshName_n_succ {pre : String} (a : Nat) :
    freshName pre "n" (a + 4) ≠ freshName pre "n" (a + 5) := fun h => by
  have := freshName_inj h; omega

/-! ## Names of subconditions -/

theorem noFresh_left {pre : String} {sp : Span} {k : ConditionKind} {l : Condition}
    (hsub : ∀ x, x ∈ condNames l → x ∈ kindNames k) (h : NoFreshNames pre ⟨sp, k⟩) :
    NoFreshNames pre l :=
  fun x hx => h x (hsub x hx)

section
variable {ι : ImplChoices} {rate : TickRate} {σ : Trace} {e : Event} {S : EventSchema}
  {μ : Span → Condition} {pre : String}

/-- **A guarded body holds at the visible timepoints at which the body holds.** -/
theorem rsat_guard (hμ : ∀ sp v k, RSat ι rate σ e (fun _ => True) v k (μ sp) ↔ S.Visible σ e k)
    {b c : Condition} {ψ : Formula} (hc : c.toFormula = .ok ψ) (hp : ψ.Pinned S)
    (hnf : NoFreshNames pre c) (himp : impliesMine b = impliesMine c)
    (hIH : ∀ v k, RSat ι rate σ e (fun _ => True) v k b ↔ RSat ι rate σ e (S.Visible σ e) v k c)
    (v : Valuation) :
    ∀ v' k, AgreeOff pre v v' → (RSat ι rate σ e (fun _ => True) v' k (guardMine μ b) ↔
      S.Visible σ e k ∧ RSat ι rate σ e (S.Visible σ e) v k c) := by
  intro v' k hA
  refine (xsat_guardMine (ord := true) (dom := anyValue) μ b v' k).trans ?_
  have e₁ : XSat ι rate σ e (fun _ => True) true anyValue v' k b ↔
      RSat ι rate σ e (S.Visible σ e) v k c := (hIH v' k).trans (xsat_congr_fresh hnf hA k)
  have e₂ : XSat ι rate σ e (fun _ => True) true anyValue v' k (μ b.span) ↔ S.Visible σ e k :=
    hμ _ v' k
  rw [e₁, e₂, himp]
  cases hm : impliesMine c
  · simp
  · simp only [reduceCtorEq, false_implies, true_and]
    exact ⟨fun h => ⟨xsat_visible hm hc hp h, h⟩, fun h => h.2⟩

/-- The `since` of the specification, unfolded: the visible anchor in the window, and the left at
every visible timepoint after it. -/
theorem rsat_since_iff {vis : Nat → Prop} {sp : Span} {l r : Condition} {w : WithinSpec} {win : Window}
    (hw : w.toSpec = .ok win) (v : Valuation) (j : Nat) :
    RSat ι rate σ e vis v j ⟨sp, .since l w r⟩ ↔
      ∃ k, k ≤ j ∧ vis k ∧ InWindow rate σ j k win ∧ RSat ι rate σ e vis v k r ∧
        ∀ k', k < k' → k' ≤ j → vis k' → RSat ι rate σ e vis v k' l := by
  simp [XSat, hw]

/-- **The `since` case.** -/
theorem rsat_since_case (hμ : ∀ sp v k, RSat ι rate σ e (fun _ => True) v k (μ sp) ↔ S.Visible σ e k)
    (hσ : σ.Nondecreasing) (hlen : (σ.length : Int) ≤ Int64.MAX)
    {sp : Span} {l r : Condition} {w : WithinSpec} {ψl ψr : Formula} {win : Window}
    (hl : l.toFormula = .ok ψl) (hw : w.toSpec = .ok win) (hr : r.toFormula = .ok ψr)
    (hpl : ψl.Pinned S) (hpr : ψr.Pinned S) (hnfl : NoFreshNames pre l) (hnfr : NoFreshNames pre r)
    (IHl : ∀ n v j, RSat ι rate σ e (fun _ => True) v j ((relCond pre μ l).run n).1 ↔
      RSat ι rate σ e (S.Visible σ e) v j l)
    (IHr : ∀ n v j, RSat ι rate σ e (fun _ => True) v j ((relCond pre μ r).run n).1 ↔
      RSat ι rate σ e (S.Visible σ e) v j r) (n : Nat) (v : Valuation) (j : Nat) :
    RSat ι rate σ e (fun _ => True) v j ((relKind pre μ sp (.since l w r)).run n).1 ↔
      RSat ι rate σ e (S.Visible σ e) v j ⟨sp, .since l w r⟩ := by
  have hguard := rsat_guard hμ hr hpr hnfr (impliesMine_relCond pre μ r n) (IHr n) v
  have general : RSat ι rate σ e (fun _ => True) v j ((relSinceGeneral pre μ sp (relCond pre μ l) w
      (guardMine μ ((relCond pre μ r).run n).1)).run ((relCond pre μ r).run n).2).1 ↔
      RSat ι rate σ e (S.Visible σ e) v j ⟨sp, .since l w r⟩ := by
    rw [run_relSinceGeneral]
    have hl' : ∀ v' k, AgreeOff pre v v' → (RSat ι rate σ e (fun _ => True) v' k
        ((relCond pre μ l).run ((relCond pre μ r).run n).2).1 ↔ RSat ι rate σ e (S.Visible σ e) v k l) :=
      fun v' k hA => (IHl _ v' k).trans (xsat_congr_fresh hnfl hA k)
    rw [rsat_encodeSince hμ hw (startsWith_freshName _ _ _) (startsWith_freshName _ _ _)
      (startsWith_freshName _ _ _) (startsWith_freshName _ _ _) (startsWith_freshName _ _ _)
      (startsWith_freshName _ _ _) (freshName_ti_tj _ _) (freshName_ti_n _ _) (freshName_ti_n _ _)
      (freshName_tj_n _ _) (freshName_tj_n _ _) (freshName_n_succ _) (freshName_tkAll_ti _ _)
      (freshName_tkAll_tj _ _) (freshName_tkLeft_ti _ _) (freshName_tkLeft_tj _ _) hlen hguard hl' j,
      rsat_since_iff hw]
    constructor
    · rintro ⟨k, hkj, hiw, ⟨hvk, hrk⟩, hall⟩
      exact ⟨k, hkj, hvk, hiw, hrk, fun k' h₁ h₂ h₃ =>
        hall k' h₁ h₂ (inWindow_between hσ hiw (Nat.le_of_lt h₁) h₂) h₃⟩
    · rintro ⟨k, hkj, hvk, hiw, hrk, hall⟩
      exact ⟨k, hkj, hiw, ⟨hvk, hrk⟩, fun m h₁ h₂ _ h₄ => hall m h₁ h₂ h₄⟩
  by_cases hnot : ∃ lsp x, l = ⟨lsp, .not x⟩
  · obtain ⟨lsp, x, rfl⟩ := hnot
    rw [relKind_since_not pre]
    cases hm : impliesMine x
    · exact general
    · -- The native `since`.
      have hx : ∃ ψx, x.toFormula = .ok ψx ∧ ψx.Pinned S := by
        simp only [Condition.toFormula, ConditionKind.toFormula, bind_eq_ok, pure_eq_ok] at hl
        obtain ⟨ψx, hx, rfl⟩ := hl
        exact ⟨ψx, hx, hpl⟩
      obtain ⟨ψx, hxf, hpx⟩ := hx
      show RSat ι rate σ e (fun _ => True) v j ⟨sp, .since (mkNot sp ((relCond pre μ x).run
        ((relCond pre μ r).run n).2).1) w (guardMine μ ((relCond pre μ r).run n).1)⟩ ↔ _
      rw [rsat_since_iff hw, rsat_since_iff hw]
      have hleft : ∀ k', RSat ι rate σ e (fun _ => True) v k'
          (mkNot sp ((relCond pre μ x).run ((relCond pre μ r).run n).2).1) ↔
          RSat ι rate σ e (S.Visible σ e) v k' ⟨lsp, .not x⟩ :=
        fun k' => IHl ((relCond pre μ r).run n).2 v k'
      constructor
      · rintro ⟨k, hkj, _, hiw, ha, hall⟩
        obtain ⟨hvk, hrk⟩ := (hguard v k (AgreeOff.refl pre v)).mp ha
        exact ⟨k, hkj, hvk, hiw, hrk, fun k' h₁ h₂ _ => (hleft k').mp (hall k' h₁ h₂ trivial)⟩
      · rintro ⟨k, hkj, hvk, hiw, hrk, hall⟩
        refine ⟨k, hkj, trivial, hiw, (hguard v k (AgreeOff.refl pre v)).mpr ⟨hvk, hrk⟩,
          fun k' h₁ h₂ _ => (hleft k').mpr ?_⟩
        intro hxk
        exact hall k' h₁ h₂ (xsat_visible hm hxf hpx hxk) hxk
  · rw [relKind_since_general pre μ sp l w r fun lsp x h => hnot ⟨lsp, x, h⟩]
    exact general

/-- The `previous` of the specification, unfolded. -/
theorem rsat_previous_iff {vis : Nat → Prop} {sp : Span} {c : Condition} {w : WithinSpec} {win : Window}
    (hw : w.toSpec = .ok win) (v : Valuation) (j : Nat) :
    RSat ι rate σ e vis v j ⟨sp, .previous w c⟩ ↔
      ∃ k, k < j ∧ vis k ∧ (∀ k', k < k' → k' < j → ¬ vis k') ∧ InWindow rate σ j k win ∧
        RSat ι rate σ e vis v k c := by
  simp [XSat, hw]

/-- The `formerly` of the specification, unfolded. -/
theorem rsat_formerly_iff {vis : Nat → Prop} {sp : Span} {c : Condition} {w : WithinSpec} {win : Window}
    (hw : w.toSpec = .ok win) (v : Valuation) (j : Nat) :
    RSat ι rate σ e vis v j ⟨sp, .formerly w c⟩ ↔
      ∃ k, k ≤ j ∧ vis k ∧ InWindow rate σ j k win ∧ RSat ι rate σ e vis v k c := by
  simp [XSat, hw]

mutual

/-- **The relativization rewrite, read with every timepoint visible, is the condition read with
the key's timepoints visible**, on a trace whose timestamps never decrease and whose counts fit a
`Long`, under every valuation and from every state of the rewrite's counter. -/
theorem rsat_relCond (hμ : ∀ sp v k, RSat ι rate σ e (fun _ => True) v k (μ sp) ↔ S.Visible σ e k)
    (hσ : σ.Nondecreasing) (hlen : (σ.length : Int) ≤ Int64.MAX) :
    (b : Condition) → {ψ : Formula} → b.toFormula = .ok ψ → ψ.Pinned S → NoFreshNames pre b →
    (n : Nat) → (v : Valuation) → (j : Nat) →
    (RSat ι rate σ e (fun _ => True) v j ((relCond pre μ b).run n).1 ↔
      RSat ι rate σ e (S.Visible σ e) v j b)
  | ⟨sp, .and l r⟩, ψ, h, hp, hnf, n, v, j => by
    simp only [Condition.toFormula, ConditionKind.toFormula, bind_eq_ok, pure_eq_ok] at h
    obtain ⟨a, ha, b, hb, rfl⟩ := h
    have hnfl : NoFreshNames pre l := fun x hx => hnf x (by simp [condNames, kindNames, hx])
    have hnfr : NoFreshNames pre r := fun x hx => hnf x (by simp [condNames, kindNames, hx])
    exact and_congr (rsat_relCond hμ hσ hlen l ha hp.1 hnfl n v j)
      (rsat_relCond hμ hσ hlen r hb hp.2 hnfr _ v j)
  | ⟨sp, .or l r⟩, ψ, h, _, _, _, _, _ => by
    simp [Condition.toFormula, ConditionKind.toFormula] at h
  | ⟨sp, .not c⟩, ψ, h, hp, hnf, n, v, j => by
    simp only [Condition.toFormula, ConditionKind.toFormula, bind_eq_ok, pure_eq_ok] at h
    obtain ⟨a, ha, rfl⟩ := h
    exact not_congr (rsat_relCond hμ hσ hlen c ha hp hnf n v j)
  | ⟨sp, .formerly w c⟩, ψ, h, hp, hnf, n, v, j => by
    simp only [Condition.toFormula, ConditionKind.toFormula, bind_eq_ok, pure_eq_ok] at h
    obtain ⟨win, hw, a, ha, rfl⟩ := h
    have hguard := rsat_guard hμ ha hp hnf (impliesMine_relCond pre μ c n)
      (rsat_relCond hμ hσ hlen c ha hp hnf n) v
    show RSat ι rate σ e (fun _ => True) v j ⟨sp, .formerly w (guardMine μ ((relCond pre μ c).run n).1)⟩ ↔ _
    rw [rsat_formerly_iff hw, rsat_formerly_iff hw]
    constructor
    · rintro ⟨k, hkj, _, hiw, hb⟩
      obtain ⟨hvk, hck⟩ := (hguard v k (AgreeOff.refl pre v)).mp hb
      exact ⟨k, hkj, hvk, hiw, hck⟩
    · rintro ⟨k, hkj, hvk, hiw, hck⟩
      exact ⟨k, hkj, trivial, hiw, (hguard v k (AgreeOff.refl pre v)).mpr ⟨hvk, hck⟩⟩
  | ⟨sp, .previous w c⟩, ψ, h, hp, hnf, n, v, j => by
    simp only [Condition.toFormula, ConditionKind.toFormula, bind_eq_ok, pure_eq_ok] at h
    obtain ⟨win, hw, a, ha, rfl⟩ := h
    have hguard := rsat_guard hμ ha hp hnf (impliesMine_relCond pre μ c n)
      (rsat_relCond hμ hσ hlen c ha hp hnf n) v
    show RSat ι rate σ e (fun _ => True) v j ((relKind pre μ sp (.previous w c)).run n).1 ↔ _
    rw [run_relKind_previous, rsat_encodePrevious hμ hw (startsWith_freshName _ _ _)
      (startsWith_freshName _ _ _) (startsWith_freshName _ _ _) (freshName_ti_tj _ _) (freshName_ti_tk _ _)
      (freshName_tj_tk _ _) hguard j, rsat_previous_iff hw]
    constructor
    · rintro ⟨k, hkj, hiw, ⟨hvk, hck⟩, hno⟩
      refine ⟨k, hkj, hvk, fun k' h₁ h₂ hv' => hno ⟨k', h₁, h₂, ?_, hv'⟩, hiw, hck⟩
      exact inWindow_between hσ hiw (Nat.le_of_lt h₁) (Nat.le_of_lt h₂)
    · rintro ⟨k, hkj, hvk, hno, hiw, hck⟩
      exact ⟨k, hkj, hiw, ⟨hvk, hck⟩, fun ⟨m, h₁, h₂, _, hvm⟩ => hno m h₁ h₂ hvm⟩
  | ⟨sp, .since l w r⟩, ψ, h, hp, hnf, n, v, j => by
    simp only [Condition.toFormula, ConditionKind.toFormula, bind_eq_ok, pure_eq_ok] at h
    obtain ⟨a, ha, win, hw, b, hb, rfl⟩ := h
    have hnfl : NoFreshNames pre l := fun x hx => hnf x (by simp [condNames, kindNames, hx])
    have hnfr : NoFreshNames pre r := fun x hx => hnf x (by simp [condNames, kindNames, hx])
    exact rsat_since_case hμ hσ hlen ha hw hb hp.1 hp.2 hnfl hnfr
      (rsat_relCond hμ hσ hlen l ha hp.1 hnfl) (rsat_relCond hμ hσ hlen r hb hp.2 hnfr) n v j
  | ⟨sp, .exists ⟨s, ty⟩ c⟩, ψ, h, hp, hnf, n, v, j => by
    simp only [Condition.toFormula, ConditionKind.toFormula, TypedBinder.toSpec, bind_eq_ok,
      pure_eq_ok] at h
    obtain ⟨y, ⟨x, hx, rfl⟩, a, ha, rfl⟩ := h
    have hnfc : NoFreshNames pre c := fun z hz => hnf z (by simp [condNames, kindNames, hz])
    show XSat ι rate σ e (fun _ => True) true anyValue v j
      ⟨sp, .exists ⟨s, ty⟩ ((relCond pre μ c).run n).1⟩ ↔ _
    simp only [XSat]
    exact exists_congr fun x' => and_congr_right' (exists_congr fun w => and_congr_right' (
      rsat_relCond hμ hσ hlen c ha hp hnfc n _ j))
  | ⟨sp, .comparison op l r⟩, ψ, h, hp, hnf, n, v, j => by
    simp only [Condition.toFormula, ConditionKind.toFormula, bind_eq_ok, pure_eq_ok] at h
    obtain ⟨l', hl, r', hr, rfl⟩ := h
    have hnfl : ∀ x ∈ termNames l, hasPrefix pre x = false :=
      fun x hx => hnf x (by simp [condNames, kindNames, hx])
    have hnfr : ∀ x ∈ termNames r, hasPrefix pre x = false :=
      fun x hx => hnf x (by simp [condNames, kindNames, hx])
    show XSat ι rate σ e (fun _ => True) true anyValue v j
      ⟨sp, .comparison op ((relTerm pre μ l).run n).1 ((relTerm pre μ r).run ((relTerm pre μ l).run n).2).1⟩ ↔ _
    simp only [XSat]
    exact exists_congr fun a => exists_congr fun b => and_congr
      (rsat_relTerm hμ hσ hlen l hl hp.1 hnfl n v j a)
      (and_congr_left' (rsat_relTerm hμ hσ hlen r hr hp.2 hnfr _ v j b))
  | ⟨sp, .predicate ⟨_, _, _, _, _⟩⟩, _, _, _, _, _, _, _ => Iff.rfl
  | ⟨sp, .tp _⟩, _, _, _, _, _, _, _ => Iff.rfl
  | ⟨sp, .call _⟩, _, _, _, _, _, _, _ => Iff.rfl
  | ⟨sp, .sigilRef _ _⟩, _, _, _, _, _, _, _ => Iff.rfl
  | ⟨sp, .refine _ _ _⟩, ψ, h, _, _, _, _, _ => by
    simp [Condition.toFormula, ConditionKind.toFormula] at h

theorem rsat_relTerm (hμ : ∀ sp v k, RSat ι rate σ e (fun _ => True) v k (μ sp) ↔ S.Visible σ e k)
    (hσ : σ.Nondecreasing) (hlen : (σ.length : Int) ≤ Int64.MAX) :
    (t : Surface.Temporal.Term) → {t' : Dogwood.Spec.Temporal.Term} → t.toSpec = .ok t' →
    t'.Pinned S → (∀ x ∈ termNames t, hasPrefix pre x = false) →
    (n : Nat) → (v : Valuation) → (j : Nat) → (c : CVal) →
    (XDenotes ι rate σ e (fun _ => True) true anyValue v j ((relTerm pre μ t).run n).1 c ↔
      XDenotes ι rate σ e (S.Visible σ e) true anyValue v j t c)
  | .agg ⟨sp, k⟩, t', h, hp, hnf, n, v, j, c => by
    simp only [Surface.Temporal.Term.toSpec, bind_eq_ok, pure_eq_ok] at h
    obtain ⟨a, ha, rfl⟩ := h
    show XDenotes ι rate σ e (fun _ => True) true anyValue v j (.agg ⟨sp, ((relAggKind pre μ k).run n).1⟩) c ↔ _
    simp only [XDenotes]
    exact exists_congr fun N => and_congr_left' (rsat_relAggKind hμ hσ hlen k ha hp hnf n v j N)
  | .arith op l r, t', h, hp, hnf, n, v, j, c => by
    simp only [Surface.Temporal.Term.toSpec, bind_eq_ok, pure_eq_ok] at h
    obtain ⟨l', hl, r', hr, rfl⟩ := h
    have hnfl : ∀ x ∈ termNames l, hasPrefix pre x = false :=
      fun x hx => hnf x (by simp [termNames, hx])
    have hnfr : ∀ x ∈ termNames r, hasPrefix pre x = false :=
      fun x hx => hnf x (by simp [termNames, hx])
    show XDenotes ι rate σ e (fun _ => True) true anyValue v j
      (.arith op ((relTerm pre μ l).run n).1 ((relTerm pre μ r).run ((relTerm pre μ l).run n).2).1) c ↔ _
    simp only [XDenotes]
    exact exists_congr fun m => exists_congr fun m' => and_congr
      (rsat_relTerm hμ hσ hlen l hl hp.1 hnfl n v j _)
      (and_congr_left' (rsat_relTerm hμ hσ hlen r hr hp.2 hnfr _ v j _))
  | .array _, t', h, _, _, _, _, _, _ => by simp [Surface.Temporal.Term.toSpec, throw, throwThe,
      MonadExceptOf.throw] at h
  | .entity _ _, _, _, _, _, _, _, _, _ | .integer _, _, _, _, _, _, _, _, _
  | .decimal _, _, _, _, _, _, _, _, _ | .string _, _, _, _, _, _, _, _, _
  | .bool _, _, _, _, _, _, _, _, _ | .contextField _, _, _, _, _, _, _, _, _
  | .scopeField _, _, _, _, _, _, _, _, _ | .var _, _, _, _, _, _, _, _, _
  | .wildcard, _, _, _, _, _, _, _, _ | .paramRef _, _, _, _, _, _, _, _, _
  | .binderRef _, _, _, _, _, _, _, _, _ => Iff.rfl

theorem rsat_relAggKind (hμ : ∀ sp v k, RSat ι rate σ e (fun _ => True) v k (μ sp) ↔ S.Visible σ e k)
    (hσ : σ.Nondecreasing) (hlen : (σ.length : Int) ≤ Int64.MAX) :
    (k : AggExprKind) → {a : Aggregate} → AggExprKind.toSpec k = .ok a → a.Pinned S →
    (∀ x ∈ aggNames k, hasPrefix pre x = false) →
    (n : Nat) → (v : Valuation) → (j : Nat) → (N : Int) →
    (XTotal ι rate σ e (fun _ => True) true anyValue v j ((relAggKind pre μ k).run n).1 N ↔
      XTotal ι rate σ e (S.Visible σ e) true anyValue v j k N)
  | .count vs b, a, h, hp, hnf, n, v, j, N => by
    simp only [AggExprKind.toSpec, bind_eq_ok, pure_eq_ok] at h
    obtain ⟨bs, hbs, body, hb, rfl⟩ := h
    have hnfb : NoFreshNames pre b := fun x hx => hnf x (by simp [aggNames, hx])
    show XTotal ι rate σ e (fun _ => True) true anyValue v j (.count vs ((relCond pre μ b).run n).1) N ↔ _
    simp only [XTotal]
    exact exists_congr fun bs' => and_congr_right' (exists_congr fun rows => and_congr_right'
      (and_congr_left' (forall_congr' fun row => iff_congr Iff.rfl (and_congr_right' (and_congr_right'
        (rsat_relCond hμ hσ hlen b hb hp hnfb n _ j))))))
  | .sum s vs b, a, h, hp, hnf, n, v, j, N => by
    simp only [AggExprKind.toSpec, bind_eq_ok, pure_eq_ok] at h
    obtain ⟨x, hx, bs, hbs, body, hb, rfl⟩ := h
    have hnfb : NoFreshNames pre b := fun z hz => hnf z (by simp [aggNames, hz])
    show XTotal ι rate σ e (fun _ => True) true anyValue v j (.sum s vs ((relCond pre μ b).run n).1) N ↔ _
    simp only [XTotal]
    exact exists_congr fun x' => exists_congr fun bs' => and_congr_right' (and_congr_right'
      (exists_congr fun rows => and_congr_right' (and_congr_left' (forall_congr' fun row =>
        iff_congr Iff.rfl (and_congr_right' (and_congr_right'
          (rsat_relCond hμ hσ hlen b hb hp hnfb n _ j)))))))
  | .call _, a, h, _, _, _, _, _, _ => by simp [AggExprKind.toSpec] at h

end

end

end Dogwood.Thm.Frontend
