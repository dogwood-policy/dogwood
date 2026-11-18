import Dogwood.Thm.Horizon

/-!
# The horizon of a validated condition is at most its depth times `max_window`

Validation caps each `within` window at the event schema's `max_window` (`Window.withinCap`, at
every window, `Formula.WellTyped`), but not how far back a condition looks: nested temporal
operators add their windows, so `formerly within 24h (formerly within 24h φ)` passes a 24h cap
and looks back 48h. How far back a condition looks is its horizon (`Formula.horizon`; events
older than it never matter, `Dogwood.Thm.authorize_drop_horizon`).

* **The bound** (`Formula.WellTyped.horizon_le`): a well-typed condition's horizon is at most its
  temporal depth (`Formula.depth`: the deepest nesting of `formerly`, `previous`, and `since`,
  through conjunctions, negations, `exists`, comparisons, and aggregate bodies) times `max_window`,
  in ticks. `since` counts once for both of its sides: its window bounds the anchor, and the left
  side must hold at every point back to it.
* **For a policy set** (`horizon_le_depth_mul_maxWindow`): every temporal leaf of a valid policy
  set, of a rule whose scope admits some request environment, has a horizon at most its depth
  times the set's `max_window`.
* **The bound is reached** (`horizon_formerlyIter_eq`): `n` nested `formerly within max_window`
  around a predicate have depth `n` and horizon exactly `n × max_window`.

Since the depth is not capped, this is no retention bound for the policies a service may accept;
the event schema's `max_horizon` is (`Dogwood.Thm.MaxHorizon`).
-/

namespace Dogwood.Spec.Temporal

mutual

/-- The temporal depth of a condition: the deepest nesting of `formerly`, `previous`, and
`since`. -/
def Formula.depth : Formula → Nat
  | .and φ ψ => max φ.depth ψ.depth
  | .not φ | .exist _ φ => φ.depth
  | .formerly _ φ | .previous _ φ => φ.depth + 1
  | .since φ _ ψ => max φ.depth ψ.depth + 1
  | .pred .. | .tp _ => 0
  | .cmp _ l r => max l.depth r.depth

def Term.depth : Term → Nat
  | .agg a => a.depth
  | .arith _ l r => max l.depth r.depth
  | _ => 0

def Aggregate.depth : Aggregate → Nat
  | .count _ body | .sum _ _ body => body.depth

end

end Dogwood.Spec.Temporal

namespace Dogwood.Thm

open Dogwood.Spec Dogwood.Spec.Temporal

section

variable {C : TypingCtx} {rate : TickRate}

/-- A window within the cap reaches at most the cap, in ticks. -/
theorem Window.reach_le_of_withinCap {w : Window} (hc : w.withinCap C.maxWindow = true) :
    w.reach rate ≤ C.maxWindow * rate.perSecond := by
  have hpos := Window.seconds_pos_of_withinCap hc
  simp only [Window.withinCap, Bool.and_eq_true, decide_eq_true_eq] at hc
  have hps : (0 : Int) ≤ rate.perSecond := Int.natCast_nonneg _
  unfold Window.reach Window.ticks
  refine Int.max_le.mpr ⟨Int.mul_nonneg (by omega) hps, Int.mul_le_mul_of_nonneg_right hc.2 hps⟩

private theorem le_max_left_mul {x W : Int} {a b : Nat} (hW : 0 ≤ W) (h : x ≤ a * W) :
    x ≤ ((max a b : Nat) : Int) * W :=
  Int.le_trans h (Int.mul_le_mul_of_nonneg_right (by omega) hW)

private theorem le_max_right_mul {x W : Int} {a b : Nat} (hW : 0 ≤ W) (h : x ≤ b * W) :
    x ≤ ((max a b : Nat) : Int) * W :=
  Int.le_trans h (Int.mul_le_mul_of_nonneg_right (by omega) hW)

private theorem max_le_max_mul {x y W : Int} {a b : Nat} (hW : 0 ≤ W) (hx : x ≤ a * W)
    (hy : y ≤ b * W) : max x y ≤ ((max a b : Nat) : Int) * W :=
  Int.max_le.mpr ⟨le_max_left_mul hW hx, le_max_right_mul hW hy⟩

private theorem succ_mul_bound {r h W : Int} {d : Nat} (hr : r ≤ W) (hh : h ≤ d * W) :
    r + h ≤ ((d + 1 : Nat) : Int) * W := by
  rw [Int.natCast_add, Int.add_mul, Int.natCast_one, Int.one_mul]
  omega

mutual

/-- **A well-typed condition looks back at most its depth times `max_window`**, in ticks, when
the cap is nonnegative. -/
theorem Formula.WellTyped.horizon_le (hM : 0 ≤ C.maxWindow) : {Γ : Bindings} → {φ : Formula} →
    Formula.WellTyped C Γ φ →
      φ.horizon rate ≤ (φ.depth : Int) * (C.maxWindow * rate.perSecond)
  | _, _, .and h₁ h₂ => by
    simp only [Formula.horizon, Formula.depth]
    exact max_le_max_mul (Int.mul_nonneg hM (Int.natCast_nonneg _))
      (Formula.WellTyped.horizon_le hM h₁) (Formula.WellTyped.horizon_le hM h₂)
  | _, _, .not h => by
    simp only [Formula.horizon, Formula.depth]; exact Formula.WellTyped.horizon_le hM h
  | _, _, .formerly hc h => by
    simp only [Formula.horizon, Formula.depth]
    exact succ_mul_bound (Window.reach_le_of_withinCap hc) (Formula.WellTyped.horizon_le hM h)
  | _, _, .previous hc h => by
    simp only [Formula.horizon, Formula.depth]
    exact succ_mul_bound (Window.reach_le_of_withinCap hc) (Formula.WellTyped.horizon_le hM h)
  | _, _, .since hc h₁ h₂ => by
    simp only [Formula.horizon, Formula.depth]
    exact succ_mul_bound (Window.reach_le_of_withinCap hc)
      (max_le_max_mul (Int.mul_nonneg hM (Int.natCast_nonneg _))
        (Formula.WellTyped.horizon_le hM h₁) (Formula.WellTyped.horizon_le hM h₂))
  | _, _, .pred _ _ _ => by simp [Formula.horizon, Formula.depth]
  | _, _, .eq _ hl hr _ => by
    simp only [Formula.horizon, Formula.depth]
    exact max_le_max_mul (Int.mul_nonneg hM (Int.natCast_nonneg _))
      (Term.Typed.horizon_le hM hl) (Term.Typed.horizon_le hM hr)
  | _, _, .ord _ hl hr => by
    simp only [Formula.horizon, Formula.depth]
    exact max_le_max_mul (Int.mul_nonneg hM (Int.natCast_nonneg _))
      (Term.Typed.horizon_le hM hl) (Term.Typed.horizon_le hM hr)
  | _, _, .exist _ h => by
    simp only [Formula.horizon, Formula.depth]; exact Formula.WellTyped.horizon_le hM h
  | _, _, .tp _ => by simp [Formula.horizon, Formula.depth]

theorem Term.Typed.horizon_le (hM : 0 ≤ C.maxWindow) : {Γ : Bindings} → {t : Term} →
    {τ : TType} → Term.Typed C Γ t τ →
      t.horizon rate ≤ (t.depth : Int) * (C.maxWindow * rate.perSecond)
  | _, _, _, .entity _ | _, _, _, .long | _, _, _, .decimal _ | _, _, _, .string
  | _, _, _, .bool | _, _, _, .context _ _ | _, _, _, .scopeRoot
  | _, _, _, .scopeAttr _ _ _ | _, _, _, .var _ => by simp [Term.horizon, Term.depth]
  | _, _, _, .agg h => by
    simp only [Term.horizon, Term.depth]; exact Aggregate.Typed.horizon_le hM h
  | _, _, _, .arith h₁ h₂ => by
    simp only [Term.horizon, Term.depth]
    exact max_le_max_mul (Int.mul_nonneg hM (Int.natCast_nonneg _))
      (Term.Typed.horizon_le hM h₁) (Term.Typed.horizon_le hM h₂)

theorem Aggregate.Typed.horizon_le (hM : 0 ≤ C.maxWindow) : {Γ : Bindings} → {a : Aggregate} →
    Aggregate.Typed C Γ a →
      a.horizon rate ≤ (a.depth : Int) * (C.maxWindow * rate.perSecond)
  | _, _, .count _ h => by
    simp only [Aggregate.horizon, Aggregate.depth]; exact Formula.WellTyped.horizon_le hM h
  | _, _, .sum _ _ h => by
    simp only [Aggregate.horizon, Aggregate.depth]; exact Formula.WellTyped.horizon_le hM h

end

end

/-- **Every temporal leaf of a valid policy set looks back at most its depth times
`max_window`**, in ticks of the set's clock, when its rule's scope admits a request environment
(validation types the leaf in each environment the rule admits, and checks every window's cap
there) and the cap is nonnegative. -/
theorem horizon_le_depth_mul_maxWindow {P : PolicySet} (hv : P.Valid) {p : Policy}
    (hp : p ∈ P.policies) {φ : Formula} {F : List Guard}
    (hφ : (.inl φ, F) ∈ p.toExpr.leafFacts []) (henv : P.envsOf p ≠ [])
    (hM : 0 ≤ P.maxWindow) :
    φ.horizon P.tickRate ≤ (φ.depth : Int) * (P.maxWindow * P.tickRate.perSecond) := by
  obtain ⟨env, he⟩ := List.exists_mem_of_ne_nil _ henv
  exact Formula.WellTyped.horizon_le (C := P.typingCtx env F) hM
    ((hv.temporal p hp φ F hφ).wellTyped env he)

/-- `n` nested `formerly within w` around `φ`. -/
def formerlyIter (w : Window) : Nat → Formula → Formula
  | 0, φ => φ
  | n + 1, φ => .formerly w (formerlyIter w n φ)

theorem formerlyIter_depth (w : Window) (φ : Formula) :
    (n : Nat) → (formerlyIter w n φ).depth = n + φ.depth
  | 0 => by simp [formerlyIter]
  | n + 1 => by simp only [formerlyIter, Formula.depth, formerlyIter_depth w φ n]; omega

theorem formerlyIter_horizon (rate : TickRate) (w : Window) (φ : Formula) :
    (n : Nat) → (formerlyIter w n φ).horizon rate = n * w.reach rate + φ.horizon rate
  | 0 => by simp [formerlyIter]
  | n + 1 => by
    simp only [formerlyIter, Formula.horizon, formerlyIter_horizon rate w φ n, Int.natCast_add,
      Int.add_mul, Int.natCast_one, Int.one_mul]
    omega

/-- **The bound is reached**: `n` nested `formerly within max_window` around a condition that
looks back no further than its timepoint, such as a predicate, have depth `n` and horizon
exactly `n` times `max_window`. -/
theorem horizon_formerlyIter_eq {rate : TickRate} {M : Int} {w : Window} (hw : w.seconds = M)
    (hM : 0 ≤ M) {φ : Formula} (hh : φ.horizon rate = 0) (hd : φ.depth = 0) (n : Nat) :
    (formerlyIter w n φ).horizon rate =
      ((formerlyIter w n φ).depth : Int) * (M * rate.perSecond) := by
  have hreach : w.reach rate = M * rate.perSecond := by
    unfold Window.reach Window.ticks
    rw [hw]
    exact Int.max_eq_right (Int.mul_nonneg hM (Int.natCast_nonneg _))
  rw [formerlyIter_horizon, formerlyIter_depth, hd, hh, hreach, Nat.add_zero, Int.add_zero]

end Dogwood.Thm
