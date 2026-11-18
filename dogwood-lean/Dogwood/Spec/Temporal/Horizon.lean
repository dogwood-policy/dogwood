import Dogwood.Spec.Temporal.Syntax

/-!
# Horizons, and conditions that do not read timepoint indices

Two syntactic measures of a temporal condition that an implementation may rely
on when it prunes or partitions the history it keeps.

* **The horizon** (`Formula.horizon`): how far back, in ticks of a clock rate,
  a condition can look from the timepoint it is evaluated at. A temporal
  operator adds its window to the horizon of what it scans, and a conjunction,
  a comparison, or a compound operand takes the larger horizon of its parts. An
  aggregate looks as far back as its `where` body does. A window counts as `0`
  when it is negative, which validation rejects in any case
  (`Formula.WellTyped`), so a horizon is never negative. On a trace whose
  timestamps never decrease, a condition at timepoint `j` depends only on the
  timepoints `k ≤ j` with `ts(j) − ts(k) ≤ horizon` (`Dogwood.Thm.sat_horizon`).

  For a condition whose windows are nonnegative, the horizon is the largest sum
  of windows along a chain of nested temporal operators. It is not the event
  schema's `max_window`, which caps each window alone: `formerly within 1h (
  formerly within 1h … )` has a horizon of 2h under a 1h cap. The event
  schema's `max_horizon` caps the horizon itself. When the schema declares it,
  validation requires every temporal leaf's horizon to be at most
  `max_horizon` (`PolicySet.Valid.horizon`).

* **Conditions without `tp`** (`Formula.tpFree`): `tp(x)` reads a
  timepoint's index. A condition observes the index only through equality,
  so a renumbering of the timepoints changes no truth value. So every
  condition, `tp` included, means the same over a subsequence of the trace as
  over the full trace with only that subsequence visible, under a valuation
  that holds no timepoint (`Dogwood.Thm.sat_slice`). `Formula.tpFree` remains
  for proofs of implementations that use it.
-/

namespace Dogwood.Spec.Temporal

/-! ## The horizon -/

/-- A window's length in ticks of the rate `rate`, or `0` for a negative window. -/
def Window.reach (w : Window) (rate : TickRate) : Int := max 0 (w.ticks rate)

mutual

/-- How far back, in ticks of the rate `rate`, the condition can look from the
timepoint it is evaluated at. -/
def Formula.horizon (rate : TickRate) : Formula → Int
  | .and φ ψ => max (φ.horizon rate) (ψ.horizon rate)
  | .not φ | .exist _ φ => φ.horizon rate
  | .formerly w φ | .previous w φ => w.reach rate + φ.horizon rate
  | .since φ w ψ => w.reach rate + max (φ.horizon rate) (ψ.horizon rate)
  | .pred .. | .tp _ => 0
  | .cmp _ l r => max (l.horizon rate) (r.horizon rate)

/-- How far back a comparison operand can look: an aggregate's body's horizon,
and the larger horizon of a compound's operands. -/
def Term.horizon (rate : TickRate) : Term → Int
  | .agg a => a.horizon rate
  | .arith _ l r => max (l.horizon rate) (r.horizon rate)
  | _ => 0

def Aggregate.horizon (rate : TickRate) : Aggregate → Int
  | .count _ body | .sum _ _ body => body.horizon rate

end

/-! ## Windows -/

mutual

/-- Every `within` window of the condition, including those in aggregation
bodies. -/
def Formula.windows : Formula → List Window
  | .and φ ψ => φ.windows ++ ψ.windows
  | .not φ | .exist _ φ => φ.windows
  | .formerly w φ | .previous w φ => w :: φ.windows
  | .since φ w ψ => w :: (φ.windows ++ ψ.windows)
  | .cmp _ l r => l.windows ++ r.windows
  | .pred _ _ _ | .tp _ => []

def Term.windows : Term → List Window
  | .agg (.count _ body) | .agg (.sum _ _ body) => body.windows
  | .arith _ l r => l.windows ++ r.windows
  | _ => []

end

/-- Every window of the condition, including those in aggregation bodies, is
nonnegative. Validation guarantees it (`Window.withinCap` requires a positive
amount, `Dogwood.Thm.Formula.WellTyped.windowsNonneg`), and the proofs of
implementations assume it. -/
def Formula.WindowsNonneg (φ : Formula) : Prop := ∀ w ∈ φ.windows, 0 ≤ w.seconds

/-! ## Conditions without `tp` -/

mutual

/-- The condition binds no timepoint index: it contains no `tp`, including in
aggregation bodies. -/
def Formula.tpFree : Formula → Bool
  | .tp _ => false
  | .and φ ψ | .since φ _ ψ => φ.tpFree && ψ.tpFree
  | .not φ | .formerly _ φ | .previous _ φ | .exist _ φ => φ.tpFree
  | .pred .. => true
  | .cmp _ l r => l.tpFree && r.tpFree

def Term.tpFree : Term → Bool
  | .agg a => a.tpFree
  | .arith _ l r => l.tpFree && r.tpFree
  | _ => true

def Aggregate.tpFree : Aggregate → Bool
  | .count _ body | .sum _ _ body => body.tpFree

end

end Dogwood.Spec.Temporal
