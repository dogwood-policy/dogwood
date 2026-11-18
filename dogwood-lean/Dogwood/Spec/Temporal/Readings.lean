import Dogwood.Spec.Temporal.Semantics

/-!
# Readings of out-of-range results

The language leaves the reading of an integer result outside the `Long` range implementation
defined (`ImplChoices`): an implementation may compute it exactly (`ImplChoices.widen`), clamp
it to the range (`ImplChoices.clamp`, the reference interpreter's choice), or report an error
(`ImplChoices.error`). This module states which readings conform, and how a decision is made
under a reading that reports errors.

**Admissible readings.** A reading is admissible when it preserves the side of the range an
out-of-range result lies on (`ImplChoices.Admissible`): a result above `Int64.MAX` is read as an
integer no less than `Int64.MAX`, and a result below `Int64.MIN` as one no greater than
`Int64.MIN`, or as an error. Widening, clamping, and reporting errors are admissible; wrapping
around, as two's-complement arithmetic does, is not. A comparison of an aggregate total with a
threshold strictly inside the range is then read alike by every admissible reading
(`Dogwood.Thm.sat_interior_threshold`).

**Erroring readings fail closed.** A reading that reports an error for some results is
*completed* by every total admissible reading that agrees with it where it does not report an
error (`ImplChoices.Completes`). A decision under the reading is the decision every completion
makes, when they all make the same one; otherwise the decision depends on how the erroring
results would have been read, and it fails closed (`ImplChoices.supervaluate`,
`Dogwood.Spec.PolicySet.respond`, `FailClosed.temporalError`). A total reading is its own only
completion, so under a total reading this is the decision `Sat` gives
(`Dogwood.Thm.supervaluate_total`): the total semantics is unchanged.

**In range, the readings agree.** When every aggregate total and arithmetic result a condition
computes is inside the range (`Formula.InRange`), every reading gives it the same truth value
(`Dogwood.Thm.sat_readings_agree`), and every reading decides alike
(`Dogwood.Thm.authorize_readings_agree`).
-/

namespace Dogwood.Spec.Temporal

/-! ## Admissible readings -/

/-- The integer `n` lies in the `Long` range. -/
def InLong (n : Int) : Prop := Int64.MIN ≤ n ∧ n ≤ Int64.MAX

instance (n : Int) : Decidable (InLong n) := inferInstanceAs (Decidable (_ ∧ _))

/-- An out-of-range reading `f` keeps the side of the range a result lies on: when it reads a
result, it reads one above the range as an integer no less than `Int64.MAX`, and one below the
range as an integer no greater than `Int64.MIN`. -/
def SidePreserving (f : Int → Option Int) : Prop :=
  ∀ n m, f n = some m → (Int64.MAX < n → Int64.MAX ≤ m) ∧ (n < Int64.MIN → m ≤ Int64.MIN)

/-- **An admissible reading** preserves the side of the range of every out-of-range aggregate
total and arithmetic result it reads. -/
structure ImplChoices.Admissible (ι : ImplChoices) : Prop where
  aggregate : SidePreserving ι.outOfRange
  arith : SidePreserving ι.arithOutOfRange

/-- A reading that reads every out-of-range result: it never reports an error. -/
structure ImplChoices.Total (ι : ImplChoices) : Prop where
  aggregate : ∀ n, (ι.outOfRange n).isSome = true
  arith : ∀ n, (ι.arithOutOfRange n).isSome = true

/-- The out-of-range reading `f'` completes `f`: it reads every result, as `f` does where `f`
reads it, and preserves the side of the range where `f` reports an error. -/
structure ReadingCompletes (f' f : Int → Option Int) : Prop where
  total : ∀ n, (f' n).isSome = true
  agrees : ∀ n m, f n = some m → f' n = some m
  sides : ∀ n m, f n = none → f' n = some m →
    (Int64.MAX < n → Int64.MAX ≤ m) ∧ (n < Int64.MIN → m ≤ Int64.MIN)

/-- **A completion** of the reading `ι`: a total reading that agrees with `ι` wherever `ι` reads
a result, and reads the results `ι` reports an error for admissibly. -/
structure ImplChoices.Completes (ι' ι : ImplChoices) : Prop where
  aggregate : ReadingCompletes ι'.outOfRange ι.outOfRange
  arith : ReadingCompletes ι'.arithOutOfRange ι.arithOutOfRange

/-- **The decision under a reading.** The value `f ι'` every completion `ι'` of `ι` gives, when
they all give the same; `none` when two completions give different values: the value depends on
how the results `ι` reports an error for would have been read. -/
noncomputable def ImplChoices.supervaluate {α : Type} (ι : ImplChoices) (f : ImplChoices → α) :
    Option α :=
  open Classical in
  if h : ∃ r, ∀ ι', ι'.Completes ι → f ι' = r then some h.choose else none

/-! ## Results in range -/

section

variable (ι : ImplChoices) (rate : TickRate) (σ : Trace) (e : Event) (vis : Nat → Prop)

mutual

/-- **Every result is in range.** Every aggregate total and every arithmetic result the
condition `φ` computes at timepoint `j` under `v`, under every valuation its binders reach, lies
in the `Long` range, under the reading `ι`. A temporal operator's operands are checked at every
timepoint up to and including `j` (for `previous`, every one before `j`), not only those inside
its window, so this is stronger than what an evaluation reads. -/
def Formula.InRange (v : Valuation) (j : Nat) : Formula → Prop
  | .and φ ψ => Formula.InRange v j φ ∧ Formula.InRange v j ψ
  | .not φ => Formula.InRange v j φ
  | .formerly _ φ => ∀ k ≤ j, Formula.InRange v k φ
  | .previous _ φ => ∀ k < j, Formula.InRange v k φ
  | .since φ _ ψ => ∀ k ≤ j, Formula.InRange v k φ ∧ Formula.InRange v k ψ
  | .pred _ _ _ => True
  | .cmp _ l r => Term.InRange v j l ∧ Term.InRange v j r
  | .exist x φ => ∀ w, Formula.InRange (v.bind x.name w) j φ
  | .tp _ => True

/-- Every result the operand `t` computes is in range. -/
def Term.InRange (v : Valuation) (j : Nat) : Term → Prop
  | .agg a => Aggregate.InRange v j a ∧ ∀ n, Total ι rate σ e vis v j a n → InLong n
  | .arith op l r => Term.InRange v j l ∧ Term.InRange v j r ∧
      ∀ m n, Denotes ι rate σ e vis v j l (.num m) → Denotes ι rate σ e vis v j r (.num n) →
        InLong (op.apply m n)
  | _ => True

/-- Every result the aggregation's body computes, for every row, is in range. -/
def Aggregate.InRange (v : Valuation) (j : Nat) : Aggregate → Prop
  | .count dom body => ∀ row, Formula.InRange (v.bindAll (domainNames dom) row) j body
  | .sum _ dom body => ∀ row, Formula.InRange (v.bindAll (domainNames dom) row) j body

end

end

end Dogwood.Spec.Temporal
