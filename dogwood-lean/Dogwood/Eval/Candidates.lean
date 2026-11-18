import Dogwood.Spec.Temporal.Semantics
import Dogwood.Spec.Temporal.Safety

/-!
# Candidate values

A finite list of values that over-approximates every value a range-restricted variable of a
safe condition can take, in any satisfying assignment, at any timepoint up to `J` of a trace.
The list is computed from `X`, a list that holds the values of the variables restricted outside
the condition.

A range-restricted variable takes its value from a positive atom:

* a predicate argument `P{ f: x }`: a value of field `f` in a logged event at a timepoint up to
  `J`;
* `tp(x)`: a timepoint up to `J`;
* a binding equality `x == t`: a value the operand `t` can denote (`Term.opCand`). A ground term
  denotes its value, which does not depend on the valuation; an aggregate, any of the values its
  total can compare as — a `count` is at most the number of candidate rows, and a `sum` at most
  the sum of the absolute values of their summands; a compound, the result of its operator on
  values its operands can denote. A variable inside the value side takes a value of `X`.

Within a `&&` chain, a conjunct may restrict a variable from variables that other conjuncts
restrict, in any order (`Formula.Restricts`). So the candidates of a chain are computed by
iteration: each round adds the candidates every conjunct gives from the values found so far. The
restriction closure of a chain is reached after at most as many rounds as the chain has free
variables, so that many rounds, plus one, suffice (`Dogwood.Thm.rr_sound`).

These definitions are not part of the specification. The evaluator (`Dogwood.Eval.eval`)
searches them, and `Dogwood.Thm.Monitorable` proves them sound.
-/

namespace Dogwood.Spec.Temporal

open Cedar.Spec (Value)

/-- `f` applied `n` times. -/
def iter {α : Type} (f : α → α) : Nat → α → α
  | 0, a => a
  | n + 1, a => f (iter f n a)

/-- All lists of length `m` drawn from `xs`. -/
def product {α : Type} (xs : List α) : Nat → List (List α)
  | 0 => [[]]
  | m + 1 => xs.flatMap fun x => (product xs m).map (x :: ·)

/-- The value whose comparison operand is `c`. An integer is read back as the `Long` it would
have to be; one outside the `Long` range is never a variable's operand value, so the
wrap-around does no harm. -/
def CVal.toTVal : CVal → TVal
  | .num m => .val (.prim (.int (Int64.ofInt m)))
  | .val w => .val w
  | .tp k => .tp k

/-- The operand value of an arithmetic operation on two candidate operand values. -/
def arithCand (ι : ImplChoices) (op : ArithOp) : CVal → CVal → Option CVal
  | .num m, .num n => ι.arithValue (op.apply m n)
  | _, _ => none

section

variable (ι : ImplChoices) (σ : Trace) (e : Event) (J : Nat)

/-- The values the field paths `paths` hold in the logged events at timepoints `0 … J`. -/
def traceValues (paths : List Path) : List TVal :=
  (List.range (J + 1)).flatMap fun k =>
    match σ[k]? with
    | some p => (paths.filterMap (recordPath? p.event.logged)).map .val
    | none => []

/-- The values `tp` binds at timepoints `0 … J`. -/
def tpValues : List TVal := (List.range (J + 1)).map tpValue

/-- The operand values of an aggregate whose exact total lies in `lo … hi`. -/
def aggValues (lo hi : Int) : List CVal :=
  ((List.range (hi - lo + 1).toNat).map fun (i : Nat) => lo + (i : Int)).filterMap
    ι.aggregateValue

mutual

/-- The candidate values of the variables `φ` range-restricts, given the values `X` of the
variables restricted outside it. -/
def Formula.cand (X : List TVal) : Formula → List TVal
  | .and φ ψ =>
    iter (fun Y => (Y ++ φ.cand Y ++ ψ.cand Y).eraseDups) ((Formula.and φ ψ).fv.length + 1) X
  | .not _ => []
  | .formerly _ φ => φ.cand X
  | .previous _ φ => φ.cand X
  | .exist _ φ => φ.cand X
  | .since _ _ ψ => ψ.cand X
  | .pred _ _ args => traceValues σ J (args.map (·.1))
  | .cmp .eq l r => (l.opCand X ++ r.opCand X).map CVal.toTVal
  | .cmp _ _ _ => []
  | .tp _ => tpValues J

/-- The values a comparison operand can denote, given the values `X` of the variables it
reads. -/
def Term.opCand (X : List TVal) : Term → List CVal
  | .var _ => X.map CVal.ofTVal
  | .wildcard => []
  | .agg a => a.cand X
  | .arith op l r => (l.opCand X).flatMap fun a => (r.opCand X).filterMap (arithCand ι op a)
  | t => (t.eval? e Valuation.empty).toList.map CVal.ofTVal

/-- The values an aggregate can compare as. Its rows are drawn from the candidates of its body's
variables. -/
def Aggregate.cand (X : List TVal) : Aggregate → List CVal
  | .count dom body =>
    let rows := product (body.cand X) (domainNames dom).length
    aggValues ι 0 rows.length
  | .sum s dom body =>
    let rows := product (body.cand X) (domainNames dom).length
    let bound : Int := (rows.map fun row => (summand s (domainNames dom) row).natAbs).sum
    aggValues ι (-bound) bound

end

end

end Dogwood.Spec.Temporal
