import Dogwood.Eval.Candidates

/-!
# Deciding safety

`restrictsB R φ` computes the variables `φ` restricts given the variables `R`
(`Formula.Restricts`), iterating each `&&` chain to its closure, without repetitions (each round
keeps every variable once, so nested chains stay small). `safeB R φ` decides
`Formula.Safe`. `Dogwood.Thm.restrictsB_iff` and `Dogwood.Thm.safeB_iff` prove them equal to the
relations. They are not part of the specification: the conformance harness runs them.
-/

namespace Dogwood.Eval

open Dogwood.Spec Dogwood.Spec.Temporal

/-- `Formula.Restricts`, computed. -/
def restrictsB (R : List VarName) : Formula → List VarName
  | .pred _ _ args => predVars args
  | .tp y => [y]
  | .cmp .eq l r =>
    match eqRestricted? l r with
    | some x => if (valueSide x l r).fv.all (R.contains ·) then [x] else []
    | none => []
  | .cmp _ _ _ => []
  | .not _ => []
  | .formerly _ φ => restrictsB R φ
  | .previous _ φ => restrictsB R φ
  | .since _ _ ψ => restrictsB R ψ
  | .exist y φ => (restrictsB (R.filter (· != y.name)) φ).filter (· != y.name)
  | .and φ ψ =>
    iter (fun S => (S ++ restrictsB S φ ++ restrictsB S ψ).eraseDups)
      ((Formula.and φ ψ).fv.length + 1) R

mutual

/-- `Formula.Safe`, decided. -/
def safeB (R : List VarName) : Formula → Bool
  | .and φ ψ =>
    safeB (restrictsB R (.and φ ψ)) φ && safeB (restrictsB R (.and φ ψ)) ψ
  | .not φ => φ.fv.all (R.contains ·) && safeB R φ
  | .formerly _ φ => safeB R φ
  | .previous _ φ => safeB R φ
  | .since φ _ ψ =>
    safeB R ψ && φ.fv.all ((R ++ restrictsB R ψ).contains ·) && safeB (R ++ restrictsB R ψ) φ
  | .pred _ _ _ => true
  | .tp _ => true
  | .cmp op l r =>
    (l.fv ++ r.fv).all ((R ++ restrictsB R (.cmp op l r)).contains ·) &&
      termSafeB R l && termSafeB R r
  | .exist x φ =>
    (restrictsB (R.filter (· != x.name)) φ).contains x.name && safeB (R.filter (· != x.name)) φ

/-- `Term.Safe`, decided. -/
def termSafeB (R : List VarName) : Term → Bool
  | .agg a => aggSafeB R a
  | .arith _ l r => termSafeB R l && termSafeB R r
  | _ => true

/-- `Aggregate.Safe`, decided. -/
def aggSafeB (R : List VarName) : Aggregate → Bool
  | .count dom body | .sum _ dom body =>
    dom.all (fun b => (restrictsB (R.filter fun z => !(dom.map (·.name)).contains z) body).contains
        b.name) &&
      safeB (R.filter fun z => !(dom.map (·.name)).contains z) body

end

/-- `Formula.IsSafe`, decided. -/
def isSafeB (φ : Formula) : Bool := safeB [] φ

end Dogwood.Eval
