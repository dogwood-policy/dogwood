import Dogwood.Spec.Temporal.Syntax

/-!
# Temporal conditions: safety

A temporal condition is *safe* when every variable it quantifies over, by `exists` or by an
aggregation's `for` list, is range-restricted, and every atom that reads a variable reads one
that is range-restricted. Safety is what makes a condition monitorable: in every satisfying
assignment, each restricted variable takes one of finitely many values, which the trace and the
request determine. So every aggregate has a total, and every `exists` is witnessed by one of
finitely many candidates (`Dogwood.Thm.Monitorable`).

## Range restriction is a closure

A positive atom *restricts* a variable:

* a predicate argument `P{ f: x }` restricts `x` to the value of field `f` of the event at the
  timepoint being evaluated;
* `tp(x)` restricts `x` to the timepoint being evaluated;
* a binding equality `x == t` (or `t == x`), where `t` is neither a variable nor a wildcard nor
  a compound holding a wildcard, restricts `x` to the value `t` denotes, *provided the variables
  of `t` are restricted*.

Restrictions propagate through `&&`, the bodies of `formerly` and `previous`, the anchor of
`since`, and nested `exists` (minus the inner binder). A negation restricts nothing, and neither
does the left operand of `since`, which holds at every timepoint after the anchor and so may hold
vacuously.

Within a `&&` chain, the restricted variables are a **least closure** (`Formula.Restricts`):
starting from the variables restricted outside the chain, a conjunct adds the variables it
restricts once the variables it reads are in. The closure is the same however the conjuncts are
ordered, so safety is invariant under the commutativity and associativity of `&&`. The closure
is least, so a cycle restricts nothing: in `x == y + 1 && y == x - 1` neither equality's
variable is restricted unless something else restricts the other variable first
(`Dogwood.Examples.Acceptance.circular`).

This follows the range-restriction analysis of metric first-order temporal logic (Basin, Klaedtke,
Müller and Zălinescu, *Monitoring metric first-order temporal properties*, JACM 62(2), 2015),
extended with equalities whose value side computes from restricted variables.

## Safety

`Formula.Safe R φ` holds when, with the variables `R` restricted outside `φ`:

* a comparison reads only restricted variables, or the variable it restricts itself; inside a
  `&&` chain, the restricted variables include the chain's closure;
* a negation reads only restricted variables;
* the left operand of `since` reads only variables restricted outside or by the anchor;
* every `exists` variable is restricted by its body;
* every aggregation's `for` variables are restricted by its `where` body.

`Formula.IsSafe φ` is `φ.Safe` with nothing restricted outside: the condition of a temporal
leaf. The checks that need the schema, including that a condition is closed, are typing
(`Dogwood.Spec.Temporal.Typing`).

The reference checker (`extension/temporal/check.rs`) walks each `&&` chain left to right and
requires every conjunct's variables to be restricted by the conjuncts before it. That is
stricter: it rejects `x > 0 && P{ f: x }`, which this definition accepts. Reordering the
conjuncts does not always help, because the closure is computed over the nested chains too: a
conjunct may need, inside it, a variable that only a later conjunct restricts, while restricting
a variable that the later conjunct needs. In
`∃ y z. formerly (P{f: z} && !Q{g: y}) && formerly (Q{g: y} && !R{h: z})` each conjunct
restricts the variable the other one's negation reads, so the condition is safe, and no order of
its conjuncts, nor of the conjuncts of the nested chains, passes a left-to-right check
(`Dogwood.Thm.Frontend.Macros.Examples.interleaved_rejected`). A left-to-right check is sound for
this definition but not complete, even up to the order of conjuncts.

`Dogwood.Eval.safeB` decides safety (`Dogwood.Thm.safeB_iff`).
-/

namespace Dogwood.Spec.Temporal

/-! ## Free variables -/

mutual

/-- The variables a term uses. An aggregate exposes its body's free variables
other than its `for` variables; a compound, those of its operands. -/
def Term.fv : Term → List VarName
  | .var x => [x]
  | .agg a => a.fv
  | .arith _ l r => l.fv ++ r.fv
  | _ => []

def Aggregate.fv : Aggregate → List VarName
  | .count dom body | .sum _ dom body =>
    body.fv.filter fun x => !(dom.map (·.name)).contains x

/-- The free variables of a condition. -/
def Formula.fv : Formula → List VarName
  | .and φ ψ | .since φ _ ψ => φ.fv ++ ψ.fv
  | .not φ | .formerly _ φ | .previous _ φ => φ.fv
  | .pred _ _ args => Formula.argsFv args
  | .cmp _ l r => l.fv ++ r.fv
  | .exist x φ => φ.fv.filter (· != x.name)
  | .tp x => [x]

def Formula.argsFv : List (Path × Term) → List VarName
  | [] => []
  | (_, t) :: args => t.fv ++ Formula.argsFv args

end

/-! ## Binding equalities -/

/-- The term holds a wildcard, as itself or in a compound. -/
def Term.hasWildcard : Term → Bool
  | .wildcard => true
  | .arith _ l r => l.hasWildcard || r.hasWildcard
  | _ => false

/-- The variable an equality can restrict: `x == t` or `t == x`, where `t` is neither a variable
nor a wildcard, nor a compound holding a wildcard. A compound restricts only a bare variable
compared with it: a variable inside a compound is never restricted (there is no algebraic
solving). An equality between two variables restricts neither. -/
def eqRestricted? : Term → Term → Option VarName
  | .var _, .var _ => none
  | .var x, t => if t.hasWildcard then none else some x
  | t, .var x => if t.hasWildcard then none else some x
  | _, _ => none

/-- The value side of an equality that restricts `x`: the other operand. -/
def valueSide (x : VarName) (l r : Term) : Term :=
  match l with
  | .var z => if z = x then r else l
  | _ => l

/-! ## Restriction -/

/-- The variables a predicate's arguments name. -/
def predVars : List (Path × Term) → List VarName
  | [] => []
  | (_, .var x) :: args => x :: predVars args
  | _ :: args => predVars args


/-- `φ.Restricts R x`: when `φ` holds, and the variables of `R` are restricted, so is `x`.
For a `&&` chain this is the least set that contains `R` and is closed under what each
conjunct restricts; it is order-independent. -/
def Formula.Restricts (R : VarName → Prop) : Formula → VarName → Prop
  | .pred _ _ args, x => ∃ p, (p, Term.var x) ∈ args
  | .tp y, x => x = y
  | .cmp .eq l r, x => eqRestricted? l r = some x ∧ ∀ y ∈ (valueSide x l r).fv, R y
  | .cmp _ _ _, _ => False
  | .not _, _ => False
  | .formerly _ φ, x => φ.Restricts R x
  | .previous _ φ, x => φ.Restricts R x
  | .since _ _ ψ, x => ψ.Restricts R x
  | .exist y φ, x => x ≠ y.name ∧ φ.Restricts (fun z => z ≠ y.name ∧ R z) x
  | .and φ ψ, x =>
    ∀ S : VarName → Prop, (∀ z, R z → S z) →
      (∀ z, φ.Restricts S z → S z) → (∀ z, ψ.Restricts S z → S z) → S x

/-- The variables restricted at a position: those restricted outside it, and those it restricts
itself. -/
def Formula.Restricted (R : VarName → Prop) (φ : Formula) (x : VarName) : Prop :=
  R x ∨ φ.Restricts R x

/-! ## Safety -/

mutual

/-- `φ.Safe R`: `φ` is safe when the variables of `R` are restricted outside it. -/
def Formula.Safe (R : VarName → Prop) : Formula → Prop
  | .and φ ψ =>
    φ.Safe ((Formula.and φ ψ).Restricts R) ∧ ψ.Safe ((Formula.and φ ψ).Restricts R)
  | .not φ => (∀ y ∈ φ.fv, R y) ∧ φ.Safe R
  | .formerly _ φ => φ.Safe R
  | .previous _ φ => φ.Safe R
  | .since φ _ ψ =>
    ψ.Safe R ∧ (∀ y ∈ φ.fv, ψ.Restricted R y) ∧ φ.Safe (ψ.Restricted R)
  | .pred _ _ _ => True
  | .tp _ => True
  | .cmp op l r =>
    (∀ y ∈ l.fv ++ r.fv, (Formula.cmp op l r).Restricted R y) ∧ l.Safe R ∧ r.Safe R
  | .exist x φ =>
    φ.Restricts (fun z => z ≠ x.name ∧ R z) x.name ∧ φ.Safe (fun z => z ≠ x.name ∧ R z)

/-- An operand is safe: its aggregates are, including those that are leaves of a compound. -/
def Term.Safe (R : VarName → Prop) : Term → Prop
  | .agg a => a.Safe R
  | .arith _ l r => l.Safe R ∧ r.Safe R
  | _ => True

/-- An aggregation is safe: its body restricts every `for` variable, from the variables
restricted outside it, and is safe. -/
def Aggregate.Safe (R : VarName → Prop) : Aggregate → Prop
  | .count dom body | .sum _ dom body =>
    (∀ b ∈ dom, body.Restricts (fun z => z ∉ dom.map (·.name) ∧ R z) b.name) ∧
      body.Safe (fun z => z ∉ dom.map (·.name) ∧ R z)

end

/-- A temporal leaf's condition is safe: nothing is restricted outside it. -/
def Formula.IsSafe (φ : Formula) : Prop := φ.Safe fun _ => False

end Dogwood.Spec.Temporal
