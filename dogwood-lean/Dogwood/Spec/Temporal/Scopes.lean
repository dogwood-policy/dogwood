import Dogwood.Spec.Temporal.Syntax

/-!
# Temporal conditions: every monitoring scope varies with the timepoint

A *monitoring scope* is a part of a condition that is evaluated at more than one timepoint: each
top-level conjunct of a leaf, each temporal operator's body, both operands of `since`, each
`exists` body, and each aggregation's `where` body. A scope whose truth cannot change from one
timepoint to another of the same decision monitors nothing: `formerly within 1h (5 > 3)` is
just `5 > 3`. Such a condition is almost always a mistake, so validation rejects it
(`Formula.MonitorsTime`; guide chapter 8, §5.4, "tp-dependence").

A condition *varies with the timepoint* (`Formula.Varies`) when it contains a predicate, `tp`,
an aggregate, a temporal operator, or an `exists`, or compares a variable that varies. The
variables that vary are those bound by `exists` and, for a `sum`, its summand, and the variables
the leaf's top-level predicates bind outside aggregation bodies (`Formula.ruleWideBinders`).
Literals and request-side terms denote the same value at every timepoint of a decision.

This rule has no semantic consequence: a condition that breaks it has a meaning, and the
theorems do not use it. Its boundary is the reference validator's
(`extension/temporal/validate.rs`, `check_tp_dependence`), including the aggregates that are
atoms of a compound operand.

`Formula.monitorsTimeB` decides it (`Dogwood.Thm.monitorsTimeB_iff`).
-/

namespace Dogwood.Spec.Temporal

/-- The top-level conjuncts of a condition. -/
def Formula.conjuncts : Formula → List Formula
  | .and φ ψ => φ.conjuncts ++ ψ.conjuncts
  | φ => [φ]

/-- The variables predicates bind for the whole condition: predicate-field variables in
positive position, outside aggregation bodies (`collect_rule_wide_tp_binders`). -/
def Formula.ruleWideBinders : Formula → List VarName
  | .and φ ψ | .since φ _ ψ => φ.ruleWideBinders ++ ψ.ruleWideBinders
  | .formerly _ φ | .previous _ φ | .exist _ φ => φ.ruleWideBinders
  | .pred _ _ args => args.filterMap fun
      | (_, .var x) => some x
      | _ => none
  | .not _ | .cmp _ _ _ | .tp _ => []

/-- A term varies with the timepoint: an aggregate, a variable of `E`, or a compound with an
operand that does. -/
def Term.Varies (E : List VarName) : Term → Prop
  | .var x => x ∈ E
  | .agg _ => True
  | .arith _ l r => l.Varies E ∨ r.Varies E
  | _ => False

/-- The condition varies with the timepoint. -/
def Formula.Varies (E : List VarName) : Formula → Prop
  | .pred _ _ _ | .tp _ => True
  | .cmp _ l r => l.Varies E ∨ r.Varies E
  | .not φ => φ.Varies E
  | .and φ ψ => φ.Varies E ∨ ψ.Varies E
  | .formerly _ _ | .previous _ _ | .since _ _ _ | .exist _ _ => True

mutual

/-- Every monitoring scope inside the condition varies with the timepoint. -/
def Formula.ScopesVary (E : List VarName) : Formula → Prop
  | .pred _ _ _ | .tp _ => True
  | .cmp _ l r => l.ScopesVary E ∧ r.ScopesVary E
  | .not φ => φ.ScopesVary E
  | .and φ ψ => φ.ScopesVary E ∧ ψ.ScopesVary E
  | .formerly _ φ | .previous _ φ => φ.Varies E ∧ φ.ScopesVary E
  | .since φ _ ψ => φ.Varies E ∧ φ.ScopesVary E ∧ ψ.Varies E ∧ ψ.ScopesVary E
  | .exist x φ => φ.Varies (x.name :: E) ∧ φ.ScopesVary (x.name :: E)

/-- Every aggregation body of an operand varies with the timepoint, and so do the scopes inside
it. For a `sum`, the summed variable counts as varying. -/
def Term.ScopesVary (E : List VarName) : Term → Prop
  | .agg (.count _ body) => body.Varies E ∧ body.ScopesVary E
  | .agg (.sum s _ body) => body.Varies (s :: E) ∧ body.ScopesVary (s :: E)
  | .arith _ l r => l.ScopesVary E ∧ r.ScopesVary E
  | _ => True

end

/-- Every monitoring scope of a leaf varies with the timepoint. -/
def Formula.MonitorsTime (φ : Formula) : Prop :=
  ∀ c ∈ φ.conjuncts, c.Varies φ.ruleWideBinders ∧ c.ScopesVary φ.ruleWideBinders

end Dogwood.Spec.Temporal
