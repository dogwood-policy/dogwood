import Dogwood.Spec.EventSchema
import Dogwood.Spec.Provider
import Dogwood.Spec.Temporal.Typing

/-!
# Condition expressions

A Dogwood condition is a Cedar expression with two kinds of **leaf** Cedar
cannot express: a temporal condition (a `temporal { … }` marker, as a whole
clause or inline) and an information-provider invocation. `Expr` is Cedar's
abstract syntax (`Cedar.Spec.Expr`) extended with exactly those two leaves;
every other constructor is Cedar's, with Cedar's meaning.

This is the abstract syntax *after* the front end: macros expanded, surface
operators desugared to Cedar's (`!=`, `>`, `>=`, extension methods), and
`guardrails { E }` read as `when { E }`. The reference implementation's
lowering then *hoists* each leaf to a `context.<id>` attribute that it fills
at decision time; this specification gives each leaf its value directly (see
`Dogwood.Spec.Evaluator`).
-/

namespace Dogwood.Spec

open Cedar.Spec (Prim Var UnaryOp BinaryOp Attr ExtFun)

inductive Expr where
  | lit (p : Prim)
  | var (v : Var)
  | ite (cond : Expr) (thenExpr : Expr) (elseExpr : Expr)
  | and (a : Expr) (b : Expr)
  | or (a : Expr) (b : Expr)
  | unaryApp (op : UnaryOp) (expr : Expr)
  | binaryApp (op : BinaryOp) (a : Expr) (b : Expr)
  | getAttr (expr : Expr) (attr : Attr)
  | hasAttr (expr : Expr) (attr : Attr)
  | extHasAttr (expr : Expr) (attr : Attr) (attrs : List Attr)
  | set (ls : List Expr)
  | record (map : List (Attr × Expr))
  | call (xfn : ExtFun) (args : List Expr)
  /-- A temporal condition. Its value is a `Bool`: whether it holds at the
  decision timepoint. -/
  | temporal (φ : Temporal.Formula)
  /-- An information-provider invocation. Its value is the provider's output. -/
  | provider (c : Provider.Call)
deriving Repr, Inhabited

mutual

/-- Every Cedar expression is a Dogwood expression without leaves. -/
def Expr.ofCedar : Cedar.Spec.Expr → Expr
  | .lit p => .lit p
  | .var v => .var v
  | .ite c t f => .ite (Expr.ofCedar c) (Expr.ofCedar t) (Expr.ofCedar f)
  | .and a b => .and (Expr.ofCedar a) (Expr.ofCedar b)
  | .or a b => .or (Expr.ofCedar a) (Expr.ofCedar b)
  | .unaryApp op x => .unaryApp op (Expr.ofCedar x)
  | .binaryApp op a b => .binaryApp op (Expr.ofCedar a) (Expr.ofCedar b)
  | .getAttr x a => .getAttr (Expr.ofCedar x) a
  | .hasAttr x a => .hasAttr (Expr.ofCedar x) a
  | .extHasAttr x a as => .extHasAttr (Expr.ofCedar x) a as
  | .set xs => .set (Expr.ofCedarList xs)
  | .record axs => .record (Expr.ofCedarRecord axs)
  | .call f xs => .call f (Expr.ofCedarList xs)

def Expr.ofCedarList : List Cedar.Spec.Expr → List Expr
  | [] => []
  | x :: xs => Expr.ofCedar x :: Expr.ofCedarList xs

def Expr.ofCedarRecord : List (Attr × Cedar.Spec.Expr) → List (Attr × Expr)
  | [] => []
  | (a, x) :: axs => (a, Expr.ofCedar x) :: Expr.ofCedarRecord axs

end

instance : Coe Cedar.Spec.Expr Expr := ⟨Expr.ofCedar⟩

/-- A leaf of a condition expression. -/
abbrev Leaf := Temporal.Formula ⊕ Provider.Call

mutual

/-- The leaves an expression contains, in evaluation order. -/
def Expr.leaves : Expr → List Leaf
  | .lit _ | .var _ => []
  | .ite a b c => Expr.leaves a ++ Expr.leaves b ++ Expr.leaves c
  | .and a b | .or a b | .binaryApp _ a b => Expr.leaves a ++ Expr.leaves b
  | .unaryApp _ a | .getAttr a _ | .hasAttr a _ | .extHasAttr a _ _ => Expr.leaves a
  | .set xs | .call _ xs => Expr.leavesList xs
  | .record axs => Expr.leavesRecord axs
  | .temporal φ => [.inl φ]
  | .provider c => [.inr c]

def Expr.leavesList : List Expr → List Leaf
  | [] => []
  | x :: xs => Expr.leaves x ++ Expr.leavesList xs

def Expr.leavesRecord : List (Attr × Expr) → List Leaf
  | [] => []
  | (_, x) :: axs => Expr.leaves x ++ Expr.leavesRecord axs

end

/-! ## Guards

A temporal term may read an optional attribute of the request context, or of the principal or
resource, only where the Cedar part of the rule has tested it present with `has`
(`Dogwood.Spec.Temporal.Formula.WellTyped`). `Expr.leafFacts` computes, for each leaf, the
attribute paths tested present at its position: the leaf is evaluated by Cedar only after those
tests held (`Dogwood.Thm.evaluate_congr_facts`).

A test establishes a fact when it is `has` on an attribute chain rooted at `context`,
`principal` or `resource`: `context has input`, or `context.input has amount`. Cedar's
`context has input.amount` (one `extHasAttr` node) establishes both, as the conjunction
`context has input && context.input has amount` it abbreviates would. A conjunction establishes
the facts of both operands.
Facts flow from the left operand of `&&` to the right, and from the condition of `if` to its
`then` branch, because Cedar evaluates those only when the left operand or the condition is
`true`. -/

/-- The attribute chain an expression reads: a request variable, then attribute names. -/
def Expr.attrChain? : Expr → Option (Cedar.Spec.Var × Path)
  | .var v => some (v, [])
  | .getAttr x a => (Expr.attrChain? x).map fun (v, p) => (v, p ++ [a])
  | _ => none

/-- The fact a `has` test on an attribute chain establishes. -/
def Expr.hasFact? (x : Expr) (a : Attr) : Option Temporal.Guard :=
  match Expr.attrChain? x with
  | some (.context, p) => some (.context (p ++ [a]))
  | some (.principal, p) => some (.scope .principal (p ++ [a]))
  | some (.resource, p) => some (.scope .resource (p ++ [a]))
  | _ => none

/-- The facts `x has a.b.c` establishes: one for each prefix of the path, as for
`x has a && x.a has b && x.a.b has c`. -/
def Expr.extHasFacts (x : Expr) : Attr → List Attr → List Temporal.Guard
  | a, [] => (Expr.hasFact? x a).toList
  | a, b :: rest => (Expr.hasFact? x a).toList ++ Expr.extHasFacts (.getAttr x a) b rest

/-- The facts an expression establishes when it evaluates to `true`. -/
def Expr.facts : Expr → List Temporal.Guard
  | .hasAttr x a => (Expr.hasFact? x a).toList
  | .extHasAttr x a as => Expr.extHasFacts x a as
  | .and a b => Expr.facts a ++ Expr.facts b
  | _ => []

mutual

/-- Each leaf of the expression, in evaluation order, with the facts established at its
position, given the facts `F` established before the expression. -/
def Expr.leafFacts (F : List Temporal.Guard) : Expr → List (Leaf × List Temporal.Guard)
  | .lit _ | .var _ => []
  | .ite a b c => Expr.leafFacts F a ++ Expr.leafFacts (F ++ Expr.facts a) b ++ Expr.leafFacts F c
  | .and a b => Expr.leafFacts F a ++ Expr.leafFacts (F ++ Expr.facts a) b
  | .or a b | .binaryApp _ a b => Expr.leafFacts F a ++ Expr.leafFacts F b
  | .unaryApp _ a | .getAttr a _ | .hasAttr a _ | .extHasAttr a _ _ => Expr.leafFacts F a
  | .set xs | .call _ xs => Expr.leafFactsList F xs
  | .record axs => Expr.leafFactsRecord F axs
  | .temporal φ => [(.inl φ, F)]
  | .provider c => [(.inr c, F)]

def Expr.leafFactsList (F : List Temporal.Guard) : List Expr → List (Leaf × List Temporal.Guard)
  | [] => []
  | x :: xs => Expr.leafFacts F x ++ Expr.leafFactsList F xs

def Expr.leafFactsRecord (F : List Temporal.Guard) :
    List (Attr × Expr) → List (Leaf × List Temporal.Guard)
  | [] => []
  | (_, x) :: axs => Expr.leafFacts F x ++ Expr.leafFactsRecord F axs

end

/-! ## Reading the request context

The Cedar part of a rule may read `context` only through its attributes, and not through the
attributes that lowering reserves for the leaves (`Dogwood.Spec.PolicySet.lowered`). So a rule
evaluates the same on the request context as authored and on the context that lowering extends
with the leaves' values (`Dogwood.Thm.evaluate_lower`). -/

/-- The expression is the request variable `context`. -/
def Expr.isContext : Expr → Bool
  | .var .context => true
  | _ => false

mutual

/-- Every occurrence of `context` in the expression is the operand of an attribute access or a
`has` test, on an attribute outside `reserved`. -/
def Expr.ReadsContext (reserved : List Attr) : Expr → Prop
  | .lit _ => True
  | .var v => v ≠ .context
  | .getAttr x a | .hasAttr x a | .extHasAttr x a _ =>
    if x.isContext then a ∉ reserved else Expr.ReadsContext reserved x
  | .unaryApp _ x => Expr.ReadsContext reserved x
  | .ite a b c => Expr.ReadsContext reserved a ∧ Expr.ReadsContext reserved b ∧
      Expr.ReadsContext reserved c
  | .and a b | .or a b | .binaryApp _ a b =>
    Expr.ReadsContext reserved a ∧ Expr.ReadsContext reserved b
  | .set xs | .call _ xs => Expr.ReadsContextList reserved xs
  | .record axs => Expr.ReadsContextRecord reserved axs
  | .temporal _ | .provider _ => True

def Expr.ReadsContextList (reserved : List Attr) : List Expr → Prop
  | [] => True
  | x :: xs => Expr.ReadsContext reserved x ∧ Expr.ReadsContextList reserved xs

def Expr.ReadsContextRecord (reserved : List Attr) : List (Attr × Expr) → Prop
  | [] => True
  | (_, x) :: axs => Expr.ReadsContext reserved x ∧ Expr.ReadsContextRecord reserved axs

end

end Dogwood.Spec
