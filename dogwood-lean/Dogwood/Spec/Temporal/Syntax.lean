import Dogwood.Spec.Event

/-!
# Temporal conditions: abstract syntax

The body of a `temporal { … }` block, after macro expansion: a past-only
fragment of metric first-order temporal logic (guide chapter 4; crate module
`extension::temporal::ast`).

The transient forms of the surface AST — macro calls, sigil references, field
refinements, `?w` windows — are removed by macro expansion and have no
counterpart here. Neither do array constants, which the grammar accepts but
lowering rejects (`ParsedPolicySet::reject_temporal_arrays`). The internal
disjunction synthesized by the pin relativization rewrite has none either:
the rewrite is an implementation of key-local semantics, which this
specification states directly (see `Dogwood.Spec.EventSchema`).

There is no disjunction, implication or `true` among the conditions: `&&` is
the loosest operator of the grammar, and a bare `true` is a term, not a
condition. A disjunction is written `!(!φ && !ψ)`.
-/

namespace Dogwood.Spec.Temporal

open Cedar.Spec (EntityUID)

/-- A variable bound by `exists` or an aggregation `for` list. `tp(x)` binds
nothing: it constrains a bound timepoint variable to the timepoint being
evaluated (`Formula.tp`), and range-restricts it for safety. -/
abbrev VarName := String

inductive TimeUnit where
  | seconds
  | minutes
  | hours
  | days
deriving Repr, DecidableEq, Inhabited

def TimeUnit.toSeconds : TimeUnit → Int
  | .seconds => 1
  | .minutes => 60
  | .hours => 3600
  | .days => 86400

/-- A `within <amount><unit>` window. The parser accepts any integer amount;
validation requires it to be positive, and the length to fit a `Long` and to be
at most the event schema's `max_window` (`Window.withinCap`). -/
structure Window where
  amount : Int
  unit : TimeUnit
deriving Repr, DecidableEq, Inhabited

/-- The window's length in seconds. -/
def Window.seconds (w : Window) : Int := w.amount * w.unit.toSeconds

/-- The window's length in ticks of the rate `rate`: the length the semantics compares a
difference of two timestamps with (`InWindow`). -/
def Window.ticks (w : Window) (rate : TickRate) : Int := w.seconds * rate.perSecond

inductive CmpOp where
  | eq
  | ne
  | lt
  | le
  | gt
  | ge
deriving Repr, DecidableEq, Inhabited

/-- An arithmetic operator of a compound comparison operand. -/
inductive ArithOp where
  | add
  | sub
  | mul
deriving Repr, DecidableEq, Inhabited

/-- The exact integer result of an arithmetic operator. -/
def ArithOp.apply : ArithOp → Int → Int → Int
  | .add, m, n => m + n
  | .sub, m, n => m - n
  | .mul, m, n => m * n

/-- A binder's declared type. Annotations are consulted by validation only;
evaluation never enumerates a type. -/
inductive BinderType where
  | timepoint
  /-- A concrete or entity type, e.g. `Long` or `Drupe::OAuthUser`. -/
  | named (path : List String)
deriving Repr, DecidableEq, Inhabited

/-- A declaration-site binder `(x : T)`. -/
structure Binder where
  name : VarName
  ty : BinderType
deriving Repr, DecidableEq, Inhabited

mutual

inductive Term where
  /-- An entity reference `Ns::Type::"id"`. -/
  | entity (uid : EntityUID)
  | long (i : Int64)
  /-- `decimal("…")`, with its payload as written. -/
  | decimal (text : String)
  | string (s : String)
  | bool (b : Bool)
  /-- `context.<path>`: a field of the current request's context (`path` is
  non-empty and excludes the leading `context`). -/
  | context (path : Path)
  /-- `principal` / `resource`, optionally followed by an attribute path. -/
  | scope (root : ScopeRoot) (path : Path)
  | var (x : VarName)
  /-- `*` (or `_`): matches any field value, binds nothing, never resolves. -/
  | wildcard
  /-- An aggregate. Well-placed only as a comparison operand, or a leaf of one. -/
  | agg (a : Aggregate)
  /-- `l + r`, `l - r`, `l * r`: a compound operand over `Long`s. Well-placed
  only as a comparison operand, or nested in one. The parser builds the tree
  left-associatively, with `*` binding tighter, and collapses an
  operator-free operand to its single term. -/
  | arith (op : ArithOp) (l r : Term)

inductive Aggregate where
  /-- `count for (g₁ : T₁), …, (gₙ : Tₙ). where φ` -/
  | count (domain : List Binder) (body : Formula)
  /-- `sum s for (g₁ : T₁), …, (gₙ : Tₙ). where φ` -/
  | sum (summand : VarName) (domain : List Binder) (body : Formula)

inductive Formula where
  /-- `φ && ψ` -/
  | and (φ ψ : Formula)
  /-- `!φ` -/
  | not (φ : Formula)
  /-- `formerly within W φ` -/
  | formerly (w : Window) (φ : Formula)
  /-- `previous within W φ` -/
  | previous (w : Window) (φ : Formula)
  /-- `φ since within W ψ`: `ψ` is the anchor. -/
  | since (φ : Formula) (w : Window) (ψ : Formula)
  /-- A predicate `Ns::Action::"a"::kind{ f₁: t₁, … }` matching the event at the
  timepoint being evaluated when it has the given action and kind; each named
  argument is a field path and a term, matched against the event's logged record,
  not its request context (`ArgsMatch`). -/
  | pred (action : EntityUID) (kind : String) (args : List (Path × Term))
  /-- `t₁ ⋈ t₂` -/
  | cmp (op : CmpOp) (l r : Term)
  /-- `exists (x : T). φ` -/
  | exist (x : Binder) (φ : Formula)
  /-- `tp(x)`: `x` is the timepoint being evaluated. -/
  | tp (x : VarName)

end

deriving instance Repr, Inhabited for Term
deriving instance Repr, Inhabited for Formula
deriving instance Repr for Aggregate

end Dogwood.Spec.Temporal
