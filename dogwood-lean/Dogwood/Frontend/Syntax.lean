import Dogwood.Spec.Temporal.Syntax
import Cedar.Spec.Template

/-!
# The parsers' output: the surface policy AST and the crate's temporal AST

The frontend starts where the parsers end. This module gives the Lean form of what the
`dogwood-language` crate's policy parser produces (`ast.rs`, `extension/temporal/ast.rs`): a
policy set of rules and macro definitions, whose conditions are Cedar-shaped surface expressions
that may hold `temporal { … }` blocks.

The types mirror the crate's one for one, so that each frontend stage can be ported against them
and compared with the crate's own observable for that stage. They keep what the crate keeps and
the specification drops:

* every node's **source span**: the macro expander names a fresh `$t` binder after the span of
  the call that introduces it (`<t>$<start>`, `macros/mod.rs`, `gensym_for`), so the expanded
  leaves depend on spans. A temporal block's spans are relative to the block's body;
* the **transient forms** that macro expansion removes: macro calls, `?p` and `$t` references,
  field refinements, `within ?w`;
* the **internal disjunction** `or`, which only the relativization rewrite builds;
* **array constants**, which lowering rejects (`reject_temporal_arrays`).

Where the crate's type is the specification's or cedar-lean's, the Lean type is reused: time
units, comparison and arithmetic operators and binder types (`Dogwood.Spec.Temporal`), and
literals, variables, like-pattern elements, entity types and the scope constraints of a policy
head (cedar-lean). A Cedar `Long` is an `Int64`, as in the crate.
-/

namespace Dogwood.Frontend

/-- A byte range `[start, end)` of a source text. -/
structure Span where
  start : Nat
  «end» : Nat
deriving Repr, DecidableEq, BEq, Inhabited

/-! ## The temporal AST -/

namespace Surface.Temporal

open Dogwood.Spec.Temporal (TimeUnit CmpOp ArithOp BinderType)

/-- A window `within <amount><unit>` (crate `Interval`). The amount is an integer literal, which
the parser rejects unless it fits `i64`. -/
structure Interval where
  amount : Int64
  unit : TimeUnit
deriving Repr, DecidableEq, BEq, Inhabited

/-- A window: concrete, or a macro body's `?w` parameter (crate `WithinSpec`). -/
inductive WithinSpec where
  | concrete (i : Interval)
  | paramRef (name : String)
deriving Repr, DecidableEq, BEq, Inhabited

/-- A position that names a binder: a name, or, in a macro body, `?p` or `$t`
(crate `BinderSlot`). -/
inductive BinderSlot where
  | name (n : String)
  | paramRef (name : String)
  | binderRef (name : String)
deriving Repr, DecidableEq, BEq, Inhabited

/-- A declaration-site binder `(x: T)` (crate `TypedBinder`). -/
structure TypedBinder where
  slot : BinderSlot
  ty : BinderType
deriving Repr, DecidableEq, BEq, Inhabited

/-- The sigil of a reference that stands for a whole condition in a macro body. -/
inductive Sigil where
  /-- `?p` -/
  | param
  /-- `$t` -/
  | binder
deriving Repr, DecidableEq, BEq, Inhabited

mutual

/-- A temporal condition and its span (crate `Condition`). -/
structure Condition where
  span : Span
  kind : ConditionKind

/-- The shape of a temporal condition (crate `ConditionKind`). -/
inductive ConditionKind where
  | and (left right : Condition)
  /-- Built only by the relativization rewrite; the parser never produces it. -/
  | or (left right : Condition)
  | not (inner : Condition)
  | formerly (within : WithinSpec) (body : Condition)
  | previous (within : WithinSpec) (body : Condition)
  /-- `left since within w right`; `right` is the anchor. -/
  | since (left : Condition) (within : WithinSpec) (right : Condition)
  | predicate (p : Predicate)
  | comparison (op : CmpOp) (left right : Term)
  | «exists» (var : TypedBinder) (body : Condition)
  | tp (var : BinderSlot)
  /-- A macro call in condition position (transient). -/
  | call (c : Call)
  /-- `?p` or `$t` standing for a condition, in a macro body (transient). -/
  | sigilRef (sigil : Sigil) (name : String)
  /-- `base{ f: t, … }`: a predicate refined with more arguments (transient). -/
  | refine (base : Condition) (fields : List NamedArg) (span : Span)

/-- A predicate `Ns::Action::"a"::kind{ f: t, … }` (crate `Predicate`). `namespace` holds the
action's entity type path, `Action` included. -/
structure Predicate where
  span : Span
  «namespace» : List String
  action : String
  kind : String
  args : List NamedArg

/-- A predicate argument `f: t`. `name` is the field path's text, each segment escaped (`\`
as `\\`, `.` as `\.`) and the segments joined by `.` (`fieldPathJoin`). -/
structure NamedArg where
  name : String
  value : Term

/-- A term (crate `Term`). -/
inductive Term where
  /-- `ty` is the entity type's text, `A::B`. -/
  | entity (ty id : String)
  | integer (i : Int64)
  | decimal (text : String)
  | string (s : String)
  | bool (b : Bool)
  /-- `context.p`, without the leading `context`. -/
  | contextField (path : List String)
  /-- `principal.p` or `resource.p`, the root included as the first segment. -/
  | scopeField (path : List String)
  | var (x : String)
  | wildcard
  /-- An array constant; lowering rejects it in a predicate argument or a comparison operand. -/
  | array (items : List Term)
  | agg (a : AggExpr)
  | arith (op : ArithOp) (left right : Term)
  /-- `?p` in a macro body (transient). -/
  | paramRef (name : String)
  /-- `$t` in a macro body (transient). -/
  | binderRef (name : String)

/-- An aggregation and its span (crate `AggExpr`). -/
structure AggExpr where
  span : Span
  kind : AggExprKind

/-- The shape of an aggregation (crate `AggExprKind`). -/
inductive AggExprKind where
  | sum (boundVar : BinderSlot) (forVars : List TypedBinder) (body : Condition)
  | count (forVars : List TypedBinder) (body : Condition)
  /-- A value-macro call in operand position (transient). -/
  | call (c : Call)

/-- A macro call `name(arg, …)` (crate `Call`). -/
structure Call where
  span : Span
  name : String
  args : List CallArg

/-- A macro call argument, tagged with the category it parsed as (crate `CallArg`). -/
inductive CallArg where
  | condition (c : Condition)
  | within (i : Interval)
  | term (t : Term)

end

deriving instance Repr, BEq for Condition, ConditionKind, Predicate, NamedArg, Term, AggExpr,
  AggExprKind, Call, CallArg

instance : Inhabited Term := ⟨.wildcard⟩
instance : Inhabited Condition := ⟨⟨default, .tp (.name "")⟩⟩

/-- A parsed `temporal { … }` block: its condition, and the span of its body in the policy
source, the base of the condition's spans (crate `Temporal`). -/
structure Block where
  condition : Condition
  span : Span
deriving Repr, BEq, Inhabited

end Surface.Temporal

/-! ## Field paths -/

/-- One segment of a field path's text: `\` as `\\`, `.` as `\.` (crate
`field_path::push_segment`). -/
def escapeSegment (s : String) : String :=
  String.join (s.toList.map fun c =>
    if c == '\\' then "\\\\" else if c == '.' then "\\." else String.singleton c)

/-- The text of a field path: its segments escaped and joined by `.` (crate `field_path::join`).
`["input", "user.id"]` is `input.user\.id`. -/
def fieldPathJoin (path : List String) : String :=
  ".".intercalate (path.map escapeSegment)

/-- The path a field path's text names: the text cut at its unescaped dots, with the escapes
dropped (crate `field_path::split`). It inverts `fieldPathJoin` on every non-empty path. -/
def fieldPathSplit (text : String) : List String :=
  let rec go : List Char → String → List String → List String
    | [], cur, acc => (acc ++ [cur])
    | '\\' :: c :: rest, cur, acc => go rest (cur.push c) acc
    | '.' :: rest, cur, acc => go rest "" (acc ++ [cur])
    | c :: rest, cur, acc => go rest (cur.push c) acc
  go text.toList "" []

namespace Surface.Temporal

/-- The argument's field path (crate `NamedArg::field_path`). -/
def NamedArg.fieldPath (a : NamedArg) : List String := fieldPathSplit a.name

end Surface.Temporal

/-! ## The surface policy AST -/

namespace Surface

open Cedar.Spec (Prim Var PatElem EntityType EntityUID ScopeTemplate SlotID)

/-- Dogwood's surface unary operators, before Cedar's desugaring (crate `UnOp`): negations,
`isEmpty`, the extension constructors, and the zero-argument extension methods. -/
inductive UnOp where
  | not | neg | isEmpty
  | decimal | datetime | duration | ip
  | isIpv4 | isIpv6 | isLoopback | isMulticast
  | toDate | toTime | toMilliseconds | toSeconds | toMinutes | toHours | toDays
deriving Repr, DecidableEq, BEq, Inhabited

/-- Dogwood's surface binary operators, before Cedar's desugaring (crate `BinOp`), including
`!=`, `>` and `>=`, and the one-argument extension methods. -/
inductive BinOp where
  | eq | notEq | less | lessEq | greater | greaterEq
  | and | or | add | sub | mul | «in»
  | contains | containsAll | containsAny | getTag | hasTag
  | isInRange | offset | durationSince
  | decimalLessThan | decimalLessEq | decimalGreater | decimalGreaterEq
deriving Repr, DecidableEq, BEq, Inhabited

mutual

/-- A Cedar condition expression with the extension hole, and its span (crate `Expr`). -/
structure Expr where
  kind : ExprKind
  span : Span

/-- The shape of a surface expression (crate `ExprKind`). The parser has mapped Cedar's
built-in functions and methods to `UnOp`/`BinOp`, and `x["k"]` to `getAttr`. -/
inductive ExprKind where
  | lit (l : Prim)
  | var (v : Var)
  /-- `?principal` or `?resource`, by that name. -/
  | slot (id : SlotID)
  /-- A `temporal { … }` block. -/
  | extension (t : Temporal.Block)
  | unaryApp (op : UnOp) (expr : Expr)
  | binaryApp (op : BinOp) (left right : Expr)
  | getAttr (expr : Expr) (attr : String)
  /-- `e has a.b.c`: a non-empty path. -/
  | hasAttr (expr : Expr) (attrs : List String)
  | like (expr : Expr) (pattern : List PatElem)
  | is (expr : Expr) (entityType : EntityType) (inExpr : Option Expr)
  | ite (cond thenExpr elseExpr : Expr)
  | set (items : List Expr)
  /-- A record literal; its entries in key order. -/
  | record (entries : List (String × Expr))
  /-- A call the parser did not recognize: a macro call (a single-segment name) or a provider
  invocation (a `::` name). -/
  | call (name : String) (args : List Expr)
  /-- A method the parser did not recognize: possibly a provider output method. -/
  | methodCall (receiver : Expr) (method : String) (args : List Expr)
  /-- `?p` in a `def cedar` body. -/
  | paramRef (name : String)

end

deriving instance Repr, BEq for Expr, ExprKind

instance : Inhabited Expr := ⟨⟨.lit (.bool true), default⟩⟩

/-- A policy head's action constraint, as Cedar's AST holds it (crate scope, Cedar
`ActionConstraint`): `action in X` and `action in [X, …]` are both `in`. -/
inductive ActionConstraint where
  | any
  | eq (entity : EntityUID)
  | «in» (entities : List EntityUID)
deriving Repr, DecidableEq, BEq, Inhabited

instance : Inhabited ScopeTemplate := ⟨.any⟩

/-- A policy head (crate `Scope`). A template slot is `ScopeTemplate`'s `slot "?principal"` or
`slot "?resource"`; lowering rejects it. -/
structure Scope where
  span : Span
  principal : ScopeTemplate
  action : ActionConstraint
  resource : ScopeTemplate
deriving Repr, DecidableEq, BEq, Inhabited

/-- A `when`/`unless` clause (crate `Cond`). The keyword is cedar-lean's `ConditionKind`. -/
structure Cond where
  span : Span
  keyword : Cedar.Spec.ConditionKind
  body : Expr
deriving Repr, BEq, Inhabited

/-- `@key` or `@key("value")`. -/
structure Annotation where
  key : String
  value : Option String
deriving Repr, DecidableEq, BEq, Inhabited

/-- A rule (crate `Policy`). -/
structure Policy where
  span : Span
  annotations : List Annotation
  effect : Cedar.Spec.Effect
  scope : Scope
  conditions : List Cond
deriving Repr, BEq, Inhabited

/-- A macro parameter `?name`. -/
structure MacroParam where
  span : Span
  name : String
deriving Repr, DecidableEq, BEq, Inhabited

/-- A macro body, parsed under its kind (crate `MacroBody`). -/
inductive MacroBody where
  /-- `def cedar`. -/
  | cedar (e : Expr)
  /-- `def temporal` with a condition body. -/
  | condition (c : Temporal.Condition)
  /-- `def temporal` with a value body: an aggregation, or arithmetic over aggregations. -/
  | value (t : Temporal.Term)
deriving Repr, BEq, Inhabited

/-- A macro definition (crate `MacroDef`). -/
structure MacroDef where
  span : Span
  name : String
  params : List MacroParam
  body : MacroBody
deriving Repr, BEq, Inhabited

/-- A parsed policy set: rules and macro definitions (crate `ast::PolicySet`). After expansion,
`defs` is empty. -/
structure PolicySet where
  policies : List Policy
  defs : List MacroDef
deriving Repr, BEq, Inhabited

end Surface

/-! ## Provider invocations -/

namespace Provider

/-- A provider (or method) argument (crate `extension::provider::ast::Arg`). A field path keeps
its root, `context`, `principal` or `resource`, as its first segment. -/
inductive Arg where
  | field (path : List String)
  | string (s : String)
  | integer (i : Int64)
  | decimal (text : String)
  | bool (b : Bool)
  | set (items : List Arg)
deriving Repr, BEq, Inhabited

/-- A provider invocation `Ns::Fn(args)` (crate `Invocation`). -/
structure Invocation where
  span : Span
  function : List String
  args : List Arg
deriving Repr, BEq, Inhabited

/-- The declaration key of an invocation, `Ns::Fn`. -/
def Invocation.key (i : Invocation) : String := "::".intercalate i.function

/-- A provider output method `.m(args)` (crate `MethodCall`). -/
structure MethodCall where
  span : Span
  name : String
  args : List Arg
deriving Repr, BEq, Inhabited

end Provider

end Dogwood.Frontend
