import Dogwood.Frontend.Syntax

/-!
# The temporal static checks

The crate's `extension/temporal/check.rs`, with the `experimental-arithmetic` feature on, so
that the arithmetic gate (`reject_arithmetic_unless_enabled`) accepts everything (the crate's
default build has it off: arithmetic is experimental). Three passes check one temporal block:

* `checkCondition` (crate `check_condition`): aggregates and arithmetic only in comparison
  operands, an aggregate as the whole operand or a leaf of an arithmetic one (never a predicate
  argument or an array element); no binder named after a Cedar request variable; every
  `exists` variable range-restricted by its body; for every aggregation, the summand is one of
  its `for` variables, every free variable of its body is bound, and every `for` variable occurs
  in the body and is range-restricted by it;
* `checkLeafClosed` (crate `check_leaf_closed`): no free variable;
* `checkDemands` (crate `check_demands`): within each `&&` chain, left to right, every conjunct
  reads only variables the conjuncts before it restrict (or the chain's seed), recursively.

Range restriction (`condRR`, crate `collect_range_restricted`) is computed without regard to
what the restricting atom reads: a binding equality `x == t` restricts `x` whatever `t` reads,
and the demands pass checks separately that `t`'s variables are restricted before it.

The crate's sets (`BTreeSet<String>`) are lists here; where a message names one element of a
set, it names the least, as the crate's sorted iteration does. Lean's order on strings is the
crate's (code points, which UTF-8 bytes preserve).

A condition that still holds a macro call or sigil is checked only partly (the crate's "punt"
to the post-expansion re-run); after expansion none does.
-/

namespace Dogwood.Frontend.Macros

open Surface.Temporal

/-! ## Sets of names -/

/-- The least element of a list (crate: the first element of a `BTreeSet` in iteration
order). -/
def least : List String → Option String
  | [] => none
  | x :: xs =>
    match least xs with
    | none => some x
    | some y => some (if x < y then x else y)

/-- Remove a name from a set. -/
def without (xs : List String) (n : String) : List String := xs.filter (· != n)

/-- The concrete name of a binder slot, if it has one. -/
def slotName? : BinderSlot → Option String
  | .name n => some n
  | _ => none

/-- The concrete names of a `for` list. -/
def slotNames (vs : List TypedBinder) : List String := vs.filterMap (slotName? ·.slot)

/-- A set without the concrete names of a `for` list. -/
def withoutAll (xs : List String) (vs : List TypedBinder) : List String :=
  xs.filter fun y => !(slotNames vs).contains y

/-- The names of a binder slot as a `for` list prints them (crate `fmt_for_vars`). -/
def fmtForVars (vs : List TypedBinder) : String :=
  ", ".intercalate (vs.map fun v => match v.slot with
    | .name s => s
    | .paramRef p => s!"?{p}"
    | .binderRef b => s!"${b}")

/-! ## Free variables (crate `collect_free`, `collect_term_var`) -/

mutual

/-- The free variables of a condition (crate `collect_free`). A binder removes its own name;
a macro call or sigil is opaque. -/
def condFree : Condition → List String
  | ⟨_, k⟩ => kindFree k

def kindFree : ConditionKind → List String
  | .and l r => condFree l ++ condFree r
  | .or l r => condFree l ++ condFree r
  | .not c => condFree c
  | .formerly _ c => condFree c
  | .previous _ c => condFree c
  | .since l _ r => condFree l ++ condFree r
  | .predicate ⟨_, _, _, _, args⟩ => argsFree args
  | .refine b fs _ => condFree b ++ argsFree fs
  | .comparison _ l r => termVars l ++ termVars r
  | .tp v => match v with
    | .name n => [n]
    | _ => []
  | .exists v b => match v.slot with
    | .name n => without (condFree b) n
    | _ => condFree b
  | .call _ => []
  | .sigilRef _ _ => []

def argsFree : List NamedArg → List String
  | [] => []
  | ⟨_, t⟩ :: rest => termVars t ++ argsFree rest

/-- The variables a term uses (crate `collect_term_var`). An aggregate exposes its body's free
variables other than its `for` variables. -/
def termVars : Term → List String
  | .var x => [x]
  | .array items => termsVars items
  | .arith _ l r => termVars l ++ termVars r
  | .agg ⟨_, k⟩ => aggVars k
  | _ => []

def termsVars : List Term → List String
  | [] => []
  | t :: rest => termVars t ++ termsVars rest

def aggVars : AggExprKind → List String
  | .sum _ vs b => withoutAll (condFree b) vs
  | .count vs b => withoutAll (condFree b) vs
  | .call _ => []

end

/-! ## Range restriction (crate `collect_range_restricted`, `eq_restricted_var`) -/

mutual

/-- The term holds a wildcard, as itself, in a compound or in an array (crate
`term_contains_wildcard`). -/
def termHasWildcard : Term → Bool
  | .wildcard => true
  | .arith _ l r => termHasWildcard l || termHasWildcard r
  | .array items => termsHaveWildcard items
  | _ => false

def termsHaveWildcard : List Term → Bool
  | [] => false
  | t :: rest => termHasWildcard t || termsHaveWildcard rest

end

/-- A term that can be the value side of a binding equality: neither a variable nor a wildcard,
nor a compound holding a wildcard. -/
def isRestrictor : Term → Bool
  | .var _ => false
  | .wildcard => false
  | t@(.arith _ _ _) => !termHasWildcard t
  | _ => true

/-- The variable an equality restricts: exactly one operand is a bare variable, and the other
can be a value side (crate `eq_restricted_var`). -/
def eqRestrictedVar (l r : Term) : Option String :=
  match l, r with
  | .var _, .var _ => none
  | .var n, r => if isRestrictor r then some n else none
  | l, .var n => if isRestrictor l then some n else none
  | _, _ => none

/-- The value side of a binding equality on `x`. -/
def valueSide (x : String) (l r : Term) : Term :=
  match l with
  | .var n => if n == x then r else l
  | _ => l

/-- The variables a list of predicate arguments names bare. -/
def argVarNames (args : List NamedArg) : List String :=
  args.filterMap fun a => match a.value with
    | .var n => some n
    | _ => none

mutual

/-- The variables a positive atom of the condition restricts (crate
`collect_range_restricted`). -/
def condRR : Condition → List String
  | ⟨_, k⟩ => kindRR k

def kindRR : ConditionKind → List String
  | .and l r => condRR l ++ condRR r
  | .not _ => []
  | .predicate ⟨_, _, _, _, args⟩ => argVarNames args
  | .tp v => match v with
    | .name n => [n]
    | _ => []
  | .comparison op l r => match op with
    | .eq => (eqRestrictedVar l r).toList
    | _ => []
  | .formerly _ b => condRR b
  | .previous _ b => condRR b
  | .since _ _ r => condRR r
  | .exists v b => match v.slot with
    | .name n => without (condRR b) n
    | _ => condRR b
  | .refine b fs _ => condRR b ++ argVarNames fs
  | .or _ _ => []
  | .call _ => []
  | .sigilRef _ _ => []

end

/-! ## Unresolved macro syntax (crate `body_has_sigil`, `term_has_sigil`) -/

mutual

def condHasSigil : Condition → Bool
  | ⟨_, k⟩ => kindHasSigil k

def kindHasSigil : ConditionKind → Bool
  | .call _ => true
  | .sigilRef _ _ => true
  | .and l r => condHasSigil l || condHasSigil r
  | .or l r => condHasSigil l || condHasSigil r
  | .since l _ r => condHasSigil l || condHasSigil r
  | .not c => condHasSigil c
  | .formerly _ c => condHasSigil c
  | .previous _ c => condHasSigil c
  | .exists _ c => condHasSigil c
  | .refine b fs _ => condHasSigil b || argsHaveSigil fs
  | .comparison _ l r => termHasSigil l || termHasSigil r
  | .predicate ⟨_, _, _, _, args⟩ => argsHaveSigil args
  | .tp v => match v with
    | .name _ => false
    | _ => true

def argsHaveSigil : List NamedArg → Bool
  | [] => false
  | ⟨_, t⟩ :: rest => termHasSigil t || argsHaveSigil rest

def termHasSigil : Term → Bool
  | .paramRef _ => true
  | .binderRef _ => true
  | .array items => termsHaveSigil items
  | .arith _ l r => termHasSigil l || termHasSigil r
  | .agg ⟨_, k⟩ => aggHasSigil k
  | _ => false

def termsHaveSigil : List Term → Bool
  | [] => false
  | t :: rest => termHasSigil t || termsHaveSigil rest

def aggHasSigil : AggExprKind → Bool
  | .call _ => true
  | .sum _ _ b => condHasSigil b
  | .count _ b => condHasSigil b

end

/-! ## The scoping pass (crate `check_condition`) -/

def aggMisplacedMsg : String :=
  "an aggregate (`sum`/`count`) may appear only as the immediate operand of a comparison, \
  not as a predicate-argument value or nested in another term"

def arithMisplacedMsg : String :=
  "arithmetic (`+`/`-`/`*`) may appear only as the immediate operand of a comparison, \
  not as a predicate-argument value or nested in another term"

mutual

/-- Reject an aggregate or arithmetic anywhere in a term that is not a comparison operand
(crate `reject_nested_agg`). -/
def rejectNestedAgg : Term → Except String Unit
  | .agg _ => throw aggMisplacedMsg
  | .array items => rejectNestedAggs items
  | .arith _ _ _ => throw arithMisplacedMsg
  | _ => pure ()

def rejectNestedAggs : List Term → Except String Unit
  | [] => pure ()
  | t :: rest => do rejectNestedAgg t; rejectNestedAggs rest

end

/-- The four Cedar request variables, which no binder may be named. -/
def reservedBinderNames : List String := ["principal", "action", "resource", "context"]

/-- Reject a binder named after a Cedar request variable (crate `reject_reserved_binder`). -/
def rejectReservedBinder : BinderSlot → Except String Unit
  | .name n =>
    if reservedBinderNames.contains n then
      throw s!"`{n}` is a reserved word and cannot be used as a binder name; `principal`, \
        `action`, `resource`, and `context` are the Cedar request variables — rename the \
        `exists` / `for` / `tp` variable"
    else pure ()
  | _ => pure ()

/-- `exists x. body` is accepted only if `x` is range-restricted by the body (crate
`check_exists_safe`); a sigil binder or a body with unresolved macro syntax is accepted, to be
checked after expansion. -/
def checkExistsSafe (v : TypedBinder) (body : Condition) : Except String Unit :=
  match v.slot with
  | .name n =>
    if condHasSigil body then pure ()
    else if (condRR body).contains n then pure ()
    else throw s!"existential variable `{n}` is not range-restricted by any positive atom in \
      the `exists` body; bind it with a predicate field (`P\{ f: {n} }`), a `tp({n})`, or an \
      equality (`(count …) == {n}`)"
  | _ => pure ()

/-- Whether a binder slot is still a macro sigil. -/
def slotIsSigil : BinderSlot → Bool
  | .name _ => false
  | _ => true

/-- The summand must be one of the `for` variables. -/
def checkSummand (summand : Option BinderSlot) (vs : List TypedBinder) : Except String Unit :=
  match summand with
  | some (.name bv) =>
    if !(slotNames vs).contains bv then
      throw s!"aggregation sums `{bv}`, which is not one of its `for` binders \
        ({fmtForVars vs}); the summed variable must appear in the `for` list (the sum is \
        computed over the `for` columns)"
    else pure ()
  | _ => pure ()

/-- Every free variable of the body must be in scope. -/
def checkAggBound (inner : List String) (vs : List TypedBinder) (body : Condition) :
    Except String Unit :=
  match least ((condFree body).filter fun y => !inner.contains y) with
  | none => pure ()
  | some unbound => throw s!"variable `{unbound}` is used in the aggregation body but is bound \
      by neither the `for` list ({fmtForVars vs}) nor an enclosing binder; add it to the `for` \
      list"

/-- Every `for` variable must occur in the body. -/
def checkForOccur (vs : List TypedBinder) (body : Condition) : Except String Unit :=
  (slotNames vs).forM fun n =>
    if !(condFree body).contains n then
      throw s!"`for`-variable `{n}` does not occur in the aggregation body ({fmtForVars vs}); \
        a group-by variable must be used in the `where` body, otherwise the grouping ranges \
        over an unbounded domain"
    else pure ()

/-- Every `for` variable must be range-restricted by the body. -/
def checkForRestricted (vs : List TypedBinder) (body : Condition) : Except String Unit :=
  (slotNames vs).forM fun n =>
    if !(condRR body).contains n then
      throw s!"aggregation `for`-variable `{n}` is not range-restricted by any positive atom \
        in the `where` body; bind it with a predicate field (`P\{ f: {n} }`), a `tp({n})`, or \
        an equality (`(count …) == {n}`) — an occurrence under a negation or in the left \
        operand of a `since` does not restrict"
    else pure ()

/-- Reject a `for` list with a reserved, unbound or unused variable, or a summand that is not
one of the `for` variables (crate `check_aggregation`, without its recursion into the body).
`none` when a binder is still a sigil (checked after expansion); otherwise the names in scope
in the body. -/
def checkAggregation (bound : List String) (summand : Option BinderSlot)
    (vs : List TypedBinder) (body : Condition) : Except String (Option (List String)) :=
  if (summand.map slotIsSigil).getD false || vs.any (slotIsSigil ·.slot) then pure none
  else do
    vs.forM fun v => rejectReservedBinder v.slot
    checkSummand summand vs
    checkAggBound (bound ++ slotNames vs) vs body
    checkForOccur vs body
    checkForRestricted vs body
    pure (some (bound ++ slotNames vs))

mutual

/-- The scoping pass (crate `check_condition`). `bound` holds the enclosing binders. -/
def checkCondition (bound : List String) : Condition → Except String Unit
  | ⟨_, k⟩ => checkKind bound k

def checkKind (bound : List String) : ConditionKind → Except String Unit
  | .and l r => do checkCondition bound l; checkCondition bound r
  | .not c => checkCondition bound c
  | .or l r => do checkCondition bound l; checkCondition bound r
  | .formerly _ b => checkCondition bound b
  | .previous _ b => checkCondition bound b
  | .since l _ r => do checkCondition bound l; checkCondition bound r
  | .refine b _ _ => checkCondition bound b
  | .exists v b => do
    rejectReservedBinder v.slot
    checkExistsSafe v b
    checkCondition (match v.slot with
      | .name n => bound ++ [n]
      | _ => bound) b
  | .comparison _ l r => do checkOperand bound l; checkOperand bound r
  | .predicate ⟨_, _, _, _, args⟩ => args.forM fun a => rejectNestedAgg a.value
  | .tp v => rejectReservedBinder v
  | .call _ => pure ()
  | .sigilRef _ _ => pure ()

/-- A comparison operand: an aggregate, bare or a leaf of a compound, is checked; any other
term may hold no aggregate (crate `check_operand`). -/
def checkOperand (bound : List String) : Term → Except String Unit
  | .agg ⟨_, k⟩ => checkAgg bound k
  | .arith _ l r => do checkOperand bound l; checkOperand bound r
  | t => rejectNestedAgg t

/-- An aggregation (crate `check_agg_expr`, `check_aggregation`). -/
def checkAgg (bound : List String) : AggExprKind → Except String Unit
  | .sum bv vs b => do
    match ← checkAggregation bound (some bv) vs b with
    | none => pure ()
    | some inner => checkCondition inner b
  | .count vs b => do
    match ← checkAggregation bound none vs b with
    | none => pure ()
    | some inner => checkCondition inner b
  | .call _ => pure ()

end

/-! ## Closedness (crate `check_leaf_closed`) -/

/-- A temporal leaf must have no free variable (crate `check_leaf_closed`). -/
def checkLeafClosed (c : Condition) : Except String Unit :=
  match least (condFree c) with
  | none => pure ()
  | some n => throw s!"variable `{n}` is free in this temporal condition (bound by no `exists` \
      binder or aggregation `for` list); a temporal condition must be closed — wrap it as \
      `exists ({n}: <type>). (…)`, or use `*` to match any value"

/-! ## Evaluation-order demands (crate `check_demands`) -/

/-- A filter's variables must be restricted before it (crate `reject_unmet_filter_var`). -/
def rejectUnmetFilter (fv rho : List String) : Except String Unit :=
  match least (fv.filter fun v => !rho.contains v) with
  | none => pure ()
  | some v => throw s!"variable `{v}` is used in a filter (a comparison or negation) that is \
      not range-restricted by a preceding conjunct; place a conjunct that binds `{v}` (a \
      predicate, `tp`, or a binding equality) before it"

/-- Where a binding equality's value side reads the variable `unmet`: an aggregate's body, or
the operands of any other value side (crate `check_conjunct_demands`). -/
def demandSite (value : Term) (unmet : String) : String :=
  match value with
  | .agg _ => s!"inside its aggregate operand (`{unmet}` is used in the aggregation body but \
      not bound by its `for` list)"
  | _ => "in its value operand"

/-- The demands of a binding equality on `bound`: its value side's variables (crate
`check_conjunct_demands`, its first arm). -/
def bindingDemands (bound : String) (l r : Term) (rho : List String) : Except String Unit :=
  match least ((termVars (valueSide bound l r)).filter fun v => !rho.contains v) with
  | none => pure ()
  | some unmet => throw s!"the equality binding `{bound}` reads `{unmet}` \
      {demandSite (valueSide bound l r) unmet}, and `{unmet}` is not range-restricted by a \
      preceding conjunct; place the conjunct that binds `{unmet}` before the equality, widening \
      the `exists` scope if needed"

/-- The demands of a `since`: the variables of its left that its anchor does not restrict. -/
def sinceDemands (l r : Condition) (rho : List String) : Except String Unit :=
  let anchor := condRR r
  match least ((condFree l).filter fun v => !anchor.contains v && !rho.contains v) with
  | none => pure ()
  | some unmet => throw s!"variable `{unmet}` is used in the left operand of a `since` but is \
      restricted neither by the `since` anchor (its right operand) nor by a preceding \
      conjunct; the left of a `since` is a per-step condition and cannot bind `{unmet}` — \
      restrict it in the anchor or in a conjunct before the `since`"

/-- Whether a condition is a conjunction. -/
def isAnd : Condition → Bool
  | ⟨_, .and _ _⟩ => true
  | _ => false

mutual

/-- One `&&` chain, left to right, from the seed `rho` (crate `check_chain`, without its
punt): each conjunct's demands, then its nested chains, then its restrictions join the seed. A
nested `&&` is flattened into the chain. -/
def chain (rho : List String) : Condition → Except String Unit
  | ⟨_, .and l r⟩ => do chain rho l; chain (rho ++ condRR l) r
  | ⟨_, k⟩ => do conjDemands rho k; descend rho k

/-- The demands of one conjunct (crate `check_conjunct_demands`): through `formerly`,
`previous` and `exists`, but not into a nested chain. -/
def conjDemands (rho : List String) : ConditionKind → Except String Unit
  | .comparison op l r =>
    match op, eqRestrictedVar l r with
    | .eq, some bound => bindingDemands bound l r rho
    | _, _ => rejectUnmetFilter (termVars l ++ termVars r) rho
  | .not c => rejectUnmetFilter (condFree c) rho
  | .since l _ r => sinceDemands l r rho
  | .formerly _ ⟨_, bk⟩ => match bk with
    | .and _ _ => pure ()
    | _ => conjDemands rho bk
  | .previous _ ⟨_, bk⟩ => match bk with
    | .and _ _ => pure ()
    | _ => conjDemands rho bk
  | .exists v ⟨_, bk⟩ => match bk with
    | .and _ _ => pure ()
    | _ => conjDemands (match v.slot with
      | .name n => without rho n
      | _ => rho) bk
  | _ => pure ()

/-- The chains nested in one conjunct, each from the seed at the conjunct's position, minus a
shadowing binder (crate `descend_nested_chains`). A chain with unresolved macro syntax is
skipped. -/
def descend (rho : List String) : ConditionKind → Except String Unit
  | .and l r =>
    if condHasSigil l || condHasSigil r then pure () else do chain rho l; chain (rho ++ condRR l) r
  | .or l r => do
    if condHasSigil l then pure () else chain rho l
    if condHasSigil r then pure () else chain rho r
  | .not ⟨_, k⟩ => descend rho k
  | .formerly _ b => if condHasSigil b then pure () else chain rho b
  | .previous _ b => if condHasSigil b then pure () else chain rho b
  | .since l _ r => do
    if condHasSigil l then pure () else chain (rho ++ condRR r) l
    if condHasSigil r then pure () else chain rho r
  | .exists v b =>
    if condHasSigil b then pure ()
    else chain (match v.slot with
      | .name n => without rho n
      | _ => rho) b
  | .comparison _ l r => do descendTerm rho l; descendTerm rho r
  | .refine ⟨_, k⟩ _ _ => descend rho k
  | .predicate _ => pure ()
  | .tp _ => pure ()
  | .call _ => pure ()
  | .sigilRef _ _ => pure ()

/-- The aggregates of a comparison operand, bare or leaves of a compound: each body is a chain
from the seed minus the aggregate's `for` variables. -/
def descendTerm (rho : List String) : Term → Except String Unit
  | .agg ⟨_, .sum _ vs b⟩ => if condHasSigil b then pure () else chain (withoutAll rho vs) b
  | .agg ⟨_, .count vs b⟩ => if condHasSigil b then pure () else chain (withoutAll rho vs) b
  | .arith _ l r => do descendTerm rho l; descendTerm rho r
  | _ => pure ()

end

/-- The evaluation-order check of a block (crate `check_demands`). -/
def checkDemands (c : Condition) : Except String Unit :=
  if condHasSigil c then pure () else chain [] c

/-- The static checks of one temporal block, in the crate's order: `check_condition`,
`check_leaf_closed`, `check_demands` (and the arithmetic gate, which accepts everything with
`experimental-arithmetic` on). -/
def checkLeaf (c : Condition) : Except String Unit := do
  checkCondition [] c
  checkLeafClosed c
  checkDemands c

end Dogwood.Frontend.Macros
