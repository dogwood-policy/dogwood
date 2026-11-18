import Dogwood.Frontend.Types
import Dogwood.Frontend.Balanced

/-!
# The passes over each temporal leaf (WP5)

Three passes rewrite each hoisted temporal leaf after cedarify, in this order:

* **pin injection** (crate `event_schema/pin.rs`, `inject_pins`): every predicate that names a
  derived event gets one argument per pin of that event, appended unconditionally;
* **timepoint unordering** (crate `extension/temporal/timepoints.rs`, `unorder_timepoints`): the
  executable form of a leaf, in which every comparison that orders a timepoint variable, or
  computes with one, is the false comparison `0 == 1`;
* **relativization** (crate `event_schema/relativize.rs`, `relativize_condition`): when the
  schema has universal symmetric pins, the rewrite whose verdict with every timepoint visible is
  the authored leaf's verdict over the key's own events.

Each function follows the crate's traversal: which nodes it descends, which it copies,
the spans it gives the nodes it builds, and, for relativization, the order in which it draws
fresh names. The specification states key-local semantics directly, by visibility
(`Dogwood.Spec.EventSchema.Visible`); `Dogwood.Frontend.LeafPasses.Semantics` gives the
relativized leaves a meaning, and states the theorem that relates the two.
-/

namespace Dogwood.Frontend.LeafPasses

open Surface.Temporal
open Dogwood.Spec.Temporal (CmpOp BinderType)

/-! ## Pin injection -/

/-- The derived event a predicate names: the first with its namespace, action and kind (crate
`DerivedEventSchema::get`). -/
def eventOf (d : DerivedEventSchema) (ns : List String) (action kind : String) :
    Option DerivedEvent :=
  d.events.find? fun e => e.action == action && e.kind == kind && e.namespace == ns

/-- The request-side term a pin reads: a scope term for a `= principal…`/`= resource…` pin, a
context term for a `= context.…` pin (crate `inject_into_predicate`). -/
def pinTerm (p : Pin) : Term :=
  match p.root with
  | .scope => .scopeField p.contextPath
  | .context => .contextField p.contextPath

/-- The argument pin injection appends for a pin: the escaped text of the pinned field's path,
and the pin's request-side term. -/
def pinArg (p : Pin) : NamedArg := ⟨fieldPathJoin p.fieldPath, pinTerm p⟩

/-- The pins injected onto a predicate of the event `(ns, action, kind)`: the event's pins, or
none when no derived event has that name. -/
def pinsFor (d : DerivedEventSchema) (ns : List String) (action kind : String) : List Pin :=
  match eventOf d ns action kind with
  | some e => e.pins
  | none => []

/-- The predicate with the pins of its event appended. -/
def injectPred (d : DerivedEventSchema) (p : Predicate) : Predicate :=
  { p with args := p.args ++ (pinsFor d p.namespace p.action p.kind).map pinArg }

mutual

/-- Pin injection on a condition. It descends `&&`, `||`, `since`, `!`, `formerly`, `previous`,
`exists`, the base of a refinement, and the aggregates of comparison operands; it does not
descend predicate arguments. -/
def injectCond (d : DerivedEventSchema) : Condition → Condition
  | ⟨sp, k⟩ => ⟨sp, injectKind d k⟩

def injectKind (d : DerivedEventSchema) : ConditionKind → ConditionKind
  | .and l r => .and (injectCond d l) (injectCond d r)
  | .or l r => .or (injectCond d l) (injectCond d r)
  | .since l w r => .since (injectCond d l) w (injectCond d r)
  | .not c => .not (injectCond d c)
  | .formerly w c => .formerly w (injectCond d c)
  | .previous w c => .previous w (injectCond d c)
  | .exists x c => .exists x (injectCond d c)
  | .predicate p => .predicate (injectPred d p)
  | .refine b fs sp => .refine (injectCond d b) fs sp
  | .comparison op l r => .comparison op (injectTerm d l) (injectTerm d r)
  | .tp x => .tp x
  | .call c => .call c
  | .sigilRef s n => .sigilRef s n

/-- Pin injection on a comparison operand: the bodies of its aggregates, through arithmetic
(crate `inject_into_operand`). -/
def injectTerm (d : DerivedEventSchema) : Term → Term
  | .agg a => .agg (injectAgg d a)
  | .arith op l r => .arith op (injectTerm d l) (injectTerm d r)
  | t => t

def injectAgg (d : DerivedEventSchema) : AggExpr → AggExpr
  | ⟨sp, k⟩ => ⟨sp, injectAggKind d k⟩

def injectAggKind (d : DerivedEventSchema) : AggExprKind → AggExprKind
  | .sum v vs b => .sum v vs (injectCond d b)
  | .count vs b => .count vs (injectCond d b)
  | .call c => .call c

end

/-- Append each pin of a predicate's event to its arguments (crate `inject_pins`). It raises no
error. -/
def injectPins (schema : DerivedEventSchema) (c : Condition) : Result Condition :=
  pure (injectCond schema c)

/-! ## Timepoint unordering -/

/-- The binders in scope, innermost first: each name, and whether its declared type is
`Timepoint` (the crate keeps the same list innermost last). -/
abbrev TpScope := List (String × Bool)

/-- A binder's name and whether it is a timepoint. A binder still carrying a macro sigil binds no
name a term can refer to (crate `binding`). -/
def binding (b : TypedBinder) : String × Bool :=
  ((match b.slot with
    | .name n => n
    | _ => ""), b.ty == .timepoint)

/-- `x` is a timepoint: its innermost binder declares it `Timepoint`. A free name is not. -/
def isTimepoint (Γ : TpScope) (x : String) : Bool :=
  match Γ.find? (·.1 == x) with
  | some (_, t) => t
  | none => false

/-- The operand is a timepoint variable. -/
def isTimepointVar (Γ : TpScope) : Term → Bool
  | .var x => isTimepoint Γ x
  | _ => false

/-- The compound operand has a timepoint atom (crate `computes_with_timepoint`). -/
def computesWithTimepoint (Γ : TpScope) : Term → Bool
  | .arith _ l r => isTimepointVar Γ l || isTimepointVar Γ r ||
      computesWithTimepoint Γ l || computesWithTimepoint Γ r
  | _ => false

/-- The ordering operators. -/
def CmpOp.orders : CmpOp → Bool
  | .lt | .le | .gt | .ge => true
  | .eq | .ne => false

/-- The comparison `0 == 1`, which is false at every timepoint, with the span `sp`. -/
def constantFalse (sp : Span) : Condition := ⟨sp, .comparison .eq (.integer 0) (.integer 1)⟩

/-- The comparison is replaced by `0 == 1`: it orders a timepoint variable, or one of its
operands computes with one. -/
def unordersComparison (Γ : TpScope) (op : CmpOp) (l r : Term) : Bool :=
  computesWithTimepoint Γ l || computesWithTimepoint Γ r ||
    (CmpOp.orders op && (isTimepointVar Γ l || isTimepointVar Γ r))

mutual

/-- The executable form of a condition under the binders `Γ` (crate `rewrite`). It descends the
connectives, the temporal operators, `exists` and the aggregates of comparison operands; it
copies predicates, `tp`, refinements and the macro forms. -/
def unorderCond (Γ : TpScope) : Condition → Condition
  | ⟨sp, k⟩ => unorderKind Γ sp k

def unorderKind (Γ : TpScope) (sp : Span) : ConditionKind → Condition
  | .and l r => ⟨sp, .and (unorderCond Γ l) (unorderCond Γ r)⟩
  | .or l r => ⟨sp, .or (unorderCond Γ l) (unorderCond Γ r)⟩
  | .not c => ⟨sp, .not (unorderCond Γ c)⟩
  | .formerly w c => ⟨sp, .formerly w (unorderCond Γ c)⟩
  | .previous w c => ⟨sp, .previous w (unorderCond Γ c)⟩
  | .since l w r => ⟨sp, .since (unorderCond Γ l) w (unorderCond Γ r)⟩
  | .exists x c => ⟨sp, .exists x (unorderCond (binding x :: Γ) c)⟩
  | .comparison op l r =>
    let l' := unorderTerm Γ l
    let r' := unorderTerm Γ r
    if unordersComparison Γ op l' r' then constantFalse sp else ⟨sp, .comparison op l' r'⟩
  | .predicate p => ⟨sp, .predicate p⟩
  | .tp x => ⟨sp, .tp x⟩
  | .call c => ⟨sp, .call c⟩
  | .sigilRef s n => ⟨sp, .sigilRef s n⟩
  | .refine b fs rsp => ⟨sp, .refine b fs rsp⟩

/-- The executable form of a comparison operand (crate `rewrite_term`): its aggregates, through
arithmetic. -/
def unorderTerm (Γ : TpScope) : Term → Term
  | .agg a => .agg (unorderAgg Γ a)
  | .arith op l r => .arith op (unorderTerm Γ l) (unorderTerm Γ r)
  | t => t

def unorderAgg (Γ : TpScope) : AggExpr → AggExpr
  | ⟨sp, k⟩ => ⟨sp, unorderAggKind Γ k⟩

/-- An aggregate's `for` variables scope over its body, the last innermost (crate
`rewrite_agg`). -/
def unorderAggKind (Γ : TpScope) : AggExprKind → AggExprKind
  | .count vs b => .count vs (unorderCond ((vs.map binding).reverse ++ Γ) b)
  | .sum v vs b => .sum v vs (unorderCond ((vs.map binding).reverse ++ Γ) b)
  | .call c => .call c

end

mutual

/-- No comparison the pass reaches orders a timepoint variable or computes with one, under the
binders `Γ`: the pass leaves the condition as it is (`Dogwood.Thm.Frontend.unorderCond_eq_self`).
-/
def unorderFree (Γ : TpScope) : Condition → Bool
  | ⟨_, k⟩ => unorderFreeKind Γ k

def unorderFreeKind (Γ : TpScope) : ConditionKind → Bool
  | .and l r => unorderFree Γ l && unorderFree Γ r
  | .or l r => unorderFree Γ l && unorderFree Γ r
  | .not c => unorderFree Γ c
  | .formerly _ c => unorderFree Γ c
  | .previous _ c => unorderFree Γ c
  | .since l _ r => unorderFree Γ l && unorderFree Γ r
  | .exists x c => unorderFree (binding x :: Γ) c
  | .comparison op l r =>
    !unordersComparison Γ op l r && unorderFreeTerm Γ l && unorderFreeTerm Γ r
  | .predicate _ => true
  | .tp _ => true
  | .call _ => true
  | .sigilRef _ _ => true
  | .refine _ _ _ => true

def unorderFreeTerm (Γ : TpScope) : Term → Bool
  | .agg ⟨_, k⟩ => unorderFreeAgg Γ k
  | .arith _ l r => unorderFreeTerm Γ l && unorderFreeTerm Γ r
  | _ => true

def unorderFreeAgg (Γ : TpScope) : AggExprKind → Bool
  | .count vs b => unorderFree ((vs.map binding).reverse ++ Γ) b
  | .sum _ vs b => unorderFree ((vs.map binding).reverse ++ Γ) b
  | .call _ => true

end

/-- Replace every comparison that orders a timepoint, or computes with one, by `0 == 1` (crate
`unorder_timepoints`). It raises no error. -/
def unorderTimepoints (c : Condition) : Result Condition :=
  pure (unorderCond [] c)

/-! ## Relativization -/

/-- The condition implies that it matched a (pinned) event: its positive structure has a
predicate conjunct. It descends `&&` (either side), `exists`, and both sides of `||` (crate
`implies_mine`). -/
def impliesMine : Condition → Bool
  | ⟨_, .predicate _⟩ => true
  | ⟨_, .and l r⟩ => impliesMine l || impliesMine r
  | ⟨_, .or l r⟩ => impliesMine l && impliesMine r
  | ⟨_, .exists _ b⟩ => impliesMine b
  | _ => false

/-! ### The constructors the rewrite builds with -/

def mkAnd (sp : Span) (l r : Condition) : Condition := ⟨sp, .and l r⟩

/-- The left fold of `&&` over a non-empty list (crate `ands`). -/
def mkAnds (sp : Span) : List Condition → Condition
  | [] => ⟨sp, .comparison .eq (.integer 0) (.integer 0)⟩
  | c :: cs => cs.foldl (mkAnd sp) c

def mkNot (sp : Span) (c : Condition) : Condition := ⟨sp, .not c⟩

def mkTp (sp : Span) (x : String) : Condition := ⟨sp, .tp (.name x)⟩

def mkFormerly (sp : Span) (w : WithinSpec) (c : Condition) : Condition := ⟨sp, .formerly w c⟩

/-- The comparison of two variables. -/
def mkCmp (sp : Span) (op : CmpOp) (a b : String) : Condition :=
  ⟨sp, .comparison op (.var a) (.var b)⟩

/-- `(count for (x: Timepoint). where body)` as a comparison operand. -/
def mkCount (sp : Span) (x : String) (body : Condition) : Term :=
  .agg ⟨sp, .count [⟨.name x, .timepoint⟩] body⟩

/-- `agg == n`, the aggregate on the left (crate `cmp_agg_eq`). -/
def mkAggEq (sp : Span) (agg : Term) (n : String) : Condition :=
  ⟨sp, .comparison .eq agg (.var n)⟩

/-- `exists (x: Timepoint). body`. -/
def mkExistsTp (sp : Span) (x : String) (body : Condition) : Condition :=
  ⟨sp, .exists ⟨.name x, .timepoint⟩ body⟩

/-- `exists (x: Long). body`. -/
def mkExistsLong (sp : Span) (x : String) (body : Condition) : Condition :=
  ⟨sp, .exists ⟨.name x, .named ["Long"]⟩ body⟩

/-- One branch of μ: a predicate for the event carrying exactly the pinned correlations, each
pin's request-side term as pin injection writes it (crate `mu_branch`). -/
def muBranch (pins : List Pin) (sp : Span) (ev : DerivedEvent) : Condition :=
  ⟨sp, .predicate ⟨sp, ev.namespace, ev.action, ev.kind, pins.map pinArg⟩⟩

/-- μ, "an event of any declared kind of mine": the balanced `||` tree over one branch per
derived event, in the events' order (crate `mu`, `balancedFold`). -/
def mu (pins : List Pin) (first : DerivedEvent) (rest : List DerivedEvent) (sp : Span) :
    Condition :=
  balancedFold (fun l r => ⟨sp, .or l r⟩) (muBranch pins sp first) (rest.map (muBranch pins sp))

/-- `body`, conjoined on the left with μ unless it implies mine (crate `guard_mine`). -/
def guardMine (μ : Span → Condition) (body : Condition) : Condition :=
  if impliesMine body then body else mkAnd body.span (μ body.span) body

/-- The name a binder slot binds or refers to (a macro slot by its sigil and name). -/
def slotName : BinderSlot → String
  | .name n => n
  | .paramRef p => "?" ++ p
  | .binderRef b => "$" ++ b

mutual

/-- Every variable name of a condition, bound or used. -/
def condNames : Condition → List String
  | ⟨_, k⟩ => kindNames k

def kindNames : ConditionKind → List String
  | .and l r => condNames l ++ condNames r
  | .or l r => condNames l ++ condNames r
  | .since l _ r => condNames l ++ condNames r
  | .not c => condNames c
  | .formerly _ c => condNames c
  | .previous _ c => condNames c
  | .exists x c => (binding x).1 :: condNames c
  | .predicate ⟨_, _, _, _, args⟩ => argNames args
  | .comparison _ l r => termNames l ++ termNames r
  | .tp s => [slotName s]
  | .call _ => []
  | .sigilRef _ _ => []
  | .refine b fs _ => condNames b ++ argNames fs

def argNames : List NamedArg → List String
  | [] => []
  | ⟨_, t⟩ :: rest => termNames t ++ argNames rest

def termNames : Surface.Temporal.Term → List String
  | .var x => [x]
  | .agg ⟨_, k⟩ => aggNames k
  | .arith _ l r => termNames l ++ termNames r
  | _ => []

def aggNames : AggExprKind → List String
  | .sum x vs b => slotName x :: (vs.map fun v => (binding v).1) ++ condNames b
  | .count vs b => (vs.map fun v => (binding v).1) ++ condNames b
  | .call _ => []

end

/-- The candidate prefix with `k` more `_` than `__pin_`. -/
def pinPrefix (k : Nat) : String := "__pin_" ++ String.ofList (List.replicate k '_')

/-- `x` starts with `pre`, character by character (as Rust's `str::starts_with` compares
bytes; on UTF-8 text the two agree). -/
def hasPrefix (pre x : String) : Bool := pre.toList.isPrefixOf x.toList

/-- The prefix of the rewrite's fresh names, for a leaf with the variables `names` (crate
`fresh_prefix`): `__pin_`, with one more `_` for as long as some name starts with it. A prefix
longer than every name starts none, so the search ends by the longest name's length. -/
def freshPrefix (names : List String) : String :=
  let bound := (names.map String.length).foldl max 0
  match (List.range (bound + 1)).find? (fun k => names.all fun x => !hasPrefix (pinPrefix k) x)
  with
  | some k => pinPrefix k
  | none => pinPrefix bound

/-- A fresh name `<pre><stem><n>` from the leaf's counter (crate `Cx::fresh`). -/
def fresh (pre stem : String) : StateM Nat String := do
  let n ← get
  set (n + 1)
  return s!"{pre}{stem}{n}"

/-- The encoding of `previous within w` with the guarded body `b`, the names `ti`, `tj`, `tk`
drawn (crate `rewrite_previous`):

```text
exists ti. exists tj. tp(ti) && formerly within w (b && tp(tj)) && tj < ti
  && !(exists tk. formerly within w (μ && tp(tk)) && formerly within w (b && tp(tj)) && tp(ti)
                  && tj < tk && tk < ti)
```
-/
def encodePrevious (μ : Span → Condition) (sp : Span) (w : WithinSpec) (b : Condition)
    (ti tj tk : String) : Condition :=
  let anchor := mkFormerly sp w (mkAnd sp b (mkTp sp tj))
  let between := mkExistsTp sp tk (mkAnds sp
    [mkFormerly sp w (mkAnd sp (μ sp) (mkTp sp tk)), anchor, mkTp sp ti,
     mkCmp sp .lt tj tk, mkCmp sp .lt tk ti])
  mkExistsTp sp ti (mkExistsTp sp tj (mkAnds sp
    [mkTp sp ti, anchor, mkCmp sp .lt tj ti, mkNot sp between]))

/-- The general encoding of `l since within w a`, with the guarded anchor `a` and the rewritten
left `l`, the names `ti`, `tj`, `tkAll`, `tkLeft`, `n1`, `n2` drawn (crate `rewrite_since`): the
continuity of `l` over the mine positions of `(tj, ti]` as a count equality.

```text
exists ti. exists tj. exists n1. exists n2. tp(ti) && A
  && (count tkAll. where formerly within w (μ && tp(tkAll)) && R(tkAll)) == n1
  && (count tkLeft. where formerly within w ((μ && l) && tp(tkLeft)) && R(tkLeft)) == n2
  && n1 == n2
```

where `A` is `formerly within w (a && tp(tj))` and `R(t)` is `A && tp(ti) && tj < t && t <= ti`.
-/
def encodeSince (μ : Span → Condition) (sp : Span) (l : Condition) (w : WithinSpec)
    (a : Condition) (ti tj tkAll tkLeft n1 n2 : String) : Condition :=
  let anchor := mkFormerly sp w (mkAnd sp a (mkTp sp tj))
  let range := fun (t : String) => [anchor, mkTp sp ti, mkCmp sp .lt tj t, mkCmp sp .le t ti]
  let n1Count := mkCount sp tkAll (mkAnds sp
    (mkFormerly sp w (mkAnd sp (μ sp) (mkTp sp tkAll)) :: range tkAll))
  let n2Count := mkCount sp tkLeft (mkAnds sp
    (mkFormerly sp w (mkAnd sp (mkAnd sp (μ sp) l) (mkTp sp tkLeft)) :: range tkLeft))
  mkExistsTp sp ti (mkExistsTp sp tj (mkExistsLong sp n1 (mkExistsLong sp n2 (mkAnds sp
    [mkTp sp ti, anchor, mkAggEq sp n1Count n1, mkAggEq sp n2Count n2, mkCmp sp .eq n1 n2]))))

/-- The general `since` encoding: the left's rewrite `left'` runs first, then the six names are
drawn. -/
def relSinceGeneral (pre : String) (μ : Span → Condition) (sp : Span)
    (left' : StateM Nat Condition) (w : WithinSpec) (a : Condition) : StateM Nat Condition := do
  let l ← left'
  let ti ← fresh pre "ti"
  let tj ← fresh pre "tj"
  let tkAll ← fresh pre "tk_all"
  let tkLeft ← fresh pre "tk_left"
  let n1 ← fresh pre "n"
  let n2 ← fresh pre "n"
  return encodeSince μ sp l w a ti tj tkAll tkLeft n1 n2

mutual

/-- The rewrite of a condition, with μ given (crate `Cx::rewrite`). Inner rewrites draw their
fresh names first, with the prefix `pre`. -/
def relCond (pre : String) (μ : Span → Condition) : Condition → StateM Nat Condition
  | ⟨sp, k⟩ => relKind pre μ sp k

def relKind (pre : String) (μ : Span → Condition) (sp : Span) :
    ConditionKind → StateM Nat Condition
  | .and l r => do
    let l' ← relCond pre μ l
    let r' ← relCond pre μ r
    return ⟨sp, .and l' r'⟩
  | .or l r => do
    let l' ← relCond pre μ l
    let r' ← relCond pre μ r
    return ⟨sp, .or l' r'⟩
  | .not c => do
    let c' ← relCond pre μ c
    return ⟨sp, .not c'⟩
  | .exists x c => do
    let c' ← relCond pre μ c
    return ⟨sp, .exists x c'⟩
  | .comparison op l r => do
    let l' ← relTerm pre μ l
    let r' ← relTerm pre μ r
    return ⟨sp, .comparison op l' r'⟩
  | .formerly w c => do
    let c' ← relCond pre μ c
    return ⟨sp, .formerly w (guardMine μ c')⟩
  | .previous w c => do
    let b ← relCond pre μ c
    let ti ← fresh pre "ti"
    let tj ← fresh pre "tj"
    let tk ← fresh pre "tk"
    return encodePrevious μ sp w (guardMine μ b) ti tj tk
  | .since ⟨lsp, .not x⟩ w r => do
    let a ← relCond pre μ r
    let a := guardMine μ a
    if impliesMine x then
      -- The negated-left idiom with a mine-confined `x`: the native `since`.
      let x' ← relCond pre μ x
      return ⟨sp, .since (mkNot sp x') w a⟩
    else
      relSinceGeneral pre μ sp (do let x' ← relCond pre μ x; return ⟨lsp, .not x'⟩) w a
  | .since l w r => do
    let a ← relCond pre μ r
    relSinceGeneral pre μ sp (relCond pre μ l) w (guardMine μ a)
  | .refine b fs rsp => do
    let b' ← relCond pre μ b
    return ⟨sp, .refine b' fs rsp⟩
  | .predicate p => pure ⟨sp, .predicate p⟩
  | .tp x => pure ⟨sp, .tp x⟩
  | .call c => pure ⟨sp, .call c⟩
  | .sigilRef s n => pure ⟨sp, .sigilRef s n⟩

/-- The rewrite of a comparison operand (crate `rewrite_term`): aggregate bodies, array items and
arithmetic. -/
def relTerm (pre : String) (μ : Span → Condition) : Term → StateM Nat Term
  | .agg a => do
    let a' ← relAgg pre μ a
    return .agg a'
  | .array items => do
    let items' ← relTerms pre μ items
    return .array items'
  | .arith op l r => do
    let l' ← relTerm pre μ l
    let r' ← relTerm pre μ r
    return .arith op l' r'
  | t => pure t

def relTerms (pre : String) (μ : Span → Condition) : List Term → StateM Nat (List Term)
  | [] => pure []
  | t :: ts => do
    let t' ← relTerm pre μ t
    let ts' ← relTerms pre μ ts
    return t' :: ts'

def relAgg (pre : String) (μ : Span → Condition) : AggExpr → StateM Nat AggExpr
  | ⟨sp, k⟩ => do
    let k' ← relAggKind pre μ k
    return ⟨sp, k'⟩

def relAggKind (pre : String) (μ : Span → Condition) : AggExprKind → StateM Nat AggExprKind
  | .sum v vs b => do
    let b' ← relCond pre μ b
    return .sum v vs b'
  | .count vs b => do
    let b' ← relCond pre μ b
    return .count vs b'
  | .call c => pure (.call c)

end

/-- The relativization rewrite for the universal symmetric pins `pins` (crate
`relativize_condition`), its fresh names drawn with a prefix no variable of the leaf starts with
(`freshPrefix`); the identity when `pins` is empty. The crate's rewrite assumes a schema
with events whenever it has universal pins (`universal_pins` is empty without events); on an
event-less schema with pins it panics, and this port reports an error. -/
def relativize (schema : DerivedEventSchema) (pins : List Pin) (c : Condition) :
    Result Condition :=
  if pins.isEmpty then pure c
  else match schema.events with
    | [] => throw { stage := .relativize, category := .other,
                    message := "universal pins over an event-less schema" }
    | e :: es => pure ((relCond (freshPrefix (condNames c)) (mu pins e es) c).run' 0)

end Dogwood.Frontend.LeafPasses
