import Dogwood.Frontend.Types
import Dogwood.Frontend.Conformance
import Dogwood.Frontend.Balanced
import Dogwood.Frontend.Cedarify.Targets

/-!
# Cedarify (WP3)

The crate's `cedarify/mod.rs` and `cedarify/to_ast.rs`, with `scope_target_actions`
(`schema_augment.rs`, in `Dogwood.Frontend.Cedarify.Targets`): each rule of an expanded policy
set lowered to a Cedar policy.

Rule `i` has the key `policy_<i>` (`<distincter>_<i>` under a distincter) and the Cedar id of its
key (or its stable id). Its clause bodies are desugared as Cedar's `ExprBuilder` desugars them
(`!=` is `!(==)`, `>` is `!(<=)`, `>=` is `!(<)`, `e is T in x` is `e is T && e in x`,
`e has a.b` is Cedar's extended `has`, or `e has a && e.a has b` when the path has a reserved
word, extension constructors and methods are calls), the
clauses folded left to right with `&&` (an `unless` body negated, `true` when there is none), and
each leaf hoisted to the request context:

* a `temporal { … }` block to `context.<key>__temporal_<n>`, a `Bool`;
* a provider chain `Ns::Fn(args).m(…)…` to `context.providers.<key>_p_<n>`, whose type is the
  last method's output type (the provider's when there is no method), and whose projections
  after the chain stay Cedar attribute accesses;

where `n` counts the rule's leaves of both kinds from `0`, in evaluation order. An entity literal
of a provider enum the set uses is renamed to the enum's exported name; as that name is known only
once every rule is lowered, a set that uses provider enums is lowered twice, as the crate does.

Lowering also produces each rule in the **specification's form** (`Dogwood.Spec.Policy`): the
same desugared rule with each leaf inline, as `temporal φ` or `provider c`, where the crate has
its hoisted attribute (`cedarifyWithSpec`). The crate's rule is the specification's lowering of
it, with the specification's attribute of each leaf replaced by the crate's
(`cedarifyFull_lowered_rename`). A leaf that has no form in the specification (one holding an
array constant, which the crate rejects before lowering, or a form macro expansion removes) has
a placeholder, and makes `cedarifyWithSpec` fail; it does not affect the crate-named result.
-/

namespace Dogwood.Frontend.Cedarify

open Surface (UnOp BinOp)
open Dogwood.Spec (Expr)

/-! ## Names -/

/-- The key of rule `i` (crate `rule_key`): `<distincter>_<i>`, or `policy_<i>`. -/
def ruleKey (distincter : Option String) (i : Nat) : String :=
  match distincter with
  | some d => d ++ "_" ++ toString i
  | none => "policy_" ++ toString i

/-- The Cedar id of rule `i` (crate `lower_policies`): its stable id (`<distincter>/<id>` under a
distincter) when the set has stable ids, its key otherwise. -/
def ruleId (distincter : Option String) (ids : Option (List String)) (i : Nat) : String :=
  match ids with
  | some ids =>
    let id := ids.getD i (ruleKey distincter i)
    match distincter with
    | some d => d ++ "/" ++ id
    | none => id
  | none => ruleKey distincter i

/-- The context attribute of a rule's `n`-th leaf when it is temporal. -/
def temporalName (key : String) (n : Nat) : String := key ++ "__temporal_" ++ toString n

/-- The attribute of `context.providers` of a rule's `n`-th leaf when it is a provider chain. -/
def providerName (key : String) (n : Nat) : String := key ++ "_p_" ++ toString n

/-- The crate's reference to a hoisted temporal leaf, `context.<name>`. -/
def temporalRef (name : String) : Cedar.Spec.Expr := .getAttr (.var .context) name

/-- The crate's reference to a hoisted provider leaf, `context.providers.<name>`. -/
def providerRef (name : String) : Cedar.Spec.Expr :=
  .getAttr (.getAttr (.var .context) "providers") name

/-! ## Scopes -/

/-- The action scope a rule pins (crate `scope_action`): an action is its namespace's text and
its id. -/
def scopeAction : Surface.ActionConstraint → ScopedAction
  | .any => .unconstrained
  | .eq u => .concrete ("::".intercalate u.ty.path) u.eid
  | .in us => .list (us.map fun u => ("::".intercalate u.ty.path, u.eid))

/-- What a principal or resource scope admits on the entity-type axis (crate
`scope_constraint`); a slot reads as `any`. -/
def scopeConstraint : Cedar.Spec.ScopeTemplate → ScopeConstraint
  | .any => .any
  | .is t | .isMem t _ => .isType (nameText t)
  | .eq (.entityUID u) => .uid (nameText u.ty) false
  | .mem (.entityUID u) => .uid (nameText u.ty) true
  | .eq (.slot _) | .mem (.slot _) => .any

/-- A principal or resource scope as Cedar's policy holds it, once it has no slot. -/
def scopeOf : Cedar.Spec.ScopeTemplate → Cedar.Spec.Scope
  | .any => .any
  | .eq (.entityUID u) => .eq u
  | .mem (.entityUID u) => .mem u
  | .is t => .is t
  | .isMem t (.entityUID u) => .isMem t u
  | .eq (.slot _) | .mem (.slot _) | .isMem _ (.slot _) => .any

/-- The action scope as Cedar's policy holds it: a list of one action is `in` that action (as
Cedar's policy JSON has it). -/
def actionScopeOf : Surface.ActionConstraint → Cedar.Spec.ActionScope
  | .any => .actionScope .any
  | .eq u => .actionScope (.eq u)
  | .in [u] => .actionScope (.mem u)
  | .in us => .actionInAny us

/-- The slot a scope constraint holds. -/
def templateSlot? : Cedar.Spec.ScopeTemplate → Option Cedar.Spec.SlotID
  | .eq (.slot s) | .mem (.slot s) | .isMem _ (.slot s) => some s
  | _ => none

/-! ## Desugaring -/

/-- A surface unary operator applied (crate `lower_unary`). -/
def unaryC : UnOp → Cedar.Spec.Expr → Cedar.Spec.Expr
  | .not, x => .unaryApp .not x
  | .neg, x => .unaryApp .neg x
  | .isEmpty, x => .unaryApp .isEmpty x
  | .decimal, x => .call .decimal [x]
  | .datetime, x => .call .datetime [x]
  | .duration, x => .call .duration [x]
  | .ip, x => .call .ip [x]
  | .isIpv4, x => .call .isIpv4 [x]
  | .isIpv6, x => .call .isIpv6 [x]
  | .isLoopback, x => .call .isLoopback [x]
  | .isMulticast, x => .call .isMulticast [x]
  | .toDate, x => .call .toDate [x]
  | .toTime, x => .call .toTime [x]
  | .toMilliseconds, x => .call .toMilliseconds [x]
  | .toSeconds, x => .call .toSeconds [x]
  | .toMinutes, x => .call .toMinutes [x]
  | .toHours, x => .call .toHours [x]
  | .toDays, x => .call .toDays [x]

/-- `unaryC`, in the specification's syntax. -/
def unaryS : UnOp → Expr → Expr
  | .not, x => .unaryApp .not x
  | .neg, x => .unaryApp .neg x
  | .isEmpty, x => .unaryApp .isEmpty x
  | .decimal, x => .call .decimal [x]
  | .datetime, x => .call .datetime [x]
  | .duration, x => .call .duration [x]
  | .ip, x => .call .ip [x]
  | .isIpv4, x => .call .isIpv4 [x]
  | .isIpv6, x => .call .isIpv6 [x]
  | .isLoopback, x => .call .isLoopback [x]
  | .isMulticast, x => .call .isMulticast [x]
  | .toDate, x => .call .toDate [x]
  | .toTime, x => .call .toTime [x]
  | .toMilliseconds, x => .call .toMilliseconds [x]
  | .toSeconds, x => .call .toSeconds [x]
  | .toMinutes, x => .call .toMinutes [x]
  | .toHours, x => .call .toHours [x]
  | .toDays, x => .call .toDays [x]

/-- Cedar's `ExprBuilder::and`: the conjunction of two Boolean literals is the literal of their
conjunction, any other an `&&` node (`cedar-policy-core`, `ast/expr.rs`). The crate builds every
`&&` it lowers, and the conjunction of a rule's clauses, with it. -/
def andC (l r : Cedar.Spec.Expr) : Cedar.Spec.Expr :=
  match l, r with
  | .lit (.bool a), .lit (.bool b) => .lit (.bool (a && b))
  | _, _ => .and l r

/-- Cedar's `ExprBuilder::or`: the disjunction of two Boolean literals is the literal of their
disjunction, any other an `||` node. -/
def orC (l r : Cedar.Spec.Expr) : Cedar.Spec.Expr :=
  match l, r with
  | .lit (.bool a), .lit (.bool b) => .lit (.bool (a || b))
  | _, _ => .or l r

/-- `andC`, in the specification's syntax. -/
def andS (l r : Expr) : Expr :=
  match l, r with
  | .lit (.bool a), .lit (.bool b) => .lit (.bool (a && b))
  | _, _ => .and l r

/-- `orC`, in the specification's syntax. -/
def orS (l r : Expr) : Expr :=
  match l, r with
  | .lit (.bool a), .lit (.bool b) => .lit (.bool (a || b))
  | _, _ => .or l r

/-- A surface binary operator applied (crate `lower_binary`, through Cedar's `ExprBuilder`). -/
def binaryC : BinOp → Cedar.Spec.Expr → Cedar.Spec.Expr → Cedar.Spec.Expr
  | .eq, l, r => .binaryApp .eq l r
  | .notEq, l, r => .unaryApp .not (.binaryApp .eq l r)
  | .less, l, r => .binaryApp .less l r
  | .lessEq, l, r => .binaryApp .lessEq l r
  | .greater, l, r => .unaryApp .not (.binaryApp .lessEq l r)
  | .greaterEq, l, r => .unaryApp .not (.binaryApp .less l r)
  | .and, l, r => andC l r
  | .or, l, r => orC l r
  | .add, l, r => .binaryApp .add l r
  | .sub, l, r => .binaryApp .sub l r
  | .mul, l, r => .binaryApp .mul l r
  | .in, l, r => .binaryApp .mem l r
  | .contains, l, r => .binaryApp .contains l r
  | .containsAll, l, r => .binaryApp .containsAll l r
  | .containsAny, l, r => .binaryApp .containsAny l r
  | .getTag, l, r => .binaryApp .getTag l r
  | .hasTag, l, r => .binaryApp .hasTag l r
  | .isInRange, l, r => .call .isInRange [l, r]
  | .offset, l, r => .call .offset [l, r]
  | .durationSince, l, r => .call .durationSince [l, r]
  | .decimalLessThan, l, r => .call .lessThan [l, r]
  | .decimalLessEq, l, r => .call .lessThanOrEqual [l, r]
  | .decimalGreater, l, r => .call .greaterThan [l, r]
  | .decimalGreaterEq, l, r => .call .greaterThanOrEqual [l, r]

/-- `binaryC`, in the specification's syntax. -/
def binaryS : BinOp → Expr → Expr → Expr
  | .eq, l, r => .binaryApp .eq l r
  | .notEq, l, r => .unaryApp .not (.binaryApp .eq l r)
  | .less, l, r => .binaryApp .less l r
  | .lessEq, l, r => .binaryApp .lessEq l r
  | .greater, l, r => .unaryApp .not (.binaryApp .lessEq l r)
  | .greaterEq, l, r => .unaryApp .not (.binaryApp .less l r)
  | .and, l, r => andS l r
  | .or, l, r => orS l r
  | .add, l, r => .binaryApp .add l r
  | .sub, l, r => .binaryApp .sub l r
  | .mul, l, r => .binaryApp .mul l r
  | .in, l, r => .binaryApp .mem l r
  | .contains, l, r => .binaryApp .contains l r
  | .containsAll, l, r => .binaryApp .containsAll l r
  | .containsAny, l, r => .binaryApp .containsAny l r
  | .getTag, l, r => .binaryApp .getTag l r
  | .hasTag, l, r => .binaryApp .hasTag l r
  | .isInRange, l, r => .call .isInRange [l, r]
  | .offset, l, r => .call .offset [l, r]
  | .durationSince, l, r => .call .durationSince [l, r]
  | .decimalLessThan, l, r => .call .lessThan [l, r]
  | .decimalLessEq, l, r => .call .lessThanOrEqual [l, r]
  | .decimalGreater, l, r => .call .greaterThan [l, r]
  | .decimalGreaterEq, l, r => .call .greaterThanOrEqual [l, r]

/-- The words Cedar reserves (`RESERVED_IDS`). -/
def reservedIds : List String := ["true", "false", "if", "then", "else", "in", "is", "like", "has",
  "__cedar"]

/-- Whether `s` matches `^[_a-zA-Z][_a-zA-Z0-9]*$`. -/
def isAnyIdent (s : String) : Bool :=
  match s.toList with
  | [] => false
  | c :: cs => (c == '_' || c.isAlpha) && cs.all fun d => d == '_' || d.isAlphanum

/-- Whether `s` is an identifier Cedar does not reserve (`is_normalized_ident`): Cedar prints it
bare, and an extended `has` path may hold it. -/
def isNormalizedIdent (s : String) : Bool := isAnyIdent s && !reservedIds.contains s

/-- Whether lowering keeps `x has a.rest` as one extended `has` node (crate `lower_has`): the path
has at least two attributes, each an identifier Cedar does not reserve. -/
def extHasPath (a : String) (rest : List String) : Bool :=
  !rest.isEmpty && (a :: rest).all isNormalizedIdent

/-- The rest of `x has a.b.c`, after the test `h` of the attributes so far and the access `g` to
the last of them, as the left-nested conjunction (crate `lower_has`). -/
def hasRestC (h g : Cedar.Spec.Expr) : List String → Cedar.Spec.Expr
  | [] => h
  | b :: rest => hasRestC (.and h (.hasAttr g b)) (.getAttr g b) rest

/-- `x has a.b.c` (crate `lower_has`): one attribute is Cedar's `x has a`; a path of
identifiers Cedar does not reserve is Cedar 4.14's one extended `has` node; any other path, one
with a reserved word (which only Dogwood's grammar admits), is the conjunction
`x has a && x.a has b && x.a.b has c`. The grammar makes the path non-empty; an empty one reads
as one empty attribute, as in the crate. -/
def hasPathC (x : Cedar.Spec.Expr) : List String → Cedar.Spec.Expr
  | [] => .hasAttr x ""
  | a :: rest =>
    if extHasPath a rest then .extHasAttr x a rest else hasRestC (.hasAttr x a) (.getAttr x a) rest

/-- The references of `x has attrs`, those of `x` being `refs`: those of `x` once in an extended
`has`, once per attribute in the conjunction (`hasPathC`). -/
def hasRefs (refs : List Cedar.Spec.Expr) : List String → List Cedar.Spec.Expr
  | [] => refs
  | a :: rest => if extHasPath a rest then refs else (List.replicate (rest.length + 1) refs).flatten

/-- `hasRestC`, in the specification's syntax. -/
def hasRestS (h g : Expr) : List String → Expr
  | [] => h
  | b :: rest => hasRestS (.and h (.hasAttr g b)) (.getAttr g b) rest

/-- `hasPathC`, in the specification's syntax. -/
def hasPathS (x : Expr) : List String → Expr
  | [] => .hasAttr x ""
  | a :: rest =>
    if extHasPath a rest then .extHasAttr x a rest else hasRestS (.hasAttr x a) (.getAttr x a) rest

/-- An entity literal of a used provider enum, renamed to the enum's exported name (crate
`rename_enum_literal`). -/
def renameEnum (names : List (String × String)) : Cedar.Spec.Prim → Cedar.Spec.Prim
  | .entityUID u =>
    match names.lookup (nameText u.ty) with
    | some exported =>
      let segs := exported.splitOn "::"
      .entityUID ⟨⟨segs.getLast?.getD "", segs.dropLast⟩, u.eid⟩
    | none => .entityUID u
  | p => p

/-! ## Provider chains -/

/-- A cedarify error. -/
def err (message : String) (span : Option Span) : Error :=
  { stage := .cedarify, category := .cedarify, message, span }

/-- A call's name is a provider's: it is qualified (crate `is_provider_name`). -/
def isProviderName (name : String) : Bool := (name.splitOn "::").length > 1

/-- The attribute path an argument reads, rooted at `context`, `principal` or `resource` (crate
`flatten_arg_path`). -/
def flattenPath : Surface.Expr → Option (List String)
  | ⟨.var .context, _⟩ => some ["context"]
  | ⟨.var .principal, _⟩ => some ["principal"]
  | ⟨.var .resource, _⟩ => some ["resource"]
  | ⟨.getAttr e a, _⟩ => (flattenPath e).map (· ++ [a])
  | _ => none

def msgArgPath : String :=
  "a provider argument that is an attribute access must be an attribute path rooted at " ++
  "`context`, `principal`, or `resource` (e.g. `context.input.x`, `principal.id`)"

def msgArgDecimal : String :=
  "`decimal(…)` provider argument requires a string literal, e.g. `decimal(\"0.5\")`"

def msgArg : String :=
  "a provider argument must be an attribute path rooted at `context`, `principal`, or " ++
  "`resource`, a string / integer / bool / `decimal(…)` literal, or a set of those"

def msgProjection : String :=
  "a field or index projection may not appear before a provider method in the same chain; " ++
  "put projections after the method chain"

def msgUnresolved (name : String) : String :=
  s!"unresolved call to `{name}` reached lowering — it is not a declared information provider, " ++
  "not a declared macro, and not a Cedar built-in (macro expansion runs before lowering)"

mutual

/-- One provider argument (crate `cedar_expr_to_provider_arg`); an error has the call's span. -/
def toProviderArg (sp : Span) : Surface.Expr → Result Provider.Arg
  | e@⟨.getAttr _ _, _⟩ | e@⟨.var .context, _⟩ | e@⟨.var .principal, _⟩
  | e@⟨.var .resource, _⟩ =>
    match flattenPath e with
    | some p => .ok (.field p)
    | none => throw (err msgArgPath (some sp))
  | ⟨.unaryApp .decimal ⟨.lit (.string s), _⟩, _⟩ => .ok (.decimal s)
  | ⟨.unaryApp .decimal _, _⟩ => throw (err msgArgDecimal (some sp))
  | ⟨.lit (.string s), _⟩ => .ok (.string s)
  | ⟨.lit (.int n), _⟩ => .ok (.integer n)
  | ⟨.lit (.bool b), _⟩ => .ok (.bool b)
  | ⟨.set xs, _⟩ => return .set (← toProviderArgs sp xs)
  | _ => throw (err msgArg (some sp))

def toProviderArgs (sp : Span) : List Surface.Expr → Result (List Provider.Arg)
  | [] => .ok []
  | x :: xs => return (← toProviderArg sp x) :: (← toProviderArgs sp xs)

end

/-- A provider call (crate `cedar_call_to_invocation`). -/
def toInvocation (name : String) (args : List Surface.Expr) (sp : Span) :
    Result Provider.Invocation := do
  return { span := sp, function := name.splitOn "::", args := ← toProviderArgs sp args }

/-- An accessor of a provider chain. -/
inductive Accessor where
  | method (m : Provider.MethodCall)
  | field (attr : String) (span : Span)

def Accessor.isField : Accessor → Bool
  | .field _ _ => true
  | .method _ => false

def Accessor.method? : Accessor → Option Provider.MethodCall
  | .method m => some m
  | .field _ _ => none

/-- A chain of methods and attribute accesses down to a provider call (crate
`peel_provider_chain`): its accessors, outermost first, and the call; `none` when the chain does
not end at a provider call. Each method's arguments are read before the methods it is applied
to, as the crate walks the chain. -/
def peel : Surface.Expr → Result (Option (List Accessor × Provider.Invocation))
  | ⟨.methodCall recv m args, sp⟩ => do
    let margs ← toProviderArgs sp args
    match ← peel recv with
    | none => pure none
    | some (accs, inv) => pure (some (.method ⟨sp, m, margs⟩ :: accs, inv))
  | ⟨.getAttr inner a, sp⟩ => do
    match ← peel inner with
    | none => pure none
    | some (accs, inv) => pure (some (.field a sp :: accs, inv))
  | ⟨.call name args, sp⟩ =>
    if isProviderName name then do pure (some ([], ← toInvocation name args sp)) else pure none
  | _ => pure none

/-- A provider call and its methods, as the specification's call. -/
def callOf (inv : Provider.Invocation) (methods : List Provider.MethodCall) :
    Except String Dogwood.Spec.Provider.Call := do
  let function : Cedar.Spec.Name ← match inv.function.getLast? with
    | some id => pure ⟨id, inv.function.dropLast⟩
    | none => throw "a provider invocation without a name"
  return { function, args := ← inv.args.mapM Provider.Arg.toSpec,
           methods := ← methods.mapM fun m => do
             return { name := m.name, args := ← m.args.mapM Provider.Arg.toSpec } }

/-! ## Expressions -/

/-- What lowering a rule reads: its action scope and its principal and resource constraints,
the provider declarations, and the exported names of the used provider enums. -/
structure Env where
  action : ScopedAction
  principal : ScopeConstraint
  resource : ScopeConstraint
  decls : Option ProviderDecls.Declarations
  enumNames : List (String × String)

/-- The hoisting state: the current rule's key, the ordinal of its next leaf, the fields hoisted
so far, and the leaves that have no form in the specification. -/
structure St where
  key : String
  ordinal : Nat
  contextFields : List ContextField
  providerFields : List ProviderField
  specErrors : List String

/-- A lowered expression: the crate's Cedar expression, the specification's form, and, for each
leaf of the specification's form in evaluation order, the crate's reference that replaces it. -/
structure Out where
  cedar : Cedar.Spec.Expr
  spec : Expr
  refs : List Cedar.Spec.Expr

/-- Hoist a temporal block (crate `lower_expr`, `Extension::Temporal`). -/
def hoistTemporal (env : Env) (t : Surface.Temporal.Block) (s : St) : Out × St :=
  let name := temporalName s.key s.ordinal
  let field : ContextField := { action := env.action, fieldName := name, temporal := t,
                                targetActions := [], principal := env.principal,
                                resource := env.resource }
  let (φ, errs) := match t.condition.toFormula with
    | .ok φ => (φ, s.specErrors)
    | .error e => (default, s.specErrors ++ [e])
  (⟨temporalRef name, .temporal φ, [temporalRef name]⟩,
   { s with ordinal := s.ordinal + 1, contextFields := s.contextFields ++ [field],
            specErrors := errs })

/-- Hoist a provider call and its eager methods (crate `lower_provider_invocation`). -/
def hoistProvider (env : Env) (inv : Provider.Invocation) (methods : List Provider.MethodCall)
    (s : St) : Out × St :=
  let name := providerName s.key s.ordinal
  let field : ProviderField := {
    action := env.action, targetActions := [], fieldName := name,
    cedarType := ProviderDecls.cedarTypeOf env.decls env.enumNames inv.key (methods.map (·.name)),
    bodyBase := 0, invocation := inv, methods, principal := env.principal,
    resource := env.resource }
  let (c, errs) := match callOf inv methods with
    | .ok c => (c, s.specErrors)
    | .error e => (default, s.specErrors ++ [e])
  (⟨providerRef name, .provider c, [providerRef name]⟩,
   { s with ordinal := s.ordinal + 1, providerFields := s.providerFields ++ [field],
            specErrors := errs })

mutual

/-- Lower an expression (crate `to_ast::lower_expr`), hoisting its leaves. Children are lowered
left to right, record entries in key order. -/
def lowerExpr (env : Env) : Surface.Expr → St → Result (Out × St)
  | ⟨k, sp⟩, s => lowerKind env sp k s

def lowerKind (env : Env) (sp : Span) : Surface.ExprKind → St → Result (Out × St)
  | .lit l, s => let l' := renameEnum env.enumNames l; .ok (⟨.lit l', .lit l', []⟩, s)
  | .var v, s => .ok (⟨.var v, .var v, []⟩, s)
  -- A slot makes the rule a template, which `lowerPolicy` reports once its clauses are lowered.
  | .slot _, s => .ok (⟨.lit (.bool true), .lit (.bool true), []⟩, s)
  | .extension t, s => .ok (hoistTemporal env t s)
  | .unaryApp op e, s => do
    let (o, s) ← lowerExpr env e s
    pure (⟨unaryC op o.cedar, unaryS op o.spec, o.refs⟩, s)
  | .binaryApp op l r, s => do
    let (ol, s) ← lowerExpr env l s
    let (or, s) ← lowerExpr env r s
    pure (⟨binaryC op ol.cedar or.cedar, binaryS op ol.spec or.spec, ol.refs ++ or.refs⟩, s)
  | .getAttr e a, s => do
    let (o, s) ← lowerExpr env e s
    pure (⟨.getAttr o.cedar a, .getAttr o.spec a, o.refs⟩, s)
  | .hasAttr e attrs, s => do
    let (o, s) ← lowerExpr env e s
    -- The lowered operand occurs once in an extended `has`, and once per attribute in the
    -- conjunction.
    pure (⟨hasPathC o.cedar attrs, hasPathS o.spec attrs, hasRefs o.refs attrs⟩, s)
  | .like e p, s => do
    let (o, s) ← lowerExpr env e s
    pure (⟨.unaryApp (.like p) o.cedar, .unaryApp (.like p) o.spec, o.refs⟩, s)
  | .is e ty none, s => do
    let (o, s) ← lowerExpr env e s
    pure (⟨.unaryApp (.is ty) o.cedar, .unaryApp (.is ty) o.spec, o.refs⟩, s)
  | .is e ty (some x), s => do
    let (o, s) ← lowerExpr env e s
    let (ox, s) ← lowerExpr env x s
    pure (⟨.and (.unaryApp (.is ty) o.cedar) (.binaryApp .mem o.cedar ox.cedar),
           .and (.unaryApp (.is ty) o.spec) (.binaryApp .mem o.spec ox.spec),
           o.refs ++ o.refs ++ ox.refs⟩, s)
  | .ite c t e, s => do
    let (oc, s) ← lowerExpr env c s
    let (ot, s) ← lowerExpr env t s
    let (oe, s) ← lowerExpr env e s
    pure (⟨.ite oc.cedar ot.cedar oe.cedar, .ite oc.spec ot.spec oe.spec,
           oc.refs ++ ot.refs ++ oe.refs⟩, s)
  | .set xs, s => do
    let (os, s) ← lowerList env xs s
    pure (⟨.set (os.map (·.cedar)), .set (os.map (·.spec)), (os.map (·.refs)).flatten⟩, s)
  | .record m, s => do
    let (os, s) ← lowerRecord env m s
    pure (⟨.record (os.map fun (a, o) => (a, o.cedar)), .record (os.map fun (a, o) => (a, o.spec)),
           (os.map (·.2.refs)).flatten⟩, s)
  | .call name args, s =>
    if isProviderName name then do
      let inv ← toInvocation name args sp
      pure (hoistProvider env inv [] s)
    else throw (err (msgUnresolved name) (some sp))
  | .methodCall recv m args, s => do
    -- The chain is a method call, so its last accessor is a method: every accessor is eager,
    -- and attribute accesses after the chain are the `getAttr`s around it.
    match ← peel ⟨.methodCall recv m args, sp⟩ with
    | none => throw (err s!"unknown method `{m}`" (some sp))
    | some (accs, inv) =>
      let accs := accs.reverse
      if accs.any Accessor.isField then throw (err msgProjection (some sp))
      else pure (hoistProvider env inv (accs.filterMap Accessor.method?) s)
  | .paramRef n, _ =>
    throw (err s!"macro parameter `?{n}` reached lowering — expansion did not substitute it" (some sp))

def lowerList (env : Env) : List Surface.Expr → St → Result (List Out × St)
  | [], s => .ok ([], s)
  | x :: xs, s => do
    let (o, s) ← lowerExpr env x s
    let (os, s) ← lowerList env xs s
    pure (o :: os, s)

def lowerRecord (env : Env) : List (String × Surface.Expr) → St → Result (List (String × Out) × St)
  | [], s => .ok ([], s)
  | (a, x) :: xs, s => do
    let (o, s) ← lowerExpr env x s
    let (os, s) ← lowerRecord env xs s
    pure ((a, o) :: os, s)

end

/-! ## Rules -/

/-- The clauses of a rule, lowered in order; an `unless` body negated. -/
def lowerClauses (env : Env) : List Surface.Cond → St → Result (List Out × St)
  | [], s => .ok ([], s)
  | c :: cs, s => do
    let (o, s) ← lowerExpr env c.body s
    let o := match c.keyword with
      | .when => o
      | .unless => ⟨.unaryApp .not o.cedar, .unaryApp .not o.spec, o.refs⟩
    let (os, s) ← lowerClauses env cs s
    pure (o :: os, s)

/-- Two lowered clauses conjoined, through Cedar's `ExprBuilder::and`. -/
def andOut (l r : Out) : Out := ⟨andC l.cedar r.cedar, andS l.spec r.spec, l.refs ++ r.refs⟩

/-- The clauses conjoined as a balanced `&&` tree in clause order, `true` when there is none
(crate `emit_policy`, `balancedFold`). Any `&&` tree over the clauses in their order evaluates as
the left-nested chain does: left to right, stopping at the first `false` or error. -/
def conjoin : List Out → Out
  | [] => ⟨.lit (.bool true), .lit (.bool true), []⟩
  | o :: os => balancedFold andOut o os

mutual

/-- The first template slot Cedar finds in a lowered expression: it walks the expression with a
stack, so the last operand first (Cedar's `StaticPolicy::try_from` and `ExprIterator`). A
provider call holds no slot once lowered: a slot argument is rejected first. -/
def slotIn : Surface.Expr → Option Cedar.Spec.SlotID
  | ⟨k, _⟩ => slotInKind k

def slotInKind : Surface.ExprKind → Option Cedar.Spec.SlotID
  | .slot s => some s
  | .unaryApp _ e | .getAttr e _ | .hasAttr e _ | .like e _ | .is e _ none => slotIn e
  | .is e _ (some x) => (slotIn x).or (slotIn e)
  | .binaryApp _ l r => (slotIn r).or (slotIn l)
  | .ite c t e => ((slotIn e).or (slotIn t)).or (slotIn c)
  | .set xs => slotInList xs
  | .record m => slotInRecord m
  | _ => none

/-- The last element's slot first. -/
def slotInList : List Surface.Expr → Option Cedar.Spec.SlotID
  | [] => none
  | x :: xs => (slotInList xs).or (slotIn x)

def slotInRecord : List (String × Surface.Expr) → Option Cedar.Spec.SlotID
  | [] => none
  | (_, x) :: xs => (slotInRecord xs).or (slotIn x)

end

/-- The first slot Cedar finds in a rule: in its condition (the last clause first), then in its
resource scope, then in its principal scope. -/
def firstSlot (p : Surface.Policy) : Option Cedar.Spec.SlotID :=
  ((p.conditions.reverse.findSome? fun c => slotIn c.body).or (templateSlot? p.scope.resource)).or
    (templateSlot? p.scope.principal)

/-- A lowered rule: the crate's Cedar policy, the specification's form, and the crate's
references of the specification's leaves. -/
structure RuleOut where
  cedar : Cedar.Spec.Policy
  spec : Dogwood.Spec.Policy
  refs : List Cedar.Spec.Expr

/-- What lowering the rule `p` reads. -/
def ruleEnv (decls : Option ProviderDecls.Declarations) (enumNames : List (String × String))
    (p : Surface.Policy) : Env :=
  { action := scopeAction p.scope.action, principal := scopeConstraint p.scope.principal,
    resource := scopeConstraint p.scope.resource, decls, enumNames }

/-- Lower one rule under its key and id (crate `emit_policy`). -/
def lowerPolicy (decls : Option ProviderDecls.Declarations) (enumNames : List (String × String))
    (key id : String) (p : Surface.Policy) (s : St) : Result (RuleOut × St) := do
  let (os, s) ← lowerClauses (ruleEnv decls enumNames p) p.conditions { s with key, ordinal := 0 }
  let o := conjoin os
  match firstSlot p with
  | some slot =>
    throw (err s!"policy is not static (contains a template slot): found slot `{slot}` where slots are not allowed"
      (some p.span))
  | none =>
    let ps := Cedar.Spec.PrincipalScope.principalScope (scopeOf p.scope.principal)
    let rs := Cedar.Spec.ResourceScope.resourceScope (scopeOf p.scope.resource)
    let acts := actionScopeOf p.scope.action
    pure ({ cedar := { id, effect := p.effect, principalScope := ps, actionScope := acts,
                       resourceScope := rs, condition := [⟨.when, o.cedar⟩] },
            spec := { id, effect := p.effect, principalScope := ps, actionScope := acts,
                      resourceScope := rs, condition := [⟨.when, o.spec⟩] },
            refs := o.refs }, s)

/-- The rules lowered, with each rule's id and key and each hoisted field's rule. -/
structure Rules where
  rules : List RuleOut
  st : St
  ruleIds : List String
  ruleKeys : List String
  temporalRules : List Nat
  providerRules : List Nat

/-- Lower the rules from the `i`-th on (crate `lower_policies`). -/
def lowerPoliciesFrom (decls : Option ProviderDecls.Declarations)
    (enumNames : List (String × String)) (distincter : Option String) (ids : Option (List String)) :
    Nat → List Surface.Policy → Rules → Result Rules
  | _, [], acc => .ok acc
  | i, p :: ps, acc => do
    let key := ruleKey distincter i
    let id := ruleId distincter ids i
    let (r, s) ← lowerPolicy decls enumNames key id p acc.st
    if acc.ruleIds.contains id then
      throw (err s!"duplicate policy id `{id}`: duplicate template or policy id `{id}`" none)
    let acc : Rules := {
      rules := acc.rules ++ [r], st := s, ruleIds := acc.ruleIds ++ [id],
      ruleKeys := acc.ruleKeys ++ [key],
      temporalRules := acc.temporalRules ++
        List.replicate (s.contextFields.length - acc.temporalRules.length) i,
      providerRules := acc.providerRules ++
        List.replicate (s.providerFields.length - acc.providerRules.length) i }
    lowerPoliciesFrom decls enumNames distincter ids (i + 1) ps acc

/-- Lower every rule of the set. -/
def lowerPolicies (decls : Option ProviderDecls.Declarations) (enumNames : List (String × String))
    (distincter : Option String) (ids : Option (List String)) (ps : List Surface.Policy) :
    Result Rules :=
  lowerPoliciesFrom decls enumNames distincter ids 0 ps
    { rules := [], st := ⟨"", 0, [], [], []⟩, ruleIds := [], ruleKeys := [], temporalRules := [],
      providerRules := [] }

/-! ## The policy set -/

/-- Cedarify's result together with the rules in the specification's form. -/
structure WithSpec where
  cedarified : Cedarified
  /-- The rules as Cedar policies with the crate's names. -/
  cedar : List Cedar.Spec.Policy
  /-- The rules in the specification's form, each leaf inline. -/
  spec : List Dogwood.Spec.Policy
  /-- For each leaf of `spec`, in order over the set, the crate's reference that replaces it. -/
  refs : List Cedar.Spec.Expr
  /-- Why some leaves have no form in the specification. -/
  specErrors : List String

/-- The provider enums the hoisted provider fields reference, sorted, and the exported name of
each declared one (crate `cedarify_with_providers`). -/
def enumsOf (fragment : CedarSchema.Fragment) (decls : Option ProviderDecls.Declarations)
    (fields : List ProviderField) : List String × List (String × String) :=
  let calls := fields.map fun f => (f.invocation.key, f.methods.map (·.name))
  let referenced := ProviderDecls.referencedEnums decls calls
  (referenced, match decls with
    | some d => ProviderDecls.providerEnumNames fragment d referenced
    | none => [])

/-- Cedarify's result from the lowered rules: each hoisted field's target actions resolved
against the fragment. -/
def assemble (fragment : CedarSchema.Fragment) (referenced : List String)
    (enumNames : List (String × String)) (rules : Rules) : WithSpec :=
  let cedar := rules.rules.map (·.cedar)
  { cedarified := {
      policies := cedar.map Dogwood.Spec.Policy.ofCedar
      contextFields := rules.st.contextFields.map fun f =>
        { f with targetActions := scopeTargetActions f.action fragment }
      providerFields := rules.st.providerFields.map fun f =>
        { f with targetActions := scopeTargetActions f.action fragment }
      ruleIds := rules.ruleIds, ruleKeys := rules.ruleKeys, temporalRules := rules.temporalRules
      providerRules := rules.providerRules, referencedEnums := referenced, enumNames }
    cedar, spec := rules.rules.map (·.spec), refs := (rules.rules.map (·.refs)).flatten
    specErrors := rules.st.specErrors }

/-- Lower an expanded policy set (crate `cedarify_with_providers`), with the specification's
form of each rule. A set that uses provider enums is lowered a second time, with their exported
names. -/
def cedarifyFull (ps : Surface.PolicySet) (fragment : CedarSchema.Fragment)
    (decls : Option ProviderDecls.Declarations) (distincter : Option String := none)
    (ids : Option (List String) := none) : Result WithSpec := do
  let first ← lowerPolicies decls [] distincter ids ps.policies
  let (referenced, enumNames) := enumsOf fragment decls first.st.providerFields
  let rules ← if enumNames.isEmpty then pure first
    else lowerPolicies decls enumNames distincter ids ps.policies
  return assemble fragment referenced enumNames rules

/-- Lower an expanded policy set (crate `cedarify_with_providers`). An error has category
`cedarify`. -/
def cedarify (ps : Surface.PolicySet) (fragment : CedarSchema.Fragment)
    (decls : Option ProviderDecls.Declarations) (distincter : Option String := none)
    (ids : Option (List String) := none) : Result Cedarified :=
  (cedarifyFull ps fragment decls distincter ids).map (·.cedarified)

/-- Lower an expanded policy set, with each rule also in the specification's form; an error when
a leaf has no form in the specification. -/
def cedarifyWithSpec (ps : Surface.PolicySet) (fragment : CedarSchema.Fragment)
    (decls : Option ProviderDecls.Declarations) (distincter : Option String := none)
    (ids : Option (List String) := none) : Result WithSpec := do
  let w ← cedarifyFull ps fragment decls distincter ids
  match w.specErrors with
  | [] => pure w
  | e :: _ =>
    throw { stage := .cedarify, category := .other,
            message := s!"a leaf has no form in the specification: {e}" }

end Dogwood.Frontend.Cedarify
