import Dogwood.Frontend.Types
import Dogwood.Frontend.Identity.Sha256
import Dogwood.Frontend.Escape

/-!
# Rule identity (WP5)

The crate's `identity.rs`: the canonical encoding of each hoisted leaf, from which the rule
revisions and the content hashes are SHA-256 digests. A canonical encoding drops what carries no
meaning: spans, the positional names of the hoisted fields (`policy_<k>__temporal_<j>` becomes
`dw__temporal_<j>`), and the spellings of bound variables, which are renamed `v0`, `v1`, … in
binding order, shadowing respected. Strings are quoted as JSON strings, so the encodings are
injective.

This module computes the encodings, byte for byte, as `lower_entry` does for the revisions
(`RuleIdentity.leaves`), the rule revisions from them and each rule's canonical Cedar text
(`ruleRevision`), and the content hash of each temporal leaf (`contentHash`), with SHA-256
(`Dogwood.Frontend.Sha256`). The canonical Cedar text is Cedar's printing of the rule under the
canonical names, which cedarify produces. The policy-set version hash (crate `version_hash`),
which also covers Cedar's JSON of the augmented schema, is not computed here.
-/

namespace Dogwood.Frontend.RuleIdentity

open Surface.Temporal
open Dogwood.Spec.Temporal (CmpOp ArithOp TimeUnit BinderType)

/-! ## Quoting -/

/-- The lowercase hexadecimal digit of `n`, for `n < 16`. -/
def hexDigit (n : Nat) : Char :=
  if n < 10 then Char.ofNat (48 + n) else Char.ofNat (87 + n)

/-- The lowercase hexadecimal digits of `n`, without leading zeros (`0` is `0`). -/
def hexDigits (n : Nat) : String :=
  String.ofList (Nat.toDigits 16 n)

/-- One character of a JSON string, as `serde_json` writes it: `"` and `\` escaped, the short
escapes `\b \t \n \f \r`, every other control character below `0x20` as `\u00XX` in lowercase
hexadecimal, and every other character as itself. -/
def jsonChar (c : Char) : String :=
  if c == '"' then "\\\""
  else if c == '\\' then "\\\\"
  else if c == '\n' then "\\n"
  else if c == '\r' then "\\r"
  else if c == '\t' then "\\t"
  else if c.toNat == 8 then "\\b"
  else if c.toNat == 12 then "\\f"
  else if c.toNat < 0x20 then
    "\\u00" ++ String.singleton (hexDigit (c.toNat / 16)) ++ String.singleton (hexDigit (c.toNat % 16))
  else String.singleton c

/-- A string quoted as `serde_json::to_string` quotes it (crate `q`). -/
def q (s : String) : String := "\"" ++ String.join (s.toList.map jsonChar) ++ "\""

/-- Each segment of a path quoted, in brackets (crate `qpath`). -/
def qpath (path : List String) : String := "[" ++ ",".intercalate (path.map q) ++ "]"

/-- A string as Rust's `Debug` writes it (`Escape.strDebug`). -/
def debugString (s : String) : String := Escape.strDebug s

mutual

/-- A provider argument as its derived Rust `Debug` writes it (`Field(["context", "x"])`,
`Integer(5)`, `Set([String("a")])`). -/
def debugArg : Provider.Arg → String
  | .field path => "Field([" ++ ", ".intercalate (path.map debugString) ++ "])"
  | .string s => "String(" ++ debugString s ++ ")"
  | .integer i => "Integer(" ++ toString i.toInt ++ ")"
  | .decimal t => "Decimal(" ++ debugString t ++ ")"
  | .bool b => "Bool(" ++ toString b ++ ")"
  | .set items => "Set([" ++ ", ".intercalate (debugArgs items) ++ "])"

def debugArgs : List Provider.Arg → List String
  | [] => []
  | a :: rest => debugArg a :: debugArgs rest

end

/-! ## Temporal conditions -/

/-- A time unit's token. -/
def unitToken : TimeUnit → String
  | .seconds => "s" | .minutes => "m" | .hours => "h" | .days => "d"

/-- An arithmetic operator's token. -/
def arithToken : ArithOp → String
  | .add => "+" | .sub => "-" | .mul => "*"

/-- A comparison operator's token (crate `cmp`). -/
def cmpToken : CmpOp → String
  | .le => "<=" | .lt => "<" | .ge => ">=" | .gt => ">" | .eq => "==" | .ne => "!="

/-- A binder type as the crate renders it (`Type::render`). -/
def renderType : BinderType → String
  | .timepoint => "Timepoint"
  | .named path => "::".intercalate path

/-- A window (crate `within`). -/
def within : WithinSpec → String
  | .concrete i => toString i.amount.toInt ++ unitToken i.unit
  | .paramRef p => "(param " ++ q p ++ ")"

/-- The name a binder slot binds or refers to; the macro forms keep their sigil. -/
def slotName : BinderSlot → String
  | .name n => n
  | .paramRef p => "?" ++ p
  | .binderRef b => "$" ++ b

/-- The binders in scope, innermost first: each source name and its canonical index. -/
abbrev Scope := List (String × Nat)

/-- A use of a variable: `v<i>` for its innermost binder, `(free "x")` when none binds it. -/
def lookup (sc : Scope) (x : String) : String :=
  match sc.find? (·.1 == x) with
  | some (_, i) => s!"v{i}"
  | none => "(free " ++ q x ++ ")"

/-- Bind a name to the next canonical index. -/
def bind (sc : Scope) (x : String) : StateM Nat (Scope × Nat) := do
  let i ← get
  set (i + 1)
  return ((x, i) :: sc, i)

/-- A `for` list: each binder bound in turn, encoded `(v<i> "type")`. -/
def encForVars (sc : Scope) : List TypedBinder → StateM Nat (Scope × List String)
  | [] => pure (sc, [])
  | b :: rest => do
    let (sc', i) ← bind sc (slotName b.slot)
    let (sc'', enc) ← encForVars sc' rest
    return (sc'', (s!"(v{i} " ++ q (renderType b.ty) ++ ")") :: enc)

mutual

/-- The canonical encoding of a condition (crate `enc_condition`). -/
def encCond (sc : Scope) : Condition → StateM Nat String
  | ⟨_, k⟩ => encKind sc k

def encKind (sc : Scope) : ConditionKind → StateM Nat String
  | .and l r => do
    let a ← encCond sc l
    let b ← encCond sc r
    return "(and " ++ a ++ " " ++ b ++ ")"
  | .or l r => do
    let a ← encCond sc l
    let b ← encCond sc r
    return "(or " ++ a ++ " " ++ b ++ ")"
  | .not c => do
    let a ← encCond sc c
    return "(not " ++ a ++ ")"
  | .formerly w c => do
    let a ← encCond sc c
    return "(formerly " ++ within w ++ " " ++ a ++ ")"
  | .previous w c => do
    let a ← encCond sc c
    return "(previous " ++ within w ++ " " ++ a ++ ")"
  | .since l w r => do
    let a ← encCond sc l
    let b ← encCond sc r
    return "(since " ++ a ++ " " ++ within w ++ " " ++ b ++ ")"
  | .predicate ⟨_, ns, a, k, args⟩ => do
    let enc ← encArgs sc args
    return "(pred " ++ qpath ns ++ " " ++ q a ++ " " ++ q k ++ " (" ++ " ".intercalate enc ++ "))"
  | .comparison op l r => do
    let a ← encTerm sc l
    let b ← encTerm sc r
    return "(cmp " ++ cmpToken op ++ " " ++ a ++ " " ++ b ++ ")"
  | .exists x c => do
    let (sc', i) ← bind sc (slotName x.slot)
    let a ← encCond sc' c
    return s!"(exists v{i} " ++ q (renderType x.ty) ++ " " ++ a ++ ")"
  | .tp x => pure ("(tp " ++ lookup sc (slotName x) ++ ")")
  | .call ⟨_, name, args⟩ => do
    let enc ← encCallArgs sc args
    return "(call " ++ q name ++ String.join (enc.map (" " ++ ·)) ++ ")"
  | .sigilRef s n =>
    let sigil := match s with
      | .param => "Param"
      | .binder => "Binder"
    pure ("(sigil " ++ sigil ++ " " ++ q n ++ ")")
  | .refine b fs _ => do
    let a ← encCond sc b
    let enc ← encFields sc fs
    return "(refine " ++ a ++ String.join enc ++ ")"

/-- A predicate's arguments, each `("name" term)`. -/
def encArgs (sc : Scope) : List NamedArg → StateM Nat (List String)
  | [] => pure []
  | ⟨n, t⟩ :: rest => do
    let a ← encTerm sc t
    let as ← encArgs sc rest
    return ("(" ++ q n ++ " " ++ a ++ ")") :: as

/-- A refinement's fields, each ` ("name" term)`. -/
def encFields (sc : Scope) : List NamedArg → StateM Nat (List String)
  | [] => pure []
  | ⟨n, t⟩ :: rest => do
    let a ← encTerm sc t
    let as ← encFields sc rest
    return (" (" ++ q n ++ " " ++ a ++ ")") :: as

/-- The canonical encoding of a term (crate `enc_term`). -/
def encTerm (sc : Scope) : Term → StateM Nat String
  | .entity ty id => pure ("(entity " ++ q ty ++ " " ++ q id ++ ")")
  | .integer n => pure ("(int " ++ toString n.toInt ++ ")")
  | .decimal s => pure ("(decimal " ++ q s ++ ")")
  | .string s => pure ("(str " ++ q s ++ ")")
  | .bool b => pure ("(bool " ++ toString b ++ ")")
  | .contextField p => pure ("(context " ++ qpath p ++ ")")
  | .scopeField p => pure ("(scope " ++ qpath p ++ ")")
  | .var x => pure (lookup sc x)
  | .wildcard => pure "*"
  | .array items => do
    let enc ← encTerms sc items
    return "(array" ++ String.join (enc.map (" " ++ ·)) ++ ")"
  | .agg ⟨_, k⟩ => encAgg sc k
  | .arith op l r => do
    let a ← encTerm sc l
    let b ← encTerm sc r
    return "(arith " ++ arithToken op ++ " " ++ a ++ " " ++ b ++ ")"
  | .paramRef p => pure ("(param " ++ q p ++ ")")
  | .binderRef b => pure ("(binder-ref " ++ q b ++ ")")

def encTerms (sc : Scope) : List Term → StateM Nat (List String)
  | [] => pure []
  | t :: rest => do
    let a ← encTerm sc t
    let as ← encTerms sc rest
    return a :: as

/-- The canonical encoding of an aggregate (crate `enc_agg`). A `sum`'s summand is bound first,
then the `for` variables, and all scope over the body. -/
def encAgg (sc : Scope) : AggExprKind → StateM Nat String
  | .sum v vs b => do
    let (sc₁, x) ← bind sc (slotName v)
    let (sc₂, enc) ← encForVars sc₁ vs
    let a ← encCond sc₂ b
    return s!"(sum v{x} " ++ "(" ++ " ".intercalate enc ++ ") " ++ a ++ ")"
  | .count vs b => do
    let (sc', enc) ← encForVars sc vs
    let a ← encCond sc' b
    return "(count " ++ "(" ++ " ".intercalate enc ++ ") " ++ a ++ ")"
  | .call c => pure ("(agg-call " ++ q c.name ++ ")")

/-- The arguments of a macro call in condition position. -/
def encCallArgs (sc : Scope) : List CallArg → StateM Nat (List String)
  | [] => pure []
  | .condition c :: rest => do
    let a ← encCond sc c
    let as ← encCallArgs sc rest
    return a :: as
  | .within i :: rest => do
    let as ← encCallArgs sc rest
    return (toString i.amount.toInt ++ unitToken i.unit) :: as
  | .term t :: rest => do
    let a ← encTerm sc t
    let as ← encCallArgs sc rest
    return a :: as

end

/-- The canonical, span-free, alpha-normalized encoding of a temporal condition (crate
`canonical_condition`). -/
def canonicalCondition (c : Condition) : String := (encCond [] c).run' 0

/-! ## Hoisted leaves -/

/-- An action `(namespace, id)`. -/
def action (ns id : String) : String := "(" ++ q ns ++ " " ++ q id ++ ")"

def scopedAction : ScopedAction → String
  | .concrete ns id => "(concrete " ++ action ns id ++ ")"
  | .list as => "(list " ++ " ".intercalate (as.map fun (ns, id) => action ns id) ++ ")"
  | .unconstrained => "(unconstrained)"

/-- The concrete actions, encoded, sorted and free of duplicates (crate `targets`). -/
def targets (t : List (String × String)) : String :=
  let items := (t.map fun (ns, id) => action ns id).mergeSort fun a b => decide (a ≤ b)
  "(" ++ " ".intercalate items.eraseDups ++ ")"

def scopeConstraint : ScopeConstraint → String
  | .any => "(any)"
  | .isType t => "(is " ++ q t ++ ")"
  | .uid ty m => "(uid " ++ q ty ++ " " ++ toString m ++ ")"

/-- The canonical encoding of a hoisted temporal leaf: its rule's action scope, the concrete
actions it resolves to, what its principal and resource scopes admit, and its condition after pin
injection (crate `canonical_context_field`). -/
def canonicalContextField (f : ContextField) : String :=
  "(temporal (action " ++ scopedAction f.action ++ ") (targets " ++ targets f.targetActions ++
    ") (principal " ++ scopeConstraint f.principal ++ ") (resource " ++
    scopeConstraint f.resource ++ ") (condition " ++ canonicalCondition f.temporal.condition ++ "))"

/-- A provider argument list: each argument's Rust `Debug` text, quoted. -/
def providerArgs (args : List Provider.Arg) : String :=
  "(" ++ " ".intercalate (args.map fun a => q (debugArg a)) ++ ")"

/-- The canonical encoding of a hoisted provider leaf (crate `canonical_provider_field`). -/
def canonicalProviderField (f : ProviderField) : String :=
  let methods := f.methods.map fun m => "(" ++ q m.name ++ " " ++ providerArgs m.args ++ ")"
  "(provider " ++ qpath f.invocation.function ++ " " ++ providerArgs f.invocation.args ++
    " (methods " ++ " ".intercalate methods ++ ") (type " ++ q f.cedarType ++ ") (action " ++
    scopedAction f.action ++ ") (targets " ++ targets f.targetActions ++ ") (principal " ++
    scopeConstraint f.principal ++ ") (resource " ++ scopeConstraint f.resource ++ "))"

/-- The canonical name of a hoisted field minted under `ruleKey`: the key replaced by `dw`
(crate `canonical_field_name`). -/
def canonicalFieldName (ruleKey fieldName : String) : String :=
  match fieldName.dropPrefix? ruleKey with
  | some suffix => "dw" ++ suffix.toString
  | none => fieldName

/-- Append `entry` to the list at index `k` (no change when `k` is out of range). -/
def pushAt {α : Type} (acc : List (List α)) (k : Nat) (entry : α) : List (List α) :=
  acc.set k (acc.getD k [] ++ [entry])

/-- Each rule's hoisted leaves as `(canonical field name, canonical encoding)`, temporal leaves
first, as `lower_entry` computes them (crate `canonical_field_name`, `canonical_context_field`,
`canonical_provider_field`). `pinned` are the context fields after pin injection. -/
def leaves (c : Cedarified) (pinned : List ContextField) : Result (List (List (String × String))) :=
  let key := fun k => c.ruleKeys.getD k ""
  let init : List (List (String × String)) := List.replicate c.ruleIds.length []
  let withTemporal := (pinned.zip c.temporalRules).foldl (init := init) fun acc (f, k) =>
    pushAt acc k (canonicalFieldName (key k) f.fieldName, canonicalContextField f)
  let all := (c.providerFields.zip c.providerRules).foldl (init := withTemporal) fun acc (f, k) =>
    pushAt acc k (canonicalFieldName (key k) f.fieldName, canonicalProviderField f)
  pure all

/-! ## Revisions and content hashes -/

/-- The version tag of a rule revision (crate `REVISION_TAG`). -/
def revisionTag : String := "dogwood-rule-revision/1"

/-- The version tag of a leaf content hash (crate `LEAF_TAG`). -/
def leafTag : String := "dogwood-temporal-leaf/1"

/-- The revision of one rule: SHA-256 over the tag, its canonical Cedar text, quoted, and each of
its leaves as `"name" encoding`, one per line (crate `rule_revision`). -/
def ruleRevision (canonicalCedar : String) (leaves : List (String × String)) : String :=
  Sha256.hex (revisionTag ++ "\n" ++ q canonicalCedar ++ "\n" ++
    String.join (leaves.map fun (name, enc) => q name ++ " " ++ enc ++ "\n"))

/-- Each rule's revision, from its canonical Cedar text and its leaves. -/
def ruleRevisions (canonical : List String) (leaves : List (List (String × String))) : List String :=
  (canonical.zip leaves).map fun (c, ls) => ruleRevision c ls

/-- The content hash of a temporal leaf of the lowered set: SHA-256 over the tag and the leaf's
canonical encoding, the same parts as `canonicalContextField` (crate `temporal_field_hash`). -/
def contentHash (f : TemporalField) : String :=
  Sha256.hex (leafTag ++ "\n" ++ "(temporal (action " ++ scopedAction f.action ++ ") (targets " ++
    targets f.targetActions ++ ") (principal " ++ scopeConstraint f.principal ++ ") (resource " ++
    scopeConstraint f.resource ++ ") (condition " ++ canonicalCondition f.condition.condition ++ "))")

end Dogwood.Frontend.RuleIdentity
