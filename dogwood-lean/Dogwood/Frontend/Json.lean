import Dogwood.Frontend.Types
import Dogwood.Conformance.Json

/-!
# The JSON form of the crate's frontend export

`bridge/ --frontend` writes, for each bundle, the crate's export of its frontend
(`dogwood_language::frontend_export`). This module decodes every type the export writes, and
encodes each back, in one encoding: a constructor without arguments is its name, any other
constructor a one-key object holding its arguments by name, a structure an object of its fields,
an optional value `null` when absent, a pair a two-element array, and a map an array of
`[key, value]` pairs. Cedar's values, names and scope constraints use the encoding of
`Dogwood.Conformance.Json`.

Most instances are derived. The recursive types (the temporal AST, surface expressions, the
event-schema DSL's fields, provider parameter types and arguments, schema types, derived field
trees) have hand-written decoders, total by well-founded recursion on the size of the JSON value
they read (the accessors of `Dogwood.Conformance.JsonSize`), and structural encoders.

The differential harness compares two values by comparing their encodings
(`Dogwood.Frontend.Diff`).
-/

namespace Dogwood.Frontend

open Lean (Json FromJson ToJson fromJson? toJson)
open Dogwood.Conformance (getObjValS getArrS getArrValS ctorOfS ctor)

/-- The field `k` of an object, decoded. -/
def field {α : Type} [FromJson α] (j : Json) (k : String) : Except String α := do
  fromJson? (← j.getObjVal? k)

/-- A JSON array of encodings. -/
def arr (xs : List Json) : Json := Lean.Json.arr xs.toArray

/-! ## Non-recursive types -/

deriving instance FromJson, ToJson for Span

namespace Surface.Temporal
deriving instance FromJson, ToJson for Interval, WithinSpec, BinderSlot, TypedBinder, Sigil
end Surface.Temporal

namespace Surface
deriving instance FromJson, ToJson for UnOp, BinOp, ActionConstraint, Annotation, MacroParam
end Surface

deriving instance FromJson, ToJson for Cedar.Spec.EntityUIDOrSlot, Cedar.Spec.ScopeTemplate

namespace EventSchemaDsl
deriving instance FromJson, ToJson for Selector, PinRoot, PinValue
end EventSchemaDsl

namespace CedarSchema
deriving instance FromJson, ToJson for ActionUid
end CedarSchema

deriving instance FromJson, ToJson for FieldType, Pin, ScopedAction, ScopeConstraint, Identity,
  Stage, Category, PolicyIdKind, PolicyIdInfo, Error, ContextRead

/-! ## The temporal AST -/

namespace Surface.Temporal

mutual

def conditionToJson : Condition → Json
  | ⟨sp, k⟩ => Json.mkObj [("span", toJson sp), ("kind", conditionKindToJson k)]

def conditionKindToJson : ConditionKind → Json
  | .and l r => ctor "and" [("left", conditionToJson l), ("right", conditionToJson r)]
  | .or l r => ctor "or" [("left", conditionToJson l), ("right", conditionToJson r)]
  | .not c => ctor "not" [("inner", conditionToJson c)]
  | .formerly w c => ctor "formerly" [("within", toJson w), ("body", conditionToJson c)]
  | .previous w c => ctor "previous" [("within", toJson w), ("body", conditionToJson c)]
  | .since l w r =>
    ctor "since" [("left", conditionToJson l), ("within", toJson w), ("right", conditionToJson r)]
  | .predicate p => ctor "predicate" [("p", predicateToJson p)]
  | .comparison op l r =>
    ctor "comparison" [("op", toJson op), ("left", termToJson l), ("right", termToJson r)]
  | .exists x c => ctor "exists" [("var", toJson x), ("body", conditionToJson c)]
  | .tp x => ctor "tp" [("var", toJson x)]
  | .call c => ctor "call" [("c", callToJson c)]
  | .sigilRef s n => ctor "sigilRef" [("sigil", toJson s), ("name", toJson n)]
  | .refine b fs sp =>
    ctor "refine" [("base", conditionToJson b), ("fields", arr (namedArgsToJson fs)),
      ("span", toJson sp)]

def predicateToJson : Predicate → Json
  | ⟨sp, ns, a, k, args⟩ =>
    Json.mkObj [("span", toJson sp), ("namespace", toJson ns), ("action", toJson a),
      ("kind", toJson k), ("args", arr (namedArgsToJson args))]

def namedArgsToJson : List NamedArg → List Json
  | [] => []
  | ⟨n, t⟩ :: rest => Json.mkObj [("name", toJson n), ("value", termToJson t)] :: namedArgsToJson rest

def termToJson : Term → Json
  | .entity ty id => ctor "entity" [("ty", toJson ty), ("id", toJson id)]
  | .integer i => ctor "integer" [("i", toJson i)]
  | .decimal t => ctor "decimal" [("text", toJson t)]
  | .string s => ctor "string" [("s", toJson s)]
  | .bool b => ctor "bool" [("b", toJson b)]
  | .contextField p => ctor "contextField" [("path", toJson p)]
  | .scopeField p => ctor "scopeField" [("path", toJson p)]
  | .var x => ctor "var" [("x", toJson x)]
  | .wildcard => "wildcard"
  | .array xs => ctor "array" [("items", arr (termsToJson xs))]
  | .agg a => ctor "agg" [("a", aggExprToJson a)]
  | .arith op l r => ctor "arith" [("op", toJson op), ("left", termToJson l), ("right", termToJson r)]
  | .paramRef n => ctor "paramRef" [("name", toJson n)]
  | .binderRef n => ctor "binderRef" [("name", toJson n)]

def termsToJson : List Term → List Json
  | [] => []
  | t :: rest => termToJson t :: termsToJson rest

def aggExprToJson : AggExpr → Json
  | ⟨sp, k⟩ => Json.mkObj [("span", toJson sp), ("kind", aggExprKindToJson k)]

def aggExprKindToJson : AggExprKind → Json
  | .sum v vs b => ctor "sum" [("boundVar", toJson v), ("forVars", toJson vs), ("body", conditionToJson b)]
  | .count vs b => ctor "count" [("forVars", toJson vs), ("body", conditionToJson b)]
  | .call c => ctor "call" [("c", callToJson c)]

def callToJson : Call → Json
  | ⟨sp, n, args⟩ => Json.mkObj [("span", toJson sp), ("name", toJson n), ("args", arr (callArgsToJson args))]

def callArgsToJson : List CallArg → List Json
  | [] => []
  | .condition c :: rest => ctor "condition" [("c", conditionToJson c)] :: callArgsToJson rest
  | .within i :: rest => ctor "within" [("i", toJson i)] :: callArgsToJson rest
  | .term t :: rest => ctor "term" [("t", termToJson t)] :: callArgsToJson rest

end

mutual

def conditionOfJson (j : Json) : Except String Condition := do
  let sp ← field j "span"
  let ⟨k, _⟩ ← getObjValS j "kind"
  return ⟨sp, ← conditionKindOfJson k⟩
termination_by sizeOf j
decreasing_by all_goals (simp_wf; omega)

def conditionKindOfJson (j : Json) : Except String ConditionKind := do
  let (c, ⟨a, _⟩) ← ctorOfS j
  match c with
  | "and" | "or" => do
    let ⟨l, _⟩ ← getObjValS a "left"
    let l ← conditionOfJson l
    let ⟨r, _⟩ ← getObjValS a "right"
    let r ← conditionOfJson r
    return if c == "and" then .and l r else .or l r
  | "not" => do
    let ⟨x, _⟩ ← getObjValS a "inner"
    return .not (← conditionOfJson x)
  | "formerly" | "previous" => do
    let w ← field a "within"
    let ⟨b, _⟩ ← getObjValS a "body"
    let b ← conditionOfJson b
    return if c == "formerly" then .formerly w b else .previous w b
  | "since" => do
    let ⟨l, _⟩ ← getObjValS a "left"
    let l ← conditionOfJson l
    let w ← field a "within"
    let ⟨r, _⟩ ← getObjValS a "right"
    return .since l w (← conditionOfJson r)
  | "predicate" => do
    let ⟨p, _⟩ ← getObjValS a "p"
    return .predicate (← predicateOfJson p)
  | "comparison" => do
    let op ← field a "op"
    let ⟨l, _⟩ ← getObjValS a "left"
    let l ← termOfJson l
    let ⟨r, _⟩ ← getObjValS a "right"
    return .comparison op l (← termOfJson r)
  | "exists" => do
    let x ← field a "var"
    let ⟨b, _⟩ ← getObjValS a "body"
    return .exists x (← conditionOfJson b)
  | "tp" => return .tp (← field a "var")
  | "call" => do
    let ⟨x, _⟩ ← getObjValS a "c"
    return .call (← callOfJson x)
  | "sigilRef" => return .sigilRef (← field a "sigil") (← field a "name")
  | "refine" => do
    let ⟨b, _⟩ ← getObjValS a "base"
    let b ← conditionOfJson b
    let ⟨fs, _⟩ ← getObjValS a "fields"
    let fs ← namedArgsOfJson fs
    return .refine b fs (← field a "span")
  | _ => throw s!"unknown condition {c}"
termination_by sizeOf j
decreasing_by all_goals (simp_wf; omega)

def predicateOfJson (j : Json) : Except String Predicate := do
  let ⟨args, _⟩ ← getObjValS j "args"
  return ⟨← field j "span", ← field j "namespace", ← field j "action", ← field j "kind",
    ← namedArgsOfJson args⟩
termination_by sizeOf j
decreasing_by all_goals (simp_wf; omega)

def namedArgsOfJson (j : Json) : Except String (List NamedArg) := do
  let items ← getArrS j
  items.toList.mapM fun ⟨x, _⟩ => do
    let ⟨v, _⟩ ← getObjValS x "value"
    return ⟨← field x "name", ← termOfJson v⟩
termination_by sizeOf j
decreasing_by all_goals (simp_wf; omega)

def termOfJson (j : Json) : Except String Term := do
  let (c, ⟨a, _⟩) ← ctorOfS j
  match c with
  | "entity" => return .entity (← field a "ty") (← field a "id")
  | "integer" => return .integer (← field a "i")
  | "decimal" => return .decimal (← field a "text")
  | "string" => return .string (← field a "s")
  | "bool" => return .bool (← field a "b")
  | "contextField" => return .contextField (← field a "path")
  | "scopeField" => return .scopeField (← field a "path")
  | "var" => return .var (← field a "x")
  | "wildcard" => return .wildcard
  | "array" => do
    let ⟨xs, _⟩ ← getObjValS a "items"
    return .array (← termsOfJson xs)
  | "agg" => do
    let ⟨x, _⟩ ← getObjValS a "a"
    return .agg (← aggExprOfJson x)
  | "arith" => do
    let op ← field a "op"
    let ⟨l, _⟩ ← getObjValS a "left"
    let l ← termOfJson l
    let ⟨r, _⟩ ← getObjValS a "right"
    return .arith op l (← termOfJson r)
  | "paramRef" => return .paramRef (← field a "name")
  | "binderRef" => return .binderRef (← field a "name")
  | _ => throw s!"unknown term {c}"
termination_by sizeOf j
decreasing_by all_goals (simp_wf; omega)

def termsOfJson (j : Json) : Except String (List Term) := do
  let items ← getArrS j
  items.toList.mapM fun ⟨x, _⟩ => termOfJson x
termination_by sizeOf j
decreasing_by all_goals (simp_wf; omega)

def aggExprOfJson (j : Json) : Except String AggExpr := do
  let sp ← field j "span"
  let ⟨k, _⟩ ← getObjValS j "kind"
  let (c, ⟨a, _⟩) ← ctorOfS k
  match c with
  | "sum" => do
    let v ← field a "boundVar"
    let vs ← field a "forVars"
    let ⟨b, _⟩ ← getObjValS a "body"
    return ⟨sp, .sum v vs (← conditionOfJson b)⟩
  | "count" => do
    let vs ← field a "forVars"
    let ⟨b, _⟩ ← getObjValS a "body"
    return ⟨sp, .count vs (← conditionOfJson b)⟩
  | "call" => do
    let ⟨x, _⟩ ← getObjValS a "c"
    return ⟨sp, .call (← callOfJson x)⟩
  | _ => throw s!"unknown aggregation {c}"
termination_by sizeOf j
decreasing_by all_goals (simp_wf; omega)

def callOfJson (j : Json) : Except String Call := do
  let ⟨args, _⟩ ← getObjValS j "args"
  let items ← getArrS args
  let args ← items.toList.mapM fun ⟨x, _⟩ => do
    let (c, ⟨a, _⟩) ← ctorOfS x
    match c with
    | "condition" => do
      let ⟨y, _⟩ ← getObjValS a "c"
      return CallArg.condition (← conditionOfJson y)
    | "within" => return CallArg.within (← field a "i")
    | "term" => do
      let ⟨y, _⟩ ← getObjValS a "t"
      return CallArg.term (← termOfJson y)
    | _ => throw s!"unknown call argument {c}"
  return ⟨← field j "span", ← field j "name", args⟩
termination_by sizeOf j
decreasing_by all_goals (simp_wf; omega)

end

instance : ToJson Condition := ⟨conditionToJson⟩
instance : FromJson Condition := ⟨conditionOfJson⟩
instance : ToJson Term := ⟨termToJson⟩
instance : FromJson Term := ⟨termOfJson⟩

deriving instance FromJson, ToJson for Block

end Surface.Temporal

/-! ## Surface expressions -/

namespace Surface

open Dogwood.Conformance (primOfJson primToJson)

mutual

def exprToJson : Expr → Json
  | ⟨k, sp⟩ => Json.mkObj [("kind", exprKindToJson k), ("span", toJson sp)]

def exprKindToJson : ExprKind → Json
  | .lit l => ctor "lit" [("l", primToJson l)]
  | .var v => ctor "var" [("v", toJson v)]
  | .slot s => ctor "slot" [("id", toJson s)]
  | .extension t => ctor "extension" [("t", toJson t)]
  | .unaryApp op e => ctor "unaryApp" [("op", toJson op), ("expr", exprToJson e)]
  | .binaryApp op l r => ctor "binaryApp" [("op", toJson op), ("left", exprToJson l), ("right", exprToJson r)]
  | .getAttr e a => ctor "getAttr" [("expr", exprToJson e), ("attr", toJson a)]
  | .hasAttr e as => ctor "hasAttr" [("expr", exprToJson e), ("attrs", toJson as)]
  | .like e p => ctor "like" [("expr", exprToJson e), ("pattern", toJson p)]
  | .is e t none => ctor "is" [("expr", exprToJson e), ("entityType", toJson t), ("inExpr", Json.null)]
  | .is e t (some x) => ctor "is" [("expr", exprToJson e), ("entityType", toJson t), ("inExpr", exprToJson x)]
  | .ite c t e => ctor "ite" [("cond", exprToJson c), ("thenExpr", exprToJson t), ("elseExpr", exprToJson e)]
  | .set xs => ctor "set" [("items", arr (exprsToJson xs))]
  | .record m => ctor "record" [("entries", arr (entriesToJson m))]
  | .call n args => ctor "call" [("name", toJson n), ("args", arr (exprsToJson args))]
  | .methodCall r m args =>
    ctor "methodCall" [("receiver", exprToJson r), ("method", toJson m), ("args", arr (exprsToJson args))]
  | .paramRef n => ctor "paramRef" [("name", toJson n)]

def exprsToJson : List Expr → List Json
  | [] => []
  | e :: rest => exprToJson e :: exprsToJson rest

def entriesToJson : List (String × Expr) → List Json
  | [] => []
  | (k, e) :: rest => Lean.Json.arr #[toJson k, exprToJson e] :: entriesToJson rest

end

mutual

def exprOfJson (j : Json) : Except String Expr := do
  let ⟨k, _⟩ ← getObjValS j "kind"
  let k ← exprKindOfJson k
  return ⟨k, ← field j "span"⟩
termination_by sizeOf j
decreasing_by all_goals (simp_wf; omega)

def exprKindOfJson (j : Json) : Except String ExprKind := do
  let (c, ⟨a, _⟩) ← ctorOfS j
  match c with
  | "lit" => return .lit (← primOfJson (← a.getObjVal? "l"))
  | "var" => return .var (← field a "v")
  | "slot" => return .slot (← field a "id")
  | "extension" => return .extension (← field a "t")
  | "unaryApp" => do
    let ⟨e, _⟩ ← getObjValS a "expr"
    return .unaryApp (← field a "op") (← exprOfJson e)
  | "binaryApp" => do
    let ⟨l, _⟩ ← getObjValS a "left"
    let l ← exprOfJson l
    let ⟨r, _⟩ ← getObjValS a "right"
    return .binaryApp (← field a "op") l (← exprOfJson r)
  | "getAttr" => do
    let ⟨e, _⟩ ← getObjValS a "expr"
    return .getAttr (← exprOfJson e) (← field a "attr")
  | "hasAttr" => do
    let ⟨e, _⟩ ← getObjValS a "expr"
    return .hasAttr (← exprOfJson e) (← field a "attrs")
  | "like" => do
    let ⟨e, _⟩ ← getObjValS a "expr"
    return .like (← exprOfJson e) (← field a "pattern")
  | "is" => do
    let ⟨e, _⟩ ← getObjValS a "expr"
    let e ← exprOfJson e
    let ⟨x, _⟩ ← getObjValS a "inExpr"
    let x ← match x with
      | .null => pure none
      | _ => some <$> exprOfJson x
    return .is e (← field a "entityType") x
  | "ite" => do
    let ⟨c', _⟩ ← getObjValS a "cond"
    let c' ← exprOfJson c'
    let ⟨t, _⟩ ← getObjValS a "thenExpr"
    let t ← exprOfJson t
    let ⟨e, _⟩ ← getObjValS a "elseExpr"
    return .ite c' t (← exprOfJson e)
  | "set" => do
    let ⟨xs, _⟩ ← getObjValS a "items"
    return .set (← exprsOfJson xs)
  | "record" => do
    let ⟨xs, _⟩ ← getObjValS a "entries"
    let items ← getArrS xs
    let entries ← items.toList.mapM fun ⟨p, _⟩ => do
      let k : String ← fromJson? (← p.getArrVal? 0)
      let ⟨v, _⟩ ← getArrValS p 1
      return (k, ← exprOfJson v)
    return .record entries
  | "call" => do
    let ⟨xs, _⟩ ← getObjValS a "args"
    return .call (← field a "name") (← exprsOfJson xs)
  | "methodCall" => do
    let ⟨r, _⟩ ← getObjValS a "receiver"
    let r ← exprOfJson r
    let ⟨xs, _⟩ ← getObjValS a "args"
    return .methodCall r (← field a "method") (← exprsOfJson xs)
  | "paramRef" => return .paramRef (← field a "name")
  | _ => throw s!"unknown expression {c}"
termination_by sizeOf j
decreasing_by all_goals (simp_wf; omega)

def exprsOfJson (j : Json) : Except String (List Expr) := do
  let items ← getArrS j
  items.toList.mapM fun ⟨x, _⟩ => exprOfJson x
termination_by sizeOf j
decreasing_by all_goals (simp_wf; omega)

end

instance : ToJson Expr := ⟨exprToJson⟩
instance : FromJson Expr := ⟨exprOfJson⟩

deriving instance FromJson, ToJson for Scope, Cond, Policy, MacroBody, MacroDef, PolicySet

end Surface

/-! ## Provider invocations -/

namespace Provider

def argToJson : Arg → Json
  | .field p => ctor "field" [("path", toJson p)]
  | .string s => ctor "string" [("s", toJson s)]
  | .integer i => ctor "integer" [("i", toJson i)]
  | .decimal t => ctor "decimal" [("text", toJson t)]
  | .bool b => ctor "bool" [("b", toJson b)]
  | .set xs => ctor "set" [("items", arr (argsToJson xs))]
where
  argsToJson : List Arg → List Json
    | [] => []
    | x :: rest => argToJson x :: argsToJson rest

def argOfJson (j : Json) : Except String Arg := do
  let (c, ⟨a, _⟩) ← ctorOfS j
  match c with
  | "field" => return .field (← field a "path")
  | "string" => return .string (← field a "s")
  | "integer" => return .integer (← field a "i")
  | "decimal" => return .decimal (← field a "text")
  | "bool" => return .bool (← field a "b")
  | "set" => do
    let ⟨xs, _⟩ ← getObjValS a "items"
    let items ← getArrS xs
    return .set (← items.toList.mapM fun ⟨x, _⟩ => argOfJson x)
  | _ => throw s!"unknown provider argument {c}"
termination_by sizeOf j
decreasing_by all_goals (simp_wf; omega)

instance : ToJson Arg := ⟨argToJson⟩
instance : FromJson Arg := ⟨argOfJson⟩

deriving instance FromJson, ToJson for Invocation, MethodCall

end Provider

/-! ## The event-schema DSL -/

namespace EventSchemaDsl

mutual

def fieldSpecToJson : FieldSpec → Json
  | .spread s sp => ctor "spread" [("selector", toJson s), ("span", toJson sp)]
  | .named n ty pin sp =>
    ctor "named" [("name", toJson n), ("ty", typeExprToJson ty), ("pin", toJson pin), ("span", toJson sp)]

def typeExprToJson : TypeExpr → Json
  | .selector s => ctor "selector" [("s", toJson s)]
  | .concrete p => ctor "concrete" [("path", toJson p)]
  | .record fs => ctor "record" [("fields", arr (fieldSpecsToJson fs))]

def fieldSpecsToJson : List FieldSpec → List Json
  | [] => []
  | f :: rest => fieldSpecToJson f :: fieldSpecsToJson rest

end

mutual

def fieldSpecOfJson (j : Json) : Except String FieldSpec := do
  let (c, ⟨a, _⟩) ← ctorOfS j
  match c with
  | "spread" => return .spread (← field a "selector") (← field a "span")
  | "named" => do
    let ⟨ty, _⟩ ← getObjValS a "ty"
    let ty ← typeExprOfJson ty
    return .named (← field a "name") ty (← field a "pin") (← field a "span")
  | _ => throw s!"unknown field {c}"
termination_by sizeOf j
decreasing_by all_goals (simp_wf; omega)

def typeExprOfJson (j : Json) : Except String TypeExpr := do
  let (c, ⟨a, _⟩) ← ctorOfS j
  match c with
  | "selector" => return .selector (← field a "s")
  | "concrete" => return .concrete (← field a "path")
  | "record" => do
    let ⟨fs, _⟩ ← getObjValS a "fields"
    let items ← getArrS fs
    return .record (← items.toList.mapM fun ⟨x, _⟩ => fieldSpecOfJson x)
  | _ => throw s!"unknown field type {c}"
termination_by sizeOf j
decreasing_by all_goals (simp_wf; omega)

end

instance : ToJson FieldSpec := ⟨fieldSpecToJson⟩
instance : FromJson FieldSpec := ⟨fieldSpecOfJson⟩

deriving instance FromJson, ToJson for EventDecl, EventSchema

end EventSchemaDsl

/-! ## Provider declarations -/

namespace ProviderDecls

mutual

def paramTypeToJson : ParamType → Json
  | ⟨k, fields, items, required, et⟩ =>
    Json.mkObj [("paramType", toJson k), ("fields", arr (paramFieldsToJson fields)),
      ("items", paramTypeOptToJson items), ("required", toJson required), ("entityType", toJson et)]

def paramTypeOptToJson : Option ParamType → Json
  | none => Json.null
  | some p => paramTypeToJson p

def paramFieldsToJson : List (String × ParamType) → List Json
  | [] => []
  | (k, p) :: rest => Lean.Json.arr #[toJson k, paramTypeToJson p] :: paramFieldsToJson rest

end

def paramTypeOfJson (j : Json) : Except String ParamType := do
  let ⟨fs, _⟩ ← getObjValS j "fields"
  let items ← getArrS fs
  let fields ← items.toList.mapM fun ⟨p, _⟩ => do
    let k : String ← fromJson? (← p.getArrVal? 0)
    let ⟨v, _⟩ ← getArrValS p 1
    return (k, ← paramTypeOfJson v)
  let ⟨it, _⟩ ← getObjValS j "items"
  let it ← match it with
    | .null => pure none
    | _ => some <$> paramTypeOfJson it
  return ⟨← field j "paramType", fields, it, ← field j "required", ← field j "entityType"⟩
termination_by sizeOf j
decreasing_by all_goals (simp_wf; omega)

instance : ToJson ParamType := ⟨paramTypeToJson⟩
instance : FromJson ParamType := ⟨paramTypeOfJson⟩

deriving instance FromJson, ToJson for MethodDecl, Implementation, ProviderDecl, EntityTypeDecl,
  Declarations

end ProviderDecls

/-! ## Cedar schema fragments -/

namespace CedarSchema

mutual

def schemaTypeToJson : SchemaType → Json
  | .commonRef n => ctor "commonRef" [("name", toJson n)]
  | .string => "string"
  | .long => "long"
  | .boolean => "boolean"
  | .set t => ctor "set" [("element", schemaTypeToJson t)]
  | .record attrs add =>
    ctor "record" [("attributes", arr (attrsToJson attrs)), ("additionalAttributes", toJson add)]
  | .entity n => ctor "entity" [("name", toJson n)]
  | .entityOrCommon n => ctor "entityOrCommon" [("name", toJson n)]
  | .extension n => ctor "extension" [("name", toJson n)]

def attrsToJson : List (String × AttrType) → List Json
  | [] => []
  | (k, ⟨t, req, anns⟩) :: rest =>
    Lean.Json.arr #[toJson k, Json.mkObj [("ty", schemaTypeToJson t), ("required", toJson req),
      ("annotations", toJson anns)]] :: attrsToJson rest

end

def schemaTypeOfJson (j : Json) : Except String SchemaType := do
  let (c, ⟨a, _⟩) ← ctorOfS j
  match c with
  | "commonRef" => return .commonRef (← field a "name")
  | "string" => return .string
  | "long" => return .long
  | "boolean" => return .boolean
  | "set" => do
    let ⟨t, _⟩ ← getObjValS a "element"
    return .set (← schemaTypeOfJson t)
  | "record" => do
    let ⟨xs, _⟩ ← getObjValS a "attributes"
    let items ← getArrS xs
    let attrs ← items.toList.mapM fun ⟨p, _⟩ => do
      let k : String ← fromJson? (← p.getArrVal? 0)
      let ⟨q, _⟩ ← getArrValS p 1
      let ⟨t, _⟩ ← getObjValS q "ty"
      let t ← schemaTypeOfJson t
      return (k, ⟨t, ← field q "required", ← field q "annotations"⟩)
    return .record attrs (← field a "additionalAttributes")
  | "entity" => return .entity (← field a "name")
  | "entityOrCommon" => return .entityOrCommon (← field a "name")
  | "extension" => return .extension (← field a "name")
  | _ => throw s!"unknown schema type {c}"
termination_by sizeOf j
decreasing_by all_goals (simp_wf; omega)

instance : ToJson SchemaType := ⟨schemaTypeToJson⟩
instance : FromJson SchemaType := ⟨schemaTypeOfJson⟩

deriving instance FromJson, ToJson for CommonType, EntityTypeKind, EntityTypeDef, ApplySpec,
  ActionDef, NamespaceDef

end CedarSchema

/-! ## Derived event schemas and hoisted fields -/

mutual

def derivedFieldNodeToJson : DerivedFieldNode → Json
  | .leaf t => ctor "leaf" [("ty", toJson t)]
  | .group ms => ctor "group" [("members", arr (derivedMembersToJson ms))]

def derivedMembersToJson : List (String × DerivedFieldNode) → List Json
  | [] => []
  | (k, n) :: rest => Lean.Json.arr #[toJson k, derivedFieldNodeToJson n] :: derivedMembersToJson rest

end

def derivedFieldNodeOfJson (j : Json) : Except String DerivedFieldNode := do
  let (c, ⟨a, _⟩) ← ctorOfS j
  match c with
  | "leaf" => return .leaf (← field a "ty")
  | "group" => do
    let ⟨xs, _⟩ ← getObjValS a "members"
    let items ← getArrS xs
    let ms ← items.toList.mapM fun ⟨p, _⟩ => do
      let k : String ← fromJson? (← p.getArrVal? 0)
      let ⟨v, _⟩ ← getArrValS p 1
      return (k, ← derivedFieldNodeOfJson v)
    return .group ms
  | _ => throw s!"unknown field node {c}"
termination_by sizeOf j
decreasing_by all_goals (simp_wf; omega)

instance : ToJson DerivedFieldNode := ⟨derivedFieldNodeToJson⟩
instance : FromJson DerivedFieldNode := ⟨derivedFieldNodeOfJson⟩

deriving instance FromJson, ToJson for DerivedEvent, DerivedEventSchema, EventSignature,
  ContextField, ProviderField, ResolvedProvider, TemporalField, LoweredProviderField

end Dogwood.Frontend
