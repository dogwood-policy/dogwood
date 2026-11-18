/-
Differential check of the conformance JSON functions: the earlier `partial`
definitions (copied verbatim, renamed `old_*`) against the total ones of
`Dogwood.Conformance.Json`, on random JSON trees (shapes the encoders write, mutated, and noise)
and on the encodings of every value they decode. Run from `dogwood-lean/`:
`lake env lean --run conformance/JsonTotalCheck.lean [count] [seed]`.
-/
import Dogwood.Conformance.JsonRoundTrip

open Lean (Json ToJson FromJson toJson fromJson?)
open Cedar.Spec Cedar.Data
open Dogwood.Spec Dogwood.Spec.Temporal

namespace Dogwood.Conformance.OldJson
open Dogwood.Conformance (ctor ctorOf arg primOfJson decimalValue extensionValue extTypeOfName)
open Cedar.Validation (CedarType ExtType Qualified QualifiedType RecordType)
instance : Inhabited Formula := ⟨.tp ""⟩
instance : Inhabited Term := ⟨.wildcard⟩
instance : Inhabited Aggregate := ⟨.count [] (.tp "")⟩

partial def old_valueOfJson (j : Json) : Except String Value := do
  match j.getObjVal? "set", j.getObjVal? "record", j.getObjVal? "decimal",
      j.getObjVal? "extension" with
  | .ok s, _, _, _ =>
    let items ← s.getArr?
    pure (.set (Set.make (← items.toList.mapM old_valueOfJson)))
  | _, .ok r, _, _ =>
    let fields ← r.getArr?
    let kvs ← fields.toList.mapM fun f => do
      pure ((← fromJson? (← f.getArrVal? 0) : String), ← old_valueOfJson (← f.getArrVal? 1))
    pure (.record (Map.make kvs))
  | _, _, .ok d, _ => decimalValue <$> fromJson? d
  | _, _, _, .ok x => do
    pure (extensionValue (← fromJson? (← x.getObjVal? "fn")) (← fromJson? (← x.getObjVal? "arg")))
  | _, _, _, _ => (.prim ·) <$> primOfJson j

partial def old_valueToJson : Value → Json
  | .prim p => primToJson p
  | .set s => Json.mkObj [("set", Json.arr (s.toList.map old_valueToJson).toArray)]
  | .record m =>
    Json.mkObj [("record", Json.arr (m.toList.map fun (k, v) => Json.arr #[toJson k, old_valueToJson v]).toArray)]
  | .ext (.decimal d) => Json.mkObj [("decimal", toJson (toString d))]
  | .ext x => Json.mkObj [("unsupported", toJson (toString (repr x)))]

partial def old_cedarTypeOfJson (j : Json) : Except String CedarType := do
  match j with
  | .str "bool" => pure (.bool .anyBool)
  | .str "long" => pure .int
  | .str "string" => pure .string
  | _ =>
    match j.getObjVal? "set", j.getObjVal? "entity", j.getObjVal? "record", j.getObjVal? "ext" with
    | .ok t, _, _, _ => .set <$> old_cedarTypeOfJson t
    | _, .ok e, _, _ => .entity <$> fromJson? e
    | _, _, .ok r, _ => .record <$> recordTypeOfJson r
    | _, _, _, .ok x => .ext <$> (extTypeOfName (← fromJson? x))
    | _, _, _, _ => throw s!"not a cedar type: {j.compress}"
where
  recordTypeOfJson (r : Json) : Except String RecordType := do
    let fields ← r.getArr?
    let kvs ← fields.toList.mapM fun f => do
      let k : String ← fromJson? (← f.getArrVal? 0)
      let q ← f.getArrVal? 1
      let ty ← old_cedarTypeOfJson (← q.getObjVal? "ty")
      let req : Bool ← fromJson? (← q.getObjVal? "required")
      pure (k, if req then Qualified.required ty else Qualified.optional ty)
    pure (Map.make kvs)

partial def old_cedarTypeToJson : CedarType → Json
  | .bool _ => "bool"
  | .int => "long"
  | .string => "string"
  | .set t => Json.mkObj [("set", old_cedarTypeToJson t)]
  | .entity e => Json.mkObj [("entity", toJson e)]
  | .record r => Json.mkObj [("record", Json.arr (r.toList.map fun (k, q) =>
      Json.arr #[toJson k, Json.mkObj [("ty", old_cedarTypeToJson q.getType),
        ("required", toJson q.isRequired)]]).toArray)]
  | .ext x => Json.mkObj [("ext", toJson (match x with
      | .decimal => "decimal" | .ipAddr => "ipaddr" | .datetime => "datetime"
      | .duration => "duration"))]

mutual

partial def old_termToJson : Term → Json
  | .entity uid => ctor "entity" [("uid", toJson uid)]
  | .long i => ctor "long" [("i", toJson i)]
  | .decimal t => ctor "decimal" [("text", toJson t)]
  | .string s => ctor "string" [("s", toJson s)]
  | .bool b => ctor "bool" [("b", toJson b)]
  | .context p => ctor "context" [("path", toJson p)]
  | .scope r p => ctor "scope" [("root", toJson r), ("path", toJson p)]
  | .var x => ctor "var" [("x", toJson x)]
  | .wildcard => "wildcard"
  | .agg a => ctor "agg" [("a", old_aggregateToJson a)]
  | .arith op l r => ctor "arith" [("op", toJson op), ("l", old_termToJson l), ("r", old_termToJson r)]

partial def old_aggregateToJson : Aggregate → Json
  | .count dom body => ctor "count" [("domain", toJson dom), ("body", old_formulaToJson body)]
  | .sum s dom body =>
    ctor "sum" [("summand", toJson s), ("domain", toJson dom), ("body", old_formulaToJson body)]

partial def old_formulaToJson : Formula → Json
  | .and φ ψ => ctor "and" [("φ", old_formulaToJson φ), ("ψ", old_formulaToJson ψ)]
  | .not φ => ctor "not" [("φ", old_formulaToJson φ)]
  | .formerly w φ => ctor "formerly" [("w", toJson w), ("φ", old_formulaToJson φ)]
  | .previous w φ => ctor "previous" [("w", toJson w), ("φ", old_formulaToJson φ)]
  | .since φ w ψ => ctor "since" [("φ", old_formulaToJson φ), ("w", toJson w), ("ψ", old_formulaToJson ψ)]
  | .pred a k args =>
    ctor "pred" [("action", toJson a), ("kind", toJson k),
      ("args", Json.arr (args.map fun (p, t) => Json.arr #[toJson p, old_termToJson t]).toArray)]
  | .cmp op l r => ctor "cmp" [("op", toJson op), ("l", old_termToJson l), ("r", old_termToJson r)]
  | .exist x φ => ctor "exist" [("x", toJson x), ("φ", old_formulaToJson φ)]
  | .tp x => ctor "tp" [("x", toJson x)]

end

mutual

partial def old_termOfJson (j : Json) : Except String Term := do
  let (c, a) ← ctorOf j
  match c with
  | "entity" => .entity <$> arg a "uid"
  | "long" => .long <$> arg a "i"
  | "decimal" => .decimal <$> arg a "text"
  | "string" => .string <$> arg a "s"
  | "bool" => .bool <$> arg a "b"
  | "context" => .context <$> arg a "path"
  | "scope" => return .scope (← arg a "root") (← arg a "path")
  | "var" => .var <$> arg a "x"
  | "wildcard" => pure .wildcard
  | "agg" => .agg <$> old_aggregateOfJson (← a.getObjVal? "a")
  | "arith" =>
    return .arith (← arg a "op") (← old_termOfJson (← a.getObjVal? "l")) (← old_termOfJson (← a.getObjVal? "r"))
  | _ => throw s!"unknown term {c}"

partial def old_aggregateOfJson (j : Json) : Except String Aggregate := do
  let (c, a) ← ctorOf j
  match c with
  | "count" => return .count (← arg a "domain") (← old_formulaOfJson (← a.getObjVal? "body"))
  | "sum" =>
    return .sum (← arg a "summand") (← arg a "domain") (← old_formulaOfJson (← a.getObjVal? "body"))
  | _ => throw s!"unknown aggregate {c}"

partial def old_formulaOfJson (j : Json) : Except String Formula := do
  let (c, a) ← ctorOf j
  let sub (name : String) : Except String Formula := do old_formulaOfJson (← a.getObjVal? name)
  match c with
  | "and" => return .and (← sub "φ") (← sub "ψ")
  | "not" => .not <$> sub "φ"
  | "formerly" => return .formerly (← arg a "w") (← sub "φ")
  | "previous" => return .previous (← arg a "w") (← sub "φ")
  | "since" => return .since (← sub "φ") (← arg a "w") (← sub "ψ")
  | "pred" =>
    let args ← (← a.getObjVal? "args").getArr?
    let args ← args.toList.mapM fun p => do
      return ((← fromJson? (← p.getArrVal? 0) : Path), ← old_termOfJson (← p.getArrVal? 1))
    return .pred (← arg a "action") (← arg a "kind") args
  | "cmp" =>
    return .cmp (← arg a "op") (← old_termOfJson (← a.getObjVal? "l")) (← old_termOfJson (← a.getObjVal? "r"))
  | "exist" => return .exist (← arg a "x") (← sub "φ")
  | "tp" => .tp <$> arg a "x"
  | _ => throw s!"unknown condition {c}"

end


end Dogwood.Conformance.OldJson

namespace JsonTotalCheck

structure G where s : UInt64
abbrev M := StateM G
def next : M Nat := do
  let g ← get
  let s := g.s * 6364136223846793005 + 1442695040888963407
  set ({ s := s } : G)
  return (s >>> 33).toNat
def pick {α : Type} [Inhabited α] (xs : List α) : M α := do return xs[(← next) % xs.length]!

def keys : List String :=
  ["and", "not", "formerly", "previous", "since", "pred", "cmp", "exist", "tp", "φ", "ψ", "w", "x",
   "entity", "long", "decimal", "string", "bool", "context", "scope", "var", "agg", "arith", "count",
   "sum", "a", "l", "r", "op", "i", "text", "s", "b", "path", "root", "uid", "ty", "eid", "id",
   "domain", "body", "summand", "action", "kind", "args", "amount", "unit", "name", "named",
   "set", "record", "extension", "fn", "arg", "ext", "required", "zz"]
def strs : List String :=
  ["wildcard", "timepoint", "eq", "lt", "add", "seconds", "hours", "principal", "resource", "bool",
   "long", "string", "decimal", "ipaddr", "", "x", "1.5", "ip", "10.0.0.1", "datetime"]

partial def json (d : Nat) : M Json := do
  match (← next) % (if d == 0 then 4 else 7) with
  | 0 => return .str (← pick strs)
  | 1 => return .num (((← next) % 200 : Nat) - 100 : Int)
  | 2 => return .bool ((← next) % 2 == 0)
  | 3 => return .null
  | 4 =>
    let n := (← next) % 4
    return .arr ((← (List.range n).mapM fun _ => json (d - 1)).toArray)
  | _ =>
    let n := (← next) % 4
    let kvs ← (List.range n).mapM fun _ => do return (← pick keys, ← json (d - 1))
    return Json.mkObj kvs

def show? {α : Type} [Repr α] (r : Except String α) : String := reprStr r

def str : M String := pick ["", "a", "x", "é", "\"q\"", "ns::T", "a.b", "0"]
def path : M (List String) := do (List.range ((← next) % 3)).mapM fun _ => str
def uid : M EntityUID := do return { ty := { id := ← str, path := ← path }, eid := ← str }
def window : M Window := do
  return { amount := (((← next) % 100 : Nat) : Int) - 5, unit := ← pick [.seconds, .minutes, .hours, .days] }
def binder : M Binder := do
  let ty ← if (← next) % 2 == 0 then pure BinderType.timepoint else (.named <$> path)
  return { name := ← str, ty }
instance : Inhabited Aggregate := ⟨.count [] (.tp "")⟩
mutual
partial def term (d : Nat) : M Term := do
  match (← next) % (if d == 0 then 9 else 11) with
  | 0 => return .entity (← uid)
  | 1 => return .long (Int64.ofInt ((((← next) % 1000 : Nat) : Int) - 500))
  | 2 => return .decimal (← str)
  | 3 => return .string (← str)
  | 4 => return .bool true
  | 5 => return .context (← path)
  | 6 => return .scope (← pick [.principal, .resource]) (← path)
  | 7 => return .var (← str)
  | 8 => return .wildcard
  | 9 => return .agg (← agg (d - 1))
  | _ => return .arith (← pick [.add, .sub, .mul]) (← term (d - 1)) (← term (d - 1))
partial def agg (d : Nat) : M Aggregate := do
  let dom ← (List.range ((← next) % 3)).mapM fun _ => binder
  if (← next) % 2 == 0 then return .count dom (← formula d) else return .sum (← str) dom (← formula d)
partial def formula (d : Nat) : M Formula := do
  match (← next) % (if d == 0 then 3 else 9) with
  | 0 => return .pred (← uid) (← str) (← (List.range ((← next) % 3)).mapM fun _ => do return (← path, ← term d))
  | 1 => return .cmp (← pick [.eq, .ne, .lt, .le, .gt, .ge]) (← term d) (← term d)
  | 2 => return .tp (← str)
  | 3 => return .and (← formula (d - 1)) (← formula (d - 1))
  | 4 => return .not (← formula (d - 1))
  | 5 => return .formerly (← window) (← formula (d - 1))
  | 6 => return .previous (← window) (← formula (d - 1))
  | 7 => return .since (← formula (d - 1)) (← window) (← formula (d - 1))
  | _ => return .exist (← binder) (← formula (d - 1))
end

/-- Replace one random sub-value of `j` with `r`. -/
partial def mutate (j r : Json) : M Json := do
  if (← next) % 4 == 0 then return r
  match j with
  | .arr a =>
    if a.isEmpty then return r
    let i := (← next) % a.size
    return .arr (a.set! i (← mutate a[i]! r))
  | .obj kvs =>
    let l := kvs.toList
    if l.isEmpty then return r
    let i := (← next) % l.length
    let (k, v) := l[i]!
    return .obj (kvs.insert k (← mutate v r))
  | _ => return r

end JsonTotalCheck

open JsonTotalCheck in
def main (args : List String) : IO UInt32 := do
  let count := (args[0]? >>= String.toNat?).getD 20000
  let seed := (args[1]? >>= String.toNat?).getD 1016
  let mut g : G := { s := seed.toUInt64 }
  let mut n := 0
  let mut okF := 0
  let mut okV := 0
  let mut okT := 0
  let mut bad : Array String := #[]
  for _ in List.range count do
    let (j0, g') := (json 5).run g
    g := g'
    let (φ, g') := (formula 3).run g
    g := g'
    let enc := Dogwood.Conformance.formulaToJson φ
    if show? (Dogwood.Conformance.OldJson.old_formulaOfJson enc) != show? (Dogwood.Conformance.formulaOfJson enc) then
      bad := bad.push s!"formula encoding decodes differently: {enc.compress}"
    if show? (Dogwood.Conformance.formulaOfJson enc) != show? (Except.ok φ : Except String Formula) then
      bad := bad.push s!"round trip fails at run time: {enc.compress}"
    let (j, g') := (if (← pure (j0.compress.length % 2 == 0)) then (mutate enc j0).run g else (pure j0 : M Json).run g)
    g := g'
    let checks : List (String × String × String) := [
      ("formula", show? (Dogwood.Conformance.OldJson.old_formulaOfJson j), show? (Dogwood.Conformance.formulaOfJson j)),
      ("term", show? (Dogwood.Conformance.OldJson.old_termOfJson j), show? (Dogwood.Conformance.termOfJson j)),
      ("aggregate", show? (Dogwood.Conformance.OldJson.old_aggregateOfJson j), show? (Dogwood.Conformance.aggregateOfJson j)),
      ("value", show? (Dogwood.Conformance.OldJson.old_valueOfJson j), show? (Dogwood.Conformance.valueOfJson j)),
      ("cedarType", show? (Dogwood.Conformance.OldJson.old_cedarTypeOfJson j), show? (Dogwood.Conformance.cedarTypeOfJson j))]
    for (what, a, b) in checks do
      n := n + 1
      if a != b then bad := bad.push s!"{what}: {j.compress}\n  old {a}\n  new {b}"
    -- the encoders, on whatever decodes
    if let .ok φ := Dogwood.Conformance.formulaOfJson j then
      okF := okF + 1
      if Dogwood.Conformance.OldJson.old_formulaToJson φ != Dogwood.Conformance.formulaToJson φ then
        bad := bad.push s!"formulaToJson differs on {j.compress}"
    if let .ok v := Dogwood.Conformance.valueOfJson j then
      okV := okV + 1
      if Dogwood.Conformance.OldJson.old_valueToJson v != Dogwood.Conformance.valueToJson v then
        bad := bad.push s!"valueToJson differs on {j.compress}"
    if let .ok t := Dogwood.Conformance.cedarTypeOfJson j then
      okT := okT + 1
      if Dogwood.Conformance.OldJson.old_cedarTypeToJson t != Dogwood.Conformance.cedarTypeToJson t then
        bad := bad.push s!"cedarTypeToJson differs on {j.compress}"
  IO.println s!"{count} random JSON trees, {n} decoder comparisons ({okF} decode as formulas, {okV} as values, {okT} as types): {bad.size} differ"
  for b in bad.toList.take 5 do IO.println b
  return if bad.isEmpty then 0 else 1
