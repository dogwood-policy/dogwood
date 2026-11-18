import Lean.Data.Json
import Dogwood.Conformance.Harness
import Dogwood.Conformance.JsonSize

/-!
# The JSON form of exported bundles

`bridge/` writes each bundle group as a JSON array of `Case`s. Most types use Lean's derived
encoding: a constructor without arguments is its name, `"permit"`; any other constructor is an
object with one key, its name, whose value holds the arguments by name,
`{"eq": {"entity": …}}`; a structure is an object of its fields; a pair is a two-element array;
`none` is `null`.

A few types are encoded by hand:

* a Cedar `Set` is an array of its elements, and a `Map` an array of `[key, value]` pairs.
  Decoding goes through `Set.make` and `Map.make`, so the result is well-formed whatever the
  order of the input;
* a primitive value is a JSON Boolean, number, or string, or `{"entity": uid}`;
* a value is a primitive value, `{"set": [...]}`, `{"record": [[k, v], ...]}`,
  `{"decimal": text}`, or `{"extension": {"fn": f, "arg": text}}` for a value of the `ipaddr`,
  `datetime`, or `duration` type whose Cedar constructor is `f`. Text that Cedar does not accept is
  read as a string, which is how the reference implementation compares a decimal;
* an `Int64` is a JSON number in range, and a `Char` a one-character string;
* a cedar type is `"bool"`, `"long"`, `"string"`, `{"set": T}`, `{"entity": name}`,
  `{"record": [[attr, {"ty": T, "required": b}], …]}`, or `{"ext": name}`.
-/

namespace Dogwood.Conformance

open Lean (Json FromJson ToJson fromJson? toJson)
open Cedar.Spec Cedar.Data

instance : FromJson Int64 where
  fromJson? j := do
    let i : Int ← fromJson? j
    match Int64.ofInt? i with
    | some n => pure n
    | none => throw s!"{i} is not a Long"

instance : ToJson Int64 where
  toJson n := toJson n.toInt

instance : FromJson Char where
  fromJson? j := do
    let s : String ← fromJson? j
    match s.toList with
    | [c] => pure c
    | _ => throw s!"{s.quote} is not one character"

instance : ToJson Char where
  toJson c := toJson (String.singleton c)

instance {α : Type} [FromJson α] [LT α] [DecidableLT α] : FromJson (Set α) where
  fromJson? j := Set.make <$> fromJson? j

instance (priority := high) {α : Type} [ToJson α] : ToJson (Set α) where
  toJson s := toJson s.toList

instance {α β : Type} [FromJson α] [FromJson β] [LT α] [DecidableLT α] : FromJson (Map α β) where
  fromJson? j := Map.make <$> fromJson? j

instance {α β : Type} [ToJson α] [ToJson β] : ToJson (Map α β) where
  toJson m := toJson m.toList

deriving instance FromJson for Name, EntityUID

def primOfJson : Json → Except String Prim
  | .bool b => pure (.bool b)
  | .str s => pure (.string s)
  | j@(.num _) => (.int ·) <$> fromJson? j
  | j => do pure (.entityUID (← fromJson? (← j.getObjVal? "entity")))

def primToJson : Prim → Json
  | .bool b => toJson b
  | .int i => toJson i
  | .string s => toJson s
  | .entityUID uid => Json.mkObj [("entity", toJson uid)]

instance : FromJson Prim := ⟨primOfJson⟩
instance : ToJson Prim := ⟨primToJson⟩

/-- A decimal value, from its text: as a string when Cedar does not accept the text. -/
def decimalValue (s : String) : Value :=
  match Ext.Decimal.parse s with
  | some d => .ext (.decimal d)
  | none => .prim (.string s)

/-- A value of the extension type whose Cedar constructor is `f` (`ip`, `datetime`, or
`duration`), from its argument: as a string when Cedar does not accept the argument. -/
def extensionValue (f s : String) : Value :=
  let x : Option Ext := match f with
    | "ip" => Ext.ipaddr <$> Ext.IPAddr.ip s
    | "datetime" => Ext.datetime <$> Ext.Datetime.parse s
    | "duration" => Ext.duration <$> Ext.Datetime.Duration.parse s
    | _ => none
  match x with
  | some x => .ext x
  | none => .prim (.string s)

def valueOfJson (j : Json) : Except String Value := do
  match getObjValS j "set", getObjValS j "record", getObjValS j "decimal",
      getObjValS j "extension" with
  | .ok ⟨s, _⟩, _, _, _ =>
    let items ← getArrS s
    pure (.set (Set.make (← items.toList.mapM fun ⟨v, _⟩ => valueOfJson v)))
  | _, .ok ⟨r, _⟩, _, _ =>
    let fields ← getArrS r
    let kvs ← fields.toList.mapM fun ⟨f, _⟩ => do
      let k : String ← fromJson? (← f.getArrVal? 0)
      let ⟨v, _⟩ ← getArrValS f 1
      pure (k, ← valueOfJson v)
    pure (.record (Map.make kvs))
  | _, _, .ok ⟨d, _⟩, _ => decimalValue <$> fromJson? d
  | _, _, _, .ok ⟨x, _⟩ => do
    pure (extensionValue (← fromJson? (← x.getObjVal? "fn")) (← fromJson? (← x.getObjVal? "arg")))
  | _, _, _, _ => (.prim ·) <$> primOfJson j
termination_by sizeOf j
decreasing_by all_goals (simp_wf; omega)

def valueToJson : Value → Json
  | .prim p => primToJson p
  | .set s => Json.mkObj [("set", Json.arr (s.toList.attach.map fun ⟨v, _⟩ => valueToJson v).toArray)]
  | .record m =>
    Json.mkObj [("record", Json.arr (m.toList.attach.map fun ⟨(k, v), _⟩ =>
      Json.arr #[toJson k, valueToJson v]).toArray)]
  | .ext (.decimal d) => Json.mkObj [("decimal", toJson (toString d))]
  | .ext x => Json.mkObj [("unsupported", toJson (toString (repr x)))]
termination_by v => sizeOf v
decreasing_by
  · rename_i h
    have := Set.sizeOf_lt_of_mem (s := s) h
    simp; omega
  · rename_i h
    have := Map.sizeOf_lt_of_value (m := m) h
    simp; omega

instance : FromJson Value := ⟨valueOfJson⟩
instance : ToJson Value := ⟨valueToJson⟩

deriving instance FromJson, ToJson for EntityData, Effect, Scope, PrincipalScope, ResourceScope,
  ActionScope, ConditionKind, Var, PatElem, UnaryOp, BinaryOp, ExtFun

/-! ## Cedar types

A cedar type is `"bool"`, `"long"`, `"string"`, `{"set": T}`, `{"entity": name}`,
`{"record": [[attr, {"ty": T, "required": b}], …]}`, or `{"ext": name}`. -/

open Cedar.Validation (CedarType ExtType Qualified QualifiedType RecordType)

def extTypeOfName : String → Except String ExtType
  | "decimal" => pure .decimal
  | "ipaddr" => pure .ipAddr
  | "datetime" => pure .datetime
  | "duration" => pure .duration
  | x => throw s!"unknown extension type {x}"

def cedarTypeOfJson (j : Json) : Except String CedarType := do
  match j with
  | .str "bool" => pure (.bool .anyBool)
  | .str "long" => pure .int
  | .str "string" => pure .string
  | j' =>
    match getObjValS j' "set", getObjValS j' "entity", getObjValS j' "record", getObjValS j' "ext" with
    | .ok ⟨t, _⟩, _, _, _ => .set <$> cedarTypeOfJson t
    | _, .ok ⟨e, _⟩, _, _ => .entity <$> fromJson? e
    | _, _, .ok ⟨r, _⟩, _ => .record <$> recordTypeOfJson r
    | _, _, _, .ok ⟨x, _⟩ => .ext <$> (extTypeOfName (← fromJson? x))
    | _, _, _, _ => throw s!"not a cedar type: {j'.compress}"
termination_by sizeOf j
decreasing_by all_goals (simp_wf; omega)
where
  recordTypeOfJson (r : Json) : Except String RecordType := do
    let fields ← getArrS r
    let kvs ← fields.toList.mapM fun ⟨f, _⟩ => do
      let k : String ← fromJson? (← f.getArrVal? 0)
      let ⟨q, _⟩ ← getArrValS f 1
      let ⟨t, _⟩ ← getObjValS q "ty"
      let ty ← cedarTypeOfJson t
      let req : Bool ← fromJson? (← q.getObjVal? "required")
      pure (k, if req then Qualified.required ty else Qualified.optional ty)
    pure (Map.make kvs)
  termination_by sizeOf r
  decreasing_by all_goals (simp_wf; omega)

instance : FromJson CedarType := ⟨cedarTypeOfJson⟩

instance : FromJson QualifiedType where
  fromJson? q := do
    let ty ← cedarTypeOfJson (← q.getObjVal? "ty")
    let req : Bool ← fromJson? (← q.getObjVal? "required")
    pure (if req then .required ty else .optional ty)

def cedarTypeToJson : CedarType → Json
  | .bool _ => "bool"
  | .int => "long"
  | .string => "string"
  | .set t => Json.mkObj [("set", cedarTypeToJson t)]
  | .entity e => Json.mkObj [("entity", toJson e)]
  | .record r => Json.mkObj [("record", Json.arr (r.toList.attach.map fun ⟨(k, q), _⟩ =>
      Json.arr #[toJson k, Json.mkObj [("ty", cedarTypeToJson q.getType),
        ("required", toJson q.isRequired)]]).toArray)]
  | .ext x => Json.mkObj [("ext", toJson (match x with
      | .decimal => "decimal" | .ipAddr => "ipaddr" | .datetime => "datetime"
      | .duration => "duration"))]
termination_by t => sizeOf t
decreasing_by
  · simp_wf <;> omega
  · rename_i h
    have := Map.sizeOf_lt_of_value (m := r) h
    have hq : sizeOf q.getType < sizeOf q := by cases q <;> simp [Qualified.getType]
    simp; omega

instance : ToJson CedarType := ⟨cedarTypeToJson⟩

open Dogwood.Spec Dogwood.Spec.Temporal

deriving instance FromJson, ToJson for ScopeRoot, TimeUnit, Window, CmpOp, ArithOp, BinderType

/-! ### Constructor tags the kernel reads

The derived decoder of an inductive type reads a constructor's tag with `Json.getTag?`, which takes
the least key of the object's `Std.TreeMap` (`Std.DTreeMap.Internal.Impl.minKey?`). That function
is defined by well-founded recursion, which the kernel does not reduce, so a proof cannot run the
decoder on a concrete value (`decide +kernel`) once it meets a constructor with arguments, such as
`BinderType.named`. `minKeyS` is `minKey?` by structural recursion (`minKeyS_eq`), `getTagS?` is
`getTag?` with it (`getTagS?_eq`), and `binderTypeOfJson` is the derived decoder of `BinderType`
with `getTagS?` (`binderTypeOfJson_eq`: it is the derived decoder, on every value). It is the
instance the decoders below use. -/

/-- `Std.DTreeMap.Internal.Impl.minKey?`, by structural recursion. -/
def minKeyS {α : Type} {β : α → Type} : Std.DTreeMap.Internal.Impl α β → Option α
  | .leaf => none
  | .inner _ k _ l _ =>
    match l with
    | .leaf => some k
    | .inner .. => minKeyS l

theorem minKeyS_eq {α : Type} {β : α → Type} [Ord α] (t : Std.DTreeMap.Internal.Impl α β) :
    minKeyS t = t.minKey? := by
  induction t with
  | leaf => unfold minKeyS Std.DTreeMap.Internal.Impl.minKey?; rfl
  | inner sz k v l r ihl _ =>
    cases l with
    | leaf => unfold minKeyS Std.DTreeMap.Internal.Impl.minKey?; rfl
    | inner sz' k' v' l' r' =>
      show minKeyS (Std.DTreeMap.Internal.Impl.inner sz' k' v' l' r') = _
      rw [ihl]
      conv => rhs; unfold Std.DTreeMap.Internal.Impl.minKey?

/-- `Json.getTag?`, with the least key read by `minKeyS`. -/
def getTagS? : Json → Option String
  | .str tag => some tag
  | .obj kvs => guard ((kvs.size == 1) = true) *> minKeyS kvs.inner.inner
  | _ => none

theorem getTagS?_eq (j : Json) : getTagS? j = j.getTag? := by
  cases j with
  | obj kvs =>
    show guard _ *> minKeyS kvs.inner.inner = guard _ *> kvs.minKey?
    rw [minKeyS_eq]; rfl
  | _ => rfl

/-- The decoder of `BinderType`: the derived one, with the tag read by `getTagS?`. -/
def binderTypeOfJson (json : Json) : Except String BinderType :=
  match getTagS? json with
  | some tag =>
    match tag with
    | "timepoint" => pure BinderType.timepoint
    | "named" =>
      (json.parseCtorFields "named" 1 (some #[`path])).bind fun (jsons : Array Json) => do
        let a ← fromJson? jsons[0]!
        pure (BinderType.named a)
    | _ => Except.error "no inductive constructor matched"
  | none => Except.error "no inductive tag found"

/-- **The decoder of `BinderType` is the derived one**, on every value. -/
theorem binderTypeOfJson_eq (j : Json) : binderTypeOfJson j = instFromJsonBinderType.fromJson? j := by
  show _ = instFromJsonBinderType.fromJson j
  unfold binderTypeOfJson instFromJsonBinderType.fromJson
  rw [getTagS?_eq]

instance (priority := high) instFromJsonBinderTypeS : FromJson BinderType := ⟨binderTypeOfJson⟩

deriving instance FromJson, ToJson for Binder

/-! Lean cannot derive instances for the mutual block of temporal conditions, so they are written
out below, in the derived encoding. -/

/-- A constructor applied to named arguments. -/
def ctor (name : String) (args : List (String × Json)) : Json :=
  Json.mkObj [(name, Json.mkObj args)]

/-- The constructor name of a value in the derived encoding, and its arguments. -/
def ctorOf (j : Json) : Except String (String × Json) :=
  match j with
  | .str s => pure (s, Json.null)
  | .obj kvs =>
    match kvs.toList with
    | [(k, v)] => pure (k, v)
    | _ => throw s!"not a constructor: {j.compress}"
  | _ => throw s!"not a constructor: {j.compress}"

def arg {α : Type} [FromJson α] (args : Json) (name : String) : Except String α := do
  fromJson? (← args.getObjVal? name)

mutual

def termToJson : Term → Json
  | .entity uid => ctor "entity" [("uid", toJson uid)]
  | .long i => ctor "long" [("i", toJson i)]
  | .decimal t => ctor "decimal" [("text", toJson t)]
  | .string s => ctor "string" [("s", toJson s)]
  | .bool b => ctor "bool" [("b", toJson b)]
  | .context p => ctor "context" [("path", toJson p)]
  | .scope r p => ctor "scope" [("root", toJson r), ("path", toJson p)]
  | .var x => ctor "var" [("x", toJson x)]
  | .wildcard => "wildcard"
  | .agg a => ctor "agg" [("a", aggregateToJson a)]
  | .arith op l r => ctor "arith" [("op", toJson op), ("l", termToJson l), ("r", termToJson r)]

def aggregateToJson : Aggregate → Json
  | .count dom body => ctor "count" [("domain", toJson dom), ("body", formulaToJson body)]
  | .sum s dom body =>
    ctor "sum" [("summand", toJson s), ("domain", toJson dom), ("body", formulaToJson body)]

def formulaToJson : Formula → Json
  | .and φ ψ => ctor "and" [("φ", formulaToJson φ), ("ψ", formulaToJson ψ)]
  | .not φ => ctor "not" [("φ", formulaToJson φ)]
  | .formerly w φ => ctor "formerly" [("w", toJson w), ("φ", formulaToJson φ)]
  | .previous w φ => ctor "previous" [("w", toJson w), ("φ", formulaToJson φ)]
  | .since φ w ψ => ctor "since" [("φ", formulaToJson φ), ("w", toJson w), ("ψ", formulaToJson ψ)]
  | .pred a k args =>
    ctor "pred" [("action", toJson a), ("kind", toJson k), ("args", Json.arr (argsToJson args).toArray)]
  | .cmp op l r => ctor "cmp" [("op", toJson op), ("l", termToJson l), ("r", termToJson r)]
  | .exist x φ => ctor "exist" [("x", toJson x), ("φ", formulaToJson φ)]
  | .tp x => ctor "tp" [("x", toJson x)]

/-- A predicate's arguments, each `[path, term]` (`args.map`, written out so that the recursion
is structural: `argsToJson_eq`). -/
def argsToJson : List (Path × Term) → List Json
  | [] => []
  | (p, t) :: rest => Json.arr #[toJson p, termToJson t] :: argsToJson rest

end

theorem argsToJson_eq (args : List (Path × Term)) :
    argsToJson args = args.map fun (p, t) => Json.arr #[toJson p, termToJson t] := by
  induction args with
  | nil => rfl
  | cons a rest ih => obtain ⟨p, t⟩ := a; simp [argsToJson, ih]

/-- `ctorOf`, with the fact that the arguments are smaller than the value (`ctorOfS_val`). -/
def ctorOfS (j : Json) : Except String (String × {a : Json // sizeOf a < sizeOf j}) :=
  match j with
  | .str s => pure (s, ⟨Json.null, by simp; cases s; simp; omega⟩)
  | .obj kvs =>
    match h : kvs.toList with
    | [(k, v)] =>
      pure (k, ⟨v, by
        have := sizeOf_lt_of_mem_toList (kvs := kvs) (x := (k, v)) (by rw [h]; simp)
        exact this⟩)
    | _ => throw s!"not a constructor: {(Json.obj kvs).compress}"
  | j => throw s!"not a constructor: {j.compress}"

theorem ctorOfS_val (j : Json) : (ctorOfS j).map (fun p => (p.1, p.2.val)) = ctorOf j := by
  unfold ctorOfS ctorOf
  split
  · rfl
  · rename_i kvs
    split <;> simp_all [Except.map, pure, Except.pure, throw, throwThe, MonadExceptOf.throw]
  · rename_i j hs ho
    cases j <;> simp_all [Except.map, throw, throwThe, MonadExceptOf.throw]

/-! The decoders below are well-founded on the size of the value they read: every recursive call
is on a value read from it by `ctorOfS`, `getObjValS`, `getArrS` or `getArrValS`, which read what
`ctorOf`, `getObjVal?`, `getArr?` and `getArrVal?` read, in the same order. -/

mutual

def termOfJson (j : Json) : Except String Term := do
  let (c, ⟨a, ha⟩) ← ctorOfS j
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
  | "agg" => do
    let ⟨x, _⟩ ← getObjValS a "a"
    .agg <$> aggregateOfJson x
  | "arith" => do
    let op ← arg a "op"
    let ⟨l, _⟩ ← getObjValS a "l"
    let l' ← termOfJson l
    let ⟨r, _⟩ ← getObjValS a "r"
    return .arith op l' (← termOfJson r)
  | _ => throw s!"unknown term {c}"
termination_by sizeOf j
decreasing_by all_goals (simp_wf; omega)

def aggregateOfJson (j : Json) : Except String Aggregate := do
  let (c, ⟨a, ha⟩) ← ctorOfS j
  match c with
  | "count" => do
    let dom ← arg a "domain"
    let ⟨b, _⟩ ← getObjValS a "body"
    return .count dom (← formulaOfJson b)
  | "sum" => do
    let s ← arg a "summand"
    let dom ← arg a "domain"
    let ⟨b, _⟩ ← getObjValS a "body"
    return .sum s dom (← formulaOfJson b)
  | _ => throw s!"unknown aggregate {c}"
termination_by sizeOf j
decreasing_by all_goals (simp_wf; omega)

def formulaOfJson (j : Json) : Except String Formula := do
  let (c, ⟨a, ha⟩) ← ctorOfS j
  match c with
  | "and" => do
    let ⟨x, _⟩ ← getObjValS a "φ"
    let φ ← formulaOfJson x
    let ⟨y, _⟩ ← getObjValS a "ψ"
    return .and φ (← formulaOfJson y)
  | "not" => do
    let ⟨x, _⟩ ← getObjValS a "φ"
    .not <$> formulaOfJson x
  | "formerly" => do
    let w ← arg a "w"
    let ⟨x, _⟩ ← getObjValS a "φ"
    return .formerly w (← formulaOfJson x)
  | "previous" => do
    let w ← arg a "w"
    let ⟨x, _⟩ ← getObjValS a "φ"
    return .previous w (← formulaOfJson x)
  | "since" => do
    let ⟨x, _⟩ ← getObjValS a "φ"
    let φ ← formulaOfJson x
    let w ← arg a "w"
    let ⟨y, _⟩ ← getObjValS a "ψ"
    return .since φ w (← formulaOfJson y)
  | "pred" => do
    let ⟨argsJ, _⟩ ← getObjValS a "args"
    let args ← getArrS argsJ
    let args ← args.toList.mapM fun ⟨p, _⟩ => do
      let path : Path ← fromJson? (← p.getArrVal? 0)
      let ⟨t, _⟩ ← getArrValS p 1
      return (path, ← termOfJson t)
    return .pred (← arg a "action") (← arg a "kind") args
  | "cmp" => do
    let op ← arg a "op"
    let ⟨l, _⟩ ← getObjValS a "l"
    let l' ← termOfJson l
    let ⟨r, _⟩ ← getObjValS a "r"
    return .cmp op l' (← termOfJson r)
  | "exist" => do
    let x ← arg a "x"
    let ⟨b, _⟩ ← getObjValS a "φ"
    return .exist x (← formulaOfJson b)
  | "tp" => .tp <$> arg a "x"
  | _ => throw s!"unknown condition {c}"
termination_by sizeOf j
decreasing_by all_goals (simp_wf; omega)

end

instance : ToJson Term := ⟨termToJson⟩
instance : FromJson Term := ⟨termOfJson⟩
instance : ToJson Aggregate := ⟨aggregateToJson⟩
instance : FromJson Aggregate := ⟨aggregateOfJson⟩
instance : ToJson Formula := ⟨formulaToJson⟩
instance : FromJson Formula := ⟨formulaOfJson⟩

deriving instance FromJson, ToJson for Provider.Arg, Provider.MethodCall, Provider.Call

deriving instance FromJson for Provider.MethodSig, Provider.Signature

deriving instance FromJson, ToJson for Dogwood.Spec.Expr

deriving instance FromJson, ToJson for Dogwood.Spec.Condition, Dogwood.Spec.Policy, Event,
  TimePoint, PinRef, Pin

deriving instance FromJson for FieldTy, FieldDecl, EventSignature

deriving instance FromJson for CrateFinding, EntityDecl, ActionDecl, ActionSchemaJson,
  TraceCase, Decisions, Lowered, Outcome, Case

end Dogwood.Conformance
