import Dogwood.Conformance.Json
import Std.Data.TreeMap.Raw

/-!
# The decoder inverts the encoder

`formulaOfJson_formulaToJson`: decoding the JSON form of a temporal condition gives the condition
back. `formulaToJson` and `formulaOfJson` (`Dogwood.Conformance.Json`) are total: the encoders by
structural recursion, the decoders by well-founded recursion on the size of the JSON value they
read. A conformance bundle that writes a leaf in this encoding (the bridge does) is therefore
read as that leaf.

The proof unfolds each decoder once on a constructor's encoding and recurses on the parts. The
derived instances of the leaf types (`Window`, `Binder`, `EntityUID`, …) round-trip too (`rt_*`).
-/

namespace Dogwood.Conformance

open Lean (Json ToJson FromJson toJson fromJson?)
open Dogwood.Spec
open Dogwood.Spec.Temporal

/-! ## The leaf types -/

/-- The tag of a one-field object is its field's name (what a derived decoder dispatches on). -/
theorem getTag?_single (k : String) (x : Json) : (Json.mkObj [(k, x)]).getTag? = some k := by
  unfold Json.getTag? Json.mkObj
  simp only [Std.TreeMap.Raw.ofList_singleton]
  have hwf : (∅ : Std.TreeMap.Raw String Json compare).WF := Std.TreeMap.Raw.WF.emptyc
  have hmin : (∅ : Std.TreeMap.Raw String Json compare).minKey? = none :=
    Std.TreeMap.Raw.minKey?_emptyc
  rw [Std.TreeMap.Raw.size_insert hwf, Std.TreeMap.Raw.minKey?_insert hwf, hmin]
  simp [guard]
  rfl

theorem rt_list {α : Type} [FromJson α] [ToJson α]
    (h : ∀ a : α, (fromJson? (toJson a) : Except String α) = .ok a) (l : List α) :
    (fromJson? (toJson l) : Except String (List α)) = .ok l := by
  have hm : ∀ l : List α, (l.map toJson).mapM (fun j => (fromJson? j : Except String α)) = .ok l := by
    intro l; induction l with
    | nil => rfl
    | cons a rest ih => simp [List.mapM_cons, h a, ih]
  simp only [fromJson?, toJson, Lean.List.fromJson?, Lean.List.toJson, Lean.Array.fromJson?,
    Lean.Array.toJson]
  simp [Array.mapM_eq_mapM_toList, hm, Except.map]

theorem rt_string (s : String) : (fromJson? (toJson s) : Except String String) = .ok s := rfl

theorem rt_path (p : Path) : (fromJson? (toJson p) : Except String Path) = .ok p :=
  rt_list rt_string p

theorem rt_int64 (i : Int64) : (fromJson? (toJson i) : Except String Int64) = .ok i := by
  show (do let n : Int ← fromJson? (toJson i.toInt)
           match Int64.ofInt? n with
           | some n => pure n
           | none => throw s!"{n} is not a Long") = _
  have : (fromJson? (toJson i.toInt) : Except String Int) = .ok i.toInt := rfl
  rw [this]
  simp [bind, Except.bind, Int64.ofInt?_toInt, pure, Except.pure]

theorem rt_bool (b : Bool) : (fromJson? (toJson b) : Except String Bool) = .ok b := by
  cases b <;> rfl

theorem rt_name (n : Cedar.Spec.Name) :
    (fromJson? (toJson n) : Except String Cedar.Spec.Name) = .ok n := by
  obtain ⟨id, path⟩ := n
  show instFromJsonName_dogwood.fromJson (Cedar.Spec.instToJsonName.toJson ⟨id, path⟩) = _
  unfold instFromJsonName_dogwood.fromJson Cedar.Spec.instToJsonName.toJson
  simp only [List.flatten_cons, List.flatten_nil, List.cons_append, List.nil_append,
    Json.getObjValAs?]
  have h1 : (Json.mkObj [("id", toJson id), ("path", toJson path)]).getObjValD "id" = toJson id := rfl
  have h2 : (Json.mkObj [("id", toJson id), ("path", toJson path)]).getObjValD "path" = toJson path := rfl
  rw [h1, h2, rt_string, rt_path]
  rfl

theorem rt_uid (u : Cedar.Spec.EntityUID) :
    (fromJson? (toJson u) : Except String Cedar.Spec.EntityUID) = .ok u := by
  obtain ⟨ty, eid⟩ := u
  show instFromJsonEntityUID_dogwood.fromJson (Cedar.Spec.instToJsonEntityUID.toJson ⟨ty, eid⟩) = _
  unfold instFromJsonEntityUID_dogwood.fromJson Cedar.Spec.instToJsonEntityUID.toJson
  simp only [List.flatten_cons, List.flatten_nil, List.cons_append, List.nil_append,
    Json.getObjValAs?]
  have h1 : (Json.mkObj [("ty", toJson ty), ("eid", toJson eid)]).getObjValD "ty" = toJson ty := rfl
  have h2 : (Json.mkObj [("ty", toJson ty), ("eid", toJson eid)]).getObjValD "eid" = toJson eid := rfl
  rw [h1, h2, rt_name, rt_string]
  rfl

theorem rt_window (w : Window) : (fromJson? (toJson w) : Except String Window) = .ok w := by
  obtain ⟨amt, u⟩ := w
  cases u <;> rfl

theorem rt_cmpOp (o : CmpOp) : (fromJson? (toJson o) : Except String CmpOp) = .ok o := by
  cases o <;> rfl

theorem rt_arithOp (o : ArithOp) : (fromJson? (toJson o) : Except String ArithOp) = .ok o := by
  cases o <;> rfl

theorem rt_scopeRoot (r : ScopeRoot) : (fromJson? (toJson r) : Except String ScopeRoot) = .ok r := by
  cases r <;> rfl

theorem rt_binderType (t : BinderType) : (fromJson? (toJson t) : Except String BinderType) = .ok t := by
  cases t with
  | timepoint => rfl
  | named path =>
    show binderTypeOfJson (instToJsonBinderType.toJson (.named path)) = _
    rw [binderTypeOfJson_eq]
    show instFromJsonBinderType.fromJson (instToJsonBinderType.toJson (.named path)) = _
    have ht := getTag?_single "named" (Json.mkObj [("path", toJson path)])
    have hp : (Json.mkObj [("named", Json.mkObj [("path", toJson path)])]).getObjVal? "named" =
        .ok (Json.mkObj [("path", toJson path)]) := rfl
    have hq : (Json.mkObj [("path", toJson path)]).getObjVal? "path" = .ok (toJson path) := rfl
    have hf : (Json.mkObj [("named", Json.mkObj [("path", toJson path)])]).parseCtorFields "named" 1
        (some #[`path]) = .ok #[toJson path] := by
      unfold Json.parseCtorFields
      rw [hp]
      simp only [bind, Except.bind, Array.mapM_eq_mapM_toList]
      have hn : (`path : Lean.Name).getString! = "path" := rfl
      simp [hn, hq, pure, Except.pure, Functor.map, Except.map]
    unfold instFromJsonBinderType.fromJson instToJsonBinderType.toJson
    simp only [ht, hf]
    show (do let a ← fromJson? (#[toJson path])[0]!; pure (BinderType.named a)) = _
    have : (#[toJson path])[0]! = toJson path := rfl
    rw [this, rt_path]
    rfl

theorem rt_binder (b : Binder) : (fromJson? (toJson b) : Except String Binder) = .ok b := by
  obtain ⟨name, ty⟩ := b
  show instFromJsonBinder.fromJson (instToJsonBinder.toJson ⟨name, ty⟩) = _
  unfold instFromJsonBinder.fromJson instToJsonBinder.toJson
  simp only [List.flatten_cons, List.flatten_nil, List.cons_append, List.nil_append,
    Json.getObjValAs?]
  have h1 : (Json.mkObj [("name", toJson name), ("ty", toJson ty)]).getObjValD "name" = toJson name := rfl
  have h2 : (Json.mkObj [("name", toJson name), ("ty", toJson ty)]).getObjValD "ty" = toJson ty := rfl
  rw [h1, h2, rt_string, rt_binderType]
  rfl

theorem rt_binders (l : List Binder) : (fromJson? (toJson l) : Except String (List Binder)) = .ok l :=
  rt_list rt_binder l

/-! ## The decoders on a constructor's encoding -/

theorem termOfJson_entity (x : Json) :
    termOfJson (ctor "entity" [("uid", x)]) = Term.entity <$> fromJson? x := by rw [termOfJson]; rfl
theorem termOfJson_long (x : Json) :
    termOfJson (ctor "long" [("i", x)]) = Term.long <$> fromJson? x := by rw [termOfJson]; rfl
theorem termOfJson_decimal (x : Json) :
    termOfJson (ctor "decimal" [("text", x)]) = Term.decimal <$> fromJson? x := by rw [termOfJson]; rfl
theorem termOfJson_string (x : Json) :
    termOfJson (ctor "string" [("s", x)]) = Term.string <$> fromJson? x := by rw [termOfJson]; rfl
theorem termOfJson_bool (x : Json) :
    termOfJson (ctor "bool" [("b", x)]) = Term.bool <$> fromJson? x := by rw [termOfJson]; rfl
theorem termOfJson_context (x : Json) :
    termOfJson (ctor "context" [("path", x)]) = Term.context <$> fromJson? x := by rw [termOfJson]; rfl
theorem termOfJson_scope (r p : Json) :
    termOfJson (ctor "scope" [("root", r), ("path", p)]) =
      (do let r' ← fromJson? r; let p' ← fromJson? p; return Term.scope r' p') := by
  rw [termOfJson]; rfl
theorem termOfJson_var (x : Json) :
    termOfJson (ctor "var" [("x", x)]) = Term.var <$> fromJson? x := by rw [termOfJson]; rfl
theorem termOfJson_wildcard : termOfJson (Json.str "wildcard") = .ok .wildcard := by
  rw [termOfJson]; rfl
theorem termOfJson_agg (x : Json) :
    termOfJson (ctor "agg" [("a", x)]) = Term.agg <$> aggregateOfJson x := by rw [termOfJson]; rfl
theorem termOfJson_arith (o l r : Json) :
    termOfJson (ctor "arith" [("op", o), ("l", l), ("r", r)]) =
      (do let op ← fromJson? o; let l' ← termOfJson l; let r' ← termOfJson r; return .arith op l' r') := by
  rw [termOfJson]; rfl

theorem aggregateOfJson_count (d b : Json) :
    aggregateOfJson (ctor "count" [("domain", d), ("body", b)]) =
      (do let d' ← fromJson? d; let b' ← formulaOfJson b; return .count d' b') := by
  rw [aggregateOfJson]; rfl
theorem aggregateOfJson_sum (s d b : Json) :
    aggregateOfJson (ctor "sum" [("summand", s), ("domain", d), ("body", b)]) =
      (do let s' ← fromJson? s; let d' ← fromJson? d; let b' ← formulaOfJson b; return .sum s' d' b') := by
  rw [aggregateOfJson]; rfl

theorem formulaOfJson_and (x y : Json) :
    formulaOfJson (ctor "and" [("φ", x), ("ψ", y)]) =
      (do let φ ← formulaOfJson x; let ψ ← formulaOfJson y; return .and φ ψ) := by
  rw [formulaOfJson]; rfl
theorem formulaOfJson_not (x : Json) :
    formulaOfJson (ctor "not" [("φ", x)]) = Formula.not <$> formulaOfJson x := by
  rw [formulaOfJson]; rfl
theorem formulaOfJson_formerly (w x : Json) :
    formulaOfJson (ctor "formerly" [("w", w), ("φ", x)]) =
      (do let w' ← fromJson? w; let φ ← formulaOfJson x; return .formerly w' φ) := by
  rw [formulaOfJson]; rfl
theorem formulaOfJson_previous (w x : Json) :
    formulaOfJson (ctor "previous" [("w", w), ("φ", x)]) =
      (do let w' ← fromJson? w; let φ ← formulaOfJson x; return .previous w' φ) := by
  rw [formulaOfJson]; rfl
theorem formulaOfJson_since (x w y : Json) :
    formulaOfJson (ctor "since" [("φ", x), ("w", w), ("ψ", y)]) =
      (do let φ ← formulaOfJson x; let w' ← fromJson? w; let ψ ← formulaOfJson y
          return .since φ w' ψ) := by
  rw [formulaOfJson]; rfl

/-- One predicate argument, as `formulaOfJson` decodes it. -/
def predArg (p : Json) : Except String (Path × Term) := do
  let path : Path ← fromJson? (← p.getArrVal? 0)
  let ⟨t, _⟩ ← getArrValS p 1
  return (path, ← termOfJson t)

theorem formulaOfJson_pred (a k argsJ : Json) :
    formulaOfJson (ctor "pred" [("action", a), ("kind", k), ("args", argsJ)]) =
    (do
      let as ← getArrS argsJ
      let args' ← as.toList.mapM fun x => predArg x.val
      return .pred (← fromJson? a) (← fromJson? k) args') := by
  rw [formulaOfJson]; rfl

theorem formulaOfJson_cmp (o l r : Json) :
    formulaOfJson (ctor "cmp" [("op", o), ("l", l), ("r", r)]) =
      (do let op ← fromJson? o; let l' ← termOfJson l; let r' ← termOfJson r; return .cmp op l' r') := by
  rw [formulaOfJson]; rfl
theorem formulaOfJson_exist (x b : Json) :
    formulaOfJson (ctor "exist" [("x", x), ("φ", b)]) =
      (do let x' ← fromJson? x; let φ ← formulaOfJson b; return .exist x' φ) := by
  rw [formulaOfJson]; rfl
theorem formulaOfJson_tp (x : Json) :
    formulaOfJson (ctor "tp" [("x", x)]) = Formula.tp <$> fromJson? x := by
  rw [formulaOfJson]; rfl

theorem predArg_arr (x y : Json) :
    predArg (Json.arr #[x, y]) = (do let p ← fromJson? x; let t ← termOfJson y; return (p, t)) := rfl

theorem getArrS_mapM_bind {β γ : Type} (l : List Json) (g : Json → Except String β)
    (k : List β → Except String γ) :
    (do let as ← getArrS (Json.arr l.toArray); let r ← as.toList.mapM (fun x => g x.val); k r) =
      (do let r ← l.mapM g; k r) := by
  have h : (do let as ← getArrS (Json.arr l.toArray); as.toList.mapM fun x => g x.val) = l.mapM g := by
    simp only [getArrS, bind, Except.bind]
    simp [List.mapM_map]
  simp only [getArrS, bind, Except.bind] at h ⊢
  rw [h]

/-! ## The round trip -/

mutual

theorem termOfJson_termToJson : (t : Term) → termOfJson (termToJson t) = .ok t
  | .entity u => by simp only [termToJson, termOfJson_entity, rt_uid]; rfl
  | .long i => by simp only [termToJson, termOfJson_long, rt_int64]; rfl
  | .decimal t => by simp only [termToJson, termOfJson_decimal, rt_string]; rfl
  | .string t => by simp only [termToJson, termOfJson_string, rt_string]; rfl
  | .bool b => by simp only [termToJson, termOfJson_bool, rt_bool]; rfl
  | .context p => by simp only [termToJson, termOfJson_context, rt_path]; rfl
  | .scope r p => by simp only [termToJson, termOfJson_scope, rt_scopeRoot, rt_path]; rfl
  | .var x => by simp only [termToJson, termOfJson_var, rt_string]; rfl
  | .wildcard => termOfJson_wildcard
  | .agg a => by
    simp only [termToJson, termOfJson_agg, aggregateOfJson_aggregateToJson a]; rfl
  | .arith op l r => by
    simp only [termToJson, termOfJson_arith, rt_arithOp, termOfJson_termToJson l,
      termOfJson_termToJson r]; rfl

theorem aggregateOfJson_aggregateToJson : (a : Aggregate) → aggregateOfJson (aggregateToJson a) = .ok a
  | .count dom body => by
    simp only [aggregateToJson, aggregateOfJson_count, rt_binders, formulaOfJson_formulaToJson body]
    rfl
  | .sum s dom body => by
    simp only [aggregateToJson, aggregateOfJson_sum, rt_string, rt_binders,
      formulaOfJson_formulaToJson body]
    rfl

/-- **The decoder inverts the encoder.** -/
theorem formulaOfJson_formulaToJson : (φ : Formula) → formulaOfJson (formulaToJson φ) = .ok φ
  | .and φ ψ => by
    simp only [formulaToJson, formulaOfJson_and, formulaOfJson_formulaToJson φ,
      formulaOfJson_formulaToJson ψ]; rfl
  | .not φ => by simp only [formulaToJson, formulaOfJson_not, formulaOfJson_formulaToJson φ]; rfl
  | .formerly w φ => by
    simp only [formulaToJson, formulaOfJson_formerly, rt_window, formulaOfJson_formulaToJson φ]; rfl
  | .previous w φ => by
    simp only [formulaToJson, formulaOfJson_previous, rt_window, formulaOfJson_formulaToJson φ]; rfl
  | .since φ w ψ => by
    simp only [formulaToJson, formulaOfJson_since, rt_window, formulaOfJson_formulaToJson φ,
      formulaOfJson_formulaToJson ψ]; rfl
  | .pred a k args => by
    simp only [formulaToJson, formulaOfJson_pred]
    rw [getArrS_mapM_bind, argsOfJson_argsToJson args]
    simp only [bind, Except.bind, rt_uid, rt_string]
    rfl
  | .cmp op l r => by
    simp only [formulaToJson, formulaOfJson_cmp, rt_cmpOp, termOfJson_termToJson l,
      termOfJson_termToJson r]; rfl
  | .exist x φ => by
    simp only [formulaToJson, formulaOfJson_exist, rt_binder, formulaOfJson_formulaToJson φ]; rfl
  | .tp x => by simp only [formulaToJson, formulaOfJson_tp, rt_string]; rfl

theorem argsOfJson_argsToJson : (args : List (Path × Term)) → (argsToJson args).mapM predArg = .ok args
  | [] => rfl
  | (p, t) :: rest => by
    simp only [argsToJson, List.mapM_cons, predArg_arr, rt_path, termOfJson_termToJson t,
      argsOfJson_argsToJson rest]
    rfl

end

end Dogwood.Conformance
