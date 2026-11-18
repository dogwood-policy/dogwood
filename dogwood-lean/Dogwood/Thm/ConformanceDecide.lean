import Dogwood.Eval.Conformance
import Cedar.Thm.Data.List.Lemmas
import Cedar.Thm.Data.Set

/-!
# The conformance checks decide conformance

The structural restatement of Cedar's `instanceOfType` is Cedar's (`valueInstanceOf_eq`), so the
Boolean checks of `Dogwood.Eval.Conformance` decide the runtime conformance relations of
`Dogwood.Spec.Conformance`, and the kernel can evaluate them on concrete data.
-/

namespace Dogwood.Thm

open Dogwood.Spec Dogwood.Spec.Temporal Dogwood.Eval
open Cedar.Spec (Value Attr Request)
open Cedar.Data (Map Set)
open Cedar.Validation (CedarType RecordType TypeEnv Schema instanceOfType)

mutual

/-- **The structural restatement is Cedar's `instanceOfType`.** -/
theorem valueInstanceOf_eq (env : Schema) : (v : Value) → (ty : CedarType) →
    valueInstanceOf env v ty = instanceOfType v ty env
  | .prim (.bool _), ty => by cases ty <;> simp [valueInstanceOf, instanceOfType]
  | .prim (.int _), ty => by cases ty <;> simp [valueInstanceOf, instanceOfType]
  | .prim (.string _), ty => by cases ty <;> simp [valueInstanceOf, instanceOfType]
  | .prim (.entityUID _), ty => by cases ty <;> simp [valueInstanceOf, instanceOfType]
  | .ext _, ty => by cases ty <;> simp [valueInstanceOf, instanceOfType]
  | .set (.mk vs), ty => by
    cases ty with
    | set ty =>
      rw [instanceOfType, valueInstanceOf, valuesInstanceOf_eq env vs ty]
      simp [Set.all₁]
    | _ => simp [valueInstanceOf, instanceOfType]
  | .record (.mk kvs), ty => by
    cases ty with
    | record rty =>
      rw [instanceOfType, valueInstanceOf, fieldsInstanceOf_eq env kvs rty]
      congr 2
      rw [Bool.eq_iff_iff, List.all_eq_true, List.all_eq_true]
      constructor
      · rintro h ⟨⟨k, v⟩, hp⟩ hm
        simp only [Map.toList, List.attach₂] at hm
        have := h (k, v) ((List.mem_pmap_subtype _ _ _ _).mp hm)
        cases hf : rty.find? k <;> simp_all
      · intro h kv hkv
        obtain ⟨k, v⟩ := kv
        have := h ⟨(k, v), List.sizeOf_snd_lt_sizeOf_list hkv⟩
          (by simp only [Map.toList, List.attach₂]; exact (List.mem_pmap_subtype _ _ _ _).mpr hkv)
        cases hf : rty.find? k <;> simp_all
    | _ => simp [valueInstanceOf, instanceOfType]

theorem valuesInstanceOf_eq (env : Schema) : (vs : List Value) → (ty : CedarType) →
    valuesInstanceOf env vs ty = vs.all (instanceOfType · ty env)
  | [], _ => rfl
  | v :: vs, ty => by
    simp only [valuesInstanceOf, List.all_cons, valueInstanceOf_eq env v ty,
      valuesInstanceOf_eq env vs ty]

theorem fieldsInstanceOf_eq (env : Schema) : (kvs : List (Attr × Value)) → (rty : RecordType) →
    fieldsInstanceOf env kvs rty = kvs.all (fun (k, v) => match rty.find? k with
      | some qty => instanceOfType v qty.getType env
      | none => true)
  | [], _ => rfl
  | (k, v) :: kvs, rty => by
    simp only [fieldsInstanceOf, List.all_cons, fieldsInstanceOf_eq env kvs rty]
    cases rty.find? k with
    | none => rfl
    | some qty => simp only [valueInstanceOf_eq env v qty.getType]

end

theorem hasValueB_iff (A : Schema) (ft : FieldTy) (w : Value) :
    ft.hasValueB A w = true ↔ ft.HasValue A w := by
  cases ft with
  | cedar ty => simp [FieldTy.hasValueB, FieldTy.HasValue, valueInstanceOf_eq]
  | entities etys =>
    cases w with
    | prim p =>
      cases p with
      | entityUID uid => simp [FieldTy.hasValueB, FieldTy.HasValue]
      | _ => simp [FieldTy.hasValueB, FieldTy.HasValue]
    | _ => simp [FieldTy.hasValueB, FieldTy.HasValue]

theorem loggedByB_iff (A : Schema) (fd : FieldDecl) (ev : Event) :
    fd.loggedByB A ev = true ↔ fd.LoggedBy A ev := by
  unfold FieldDecl.loggedByB FieldDecl.LoggedBy
  cases recordPath? ev.logged fd.path with
  | some w => exact hasValueB_iff A fd.ty w
  | none => simp

theorem mirroredB_iff (ev : Event) (m : Path × PinRef) : mirroredB ev m = true ↔ Mirrored ev m := by
  unfold mirroredB Mirrored
  cases m.2.toTerm.eval? ev Valuation.empty with
  | some t => cases t <;> simp
  | none => simp

theorem admitsB_iff (A : Schema) (sig : EventSignature) (ev : Event) :
    sig.admitsB A ev = true ↔ sig.Admits A ev := by
  simp only [EventSignature.admitsB, Bool.and_eq_true, List.all_eq_true, loggedByB_iff,
    mirroredB_iff, canonicalB_iff]
  exact ⟨fun ⟨⟨⟨⟨h₁, h₂⟩, h₃⟩, h₄⟩, h₅⟩ => ⟨h₁, h₂, h₃, h₄, h₅⟩,
    fun ⟨h₁, h₂, h₃, h₄, h₅⟩ => ⟨⟨⟨⟨h₁, h₂⟩, h₃⟩, h₄⟩, h₅⟩⟩

/-- **The event check decides event conformance.** -/
theorem conformsB_iff (A : Schema) (S : EventSchema) (ev : Event) :
    ev.conformsB A S = true ↔ ev.Conforms A S := by
  unfold Event.conformsB Event.Conforms
  cases S.signature? ev.action ev.kind with
  | some sig => exact admitsB_iff A sig ev
  | none => simp

/-- **The request check is Cedar's request validation.** -/
theorem requestConformsB_eq (A : Schema) (req : Request) :
    requestConformsB A req = succeeds (Cedar.Validation.validateRequest A req) := by
  have h : requestConformsB A req =
      A.environments.any (Cedar.Validation.requestMatchesEnvironment · req) := by
    unfold requestConformsB
    simp only [Cedar.Validation.requestMatchesEnvironment, Cedar.Validation.instanceOfRequestType,
      valueInstanceOf_eq]
  rw [h]
  unfold Cedar.Validation.validateRequest
  by_cases hb : A.environments.any (Cedar.Validation.requestMatchesEnvironment · req) = true <;>
    simp [hb, succeeds]

/-- **The output check decides output conformance.** -/
theorem output_conformsB_iff (A : Schema) (ty : CedarType) (o : Provider.Output) :
    o.conformsB A ty = true ↔ o.Conforms A ty := by
  cases o <;> simp [Provider.Output.conformsB, Provider.Output.Conforms, valueInstanceOf_eq]

end Dogwood.Thm
