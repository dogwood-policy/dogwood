import Dogwood.Thm.Lowering
import Dogwood.Thm.Leaves
import Cedar.Thm.Validation
import Cedar.Thm.Validation.EnvironmentValidation

/-!
# Augmented schemas and requests: the basic facts

The request environments of a schema (`mem_environments`), the schema with attributes added to
every action's context (`augmentEnv`), the leaves' attributes and types (`PolicySet.leafTypes`,
`hoistedTypes_eq`), and the augmented request (`PolicySet.augmentRequest`). Moved here from
`Dogwood.Thm.CedarSoundness`, so that the action-selective augmentation
(`Dogwood.Thm.SelectiveAugment`) can use them.
-/

namespace Dogwood.Thm

open Dogwood.Spec Dogwood.Spec.Temporal
open Cedar.Spec (Value Attr Request Entities EntityUID)
open Cedar.Data (Map)
open Cedar.Validation (CedarType RecordType TypeEnv Schema QualifiedType Qualified
  ActionSchemaEntry RequestType)
open Cedar.Thm (InstanceOfType InstanceOfEntityType InstanceOfRequestType InstanceOfSchema
  InstanceOfWellFormedEnvironment)

/-! ## Environments -/

/-- `Schema.environments`, restated: each action, with each principal and resource type it
applies to. -/
def schemaEnvironments (A : Schema) : List TypeEnv :=
  (A.acts.toList.flatMap (fun (action, entry) =>
    entry.appliesToPrincipal.toList.product entry.appliesToResource.toList |>.map
      (fun (principal, resource) =>
        ({ principal, action, resource, context := entry.context } : RequestType)))).map
    ({ ets := A.ets, acts := A.acts, reqty := · })

theorem environments_eq (A : Schema) : A.environments = schemaEnvironments A := rfl

theorem mem_product' {α β : Type} {xs : List α} {ys : List β} {a : α} {b : β} :
    (a, b) ∈ xs.product ys ↔ a ∈ xs ∧ b ∈ ys := by
  simp [List.product]

theorem mem_environments {A : Schema} {env : TypeEnv} :
    env ∈ A.environments ↔ ∃ a entry p r, (a, entry) ∈ A.acts.toList ∧
      p ∈ entry.appliesToPrincipal.toList ∧ r ∈ entry.appliesToResource.toList ∧
      env = { ets := A.ets, acts := A.acts,
              reqty := { principal := p, action := a, resource := r, context := entry.context } } := by
  rw [environments_eq]
  unfold schemaEnvironments
  simp only [List.mem_map, List.mem_flatMap]
  constructor
  · rintro ⟨rt, ⟨⟨a, entry⟩, hmem, ⟨p, r⟩, hpr, rfl⟩, rfl⟩
    obtain ⟨hp, hr⟩ := mem_product'.mp hpr
    exact ⟨a, entry, p, r, hmem, hp, hr, rfl⟩
  · rintro ⟨a, entry, p, r, hmem, hp, hr, rfl⟩
    exact ⟨_, ⟨⟨a, entry⟩, hmem, ⟨p, r⟩, mem_product'.mpr ⟨hp, hr⟩, rfl⟩, rfl⟩

/-- The action entry `entry` with the attributes `H` added to its context record type. -/
def augmentEntry (H : List (Attr × QualifiedType)) (entry : ActionSchemaEntry) :
    ActionSchemaEntry :=
  { entry with context := Map.make (entry.context.toList ++ H) }

theorem augment_acts (A : Schema) (H : List (Attr × QualifiedType)) :
    (Schema.augment A H).acts = A.acts.mapOnValues (augmentEntry H) := rfl

/-- The environment of the augmented schema that corresponds to an environment of the schema:
the same request type, with the attributes `H` added to its context record type. -/
def augmentEnv (A : Schema) (H : List (Attr × QualifiedType)) (env : TypeEnv) : TypeEnv :=
  { ets := env.ets, acts := (Schema.augment A H).acts,
    reqty := { env.reqty with context := Map.make (env.reqty.context.toList ++ H) } }

theorem augmentEnv_mem {A : Schema} {H : List (Attr × QualifiedType)} {env : TypeEnv}
    (h : env ∈ A.environments) : augmentEnv A H env ∈ (Schema.augment A H).environments := by
  obtain ⟨a, entry, p, r, hmem, hp, hr, rfl⟩ := mem_environments.mp h
  refine mem_environments.mpr ⟨a, augmentEntry H entry, p, r, ?_, hp, hr, rfl⟩
  rw [augment_acts]
  show (a, augmentEntry H entry) ∈ (A.acts.toList.map fun x => (x.1, augmentEntry H x.2))
  exact List.mem_map.mpr ⟨(a, entry), hmem, rfl⟩

theorem augmentEnv_contains {A : Schema} {H : List (Attr × QualifiedType)} {env : TypeEnv}
    (h : env ∈ A.environments) (uid : EntityUID) :
    (augmentEnv A H env).acts.contains uid = env.acts.contains uid := by
  obtain ⟨_, _, _, _, _, _, _, rfl⟩ := mem_environments.mp h
  exact Map.contains_mapOnValues _

/-- A value's type depends on the environment only through its entity types and the actions it
contains. -/
theorem instanceOfType_congr_contains {env env' : TypeEnv} (hets : env'.ets = env.ets)
    (hacts : ∀ uid, env'.acts.contains uid = env.acts.contains uid) {w : Value} {ty : CedarType}
    (h : InstanceOfType env w ty) : InstanceOfType env' w ty := by
  induction h with
  | instance_of_bool b bty h₁ => exact .instance_of_bool b bty h₁
  | instance_of_int => exact .instance_of_int
  | instance_of_string => exact .instance_of_string
  | instance_of_entity e ety h₁ =>
    refine .instance_of_entity e ety ⟨h₁.1, ?_⟩
    have := h₁.2
    simp only [Cedar.Validation.EntityUID.WellFormed] at this ⊢
    rw [hets, hacts]
    exact this
  | instance_of_set s ty _ ih => exact .instance_of_set s ty ih
  | instance_of_record r rty h₁ _ h₃ ih => exact .instance_of_record r rty h₁ ih h₃
  | instance_of_ext x xty h₁ => exact .instance_of_ext x xty h₁

theorem instanceOfEntityType_congr {env env' : TypeEnv} (hets : env'.ets = env.ets)
    (hacts : ∀ uid, env'.acts.contains uid = env.acts.contains uid) {uid : EntityUID}
    {ety : Cedar.Spec.EntityType} (h : InstanceOfEntityType uid ety env) :
    InstanceOfEntityType uid ety env' := by
  refine ⟨h.1, ?_⟩
  have := h.2
  simp only [Cedar.Validation.EntityUID.WellFormed] at this ⊢
  rw [hets, hacts]
  exact this

/-! ## Lists of attributes -/

theorem map_find?_eq {β : Type} (m : Map Attr β) (k : Attr) :
    m.find? k = (m.toList.find? (·.1 == k)).map (·.2) := by
  unfold Map.find?
  cases m.toList.find? (fun x => x.1 == k) with
  | none => rfl
  | some p => rfl

theorem make_append_find? {β : Type} (l₁ l₂ : List (Attr × β)) (k : Attr) :
    (Map.make (l₁ ++ l₂)).find? k = ((l₁.find? (·.1 == k)).or (l₂.find? (·.1 == k))).map (·.2) := by
  rw [Map.make_find?_eq_list_find?, List.find?_append]

theorem eq_of_mem_of_key {β : Type} : {L : List (Attr × β)} → (L.map (·.1)).Nodup →
    ∀ {p q : Attr × β}, p ∈ L → q ∈ L → p.1 = q.1 → p = q
  | [], _, _, _, hp, _, _ => by cases hp
  | x :: L, hnd, p, q, hp, hq, h => by
    simp only [List.map_cons, List.nodup_cons] at hnd
    obtain ⟨hx, hnd⟩ := hnd
    rcases List.mem_cons.mp hp with rfl | hp' <;> rcases List.mem_cons.mp hq with rfl | hq'
    · rfl
    · exact absurd (h ▸ List.mem_map.mpr ⟨q, hq', rfl⟩) hx
    · exact absurd (h.symm ▸ List.mem_map.mpr ⟨p, hp', rfl⟩) hx
    · exact eq_of_mem_of_key hnd hp' hq' h

/-- In a list whose keys are distinct, a key finds its pair. -/
theorem find?_of_mem {β : Type} {L : List (Attr × β)} (hnd : (L.map (·.1)).Nodup) {k : Attr} {v : β}
    (h : (k, v) ∈ L) : L.find? (·.1 == k) = some (k, v) := by
  cases hf : L.find? (·.1 == k) with
  | none =>
    have := List.find?_eq_none.mp hf (k, v) h
    simp at this
  | some p =>
    have hp := List.mem_of_find?_eq_some hf
    have hpk : p.1 = k := by simpa using List.find?_some hf
    rw [Option.some.injEq]
    exact eq_of_mem_of_key hnd hp h hpk

theorem find?_of_not_mem {β : Type} {L : List (Attr × β)} {k : Attr} (h : k ∉ L.map (·.1)) :
    L.find? (·.1 == k) = none :=
  List.find?_eq_none.mpr fun x hx hk => h (List.mem_map.mpr ⟨x, hx, by simpa using hk⟩)

/-- An `Option`-valued `mapM` that succeeds maps every element. -/
theorem mapM_option_eq_map {α β : Type} [Inhabited β] {f : α → Option β} :
    ∀ {xs : List α} {ys : List β}, xs.mapM f = some ys →
      ys = xs.map (fun x => (f x).getD default) ∧ ∀ x ∈ xs, (f x).isSome = true
  | [], ys, h => by simp at h; subst h; simp
  | x :: xs, ys, h => by
    simp only [List.mapM_cons] at h
    cases hx : f x with
    | none => rw [hx] at h; cases h
    | some y =>
      cases hxs : xs.mapM f with
      | none => rw [hx, hxs] at h; cases h
      | some ys' =>
        rw [hx, hxs] at h
        have hys : ys = y :: ys' := by simpa using h.symm
        subst hys
        obtain ⟨h₁, h₂⟩ := mapM_option_eq_map hxs
        refine ⟨by simp [hx, h₁], fun z hz => ?_⟩
        rcases List.mem_cons.mp hz with rfl | hz
        · simp [hx]
        · exact h₂ z hz

/-! ## The augmented request -/

/-- The leaves' attributes and values, in order. -/
def _root_.Dogwood.Spec.PolicySet.leafEntries (P : PolicySet) (θ : Leaves) : List (Attr × Value) :=
  P.leafList.zipIdx.map fun (l, k) => (leafAttr k, θ.valueOf l)

/-- The augmented context: the context, extended by every leaf's value at the leaf's attribute.
A policy set without leaves leaves the context as it is. -/
def _root_.Dogwood.Spec.PolicySet.augmentContext (P : PolicySet) (θ : Leaves)
    (ctx : Map Attr Value) : Map Attr Value :=
  if P.leafList = [] then ctx else Map.make (P.leafEntries θ ++ ctx.toList)

/-- **The augmented request**: the request, with its context extended by every leaf's value at
the leaf's attribute. A policy set without leaves leaves the request as it is. -/
def _root_.Dogwood.Spec.PolicySet.augmentRequest (P : PolicySet) (θ : Leaves) (req : Request) :
    Request :=
  { req with context := P.augmentContext θ req.context }

/-- The type of every leaf's attribute, in order. -/
def _root_.Dogwood.Spec.PolicySet.leafTypes (P : PolicySet) : List (Attr × QualifiedType) :=
  P.leafList.zipIdx.map fun (l, k) => (leafAttr k, .required ((P.leafType? l).getD default))

theorem leafEntries_keys (P : PolicySet) (θ : Leaves) :
    (P.leafEntries θ).map (·.1) = P.hoistedNames := by
  simp only [PolicySet.leafEntries, PolicySet.hoistedNames, List.map_map, Function.comp_def]
  rw [show (fun x : Leaf × Nat => leafAttr x.2) = leafAttr ∘ Prod.snd from rfl, ← List.map_map,
    List.zipIdx_map_snd, List.range_eq_range']

theorem leafTypes_keys (P : PolicySet) : P.leafTypes.map (·.1) = P.hoistedNames := by
  simp only [PolicySet.leafTypes, PolicySet.hoistedNames, List.map_map, Function.comp_def]
  rw [show (fun x : Leaf × Nat => leafAttr x.2) = leafAttr ∘ Prod.snd from rfl, ← List.map_map,
    List.zipIdx_map_snd, List.range_eq_range']

theorem hoistedTypes_eq {P : PolicySet} {H : List (Attr × QualifiedType)}
    (h : P.hoistedTypes? = some H) : H = P.leafTypes ∧ ∀ l ∈ P.leafList, (P.leafType? l).isSome := by
  unfold PolicySet.hoistedTypes? at h
  obtain ⟨h₁, h₂⟩ := mapM_option_eq_map h
  refine ⟨?_, fun l hl => ?_⟩
  · rw [h₁]
    unfold PolicySet.leafTypes
    apply List.map_congr_left
    intro ⟨l, k⟩ hlk
    have := h₂ (l, k) hlk
    simp only at this ⊢
    cases hty : P.leafType? l with
    | none => rw [hty] at this; cases this
    | some ty => rfl
  · obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hl
    have := h₂ (P.leafList[i], i) (by
      rw [List.mem_iff_getElem?]
      exact ⟨i, by simp [hi]⟩)
    simpa [Option.isSome_map] using this

theorem mem_leafEntries {P : PolicySet} {θ : Leaves} {i : Nat} (hi : i < P.leafList.length) :
    (leafAttr i, θ.valueOf P.leafList[i]) ∈ P.leafEntries θ := by
  unfold PolicySet.leafEntries
  exact List.mem_map.mpr ⟨(P.leafList[i], i), by
    rw [List.mem_iff_getElem?]; exact ⟨i, by simp [hi]⟩, rfl⟩

theorem mem_leafTypes {P : PolicySet} {i : Nat} (hi : i < P.leafList.length) :
    (leafAttr i, .required ((P.leafType? P.leafList[i]).getD default)) ∈ P.leafTypes := by
  unfold PolicySet.leafTypes
  exact List.mem_map.mpr ⟨(P.leafList[i], i), by
    rw [List.mem_iff_getElem?]; exact ⟨i, by simp [hi]⟩, rfl⟩

theorem mem_hoistedNames {P : PolicySet} {a : Attr} :
    a ∈ P.hoistedNames ↔ ∃ i, i < P.leafList.length ∧ a = leafAttr i := by
  simp only [PolicySet.hoistedNames, List.mem_map, List.mem_range]
  exact ⟨fun ⟨i, hi, h⟩ => ⟨i, hi, h.symm⟩, fun ⟨i, hi, h⟩ => ⟨i, hi, h.symm⟩⟩

end Dogwood.Thm
