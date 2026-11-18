/-
 Copyright Cedar Contributors

 Licensed under the Apache License, Version 2.0 (the "License");
 you may not use this file except in compliance with the License.
 You may obtain a copy of the License at

      https://www.apache.org/licenses/LICENSE-2.0

 Unless required by applicable law or agreed to in writing, software
 distributed under the License is distributed on an "AS IS" BASIS,
 WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 See the License for the specific language governing permissions and
 limitations under the License.
-/

import Cedar.Spec
import Cedar.Validation
import Cedar.Thm.Data.Control
import Cedar.Thm.Data.Set
import Cedar.Thm.Validation.Typechecker.LUB
import Cedar.Thm.Validation.Typechecker.WF

/-!
This file contains useful definitions and lemmas about Cedar types.
-/

namespace Cedar.Thm

open Cedar.Data
open Cedar.Spec
open Cedar.Validation

----- Definitions -----

def InstanceOfBoolType : Bool → BoolType → Prop
  | true,  .tt      => True
  | false, .ff      => True
  | _,     .anyBool => True
  | _, _            => False

def InstanceOfEntityType (e : EntityUID) (ety: EntityType) (env : TypeEnv) : Prop :=
  ety = e.ty ∧ EntityUID.WellFormed env e

def InstanceOfExtType : Ext → ExtType → Prop
  | .decimal _, .decimal => True
  | .ipaddr _,  .ipAddr  => True
  | .datetime _, .datetime => True
  | .duration _, .duration => True
  | _, _                 => False

inductive InstanceOfType (env : TypeEnv) : Value → CedarType → Prop where
  | instance_of_bool (b : Bool) (bty : BoolType)
      (h₁ : InstanceOfBoolType b bty) :
      InstanceOfType env (.prim (.bool b)) (.bool bty)
  | instance_of_int :
      InstanceOfType env (.prim (.int _)) .int
  | instance_of_string :
      InstanceOfType env (.prim (.string _)) .string
  | instance_of_entity (e : EntityUID) (ety: EntityType)
      (h₁ : InstanceOfEntityType e ety env) :
      InstanceOfType env (.prim (.entityUID e)) (.entity ety)
  | instance_of_set (s : Set Value) (ty : CedarType)
      (h₁ : ∀ v, v ∈ s → InstanceOfType env v ty) :
      InstanceOfType env (.set s) (.set ty)
  | instance_of_record (r : Map Attr Value) (rty : RecordType)
      -- if an attribute is present in the record, then it is present in the type
      (h₁ : ∀ (k : Attr), r.contains k → rty.contains k)
      -- if an attribute is present, then it has the expected type
      (h₂ : ∀ (k : Attr) (v : Value) (qty : QualifiedType),
        r.find? k = some v → rty.find? k = some qty → InstanceOfType env v qty.getType)
      -- required attributes are present
      (h₃ : ∀ (k : Attr) (qty : QualifiedType), rty.find? k = some qty → qty.isRequired → r.contains k) :
      InstanceOfType env (.record r) (.record rty)
  | instance_of_ext (x : Ext) (xty : ExtType)
      (h₁ : InstanceOfExtType x xty) :
      InstanceOfType env (.ext x) (.ext xty)

def InstanceOfRequestType (request : Request) (env : TypeEnv) : Prop :=
  InstanceOfEntityType request.principal env.reqty.principal env ∧
  request.action = env.reqty.action ∧
  InstanceOfEntityType request.resource env.reqty.resource env ∧
  InstanceOfType env request.context (.record env.reqty.context)

def InstanceOfEntityTags (data : EntityData) (entry : EntitySchemaEntry) (env : TypeEnv) : Prop :=
  match entry.tags? with
  | .some tty => ∀ v ∈ data.tags.values, InstanceOfType env v tty
  | .none     => data.tags = Map.empty

def IsValidEntityEID (entry: EntitySchemaEntry) (eid: String) : Prop :=
  match entry with
  | .standard _ => True
  | .enum eids => eid ∈ eids

/--
For every entity `(uid, data)` in the store,
1. The entity's type is defined in the type store.
2. The entity's attributes match the attribute types indicated in the type store.
3. The entity's ancestors' types are consistent with the ancestor information
   in the type store.
4. The entity's tags' types are consistent with the tags information in the type store.
-/
def InstanceOfEntitySchemaEntry (uid : EntityUID) (data : EntityData) (env : TypeEnv) : Prop :=
  ∃ entry, env.ets.find? uid.ty = some entry ∧
    IsValidEntityEID entry uid.eid ∧
    InstanceOfType env data.attrs (.record entry.attrs) ∧
    (∀ ancestor, ancestor ∈ data.ancestors → ancestor.ty ∈ entry.ancestors) ∧
    InstanceOfEntityTags data entry env

/--
Similar to `WellFormedEntityData`, but a special case for action entities
since they are stored disjoint from `ets`
-/
def InstanceOfActionSchemaEntry (uid : EntityUID) (data : EntityData) (env : TypeEnv) : Prop :=
  -- Action entities cannot have attributes or tags
  data.attrs = .empty ∧
  data.tags = .empty ∧
  ∃ entry,
    env.acts.find? uid = some entry ∧
    data.ancestors = entry.ancestors

def InstanceOfSchemaEntry (uid : EntityUID) (data : EntityData) (env : TypeEnv) : Prop :=
  InstanceOfEntitySchemaEntry uid data env ∨
  InstanceOfActionSchemaEntry uid data env

def Entities.HasAllActions (entities : Entities) (env : TypeEnv) : Prop :=
  ∀ (uid : EntityUID) (entry : ActionSchemaEntry),
    env.acts.find? uid = some entry → ∃ data, entities.find? uid = some data

/--
Each entry in the store is valid
-/
def InstanceOfSchema (entities : Entities) (env : TypeEnv) : Prop :=
  -- Each entity data is valid
  (∀ (uid : EntityUID) (data : EntityData),
    entities.find? uid = some data → InstanceOfSchemaEntry uid data env) ∧
  Entities.HasAllActions entities env

def InstanceOfWellFormedEnvironment (request : Request) (entities : Entities) (env : TypeEnv) : Prop :=
  env.WellFormed ∧
  InstanceOfRequestType request env ∧
  InstanceOfSchema entities env

----- Theorems -----

theorem false_is_instance_of_ff {env : TypeEnv} :
  InstanceOfType env (Value.prim (Prim.bool false)) (CedarType.bool BoolType.ff)
:= by
  apply InstanceOfType.instance_of_bool
  simp [InstanceOfBoolType]

theorem true_is_instance_of_tt {env : TypeEnv} :
  InstanceOfType env (Value.prim (Prim.bool true)) (CedarType.bool BoolType.tt)
:= by
  apply InstanceOfType.instance_of_bool
  simp [InstanceOfBoolType]

theorem bool_is_instance_of_anyBool {env : TypeEnv} (b : Bool) :
  InstanceOfType env (Value.prim (Prim.bool b)) (CedarType.bool BoolType.anyBool)
:= by
  apply InstanceOfType.instance_of_bool
  simp [InstanceOfBoolType]

theorem duration_is_instance_of_duration {env : TypeEnv} {d : Duration}:
  InstanceOfType env (Value.ext (Ext.duration d)) (CedarType.ext .duration)
:= by
  apply InstanceOfType.instance_of_ext _ _
  simp only [InstanceOfExtType]

theorem datetime_is_instance_of_datetime {env : TypeEnv} {d : Ext.Datetime}:
  InstanceOfType env (Value.ext (Ext.datetime d)) (CedarType.ext .datetime)
:= by
  apply InstanceOfType.instance_of_ext _ _
  simp only [InstanceOfExtType]

theorem decimal_is_instance_of_decimal {env : TypeEnv} {d : Ext.Decimal}:
  InstanceOfType env (Value.ext (Ext.decimal d)) (CedarType.ext .decimal)
:= by
  apply InstanceOfType.instance_of_ext _ _
  simp only [InstanceOfExtType]

theorem ipaddr_is_instance_of_ipaddr {env : TypeEnv} {ip : IPAddr}:
  InstanceOfType env (Value.ext (Ext.ipaddr ip)) (CedarType.ext .ipAddr)
:= by
  apply InstanceOfType.instance_of_ext _ _
  simp only [InstanceOfExtType]

theorem instance_of_bool_is_bool {env : TypeEnv} {v₁ : Value} {bty : BoolType} :
  InstanceOfType env v₁ (CedarType.bool bty) →
  ∃ b, v₁ = .prim (.bool b)
:= by
  intro h₁
  rcases h₁ with ⟨b, _, _⟩
  exists b

theorem instance_of_ff_is_false {env : TypeEnv} {v₁ : Value} :
  InstanceOfType env v₁ (CedarType.bool BoolType.ff) →
  v₁ = .prim (.bool false)
:= by
  intro h₁
  cases h₁ with
  | instance_of_bool b _ h₁ =>
    simp [InstanceOfBoolType] at h₁
    cases b <;> simp at h₁
    rfl

theorem instance_of_tt_is_true {env : TypeEnv} {v₁ : Value} :
  InstanceOfType env v₁ (CedarType.bool BoolType.tt) →
  v₁ = .prim (.bool true)
:= by
  intro h₁
  cases h₁ with
  | instance_of_bool b _ h₁ =>
    simp [InstanceOfBoolType] at h₁
    cases b <;> simp at h₁
    rfl

theorem instance_of_anyBool_is_bool {env : TypeEnv} {v₁ : Value} :
  InstanceOfType env v₁ (CedarType.bool BoolType.anyBool) →
  ∃ b, v₁ = .prim (.bool b)
:= instance_of_bool_is_bool

theorem instance_of_int_is_int {env : TypeEnv} {v₁ : Value} :
  InstanceOfType env v₁ CedarType.int →
  ∃ i, v₁ = .prim (.int i)
:= by
  intro h₁
  cases h₁
  rename_i y
  exists y

theorem instance_of_string_is_string {env : TypeEnv} {v₁ : Value} :
  InstanceOfType env v₁ CedarType.string →
  ∃ s, v₁ = .prim (.string s)
:= by
  intro h₁
  cases h₁
  rename_i y
  exists y

theorem instance_of_entity_type_is_entity {env : TypeEnv} {ety : EntityType} :
  InstanceOfType env v₁ (.entity ety) →
  ∃ euid, euid.ty = ety ∧ v₁ = .prim (.entityUID euid)
:= by
  intro h₁
  cases h₁
  rename_i euid h₁
  simp only [InstanceOfEntityType] at h₁
  exists euid
  simp [h₁]

theorem instance_of_decimal_type_is_decimal {env : TypeEnv} {v₁ : Value} :
  InstanceOfType env v₁ (CedarType.ext ExtType.decimal) →
  ∃ d, v₁ = .ext (.decimal d)
:= by
  intro h₁
  cases h₁
  rename_i x h₁
  simp only [InstanceOfExtType] at h₁
  split at h₁ <;> try { contradiction }
  rename_i d _
  exists d

theorem instance_of_ipAddr_type_is_ipAddr {env : TypeEnv} {v₁ : Value} :
  InstanceOfType env v₁ (CedarType.ext ExtType.ipAddr) →
  ∃ d, v₁ = .ext (.ipaddr d)
:= by
  intro h₁
  cases h₁
  rename_i x h₁
  simp only [InstanceOfExtType] at h₁
  split at h₁ <;> try { contradiction }
  rename_i ip _
  exists ip

theorem instance_of_datetime_type_is_datetime {env : TypeEnv} {v₁ : Value} :
  InstanceOfType env v₁ (CedarType.ext ExtType.datetime) →
  ∃ d, v₁ = .ext (.datetime d)
:= by
  intro h₁
  cases h₁
  rename_i x h₁
  simp only [InstanceOfExtType] at h₁
  split at h₁ <;> try { contradiction }
  rename_i d _
  exists d

theorem instance_of_duration_type_is_duration {env : TypeEnv} {v₁ : Value} :
  InstanceOfType env v₁ (CedarType.ext ExtType.duration) →
  ∃ d, v₁ = .ext (.duration d)
:= by
  intro h₁
  cases h₁
  rename_i x h₁
  simp only [InstanceOfExtType] at h₁
  split at h₁ <;> try { contradiction }
  rename_i d _
  exists d

theorem instance_of_set_type_is_set {env : TypeEnv} {v : Value} {ty : CedarType} :
  InstanceOfType env v (.set ty) →
  ∃ s, v = .set s ∧ (∀ ev ∈ s, InstanceOfType env ev ty)
:= by
  intro h₁
  cases h₁
  rename_i s h₁
  exists s

theorem instance_of_record_type_is_record {env : TypeEnv} {v : Value} {rty : RecordType} :
  InstanceOfType env v (.record rty) →
  ∃ r, v = .record r
:= by
  intro h₁
  cases h₁
  rename_i r _ _ _
  exists r

theorem instance_of_attribute_type {env : TypeEnv} {r : Map Attr Value} {v : Value} {rty : RecordType} {a : Attr} {aty : CedarType} {qaty : QualifiedType}
  (h₁ : InstanceOfType env (.record r) (.record rty))
  (h₂ : rty.find? a = .some qaty)
  (h₃ : qaty.getType = aty)
  (h₄ : r.find? a = .some v) :
  InstanceOfType env v aty
:= by
  cases h₁
  rename_i _ h₅ _
  rw [←h₃]
  apply h₅ a v qaty h₄ h₂

theorem absent_attribute_is_absent {env : TypeEnv} {r : Map Attr Value} {rty : RecordType} {a : Attr}
  (h₁ : InstanceOfType env (.record r) (.record rty))
  (h₂ : rty.find? a = .none) :
  r.find? a = .none
:= by
  cases h₁
  case instance_of_record h₃ _ _ =>
    by_contra h₄
    simp [Option.ne_none_iff_exists', ←Map.contains_iff_some_find?] at h₄
    specialize h₃ a h₄
    simp [Map.contains_iff_some_find?, h₂] at h₃

theorem required_attribute_is_present {env : TypeEnv} {r : Map Attr Value} {rty : RecordType} {a : Attr} {aty : CedarType}
  (h₁ : InstanceOfType env (.record r) (.record rty))
  (h₂ : rty.find? a = .some (Qualified.required aty)) :
  ∃ v, r.find? a = .some v
:= by
  cases h₁
  rename_i h₃
  rw [←Map.contains_iff_some_find?]
  apply h₃ _ _ h₂
  simp [Qualified.isRequired]

theorem well_typed_entity_attributes
  {env : TypeEnv} {request : Request} {entities : Entities}
  {uid: EntityUID} {d: EntityData} {rty : RecordType}
  (h₁ : InstanceOfWellFormedEnvironment request entities env)
  (h₂ : Map.find? entities uid = some d)
  (h₃ : EntitySchema.attrs? env.ets uid.ty = some rty) :
  InstanceOfType env d.attrs (.record rty)
:= by
  have ⟨_, _, h₁, _⟩ := h₁
  simp [InstanceOfSchemaEntry] at h₁
  specialize h₁ uid d h₂
  cases h₁ with
  | inl h₁ =>
    have ⟨entry, h₁₂, _, h₁, _⟩ := h₁
    unfold EntitySchema.attrs? at h₃
    simp [h₁₂] at h₃
    subst h₃
    exact h₁
  | inr h₁ =>
    have ⟨h₁, _, _, ⟨_, hentry⟩⟩ := h₁
    simp only [EntitySchema.attrs?, Option.map] at h₃
    split at h₃
    · apply False.elim
      apply wf_env_disjoint_ets_acts
      all_goals assumption
    · contradiction

theorem instance_of_type_bool_is_bool {env : TypeEnv} (v : Value) (ty : CedarType) :
  InstanceOfType env v ty →
  ty ⊑ .bool .anyBool →
  ∃ b, v = .prim (.bool b)
:= by
  intro h₀ h₁
  cases v <;> cases ty <;> try cases h₀ <;>
  try simp [subty, lub?] at h₁
  case instance_of_bool b bty =>
    exists b

theorem bool_type_is_inhabited (bty : BoolType) :
  ∃ b, InstanceOfBoolType b bty
:= by
  simp [InstanceOfBoolType]
  cases bty
  case tt => simp only [or_true]
  case ff => simp only [or_false]
  case anyBool => simp only [or_self]

theorem entity_type_is_inhabited {env : TypeEnv} {ety : EntityType}
  (hwf_env : env.WellFormed)
  (hwf : EntityType.WellFormed env ety) :
  ∃ euid, InstanceOfEntityType euid ety env
:= by
  cases hwf
  -- Non-action entity
  case inl hwf_ets =>
    simp only [EntitySchema.contains, Option.isSome] at hwf_ets
    split at hwf_ets
    case _ entry hentry =>
      have hwf_entry := wf_env_implies_wf_entity_schema_entry hwf_env hentry
      cases entry with
      | standard entry =>
        exists (EntityUID.mk ety default)
        simp only [InstanceOfEntityType, EntityUID.WellFormed, true_and]
        apply Or.inl
        simp [
          EntitySchema.isValidEntityUID,
          hentry,
          EntitySchemaEntry.isValidEntityEID,
        ]
      | enum eids =>
        have ⟨_, hnon_empty⟩ := hwf_entry
        have ⟨eid, heid⟩ := (Set.non_empty_iff_exists eids).mp hnon_empty
        exists (EntityUID.mk ety eid)
        simp only [InstanceOfEntityType, EntityUID.WellFormed, true_and]
        apply Or.inl
        simp only [Membership.mem] at heid
        simp [
          EntitySchema.isValidEntityUID,
          hentry,
          EntitySchemaEntry.isValidEntityEID,
          Set.contains, Membership.mem, heid,
        ]
    case _ => contradiction
  -- Action entity
  case inr hwf_acts =>
    have ⟨act, hwf_act, hty_act⟩ := hwf_acts
    exists act
    simp only [InstanceOfEntityType, hty_act, true_and]
    apply Or.inr
    exact hwf_act

theorem ext_type_is_inhabited (xty : ExtType) :
  ∃ x, InstanceOfExtType x xty
:= by
  simp [InstanceOfExtType]
  cases xty
  case ipAddr  => exists (Ext.ipaddr (default : IPAddr))
  case decimal => exists (Ext.decimal (default : Ext.Decimal))
  case datetime => exists (Ext.datetime (default : Ext.Datetime))
  case duration => exists (Ext.duration (default : Ext.Datetime.Duration))

theorem instance_of_record_nil {env : TypeEnv} :
  InstanceOfType env (Value.record (Map.mk [])) (CedarType.record (Map.mk []))
:= by
  apply InstanceOfType.instance_of_record <;>
  simp [Map.contains, Map.find?]

theorem instance_of_record_cons {env : TypeEnv} {hd : Attr × Qualified CedarType} {tl : List (Attr × Qualified CedarType)} {rhd : Value} {rtl : List (Attr × Value)}
  (h₁ : InstanceOfType env rhd (Qualified.getType hd.snd))
  (h₂ : InstanceOfType env (Value.record (Map.mk rtl)) (CedarType.record (Map.mk tl))) :
  InstanceOfType env (Value.record (Map.mk ((hd.fst, rhd) :: rtl))) (CedarType.record (Map.mk (hd :: tl)))
:= by
  cases h₂ ; rename_i h₂ h₃ h₄
  apply InstanceOfType.instance_of_record
  case h₁ =>
    intro a
    specialize h₂ a
    simp [Map.contains, Map.find?, List.find?]
    simp [Map.contains, Map.find?, Map.toList] at h₂
    cases h₅ : hd.fst == a <;> simp
    exact h₂
  case h₂ =>
    intro a v qty
    specialize h₃ a v qty
    simp [Map.find?, List.find?]
    simp [Map.find?, Map.toList] at h₃
    cases h₅ : hd.fst == a <;> simp
    case false => exact h₃
    case true =>
      intro h₆ h₇
      subst h₆ h₇
      exact h₁
  case h₃ =>
    intro a qty
    specialize h₄ a qty
    simp [Map.contains, Map.find?, List.find?]
    simp [Map.contains, Map.find?, Map.toList] at h₄
    cases h₅ : hd.fst == a <;> simp
    exact h₄


theorem sizeOf_attribute_lt_sizeOf_qualified (aqty : Attr × Qualified CedarType) :
  sizeOf (Qualified.getType aqty.snd) < sizeOf aqty
:= by
  simp [Qualified.getType]
  split
  all_goals {
    rename_i aty h
    apply @Nat.lt_trans _ (sizeOf aqty.snd)
    case h₁ => simp [h, ←Nat.succ_eq_one_add]
    case a =>
      cases aqty ; simp
      omega
  }

theorem type_is_inhabited_bool {env : TypeEnv} {bty : BoolType} :
  ∃ v, InstanceOfType env v (.bool bty)
:= by
  have ⟨v, h⟩ := bool_type_is_inhabited bty
  exists v
  exact InstanceOfType.instance_of_bool _ _ h

theorem type_is_inhabited_int {env : TypeEnv} :
  ∃ v, InstanceOfType env v CedarType.int
:= by
  exists (.prim (.int default))
  exact InstanceOfType.instance_of_int

theorem type_is_inhabited_string {env : TypeEnv} :
  ∃ v, InstanceOfType env v CedarType.string
:= by
  exists (.prim (.string default))
  exact InstanceOfType.instance_of_string

theorem type_is_inhabited_entity {env : TypeEnv} {ety : EntityType} :
  env.WellFormed → CedarType.WellFormed env (.entity ety) →
  ∃ v, InstanceOfType env v (.entity ety)
:= by
  intro hwf_env hwf
  cases hwf with | entity_wf hwf_ety =>
  have ⟨euid, h₁⟩ := entity_type_is_inhabited hwf_env hwf_ety
  exists (.prim (.entityUID euid))
  exact InstanceOfType.instance_of_entity _ _ h₁

theorem type_is_inhabited_set {env : TypeEnv} {ty : CedarType} :
  ∃ v, InstanceOfType env v (.set ty)
:= by
  exists (.set Set.empty)
  apply InstanceOfType.instance_of_set
  exact (False.elim $ Set.not_mem_empty · ·)

theorem type_is_inhabited_ext {env : TypeEnv} {xty : ExtType} :
  ∃ v, InstanceOfType env v (.ext xty)
:= by
  have ⟨x, h₁⟩ := ext_type_is_inhabited xty
  exists (.ext x)
  apply InstanceOfType.instance_of_ext _ _ h₁

theorem type_is_inhabited_record {env : TypeEnv} {rty : List (Attr × Qualified CedarType) }
  (hwf : (CedarType.record (Map.mk rty)).WellFormed env)
  (ih_ty : ∀ aty ∈ rty, aty.snd.getType.WellFormed env → ∃ v, InstanceOfType env v aty.snd.getType) :
  ∃ v, InstanceOfType env v (.record (Map.mk rty))
:= by
  cases rty
  case nil =>
    exists (.record (Map.mk []))
    exact instance_of_record_nil
  case cons hd tl =>
    have ⟨hwf_hd, hwf_tl⟩ := wf_record_type_cons hwf
    simp only [List.mem_cons, forall_eq_or_imp] at ih_ty
    have ⟨rhd, h₂⟩ := ih_ty.left hwf_hd
    have ⟨vtl, h₃⟩ := type_is_inhabited_record hwf_tl ih_ty.right
    have ⟨mtl, h₄⟩ := instance_of_record_type_is_record h₃
    subst h₄ ; cases mtl ; rename_i rtl
    exists (.record (Map.mk ((hd.fst, rhd) :: rtl)))
    exact instance_of_record_cons h₂ h₃

theorem type_is_inhabited {env : TypeEnv} {ty : CedarType}
  (hwf_env : env.WellFormed)
  (hwf : ty.WellFormed env) :
  ∃ v, InstanceOfType env v ty
:= by
  match ty with
  | .bool bty =>
    exact type_is_inhabited_bool
  | .int =>
    exact type_is_inhabited_int
  | .string =>
    exact type_is_inhabited_string
  | .entity ety =>
    exact type_is_inhabited_entity hwf_env hwf
  | .set ty₁ =>
    exact type_is_inhabited_set
  | .ext xty =>
    exact type_is_inhabited_ext
  | .record (Map.mk rty) =>
    have ih : ∀ aty ∈ rty, aty.snd.getType.WellFormed env → ∃ v, InstanceOfType env v aty.snd.getType := by
      intro aty hart hwf
      have _ : sizeOf aty.snd.getType < (1 + (1 + sizeOf rty)) := by
        suffices h : sizeOf aty.snd.getType < sizeOf rty by omega
        exact Nat.lt_trans
          (sizeOf_attribute_lt_sizeOf_qualified aty)
          (List.sizeOf_lt_of_mem hart)
      exact type_is_inhabited hwf_env hwf
    exact type_is_inhabited_record hwf ih

theorem instance_of_lubBool_left {env : TypeEnv} {v : Value} {bty₁ bty₂ : BoolType} :
  InstanceOfType env v (CedarType.bool bty₁) →
  InstanceOfType env v (CedarType.bool (lubBool bty₁ bty₂))
:= by
  intro h₁ ; cases h₁
  simp [lubBool]
  split <;> rename_i b h₁ h₂
  · subst h₂
    apply InstanceOfType.instance_of_bool b bty₁ h₁
  · exact bool_is_instance_of_anyBool b

theorem instance_of_lubBool {env : TypeEnv} {v : Value} {bty₁ bty₂ : BoolType} :
  (InstanceOfType env v (CedarType.bool bty₁) ∨ InstanceOfType env v (CedarType.bool bty₂)) →
  InstanceOfType env v (CedarType.bool (lubBool bty₁ bty₂))
:= by
  intro h₁ ; cases h₁ <;> rename_i h₂
  · exact instance_of_lubBool_left h₂
  · rw [lubBool_comm]
    exact instance_of_lubBool_left h₂

theorem sizeOf_attr_type_lt_sizeOf_record_type {a : Attr} {qty : QualifiedType } {rty : List (Attr × Qualified CedarType) }
  (h₁ : CedarType.record (Map.mk rty) = ty)
  (h₂ : Map.find? (Map.mk rty) a = .some qty) :
  sizeOf qty.getType < sizeOf ty
:= by
  subst h₁
  apply @Nat.lt_trans _ (sizeOf qty)
  case h₁ =>
    simp [Qualified.getType]
    split <;> simp [←Nat.succ_eq_one_add]
  case a =>
    apply @Nat.lt_trans _ (sizeOf (Map.mk rty))
    case h₁ =>
      apply @Nat.lt_trans _ (sizeOf rty)
      case h₁ =>
        simp [Map.find?, Map.toList] at h₂
        split at h₂ <;> simp at h₂
        rename_i a' qty' h₃ ; rw [eq_comm] at h₂ ; subst h₂
        have h₄ := List.mem_of_find?_eq_some h₃
        apply @Nat.lt_trans _ (sizeOf (a', qty))
        case h₁ =>
          simp only [Prod.mk.sizeOf_spec]
          omega
        case a => exact List.sizeOf_lt_of_mem h₄
      case a => simp [←Nat.succ_eq_one_add]
    case a => simp [←Nat.succ_eq_one_add]


theorem instance_of_lub_left {env : TypeEnv} {v : Value} {ty ty₁ ty₂ : CedarType}
  (h₁ : (ty₁ ⊔ ty₂) = .some ty)
  (h₂ : InstanceOfType env v ty₁) :
  InstanceOfType env v ty
:= by
  unfold lub? at h₁
  -- Generalizing here lets us retain hypotheses of the form ty₁ = CedarType.set
  -- s₁ after the split.  We need these for the termination proof.
  generalize hty₁ : ty₁ = ty₁'
  generalize hty₂ : ty₂ = ty₂'
  simp only [hty₁] at h₂
  split at h₁
  case h_1 =>
    simp at h₁ ; subst h₁ hty₁ hty₂
    exact instance_of_lubBool_left h₂
  case h_2 _ _ sty₁ sty₂ =>
    cases h₃ : sty₁ ⊔ sty₂ <;> simp [h₃] at h₁
    rename_i sty
    subst h₁ ; simp only [← hty₁] at h₂
    cases h₂ ; rename_i h₄
    apply InstanceOfType.instance_of_set
    intro w h₅
    specialize h₄ w h₅
    apply instance_of_lub_left h₃ (by simp [h₄])
  case h_3 _ _ rty₁ rty₂ =>
    cases h₃ : lubRecordType rty₁ rty₂ <;> simp [h₃] at h₁
    rename_i rty
    have hl := lubRecordType_is_lub_of_record_types h₃
    subst h₁ ; simp [←hty₁] at h₂
    cases h₂ ; rename_i r h₄ h₅ h₆
    apply InstanceOfType.instance_of_record
    case h₁ =>
      intro a h₇
      specialize h₄ a h₇
      exact lubRecord_contains_left hl h₄
    case h₂ =>
      intro a v qty h₇ h₈
      have ⟨qty₁, qty₂, h₉, _, h₁₁⟩ := lubRecord_find_implies_find hl h₈
      specialize h₅ a v qty₁ h₇ h₉
      have h₁₂ := lubQualified_is_lub_of_getType h₁₁
      have _ : sizeOf qty₁.getType < sizeOf ty₁' :=  -- termination
        sizeOf_attr_type_lt_sizeOf_record_type hty₁ h₉
      apply instance_of_lub_left h₁₂ h₅
    case h₃ =>
      intro a qty h₇ h₈
      have ⟨qty₁, h₉, h₁₀⟩ := lubRecord_find_implies_find_left hl h₇
      apply h₆ a qty₁ h₉
      simp [h₁₀, h₈]
  case h_4 =>
    split at h₁ <;> simp at h₁
    rename_i h₃
    subst h₁ h₃ hty₁ hty₂
    exact h₂
termination_by (sizeOf ty₁, sizeOf ty₂)

theorem instance_of_lub {env : TypeEnv} {v : Value} {ty ty₁ ty₂ : CedarType}
  (h₁ : (ty₁ ⊔ ty₂) = .some ty)
  (h₂ : InstanceOfType env v ty₁ ∨ InstanceOfType env v ty₂) :
  InstanceOfType env v ty
:= by
  cases h₂ <;> rename_i h₃
  · exact instance_of_lub_left h₁ h₃
  · rw [lub_comm] at h₁
    exact instance_of_lub_left h₁ h₃

/--
TODO: move this back to Cedar/Thm/Validation/Typechecker/LitVar.lean
after we fix the proof.
-/
theorem type_of_lit_inversion {p : Prim} {c₁ c₂ : Capabilities} {tx : TypedExpr} {env : TypeEnv}
  (h₁ : (typeOf (.lit p) c₁ env) = .ok (tx, c₂)) :
  ∃ ty, tx = .lit p ty
:= by
  simp only [typeOf, typeOfLit, ok, err, Function.comp_apply] at h₁
  (split at h₁ <;> try split at h₁) <;> first
  | simp only [reduceCtorEq] at h₁
  | injections h₁ h₁ ; simp [←h₁]

/--
Obtains the fact of well-formed environment from `InstanceOfWellFormedEnvironment`.
-/
theorem InstanceOfWellFormedEnvironment.wf_env
  {env : TypeEnv} {request : Request} {entities : Entities}
  (h : InstanceOfWellFormedEnvironment request entities env):
  env.WellFormed
:= by
  have ⟨h, _, _,⟩ := h
  exact h

theorem InstanceOfWellFormedEnvironment.instance_of_schema_entry
  {env : TypeEnv} {request : Request} {entities : Entities}
  {uid : EntityUID} {data : EntityData}
  (h : InstanceOfWellFormedEnvironment request entities env)
  (hentry : entities.find? uid = some data) :
  InstanceOfSchemaEntry uid data env
:= by
  have ⟨_, _, hsch⟩ := h
  exact hsch.1 uid data hentry

theorem InstanceOfWellFormedEnvironment.instance_of_schema
  {env : TypeEnv} {request : Request} {entities : Entities}
  (h : InstanceOfWellFormedEnvironment request entities env) :
  InstanceOfSchema entities env
:= by
  have ⟨_, _, hsch⟩ := h
  exact hsch

theorem InstanceOfWellFormedEnvironment.wf_action_data
  {env : TypeEnv} {request : Request} {entities : Entities}
  {uid : EntityUID} {entry : ActionSchemaEntry}
  (h : InstanceOfWellFormedEnvironment request entities env)
  (hacts : Map.find? env.acts uid = some entry) :
  ∃ data,
    Map.find? entities uid = some data ∧
    data.ancestors = entry.ancestors
:= by
  have ⟨hwf, _, hsch⟩ := h
  have ⟨data, hdata⟩ := hsch.2 uid entry hacts
  exists data
  simp only [hdata, true_and]
  cases hsch.1 uid data hdata with
  | inl hets =>
    have ⟨_, hets, _⟩ := hets
    apply False.elim
    apply wf_env_disjoint_ets_acts hwf
    all_goals assumption
  | inr hacts2 =>
    have ⟨_, _, ⟨entry, hacts2, hanc⟩⟩ := hacts2
    simp only [hacts2, Option.some.injEq] at hacts
    simp [hacts, hanc]

end Cedar.Thm
