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

/-!
This file contains the definition of well-formedness of `TypeEnv`
and related definitions.
--/

namespace Cedar.Validation

open Cedar.Data
open Cedar.Validation
open Cedar.Spec

----- Well-formedness of environment -----

def ActionSchema.IsActionEntityType (acts : ActionSchema) (ety : EntityType) : Prop :=
  ∃ uid, acts.contains uid ∧ uid.ty = ety

/--
Either a non-action entity type in `env.ets`,
or an action entity type in `env.acts`.
-/
def EntityType.WellFormed (env : TypeEnv) (ety : EntityType) : Prop :=
  env.ets.contains ety ∨ env.acts.IsActionEntityType ety

mutual
inductive QualifiedType.WellFormed (env : TypeEnv) : Qualified CedarType → Prop where
  | optional_wf {ty : CedarType}
    (h : CedarType.WellFormed env ty) :
    QualifiedType.WellFormed env (.optional ty)
  | required_wf {ty : CedarType}
    (h : CedarType.WellFormed env ty) :
    QualifiedType.WellFormed env (.required ty)

/--
Defines when a `CedarType` is well-formed in an `TypeEnv`.
-/
inductive CedarType.WellFormed (env : TypeEnv) : CedarType → Prop where
  | bool_wf {bty : BoolType} : CedarType.WellFormed env (.bool bty)
  | int_wf : CedarType.WellFormed env .int
  | string_wf : CedarType.WellFormed env .string
  | entity_wf {ety : EntityType}
    (h : EntityType.WellFormed env ety) :
    CedarType.WellFormed env (.entity ety)
  | set_wf {ty : CedarType}
    (h : CedarType.WellFormed env ty) :
    CedarType.WellFormed env (.set ty)
  | record_wf {rty : RecordType}
    -- Well-formed as a `Map`
    (h₁ : rty.WellFormed)
    -- Each attribute type is well-formed
    (h₂ : ∀ attr qty, rty.find? attr = some qty → QualifiedType.WellFormed env qty) :
    CedarType.WellFormed env (.record rty)
  | ext_wf {xty : ExtType} : CedarType.WellFormed env (.ext xty)
end

mutual
inductive QualifiedType.IsLifted : Qualified CedarType → Prop where
  | optional_lifted {ty : CedarType}
    (h : CedarType.IsLifted ty) :
    QualifiedType.IsLifted (.optional ty)
  | required_lifted {ty : CedarType}
    (h : CedarType.IsLifted ty) :
    QualifiedType.IsLifted (.required ty)

/--
Defines when a `CedarType` does not have any singleton Bool types.
-/
inductive CedarType.IsLifted : CedarType → Prop where
  | bool_lifted : CedarType.IsLifted (.bool .anyBool)
  | int_lifted : CedarType.IsLifted .int
  | string_lifted : CedarType.IsLifted .string
  | entity_lifted {ety : EntityType} : CedarType.IsLifted (.entity ety)
  | set_lifted {ty : CedarType}
    (h : CedarType.IsLifted ty) :
    CedarType.IsLifted (.set ty)
  | record_lifted {rty : RecordType}
    (h₂ : ∀ attr qty, (attr, qty) ∈ rty.toList → QualifiedType.IsLifted qty) :
    CedarType.IsLifted (.record rty)
  | ext_lifted {xty : ExtType} : CedarType.IsLifted (.ext xty)
end

def StandardSchemaEntry.WellFormed (env : TypeEnv) (entry : StandardSchemaEntry) : Prop :=
  -- Well-formed as `Map`/`Set`s
  entry.ancestors.WellFormed ∧
  -- Each ancestor must be a declared, non-action entity type
  (∀ anc ∈ entry.ancestors,
    ∃ entry, env.ets.find? anc = some entry) ∧
  -- The attribute types are well-formed
  (CedarType.record entry.attrs).WellFormed env ∧
  (CedarType.record entry.attrs).IsLifted ∧
  -- The tag type is well-formed
  (∀ ty, entry.tags = .some ty →
    CedarType.WellFormed env ty ∧ ty.IsLifted)

def EntitySchemaEntry.WellFormed (env : TypeEnv) (entry : EntitySchemaEntry) : Prop :=
  match entry with
  | standard entry => entry.WellFormed env
  | enum es => es.WellFormed ∧ ¬es.isEmpty

def EntitySchema.WellFormed (env : TypeEnv) (ets : EntitySchema) : Prop :=
  Map.WellFormed ets ∧
  ∀ ety entry, ets.find? ety = some entry → entry.WellFormed env

def EntityUID.WellFormed (env : TypeEnv) (uid : EntityUID) : Prop :=
  env.ets.isValidEntityUID uid ∨ env.acts.contains uid

def ActionSchemaEntry.WellFormed (env : TypeEnv) (entry : ActionSchemaEntry) : Prop :=
  -- Well-formed as `Map`/`Set`s
  entry.appliesToPrincipal.WellFormed ∧
  entry.appliesToResource.WellFormed ∧
  entry.ancestors.WellFormed ∧
  -- Each principal/resource entity type is well-formed
  (∀ ety, entry.appliesToPrincipal.contains ety → EntityType.WellFormed env ety) ∧
  (∀ ety, entry.appliesToResource.contains ety → EntityType.WellFormed env ety) ∧
  -- Ancestors of each action entity must also be an action entity
  (∀ uid ∈ entry.ancestors, env.acts.contains uid) ∧
  -- Context is a well-formed `RecordType`
  (CedarType.record entry.context).WellFormed env ∧
  (CedarType.record entry.context).IsLifted

def ActionSchema.AcyclicActionHierarchy (acts : ActionSchema) : Prop :=
  ∀ uid entry, acts.find? uid = .some entry → uid ∉ entry.ancestors

def ActionSchema.TransitiveActionHierarchy (acts : ActionSchema) : Prop :=
  ∀ uid₁ entry₁ uid₂ entry₂,
    acts.find? uid₁ = .some entry₁ →
    acts.find? uid₂ = .some entry₂ →
    uid₂ ∈ entry₁.ancestors →
    entry₂.ancestors ⊆ entry₁.ancestors

def ActionSchema.WellFormed (env : TypeEnv) (acts : ActionSchema) : Prop :=
  Map.WellFormed acts ∧
  (∀ uid entry, acts.find? uid = some entry → entry.WellFormed env) ∧
  (∀ uid, acts.contains uid → ¬env.ets.contains uid.ty) ∧
  acts.AcyclicActionHierarchy ∧
  acts.TransitiveActionHierarchy

def RequestType.WellFormed (env : TypeEnv) (reqty : RequestType) : Prop :=
  ∃ entry, env.acts.find? reqty.action = some entry ∧
    -- Enforce that principal/resource/context are valid for the action
    reqty.principal ∈ entry.appliesToPrincipal ∧
    reqty.resource ∈ entry.appliesToResource ∧
    reqty.context = entry.context
  -- Other properties, such as the well-formedness of principal/resource/context
  -- follows from the above and the well-formedness of `env.ets` and `env.acts`.

def TypeEnv.WellFormed (env : TypeEnv) : Prop :=
  env.ets.WellFormed env ∧
  env.acts.WellFormed env ∧
  env.reqty.WellFormed env

----- Some lemmas -----

theorem qty_wf_implies_type_of_wf {env : TypeEnv} {qty : Qualified CedarType}
  (h : QualifiedType.WellFormed env qty) :
  CedarType.WellFormed env qty.getType
:= by
  cases h with
  | optional_wf hwf => simp [Qualified.getType, hwf]
  | required_wf hwf => simp [Qualified.getType, hwf]

theorem wf_record_type_cons {env : TypeEnv}
  {hd : (Attr × Qualified CedarType)}
  {tl : List (Attr × Qualified CedarType)}
  (hwf : CedarType.WellFormed env (.record (Map.mk (hd :: tl)))) :
  CedarType.WellFormed env hd.snd.getType ∧
  CedarType.WellFormed env (.record (Map.mk tl))
:= by
  cases hwf
  rename_i hwf_map hwf_tys
  simp only [Map.WellFormed] at hwf_map
  constructor
  · have := hwf_tys hd.fst hd.snd
    simp only [Map.find?, Map.toList_mk_id, BEq.rfl, List.find?_cons_of_pos, forall_const] at this
    cases e : hd.snd
    all_goals
      simp only [e] at *
      cases this
      simp only [Qualified.getType]
      assumption
  · constructor
    · simp only [Map.WellFormed]
      apply Eq.symm
      apply Map.make_eq_mk.mp
      have := Map.make_eq_mk.mpr (Eq.symm hwf_map)
      cases this with
      | cons_nil => constructor
      | cons_cons =>
        simp only [Map.toList, Map.toList]
        assumption
    · intros attr qty hfound
      have hfound := Map.find?_mem_toList hfound
      simp only [Map.toList_mk_id] at hfound
      have : (Map.mk (hd :: tl)).find? attr = some qty := by
        apply (Map.in_list_iff_find?_some ?_).mp
        · simp [hfound]
        · simp only [Map.WellFormed]
          exact hwf_map
      exact hwf_tys attr qty this

theorem wf_record_implies_wf_attr {env : TypeEnv} {rty : RecordType} {attr : Attr} {qty : QualifiedType}
  (hwf : CedarType.WellFormed env (.record rty))
  (hqty : rty.find? attr = some qty) :
  QualifiedType.WellFormed env qty
:= by
  cases hwf with
  | record_wf _ hattr =>
    exact hattr attr qty hqty

/-- A type stays well-formed in an environment that has every entity type of the original. -/
theorem CedarType.WellFormed.mono {env₁ env₂ : TypeEnv}
  (hety : ∀ ety, EntityType.WellFormed env₁ ety → EntityType.WellFormed env₂ ety)
  {ty : CedarType} (h : CedarType.WellFormed env₁ ty) :
  CedarType.WellFormed env₂ ty
:= by
  cases h with
  | bool_wf => exact .bool_wf
  | int_wf => exact .int_wf
  | string_wf => exact .string_wf
  | entity_wf h => exact .entity_wf (hety _ h)
  | set_wf h => exact .set_wf (CedarType.WellFormed.mono hety h)
  | ext_wf => exact .ext_wf
  | @record_wf rty hmap hattrs =>
    refine .record_wf hmap fun attr qty hfind => ?_
    have hmem : (attr, qty) ∈ rty.1 := Map.find?_mem_toList hfind
    have hlt := Map.sizeOf_lt_of_value hmem
    cases hqty : qty with
    | optional ty =>
      have := hattrs attr qty hfind
      rw [hqty] at this
      cases this with
      | optional_wf h =>
        have : sizeOf ty < sizeOf qty := by simp [hqty]
        exact .optional_wf (CedarType.WellFormed.mono hety h)
    | required ty =>
      have := hattrs attr qty hfind
      rw [hqty] at this
      cases this with
      | required_wf h =>
        have : sizeOf ty < sizeOf qty := by simp [hqty]
        exact .required_wf (CedarType.WellFormed.mono hety h)
termination_by sizeOf ty
decreasing_by
  all_goals simp_wf
  all_goals omega

/-- The empty record type is well-formed. -/
theorem emptyRecord_wf {env : TypeEnv} :
  (CedarType.record Map.empty).WellFormed env
:=
  .record_wf Map.wf_empty fun _ _ h => by simp at h

/-- The empty record type is lifted. -/
theorem emptyRecord_lifted : (CedarType.record Map.empty).IsLifted
:=
  .record_lifted fun _ _ h => by simp [Map.empty, Map.toList] at h

/-- A standard entity type without tags is well-formed when its ancestors and attributes are. -/
theorem standardEntry_wf {env : TypeEnv} {ancestors : Set EntityType}
  {attrs : RecordType} (hwf : ancestors.WellFormed)
  (hdeclared : ∀ a ∈ ancestors, ∃ entry, env.ets.find? a = some entry)
  (hattrs : (CedarType.record attrs).WellFormed env)
  (hlifted : (CedarType.record attrs).IsLifted) :
  EntitySchemaEntry.WellFormed env (.standard { ancestors, attrs, tags := none })
:=
  ⟨hwf, hdeclared, hattrs, hlifted, by simp⟩

theorem wf_env_implies_wf_entity_schema_entry {env : TypeEnv} {ety : EntityType} {entry : EntitySchemaEntry}
  (hwf : env.WellFormed)
  (hets : env.ets.find? ety = some entry) :
  entry.WellFormed env
:= by
  have ⟨⟨_, hwf_ets⟩, _⟩ := hwf
  exact hwf_ets ety entry hets

theorem wf_env_implies_wf_tag_type {env : TypeEnv} {ety : EntityType} {ty : CedarType}
  (hwf : env.WellFormed)
  (hety : env.ets.tags? ety = .some (.some ty)) :
  CedarType.WellFormed env ty
:= by
  simp only [EntitySchema.tags?, Option.map_eq_some_iff] at hety
  have ⟨entry, hentry, htags⟩ := hety
  have ⟨⟨_, hwf_ets⟩, _⟩ := hwf
  have hwf_entry := hwf_ets ety entry hentry
  simp only [EntitySchemaEntry.WellFormed] at hwf_entry
  split at hwf_entry
  · have ⟨_, _, _, _, hwf_tag⟩ := hwf_entry
    simp only [EntitySchemaEntry.tags?] at htags
    exact (hwf_tag ty htags).1
  · simp [EntitySchemaEntry.tags?] at htags

theorem wf_env_implies_tag_type_lifted {env : TypeEnv} {ety : EntityType} {ty : CedarType}
  (hwf : env.WellFormed)
  (hety : env.ets.tags? ety = .some (.some ty)) :
  ty.IsLifted
:= by
  simp only [EntitySchema.tags?, Option.map_eq_some_iff] at hety
  have ⟨entry, hentry, htags⟩ := hety
  have ⟨⟨_, hwf_ets⟩, _⟩ := hwf
  have hwf_entry := hwf_ets ety entry hentry
  simp only [EntitySchemaEntry.WellFormed] at hwf_entry
  split at hwf_entry
  · have ⟨_, _, _, _, hwf_tag⟩ := hwf_entry
    simp only [EntitySchemaEntry.tags?] at htags
    exact (hwf_tag ty htags).2
  · simp [EntitySchemaEntry.tags?] at htags

theorem wf_env_implies_wf_attrs {env : TypeEnv} {ety : EntityType} {attrs : RecordType}
  (hwf : env.WellFormed)
  (hattrs : env.ets.attrs? ety = .some attrs) :
  CedarType.WellFormed env (.record attrs)
:= by
  simp only [EntitySchema.attrs?, Option.map_eq_some_iff] at hattrs
  have ⟨entry, hentry, hattrs⟩ := hattrs
  have ⟨⟨_, hwf_ets⟩, _⟩ := hwf
  have hwf_entry := hwf_ets ety entry hentry
  simp only [EntitySchemaEntry.WellFormed] at hwf_entry
  split at hwf_entry
  · have ⟨_, _, hwf_attrs, _⟩ := hwf_entry
    simp only [← hattrs]
    exact hwf_attrs
  · simp only [EntitySchemaEntry.attrs] at hattrs
    simp only [← hattrs, Map.empty]
    constructor
    . simp [Map.WellFormed, Map.make, List.canonicalize]
    · simp [Map.find?]

theorem wf_env_implies_attrs_lifted {env : TypeEnv} {ety : EntityType} {attrs : RecordType}
  (hwf : env.WellFormed)
  (hattrs : env.ets.attrs? ety = .some attrs) :
  (CedarType.record attrs).IsLifted
:= by
  simp only [EntitySchema.attrs?, Option.map_eq_some_iff] at hattrs
  have ⟨entry, hentry, hattrs⟩ := hattrs
  have ⟨⟨_, hwf_ets⟩, _⟩ := hwf
  have hwf_entry := hwf_ets ety entry hentry
  simp only [EntitySchemaEntry.WellFormed] at hwf_entry
  split at hwf_entry
  · have ⟨_, _, _, hlift, _⟩ := hwf_entry
    simp only [← hattrs]
    exact hlift
  · simp only [EntitySchemaEntry.attrs] at hattrs
    simp only [← hattrs, Map.empty]
    constructor
    simp

theorem wf_env_implies_action_wf {env : TypeEnv}
  (hwf : env.WellFormed) :
  EntityUID.WellFormed env env.reqty.action
:= by
  have ⟨_, _, hwf_req⟩ := hwf
  have ⟨_, hact, _⟩ := hwf_req
  apply Or.inr
  simp [ActionSchema.contains, hact]

theorem wf_env_disjoint_ets_acts
  {env : TypeEnv} {uid : EntityUID}
  {ets_entry : EntitySchemaEntry}
  {acts_entry : ActionSchemaEntry}
  (hwf : env.WellFormed)
  (hets : env.ets.find? uid.ty = some ets_entry)
  (hacts : env.acts.find? uid = some acts_entry) :
  False
:= by
  have ⟨_, ⟨_, _, hdisj, _⟩, _⟩ := hwf
  have := hdisj uid
  apply this
  · simp [ActionSchema.contains, hacts]
  · simp [EntitySchema.contains, hets]

/--
More well-formedness properties of `env.reqty`.
-/
theorem wf_env_implies_wf_request
  {env : TypeEnv}
  (hwf : env.WellFormed) :
  EntityType.WellFormed env env.reqty.principal ∧
  env.acts.contains env.reqty.action ∧
  EntityType.WellFormed env env.reqty.resource ∧
  (CedarType.record env.reqty.context).WellFormed env
:= by
  have ⟨_, hwf_acts, ⟨entry, hwf_act, hwf_princ, hwf_res, hwf_ctx⟩⟩ := hwf
  have ⟨_, hwf_acts, _⟩ := hwf_acts
  have hwf_act_entry := hwf_acts env.reqty.action entry hwf_act
  have ⟨_, _, _, hwf_app_to_princ, hwf_app_to_res, _, hwf_ctx_ty⟩ := hwf_act_entry
  and_intros
  · apply hwf_app_to_princ
    simp only [Membership.mem] at hwf_princ
    simp [Set.contains, hwf_princ, Membership.mem]
  · simp [ActionSchema.contains, hwf_act]
  · apply hwf_app_to_res
    simp only [Membership.mem] at hwf_res
    simp [Set.contains, hwf_res, Membership.mem]
  · simp [hwf_ctx, hwf_ctx_ty]

/--
More well-formedness properties of `env.reqty`.
-/
theorem wf_env_implies_ctx_lifted
  {env : TypeEnv}
  (hwf : env.WellFormed) :
  (CedarType.record env.reqty.context).IsLifted
:= by
  have ⟨_, hwf_acts, ⟨entry, hwf_act, _, _, hwf_ctx⟩⟩ := hwf
  have ⟨_, hwf_acts, _⟩ := hwf_acts
  have hwf_act_entry := hwf_acts env.reqty.action entry hwf_act
  have ⟨_, _, _, _, _, _, hwf_ctx_ty⟩ := hwf_act_entry
  simp [hwf_ctx, hwf_ctx_ty]

theorem wf_env_implies_wf_acts_map
  {env : TypeEnv}
  (hwf : env.WellFormed) :
  Map.WellFormed env.acts
:= by
  have ⟨_, hwf_acts, _⟩ := hwf
  exact hwf_acts.1

theorem wf_env_implies_wf_ets_map
  {env : TypeEnv}
  (hwf : env.WellFormed) :
  Map.WellFormed env.ets
:= by
  have ⟨hwf_ets, _, _⟩ := hwf
  exact hwf_ets.1

theorem wf_env_implies_wf_entity_entry
  {env : TypeEnv} {ety : EntityType} {entry : EntitySchemaEntry}
  (hwf : env.WellFormed)
  (hfind : env.ets.find? ety = some entry) :
  entry.WellFormed env
:= by
  have ⟨hwf_ets, _⟩ := hwf
  exact hwf_ets.2 ety entry hfind

theorem wf_env_implies_wf_action_entity_entry
  {env : TypeEnv} {uid : EntityUID} {entry : ActionSchemaEntry}
  (hwf : env.WellFormed)
  (hfind : env.acts.find? uid = some entry) :
  entry.WellFormed env
:= by
  have ⟨_, hwf_acts, _⟩ := hwf
  exact hwf_acts.2.1 uid entry hfind

/-- Ancestor of an action entity should also be an action entity -/
theorem wf_env_implies_wf_action_entity_ancestor
  {env : TypeEnv} {uid : EntityUID} {anc : EntityUID}
  {entry : ActionSchemaEntry}
  (hwf : env.WellFormed)
  (hfind : env.acts.find? uid = some entry)
  (hanc : anc ∈ entry.ancestors) :
  ∃ anc_entry,
    env.acts.find? anc = some anc_entry ∧
    anc_entry.WellFormed env
:= by
  have ⟨_, _, _, _, _, hwf_anc, _⟩ := wf_env_implies_wf_action_entity_entry hwf hfind
  have := hwf_anc anc hanc
  simp only [ActionSchema.contains, Option.isSome] at this
  split at this
  · rename_i h
    simp only [h, Option.some.injEq, exists_eq_left']
    exact wf_env_implies_wf_action_entity_entry hwf h
  contradiction

theorem wf_env_implies_wf_ancestor
  {env : TypeEnv} {entry : EntitySchemaEntry}
  {ety : EntityType} {anc : EntityType}
  (hwf : env.WellFormed)
  (hfind : env.ets.find? ety = some entry)
  (hanc : anc ∈ entry.ancestors) :
  EntityType.WellFormed env anc
:= by
  have ⟨hwf_ets, _⟩ := hwf
  have hwf_entry := hwf_ets.2 ety entry hfind
  cases entry with
  | standard entry =>
    simp only [EntitySchemaEntry.WellFormed] at hwf_entry
    have := hwf_entry.2.1
    have ⟨_, hanc_entry⟩ := this anc hanc
    apply Or.inl
    simp only [EntitySchema.contains, hanc_entry, Option.isSome]
  | enum es =>
    simp [
      EntitySchemaEntry.ancestors, Membership.mem,
      Set.elts, Set.empty,
    ] at hanc
    contradiction

theorem wf_env_implies_wf_ancestor_set
  {env : TypeEnv} {entry : EntitySchemaEntry}
  {ety : EntityType}
  (hwf : env.WellFormed)
  (hfind : env.ets.find? ety = some entry) :
  Set.WellFormed entry.ancestors
:= by
  have ⟨hwf_ets, _⟩ := hwf
  have hwf_entry := hwf_ets.2 ety entry hfind
  cases entry with
  | standard entry =>
    simp only [EntitySchemaEntry.ancestors]
    simp only [EntitySchemaEntry.WellFormed] at hwf_entry
    have ⟨h, _⟩ := hwf_entry
    exact h
  | enum es =>
    simp only [EntitySchemaEntry.ancestors, Set.empty_wf]

theorem wf_env_implies_wf_action_ancestor_set
  {env : TypeEnv} {entry : ActionSchemaEntry}
  {uid : EntityUID}
  (hwf : env.WellFormed)
  (hfind : env.acts.find? uid = some entry) :
  Set.WellFormed entry.ancestors
:= by
  have ⟨_, hwf_acts⟩ := hwf
  replace ⟨⟨_, hwf_acts, _⟩, _⟩ := hwf_acts
  have ⟨_, _, h, _⟩ := hwf_acts uid entry hfind
  exact h

theorem wf_env_implies_acyclic_action_hierarchy
  {env : TypeEnv}
  (hwf : env.WellFormed) :
  env.acts.AcyclicActionHierarchy
:= by
  have ⟨_, hwf_acts, _⟩ := hwf
  have ⟨_, _, _, h, _⟩ := hwf_acts
  exact h

theorem wf_env_implies_transitive_action_hierarchy
  {env : TypeEnv}
  (hwf : env.WellFormed) :
  env.acts.TransitiveActionHierarchy
:= by
  have ⟨_, hwf_acts, _⟩ := hwf
  have ⟨_, _, _, _, h⟩ := hwf_acts
  exact h

theorem wf_env_implies_ancestors_of_standard_ety_exist
  {env : TypeEnv} {ety : EntityType} {entry : StandardSchemaEntry}
  (hwf : env.WellFormed)
  (hfind : env.ets.find? ety = some (.standard entry)) :
  ∀ anc ∈ entry.ancestors,
    ∃ entry, env.ets.find? anc = some entry
:= by
  have ⟨hwf_ets, _⟩ := hwf
  have hwf_entry := hwf_ets.2 ety (.standard entry) hfind
  simp only [EntitySchemaEntry.WellFormed] at hwf_entry
  have ⟨_, hancs, _⟩ := hwf_entry
  exact hancs

theorem wf_env_implies_ancestors_of_action_is_action
  {env : TypeEnv} {uid : EntityUID} {entry : ActionSchemaEntry}
  (hwf : env.WellFormed)
  (hfind : env.acts.find? uid = some entry) :
  ∀ uid ∈ entry.ancestors, env.acts.contains uid
:= by
  have ⟨_, hwf_acts, _⟩ := hwf
  have hwf_entry := hwf_acts.2.1 uid entry hfind
  simp only [ActionSchemaEntry.WellFormed] at hwf_entry
  have ⟨_, _, _, _, _, hancs, _⟩ := hwf_entry
  exact hancs

/-- Whether an environment's maps are well-formed does not depend on its request type. -/
theorem TypeEnv.maps_wf_of_eq {env₁ env₂ : TypeEnv}
  (hets : env₁.ets = env₂.ets) (hacts : env₁.acts = env₂.acts)
  (h : env₁.ets.WellFormed env₁ ∧ env₁.acts.WellFormed env₁) :
  env₂.ets.WellFormed env₂ ∧ env₂.acts.WellFormed env₂
:= by
  obtain ⟨ets, acts, reqty₁⟩ := env₁
  obtain ⟨_, _, reqty₂⟩ := env₂
  dsimp only at hets hacts
  subst hets hacts
  -- Entity types are well-formed in both environments by definition.
  have hty : ∀ {ty}, CedarType.WellFormed ⟨ets, acts, reqty₁⟩ ty →
      CedarType.WellFormed ⟨ets, acts, reqty₂⟩ ty :=
    CedarType.WellFormed.mono (env₁ := ⟨ets, acts, reqty₁⟩)
      (env₂ := ⟨ets, acts, reqty₂⟩) fun _ h => h
  obtain ⟨⟨hetsMap, hentities⟩, hactsMap, hactions, hdisjoint, hacyclic, htransitive⟩ := h
  refine ⟨⟨hetsMap, fun ety entry hfind => ?_⟩,
    hactsMap, fun uid entry hfind => ?_, hdisjoint, hacyclic, htransitive⟩
  · have hwf := hentities ety entry hfind
    cases entry with
    | enum => exact hwf
    | standard =>
      obtain ⟨hancestors, hstandard, hattrs, hlifted, htags⟩ := hwf
      exact ⟨hancestors, hstandard, hty hattrs, hlifted,
        fun ty h => ⟨hty (htags ty h).1, (htags ty h).2⟩⟩
  · obtain ⟨h₁, h₂, h₃, hprincipals, hresources, hancestors, hcontext, hlifted⟩ :=
      hactions uid entry hfind
    exact ⟨h₁, h₂, h₃, hprincipals, hresources, hancestors, hty hcontext, hlifted⟩

end Cedar.Validation
