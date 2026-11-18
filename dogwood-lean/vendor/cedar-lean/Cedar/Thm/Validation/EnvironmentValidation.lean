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

import Cedar.Validation.EnvironmentValidator
import Cedar.Thm.Validation.Validator

/-!
This file proves that various `*.validateWellFormed` functions
correctly implement their spec versions.
-/

namespace Cedar.Thm

open Cedar.Data
open Cedar.Spec
open Cedar.Validation

theorem entity_type_validate_well_formed_is_sound
  {env : TypeEnv} {ety : EntityType}
  (hok : EntityType.validateWellFormed env ety = .ok ()) :
  EntityType.WellFormed env ety
:= by
  simp only [
    EntityType.validateWellFormed,
    List.any_eq_true, beq_iff_eq, Prod.exists,
    exists_and_right, ite_eq_left_iff, Bool.not_eq_true,
    not_exists, not_and, forall_exists_index,
    reduceCtorEq, imp_false, Classical.not_forall,
    Decidable.not_not,
  ] at hok
  simp only [EntityType.WellFormed, ActionSchema.IsActionEntityType]
  cases h : env.ets.contains ety
  · have ⟨uid, entry, hacts, heq⟩ := hok h
    simp only [Bool.false_eq_true, false_or]
    exists uid
    simp only [heq, and_true]
    have : (List.find? (fun x => x.fst == uid) (Map.toList env.acts)).isSome
    := by
      apply List.find?_isSome.mpr
      exists (uid, entry)
      simp [hacts]
    cases h : List.find? (fun x => x.fst == uid) (Map.toList env.acts)
    · simp [h] at this
    · simp [ActionSchema.contains, Map.find?, h]
  · simp only [true_or]

mutual

theorem validate_attrs_well_formed_is_sound
  {env : TypeEnv} {rty} {attr : Attr} {qty : QualifiedType}
  (hwf : (Map.mk rty).WellFormed)
  (hok : validateAttrsWellFormed env rty = .ok ())
  (hfind : (Map.mk rty).find? attr = some qty) :
  QualifiedType.WellFormed env qty
:= by
  cases rty with
  | nil => simp [Map.find?] at hfind
  | cons hd tl =>
    unfold validateAttrsWellFormed at hok
    cases h : hd.snd with
    | optional attr_ty =>
      simp only [h, bind, Except.bind] at hok
      split at hok
      · contradiction
      · rename_i hwf_hd
        simp only [QualifiedType.validateWellFormed] at hwf_hd
        have := (Map.in_list_iff_find?_some hwf).mpr hfind
        simp only [Map.toList_mk_id, List.mem_cons] at this
        cases this with
        | inl hhd =>
          have e : qty = hd.snd := by simp [← hhd]
          simp only [e, h]
          constructor
          exact type_validate_well_formed_is_sound hwf_hd
        | inr htl =>
          have hwf_tl : (Map.mk tl).WellFormed := Map.wf_implies_tail_wf hwf
          have := (Map.in_list_iff_find?_some hwf_tl).mp htl
          exact validate_attrs_well_formed_is_sound hwf_tl hok this
    | required attr_ty =>
      simp only [h, bind, Except.bind] at hok
      split at hok
      · contradiction
      · rename_i hwf_hd
        simp only [QualifiedType.validateWellFormed] at hwf_hd
        have := (Map.in_list_iff_find?_some hwf).mpr hfind
        simp only [Map.toList_mk_id, List.mem_cons] at this
        cases this with
        | inl hhd =>
          have e : qty = hd.snd := by simp [← hhd]
          simp only [e, h]
          constructor
          exact type_validate_well_formed_is_sound hwf_hd
        | inr htl =>
          have hwf_tl : (Map.mk tl).WellFormed
          := Map.wf_implies_tail_wf hwf
          have := (Map.in_list_iff_find?_some hwf_tl).mp htl
          exact validate_attrs_well_formed_is_sound hwf_tl hok this
termination_by sizeOf rty
decreasing_by
  all_goals simp_wf
  all_goals subst_vars
  all_goals simp only [List.cons.sizeOf_spec]
  · cases hd
    simp_all [Prod.mk.sizeOf_spec]
    omega
  · omega
  · cases hd
    simp_all [Prod.mk.sizeOf_spec]
    omega
  · omega

theorem type_validate_well_formed_is_sound
  {env : TypeEnv} {ty : CedarType}
  (hok : ty.validateWellFormed env = .ok ()) :
  CedarType.WellFormed env ty
:= by
  cases ty with
  | bool _ | int | string | ext _ => constructor
  | entity ety =>
    simp only [CedarType.validateWellFormed] at hok
    constructor
    exact entity_type_validate_well_formed_is_sound hok
  | set ty =>
    simp only [CedarType.validateWellFormed] at hok
    constructor
    exact type_validate_well_formed_is_sound hok
  | record rty =>
    simp only [CedarType.validateWellFormed] at hok
    change (do
    if rty.wellFormed then Except.ok ()
    else .error (Cedar.Validation.EnvironmentValidationError.typeError s!"record type is not a well-formed map")
    validateAttrsWellFormed env rty.toList) = _ at hok
    simp only [Except.bind_ok, Except.bind_err] at hok
    split at hok
    case _ =>
      rename_i hwf_rty
      replace hwf_rty := Map.wellFormed_correct.mp hwf_rty
      constructor
      · exact hwf_rty
      · intros _ _ hfind
        exact validate_attrs_well_formed_is_sound hwf_rty hok hfind
    case _ => simp only [reduceCtorEq] at hok

termination_by sizeOf ty
decreasing_by
  · rename_i h
    simp only [h, CedarType.set.sizeOf_spec, Nat.lt_add_left_iff_pos, Nat.lt_add_one]
  · rename_i h _ _ _ _
    simp only [h, CedarType.record.sizeOf_spec]
    simp only [sizeOf, Map._sizeOf_1]
    generalize List._sizeOf_1 rty.1 = i
    omega
end

theorem type_validate_lifted_is_sound
  {ty : CedarType}
  (hok : ty.validateLifted = .ok ()) :
  CedarType.IsLifted ty
:= by
  cases ty with
  | bool bty =>
    cases bty
    · constructor
    · simp [CedarType.validateLifted] at hok
    · simp [CedarType.validateLifted] at hok
  | int | string | entity _ => constructor
  | set ty' =>
    simp only [CedarType.validateLifted] at hok
    constructor
    exact type_validate_lifted_is_sound hok
  | record rty =>
    simp only [CedarType.validateLifted] at hok
    constructor
    intros attr qty hmem
    have := List.forM_ok_implies_all_ok _ _ hok ⟨(attr, qty), hmem⟩
    specialize this (List.mem_attach rty.toList ⟨(attr, qty), hmem⟩)
    simp only at this
    cases qty with
    | optional ty' =>
      simp only at this
      constructor
      exact type_validate_lifted_is_sound this
    | required ty' =>
      simp only at this
      constructor
      exact type_validate_lifted_is_sound this
  | ext _ => constructor
termination_by sizeOf ty
decreasing_by
  · rename ty = ty'.set => h
    simp [h]
  all_goals
    rename ty = CedarType.record rty => h
    simp only [h, CedarType.record.sizeOf_spec]
    rename (attr, qty) ∈ rty.toList => hmem
    have := List.sizeOf_lt_of_mem hmem
    cases rty
    simp at this ⊢
    omega

theorem standard_schema_entry_validate_well_formed_is_sound
  {env : TypeEnv} {entry : StandardSchemaEntry}
  (hok : entry.validateWellFormed env = .ok ()) :
  StandardSchemaEntry.WellFormed env entry
:= by
  simp only [StandardSchemaEntry.WellFormed]
  simp only [StandardSchemaEntry.validateWellFormed] at hok
  -- Ancestors set is well-formed
  cases hwf_anc : entry.ancestors.wellFormed
  all_goals simp [hwf_anc] at hok
  replace hwf_anc := Set.wellFormed_correct.mp hwf_anc
  simp only [hwf_anc, true_and]
  -- Every ancestor is a valid entity type
  simp only [bind, Except.bind] at hok
  split at hok
  contradiction
  rename_i hwf_anc_tys
  have := List.forM_ok_implies_all_ok' hwf_anc_tys
  constructor
  intros anc hmem_anc
  specialize this anc hmem_anc
  split at this
  · rename_i entry hfind
    exists entry
  · contradiction
  -- Attribute types are well-formed
  split at hok
  contradiction
  rename_i hwf_attrs
  simp only [type_validate_well_formed_is_sound hwf_attrs, true_and]
  split at hok
  contradiction
  rename_i hlift_attrs
  simp only [type_validate_lifted_is_sound hlift_attrs, true_and]
  -- Tag type is well-formed
  split at hok
  · rename_i tag_ty htags
    split at hok
    contradiction
    rename_i hwf_tags
    simp [
      type_validate_well_formed_is_sound hwf_tags, htags,
      type_validate_lifted_is_sound hok,
    ]
  · rename_i htags
    simp [htags]

theorem entity_schema_entry_validate_well_formed_is_sound
  {env : TypeEnv} {entry : EntitySchemaEntry}
  (hok : entry.validateWellFormed env = .ok ()) :
  EntitySchemaEntry.WellFormed env entry
:= by
  simp only [EntitySchemaEntry.WellFormed]
  simp only [EntitySchemaEntry.validateWellFormed] at hok
  cases entry with
  | standard entry =>
    simp only at ⊢ hok
    exact standard_schema_entry_validate_well_formed_is_sound hok
  | enum es =>
    simp only at ⊢ hok
    cases hwf_es : es.wellFormed
    · simp [hwf_es] at hok
    simp only [
      hwf_es, ↓reduceIte,
      Except.bind_ok,
      ite_eq_right_iff,
      reduceCtorEq, imp_false,
      Bool.not_eq_true,
    ] at hok
    simp [Set.wellFormed_correct.mp hwf_es, hok]

theorem entity_schema_validate_well_formed_is_sound
  {env : TypeEnv} {ets : EntitySchema}
  (hok : ets.validateWellFormed env = .ok ()) :
  EntitySchema.WellFormed env ets
:= by
  simp only [EntitySchema.WellFormed]
  simp only [EntitySchema.validateWellFormed] at hok
  cases hwf_ets : Map.wellFormed ets
  · simp [hwf_ets] at hok
  simp only [
    hwf_ets, ↓reduceIte,
    List.forM_eq_forM, Except.bind_ok,
  ] at hok
  simp only [Map.wellFormed_correct.mp hwf_ets, true_and]
  have := List.forM_ok_implies_all_ok' hok
  intros ety entry hfind
  specialize this (ety, entry) (Map.find?_mem_toList hfind)
  exact entity_schema_entry_validate_well_formed_is_sound this

theorem action_schema_entry_validate_well_formed_is_sound
  {env : TypeEnv} {entry : ActionSchemaEntry}
  (hok : entry.validateWellFormed env = .ok ()) :
  ActionSchemaEntry.WellFormed env entry
:= by
  simp only [ActionSchemaEntry.WellFormed]
  simp only [ActionSchemaEntry.validateWellFormed] at hok
  -- Check `entry.appliesToPrincipal.WellFormed`
  cases hwf_princ : entry.appliesToPrincipal.wellFormed
  · simp [hwf_princ] at hok
  simp only [
    hwf_princ,
    ↓reduceIte, List.forM_eq_forM,
    Except.bind_ok, Except.bind_err,
  ] at hok
  simp only [Set.wellFormed_correct.mp hwf_princ, true_and]
  -- Check `entry.appliesToResource.WellFormed`
  cases hwf_res : entry.appliesToResource.wellFormed
  · simp [hwf_res] at hok
  simp only [hwf_res, ↓reduceIte] at hok
  simp only [Set.wellFormed_correct.mp hwf_res, true_and]
  -- Check `entry.ancestors.WellFormed`
  cases hwf_anc : entry.ancestors.wellFormed
  · simp [hwf_anc] at hok
  simp [hwf_anc, ↓reduceIte] at hok
  simp only [Set.wellFormed_correct.mp hwf_anc, true_and]
  -- Each principal entity type is well-formed
  simp only [bind, Except.bind] at hok
  split at hok
  contradiction
  rename_i hwf_princ_tys
  have := List.forM_ok_implies_all_ok' hwf_princ_tys
  constructor
  intros ety hmem_princ
  specialize this ety (List.contains_iff_mem.mp hmem_princ)
  exact entity_type_validate_well_formed_is_sound this
  -- Each resource entity type is well-formed
  split at hok
  contradiction
  rename_i hwf_res_tys
  have := List.forM_ok_implies_all_ok' hwf_res_tys
  constructor
  intros ety hmem_res
  specialize this ety (List.contains_iff_mem.mp hmem_res)
  exact entity_type_validate_well_formed_is_sound this
  -- Each ancestor is an action entity
  split at hok
  contradiction
  rename_i hwf_anc
  have := List.forM_ok_implies_all_ok' hwf_anc
  constructor
  intros uid hmem_anc
  specialize this uid hmem_anc
  cases hmem_anc_acts : env.acts.contains uid
  · simp [hmem_anc_acts] at this
  · rfl
  -- Check context type well-formedness
  split at hok
  contradiction
  rename_i hwf_ctx
  simp only [type_validate_well_formed_is_sound hwf_ctx, true_and]
  exact type_validate_lifted_is_sound hok

theorem action_schema_validate_acyclic_action_hierarchy_is_sound
  {acts : ActionSchema}
  (hok : acts.validateAcyclicActionHierarchy = .ok ()) :
  ActionSchema.AcyclicActionHierarchy acts
:= by
  simp only [ActionSchema.AcyclicActionHierarchy]
  simp only [ActionSchema.validateAcyclicActionHierarchy] at hok
  have := List.forM_ok_implies_all_ok' hok
  intros uid entry h
  specialize this (uid, entry) (Map.find?_mem_toList h)
  split at this
  contradiction
  rename_i hnot_find
  simp only [Bool.not_eq_true] at hnot_find
  intros hfind
  simp only [
    Set.contains, List.elem_eq_contains,
    List.contains_eq_mem,
    decide_eq_false_iff_not,
  ] at hnot_find
  contradiction

theorem action_schema_validate_transitive_action_hierarchy_is_sound
  {acts : ActionSchema}
  (hok : acts.validateTransitiveActionHierarchy = .ok ()) :
  ActionSchema.TransitiveActionHierarchy acts
:= by
  simp only [ActionSchema.TransitiveActionHierarchy]
  simp only [ActionSchema.validateTransitiveActionHierarchy] at hok
  have := List.forM_ok_implies_all_ok' hok
  intros uid₁ entry₁ uid₂ entry₂ hmem₁ hmem₂
  specialize this (uid₁, entry₁) (Map.find?_mem_toList hmem₁)
  have := List.forM_ok_implies_all_ok' this
  specialize this (uid₂, entry₂) (Map.find?_mem_toList hmem₂)
  intros hanc
  simp only [
    ite_eq_right_iff, ite_eq_left_iff,
    Bool.not_eq_true, reduceCtorEq,
    imp_false,
    Bool.not_eq_false,
  ] at this
  exact this (Set.contains_prop_bool_equiv.mpr hanc)

theorem action_schema_validate_well_formed_is_sound
  {env : TypeEnv} {acts : ActionSchema}
  (hok : acts.validateWellFormed env = .ok ()) :
  ActionSchema.WellFormed env acts
:= by
  simp only [ActionSchema.WellFormed]
  simp only [ActionSchema.validateWellFormed] at hok
  -- Check `Map.WellFormed acts`
  cases hwf_acts : Map.wellFormed acts
  · simp [hwf_acts] at hok
  simp only [
    hwf_acts, ↓reduceIte, Except.bind_err,
    Except.bind_ok, List.forM_eq_forM,
  ] at hok
  simp only [Map.wellFormed_correct.mp hwf_acts, true_and]
  -- Check that each action entity type is well-formed
  -- and disjoint from the entity schema
  simp only [bind, Except.bind] at hok
  split at hok
  contradiction
  rename_i hwf_acts
  have := List.forM_ok_implies_all_ok' hwf_acts
  constructor
  · intros uid entry hfind
    specialize this (uid, entry) (Map.find?_mem_toList hfind)
    split at this
    contradiction
    exact action_schema_entry_validate_well_formed_is_sound this
  constructor
  · intros uid hmem_acts
    simp only [ActionSchema.contains, Option.isSome] at hmem_acts
    split at hmem_acts
    · rename_i entry hfind
      specialize this (uid, entry) (Map.find?_mem_toList hfind)
      split at this
      contradiction
      rename_i hnot_ets
      exact hnot_ets
    · contradiction
  -- Check `acts.validateAcyclicActionHierarchy`
  cases hacts_acyclic : acts.validateAcyclicActionHierarchy
  · simp [hacts_acyclic] at hok
  simp only [hacts_acyclic] at hok
  simp only [
    action_schema_validate_acyclic_action_hierarchy_is_sound hacts_acyclic,
    true_and,
  ]
  -- Check `acts.validateTransitiveActionHierarchy`
  exact action_schema_validate_transitive_action_hierarchy_is_sound hok

theorem request_type_validate_well_formed_is_sound
  {env : TypeEnv} {reqty : RequestType}
  (hok : reqty.validateWellFormed env = .ok ()) :
  RequestType.WellFormed env reqty
:= by
  simp only [RequestType.WellFormed]
  simp only [RequestType.validateWellFormed] at hok
  split at hok
  rotate_left
  · contradiction
  rename_i entry hfind
  exists entry
  simp only [hfind, true_and]
  -- Check that the principal matches the action
  split at hok
  rotate_left
  · contradiction
  rename_i hprinc
  simp only [Set.contains_prop_bool_equiv.mp hprinc, true_and]
  -- Check that the resource matches the action
  split at hok
  rotate_left
  · contradiction
  rename_i hres
  simp only [Set.contains_prop_bool_equiv.mp hres, true_and]
  -- Check that the context type is correct
  split at hok
  rotate_left
  · contradiction
  rename_i hctx
  exact beq_iff_eq.mp hctx

theorem env_validate_well_formed_is_sound
  {env : TypeEnv}
  (hok : env.validateWellFormed = .ok ()) :
  TypeEnv.WellFormed env
:= by
  simp only [TypeEnv.WellFormed]
  simp only [TypeEnv.validateWellFormed] at hok
  -- Check that the entity schema is well-formed
  cases hwf_ets : env.ets.validateWellFormed env
  · simp [hwf_ets] at hok
  simp only [hwf_ets] at hok
  simp only [
    entity_schema_validate_well_formed_is_sound hwf_ets,
    true_and,
  ]
  -- Check that the action schema is well-formed
  cases hwf_acts : env.acts.validateWellFormed env
  · simp [hwf_acts] at hok
  simp only [hwf_acts] at hok
  simp only [
    action_schema_validate_well_formed_is_sound hwf_acts,
    true_and,
  ]
  -- Check that the request types are well-formed
  cases hwf_reqs : RequestType.validateWellFormed env env.reqty
  · simp [hwf_reqs] at hok
  simp only [hwf_reqs] at hok
  exact request_type_validate_well_formed_is_sound hwf_reqs

theorem environment_some_mem_environments {schema : Schema}
  {principal resource : EntityType} {action : EntityUID} {env : TypeEnv}
  (h : schema.environment? principal resource action = .some env) :
  env ∈ schema.environments
:= by
  simp only [Schema.environment?] at h
  cases h_find : schema.acts.find? action <;>
    simp only [h_find, Option.bind_none_fun, Option.bind_some_fun, reduceCtorEq] at h
  rename_i ase
  split at h <;> simp only [reduceCtorEq, Option.some.injEq] at h
  rename_i hp hr
  subst h
  simp only [Schema.environments, List.mem_map, List.mem_flatMap, TypeEnv.mk.injEq, true_and, exists_eq_right]
  exists (action, ase)
  and_intros
  · exact Map.find?_mem_toList h_find
  · show { principal, action, resource, context := ase.context : RequestType } ∈
      (ase.appliesToPrincipal.toList.product ase.appliesToResource.toList |>.map
        (λ (principal, resource) => {
          principal, action, resource,
          context := ase.context}))
    simp [Set.toList, Set.mem_elts_iff_mem_set, ← Set.contains_prop_bool_equiv, hr, hp]

/-! ### Completeness: well-formed environments pass the executable checks -/

theorem entity_type_validate_well_formed_is_complete
  {env : TypeEnv} {ety : EntityType}
  (hwf : EntityType.WellFormed env ety) :
  EntityType.validateWellFormed env ety = .ok ()
:= by
  unfold EntityType.validateWellFormed
  rcases hwf with hets | ⟨uid, hacts, rfl⟩
  · simp [hets]
  · obtain ⟨entry, hfind⟩ := Option.isSome_iff_exists.mp hacts
    split
    · rfl
    · rw [ite_eq_left
        (List.any_eq_true.mpr ⟨(uid, entry), Map.find?_mem_toList hfind, by simp⟩)]

mutual

theorem validate_attrs_well_formed_is_complete
  {env : TypeEnv} {rty : List (Attr × QualifiedType)}
  (hwf : ∀ attr qty, (attr, qty) ∈ rty → QualifiedType.WellFormed env qty) :
  validateAttrsWellFormed env rty = .ok ()
:= by
  cases rty with
  | nil => simp [validateAttrsWellFormed]
  | cons hd tl =>
    have htl : validateAttrsWellFormed env tl = .ok () :=
      validate_attrs_well_formed_is_complete fun a q hmem => hwf a q (List.mem_cons_of_mem _ hmem)
    have hhd := hwf hd.fst hd.snd List.mem_cons_self
    unfold validateAttrsWellFormed
    cases h : hd.snd with
    | optional ty =>
      rw [h] at hhd
      cases hhd with
      | optional_wf hty =>
        simp [QualifiedType.validateWellFormed, type_validate_well_formed_is_complete hty, htl]
    | required ty =>
      rw [h] at hhd
      cases hhd with
      | required_wf hty =>
        simp [QualifiedType.validateWellFormed, type_validate_well_formed_is_complete hty, htl]
termination_by sizeOf rty
decreasing_by
  all_goals simp_wf
  all_goals subst_vars
  all_goals
    cases hd
    simp_all [List.cons.sizeOf_spec, Prod.mk.sizeOf_spec]
    omega

theorem type_validate_well_formed_is_complete
  {env : TypeEnv} {ty : CedarType}
  (hwf : CedarType.WellFormed env ty) :
  ty.validateWellFormed env = .ok ()
:= by
  cases hwf with
  | bool_wf | int_wf | string_wf | ext_wf => simp [CedarType.validateWellFormed]
  | entity_wf h =>
    simp only [CedarType.validateWellFormed]
    exact entity_type_validate_well_formed_is_complete h
  | set_wf h =>
    simp only [CedarType.validateWellFormed]
    exact type_validate_well_formed_is_complete h
  | @record_wf rty hmap hattrs =>
    have hattrs' : validateAttrsWellFormed env rty.toList = .ok () :=
      validate_attrs_well_formed_is_complete fun attr qty hmem =>
        hattrs attr qty ((Map.in_list_iff_find?_some hmap).mp hmem)
    simp only [CedarType.validateWellFormed]
    simp [Map.wellFormed_correct.mpr hmap, hattrs']
termination_by sizeOf ty
decreasing_by
  all_goals simp_wf
  all_goals
    have := Map.sizeOf_lt_of_toList rty
    omega
end

theorem type_validate_lifted_is_complete
  {ty : CedarType}
  (hlifted : CedarType.IsLifted ty) :
  ty.validateLifted = .ok ()
:= by
  cases hlifted with
  | bool_lifted | int_lifted | string_lifted | entity_lifted | ext_lifted =>
    simp [CedarType.validateLifted]
  | set_lifted h =>
    simp only [CedarType.validateLifted]
    exact type_validate_lifted_is_complete h
  | @record_lifted rty h =>
    simp only [CedarType.validateLifted]
    apply List.all_ok_implies_forM_ok
    intro ⟨(attr, qty), hmem⟩ _
    have hqty := h attr qty hmem
    cases qty with
    | optional ty =>
      cases hqty with
      | optional_lifted h => exact type_validate_lifted_is_complete h
    | required ty =>
      cases hqty with
      | required_lifted h => exact type_validate_lifted_is_complete h
termination_by sizeOf ty
decreasing_by
  all_goals simp_wf
  all_goals
    have := List.sizeOf_lt_of_mem hmem
    cases rty
    simp at this ⊢
    omega

theorem standard_schema_entry_validate_well_formed_is_complete
  {env : TypeEnv} {entry : StandardSchemaEntry}
  (hwf : StandardSchemaEntry.WellFormed env entry) :
  entry.validateWellFormed env = .ok ()
:= by
  obtain ⟨hancestors, hdeclared, hattrs, hlifted, htags⟩ := hwf
  simp only [StandardSchemaEntry.validateWellFormed, Set.wellFormed_correct.mpr hancestors,
    ↓reduceIte, Except.bind_ok]
  rw [List.all_ok_implies_forM_ok _ _ ?ancestors]
  case ancestors =>
    intro ety hmem
    obtain ⟨entry', hfind⟩ := hdeclared ety ((Set.mem_elts_iff_mem_set _ _).mp hmem)
    simp [hfind]
  simp only [Except.bind_ok, type_validate_well_formed_is_complete hattrs,
    type_validate_lifted_is_complete hlifted]
  cases htag : entry.tags with
  | none => rfl
  | some ty =>
    obtain ⟨hwf, hlifted⟩ := htags ty htag
    simp [type_validate_well_formed_is_complete hwf, type_validate_lifted_is_complete hlifted]

theorem entity_schema_entry_validate_well_formed_is_complete
  {env : TypeEnv} {entry : EntitySchemaEntry}
  (hwf : EntitySchemaEntry.WellFormed env entry) :
  entry.validateWellFormed env = .ok ()
:= by
  cases entry with
  | standard entry => exact standard_schema_entry_validate_well_formed_is_complete hwf
  | enum es =>
    obtain ⟨hwf, hnonempty⟩ := hwf
    simp [EntitySchemaEntry.validateWellFormed, Set.wellFormed_correct.mpr hwf, hnonempty]

theorem entity_schema_validate_well_formed_is_complete
  {env : TypeEnv} {ets : EntitySchema}
  (hwf : EntitySchema.WellFormed env ets) :
  ets.validateWellFormed env = .ok ()
:= by
  obtain ⟨hmap, hentries⟩ := hwf
  simp only [EntitySchema.validateWellFormed, Map.wellFormed_correct.mpr hmap, ↓reduceIte,
    Except.bind_ok]
  apply List.all_ok_implies_forM_ok
  intro ⟨ety, entry⟩ hmem
  exact entity_schema_entry_validate_well_formed_is_complete
    (hentries ety entry ((Map.in_list_iff_find?_some hmap).mp hmem))

theorem action_schema_entry_validate_well_formed_is_complete
  {env : TypeEnv} {entry : ActionSchemaEntry}
  (hwf : ActionSchemaEntry.WellFormed env entry) :
  entry.validateWellFormed env = .ok ()
:= by
  obtain ⟨hprincipals, hresources, hancestors, hprincipal_tys, hresource_tys, hancestor_acts,
    hcontext, hlifted⟩ := hwf
  simp only [ActionSchemaEntry.validateWellFormed, Set.wellFormed_correct.mpr hprincipals,
    Set.wellFormed_correct.mpr hresources, Set.wellFormed_correct.mpr hancestors, ↓reduceIte,
    Except.bind_ok]
  rw [List.all_ok_implies_forM_ok _ _ ?principals, List.all_ok_implies_forM_ok _ _ ?resources,
    List.all_ok_implies_forM_ok _ _ ?ancestors]
  case principals =>
    intro ety hmem
    exact entity_type_validate_well_formed_is_complete
      (hprincipal_tys ety (List.contains_iff_mem.mpr hmem))
  case resources =>
    intro ety hmem
    exact entity_type_validate_well_formed_is_complete
      (hresource_tys ety (List.contains_iff_mem.mpr hmem))
  case ancestors =>
    intro uid hmem
    simp [hancestor_acts uid ((Set.mem_elts_iff_mem_set _ _).mp hmem)]
  simp only [Except.bind_ok, type_validate_well_formed_is_complete hcontext,
    type_validate_lifted_is_complete hlifted]

theorem action_schema_validate_acyclic_action_hierarchy_is_complete
  {acts : ActionSchema}
  (hmap : Map.WellFormed acts)
  (hacyclic : ActionSchema.AcyclicActionHierarchy acts) :
  acts.validateAcyclicActionHierarchy = .ok ()
:= by
  unfold ActionSchema.validateAcyclicActionHierarchy
  apply List.all_ok_implies_forM_ok
  intro ⟨uid, entry⟩ hmem
  have := hacyclic uid entry ((Map.in_list_iff_find?_some hmap).mp hmem)
  simp [Set.contains_prop_bool_equiv, this]

theorem action_schema_validate_transitive_action_hierarchy_is_complete
  {acts : ActionSchema}
  (hmap : Map.WellFormed acts)
  (htransitive : ActionSchema.TransitiveActionHierarchy acts) :
  acts.validateTransitiveActionHierarchy = .ok ()
:= by
  unfold ActionSchema.validateTransitiveActionHierarchy
  apply List.all_ok_implies_forM_ok
  intro ⟨uid₁, entry₁⟩ hmem₁
  apply List.all_ok_implies_forM_ok
  intro ⟨uid₂, entry₂⟩ hmem₂
  have hsub := htransitive uid₁ entry₁ uid₂ entry₂
    ((Map.in_list_iff_find?_some hmap).mp hmem₁) ((Map.in_list_iff_find?_some hmap).mp hmem₂)
  by_cases hanc : uid₂ ∈ entry₁.ancestors
  · have hsub : entry₂.ancestors.subset entry₁.ancestors = true := hsub hanc
    simp [Set.contains_prop_bool_equiv, hanc, hsub]
  · simp [Set.contains_prop_bool_equiv, hanc]

theorem action_schema_validate_well_formed_is_complete
  {env : TypeEnv} {acts : ActionSchema}
  (hwf : ActionSchema.WellFormed env acts) :
  acts.validateWellFormed env = .ok ()
:= by
  obtain ⟨hmap, hentries, hdisjoint, hacyclic, htransitive⟩ := hwf
  simp only [ActionSchema.validateWellFormed, Map.wellFormed_correct.mpr hmap, ↓reduceIte,
    Except.bind_ok]
  rw [List.all_ok_implies_forM_ok _ _ ?entries]
  case entries =>
    intro ⟨uid, entry⟩ hmem
    have hfind := (Map.in_list_iff_find?_some hmap).mp hmem
    have hnot := hdisjoint uid (by simp [ActionSchema.contains, hfind])
    simp [hnot, action_schema_entry_validate_well_formed_is_complete (hentries uid entry hfind)]
  simp only [Except.bind_ok,
    action_schema_validate_acyclic_action_hierarchy_is_complete hmap hacyclic,
    action_schema_validate_transitive_action_hierarchy_is_complete hmap htransitive]

theorem request_type_validate_well_formed_is_complete
  {env : TypeEnv} {reqty : RequestType}
  (hwf : RequestType.WellFormed env reqty) :
  reqty.validateWellFormed env = .ok ()
:= by
  obtain ⟨entry, hfind, hprincipal, hresource, hcontext⟩ := hwf
  simp [RequestType.validateWellFormed, hfind, Set.contains_prop_bool_equiv, hprincipal,
    hresource, hcontext]

theorem env_validate_well_formed_is_complete
  {env : TypeEnv}
  (hwf : TypeEnv.WellFormed env) :
  env.validateWellFormed = .ok ()
:= by
  obtain ⟨hets, hacts, hreqty⟩ := hwf
  simp [TypeEnv.validateWellFormed, entity_schema_validate_well_formed_is_complete hets,
    action_schema_validate_well_formed_is_complete hacts,
    request_type_validate_well_formed_is_complete hreqty]

/--
Every environment of a schema has the schema's maps and the request type of
one of its actions.
-/
theorem mem_environments {schema : Schema} {env : TypeEnv}
  (h : env ∈ schema.environments) :
  env.ets = schema.ets ∧ env.acts = schema.acts ∧
  ∃ entry, (env.reqty.action, entry) ∈ schema.acts.toList ∧
    env.reqty.principal ∈ entry.appliesToPrincipal ∧
    env.reqty.resource ∈ entry.appliesToResource ∧
    env.reqty.context = entry.context
:= by
  simp only [Schema.environments, List.mem_map, List.mem_flatMap] at h
  obtain ⟨reqty, ⟨⟨uid, entry⟩, hmem, hreqty⟩, rfl⟩ := h
  have hreqty : reqty ∈
      (entry.appliesToPrincipal.toList.product entry.appliesToResource.toList |>.map
        (λ (principal, resource) =>
          { principal, action := uid, resource, context := entry.context })) :=
    hreqty
  simp only [List.mem_map, Prod.exists, List.pair_mem_product] at hreqty
  obtain ⟨principal, resource, ⟨hp, hr⟩, rfl⟩ := hreqty
  exact ⟨rfl, rfl, entry, hmem, (Set.mem_elts_iff_mem_set _ _).mp hp,
    (Set.mem_elts_iff_mem_set _ _).mp hr, rfl⟩

/--
A schema passes the well-formedness check when its maps are well-formed in each
of its environments.
-/
theorem schema_validate_well_formed_is_complete
  {schema : Schema}
  (hwf : ∀ env ∈ schema.environments, env.ets.WellFormed env ∧ env.acts.WellFormed env) :
  schema.validateWellFormed = .ok ()
:= by
  apply List.all_ok_implies_forM_ok
  intro env henv
  obtain ⟨hets, hacts⟩ := hwf env henv
  obtain ⟨-, hacts_eq, entry, hmem, hprincipal, hresource, hcontext⟩ := mem_environments henv
  have hmap : Map.WellFormed schema.acts := hacts_eq ▸ hacts.1
  refine env_validate_well_formed_is_complete ⟨hets, hacts, entry, ?_, hprincipal, hresource,
    hcontext⟩
  rw [hacts_eq]
  exact (Map.in_list_iff_find?_some hmap).mp hmem

end Cedar.Thm
