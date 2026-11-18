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

import Cedar.Thm.Data.LT
import Cedar.Thm.Validation.Typechecker.Basic

/-!
This file proves that typechecking of `.binaryApp .mem` expressions is sound.
-/

namespace Cedar.Thm

open Cedar.Data
open Cedar.Spec
open Cedar.Validation


theorem type_of_mem_inversion {x₁ x₂ : Expr} {c c' : Capabilities} {env : TypeEnv} {ty : TypedExpr}
  (h₁ : typeOf (Expr.binaryApp .mem x₁ x₂) c env = Except.ok (ty, c')) :
  c' = ∅ ∧
  ∃ (ety₁ ety₂ : EntityType),
    (∃ c₁, (typeOf x₁ c env).typeOf = Except.ok (.entity ety₁, c₁)) ∧
    (∃ c₂,
      ((typeOf x₂ c env).typeOf = Except.ok (.entity ety₂, c₂) ∧
       ty.typeOf = .bool (typeOfInₑ ety₁ ety₂ x₁ x₂ env)) ∨
      ((typeOf x₂ c env).typeOf = Except.ok (.set (.entity ety₂), c₂) ∧
       ty.typeOf = .bool (typeOfInₛ ety₁ ety₂ x₁ x₂ env)))
:= by
  simp [typeOf] at h₁
  cases h₂ : typeOf x₁ c env <;> simp [h₂] at h₁
  cases h₃ : typeOf x₂ c env <;> simp [h₃] at h₁
  simp [typeOfBinaryApp, ok] at h₁
  split at h₁ <;> try { contradiction }
  all_goals {
    simp only [Except.ok.injEq, Prod.mk.injEq] at h₁
    simp [←h₁, TypedExpr.typeOf]
    rename_i tc₁ tc₂ _ _ _ ety₁ ety₂ _ h₄ h₅
    exists ety₁
    constructor
    · exists tc₁.snd ; simp [←h₄, ResultType.typeOf, Except.map]
    · exists ety₂, tc₂.snd ; simp [←h₅, ResultType.typeOf, Except.map]
  }

theorem entityUID?_some_implies_entity_lit {x : Expr} {euid : EntityUID}
  (h₁ : entityUID? x = some euid) :
  x = Expr.lit (.entityUID euid)
:= by
  simp [entityUID?] at h₁
  split at h₁ <;> simp at h₁ ; subst h₁ ; rfl


theorem actionUID?_some_implies_action_lit {x : Expr} {euid : EntityUID} {acts : ActionSchema}
  (h₁ : actionUID? x acts = some euid) :
  x = Expr.lit (.entityUID euid) ∧
  acts.contains euid = true
:= by
  simp [actionUID?] at h₁
  cases h₂ : entityUID? x <;> simp [h₂] at h₁
  replace h₂ := entityUID?_some_implies_entity_lit h₂
  rename_i euid'
  replace ⟨h₀, h₁⟩ := h₁
  subst euid'
  simp [h₀, h₂]

theorem entityUIDs?_some_implies_entity_lits {x : Expr} {euids : List EntityUID}
  (h₁ : entityUIDs? x = some euids) :
  x = Expr.set ((List.map (Expr.lit ∘ Prim.entityUID) euids))
:= by
  simp [entityUIDs?] at h₁
  split at h₁ <;> try simp at h₁
  rename_i xs
  simp [List.mapM_some_iff_forall₂] at *
  cases euids
  case nil =>
    cases xs <;> simp only [List.Forall₂.nil, List.map_nil] at *
    case cons hd tl => simp only [List.forall₂_nil_right_iff, reduceCtorEq] at h₁
  case cons hd tl =>
    cases xs <;> simp at *
    case nil => simp only [List.forall₂_nil_left_iff, reduceCtorEq] at h₁
    case cons hd' tl' =>
      cases h₂ : entityUID? hd' <;> simp [h₂] at h₁
      replace ⟨h₁', h₁⟩ := h₁
      replace h₂ := entityUID?_some_implies_entity_lit h₂
      subst hd hd'
      simp only [true_and]
      have h₄ := @entityUIDs?_some_implies_entity_lits (.set tl') tl
      simp [entityUIDs?] at h₄
      apply h₄ ; clear h₄
      simp only [List.mapM_some_iff_forall₂, h₁]

theorem acts_maybeDescendentOf_false_implies_not_ancestor_type
  {euid : EntityUID} {ety : EntityType} {data : EntityData} {entry : ActionSchemaEntry}
  {env : TypeEnv} {request : Request} {entities : Entities}
  (hwf : InstanceOfWellFormedEnvironment request entities env)
  (hdesc : env.acts.maybeDescendentOf euid.ty ety = false)
  (hent_found : Map.find? entities euid = some data)
  (hacts_entry : Map.find? env.acts euid = some entry) :
  ∀ euid', euid' ∈ data.ancestors → euid'.ty ≠ ety
:= by
  intros euid' heuid' hety
  simp only [
    ActionSchema.maybeDescendentOf,
    List.any_eq_false, Bool.and_eq_true,
    decide_eq_true_eq, not_and, Bool.not_eq_true,
    Prod.forall,
  ] at hdesc
  have hnot_ans := hdesc euid entry (Map.find?_mem_toList hacts_entry) rfl
  simp only [Set.any, List.any_eq_false, beq_iff_eq] at hnot_ans
  have ⟨data', hdata', heq_ans⟩ := hwf.wf_action_data hacts_entry
  simp only [hdata', Option.some.injEq] at hent_found
  simp only [hent_found] at heq_ans
  simp only [← heq_ans] at hnot_ans
  have h := hnot_ans euid' heuid'
  contradiction

theorem entity_type_in_false_implies_inₑ_false
  {euid₁ euid₂ : EntityUID} {env : TypeEnv} {request : Request} {entities : Entities}
  (h₁ : InstanceOfWellFormedEnvironment request entities env)
  (h₂ : env.descendentOf euid₁.ty euid₂.ty = false) :
  inₑ euid₁ euid₂ entities = false
:= by
  have hwf := h₁
  simp only [TypeEnv.descendentOf, Bool.ite_true_left, Bool.or_eq_false_iff,
    decide_eq_false_iff_not] at h₂
  simp only [inₑ, Bool.or_eq_false_iff, beq_eq_false_iff_ne, ne_eq]
  by_contra h₃
  simp only [not_and, Bool.not_eq_false] at h₃
  simp only [← Classical.or_iff_not_imp_right] at h₃
  rcases h₃ with h₃ | h₃
  case inr => subst h₃ ; simp at h₂
  case inl =>
  simp [Entities.ancestorsOrEmpty] at h₃
  split at h₃
  case h_1 data h₄ =>
    cases h₁.instance_of_schema.1 euid₁ data h₄ with
    | inl h₁ =>
      have ⟨entry, h₂₁, _, _, h₂₂, _⟩ := h₁
      specialize h₂₂ euid₂ h₃
      rw [←Set.contains_prop_bool_equiv] at h₂₂
      simp [h₂₁, h₂₂] at h₂
    | inr h₁ =>
      have ⟨h₁, _, ⟨entry, h₅, _⟩⟩ := h₁
      have h₂ := h₂.2
      split at h₂
      · apply False.elim
        apply wf_env_disjoint_ets_acts hwf.wf_env
        all_goals assumption
      · have h₆ := acts_maybeDescendentOf_false_implies_not_ancestor_type hwf h₂ h₄ h₅ euid₂ h₃
        contradiction
  case h_2 => simp [Set.not_mem_empty] at h₃

theorem action_type_in_eq_action_inₑ
  (euid₁ euid₂ : EntityUID)
  {env : TypeEnv} {request : Request} {entities : Entities}
  (h₁ : InstanceOfWellFormedEnvironment request entities env)
  (h₂ : env.acts.contains euid₁) :
  inₑ euid₁ euid₂ entities = ActionSchema.descendentOf env.acts euid₁ euid₂
:= by
  simp [ActionSchema.contains] at h₂
  cases h₃ : Map.find? env.acts euid₁ <;> simp [h₃] at h₂
  rename_i entry
  have ⟨data, h₁₁, h₁₂⟩ := h₁.wf_action_data h₃
  simp [inₑ, ActionSchema.descendentOf, h₃, Entities.ancestorsOrEmpty, h₁₁]
  rcases h₄ : euid₁ == euid₂ <;> simp at h₄ <;> simp [h₄, h₁₂]

theorem type_of_mem_is_soundₑ {x₁ x₂ : Expr} {c₁ c₁' c₂' : Capabilities} {env : TypeEnv} {request : Request} {entities : Entities} {ety₁ ety₂ : EntityType}
  (h₁ : CapabilitiesInvariant c₁ request entities)
  (h₂ : InstanceOfWellFormedEnvironment request entities env)
  (h₃ : (typeOf x₁ c₁ env).typeOf = Except.ok (CedarType.entity ety₁, c₁'))
  (h₄ : (typeOf x₂ c₁ env).typeOf = Except.ok (CedarType.entity ety₂, c₂'))
  (ih₁ : TypeOfIsSound x₁)
  (ih₂ : TypeOfIsSound x₂) :
  ∃ v,
    EvaluatesTo (Expr.binaryApp BinaryOp.mem x₁ x₂) request entities v ∧
    InstanceOfType env v (CedarType.bool (typeOfInₑ ety₁ ety₂ x₁ x₂ env))
:= by
  have hwf := h₂
  split_type_of h₃ ; rename_i h₃ hl₃ hr₃
  split_type_of h₄ ; rename_i h₄ hl₄ hr₄
  have ⟨_, v₁, hev₁, hty₁⟩ := ih₁ h₁ h₂ h₃
  have ⟨_, v₂, hev₂, hty₂⟩ := ih₂ h₁ h₂ h₄
  simp [EvaluatesTo] at *
  simp [evaluate]
  cases h₅ : evaluate x₁ request entities <;> simp [h₅] at hev₁ <;> simp [hev₁] <;>
  try { apply type_is_inhabited_bool }
  rw [eq_comm] at hev₁ ; subst hev₁
  cases h₆ : evaluate x₂ request entities <;> simp [h₆] at hev₂ <;> simp [hev₂] <;>
  try { apply type_is_inhabited_bool }
  rw [eq_comm] at hev₂ ; subst hev₂
  rw [hl₃] at hty₁
  replace hty₁ := instance_of_entity_type_is_entity hty₁
  replace ⟨euid₁, hty₁, hty₁'⟩ := hty₁
  subst hty₁ hty₁'
  rw [hl₄] at hty₂
  replace hty₂ := instance_of_entity_type_is_entity hty₂
  replace ⟨euid₂, hty₂, hty₂'⟩ := hty₂
  subst hty₂ hty₂'
  simp [apply₂]
  apply InstanceOfType.instance_of_bool
  simp [InstanceOfBoolType]
  split <;> try simp only
  rename_i b bty  h₇ h₈ h₉
  simp [typeOfInₑ] at *
  have ⟨_, hents, hacts⟩ := h₂ ; clear h₂
  cases hₐ : actionUID? x₁ env.acts <;> simp [hₐ] at h₇ h₈ h₉
  case none =>
    cases hin : env.descendentOf euid₁.ty euid₂.ty <;>
    simp [hin] at h₇ h₈ h₉
    simp [entity_type_in_false_implies_inₑ_false hwf hin] at h₉
  case some =>
    cases he : entityUID? x₂ <;> simp [he] at h₇ h₈ h₉
    case none =>
      cases hin : env.descendentOf euid₁.ty euid₂.ty <;>
      simp [hin] at h₇ h₈ h₉
      simp [entity_type_in_false_implies_inₑ_false hwf hin] at h₉
    case some =>
      replace ⟨hₐ, hₐ'⟩ := actionUID?_some_implies_action_lit hₐ
      subst hₐ
      replace he := entityUID?_some_implies_entity_lit he ; subst he
      rename_i auid euid _ _
      simp [evaluate] at h₅ h₆ ; subst h₅ h₆
      have h₁₀ := action_type_in_eq_action_inₑ auid euid hwf hₐ'
      simp [h₁₀] at h₈ h₉
      cases heq : ActionSchema.descendentOf env.acts auid euid <;> simp [heq] at h₈ h₉

theorem entity_set_type_implies_set_of_entities {env : TypeEnv} {vs : List Value} {ety : EntityType}
  (h₁ : InstanceOfType env (Value.set (Set.mk vs)) (CedarType.set (CedarType.entity ety))) :
  ∃ (euids : List EntityUID),
    vs.mapM Value.asEntityUID = Except.ok euids ∧
    ∀ euid, euid ∈ euids → euid.ty = ety
:= by
  rw [←List.mapM'_eq_mapM]
  cases vs
  case nil =>
    simp [pure, Except.pure]
  case cons hd tl =>
    simp only [List.mapM'_cons]
    cases h₁ ; rename_i h₁
    have h₂ := h₁ hd
    simp only [Set.mem_cons, true_or, forall_const] at h₂
    replace ⟨heuid, hdty, h₂⟩ := instance_of_entity_type_is_entity h₂
    subst h₂
    rw [Value.asEntityUID] ; simp only [Except.bind_ok]
    rw [List.mapM'_eq_mapM]
    have h₃ : InstanceOfType env (Value.set (Set.mk tl)) (CedarType.set (CedarType.entity ety)) := by
      apply InstanceOfType.instance_of_set
      intro v h₃
      apply h₁ v
      apply Set.mem_mk_tl
      exact h₃
    have ⟨tleuids, h₄, h₅⟩ := entity_set_type_implies_set_of_entities h₃
    simp [h₄, pure, Except.pure, hdty]
    intro euid heuid
    apply h₅ euid heuid

theorem entity_type_in_false_implies_inₛ_false
  {euid : EntityUID} {euids : List EntityUID} {ety : EntityType}
  {env : TypeEnv} {request : Request} {entities : Entities}
  (h₁ : InstanceOfWellFormedEnvironment request entities env)
  (h₂ : env.descendentOf euid.ty ety = false)
  (h₃ : ∀ euid, euid ∈ euids → euid.ty = ety) :
  Set.any (fun x => inₑ euid x entities) (Set.make euids) = false
:= by
  have hwf := h₁
  simp only [TypeEnv.descendentOf] at h₂
  rw [Set.any_make]
  by_contra h₄
  simp only [Bool.not_eq_false, List.any_eq_true] at h₄
  replace ⟨euid', h₄, h₅⟩ := h₄
  simp only [inₑ, Bool.or_eq_true, beq_iff_eq] at h₅
  rcases h₅ with h₅ | h₅
  case inl =>
    subst h₅
    specialize h₃ euid h₄
    simp [h₃] at h₂
  case inr =>
    simp only [Set.contains, Set.elts, Entities.ancestorsOrEmpty, Set.empty, List.elem_eq_mem,
      decide_eq_true_eq] at h₅
    cases h₆ : Map.find? entities euid <;>
    simp only [h₆, List.not_mem_nil] at h₅
    rename_i data
    cases h₁.instance_of_schema_entry h₆ with
    | inl h₁ =>
      replace ⟨entry, h₁, _, _, h₇, _⟩ := h₁
      specialize h₇ euid' h₅
      split at h₂ <;> try contradiction
      rename_i h₈
      specialize h₃ euid' h₄ ; subst h₃
      split at h₂ <;> rename_i h₉ <;> simp [h₁] at h₉
      subst h₉
      rw [← Set.mem_elts_iff_mem_set] at h₇
      simp only [Set.contains, Set.elts] at h₂ h₇
      rw [← List.elem_iff] at h₇
      rw [h₂] at h₇
      contradiction
    | inr h₁ =>
      have ⟨h₁, _, ⟨entry, h₉, _⟩⟩ := h₁
      simp only [
        Bool.ite_true_left,
        Bool.or_eq_false_iff,
        decide_eq_false_iff_not,
      ] at h₂
      have h₂ := h₂.2
      split at h₂
      · apply False.elim
        apply wf_env_disjoint_ets_acts hwf.wf_env
        all_goals assumption
      · have h₇ := acts_maybeDescendentOf_false_implies_not_ancestor_type hwf h₂ h₆ h₉ euid' h₅
        have h₈ := h₃ euid' h₄
        contradiction

theorem mapM'_eval_lits_eq_prims {ps : List Prim} {vs : List Value} {request : Request} {entities : Entities}
  (h₁ : List.mapM' (evaluate · request entities) (List.map Expr.lit ps) = Except.ok vs) :
  vs = List.map Value.prim ps
:= by
  cases ps
  case nil =>
    simp [pure, Except.pure] at h₁
    subst h₁
    simp only [List.map_nil]
  case cons hd tl =>
    cases h₂ : evaluate (Expr.lit hd) request entities <;> simp [h₂] at h₁
    cases h₃ : List.mapM' (fun x => evaluate x request entities) (List.map Expr.lit tl) <;> simp [h₃] at h₁
    rename_i vhd vtl
    subst h₁
    simp only [List.map, List.cons.injEq]
    constructor
    · simp [evaluate] at h₂ ; simp [h₂]
    · exact mapM'_eval_lits_eq_prims h₃

theorem mapM'_asEntityUID_eq_entities {vs : List Value} {euids : List EntityUID}
  (h₁ : List.mapM' Value.asEntityUID vs = Except.ok euids) :
  vs = List.map (Value.prim ∘ Prim.entityUID) euids
:= by
  cases vs
  case nil =>
    simp only [List.mapM', pure, Except.pure, Except.ok.injEq, List.nil_eq] at h₁
    subst h₁
    simp only [List.map_nil]
  case cons hd tl =>
    simp only [List.mapM', bind_pure_comp] at h₁
    cases h₂ : Value.asEntityUID hd <;> simp [h₂] at h₁
    cases h₃ : List.mapM' Value.asEntityUID tl <;> simp [h₃] at h₁
    rename_i vhd vtl
    subst h₁
    simp only [List.map, Function.comp_apply, List.cons.injEq]
    constructor
    · simp only [Value.asEntityUID] at h₂
      split at h₂ <;> simp at h₂
      rw [eq_comm] at h₂ ; subst h₂
      rfl
    · exact mapM'_asEntityUID_eq_entities h₃

theorem evaluate_entity_set_eqv {vs : List Value} {euids euids' : List EntityUID} {request : Request} {entities : Entities}
  (h₁ : evaluate (Expr.set (List.map (Expr.lit ∘ Prim.entityUID) euids')) request entities =
        Except.ok (Value.set (Set.mk vs)))
  (h₂ : List.mapM Value.asEntityUID vs = Except.ok euids) :
  euids ≡ euids'
:= by
  simp only [evaluate] at h₁
  cases h₃ : List.mapM₁ (List.map (Expr.lit ∘ Prim.entityUID) euids') fun x => evaluate x.val request entities <;> simp [h₃] at h₁
  rename_i vs'
  simp only [List.mapM₁_eq_mapM (evaluate · request entities)] at h₃
  rw [←List.mapM'_eq_mapM, ←List.map_map] at h₃
  replace h₃ := mapM'_eval_lits_eq_prims h₃
  rw [List.map_map] at h₃
  rw [←List.mapM'_eq_mapM] at h₂
  replace h₂ := mapM'_asEntityUID_eq_entities h₂
  replace h₁ := Set.make_mk_eqv h₁
  subst h₂ h₃
  simp [List.Equiv, List.subset_def] at *
  have ⟨hl₁, hr₁⟩ := h₁
  constructor
  · apply hr₁
  · apply hl₁

theorem action_type_in_eq_action_inₛ
  {auid : EntityUID} {euids euids' : List EntityUID}
  {env : TypeEnv} {request : Request} {entities : Entities}
  (h₁ : InstanceOfWellFormedEnvironment request entities env)
  (h₂ : env.acts.contains auid)
  (h₃ : euids ≡ euids') :
  Set.any (fun x => inₑ auid x entities) (Set.make euids) ↔
  ∃ euid, euid ∈ euids' ∧ ActionSchema.descendentOf env.acts auid euid
:= by
  rw [Set.any_make]
  simp only [ActionSchema.contains] at h₂
  cases h₄ : Map.find? env.acts auid <;> simp [h₄] at h₂
  rename_i entry
  have h₁ := h₁.wf_action_data h₄
  constructor <;> intro h₄ <;> rename_i hfnd <;>
  have ⟨data, hl₁, hr₁⟩ := h₁ <;> clear h₁
  case some.mp =>
    rw [List.any_eq_true] at h₄
    replace ⟨euid, h₄, h₅⟩ := h₄
    exists euid
    replace ⟨h₃, _⟩ := h₃
    simp only [List.subset_def] at h₃
    specialize h₃ h₄ ; simp [h₃]
    simp [inₑ] at h₅
    rcases h₅ with h₅ | h₅
    case inl =>
      subst h₅ ; simp [ActionSchema.descendentOf]
    case inr =>
      simp only [ActionSchema.descendentOf, beq_iff_eq, hfnd, Bool.ite_true_left, Bool.or_eq_true,
        decide_eq_true_eq]
      simp only [Entities.ancestorsOrEmpty, hl₁, hr₁] at h₅
      simp [h₅]
  case some.mpr =>
    rw [List.any_eq_true]
    replace ⟨euid, h₄, h₅⟩ := h₄
    exists euid
    replace ⟨_, h₃⟩ := h₃
    simp only [List.subset_def] at h₃
    specialize h₃ h₄ ; simp [h₃]
    simp only [ActionSchema.descendentOf, beq_iff_eq, hfnd, Bool.ite_true_left, Bool.or_eq_true,
      decide_eq_true_eq] at h₅
    by_cases h₆ : auid = euid <;> simp [h₆] at h₅
    case pos =>
      subst h₆ ; simp [inₑ]
    case neg =>
      simp [inₑ, Entities.ancestorsOrEmpty, hl₁, hr₁, h₅]

theorem type_of_mem_is_soundₛ {x₁ x₂ : Expr} {c₁ c₁' c₂' : Capabilities} {env : TypeEnv} {request : Request} {entities : Entities} {ety₁ ety₂ : EntityType}
  (h₁ : CapabilitiesInvariant c₁ request entities)
  (h₂ : InstanceOfWellFormedEnvironment request entities env)
  (h₃ : (typeOf x₁ c₁ env).typeOf = Except.ok (CedarType.entity ety₁, c₁'))
  (h₄ : (typeOf x₂ c₁ env).typeOf = Except.ok (CedarType.set (CedarType.entity ety₂), c₂'))
  (ih₁ : TypeOfIsSound x₁)
  (ih₂ : TypeOfIsSound x₂) :
  ∃ v,
    EvaluatesTo (Expr.binaryApp BinaryOp.mem x₁ x₂) request entities v ∧
    InstanceOfType env v (CedarType.bool (typeOfInₛ ety₁ ety₂ x₁ x₂ env))
:= by
  have hwf := h₂
  split_type_of h₃ ; rename_i h₃ hl₃ hr₃
  split_type_of h₄ ; rename_i h₄ hl₄ hr₄
  have ⟨_, v₁, hev₁, hty₁⟩ := ih₁ h₁ h₂ h₃
  have ⟨_, v₂, hev₂, hty₂⟩ := ih₂ h₁ h₂ h₄
  simp only [EvaluatesTo] at *
  simp only [evaluate]
  cases h₅ : evaluate x₁ request entities <;> simp [h₅] at hev₁ <;> simp [hev₁] <;>
  try { apply type_is_inhabited_bool }
  rw [eq_comm] at hev₁ ; subst hev₁
  cases h₆ : evaluate x₂ request entities <;> simp [h₆] at hev₂ <;> simp [hev₂] <;>
  try { apply type_is_inhabited_bool }
  rw [eq_comm] at hev₂ ; subst hev₂
  rw [hl₃] at hty₁
  replace ⟨euid, hty₁, hty₁'⟩ := instance_of_entity_type_is_entity hty₁
  subst hty₁ hty₁'
  rw [hl₄] at hty₂
  have ⟨vs, hset, _⟩ := instance_of_set_type_is_set hty₂
  subst hset
  simp only [apply₂, inₛ]
  simp only [Set.mapOrErr, Set.elts]
  have ⟨euids, h₇, hty₇⟩ := entity_set_type_implies_set_of_entities hty₂
  simp only [h₇, Except.bind_ok, Except.ok.injEq, false_or, exists_eq_left', reduceCtorEq]
  apply InstanceOfType.instance_of_bool
  simp only [InstanceOfBoolType]
  split <;> try simp only
  rename_i h₈ h₉ h₁₀
  have ⟨_, hents, hacts⟩ := h₂ ; clear h₂
  simp only [typeOfInₛ, List.any_eq_true, imp_false] at *
  cases ha : actionUID? x₁ env.acts <;>
  simp only [ha, ite_eq_left_iff, Bool.not_eq_true, imp_false, Bool.not_eq_false,
    ite_eq_right_iff, reduceCtorEq] at h₈ h₉ h₁₀
  case none =>
    cases hin : env.descendentOf euid.ty ety₂ <;>
    simp only [hin, Bool.false_eq_true, ↓reduceIte, imp_false,
      Bool.not_eq_false, Bool.true_eq_false] at h₈ h₉ h₁₀
    simp only [entity_type_in_false_implies_inₛ_false hwf hin hty₇,
      Bool.false_eq_true] at h₁₀
  case some =>
    cases he : entityUIDs? x₂ <;>
    simp only [he, ite_eq_left_iff, not_exists, not_and, Bool.not_eq_true, imp_false,
      Classical.not_forall, Bool.not_eq_false, ite_eq_right_iff, reduceCtorEq] at h₈ h₉ h₁₀
    case none =>
      cases hin : env.descendentOf euid.ty ety₂ <;>
      simp only [hin, Bool.false_eq_true, ↓reduceIte, imp_false,
        Bool.not_eq_false, Bool.true_eq_false] at h₈ h₉ h₁₀
      simp only [entity_type_in_false_implies_inₛ_false hwf hin hty₇, Bool.false_eq_true] at h₁₀
    case some =>
      replace ⟨ha, hac⟩ := actionUID?_some_implies_action_lit ha
      subst ha
      have he := entityUIDs?_some_implies_entity_lits he
      subst he
      simp only [evaluate, Except.ok.injEq, Value.prim.injEq, Prim.entityUID.injEq] at h₅
      rw [eq_comm] at h₅ ; subst h₅
      rename_i euids' _ _
      have h₁₁ := evaluate_entity_set_eqv h₆ h₇
      have h₁₂ := action_type_in_eq_action_inₛ hwf hac h₁₁
      cases h₁₃ : Set.any (fun x => inₑ euid x entities) (Set.make euids) <;>
      simp only [h₁₃, Bool.false_eq_true, Bool.true_eq_false, false_implies,
        exists_prop, false_implies, true_implies, false_iff, true_iff,
        not_exists, not_and, Bool.not_eq_true] at h₉ h₁₀ h₁₂
      case false =>
        replace ⟨euid', h₁₀⟩ := h₁₀
        specialize h₁₂ euid' h₁₀.left
        simp only [h₁₀.right, Bool.true_eq_false] at h₁₂
      case true =>
        replace ⟨euid', h₁₂⟩ := h₁₂
        specialize h₉ euid' h₁₂.left
        simp only [h₁₂.right, Bool.true_eq_false] at h₉

theorem type_of_mem_is_sound {x₁ x₂ : Expr} {c₁ c₂ : Capabilities} {env : TypeEnv} {ty : TypedExpr} {request : Request} {entities : Entities}
  (h₁ : CapabilitiesInvariant c₁ request entities)
  (h₂ : InstanceOfWellFormedEnvironment request entities env)
  (h₃ : typeOf (Expr.binaryApp .mem x₁ x₂) c₁ env = Except.ok (ty, c₂))
  (ih₁ : TypeOfIsSound x₁)
  (ih₂ : TypeOfIsSound x₂) :
  GuardedCapabilitiesInvariant (Expr.binaryApp .mem x₁ x₂) c₂ request entities ∧
  ∃ v, EvaluatesTo (Expr.binaryApp .mem x₁ x₂) request entities v ∧ InstanceOfType env v ty.typeOf
:= by
  have ⟨hc, ety₁, ety₂, ⟨c₁', h₄⟩ , c₂', h₅⟩ := type_of_mem_inversion h₃
  subst hc
  apply And.intro empty_guarded_capabilities_invariant
  rcases h₅ with ⟨h₅, h₆⟩ | ⟨h₅, h₆⟩ <;> rw [h₆]
  · exact type_of_mem_is_soundₑ h₁ h₂ h₄ h₅ ih₁ ih₂
  · exact type_of_mem_is_soundₛ h₁ h₂ h₄ h₅ ih₁ ih₂

end Cedar.Thm
