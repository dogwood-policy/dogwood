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

import Cedar.Thm.Data.List
import Cedar.Thm.Data.LT
import Cedar.Thm.Validation.Typechecker.Basic
import Cedar.Thm.Validation.Typechecker.LUB

/-!
This file proves that typechecking of `.set` expressions is sound.
-/

namespace Cedar.Thm

open Cedar.Data
open Cedar.Spec
open Cedar.Validation

theorem type_of_set_tail
  {x xhd : Expr } {xtl : List Expr} {c : Capabilities}
  {env : TypeEnv} {ty : CedarType} {hd : TypedExpr } {tl : List TypedExpr}
  (h₁ : (List.mapM₁ (xhd :: xtl) fun x => justType (typeOf x.val c env)) = Except.ok (hd :: tl))
  (h₂ : List.foldlM lub? hd.typeOf (tl.map TypedExpr.typeOf) = some ty)
  (h₃ : List.Mem x xtl) :
  ∃ ty', (typeOf (Expr.set xtl) c env) = Except.ok (.set tl (.set ty'), []) ∧
  (ty' ⊔ ty) = some ty
:= by
  cases xtl
  case nil =>
    have _ := @List.not_mem_nil _ x
    contradiction
  case cons xhd' xtl' =>
    simp only [typeOf]
    cases tl
    case nil =>
      simp only [List.mapM₁_eq_mapM λ x => justType (typeOf x c env), List.mapM_cons,
        bind_assoc, pure_bind] at h₁
      cases h₄ : justType (typeOf xhd c env) <;> simp [h₄] at h₁
      cases h₅ : justType (typeOf xhd' c env) <;> simp [h₅] at h₁
      cases h₆ : List.mapM (fun x => justType (typeOf x c env)) xtl' <;> simp [h₆] at h₁
    case cons hd' tl' =>
      simp only [List.mapM₁_eq_mapM λ x => justType (typeOf x c env)] at h₁
      have h₁ := List.mapM_head_tail h₁
      rw [←List.mapM₁_eq_mapM] at h₁
      simp only [h₁, typeOfSet, List.empty_eq, Except.bind_ok]
      cases h₄ : List.foldlM lub? hd'.typeOf (tl'.map TypedExpr.typeOf) <;>
      simp only [err, ok, Except.ok.injEq, Prod.mk.injEq, and_true]
      case none =>
        have h₅ := foldlM_of_lub_assoc hd.typeOf hd'.typeOf (tl'.map TypedExpr.typeOf)
        simp only [List.map] at h₂
        rw [h₂, h₄] at h₅
        simp at h₅
      case some ty' =>
        have h₅ := foldlM_of_lub_assoc hd.typeOf hd'.typeOf (tl'.map TypedExpr.typeOf)
        simp only [List.map] at h₂
        rw [h₂, h₄] at h₅
        simp only [Option.bind_some_fun] at h₅
        rw [eq_comm, lub_comm] at h₅
        have h₆ := lub_left_subty h₅
        simp only [subty] at h₆
        split at h₆ <;> simp at h₆
        subst h₆
        exists ty'

theorem type_of_set_inversion {xs : List Expr} {c c' : Capabilities} {env : TypeEnv} {tx : TypedExpr}
  (h₁ : typeOf (Expr.set xs) c env = Except.ok (tx, c')) :
  c' = ∅ ∧
  ∃ txs ty,
    tx = (.set txs (.set ty)) ∧
    ∀ xᵢ ∈ xs,
      ∃ txᵢ cᵢ,
        txᵢ ∈ txs ∧
        typeOf xᵢ c env = Except.ok (txᵢ, cᵢ) ∧
        (txᵢ.typeOf ⊔ ty) = .some ty
:= by
  simp [typeOf] at h₁
  cases h₂ : List.mapM₁ xs fun x => justType (typeOf x.val c env) <;>
  simp [h₂] at h₁
  simp [typeOfSet] at h₁
  split at h₁ <;> simp [ok, err] at h₁
  rename_i hd tl
  split at h₁ <;> simp at h₁
  rename_i ty h₃
  have ⟨hl₁, hr₁⟩ := h₁
  subst hl₁ hr₁
  simp only [List.empty_eq, true_and]
  exists (hd :: tl), ty
  apply And.intro ; case left => simp
  intro x h₄
  cases h₄
  case head xtl =>
    simp only [List.mapM₁_eq_mapM λ x => justType (typeOf x c env), List.mapM_cons] at h₂
    rcases h₅ : justType (typeOf x c env) <;>
    simp only [h₅, Except.bind_err, reduceCtorEq] at h₂
    rcases h₆ : xtl.mapM λ x => justType (typeOf x c env) <;>
    simp only [h₆, pure, Except.pure, Except.bind_err, Except.bind_ok, Except.ok.injEq, List.cons.injEq, reduceCtorEq] at h₂
    have ⟨hl₂, hr₂⟩ := h₂ ; subst hl₂ hr₂
    rename_i hdty tlty
    simp only [justType, Except.map] at h₅
    split at h₅ <;> simp at h₅
    rename_i res h₇
    exists hdty, res.snd
    and_intros
    · simp
    · simp [←h₅, h₇]
    · exact foldlM_of_lub_is_LUB h₃
  case tail xhd xtl h₄ =>
    have ⟨ty', h₅, h₆⟩ := type_of_set_tail h₂ h₃ h₄
    have h₇ := @type_of_set_inversion xtl c ∅ env (.set tl ty'.set) h₅
    simp only [List.empty_eq, true_and] at h₇
    replace ⟨ txs, ty, h₇, h₈ ⟩ := h₇
    simp only [TypedExpr.set.injEq, CedarType.set.injEq] at h₇
    replace ⟨ h₇, h₉ ⟩ := h₇
    subst h₇ h₉
    specialize h₈ x h₄
    replace ⟨txᵢ, c₁, htl, htxᵢ, hlub ⟩ := h₈
    exists txᵢ, c₁
    and_intros
    · exact List.Mem.tail _ htl
    · exact htxᵢ
    · exact lub_trans hlub h₆

theorem list_is_sound_implies_tail_is_sound {hd : Expr} {tl : List Expr}
  (h₁ : ∀ (xᵢ : Expr), xᵢ ∈ hd :: tl → TypeOfIsSound xᵢ) :
  ∀ (xᵢ : Expr), xᵢ ∈ tl → TypeOfIsSound xᵢ
:= by
  intro xᵢ h₂
  apply h₁
  simp [h₂]

theorem list_is_typed_implies_tail_is_typed {hd : Expr} {tl : List Expr} {c₁ : Capabilities} {env : TypeEnv} {ty : CedarType}
  (h₁ : ∀ (xᵢ : Expr), xᵢ ∈ hd :: tl → ∃ txᵢ cᵢ, (typeOf xᵢ c₁ env) = Except.ok (txᵢ, cᵢ) ∧ (txᵢ.typeOf ⊔ ty) = some ty) :
  ∀ (xᵢ : Expr), xᵢ ∈ tl → ∃ txᵢ cᵢ, typeOf xᵢ c₁ env = Except.ok (txᵢ, cᵢ) ∧ (txᵢ.typeOf ⊔ ty) = some ty
:= by
  intro xᵢ h₂
  apply h₁
  simp [h₂]

theorem type_of_set_is_sound_err {xs : List Expr} {c₁ : Capabilities} {env : TypeEnv} {ty : CedarType} {request : Request} {entities : Entities} {err : Error}
  (ih : ∀ (xᵢ : Expr), xᵢ ∈ xs → TypeOfIsSound xᵢ)
  (h₁ : CapabilitiesInvariant c₁ request entities)
  (h₂ : InstanceOfWellFormedEnvironment request entities env)
  (h₄ : ∀ (xᵢ : Expr), xᵢ ∈ xs → ∃ txᵢ cᵢ, (typeOf xᵢ c₁ env) = Except.ok (txᵢ, cᵢ) ∧ (txᵢ.typeOf ⊔ ty) = some ty)
  (h₅ : (xs.mapM fun x => evaluate x request entities) = Except.error err) :
  err = Error.entityDoesNotExist ∨
  err = Error.extensionError ∨
  err = Error.arithBoundsError
:= by
  cases h₆ : xs
  case nil =>
    subst h₆
    simp [pure, Except.pure] at h₅
  case cons hd tl =>
    simp [h₆] at h₅
    have h₄ := h₄ hd
    simp only [h₆, List.mem_cons, true_or, forall_const] at h₄
    have ⟨tyᵢ, cᵢ, h₇, _⟩ := h₄
    have h₉ := ih hd ; simp [h₆, TypeOfIsSound] at h₉
    specialize (h₉ h₁ h₂ h₇) ; have ⟨_, v, h₉⟩ := h₉
    simp [EvaluatesTo] at h₉
    have ⟨h₉, _⟩ := h₉
    rcases h₉ with h₉ | h₉ | h₉ | h₉ <;>
    simp [h₉] at h₅ <;>
    try { simp [h₅] }
    subst h₆
    cases h₁₀ : List.mapM (fun x => evaluate x request entities) tl <;>
    simp [h₁₀] at h₅ ; rw [eq_comm] at h₅
    subst h₅
    apply @type_of_set_is_sound_err
      tl c₁ env ty request entities err
      (list_is_sound_implies_tail_is_sound ih)
      h₁ h₂
      (list_is_typed_implies_tail_is_typed h₄)
    exact h₁₀

theorem type_of_set_is_sound_ok { xs : List Expr } { c₁ : Capabilities } { env : TypeEnv } { request : Request } { entities : Entities } { ty : CedarType } { v : Value } { vs : List Value }
  (ih : ∀ (xᵢ : Expr), xᵢ ∈ xs → TypeOfIsSound xᵢ)
  (h₁ : CapabilitiesInvariant c₁ request entities)
  (h₂ : InstanceOfWellFormedEnvironment request entities env)
  (h₃ : ∀ (xᵢ : Expr), xᵢ ∈ xs → ∃ txᵢ cᵢ, (typeOf xᵢ c₁ env) = Except.ok (txᵢ, cᵢ) ∧ (txᵢ.typeOf ⊔ ty) = some ty)
  (h₄ : (xs.mapM fun x => evaluate x request entities) = Except.ok vs)
  (h₅ : v ∈ vs):
  InstanceOfType env v ty
:= by
  cases xs
  case nil =>
    simp [pure, Except.pure] at h₄
    subst h₄
    simp only [List.not_mem_nil] at h₅
  case cons hd tl =>
    simp at h₄
    cases h₇ : evaluate hd request entities <;>
    simp [h₇] at h₄
    rename_i vhd
    cases h₈ : List.mapM (fun x => evaluate x request entities) tl <;>
    simp [h₈] at h₄
    rename_i vtl
    subst h₄
    cases h₅
    case head =>
      specialize h₃ hd
      simp only [List.mem_cons, true_or, forall_const] at h₃
      have ⟨tyᵢ, cᵢ, h₃, h₆⟩ := h₃
      specialize ih hd
      simp [TypeOfIsSound] at ih
      specialize ih h₁ h₂ h₃
      have ⟨_, v', ihl, ihr⟩ := ih
      simp [EvaluatesTo] at ihl
      rcases ihl with ihl | ihl | ihl | ihl <;>
      simp [ihl] at h₇
      subst h₇
      exact instance_of_lub_left h₆ ihr
    case tail h₉ =>
      apply @type_of_set_is_sound_ok
        tl c₁ env request entities ty v vtl
        (list_is_sound_implies_tail_is_sound ih)
        h₁ h₂
        (list_is_typed_implies_tail_is_typed h₃)
        _ h₉
      simp [h₈]

theorem type_of_set_is_sound {xs : List Expr} {c₁ c₂ : Capabilities} {env : TypeEnv} {sty : TypedExpr} {request : Request} {entities : Entities}
  (h₁ : CapabilitiesInvariant c₁ request entities)
  (h₂ : InstanceOfWellFormedEnvironment request entities env)
  (h₃ : typeOf (Expr.set xs) c₁ env = Except.ok (sty, c₂))
  (ih : ∀ (xᵢ : Expr), xᵢ ∈ xs → TypeOfIsSound xᵢ) :
  GuardedCapabilitiesInvariant (Expr.set xs) c₂ request entities ∧
  ∃ v, EvaluatesTo (Expr.set xs) request entities v ∧ InstanceOfType env v sty.typeOf
:= by
  have ⟨h₆, txs, ty, h₄, h₅⟩ := type_of_set_inversion h₃
  subst h₆ ; rw [h₄]
  apply And.intro empty_guarded_capabilities_invariant
  simp only [EvaluatesTo, evaluate, List.mapM₁_eq_mapM (evaluate · request entities)]
  replace h₅ : ∀ xᵢ ∈ xs, ∃ tx c', typeOf xᵢ c₁ env = .ok (tx, c') ∧ (tx.typeOf ⊔ ty) = some ty := by
    intros x h₁
    replace ⟨txᵢ, cᵢ, h₅⟩ := h₅ x h₁
    simp [h₅]
  cases h₆ : xs.mapM fun x => evaluate x request entities <;>
  simp
  case error err =>
    simp only [TypedExpr.typeOf, type_is_inhabited_set, and_true]
    exact type_of_set_is_sound_err ih h₁ h₂ h₅ h₆
  case ok vs =>
    apply InstanceOfType.instance_of_set
    intro v h₇
    rw [Set.mem_make] at h₇
    exact type_of_set_is_sound_ok ih h₁ h₂ h₅ h₆ h₇

/- Used by `type_of_preserves_evaluation_results` -/
theorem type_of_ok_attr_list {c₁ env atys request entities} {axs : List (Attr × Expr)} :
  List.Forall₂ (fun x y => Except.map (fun x_1 => (x.fst, x_1.fst)) (typeOf x.snd c₁ env) = Except.ok y) axs atys →
  (∀ (a₁ : Attr) (x₁ : Expr),
    sizeOf (a₁, x₁).snd < 1 + sizeOf axs →
      ∀ {c₂ : Capabilities} {ty : TypedExpr},
        typeOf x₁ c₁ env = Except.ok (ty, c₂) → evaluate x₁ request entities = evaluate ty.toExpr request entities) →
 List.Forall₂ (fun x y => bindAttr x.fst (evaluate x.snd request entities) = bindAttr y.fst (evaluate y.snd.toExpr request entities)) axs atys
:= by
  intro h₁ h₂
  cases h₁
  case nil => simp only [List.Forall₂.nil]
  case cons a b l₁ l₂ h₃ h₄ =>
    constructor
    · simp [Except.map] at h₃
      split at h₃ <;> cases h₃
      rename_i heq
      have : a ∈ a :: l₁ := by simp
      have : sizeOf (a.fst, a.snd).snd < 1 + sizeOf (a :: l₁) := by
        have : a = (a.fst, a.snd) := by rfl
        rw [this]
        simp only [List.cons.sizeOf_spec, Prod.mk.sizeOf_spec, gt_iff_lt]
        omega
      specialize h₂ a.fst a.snd this heq
      simp only [h₂]
    · have : (∀ (a₁ : Attr) (x₁ : Expr),
        sizeOf (a₁, x₁).snd < 1 + sizeOf l₁ →
          ∀ {c₂ : Capabilities} {ty : TypedExpr},
            typeOf x₁ c₁ env = Except.ok (ty, c₂) → evaluate x₁ request entities = evaluate ty.toExpr request entities) := by
        intro a' x₁ hᵢ c₂ ty
        have : sizeOf (a', x₁).snd < 1 + sizeOf (a :: l₁) := by
          simp
          simp at hᵢ
          omega
        exact h₂ a' x₁ this
      exact type_of_ok_attr_list h₄ this

end Cedar.Thm
