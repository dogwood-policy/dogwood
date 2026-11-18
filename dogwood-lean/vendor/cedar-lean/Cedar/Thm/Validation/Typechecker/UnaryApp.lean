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

import Cedar.Thm.Validation.Typechecker.Basic

/-!
This file proves that typechecking of `.unaryApp` expressions is sound.
-/

namespace Cedar.Thm

open Cedar.Data
open Cedar.Spec
open Cedar.Validation

theorem type_of_unary_inversion {op : UnaryOp} {x₁ : Expr} {c₁ c₂ : Capabilities} {env : TypeEnv} {tx : TypedExpr}
  (h₁ : typeOf (Expr.unaryApp op x₁) c₁ env = Except.ok (tx, c₂)) :
  c₂ = ∅ ∧
  ∃ tx₁ ty c₁',
    tx = .unaryApp op tx₁ ty ∧
    typeOf x₁ c₁ env = Except.ok (tx₁, c₁') ∧
    match op with
    | .not => ∃ bty, ty = .bool bty.not ∧ tx₁.typeOf = .bool bty
    | .neg => tx₁.typeOf = .int ∧ ty = .int
    | .isEmpty => ty = .bool .anyBool ∧ ∃ ty₀, tx₁.typeOf = .set ty₀
    | .like _ => ty = .bool .anyBool ∧ tx₁.typeOf = .string
    | .is ety₀  => ∃ ety₁, ty = .bool (if ety₀ = ety₁ then .tt else .ff) ∧ tx₁.typeOf = .entity ety₁
:= by
  simp only [typeOf] at h₁
  simp_do_let (typeOf x₁ c₁ env) as h₂ at h₁
  rename_i res ; have ⟨ty₁, c₁'⟩ := res
  simp only [typeOfUnaryApp, Function.comp_apply] at h₁
  split at h₁ <;> try contradiction
  all_goals {
    simp only [ok, Except.ok.injEq, Prod.mk.injEq] at h₁
    replace ⟨ h₁, hc ⟩ := h₁
    simp only [hc, true_and]
    exists ty₁
    rename_i hty₁ _
    simp [h₁, hty₁]
  }

theorem type_of_not_inversion {x₁ : Expr} {c₁ c₂ : Capabilities} {env : TypeEnv} {ty : TypedExpr}
  (h₁ : typeOf (Expr.unaryApp .not x₁) c₁ env = Except.ok (ty, c₂)) :
  c₂ = ∅ ∧
  ∃ bty c₁',
    ty.typeOf = .bool bty.not ∧
    (typeOf x₁ c₁ env).typeOf = Except.ok (.bool bty, c₁')
:= by
  simp [typeOf] at h₁
  cases h₂ : typeOf x₁ c₁ env <;> simp [h₂] at h₁
  case ok res =>
    have ⟨ty₁, c₁'⟩ := res
    simp [typeOfUnaryApp] at h₁
    split at h₁ <;> try contradiction
    case h_1 _ ty₁ bty _ h'₁ =>
      simp [ok] at h₁
      apply And.intro
      · simp [h₁]
      · exists bty, c₁'
        have ⟨ hl₁, _ ⟩ := h₁
        rw [←hl₁]
        simp only [TypedExpr.typeOf]
        simp [ResultType.typeOf, Except.map, h'₁]

theorem type_of_not_is_sound {x₁ : Expr} {c₁ c₂ : Capabilities} {env : TypeEnv} {ty : TypedExpr} {request : Request} {entities : Entities}
  (h₁ : CapabilitiesInvariant c₁ request entities)
  (h₂ : InstanceOfWellFormedEnvironment request entities env)
  (h₃ : typeOf (Expr.unaryApp .not x₁) c₁ env = Except.ok (ty, c₂))
  (ih : TypeOfIsSound x₁) :
  GuardedCapabilitiesInvariant (Expr.unaryApp .not x₁) c₂ request entities ∧
  ∃ v, EvaluatesTo (Expr.unaryApp .not x₁) request entities v ∧ InstanceOfType env v ty.typeOf
:= by
  have ⟨h₅, bty, c₁', h₆, h₄⟩ := type_of_not_inversion h₃
  subst h₅; rw [h₆]
  split_type_of h₄ ; rename_i h₄ hl₄ hr₄
  apply And.intro empty_guarded_capabilities_invariant
  have ⟨_, v₁, h₆, h₇⟩ := ih h₁ h₂ h₄ -- IH
  rw [hl₄] at h₇
  simp [EvaluatesTo] at h₆
  simp [EvaluatesTo, evaluate]
  rcases h₆ with h₆ | h₆ | h₆ | h₆ <;> simp [h₆]
  case inr.inr.inr =>
    cases bty
    case anyBool =>
      have ⟨b, h₈⟩ := instance_of_anyBool_is_bool h₇
      cases b <;>
      subst h₈ <;>
      simp [apply₁] <;>
      apply bool_is_instance_of_anyBool
    case tt =>
      have h₈ := instance_of_tt_is_true h₇
      subst h₈
      simp [apply₁, BoolType.not]
      exact false_is_instance_of_ff
    case ff =>
      have h₈ := instance_of_ff_is_false h₇
      subst h₈
      simp [apply₁, BoolType.not]
      exact true_is_instance_of_tt
  all_goals {
    exact type_is_inhabited_bool
  }

theorem type_of_neg_inversion {x₁ : Expr} {c₁ c₂ : Capabilities} {env : TypeEnv} {ty : TypedExpr}
  (h₁ : typeOf (Expr.unaryApp .neg x₁) c₁ env = Except.ok (ty, c₂)) :
  c₂ = ∅ ∧
  ty.typeOf = .int ∧
  ∃ c₁', (typeOf x₁ c₁ env).typeOf = Except.ok (.int, c₁')
:= by
  simp [typeOf] at h₁
  cases h₂ : typeOf x₁ c₁ env <;> simp [h₂] at h₁
  case ok res =>
    have ⟨ty₁, c₁'⟩ := res
    simp [typeOfUnaryApp] at h₁
    split at h₁ <;> try contradiction
    rename_i h'₁
    simp only [h'₁, ResultType.typeOf, Except.map, Except.ok.injEq, Prod.mk.injEq]
    simp only [ok, Except.ok.injEq, Prod.mk.injEq] at h₁
    simp [←h₁, TypedExpr.typeOf]

theorem type_of_neg_is_sound {x₁ : Expr} {c₁ c₂ : Capabilities} {env : TypeEnv} {ty : TypedExpr} {request : Request} {entities : Entities}
  (h₁ : CapabilitiesInvariant c₁ request entities)
  (h₂ : InstanceOfWellFormedEnvironment request entities env)
  (h₃ : typeOf (Expr.unaryApp .neg x₁) c₁ env = Except.ok (ty, c₂))
  (ih : TypeOfIsSound x₁) :
  GuardedCapabilitiesInvariant (Expr.unaryApp .neg x₁) c₂ request entities ∧
  ∃ v, EvaluatesTo (Expr.unaryApp .neg x₁) request entities v ∧ InstanceOfType env v ty.typeOf
:= by
  have ⟨h₅, h₆, c₁', h₄⟩ := type_of_neg_inversion h₃
  subst h₅; rw [h₆]
  apply And.intro empty_guarded_capabilities_invariant
  split_type_of h₄ ; rename_i h₄ hl₄ hr₄
  have ⟨_, v₁, h₆, h₇⟩ := ih h₁ h₂ h₄ -- IH
  simp [EvaluatesTo] at h₆
  simp [EvaluatesTo, evaluate]
  rcases h₆ with h₆ | h₆ | h₆ | h₆ <;> simp [h₆]
  case inr.inr.inr =>
    rw [hl₄] at h₇
    have ⟨i, h₈⟩ := instance_of_int_is_int h₇
    subst h₈
    simp [apply₁, intOrErr]
    cases i.neg?
    case none =>
      simp only [or_false, or_true, true_and, reduceCtorEq]
      exact type_is_inhabited_int
    case some i' =>
      simp only [Except.ok.injEq, false_or, exists_eq_left', reduceCtorEq]
      exact InstanceOfType.instance_of_int
  all_goals {
    exact type_is_inhabited_int
  }

theorem type_of_isEmpty_inversion {x₁ : Expr} {c₁ c₂ : Capabilities} {env : TypeEnv} {ty : TypedExpr}
  (h₁ : typeOf (Expr.unaryApp .isEmpty x₁) c₁ env = Except.ok (ty, c₂)) :
  c₂ = ∅ ∧
  ty.typeOf = .bool .anyBool ∧
  ∃ c₁' ty₀, (typeOf x₁ c₁ env).typeOf = Except.ok (.set ty₀, c₁')
:= by
  simp [typeOf] at h₁
  cases h₂ : typeOf x₁ c₁ env <;> simp [h₂] at h₁
  case ok res =>
    have ⟨ty₁, c₁'⟩ := res
    simp [typeOfUnaryApp] at h₁
    split at h₁ <;> try contradiction
    simp [ok] at h₁
    simp only [←h₁, List.empty_eq, TypedExpr.typeOf]
    rename_i h₃
    simp [h₃, ResultType.typeOf, Except.map]

theorem type_of_isEmpty_is_sound {x₁ : Expr} {c₁ c₂ : Capabilities} {env : TypeEnv} {ty : TypedExpr} {request : Request} {entities : Entities}
  (h₁ : CapabilitiesInvariant c₁ request entities)
  (h₂ : InstanceOfWellFormedEnvironment request entities env)
  (h₃ : typeOf (Expr.unaryApp .isEmpty x₁) c₁ env = Except.ok (ty, c₂))
  (ih : TypeOfIsSound x₁) :
  GuardedCapabilitiesInvariant (Expr.unaryApp .isEmpty x₁) c₂ request entities ∧
  ∃ v, EvaluatesTo (Expr.unaryApp .isEmpty x₁) request entities v ∧ InstanceOfType env v ty.typeOf
:= by
  have ⟨h₅, h₆, c₁', h₄⟩ := type_of_isEmpty_inversion h₃
  subst h₅; rw [h₆]
  apply And.intro empty_guarded_capabilities_invariant
  replace ⟨ty₀, h₄⟩ := h₄
  split_type_of h₄ ; rename_i h₄ hl₄ hr₄
  have ⟨_, v₁, h₆, h₇⟩ := ih h₁ h₂ h₄
  simp [EvaluatesTo, evaluate] at *
  rcases h₆ with h₆ | h₆ | h₆ | h₆ <;> simp [h₆]
  case inr.inr.inr =>
    rw [hl₄] at h₇
    have ⟨s, h₈, _⟩ := instance_of_set_type_is_set h₇
    subst h₈
    simp [apply₁]
    exact bool_is_instance_of_anyBool _
  all_goals {
    exact type_is_inhabited_bool
  }

theorem type_of_like_inversion {x₁ : Expr} {p : Pattern} {c₁ c₂ : Capabilities} {env : TypeEnv} {ty : TypedExpr}
  (h₁ : typeOf (Expr.unaryApp (.like p) x₁) c₁ env = Except.ok (ty, c₂)) :
  c₂ = ∅ ∧
  ty.typeOf = .bool .anyBool ∧
  ∃ c₁', (typeOf x₁ c₁ env).typeOf = Except.ok (.string, c₁')
:= by
  simp [typeOf] at h₁
  cases h₂ : typeOf x₁ c₁ env <;> simp [h₂] at h₁
  case ok res =>
    have ⟨ty₁, c₁'⟩ := res
    simp [typeOfUnaryApp] at h₁
    split at h₁ <;> try contradiction
    simp [ok] at h₁
    rename_i h'₁
    simp only [ResultType.typeOf, Except.map, h'₁]
    simp [←h₁, TypedExpr.typeOf]

theorem type_of_like_is_sound {x₁ : Expr} {p : Pattern} {c₁ c₂ : Capabilities} {env : TypeEnv} {ty : TypedExpr} {request : Request} {entities : Entities}
  (h₁ : CapabilitiesInvariant c₁ request entities)
  (h₂ : InstanceOfWellFormedEnvironment request entities env)
  (h₃ : typeOf (Expr.unaryApp (.like p) x₁) c₁ env = Except.ok (ty, c₂))
  (ih : TypeOfIsSound x₁) :
  GuardedCapabilitiesInvariant (Expr.unaryApp (.like p) x₁) c₂ request entities ∧
  ∃ v, EvaluatesTo (Expr.unaryApp (.like p) x₁) request entities v ∧ InstanceOfType env v ty.typeOf
:= by
  have ⟨h₅, h₆, c₁', h₄⟩ := type_of_like_inversion h₃
  subst h₅; rw [h₆]
  apply And.intro empty_guarded_capabilities_invariant
  split_type_of h₄ ; rename_i h₄ hl₄ hr₄
  have ⟨_, v₁, h₆, h₇⟩ := ih h₁ h₂ h₄ -- IH
  simp [EvaluatesTo] at h₆
  simp [EvaluatesTo, evaluate]
  rcases h₆ with h₆ | h₆ | h₆ | h₆ <;> simp [h₆]
  case inr.inr.inr =>
    rw [hl₄] at h₇
    have ⟨s, h₈⟩ := instance_of_string_is_string h₇
    subst h₈
    simp [apply₁]
    exact bool_is_instance_of_anyBool (wildcardMatch s p)
  all_goals {
    exact type_is_inhabited_bool
  }

theorem type_of_is_inversion {x₁ : Expr} {ety : EntityType} {c₁ c₂ : Capabilities} {env : TypeEnv} {ty : TypedExpr}
  (h₁ : typeOf (Expr.unaryApp (.is ety) x₁) c₁ env = Except.ok (ty, c₂)) :
  c₂ = ∅ ∧
  ∃ ety' c₁',
    ty.typeOf = (.bool (if ety = ety' then .tt else .ff)) ∧
    (typeOf x₁ c₁ env).typeOf = Except.ok (.entity ety', c₁')
:= by
  simp [typeOf] at h₁
  cases h₂ : typeOf x₁ c₁ env <;> simp [h₂] at h₁
  case ok res =>
    have ⟨ty₁, c₁'⟩ := res
    simp [typeOfUnaryApp] at h₁
    split at h₁ <;> try contradiction
    case h_5 _ _ ety' h₃ h'₁ =>
      simp only [UnaryOp.is.injEq] at h₃
      rw [h₃] at h₁
      simp [ok] at h₁
      apply And.intro
      · simp [h₁]
      · exists ety', c₁'
        simp only [←h₁, h'₁, ResultType.typeOf, Except.map, and_true]
        simp [TypedExpr.typeOf, h₃]

theorem type_of_is_is_sound {x₁ : Expr} {ety : EntityType} {c₁ c₂ : Capabilities} {env : TypeEnv} {ty : TypedExpr} {request : Request} {entities : Entities}
  (h₁ : CapabilitiesInvariant c₁ request entities)
  (h₂ : InstanceOfWellFormedEnvironment request entities env)
  (h₃ : typeOf (Expr.unaryApp (.is ety) x₁) c₁ env = Except.ok (ty, c₂))
  (ih : TypeOfIsSound x₁) :
  GuardedCapabilitiesInvariant (Expr.unaryApp (.is ety) x₁) c₂ request entities ∧
  ∃ v, EvaluatesTo (Expr.unaryApp (.is ety) x₁) request entities v ∧ InstanceOfType env v ty.typeOf
:= by
  have ⟨h₅, ety', c₁', h₆, h₄⟩ := type_of_is_inversion h₃
  subst h₅; rw [h₆]
  apply And.intro empty_guarded_capabilities_invariant
  split_type_of h₄ ; rename_i h₄ hl₄ hr₄
  have ⟨_, v₁, h₆, h₇⟩ := ih h₁ h₂ h₄ -- IH
  simp [EvaluatesTo] at h₆
  simp [EvaluatesTo, evaluate]
  rcases h₆ with h₆ | h₆ | h₆ | h₆ <;> simp [h₆]
  case inr.inr.inr =>
    rw [hl₄] at h₇
    have ⟨uid, h₈, h₉⟩ := instance_of_entity_type_is_entity h₇
    simp [apply₁, h₉, h₈]
    cases h₁₀ : ety == ety' <;>
    simp at h₁₀ <;>
    simp [h₁₀]
    case false => exact false_is_instance_of_ff
    case true => exact true_is_instance_of_tt
  all_goals {
    apply type_is_inhabited_bool
  }

theorem type_of_unaryApp_is_sound {op₁ : UnaryOp} {x₁ : Expr} {c₁ c₂ : Capabilities} {env : TypeEnv} {ty : TypedExpr} {request : Request} {entities : Entities}
  (h₁ : CapabilitiesInvariant c₁ request entities)
  (h₂ : InstanceOfWellFormedEnvironment request entities env)
  (h₃ : typeOf (Expr.unaryApp op₁ x₁) c₁ env = Except.ok (ty, c₂))
  (ih : TypeOfIsSound x₁) :
  GuardedCapabilitiesInvariant (Expr.unaryApp op₁ x₁) c₂ request entities ∧
  ∃ v, EvaluatesTo (Expr.unaryApp op₁ x₁) request entities v ∧ InstanceOfType env v ty.typeOf
:= by
  match op₁ with
  | .not     => exact type_of_not_is_sound h₁ h₂ h₃ ih
  | .neg     => exact type_of_neg_is_sound h₁ h₂ h₃ ih
  | .isEmpty => exact type_of_isEmpty_is_sound h₁ h₂ h₃ ih
  | .like p  => exact type_of_like_is_sound h₁ h₂ h₃ ih
  | .is ety  => exact type_of_is_is_sound h₁ h₂ h₃ ih

end Cedar.Thm
