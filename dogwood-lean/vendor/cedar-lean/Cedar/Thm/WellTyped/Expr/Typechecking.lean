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

import Cedar.Thm.WellTyped.Expr.Definition
import Cedar.Thm.WellTyped.Expr.TypeLifting

/-!
This file contains expression-kind-specific lemmas of the theorem `typechecked_is_well_typed_after_lifting`
-/

namespace Cedar.Thm

open Cedar.Thm
open Cedar.Validation
open Cedar.Spec

theorem typechecked_is_well_typed_after_lifting_lit
{p : Prim}
{c₁ c₂ : Capabilities}
{env : TypeEnv}
{ty : TypedExpr} :
  typeOf (Expr.lit p) c₁ env = Except.ok (ty, c₂) → TypedExpr.WellTyped env ty.liftBoolTypes
:= by
  intro h₂
  simp only [typeOf, typeOfLit, List.empty_eq, Function.comp_apply, Bool.or_eq_true, ok] at h₂
  split at h₂ <;> try simp at h₂ ; rcases h₂ with ⟨h₂, _⟩
  · simp only [← h₂, TypedExpr.liftBoolTypes, CedarType.liftBoolTypes, BoolType.lift]
    exact TypedExpr.WellTyped.lit (Prim.WellTyped.bool true)
  · simp only [← h₂, TypedExpr.liftBoolTypes, CedarType.liftBoolTypes, BoolType.lift]
    exact TypedExpr.WellTyped.lit (Prim.WellTyped.bool false)
  · simp only [← h₂, TypedExpr.liftBoolTypes, CedarType.liftBoolTypes]
    rename_i i _
    exact TypedExpr.WellTyped.lit (Prim.WellTyped.int i)
  · simp only [← h₂, TypedExpr.liftBoolTypes, CedarType.liftBoolTypes]
    rename_i s _
    exact TypedExpr.WellTyped.lit (Prim.WellTyped.string s)
  · split at h₂
    · simp only [Except.ok.injEq, Prod.mk.injEq, List.nil_eq] at h₂
      rcases h₂ with ⟨h₂, _⟩
      simp only [← h₂, TypedExpr.liftBoolTypes, CedarType.liftBoolTypes]
      rename_i uid h₄ _
      exact TypedExpr.WellTyped.lit (Prim.WellTyped.entityUID uid h₄)
    · cases h₂

theorem typechecked_is_well_typed_after_lifting_var
{v : Var}
{c₁ c₂ : Capabilities}
{env : TypeEnv}
{ty : TypedExpr} :
  typeOf (Expr.var v) c₁ env = Except.ok (ty, c₂) →
  TypedExpr.WellTyped env ty.liftBoolTypes
:= by
  intro h₂
  simp only [typeOf, typeOfVar] at h₂
  split at h₂
  all_goals simp only [List.empty_eq, Function.comp_apply] at h₂
  all_goals rcases h₂ with ⟨rfl, _⟩
  all_goals simp only [TypedExpr.liftBoolTypes]
  -- principal, action, resource: entity types where liftBoolTypes is identity
  · simp only [CedarType.liftBoolTypes]; constructor; constructor
  · simp only [CedarType.liftBoolTypes]; constructor; constructor
  · simp only [CedarType.liftBoolTypes]; constructor; constructor
  -- context: liftBoolTypes (.record ...) must stay folded
  · constructor; constructor

theorem typechecked_is_well_typed_after_lifting_ite
{cond thenExpr elseExpr : Expr}
{c₁ c₂ : Capabilities}
{env : TypeEnv}
{ty : TypedExpr}
(hᵢ₁ : ∀ {c₂ : Capabilities} {ty : TypedExpr},
    typeOf cond c₁ env = Except.ok (ty, c₂) → TypedExpr.WellTyped env ty.liftBoolTypes)
(hᵢ₂ : ∀ (c₁_1 : Capabilities) {c₂ : Capabilities} {ty : TypedExpr},
    typeOf thenExpr (c₁ ∪ c₁_1) env = Except.ok (ty, c₂) → TypedExpr.WellTyped env ty.liftBoolTypes)
(hᵢ₃ : ∀ {c₂ : Capabilities} {ty : TypedExpr},
    typeOf elseExpr c₁ env = Except.ok (ty, c₂) → TypedExpr.WellTyped env ty.liftBoolTypes)
:
  typeOf (cond.ite thenExpr elseExpr) c₁ env = Except.ok (ty, c₂) →
  TypedExpr.WellTyped env ty.liftBoolTypes
:= by
  intro h₂
  simp only [typeOf] at h₂
  generalize heq : typeOf cond c₁ env = res₁
  cases res₁
  case error =>
    simp only [heq, Except.bind_err, reduceCtorEq] at h₂
  case ok =>
    simp only [heq, typeOfIf, Except.bind_ok] at h₂
    split at h₂
    case _ ty₁ _ heq₁ =>
      generalize heq₂ : typeOf thenExpr (c₁ ∪ ty₁.snd) env = res₂
      cases res₂
      case error =>
        simp only [heq₂, Except.bind_err, reduceCtorEq] at h₂
      case ok ty' =>
        simp only [heq₂, ok, Except.bind_ok, Except.ok.injEq, Prod.mk.injEq] at h₂
        rcases h₂ with ⟨h₂, _⟩
        subst h₂
        simp [TypedExpr.liftBoolTypes, ←type_of_after_lifted_is_lifted]
        constructor
        · exact hᵢ₁ heq
        · exact hᵢ₂ ty₁.snd heq₂
        · exact hᵢ₂ ty₁.snd heq₂
        · simp [type_of_after_lifted_is_lifted, heq₁, CedarType.liftBoolTypes, BoolType.lift]
        · rfl
    case _ heq₁ =>
      generalize heq₂ : typeOf elseExpr c₁ env = res₃
      cases res₃
      case error =>
        simp only [heq₂, Except.bind_err, reduceCtorEq] at h₂
      case ok ty' =>
        simp only [heq₂, ok, Except.bind_ok, Except.ok.injEq, Prod.mk.injEq] at h₂
        rcases h₂ with ⟨h₂, _⟩
        subst h₂
        simp [TypedExpr.liftBoolTypes, ←type_of_after_lifted_is_lifted]
        constructor
        · exact hᵢ₁ heq
        · exact hᵢ₃ heq₂
        · exact hᵢ₃ heq₂
        · simp [type_of_after_lifted_is_lifted, heq₁, CedarType.liftBoolTypes, BoolType.lift]
        · rfl
    case _ ty₁ _ heq₁ =>
      generalize heq₂ : typeOf thenExpr (c₁ ∪ ty₁.snd) env = res₂
      cases res₂
      case error => simp [heq₂] at h₂
      case ok =>
        simp only [heq₂, Except.bind_ok] at h₂
        generalize heq₃ : typeOf elseExpr c₁ env = res₃
        cases res₃
        case error => simp [heq₃] at h₂
        case ok =>
          simp only [heq₃, Except.bind_ok] at h₂
          split at h₂
          case _ ty₂ ty₃ _ ty' heq₄ =>
            simp only [ok, Except.ok.injEq, Prod.mk.injEq] at h₂
            rcases h₂ with ⟨h₂, _⟩
            subst h₂
            simp [TypedExpr.liftBoolTypes]
            have : ty'.liftBoolTypes = ty₂.fst.liftBoolTypes.typeOf := by
              simp [type_of_after_lifted_is_lifted]
              symm
              exact lifted_type_is_top (lub_left_subty heq₄)
            simp [this]
            clear this
            constructor
            · exact hᵢ₁ heq
            · exact hᵢ₂ ty₁.snd heq₂
            · exact hᵢ₃ heq₃
            · simp only [type_of_after_lifted_is_lifted, heq₁, CedarType.liftBoolTypes,
              BoolType.lift]
            · simp only [type_of_after_lifted_is_lifted, lifted_type_lub heq₄]
          case _ => simp only [err, reduceCtorEq] at h₂
    case _ => simp only [err, reduceCtorEq] at h₂

theorem typechecked_is_well_typed_after_lifting_and
{x₁ x₂ : Expr}
{c₁ c₂ : Capabilities}
{env : TypeEnv}
{ty : TypedExpr}
(hᵢ₁ : ∀ {c₂ : Capabilities} {ty : TypedExpr},
    typeOf x₁ c₁ env = Except.ok (ty, c₂) → TypedExpr.WellTyped env ty.liftBoolTypes)
(hᵢ₂ : ∀ (c : Capabilities) {c₂ : Capabilities} {ty : TypedExpr},
    typeOf x₂ (c₁ ∪ c) env = Except.ok (ty, c₂) → TypedExpr.WellTyped env ty.liftBoolTypes) :
  typeOf (x₁.and x₂) c₁ env = Except.ok (ty, c₂) → TypedExpr.WellTyped env ty.liftBoolTypes
:= by
  intro h₃
  simp [typeOf] at h₃
  generalize hₓ₁ : typeOf x₁ c₁ env = res₁
  cases res₁
  case error =>
    simp only [hₓ₁, Except.bind_err, reduceCtorEq] at h₃
  case ok ty₁ =>
    simp only [hₓ₁, Except.bind_ok] at h₃
    simp only [typeOfAnd, List.empty_eq] at h₃
    split at h₃
    case _ heq =>
      simp only [ok, Except.ok.injEq, Prod.mk.injEq, List.nil_eq] at h₃
      rcases h₃ with ⟨h₃, _⟩
      subst h₃
      exact hᵢ₁ hₓ₁
    case _ heq =>
      generalize hₓ₂ : typeOf x₂ (c₁ ∪ ty₁.snd) env = res₂
      cases res₂
      case error =>
        simp only [hₓ₂, Except.bind_err, reduceCtorEq] at h₃
      case ok ty₂ =>
        simp only [hₓ₂, Except.bind_ok] at h₃
        split at h₃ <;> try
        {
          rename_i heq₁
          simp [ok] at h₃
          rcases h₃ with ⟨h₃, _⟩
          subst h₃
          simp [TypedExpr.liftBoolTypes, CedarType.liftBoolTypes, BoolType.lift]
          apply TypedExpr.WellTyped.and
          · exact hᵢ₁ hₓ₁
          · exact hᵢ₂ ty₁.snd hₓ₂
          · simp [type_of_after_lifted_is_lifted, heq, CedarType.liftBoolTypes, BoolType.lift]
          · simp [type_of_after_lifted_is_lifted, heq₁, CedarType.liftBoolTypes, BoolType.lift]
        }
        case _ => simp only [err, reduceCtorEq] at h₃
    case _ => simp only [err, reduceCtorEq] at h₃

theorem typechecked_is_well_typed_after_lifting_or
{x₁ x₂ : Expr}
{c₁ c₂ : Capabilities}
{env : TypeEnv}
{ty : TypedExpr}
(hᵢ₁ : ∀ {c₂ : Capabilities} {ty : TypedExpr},
    typeOf x₁ c₁ env = Except.ok (ty, c₂) → TypedExpr.WellTyped env ty.liftBoolTypes)
(hᵢ₂ : ∀ {c₂ : Capabilities} {ty : TypedExpr},
    typeOf x₂ c₁ env = Except.ok (ty, c₂) → TypedExpr.WellTyped env ty.liftBoolTypes) :
  typeOf (x₁.or x₂) c₁ env = Except.ok (ty, c₂) → TypedExpr.WellTyped env ty.liftBoolTypes
:= by
  intro h₃
  simp [typeOf] at h₃
  generalize hₓ₁ : typeOf x₁ c₁ env = res₁
  cases res₁
  case error =>
    simp only [hₓ₁, Except.bind_err, reduceCtorEq] at h₃
  case ok ty₁ =>
    simp only [hₓ₁, Except.bind_ok, typeOfOr, List.empty_eq] at h₃
    split at h₃
    case _ heq =>
      simp only [ok, Except.ok.injEq, Prod.mk.injEq, List.nil_eq] at h₃
      rcases h₃ with ⟨h₃, _⟩
      subst h₃
      exact hᵢ₁ hₓ₁
    case _ heq =>
      generalize hₓ₂ : typeOf x₂ c₁ env = res₂
      cases res₂
      case error =>
        simp only [hₓ₂, Except.bind_err, reduceCtorEq] at h₃
      case ok ty₂ =>
        simp only [hₓ₂, Except.bind_ok] at h₃
        split at h₃
        case _ heq₁ =>
          simp only [ok, Except.ok.injEq, Prod.mk.injEq] at h₃
          rcases h₃ with ⟨h₃, _⟩
          subst h₃
          simp [TypedExpr.liftBoolTypes, heq₁, CedarType.liftBoolTypes, BoolType.lift]
          apply TypedExpr.WellTyped.or
          · exact hᵢ₁ hₓ₁
          · exact hᵢ₂ hₓ₂
          · simp [type_of_after_lifted_is_lifted, heq, CedarType.liftBoolTypes, BoolType.lift]
          · simp [type_of_after_lifted_is_lifted, heq₁, CedarType.liftBoolTypes, BoolType.lift]
        case _ => simp [err] at h₃
    case _ heq =>
      generalize hₓ₂ : typeOf x₂ c₁ env = res₂
      cases res₂
      case error =>
        simp only [hₓ₂, Except.bind_err, reduceCtorEq] at h₃
      case ok =>
        simp only [hₓ₂, Except.bind_ok] at h₃
        split at h₃ <;> try {
          rename_i heq₁
          simp [ok] at h₃
          rcases h₃ with ⟨h₃, _⟩
          subst h₃
          simp only [TypedExpr.liftBoolTypes, CedarType.liftBoolTypes, BoolType.lift]
          apply TypedExpr.WellTyped.or
          · exact hᵢ₁ hₓ₁
          · exact hᵢ₂ hₓ₂
          · simp [type_of_after_lifted_is_lifted, heq, CedarType.liftBoolTypes, BoolType.lift]
          · simp [type_of_after_lifted_is_lifted, heq₁, CedarType.liftBoolTypes, BoolType.lift]
        }
        case _ => simp only [err, reduceCtorEq] at h₃
    case _ => simp only [err, reduceCtorEq] at h₃

theorem typechecked_is_well_typed_after_lifting_unary_app
{x₁: Expr}
{c₁ c₂ : Capabilities}
{env : TypeEnv}
{ty : TypedExpr}
{op₁ : UnaryOp}
(hᵢ₁ : ∀ {c₂ : Capabilities} {ty : TypedExpr},
    typeOf x₁ c₁ env = Except.ok (ty, c₂) → TypedExpr.WellTyped env ty.liftBoolTypes) :
  typeOf (Expr.unaryApp op₁ x₁) c₁ env = Except.ok (ty, c₂) → TypedExpr.WellTyped env ty.liftBoolTypes
:= by
  intro h₃
  simp only [typeOf] at h₃
  generalize hᵢ : typeOf x₁ c₁ env = res₁
  cases res₁
  case error => simp [hᵢ] at h₃
  case ok ty₁ =>
    simp only [hᵢ, typeOfUnaryApp, ok, List.empty_eq, Function.comp_apply, Except.bind_ok] at h₃
    split at h₃ <;>
    simp [err] at h₃ <;>
    rcases h₃ with ⟨h₃₁, _⟩ <;>
    subst h₃₁ <;>
    simp [TypedExpr.liftBoolTypes, CedarType.liftBoolTypes, BoolType.lift] <;>
    apply TypedExpr.WellTyped.unaryApp <;>
    try exact hᵢ₁ hᵢ
    case _ h₃ _ =>
      constructor
      simp only [type_of_after_lifted_is_lifted, h₃, CedarType.liftBoolTypes, BoolType.lift]
    case _ h₃ _ =>
      constructor
      simp only [type_of_after_lifted_is_lifted, h₃, CedarType.liftBoolTypes]
    case _ elmTy heq _ =>
      apply @UnaryOp.WellTyped.isEmpty _ elmTy.liftBoolTypes
      simp only [type_of_after_lifted_is_lifted, heq, CedarType.liftBoolTypes]
    case _ heq _ =>
      constructor
      simp only [type_of_after_lifted_is_lifted, heq, CedarType.liftBoolTypes]
    case _ ety₁ ety₂ heq _ =>
      apply @UnaryOp.WellTyped.is _ ety₁ ety₂
      simp only [type_of_after_lifted_is_lifted, heq, CedarType.liftBoolTypes]

theorem typechecked_is_well_typed_after_lifting_binary_app
{x₁ x₂ : Expr}
{c₁ c₂ : Capabilities}
{env : TypeEnv}
{ty : TypedExpr}
{op₂ : BinaryOp}
(hᵢ₁ : ∀ {c₂ : Capabilities} {ty : TypedExpr},
    typeOf x₁ c₁ env = Except.ok (ty, c₂) → TypedExpr.WellTyped env ty.liftBoolTypes)
(hᵢ₂ : ∀ {c₂ : Capabilities} {ty : TypedExpr},
    typeOf x₂ c₁ env = Except.ok (ty, c₂) → TypedExpr.WellTyped env ty.liftBoolTypes) :
  typeOf (Expr.binaryApp op₂ x₁ x₂) c₁ env = Except.ok (ty, c₂) → TypedExpr.WellTyped env ty.liftBoolTypes
:= by
  intro h₃
  simp only [typeOf] at h₃
  generalize hᵢ₁' : typeOf x₁ c₁ env = res₁
  generalize hᵢ₂' : typeOf x₂ c₁ env = res₂
  cases res₁ <;> cases res₂ <;> simp [hᵢ₁', hᵢ₂'] at h₃
  rename_i tc₁ tc₂
  simp only [typeOfBinaryApp] at h₃
  split at h₃
  case _ =>
    simp only [typeOfEq, beq_iff_eq, List.empty_eq, Function.comp_apply] at h₃
    split at h₃
    case _ p₁ p₂ =>
      split at h₃ <;>
      simp [ok] at h₃ <;>
      rcases h₃ with ⟨h₃, _⟩ <;>
      subst h₃ <;>
      simp [TypedExpr.liftBoolTypes, CedarType.liftBoolTypes, BoolType.lift] <;>
      constructor
      · exact hᵢ₁ hᵢ₁'
      · exact hᵢ₂ hᵢ₂'
      · rcases type_of_lit_inversion hᵢ₁' with ⟨ty₁, hᵢ₁'⟩
        rw [hᵢ₁']
        rcases type_of_lit_inversion hᵢ₂' with ⟨ty₂, hᵢ₂'⟩
        rw [hᵢ₂']
        simp [TypedExpr.liftBoolTypes]
        exact BinaryOp.WellTyped.eq_lit
      · exact hᵢ₁ hᵢ₁'
      · exact hᵢ₂ hᵢ₂'
      · rcases type_of_lit_inversion hᵢ₁' with ⟨ty₁, hᵢ₁'⟩
        rw [hᵢ₁']
        rcases type_of_lit_inversion hᵢ₂' with ⟨ty₂, hᵢ₂'⟩
        rw [hᵢ₂']
        simp [TypedExpr.liftBoolTypes]
        exact BinaryOp.WellTyped.eq_lit
    case _ =>
      split at h₃
      case _ heq =>
        simp [ok] at h₃
        rcases h₃ with ⟨h₃, _⟩
        subst h₃
        simp only [TypedExpr.liftBoolTypes, CedarType.liftBoolTypes, BoolType.lift]
        constructor
        · exact hᵢ₁ hᵢ₁'
        · exact hᵢ₂ hᵢ₂'
        · apply BinaryOp.WellTyped.eq
          simp only [type_of_after_lifted_is_lifted, lifted_type_lub heq]
      case _ =>
        split at h₃
        case _ ety₁ ety₂ heq₁ heq₂ =>
          simp [ok] at h₃
          rcases h₃ with ⟨h₃, _⟩
          subst h₃
          simp only [TypedExpr.liftBoolTypes, CedarType.liftBoolTypes, BoolType.lift]
          constructor
          · exact hᵢ₁ hᵢ₁'
          · exact hᵢ₂ hᵢ₂'
          · apply @BinaryOp.WellTyped.eq_entity _ ety₁ ety₂ <;>
            simp [type_of_after_lifted_is_lifted]
            · simp [heq₁, CedarType.liftBoolTypes]
            · simp [heq₂, CedarType.liftBoolTypes]
        case _ => simp only [err, reduceCtorEq] at h₃
  case _ ety₁ ety₂ heq₁ heq₂ =>
    simp only [ok, List.empty_eq, Except.ok.injEq, Prod.mk.injEq, List.nil_eq] at h₃
    rcases h₃ with ⟨h₃, _⟩
    subst h₃
    simp only [TypedExpr.liftBoolTypes, CedarType.liftBoolTypes, BoolType.lift]
    constructor
    · exact hᵢ₁ hᵢ₁'
    · exact hᵢ₂ hᵢ₂'
    · apply @BinaryOp.WellTyped.memₑ _ _ _ ety₁ ety₂ <;>
      simp [type_of_after_lifted_is_lifted]
      · simp [heq₁, CedarType.liftBoolTypes]
      · simp [heq₂, CedarType.liftBoolTypes]
  case _ ety₁ ety₂ heq₁ heq₂ =>
    simp only [ok, List.empty_eq, Except.ok.injEq, Prod.mk.injEq, List.nil_eq] at h₃
    rcases h₃ with ⟨h₃, _⟩
    subst h₃
    simp only [TypedExpr.liftBoolTypes, CedarType.liftBoolTypes, BoolType.lift]
    constructor
    · exact hᵢ₁ hᵢ₁'
    · exact hᵢ₂ hᵢ₂'
    · apply @BinaryOp.WellTyped.memₛ _ _ _ ety₁ ety₂ <;>
      simp [type_of_after_lifted_is_lifted]
      · simp [heq₁, CedarType.liftBoolTypes]
      · simp [heq₂, CedarType.liftBoolTypes]
  case _ ety heq₁ heq₂ =>
    simp only [ok, do_ok_eq_ok, Prod.mk.injEq, Prod.exists, exists_eq_right_right] at h₃
    rcases h₃ with ⟨a, h₃₁, h₃₂⟩
    subst h₃₂
    simp only [TypedExpr.liftBoolTypes]
    constructor
    · exact hᵢ₁ hᵢ₁'
    · exact hᵢ₂ hᵢ₂'
    · simp only [typeOfHasTag, List.empty_eq] at h₃₁
      split at h₃₁
      case _ =>
        simp only [ok, Except.ok.injEq, Prod.mk.injEq, List.nil_eq] at h₃₁
        rcases h₃₁ with ⟨h₃₁, _⟩
        subst h₃₁
        simp only [CedarType.liftBoolTypes, BoolType.lift]
        apply @BinaryOp.WellTyped.hasTag _ _ _ ety  <;>
        simp [type_of_after_lifted_is_lifted]
        · simp [heq₁, CedarType.liftBoolTypes]
        · simp [heq₂, CedarType.liftBoolTypes]
      case _ =>
        split at h₃₁ <;> {
          simp [ok] at h₃₁
          rcases h₃₁ with ⟨h₃₁, _⟩
          subst h₃₁
          simp [CedarType.liftBoolTypes, BoolType.lift]
          apply @BinaryOp.WellTyped.hasTag _ _ _ ety  <;>
          simp [type_of_after_lifted_is_lifted]
          · simp [heq₁, CedarType.liftBoolTypes]
          · simp [heq₂, CedarType.liftBoolTypes]
        }
      case _ =>
        split at h₃₁
        case _ =>
          simp [ok] at h₃₁
          rcases h₃₁ with ⟨h₃₁, _⟩
          subst h₃₁
          simp [CedarType.liftBoolTypes, BoolType.lift]
          apply @BinaryOp.WellTyped.hasTag _ _ _ ety  <;>
          simp [type_of_after_lifted_is_lifted]
          · simp [heq₁, CedarType.liftBoolTypes]
          · simp [heq₂, CedarType.liftBoolTypes]
        case _ => simp [err] at h₃₁
  case _ ety heq₁ heq₂ =>
    simp [ok, do_ok_eq_ok] at h₃
    rcases h₃ with ⟨a, h₃₁, h₃₂⟩
    subst h₃₂
    simp [typeOfGetTag] at h₃₁
    split at h₃₁
    case _ => simp [err] at h₃₁
    case _ ty' heq₃ =>
      split at h₃₁
      case _ =>
        simp [ok] at h₃₁
        rcases h₃₁ with ⟨h₃₁, _⟩
        simp [TypedExpr.liftBoolTypes]
        subst h₃₁
        constructor
        · exact hᵢ₁ hᵢ₁'
        · exact hᵢ₂ hᵢ₂'
        · apply @BinaryOp.WellTyped.getTag _ _ _ ety ty' <;>
          try simp [type_of_after_lifted_is_lifted]
          · simp [heq₁, CedarType.liftBoolTypes]
          · simp [heq₂, CedarType.liftBoolTypes]
          · exact heq₃
      case _ => simp [err] at h₃₁
    case _ => simp [err] at h₃₁
  case _ heq₁ heq₂ =>
    simp [ok] at h₃
    rcases h₃ with ⟨h₃, _⟩
    subst h₃
    simp [TypedExpr.liftBoolTypes, CedarType.liftBoolTypes, BoolType.lift]
    constructor
    · exact hᵢ₁ hᵢ₁'
    · exact hᵢ₂ hᵢ₂'
    · constructor <;> simp [type_of_after_lifted_is_lifted]
      · simp [heq₁, CedarType.liftBoolTypes]
      · simp [heq₂, CedarType.liftBoolTypes]
  case _ heq₁ heq₂ =>
    simp [ok] at h₃
    rcases h₃ with ⟨h₃, _⟩
    subst h₃
    simp [TypedExpr.liftBoolTypes, CedarType.liftBoolTypes, BoolType.lift]
    constructor
    · exact hᵢ₁ hᵢ₁'
    · exact hᵢ₂ hᵢ₂'
    · apply BinaryOp.WellTyped.less_datetime <;> simp [type_of_after_lifted_is_lifted]
      · simp [heq₁, CedarType.liftBoolTypes]
      · simp [heq₂, CedarType.liftBoolTypes]
  case _ heq₁ heq₂ =>
    simp [ok] at h₃
    rcases h₃ with ⟨h₃, _⟩
    subst h₃
    simp [TypedExpr.liftBoolTypes, CedarType.liftBoolTypes, BoolType.lift]
    constructor
    · exact hᵢ₁ hᵢ₁'
    · exact hᵢ₂ hᵢ₂'
    · apply BinaryOp.WellTyped.less_duration <;> simp [type_of_after_lifted_is_lifted]
      · simp [heq₁, CedarType.liftBoolTypes]
      · simp [heq₂, CedarType.liftBoolTypes]
  case _ heq₁ heq₂ =>
      simp [ok] at h₃
      rcases h₃ with ⟨h₃, _⟩
      subst h₃
      simp [TypedExpr.liftBoolTypes, CedarType.liftBoolTypes, BoolType.lift]
      constructor
      · exact hᵢ₁ hᵢ₁'
      · exact hᵢ₂ hᵢ₂'
      · constructor <;> simp [type_of_after_lifted_is_lifted]
        · simp [heq₁, CedarType.liftBoolTypes]
        · simp [heq₂, CedarType.liftBoolTypes]
  case _ heq₁ heq₂ =>
    simp [ok] at h₃
    rcases h₃ with ⟨h₃, _⟩
    subst h₃
    simp [TypedExpr.liftBoolTypes, CedarType.liftBoolTypes, BoolType.lift]
    constructor
    · exact hᵢ₁ hᵢ₁'
    · exact hᵢ₂ hᵢ₂'
    · apply BinaryOp.WellTyped.lessEq_datetime <;> simp [type_of_after_lifted_is_lifted]
      · simp [heq₁, CedarType.liftBoolTypes]
      · simp [heq₂, CedarType.liftBoolTypes]
  case _ heq₁ heq₂ =>
    simp [ok] at h₃
    rcases h₃ with ⟨h₃, _⟩
    subst h₃
    simp [TypedExpr.liftBoolTypes, CedarType.liftBoolTypes, BoolType.lift]
    constructor
    · exact hᵢ₁ hᵢ₁'
    · exact hᵢ₂ hᵢ₂'
    · apply BinaryOp.WellTyped.lessEq_duration <;> simp [type_of_after_lifted_is_lifted]
      · simp [heq₁, CedarType.liftBoolTypes]
      · simp [heq₂, CedarType.liftBoolTypes]
  case _ heq₁ heq₂ =>
    simp [ok] at h₃
    rcases h₃ with ⟨h₃, _⟩
    subst h₃
    simp only [TypedExpr.liftBoolTypes, CedarType.liftBoolTypes]
    constructor
    · exact hᵢ₁ hᵢ₁'
    · exact hᵢ₂ hᵢ₂'
    · constructor <;> simp [type_of_after_lifted_is_lifted]
      · simp [heq₁, CedarType.liftBoolTypes]
      · simp [heq₂, CedarType.liftBoolTypes]
  case _ heq₁ heq₂ =>
    simp [ok] at h₃
    rcases h₃ with ⟨h₃, _⟩
    subst h₃
    simp only [TypedExpr.liftBoolTypes, CedarType.liftBoolTypes]
    constructor
    · exact hᵢ₁ hᵢ₁'
    · exact hᵢ₂ hᵢ₂'
    · constructor <;> simp [type_of_after_lifted_is_lifted]
      · simp [heq₁, CedarType.liftBoolTypes]
      · simp [heq₂, CedarType.liftBoolTypes]
  case _ heq₁ heq₂ =>
    simp [ok] at h₃
    rcases h₃ with ⟨h₃, _⟩
    subst h₃
    simp only [TypedExpr.liftBoolTypes, CedarType.liftBoolTypes]
    constructor
    · exact hᵢ₁ hᵢ₁'
    · exact hᵢ₂ hᵢ₂'
    · constructor <;> simp [type_of_after_lifted_is_lifted]
      · simp [heq₁, CedarType.liftBoolTypes]
      · simp [heq₂, CedarType.liftBoolTypes]
  case _ heq =>
    simp [ok, do_ok_eq_ok] at h₃
    rcases h₃ with ⟨a, h₃₁, h₃₂⟩
    subst h₃₂
    simp [TypedExpr.liftBoolTypes]
    simp [ifLubThenBool] at h₃₁
    split at h₃₁
    case _ heq₁ =>
      simp [ok] at h₃₁
      rcases h₃₁ with ⟨h₃₁, _⟩
      subst h₃₁
      simp [CedarType.liftBoolTypes, BoolType.lift]
      constructor
      · exact hᵢ₁ hᵢ₁'
      · exact hᵢ₂ hᵢ₂'
      · constructor
        simp [type_of_after_lifted_is_lifted, heq, CedarType.liftBoolTypes]
        symm
        exact lifted_type_lub heq₁
    case _ => simp [err] at h₃₁
  case _ =>
    simp [ok, do_ok_eq_ok] at h₃
    rcases h₃ with ⟨a, h₃₁, h₃₂⟩
    subst h₃₂
    simp [TypedExpr.liftBoolTypes]
    simp [ifLubThenBool] at h₃₁
    split at h₃₁
    case _ ty' heq₁ heq₂ _ _ heq₃ =>
      simp [ok] at h₃₁
      rcases h₃₁ with ⟨h₃₁, _⟩
      subst h₃₁
      simp [CedarType.liftBoolTypes, BoolType.lift]
      constructor
      · exact hᵢ₁ hᵢ₁'
      · exact hᵢ₂ hᵢ₂'
      · apply @BinaryOp.WellTyped.containsAll _ _ _ ty'.liftBoolTypes <;>
        simp [type_of_after_lifted_is_lifted, heq₁, heq₂, CedarType.liftBoolTypes]
        exact lifted_type_lub heq₃
    case _ => simp [err] at h₃₁
  case _ =>
    simp [ok, do_ok_eq_ok] at h₃
    rcases h₃ with ⟨a, h₃₁, h₃₂⟩
    subst h₃₂
    simp [TypedExpr.liftBoolTypes]
    simp [ifLubThenBool] at h₃₁
    split at h₃₁
    case _ ty' heq₁ heq₂ _ _ heq₃ =>
      simp [ok] at h₃₁
      rcases h₃₁ with ⟨h₃₁, _⟩
      subst h₃₁
      simp [CedarType.liftBoolTypes, BoolType.lift]
      constructor
      · exact hᵢ₁ hᵢ₁'
      · exact hᵢ₂ hᵢ₂'
      · apply @BinaryOp.WellTyped.containsAny _ _ _ ty'.liftBoolTypes <;>
        simp [type_of_after_lifted_is_lifted, heq₁, heq₂, CedarType.liftBoolTypes]
        exact lifted_type_lub heq₃
    case _ => simp [err] at h₃₁
  case _ => simp [err] at h₃

theorem typechecked_is_well_typed_after_lifting_has_attr
{x₁ : Expr}
{c₁ c₂ : Capabilities}
{env : TypeEnv}
{ty : TypedExpr}
{attr : Attr}
(hᵢ₁ : ∀ {c₂ : Capabilities} {ty : TypedExpr},
    typeOf x₁ c₁ env = Except.ok (ty, c₂) → TypedExpr.WellTyped env ty.liftBoolTypes) :
  typeOf (x₁.hasAttr attr) c₁ env = Except.ok (ty, c₂) → TypedExpr.WellTyped env ty.liftBoolTypes
:= by
  intro h₃
  simp only [typeOf] at h₃
  generalize hᵢ : typeOf x₁ c₁ env = res₁
  cases res₁ <;> simp [hᵢ] at h₃
  simp [typeOfHasAttr] at h₃
  split at h₃
  case _ rty heq =>
    simp only [ok, do_ok_eq_ok, Prod.mk.injEq, Prod.exists, exists_eq_right_right] at h₃
    rcases h₃ with ⟨_, h₃₁, h₃₂⟩
    subst h₃₂
    simp only [TypedExpr.liftBoolTypes]
    simp only [hasAttrInRecord, Bool.and_true, Bool.or_eq_true, decide_eq_true_eq,
      List.empty_eq] at h₃₁
    split at h₃₁
    · split at h₃₁ <;>
      {
        simp [ok] at h₃₁
        rcases h₃₁ with ⟨h₃₁, _⟩
        subst h₃₁
        simp [CedarType.liftBoolTypes, BoolType.lift]
        apply @TypedExpr.WellTyped.hasAttr_record env (RecordType.liftBoolTypes rty)
        · exact hᵢ₁ hᵢ
        · simp [type_of_after_lifted_is_lifted, heq, CedarType.liftBoolTypes, RecordType.liftBoolTypes]
      }
    · simp only [ok, Except.ok.injEq, Prod.mk.injEq, List.nil_eq] at h₃₁
      rcases h₃₁ with ⟨h₃₁, _⟩
      subst h₃₁
      simp [CedarType.liftBoolTypes, BoolType.lift]
      apply @TypedExpr.WellTyped.hasAttr_record env (RecordType.liftBoolTypes rty)
      · exact hᵢ₁ hᵢ
      · simp [type_of_after_lifted_is_lifted, heq, CedarType.liftBoolTypes, RecordType.liftBoolTypes]
  case _ ety heq =>
    split at h₃
    case _ =>
      simp only [ok, do_ok_eq_ok, Prod.mk.injEq, Prod.exists, exists_eq_right_right] at h₃
      rcases h₃ with ⟨_, h₃₁, h₃₂⟩
      subst h₃₂
      simp only [TypedExpr.liftBoolTypes]
      simp only [hasAttrInRecord, Bool.and_false, Bool.or_false, decide_eq_true_eq,
        List.empty_eq] at h₃₁
      split at h₃₁
      · split at h₃₁ <;>
      {
        simp [ok] at h₃₁
        rcases h₃₁ with ⟨h₃₁, _⟩
        subst h₃₁
        simp [CedarType.liftBoolTypes, BoolType.lift]
        apply @TypedExpr.WellTyped.hasAttr_entity env ety
        · exact hᵢ₁ hᵢ
        · simp only [type_of_after_lifted_is_lifted, heq, CedarType.liftBoolTypes]
      }
      · simp only [ok, Except.ok.injEq, Prod.mk.injEq, List.nil_eq] at h₃₁
        rcases h₃₁ with ⟨h₃₁, _⟩
        subst h₃₁
        simp only [CedarType.liftBoolTypes, BoolType.lift]
        apply @TypedExpr.WellTyped.hasAttr_entity env ety
        · exact hᵢ₁ hᵢ
        · simp only [type_of_after_lifted_is_lifted, heq, CedarType.liftBoolTypes]
    case _ =>
      split at h₃
      · simp only [ok, Except.ok.injEq, Prod.mk.injEq, List.nil_eq] at h₃
        rcases h₃ with ⟨h₃₁, h₃₂⟩
        subst h₃₁
        simp [TypedExpr.liftBoolTypes, CedarType.liftBoolTypes, BoolType.lift]
        apply @TypedExpr.WellTyped.hasAttr_entity env ety
        · exact hᵢ₁ hᵢ
        · simp only [type_of_after_lifted_is_lifted, heq, CedarType.liftBoolTypes]
      · simp only [err, reduceCtorEq] at h₃
  case _ => simp only [err, reduceCtorEq] at h₃

private theorem typeOfHasAttr_ok_implies_entity_or_record
{ty₁ : TypedExpr} {x₁ : Expr} {a : Attr} {c : Capabilities} {env : TypeEnv} {r : TypedExpr × Capabilities} :
  typeOfHasAttr ty₁ x₁ a c env = .ok r →
  (∃ ety, ty₁.typeOf = .entity ety) ∨ (∃ rty, ty₁.typeOf = .record rty)
:= by
  intro h
  simp only [typeOfHasAttr] at h
  split at h
  case h_1 rty heq => exact Or.inr ⟨rty, heq⟩
  case h_2 ety heq => exact Or.inl ⟨ety, heq⟩
  case h_3 => simp only [err, reduceCtorEq] at h

private theorem qualifiedType_liftBoolTypes_getType (qty : QualifiedType) :
  (QualifiedType.liftBoolTypes qty).getType = qty.getType.liftBoolTypes := by
  cases qty <;> simp [QualifiedType.liftBoolTypes, Qualified.getType]

private theorem typeOfGetAttr_entity_ok_implies
  {ty₁ : TypedExpr} {x₁ : Expr} {attr : Attr} {c : Capabilities} {env : TypeEnv}
  {tyNext : TypedExpr} {cga : Capabilities} {ety : EntityType}
  (hga : typeOfGetAttr ty₁ x₁ attr c env = .ok (tyNext, cga))
  (hety : ty₁.typeOf = .entity ety) :
  ∃ rty qty, env.ets.attrs? ety = .some rty ∧ rty.find? attr = .some qty ∧ tyNext.typeOf = qty.getType := by
  unfold typeOfGetAttr at hga
  rw [hety] at hga
  simp only [bind, Except.bind] at hga
  split at hga
  case h_1 rty hschema =>
    -- hga : (match getAttrInRecord ... with ...) = .ok (tyNext, cga)
    split at hga
    case h_1 => simp at hga  -- .error case
    case h_2 val hgir =>
      -- getAttrInRecord succeeded with val
      simp [ok] at hga
      obtain ⟨heq, _⟩ := hga
      -- Now extract from hgir: getAttrInRecord (.entity ety) rty x₁ attr c = .ok val
      simp only [getAttrInRecord] at hgir
      split at hgir
      case h_1 aty hfind =>
        simp [ok] at hgir
        have hval : val = (aty, ∅) := by exact hgir.symm
        rw [hval] at heq
        simp at heq
        exact ⟨rty, .required aty, hschema, hfind, by rw [← heq]; simp [TypedExpr.typeOf, Qualified.getType]⟩
      case h_2 aty hfind =>
        split at hgir
        · simp [ok] at hgir
          have hval : val = (aty, ∅) := by exact hgir.symm
          rw [hval] at heq
          simp at heq
          exact ⟨rty, .optional aty, hschema, hfind, by rw [← heq]; simp [TypedExpr.typeOf, Qualified.getType]⟩
        · simp [err] at hgir
      case h_3 => simp [err] at hgir
  case h_2 => simp [err] at hga

private theorem typeOfGetAttr_record_ok_implies
  {ty₁ : TypedExpr} {x₁ : Expr} {attr : Attr} {c : Capabilities} {env : TypeEnv}
  {tyNext : TypedExpr} {cga : Capabilities} {rty : RecordType}
  (hga : typeOfGetAttr ty₁ x₁ attr c env = .ok (tyNext, cga))
  (hrty : ty₁.typeOf = .record rty) :
  ∃ qty, rty.find? attr = .some qty ∧ tyNext.typeOf = qty.getType := by
  unfold typeOfGetAttr at hga
  rw [hrty] at hga
  simp only [bind, Except.bind] at hga
  split at hga
  case h_1 => simp at hga  -- .error case
  case h_2 val hgir =>
    simp [ok] at hga
    obtain ⟨heq, _⟩ := hga
    simp only [getAttrInRecord] at hgir
    split at hgir
    case h_1 aty hfind =>
      simp [ok] at hgir
      have hval : val = (aty, ∅) := by exact hgir.symm
      rw [hval] at heq; simp at heq
      exact ⟨.required aty, hfind, by rw [← heq]; simp [TypedExpr.typeOf, Qualified.getType]⟩
    case h_2 aty hfind =>
      split at hgir
      · simp [ok] at hgir
        have hval : val = (aty, ∅) := by exact hgir.symm
        rw [hval] at heq; simp at heq
        exact ⟨.optional aty, hfind, by rw [← heq]; simp [TypedExpr.typeOf, Qualified.getType]⟩
      · simp [err] at hgir
    case h_3 => simp [err] at hgir

theorem typeOfExtHasAttr_tyNext_type_entity_or_record
  {tyNext : TypedExpr} {x₁ : Expr} {b : Attr} {rest : List Attr}
  {c : Capabilities} {env : TypeEnv} {res : BoolType × Capabilities}
  (hrec : typeOfExtHasAttr tyNext x₁ (b :: rest) c env = .ok res) :
  (∃ ety, tyNext.typeOf = .entity ety) ∨ (∃ rty, tyNext.typeOf = .record rty) := by
  cases rest with
  | nil =>
    simp only [typeOfExtHasAttr, bind, Except.bind] at hrec
    generalize hha : typeOfHasAttr tyNext x₁ b c env = resHA at hrec
    cases resHA with
    | error => simp at hrec
    | ok val => exact typeOfHasAttr_ok_implies_entity_or_record hha
  | cons c' more =>
    -- After the change, typeOfExtHasAttr for (b :: c' :: more) starts with typeOfHasAttr
    simp only [typeOfExtHasAttr, bind, Except.bind] at hrec
    generalize hha : typeOfHasAttr tyNext x₁ b c env = resHA at hrec
    cases resHA with
    | error => simp at hrec
    | ok val => exact typeOfHasAttr_ok_implies_entity_or_record hha

private theorem typeOfHasAttr_ff_implies_attr_not_found
  {ty₁ : TypedExpr} {x₁ : Expr} {attr : Attr} {c : Capabilities} {env : TypeEnv}
  {tyHas : TypedExpr} {ci : Capabilities}
  (hha : typeOfHasAttr ty₁ x₁ attr c env = .ok (tyHas, ci))
  (hety : ty₁.typeOf = .entity ety)
  (hff : tyHas.typeOf = .bool .ff) :
  env.ets.attrs? ety = .none ∨ ∀ rty, env.ets.attrs? ety = .some rty → rty.find? attr = .none := by
  simp only [typeOfHasAttr, hety, bind, Except.bind] at hha
  split at hha
  case h_1 rty hattrs =>
    -- env.ets.attrs? ety = .some rty — need to show rty.find? attr = .none
    right; intro rty' hrty'
    have hrty_eq : rty = rty' := by rw [hattrs] at hrty'; exact Option.some.inj hrty'
    subst hrty_eq
    simp only [hasAttrInRecord] at hha
    split at hha
    · simp at hha
    · rename_i v heq
      simp only [ok, Except.ok.injEq, Prod.mk.injEq] at hha
      obtain ⟨hty_eq, _⟩ := hha
      split at heq
      case h_1 qty hfind =>
        split at heq <;> {
          simp only [ok, Except.ok.injEq] at heq
          subst heq; simp [TypedExpr.typeOf, ← hty_eq] at hff
        }
      case h_2 hfind => exact hfind
  case h_2 hattrs =>
    -- env.ets.attrs? ety = .none
    exact Or.inl hattrs

private theorem typeOfHasAttr_ff_implies_record_attr_not_found
  {ty₁ : TypedExpr} {x₁ : Expr} {attr : Attr} {c : Capabilities} {env : TypeEnv}
  {tyHas : TypedExpr} {ci : Capabilities}
  (hha : typeOfHasAttr ty₁ x₁ attr c env = .ok (tyHas, ci))
  (hrty : ty₁.typeOf = .record rty)
  (hff : tyHas.typeOf = .bool .ff) :
  rty.find? attr = .none := by
  simp only [typeOfHasAttr, hrty, bind, Except.bind] at hha
  simp only [hasAttrInRecord] at hha
  split at hha
  · simp at hha
  · rename_i v heq
    simp only [ok, Except.ok.injEq, Prod.mk.injEq] at hha
    obtain ⟨hty_eq, _⟩ := hha
    split at heq
    case h_1 qty hfind =>
      -- rty.find? attr = .some qty → result is .tt or .anyBool, contradicts hff
      split at heq <;> {
        simp only [ok, Except.ok.injEq] at heq
        subst heq
        simp [TypedExpr.typeOf, ← hty_eq] at hff
      }
    case h_2 hfind =>
      exact hfind

private theorem typeOfExtHasAttr_implies_chain_valid
  {ty₁ : TypedExpr} {x₁ : Expr} {attr : Attr} {attrs : List Attr}
  {c : Capabilities} {env : TypeEnv} {res : BoolType × Capabilities}
  (h : typeOfExtHasAttr ty₁ x₁ (attr :: attrs) c env = .ok res) :
  (∀ ety, ty₁.typeOf = .entity ety → ExtHasAttrChainValid env.ets (.entity ety) (attr :: attrs)) ∧
  (∀ rty, ty₁.typeOf = .record rty → ExtHasAttrChainValid env.ets (.record rty) (attr :: attrs)) := by
  induction attrs generalizing ty₁ x₁ attr c res with
  | nil =>
    constructor
    · intro ety _; exact ExtHasAttrChainValid.last
    · intro rty _; exact ExtHasAttrChainValid.last
  | cons b rest ih =>
    simp only [typeOfExtHasAttr, bind, Except.bind] at h
    -- typeOfHasAttr ty₁ x₁ attr c env must succeed (first in the new structure)
    generalize hha : typeOfHasAttr ty₁ x₁ attr c env = resHA at h
    cases resHA with
    | error => simp at h
    | ok valHA =>
      obtain ⟨tyHas, ci⟩ := valHA
      simp only at h
      -- Split on tyHas.typeOf to handle the match
      split at h
      case h_1 hff =>
        -- tyHas.typeOf = .bool .ff: intermediate attr definitely missing → vacuously valid
        simp only [Except.ok.injEq] at h
        constructor
        · intro ety hety
          have hnotfound := typeOfHasAttr_ff_implies_attr_not_found hha hety hff
          exact .cons_not_in_schema_entity hnotfound
        · intro rty hrty
          have hnotfound := typeOfHasAttr_ff_implies_record_attr_not_found hha hrty hff
          exact .cons_not_in_record hnotfound
      case h_2 hnotff =>
        -- Normal case: proceed to typeOfGetAttr
        generalize hga : typeOfGetAttr ty₁ x₁ attr (c ∪ ci) env = resGA at h
        cases resGA with
        | error => simp at h
        | ok valGA =>
          obtain ⟨tyNext, cga⟩ := valGA
          simp only at h
          generalize hrec : typeOfExtHasAttr tyNext (Expr.getAttr x₁ attr) (b :: rest) (c ∪ ci) env = resRec at h
          cases resRec with
          | error => simp at h
          | ok valRec =>
            -- The final match on tyHas.typeOf (for .tt vs other) doesn't affect chain validity
            have hrec_ok : ∃ r, typeOfExtHasAttr tyNext (Expr.getAttr x₁ attr) (b :: rest) (c ∪ ci) env = .ok r :=
              ⟨valRec, hrec⟩
            have ihResult := ih hrec
            have htyNext_ety_or_rty := typeOfExtHasAttr_tyNext_type_entity_or_record hrec
            constructor
            · intro ety hety
              have ⟨rty_schema, qty, hschema, hfind, htyNext⟩ := typeOfGetAttr_entity_ok_implies hga hety
              rcases htyNext_ety_or_rty with ⟨nextEty, hnext⟩ | ⟨nextRty, hnext⟩
              · have hqtyType : qty.getType = .entity nextEty := by rw [← htyNext]; exact hnext
                exact .cons_entity hschema hfind hqtyType (ihResult.1 nextEty hnext)
              · have hqtyType : qty.getType = .record nextRty := by rw [← htyNext]; exact hnext
                exact .cons_record_from_entity hschema hfind hqtyType (ihResult.2 nextRty hnext)
            · intro rty hrty
              have ⟨qty, hfind, htyNext⟩ := typeOfGetAttr_record_ok_implies hga hrty
              rcases htyNext_ety_or_rty with ⟨nextEty, hnext⟩ | ⟨nextRty, hnext⟩
              · have hqtyType : qty.getType = .entity nextEty := by rw [← htyNext]; exact hnext
                exact .cons_entity_from_record hfind hqtyType (ihResult.1 nextEty hnext)
              · have hqtyType : qty.getType = .record nextRty := by rw [← htyNext]; exact hnext
                exact .cons_record_from_record hfind hqtyType (ihResult.2 nextRty hnext)



private theorem ExtHasAttrChainValid_liftBoolTypes_entity
  {ets : EntitySchema} {ety : EntityType} {attrs : List Attr}
  (h : ExtHasAttrChainValid ets (.entity ety) attrs) :
  ExtHasAttrChainValid ets (.entity ety) attrs := h

private theorem ExtHasAttrChainValid_liftBoolTypes_record
  {ets : EntitySchema} {rty : RecordType} {attrs : List Attr}
  (h : ExtHasAttrChainValid ets (.record rty) attrs) :
  ExtHasAttrChainValid ets (.record (RecordType.liftBoolTypes rty)) attrs := by
  generalize hty_eq : CedarType.record rty = ty at h
  induction h generalizing rty with
  | last => exact ExtHasAttrChainValid.last
  | cons_entity_from_record h₁ h₂ h₃ _ =>
    cases hty_eq
    exact ExtHasAttrChainValid.cons_entity_from_record
      (by rw [lift_bool_types_record_eq_map_on_values]; exact Data.Map.find?_mapOnValues_some QualifiedType.liftBoolTypes h₁)
      (by rw [qualifiedType_liftBoolTypes_getType]; simp [h₂, CedarType.liftBoolTypes])
      h₃
  | cons_record_from_record h₁ h₂ _ ih =>
    cases hty_eq
    exact ExtHasAttrChainValid.cons_record_from_record
      (by rw [lift_bool_types_record_eq_map_on_values]; exact Data.Map.find?_mapOnValues_some QualifiedType.liftBoolTypes h₁)
      (by rw [qualifiedType_liftBoolTypes_getType]; simp [h₂, CedarType.liftBoolTypes])
      (ih rfl)
  | cons_not_in_record h₁ =>
    cases hty_eq
    exact ExtHasAttrChainValid.cons_not_in_record
      (by rw [lift_bool_types_record_eq_map_on_values]; exact (Data.Map.find?_mapOnValues_none QualifiedType.liftBoolTypes).mpr h₁)
  | cons_entity _ _ _ _ => cases hty_eq
  | cons_record_from_entity _ _ _ _ => cases hty_eq
  | cons_not_in_schema_entity _ => cases hty_eq


theorem typechecked_is_well_typed_after_lifting_ext_has_attr
{x₁ : Expr}
{c₁ c₂ : Capabilities}
{env : TypeEnv}
{ty : TypedExpr}
{attr : Attr}
{attrs : List Attr}
(hᵢ₁ : ∀ {c₂ : Capabilities} {ty : TypedExpr},
    typeOf x₁ c₁ env = Except.ok (ty, c₂) → TypedExpr.WellTyped env ty.liftBoolTypes) :
  typeOf (x₁.extHasAttr attr attrs) c₁ env = Except.ok (ty, c₂) → TypedExpr.WellTyped env ty.liftBoolTypes
:= by
  intro h₃
  simp only [typeOf] at h₃
  generalize hᵢ : typeOf x₁ c₁ env = res₁ at h₃
  cases res₁ <;> simp only [ExceptT.stM_eq, Except.bind_err, reduceCtorEq] at h₃
  rename_i val₁
  have ⟨ty₁, c₁'⟩ := val₁
  simp only [bind, Except.bind] at h₃
  generalize hext : typeOfExtHasAttr ty₁ x₁ (attr :: attrs) c₁ env = res₂ at h₃
  cases res₂ <;> simp [ok] at h₃
  obtain ⟨hty_eq, _⟩ := h₃
  subst hty_eq
  simp only [TypedExpr.liftBoolTypes, CedarType.liftBoolTypes, BoolType.lift]
  have hwt₁ := hᵢ₁ hᵢ
  -- typeOfExtHasAttr on (attr :: attrs) implies typeOfHasAttr ty₁ x₁ attr succeeds
  -- (it's always the first operation in the function for non-empty lists)
  have hha : ∃ r, typeOfHasAttr ty₁ x₁ attr c₁ env = .ok r := by
    have h := hext
    cases attrs with
    | nil =>
      simp only [typeOfExtHasAttr, bind, Except.bind] at h
      split at h <;> simp_all
    | cons attr₂ rest =>
      simp only [typeOfExtHasAttr, bind, Except.bind] at h
      split at h <;> simp_all
  obtain ⟨⟨_, _⟩, hha⟩ := hha
  have hety_or_rty := typeOfHasAttr_ok_implies_entity_or_record hha
  have hchain_valid := typeOfExtHasAttr_implies_chain_valid hext
  rcases hety_or_rty with ⟨ety, hety⟩ | ⟨rty, hrty⟩
  · have hlift : ty₁.liftBoolTypes.typeOf = .entity ety := by
      simp [type_of_after_lifted_is_lifted, hety, CedarType.liftBoolTypes]
    apply @TypedExpr.WellTyped.extHasAttr_ff env
    · exact hwt₁
    · exact Or.inl ⟨ety, hlift⟩
    · rw [hlift]; exact hchain_valid.1 ety hety
  · have hlift : ty₁.liftBoolTypes.typeOf = .record (RecordType.liftBoolTypes rty) := by
      simp [type_of_after_lifted_is_lifted, hrty, CedarType.liftBoolTypes]
    apply @TypedExpr.WellTyped.extHasAttr_ff env
    · exact hwt₁
    · exact Or.inr ⟨RecordType.liftBoolTypes rty, hlift⟩
    · rw [hlift]; exact ExtHasAttrChainValid_liftBoolTypes_record (hchain_valid.2 rty hrty)

theorem typechecked_is_well_typed_after_lifting_get_attr_in_record
{x₁ : Expr}
{c₁ c₂ : Capabilities}
{attr : Attr}
{tc : TypedExpr × Capabilities}
{rty : Data.Map Attr (Qualified CedarType)}
{a : CedarType}
(h₃ : getAttrInRecord tc.fst.typeOf rty x₁ attr c₁ = Except.ok (a, c₂)) :
  Option.map Qualified.getType ((RecordType.liftBoolTypes rty).find? attr) = some a.liftBoolTypes
:= by
  simp
  simp [getAttrInRecord] at h₃
  split at h₃ <;> try
  {
    rename_i aty heq₁
    simp [ok] at h₃
    rcases h₃ with ⟨h₃, _⟩
    exists QualifiedType.liftBoolTypes (.required aty)
    apply And.intro
    · simp [lift_bool_types_record_eq_map_on_values,
        Data.Map.find?_mapOnValues_some QualifiedType.liftBoolTypes heq₁]
    · subst h₃
      simp [QualifiedType.liftBoolTypes, Qualified.getType]
  }
  case _ =>
    split at h₃
    case _ aty heq₁ _ =>
      simp [ok] at h₃
      rcases h₃ with ⟨h₃, _⟩
      exists QualifiedType.liftBoolTypes (.optional aty)
      apply And.intro
      · simp [lift_bool_types_record_eq_map_on_values,
        Data.Map.find?_mapOnValues_some QualifiedType.liftBoolTypes heq₁]
      · subst h₃
        simp [QualifiedType.liftBoolTypes, Qualified.getType]
    case _ => simp [err] at h₃
  case _ => simp [err] at h₃

theorem typechecked_is_well_typed_after_lifting_get_attr
{x₁ : Expr}
{c₁ c₂ : Capabilities}
{env : TypeEnv}
{ty : TypedExpr}
{attr : Attr}
(hᵢ₁ : ∀ {c₂ : Capabilities} {ty : TypedExpr},
    typeOf x₁ c₁ env = Except.ok (ty, c₂) → TypedExpr.WellTyped env ty.liftBoolTypes) :
  typeOf (x₁.getAttr attr) c₁ env = Except.ok (ty, c₂) → TypedExpr.WellTyped env ty.liftBoolTypes
:= by
  intro h₃
  simp only [typeOf] at h₃
  generalize hᵢ : typeOf x₁ c₁ env = res₁
  cases res₁
  case error => simp [hᵢ] at h₃
  case ok tc =>
    simp only [hᵢ, typeOfGetAttr, Except.bind_ok] at h₃
    split at h₃
    case _ rty heq =>
      simp [ok, do_ok_eq_ok] at h₃
      rcases h₃ with ⟨a, h₃₁, h₃₂⟩
      subst h₃₂
      simp only [TypedExpr.liftBoolTypes]
      apply @TypedExpr.WellTyped.getAttr_record _ (RecordType.liftBoolTypes rty)
      · exact hᵢ₁ hᵢ
      · simp only [type_of_after_lifted_is_lifted, heq, CedarType.liftBoolTypes,
        RecordType.liftBoolTypes]
      · exact typechecked_is_well_typed_after_lifting_get_attr_in_record h₃₁
    case _ ety heq =>
      split at h₃
      case _ rty heq₁ =>
        simp [ok, do_ok_eq_ok] at h₃
        rcases h₃ with ⟨a, h₃₁, h₃₂⟩
        subst h₃₂
        simp [TypedExpr.liftBoolTypes]
        apply @TypedExpr.WellTyped.getAttr_entity _ ety (RecordType.liftBoolTypes rty)
        · exact hᵢ₁ hᵢ
        · simp [type_of_after_lifted_is_lifted, heq, CedarType.liftBoolTypes]
        · simp [heq₁, RecordType.liftBoolTypes]
        · exact typechecked_is_well_typed_after_lifting_get_attr_in_record h₃₁
      case _ => simp [err] at h₃
    case _ => simp [err] at h₃

theorem typechecked_is_well_typed_after_lifting_call_arg
{c₁: Capabilities}
{env : TypeEnv}
{xs : List Expr}
{tys : List TypedExpr}
(hᵢ : List.Forall₂ (fun x y => justType (typeOf x c₁ env) = Except.ok y) xs tys)
(hᵢ₁ : ∀ (x₁ : Expr),
  x₁ ∈ xs →
    ∀ {c₂ : Capabilities} {ty : TypedExpr},
        typeOf x₁ c₁ env = Except.ok (ty, c₂) → TypedExpr.WellTyped env ty.liftBoolTypes) :
  ∀ (x : TypedExpr), (x ∈ tys.map₁ fun x => x.val.liftBoolTypes) → TypedExpr.WellTyped env x
:= by
  simp only [List.map₁_eq_map, List.mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
  intro a h
  rcases List.forall₂_implies_all_right hᵢ a h with ⟨_, h₅, h₄⟩
  simp only [justType, Except.map] at h₄
  split at h₄
  case _ => cases h₄
  case _ e _ v heq =>
    simp only [Except.ok.injEq] at h₄
    have : v = (v.fst, v.snd) := by rfl
    rw [this, h₄] at heq
    exact hᵢ₁ e h₅ heq

theorem typechecked_is_well_typed_after_lifting_call
{c₁ c₂ : Capabilities}
{env : TypeEnv}
{ty : TypedExpr}
{xfn : ExtFun}
{xs : List Expr}
(hᵢ₁ : ∀ (x₁ : Expr),
  x₁ ∈ xs →
    ∀ {c₂ : Capabilities} {ty : TypedExpr},
        typeOf x₁ c₁ env = Except.ok (ty, c₂) → TypedExpr.WellTyped env ty.liftBoolTypes) :
  typeOf (Expr.call xfn xs) c₁ env = Except.ok (ty, c₂) → TypedExpr.WellTyped env ty.liftBoolTypes
:= by
  intro h₃
  simp [typeOf] at h₃
  simp [List.mapM₁_eq_mapM (λ x => justType (typeOf x c₁ env))] at h₃
  generalize hᵢ : List.mapM (fun x => justType (typeOf x c₁ env)) xs = res₁
  cases res₁ <;> simp [hᵢ] at h₃
  simp [List.mapM_ok_iff_forall₂] at hᵢ
  simp [typeOfCall] at h₃
  split at h₃ <;>
  simp [err, ok, do_ok_eq_ok] at h₃
  · rcases h₃ with ⟨_, h₃₁, h₃₂⟩
    subst h₃₂
    simp only [TypedExpr.liftBoolTypes]
    apply TypedExpr.WellTyped.call
    · exact typechecked_is_well_typed_after_lifting_call_arg hᵢ hᵢ₁
    · --TODO: abstract this
      simp [typeOfConstructor] at h₃₁
      split at h₃₁ <;> simp [err] at h₃₁
      · split at h₃₁ <;> try simp at h₃₁
        · rename_i heq
          simp [ok] at h₃₁
          rcases h₃₁ with ⟨h₃₁, _⟩
          subst h₃₁
          simp [CedarType.liftBoolTypes, List.map₁_eq_map]
          cases hᵢ
          · rename_i heq₁
            cases heq₁
            rename_i heq₂
            simp [typeOf, typeOfLit, ok, justType, Except.map] at heq₂
            subst heq₂
            simp [TypedExpr.liftBoolTypes, CedarType.liftBoolTypes]
            symm at heq
            exact ExtFun.WellTyped.decimal heq
  · rcases h₃ with ⟨_, h₃₁, h₃₂⟩
    subst h₃₂
    simp only [TypedExpr.liftBoolTypes]
    apply TypedExpr.WellTyped.call
    · exact typechecked_is_well_typed_after_lifting_call_arg hᵢ hᵢ₁
    · --TODO: abstract this
      simp [typeOfConstructor] at h₃₁
      split at h₃₁ <;> simp [err] at h₃₁
      · split at h₃₁ <;> try simp at h₃₁
        · rename_i heq
          simp [ok] at h₃₁
          rcases h₃₁ with ⟨h₃₁, _⟩
          subst h₃₁
          simp [CedarType.liftBoolTypes, List.map₁_eq_map]
          cases hᵢ
          · rename_i heq₁
            cases heq₁
            rename_i heq₂
            simp [typeOf, typeOfLit, ok, justType, Except.map] at heq₂
            subst heq₂
            simp [TypedExpr.liftBoolTypes, CedarType.liftBoolTypes]
            symm at heq
            exact ExtFun.WellTyped.ip heq
  · rcases h₃ with ⟨_, h₃₁, h₃₂⟩
    subst h₃₂
    simp only [TypedExpr.liftBoolTypes]
    apply TypedExpr.WellTyped.call
    · exact typechecked_is_well_typed_after_lifting_call_arg hᵢ hᵢ₁
    · --TODO: abstract this
      simp [typeOfConstructor] at h₃₁
      split at h₃₁ <;> simp [err] at h₃₁
      · split at h₃₁ <;> try simp at h₃₁
        · rename_i heq
          simp [ok] at h₃₁
          rcases h₃₁ with ⟨h₃₁, _⟩
          subst h₃₁
          simp [CedarType.liftBoolTypes, List.map₁_eq_map]
          cases hᵢ
          · rename_i heq₁
            cases heq₁
            rename_i heq₂
            simp [typeOf, typeOfLit, ok, justType, Except.map] at heq₂
            subst heq₂
            simp [TypedExpr.liftBoolTypes, CedarType.liftBoolTypes]
            symm at heq
            exact ExtFun.WellTyped.datetime heq
  · rcases h₃ with ⟨_, h₃₁, h₃₂⟩
    subst h₃₂
    simp only [TypedExpr.liftBoolTypes]
    apply TypedExpr.WellTyped.call
    · exact typechecked_is_well_typed_after_lifting_call_arg hᵢ hᵢ₁
    · --TODO: abstract this
      simp [typeOfConstructor] at h₃₁
      split at h₃₁ <;> simp [err] at h₃₁
      · split at h₃₁ <;> try simp at h₃₁
        · rename_i heq
          simp [ok] at h₃₁
          rcases h₃₁ with ⟨h₃₁, _⟩
          subst h₃₁
          simp [CedarType.liftBoolTypes, List.map₁_eq_map]
          cases hᵢ
          · rename_i heq₁
            cases heq₁
            rename_i heq₂
            simp [typeOf, typeOfLit, ok, justType, Except.map] at heq₂
            subst heq₂
            simp [TypedExpr.liftBoolTypes, CedarType.liftBoolTypes]
            symm at heq
            exact ExtFun.WellTyped.duration heq
  case _ tys _ _ heq =>
    rcases h₃ with ⟨h₃, _⟩
    subst h₃
    simp only [TypedExpr.liftBoolTypes]
    apply TypedExpr.WellTyped.call
    · exact typechecked_is_well_typed_after_lifting_call_arg hᵢ hᵢ₁
    · simp [CedarType.liftBoolTypes, List.map₁_eq_map, BoolType.lift]
      unfold List.map at heq
      split at heq <;> simp at heq
      rcases heq with ⟨h₂, _, h₃, h₄⟩
      subst h₃
      simp only [List.map_cons, List.map_nil]
      constructor <;> simp [type_of_after_lifted_is_lifted]
      · simp [h₂, CedarType.liftBoolTypes]
      · simp [h₄, CedarType.liftBoolTypes]
  case _ tys _ _ heq =>
    rcases h₃ with ⟨h₃, _⟩
    subst h₃
    simp only [TypedExpr.liftBoolTypes]
    apply TypedExpr.WellTyped.call
    · exact typechecked_is_well_typed_after_lifting_call_arg hᵢ hᵢ₁
    · simp [CedarType.liftBoolTypes, List.map₁_eq_map, BoolType.lift]
      unfold List.map at heq
      split at heq <;> simp at heq
      rcases heq with ⟨h₂, _, h₃, h₄⟩
      subst h₃
      simp only [List.map_cons, List.map_nil]
      constructor <;> simp [type_of_after_lifted_is_lifted]
      · simp [h₂, CedarType.liftBoolTypes]
      · simp [h₄, CedarType.liftBoolTypes]
  case _ tys _ _ heq =>
    rcases h₃ with ⟨h₃, _⟩
    subst h₃
    simp only [TypedExpr.liftBoolTypes]
    apply TypedExpr.WellTyped.call
    · exact typechecked_is_well_typed_after_lifting_call_arg hᵢ hᵢ₁
    · simp [CedarType.liftBoolTypes, List.map₁_eq_map, BoolType.lift]
      unfold List.map at heq
      split at heq <;> simp at heq
      rcases heq with ⟨h₂, _, h₃, h₄⟩
      subst h₃
      simp only [List.map_cons, List.map_nil]
      constructor <;> simp [type_of_after_lifted_is_lifted]
      · simp [h₂, CedarType.liftBoolTypes]
      · simp [h₄, CedarType.liftBoolTypes]
  case _ tys _ _ heq =>
    rcases h₃ with ⟨h₃, _⟩
    subst h₃
    simp only [TypedExpr.liftBoolTypes]
    apply TypedExpr.WellTyped.call
    · exact typechecked_is_well_typed_after_lifting_call_arg hᵢ hᵢ₁
    · simp [CedarType.liftBoolTypes, List.map₁_eq_map, BoolType.lift]
      unfold List.map at heq
      split at heq <;> simp at heq
      rcases heq with ⟨h₂, _, h₃, h₄⟩
      subst h₃
      simp only [List.map_cons, List.map_nil]
      constructor <;> simp [type_of_after_lifted_is_lifted]
      · simp [h₂, CedarType.liftBoolTypes]
      · simp [h₄, CedarType.liftBoolTypes]
  case _ tys _ _ heq =>
    rcases h₃ with ⟨h₃, _⟩
    subst h₃
    simp only [TypedExpr.liftBoolTypes]
    apply TypedExpr.WellTyped.call
    · exact typechecked_is_well_typed_after_lifting_call_arg hᵢ hᵢ₁
    · simp [CedarType.liftBoolTypes, List.map₁_eq_map, BoolType.lift]
      unfold List.map at heq
      split at heq <;> simp at heq
      rcases heq with ⟨h₂, h₃⟩
      subst h₃
      simp only [List.map_cons, List.map_nil]
      constructor
      simp [type_of_after_lifted_is_lifted, h₂, CedarType.liftBoolTypes]
  case _ tys _ _ heq =>
    rcases h₃ with ⟨h₃, _⟩
    subst h₃
    simp only [TypedExpr.liftBoolTypes]
    apply TypedExpr.WellTyped.call
    · exact typechecked_is_well_typed_after_lifting_call_arg hᵢ hᵢ₁
    · simp [CedarType.liftBoolTypes, List.map₁_eq_map, BoolType.lift]
      unfold List.map at heq
      split at heq <;> simp at heq
      rcases heq with ⟨h₂, h₃⟩
      subst h₃
      simp only [List.map_cons, List.map_nil]
      constructor
      simp [type_of_after_lifted_is_lifted, h₂, CedarType.liftBoolTypes]
  case _ tys _ _ heq =>
    rcases h₃ with ⟨h₃, _⟩
    subst h₃
    simp only [TypedExpr.liftBoolTypes]
    apply TypedExpr.WellTyped.call
    · exact typechecked_is_well_typed_after_lifting_call_arg hᵢ hᵢ₁
    · simp [CedarType.liftBoolTypes, List.map₁_eq_map, BoolType.lift]
      unfold List.map at heq
      split at heq <;> simp at heq
      rcases heq with ⟨h₂, h₃⟩
      subst h₃
      simp only [List.map_cons, List.map_nil]
      constructor
      simp [type_of_after_lifted_is_lifted, h₂, CedarType.liftBoolTypes]
  case _ tys _ _ heq =>
    rcases h₃ with ⟨h₃, _⟩
    subst h₃
    simp only [TypedExpr.liftBoolTypes]
    apply TypedExpr.WellTyped.call
    · exact typechecked_is_well_typed_after_lifting_call_arg hᵢ hᵢ₁
    · simp [CedarType.liftBoolTypes, List.map₁_eq_map, BoolType.lift]
      unfold List.map at heq
      split at heq <;> simp at heq
      rcases heq with ⟨h₂, h₃⟩
      subst h₃
      simp only [List.map_cons, List.map_nil]
      constructor
      simp [type_of_after_lifted_is_lifted, h₂, CedarType.liftBoolTypes]
  case _ tys _ _ heq =>
    rcases h₃ with ⟨h₃, _⟩
    subst h₃
    simp only [TypedExpr.liftBoolTypes]
    apply TypedExpr.WellTyped.call
    · exact typechecked_is_well_typed_after_lifting_call_arg hᵢ hᵢ₁
    · simp [CedarType.liftBoolTypes, List.map₁_eq_map, BoolType.lift]
      unfold List.map at heq
      split at heq <;> simp at heq
      rcases heq with ⟨h₂, _, h₃, h₄⟩
      subst h₃
      simp only [List.map_cons, List.map_nil]
      constructor <;> simp [type_of_after_lifted_is_lifted]
      · simp [h₂, CedarType.liftBoolTypes]
      · simp [h₄, CedarType.liftBoolTypes]
  case _ tys _ _ heq =>
    rcases h₃ with ⟨h₃, _⟩
    subst h₃
    simp only [TypedExpr.liftBoolTypes]
    apply TypedExpr.WellTyped.call
    · exact typechecked_is_well_typed_after_lifting_call_arg hᵢ hᵢ₁
    · simp only [List.map₁_eq_map, CedarType.liftBoolTypes]
      unfold List.map at heq
      split at heq <;> simp at heq
      rcases heq with ⟨h₂, _, h₃, h₄⟩
      subst h₃
      simp only [List.map_cons, List.map_nil]
      constructor <;> simp [type_of_after_lifted_is_lifted]
      · simp only [h₂, CedarType.liftBoolTypes]
      · simp only [h₄, CedarType.liftBoolTypes]
  case _ tys _ _ heq =>
    rcases h₃ with ⟨h₃, _⟩
    subst h₃
    simp only [TypedExpr.liftBoolTypes]
    apply TypedExpr.WellTyped.call
    · exact typechecked_is_well_typed_after_lifting_call_arg hᵢ hᵢ₁
    · simp only [List.map₁_eq_map, CedarType.liftBoolTypes]
      unfold List.map at heq
      split at heq <;> simp at heq
      rcases heq with ⟨h₂, _, h₃, h₄⟩
      subst h₃
      simp only [List.map_cons, List.map_nil]
      constructor <;> simp [type_of_after_lifted_is_lifted]
      · simp only [h₂, CedarType.liftBoolTypes]
      · simp only [h₄, CedarType.liftBoolTypes]
  case _ tys _ _ heq =>
    rcases h₃ with ⟨h₃, _⟩
    subst h₃
    simp only [TypedExpr.liftBoolTypes]
    apply TypedExpr.WellTyped.call
    · exact typechecked_is_well_typed_after_lifting_call_arg hᵢ hᵢ₁
    · simp only [List.map₁_eq_map, CedarType.liftBoolTypes]
      unfold List.map at heq
      split at heq <;> simp at heq
      rcases heq with ⟨h₂, h₃⟩
      subst h₃
      simp only [List.map_cons, List.map_nil]
      constructor
      simp [type_of_after_lifted_is_lifted, h₂, CedarType.liftBoolTypes]
  case _ tys _ _ heq =>
    rcases h₃ with ⟨h₃, _⟩
    subst h₃
    simp only [TypedExpr.liftBoolTypes]
    apply TypedExpr.WellTyped.call
    · exact typechecked_is_well_typed_after_lifting_call_arg hᵢ hᵢ₁
    · simp only [List.map₁_eq_map, CedarType.liftBoolTypes]
      unfold List.map at heq
      split at heq <;> simp at heq
      rcases heq with ⟨h₂, h₃⟩
      subst h₃
      simp only [List.map_cons, List.map_nil]
      constructor
      simp [type_of_after_lifted_is_lifted, h₂, CedarType.liftBoolTypes]
  case _ tys _ _ heq =>
    rcases h₃ with ⟨h₃, _⟩
    subst h₃
    simp only [TypedExpr.liftBoolTypes]
    apply TypedExpr.WellTyped.call
    · exact typechecked_is_well_typed_after_lifting_call_arg hᵢ hᵢ₁
    · simp only [List.map₁_eq_map, CedarType.liftBoolTypes]
      unfold List.map at heq
      split at heq <;> simp at heq
      rcases heq with ⟨h₂, h₃⟩
      subst h₃
      simp only [List.map_cons, List.map_nil]
      constructor
      simp [type_of_after_lifted_is_lifted, h₂, CedarType.liftBoolTypes]
  case _ tys _ _ heq =>
    rcases h₃ with ⟨h₃, _⟩
    subst h₃
    simp only [TypedExpr.liftBoolTypes]
    apply TypedExpr.WellTyped.call
    · exact typechecked_is_well_typed_after_lifting_call_arg hᵢ hᵢ₁
    · simp only [List.map₁_eq_map, CedarType.liftBoolTypes]
      unfold List.map at heq
      split at heq <;> simp at heq
      rcases heq with ⟨h₂, h₃⟩
      subst h₃
      simp only [List.map_cons, List.map_nil]
      constructor
      simp [type_of_after_lifted_is_lifted, h₂, CedarType.liftBoolTypes]
  case _ tys _ _ heq =>
    rcases h₃ with ⟨h₃, _⟩
    subst h₃
    simp only [TypedExpr.liftBoolTypes]
    apply TypedExpr.WellTyped.call
    · exact typechecked_is_well_typed_after_lifting_call_arg hᵢ hᵢ₁
    · simp only [List.map₁_eq_map, CedarType.liftBoolTypes]
      unfold List.map at heq
      split at heq <;> simp at heq
      rcases heq with ⟨h₂, h₃⟩
      subst h₃
      simp only [List.map_cons, List.map_nil]
      constructor
      simp [type_of_after_lifted_is_lifted, h₂, CedarType.liftBoolTypes]
  case _ tys _ _ heq =>
    rcases h₃ with ⟨h₃, _⟩
    subst h₃
    simp only [TypedExpr.liftBoolTypes]
    apply TypedExpr.WellTyped.call
    · exact typechecked_is_well_typed_after_lifting_call_arg hᵢ hᵢ₁
    · simp only [List.map₁_eq_map, CedarType.liftBoolTypes]
      unfold List.map at heq
      split at heq <;> simp at heq
      rcases heq with ⟨h₂, h₃⟩
      subst h₃
      simp only [List.map_cons, List.map_nil]
      constructor
      simp [type_of_after_lifted_is_lifted, h₂, CedarType.liftBoolTypes]
  case _ tys _ _ heq =>
    rcases h₃ with ⟨h₃, _⟩
    subst h₃
    simp only [TypedExpr.liftBoolTypes]
    apply TypedExpr.WellTyped.call
    · exact typechecked_is_well_typed_after_lifting_call_arg hᵢ hᵢ₁
    · simp only [List.map₁_eq_map, CedarType.liftBoolTypes]
      unfold List.map at heq
      split at heq <;> simp at heq
      rcases heq with ⟨h₂, h₃⟩
      subst h₃
      simp only [List.map_cons, List.map_nil]
      constructor
      simp [type_of_after_lifted_is_lifted, h₂, CedarType.liftBoolTypes]

theorem foldM_lub_some {x y: CedarType} {xs : List CedarType} :
  List.foldlM lub? x xs = some y →
  ∀ t ∈ xs, t ⊑ y
:= by
  induction xs generalizing x
  case nil =>
    simp
  case cons head tail hᵢ =>
    intro h
    simp at h
    generalize heq : (x ⊔ head) = res
    cases res <;> simp [heq] at h
    rename_i val
    simp only [List.mem_cons, forall_eq_or_imp]
    apply And.intro
    · have heq₁ := foldlM_of_lub_is_LUB h
      simp [lub_comm] at heq
      have heq₂ := lub_lub_fixed heq heq₁
      simp only [subty, heq₂, decide_true]
    · exact hᵢ h

theorem typechecked_is_well_typed_after_lifting_set
{c₁ c₂ : Capabilities}
{env : TypeEnv}
{ty : TypedExpr}
{xs : List Expr}
(hᵢ₁ : ∀ (x₁ : Expr),
  x₁ ∈ xs →
    ∀ {c₂ : Capabilities} {ty : TypedExpr},
        typeOf x₁ c₁ env = Except.ok (ty, c₂) → TypedExpr.WellTyped env ty.liftBoolTypes) :
  typeOf (Expr.set xs) c₁ env = Except.ok (ty, c₂) → TypedExpr.WellTyped env ty.liftBoolTypes
:= by
  intro h₃
  simp [typeOf, List.mapM₁_eq_mapM fun x => justType (typeOf x c₁ env)] at h₃
  generalize hᵢ : List.mapM (fun x => justType (typeOf x c₁ env)) xs = res₁
  cases res₁ <;> simp only [hᵢ, Except.bind_err, reduceCtorEq] at h₃
  rename_i tys
  simp [List.mapM_ok_iff_forall₂] at hᵢ
  simp [typeOfSet] at h₃
  split at h₃ <;> simp [err] at h₃
  split at h₃ <;> simp [ok] at h₃
  rcases h₃ with ⟨h₃, _⟩
  subst h₃
  simp [TypedExpr.liftBoolTypes, List.map₁_eq_map, CedarType.liftBoolTypes]
  constructor
  · rename_i hd _ _ _ heq _
    simp only [List.mem_cons, List.mem_map, forall_eq_or_imp, forall_exists_index, and_imp,
      forall_apply_eq_imp_iff₂]
    cases hᵢ
    rename_i e es heq₁ _
    simp [justType, Except.map] at heq₁
    split at heq₁ <;> simp at heq₁
    rename_i heq₃ _ _ heq₂
    apply And.intro
    · have ht₁ : e ∈ e :: es := by
        simp only [List.mem_cons, true_or]
      subst heq₁
      exact hᵢ₁ e ht₁ heq₂
    · replace heq₃ := List.forall₂_implies_all_right heq₃
      intro y h₃
      rcases heq₃ y h₃ with ⟨e', h₄, h₅⟩
      simp [justType, Except.map] at h₅
      split at h₅ <;> simp at h₅
      rename_i heq₄
      have ht₂ : e' ∈ e :: es := by
        simp only [List.mem_cons, h₄, or_true]
      subst h₅
      exact hᵢ₁ e' ht₂ heq₄
  · rename_i hd _ _ _ heq _
    simp only [List.mem_cons, List.mem_map, forall_eq_or_imp, type_of_after_lifted_is_lifted,
      forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
    apply And.intro
    · exact lifted_type_lub (foldlM_of_lub_is_LUB heq)
    · replace heq := foldM_lub_some heq
      intro a h₃
      simp only [List.mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂] at heq
      specialize heq a h₃
      exact lifted_type_is_top heq
  · simp only [bne_iff_ne, ne_eq, reduceCtorEq, not_false_eq_true]

theorem record_lifting_make {tys : List (Attr × TypedExpr)} :
  RecordType.liftBoolTypes
    (Data.Map.make (List.map (fun x => (x.fst, Qualified.required x.snd.typeOf)) tys)) =
  Data.Map.make
    (List.map (fun x => (x.fst, Qualified.required x.snd.typeOf))
      (List.map (fun x => (x.fst, x.snd.liftBoolTypes)) tys))
:= by
  simp only [lift_bool_types_record_eq_map_on_values]
  rw [Data.Map.mapOnValues_eq_make_map QualifiedType.liftBoolTypes]
  simp only [List.map_map]
  · simp only [Data.Map.make, Data.Map.mk.injEq]
    have : (λ (x : Attr × TypedExpr) => (x.fst, Qualified.required x.snd.typeOf)) =
           (Prod.map id (λ (tx : TypedExpr) => Qualified.required tx.typeOf)) := by
      unfold Prod.map
      simp only [id_eq]
    simp only [this, List.canonicalize_of_map_fst, Data.Map.toList_mk_id, List.map_map]
    have : ((λ (kv : Attr × QualifiedType) => (kv.fst, kv.snd.liftBoolTypes)) ∘ Prod.map id (λ (tx : TypedExpr) => Qualified.required tx.typeOf)) =
           (Prod.map id (λ (tx : TypedExpr) => QualifiedType.liftBoolTypes (Qualified.required tx.typeOf))) := by
      unfold Prod.map
      simp only [id_eq]
      apply funext
      intros
      simp only [Function.comp_apply]
    simp only [this, List.canonicalize_of_map_fst]
    have : (Prod.map id (λ (tx : TypedExpr) => Qualified.required tx.typeOf)) ∘ (λ (x : Attr × TypedExpr) => (x.fst, x.snd.liftBoolTypes)) =
           (Prod.map id (λ (tx : TypedExpr) => QualifiedType.liftBoolTypes (Qualified.required tx.typeOf))) := by
      unfold Prod.map
      simp only [id_eq]
      apply funext
      intro (_, tx)
      simp only [Function.comp_apply, type_of_after_lifted_is_lifted, QualifiedType.liftBoolTypes]
    simp only [List.canonicalize_idempotent, this, List.canonicalize_of_map_fst]
  · simp only [Data.Map.make_wf]

theorem typechecked_is_well_typed_after_lifting_record
{c₁ c₂ : Capabilities}
{env : TypeEnv}
{ty : TypedExpr}
{axs : List (Attr × Expr)}
(hᵢ₁ : ∀ (a₁ : Attr) (x₁ : Expr),
  sizeOf (a₁, x₁).snd < 1 + sizeOf axs →
    ∀ {c₂ : Capabilities} {ty : TypedExpr},
        typeOf x₁ c₁ env = Except.ok (ty, c₂) → TypedExpr.WellTyped env ty.liftBoolTypes) :
  typeOf (Expr.record axs) c₁ env = Except.ok (ty, c₂) → TypedExpr.WellTyped env ty.liftBoolTypes
:= by
  intro h₃
  simp only [typeOf, List.empty_eq] at h₃
  rw [List.mapM₂_eq_mapM λ (x : Attr × Expr) => Except.map (fun x_1 => (x.fst, x_1.fst)) (typeOf x.snd c₁ env)] at h₃
  generalize hᵢ : List.mapM (fun x => Except.map (fun x_1 => (x.fst, x_1.fst)) (typeOf x.snd c₁ env)) axs = res
  cases res <;> simp [hᵢ, ok] at h₃
  rename_i tys
  rcases h₃ with ⟨h₃, _⟩
  subst h₃
  simp only [TypedExpr.liftBoolTypes, CedarType.liftBoolTypes]
  constructor
  · intro k v h₂
    simp [List.map₂_eq_map λ (x : Attr × TypedExpr) => (x.fst, x.snd.liftBoolTypes)] at h₂
    rcases h₂ with ⟨a₁, x₁, h₂, h₃, h₆⟩
    simp [List.mapM_ok_iff_forall₂] at hᵢ
    rcases List.forall₂_implies_all_right hᵢ (a₁, x₁) h₂ with ⟨ax, h₄, h₅⟩
    simp [Except.map] at h₅
    split at h₅ <;> simp at h₅
    rename_i heq
    rcases h₅ with ⟨_, h₅⟩
    specialize hᵢ₁ ax.fst ax.snd (List.sizeOf_snd_lt_sizeOf_list h₄) heq
    subst h₆
    subst h₅
    exact hᵢ₁
  · simp only [List.map₂_eq_map λ (x : Attr × TypedExpr) => (x.fst, x.snd.liftBoolTypes)]
    exact record_lifting_make

/-- The type checker produces typed expressions that are well-typed after type
lifting. TODO: move this around after the proof is fixed -/
theorem typechecked_is_well_typed_after_lifting
{e : Expr}
{c₁ c₂ : Capabilities}
{env : TypeEnv}
{ty : TypedExpr} :
  typeOf e c₁ env = .ok (ty, c₂) →
  TypedExpr.WellTyped env ty.liftBoolTypes
:= by
  induction e, c₁ using typeOf.induct generalizing ty c₂
  case _ =>
    exact typechecked_is_well_typed_after_lifting_lit
  case _ =>
    exact typechecked_is_well_typed_after_lifting_var
  case _ hᵢ₁ hᵢ₂ hᵢ₃ =>
    exact typechecked_is_well_typed_after_lifting_ite hᵢ₁ hᵢ₂ hᵢ₃
  case _ hᵢ₁ hᵢ₂ =>
    exact typechecked_is_well_typed_after_lifting_and hᵢ₁ hᵢ₂
  case _ hᵢ₁ hᵢ₂ =>
    exact typechecked_is_well_typed_after_lifting_or hᵢ₁ hᵢ₂
  case _ hᵢ =>
    exact typechecked_is_well_typed_after_lifting_unary_app hᵢ
  case _ hᵢ₁ hᵢ₂ =>
    exact typechecked_is_well_typed_after_lifting_binary_app hᵢ₁ hᵢ₂
  case _ hᵢ =>
    exact typechecked_is_well_typed_after_lifting_has_attr hᵢ
  case _ hᵢ =>
    exact typechecked_is_well_typed_after_lifting_ext_has_attr hᵢ
  case _ hᵢ =>
    exact typechecked_is_well_typed_after_lifting_get_attr hᵢ
  case _ hᵢ =>
    exact typechecked_is_well_typed_after_lifting_set hᵢ
  case _ hᵢ =>
    exact typechecked_is_well_typed_after_lifting_record hᵢ
  case _ hᵢ =>
    exact typechecked_is_well_typed_after_lifting_call hᵢ

end Cedar.Thm
