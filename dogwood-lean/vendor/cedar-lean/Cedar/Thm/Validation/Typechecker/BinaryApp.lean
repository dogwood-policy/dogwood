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

import Cedar.Thm.Validation.Typechecker.BinaryApp.Eq
import Cedar.Thm.Validation.Typechecker.BinaryApp.Cmp
import Cedar.Thm.Validation.Typechecker.BinaryApp.Arith
import Cedar.Thm.Validation.Typechecker.BinaryApp.Contains
import Cedar.Thm.Validation.Typechecker.BinaryApp.ContainsAnyAll
import Cedar.Thm.Validation.Typechecker.BinaryApp.Mem
import Cedar.Thm.Validation.Typechecker.BinaryApp.HasTag
import Cedar.Thm.Validation.Typechecker.BinaryApp.GetTag

/-!
This file proves that typechecking of `.binaryApp` expressions is sound.
-/

namespace Cedar.Thm

open Cedar.Data
open Cedar.Spec
open Cedar.Validation

theorem type_of_binaryApp_inversion {op₂ : BinaryOp} {x₁ x₂ : Expr} {c c' : Capabilities} {env : TypeEnv} {tx : TypedExpr}
  (htx : typeOf (Expr.binaryApp op₂ x₁ x₂) c env = Except.ok (tx, c')) :
  ∃ tx₁ c₁ tx₂ c₂,
    typeOf x₁ c env = Except.ok (tx₁, c₁) ∧
    typeOf x₂ c env = Except.ok (tx₂, c₂) ∧
    ∃ ty, tx = .binaryApp op₂ tx₁ tx₂ ty
:= by
  simp only [typeOf] at htx
  simp_do_let (typeOf x₁ c env) as htx₁ at htx
  simp_do_let (typeOf x₂ c env) as htx₂ at htx
  rename_i r₁ r₂
  simp [typeOfBinaryApp, typeOfEq, ifLubThenBool, typeOfGetTag, typeOfHasTag, ok, err] at htx
  (split at htx <;> try split at htx <;> try split at htx <;> try split at htx) <;> try simp at htx
  all_goals
    have ⟨ htx, _ ⟩ := htx
    rw [←htx]
    exists r₁.fst, r₁.snd, r₂.fst, r₂.snd
    and_intros
    · rfl
    · rfl
    · simp only [TypedExpr.binaryApp.injEq, true_and, exists_eq']

theorem type_of_binaryApp_is_sound {op₂ : BinaryOp} {x₁ x₂ : Expr} {c₁ c₂ : Capabilities} {env : TypeEnv} {ty : TypedExpr} {request : Request} {entities : Entities}
  (h₁ : CapabilitiesInvariant c₁ request entities)
  (h₂ : InstanceOfWellFormedEnvironment request entities env)
  (h₃ : typeOf (Expr.binaryApp op₂ x₁ x₂) c₁ env = Except.ok (ty, c₂))
  (ih₁ : TypeOfIsSound x₁)
  (ih₂ : TypeOfIsSound x₂) :
  GuardedCapabilitiesInvariant (Expr.binaryApp op₂ x₁ x₂) c₂ request entities ∧
  ∃ v, EvaluatesTo (Expr.binaryApp op₂ x₁ x₂) request entities v ∧ InstanceOfType env v ty.typeOf
:= by
  match op₂ with
  | .eq          => exact type_of_eq_is_sound h₁ h₂ h₃ ih₁ ih₂
  | .less
  | .lessEq      => exact type_of_int_cmp_is_sound (by simp) h₁ h₂ h₃ ih₁ ih₂
  | .add
  | .sub
  | .mul         => exact type_of_int_arith_is_sound (by simp) h₁ h₂ h₃ ih₁ ih₂
  | .contains    => exact type_of_contains_is_sound h₁ h₂ h₃ ih₁ ih₂
  | .containsAll
  | .containsAny => exact type_of_containsA_is_sound (by simp) h₁ h₂ h₃ ih₁ ih₂
  | .mem         => exact type_of_mem_is_sound h₁ h₂ h₃ ih₁ ih₂
  | .hasTag      => exact type_of_hasTag_is_sound h₁ h₂ h₃ ih₁ ih₂
  | .getTag      => exact type_of_getTag_is_sound h₁ h₂ h₃ ih₁ ih₂

end Cedar.Thm
