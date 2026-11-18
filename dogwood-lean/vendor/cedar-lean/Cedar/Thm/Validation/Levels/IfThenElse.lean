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
import Cedar.Data
import Cedar.Validation
import Cedar.Thm.Validation.Typechecker
import Cedar.Thm.Validation.Typechecker.Basic
import Cedar.Thm.Validation.Typechecker.IfThenElse
import Cedar.Thm.Validation.Typechecker.Types
import Cedar.Thm.Validation.Levels.Basic

/-!
This file proves that level checking for `.ite` expressions is sound.
-/

namespace Cedar.Thm

open Cedar.Data
open Cedar.Spec
open Cedar.Validation

theorem level_based_slicing_is_sound_if {x₁ x₂ x₃ : Expr} {n : Nat} {c₀ c₁: Capabilities} {env : TypeEnv} {request : Request} {entities : Entities}
  (hc : CapabilitiesInvariant c₀ request entities)
  (hr : InstanceOfWellFormedEnvironment request entities env)
  (htx : typeOf (.ite x₁ x₂ x₃) c₀ env = Except.ok (tx, c₁))
  (hl : tx.AtLevel env n)
  (ih₁ : TypedAtLevelIsSound x₁)
  (ih₂ : TypedAtLevelIsSound x₂)
  (ih₃ : TypedAtLevelIsSound x₃)
  : evaluate (.ite x₁ x₂ x₃) request entities = evaluate (.ite x₁ x₂ x₃) request (entities.sliceAtLevel request n)
:= by
    replace ⟨tx₁, bty₁, c₁, tx₂, c₂, tx₃, c₃, htx, htx₁, hty₁, htx₂₃ ⟩ := type_of_ite_inversion htx
    have ⟨ hgc, v₁, he₁, hv₁ ⟩ := type_of_is_sound hc hr htx₁
    rw [hty₁] at hv₁
    rw [htx] at hl
    cases hl
    rename_i hl₁ hl₂ hl₃
    specialize ih₁ hc hr htx₁ hl₁
    simp only [ih₁, evaluate]
    simp_do_let (Result.as Bool (evaluate x₁ request (entities.sliceAtLevel request n))) as he₁'
    rename_i b
    replace he₁' : evaluate x₁ request (entities.sliceAtLevel request n) = .ok (.prim (.bool b)) := by
      simp only [Result.as, Coe.coe, Value.asBool] at he₁'
      split at he₁' <;> try simp only [reduceCtorEq] at he₁'
      split at he₁' <;> try simp only [reduceCtorEq, Except.ok.injEq] at he₁'
      rw [←he₁']
      assumption
    split at htx₂₃
    · replace he₁ : b = false := by
        simpa [ih₁, he₁', instance_of_ff_is_false hv₁, EvaluatesTo] using he₁
      subst he₁
      specialize ih₃ hc hr htx₂₃.left hl₃
      simp [ih₃]
    · replace he₁ : b = true := by
        simpa [ih₁, he₁', instance_of_tt_is_true hv₁, EvaluatesTo] using he₁
      subst he₁
      replace hgc : CapabilitiesInvariant c₁ request entities := by
        simpa [GuardedCapabilitiesInvariant, ih₁, he₁'] using hgc
      specialize ih₂ (capability_union_invariant hc hgc) hr htx₂₃.left hl₂
      simp [ih₂]
    · replace ⟨htx₂, htx₃, _, _⟩ := htx₂₃
      specialize ih₃ hc hr htx₃ hl₃
      simp only [ih₃]
      cases b
      case false => simp
      case true =>
        replace hgc : CapabilitiesInvariant c₁ request entities := by
          simpa [GuardedCapabilitiesInvariant, ih₁, he₁'] using hgc
        specialize ih₂ (capability_union_invariant hc hgc) hr htx₂ hl₂
        simp [ih₂]
