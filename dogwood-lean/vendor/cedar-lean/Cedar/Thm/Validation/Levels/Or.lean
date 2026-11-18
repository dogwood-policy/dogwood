
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
This file proves that level checking for `.or` expressions is sound.
-/

namespace Cedar.Thm

open Cedar.Data
open Cedar.Spec
open Cedar.Validation

theorem level_based_slicing_is_sound_or {e₁ e₂ : Expr} {n : Nat} {c₀ c₁: Capabilities} {env : TypeEnv} {request : Request} {entities : Entities}
  (hc : CapabilitiesInvariant c₀ request entities)
  (hr : InstanceOfWellFormedEnvironment request entities env)
  (ht : typeOf (.or e₁ e₂) c₀ env = Except.ok (tx, c₁))
  (hl : tx.AtLevel env n)
  (ih₁ : TypedAtLevelIsSound e₁)
  (ih₂ : TypedAtLevelIsSound e₂)
  : evaluate (.or e₁ e₂) request entities = evaluate (.or e₁ e₂) request (entities.sliceAtLevel request n)
:= by
  replace ⟨ tx₁, bty, c', htx₁, hty₁, ht ⟩ := type_of_or_inversion ht
  have ⟨ hgc, v₁, he₁, hv₁⟩  := type_of_is_sound hc hr htx₁
  rw [hty₁] at hv₁
  split at ht
  case isTrue =>
    replace ⟨ ht, _ ⟩ := ht
    subst tx bty
    replace hv₁ := instance_of_tt_is_true hv₁
    subst v₁
    unfold EvaluatesTo at he₁
    simp only [evaluate]
    specialize ih₁ hc hr htx₁ hl
    rw [←ih₁]
    rcases he₁ with he₁ | he₁ | he₁ | he₁ <;>
    simp [he₁, Result.as, Coe.coe, Value.asBool]
  case isFalse =>
    replace ⟨ bt, tx₂, bty₂, c₂, htx, htx₂, hty₂, ht ⟩ := ht
    subst tx
    cases hl
    rename_i hl₁ hl₂
    specialize ih₁ hc hr htx₁ hl₁
    specialize ih₂ hc hr htx₂ hl₂
    simp only [evaluate]
    rw [ih₁, ih₂]
