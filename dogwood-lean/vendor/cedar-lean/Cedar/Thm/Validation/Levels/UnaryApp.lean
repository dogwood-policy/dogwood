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
import Cedar.Thm.Validation.Typechecker.Types
import Cedar.Thm.Validation.Levels.Basic

/-!
This file proves that level checking for `.unaryApp` expressions is sound.
-/

namespace Cedar.Thm

open Cedar.Data
open Cedar.Spec
open Cedar.Validation

theorem level_based_slicing_is_sound_unary_app {op : UnaryOp} {e : Expr} {n : Nat} {c₀ c₁: Capabilities} {env : TypeEnv} {request : Request} {entities : Entities}
  (hc : CapabilitiesInvariant c₀ request entities)
  (hr : InstanceOfWellFormedEnvironment request entities env)
  (ht : typeOf (.unaryApp op e) c₀ env = Except.ok (tx, c₁))
  (hl : tx.AtLevel env n)
  (ihe : TypedAtLevelIsSound e)
  : evaluate (.unaryApp op e) request entities = evaluate (.unaryApp op e) request (entities.sliceAtLevel request n)
:= by
  replace ⟨hc₁, tx₁, ty, c₁', htx, htx₁, ht⟩ := type_of_unary_inversion ht
  subst tx
  cases hl
  rename_i hl₁
  specialize ihe hc hr htx₁ hl₁
  simp [evaluate, ihe]
