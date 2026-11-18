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
import Cedar.Thm.Validation.Typechecker.Types
import Cedar.Thm.Data.MapUnion
import Cedar.Thm.Validation.Levels.CheckLevel

import Cedar.Thm.Validation.Slice.Reachable.Basic

namespace Cedar.Thm

open Cedar.Data
open Cedar.Spec
open Cedar.Validation

theorem checked_eval_entity_reachable_ite {e₁ e₂ e₃: Expr} {n : Nat} {c c' : Capabilities} {tx : TypedExpr} {env : TypeEnv} {entities : Entities} {path : List Attr}
  (hc : CapabilitiesInvariant c request entities)
  (hr : InstanceOfWellFormedEnvironment request entities env)
  (ht : typeOf (.ite e₁ e₂ e₃) c env = .ok (tx, c'))
  (hl : tx.EntityAccessAtLevel env n nmax path)
  (he : evaluate (.ite e₁ e₂ e₃) request entities = .ok v)
  (ha : Value.EuidViaPath v path euid)
  (ih₂ : CheckedEvalEntityReachable e₂)
  (ih₃ : CheckedEvalEntityReachable e₃) :
  ReachableIn entities request.sliceEUIDs euid (n + 1)
:= by
  have ⟨tx₁, bty₁, c₁, tx₂, c₂, tx₃, c₃, htx, htx₁, hty₁, hif ⟩ := type_of_ite_inversion ht
  have ⟨ hgc, v, he₁, hi₁⟩ := type_of_is_sound hc hr htx₁

  rw [htx] at hl
  cases hl
  rename_i hl₁ hl₂ hl₃

  simp only [evaluate] at he
  simp_do_let (Result.as Bool (evaluate e₁ request entities)) as he₁' at he
  rename_i b
  replace he₁' : evaluate e₁ request entities = .ok (.prim (.bool b)) := by
    simp only [Result.as, Coe.coe, Value.asBool] at he₁'
    split at he₁' <;> try contradiction
    split at he₁' <;> try contradiction
    injections he₁'
    subst he₁'
    assumption
  replace he₁ : .prim (.bool b) = v := by
    simpa [EvaluatesTo, he₁'] using he₁
  subst he₁
  split at he
  case isTrue hb =>
    subst hb
    have htx₂ : typeOf e₂ (c ∪ c₁) env = .ok (tx₂, c₂) := by
      split at hif <;> first
        | simp only [hif]
        | rw [hty₁] at hi₁
          contradiction
    replace hgc : CapabilitiesInvariant c₁ request entities := by
      simpa [he₁', GuardedCapabilitiesInvariant] using hgc
    exact ih₂ (capability_union_invariant hc hgc) hr htx₂ hl₂ he ha
  case isFalse hb =>
    replace hb : b = false := by
      cases b <;> simp only [Bool.true_eq_false] ; contradiction
    subst hb
    have htx₃ : typeOf e₃ c env = .ok (tx₃, c₃) := by
      split at hif <;> first
        | simp only [hif]
        | rw [hty₁] at hi₁
          contradiction
    exact ih₃ hc hr htx₃ hl₃ he ha
