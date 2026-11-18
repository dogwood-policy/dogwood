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

import Cedar.Thm.Validation.Typechecker.And
import Cedar.Thm.Validation.Typechecker.BinaryApp
import Cedar.Thm.Validation.Typechecker.Call
import Cedar.Thm.Validation.Typechecker.GetAttr
import Cedar.Thm.Validation.Typechecker.HasAttr
import Cedar.Thm.Validation.Typechecker.ExtHasAttr
import Cedar.Thm.Validation.Typechecker.IfThenElse
import Cedar.Thm.Validation.Typechecker.LitVar
import Cedar.Thm.Validation.Typechecker.Record
import Cedar.Thm.Validation.Typechecker.Set
import Cedar.Thm.Validation.Typechecker.Or
import Cedar.Thm.Validation.Typechecker.UnaryApp
import Cedar.Thm.Validation.Typechecker.LUB
import Cedar.Thm.Validation.Typechecker.WF
import Cedar.Thm.Validation.Typechecker.Basic
import Cedar.Thm.Validation.Typechecker.Types

/-!
This file contains useful definitions and lemmas about the `Typechecker` functions.
-/

namespace Cedar.Thm

open Cedar.Data
open Cedar.Spec
open Cedar.Validation

/--
If an expression is well-typed according to the typechecker, and the input
environment and capabilities satisfy some invariants, then either (1) evaluation
produces a value of the returned type or (2) it returns an error of type
`entityDoesNotExist`, `extensionError`, or `arithBoundsError`. Both options are
encoded in the `EvaluatesTo` predicate.
-/
theorem type_of_is_sound {e : Expr} {c₁ c₂ : Capabilities} {env : TypeEnv} {ty : TypedExpr} {request : Request} {entities : Entities} :
  CapabilitiesInvariant c₁ request entities →
  InstanceOfWellFormedEnvironment request entities env →
  typeOf e c₁ env = .ok (ty, c₂) →
  GuardedCapabilitiesInvariant e c₂ request entities ∧
  ∃ (v : Value), EvaluatesTo e request entities v ∧ InstanceOfType env v ty.typeOf
:= by
  intro h₁ h₂ h₃
  match e with
  | .lit l => exact type_of_lit_is_sound h₃
  | .var var => exact type_of_var_is_sound h₂ h₃
  | .ite x₁ x₂ x₃ =>
    have ih₁ := @type_of_is_sound x₁
    have ih₂ := @type_of_is_sound x₂
    have ih₃ := @type_of_is_sound x₃
    exact type_of_ite_is_sound h₁ h₂ h₃ ih₁ ih₂ ih₃
  | .and x₁ x₂ =>
    have ih₁ := @type_of_is_sound x₁
    have ih₂ := @type_of_is_sound x₂
    exact type_of_and_is_sound h₁ h₂ h₃ ih₁ ih₂
  | .or x₁ x₂ =>
    have ih₁ := @type_of_is_sound x₁
    have ih₂ := @type_of_is_sound x₂
    exact type_of_or_is_sound h₁ h₂ h₃ ih₁ ih₂
  | .unaryApp op₁ x₁ =>
    have ih := @type_of_is_sound x₁
    exact type_of_unaryApp_is_sound h₁ h₂ h₃ ih
  | .binaryApp op₂ x₁ x₂ =>
    have ih₁ := @type_of_is_sound x₁
    have ih₂ := @type_of_is_sound x₂
    exact type_of_binaryApp_is_sound h₁ h₂ h₃ ih₁ ih₂
  | .hasAttr x₁ a =>
    have ih := @type_of_is_sound x₁
    exact type_of_hasAttr_is_sound h₁ h₂ h₃ ih
  | .extHasAttr x₁ a attrs =>
    have ih := @type_of_is_sound x₁
    exact type_of_extHasAttr_is_sound h₁ h₂ h₃ ih
  | .getAttr x₁ a =>
    have ih := @type_of_is_sound x₁
    exact type_of_getAttr_is_sound h₁ h₂ h₃ ih
  | .set xs =>
    have ih : ∀ xᵢ, xᵢ ∈ xs → TypeOfIsSound xᵢ := by
      intro xᵢ _
      exact @type_of_is_sound xᵢ
    exact type_of_set_is_sound h₁ h₂ h₃ ih
  | .record axs =>
    have ih : ∀ axᵢ, axᵢ ∈ axs → TypeOfIsSound axᵢ.snd := by
      intro axᵢ hᵢ
      have _ : sizeOf axᵢ.snd < 1 + sizeOf axs := by
        apply List.sizeOf_snd_lt_sizeOf_list hᵢ
      exact @type_of_is_sound axᵢ.snd
    exact type_of_record_is_sound h₁ h₂ h₃ ih
  | .call xfn xs =>
    have ih : ∀ xᵢ, xᵢ ∈ xs → TypeOfIsSound xᵢ := by
      intro xᵢ _
      exact @type_of_is_sound xᵢ
    exact type_of_call_is_sound h₁ h₂ h₃ ih
termination_by sizeOf e

/-- The type checker, if succeeds, should produce a typed expression that
evaluates to the same result as the input expression.
-/
theorem type_of_preserves_evaluation_results {e : Expr} {c₁ c₂ : Capabilities} {env : TypeEnv} {ty : TypedExpr} {request : Request} {entities : Entities} :
  CapabilitiesInvariant c₁ request entities →
  InstanceOfWellFormedEnvironment request entities env →
  typeOf e c₁ env = .ok (ty, c₂) →
  evaluate e request entities = evaluate ty.toExpr request entities
:= by
  intro h₁ h₂ h₃
  induction e, c₁ using typeOf.induct generalizing ty c₂
  case _ =>
    simp [typeOf, typeOfLit, ok] at h₃
    split at h₃ <;>
    try (
      simp at h₃
      rcases h₃ with ⟨h₃, _⟩
      subst h₃
      simp only [TypedExpr.toExpr]
    )
    split at h₃ <;> simp [err] at h₃
    rcases h₃ with ⟨h₃, _⟩
    subst h₃
    simp only [TypedExpr.toExpr]
  case _ =>
    simp [typeOf, typeOfVar, ok] at h₃
    split at h₃ <;>
    (
      simp at h₃
      rcases h₃ with ⟨h₃, _⟩
      subst h₃
      simp only [TypedExpr.toExpr]
    )
  case _ c₁ x₁ x₂ x₃ hᵢ₁ hᵢ₂ hᵢ₃ =>
    simp [typeOf] at h₃
    generalize h₁ᵢ : typeOf x₁ c₁ env = res₁
    cases res₁
    case ok ty =>
      simp [h₁ᵢ] at h₃
      simp [typeOfIf, ok] at h₃
      specialize hᵢ₁ h₁ h₁ᵢ
      split at h₃
      case _ heq =>
        simp [do_ok_eq_ok] at h₃
        rcases h₃ with ⟨_, _, h₃₁, h₃₂, h₃₃⟩
        subst h₃₂
        simp only [evaluate, TypedExpr.toExpr, ←hᵢ₁]
        generalize h₃ : evaluate x₁ request entities = res₁
        cases res₁
        case _ => simp only [Result.as, Except.bind_err, ite_self]
        case _ =>
          have h₄ := type_of_is_sound h₁ h₂ h₁ᵢ
          rcases h₄ with ⟨h₄₁, _, h₄₂, h₄₃⟩
          rw [heq] at h₄₃
          replace h₄₃ := instance_of_tt_is_true h₄₃
          subst h₄₃
          simp [EvaluatesTo, h₃] at h₄₂
          subst h₄₂
          simp [Result.as, Coe.coe, Value.asBool]
          simp [GuardedCapabilitiesInvariant] at h₄₁
          specialize h₄₁ h₃
          exact hᵢ₂ _ (capability_union_invariant h₁ h₄₁) h₃₁
      case _ heq =>
        simp [do_ok_eq_ok] at h₃
        rcases h₃ with ⟨_, h₃₁, h₃₂⟩
        subst h₃₂
        simp only [evaluate, TypedExpr.toExpr, ←hᵢ₁]
        generalize h₃ : evaluate x₁ request entities = res₁
        cases res₁
        case _ => simp only [Result.as, Except.bind_err, ite_self]
        case _ =>
          have h₄ := type_of_is_sound h₁ h₂ h₁ᵢ
          rcases h₄ with ⟨h₄₁, _, h₄₂, h₄₃⟩
          rw [heq] at h₄₃
          replace h₄₃ := instance_of_ff_is_false h₄₃
          subst h₄₃
          simp [EvaluatesTo, h₃] at h₄₂
          subst h₄₂
          simp [Result.as, Coe.coe, Value.asBool]
          exact hᵢ₃ h₁ h₃₁
      case _ heq =>
        simp [do_eq_ok] at h₃
        rcases h₃ with ⟨_, _, h₃₁, _, _, h₃₂, h₃₃⟩
        split at h₃₃ <;> simp [err] at h₃₃
        rcases h₃₃ with ⟨h₃₃, _⟩
        subst h₃₃
        simp [TypedExpr.toExpr, evaluate, ←hᵢ₁]
        generalize h₃ : evaluate x₁ request entities = res₁
        cases res₁
        case _ => simp only [Result.as, Except.bind_err]
        case _ =>
          have h₄ := type_of_is_sound h₁ h₂ h₁ᵢ
          rcases h₄ with ⟨h₄₁, _, h₄₂, h₄₃⟩
          rw [heq] at h₄₃
          rcases instance_of_anyBool_is_bool h₄₃ with ⟨b₁, h₄₃⟩
          subst h₄₃
          simp [EvaluatesTo, h₃] at h₄₂
          subst h₄₂
          simp [Result.as, Coe.coe, Value.asBool]
          cases b₁
          case _ =>
            simp only [Bool.false_eq_true, ↓reduceIte]
            exact hᵢ₃ h₁ h₃₂
          case _ =>
            simp only [↓reduceIte]
            simp [GuardedCapabilitiesInvariant] at h₄₁
            specialize h₄₁ h₃
            exact hᵢ₂ _ (capability_union_invariant h₁ h₄₁) h₃₁
      case _ => simp only [err, reduceCtorEq] at h₃
    case error => simp only [h₁ᵢ, Except.bind_err, reduceCtorEq] at h₃
  case _ c₁ x₁ x₂ hᵢ₁ hᵢ₂ =>
    simp [typeOf, do_eq_ok] at h₃
    rcases h₃ with ⟨_, _, h₃₁, h₃₂⟩
    specialize hᵢ₁ h₁ h₃₁
    simp [typeOfAnd] at h₃₂
    split at h₃₂ <;> simp [ok, err] at h₃₂
    case _ heq =>
      rcases h₃₂ with ⟨h₃₂, _⟩
      subst h₃₂
      simp [evaluate, ←hᵢ₁]
      generalize h₃ : evaluate x₁ request entities = res₁
      cases res₁
      case _ => simp only [Result.as, Except.bind_err]
      case _ =>
        have h₄ := type_of_is_sound h₁ h₂ h₃₁
        rcases h₄ with ⟨_, _, h₄₁, h₄₂⟩
        rw [heq] at h₄₂
        replace h₄₂ := instance_of_ff_is_false h₄₂
        subst h₄₂
        simp only [EvaluatesTo, h₃, reduceCtorEq, Except.ok.injEq, false_or] at h₄₁
        subst h₄₁
        simp only [Result.as, Coe.coe, Value.asBool, Except.bind_ok, ↓reduceIte]
    case _ heq =>
      simp [do_eq_ok] at h₃₂
      rcases h₃₂ with ⟨_, _, h₃₂₁, h₃₂₂⟩
      split at h₃₂₂ <;> simp at h₃₂₂
      all_goals
        rcases h₃₂₂ with ⟨h₃₂₂, _⟩
        subst h₃₂₂
        have h₄ := type_of_is_sound h₁ h₂ h₃₁
        rcases h₄ with ⟨h₄₁, _, h₄₂, h₄₃⟩
        simp [TypedExpr.toExpr, evaluate, ←hᵢ₁]
        generalize h₃ : evaluate x₁ request entities = res₁
        cases res₁
        case _ => simp only [Result.as, Except.bind_err]
        case _ =>
          rw [heq] at h₄₃
          rcases instance_of_bool_is_bool h₄₃ with ⟨b₁, h₄₃⟩
          simp [EvaluatesTo, h₃] at h₄₂
          subst h₄₂
          subst h₄₃
          cases b₁
          case _ =>
            simp only [Result.as, Coe.coe, Value.asBool, Except.bind_ok, ↓reduceIte]
          case _ =>
            simp [Result.as, Coe.coe, Value.asBool]
            simp [GuardedCapabilitiesInvariant] at h₄₁
            specialize h₄₁ h₃
            specialize hᵢ₂ _ (capability_union_invariant h₁ h₄₁) h₃₂₁
            simp only [hᵢ₂]
  case _ c₁ x₁ x₂ hᵢ₁ hᵢ₂ =>
    simp [typeOf, do_eq_ok] at h₃
    rcases h₃ with ⟨_, _, h₃₁, h₃₂⟩
    simp [typeOfOr] at h₃₂
    specialize hᵢ₁ h₁ h₃₁
    split at h₃₂ <;> simp [ok, err] at h₃₂
    case _ heq =>
      rcases h₃₂ with ⟨h₃₂, _⟩
      subst h₃₂
      simp [evaluate, ←hᵢ₁]
      generalize h₃ : evaluate x₁ request entities = res₁
      cases res₁
      case _ => simp [Result.as, Except.bind_err]
      case _ =>
        have h₄ := type_of_is_sound h₁ h₂ h₃₁
        rcases h₄ with ⟨_, _, h₄₁, h₄₂⟩
        rw [heq] at h₄₂
        replace h₄₂ := instance_of_tt_is_true h₄₂
        subst h₄₂
        simp only [EvaluatesTo, h₃, reduceCtorEq, Except.ok.injEq, false_or] at h₄₁
        subst h₄₁
        simp only [Result.as, Coe.coe, Value.asBool, Except.bind_ok, ↓reduceIte]
    case _ heq =>
      simp [do_eq_ok] at h₃₂
      rcases h₃₂ with ⟨_, _, h₃₂₁, h₃₂₂⟩
      specialize hᵢ₂ h₁ h₃₂₁
      split at h₃₂₂ <;> simp at h₃₂₂
      rcases h₃₂₂ with ⟨h₃₂₂, _⟩
      subst h₃₂₂
      simp only [evaluate, hᵢ₁, hᵢ₂, bind_pure_comp, TypedExpr.toExpr]
    case _ heq =>
      simp [do_eq_ok] at h₃₂
      rcases h₃₂ with ⟨_, _, h₃₂₁, h₃₂₂⟩
      specialize hᵢ₂ h₁ h₃₂₁
      split at h₃₂₂ <;> simp at h₃₂₂
      all_goals
        rcases h₃₂₂ with ⟨h₃₂₂, _⟩
        subst h₃₂₂
        have h₄ := type_of_is_sound h₁ h₂ h₃₁
        rcases h₄ with ⟨h₄₁, _, h₄₂, h₄₃⟩
        simp [TypedExpr.toExpr, evaluate, ←hᵢ₁]
        generalize h₃ : evaluate x₁ request entities = res₁
        cases res₁
        case _ => simp only [Result.as, Except.bind_err]
        case _ =>
          rw [heq] at h₄₃
          rcases instance_of_bool_is_bool h₄₃ with ⟨b₁, h₄₃⟩
          simp [EvaluatesTo, h₃] at h₄₂
          subst h₄₂
          subst h₄₃
          cases b₁
          case _ =>
            simp only [Result.as, Coe.coe, Value.asBool, hᵢ₂, Except.bind_ok, Bool.false_eq_true,
              ↓reduceIte]
          case _ =>
            simp only [Result.as, Coe.coe, Value.asBool, Except.bind_ok, ↓reduceIte]
  case _ hᵢ =>
    simp [typeOf, do_eq_ok] at h₃
    rcases h₃ with ⟨_, ⟨_, h₃₁⟩, h₃₂⟩
    simp [typeOfUnaryApp] at h₃₂
    specialize hᵢ h₁ h₃₁
    split at h₃₂ <;>
    simp [ok, err] at h₃₂ <;>
    try (
      rcases h₃₂ with ⟨h₃₂, _⟩
      subst h₃₂
      simp only [TypedExpr.toExpr, evaluate, hᵢ]
    )
  case _ hᵢ₁ hᵢ₂ =>
    simp [typeOf, do_eq_ok] at h₃
    rcases h₃ with ⟨_, ⟨_, h₃₁⟩, _, ⟨_, h₃₂⟩, h₃₃⟩
    specialize hᵢ₁ h₁ h₃₁
    specialize hᵢ₂ h₁ h₃₂
    simp [typeOfBinaryApp] at h₃₃
    split at h₃₃ <;> try simp [ok, err] at h₃₃
    any_goals
      rcases h₃₃ with ⟨h₃₃, _⟩
      subst h₃₃
      simp only [TypedExpr.toExpr, evaluate, hᵢ₁, hᵢ₂]
    any_goals
      simp [do_ok_eq_ok] at h₃₃
      rcases h₃₃ with ⟨_, h₃₃₁, h₃₃₂⟩
      subst h₃₃₂
      simp only [TypedExpr.toExpr, evaluate, hᵢ₁, hᵢ₂]
    case _ =>
      simp [typeOfEq] at h₃₃
      split at h₃₃ <;>
      split at h₃₃ <;>
      try (
        simp [ok] at h₃₃
        rcases h₃₃ with ⟨h₃₃, _⟩
        subst h₃₃
        try simp [evaluate] at hᵢ₁
        try simp [evaluate] at hᵢ₂
        simp only [TypedExpr.toExpr, evaluate, hᵢ₁, hᵢ₂]
      )
      split at h₃₃ <;> simp [ok, err] at h₃₃
      rcases h₃₃ with ⟨h₃₃, _⟩
      subst h₃₃
      simp only [TypedExpr.toExpr, evaluate, hᵢ₁, hᵢ₂]
  case _ hᵢ =>
    simp only [typeOf, do_eq_ok, Prod.exists, exists_and_right] at h₃
    rcases h₃ with ⟨ty, ⟨c, h₃₁⟩, h₃₂⟩
    simp only [typeOfHasAttr, List.empty_eq] at h₃₂
    specialize hᵢ h₁ h₃₁
    split at h₃₂
    case _ =>
      simp only [ok, do_ok_eq_ok, Prod.mk.injEq, Prod.exists, exists_eq_right_right] at h₃₂
      rcases h₃₂ with ⟨_, _, h₃₂⟩
      subst h₃₂
      simp only [TypedExpr.toExpr, evaluate, hᵢ]
    case _ => --hasAttr
      split at h₃₂ <;>
      try split at h₃₂
      case _ =>
        simp only [ok, do_ok_eq_ok, Prod.mk.injEq, Prod.exists, exists_eq_right_right] at h₃₂
        rcases h₃₂ with ⟨_, _, h₃₂⟩
        subst h₃₂
        simp only [TypedExpr.toExpr, evaluate, hᵢ]
      case _ =>
        simp only [ok, Except.ok.injEq, Prod.mk.injEq, List.nil_eq] at h₃₂
        rcases h₃₂ with ⟨h₃₂, _⟩
        subst h₃₂
        simp only [TypedExpr.toExpr, evaluate, hᵢ]
      simp only [err, reduceCtorEq] at h₃₂
    simp only [err, reduceCtorEq] at h₃₂
  case _ hᵢ => -- extHasAttr
    simp only [typeOf] at h₃
    generalize hx₁ : typeOf _ _ env = res₁ at h₃
    cases res₁ with
    | error => simp at h₃
    | ok v =>
      simp at h₃
      specialize hᵢ h₁ hx₁
      generalize hext : typeOfExtHasAttr _ _ _ _ _ = res₂ at h₃
      cases res₂ with
      | error => simp at h₃
      | ok r =>
        simp [ok] at h₃
        obtain ⟨h₃, _⟩ := h₃
        subst h₃
        simp only [TypedExpr.toExpr, evaluate, hᵢ]
  case _ hᵢ => -- getAttr
    simp only [typeOf, do_eq_ok, Prod.exists, exists_and_right] at h₃
    rcases h₃ with ⟨ty, ⟨c, h₃₁⟩, h₃₂⟩
    simp only [typeOfGetAttr] at h₃₂
    specialize hᵢ h₁ h₃₁
    split at h₃₂
    case _ =>
      simp only [ok, do_ok_eq_ok, Prod.mk.injEq, Prod.exists, exists_eq_right_right] at h₃₂
      rcases h₃₂ with ⟨_, _, h₃₂⟩
      subst h₃₂
      simp only [TypedExpr.toExpr, evaluate, hᵢ]
    case _ =>
      split at h₃₂
      simp only [ok, do_ok_eq_ok, Prod.mk.injEq, Prod.exists, exists_eq_right_right] at h₃₂
      rcases h₃₂ with ⟨_, _, h₃₂⟩
      subst h₃₂
      simp only [TypedExpr.toExpr, evaluate, hᵢ]
      simp only [err, reduceCtorEq] at h₃₂
    simp only [err, reduceCtorEq] at h₃₂
  case _ c₁ xs hᵢ =>
    simp only [typeOf, do_eq_ok] at h₃
    replace ⟨ty, h₃₁, h₃₂⟩ := h₃
    simp only [List.mapM₁_eq_mapM (fun x => justType (typeOf x c₁ env)), List.mapM_ok_iff_forall₂] at h₃₁
    simp only [typeOfSet, List.empty_eq] at h₃₂
    split at h₃₂ <;> simp only [err, reduceCtorEq] at h₃₂
    split at h₃₂ <;> simp only [ok, Except.ok.injEq, Prod.mk.injEq, List.nil_eq, reduceCtorEq] at h₃₂
    replace ⟨h₃₂, _⟩ := h₃₂
    subst h₃₂
    simp only [TypedExpr.toExpr, evaluate, List.map₁_eq_map, List.mapM₁_eq_mapM (fun x => evaluate x request entities), List.mapM_map, Function.comp_def]
    have h₄ := type_of_ok_list h₃₁ (λ x₁ h => hᵢ x₁ h h₁)
    simp only [List.forall₂_implies_mapM_eq _ _ h₄, List.mapM_cons, bind_pure_comp, bind_assoc,
      bind_map_left]
  case _ c₁ axs hᵢ =>
    simp only [typeOf, List.empty_eq, do_eq_ok] at h₃
    replace ⟨atys, h₃₁, h₃₂⟩ := h₃
    simp only [ok, Except.ok.injEq, Prod.mk.injEq, List.nil_eq] at h₃₂
    replace ⟨h₃₂, _⟩ := h₃₂
    subst h₃₂
    simp only [evaluate, List.mapM₂_eq_mapM λ (x : Attr × Expr) => bindAttr x.fst (evaluate x.snd request entities)]
    simp only [TypedExpr.toExpr, List.map₂_eq_map λ (x : Attr × TypedExpr) => (x.fst, x.snd.toExpr)]
    simp only [evaluate, List.mapM₂_eq_mapM λ (x : Attr × Expr) => bindAttr x.fst (evaluate x.snd request entities)]
    simp only [List.mapM_map, Function.comp_def]
    simp only [List.mapM₂_eq_mapM λ (x : Attr × Expr) => Except.map (fun x_1 => (x.fst, x_1.fst)) (typeOf x.snd c₁ env), List.mapM_ok_iff_forall₂] at h₃₁
    have h₄ := type_of_ok_attr_list h₃₁ (λ a₁ x₁ h => hᵢ a₁ x₁ h h₁)
    simp only [List.forall₂_implies_mapM_eq _ _ h₄]
  case _ c₁ xfn xs hᵢ =>
    simp [typeOf, do_eq_ok] at h₃
    rcases h₃ with ⟨tys, h₃₁, h₃₂⟩
    simp [List.mapM₁_eq_mapM fun x => justType (typeOf x c₁ env), List.mapM_ok_iff_forall₂] at h₃₁
    have h₄ := type_of_ok_list h₃₁ (λ x₁ h => hᵢ x₁ h h₁)
    exact type_of_preserves_evaluation_results_call h₃₂ (List.forall₂_implies_mapM_eq _ _ h₄)

end Cedar.Thm
