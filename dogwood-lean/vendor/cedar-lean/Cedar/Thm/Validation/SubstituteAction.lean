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
import Cedar.Thm.Data

namespace Cedar.Thm

open Cedar.Data
open Cedar.Spec
open Cedar.Validation

def SubstituteActionPreservesEvaluation (expr : Expr) (request : Request) (entities : Entities) : Prop :=
  evaluate (substituteAction request.action expr) request entities = evaluate expr request entities


theorem substitute_action_preserves_evaluation_ite {i t e : Expr} {request : Request} {entities : Entities}
  (ih₁ : SubstituteActionPreservesEvaluation i request entities)
  (ih₂ : SubstituteActionPreservesEvaluation t request entities)
  (ih₃ : SubstituteActionPreservesEvaluation e request entities) :
  evaluate (substituteAction request.action (Expr.ite i t e)) request entities =
  evaluate (Expr.ite i t e) request entities
:= by
  simp only [SubstituteActionPreservesEvaluation, substituteAction, mapOnVars] at *
  simp only [evaluate, ih₁, ih₂, ih₃]

theorem substitute_action_preserves_evaluation_getAttr {e : Expr} {attr : Attr} {request : Request} {entities : Entities}
(ih₁ : SubstituteActionPreservesEvaluation e request entities) :
  evaluate (substituteAction request.action (Expr.getAttr e attr)) request entities =
  evaluate (Expr.getAttr e attr) request entities
:= by
  simp only [SubstituteActionPreservesEvaluation] at ih₁
  simp only [substituteAction, mapOnVars] at *
  simp only [evaluate, ih₁]

theorem substitute_action_preserves_evaluation_hasAttr {e : Expr} {attr : Attr} {request : Request} {entities : Entities}
(ih₁ : SubstituteActionPreservesEvaluation e request entities) :
  evaluate (substituteAction request.action (Expr.hasAttr e attr)) request entities =
  evaluate (Expr.hasAttr e attr) request entities
:= by
  simp only [SubstituteActionPreservesEvaluation] at ih₁
  simp only [substituteAction, mapOnVars] at *
  simp only [evaluate, ih₁]

theorem substitute_action_preserves_evaluation_unaryApp {op : UnaryOp} {e : Expr} {request : Request} {entities : Entities}
(ih₁ : SubstituteActionPreservesEvaluation e request entities) :
  evaluate (substituteAction request.action (Expr.unaryApp op e)) request entities =
  evaluate (Expr.unaryApp op e) request entities
:= by
  simp only [SubstituteActionPreservesEvaluation] at ih₁
  simp only [substituteAction, mapOnVars] at *
  simp only [evaluate, ih₁]

theorem substitute_action_preserves_evaluation_binaryApp {op : BinaryOp} {a b : Expr} {request : Request} {entities : Entities}
(ih₁ : SubstituteActionPreservesEvaluation a request entities)
(ih₂ : SubstituteActionPreservesEvaluation b request entities) :
  evaluate (substituteAction request.action (Expr.binaryApp op a b)) request entities =
  evaluate (Expr.binaryApp op a b) request entities
:= by
  simp only [SubstituteActionPreservesEvaluation] at *
  simp only [substituteAction, mapOnVars] at *
  simp only [evaluate, ih₁, ih₂]

theorem substitute_action_preserves_evaluation_and {a b : Expr} {request : Request} {entities : Entities}
(ih₁ : SubstituteActionPreservesEvaluation a request entities)
(ih₂ : SubstituteActionPreservesEvaluation b request entities) :
  evaluate (substituteAction request.action (Expr.and a b)) request entities =
  evaluate (Expr.and a b) request entities
:= by
  simp only [SubstituteActionPreservesEvaluation, substituteAction, mapOnVars] at *
  simp only [evaluate, ih₁, ih₂]

theorem substitute_action_preserves_evaluation_or {a b : Expr} {request : Request} {entities : Entities}
(ih₁ : SubstituteActionPreservesEvaluation a request entities)
(ih₂ : SubstituteActionPreservesEvaluation b request entities) :
  evaluate (substituteAction request.action (Expr.or a b)) request entities =
  evaluate (Expr.or a b) request entities
:= by
  simp only [SubstituteActionPreservesEvaluation, substituteAction, mapOnVars] at *
  simp only [evaluate, ih₁, ih₂]

theorem substitute_action_nil_set : ∀ (uid : EntityUID),
  substituteAction uid (.set []) = .set []
:= by
  intro uid
  simp only [substituteAction, mapOnVars, List.map₁_eq_map, List.map_nil]

theorem substitute_action_cons_set : ∀ (h : Expr) (t : List Expr) (uid : EntityUID),
  substituteAction uid (.set (h :: t)) = .set ((substituteAction uid h) :: t.map (substituteAction uid))
:= by
  intro h t uid
  simp only [substituteAction, mapOnVars, List.map₁_eq_map, List.map_cons]
  simp only [Expr.set.injEq, List.cons.injEq, true_and]
  unfold substituteAction
  simp only

theorem substitute_action_preserves_evaluation_set {xs : List Expr} {request : Request} {entities : Entities}
(ih₁ : ∀ xᵢ, xᵢ ∈ xs → SubstituteActionPreservesEvaluation xᵢ request entities) :
  evaluate (substituteAction request.action (Expr.set xs)) request entities =
  evaluate (Expr.set xs) request entities
:= by
  cases h₀ : xs with
  | nil =>
    rw [substitute_action_nil_set]
  | cons h t =>
    simp only [SubstituteActionPreservesEvaluation] at ih₁
    have h₁ := ih₁ h
    simp only [h₀, List.mem_cons, true_or, true_implies] at h₁
    rw [substitute_action_cons_set]
    simp only [evaluate, List.mapM₁_eq_mapM (evaluate · request entities)]
    simp only [List.mapM_cons, bind_assoc, pure_bind]
    rw [h₁]
    simp only [List.mapM_map, Function.comp_def]
    have h₂ : ∀ (x₁ : Expr), x₁ ∈ t → SubstituteActionPreservesEvaluation x₁ request entities :=
    by
      simp only [h₀, List.mem_cons, forall_eq_or_imp] at ih₁
      exact ih₁.right
    simp [List.mapM_congr h₂]

theorem substitute_action_nil_record : ∀ (uid : EntityUID),
  substituteAction uid (.record []) = .record []
:= by
  intro uid
  simp only [substituteAction, mapOnVars, List.map₂_eq_map_snd, List.map_nil]

theorem substitute_action_cons_record : ∀ (ax : Attr × Expr) (axs : List (Attr × Expr)) (uid : EntityUID),
  substituteAction uid (.record (ax :: axs)) =
  .record ((ax.fst, substituteAction uid ax.snd) :: axs.map (fun (a, e) => (a, substituteAction uid e)))
:= by
  intro h t uid
  simp only [substituteAction, mapOnVars, List.map₂_eq_map_snd, List.map_cons]

theorem substitute_action_preserves_evaluation_record {axs : List (Attr × Expr)} {request : Request} {entities : Entities}
(ih₁ : ∀ axᵢ, axᵢ ∈ axs → SubstituteActionPreservesEvaluation axᵢ.snd request entities) :
  evaluate (substituteAction request.action (Expr.record axs)) request entities =
  evaluate (Expr.record axs) request entities
:= by
  cases h₀ : axs with
  | nil =>
    rw [substitute_action_nil_record]
  | cons hd tl =>
    simp only [SubstituteActionPreservesEvaluation] at ih₁
    have h₁ := ih₁ hd
    simp only [h₀, List.mem_cons, true_or, true_implies] at h₁
    rw [substitute_action_cons_record]
    simp only [evaluate, List.mapM₂_eq_mapM λ (a, e) => bindAttr a (evaluate e request entities)]
    simp only [bindAttr]
    simp only [List.mapM_cons, bind_assoc, pure_bind]
    rw [h₁]
    simp only [List.mapM_map, Function.comp_def]
    have h₂ : ∀ x ∈ tl,
    (do
      let v ← evaluate (substituteAction request.action x.snd) request entities
      pure (x.fst, v)) =
    (do
      let v ← evaluate x.snd request entities
      pure (x.fst, v))
    := by
      intro x hx
      replace (a, x) := x
      simp only [h₀, List.mem_cons, forall_eq_or_imp, Prod.forall] at ih₁
      simp [ih₁.right a x hx]
    rw [List.mapM_congr h₂]

theorem substitute_action_nil_call : ∀ (uid : EntityUID) (xfn : ExtFun),
  substituteAction uid (.call xfn []) = .call xfn [] :=
by
  intro uid
  simp only [substituteAction, mapOnVars, List.map₁_eq_map, List.map_nil, implies_true]

theorem substitute_action_cons_call : ∀ (x : Expr) (xs : List Expr) (uid : EntityUID) (xfn : ExtFun),
  substituteAction uid (.call xfn (x :: xs)) = .call xfn ((substituteAction uid x) :: xs.map (substituteAction uid)) :=
by
  intro h t uid
  simp only [substituteAction, mapOnVars, List.map₁_eq_map, List.map_cons]
  simp only [Expr.call.injEq, List.cons.injEq, true_and, forall_const]
  unfold substituteAction
  simp only


theorem substitute_action_preserves_evaluation_call {xfn : ExtFun} {xs : List Expr} {request : Request} {entities : Entities}
(ih₁ : ∀ xᵢ, xᵢ ∈ xs → SubstituteActionPreservesEvaluation xᵢ request entities) :
  evaluate (substituteAction request.action (Expr.call xfn xs)) request entities =
  evaluate (Expr.call xfn xs) request entities
:= by
  cases h₀ : xs with
  | nil =>
    rw [substitute_action_nil_call]
  | cons h t =>
    simp only [SubstituteActionPreservesEvaluation] at ih₁
    have h₁ := ih₁ h
    simp only [h₀, List.mem_cons, true_or, true_implies] at h₁
    rw [substitute_action_cons_call]
    simp only [evaluate, List.mapM₁_eq_mapM (evaluate · request entities)]
    simp only [List.mapM_cons, bind_assoc, pure_bind]
    rw [h₁]
    simp only [List.mapM_map, Function.comp_def]
    have h₂ : ∀ (x₁ : Expr), x₁ ∈ t → SubstituteActionPreservesEvaluation x₁ request entities :=
    by
      simp only [h₀, List.mem_cons, forall_eq_or_imp] at ih₁
      exact ih₁.right
    rw [List.mapM_congr h₂]

theorem substitute_action_preserves_evaluation (expr : Expr) (request : Request) (entities : Entities) :
  evaluate (substituteAction request.action expr) request entities =
  evaluate expr request entities
:= by
  cases h₀ : expr with
  | lit p => simp only [substituteAction, mapOnVars]
  | var vr =>
    cases vr <;> simp only [substituteAction, mapOnVars] ; try assumption
    case action =>
      simp [evaluate]
  | ite i t e =>
    have ih₁ := substitute_action_preserves_evaluation i request entities
    have ih₂ := substitute_action_preserves_evaluation t request entities
    have ih₃ := substitute_action_preserves_evaluation e request entities
    exact @substitute_action_preserves_evaluation_ite i t e request entities ih₁ ih₂ ih₃
  | and a b =>
    have ih₁ := substitute_action_preserves_evaluation a request entities
    have ih₂ := substitute_action_preserves_evaluation b request entities
    exact @substitute_action_preserves_evaluation_and a b request entities ih₁ ih₂
  | or a b =>
    have ih₁ := substitute_action_preserves_evaluation a request entities
    have ih₂ := substitute_action_preserves_evaluation b request entities
    exact @substitute_action_preserves_evaluation_or a b request entities ih₁ ih₂
  | unaryApp op e =>
    have ih₁ := substitute_action_preserves_evaluation e request entities
    exact @substitute_action_preserves_evaluation_unaryApp op e request entities ih₁
  | binaryApp op a b =>
    have ih₁ := substitute_action_preserves_evaluation a request entities
    have ih₂:= substitute_action_preserves_evaluation b request entities
    exact @substitute_action_preserves_evaluation_binaryApp op a b request entities ih₁ ih₂
  | getAttr x attr =>
    have ih₁ := substitute_action_preserves_evaluation x request entities
    exact @substitute_action_preserves_evaluation_getAttr x attr request entities ih₁
  | hasAttr x attr =>
    have ih₁ := substitute_action_preserves_evaluation x request entities
    exact @substitute_action_preserves_evaluation_hasAttr x attr request entities ih₁
  | extHasAttr x attr attrs =>
    have ih₁ := substitute_action_preserves_evaluation x request entities
    simp only [substituteAction] at ih₁
    simp only [substituteAction, mapOnVars, evaluate]
    rw [ih₁]
  | set xs =>
    have ih : ∀ xᵢ, xᵢ ∈ xs → SubstituteActionPreservesEvaluation xᵢ request entities := by
      intro xᵢ _
      exact @substitute_action_preserves_evaluation xᵢ request entities
    exact @substitute_action_preserves_evaluation_set xs request entities ih
  | record axs =>
    have ih : ∀ axᵢ, axᵢ ∈ axs → SubstituteActionPreservesEvaluation axᵢ.snd request entities := by
      intro axᵢ hᵢ
      have _ : sizeOf axᵢ.snd < 1 + sizeOf axs := by
        apply List.sizeOf_snd_lt_sizeOf_list hᵢ
      exact @substitute_action_preserves_evaluation axᵢ.snd request entities
    exact @substitute_action_preserves_evaluation_record axs request entities ih
  | call xfn xs =>
    have ih : ∀ xᵢ, xᵢ ∈ xs → SubstituteActionPreservesEvaluation xᵢ request entities := by
      intro xᵢ _
      exact @substitute_action_preserves_evaluation xᵢ request entities
    exact @substitute_action_preserves_evaluation_call xfn xs request entities ih

theorem substitute_action_preserves_evaluates_to {expr : Expr} {request : Request} {entities : Entities} {v : Value}:
  EvaluatesTo (substituteAction request.action expr) request entities v ↔
  EvaluatesTo expr request entities v
:= by simp only [EvaluatesTo, substitute_action_preserves_evaluation]

end Cedar.Thm
