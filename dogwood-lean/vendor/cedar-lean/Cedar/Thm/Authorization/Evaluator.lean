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
import Cedar.Thm.Tactics
import Cedar.Thm.Data.List
import Cedar.Thm.Data.Map

/-!
This file contains useful lemmas about the `Evaluator` functions.
-/

namespace Cedar.Thm

open Cedar.Spec
open Cedar.Data

/- some shorthand to make things easier to read and write -/
/--
  `producesBool` means the expression evaluates to a bool (and not an error)
-/
def producesBool (e : Expr) (request : Request) (entities : Entities) : Prop :=
  match (evaluate e request entities) with
  | .ok (.prim (.bool _)) => true
  | _ => false
/--
  `producesNonBool` means the expression evaluates to a non-bool (and not an error)
-/
def producesNonBool (e : Expr) (request : Request) (entities : Entities) : Prop :=
  match (evaluate e request entities) with
  | .ok (.prim (.bool _)) => false
  | .error _ => false
  | _ => true

theorem and_bool_operands_is_boolean_and {b₁ b₂ : Bool} {e₁ e₂ : Expr} {request : Request} {entities : Entities} :
  evaluate e₁ request entities = .ok b₁ →
  evaluate e₂ request entities = .ok b₂ →
  evaluate (Expr.and e₁ e₂) request entities = .ok (b₁ && b₂)
:= by
  intro h₁ h₂
  simp [h₁, h₂, evaluate, Result.as, Coe.coe, Value.asBool]
  split
  · subst b₁
    simp
  · rename_i hb₁
    simp at hb₁
    subst hb₁
    simp

theorem left_false_implies_and_false {e₁ e₂ : Expr} {request : Request} {entities : Entities} :
  evaluate e₁ request entities = .ok false →
  evaluate (Expr.and e₁ e₂) request entities = .ok false
:= by
  intro h₁
  simp [h₁, evaluate, Result.as, Coe.coe, Value.asBool]

theorem left_bool_right_false_implies_and_false {e₁ e₂ : Expr} {request : Request} {entities : Entities} :
  producesBool e₁ request entities →
  evaluate e₂ request entities = .ok false →
  evaluate (Expr.and e₁ e₂) request entities = .ok false
:= by
  intro h₁ h₂
  simp only [producesBool] at h₁
  split at h₁ <;> try contradiction
  clear h₁ ; rename_i h₁
  have h₃ := and_bool_operands_is_boolean_and h₁ h₂
  simp only [h₃, Bool.and_false]

theorem and_true_implies_left_true {e₁ e₂ : Expr} {request : Request} {entities : Entities} :
  evaluate (Expr.and e₁ e₂) request entities = .ok true →
  evaluate e₁ request entities = .ok true
:= by
  intro h₁
  simp [evaluate, Result.as] at h₁
  generalize h₂ : (evaluate e₁ request entities) = r₁
  simp [h₂] at h₁
  cases r₁ <;> simp at h₁
  case ok v₁ =>
    generalize h₃ : (Coe.coe v₁ : Result Bool) = rb
    simp [h₃] at h₁
    cases rb <;> simp at h₁
    case ok b =>
      cases b <;> simp at h₁
      simp [Coe.coe, Value.asBool] at h₃
      cases v₁ <;> try simp at h₃
      case _ p₁ =>
        cases p₁ <;> simp at h₃
        simp [h₃]

theorem and_true_implies_right_true {e₁ e₂ : Expr} {request : Request} {entities : Entities} :
  evaluate (Expr.and e₁ e₂) request entities = .ok true →
  evaluate e₂ request entities = .ok true
:= by
  intro h₁
  have h₂ := and_true_implies_left_true h₁
  simp only [evaluate, Result.as, h₂, Coe.coe, Value.asBool, Bool.not_eq_eq_eq_not, Bool.not_true,
    bind_pure_comp, Except.bind_ok, Bool.true_eq_false, ↓reduceIte] at h₁
  generalize h₃ : (evaluate e₂ request entities) = r₂
  simp only [h₃] at h₁
  cases r₂
  case error => simp only [Except.map_error, reduceCtorEq] at h₁
  case ok v₂ =>
    cases v₂ <;> try simp only [Except.map_error, reduceCtorEq] at h₁
    case _ p₂ =>
      cases p₂ <;> simp only [Except.map_error, reduceCtorEq] at h₁
      case bool b =>
        cases b
        case false =>
          simp only [Except.map_ok, Except.ok.injEq, Value.prim.injEq, Prim.bool.injEq,
            Bool.false_eq_true] at h₁
        case true => rfl

/--
  If an `and` expression results in an error, it's because either:
  - the left subexpression had that error
  - the right subexpression had that error (and the left subexpression evaluated to .ok true)
  - the left subexpression evaluated to .ok with a non-bool
  - the right subexpression evaluated to .ok with a non-bool (and the left subexpression evaluated to .ok true)
-/
theorem ways_and_can_error {e₁ e₂ : Expr} {request : Request} {entities : Entities} {err : Error} :
  evaluate (Expr.and e₁ e₂) request entities = .error err →
  evaluate e₁ request entities = .error err ∨
  (evaluate e₁ request entities = .ok true ∧ evaluate e₂ request entities = .error err) ∨
  (err = Error.typeError ∧ producesNonBool e₁ request entities) ∨
  (err = Error.typeError ∧ evaluate e₁ request entities = .ok true ∧ producesNonBool e₂ request entities)
:= by
  intro h₁
  cases h_e₁ : (evaluate e₁ request entities) <;> simp [h_e₁, producesNonBool]
  case ok val =>
    cases val <;>
    simp [h_e₁, evaluate, Result.as, Coe.coe, Value.asBool] at h₁ <;>
    simp [h₁]
    case prim prim =>
      cases prim <;>
      simp at h₁ <;>
      simp [h₁]
      case bool b =>
        cases b with
        | true =>
          simp only [true_and]
          simp only [reduceCtorEq] at h₁
          cases h_e₂ : (evaluate e₂ request entities) with
          | ok val =>
            cases val <;>
            simp [h_e₂] at h₁ <;>
            simp [h₁]
            case prim prim =>
              cases prim <;>
              simp at h₁ <;>
              simp [h₁]
          | error e =>
            simp only [↓reduceIte, h_e₂, Except.map_error, Except.error.injEq] at h₁
            simp only [h₁, and_false, or_false]
        | false => simp at h₁
  case error e =>
    simp [h_e₁, evaluate, Result.as, Coe.coe, Value.asBool] at h₁
    simp [h₁]

/--
  Every `and` expression produces either .ok bool or .error
-/
theorem and_produces_bool_or_error (e₁ e₂ : Expr) (request : Request) (entities : Entities) :
  match (evaluate (Expr.and e₁ e₂) request entities) with
  | .ok (.prim (.bool _)) => true
  | .error _ => true
  | _ => false
:= by
  cases h : evaluate (Expr.and e₁ e₂) request entities <;> simp
  case ok val =>
    cases val
    <;> simp only [evaluate, Result.as, Coe.coe, Value.asBool, Bool.not_eq_true', pure, Except.pure] at h
    <;> generalize (evaluate e₁ request entities) = r₁ at h
    <;> generalize (evaluate e₂ request entities) = r₂ at h
    case prim prim =>
      cases prim <;> simp
      case int | string | entityUID =>
        split at h <;> split at h <;> simp only [Except.bind_ok, Except.bind_err, reduceCtorEq] at h
        split at h
        case _ => simp only [Except.ok.injEq, Value.prim.injEq, reduceCtorEq] at h
        case _ =>
          split at h
          case _ => split at h <;> simp only [Except.bind_ok, Except.bind_err, Except.ok.injEq, Value.prim.injEq, reduceCtorEq] at h
          case _ => simp only [Except.bind_err, reduceCtorEq] at h
    case set | record | ext =>
      exfalso
      split at h <;> split at h <;> simp only [Except.bind_ok, Except.bind_err, reduceCtorEq] at h
      split at h
      · simp only [Except.ok.injEq, reduceCtorEq] at h
      · split at h
        · split at h <;> simp only [Except.bind_ok, Except.bind_err, Except.ok.injEq, reduceCtorEq] at h
        · simp only [Except.bind_err, reduceCtorEq] at h

/--
  Corollary of the above:
  Evaluating a policy produces either .ok bool or .error
-/
theorem policy_produces_bool_or_error (p : Policy) (request : Request) (entities : Entities) :
  match (evaluate p.toExpr request entities) with
  | .ok (.prim (.bool _)) => true
  | .error _ => true
  | _ => false
:= by
  unfold Policy.toExpr
  apply and_produces_bool_or_error

/--
  If evaluating a record produces a value, then it always produces a record value.
-/
theorem record_produces_record_value {rxs : List (Attr × Expr)} {v : Value} {request : Request} {entities : Entities}
  (he : evaluate (.record rxs) request entities = .ok v) :
  ∃ rvs, .record rvs = v
:= by
  simp only [evaluate] at he
  cases he₁ : rxs.mapM₂ λ ax => bindAttr ax.val.fst (evaluate ax.val.snd request entities) <;>
  simp only [he₁, Except.bind_err, Except.bind_ok, Except.ok.injEq, reduceCtorEq] at he
  simp [←he]

/--
  If evaluating a record produces a record value containing an attribute, then
  that attribute existed in the original record, and corresponding expression
  evaluates to the same value.
 -/
theorem record_value_contains_evaluated_attrs {rxs : List (Attr × Expr)} {rvs : Map Attr Value} {a : Attr} {av : Value} {request : Request} {entities : Entities}
  (he : evaluate (.record rxs) request entities = .ok (.record rvs))
  (hfv : rvs.find? a = some av) :
  ∃ x, (Map.make rxs).find? a = some x ∧ evaluate x request entities = .ok av
:= by
  simp only [evaluate] at he
  cases he₁ : rxs.mapM₂ fun x => bindAttr x.1.fst (evaluate x.1.snd request entities) <;>
    simp only [he₁, Except.bind_err, reduceCtorEq, Except.bind_ok, Except.ok.injEq, Value.record.injEq] at he
  subst rvs
  rename_i rvs'
  replace he₁ : List.Forallᵥ (λ x y => evaluate x request entities = Except.ok y) rxs rvs' := by
    simp only [List.forallᵥ_def]
    rw [List.mapM₂_eq_mapM λ (x : Attr × Expr) => bindAttr x.fst (evaluate x.snd request entities)] at he₁
    rw [List.mapM_ok_iff_forall₂] at he₁
    apply List.Forall₂.imp _ he₁
    intro x y h
    simp only [bindAttr] at h
    simp_do_let (evaluate x.snd request entities) as hx at h
    simp only [pure, Except.pure, Except.ok.injEq] at h
    simp only [←h, and_self]
  replace he₁ := List.canonicalize_preserves_forallᵥ _ _ _ he₁
  have hfv : List.find? (λ x => x.fst == a) (Map.make rvs').toList = some (a, av) := by
    simp only [Map.find?] at hfv
    split at hfv <;> simp only [Option.some.injEq, reduceCtorEq] at hfv
    subst hfv
    rename_i a' _ hfv
    rw [(by simpa using List.find?_some hfv : a' = a)] at hfv
    exact hfv
  rw [List.forallᵥ_def] at he₁
  rw [Map.toList_make_eq_canonicalize] at hfv
  have ⟨(a', x), he₂, he₃⟩ := List.forall₂_implies_all_right he₁ (a, av) (List.mem_of_find?_eq_some hfv)
  simp only at he₃ ; replace ⟨_, he₃⟩ := he₃ ; subst a'
  exists x
  simp [Map.find?, Map.toList_make_eq_canonicalize, List.mem_of_sortedBy_implies_find? he₂ (List.canonicalize_sortedBy _ _), he₃]

end Cedar.Thm
