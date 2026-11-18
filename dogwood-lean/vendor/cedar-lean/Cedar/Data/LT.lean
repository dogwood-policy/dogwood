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

module

import Init.Classical
import Batteries.Tactic.Init
public import Batteries.Data.String
public import Batteries.Data.UInt

/-!
This file contains utilities for working with strict and decidable LT relations.
-/

namespace Cedar.Data

public class StrictLT (α) [LT α] : Prop where
  asymmetric : ∀ (a b : α), a < b → ¬ b < a
  transitive : ∀ (a b c : α), a < b → b < c → a < c
  connected  : ∀ (a b : α), a ≠ b → (a < b ∨ b < a)

public theorem StrictLT.irreflexive [LT α] [StrictLT α] (x : α) :
  ¬ x < x
:= by
  by_contra h₁
  have h₂ := StrictLT.asymmetric x x h₁
  contradiction

public theorem StrictLT.if_not_lt_gt_then_eq [LT α] [StrictLT α] (x y : α) :
  ¬ x < y → ¬ y < x → x = y
:= by
  intro h₁ h₂
  by_contra h₃
  have h₄ := StrictLT.connected x y h₃
  simp [h₁, h₂] at h₄

public theorem StrictLT.if_not_lt_eq_then_gt [LT α] [StrictLT α] (x y : α) :
  ¬ x < y → ¬ x = y → x > y
:= by
  intro h₁ h₂
  by_contra h₃
  have h₄ := StrictLT.connected x y h₂
  simp [h₁, h₃] at h₄

public theorem StrictLT.not_eq [LT α] [StrictLT α] (x y : α) :
  x < y → ¬ x = y
:= by
  intro h₁
  by_contra h₂
  subst h₂
  have h₃ := StrictLT.irreflexive x
  contradiction

end Cedar.Data

----- Theorems and instances -----

open Cedar.Data

theorem List.lt_cons_cases [LT α] [DecidableLT α] {x y : α} {xs ys : List α} :
  x :: xs < y :: ys →
  (x < y ∨ (¬ x < y ∧ ¬ y < x ∧ xs < ys))
:= by
  intro h₁
  cases h₁ <;> simp_all [lex_lt, Decidable.em]

public theorem List.cons_lt_cons [LT α] [StrictLT α] (x : α) (xs ys : List α) :
  xs < ys → x :: xs < x :: ys
:= by
  intro h₁
  apply List.Lex.cons
  simp only [lex_lt, h₁]

public theorem List.slt_irrefl [LT α] [StrictLT α] [DecidableLT α] (xs : List α) :
  ¬ xs < xs
:= by
  induction xs
  case nil => by_contra; contradiction
  case cons _ _ hd tl ih =>
    by_contra h₁
    replace h₁ := List.lt_cons_cases h₁
    simp [StrictLT.irreflexive hd] at h₁
    contradiction

public theorem List.slt_trans [LT α] [StrictLT α] {xs ys zs : List α} :
  xs < ys → ys < zs → xs < zs
:= by
  intro h₁ h₂
  cases h₁
  case nil => cases h₂ <;> apply List.Lex.nil
  case rel _ _ xhd xtl yhd ytl h₃ =>
    cases h₂ <;> apply List.Lex.rel
    case rel _ _ zhd ztl h₄ => exact StrictLT.transitive _ _ _ h₃ h₄
    case cons _ _ ztl h₄ => exact h₃
  case cons _ _ xhd xtl ytl h₃ =>
    cases h₂
    case rel _ _ zhd ztl h₆ =>
      apply List.Lex.rel
      exact h₆
    case cons _ _ ztl h₆ =>
      apply List.Lex.cons
      exact List.slt_trans h₃ h₆

public theorem List.slt_asymm [LT α] [StrictLT α] [DecidableLT α] {xs ys : List α} :
  xs < ys → ¬ ys < xs
:= by
  intro h₁
  cases xs
  case nil =>
    by_contra h₂
    contradiction
  case cons _ _ hd tl =>
    cases ys
    case nil => contradiction
    case cons _ _ hd' tl' =>
      by_contra h₂
      have h₃ := List.slt_trans h₁ h₂
      have h₄ := List.slt_irrefl (hd :: tl)
      contradiction

public theorem List.lt_conn [LT α] [StrictLT α] {xs ys : List α} :
  xs ≠ ys → (xs < ys ∨ ys < xs)
:= by
  intro h₁
  by_contra h₂
  simp only [not_or] at h₂
  replace ⟨h₂, h₃⟩ := h₂
  cases xs <;> cases ys
  case nil.nil => contradiction
  case nil.cons xhd xtl =>
    simp_all only [ne_eq, nil_eq, nil_lt_cons, not_true_eq_false]
  case cons.nil yhd ytl =>
    simp_all only [ne_eq, not_false_eq_true, not_lt_nil, nil_lt_cons, not_true_eq_false]
  case cons.cons xhd xtl yhd ytl =>
    by_cases (xhd < yhd)
    case pos h₄ =>
      have h₅ : xhd :: xtl < yhd :: ytl := List.Lex.rel h₄
      contradiction
    case neg h₄ =>
      by_cases (xhd = yhd)
      case pos h₅ =>
        subst yhd
        suffices xtl < ytl ∨ ytl < xtl by
          cases this <;> rename_i h₅
          · apply h₂ ; clear h₂
            apply List.Lex.cons ; simp only [lex_lt]
            exact h₅
          · apply h₃ ; clear h₃
            apply List.Lex.cons ; simp only [lex_lt]
            exact h₅
        apply List.lt_conn (xs := xtl) (ys := ytl)
        intro h₅
        subst ytl
        contradiction
      case neg h₅ =>
        apply h₃ ; clear h₃
        apply List.Lex.rel
        exact StrictLT.if_not_lt_eq_then_gt xhd yhd h₄ h₅

public instance List.strictLT (α) [LT α] [StrictLT α] [DecidableLT α] : StrictLT (List α) where
  asymmetric _ _   := List.slt_asymm
  transitive _ _ _ := List.slt_trans
  connected  _ _   := List.lt_conn

public def Bool.lt (a b : Bool) : Bool := match a,b with
  | false, true => true
  | _, _ => false

public instance : LT Bool where
  lt a b := Bool.lt a b

public instance Bool.decLt (a b : Bool) : Decidable (a < b) :=
  if h : Bool.lt a b then isTrue h else isFalse h

public instance Bool.strictLT : StrictLT Bool where
  asymmetric a b   := by
    simp [LT.lt, Bool.lt]
    split <;> simp
  transitive a b c := by
    simp [LT.lt, Bool.lt]
    split <;> simp
  connected  a b   := by
    simp [LT.lt, Bool.lt]
    split <;> simp only [false_eq_true, not_false_eq_true, _root_.or_false, _root_.false_or, imp_self]
    split
    · simp only [true_eq_false, not_false_eq_true, imp_self]
    · simp only [false_eq_true, imp_false, Decidable.not_not]
      cases a <;> cases b <;> simp at *

public instance Nat.strictLT : StrictLT Nat where
  asymmetric a b   := Nat.lt_asymm
  transitive a b c := Nat.lt_trans
  connected  a b   := by omega

public instance Int.strictLT : StrictLT Int where
  asymmetric a b   := by omega
  transitive a b c := Int.lt_trans
  connected  a b   := by omega

public instance UInt32.strictLT : StrictLT UInt32 where
  asymmetric a b   := by apply Nat.strictLT.asymmetric
  transitive a b c := by apply Nat.strictLT.transitive
  connected  a b   := by
    simp only [ne_eq, UInt32.ext_iff, LT.lt, Nat.lt,
      toNat_toBitVec, Nat.succ_eq_add_one, Nat.le_eq]
    apply StrictLT.connected

public instance Char.strictLT : StrictLT Char where
  asymmetric a b   := by apply UInt32.strictLT.asymmetric
  transitive a b c := by apply UInt32.strictLT.transitive
  connected  a b   := by
    intro h₁
    apply UInt32.strictLT.connected
    by_contra h₂
    have h₄ : a = b := by apply Char.ext h₂
    contradiction

public instance String.strictLT : StrictLT String where
  asymmetric a b   := by
    simp [String.lt_iff]
    have h : StrictLT (List Char) := by apply List.strictLT
    apply h.asymmetric
  transitive a b c := by
    simp [String.lt_iff]
    have h : StrictLT (List Char) := by apply List.strictLT
    apply h.transitive
  connected  a b   := by
    simp [String.lt_iff, String.ext_iff]
    have h : StrictLT (List Char) := by apply List.strictLT
    apply h.connected
