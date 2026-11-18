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

import Cedar.Validation

namespace Cedar.Thm

/-!
This file contains some simple lemmas about the `checkLevel` and `typedAtLevel`
functions that do not need reason about the slicing functions.
-/

open Cedar.Validation
open Cedar.Data
open Cedar.Spec

def DereferencingBinaryOp : BinaryOp → Prop
  | .mem | .hasTag | .getTag => True
  | _ => False

end Cedar.Thm

namespace Cedar.Validation

open Cedar.Validation
open Cedar.Data
open Cedar.Spec
open Cedar.Thm

mutual

inductive TypedExpr.EntityAccessAtLevel (env : TypeEnv) : TypedExpr → Nat → Nat → List Attr → Prop where
  | var (v : Var) (ty : CedarType) (n nmax : Nat) (path : List Attr) :
    EntityAccessAtLevel env (.var v ty) n nmax path
  | action (ty : CedarType) (n nmax : Nat) (path : List Attr) :
    EntityAccessAtLevel env (.lit (.entityUID env.reqty.action) ty) n nmax path
  | ite (tx₁ tx₂ tx₃ : TypedExpr) (ty : CedarType)  (n nmax : Nat) (path : List Attr)
    (hl₁ : AtLevel env tx₁ nmax)
    (hl₂ : tx₂.EntityAccessAtLevel env n nmax path)
    (hl₃ : tx₃.EntityAccessAtLevel env n nmax path) :
    EntityAccessAtLevel env (.ite tx₁ tx₂ tx₃ ty) n nmax path
  | getTag (tx₁ tx₂ : TypedExpr) (ty : CedarType) (n nmax : Nat) (path : List Attr)
    (hl₁ : tx₁.EntityAccessAtLevel env n nmax [])
    (hl₂ : tx₂.AtLevel env nmax) :
    EntityAccessAtLevel env (.binaryApp .getTag tx₁ tx₂ ty) (n + 1) nmax path
  | getAttr (tx₁ : TypedExpr) (a : Attr) (ty : CedarType) (ety : EntityType) (n nmax : Nat) {path : List Attr}
    (hl₁ : tx₁.EntityAccessAtLevel env n nmax [])
    (hty : tx₁.typeOf = .entity ety) :
    EntityAccessAtLevel env (.getAttr tx₁ a ty) (n + 1) nmax path
  | getAttrRecord (tx₁ : TypedExpr) (a : Attr) (ty : CedarType) (n nmax : Nat) {path : List Attr}
    (hl₁ : tx₁.EntityAccessAtLevel env n nmax (a :: path))
    (hty : ∀ ety, tx₁.typeOf ≠ .entity ety) :
    EntityAccessAtLevel env (.getAttr tx₁ a ty) n nmax path
  | record (attrs : List (Attr × TypedExpr)) (ty : CedarType) (n nmax : Nat) {a : Attr} {path : List Attr}
    (hl₁ : ∀ atx ∈ attrs, atx.snd.AtLevel env nmax)
    (hf : (Map.make attrs).find? a = some tx)
    (hl₂ : tx.EntityAccessAtLevel env n nmax path) :
    EntityAccessAtLevel env (.record attrs ty) n nmax (a :: path)

inductive TypedExpr.AtLevel (env : TypeEnv) : TypedExpr → Nat → Prop where
  | lit (p : Prim) (ty : CedarType) (n : Nat) :
    AtLevel env (.lit p ty) n
  | var (v : Var) (ty : CedarType) (n : Nat) :
    AtLevel env (.var v ty) n
  | ite (tx₁ tx₂ tx₃ : TypedExpr) (ty : CedarType) (n : Nat)
    (hl₁ : tx₁.AtLevel env n)
    (hl₂ : tx₂.AtLevel env n)
    (hl₃ : tx₃.AtLevel env n) :
    AtLevel env (.ite tx₁ tx₂ tx₃ ty) n
  | and (tx₁ tx₂ : TypedExpr) (ty : CedarType) (n : Nat)
    (hl₁ : tx₁.AtLevel env n)
    (hl₂ : tx₂.AtLevel env n) :
    AtLevel env (.and tx₁ tx₂ ty) n
  | or (tx₁ tx₂ : TypedExpr) (ty : CedarType) (n : Nat)
    (hl₁ : tx₁.AtLevel env n)
    (hl₂ : tx₂.AtLevel env n) :
    AtLevel env (.or tx₁ tx₂ ty) n
  | unaryApp (op : UnaryOp) (tx₁ : TypedExpr) (ty : CedarType) (n : Nat)
    (hl₁ : AtLevel env tx₁ n) :
    AtLevel env (.unaryApp op tx₁ ty) n
  | mem (tx₁ tx₂ : TypedExpr) (ty : CedarType) (n : Nat)
    (hl₁ : tx₁.EntityAccessAtLevel env n (n + 1) [])
    (hl₂ : tx₂.AtLevel env (n + 1)) :
    AtLevel env (.binaryApp .mem tx₁ tx₂ ty) (n + 1)
  | getTag (tx₁ tx₂ : TypedExpr) (ty : CedarType) (n : Nat)
    (hl₁ : tx₁.EntityAccessAtLevel env n (n + 1) [])
    (hl₂ : tx₂.AtLevel env (n + 1)) :
    AtLevel env (.binaryApp .getTag tx₁ tx₂ ty) (n + 1)
  | hasTag (tx₁ tx₂ : TypedExpr) (ty : CedarType) (n : Nat)
    (hl₁ : tx₁.EntityAccessAtLevel env n (n + 1) [])
    (hl₂ : tx₂.AtLevel env (n + 1)) :
    AtLevel env (.binaryApp .hasTag tx₁ tx₂ ty) (n + 1)
  | binaryApp (op : BinaryOp) (tx₁ tx₂ : TypedExpr) (ty : CedarType) (n : Nat)
    (hop : ¬ DereferencingBinaryOp op)
    (hl₁ : tx₁.AtLevel env n)
    (hl₂ : tx₂.AtLevel env n) :
    AtLevel env (.binaryApp op tx₁ tx₂ ty) n
  | getAttr (tx₁ : TypedExpr) (a : Attr) (ty : CedarType) {ety : EntityType} (n : Nat)
    (hl₁ : tx₁.EntityAccessAtLevel env n (n + 1) [])
    (hty : tx₁.typeOf = .entity ety) :
    AtLevel env (.getAttr tx₁ a ty) (n + 1)
  | hasAttr (tx₁ : TypedExpr) (a : Attr) (ty : CedarType) {ety : EntityType} (n : Nat)
    (hl₁ : tx₁.EntityAccessAtLevel env n (n + 1) [])
    (hty : tx₁.typeOf = .entity ety) :
    AtLevel env (.hasAttr tx₁ a ty) (n + 1)
  | extHasAttr (tx₁ : TypedExpr) (a : Attr) (as : List Attr) (ty : CedarType) {ety : EntityType} (n : Nat)
    (hl₁ : tx₁.EntityAccessAtLevel env (n - extHasAttrChainCost env (.entity ety) (a :: as)) (n + 1) [])
    (hty : tx₁.typeOf = .entity ety)
    (hk : extHasAttrChainCost env (.entity ety) (a :: as) ≤ n) :
    AtLevel env (.extHasAttr tx₁ a as ty) (n + 1)
  | getAttrRecord (tx₁ : TypedExpr) (a : Attr) (ty : CedarType) (n : Nat)
    (hl₁ : tx₁.AtLevel env n)
    (hty : ∀ ety, tx₁.typeOf ≠ .entity ety) :
    AtLevel env (.getAttr tx₁ a ty) n
  | hasAttrRecord (tx₁ : TypedExpr) (a : Attr) (ty : CedarType) (n : Nat)
    (hl₁ : tx₁.AtLevel env n)
    (hty : ∀ ety, tx₁.typeOf ≠ .entity ety) :
    AtLevel env (.hasAttr tx₁ a ty) n
  | extHasAttrRecord (tx₁ : TypedExpr) (a : Attr) (as : List Attr) (ty : CedarType) (n : Nat)
    (hl₁ : tx₁.AtLevel env n)
    (hty : ∀ ety, tx₁.typeOf ≠ .entity ety)
    (hchain : ∀ rty, tx₁.typeOf = .record rty →
      extHasAttrChainCost env (.record rty) (a :: as) <= n ∧
      extHasAttrFirstEntityPath? env (.record rty) (a :: as) = none)
    : AtLevel env (.extHasAttr tx₁ a as ty) n
  | extHasAttrRecordEntity (tx₁ : TypedExpr) (a : Attr) (as : List Attr)
    (ty : CedarType) (n : Nat) (rty : RecordType) (path : List Attr)
    (hl₁ : tx₁.AtLevel env n)
    (hty : tx₁.typeOf = .record rty)
    (hk : extHasAttrChainCost env (.record rty) (a :: as) <= n)
    (hpath : extHasAttrFirstEntityPath? env (.record rty) (a :: as) = some path)
    (haccess : tx₁.EntityAccessAtLevel env
      (n - extHasAttrChainCost env (.record rty) (a :: as)) n path) :
    AtLevel env (.extHasAttr tx₁ a as ty) n
  | set (txs : List TypedExpr) (ty : CedarType) (n : Nat)
    (hl : ∀ tx ∈ txs, tx.AtLevel env n) :
    AtLevel env (.set txs ty) n
  | record (attrs : List (Attr × TypedExpr)) (ty : CedarType) (n : Nat)
    (hl : ∀ atx ∈ attrs, atx.snd.AtLevel env n) :
    AtLevel env (.record attrs ty) n
  | call (xfn : ExtFun) (args : List TypedExpr) (ty : CedarType) (n : Nat)
    (hl : ∀ tx ∈ args, tx.AtLevel env n) :
    AtLevel env (.call xfn args ty) n
end

end Cedar.Validation

namespace Cedar.Thm

open Cedar.Validation
open Cedar.Data
open Cedar.Spec

theorem entity_access_at_level_succ {path} {tx : TypedExpr} {env : TypeEnv} {n n' : Nat}
  (h₁ : tx.EntityAccessAtLevel env n n' path) :
  tx.EntityAccessAtLevel env (n + 1) n' path
:= by
  cases h₁
  case record tx attrs _ ha _ _ _ _ =>
    apply TypedExpr.EntityAccessAtLevel.record
    · assumption
    · assumption
    · rename_i path hf _ hl
      have : sizeOf tx < sizeOf attrs := by
        have h₁ := List.sizeOf_lt_of_mem ∘ Map.mem_make_mem_list ∘ Map.find?_mem_toList $ hf
        rw [Prod.mk.sizeOf_spec ha tx] at h₁
        omega
      exact entity_access_at_level_succ hl
  case getAttrRecord h₁ h₂ =>
    rename_i tx₁ a ty
    have ih : ∀ {n n'}, tx₁.EntityAccessAtLevel env n n' (a :: path) → tx₁.EntityAccessAtLevel env (n + 1) n' (a :: path) := by
      intro _ _ h
      exact entity_access_at_level_succ h
    specialize ih h₂
    apply TypedExpr.EntityAccessAtLevel.getAttrRecord <;> assumption
  all_goals
    constructor <;> first
    | assumption
    | exact entity_access_at_level_succ (by assumption)
termination_by tx

theorem entity_access_at_level_then_at_level {tx : TypedExpr} {n : Nat} {env : TypeEnv} {path : List Attr}
  (h₁ : tx.EntityAccessAtLevel env n (n + 1) path) :
  tx.AtLevel env (n + 1)
:= by
  cases h₁
  case getAttrRecord =>
    apply TypedExpr.AtLevel.getAttrRecord
    · apply entity_access_at_level_then_at_level
      assumption
    · assumption
  all_goals
    constructor <;>
    first
    | assumption
    | exact entity_access_at_level_succ (by assumption)
    | exact entity_access_at_level_then_at_level (by assumption)
termination_by tx

mutual

theorem entity_access_level_spec {tx : TypedExpr} {env : TypeEnv} {n nmax : Nat} {path : List Attr} :
  (tx.EntityAccessAtLevel env n nmax path) ↔ (tx.checkEntityAccessLevel env n nmax path)
:= by
  cases tx
  case var =>
    simp only [TypedExpr.checkEntityAccessLevel, iff_true]
    constructor
  case lit p _ =>
    cases p
    case entityUID =>
      simp only [TypedExpr.checkEntityAccessLevel, beq_iff_eq]
      apply Iff.intro
      · intro hl ; cases hl
        rfl
      · intro hl
        subst hl
        constructor
    all_goals
      simp only [TypedExpr.checkEntityAccessLevel, Bool.false_eq_true, iff_false]
      intro hc
      cases hc
  case ite tx₁ tx₂ tx₃ _ =>
    have ih₁ := @level_spec tx₁
    have ih₂ := @entity_access_level_spec tx₂
    have ih₃ := @entity_access_level_spec tx₃
    simp only [TypedExpr.checkEntityAccessLevel, Bool.and_eq_true]
    rw [←ih₁, ←ih₂, ←ih₃]
    apply Iff.intro
    · intro hl; cases hl
      and_intros <;> assumption
    · intro ⟨⟨h₁, h₂⟩, h₃⟩
      constructor <;> assumption
  case binaryApp op tx₁ tx₂ _ =>
    cases op
    case getTag =>
      have ih₁ := @entity_access_level_spec tx₁
      have ih₂ := @level_spec tx₂
      simp only [TypedExpr.checkEntityAccessLevel, gt_iff_lt, Bool.and_eq_true, decide_eq_true_eq]
      rw [←ih₁, ←ih₂]
      apply Iff.intro
      · intro hl; cases hl
        and_intros <;> first
          | assumption
          | simp only [Nat.zero_lt_succ]
      · intro ⟨ ⟨h₁, h₂⟩, h₃ ⟩
        have ⟨ n', hn ⟩  : ∃ n' : Nat , n = (n' + 1) := by simp [h₁]
        subst n
        constructor <;> assumption
    all_goals
      simp only [TypedExpr.checkEntityAccessLevel, Bool.false_eq_true, iff_false]
      intro hc
      cases hc
  case getAttr tx₁ a ty =>
    simp only [TypedExpr.checkEntityAccessLevel]
    split
    · have ih₁ := @entity_access_level_spec tx₁
      simp only [←ih₁, gt_iff_lt, Bool.and_eq_true, decide_eq_true_eq]
      apply Iff.intro
      · intro hl
        cases hl
        · apply And.intro
          · simp only [Nat.zero_lt_succ]
          · simp only [Nat.add_one_sub_one]
            assumption
        · rename_i h₂ h₁ _
          simp [h₂] at h₁
      · intro ⟨h₁, h₂⟩
        have ⟨ n', hn ⟩  : ∃ n' : Nat , n = (n' + 1) := by simp [h₁]
        subst n
        apply TypedExpr.EntityAccessAtLevel.getAttr
        · simpa using h₂
        · assumption
    · have ih₁ := @entity_access_level_spec tx₁
      rw [←ih₁]
      apply Iff.intro
      · intro hl
        cases hl
        · rename_i h₁ _ _ h₂ _
          simp only [h₂, CedarType.entity.injEq, imp_false, forall_eq'] at h₁
        · assumption
      · intro hl
        apply TypedExpr.EntityAccessAtLevel.getAttrRecord <;> assumption
  case record atxs _ =>
    cases path
    case nil =>
      simp only [TypedExpr.checkEntityAccessLevel, Bool.false_eq_true, iff_false]
      intro hc
      cases hc
    case cons =>
      simp only [TypedExpr.checkEntityAccessLevel]
      split <;> simp only [iff_false, Bool.and_eq_true, Bool.false_eq_true, List.all_eq_true, Subtype.forall, Prod.forall]
      · apply Iff.intro
        · intro hl
          cases hl
          rename_i tx h₁ tx' h₃ h₄ h₅
          replace h₄ : tx = tx' := by
            simpa [h₁] using h₄
          subst tx
          and_intros
          · have : sizeOf tx' < 1 + sizeOf atxs := by
              replace h₁ := List.sizeOf_lt_of_mem ∘ Map.mem_make_mem_list ∘ Map.find?_mem_toList $ h₁
              rw [Prod.mk.sizeOf_spec _ tx'] at h₁
              omega
            have ih := @entity_access_level_spec tx'
            exact ih.mp h₅
          · intros
            rename_i a tx _ h₂
            replace h₂ : (a, tx) ∈ atxs := by
              simpa [List.attach₂] using h₂
            have ih := @level_spec tx
            exact ih.mp (h₃ _ h₂)
        · intro ⟨ h₁, h₂ ⟩
          constructor
          · intro atx hatx
            have hSizeOf : sizeOf atx.snd < 1 + sizeOf atxs := by
              have h₄ := List.sizeOf_lt_of_mem hatx
              rw [Prod.mk.sizeOf_spec _ atx.snd] at h₄
              omega
            replace h₂ : atx.snd.checkLevel env nmax = true := by
              specialize h₂ atx.fst atx.snd hSizeOf
              replace h₂ : atx ∈ atxs → atx.snd.checkLevel env nmax = true := by
                simpa [List.attach₂] using h₂
              exact h₂ hatx
            have ih := @level_spec atx.snd
            exact ih.mpr h₂
          · assumption
          · rename_i a _ tx hf
            have : sizeOf tx < 1 + sizeOf atxs := by
              replace h₁ := List.sizeOf_lt_of_mem ∘ Map.mem_make_mem_list ∘ Map.find?_mem_toList $ hf
              rw [Prod.mk.sizeOf_spec _ tx] at h₁
              omega
            have ih := @entity_access_level_spec tx
            exact ih.mpr h₁
      · intro hc
        cases hc
        rename_i h₁ _ _ h₂ _
        simp [h₁] at h₂
  all_goals
    simp only [TypedExpr.checkEntityAccessLevel, Bool.false_eq_true, iff_false]
    intro hc
    cases hc
termination_by tx

theorem level_spec {tx : TypedExpr} {env : TypeEnv} {n : Nat}:
  (tx.AtLevel env n) ↔ (tx.checkLevel env n = true)
:= by
  cases tx
  case lit =>
    simp only [TypedExpr.checkLevel, iff_true]
    constructor
  case var =>
    simp only [TypedExpr.checkLevel, iff_true]
    constructor
  case ite tx₁ tx₂ tx₃ _ =>
    have ih₁ := @level_spec tx₁
    have ih₂ := @level_spec tx₂
    have ih₃ := @level_spec tx₃
    simp only [TypedExpr.checkLevel, Bool.and_eq_true]
    rw [←ih₁, ←ih₂, ←ih₃]
    apply Iff.intro
    · intros h
      cases h
      and_intros <;> assumption
    · intro ⟨⟨h₁, h₂⟩, h₃⟩
      constructor <;> assumption

  case or tx₁ tx₂ _ | and tx₁ tx₂ _ =>
    have ih₁ := @level_spec tx₁
    have ih₂ := @level_spec tx₂
    simp only [TypedExpr.checkLevel, Bool.and_eq_true]
    rw [←ih₁, ←ih₂]
    apply Iff.intro
    · intro h
      cases h
      constructor <;> assumption
    · intro ⟨ h₁, h₂ ⟩
      constructor <;> assumption

  case unaryApp op tx₁ _ =>
    have ih₁ := @level_spec tx₁
    simp only [TypedExpr.checkLevel]
    rw [←ih₁]
    apply Iff.intro
    · intro h
      cases h
      assumption
    · intro h₁
      constructor
      assumption

  case binaryApp op tx₁ tx₂ _ =>
    cases op
    case getTag | hasTag | mem =>
      have ih₁ := @entity_access_level_spec tx₁
      have ih₂ := @level_spec tx₂
      simp only [TypedExpr.checkLevel, gt_iff_lt, Bool.and_eq_true, decide_eq_true_eq]
      rw [←ih₁, ←ih₂]
      apply Iff.intro
      · intro h
        cases h
        rename_i h₁ h₂ h₃
        and_intros <;> first
        | assumption
        | simp only [Nat.zero_lt_succ]
        rename_i hop _ _
        simp [DereferencingBinaryOp] at hop
      · intro ⟨ ⟨ h₁, h₂⟩, h₃ ⟩
        have ⟨ n', hn ⟩  : ∃ n' : Nat , n = (n' + 1) := by simp [h₁]
        subst n
        constructor <;> assumption
    all_goals
      have ih₁ := @level_spec tx₁
      have ih₂ := @level_spec tx₂
      simp only [TypedExpr.checkLevel, Bool.and_eq_true]
      rw [←ih₁, ←ih₂]
      apply Iff.intro
      · intro h
        cases h
        apply And.intro <;> assumption
      · intro ⟨ h₁, h₂ ⟩
        constructor <;> first
        | assumption
        | simp only [DereferencingBinaryOp, not_false_eq_true]

  case getAttr tx₁ a _ | hasAttr tx₁ a _ =>
    simp only [TypedExpr.checkLevel, gt_iff_lt]
    split <;> (rename_i hety ; apply Iff.intro)
    · intro h
      cases h
      · simp only [Nat.zero_lt_succ, decide_true, Bool.true_and]
        have ih₁ := @entity_access_level_spec tx₁
        rw [←ih₁]
        assumption
      · rename_i hnety _
        simp [hety] at hnety
    · have ih₁ := @entity_access_level_spec tx₁
      simp only [Bool.and_eq_true, decide_eq_true_eq, and_imp]
      rw [←ih₁]
      intro h₁ h₂
      have ⟨ n', hn ⟩  : ∃ n' : Nat , n = (n' + 1) := by simp [h₁]
      subst n
      constructor <;> assumption
    · intro h
      cases h
      · rename_i hety'
        simp [hety'] at hety
      · have ih₁ := @level_spec tx₁
        rw [←ih₁]
        assumption
    · intro h
      have ih₁ := @level_spec tx₁
      rw [←ih₁] at h
      constructor <;> assumption

  case extHasAttr tx₁ a attrs _ =>
    simp only [TypedExpr.checkLevel, gt_iff_lt]
    constructor
    · -- forward: AtLevel → checkLevel = true
      intro h
      cases h with
      | extHasAttr _ _ _ _ n_inner hl₁ hty  hk =>
        rename_i ety
        simp only [hty]
        simp only [Bool.and_eq_true, decide_eq_true_eq]
        refine ⟨by omega, ?_⟩
        rw [←entity_access_level_spec]
        have heq : n_inner + 1 - extHasAttrChainCost env (.entity ety) (a :: attrs) - 1 =
            n_inner - extHasAttrChainCost env (.entity ety) (a :: attrs) := by omega
        exact heq ▸ hl₁
      | extHasAttrRecord _ _ _ _ _ hl₁ hnety hchain =>
        have hne : ∀ ety, tx₁.typeOf ≠ .entity ety := hnety
        split
        · rename_i ety heq
          exfalso; exact hne ety heq
        · rename_i rty heq
          simp only [Bool.and_eq_true, decide_eq_true_eq]
          obtain ⟨hlt, hpath⟩ := hchain rty heq
          exact ⟨⟨by simp [hpath], hlt⟩, level_spec.mp hl₁⟩
        · rw [←level_spec]; exact hl₁
      | extHasAttrRecordEntity _ _ _ _ _ rty path hl₁ hrty hk hpath haccess =>
        simp only [hrty, Bool.and_eq_true, decide_eq_true_eq]
        exact ⟨⟨
          by simp only [hpath]; exact entity_access_level_spec.mp haccess,
          hk⟩,
          level_spec.mp hl₁
        ⟩
    · -- backward: checkLevel = true → AtLevel
      intro h
      split at h
      · -- entity branch
        rename_i ety heq
        simp only [Bool.and_eq_true, decide_eq_true_eq] at h
        obtain ⟨h₁, h₂⟩ := h
        have ⟨n', hn⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
        subst hn
        rw [←entity_access_level_spec] at h₂
        have hk : extHasAttrChainCost env (.entity ety) (a :: attrs) ≤ n' := by omega
        have h₂' : tx₁.EntityAccessAtLevel env (n' - extHasAttrChainCost env (.entity ety) (a :: attrs)) (n' + 1) [] := by
          have heq2 : n' + 1 - extHasAttrChainCost env (.entity ety) (a :: attrs) - 1 =
                     n' - extHasAttrChainCost env (.entity ety) (a :: attrs) := by omega
          exact heq2 ▸ h₂
        exact TypedExpr.AtLevel.extHasAttr tx₁ a attrs _ n' h₂' heq hk
      · -- record branch
        rename_i rty heq
        simp only [Bool.and_eq_true, decide_eq_true_eq] at h
        obtain ⟨⟨hpathcheck, h₁⟩, hlvl⟩ := h
        rw [←level_spec] at hlvl
        cases hpath : extHasAttrFirstEntityPath? env (.record rty) (a :: attrs) with
        | none =>
          have hnotety : ∀ ety, tx₁.typeOf ≠ .entity ety := by
            intro ety he; simp [heq] at he
          exact .extHasAttrRecord tx₁ a attrs _ _ hlvl hnotety (fun rty' hrty' => by
            have : rty = rty' := by
              have := heq ▸ hrty'
              exact CedarType.record.inj this
            subst rty'
            exact ⟨h₁, hpath⟩)
        | some path =>
          have haccess : tx₁.EntityAccessAtLevel env
              (n - extHasAttrChainCost env (.record rty) (a :: attrs)) n path := by
            rw [entity_access_level_spec]
            simpa [hpath] using hpathcheck
          exact .extHasAttrRecordEntity tx₁ a attrs _ _ rty path hlvl heq h₁ hpath haccess
      · -- other branch
        rename_i hne
        rw [←level_spec] at h
        have hnotety : ∀ ety, tx₁.typeOf ≠ .entity ety := by
          intro ety he
          have : ∀ ety, tx₁.typeOf = .entity ety → False := by assumption
          exact this ety he
        exact .extHasAttrRecord tx₁ a attrs _ _ h hnotety (fun rty hrty => by
          have : ∀ rty, tx₁.typeOf = .record rty → False := by assumption
          exact absurd hrty (this rty))

  case call | set =>
    simp only [TypedExpr.checkLevel, List.all_eq_true, List.mem_attach, forall_const, Subtype.forall]
    apply Iff.intro
    · intro h₁ tx h₂
      have ih := @level_spec tx
      cases h₁
      rename_i h₃
      specialize h₃ tx h₂
      rw [←ih]
      exact h₃
    · intro h₁
      constructor
      intro tx h₂
      have _ := List.sizeOf_lt_of_mem h₂
      have ih := @level_spec tx
      rw [ih]
      exact h₁ tx h₂

  case record attrs _ =>
    simp only [TypedExpr.checkLevel, List.all_eq_true, Subtype.forall, Prod.forall]
    apply Iff.intro
    · intro h₁ a tx h₂ h₃
      replace h₃ : (a, tx) ∈ attrs :=
        by simpa [List.attach₂] using h₃
      cases h₁
      rename_i h₄
      specialize h₄ (a, tx) h₃
      have ih := @level_spec tx
      exact ih.mp h₄
    · intro h₁
      constructor
      intro atx h₂
      have hSizeOf : sizeOf atx.snd < 1 + sizeOf attrs := by
        have h₄ := List.sizeOf_lt_of_mem h₂
        rw [Prod.mk.sizeOf_spec atx.fst atx.snd] at h₄
        omega
      replace h₁ : atx.snd.checkLevel env n := by
        specialize h₁ atx.fst atx.snd hSizeOf
        replace h₁ : atx ∈ attrs → atx.snd.checkLevel env n= true := by
          simpa [List.attach₂] using h₁
        exact h₁ h₂
      have ih := @level_spec atx.snd
      exact ih.mpr h₁
termination_by tx

end
