import Dogwood.Frontend.SchemaJson

/-!
# Theorems about the policy-set version hash

The version hash (`Dogwood.Frontend.SchemaJson.versionHash`) digests the rules' `(policy id,
revision)` pairs and the decision kinds as sorted sequences, so it names a policy set, not an
order of its rules: it does not change when the rules are listed in another order
(`versionHash_perm`), or the decision kinds (`versionHash_kinds_perm`).
-/

namespace Dogwood.Thm.Frontend

open Dogwood.Frontend
open Dogwood.Frontend.SchemaJson

/-- Sorting with a total, transitive and antisymmetric order gives the same list for any two
permutations of each other. -/
theorem mergeSort_eq_of_perm {α : Type} (le : α → α → Bool)
    (trans : ∀ a b c, le a b → le b c → le a c) (total : ∀ a b, le a b || le b a)
    (antisymm : ∀ a b, le a b → le b a → a = b) {l₁ l₂ : List α} (h : l₁.Perm l₂) :
    l₁.mergeSort le = l₂.mergeSort le :=
  List.Perm.eq_of_pairwise (fun a b _ _ => antisymm a b)
    (List.pairwise_mergeSort trans total l₁) (List.pairwise_mergeSort trans total l₂)
    ((List.mergeSort_perm l₁ le).trans (h.trans (List.mergeSort_perm l₂ le).symm))

theorem pairLe_trans (a b c : String × String) (h₁ : pairLe a b = true) (h₂ : pairLe b c = true) :
    pairLe a c = true := by
  simp only [pairLe, Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true, beq_iff_eq] at *
  rcases h₁ with h₁ | ⟨e₁, h₁⟩ <;> rcases h₂ with h₂ | ⟨e₂, h₂⟩
  · exact .inl (String.lt_trans h₁ h₂)
  · exact .inl (e₂ ▸ h₁)
  · exact .inl (e₁ ▸ h₂)
  · exact .inr ⟨e₁.trans e₂, String.le_trans h₁ h₂⟩

theorem pairLe_total (a b : String × String) : (pairLe a b || pairLe b a) = true := by
  simp only [pairLe, Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true, beq_iff_eq]
  by_cases h : a.1 < b.1
  · exact .inl (.inl h)
  · by_cases h' : b.1 < a.1
    · exact .inr (.inl h')
    · have e : a.1 = b.1 :=
        String.le_antisymm (String.not_lt.mp h') (String.not_lt.mp h)
      rcases String.le_total a.2 b.2 with l | l
      · exact .inl (.inr ⟨e, l⟩)
      · exact .inr (.inr ⟨e.symm, l⟩)

theorem pairLe_antisymm (a b : String × String) (h₁ : pairLe a b = true) (h₂ : pairLe b a = true) :
    a = b := by
  simp only [pairLe, Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true, beq_iff_eq] at *
  rcases h₁ with h₁ | ⟨e₁, h₁⟩ <;> rcases h₂ with h₂ | ⟨e₂, h₂⟩
  · exact absurd h₂ (String.lt_asymm h₁)
  · exact absurd (e₂ ▸ h₁) (String.lt_irrefl _)
  · exact absurd (e₁ ▸ h₂) (String.lt_irrefl _)
  · exact Prod.ext e₁ (String.le_antisymm h₁ h₂)

/-- The version hash does not depend on the order in which the rules are listed. -/
theorem versionHash_perm {l₁ l₂ : List (String × String)} (h : l₁.Perm l₂)
    (schema : Option Lean.Json) (kinds : List String) (keys : List Pin) :
    versionHash l₁ schema kinds keys = versionHash l₂ schema kinds keys := by
  simp only [versionHash, versionText,
    mergeSort_eq_of_perm pairLe pairLe_trans pairLe_total pairLe_antisymm h]

/-- The version hash does not depend on the order in which the decision kinds are listed. -/
theorem versionHash_kinds_perm {k₁ k₂ : List String} (h : k₁.Perm k₂)
    (pairs : List (String × String)) (schema : Option Lean.Json) (keys : List Pin) :
    versionHash pairs schema k₁ keys = versionHash pairs schema k₂ keys := by
  have : k₁.mergeSort (fun a b => decide (a ≤ b)) = k₂.mergeSort (fun a b => decide (a ≤ b)) :=
    mergeSort_eq_of_perm _
      (fun a b c h₁ h₂ => by simp only [decide_eq_true_eq] at *; exact String.le_trans h₁ h₂)
      (fun a b => by simp only [Bool.or_eq_true, decide_eq_true_eq]; exact String.le_total a b)
      (fun a b h₁ h₂ => by simp only [decide_eq_true_eq] at *; exact String.le_antisymm h₁ h₂) h
  simp only [versionHash, versionText, sortedKinds, this]

end Dogwood.Thm.Frontend
