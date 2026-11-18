import Dogwood.Spec.Temporal.Semantics

/-!
# Out-of-range readings and comparison operands

Facts about the reference interpreter's reading of out-of-range results, clamping
(`ImplChoices.clamp`), and about how a value is read as a comparison operand (`CVal.ofValue`).
Proofs of implementations that compute with `i64`s, as the reference interpreter does, need them.
-/

namespace Dogwood.Thm

open Dogwood.Spec Dogwood.Spec.Temporal
open Cedar.Spec (Value)

/-! ## Clamping -/

theorem clampLong_bounds (n : Int) : Int64.MIN ≤ clampLong n ∧ clampLong n ≤ Int64.MAX := by
  simp only [clampLong, Int64.MIN, Int64.MAX]; omega

theorem clampLong_idem (n : Int) : clampLong (clampLong n) = clampLong n := by
  have h := clampLong_bounds n
  unfold clampLong at h ⊢
  rw [Int.min_eq_left h.2, Int.max_eq_right h.1]

theorem toInt_ofInt_clamp (n : Int) : (Int64.ofInt (clampLong n)).toInt = clampLong n := by
  have := clampLong_bounds n
  simp only [Int64.MIN, Int64.MAX] at this
  exact Int64.toInt_ofInt_of_le (by omega) (by omega)

theorem clampLong_toInt (i : Int64) : clampLong i.toInt = i.toInt := by
  have h1 := Int64.le_toInt i
  have h2 := Int64.toInt_lt i
  simp only [clampLong, Int64.MIN, Int64.MAX]
  omega

/-- Clamping reads an out-of-range arithmetic result as the nearest `Long`, and an in-range one
as itself. -/
theorem clamp_arithValue (n : Int) :
    ImplChoices.clamp.arithValue n = some (.num (clampLong n)) := by
  simp only [ImplChoices.arithValue, ImplChoices.clamp, readLong]
  split
  · simp only [Option.some.injEq, CVal.num.injEq]
    simp only [clampLong]
    omega
  · simp

/-- Clamping reads an out-of-range aggregate total as the nearest `Long`, and an in-range one as
itself. -/
theorem clamp_aggregateValue (n : Int) :
    ImplChoices.clamp.aggregateValue n = some (.num (clampLong n)) := by
  simp only [ImplChoices.aggregateValue, ImplChoices.clamp, readLong]
  split
  · simp only [Option.some.injEq, CVal.num.injEq]
    simp only [clampLong]
    omega
  · simp

/-! ## Values as comparison operands -/

/-- A value is a `Long`, or it is compared as itself. -/
theorem ofValue_cases (a : Value) :
    (∃ i, a = .prim (.int i)) ∨ (CVal.ofValue a = .val a ∧ ∀ i, a ≠ .prim (.int i)) := by
  cases a with
  | prim p =>
    cases p with
    | int i => exact .inl ⟨i, rfl⟩
    | _ => exact .inr ⟨rfl, fun _ h => by cases h⟩
  | _ => exact .inr ⟨rfl, fun _ h => by cases h⟩

theorem ofValue_eq_num {a : Value} {m : Int} :
    CVal.ofValue a = .num m ↔ ∃ i, a = .prim (.int i) ∧ i.toInt = m := by
  rcases ofValue_cases a with ⟨i, rfl⟩ | ⟨h, _⟩
  · simp [CVal.ofValue]
  · rw [h]
    constructor
    · intro h'; cases h'
    · rintro ⟨i, rfl, _⟩; simp [CVal.ofValue] at h

/-- Reading values as comparison operands loses nothing: equal operands are equal values. -/
theorem ofValue_inj {a b : Value} : CVal.ofValue a = CVal.ofValue b ↔ a = b := by
  constructor
  · intro h
    rcases ofValue_cases a with ⟨i, rfl⟩ | ⟨ha, _⟩ <;> rcases ofValue_cases b with ⟨j, rfl⟩ | ⟨hb, _⟩
    · simp only [CVal.ofValue, CVal.num.injEq] at h
      rw [Int64.toInt_inj.mp h]
    · rw [hb] at h; simp [CVal.ofValue] at h
    · rw [ha] at h; simp [CVal.ofValue] at h
    · rw [ha, hb] at h; exact CVal.val.inj h
  · rintro rfl; rfl

end Dogwood.Thm
