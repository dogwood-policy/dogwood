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

public import Cedar.Data.LT

/-!
This file defines a signed 64-bit integer datatype similar to Rust's `i64`
by adding checked arithmetic operations to Lean's Int64 datatype.
-/

namespace Int64

@[expose]
public def MIN : Int := -9223372036854775808
@[expose]
public def MAX : Int :=  9223372036854775807

----- Definitions -----

@[expose]
public def ofIntChecked (i : Int) (_ : MIN ≤ i ∧ i ≤ MAX) : Int64 :=
  Int64.ofInt i

public def ofInt? (i : Int) : Option Int64 :=
  if h : MIN ≤ i ∧ i ≤ MAX
  then .some (ofIntChecked i h)
  else .none

/-- We don't @[expose] the definition of `ofInt?`; but callers can use this
theorem, which specifies its behavior -/
public theorem ofInt?_some_iff {i : Int} :
  MIN ≤ i ∧ i ≤ MAX ↔ (ofInt? i) = some (Int64.ofInt i)
:= by simp [ofInt?, ofIntChecked]

/-- Inverse of the above -/
public theorem ofInt?_none_iff {i : Int} :
  i < MIN ∨ i > MAX ↔ (ofInt? i) = none
:= by grind [ofInt?, ofIntChecked]

public def add? (i₁ i₂ : Int64) : Option Int64 := ofInt? (i₁.toInt + i₂.toInt)

public def sub? (i₁ i₂ : Int64) : Option Int64 := ofInt? (i₁.toInt - i₂.toInt)

public def mul? (i₁ i₂ : Int64) : Option Int64 := ofInt? (i₁.toInt * i₂.toInt)

public def neg? (i₁ : Int64) : Option Int64 := ofInt? (- i₁.toInt)

public def natAbs (i₁ : Int64) : Nat := i₁.toInt.natAbs

/--
A version of Int64.mod with the property that
  b > 0 →
  ∀ a, 0 <= smod a b < b
-/
public def smod (a b : Int64) : Int64 :=
  -- this definition would work, but is hard for SymCC proofs to reason about
  -- if a % b < 0 then a % b + b else a % b
  -- BitVec.smod has the behavior we want, even though Int64.mod does not
  Int64.ofBitVec (a.toBitVec.smod b.toBitVec)

public theorem smod_result_nonneg {a b : Int64} :
  b > 0 →
  0 <= smod a b ∧ smod a b < b
:= by
  intro hb
  simp only [Int64.smod, Int64.le_iff_toInt_le, Int64.lt_iff_toInt_lt,
    Int64.toInt_ofBitVec, BitVec.toInt_smod, Int64.toInt_toBitVec]
  simp only [GT.gt, Int64.lt_iff_toInt_lt] at hb
  exact ⟨Int.fmod_nonneg_of_pos a.toInt hb, Int.fmod_lt_of_pos a.toInt hb⟩

public theorem toInt_smod (a b : Int64) : (smod a b).toInt = a.toInt.fmod b.toInt := by
  simp only [Int64.smod, Int64.toInt_ofBitVec, BitVec.toInt_smod, Int64.toInt_toBitVec]

public theorem ofInt?_toInt (v : Int64) : ofInt? v.toInt = some v := by
  simp only [ofInt?]
  have hv_lo : MIN ≤ v.toInt := by
    simp only [MIN]; rw [← toInt_toBitVec]; exact @BitVec.le_toInt 64 v.toBitVec
  have hv_hi : v.toInt ≤ MAX := by
    simp only [MAX]; rw [← toInt_toBitVec]
    have := @BitVec.toInt_lt 64 v.toBitVec; omega
  simp only [hv_lo, hv_hi, and_self, ↓reduceDIte, ofIntChecked, Int64.ofInt]
  exact congrArg some (ofInt_toInt v)

public theorem toInt_nonneg_of_ge_zero {v : Int64} (h : v ≥ 0) : v.toInt ≥ 0 := by
  simp only [GE.ge, LE.le, Int64.le, BitVec.sle, decide_eq_true_eq, toInt_toBitVec] at h
  rwa [show (0 : Int64).toInt = 0 from by native_decide] at h

public theorem toInt_neg_of_not_ge_zero {v : Int64} (h : ¬(v ≥ 0)) : v.toInt < 0 := by
  simp only [GE.ge, LE.le, Int64.le, Bool.not_eq_true] at h
  simp only [BitVec.sle, decide_eq_false_iff_not, toInt_toBitVec] at h
  have := show (0 : Int64).toInt = 0 from by native_decide
  omega

----- Derivations -----

theorem ext_iff {i₁ i₂ : Int64} : i₁ = i₂ ↔ i₁.toInt = i₂.toInt := by
  constructor <;> intro h₁
  · simp only [h₁]
  · cases i₁ ; cases i₂ ; rename_i i₁ i₂
    apply Int64.toBitVec.inj
    simp only [toInt, BitVec.toInt_inj] at h₁
    exact h₁

public theorem lt_def_toInt {i₁ i₂ : Int64} : i₁ < i₂ ↔ i₁.toInt < i₂.toInt := by
  simp only [LT.lt, Int64.lt, BitVec.slt, toInt_toBitVec, decide_eq_true_eq]

public theorem le_def_toInt {i₁ i₂ : Int64} : i₁ ≤ i₂ ↔ i₁.toInt ≤ i₂.toInt := by
  simp only [LE.le, Int64.le, BitVec.sle, toInt_toBitVec, decide_eq_true_eq]

deriving instance Repr for Int64

public instance strictLT : Cedar.Data.StrictLT Int64 where
  asymmetric a b   := by
    simp [Int64.lt_def_toInt]
    omega
  transitive a b c := by
    simp [Int64.lt_def_toInt]
    omega
  connected  a b   := by
    simp [Int64.lt_def_toInt, Int64.ext_iff]
    omega

public instance : Coe Int64 Int where
  coe i := i.toInt

end Int64
