import Dogwood.Spec.Temporal.Semantics

/-!
# Renumbering timepoints

A condition observes a timepoint's index only through equality: `tp(x)` tests whether `x` is the
current timepoint, and a comparison can only test two timepoints for equality. So renumbering the
timepoints by a bijection of the indices changes no truth value. This module builds the bijections
the slice lemma needs (`extendPerm`): one that agrees with an injective renumbering of the first `n`
timepoints, from transpositions, and the renaming of values (`TVal.rename`), of comparison operands
(`CVal.rename`), and of valuations (`Valuation.rename`) by a bijection.
-/

namespace Dogwood.Thm

open Dogwood.Spec Dogwood.Spec.Temporal

/-! ## Permutations of indices -/

/-- The transposition of `a` and `b`. -/
def swapNat (a b x : Nat) : Nat := if x = a then b else if x = b then a else x

theorem swapNat_swapNat (a b x : Nat) : swapNat a b (swapNat a b x) = x := by
  unfold swapNat
  by_cases hxa : x = a <;> by_cases hxb : x = b <;> by_cases hab : a = b <;> simp_all

theorem swapNat_left (a b : Nat) : swapNat a b a = b := by simp [swapNat]

theorem swapNat_of_ne {a b x : Nat} (ha : x ≠ a) (hb : x ≠ b) : swapNat a b x = x := by
  simp [swapNat, ha, hb]

/-- A permutation of the indices that sends `i` to `f i` for each `i < k`, built one
transposition at a time. -/
def extendPerm (f : Nat → Nat) : Nat → Nat → Nat
  | 0 => id
  | k + 1 => fun x => swapNat (extendPerm f k k) (f k) (extendPerm f k x)

/-- The inverse of `extendPerm f k`. -/
def extendPermInv (f : Nat → Nat) : Nat → Nat → Nat
  | 0 => id
  | k + 1 => fun x => extendPermInv f k (swapNat (extendPerm f k k) (f k) x)

theorem extendPermInv_extendPerm (f : Nat → Nat) : ∀ k x, extendPermInv f k (extendPerm f k x) = x
  | 0, _ => rfl
  | k + 1, x => by
    simp only [extendPerm, extendPermInv, swapNat_swapNat]
    exact extendPermInv_extendPerm f k x

theorem extendPerm_extendPermInv (f : Nat → Nat) : ∀ k x, extendPerm f k (extendPermInv f k x) = x
  | 0, _ => rfl
  | k + 1, x => by
    simp only [extendPerm, extendPermInv]
    rw [extendPerm_extendPermInv f k, swapNat_swapNat]

theorem extendPerm_inj (f : Nat → Nat) (k : Nat) {x y : Nat}
    (h : extendPerm f k x = extendPerm f k y) : x = y := by
  have := congrArg (extendPermInv f k) h
  rwa [extendPermInv_extendPerm, extendPermInv_extendPerm] at this

/-- **The permutation agrees with `f` below `k`**, when `f` is injective there. -/
theorem extendPerm_agree (f : Nat → Nat) :
    ∀ k, (∀ i j, i < k → j < k → f i = f j → i = j) → ∀ j < k, extendPerm f k j = f j
  | 0, _, _, hj => absurd hj (Nat.not_lt_zero _)
  | k + 1, hinj, j, hj => by
    have ih := extendPerm_agree f k (fun i j hi hj h => hinj i j (by omega) (by omega) h)
    simp only [extendPerm]
    rcases Nat.lt_or_ge j k with hjk | hjk
    · rw [ih j hjk]
      apply swapNat_of_ne
      · intro h
        have : extendPerm f k j = extendPerm f k k := by rw [ih j hjk]; exact h
        have := extendPerm_inj f k this
        omega
      · intro h
        have := hinj j k (by omega) (by omega) h
        omega
    · have : j = k := by omega
      subst this
      exact swapNat_left _ _

/-! ## Renaming values -/

/-- A value with its timepoint renumbered by `π`. -/
def _root_.Dogwood.Spec.Temporal.TVal.rename (π : Nat → Nat) : TVal → TVal
  | .val w => .val w
  | .tp k => .tp (π k)

/-- A comparison operand with its timepoint renumbered by `π`. -/
def _root_.Dogwood.Spec.Temporal.CVal.rename (π : Nat → Nat) : CVal → CVal
  | .tp k => .tp (π k)
  | c => c

/-- A valuation with its timepoints renumbered by `π`. -/
def _root_.Dogwood.Spec.Temporal.Valuation.rename (π : Nat → Nat) (v : Valuation) : Valuation :=
  fun x => (v x).map (TVal.rename π)

theorem TVal.rename_comp {π ρ : Nat → Nat} (h : ∀ x, ρ (π x) = x) (w : TVal) :
    (w.rename π).rename ρ = w := by
  cases w <;> simp [TVal.rename, h]

theorem TVal.rename_inj {π : Nat → Nat} (hπ : ∀ {x y}, π x = π y → x = y) {w w' : TVal}
    (h : w.rename π = w'.rename π) : w = w' := by
  cases w <;> cases w' <;> simp_all [TVal.rename]
  exact hπ h

theorem CVal.rename_inj {π : Nat → Nat} (hπ : ∀ {x y}, π x = π y → x = y) {c c' : CVal}
    (h : c.rename π = c'.rename π) : c = c' := by
  cases c <;> cases c' <;> simp_all [CVal.rename]
  exact hπ h

theorem CVal.rename_comp {π ρ : Nat → Nat} (h : ∀ x, ρ (π x) = x) (c : CVal) :
    (c.rename π).rename ρ = c := by
  cases c <;> simp [CVal.rename, h]

theorem ofTVal_rename (π : Nat → Nat) (w : TVal) :
    CVal.ofTVal (w.rename π) = (CVal.ofTVal w).rename π := by
  cases w with
  | val a =>
    simp only [TVal.rename, CVal.ofTVal]
    unfold CVal.ofValue
    split <;> rfl
  | tp k => rfl

theorem holds_rename {π : Nat → Nat} (hπ : ∀ {x y}, π x = π y → x = y) (op : CmpOp) (a b : CVal) :
    op.Holds (a.rename π) (b.rename π) ↔ op.Holds a b := by
  cases op <;> cases a <;> cases b <;> simp [CmpOp.Holds, CVal.rename] <;>
    first
    | exact ⟨fun h => hπ h, fun h => congrArg π h⟩
    | exact fun h => h ∘ congrArg π
    | exact ⟨fun h h' => h (congrArg π h'), fun h h' => h (hπ h')⟩

theorem Valuation.rename_bind (π : Nat → Nat) (v : Valuation) (x : VarName) (w : TVal) :
    (v.bind x w).rename π = (v.rename π).bind x (w.rename π) := by
  funext y
  simp only [Valuation.rename, Valuation.bind]
  split <;> rfl

theorem Valuation.rename_bindAll (π : Nat → Nat) : ∀ (v : Valuation) (xs : List VarName)
    (ws : List TVal), (v.bindAll xs ws).rename π = (v.rename π).bindAll xs (ws.map (TVal.rename π))
  | v, x :: xs, w :: ws => by
    simp only [Valuation.bindAll, List.map_cons]
    rw [Valuation.rename_bindAll π (v.bind x w) xs ws, Valuation.rename_bind]
  | _, [], _ => by simp [Valuation.bindAll]
  | _, _ :: _, [] => by simp [Valuation.bindAll]

theorem Valuation.rename_empty (π : Nat → Nat) : Valuation.empty.rename π = Valuation.empty := by
  funext x; rfl

theorem eval_rename (π : Nat → Nat) (e : Event) (v : Valuation) :
    ∀ t : Term, t.eval? e (v.rename π) = (t.eval? e v).map (TVal.rename π)
  | .var x => rfl
  | .entity _ | .long _ | .string _ | .bool _ => rfl
  | .decimal s => by simp only [Term.eval?]; cases Cedar.Spec.Ext.Decimal.parse s <;> rfl
  | .context p => by simp only [Term.eval?]; cases e.contextPath? p <;> rfl
  | .scope r p => by simp only [Term.eval?]; cases e.scopePath? r p <;> rfl
  | .wildcard | .agg _ | .arith _ _ _ => rfl

theorem summand_rename (π : Nat → Nat) (s : VarName) (names : List VarName) (row : List TVal) :
    summand s names (row.map (TVal.rename π)) = summand s names row := by
  unfold summand
  have : (names.zip (row.map (TVal.rename π))).lookup s =
      ((names.zip row).lookup s).map (TVal.rename π) := by
    induction names generalizing row with
    | nil => rfl
    | cons n ns ih =>
      cases row with
      | nil => rfl
      | cons w ws =>
        simp only [List.map_cons, List.zip_cons_cons, List.lookup]
        split <;> simp_all
  rw [this]
  cases (names.zip row).lookup s with
  | none => rfl
  | some w => cases w <;> rfl

end Dogwood.Thm
