/-!
# The crate's balanced fold

The crate joins a list of conditions or expressions with a binary operator as a balanced tree, not
a left-nested chain (`relativize.rs`, `mu`; `cedarify/mod.rs`, `emit_policy`): it pairs adjacent
items left to right, carries an odd last item up a level unchanged, and repeats until one item
remains. Four items give `(x₀ ⊕ x₁) ⊕ (x₂ ⊕ x₃)`, three `(x₀ ⊕ x₁) ⊕ x₂`, one the item itself. The
tree is ⌈log₂ n⌉ deep, and its items are in the list's order, left to right.

`pairLevel` is one round of pairing and `balancedFold` the whole fold. A property that `f`
preserves holds of the fold when it holds of every item (`balancedFold_induct`); a property that
`f` turns into a conjunction or a disjunction holds of the fold exactly when it holds of every
item (`balancedFold_all`) or of some item (`balancedFold_any`).
-/

namespace Dogwood.Frontend

universe u

variable {α : Type u}

/-- One round of the balanced fold: adjacent items paired left to right, an odd last item
carried up unchanged. -/
def pairLevel (f : α → α → α) : List α → List α
  | a :: b :: rest => f a b :: pairLevel f rest
  | l => l

theorem pairLevel_ne_nil (f : α → α → α) (x : α) (xs : List α) : pairLevel f (x :: xs) ≠ [] := by
  cases xs <;> simp [pairLevel]

theorem pairLevel_length_le (f : α → α → α) :
    ∀ (l : List α), (pairLevel f l).length ≤ l.length
  | [] | [_] => by simp [pairLevel]
  | a :: b :: rest => by
    have := pairLevel_length_le f rest
    simp only [pairLevel, List.length_cons] at this ⊢
    omega

/-- The balanced fold with a bound on the number of rounds. Each round of two or more items
shortens the list, so `xs.length` rounds suffice (`balancedFold`). The bound keeps the recursion
structural, so the fold computes in the kernel (`rfl`, `decide`). -/
def balancedFoldN (f : α → α → α) : Nat → α → List α → α
  | 0, x, _ => x
  | _ + 1, x, [] => x
  | n + 1, x, y :: ys =>
    match pairLevel f (x :: y :: ys) with
    | z :: zs => balancedFoldN f n z zs
    | [] => x

/-- The balanced fold of the non-empty list `x :: xs` with `f` (crate: the `while level.len() > 1`
loop of `mu` and `emit_policy`). -/
def balancedFold (f : α → α → α) (x : α) (xs : List α) : α :=
  balancedFoldN f xs.length x xs

/-- Every item of a round is an item of the input or `f` of two of them. -/
theorem pairLevel_induct (f : α → α → α) (P : α → Prop) (hf : ∀ a b, P a → P b → P (f a b)) :
    ∀ (l : List α), (∀ y ∈ l, P y) → ∀ y ∈ pairLevel f l, P y
  | [], h => h
  | [a], h => h
  | a :: b :: rest, h => by
    intro y hy
    simp only [pairLevel, List.mem_cons] at hy
    rcases hy with rfl | hy
    · exact hf a b (h a (by simp)) (h b (by simp))
    · exact pairLevel_induct f P hf rest (fun z hz => h z (by simp [hz])) y hy

/-- A round holds of all its items exactly when the input does, for a property `f` turns into a
conjunction. -/
theorem pairLevel_all (f : α → α → α) (Q : α → Prop) (hf : ∀ a b, Q (f a b) ↔ Q a ∧ Q b) :
    ∀ (l : List α), (∀ y ∈ pairLevel f l, Q y) ↔ ∀ y ∈ l, Q y
  | [] => Iff.rfl
  | [_] => Iff.rfl
  | a :: b :: rest => by
    have ih := pairLevel_all f Q hf rest
    simp only [pairLevel, List.mem_cons, forall_eq_or_imp, hf] at ih ⊢
    rw [ih]
    simp only [and_assoc]

/-- A round holds of some item exactly when the input does, for a property `f` turns into a
disjunction. -/
theorem pairLevel_any (f : α → α → α) (Q : α → Prop) (hf : ∀ a b, Q (f a b) ↔ Q a ∨ Q b) :
    ∀ (l : List α), (∃ y ∈ pairLevel f l, Q y) ↔ ∃ y ∈ l, Q y
  | [] => Iff.rfl
  | [_] => Iff.rfl
  | a :: b :: rest => by
    have ih := pairLevel_any f Q hf rest
    simp only [pairLevel, List.mem_cons, exists_eq_or_imp, hf] at ih ⊢
    rw [ih]
    simp only [or_assoc]

/-- Any property of the items the fold preserves round by round holds of it: `R` relates a list
of items to a value, and holds of a one-item list and its item; a round keeps it. -/
theorem balancedFoldN_rel (f : α → α → α) (R : List α → α → Prop)
    (hone : ∀ x, R [x] x) (hround : ∀ l v, l.length ≥ 2 → R (pairLevel f l) v → R l v) :
    ∀ (n : Nat) (x : α) (xs : List α), xs.length ≤ n → R (x :: xs) (balancedFoldN f n x xs)
  | 0, x, xs, h => by
    have : xs = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst this; exact hone x
  | n + 1, x, [], _ => hone x
  | n + 1, x, y :: ys, h => by
    simp only [balancedFoldN]
    split
    · rename_i z zs hp
      have hlen : zs.length ≤ n := by
        have := pairLevel_length_le f ys
        have hp' : (pairLevel f (x :: y :: ys)).length = (z :: zs).length := by rw [hp]
        simp only [pairLevel, List.length_cons] at hp' this h ⊢
        omega
      have := balancedFoldN_rel f R hone hround n z zs hlen
      rw [← hp] at this
      exact hround _ _ (by simp) this
    · rename_i hp
      exact absurd hp (pairLevel_ne_nil f x (y :: ys))

/-- **A property `f` preserves holds of the fold** when it holds of every item. -/
theorem balancedFold_induct (f : α → α → α) (P : α → Prop) (hf : ∀ a b, P a → P b → P (f a b))
    (x : α) (xs : List α) (h : ∀ y ∈ x :: xs, P y) : P (balancedFold f x xs) :=
  balancedFoldN_rel f (fun l v => (∀ y ∈ l, P y) → P v) (fun x h => h x (by simp))
    (fun l _ _ hr hl => hr (pairLevel_induct f P hf l hl)) xs.length x xs (Nat.le_refl _) h

/-- **A property `f` turns into a conjunction holds of the fold** exactly when it holds of every
item. -/
theorem balancedFold_all (f : α → α → α) (Q : α → Prop) (hf : ∀ a b, Q (f a b) ↔ Q a ∧ Q b)
    (x : α) (xs : List α) : Q (balancedFold f x xs) ↔ ∀ y ∈ x :: xs, Q y :=
  balancedFoldN_rel f (fun l v => Q v ↔ ∀ y ∈ l, Q y) (fun x => by simp)
    (fun l _ _ hr => by rw [hr, pairLevel_all f Q hf]) xs.length x xs (Nat.le_refl _)

/-- **A property `f` turns into a disjunction holds of the fold** exactly when it holds of some
item. -/
theorem balancedFold_any (f : α → α → α) (Q : α → Prop) (hf : ∀ a b, Q (f a b) ↔ Q a ∨ Q b)
    (x : α) (xs : List α) : Q (balancedFold f x xs) ↔ ∃ y ∈ x :: xs, Q y :=
  balancedFoldN_rel f (fun l v => Q v ↔ ∃ y ∈ l, Q y) (fun x => by simp)
    (fun l _ _ hr => by rw [hr, pairLevel_any f Q hf]) xs.length x xs (Nat.le_refl _)

/-! The shapes the crate's tests pin (`relativize.rs`, `mu_shape_for_up_to_three_alternatives`;
`tests/clause_fold.rs`). -/

example (f : Nat → Nat → Nat) : balancedFold f 0 [1, 2] = f (f 0 1) 2 := rfl
example (f : Nat → Nat → Nat) : balancedFold f 0 [1, 2, 3] = f (f 0 1) (f 2 3) := rfl
example (f : Nat → Nat → Nat) : balancedFold f 0 [1, 2, 3, 4] = f (f (f 0 1) (f 2 3)) 4 := rfl
example (f : Nat → Nat → Nat) :
    balancedFold f 0 [1, 2, 3, 4, 5] = f (f (f 0 1) (f 2 3)) (f 4 5) := rfl
example (f : Nat → Nat → Nat) :
    balancedFold f 0 [1, 2, 3, 4, 5, 6] = f (f (f 0 1) (f 2 3)) (f (f 4 5) 6) := rfl
example (f : Nat → Nat → Nat) :
    balancedFold f 0 [1, 2, 3, 4, 5, 6, 7] = f (f (f 0 1) (f 2 3)) (f (f 4 5) (f 6 7)) := rfl
example (f : Nat → Nat → Nat) : balancedFold f 0 [] = 0 := rfl

end Dogwood.Frontend
