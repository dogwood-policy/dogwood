import Dogwood.Spec.Expr

/-!
# Leaves and the facts at their positions

`Expr.leafFacts` lists the leaves of an expression, in evaluation order, each with the facts
established at its position. `leafFacts_fst` shows the leaves are exactly `Expr.leaves`, so every
leaf of a rule has a position, and the theorems about a rule's leaves can be stated over either
list.
-/

namespace Dogwood.Thm

open Dogwood.Spec

mutual

theorem leafFacts_fst (F : List Temporal.Guard) : (x : Expr) → (x.leafFacts F).map (·.1) = x.leaves
  | .lit _ | .var _ => rfl
  | .ite a b c => by
    simp [Expr.leafFacts, Expr.leaves, leafFacts_fst F a, leafFacts_fst _ b, leafFacts_fst F c]
  | .and a b => by simp [Expr.leafFacts, Expr.leaves, leafFacts_fst F a, leafFacts_fst _ b]
  | .or a b | .binaryApp _ a b => by
    simp [Expr.leafFacts, Expr.leaves, leafFacts_fst F a, leafFacts_fst F b]
  | .unaryApp _ a | .getAttr a _ | .hasAttr a _ | .extHasAttr a _ _ => by
    simp [Expr.leafFacts, Expr.leaves, leafFacts_fst F a]
  | .set xs | .call _ xs => by simp [Expr.leafFacts, Expr.leaves, leafFactsList_fst F xs]
  | .record axs => by simp [Expr.leafFacts, Expr.leaves, leafFactsRecord_fst F axs]
  | .temporal _ | .provider _ => rfl

theorem leafFactsList_fst (F : List Temporal.Guard) : (xs : List Expr) →
    (Expr.leafFactsList F xs).map (·.1) = Expr.leavesList xs
  | [] => rfl
  | x :: xs => by
    simp [Expr.leafFactsList, Expr.leavesList, leafFacts_fst F x, leafFactsList_fst F xs]

theorem leafFactsRecord_fst (F : List Temporal.Guard) : (axs : List (Cedar.Spec.Attr × Expr)) →
    (Expr.leafFactsRecord F axs).map (·.1) = Expr.leavesRecord axs
  | [] => rfl
  | (_, x) :: axs => by
    simp [Expr.leafFactsRecord, Expr.leavesRecord, leafFacts_fst F x, leafFactsRecord_fst F axs]

end

/-- Every leaf of an expression has a position, with some facts. -/
theorem exists_leafFacts {x : Expr} {l : Leaf} (h : l ∈ x.leaves) (F : List Temporal.Guard) :
    ∃ G, (l, G) ∈ x.leafFacts F := by
  rw [← leafFacts_fst F x] at h
  obtain ⟨⟨l', G⟩, hm, rfl⟩ := List.mem_map.mp h
  exact ⟨G, hm⟩

end Dogwood.Thm
