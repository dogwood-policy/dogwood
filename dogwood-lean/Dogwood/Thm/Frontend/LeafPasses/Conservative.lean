import Dogwood.Thm.Frontend.LeafPasses.Basic

/-!
# The extended relation extends the specification's satisfaction

`XSat` with timepoints unordered (`ord = false`) and binders ranging over every value
(`anyValue`) is the specification's `Sat` on every condition that projects to a formula
(`xsat_iff_sat`): `or`, the orderings of timepoints and the sorted reading are its only additions.
-/

namespace Dogwood.Thm.Frontend

open Dogwood.Frontend Dogwood.Frontend.LeafPasses Surface.Temporal
open Dogwood.Spec (Event Trace TickRate)
open Dogwood.Spec.Temporal (Valuation ImplChoices Sat Denotes Total Formula Aggregate CVal CmpOp)

theorem xHolds_false (op : CmpOp) (a b : CVal) : xHolds false op a b ↔ op.Holds a b := by
  simp [xHolds]

theorem rowIn_anyValue (bs : List Dogwood.Spec.Temporal.Binder) (row : List Dogwood.Spec.Temporal.TVal) :
    RowIn anyValue bs row ↔ True := by
  simp [RowIn, anyValue]

section
variable {ι : ImplChoices} {rate : TickRate} {σ : Trace} {e : Event} {vis : Nat → Prop}

theorem denotes_atom {t' : Dogwood.Spec.Temporal.Term} (ht : SpecAtom t') (v : Valuation) (j : Nat) (c : CVal) :
    Denotes ι rate σ e vis v j t' c ↔ ∃ w, t'.eval? e v = some w ∧ c = CVal.ofTVal w := by
  cases t' <;> first | exact absurd ht id | exact Iff.rfl

theorem xdenotes_atom_iff (t : Surface.Temporal.Term) (ht : TermAtom t) {t' : Dogwood.Spec.Temporal.Term}
    (h : t.toSpec = .ok t') (v : Valuation) (j : Nat) (c : CVal) :
    XDenotes ι rate σ e vis false anyValue v j t c ↔ Denotes ι rate σ e vis v j t' c := by
  have hx : XDenotes ι rate σ e vis false anyValue v j t c ↔
      ∃ t'', t.toSpec = .ok t'' ∧ ∃ w, t''.eval? e v = some w ∧ c = CVal.ofTVal w := by
    cases t <;> first | exact absurd ht id | exact Iff.rfl
  rw [hx, denotes_atom (toSpec_atom ht h), h]
  simp

mutual

/-- **The extended relation is the specification's satisfaction** on every condition that
projects to a formula, with timepoints unordered and binders ranging over every value. -/
theorem xsat_iff_sat : (c : Condition) → {φ : Formula} → c.toFormula = .ok φ → ∀ (v : Valuation) (j : Nat),
    (XSat ι rate σ e vis false anyValue v j c ↔ Sat ι rate σ e vis v j φ)
  | ⟨_, .and l r⟩, φ, h, v, j => by
    simp only [Condition.toFormula, ConditionKind.toFormula, bind_eq_ok, pure_eq_ok] at h
    obtain ⟨a, ha, b, hb, rfl⟩ := h
    simp only [XSat, Sat, xsat_iff_sat l ha, xsat_iff_sat r hb]
  | ⟨_, .or l r⟩, φ, h, v, j => by
    simp [Condition.toFormula, ConditionKind.toFormula] at h
  | ⟨_, .not c⟩, φ, h, v, j => by
    simp only [Condition.toFormula, ConditionKind.toFormula, bind_eq_ok, pure_eq_ok] at h
    obtain ⟨a, ha, rfl⟩ := h
    simp only [XSat, Sat, xsat_iff_sat c ha]
  | ⟨_, .formerly w c⟩, φ, h, v, j => by
    simp only [Condition.toFormula, ConditionKind.toFormula, bind_eq_ok, pure_eq_ok] at h
    obtain ⟨win, hw, a, ha, rfl⟩ := h
    simp only [XSat, Sat, hw, xsat_iff_sat c ha]
    simp
  | ⟨_, .previous w c⟩, φ, h, v, j => by
    simp only [Condition.toFormula, ConditionKind.toFormula, bind_eq_ok, pure_eq_ok] at h
    obtain ⟨win, hw, a, ha, rfl⟩ := h
    simp only [XSat, Sat, hw, xsat_iff_sat c ha]
    simp
  | ⟨_, .since l w r⟩, φ, h, v, j => by
    simp only [Condition.toFormula, ConditionKind.toFormula, bind_eq_ok, pure_eq_ok] at h
    obtain ⟨a, ha, win, hw, b, hb, rfl⟩ := h
    simp only [XSat, Sat, hw, xsat_iff_sat l ha, xsat_iff_sat r hb]
    simp
  | ⟨_, .predicate ⟨_, ns, a, k, args⟩⟩, φ, h, v, j => by
    simp only [Condition.toFormula, ConditionKind.toFormula, bind_eq_ok, pure_eq_ok] at h
    obtain ⟨uid, hu, args', ha, rfl⟩ := h
    simp only [XSat, Sat, hu, ha]
    simp
  | ⟨_, .comparison op l r⟩, φ, h, v, j => by
    simp only [Condition.toFormula, ConditionKind.toFormula, bind_eq_ok, pure_eq_ok] at h
    obtain ⟨l', hl, r', hr, rfl⟩ := h
    simp only [XSat, Sat, xHolds_false]
    exact exists_congr fun a => exists_congr fun b =>
      and_congr (xdenotes_iff_denotes l hl v j a) (and_congr_left' (xdenotes_iff_denotes r hr v j b))
  | ⟨_, .exists ⟨s, ty⟩ c⟩, φ, h, v, j => by
    simp only [Condition.toFormula, ConditionKind.toFormula, TypedBinder.toSpec, bind_eq_ok, pure_eq_ok] at h
    obtain ⟨x, ⟨n, hn, rfl⟩, a, ha, rfl⟩ := h
    simp only [XSat, Sat, hn, anyValue]
    simp only [Except.ok.injEq, true_and, exists_eq_left']
    exact exists_congr fun w => xsat_iff_sat c ha _ j
  | ⟨_, .tp s⟩, φ, h, v, j => by
    simp only [Condition.toFormula, ConditionKind.toFormula, bind_eq_ok, pure_eq_ok] at h
    obtain ⟨x, hx, rfl⟩ := h
    simp [XSat, Sat, hx]
  | ⟨_, .call _⟩, φ, h, v, j => by simp [Condition.toFormula, ConditionKind.toFormula] at h
  | ⟨_, .sigilRef _ _⟩, φ, h, v, j => by simp [Condition.toFormula, ConditionKind.toFormula] at h
  | ⟨_, .refine _ _ _⟩, φ, h, v, j => by simp [Condition.toFormula, ConditionKind.toFormula] at h

theorem xdenotes_iff_denotes : (t : Surface.Temporal.Term) → {t' : Dogwood.Spec.Temporal.Term} → t.toSpec = .ok t' →
    ∀ (v : Valuation) (j : Nat) (c : CVal),
    (XDenotes ι rate σ e vis false anyValue v j t c ↔ Denotes ι rate σ e vis v j t' c)
  | .agg ⟨_, k⟩, t', h, v, j, c => by
    simp only [Surface.Temporal.Term.toSpec, bind_eq_ok, pure_eq_ok] at h
    obtain ⟨a, ha, rfl⟩ := h
    simp only [XDenotes, Denotes]
    exact exists_congr fun n => and_congr_left' (xtotal_iff_total k ha v j n)
  | .arith op l r, t', h, v, j, c => by
    simp only [Surface.Temporal.Term.toSpec, bind_eq_ok, pure_eq_ok] at h
    obtain ⟨l', hl, r', hr, rfl⟩ := h
    simp only [XDenotes, Denotes]
    exact exists_congr fun m => exists_congr fun n =>
      and_congr (xdenotes_iff_denotes l hl v j _) (and_congr_left' (xdenotes_iff_denotes r hr v j _))
  | .entity x0 x1, _, h, v, j, c => xdenotes_atom_iff (.entity x0 x1) trivial h v j c
  | .integer x0, _, h, v, j, c => xdenotes_atom_iff (.integer x0) trivial h v j c
  | .decimal x0, _, h, v, j, c => xdenotes_atom_iff (.decimal x0) trivial h v j c
  | .string x0, _, h, v, j, c => xdenotes_atom_iff (.string x0) trivial h v j c
  | .bool x0, _, h, v, j, c => xdenotes_atom_iff (.bool x0) trivial h v j c
  | .contextField x0, _, h, v, j, c => xdenotes_atom_iff (.contextField x0) trivial h v j c
  | .scopeField x0, _, h, v, j, c => xdenotes_atom_iff (.scopeField x0) trivial h v j c
  | .var x0, _, h, v, j, c => xdenotes_atom_iff (.var x0) trivial h v j c
  | .wildcard, _, h, v, j, c => xdenotes_atom_iff .wildcard trivial h v j c
  | .array x0, _, h, v, j, c => xdenotes_atom_iff (.array x0) trivial h v j c
  | .paramRef x0, _, h, v, j, c => xdenotes_atom_iff (.paramRef x0) trivial h v j c
  | .binderRef x0, _, h, v, j, c => xdenotes_atom_iff (.binderRef x0) trivial h v j c

theorem xtotal_iff_total : (k : AggExprKind) → {a : Aggregate} → AggExprKind.toSpec k = .ok a →
    ∀ (v : Valuation) (j : Nat) (n : Int),
    (XTotal ι rate σ e vis false anyValue v j k n ↔ Total ι rate σ e vis v j a n)
  | .count vs b, a, h, v, j, n => by
    simp only [AggExprKind.toSpec, bind_eq_ok, pure_eq_ok] at h
    obtain ⟨bs, hbs, body, hb, rfl⟩ := h
    simp only [XTotal, Total, hbs, rowIn_anyValue, true_and, Except.ok.injEq, exists_eq_left']
    refine exists_congr fun rows => and_congr_right' (and_congr_left' (forall_congr' fun row => ?_))
    exact iff_congr Iff.rfl (and_congr_right' (xsat_iff_sat b hb _ j))
  | .sum s vs b, a, h, v, j, n => by
    simp only [AggExprKind.toSpec, bind_eq_ok, pure_eq_ok] at h
    obtain ⟨x, hx, bs, hbs, body, hb, rfl⟩ := h
    simp only [XTotal, Total, hx, hbs, rowIn_anyValue, true_and, Except.ok.injEq, exists_and_left,
      exists_eq_left']
    refine exists_congr fun rows => and_congr_right' (and_congr_left' (forall_congr' fun row => ?_))
    exact iff_congr Iff.rfl (and_congr_right' (xsat_iff_sat b hb _ j))
  | .call _, a, h, v, j, n => by simp [AggExprKind.toSpec] at h

end
end
end Dogwood.Thm.Frontend
