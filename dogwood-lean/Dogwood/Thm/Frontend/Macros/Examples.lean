import Dogwood.Thm.Frontend.Macros.Safety

/-!
# The static checks are not complete for safety

`checkLeaf_iff` says the crate's static checks decide `SafeLR`, safety with each `&&` chain read
left to right. A leaf the specification finds safe can fail them for two reasons.

* **Order.** `x > 0 && P{ f: x }` reads `x` before the predicate that restricts it. Reordering
  the conjuncts fixes it (`ordered`, `misordered`).
* **Interleaving.** In

  ```
  exists (y: String). exists (z: String). (
      formerly within 1h (P{ f: z } && !Q{ g: y })
   && formerly within 1h (Q{ g: y } && !R{ h: z }))
  ```

  each conjunct restricts one variable and reads the other under a negation. The
  specification's closure restricts both (the predicates restrict whatever the negations read),
  so the leaf is safe; but each conjunct's nested chain reads, at its own position, a variable
  that only the other conjunct restricts, so no order of the two conjuncts, nor of the conjuncts
  of the nested chains, passes: `interleaved_safe`, `interleaved_rejected` (all eight orders).
  The crate rejects all eight with "variable `y` (or `z`) is used in a filter … not
  range-restricted by a preceding conjunct" (checked on the crate's own parser).
-/

namespace Dogwood.Thm.Frontend.Macros.Examples

open Dogwood.Spec.Temporal
open Dogwood.Frontend.Macros (checkLeaf)
open Cedar.Spec (EntityUID)

/-! ## On the specification's formulas -/

def act (a : String) : EntityUID := ⟨⟨"Action", ["Repo"]⟩, a⟩

def pred (a kind : String) (f : String) (x : VarName) : Formula :=
  .pred (act a) kind [([f], .var x)]

def h1 : Window := ⟨1, .hours⟩

def ex (x : VarName) (φ : Formula) : Formula := .exist ⟨x, .named ["String"]⟩ φ

def P := pred "Open" "request" "f" "z"
def Q := pred "Close" "request" "g" "y"
def R := pred "Open" "response" "h" "z"

/-- The first conjunct, and its nested chain in the other order. -/
def A := Formula.formerly h1 (.and P (.not Q))
def A' := Formula.formerly h1 (.and (.not Q) P)
/-- The second conjunct, and its nested chain in the other order. -/
def B := Formula.formerly h1 (.and Q (.not R))
def B' := Formula.formerly h1 (.and (.not R) Q)

def leaf (φ : Formula) : Formula := ex "y" (ex "z" φ)

/-- The leaf in all eight orders of its three chains. -/
def interleaved : List Formula :=
  [A, A'].flatMap fun a => [B, B'].flatMap fun b => [leaf (.and a b), leaf (.and b a)]

theorem interleaved_safe : ∀ φ ∈ interleaved, φ.IsSafe := by
  intro φ hφ
  apply (Dogwood.Thm.isSafeB_iff φ).mp
  revert φ
  decide +kernel

theorem not_safeLR_A {ρ : List VarName} (hy : "y" ∉ ρ) : ¬ ChainF ρ A ∧ ¬ ChainF ρ A' := by
  simp [A, A', P, Q, pred, ChainF, ConjF, DescF, rr, Formula.fv, Formula.argsFv,
    Term.fv, predVars, hy]

theorem not_safeLR_B {ρ : List VarName} (hz : "z" ∉ ρ) : ¬ ChainF ρ B ∧ ¬ ChainF ρ B' := by
  simp [B, B', Q, R, pred, ChainF, ConjF, DescF, rr, Formula.fv, Formula.argsFv,
    Term.fv, predVars, hz]

theorem interleaved_not_safeLR : ∀ φ ∈ interleaved, ¬ SafeLR (fun _ => False) φ := by
  have hR : (fun _ : String => False) = (· ∈ ([] : List String)) := Dogwood.Thm.pred_ext fun _ => by simp
  intro φ hφ
  rw [hR, ← chainF_factsF_iff]
  rintro ⟨hc, -⟩
  simp only [interleaved, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.mem_append,
    List.mem_cons, List.not_mem_nil, or_false] at hφ
  have ha := @not_safeLR_A [] (by simp)
  have hb := @not_safeLR_B [] (by simp)
  rcases hφ with ((rfl | rfl) | (rfl | rfl)) | ((rfl | rfl) | (rfl | rfl)) <;>
    simp only [leaf, ex, ChainF, List.filter_nil, List.nil_append] at hc <;>
    simp_all

/-- **The interleaved leaf is safe, and the static checks reject it in every order.** -/
theorem interleaved_rejected : ∀ φ ∈ interleaved, φ.IsSafe ∧
    ∀ c : Dogwood.Frontend.Surface.Temporal.Condition, c.toFormula = .ok φ → checkLeaf c ≠ .ok () :=
  fun φ hφ => ⟨interleaved_safe φ hφ, fun _ hc hk =>
    interleaved_not_safeLR φ hφ ((checkLeaf_iff hc).mp hk).1⟩

/-- Reading a variable before its restrictor: safe, and rejected. -/
def misordered : Formula := ex "x" (.and (.cmp .gt (.var "x") (.long 0)) (pred "Open" "request" "f" "x"))

/-- The same leaf with its conjuncts in the other order: safe, and accepted. -/
def ordered : Formula := ex "x" (.and (pred "Open" "request" "f" "x") (.cmp .gt (.var "x") (.long 0)))

theorem misordered_safe : misordered.IsSafe ∧ ordered.IsSafe :=
  ⟨(Dogwood.Thm.isSafeB_iff _).mp (by decide +kernel),
    (Dogwood.Thm.isSafeB_iff _).mp (by decide +kernel)⟩

theorem misordered_rejected : ¬ SafeLR (fun _ => False) misordered := by
  have hR : (fun _ : String => False) = (· ∈ ([] : List String)) := Dogwood.Thm.pred_ext fun _ => by simp
  rw [hR, ← chainF_factsF_iff]
  simp [misordered, ex, pred, ChainF, ConjF, CmpDemands, Term.fv]

theorem ordered_accepted : SafeLR (fun _ => False) ordered := by
  have hR : (fun _ : String => False) = (· ∈ ([] : List String)) := Dogwood.Thm.pred_ext fun _ => by simp
  rw [hR, ← chainF_factsF_iff]
  simp [ordered, ex, pred, ChainF, ConjF, DescTerm, CmpDemands, FactsF, TermFacts, rr, Term.fv,
    predVars]

/-! ## On the crate's syntax: the executable check -/

section Surface

open Dogwood.Frontend Dogwood.Frontend.Surface.Temporal

def sp0 : Span := ⟨0, 0⟩
def cnd (k : ConditionKind) : Condition := ⟨sp0, k⟩
def spred (a kind f x : String) : Condition :=
  cnd (.predicate ⟨sp0, ["Repo", "Action"], a, kind, [⟨f, .var x⟩]⟩)
def sh1 : WithinSpec := .concrete ⟨1, .hours⟩
def sex (x : String) (c : Condition) : Condition := cnd (.exists ⟨.name x, .named ["String"]⟩ c)

def sP := spred "Open" "request" "f" "z"
def sQ := spred "Close" "request" "g" "y"
def sR := spred "Open" "response" "h" "z"
def sA := cnd (.formerly sh1 (cnd (.and sP (cnd (.not sQ)))))
def sA' := cnd (.formerly sh1 (cnd (.and (cnd (.not sQ)) sP)))
def sB := cnd (.formerly sh1 (cnd (.and sQ (cnd (.not sR)))))
def sB' := cnd (.formerly sh1 (cnd (.and (cnd (.not sR)) sQ)))
def sleaf (c : Condition) : Condition := sex "y" (sex "z" c)

def sinterleaved : List Condition :=
  [sA, sA'].flatMap fun a => [sB, sB'].flatMap fun b => [sleaf (cnd (.and a b)), sleaf (cnd (.and b a))]

/-- The crate-shaped check rejects the interleaved leaf in all eight orders. -/
example : sinterleaved.all (fun c => !(checkLeaf c).isOk) = true := by decide +kernel

/-- It rejects the misordered leaf and accepts the ordered one. -/
example : (checkLeaf (sex "x" (cnd (.and (cnd (.comparison .gt (.var "x") (.integer 0)))
    (spred "Open" "request" "f" "x"))))).isOk = false := by decide +kernel

example : (checkLeaf (sex "x" (cnd (.and (spred "Open" "request" "f" "x")
    (cnd (.comparison .gt (.var "x") (.integer 0))))))).isOk = true := by decide +kernel

end Surface

end Dogwood.Thm.Frontend.Macros.Examples
