import Dogwood.Thm.Frontend.Validate.Interface
import Dogwood.Thm.ScopesDecide

/-!
# The crate's time-dependence check decides time dependence

The crate's `check_tp_dependence` (ported as `Validate.checkTpDependence`) computes, for each
top-level conjunct of a leaf, whether it varies with the timepoint and the degenerate monitoring
scopes inside it (`Validate.tpDep`). Whether it varies is the specification's
`Formula.variesB` (`tpDep_fst`), and it finds no degenerate scope exactly when every monitoring
scope inside varies (`tpDep_snd_eq_nil_iff`). So the check finds nothing exactly when the leaf
monitors time (`checkTpDependence_eq_nil_iff`).
-/

namespace Dogwood.Thm.Frontend

open Dogwood.Frontend.Validate
open Dogwood.Spec Dogwood.Spec.Temporal

/-- Whether a condition varies with the timepoint, as the crate's check computes it, is the
specification's `Formula.variesB`. -/
theorem tpDep_fst (E : List VarName) : (φ : Formula) → (tpDep E φ).1 = φ.variesB E
  | .pred _ _ _ | .tp _ => by simp [tpDep, Formula.variesB]
  | .cmp _ l r => by simp [tpDep, Formula.variesB]
  | .not φ => by simp only [tpDep, Formula.variesB]; exact tpDep_fst E φ
  | .and φ ψ => by simp [tpDep, Formula.variesB, tpDep_fst E φ, tpDep_fst E ψ]
  | .formerly _ _ | .previous _ _ | .since _ _ _ | .exist _ _ => by
    simp [tpDep, Formula.variesB]

mutual

/-- The crate's check finds no degenerate scope inside a condition exactly when every monitoring
scope inside it varies with the timepoint. -/
theorem tpDep_snd_eq_nil_iff : (E : List VarName) → (φ : Formula) →
    ((tpDep E φ).2 = [] ↔ φ.scopesVaryB E = true)
  | E, .pred _ _ _ | E, .tp _ => by simp [tpDep, Formula.scopesVaryB]
  | E, .cmp _ l r => by
    simp [tpDep, Formula.scopesVaryB, tpDepT_eq_nil_iff E l, tpDepT_eq_nil_iff E r]
  | E, .not φ => by simp only [tpDep, Formula.scopesVaryB]; exact tpDep_snd_eq_nil_iff E φ
  | E, .and φ ψ => by
    simp [tpDep, Formula.scopesVaryB, tpDep_snd_eq_nil_iff E φ, tpDep_snd_eq_nil_iff E ψ]
  | E, .formerly _ φ | E, .previous _ φ => by
    simp [tpDep, Formula.scopesVaryB, tpDep_snd_eq_nil_iff E φ, tpDep_fst, and_comm]
  | E, .since φ _ ψ => by
    simp only [tpDep, Formula.scopesVaryB, List.append_eq_nil_iff, tpDep_snd_eq_nil_iff E φ,
      tpDep_snd_eq_nil_iff E ψ, tpDep_fst, Bool.and_eq_true]
    by_cases h₁ : φ.variesB E = true <;> by_cases h₂ : ψ.variesB E = true <;> simp [h₁, h₂]
  | E, .exist x φ => by
    simp [tpDep, Formula.scopesVaryB, tpDep_snd_eq_nil_iff (x.name :: E) φ, tpDep_fst, and_comm]

/-- The crate's check finds no degenerate aggregation body in an operand exactly when every
aggregation body of it varies, and so do the scopes inside it. -/
theorem tpDepT_eq_nil_iff : (E : List VarName) → (t : Term) →
    (tpDepT E t = [] ↔ t.scopesVaryB E = true)
  | E, .agg (.count _ body) => by
    simp [tpDepT, tpDepA, Term.scopesVaryB, tpDep_snd_eq_nil_iff E body, tpDep_fst, and_comm]
  | E, .agg (.sum s _ body) => by
    simp [tpDepT, tpDepA, Term.scopesVaryB, tpDep_snd_eq_nil_iff (s :: E) body, tpDep_fst,
      and_comm]
  | E, .arith _ l r => by
    simp [tpDepT, Term.scopesVaryB, tpDepT_eq_nil_iff E l, tpDepT_eq_nil_iff E r]
  | E, .entity _ | E, .long _ | E, .decimal _ | E, .string _ | E, .bool _ | E, .context _
  | E, .scope _ _ | E, .var _ | E, .wildcard => by simp [tpDepT, Term.scopesVaryB]

end

/-- **The crate's time-dependence check decides time dependence**: it finds nothing in a leaf
exactly when every monitoring scope of the leaf varies with the timepoint. -/
theorem checkTpDependence_eq_nil_iff (φ : Formula) :
    checkTpDependence φ = [] ↔ φ.MonitorsTime := by
  rw [← Dogwood.Thm.monitorsTimeB_iff]
  simp only [checkTpDependence, List.flatMap_eq_nil_iff, List.append_eq_nil_iff,
    Formula.monitorsTimeB, List.all_eq_true, Bool.and_eq_true, tpDep_snd_eq_nil_iff, tpDep_fst]
  constructor
  · intro h c hc
    have := h c hc
    by_cases hv : c.variesB φ.ruleWideBinders = true
    · exact ⟨hv, this.1⟩
    · simp [hv] at this
  · intro h c hc
    have := h c hc
    simp [this.1, this.2]

end Dogwood.Thm.Frontend
