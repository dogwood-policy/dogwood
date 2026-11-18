import Dogwood.Eval.Scopes

/-!
# The time-dependence check decides time dependence
-/

namespace Dogwood.Thm

open Dogwood.Spec Dogwood.Spec.Temporal

theorem Term.variesB_iff (E : List VarName) : (t : Term) → (t.variesB E = true ↔ t.Varies E)
  | .var x => by simp [Term.variesB, Term.Varies]
  | .agg _ => by simp [Term.variesB, Term.Varies]
  | .arith _ l r => by
    simp [Term.variesB, Term.Varies, Term.variesB_iff E l, Term.variesB_iff E r]
  | .entity _ | .long _ | .decimal _ | .string _ | .bool _ | .context _ | .scope _ _
  | .wildcard => by simp [Term.variesB, Term.Varies]

theorem Formula.variesB_iff (E : List VarName) : (φ : Formula) → (φ.variesB E = true ↔ φ.Varies E)
  | .pred _ _ _ | .tp _ | .formerly _ _ | .previous _ _ | .since _ _ _ | .exist _ _ => by
    simp [Formula.variesB, Formula.Varies]
  | .cmp _ l r => by simp [Formula.variesB, Formula.Varies, Term.variesB_iff]
  | .not φ => Formula.variesB_iff E φ
  | .and φ ψ => by
    simp [Formula.variesB, Formula.Varies, Formula.variesB_iff E φ, Formula.variesB_iff E ψ]

mutual

theorem Formula.scopesVaryB_iff : (E : List VarName) → (φ : Formula) →
    (φ.scopesVaryB E = true ↔ φ.ScopesVary E)
  | E, .pred _ _ _ | E, .tp _ => by simp [Formula.scopesVaryB, Formula.ScopesVary]
  | E, .cmp _ l r => by
    simp [Formula.scopesVaryB, Formula.ScopesVary, Term.scopesVaryB_iff E l,
      Term.scopesVaryB_iff E r]
  | E, .not φ => Formula.scopesVaryB_iff E φ
  | E, .and φ ψ => by
    simp [Formula.scopesVaryB, Formula.ScopesVary, Formula.scopesVaryB_iff E φ,
      Formula.scopesVaryB_iff E ψ]
  | E, .formerly _ φ | E, .previous _ φ => by
    simp [Formula.scopesVaryB, Formula.ScopesVary, Formula.variesB_iff,
      Formula.scopesVaryB_iff E φ]
  | E, .since φ _ ψ => by
    simp [Formula.scopesVaryB, Formula.ScopesVary, Formula.variesB_iff,
      Formula.scopesVaryB_iff E φ, Formula.scopesVaryB_iff E ψ, and_assoc]
  | E, .exist x φ => by
    simp [Formula.scopesVaryB, Formula.ScopesVary, Formula.variesB_iff,
      Formula.scopesVaryB_iff (x.name :: E) φ]

theorem Term.scopesVaryB_iff : (E : List VarName) → (t : Term) →
    (t.scopesVaryB E = true ↔ t.ScopesVary E)
  | E, .agg (.count _ body) => by
    simp [Term.scopesVaryB, Term.ScopesVary, Formula.variesB_iff,
      Formula.scopesVaryB_iff E body]
  | E, .agg (.sum s _ body) => by
    simp [Term.scopesVaryB, Term.ScopesVary, Formula.variesB_iff,
      Formula.scopesVaryB_iff (s :: E) body]
  | E, .arith _ l r => by
    simp [Term.scopesVaryB, Term.ScopesVary, Term.scopesVaryB_iff E l, Term.scopesVaryB_iff E r]
  | E, .entity _ | E, .long _ | E, .decimal _ | E, .string _ | E, .bool _ | E, .context _
  | E, .scope _ _ | E, .var _ | E, .wildcard => by simp [Term.scopesVaryB, Term.ScopesVary]

end

/-- **The time-dependence check decides time dependence.** -/
theorem monitorsTimeB_iff (φ : Formula) : φ.monitorsTimeB = true ↔ φ.MonitorsTime := by
  simp [Formula.monitorsTimeB, Formula.MonitorsTime, Formula.variesB_iff,
    Formula.scopesVaryB_iff]

end Dogwood.Thm
