import Dogwood.Spec.Temporal.Scopes

/-!
# Deciding that every monitoring scope varies with the timepoint

`monitorsTimeB` decides `Formula.MonitorsTime` (`Dogwood.Thm.monitorsTimeB_iff`). It is not part
of the specification: the conformance harness runs it.
-/

namespace Dogwood.Spec.Temporal

/-- `Term.Varies`, decided. -/
def Term.variesB (E : List VarName) : Term → Bool
  | .var x => E.contains x
  | .agg _ => true
  | .arith _ l r => l.variesB E || r.variesB E
  | _ => false

/-- `Formula.Varies`, decided. -/
def Formula.variesB (E : List VarName) : Formula → Bool
  | .pred _ _ _ | .tp _ => true
  | .cmp _ l r => l.variesB E || r.variesB E
  | .not φ => φ.variesB E
  | .and φ ψ => φ.variesB E || ψ.variesB E
  | .formerly _ _ | .previous _ _ | .since _ _ _ | .exist _ _ => true

mutual

/-- `Formula.ScopesVary`, decided. -/
def Formula.scopesVaryB (E : List VarName) : Formula → Bool
  | .pred _ _ _ | .tp _ => true
  | .cmp _ l r => l.scopesVaryB E && r.scopesVaryB E
  | .not φ => φ.scopesVaryB E
  | .and φ ψ => φ.scopesVaryB E && ψ.scopesVaryB E
  | .formerly _ φ | .previous _ φ => φ.variesB E && φ.scopesVaryB E
  | .since φ _ ψ => φ.variesB E && φ.scopesVaryB E && ψ.variesB E && ψ.scopesVaryB E
  | .exist x φ => φ.variesB (x.name :: E) && φ.scopesVaryB (x.name :: E)

/-- `Term.ScopesVary`, decided. -/
def Term.scopesVaryB (E : List VarName) : Term → Bool
  | .agg (.count _ body) => body.variesB E && body.scopesVaryB E
  | .agg (.sum s _ body) => body.variesB (s :: E) && body.scopesVaryB (s :: E)
  | .arith _ l r => l.scopesVaryB E && r.scopesVaryB E
  | _ => true

end

/-- `Formula.MonitorsTime`, decided. -/
def Formula.monitorsTimeB (φ : Formula) : Bool :=
  φ.conjuncts.all fun c => c.variesB φ.ruleWideBinders && c.scopesVaryB φ.ruleWideBinders

end Dogwood.Spec.Temporal
