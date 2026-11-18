import Dogwood.Eval.Temporal
import Dogwood.Spec.Decision

/-!
# Executable decisions over a trace

`authorize ι P ω σ n` is `PolicySet.authorize` with every temporal leaf decided by the
evaluator, with the candidates bounded by the decision's timepoint. The checks the decision makes
before it decides are computable already (`PolicySet.decideWith`). `replay` gives the outcome
at every timepoint of a trace. `Dogwood.Thm.authorize_eq` and `Dogwood.Thm.replay_eq` prove
that they agree with the specification under a total reading (`ImplChoices.Total`), for a
policy set whose temporal leaves are all safe.
-/

namespace Dogwood.Eval

open Dogwood.Spec Dogwood.Spec.Temporal
open Cedar.Spec (Entities)

/-- `PolicySet.LeafHolds`, decided: the leaf, after pin injection, holds at timepoint `n` under
the schema's visibility. -/
def leafHolds (ι : ImplChoices) (P : PolicySet) (σ : Trace) (n : Nat) (φ : Formula) : Bool :=
  match σ[n]? with
  | some p => eval ι P.tickRate σ p.event (visibleB P.schema σ p.event) n Valuation.empty n
      (φ.injectPins P.schema)
  | none => false

/-- `PolicySet.leaves`, computed. -/
def leaves (ι : ImplChoices) (P : PolicySet) (ω : Provider.Providers) (σ : Trace) (n : Nat)
    (e : Event) : Leaves where
  temporal φ := leafHolds ι P σ n φ
  provider c := (ω (c.resolve e)).leafValue

/-- `PolicySet.authorize`, computed. -/
def authorize (ι : ImplChoices) (P : PolicySet) (ω : Provider.Providers) (σ : Trace) (n : Nat) :
    Outcome :=
  P.decideWith P.policies ω σ n fun e pr rs =>
    some (isAuthorized (leaves ι P ω σ n e) (e.request pr rs) (P.decisionEntities e) P.policies)

/-- Replaying a trace: the outcome at each of its timepoints, in order. -/
def replay (ι : ImplChoices) (P : PolicySet) (ω : Provider.Providers) (σ : Trace) :
    List Outcome :=
  (List.range σ.length).map (authorize ι P ω σ)

end Dogwood.Eval
