import Dogwood.Examples.Common

/-!
# Pins reach aggregates inside compound operands

If pin injection skipped an aggregate that is a leaf of a compound operand (`(count …) + 0`),
under a pin the aggregate would count every key's events. The specification's
`Temporal.Term.injectPins` descends into `Term.arith` and into the aggregate's body (as the
crate's `inject_into_operand`, `event_schema/pin.rs`, does), so the
pinned predicate inside `(count … Refund::response{} …) + 0` carries the default schema's
`callerPrincipal = principal` pin, exactly as a bare `count` does. `Dogwood.Thm.pin_enforced`
states what the injected pin enforces, and `Dogwood.Examples.RefundBudget.outcome_isolated` shows
a decision that depends on it.
-/

namespace Dogwood.Examples.CompoundPins

open Dogwood.Spec Dogwood.Spec.Temporal Dogwood.Examples

def refund := action "Refund"
def actions : List ActionDecl := [(refund, [("amount", .int)])]
def schema : EventSchema := defaultSchema true actions

/-- `count for (t: Timepoint). where formerly within 1h (Refund::response{} && tp(t))` -/
def settled (args : List (Path × Term)) : Aggregate :=
  .count [⟨"t", .timepoint⟩] (.formerly ⟨1, .hours⟩ (.and (.pred refund "response" args) (.tp "t")))

/-- `(count …) + 0 >= 1`: the aggregate is a leaf of a compound operand. -/
def compound (args : List (Path × Term)) : Formula :=
  .cmp .ge (.arith .add (.agg (settled args)) (.long 0)) (.long 1)

/-- The pin `callerPrincipal = principal`, as pin injection appends it to a predicate. -/
def callerArg : Path × Term := (["callerPrincipal"], .scope .principal [])

/-- **The pin reaches the predicate inside the compound operand.** -/
example : (compound []).injectPins schema = compound [callerArg] := rfl

/-- The same as for the bare aggregate. -/
example : (Formula.cmp .ge (.agg (settled [])) (.long 1)).injectPins schema =
    .cmp .ge (.agg (settled [callerArg])) (.long 1) := rfl

/-- In general: injection maps a compound operand to the compound of the injected operands. -/
theorem injectPins_arith (S : EventSchema) (op : ArithOp) (l r : Term) :
    (Term.arith op l r).injectPins S = .arith op (l.injectPins S) (r.injectPins S) := rfl

end Dogwood.Examples.CompoundPins
