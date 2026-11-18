import Dogwood.Spec.Evaluator
import Dogwood.Spec.Policy

/-!
# The per-request authorizer

Cedar's authorizer (`Cedar.Spec.isAuthorized`), definition for definition,
over Dogwood rules and a leaf valuation: deny overrides allow, a rule that
errors is skipped and reported, and with no satisfied `permit` the decision
is an implicit deny.

`isAuthorizedEach` is the same authorizer over rules that each carry a leaf
valuation of their own. Rules deployed at different points of a trace observe
the history from different timepoints (`Dogwood.Spec.Log`), so two of them can
give the same temporal leaf different values.
-/

namespace Dogwood.Spec

open Cedar.Spec (Request Entities Effect PolicyID Response)
open Cedar.Data (Set)

section

variable (θ : Leaves)

def satisfied (policy : Policy) (req : Request) (entities : Entities) : Bool :=
  (evaluate θ policy.toExpr req entities) = .ok true

def satisfiedWithEffect (effect : Effect) (policy : Policy) (req : Request) (entities : Entities) : Option PolicyID :=
  if policy.effect == effect && satisfied θ policy req entities
  then some policy.id
  else none

def satisfiedPolicies (effect : Effect) (policies : Policies) (req : Request) (entities : Entities) : Set PolicyID :=
  Set.make (policies.filterMap (satisfiedWithEffect θ effect · req entities))

def hasError (policy : Policy) (req : Request) (entities : Entities) : Bool :=
  match (evaluate θ policy.toExpr req entities) with
  | .ok _ => false
  | .error _ => true

def errored (policy : Policy) (req : Request) (entities : Entities) : Option PolicyID :=
  if hasError θ policy req entities then some policy.id else none

def errorPolicies (policies : Policies) (req : Request) (entities : Entities) : Set PolicyID :=
  Set.make (policies.filterMap (errored θ · req entities))

def isAuthorized (req : Request) (entities : Entities) (policies : Policies) : Response :=
  let forbids := satisfiedPolicies θ .forbid policies req entities
  let permits := satisfiedPolicies θ .permit policies req entities
  let erroringPolicies := errorPolicies θ policies req entities
  if forbids.isEmpty && !permits.isEmpty
  then { decision := .allow, determiningPolicies := permits, erroringPolicies }
  else { decision := .deny,  determiningPolicies := forbids, erroringPolicies }

end

/-- The per-request authorizer over rules that each carry their own leaf
valuation: `isAuthorized`, definition for definition, with each rule evaluated
under its own valuation. With one valuation for every rule it is `isAuthorized`
(`Dogwood.Thm.isAuthorizedEach_const`). -/
def isAuthorizedEach (req : Request) (entities : Entities) (rules : List (Policy × Leaves)) :
    Response :=
  let forbids :=
    Set.make (rules.filterMap fun r => satisfiedWithEffect r.2 .forbid r.1 req entities)
  let permits :=
    Set.make (rules.filterMap fun r => satisfiedWithEffect r.2 .permit r.1 req entities)
  let erroringPolicies := Set.make (rules.filterMap fun r => errored r.2 r.1 req entities)
  if forbids.isEmpty && !permits.isEmpty
  then { decision := .allow, determiningPolicies := permits, erroringPolicies }
  else { decision := .deny,  determiningPolicies := forbids, erroringPolicies }

end Dogwood.Spec
