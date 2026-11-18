/-
 Copyright Cedar Contributors

 Licensed under the Apache License, Version 2.0 (the "License");
 you may not use this file except in compliance with the License.
 You may obtain a copy of the License at

      https://www.apache.org/licenses/LICENSE-2.0

 Unless required by applicable law or agreed to in writing, software
 distributed under the License is distributed on an "AS IS" BASIS,
 WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 See the License for the specific language governing permissions and
 limitations under the License.
-/

import Cedar.TPE.Input
import Cedar.TPE.Residual
import Cedar.TPE.Evaluator
import Cedar.Spec.Response
import Cedar.Spec.Policy
import Cedar.Validation.Types
import Cedar.Data

namespace Cedar.Spec

def Residual.isTrue : Residual → Bool
  | .val (.prim (.bool true)) _ => true
  | _ => false

def Residual.isFalse : Residual → Bool
  | .val (.prim (.bool false)) _ => true
  | _ => false

end Cedar.Spec

namespace Cedar.TPE

open Cedar.Data
open Cedar.Spec
open Cedar.Validation

structure ResidualPolicy where
  id : PolicyID
  effect : Effect
  residual : Residual

def ResidualPolicy.satisfied (policy : ResidualPolicy) : Bool :=
  policy.residual.isTrue

def ResidualPolicy.hasError (policy : ResidualPolicy) : Bool :=
  policy.residual.isError

def ResidualPolicy.isFalse (policy : ResidualPolicy) : Bool :=
  policy.residual.isFalse

def ResidualPolicy.isResidual (policy : ResidualPolicy) : Bool :=
  !policy.satisfied && !policy.isFalse && !policy.hasError

def ResidualPolicy.erroredWithEffect (effect : Effect) (policy : ResidualPolicy) : Option PolicyID :=
  if policy.effect == effect && policy.hasError
  then some policy.id
  else none

def ResidualPolicy.falseWithEffect (effect : Effect) (policy : ResidualPolicy) : Option PolicyID :=
  if policy.effect == effect && policy.isFalse
  then some policy.id
  else none

def ResidualPolicy.residualWithEffect (effect : Effect) (policy : ResidualPolicy) : Option PolicyID :=
  if policy.effect == effect && policy.isResidual
  then some policy.id
  else none

def ResidualPolicy.satisfiedWithEffect (effect : Effect) (policy : ResidualPolicy) : Option PolicyID :=
  if policy.effect == effect && policy.satisfied
  then some policy.id
  else none

structure Response where
  decision : Option Decision

  satisfiedPermits : Set PolicyID
  falsePermits : Set PolicyID
  errorPermits : Set PolicyID
  residualPermits : Set PolicyID

  satisfiedForbids : Set PolicyID
  falseForbids : Set PolicyID
  errorForbids : Set PolicyID
  residualForbids : Set PolicyID

  residuals : List ResidualPolicy

/-- Compute an authorization decision (if possible) from a list of partially
    evaluated policies. Also used for batched evaluation.  -/
def isAuthorizedFromResiduals (residuals : List ResidualPolicy) : Response :=
  let satisfiedForbids := satisfiedPolicies .forbid residuals
  let falseForbids := falsePolicies .forbid residuals
  let errorForbids := errorPolicies .forbid residuals
  let residualForbids := residualPolicies .forbid residuals

  let satisfiedPermits := satisfiedPolicies .permit residuals
  let falsePermits := falsePolicies .permit residuals
  let errorPermits := errorPolicies .permit residuals
  let residualPermits := residualPolicies .permit residuals

  let decision :=
    match (!satisfiedForbids.isEmpty, !satisfiedPermits.isEmpty, !residualPermits.isEmpty, !residualForbids.isEmpty) with
    | (true,  _,     _,     _)    => some Decision.deny
    | (_,     false, false, _)    => some Decision.deny
    | (false, _,     _,    true)  => none
    | (false, false, true, false) => none
    | (false, true,  _,    false) => some .allow

  {
    decision,
    satisfiedPermits,
    falsePermits,
    errorPermits,
    residualPermits,
    satisfiedForbids,
    falseForbids,
    errorForbids,
    residualForbids
    residuals
  }
  where
    satisfiedPolicies (effect : Effect) (policies : List ResidualPolicy) : Set PolicyID :=
      Set.make (policies.filterMap (ResidualPolicy.satisfiedWithEffect effect))

    errorPolicies (effect : Effect) (policies : List ResidualPolicy) : Set PolicyID :=
      Set.make (policies.filterMap (ResidualPolicy.erroredWithEffect effect))

    residualPolicies (effect : Effect) (policies : List ResidualPolicy) : Set PolicyID :=
      Set.make (policies.filterMap (ResidualPolicy.residualWithEffect effect))

    falsePolicies (effect : Effect) (policies : List ResidualPolicy) : Set PolicyID :=
      Set.make (policies.filterMap (ResidualPolicy.falseWithEffect effect))

def isAuthorized (schema : Schema) (policies : List Policy) (req : PartialRequest) (es : PartialEntities) : Except Error Response :=
  do
    let residualPolicies ← evaluatePolicies schema policies req es
    pure (isAuthorizedFromResiduals residualPolicies)
  where
    evaluatePolicies (schema : Schema) (policies : List Policy) (req : PartialRequest) (es : PartialEntities) : Except Error (List ResidualPolicy) :=
      policies.mapM (λ p => do
        pure ⟨p.id, p.effect, ← evaluatePolicy schema p req es⟩)

/--
Take a partial authorization Response and fully evaluate it using a concrete
requests and entities. This implementation of this function is fully analogous
to the concrete `isAuthorized` function, only working with residuals instead of
policies.
-/
def Response.reauthorize (response : Response) (req : Request) (es : Entities) : Spec.Response :=
  let forbids := satisfiedPolicies .forbid response.residuals req es
  let permits := satisfiedPolicies .permit response.residuals req es
  let erroringPolicies := errorPolicies response.residuals req es
  if forbids.isEmpty && !permits.isEmpty
  then { decision := .allow, determiningPolicies := permits, erroringPolicies }
  else { decision := .deny,  determiningPolicies := forbids, erroringPolicies }
where
  satisfied (rp : ResidualPolicy) (req : Request) (entities : Entities) : Bool :=
    (rp.residual.evaluate req entities) = .ok true

  satisfiedWithEffect (effect : Effect) (rp : ResidualPolicy) (req : Request) (entities : Entities) : Option PolicyID :=
    if rp.effect == effect && satisfied rp req entities
    then some rp.id
    else none

  satisfiedPolicies (effect : Effect) (rsp : List ResidualPolicy) (req : Request) (entities : Entities) : Set PolicyID :=
    Set.make (rsp.filterMap (satisfiedWithEffect effect · req entities))

  hasError (rp : ResidualPolicy) (req : Request) (entities : Entities) : Bool :=
    match (rp.residual.evaluate req entities) with
    | .ok _ => false
    | .error _ => true

  errored (rp : ResidualPolicy) (req : Request) (entities : Entities) : Option PolicyID :=
    if hasError rp req entities then some rp.id else none

  errorPolicies (rps : List ResidualPolicy) (req : Request) (entities : Entities) : Set PolicyID :=
    Set.make (rps.filterMap (errored · req entities))

end Cedar.TPE
