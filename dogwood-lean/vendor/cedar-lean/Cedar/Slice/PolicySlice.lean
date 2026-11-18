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

import Cedar.Spec

/-!
This file defines a simple policy slicing algorithm that is based
on policy scopes. For proofs of correctness, see Cedar.Thm.PolicySlice.
-/

namespace Cedar.Slice

open Cedar.Spec

/--
A policy bound consists of optional `principal` and `resource` entities.
-/
structure PolicyBound where
  principalBound : Option EntityUID
  resourceBound  : Option EntityUID

def inSomeOrNone (uid : EntityUID) (opt : Option EntityUID) (entities : Entities) : Bool :=
  match opt with
  | .some uid' => inₑ uid uid' entities
  | .none      => true

/--
A bound is satisfied by a request and store if the request principal and
resource fields are descendents of the corresponding bound fields (or if those
bound fields are `none`).
-/
def satisfiedBound (bound : PolicyBound) (request : Request) (entities : Entities) : Bool :=
  inSomeOrNone request.principal bound.principalBound entities ∧
  inSomeOrNone request.resource bound.resourceBound entities


/--
A bound analysis takes as input a policy and returns a PolicyBound.
-/
abbrev BoundAnalysis := Policy → PolicyBound

/--
A bound-based slicing algorithm takes as input a bound analysis, request, entities,
and policies, and filters out the policies whose bound is not satisfied by the
request and entities.
-/
def BoundAnalysis.slice (ba : BoundAnalysis) (request : Request) (entities : Entities) (policies : Policies) : Policies :=
  policies.filter (fun policy => satisfiedBound (ba policy) request entities)


/--
Scope-based bound analysis extracts the bound from the policy scope.
-/
def scopeAnalysis (policy : Policy) : PolicyBound :=
  {
    principalBound := policy.principalScope.scope.bound,
    resourceBound  := policy.resourceScope.scope.bound,
  }

end Cedar.Slice
