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

module

public import Cedar.Spec.Policy
import Lean.Data.Json.FromToJson

/-!
This file defines Cedar responses.
-/

namespace Cedar.Spec

open Cedar.Data

----- Definitions -----

public inductive Decision where
  | allow
  | deny

public structure Response where
  decision : Decision
  determiningPolicies : Set PolicyID
  erroringPolicies : Set PolicyID

----- Derivations -----

deriving instance Repr, DecidableEq, Lean.ToJson for Decision
deriving instance Repr, DecidableEq, Lean.ToJson for Response

end Cedar.Spec
