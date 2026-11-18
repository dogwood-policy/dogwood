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

import Std.Data.HashMap

namespace Cedar.Spec

open Std (HashMap)

public inductive PatElem where
  | star
  | justChar (c : Char)
deriving Repr, DecidableEq, Inhabited

public instance : Coe Char PatElem where
  coe c := .justChar c

public def PatElem.lt : PatElem → PatElem → Bool
  | .justChar c₁, .justChar c₂ => c₁ < c₂
  | .star, .justChar _         => true
  | _, _                       => false

public instance : LT PatElem where
  lt := fun x y => PatElem.lt x y

public instance PatElem.decLt (x y : PatElem) : Decidable (x < y) :=
  if  h : PatElem.lt x y then isTrue h else isFalse h

public abbrev Pattern := List PatElem

def charMatch (textChar : Char) : PatElem → Bool
  | .justChar c => textChar == c
  | _           => false

def wildcard : PatElem → Bool
  | .star => true
  | _     => false

abbrev Cache := HashMap (Nat × Nat) Bool

abbrev CacheM (α) := StateM Cache α

def wildcardMatchIdx (text : List Char) (pattern : Pattern) (i j : Nat)
  (h₁ : i ≤ text.length)
  (h₂ : j ≤ pattern.length) : CacheM Bool
:= do
  if let .some b := (← get).get? (i, j) then
    return b
  let mut r := false
  if h₃ : j = pattern.length then
    r := i = text.length
  else if h₄ : i = text.length then
    r := wildcard (pattern.get ⟨j, (by omega)⟩) &&
         (← wildcardMatchIdx text pattern i (j + 1) h₁ (by omega))
  else if wildcard (pattern.get ⟨j, (by omega)⟩) then
    r := (← wildcardMatchIdx text pattern i (j + 1) h₁ (by omega)) ||
         (← wildcardMatchIdx text pattern (i + 1) j (by omega) h₂)
  else
    r := charMatch (text.get ⟨i, (by omega)⟩) (pattern.get ⟨j, (by omega)⟩) &&
         (← wildcardMatchIdx text pattern (i + 1) (j + 1) (by omega) (by omega))
  modifyGet λ cache => (r, cache.insert (i, j) r)
termination_by
  (text.length - i) + (pattern.length - j)
decreasing_by
  all_goals { simp_wf ; omega }

public def wildcardMatch (text : String) (pattern : Pattern) : Bool :=
  wildcardMatchIdx text.toList pattern 0 0 (by simp) (by simp) |>.run' {}

end Cedar.Spec
