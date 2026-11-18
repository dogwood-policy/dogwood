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

public import Cedar.Spec.Ext.Decimal
public import Cedar.Spec.Ext.IPAddr
public import Cedar.Spec.Ext.Datetime

/-! This file defines Cedar extension values. -/

namespace Cedar.Spec

----- Definitions -----

public abbrev IPAddr := Ext.IPAddr.IPNet
public abbrev Duration := Ext.Datetime.Duration

public inductive Ext where
  | decimal (d : Ext.Decimal)
  | ipaddr (ip : IPAddr)
  | datetime (dt : Ext.Datetime)
  | duration (dur: Duration)

/-- Ordering on extension types: .decimal < .ipaddr < .datetime < .duration -/
public def Ext.lt : Ext → Ext → Bool
  | .decimal d₁, .decimal d₂ => d₁ < d₂
  | .ipaddr ip₁, .ipaddr ip₂ => ip₁ < ip₂
  | .datetime d₁, .datetime d₂ => d₁ < d₂
  | .duration d₁, .duration d₂ => d₁ < d₂
  | .decimal  _, _
  | .ipaddr   _, .datetime _
  | .ipaddr   _, .duration _
  | .datetime _, .duration _  => true
  | _ , _ => false

----- Derivations -----

deriving instance Repr, DecidableEq, Inhabited for Ext

public instance : LT Ext where
lt := fun x y => Ext.lt x y

public instance Ext.decLt (x y : Ext) : Decidable (x < y) :=
if  h : Ext.lt x y then isTrue h else isFalse h

public instance : Coe Ext.Decimal Ext where
  coe d := .decimal d

public instance : Coe IPAddr Ext where
  coe a := .ipaddr a

public instance : Coe Ext.Datetime Ext where
  coe dt := .datetime dt

public instance : Coe Duration Ext where
  coe dur := .duration dur

end Cedar.Spec
