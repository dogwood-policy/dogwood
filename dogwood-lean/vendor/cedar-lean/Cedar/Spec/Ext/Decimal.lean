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

public import Cedar.Data.Int64
import Cedar.Spec.Ext.Util

/-! This file defines Cedar decimal values and functions. -/

namespace Cedar.Spec.Ext

open Cedar.Data

/--
A decimal number consists of an integer part and a fractional part.
The former is the integer number before the decimal point.
The latter is the decimal number minus its integer part.
For instance, 10.234 is a decimal number. Its integer part is 10 and its fractional part is 0.234
We restrict the number of the digits after the decimal point to 4.
-/

def DECIMAL_DIGITS : Nat := 4

public abbrev Decimal := Int64

namespace Decimal

----- Definitions -----

/-- Create a `Decimal` from an `Int` representing its internal encoding. Most callers should use higher-level constructors, e.g., `Decimal.parse` -/
public def decimal? (i : Int) : Option Decimal :=
  Int64.ofInt? i

public def parse (str : String) : Option Decimal :=
  match str.splitToList (· = '.') with
  | ["-", _] => .none -- String.toInt? "-" == some 0
  | [left, right] =>
    let rlen := right.length
    if 0 < rlen ∧ rlen ≤ DECIMAL_DIGITS
    then
      match toInt?' left, toNat?' right with
      | .some l, .some r =>
        let l' := l * (Int.pow 10 DECIMAL_DIGITS)
        let r' := r * (Int.pow 10 (DECIMAL_DIGITS - rlen))
        let i  := if !left.startsWith "-" then l' + r' else l' - r'
        decimal? i
      | _, _ => .none
    else .none
  | _ => .none

instance : ToString Decimal where
  toString (d : Decimal) : String :=
    let neg   := if d < 0 then "-" else ""
    let d     := d.natAbs
    let left  := d / (Nat.pow 10 DECIMAL_DIGITS)
    let right := d % (Nat.pow 10 DECIMAL_DIGITS)
    let right :=
      -- this is not generalized for arbitrary DECIMAL_DIGITS
      if right < 10 then s!".000{right}"
      else if right < 100 then s!".00{right}"
      else if right < 1000 then s!".0{right}"
      else s!".{right}"
    s!"{neg}{left}{right}"

public abbrev decimal := parse

end Decimal

end Cedar.Spec.Ext
