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

public import Cedar.Spec.Value

/-! This file defines Cedar extension functions. -/

namespace Cedar.Spec

open Cedar.Spec.Ext
open Option

----- Definitions -----

public inductive ExtFun where
  | decimal             ----- Decimal functions -----
  | lessThan
  | lessThanOrEqual
  | greaterThan
  | greaterThanOrEqual
  | ip                  ----- IpAddr functions -----
  | isIpv4
  | isIpv6
  | isLoopback
  | isMulticast
  | isInRange
  | datetime            ----- Datetime functions -----
  | duration
  | offset
  | durationSince
  | toDate
  | toTime
  | toMilliseconds
  | toSeconds
  | toMinutes
  | toHours
  | toDays

@[expose]
public def res {α} [Coe α Ext] : Option α → Result Value
  | some v => .ok v
  | none   => .error .extensionError

@[expose]
public def call : ExtFun → List Value → Result Value
  | .decimal, [.prim (.string s)]               => res (Decimal.decimal s)
  | .lessThan,
    [.ext (.decimal d₁), .ext (.decimal d₂)]    => .ok (d₁ < d₂ : Bool)
  | .lessThanOrEqual,
    [.ext (.decimal d₁), .ext (.decimal d₂)]    => .ok (d₁ ≤ d₂ : Bool)
  | .greaterThan,
    [.ext (.decimal d₁), .ext (.decimal d₂)]    => .ok (d₁ > d₂ : Bool)
  | .greaterThanOrEqual,
    [.ext (.decimal d₁), .ext (.decimal d₂)]    => .ok (d₁ ≥ d₂ : Bool)
  | .ip, [.prim (.string s)]                    => res (IPAddr.ip s)
  | .isIpv4, [.ext (.ipaddr a)]                 => .ok a.isV4
  | .isIpv6, [.ext (.ipaddr a)]                 => .ok a.isV6
  | .isLoopback, [.ext (.ipaddr a)]             => .ok a.isLoopback
  | .isMulticast, [.ext (.ipaddr a)]            => .ok a.isMulticast
  | .isInRange,
    [.ext (.ipaddr a₁), .ext (.ipaddr a₂)]      => .ok (a₁.inRange a₂)
  | .datetime, [.prim (.string s)]              => res (Datetime.parse s)
  | .duration, [.prim (.string s)]              => res (Datetime.Duration.parse s)
  | .offset,
    [.ext (.datetime dt), .ext (.duration dur)] => res (dt.offset dur)
  | .durationSince,
    [.ext (.datetime d₁), .ext (.datetime d₂)]  => res (d₁.durationSince d₂)
  | .toDate, [.ext (.datetime dt)]              => res (dt.toDate)
  | .toTime, [.ext (.datetime dt)]              => .ok dt.toTime
  | .toMilliseconds, [.ext (.duration dur)]     => .ok dur.toMilliseconds
  | .toSeconds, [.ext (.duration dur)]          => .ok dur.toSeconds
  | .toMinutes, [.ext (.duration dur)]          => .ok dur.toMinutes
  | .toHours, [.ext (.duration dur)]            => .ok dur.toHours
  | .toDays , [.ext (.duration dur)]            => .ok dur.toDays
  | _, _                                        => .error .typeError

----- Derivations -----

deriving instance Repr, DecidableEq, Inhabited for ExtFun

end Cedar.Spec
