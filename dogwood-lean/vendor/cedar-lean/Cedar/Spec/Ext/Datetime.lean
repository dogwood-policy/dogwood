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
import Std.Time
import Std.Time.Format

/-! This file defines Cedar datetime values and functions. -/

namespace Cedar.Spec.Ext

open Cedar.Data

/--
  A datetime value is measured in milliseconds and constructed from a datetime string.
  A datetime string must be of one of the forms:
    - `YYYY-MM-DD` (date only)
    - `YYYY-MM-DDThh:mm:ssZ` (UTC)
    - `YYYY-MM-DDThh:mm:ss.SSSZ` (UTC with millisecond precision)
    - `YYYY-MM-DDThh:mm:ss(+|-)hhmm` (With timezone offset in hours and minutes)
    - `YYYY-MM-DDThh:mm:ss.SSS(+|-)hhmm` (With timezone offset in hours and minutes and millisecond precision)

  Regardless of the timezone, offset is always normalized to UTC.

  The datetime type does not provide a way to create a datetime from a Unix timestamp.
  One of the readable formats listed above must be used instead.
-/
public structure Datetime where
  val : Int64

public def Datetime.lt (d₁ d₂ : Datetime) : Bool :=
  d₁.val < d₂.val

public def Datetime.le (d₁ d₂ : Datetime) : Bool :=
  d₁.val ≤ d₂.val

public instance : LT Datetime where
  lt := fun d₁ d₂ => Datetime.lt d₁ d₂

public instance : LE Datetime where
  le := fun d₁ d₂ => Datetime.le d₁ d₂

public instance Datetime.decLt (d₁ d₂ : Datetime) : Decidable (d₁ < d₂) :=
  if h : Datetime.lt d₁ d₂ then isTrue h else isFalse h

public instance Datetime.decLe (d₁ d₂ : Datetime) : Decidable (d₁ ≤ d₂) :=
  if h : Datetime.le d₁ d₂ then isTrue h else isFalse h

public instance : Coe Int64 Datetime where
  coe i := Datetime.mk i

deriving instance Repr, Inhabited, DecidableEq for Datetime

namespace Datetime

def MAX_OFFSET_SECONDS: Nat := 86400

def DateOnly : Std.Time.GenericFormat .any := datespec("yyyy-MM-dd")
def DateUTC : Std.Time.GenericFormat .any := datespec("yyyy-MM-dd'T'HH:mm:ss'Z'")
def DateUTCWithMillis : Std.Time.GenericFormat .any := datespec("yyyy-MM-dd'T'HH:mm:ss.SSS'Z'")
def DateWithOffset : Std.Time.GenericFormat .any := datespec("yyyy-MM-dd'T'HH:mm:ssxx")
def DateWithOffsetAndMillis : Std.Time.GenericFormat .any := datespec("yyyy-MM-dd'T'HH:mm:ss.SSSxx")

public def datetime? (i: Int) : Option Datetime :=
  Int64.ofInt? i

def dateContainsLeapSeconds (str: String) : Bool :=
  str.length >= 20 && String.Pos.Raw.get? str ⟨17⟩ == some '6' && String.Pos.Raw.get? str ⟨18⟩ == some '0'

/--
  Check that the minutes for the timezone offset are in bounds (<60). We
  separately check that the whole offset is less than `MAX_OFFSET_SECONDS` which
  ensures that the hour component is in bounds. The timezone offset does not
  have a seconds component.
-/
def tzOffsetMinsLt60 (str : String) : Bool :=
  -- Short string is `DateOnly`, so no offset
  str.length <= 10 ||
  -- Ends in `Z` is either `DateUTC` or `DateUTCWithMillis`, so no offset
  str.endsWith "Z" ||
  -- `DateWithOffset` or `DateWithOffsetAndMillis` offset is last 4 chars.
  -- Minutes component is last two chars.
  match (str.takeEnd 2).toNat? with
  | .some minsOffset => minsOffset < 60
  | .none => false

/--
  Check that the timezone offset, when present, is exactly 4 digits: `(+|-)hhmm`.
  The date is split off on `T` first so the date's `-` separators are not
  mistaken for the offset sign. A date-only string, or a time without a sign
  (UTC `Z`), has no offset and passes.
-/
def checkOffsetLen (str : String) : Bool :=
  match str.splitToList (· == 'T') with
  | [_] => true
  | [_, timeMsOffset] =>
    match timeMsOffset.splitToList (λ c => c == '+' || c == '-') with
    | [_] => true
    | [_, offset] => offset.length == 4 && offset.all Char.isDigit
    | _ => false
  | _ => false

public def parse (str: String) : Option Datetime := do
  if dateContainsLeapSeconds str then failure
  if !checkOffsetLen str then failure
  if !tzOffsetMinsLt60 str then failure
  let val :=
    DateOnly.parse str <|>
    DateUTC.parse str <|>
    DateUTCWithMillis.parse str <|>
    DateWithOffset.parse str <|>
    DateWithOffsetAndMillis.parse str

  let zonedTime ← val.toOption
  if zonedTime.timezone.offset.second.val.natAbs < MAX_OFFSET_SECONDS
  then datetime? zonedTime.toTimestamp.toMillisecondsSinceUnixEpoch.toInt
  else none

public abbrev datetime := parse

/--
  A duration value is measured in milliseconds and constructed from a duration string.
  A duration string is a concatenated sequence of quantity-unit pairs where the quantity
  is a natural number and unit is one of the following:
    - `d` (for days)
    - `h` (for hours)
    - `m` (for minutes)
    - `s` (for seconds)
    - `ms` (for milliseconds)

  Duration strings are required to be ordered from largest unit to smallest
  unit, and contain one quantity per unit. Units with zero quantity may be
  omitted.

  A duration may be negative. Negative duration strings must begin with `-`.
-/
public structure Duration where
  val : Int64

deriving instance Repr, Inhabited, DecidableEq for Duration

public def Duration.lt (d₁ d₂ : Duration) : Bool :=
  d₁.val < d₂.val

public def Duration.le (d₁ d₂ : Duration) : Bool :=
  d₁.val ≤ d₂.val

public instance : LT Duration where
  lt := fun d₁ d₂ => Duration.lt d₁ d₂

public instance : LE Duration where
  le := fun d₁ d₂ => Duration.le d₁ d₂

public instance Duration.decLt (d₁ d₂ : Duration) : Decidable (d₁ < d₂) :=
  if h : Duration.lt d₁ d₂ then isTrue h else isFalse h

public instance Duration.decLe (d₁ d₂ : Duration) : Decidable (d₁ ≤ d₂) :=
  if h : Duration.le d₁ d₂ then isTrue h else isFalse h

public instance : Coe Int64 Duration where
  coe i := Duration.mk i

@[expose]
public def MILLISECONDS_PER_SECOND: Int := 1000
@[expose]
public def MILLISECONDS_PER_MINUTE: Int := 60000
@[expose]
public def MILLISECONDS_PER_HOUR: Int := 3600000
@[expose]
public def MILLISECONDS_PER_DAY: Int := 86400000

----- Definitions -----

/-- Create a `Duration` from an `Int` representing its internal encoding. Most callers should use higher-level constructors, e.g., `Duration.parse` -/
public def duration? (i: Int) : Option Duration :=
  Int64.ofInt? i

def Duration.neg? (d : Duration) : Option Duration :=
  d.val.neg?

def durationUnits? (n: Int) (suffix: String) : Option Int :=
  match Int64.ofInt? n with
  | none => none
  | some i =>
    match suffix with
    | "ms" => some i
    | "s" => some (i * MILLISECONDS_PER_SECOND)
    | "m" => some (i * MILLISECONDS_PER_MINUTE)
    | "h" => some (i * MILLISECONDS_PER_HOUR)
    | "d" => some (i * MILLISECONDS_PER_DAY)
    | _ => none

def unitsToMilliseconds (days hours minutes second milliseconds: Int) : Int :=
  days * MILLISECONDS_PER_DAY +
  hours * MILLISECONDS_PER_HOUR +
  minutes * MILLISECONDS_PER_MINUTE +
  second * MILLISECONDS_PER_SECOND +
  milliseconds

def isNegativeDuration (str: String) : Bool × String :=
  match str.front with
  | '-' => (true, str.drop 1|>.copy)
  | _   => (false, str)

def parseUnit? (isNegative : Bool) (str : String) (suffix : String) : Option (Int × String) :=
  if str.endsWith suffix
  then
    let newStr := str.dropEnd suffix.length
    let newStrList := newStr.copy.toList
    let digits := ((newStrList.reverse).takeWhile Char.isDigit).reverse
    if digits.isEmpty
    then none
    else do
      let nUnsignedUnits ← toNat?' (String.ofList digits)
      let units ← if isNegative
        then durationUnits? (Int.negOfNat nUnsignedUnits) suffix
        else durationUnits? (Int.ofNat nUnsignedUnits) suffix
      some (units, newStr.dropEnd digits.length|>.copy)
  else
    some (0, str)

def parseDuration? (isNegative : Bool) (str : String) : Option Duration := do
  if str.isEmpty then failure
  let (milliseconds, restStr) ← parseUnit? isNegative str "ms"
  let (seconds, restStr) ← parseUnit? isNegative restStr "s"
  let (minutes, restStr) ← parseUnit? isNegative restStr "m"
  let (hours, restStr) ← parseUnit? isNegative restStr "h"
  let (days, restStr) ← parseUnit? isNegative restStr "d"
  if restStr.isEmpty
  then duration? (days + hours + minutes + seconds + milliseconds)
  else none

public def Duration.parse (str : String) : Option Duration :=
  let (isNegative, restStr) := isNegativeDuration str
  parseDuration? isNegative restStr

deriving instance Repr for Duration

public abbrev duration := Duration.parse

public def offset (datetime: Datetime) (duration: Duration) : Option Datetime :=
  Int64.add? datetime.val duration.val

public def durationSince (datetime other: Datetime) : Option Duration :=
  Int64.sub? datetime.val other.val

public def toDate (datetime: Datetime) : Option Datetime :=
  let millisPerDayI64 := Int64.ofIntChecked MILLISECONDS_PER_DAY (by decide)
  if datetime.val >= 0
  then datetime? (millisPerDayI64 * (datetime.val.div millisPerDayI64))
  else if datetime.val.mod millisPerDayI64 == 0
       then datetime
       else datetime? (((datetime.val.div millisPerDayI64) - 1) * millisPerDayI64)

public def toTime (datetime: Datetime) : Duration :=
  let millisPerDayI64 := Int64.ofIntChecked MILLISECONDS_PER_DAY (by decide)
  if datetime.val >= 0
  then datetime.val.mod millisPerDayI64
  else let rem := datetime.val.mod millisPerDayI64
       if rem == 0
       then rem
       else (rem + millisPerDayI64)

public def Duration.toMilliseconds (duration: Duration) : Int64 :=
  duration.val

public def Duration.toSeconds (duration: Duration) : Int64 :=
  duration.toMilliseconds / 1000

public def Duration.toMinutes (duration: Duration) : Int64 :=
  duration.toSeconds / 60

public def Duration.toHours (duration: Duration) : Int64 :=
  duration.toMinutes / 60

public def Duration.toDays (duration: Duration) : Int64 :=
  duration.toHours / 24

end Datetime
