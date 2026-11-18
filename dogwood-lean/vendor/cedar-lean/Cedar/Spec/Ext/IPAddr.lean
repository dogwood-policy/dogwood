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

import Cedar.Spec.Ext.Util

/-! This file defines Cedar IpAddr values and functions. -/

namespace Cedar.Spec.Ext

namespace IPAddr

open BitVec

----- IPv4Addr and IPv6Addr -----

public abbrev ADDR_SIZE (w : Nat) := 2 ^ w

public abbrev V4_WIDTH := 5
public abbrev V6_WIDTH := 7
abbrev V4_SIZE := ADDR_SIZE V4_WIDTH
abbrev V6_SIZE := ADDR_SIZE V6_WIDTH

public abbrev IPNetAddr (w : Nat) := BitVec (ADDR_SIZE w)

/--
IPv4 address: a 32 bit number partitioned into 4 groups. a0 is most signifcant
and a3 is the least significant. In other words, the number represented is
a0++a1++a2++a3.
--/
public abbrev IPv4Addr := IPNetAddr V4_WIDTH

public def IPv4Addr.mk (a₀ a₁ a₂ a₃ : BitVec 8) : IPv4Addr :=
  a₀ ++ a₁ ++ a₂ ++ a₃

/--
IPv6 address: a 128 bit number partitioned into 8 groups. a0 is most signifcant
and a7 is the least significant. In other words, the number represented is
a0++a1++a2++a3++a4++a5++a6++a7.
--/
public abbrev IPv6Addr := IPNetAddr V6_WIDTH

public def IPv6Addr.mk (a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ : BitVec 16) : IPv6Addr :=
  a₀ ++ a₁ ++ a₂ ++ a₃ ++ a₄ ++ a₅ ++ a₆ ++ a₇

----- IPNetPrefix, CIDR, and IPNet -----

public abbrev IPNetPrefix (n : Nat) := Option (BitVec n)
public abbrev IPv4Prefix := IPNetPrefix V4_WIDTH
public abbrev IPv6Prefix := IPNetPrefix V6_WIDTH

def IPNetPrefix.ofNat (w : Nat) (pre : Nat) : IPNetPrefix w :=
  if pre < ADDR_SIZE w then .some pre else .none

public def IPNetPrefix.toNat {w} : IPNetPrefix w → Nat
  | .none         => ADDR_SIZE w
  | .some preSize => preSize.toNat

instance {w} : Coe Nat (IPNetPrefix w) where
  coe n := IPNetPrefix.ofNat w n

instance : CoeOut (IPNetPrefix w) Nat where
  coe p := p.toNat

instance instOfNat : OfNat (IPNetPrefix w) n
  where ofNat := IPNetPrefix.ofNat w n

public structure CIDR (w : Nat) where
  addr : IPNetAddr w
  pre  : IPNetPrefix w  -- We use "pre" because "prefix" is a keyword in Lean

public def CIDR.subnetWidth {w} (cidr : CIDR w) : BitVec (ADDR_SIZE w) :=
  let n := ADDR_SIZE w
  match cidr.pre with
  | .none            => 0#n
  | .some prefixSize => n - (prefixSize.zeroExtend n)

public def CIDR.range {w} (cidr : CIDR w) : (IPNetAddr w) × (IPNetAddr w) :=
  let n := ADDR_SIZE w
  let width := cidr.subnetWidth
  let lo := (cidr.addr >>> width) <<< width
  let hi := lo + (1#n <<< width) - 1#n
  (lo, hi)

public def CIDR.inRange {w} (cidr₁ cidr₂ : CIDR w) : Bool :=
  let r₁ := cidr₁.range
  let r₂ := cidr₂.range
  r₂.2 ≥ r₁.2 && r₁.1 ≥ r₂.1

public inductive IPNet where
  | V4 : CIDR V4_WIDTH → IPNet
  | V6 : CIDR V6_WIDTH → IPNet

@[inline, expose]
public def IPNet.isV4 : IPNet → Bool
  | .V4 _ => true
  | _     => false

@[inline, expose]
public def IPNet.isV6 : IPNet → Bool
  | .V6 _ => true
  | _     => false

public def IPNet.inRange : IPNet → IPNet → Bool
  | .V4 cidr₁, .V4 cidr₂
  | .V6 cidr₁, .V6 cidr₂ => cidr₁.inRange cidr₂
  | _, _                 => false

def LOOP_BACK_ADDRESS_V4 := IPv4Addr.mk 127 0 0 0
def LOOP_BACK_ADDRESS_V6 := IPv6Addr.mk 0 0 0 0 0 0 0 1
public def LOOP_BACK_CIDR_V4 := CIDR.mk LOOP_BACK_ADDRESS_V4 8
public def LOOP_BACK_CIDR_V6 := CIDR.mk LOOP_BACK_ADDRESS_V6 128

def MULTICAST_ADDRESS_V4 := IPv4Addr.mk 224 0 0 0
def MULTICAST_ADDRESS_V6 := IPv6Addr.mk 65280 0 0 0 0 0 0 0
public def MULTICAST_CIDR_V4 := CIDR.mk MULTICAST_ADDRESS_V4 4
public def MULTICAST_CIDR_V6 := CIDR.mk MULTICAST_ADDRESS_V6 8

public def IPNet.isLoopback : IPNet → Bool
  | .V4 cidr => cidr.inRange LOOP_BACK_CIDR_V4
  | .V6 cidr => cidr.inRange LOOP_BACK_CIDR_V6

public def IPNet.isMulticast : IPNet → Bool
  | .V4 cidr => cidr.inRange MULTICAST_CIDR_V4
  | .V6 cidr => cidr.inRange MULTICAST_CIDR_V6

private def parsePrefixNat (str : String) (digits : Nat) (size : Nat) : Option (Fin (size + 1)) :=
  let len := str.length
  if 0 < len && len ≤ digits && (str.startsWith "0" → str = "0")
  then do
    let n ← toNat?' str
    if n ≤ size then .some (Fin.ofNat (size+1) n) else .none
  else .none

private def parseNumV4 (str : String) : Option (BitVec 8) :=
  let len := str.length
  if 0 < len && len ≤ 3 && (str.startsWith "0" → str = "0")
  then do
    let n ← toNat?' str
    if n ≤ 0xff then .some n else .none
  else .none

private def parseSegsV4 (str : String) : Option IPv4Addr :=
  match str.splitToList (· = '.') with
  | [s₀, s₁, s₂, s₃] => do
    let a₀ ← parseNumV4 s₀
    let a₁ ← parseNumV4 s₁
    let a₂ ← parseNumV4 s₂
    let a₃ ← parseNumV4 s₃
    .some (IPv4Addr.mk a₀ a₁ a₂ a₃)
  | _ => .none

private def parseIPv4Net (str : String) : Option IPNet :=
  match str.splitToList (· = '/') with
  | strV4 :: rest => do
    let pre ←
      match rest with
      | []       => .some (ADDR_SIZE V4_WIDTH)
      | [strPre] => parsePrefixNat strPre 2 (ADDR_SIZE V4_WIDTH)
      | _        => .none
    let v4 ← parseSegsV4 strV4
    .some (IPNet.V4 ⟨v4, pre⟩)
  | _ => .none

private def isHexDigit (c : Char) : Bool :=
  c.isDigit || ('a' ≤ c && c ≤ 'f') || ('A' ≤ c && c ≤ 'F')

private def toHexNat (c : Char) : Nat :=
  if c.isDigit
  then c.toNat - '0'.toNat
  else if 'a' ≤ c && c ≤ 'f'
  then c.toNat - 'a'.toNat + 10
  else if 'A' ≤ c && c ≤ 'F'
  then c.toNat - 'A'.toNat + 10
  else c.toNat

private def parseNumV6 (str : String) : Option (BitVec 16) :=
  let len := str.length
  if 0 < len && len ≤ 4 && str.all isHexDigit
  then
    let n := str.foldl (fun n c => n * 16 + toHexNat c) 0
    if n ≤ 0xffff then .some n else .none
  else .none

private def parseNumSegsV6 (str : String) : Option (List (BitVec 16)) :=
  if str.isEmpty
  then .some []
  else (str.splitToList (· = ':')).mapM parseNumV6

private def parseSegsV6 (str : String) : Option IPv6Addr := do
  let segs ←
    match str.splitOn "::" with
    | [s₁] => parseNumSegsV6 s₁
    | [s₁, s₂] => do
      let ns₁ ← parseNumSegsV6 s₁
      let ns₂ ← parseNumSegsV6 s₂
      let len := ns₁.length + ns₂.length
      if len < 8
      then .some (ns₁ ++ (List.replicate (8 - len) 0) ++ ns₂)
      else .none
    | _ => .none
  match segs with
  | [a₀, a₁, a₂, a₃, a₄, a₅, a₆, a₇] =>
    .some (IPv6Addr.mk a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇)
  | _ => .none

private def parseIPv6Net (str : String) : Option IPNet :=
  match str.splitToList (· = '/') with
  | strV6 :: rest => do
    let pre ←
      match rest with
      | []       => .some (ADDR_SIZE V6_WIDTH)
      | [strPre] => parsePrefixNat strPre 3 (ADDR_SIZE V6_WIDTH)
      | _        => .none
    let v6 ← parseSegsV6 strV6
    .some (IPNet.V6 ⟨v6, pre⟩)
  | _ => .none

private def parse (str : String) : Option IPNet :=
  let ip := parseIPv4Net str
  if ip.isSome then ip else parseIPv6Net str

public def ip (str : String) : Option IPNet := parse str

----- IPNet deriviations -----

deriving instance Repr, DecidableEq, Inhabited for CIDR
deriving instance Repr, DecidableEq, Inhabited for IPNet

public def IPNetPrefix.lt {w} (p₁ p₂ : IPNetPrefix w) : Bool :=
  p₁.toNat < p₂.toNat

public instance {w} : LT (IPNetPrefix w) where
  lt := λ d₁ d₂ => IPNetPrefix.lt d₁ d₂

public instance IPNetPrefix.decLt {w} (d₁ d₂ : IPNetPrefix w) : Decidable (d₁ < d₂) :=
  if h : IPNetPrefix.lt d₁ d₂ then isTrue h else isFalse h

public def CIDR.lt {w} (cidr₁ cidr₂ : CIDR w) : Bool :=
  cidr₁.addr < cidr₂.addr || (cidr₁.addr = cidr₂.addr && cidr₁.pre < cidr₂.pre)

public instance {w} : LT (CIDR w) where
  lt := λ d₁ d₂ => CIDR.lt d₁ d₂

public instance CIDR.decLt {w} (d₁ d₂ : CIDR w) : Decidable (d₁ < d₂) :=
  if h : CIDR.lt d₁ d₂ then isTrue h else isFalse h

public def IPNet.lt : IPNet → IPNet → Bool
  | .V4 _, .V6 _         => true
  | .V6 _, .V4 _         => false
  | .V4 cidr₁, .V4 cidr₂
  | .V6 cidr₁, .V6 cidr₂ => cidr₁ < cidr₂

public instance : LT IPNet where
  lt := fun d₁ d₂ => IPNet.lt d₁ d₂

public instance IPNet.decLt (d₁ d₂ : IPNet) : Decidable (d₁ < d₂) :=
  if h : IPNet.lt d₁ d₂ then isTrue h else isFalse h

-- as of this writing, only handles nats up to 0xffff
private def toHex (n : Nat) : String :=
  let a0 := hexDigitRepr ((n % 0x10000) / 0x1000)
  let a1 := hexDigitRepr ((n % 0x1000) / 0x100)
  let a2 := hexDigitRepr ((n % 0x100) / 0x10)
  let a3 := hexDigitRepr ((n % 0x10) / 0x1)
  s!"{a0}{a1}{a2}{a3}"

instance : ToString IPNet where
  toString : IPNet → String
  | .V4 ⟨addr, pre⟩ =>
    let v  := addr.toNat
    let a0 := (v >>> 24) &&& 0xFF
    let a1 := (v >>> 16) &&& 0xFF
    let a2 := (v >>> 8) &&& 0xFF
    let a3 := v &&& 0xFF
    s!"{a0}.{a1}.{a2}.{a3}/{pre.toNat}"
  | .V6 ⟨addr, pre⟩ =>
    let v  := addr.toNat
    let a0 := toHex ((v >>> 112) &&& 0xFFFF)
    let a1 := toHex ((v >>> 96) &&& 0xFFFF)
    let a2 := toHex ((v >>> 80) &&& 0xFFFF)
    let a3 := toHex ((v >>> 64) &&& 0xFFFF)
    let a4 := toHex ((v >>> 48) &&& 0xFFFF)
    let a5 := toHex ((v >>> 32) &&& 0xFFFF)
    let a6 := toHex ((v >>> 16) &&& 0xFFFF)
    let a7 := toHex (v &&& 0xFFFF)
    s!"{a0}:{a1}:{a2}:{a3}:{a4}:{a5}:{a6}:{a7}/{pre.toNat}"

end IPAddr

end Cedar.Spec.Ext
