/-!
# SHA-256

The SHA-256 hash function (FIPS 180-4, section 6.2), as a total function from bytes to the
eight words of the digest, and its lowercase hexadecimal text: what the crate's rule revisions
and leaf content hashes are (`identity.rs`, `sha256_hex`).
-/

namespace Dogwood.Frontend.Sha256

/-- The round constants: the first 32 bits of the fractional parts of the cube roots of the first
64 primes. -/
def roundConstants : Array UInt32 := #[
  0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
  0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
  0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
  0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
  0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
  0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
  0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
  0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2]

/-- The initial hash value: the first 32 bits of the fractional parts of the square roots of the
first eight primes. -/
def initialHash : Array UInt32 :=
  #[0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a, 0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19]

/-- Rotate right by `n` bits, `0 < n < 32`. -/
def rotr (x n : UInt32) : UInt32 := (x >>> n) ||| (x <<< (32 - n))

/-- The message padded to a multiple of 64 bytes: a `1` bit, zeros, and the message's length in
bits as a big-endian 64-bit number. -/
def pad (msg : ByteArray) : ByteArray :=
  let len := msg.size
  let bits : UInt64 := (len * 8).toUInt64
  let zeros := (55 + 64 - len % 64) % 64
  let lenBytes := (List.range 8).reverse.map fun i => (bits >>> (8 * i).toUInt64).toUInt8
  (msg.push 0x80) ++ ⟨Array.replicate zeros 0⟩ ++ ⟨lenBytes.toArray⟩

/-- The big-endian word at byte `i`. -/
def word (b : ByteArray) (i : Nat) : UInt32 :=
  let byte := fun k => (b.data.getD (i + k) 0).toUInt32
  (byte 0 <<< 24) ||| (byte 1 <<< 16) ||| (byte 2 <<< 8) ||| byte 3

/-- The message schedule of the block at byte `off`. -/
def schedule (b : ByteArray) (off : Nat) : Array UInt32 :=
  let first := (List.range 16).foldl (fun w t => w.push (word b (off + 4 * t))) #[]
  (List.range 48).foldl (init := first) fun w t =>
    let i := t + 16
    let x := w.getD (i - 15) 0
    let y := w.getD (i - 2) 0
    let s0 := rotr x 7 ^^^ rotr x 18 ^^^ (x >>> 3)
    let s1 := rotr y 17 ^^^ rotr y 19 ^^^ (y >>> 10)
    w.push (w.getD (i - 16) 0 + s0 + w.getD (i - 7) 0 + s1)

/-- The working variables `a … h`. -/
structure State where
  a : UInt32
  b : UInt32
  c : UInt32
  d : UInt32
  e : UInt32
  f : UInt32
  g : UInt32
  h : UInt32

/-- One round of the compression function. -/
def round (w : Array UInt32) (s : State) (t : Nat) : State :=
  let S1 := rotr s.e 6 ^^^ rotr s.e 11 ^^^ rotr s.e 25
  let ch := (s.e &&& s.f) ^^^ ((~~~s.e) &&& s.g)
  let t1 := s.h + S1 + ch + roundConstants.getD t 0 + w.getD t 0
  let S0 := rotr s.a 2 ^^^ rotr s.a 13 ^^^ rotr s.a 22
  let maj := (s.a &&& s.b) ^^^ (s.a &&& s.c) ^^^ (s.b &&& s.c)
  let t2 := S0 + maj
  ⟨t1 + t2, s.a, s.b, s.c, s.d + t1, s.e, s.f, s.g⟩

/-- The hash value after the block whose schedule is `w`. -/
def compress (hv : Array UInt32) (w : Array UInt32) : Array UInt32 :=
  let get := fun i => hv.getD i 0
  let s := (List.range 64).foldl (round w) ⟨get 0, get 1, get 2, get 3, get 4, get 5, get 6, get 7⟩
  #[get 0 + s.a, get 1 + s.b, get 2 + s.c, get 3 + s.d, get 4 + s.e, get 5 + s.f, get 6 + s.g,
    get 7 + s.h]

/-- The digest of a message, as eight words. -/
def digest (msg : ByteArray) : Array UInt32 :=
  let p := pad msg
  (List.range (p.size / 64)).foldl (fun hv i => compress hv (schedule p (64 * i))) initialHash

/-- A word as eight lowercase hexadecimal digits. -/
def hexWord (x : UInt32) : String :=
  let digits := Nat.toDigits 16 x.toNat
  String.ofList (List.replicate (8 - digits.length) '0' ++ digits)

/-- The lowercase hexadecimal SHA-256 of the UTF-8 bytes of `s` (crate `sha256_hex`). -/
def hex (s : String) : String := String.join ((digest s.toUTF8).toList.map hexWord)

end Dogwood.Frontend.Sha256
