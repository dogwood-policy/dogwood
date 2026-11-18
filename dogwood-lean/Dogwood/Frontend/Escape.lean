import Dogwood.Frontend.UnicodeTables

/-!
# Rust's escaping of characters and strings

The crate prints strings, entity ids, attribute names, pattern characters and provider
arguments with Rust's escapes, and some of those texts are identity values (a rule's revision
hashes its canonical text, the version hash the schema's text) or appear in diagnostics. This
module ports the escapes exactly, with the Unicode tables of the Rust release the crate builds
with (`UnicodeTables`, generated from the toolchain's `library/core/src/` by
`scripts/gen_unicode_tables.py`):

* `escapeDebugExt` is `char::escape_debug_ext`: `\0 \t \r \n \\` escaped, `"` and `'` when
  asked, then a grapheme extender (when asked) and a character that is not printable as
  `\u{…}` in lowercase hexadecimal, and any other character as itself;
* `charEscapeDebug` is `char::escape_debug` (every escape);
* `strEscapeDebug` is `str::escape_debug`: the first character with every escape, the others
  without the escape of a grapheme extender (Cedar's printing of strings and ids,
  `Eid::escaped`);
* `strDebug` is `{:?}` of a string (`impl Debug for str`): quoted, every character with the
  escape of a grapheme extender and of `"`, not of `'`.

(`str::escape_default` needs no table: it is `Ids.escapeDefault`.)
-/

namespace Dogwood.Frontend.Escape

/-- The lowercase hexadecimal digits of `n`, without leading zeros. -/
def hex (n : Nat) : String := String.ofList (Nat.toDigits 16 n)

/-- The number of the leading elements of `bs` at most `x`, for `bs` sorted (a binary search
between `lo` and `hi`). -/
def countAtMost (bs : Array Nat) (x : Nat) (lo hi : Nat) : Nat :=
  if h : lo < hi then
    let mid := (lo + hi) / 2
    if bs[mid]! ≤ x then countAtMost bs x (mid + 1) hi else countAtMost bs x lo mid
  else lo
termination_by hi - lo
decreasing_by all_goals omega

/-- Whether `x` is in a table of range boundaries `[b₀, b₁), [b₂, b₃), …`: an odd number of the
boundaries are at most `x`. -/
def inTable (bs : Array Nat) (x : Nat) : Bool := countAtMost bs x 0 bs.size % 2 == 1

/-- Whether Rust prints `c` as itself when it escapes it, whatever the position: its ASCII fast
path, then the table of the code points `char::escape_debug_ext` writes as `\u{…}` whatever its
arguments (`UnicodeTables.notPrintable`). -/
def isPrintable (c : Char) : Bool :=
  let n := c.toNat
  if n < 0x20 then false
  else if n < 0x7f then true
  else !inTable UnicodeTables.notPrintable n

/-- Whether `c` has Unicode's `Grapheme_Extend` property (`char::is_grapheme_extender`: false
up to `U+02FF`). -/
def isGraphemeExtended (c : Char) : Bool :=
  0x2ff < c.toNat && inTable UnicodeTables.graphemeExtend c.toNat

/-- `c` as `\u{…}`, in lowercase hexadecimal (`char::escape_unicode`). -/
def escapeUnicode (c : Char) : String := "\\u{" ++ hex c.toNat ++ "}"

/-- One character as Rust's `char::escape_debug_ext` writes it, escaping a grapheme extender
when `graphemes`, `'` when `single` and `"` when `double`. -/
def escapeDebugExt (graphemes single double : Bool) (c : Char) : String :=
  if c.toNat == 0 then "\\0"
  else if c == '\t' then "\\t"
  else if c == '\r' then "\\r"
  else if c == '\n' then "\\n"
  else if c == '\\' then "\\\\"
  else if double && c == '"' then "\\\""
  else if single && c == '\'' then "\\'"
  else if graphemes && isGraphemeExtended c then escapeUnicode c
  else if isPrintable c then String.singleton c
  else escapeUnicode c

/-- One character as `char::escape_debug` writes it: every escape. -/
def charEscapeDebug (c : Char) : String := escapeDebugExt true true true c

/-- A string as `str::escape_debug` writes it: the first character with every escape, the others
without the escape of a grapheme extender. -/
def strEscapeDebug (s : String) : String :=
  match s.toList with
  | [] => ""
  | c :: cs => charEscapeDebug c ++ String.join (cs.map (escapeDebugExt false true true))

/-- A string as `{:?}` writes it (`impl Debug for str`): quoted, each character with the escape
of a grapheme extender and of `"`, not of `'`. -/
def strDebug (s : String) : String :=
  "\"" ++ String.join (s.toList.map (escapeDebugExt true false true)) ++ "\""

end Dogwood.Frontend.Escape
