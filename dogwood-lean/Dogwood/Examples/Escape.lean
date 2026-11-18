import Dogwood.Frontend.Escape

/-!
# Examples: Rust's escaping, with the Unicode tables

Each line is what the Rust release the tables come from prints (`str::escape_debug`,
`char::escape_debug`, `{:?}`), checked by evaluation.
-/

namespace Dogwood.Examples.Escape

open Dogwood.Frontend.Escape

-- A grapheme extender (U+0301, combining acute accent) is escaped first in a string, not after.
#guard strEscapeDebug "á" = "á"
#guard strEscapeDebug "́a" = "\\u{301}a"
#guard charEscapeDebug '́' = "\\u{301}"
#guard strDebug "á" = "\"a\\u{301}\""
-- An unassigned code point of plane 11 is not printable.
#guard strEscapeDebug (String.singleton (Char.ofNat 0xb2cb2) ++ "Deb") = "\\u{b2cb2}Deb"
-- Letters and pictographs beyond ASCII are printable.
#guard strEscapeDebug "é😀" = "é😀"
-- Format characters (soft hyphen, zero-width space, BOM, a tag) are not; nor C1 controls.
#guard strEscapeDebug "­" = "\\u{ad}"
#guard strEscapeDebug "it's ​\"" = "it\\'s \\u{200b}\\\""
#guard strDebug "it's ​\"" = "\"it's \\u{200b}\\\"\""
#guard strEscapeDebug "﻿x" = "\\u{feff}x"
#guard strEscapeDebug (String.singleton (Char.ofNat 0xe0001)) = "\\u{e0001}"
#guard strEscapeDebug "\u007f\u0085 " = "\\u{7f}\\u{85}\\u{a0}"
#guard charEscapeDebug '‍' = "\\u{200d}"
#guard charEscapeDebug '\'' = "\\'"

end Dogwood.Examples.Escape
