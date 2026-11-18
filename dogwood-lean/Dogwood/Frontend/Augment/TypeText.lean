import Dogwood.Frontend.Augment.Util

/-!
# Cedar schema text of one common type

The provider pass of augmentation recovers the types of the hoisted provider fields by writing
`type __PR = { f1: T1, … };` and parsing it with Cedar's schema parser
(`Fragment::from_cedarschema_str`). This module parses that text: a lexer for the tokens of
Cedar's schema grammar (`cedar_schema/grammar.lalrpop`) and a parser of its type syntax

```
Type      := Path | 'Set' '<' Type '>' | '{' [AttrDecls] '}'
AttrDecls := Annotation* Name ['?'] ':' Type [',' | ',' AttrDecls]
Name      := IDENT | STR
Path      := IDENT {'::' IDENT}
```

with Cedar's conversion to the JSON form: a path is an entity-or-common reference, a record
has no additional attributes, an attribute is required unless marked `?`, and of two attributes
with one name the later is kept. The whole text must be the one common-type declaration the
crate writes; error messages are this module's own, not Cedar's.
-/

namespace Dogwood.Frontend.Augment.TypeText

open CedarSchema

/-- A token of Cedar's schema syntax. Keywords are identifiers. -/
inductive Tok where
  | ident (s : String)
  | str (s : String)
  | num (s : String)
  | punct (s : String)
deriving Repr, BEq, Inhabited

/-- The punctuation tokens, `::` before `:`. -/
def puncts : List String := ["::", ",", ";", ":", "{", "}", "[", "]", "<", ">", "=", "?", "@", "(", ")"]

/-- The characters of a string literal's body after its opening quote, the text after the
closing quote, or `none` when it is not closed (`"(\\.|[^"\\])*"`). -/
def strBody : List Char → Option (List Char × List Char)
  | [] => none
  | '"' :: rest => some ([], rest)
  | '\\' :: c :: rest => (strBody rest).map fun (b, r) => ('\\' :: c :: b, r)
  | '\\' :: [] => none
  | c :: rest => (strBody rest).map fun (b, r) => (c :: b, r)

/-- A string literal's body without its escapes (`\n`, `\r`, `\t`, `\0`, `\\`, `\'`, `\"`;
any other escaped character stands for itself). -/
def unescape : List Char → List Char
  | '\\' :: 'n' :: rest => '\n' :: unescape rest
  | '\\' :: 'r' :: rest => '\r' :: unescape rest
  | '\\' :: 't' :: rest => '\t' :: unescape rest
  | '\\' :: '0' :: rest => '\x00' :: unescape rest
  | '\\' :: c :: rest => c :: unescape rest
  | c :: rest => c :: unescape rest
  | [] => []

/-- The text after a `//` comment: everything up to the end of the line, and the line breaks. -/
def skipComment (cs : List Char) : List Char :=
  (cs.dropWhile fun d => d != '\n' && d != '\r').dropWhile fun d => d == '\n' || d == '\r'

theorem strBody_length (cs : List Char) :
    ∀ {body after : List Char}, strBody cs = some (body, after) → after.length < cs.length + 1 := by
  fun_induction strBody cs with
  | case1 => intro _ _ h; simp at h
  | case2 rest => intro _ _ h; simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨_, rfl⟩ := h; simp; omega
  | case3 c rest ih =>
    intro body after h
    cases hb : strBody rest with
    | none => simp [hb] at h
    | some r =>
      obtain ⟨b', a'⟩ := r
      simp only [hb, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨_, rfl⟩ := h
      have := ih hb; simp; omega
  | case4 => intro _ _ h; simp at h
  | case5 c rest =>
    rename_i ih
    intro body after h
    cases hb : strBody rest with
    | none => simp [hb] at h
    | some r =>
      obtain ⟨b', a'⟩ := r
      simp only [hb, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨_, rfl⟩ := h
      have := ih hb; simp; omega

theorem length_dropWhile_le (p : Char → Bool) : ∀ (l : List Char), (l.dropWhile p).length ≤ l.length
  | [] => by simp
  | c :: l => by
    simp only [List.dropWhile_cons]
    split
    · have := length_dropWhile_le p l; simp; omega
    · simp

theorem puncts_length : ∀ p ∈ puncts, 1 ≤ p.length := by decide

/-- The tokens of `cs`, whitespace and `//` comments skipped. -/
def lex (cs : List Char) : Except String (List Tok) :=
  match cs with
  | [] => .ok []
  | c :: rest =>
    if c.isWhitespace then lex rest
    else if c == '/' && rest.head? == some '/' then lex (skipComment rest)
    else if isIdentHead c then
      do return .ident (String.ofList (c :: rest.takeWhile isIdentTail)) :: (← lex (rest.dropWhile isIdentTail))
    else if c.isDigit then
      do return .num (String.ofList (c :: rest.takeWhile Char.isDigit)) :: (← lex (rest.dropWhile Char.isDigit))
    else if c == '"' then
      match h : strBody rest with
      | some (body, after) =>
        have := strBody_length rest h
        do return .str (String.ofList (unescape body)) :: (← lex after)
      | none => .error "unterminated string literal"
    else
      match h : puncts.find? fun p => (c :: rest).take p.length == p.toList with
      | some p =>
        have := puncts_length p (List.mem_of_find?_eq_some h)
        do return .punct p :: (← lex ((c :: rest).drop p.length))
      | none => .error s!"invalid token `{c}`"
termination_by cs.length
decreasing_by
  all_goals simp_wf
  all_goals first
    | omega
    | (have := length_dropWhile_le (fun d => d == '\n' || d == '\r')
          (rest.dropWhile fun d => d != '\n' && d != '\r')
       have := length_dropWhile_le (fun d => d != '\n' && d != '\r') rest
       simp only [skipComment]; omega)
    | (have := length_dropWhile_le isIdentTail rest; omega)
    | (have := length_dropWhile_le Char.isDigit rest; omega)

/-- The reserved word `w` used as an identifier. -/
def reserved (w : String) : String := s!"this identifier is reserved and cannot be used: {w}"

/-- A path `IDENT {'::' IDENT}`, its segments joined by `::`, and the tokens after it. -/
def parsePath : List Tok → Except String (String × List Tok)
  | .ident i :: .punct "::" :: rest => do
    if !isIdent i then throw (reserved i)
    let (p, after) ← parsePath rest
    return (i ++ "::" ++ p, after)
  | .ident i :: rest => if isIdent i then .ok (i, rest) else .error (reserved i)
  | _ => .error "expected an identifier"

/-- The annotations `@k("v")` before an attribute. -/
def parseAnnotations : List Tok → Except String (Annotations × List Tok)
  | .punct "@" :: .ident k :: .punct "(" :: .str v :: .punct ")" :: rest => do
    let (more, after) ← parseAnnotations rest
    if more.any (·.1 == k) then throw s!"duplicate annotation: @{k}"
    return ((k, some v) :: more, after)
  | .punct "@" :: .ident k :: rest => do
    let (more, after) ← parseAnnotations rest
    if more.any (·.1 == k) then throw s!"duplicate annotation: @{k}"
    return ((k, none) :: more, after)
  | .punct "@" :: _ => .error "expected an annotation key"
  | ts => .ok ([], ts)

mutual

/-- A type, and the tokens after it. `fuel` bounds the nesting. -/
def parseType : Nat → List Tok → Except String (SchemaType × List Tok)
  | 0, _ => .error "the type is nested too deeply"
  | _ + 1, .punct "{" :: .punct "}" :: rest => .ok (.record [] false, rest)
  | fuel + 1, .punct "{" :: rest => do
    let (attrs, after) ← parseAttrDecls fuel [] rest
    match after with
    | .punct "}" :: after' => return (.record attrs false, after')
    | _ => throw "expected `}`"
  | fuel + 1, .ident "Set" :: .punct "<" :: rest => do
    let (t, after) ← parseType fuel rest
    match after with
    | .punct ">" :: after' => return (.set t, after')
    | _ => throw "expected `>`"
  | _ + 1, ts => do
    let (p, after) ← parsePath ts
    return (.entityOrCommon p, after)

/-- Attribute declarations, added to `acc` (in key order, a later one replacing an earlier one
of the same name), up to the closing `}`, which is left unread. -/
def parseAttrDecls : Nat → List (String × AttrType) → List Tok →
    Except String (List (String × AttrType) × List Tok)
  | 0, _, _ => .error "the type is nested too deeply"
  | fuel + 1, acc, ts => do
    let (anns, ts) ← parseAnnotations ts
    let (name, ts) ← match ts with
      | .ident i :: rest => if isIdent i then pure (i, rest) else throw (reserved i)
      | .str s :: rest => pure (s, rest)
      | _ => throw "expected an attribute name"
    let (required, ts) := match ts with
      | .punct "?" :: rest => (false, rest)
      | rest => (true, rest)
    let ts ← match ts with
      | .punct ":" :: rest => pure rest
      | _ => throw "expected `:`"
    let (ty, ts) ← parseType fuel ts
    let acc := insertKey name { ty, required, annotations := anns } acc
    match ts with
    | .punct "," :: .punct "}" :: rest => return (acc, .punct "}" :: rest)
    | .punct "," :: rest => parseAttrDecls fuel acc rest
    | rest => return (acc, rest)

end

/-- The type of the one common type `type <id> = T;` that the text `src` declares. -/
def parseCommonTypeDecl (src : String) : Except String SchemaType := do
  let toks ← lex src.toList
  match toks with
  | .ident "type" :: .ident id :: .punct "=" :: rest => do
    if !isIdent id then throw (reserved id)
    let (t, after) ← parseType (toks.length + 1) rest
    match after with
    | [.punct ";"] => return t
    | _ => throw "expected `;` and the end of the text"
  | _ => throw "expected a common type declaration"

end Dogwood.Frontend.Augment.TypeText
