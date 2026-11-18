import Dogwood.Thm.Frontend.Augment.Providers
import Dogwood.Thm.Frontend.Augment.Context

/-!
# The synthesized provider type parses back to the declared types

The provider pass types the hoisted provider fields by writing each field's Cedar type text
(`ParamType.toCedarTypeWith`) into `type __PR = { f: T, … };` and parsing it. This module proves
that the parse gives back the structure of the declared type (`schemaOf`): a string, a long, a
boolean or `decimal` becomes the reference of that name, a set its element, a record its fields
(required as declared), an enum the reference of its exported name
(`synthesizedAttrs_eq`), provided the record field names are Cedar identifiers and the entity
type names Cedar paths (`Printable`).

The names are then resolved by Cedar in the namespace of the shared provider type, where a name
the namespace declares itself is found first: a builtin name that some namespace declares
(`type decimal = …`) is therefore pinned to `__cedar::` before (`pinBuiltinNames`, and
`Augment/Defects.lean`). A record field name that is not a bare Cedar identifier is written as a
string (`attrNameText`); the theorems here are about bare names (`isBareAttrName`).
-/

namespace Dogwood.Frontend.Augment.TypeText

open ProviderDecls CedarSchema

/-! ## Characters -/

theorem char_le_iff {a b : Char} : a ≤ b ↔ a.val.toNat ≤ b.val.toNat := by
  rw [Char.le_def, UInt32.le_iff_toNat_le]

theorem identHead_not_ws {c : Char} (h : isIdentHead c = true) : c.isWhitespace = false := by
  simp only [isIdentHead, Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true, decide_eq_true_eq] at h
  simp only [Char.isWhitespace, Bool.or_eq_false_iff, decide_eq_false_iff_not]
  rcases h with (rfl | ⟨h1, h2⟩) | ⟨h1, h2⟩
  · decide
  all_goals
    refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩ <;> rintro rfl <;> revert h1 h2 <;> decide

theorem identHead_not_digit {c : Char} (h : isIdentHead c = true) : c.isDigit = false := by
  simp only [isIdentHead, Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true, decide_eq_true_eq] at h
  simp only [Char.isDigit, Bool.and_eq_false_iff, decide_eq_false_iff_not]
  rcases h with (rfl | ⟨h1, h2⟩) | ⟨h1, h2⟩
  · decide
  all_goals
    right; intro h3
    simp only [Char.le_def, UInt32.le_iff_toNat_le] at h1 h3
    revert h1 h3; simp; omega

theorem identHead_ne {c : Char} (h : isIdentHead c = true) (d : Char) (hd : isIdentHead d = false) :
    c ≠ d := by rintro rfl; simp_all

theorem identTail_of_head {c : Char} (h : isIdentHead c = true) : isIdentTail c = true := by
  simp [isIdentTail, h]

/-! ## Lists of characters -/

theorem takeWhile_append_of_all {p : Char → Bool} :
    ∀ {w : List Char} (rest : List Char), (∀ d ∈ w, p d = true) →
      (∀ d, rest.head? = some d → p d = false) → (w ++ rest).takeWhile p = w
  | [], [], _, _ => rfl
  | [], d :: rest, _, hr => by simp [hr d rfl]
  | c :: w, rest, hw, hr => by
    simp only [List.cons_append, List.takeWhile_cons, hw c (List.mem_cons_self ..), if_true]
    rw [takeWhile_append_of_all rest (fun d hd => hw d (List.mem_cons_of_mem _ hd)) hr]

theorem dropWhile_append_of_all {p : Char → Bool} :
    ∀ {w : List Char} (rest : List Char), (∀ d ∈ w, p d = true) →
      (∀ d, rest.head? = some d → p d = false) → (w ++ rest).dropWhile p = rest
  | [], [], _, _ => rfl
  | [], d :: rest, _, hr => by simp [hr d rfl]
  | c :: w, rest, hw, hr => by
    simp only [List.cons_append, List.dropWhile_cons, hw c (List.mem_cons_self ..), if_true]
    exact dropWhile_append_of_all rest (fun d hd => hw d (List.mem_cons_of_mem _ hd)) hr

/-! ## The lexer, on the pieces of a printed type -/

/-- The tokens of `cs`, prepended to the lexing of what follows. -/
def prepend (toks : List Tok) (r : Except String (List Tok)) : Except String (List Tok) :=
  r.map (toks ++ ·)

theorem prepend_prepend (a b : List Tok) (r : Except String (List Tok)) :
    prepend a (prepend b r) = prepend (a ++ b) r := by
  cases r <;> simp [prepend, Except.map]

theorem lex_space (rest : List Char) : lex (' ' :: rest) = lex rest := by
  rw [lex]; simp

/-- An identifier, followed by a character that cannot continue it. -/
theorem lex_ident {w : String} (hw : isAnyIdent w = true) (rest : List Char)
    (hr : ∀ d, rest.head? = some d → isIdentTail d = false) :
    lex (w.toList ++ rest) = prepend [.ident w] (lex rest) := by
  unfold isAnyIdent at hw
  cases hcs : w.toList with
  | nil => simp [hcs] at hw
  | cons c cs =>
    rw [hcs] at hw
    simp only [Bool.and_eq_true, List.all_eq_true] at hw
    obtain ⟨hc, hcs'⟩ := hw
    rw [List.cons_append, lex]
    have hc' : (c == '/') = false := by
      have := identHead_ne hc '/' (by decide); simpa using this
    simp only [identHead_not_ws hc, hc', Bool.false_and, Bool.false_eq_true, if_false, hc, if_true]
    rw [takeWhile_append_of_all rest hcs' hr, dropWhile_append_of_all rest hcs' hr]
    have : String.ofList (c :: cs) = w := by rw [← hcs, String.ofList_toList]
    rw [this]
    cases lex rest <;> simp [prepend, Except.map, bind, Except.bind, pure, Except.pure]

theorem lex_punct {c : Char} {rest : List Char} {p : String}
    (hws : c.isWhitespace = false) (hslash : c ≠ '/') (hid : isIdentHead c = false)
    (hdig : c.isDigit = false) (hq : c ≠ '"')
    (hfind : puncts.find? (fun p => (c :: rest).take p.length == p.toList) = some p) :
    lex (c :: rest) = prepend [.punct p] (lex ((c :: rest).drop p.length)) := by
  rw [lex]
  have hs : (c == '/') = false := by simpa using hslash
  have hq' : (c == '"') = false := by simpa using hq
  simp only [hws, hs, hid, hdig, hq', Bool.false_and, Bool.false_eq_true, if_false]
  split
  · rename_i p' hp'
    rw [hfind] at hp'; simp only [Option.some.injEq] at hp'; subst hp'
    cases lex _ <;> simp [prepend, Except.map, bind, Except.bind, pure, Except.pure]
  · rename_i hnone; rw [hfind] at hnone; simp at hnone

theorem lex_comma (rest : List Char) : lex (',' :: rest) = prepend [.punct ","] (lex rest) := by
  rw [lex_punct (by decide) (by decide) (by decide) (by decide) (by decide) (p := ",")
    (by simp [puncts, List.take, ← String.length_toList])]
  simp [← String.length_toList]

theorem lex_semi (rest : List Char) : lex (';' :: rest) = prepend [.punct ";"] (lex rest) := by
  rw [lex_punct (by decide) (by decide) (by decide) (by decide) (by decide) (p := ";")
    (by simp [puncts, List.take, ← String.length_toList])]
  simp [← String.length_toList]

theorem lex_lbrace (rest : List Char) : lex ('{' :: rest) = prepend [.punct "{"] (lex rest) := by
  rw [lex_punct (by decide) (by decide) (by decide) (by decide) (by decide) (p := "{")
    (by simp [puncts, List.take, ← String.length_toList])]
  simp [← String.length_toList]

theorem lex_rbrace (rest : List Char) : lex ('}' :: rest) = prepend [.punct "}"] (lex rest) := by
  rw [lex_punct (by decide) (by decide) (by decide) (by decide) (by decide) (p := "}")
    (by simp [puncts, List.take, ← String.length_toList])]
  simp [← String.length_toList]

theorem lex_langle (rest : List Char) : lex ('<' :: rest) = prepend [.punct "<"] (lex rest) := by
  rw [lex_punct (by decide) (by decide) (by decide) (by decide) (by decide) (p := "<")
    (by simp [puncts, List.take, ← String.length_toList])]
  simp [← String.length_toList]

theorem lex_rangle (rest : List Char) : lex ('>' :: rest) = prepend [.punct ">"] (lex rest) := by
  rw [lex_punct (by decide) (by decide) (by decide) (by decide) (by decide) (p := ">")
    (by simp [puncts, List.take, ← String.length_toList])]
  simp [← String.length_toList]

theorem lex_eq (rest : List Char) : lex ('=' :: rest) = prepend [.punct "="] (lex rest) := by
  rw [lex_punct (by decide) (by decide) (by decide) (by decide) (by decide) (p := "=")
    (by simp [puncts, List.take, ← String.length_toList])]
  simp [← String.length_toList]

theorem lex_qmark (rest : List Char) : lex ('?' :: rest) = prepend [.punct "?"] (lex rest) := by
  rw [lex_punct (by decide) (by decide) (by decide) (by decide) (by decide) (p := "?")
    (by simp [puncts, List.take, ← String.length_toList])]
  simp [← String.length_toList]

/-- `:`, not followed by `:`. -/
theorem lex_colon (rest : List Char) (h : rest.head? ≠ some ':') :
    lex (':' :: rest) = prepend [.punct ":"] (lex rest) := by
  rw [lex_punct (by decide) (by decide) (by decide) (by decide) (by decide) (p := ":")]
  · simp [← String.length_toList]
  · cases rest with
    | nil => simp [puncts, List.find?, List.take, ← String.length_toList]
    | cons d rest =>
      have : d ≠ ':' := fun e => h (by simp [e])
      simp [puncts, List.find?, List.take, ← String.length_toList, this]

/-- `::`. -/
theorem lex_dcolon (rest : List Char) : lex (':' :: ':' :: rest) = prepend [.punct "::"] (lex rest) := by
  rw [lex_punct (by decide) (by decide) (by decide) (by decide) (by decide) (p := "::")]
  · simp [← String.length_toList]
  · simp [puncts, List.take, ← String.length_toList]

/-! ## Strings -/

theorem intercalate_cons_cons (s a b : String) (rest : List String) :
    s.intercalate (a :: b :: rest) = s.intercalate ((a ++ s ++ b) :: rest) := rfl

theorem intercalate_append_head (s : String) :
    ∀ (acc x : String) (rest : List String),
      s.intercalate ((acc ++ x) :: rest) = acc ++ s.intercalate (x :: rest)
  | _, _, [] => rfl
  | acc, x, b :: rest => by
    rw [intercalate_cons_cons, intercalate_cons_cons,
      show acc ++ x ++ s ++ b = acc ++ (x ++ s ++ b) by simp [String.append_assoc],
      intercalate_append_head s acc (x ++ s ++ b) rest]

theorem intercalate_cons (s a b : String) (rest : List String) :
    s.intercalate (a :: b :: rest) = a ++ s ++ s.intercalate (b :: rest) := by
  rw [intercalate_cons_cons, intercalate_append_head]

theorem intercalate_singleton (s a : String) : s.intercalate [a] = a := rfl

theorem intercalate_nil (s : String) : s.intercalate [] = "" := rfl

/-! ## Paths -/

/-- A Cedar path: identifiers joined by `::`. -/
def IsPath (m : String) : Prop :=
  ∃ segs, segs ≠ [] ∧ (∀ x ∈ segs, isIdent x = true) ∧ m = "::".intercalate segs

/-- A path's tokens. -/
def pathToks : List String → List Tok
  | [] => []
  | [x] => [.ident x]
  | x :: rest => .ident x :: .punct "::" :: pathToks rest

theorem isAnyIdent_of_isIdent {x : String} (h : isIdent x = true) : isAnyIdent x = true := by
  simp only [isIdent, Bool.and_eq_true] at h; exact h.1

/-- What may follow a printed type in the synthesized text. -/
def Delim (rest : List Char) : Prop :=
  rest = [] ∨ rest.head? = some ' ' ∨ rest.head? = some ',' ∨ rest.head? = some '>'

theorem delim_not_identTail {rest : List Char} (h : Delim rest) :
    ∀ d, rest.head? = some d → isIdentTail d = false := by
  intro d hd
  rcases h with rfl | h | h | h <;> simp_all <;> subst hd <;> decide

theorem delim_not_colon {rest : List Char} (h : Delim rest) : rest.head? ≠ some ':' := by
  rcases h with rfl | h | h | h <;> simp_all

theorem lex_path : ∀ (segs : List String), segs ≠ [] → (∀ x ∈ segs, isIdent x = true) →
    ∀ (rest : List Char), Delim rest →
      lex (("::".intercalate segs).toList ++ rest) = prepend (pathToks segs) (lex rest)
  | [], h, _, _, _ => absurd rfl h
  | [x], _, hid, rest, hr => by
    rw [intercalate_singleton]
    exact lex_ident (isAnyIdent_of_isIdent (hid x (List.mem_singleton_self _))) rest
      (delim_not_identTail hr)
  | x :: y :: more, _, hid, rest, hr => by
    rw [intercalate_cons, String.toList_append, String.toList_append, List.append_assoc,
      List.append_assoc]
    rw [lex_ident (isAnyIdent_of_isIdent (hid x (List.mem_cons_self ..))) _
      (by intro d hd; simp at hd; subst hd; decide)]
    have : "::".toList = [':', ':'] := by simp
    rw [this, List.cons_append, List.cons_append, List.nil_append, lex_dcolon,
      lex_path (y :: more) (by simp) (fun z hz => hid z (List.mem_cons_of_mem _ hz)) rest hr,
      prepend_prepend, prepend_prepend]
    rfl

/-! ## The parser, on the tokens of a printed type -/

/-- What may follow a type's tokens in the synthesized text. -/
def Follow (ts : List Tok) : Prop :=
  ∀ t, ts.head? = some t → t = .punct "," ∨ t = .punct "}" ∨ t = .punct ">" ∨ t = .punct ";"

theorem follow_not_dcolon {ts : List Tok} (h : Follow ts) : ∀ rest, ts ≠ .punct "::" :: rest := by
  rintro rest rfl
  rcases h _ rfl with h | h | h | h <;> simp at h

theorem follow_not_langle {ts : List Tok} (h : Follow ts) : ∀ rest, ts ≠ .punct "<" :: rest := by
  rintro rest rfl
  rcases h _ rfl with h | h | h | h <;> simp at h

theorem parsePath_ident {w : String} (hw : isIdent w = true) {ts : List Tok} (hts : Follow ts) :
    parsePath (.ident w :: ts) = .ok (w, ts) := by
  unfold parsePath
  split
  · rename_i i rest heq
    simp only [List.cons.injEq, Tok.ident.injEq] at heq
    obtain ⟨rfl, rfl⟩ := heq
    exact absurd rfl (follow_not_dcolon hts rest)
  · rename_i i rest heq
    simp only [List.cons.injEq, Tok.ident.injEq] at heq
    obtain ⟨rfl, rfl⟩ := heq
    simp [hw]
  · rename_i heq; exact absurd rfl (heq w ts)

theorem parsePath_path : ∀ (segs : List String), segs ≠ [] → (∀ x ∈ segs, isIdent x = true) →
    ∀ {ts : List Tok}, Follow ts → parsePath (pathToks segs ++ ts) = .ok ("::".intercalate segs, ts)
  | [], h, _, _, _ => absurd rfl h
  | [x], _, hid, ts, hts => parsePath_ident (hid x (List.mem_singleton_self _)) hts
  | x :: y :: more, _, hid, ts, hts => by
    simp only [pathToks, List.cons_append]
    have ih := parsePath_path (y :: more) (by simp) (fun z hz => hid z (List.mem_cons_of_mem _ hz)) hts
    rw [parsePath, ih]
    simp [hid x (List.mem_cons_self ..), intercalate_cons, bind, Except.bind, pure, Except.pure]

theorem parseType_path (segs : List String) (hne : segs ≠ []) (hid : ∀ x ∈ segs, isIdent x = true)
    {ts : List Tok} (hts : Follow ts) (f : Nat) :
    parseType (f + 1) (pathToks segs ++ ts) = .ok (.entityOrCommon ("::".intercalate segs), ts) := by
  have hp := parsePath_path segs hne hid hts
  have hhead : ∃ x rest, pathToks segs ++ ts = .ident x :: rest ∧ (x = "Set" → rest ≠ .punct "<" :: rest.tail) := by
    match segs, hne, hid with
    | [x], _, _ => exact ⟨x, ts, rfl, fun _ h => follow_not_langle hts _ h⟩
    | x :: y :: more, _, _ => exact ⟨x, _, rfl, fun _ h => by simp at h⟩
  obtain ⟨x, rest, heq, hset⟩ := hhead
  rw [heq] at hp ⊢
  unfold parseType
  split <;> simp_all [bind, Except.bind, pure, Except.pure]

/-! ## Printed types -/

/-- The kinds of `paramType` the printing distinguishes. -/
inductive Kind where
  | str | long | bool | dec | set | record | entity | other

/-- The kind of a `paramType`. -/
def kindOf (s : String) : Kind :=
  match s with
  | "string" => .str | "integer" | "long" => .long | "bool" | "boolean" => .bool
  | "decimal" => .dec | "set" => .set | "record" => .record | "entity" => .entity | _ => .other

theorem print_eq (names : List (String × String)) (kind : String) (fields : List (String × ParamType))
    (items : Option ParamType) (required : List String) (et : Option String) :
    ParamType.toCedarTypeWith names ⟨kind, fields, items, required, et⟩ =
      match kindOf kind with
      | .str => "String" | .long => "Long" | .bool => "Bool" | .dec => "decimal"
      | .set => "Set<" ++ ParamType.toCedarTypeWithOpt names items ++ ">"
      | .record => "{ " ++ ", ".intercalate (ParamType.toCedarTypeWithFields names required fields) ++ " }"
      | .entity => (match et with | some n => (names.lookup n).getD n | none => "String")
      | .other => "String" := by
  simp only [ParamType.toCedarTypeWith]
  split <;> simp_all [kindOf] <;> cases et <;> rfl

mutual

/-- The type can be printed and parsed back: its record field names are identifiers, its entity
type names paths. -/
def Printable (names : List (String × String)) : ParamType → Prop
  | ⟨kind, fields, items, _, et⟩ =>
    match kindOf kind with
    | .set => PrintableOpt names items
    | .record => PrintableFields names fields
    | .entity => match et with
      | some n => IsPath ((names.lookup n).getD n)
      | none => True
    | _ => True

def PrintableOpt (names : List (String × String)) : Option ParamType → Prop
  | none => True
  | some p => Printable names p

def PrintableFields (names : List (String × String)) : List (String × ParamType) → Prop
  | [] => True
  | (n, p) :: rest => isBareAttrName n = true ∧ Printable names p ∧ PrintableFields names rest

end

/-- A bare attribute name is written as it is. -/
theorem attrNameText_bare {n : String} (h : isBareAttrName n = true) : attrNameText n = n := by
  simp [attrNameText, h]

/-- A bare attribute name is a Cedar identifier. -/
theorem isIdent_of_bare {n : String} (h : isBareAttrName n = true) : isIdent n = true := by
  unfold isBareAttrName at h
  unfold isIdent isAnyIdent
  simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at h ⊢
  refine ⟨h.1, ?_⟩
  have hsub : cedarReservedIds = reservedIdents ++ ["__cedar"] := rfl
  cases hr : reservedIdents.contains n with
  | false => rfl
  | true =>
    have : cedarReservedIds.contains n = true := by
      rw [hsub, List.contains_append, hr, Bool.true_or]
    rw [h.2] at this
    cases this

mutual

/-- The schema type Cedar's parser gives the printed type. -/
def schemaOf (names : List (String × String)) : ParamType → SchemaType
  | ⟨kind, fields, items, required, et⟩ =>
    match kindOf kind with
    | .str => .entityOrCommon "String"
    | .long => .entityOrCommon "Long"
    | .bool => .entityOrCommon "Bool"
    | .dec => .entityOrCommon "decimal"
    | .set => .set (schemaOfOpt names items)
    | .record => .record (schemaOfFields names required [] fields) false
    | .entity => match et with
      | some n => .entityOrCommon ((names.lookup n).getD n)
      | none => .entityOrCommon "String"
    | .other => .entityOrCommon "String"

def schemaOfOpt (names : List (String × String)) : Option ParamType → SchemaType
  | none => .entityOrCommon "String"
  | some p => schemaOf names p

/-- The record's attributes, added in field order to `acc`. -/
def schemaOfFields (names : List (String × String)) (required : List String)
    (acc : List (String × AttrType)) : List (String × ParamType) → List (String × AttrType)
  | [] => acc
  | (n, p) :: rest =>
    schemaOfFields names required (insertKey n ⟨schemaOf names p, required.contains n, []⟩ acc) rest

end

mutual

/-- A bound on the parser's nesting for the printed type. -/
def psize : ParamType → Nat
  | ⟨kind, fields, items, _, _⟩ =>
    match kindOf kind with
    | .set => psizeOpt items + 1
    | .record => psizeFields fields + 1
    | _ => 1

def psizeOpt : Option ParamType → Nat
  | none => 1
  | some p => psize p

def psizeFields : List (String × ParamType) → Nat
  | [] => 1
  | (_, p) :: rest => psize p + psizeFields rest + 1

end

/-! ## Printing then parsing -/

theorem parseAnnotations_ident (n : String) (rest : List Tok) :
    parseAnnotations (.ident n :: rest) = .ok ([], .ident n :: rest) := by
  unfold parseAnnotations; rfl

/-- The tokens of one attribute declaration `n[?]: T`. -/
def attrToks (n : String) (req : Bool) (ttoks : List Tok) : List Tok :=
  .ident n :: ((if req then [] else [.punct "?"]) ++ .punct ":" :: ttoks)

/-- The last attribute declaration, before the closing `}`. -/
theorem parseAttrDecls_last {f : Nat} {acc : List (String × AttrType)} {n : String} {req : Bool}
    {ttoks ts : List Tok} {ty : SchemaType} (hn : isIdent n = true)
    (hty : parseType f (ttoks ++ .punct "}" :: ts) = .ok (ty, .punct "}" :: ts)) :
    parseAttrDecls (f + 1) acc (attrToks n req ttoks ++ .punct "}" :: ts) =
      .ok (insertKey n ⟨ty, req, []⟩ acc, .punct "}" :: ts) := by
  rw [parseAttrDecls]
  simp only [attrToks, List.cons_append, List.append_assoc, parseAnnotations_ident]
  cases req <;> simp [hn, hty, bind, Except.bind, pure, Except.pure]

/-- An attribute declaration followed by `,` and another declaration. -/
theorem parseAttrDecls_more {f : Nat} {acc : List (String × AttrType)} {n m : String} {req : Bool}
    {ttoks ts : List Tok} {ty : SchemaType} (hn : isIdent n = true)
    (hty : parseType f (ttoks ++ .punct "," :: .ident m :: ts) = .ok (ty, .punct "," :: .ident m :: ts)) :
    parseAttrDecls (f + 1) acc (attrToks n req ttoks ++ .punct "," :: .ident m :: ts) =
      parseAttrDecls f (insertKey n ⟨ty, req, []⟩ acc) (.ident m :: ts) := by
  rw [parseAttrDecls]
  simp only [attrToks, List.cons_append, List.append_assoc, parseAnnotations_ident]
  cases req <;> simp [hn, hty, bind, Except.bind, pure, Except.pure]

/-- The text of one attribute declaration `n[?]: T` lexes to its tokens. -/
theorem lex_attr {n : String} (hn : isIdent n = true) (req : Bool) {T : String} {ttoks : List Tok}
    {rest : List Char} (hT : lex (T.toList ++ rest) = prepend ttoks (lex rest)) :
    lex ((n ++ (if req then "" else "?") ++ ": " ++ T).toList ++ rest) =
      prepend (attrToks n req ttoks) (lex rest) := by
  have hcolon : ": ".toList = [':', ' '] := by simp
  simp only [String.toList_append, hcolon, List.append_assoc]
  cases req with
  | true =>
    simp only [if_true, String.toList_empty, List.nil_append, List.cons_append]
    rw [lex_ident (isAnyIdent_of_isIdent hn) _ (by intro d hd; simp at hd; subst hd; decide),
      lex_colon _ (by simp), lex_space, hT, prepend_prepend, prepend_prepend]
    rfl
  | false =>
    have hq : "?".toList = ['?'] := by simp
    simp only [Bool.false_eq_true, if_false, hq, List.cons_append, List.nil_append]
    rw [lex_ident (isAnyIdent_of_isIdent hn) _ (by intro d hd; simp at hd; subst hd; decide),
      lex_qmark, lex_colon _ (by simp), lex_space, hT, prepend_prepend, prepend_prepend, prepend_prepend]
    rfl

mutual

/-- **Printing then parsing a printable type**: the printed text lexes to some tokens, which
parse back to `schemaOf`. -/
theorem printed_parses (names : List (String × String)) :
    ∀ (p : ParamType), Printable names p → ∀ (rest : List Char), Delim rest →
      ∃ toks, lex ((p.toCedarTypeWith names).toList ++ rest) = prepend toks (lex rest) ∧
        psize p ≤ toks.length ∧
        ∀ fuel, psize p < fuel → ∀ ts, Follow ts → parseType fuel (toks ++ ts) = .ok (schemaOf names p, ts)
  | ⟨kind, fields, items, required, et⟩, hp, rest, hr => by
    have base : ∀ w : String, isIdent w = true →
        ∃ toks, lex (w.toList ++ rest) = prepend toks (lex rest) ∧ 1 ≤ toks.length ∧
          ∀ fuel, 1 < fuel → ∀ ts, Follow ts → parseType fuel (toks ++ ts) = .ok (.entityOrCommon w, ts) :=
      fun w hw => ⟨[.ident w], lex_ident (isAnyIdent_of_isIdent hw) rest (delim_not_identTail hr),
        by simp, fun fuel hf ts hts => by
          obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
          exact parseType_path [w] (by simp) (by simpa using hw) hts f⟩
    rw [print_eq]
    simp only [Printable] at hp
    simp only [schemaOf, psize]
    cases hk : kindOf kind with
    | str => simp only; exact base "String" (by decide)
    | long => simp only; exact base "Long" (by decide)
    | bool => simp only; exact base "Bool" (by decide)
    | dec => simp only; exact base "decimal" (by decide)
    | other => simp only; exact base "String" (by decide)
    | entity =>
      simp only [hk] at hp
      cases et with
      | none => simp only; exact base "String" (by decide)
      | some n =>
        simp only at hp ⊢
        obtain ⟨segs, hne, hid, hm⟩ := hp
        rw [hm]
        refine ⟨pathToks segs, lex_path segs hne hid rest hr, ?_, fun fuel hf ts hts => by
          obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
          exact parseType_path segs hne hid hts f⟩
        match segs, hne with
        | [_], _ => simp [pathToks]
        | _ :: _ :: _, _ => simp [pathToks]
    | set =>
      simp only [hk] at hp ⊢
      obtain ⟨itoks, hilex, hilen, hiparse⟩ := printedOpt_parses names items hp ('>' :: rest)
        (.inr (.inr (.inr rfl)))
      refine ⟨[.ident "Set", .punct "<"] ++ itoks ++ [.punct ">"], ?_, by simp; omega, ?_⟩
      · rw [String.toList_append, String.toList_append, List.append_assoc, List.append_assoc]
        have h1 : "Set<".toList = "Set".toList ++ ['<'] := by simp
        have h2 : ">".toList = ['>'] := by simp
        rw [h1, h2, List.append_assoc, lex_ident (by decide) _ (by intro d hd; simp at hd; subst hd; decide),
          List.singleton_append, lex_langle, List.singleton_append, hilex, lex_rangle,
          prepend_prepend, prepend_prepend, prepend_prepend]
        simp
      · intro fuel hf ts hts
        obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
        have hin := hiparse f (by omega) (.punct ">" :: ts) (fun t ht => by simp at ht; subst ht; simp)
        simp only [List.append_assoc, List.cons_append, List.nil_append]
        simp [parseType, hin, bind, Except.bind, pure, Except.pure]
    | record =>
      simp only [hk] at hp ⊢
      by_cases hfe : fields = []
      · subst hfe
        refine ⟨[.punct "{", .punct "}"], ?_, by simp [psizeFields], ?_⟩
        · have : ("{ " ++ ", ".intercalate (ParamType.toCedarTypeWithFields names required []) ++ " }").toList =
              ['{', ' ', ' ', '}'] := by simp [ParamType.toCedarTypeWithFields, intercalate_nil]
          rw [this]
          simp only [List.cons_append, List.nil_append]
          rw [lex_lbrace, lex_space, lex_space, lex_rbrace, prepend_prepend]
          rfl
        · intro fuel hf ts _
          obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
          simp [parseType, schemaOfFields]
      · obtain ⟨ftoks, hflex, hflen, ⟨n, tl, hhead⟩, hfparse⟩ :=
          printedFields_parses names required fields hp hfe (' ' :: '}' :: rest) rfl
        refine ⟨[.punct "{"] ++ ftoks ++ [.punct "}"], ?_, by simp; omega, ?_⟩
        · have h1 : "{ ".toList = ['{', ' '] := by simp
          have h2 : " }".toList = [' ', '}'] := by simp
          simp only [String.toList_append, h1, h2, List.append_assoc, List.cons_append, List.nil_append]
          rw [lex_lbrace, lex_space, hflex, lex_space, lex_rbrace, prepend_prepend, prepend_prepend]
          simp
        · intro fuel hf ts _
          obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
          have hin := hfparse f (by omega) [] ts
          rw [hhead] at hin ⊢
          simp only [List.append_assoc, List.cons_append, List.nil_append] at hin ⊢
          simp [parseType, hin, bind, Except.bind, pure, Except.pure]

theorem printedOpt_parses (names : List (String × String)) :
    ∀ (o : Option ParamType), PrintableOpt names o → ∀ (rest : List Char), Delim rest →
      ∃ toks, lex ((ParamType.toCedarTypeWithOpt names o).toList ++ rest) = prepend toks (lex rest) ∧
        psizeOpt o ≤ toks.length ∧
        ∀ fuel, psizeOpt o < fuel → ∀ ts, Follow ts →
          parseType fuel (toks ++ ts) = .ok (schemaOfOpt names o, ts)
  | none, _, rest, hr => by
    simp only [ParamType.toCedarTypeWithOpt, schemaOfOpt, psizeOpt]
    exact ⟨[.ident "String"], lex_ident (by decide) rest (delim_not_identTail hr), by simp, fun fuel hf ts hts => by
      obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
      exact parseType_path ["String"] (by simp) (by simp; decide) hts f⟩
  | some p, hp, rest, hr => printed_parses names p hp rest hr

theorem printedFields_parses (names : List (String × String)) (required : List String) :
    ∀ (fields : List (String × ParamType)), PrintableFields names fields → fields ≠ [] →
      ∀ (rest : List Char), rest.head? = some ' ' →
        ∃ toks, lex ((", ".intercalate (ParamType.toCedarTypeWithFields names required fields)).toList ++ rest) =
            prepend toks (lex rest) ∧
          psizeFields fields ≤ toks.length + 1 ∧
          (∃ n tl, toks = .ident n :: tl) ∧
          ∀ fuel, psizeFields fields < fuel → ∀ acc ts,
            parseAttrDecls fuel acc (toks ++ .punct "}" :: ts) =
              .ok (schemaOfFields names required acc fields, .punct "}" :: ts)
  | [], _, h, _, _ => absurd rfl h
  | [(n, p)], hp, _, rest, hr => by
    simp only [PrintableFields] at hp
    obtain ⟨hb, hpp, _⟩ := hp
    have hn := isIdent_of_bare hb
    obtain ⟨ttoks, htlex, htlen, htparse⟩ := printed_parses names p hpp rest (.inr (.inl hr))
    refine ⟨attrToks n (required.contains n) ttoks, ?_, ?_, ⟨n, _, rfl⟩, ?_⟩
    · have e : ParamType.toCedarTypeWithFields names required [(n, p)] =
          [n ++ (if required.contains n then "" else "?") ++ ": " ++ ParamType.toCedarTypeWith names p] := by
        simp only [ParamType.toCedarTypeWithFields, attrNameText_bare hb]
      rw [e, intercalate_singleton]
      exact lex_attr hn _ htlex
    · simp only [psizeFields, attrToks]; split <;> simp <;> omega
    · intro fuel hf acc ts
      obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by simp [psizeFields] at hf; omega⟩
      simp only [psizeFields] at hf
      rw [parseAttrDecls_last hn (htparse f (by omega) (.punct "}" :: ts)
        (fun t ht => by simp at ht; subst ht; simp))]
      simp [schemaOfFields]
  | (n, p) :: g :: more, hp, _, rest, hr => by
    simp only [PrintableFields] at hp
    obtain ⟨hb, hpp, hrestp⟩ := hp
    have hn := isIdent_of_bare hb
    obtain ⟨rtoks, hrlex, hrlen, ⟨m, rtl, hrhead⟩, hrparse⟩ :=
      printedFields_parses names required (g :: more) hrestp (by simp) rest hr
    have hcomma : ", ".toList = [',', ' '] := by simp
    obtain ⟨ttoks, htlex, htlen, htparse⟩ := printed_parses names p hpp
      ((", ".intercalate (ParamType.toCedarTypeWithFields names required (g :: more))).toList ++ rest |>.cons ' ' |>.cons ',')
      (.inr (.inr (.inl rfl)))
    refine ⟨attrToks n (required.contains n) ttoks ++ .punct "," :: rtoks, ?_, ?_, ⟨n, _, rfl⟩, ?_⟩
    · have e : ParamType.toCedarTypeWithFields names required ((n, p) :: g :: more) =
          (n ++ (if required.contains n then "" else "?") ++ ": " ++ ParamType.toCedarTypeWith names p) ::
            ParamType.toCedarTypeWithFields names required (g :: more) := by
        conv => lhs; unfold ParamType.toCedarTypeWithFields
        rw [attrNameText_bare hb]
      have e2 : ∃ s t, ParamType.toCedarTypeWithFields names required (g :: more) = s :: t :=
        ⟨_, _, rfl⟩
      obtain ⟨s₂, t₂, he2⟩ := e2
      rw [e, he2, intercalate_cons, String.toList_append, String.toList_append, hcomma]
      rw [he2] at htlex hrlex
      simp only [List.append_assoc, List.cons_append, List.nil_append]
      rw [lex_attr hn _ htlex, lex_comma, lex_space, hrlex, prepend_prepend, prepend_prepend]
      simp
    · simp only [psizeFields, attrToks] at hrlen ⊢; split <;> simp <;> omega
    · intro fuel hf acc ts
      obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by simp [psizeFields] at hf; omega⟩
      simp only [psizeFields] at hf
      rw [hrhead]
      simp only [List.append_assoc, List.cons_append]
      rw [hrhead] at hrparse
      rw [parseAttrDecls_more hn (htparse f (by omega) _ (fun t ht => by simp at ht; subst ht; simp))]
      have := hrparse f (by simp only [psizeFields] at hf ⊢; omega) (insertKey n ⟨schemaOf names p, required.contains n, []⟩ acc) ts
      simp only [List.cons_append] at this
      rw [this]
      rfl

end

/-! ## The synthesized text -/

/-- The provider fields' attributes, in the order the parser adds them: each required, typed by
`schemaOf` of its declared type. -/
def provAttrs (names : List (String × String)) (ps : ProviderField → ParamType)
    (acc : List (String × AttrType)) : List ProviderField → List (String × AttrType)
  | [] => acc
  | f :: rest => provAttrs names ps (insertKey f.fieldName ⟨schemaOf names (ps f), true, []⟩ acc) rest

/-- A bound on the parser's nesting for the provider fields. -/
def provSize (ps : ProviderField → ParamType) : List ProviderField → Nat
  | [] => 1
  | f :: rest => psize (ps f) + provSize ps rest + 1

/-- A provider field whose Cedar type text is that of a printable declared type `p`. -/
def PrintedField (names : List (String × String)) (ps : ProviderField → ParamType) (f : ProviderField) :
    Prop :=
  isIdent f.fieldName = true ∧ f.cedarType = (ps f).toCedarTypeWith names ∧ Printable names (ps f)

theorem field_text (f : ProviderField) :
    s!"{f.fieldName}: {f.cedarType}" = f.fieldName ++ ": " ++ f.cedarType := rfl

/-- A required attribute declaration `n: T`. -/
theorem lex_attr_req {n : String} (hn : isIdent n = true) {T : String} {ttoks : List Tok}
    {rest : List Char} (hT : lex (T.toList ++ rest) = prepend ttoks (lex rest)) :
    lex ((n ++ ": " ++ T).toList ++ rest) = prepend (attrToks n true ttoks) (lex rest) := by
  have := lex_attr hn true hT
  simpa using this

theorem providerFields_parses (names : List (String × String)) (ps : ProviderField → ParamType) :
    ∀ (fields : List ProviderField), (∀ f ∈ fields, PrintedField names ps f) → fields ≠ [] →
      ∀ (rest : List Char), rest.head? = some ' ' →
        ∃ toks, lex ((", ".intercalate (fields.map fun f => s!"{f.fieldName}: {f.cedarType}")).toList ++ rest) =
            prepend toks (lex rest) ∧
          provSize ps fields ≤ toks.length + 1 ∧ (∃ n tl, toks = .ident n :: tl) ∧
          ∀ fuel, provSize ps fields < fuel → ∀ acc ts,
            parseAttrDecls fuel acc (toks ++ .punct "}" :: ts) =
              .ok (provAttrs names ps acc fields, .punct "}" :: ts)
  | [], _, h, _, _ => absurd rfl h
  | [f], hf, _, rest, hr => by
    obtain ⟨hn, hty, hpp⟩ := hf f (List.mem_singleton_self _)
    obtain ⟨ttoks, htlex, htlen, htparse⟩ := printed_parses names (ps f) hpp rest (.inr (.inl hr))
    rw [← hty] at htlex
    refine ⟨attrToks f.fieldName true ttoks, ?_, ?_, ⟨f.fieldName, _, rfl⟩, ?_⟩
    · simp only [List.map_cons, List.map_nil, intercalate_singleton, field_text]
      exact lex_attr_req hn htlex
    · simp only [provSize, attrToks]; simp; omega
    · intro fuel hfu acc ts
      obtain ⟨g, rfl⟩ : ∃ g, fuel = g + 1 := ⟨fuel - 1, by simp [provSize] at hfu; omega⟩
      simp only [provSize] at hfu
      rw [parseAttrDecls_last hn (htparse g (by omega) (.punct "}" :: ts)
        (fun t ht => by simp at ht; subst ht; simp))]
      rfl
  | f :: g :: more, hf, _, rest, hr => by
    obtain ⟨hn, hty, hpp⟩ := hf f (List.mem_cons_self ..)
    obtain ⟨rtoks, hrlex, hrlen, ⟨m, rtl, hrhead⟩, hrparse⟩ :=
      providerFields_parses names ps (g :: more) (fun x hx => hf x (List.mem_cons_of_mem _ hx)) (by simp)
        rest hr
    have hcomma : ", ".toList = [',', ' '] := by simp
    obtain ⟨ttoks, htlex, htlen, htparse⟩ := printed_parses names (ps f) hpp
      ((", ".intercalate ((g :: more).map fun f => s!"{f.fieldName}: {f.cedarType}")).toList ++ rest
        |>.cons ' ' |>.cons ',')
      (.inr (.inr (.inl rfl)))
    rw [← hty] at htlex
    refine ⟨attrToks f.fieldName true ttoks ++ .punct "," :: rtoks, ?_, ?_, ⟨f.fieldName, _, rfl⟩, ?_⟩
    · have e : (f :: g :: more).map (fun f => s!"{f.fieldName}: {f.cedarType}") =
          s!"{f.fieldName}: {f.cedarType}" :: (g :: more).map (fun f => s!"{f.fieldName}: {f.cedarType}") :=
        rfl
      have e2 : ∃ s t, (g :: more).map (fun f => s!"{f.fieldName}: {f.cedarType}") = s :: t := ⟨_, _, rfl⟩
      obtain ⟨s₂, t₂, he2⟩ := e2
      rw [e, he2, intercalate_cons, String.toList_append, String.toList_append, hcomma, field_text]
      rw [he2] at htlex hrlex
      simp only [List.append_assoc, List.cons_append, List.nil_append]
      rw [lex_attr_req hn htlex, lex_comma, lex_space, hrlex, prepend_prepend, prepend_prepend]
      simp
    · simp only [provSize, attrToks] at hrlen ⊢; simp; omega
    · intro fuel hfu acc ts
      obtain ⟨k, rfl⟩ : ∃ k, fuel = k + 1 := ⟨fuel - 1, by simp [provSize] at hfu; omega⟩
      simp only [provSize] at hfu
      rw [hrhead]
      simp only [List.append_assoc, List.cons_append]
      rw [hrhead] at hrparse
      rw [parseAttrDecls_more hn (htparse k (by omega) _ (fun t ht => by simp at ht; subst ht; simp))]
      have := hrparse k (by simp only [provSize] at hfu ⊢; omega)
        (insertKey f.fieldName ⟨schemaOf names (ps f), true, []⟩ acc) ts
      simp only [List.cons_append] at this
      rw [this]
      rfl

/-- **The synthesized provider type parses back to the declared types**: when every provider
field's name is an identifier and its Cedar type text is that of a printable declared type
`ps f`, the provider pass's parse gives each field, required, the type `schemaOf (ps f)`. -/
theorem synthesizedAttrs_eq (names : List (String × String)) (ps : ProviderField → ParamType)
    (fields : List ProviderField) (hf : ∀ f ∈ fields, PrintedField names ps f) :
    synthesizedAttrs fields = .ok (provAttrs names ps [] fields) := by
  unfold synthesizedAttrs providerTypeText parseCommonTypeDecl
  have hpre : "type __PR = { ".toList =
      "type".toList ++ ' ' :: ("__PR".toList ++ [' ', '=', ' ', '{', ' ']) := by simp
  have hpost : " };".toList = [' ', '}', ';'] := by simp
  have hnil : lex [] = .ok [] := by rw [lex]
  have hpr : isIdent "__PR" = true := by decide
  simp only [String.toList_append, hpre, hpost, List.append_assoc, List.cons_append, List.nil_append]
  rw [lex_ident (by decide) _ (by intro d hd; simp at hd; subst hd; decide), lex_space,
    lex_ident (by decide) _ (by intro d hd; simp at hd; subst hd; decide), lex_space, lex_eq, lex_space,
    lex_lbrace, lex_space]
  by_cases hfe : fields = []
  · subst hfe
    simp only [List.map_nil, intercalate_nil, String.toList_empty, List.nil_append]
    rw [lex_space, lex_rbrace, lex_semi, hnil]
    simp [prepend, Except.map, bind, Except.bind, pure, Except.pure, parseType, provAttrs, hpr]
  · obtain ⟨ftoks, hflex, hflen, ⟨n, tl, hhead⟩, hfparse⟩ :=
      providerFields_parses names ps fields hf hfe [' ', '}', ';'] rfl
    rw [hflex, lex_space, lex_rbrace, lex_semi, hnil]
    simp only [prepend, Except.map, bind, Except.bind, List.append_nil, List.cons_append]
    have hparse : ∀ k, provSize ps fields < k →
        parseType (k + 1) (.punct "{" :: (ftoks ++ .punct "}" :: [.punct ";"])) =
          .ok (.record (provAttrs names ps [] fields) false, [.punct ";"]) := by
      intro k hk
      have := hfparse k hk [] [.punct ";"]
      rw [hhead] at this ⊢
      simp only [List.cons_append] at this ⊢
      simp [parseType, this, bind, Except.bind, pure, Except.pure]
    simp only [List.nil_append, hpr, Bool.not_true, Bool.false_eq_true, if_false, pure, Except.pure]
    rw [hparse _ (by simp; omega)]
    rfl

/-! ## The shared provider type holds the declared types -/

/-- A list in strictly increasing key order. -/
def Sorted {α : Type} (l : List (String × α)) : Prop := l.Pairwise fun a b => a.1 < b.1

theorem mem_insertKey {α : Type} (k : String) (v : α) :
    ∀ {l : List (String × α)} {b : String × α}, b ∈ insertKey k v l → b = (k, v) ∨ b ∈ l
  | [], b, h => by simp [insertKey] at h; exact .inl h
  | (k', v') :: rest, b, h => by
    unfold insertKey at h
    split at h
    · rcases List.mem_cons.mp h with h | h
      · exact .inl h
      · exact .inr h
    · split at h
      · rcases List.mem_cons.mp h with h | h
        · exact .inl h
        · exact .inr (List.mem_cons_of_mem _ h)
      · rcases List.mem_cons.mp h with h | h
        · exact .inr (h ▸ List.mem_cons_self ..)
        · rcases mem_insertKey k v h with h | h
          · exact .inl h
          · exact .inr (List.mem_cons_of_mem _ h)

theorem insertKey_sorted {α : Type} (k : String) (v : α) :
    ∀ {l : List (String × α)}, Sorted l → Sorted (insertKey k v l)
  | [], _ => by simp [insertKey, Sorted]
  | (k', v') :: rest, h => by
    simp only [Sorted, List.pairwise_cons] at h
    obtain ⟨hlt, hrest⟩ := h
    unfold insertKey
    by_cases h1 : k < k'
    · rw [if_pos h1]
      simp only [Sorted, List.pairwise_cons, List.mem_cons, forall_eq_or_imp]
      exact ⟨⟨h1, fun b hb => String.lt_trans h1 (hlt b hb)⟩, hlt, hrest⟩
    · rw [if_neg h1]
      by_cases h2 : k = k'
      · subst h2; simp only [beq_self_eq_true, if_true, Sorted, List.pairwise_cons]; exact ⟨hlt, hrest⟩
      · have hb : (k == k') = false := by simpa using h2
        have hk'k : k' < k := Std.lt_of_le_of_ne (String.not_lt.mp h1) (Ne.symm h2)
        simp only [hb, Bool.false_eq_true, if_false, Sorted, List.pairwise_cons]
        refine ⟨fun b hb' => ?_, insertKey_sorted k v hrest⟩
        rcases mem_insertKey k v hb' with rfl | hmem
        · exact hk'k
        · exact hlt b hmem

theorem provAttrs_sorted (names : List (String × String)) (ps : ProviderField → ParamType) :
    ∀ {acc : List (String × AttrType)} (fields : List ProviderField), Sorted acc →
      Sorted (provAttrs names ps acc fields)
  | _, [], h => h
  | _, _ :: rest, h => provAttrs_sorted names ps rest (insertKey_sorted _ _ h)

theorem sorted_nodup_keys {α : Type} : ∀ {l : List (String × α)}, Sorted l → (l.map Prod.fst).Nodup
  | [], _ => by simp
  | (k, v) :: rest, h => by
    simp only [Sorted, List.pairwise_cons] at h
    simp only [List.map_cons, List.nodup_cons, List.mem_map]
    refine ⟨?_, sorted_nodup_keys h.2⟩
    rintro ⟨b, hb, hbk⟩
    have := h.1 b hb
    rw [hbk] at this
    exact String.lt_irrefl k this

theorem lookup_reverse_of_nodup {α : Type} {l : List (String × α)} (h : (l.map Prod.fst).Nodup)
    (key : String) : l.reverse.lookup key = l.lookup key := by
  induction l with
  | nil => rfl
  | cons p rest ih =>
    obtain ⟨k, v⟩ := p
    simp only [List.map_cons, List.nodup_cons, List.mem_map] at h
    obtain ⟨hnot, hnd⟩ := h
    rw [List.reverse_cons, List.lookup_append, ih hnd, Dogwood.Frontend.Augment.lookup_cons_eq]
    by_cases hk : key = k
    · subst hk
      have : rest.lookup key = none := by
        cases hl : rest.lookup key with
        | none => rfl
        | some w =>
          obtain ⟨l₁, l₂, heq, _⟩ := List.lookup_eq_some_iff.mp hl
          exact absurd ⟨(key, w), by rw [heq]; simp, rfl⟩ hnot
      simp [this]
    · simp [hk, Dogwood.Frontend.Augment.lookup_cons_eq]

theorem lookup_provAttrs_not_mem (names : List (String × String)) (ps : ProviderField → ParamType)
    (key : String) : ∀ {acc : List (String × AttrType)} (fields : List ProviderField),
      (∀ f ∈ fields, f.fieldName ≠ key) → (provAttrs names ps acc fields).lookup key = acc.lookup key
  | _, [], _ => rfl
  | acc, f :: rest, h => by
    simp only [provAttrs]
    rw [lookup_provAttrs_not_mem names ps key rest (fun g hg => h g (List.mem_cons_of_mem _ hg)),
      Dogwood.Frontend.Augment.lookup_insertKey_ne _ _ (Ne.symm (h f (List.mem_cons_self ..)))]

/-- With distinct names, each provider field has its declared type in the parsed record. -/
theorem lookup_provAttrs (names : List (String × String)) (ps : ProviderField → ParamType) :
    ∀ {acc : List (String × AttrType)} (fields : List ProviderField),
      (fields.map (·.fieldName)).Nodup → ∀ f ∈ fields,
        (provAttrs names ps acc fields).lookup f.fieldName = some ⟨schemaOf names (ps f), true, []⟩
  | _, [], _, _, hf => by simp at hf
  | acc, g :: rest, hnd, f, hf => by
    simp only [List.map_cons, List.nodup_cons, List.mem_map] at hnd
    obtain ⟨hnot, hnd⟩ := hnd
    simp only [provAttrs]
    rcases List.mem_cons.mp hf with rfl | hf
    · rw [lookup_provAttrs_not_mem names ps _ rest (fun h hh e => hnot ⟨h, hh, e⟩),
        Dogwood.Frontend.Augment.lookup_insertKey_self]
    · exact lookup_provAttrs names ps rest hnd f hf

end Dogwood.Frontend.Augment.TypeText

namespace Dogwood.Frontend.Augment

open CedarSchema ProviderDecls TypeText

theorem firstDuplicate_go_none : ∀ {seen xs : List String}, firstDuplicate.go seen xs = none →
    xs.Nodup ∧ ∀ x ∈ xs, x ∉ seen
  | _, [], _ => by simp
  | seen, x :: rest, h => by
    unfold firstDuplicate.go at h
    split at h
    · exact absurd h (by simp)
    · rename_i hx
      obtain ⟨hnd, hnot⟩ := firstDuplicate_go_none h
      refine ⟨List.nodup_cons.mpr ⟨fun hm => hnot x hm (List.mem_cons_self ..), hnd⟩, ?_⟩
      intro y hy
      rcases List.mem_cons.mp hy with rfl | hy
      · simpa using hx
      · exact fun hs => hnot y hy (List.mem_cons_of_mem _ hs)

theorem nodup_of_firstDuplicate {xs : List String} (h : firstDuplicate xs = none) : xs.Nodup :=
  (firstDuplicate_go_none h).1

theorem augmentSchema_nodup {F F' : Fragment} {decls : Option Declarations} {enums : List String}
    {CF : List ContextField} {PF : List ProviderField}
    (h : augmentSchema F decls enums CF PF = .ok F') :
    (CF.map (·.fieldName)).Nodup ∧ (PF.map (·.fieldName)).Nodup := by
  unfold augmentSchema at h
  split at h
  · exact absurd h (by simp)
  · rename_i hdup
    simp only [duplicateHoistedName, Option.orElse] at hdup
    split at hdup
    · exact absurd hdup (by simp)
    · rename_i h₁
      exact ⟨nodup_of_firstDuplicate h₁, nodup_of_firstDuplicate hdup⟩

/-- **The shared provider type holds every provider field with its declared type.** When every
provider field's Cedar type text is that of a printable type `ps f`, an inline context of an
action a provider field targets gets the attribute `providers`, referencing the namespace's
shared provider type, a record with every provider field, required, of type `schemaOf (ps f)`
with some builtin names pinned to `__cedar::` (`pinBuiltinNames`; the pass pins those some
namespace declares). -/
theorem augment_provider_types {F F' : Fragment} {decls : Option Declarations} {enums : List String}
    {CF : List ContextField} {PF : List ProviderField} {nsName id : String} {k : Option String}
    {attrs : List (String × AttrType)} {add : Bool} (names : List (String × String))
    (ps : ProviderField → ParamType)
    (h : augmentSchema F decls enums CF PF = .ok F') (hk : nsKey nsName = .ok k)
    (hc : contextAt F k id = some (.record attrs add)) (hmem : (nsName, id) ∈ providerTargets PF)
    (hprint : ∀ f ∈ PF, PrintedField names ps f) :
    ∃ attrs' S c allAttrs ds, contextAt F' k id = some (.record attrs' add) ∧
      (∃ pa, attrs'.lookup "providers" = some pa ∧ providerTypeReferenceMatches pa.ty nsName S = true) ∧
      commonTypeAt F' k S = some c ∧ c.ty = .record allAttrs false ∧
      ∀ f ∈ PF, allAttrs.lookup f.fieldName = some ⟨pinBuiltinNames ds (schemaOf names (ps f)), true, []⟩ := by
  obtain ⟨attrs', hc', hP⟩ := augmentSchema_context h hk hc
  rw [if_pos hmem] at hP
  obtain ⟨_, S, newAttrs, _, hnew, ⟨_, hpa⟩, c, allAttrs, ds, hcS, hcty, hall⟩ := hP
  rw [synthesizedAttrs_eq names ps PF hprint] at hnew
  simp only [Except.ok.injEq] at hnew
  subst hnew
  refine ⟨attrs', S, c, allAttrs, ds, hc', hpa, hcS, hcty, fun f hf => ?_⟩
  have hnd := (augmentSchema_nodup h).2
  have hl := lookup_provAttrs names ps (acc := []) PF hnd f hf
  rw [hall f.fieldName (by rw [hl]; rfl), pinBuiltinAttrs_reverse, lookup_pinBuiltinAttrs,
    lookup_reverse_of_nodup (sorted_nodup_keys (provAttrs_sorted names ps PF (by simp [Sorted]))), hl]
  rfl

/-- **A declared provider field is typed by its declared output type** in the shared provider
type, when cedarify typed it by `cedarTypeOf` and its declared output type is printable. -/
theorem augment_provider_declared_types {F F' : Fragment} {decls : Option Declarations}
    {enums : List String} {CF : List ContextField} {PF : List ProviderField} {nsName id : String}
    {k : Option String} {attrs : List (String × AttrType)} {add : Bool}
    (names : List (String × String)) (ps : ProviderField → ParamType)
    (h : augmentSchema F decls enums CF PF = .ok F') (hk : nsKey nsName = .ok k)
    (hc : contextAt F k id = some (.record attrs add)) (hmem : (nsName, id) ∈ providerTargets PF)
    (hname : ∀ f ∈ PF, isIdent f.fieldName = true)
    (hct : ∀ f ∈ PF, f.cedarType = cedarTypeOf decls names f.invocation.key (f.methods.map (·.name)))
    (hdecl : ∀ f ∈ PF, ∃ d, decls.bind (·.get f.invocation.key) = some d ∧
      declaredOutput d (f.methods.map (·.name)) = some (ps f) ∧ Printable names (ps f)) :
    ∃ attrs' S c allAttrs ds, contextAt F' k id = some (.record attrs' add) ∧
      (∃ pa, attrs'.lookup "providers" = some pa ∧ providerTypeReferenceMatches pa.ty nsName S = true) ∧
      commonTypeAt F' k S = some c ∧ c.ty = .record allAttrs false ∧
      ∀ f ∈ PF, allAttrs.lookup f.fieldName = some ⟨pinBuiltinNames ds (schemaOf names (ps f)), true, []⟩ := by
  refine augment_provider_types names ps h hk hc hmem fun f hf => ?_
  obtain ⟨d, hd, ho, hp⟩ := hdecl f hf
  exact ⟨hname f hf, (hct f hf).trans (cedarTypeOf_eq_declared hd ho), hp⟩

end Dogwood.Frontend.Augment
