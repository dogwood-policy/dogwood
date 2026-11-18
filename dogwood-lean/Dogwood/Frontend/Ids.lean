import Dogwood.Frontend.Types
import Dogwood.Frontend.Identity

/-!
# Stable ids and distincters

The crate's assignment of stable policy ids (`policy_set::assign_ids`, behind
`ParsedPolicySet::with_ids`) and its checks of distincters (`Distincter::from_str`, and
`lower_many`'s check that the distincters are distinct).

* **Ids.** With `IdSource.annotation`, each policy's one `@id` annotation, with a value, is its
  id; a policy without one, or with two, is an error. With `IdSource.explicit ids`, `ids` must
  have one id per policy. Then each id, in order, must be 1 to 128 bytes of `[A-Za-z0-9_.:-]`
  (`identity::validate_policy_id`), and must not repeat an earlier one. Every error has the
  category `policyId`, the crate's message byte for byte, and the policy's span when it is about
  one policy.
* **Distincters.** A distincter is a Cedar identifier (`[_A-Za-z][_A-Za-z0-9]*`, a keyword
  included) and nothing else: Cedar's parser reads an identifier with white space and `//`
  comments around it, which the crate rejects in a distincter.
-/

namespace Dogwood.Frontend.Ids

/-! ## Rust's `escape_default` -/

/-- One character as Rust's `char::escape_default` writes it: `\t \r \n \' \" \\` escaped, a
printable ASCII character as itself, and every other character as `\u{…}` in lowercase
hexadecimal. Unlike `escape_debug`, it needs no Unicode table. -/
def escapeDefaultChar (c : Char) : String :=
  if c == '\t' then "\\t"
  else if c == '\r' then "\\r"
  else if c == '\n' then "\\n"
  else if c == '\'' then "\\'"
  else if c == '"' then "\\\""
  else if c == '\\' then "\\\\"
  else if 0x20 ≤ c.toNat && c.toNat ≤ 0x7e then String.singleton c
  else "\\u{" ++ RuleIdentity.hexDigits c.toNat ++ "}"

/-- A string as Rust's `str::escape_default` writes it. -/
def escapeDefault (s : String) : String := String.join (s.toList.map escapeDefaultChar)

/-! ## Policy ids -/

/-- The longest policy id, in bytes (crate `MAX_POLICY_ID_LEN`). -/
def maxPolicyIdLen : Nat := 128

/-- A character of the portable id alphabet `[A-Za-z0-9_.:-]`. -/
def isIdChar (c : Char) : Bool :=
  c.isAlphanum || c == '_' || c == '.' || c == ':' || c == '-'

/-- Check one policy id (crate `identity::validate_policy_id`): the reason it is invalid. -/
def validatePolicyId (id : String) : Except String Unit :=
  if id.isEmpty then .error "a policy id must not be empty"
  else if id.utf8ByteSize > maxPolicyIdLen then
    .error s!"a policy id must be at most {maxPolicyIdLen} characters (this one has {id.utf8ByteSize})"
  else match id.toList.find? (fun c => !isIdChar c) with
    | some c =>
      .error ("a policy id may only use the characters [A-Za-z0-9_.:-]; `" ++ escapeDefaultChar c ++
        "` is not allowed")
    | none => .ok ()

/-- A stable-id error. -/
def idError (kind : PolicyIdKind) (message : String) (policy : Option Nat) (id : Option String)
    (span : Option Span) : Error :=
  { stage := .assignIds, category := .policyId, message, span, policyId := some { kind, policy, id } }

/-- The message of a policy without an `@id`. -/
def missingMessage (k : Nat) : String :=
  s!"policy {k} has no `@id(\"…\")` annotation, which IdSource::Annotation requires"

/-- An `@id` annotation as a message shows it: `@id("…")`, its value escaped, or `@id`. -/
def idAnnotationText (a : Surface.Annotation) : String :=
  match a.value with
  | some v => "@id(\"" ++ escapeDefault v ++ "\")"
  | none => "@id"

/-- The message of a policy with two `@id` annotations, `first` and then `second`. -/
def repeatedMessage (k : Nat) (first second : Surface.Annotation) : String :=
  s!"policy {k} has a second `@id` annotation, `{idAnnotationText second}` after `{idAnnotationText first}`; IdSource::Annotation takes a policy's id from its one `@id(\"…\")` annotation"

/-- The id of policy `k` under `IdSource.annotation`: the value of its one `@id` annotation. A
policy with two is an error: its id would be ambiguous (the crate's Cedar policy keeps the last
annotation of a key). -/
def annotationId (k : Nat) (p : Surface.Policy) : Result String :=
  match p.annotations.filter (·.key == "id") with
  | first :: second :: _ =>
    .error (idError .repeatedAnnotation (repeatedMessage k first second) (some k) none (some p.span))
  | [⟨_, some v⟩] => .ok v
  | _ => .error (idError .missing (missingMessage k) (some k) none (some p.span))

/-- Check the ids from the `k`-th on, in order: each valid, and none a repeat of an earlier one
(`seen`, each with its policy). -/
def checkIds (spans : List Span) (seen : List (String × Nat)) : Nat → List String → Result Unit
  | _, [] => .ok ()
  | k, id :: rest => do
    match validatePolicyId id with
    | .error reason =>
      throw (idError .invalid s!"invalid policy id `{escapeDefault id}` for policy {k}: {reason}"
        (some k) (some id) (spans[k]?))
    | .ok () => pure ()
    match seen.lookup id with
    | some first =>
      throw (idError .duplicate
        s!"duplicate policy id `{id}`: policies {first} and {k} both use it" (some k) (some id)
        (spans[k]?))
    | none => checkIds spans (seen ++ [(id, k)]) (k + 1) rest

/-- The stable ids of a set's policies (crate `assign_ids`): none for positional ids, else one
valid, distinct id per policy, in source order. -/
def assignIds (ps : List Surface.Policy) : IdSource → Result (Option (List String))
  | .positional => .ok none
  | .annotation => do
    let ids ← (ps.zipIdx).mapM fun (p, k) => annotationId k p
    checkIds (ps.map (·.span)) [] 0 ids
    return some ids
  | .explicit ids => do
    if ids.length != ps.length then
      throw (idError .countMismatch
        s!"IdSource::Explicit gave {ids.length} ids for {ps.length} policies" none none none)
    checkIds (ps.map (·.span)) [] 0 ids
    return some ids

/-! ## Distincters -/

/-- The first character of an identifier, `[_a-zA-Z]`. -/
def isIdentStart (c : Char) : Bool := c.isAlpha || c == '_'

/-- A later character of an identifier, `[_a-zA-Z0-9]`. -/
def isIdentChar (c : Char) : Bool := c.isAlphanum || c == '_'

/-- Whether `s` is a distincter (crate `Distincter::from_str`): an identifier
(`[_A-Za-z][_A-Za-z0-9]*`, a keyword included) and nothing around it. -/
def isDistincter (s : String) : Bool :=
  match s.toList with
  | c :: rest => isIdentStart c && rest.all isIdentChar
  | [] => false

/-- Check a distincter (crate `Error::InvalidDistincter`, whose payload is the distincter). -/
def checkDistincter (d : String) : Result Unit :=
  if isDistincter d then .ok ()
  else .error { stage := .distincters, category := .invalidDistincter, message := d }

/-- The first distincter that repeats an earlier one (crate `lower_many`: `DuplicateDistincter`). -/
def firstRepeat : List String → List String → Option String
  | _, [] => none
  | seen, d :: rest => if seen.contains d then some d else firstRepeat (d :: seen) rest

end Dogwood.Frontend.Ids
