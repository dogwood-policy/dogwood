import Dogwood.Frontend.Types
import Dogwood.Frontend.Escape

/-!
# Helpers of schema augmentation: Cedar names, maps in key order, fragment access

What the crate takes from Cedar and the Rust standard library to edit a schema fragment, in the
small: Cedar's identifiers and names (`Id`, `Name::from_normalized_str`), `str::rsplit_once`,
`str::escape_debug` (Cedar's `Eid::escaped`, which the crate's messages use for action ids),
and `BTreeMap` insertion, on the association lists, in key order, of `CedarSchema`.
-/

namespace Dogwood.Frontend.Augment

open CedarSchema

/-! ## Strings and Cedar names -/

/-- `s` cut at the last occurrence of `::` (Rust `str::rsplit_once("::")`). -/
def rsplitOnce (s : String) : Option (String × String) :=
  let cs := s.toList
  let idx := (List.range cs.length).reverse.find? fun i => (cs.drop i).take 2 == [':', ':']
  idx.map fun i => (String.ofList (cs.take i), String.ofList (cs.drop (i + 2)))

/-- A character that may start a Cedar identifier. -/
def isIdentHead (c : Char) : Bool :=
  c == '_' || ('a' ≤ c && c ≤ 'z') || ('A' ≤ c && c ≤ 'Z')

/-- A character that may continue a Cedar identifier. -/
def isIdentTail (c : Char) : Bool := isIdentHead c || ('0' ≤ c && c ≤ '9')

/-- `[_a-zA-Z][_a-zA-Z0-9]*` (Cedar `AnyId`, keywords included). -/
def isAnyIdent (s : String) : Bool :=
  match s.toList with
  | [] => false
  | c :: cs => isIdentHead c && cs.all isIdentTail

/-- The words a Cedar identifier (`Id`) cannot be. -/
def reservedIdents : List String := ["true", "false", "if", "then", "else", "in", "is", "like", "has"]

/-- A Cedar identifier (`Id::from_str`): an `AnyId` that is not a reserved word. -/
def isIdent (s : String) : Bool := isAnyIdent s && !reservedIdents.contains s

/-- A Cedar name in normal form (`Name::from_normalized_str`): identifiers joined by `::`, none of
them `__cedar`. -/
def isName (s : String) : Bool :=
  (s.splitOn "::").all fun seg => isIdent seg && seg != "__cedar"

/-- The characters contain `::`. -/
def hasPathSep : List Char → Bool
  | ':' :: ':' :: _ => true
  | _ :: rest => hasPathSep rest
  | [] => false

/-- A name without a namespace: no `::` in it. -/
def isUnqualified (s : String) : Bool := !hasPathSep s.toList

/-- `id` in the namespace `ns`. -/
def qualify : Option String → String → String
  | none, id => id
  | some ns, id => ns ++ "::" ++ id

/-- An action id as the crate's messages print it (`Eid::escaped`, Rust `str::escape_debug`). -/
def escapedActionId (id : String) : String := Escape.strEscapeDebug id

/-! ## Maps in key order -/

/-- Insert `(k, v)` into a list in key order, replacing the value of an equal key
(`BTreeMap::insert`). -/
def insertKey {α : Type} (k : String) (v : α) : List (String × α) → List (String × α)
  | [] => [(k, v)]
  | (k', v') :: rest =>
    if k < k' then (k, v) :: (k', v') :: rest
    else if k == k' then (k, v) :: rest
    else (k', v') :: insertKey k v rest

/-- The first element of `xs` equal to one before it (the crate's `duplicate`). -/
def firstDuplicate (xs : List String) : Option String :=
  go [] xs
where
  go (seen : List String) : List String → Option String
    | [] => none
    | x :: rest => if seen.contains x then some x else go (x :: seen) rest

/-! ## Fragments -/

/-- A namespace's key as the crate writes it (`""` for the root namespace). -/
def namespaceString (k : Option String) : String := k.getD ""

/-- The key of the namespace named `namespace` (the crate's `ns_key`): the root namespace for
`""`. -/
def nsKey (nsName : String) : Except String (Option String) :=
  if nsName.isEmpty then .ok none
  else if isName nsName then .ok (some nsName)
  else .error s!"bad namespace `{nsName}`: not a valid Cedar name"

/-- The namespace `k` of the fragment. -/
def getNs (f : Fragment) (k : Option String) : Option NamespaceDef := f.lookup k

/-- The fragment with the namespace `k` replaced by `nd`. -/
def setNs (f : Fragment) (k : Option String) (nd : NamespaceDef) : Fragment :=
  f.map fun (k', nd') => if k' == k then (k', nd) else (k', nd')

/-- The fragment with the action `id` of the namespace `k` replaced by `a`. -/
def setAction (f : Fragment) (k : Option String) (id : String) (a : ActionDef) : Fragment :=
  match getNs f k with
  | some nd => setNs f k { nd with actions := insertKey id a nd.actions }
  | none => f

/-- The action `id` of the namespace `k`. -/
def actionAt (f : Fragment) (k : Option String) (id : String) : Option ActionDef :=
  (getNs f k).bind (·.actions.lookup id)

/-- The context type of the action `id` of the namespace `k`, when it applies to requests. -/
def contextAt (f : Fragment) (k : Option String) (id : String) : Option SchemaType :=
  (actionAt f k id).bind fun a => a.appliesTo.map (·.context)

/-- The annotation `key`'s value, when the annotation is present. -/
def annotationValue (anns : Annotations) (key : String) : Option (Option String) :=
  (anns.find? (·.1 == key)).map (·.2)

end Dogwood.Frontend.Augment
