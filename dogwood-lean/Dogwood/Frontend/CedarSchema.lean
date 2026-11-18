import Dogwood.Frontend.Syntax

/-!
# A model of Cedar's schema fragment

The action schema reaches the frontend as Cedar parses a `.cedarschema` text:
`json_schema::Fragment<RawName>` of `cedar-policy-core`, the lossless form of Cedar's JSON
schema format, with every name as written (possibly unqualified, possibly a common type).
Event-schema derivation reads it, cedarify resolves action scopes against it, and schema
augmentation edits it; the augmented fragment is then compiled by Cedar
(`Cedar.Validation.Schema` is the compiled form, cedar-lean's).

`Fragment` is a list of namespaces in the fragment's own order: the order of Cedar's `Name`,
which compares the **basename first, then the namespace path**, with the root namespace (`none`)
first (`nameLe`). Within a namespace, every map is in key order. Source locations are dropped.
-/

namespace Dogwood.Frontend.CedarSchema

/-- Annotations, as `(key, value)` pairs in key order; `none` for `@key` without a value. -/
abbrev Annotations := List (String × Option String)

mutual

/-- A type of the JSON schema format (Cedar `json_schema::Type` and `TypeVariant`). -/
inductive SchemaType where
  /-- `{"type": "N"}`: a reference that must resolve to a common type. -/
  | commonRef (name : String)
  | string
  | long
  | boolean
  | set (element : SchemaType)
  | record (attributes : List (String × AttrType)) (additionalAttributes : Bool)
  | entity (name : String)
  /-- A reference that may resolve to an entity type or a common type. -/
  | entityOrCommon (name : String)
  | extension (name : String)

/-- A record attribute's type (Cedar `TypeOfAttribute`). -/
structure AttrType where
  ty : SchemaType
  required : Bool
  annotations : Annotations

end

deriving instance Repr, BEq for SchemaType, AttrType

instance : Inhabited SchemaType := ⟨.string⟩

/-- A common type declaration. -/
structure CommonType where
  ty : SchemaType
  annotations : Annotations
deriving Repr, BEq, Inhabited

/-- What an entity type declares (Cedar `EntityTypeKind`). -/
inductive EntityTypeKind where
  | standard (memberOfTypes : List String) (shape : SchemaType) (tags : Option SchemaType)
  | «enum» (choices : List String)
deriving Repr, BEq, Inhabited

/-- An entity type declaration. An `external` one (Cedar 4.14, RFC 116) is only declared here,
to be defined in another schema fragment: its kind is `standard`, with its `memberOfTypes` and no
attributes or tags, which Cedar leaves unknown rather than empty. -/
structure EntityTypeDef where
  kind : EntityTypeKind
  external : Bool := false
  annotations : Annotations
deriving Repr, BEq, Inhabited

/-- An action a declaration is a member of: its id, and its entity type when given. -/
structure ActionUid where
  id : String
  ty : Option String
deriving Repr, DecidableEq, BEq, Inhabited

/-- The `appliesTo` of an action. -/
structure ApplySpec where
  principalTypes : List String
  resourceTypes : List String
  context : SchemaType
deriving Repr, BEq, Inhabited

/-- An action declaration (Cedar `ActionType`). `attributes` is the (deprecated) action
attribute map as compact JSON text. An `external` action (Cedar 4.14, RFC 116) declares only its
parents: it has no `appliesTo`. -/
structure ActionDef where
  attributes : Option String
  appliesTo : Option ApplySpec
  memberOf : Option (List ActionUid)
  external : Bool := false
  annotations : Annotations
deriving Repr, BEq, Inhabited

/-- A namespace's declarations, each map in key order. -/
structure NamespaceDef where
  commonTypes : List (String × CommonType)
  entityTypes : List (String × EntityTypeDef)
  actions : List (String × ActionDef)
  annotations : Annotations
deriving Repr, BEq, Inhabited

/-- A schema fragment: its namespaces, `none` for the root namespace, in Cedar's `Name` order
(`nameLe`). -/
abbrev Fragment := List (Option String × NamespaceDef)

/-- Cedar's order on names (`InternalName`'s derived order): the basename first, then the
namespace path, lexicographically. -/
def nameLe (a b : String) : Bool :=
  let split := fun (s : String) =>
    let segs := s.splitOn "::"
    (segs.getLast?.getD "", segs.dropLast)
  let (ia, pa) := split a
  let (ib, pb) := split b
  if ia < ib then true
  else if ib < ia then false
  else decide (pa ≤ pb)

/-- Cedar's order on namespace keys: the root namespace first, then `nameLe`. -/
def namespaceLe : Option String → Option String → Bool
  | none, _ => true
  | some _, none => false
  | some a, some b => nameLe a b

/-- The fragment with its namespaces in Cedar's order, as a `BTreeMap` of them iterates. -/
def Fragment.normalize (f : Fragment) : Fragment :=
  f.mergeSort fun x y => namespaceLe x.1 y.1

end Dogwood.Frontend.CedarSchema
