import Dogwood.Frontend.Types
import Dogwood.Frontend.Identity
import Dogwood.Conformance.JsonSize

/-!
# Cedar's JSON form of a schema fragment

The Cedar JSON schema of a fragment, as `cedar_policy::SchemaFragment::to_json_value` writes the
crate's augmented fragment, and its canonical text, which the policy-set version hash digests.

`fragmentJson` follows the `serde` attributes of `cedar-policy-core`'s `json_schema` module: a
namespace is keyed by its name, `""` for the root namespace; `commonTypes` and every
`annotations` map are written only when nonempty, `entityTypes` and `actions` always; an entity
type writes `memberOfTypes` only when nonempty, `shape` only when it is not the empty closed
record, `tags` only when declared, or its `enum` choices; an action writes `attributes`,
`appliesTo` and `memberOf` only when present, `appliesTo` always its `resourceTypes` and
`principalTypes` and its `context` only when it is not the empty closed record, and a parent
action its `type` only when written; a type is tagged by `"type"` (`String`, `Long`, `Boolean`,
`Set` with `element`, `Record` with `attributes` and, when open, `additionalAttributes`, `Entity`
and `EntityOrCommon` with `name`, `Extension` with `name`), a reference that must name a common
type is `{"type": <name>}`, and a record attribute writes `required` only when it is `false`. An
annotation written without a value is `null`. Arrays keep the fragment's order; the order of an
object's keys is immaterial (`Lean.Json` keeps them sorted).

`canonicalJson` is the crate's `canonical_json` (`identity.rs`): compact text, each object's keys
in sorted order, strings quoted as `serde_json` quotes them. `versionHash` is the crate's
`version_hash`: SHA-256 over a version tag, the sorted `(policy id, revision)` pairs, the
canonical augmented schema, the sorted decision kinds and the partition keys' field paths.
-/

namespace Dogwood.Frontend.SchemaJson

open Lean (Json JsonNumber)
open CedarSchema
open Dogwood.Conformance (sizeOf_lt_of_mem_arr sizeOf_lt_of_mem_toList)

/-! ## The JSON schema of a fragment -/

/-- An annotation map: each key with its value, `null` for an annotation without one. -/
def annotationsJson (a : Annotations) : Json :=
  Json.mkObj (a.map fun (k, v) => (k, match v with
    | some s => Json.str s
    | none => Json.null))

/-- `fields`, followed by `annotations` when there are any (`skip_serializing_if =
"Annotations::is_empty"`). -/
def withAnnotations (fields : List (String × Json)) (a : Annotations) : List (String × Json) :=
  if a.isEmpty then fields else fields ++ [("annotations", annotationsJson a)]

/-- The empty closed record, which Cedar does not write as a `shape` or a `context`
(`AttributesOrContext::is_empty_record`). -/
def isEmptyRecord : SchemaType → Bool
  | .record [] false => true
  | _ => false

/-- An array of strings. -/
def strings (xs : List String) : Json := Json.arr (xs.map Json.str).toArray

mutual

/-- The fields of a type's object (Cedar `Type`, flattened into its container). -/
def typeFields : SchemaType → List (String × Json)
  | .commonRef n => [("type", Json.str n)]
  | .string => [("type", Json.str "String")]
  | .long => [("type", Json.str "Long")]
  | .boolean => [("type", Json.str "Boolean")]
  | .set t => [("type", Json.str "Set"), ("element", Json.mkObj (typeFields t))]
  | .record attrs add =>
    [("type", Json.str "Record"), ("attributes", Json.mkObj (attrsJson attrs))] ++
      (if add then [("additionalAttributes", Json.bool true)] else [])
  | .entity n => [("type", Json.str "Entity"), ("name", Json.str n)]
  | .entityOrCommon n => [("type", Json.str "EntityOrCommon"), ("name", Json.str n)]
  | .extension n => [("type", Json.str "Extension"), ("name", Json.str n)]

/-- A record's attributes (Cedar `TypeOfAttribute`): the type's fields, the annotations, and
`required` when it is `false`. -/
def attrsJson : List (String × AttrType) → List (String × Json)
  | [] => []
  | (k, ⟨t, req, anns⟩) :: rest =>
    (k, Json.mkObj (withAnnotations (typeFields t) anns ++
      (if req then [] else [("required", Json.bool false)]))) :: attrsJson rest

end

/-- A type as a JSON object. -/
def typeJson (t : SchemaType) : Json := Json.mkObj (typeFields t)

/-- A common type declaration. -/
def commonTypeJson (c : CommonType) : Json := Json.mkObj (withAnnotations (typeFields c.ty) c.annotations)

/-- `"external": true` for a declaration Cedar 4.14 marks `external`; nothing otherwise. -/
def external (b : Bool) : List (String × Json) := if b then [("external", Json.bool true)] else []

/-- An entity type declaration (Cedar `EntityType`, its `EntityTypeKind` flattened). -/
def entityTypeJson (e : EntityTypeDef) : Json :=
  let kind := match e.kind with
    | .standard memberOf shape tags =>
      (if memberOf.isEmpty then [] else [("memberOfTypes", strings memberOf)]) ++
      (if isEmptyRecord shape then [] else [("shape", typeJson shape)]) ++
      (match tags with
        | some t => [("tags", typeJson t)]
        | none => [])
    | .enum choices => [("enum", strings choices)]
  Json.mkObj (withAnnotations (kind ++ external e.external) e.annotations)

/-- An action a declaration is a member of (Cedar `ActionEntityUID`). -/
def actionUidJson (u : ActionUid) : Json :=
  Json.mkObj ([("id", Json.str u.id)] ++ match u.ty with
    | some t => [("type", Json.str t)]
    | none => [])

/-- An action's `appliesTo` (Cedar `ApplySpec`). -/
def applySpecJson (s : ApplySpec) : Json :=
  Json.mkObj ([("resourceTypes", strings s.resourceTypes), ("principalTypes", strings s.principalTypes)] ++
    if isEmptyRecord s.context then [] else [("context", typeJson s.context)])

/-- The deprecated attributes of an action, which the fragment keeps as compact JSON text. -/
def attributesJson (text : String) : Json := (Json.parse text).toOption.getD (Json.str text)

/-- An action declaration (Cedar `ActionType`). -/
def actionJson (a : ActionDef) : Json :=
  Json.mkObj (withAnnotations (
    (match a.attributes with
      | some t => [("attributes", attributesJson t)]
      | none => []) ++
    (match a.appliesTo with
      | some s => [("appliesTo", applySpecJson s)]
      | none => []) ++
    (match a.memberOf with
      | some ms => [("memberOf", Json.arr (ms.map actionUidJson).toArray)]
      | none => []) ++
    external a.external) a.annotations)

/-- A namespace's declarations (Cedar `NamespaceDefinition`). -/
def namespaceJson (n : NamespaceDef) : Json :=
  Json.mkObj (withAnnotations (
    (if n.commonTypes.isEmpty then []
     else [("commonTypes", Json.mkObj (n.commonTypes.map fun (k, c) => (k, commonTypeJson c)))]) ++
    [("entityTypes", Json.mkObj (n.entityTypes.map fun (k, e) => (k, entityTypeJson e))),
     ("actions", Json.mkObj (n.actions.map fun (k, a) => (k, actionJson a)))]) n.annotations)

/-- The Cedar JSON schema of a fragment (Cedar `Fragment`'s `Serialize`): each namespace by its
name, the root namespace as `""`. -/
def fragmentJson (f : Fragment) : Json :=
  Json.mkObj (f.map fun (ns, d) => (ns.getD "", namespaceJson d))

/-! ## Canonical JSON text -/

/-- A number as `serde_json` displays it: an integer in decimal. A JSON number with a fraction
cannot occur in a schema (Cedar has no floating-point values); it is written as Lean writes it. -/
def numberText (n : JsonNumber) : String :=
  if n.exponent == 0 then toString n.mantissa else toString n

/-- The order in which the crate sorts an object's keys (`BTreeMap<&String, _>`): byte order of
the UTF-8 encoding, which is the order of code points, Lean's `<` on strings. -/
def keyLe (a b : String × String) : Bool := decide (a.1 ≤ b.1)

/-- Compact JSON text with every object's keys sorted (crate `canonical_json`). -/
def canonicalJson (j : Json) : String :=
  match j with
  | .null => "null"
  | .bool b => toString b
  | .num n => numberText n
  | .str s => RuleIdentity.q s
  | .arr a => "[" ++ ",".intercalate (a.attach.toList.map fun ⟨x, _⟩ => canonicalJson x) ++ "]"
  | .obj kvs =>
    let items := kvs.toList.attach.map fun ⟨(k, v), _⟩ => (k, canonicalJson v)
    "{" ++ ",".intercalate ((items.mergeSort keyLe).map fun (k, t) => RuleIdentity.q k ++ ":" ++ t) ++ "}"
termination_by sizeOf j
decreasing_by
  · exact sizeOf_lt_of_mem_arr ‹_›
  · exact sizeOf_lt_of_mem_toList ‹_›

/-! ## The policy-set version hash -/

/-- The version tag of a policy-set version hash (crate `VERSION_TAG`). -/
def versionTag : String := "dogwood-policy-set-version/1"

/-- The order of `(policy id, revision)` pairs: by id, then by revision (Rust's tuple order). -/
def pairLe (a b : String × String) : Bool :=
  decide (a.1 < b.1) || (a.1 == b.1 && decide (a.2 ≤ b.2))

/-- The decision kinds as a `BTreeSet` iterates them: sorted, without duplicates. -/
def sortedKinds (kinds : List String) : List String :=
  (kinds.mergeSort fun a b => decide (a ≤ b)).eraseDups

/-- The text the version hash digests (crate `version_hash`): the tag; one line `policy "<id>"
<revision>` per rule, sorted; `schema <canonical JSON>`, or `null` without a schema; one line
`decision-kind "<kind>"` per decision kind, sorted; one line `partition-key <path>` per
partition key, in order. -/
def versionText (idsAndRevisions : List (String × String)) (schema : Option Json)
    (decisionKinds : List String) (partitionKeys : List Pin) : String :=
  versionTag ++ "\n" ++
    String.join ((idsAndRevisions.mergeSort pairLe).map fun (id, rev) =>
      "policy " ++ RuleIdentity.q id ++ " " ++ rev ++ "\n") ++
    "schema " ++ ((schema.map canonicalJson).getD "null") ++ "\n" ++
    String.join ((sortedKinds decisionKinds).map fun k => "decision-kind " ++ RuleIdentity.q k ++ "\n") ++
    String.join (partitionKeys.map fun p => "partition-key " ++ RuleIdentity.qpath p.fieldPath ++ "\n")

/-- The policy-set version hash (crate `version_hash`): SHA-256, in lowercase hexadecimal, of
`versionText`. -/
def versionHash (idsAndRevisions : List (String × String)) (schema : Option Json)
    (decisionKinds : List String) (partitionKeys : List Pin) : String :=
  Sha256.hex (versionText idsAndRevisions schema decisionKinds partitionKeys)

end Dogwood.Frontend.SchemaJson
