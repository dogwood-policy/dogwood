import Dogwood.Frontend.Validate.Provider
import Dogwood.Frontend.Resolve

/-!
# The Cedar side of validation: Cedar's validator, the context reads, and the leaves' facts

* **Cedar's validator** on the lowered rules against the augmented schema (crate
  `validate_cedar_side`): the crate runs Cedar's Rust validator in strict mode and reports an
  impossible policy as an error; this port runs cedar-lean's validator, which does both.
* **An incomplete schema** (Cedar 4.14): when the augmented schema declares a name `external`,
  Cedar's validator validates no policy, and reports each, as `cedar` findings.
* **The schema's well-formedness** (crate `validate_schema`): an enumerated entity type that is
  an ancestor of an entity type, which Cedar 4.14 and cedar-lean allow and the specification's
  validity rejects (`Schema.standardAncestors`), is a finding of code `schema`, one per such
  type.
* **Context reads** (crate `cedarify::to_ast`, `note_context_read`, reported by `validate_impl`):
  the Cedar part may not read the request context whole, in a policy set with a leaf, nor read an
  attribute of a name lowering reserves (`isHoistedName`). The crate records the reads when it
  lowers the authored rules (`Lowered.contextReads`, which `Cedarify.authoredReads` computes); this
  port also reads them off the lowered rules, where the only reads of reserved names lowering
  itself makes are `context.<id>` of a temporal leaf and `context.providers.<id>` of a provider
  leaf.
* **The leaves' facts** (crate `temporal_leaf_facts`, `facts::leaf_facts`): the `has` tests the
  lowered rule makes before Cedar evaluates `context.<id>`, read off the rule's condition with the
  rules of `Expr.facts`; a leaf read twice keeps the facts both positions establish.
-/

namespace Dogwood.Frontend.Validate

open Dogwood.Spec (Expr Policy Conditions)
open Dogwood.Spec.Temporal (Guard)
open Cedar.Spec (Attr)
open Cedar.Validation (CedarType QualifiedType)

/-- A finding of the crate's validator. -/
def finding (code message : String) (warning : Bool := false) : Conformance.CrateFinding :=
  { code, message, warning }

/-! ## Cedar's validator -/

/-- The lowered rules, as Cedar policies. -/
def cedarPolicies (l : Lowered) : Cedar.Spec.Policies :=
  (Dogwood.Spec.Policies.lowerFrom 0 l.policies).1

mutual

/-- A Cedar type as Cedar's Rust validator prints it (`validator::types::Type`'s `Display`). -/
def cedarTypeText : CedarType → String
  | .bool .anyBool => "Bool"
  | .bool .tt => "__cedar::internal::True"
  | .bool .ff => "__cedar::internal::False"
  | .int => "Long"
  | .string => "String"
  | .entity ety => nameText ety
  | .set t => "Set<" ++ cedarTypeText t ++ ">"
  | .record rty => "{" ++ String.join (cedarAttrsText rty.toList) ++ "}"
  | .ext .decimal => "decimal"
  | .ext .ipAddr => "ipaddr"
  | .ext .datetime => "datetime"
  | .ext .duration => "duration"

def cedarAttrsText : List (Attr × QualifiedType) → List String
  | [] => []
  | (a, .required t) :: rest => (a ++ ": " ++ cedarTypeText t ++ ",") :: cedarAttrsText rest
  | (a, .optional t) :: rest => (a ++ "?: " ++ cedarTypeText t ++ ",") :: cedarAttrsText rest

end

/-- The position of a type's kind in the order of Cedar's Rust validator's `Type`. -/
def cedarTypeRank : CedarType → Nat
  | .bool _ => 1 | .int => 2 | .string => 3 | .entity _ => 4 | .set _ => 5 | .record _ => 6
  | .ext _ => 7

/-- Items joined as Cedar joins them (`join_with_conjunction`): `a and b`, `a, b, and c`. -/
def joinWithAnd : List String → String
  | [] => ""
  | [a] => a
  | [a, b] => a ++ " and " ++ b
  | items => ", ".intercalate items.dropLast ++ ", and " ++ items.getLast!

/-- `the types … are not compatible` (Cedar's `IncompatibleTypes`), the types in the order of
Cedar's types. -/
def incompatibleText (tys : List CedarType) : String :=
  let sorted := tys.mergeSort fun a b =>
    cedarTypeRank a < cedarTypeRank b ||
      (cedarTypeRank a == cedarTypeRank b && decide (cedarTypeText a ≤ cedarTypeText b))
  "the types " ++ joinWithAnd (sorted.map cedarTypeText).eraseDups ++ " are not compatible"

/-- Whether no request environment of the schema admits the scope of the rule `pid`: in each,
its scope (with the action substituted) has the type `false`. -/
def noApplicableAction (l : Lowered) (pid : String) : Bool :=
  match (cedarPolicies l).find? (·.id == pid) with
  | none => false
  | some p =>
    let scope : Cedar.Spec.Expr :=
      .and p.principalScope.toExpr (.and p.actionScope.toExpr p.resourceScope.toExpr)
    l.schema.environments.all fun env =>
      match Cedar.Validation.typeOf (Cedar.Validation.substituteAction env.reqty.action scope) ∅ env with
      | .ok (tx, _) => tx.typeOf == .bool .ff
      | .error _ => false

/-- A character of a name in a message, around which a provider enum's exported name is not a
whole name (crate `declared_enum_names`). -/
def isEnumNameChar (c : Char) : Bool := c.isAlphanum || c == '_' || c == ':'

/-- `text` with each whole occurrence of the name `ex` replaced by `de` (crate
`declared_enum_names`, one pair): `before` is the character before the rest, since the last
occurrence; `::` may follow an occurrence, a name character may not. -/
def replaceName (ex de : List Char) (before : Option Char) : List Char → List Char
  | [] => []
  | c :: cs =>
    if h : ex ≠ [] ∧ ex.isPrefixOf (c :: cs) = true then
      let afterOk := match (c :: cs).drop ex.length with
        | [] => true
        | ':' :: ':' :: _ => true
        | a :: _ => !isEnumNameChar a
      let beforeOk := match before with
        | none => true
        | some b => !isEnumNameChar b
      have : 0 < ex.length := List.length_pos_iff.mpr h.1
      (if beforeOk && afterOk then de else ex) ++ replaceName ex de none ((c :: cs).drop ex.length)
    else c :: replaceName ex de (some c) cs
termination_by rest => rest.length

/-- A message with each exported name of a used provider enum replaced by its declared name, the
longest first (crate `validate::declared_enum_names`), as the crate reports Cedar's messages. -/
def declaredEnumNames (names : List (String × String)) (text : String) : String :=
  let pairs := names.mergeSort fun a b => decide (b.2.length ≤ a.2.length)
  pairs.foldl (init := text) fun out (de, ex) =>
    String.ofList (replaceName ex.toList de.toList none out.toList)

/-- The entity literals of a Cedar expression, in order. -/
def entityLiterals : Cedar.Spec.Expr → List Cedar.Spec.EntityUID
  | .lit (.entityUID uid) => [uid]
  | .lit _ | .var _ => []
  | .ite x₁ x₂ x₃ => entityLiterals x₁ ++ entityLiterals x₂ ++ entityLiterals x₃
  | .and x₁ x₂ | .or x₁ x₂ | .binaryApp _ x₁ x₂ => entityLiterals x₁ ++ entityLiterals x₂
  | .unaryApp _ x₁ | .getAttr x₁ _ | .hasAttr x₁ _ | .extHasAttr x₁ _ _ => entityLiterals x₁
  | .set xs | .call _ xs =>
    xs.attach.flatMap fun x =>
      have _ := List.sizeOf_lt_of_mem x.property
      entityLiterals x.val
  | .record axs => axs.attach₂.flatMap fun x => entityLiterals x.val.snd

/-- The first entity literal of the rule `pid` of the enumerated entity type `ety` with an id the
type does not declare: the literal cedar-lean's `unknownEntity` is about, when it is one of an
enumerated type. -/
def invalidEnumLiteral (l : Lowered) (pid : String) (ety : Cedar.Spec.EntityType) :
    Option Cedar.Spec.EntityUID :=
  match (cedarPolicies l).find? (·.id == pid), l.schema.ets.find? ety with
  | some p, some (.enum eids) =>
    (entityLiterals p.toExpr).find? fun u => u.ty == ety && !eids.contains u.eid
  | _, _ => none

/-- The message of a finding of Cedar's validator: cedar-lean's first error, worded as Cedar's
Rust validator words an error of its kind (`validator::diagnostics`), with what cedar-lean's
error carries: incompatible types; an attribute not found, on an entity type or a record; an
unrecognized entity type, or an id an enumerated type does not declare; an unexpected type (the
type cedar-lean saw, not the one expected, which its error does not carry); an empty set; an
impossible policy. Other errors keep cedar-lean's text. -/
def cedarMessage (l : Lowered) : Cedar.Validation.ValidationError → String
  | .impossiblePolicy pid =>
      s!"for policy `{Escape.strEscapeDebug pid}`, policy is impossible: the policy expression evaluates to false for all valid requests"
  | .typeError _ (.lubErr t₁ t₂) => incompatibleText [t₁, t₂]
  | .typeError _ (.incompatibleSetTypes tys) => incompatibleText tys
  | .typeError pid (.attrNotFound (.entity ety) a) =>
    s!"for policy `{Escape.strEscapeDebug pid}`, attribute `{a}` on entity type `{nameText ety}` not found"
  | .typeError pid (.attrNotFound _ a) =>
    s!"for policy `{Escape.strEscapeDebug pid}`, attribute `{a}` not found"
  | .typeError pid (.unknownEntity ety) =>
    match invalidEnumLiteral l pid ety with
    | some u =>
      let eid := Escape.strEscapeDebug u.eid
      s!"for policy `{Escape.strEscapeDebug pid}`: entity `{nameText u.ty}::\"{eid}\"` is of an enumerated entity type, but `\"{eid}\"` is not declared as a valid eid"
    | none => s!"for policy `{Escape.strEscapeDebug pid}`, unrecognized entity type `{nameText ety}`"
  | .typeError pid (.unexpectedType ty) =>
    s!"for policy `{Escape.strEscapeDebug pid}`, unexpected type: saw {cedarTypeText ty}"
  | .typeError pid .emptySetErr =>
    s!"for policy `{Escape.strEscapeDebug pid}`, empty set literals are forbidden in policies"
  | e => toString e

/-- The messages of the findings of Cedar's validator for cedar-lean's error: its message
(`cedarMessage`), after the error Cedar's Rust validator also reports for an impossible policy
when no request environment admits its scope (`InvalidActionApplication`), each with the
provider enums by their declared names, as the crate reports Cedar's messages. -/
def cedarMessages (l : Lowered) (e : Cedar.Validation.ValidationError) : String × List String :=
  let dn := declaredEnumNames l.enumNames
  match e with
  | .impossiblePolicy pid =>
    if noApplicableAction l pid then
      (dn s!"for policy `{Escape.strEscapeDebug pid}`, unable to find an applicable action given the policy scope constraints",
        [dn (cedarMessage l e)])
    else (dn (cedarMessage l e), [])
  | _ => (dn (cedarMessage l e), [])

/-! ## An incomplete schema -/

/-- Cedar's order on entities (`EntityUID`'s derived order): the type, in Cedar's order on names,
then the id. -/
def uidLe (a b : Cedar.Spec.EntityUID) : Bool :=
  if nameText a.ty == nameText b.ty then decide (a.eid ≤ b.eid)
  else CedarSchema.nameLe (nameText a.ty) (nameText b.ty)

/-- The names the augmented schema declares `external` (Cedar 4.14, RFC 116), as Cedar's
`IncompleteSchemaError` lists them: the entity types in name order, then the actions in their
order, each as Cedar prints it. -/
def incompleteNames (l : Lowered) : List String :=
  ((CedarSchema.Resolve.externalEntityTypes l.augmentedSchema).mergeSort fun a b =>
      CedarSchema.nameLe (nameText a) (nameText b)).map nameText ++
  ((CedarSchema.Resolve.externalActions l.augmentedSchema).mergeSort uidLe).map fun u =>
    nameText u.ty ++ "::\"" ++ Escape.strEscapeDebug u.eid ++ "\""

/-- Cedar's message for a policy it does not validate against an incomplete schema
(`ValidationError::IncompleteSchema`). -/
def incompleteMessage (pid : String) (names : List String) : String :=
  s!"for policy `{Escape.strEscapeDebug pid}`, schema is incomplete: " ++
    joinWithAnd (names.map fun n => "`" ++ n ++ "`") ++
    (if names.length == 1 then " is" else " are") ++ " declared `external` but not defined"

/-- Cedar's findings when the augmented schema declares a name `external`: Cedar's validator
validates no policy against an incomplete schema, and reports each, in rule order. -/
def incompleteFindings (l : Lowered) : List Conformance.CrateFinding :=
  l.policies.map fun p =>
    finding "cedar" (declaredEnumNames l.enumNames (incompleteMessage p.id (incompleteNames l)))

/-- Cedar's findings on the lowered rules. -/
def cedarFindings (l : Lowered) : List Conformance.CrateFinding :=
  if l.policies.isEmpty then []
  else if (incompleteNames l).isEmpty then
    match Cedar.Validation.validate (cedarPolicies l) l.schema with
    | .ok () => []
    | .error e =>
      finding "cedar" (cedarMessages l e).1 :: (cedarMessages l e).2.map (finding "cedar" ·)
  else incompleteFindings l

/-! ## The schema's well-formedness -/

/-- The entity types of the schema whose declared ancestors include `E`. -/
def descendantsOf (S : Cedar.Validation.Schema) (E : Cedar.Spec.EntityType) : List Cedar.Spec.EntityType :=
  S.ets.toList.filterMap fun (d, e) =>
    match e with
    | .standard se => if se.ancestors.contains E then some d else none
    | .enum _ => none

/-- The enumerated entity types that are an ancestor of an entity type, with their descendants,
in name order. -/
def enumAncestors (S : Cedar.Validation.Schema) : List (Cedar.Spec.EntityType × List Cedar.Spec.EntityType) :=
  (S.ets.toList.filterMap fun (E, e) =>
    match e with
    | .enum _ => if (descendantsOf S E).isEmpty then none else some (E, descendantsOf S E)
    | .standard _ => none).mergeSort fun a b => decide (nameText a.1 ≤ nameText b.1)

/-- The schema findings (crate `validate_schema`): one per enumerated entity type that is an
ancestor. -/
def schemaFindings (l : Lowered) : List Conformance.CrateFinding :=
  (enumAncestors l.schema).map fun (E, ds) =>
    let names := (ds.map fun d => "`" ++ nameText d ++ "`").mergeSort fun a b => decide (a ≤ b)
    finding "schema" (s!"the enumerated entity type `{nameText E}` is an ancestor of " ++
      ", ".intercalate names ++ "; Dogwood requires every ancestor of an entity type to be a " ++
      "standard entity type, as the formal specification's schema well-formedness does, though " ++
      "Cedar allows an enumerated one")

/-! ## Context reads -/

/-- The ids of the leaves lowering reads: `context.<id>` of a temporal leaf (`temporal`),
`context.providers.<id>` of a provider leaf (`providers`). -/
structure Generated where
  temporal : List String
  providers : List String

def wholeRead : String :=
  "the rule reads the request context whole, not through one of its attributes; lowering adds the values of the policy set's temporal and provider leaves to the context, so read the attributes the rule needs (`context.<attr>`) instead"

def reservedRead (a : String) : String :=
  s!"the rule reads the request context attribute `{a}`, a name lowering reserves for the value of a temporal or provider leaf; a request cannot supply it, so rename the attribute"

mutual

/-- The reads of the request context a lowered rule makes that lowering does not preserve: whole
(`true`), or of a reserved name (`false`, with the name). -/
def contextReads (g : Generated) : Expr → List (Bool × String)
  | .var v => if v == .context then [(true, "")] else []
  | .getAttr (.getAttr (.var .context) "providers") pid =>
    if g.providers.contains pid then [] else [(false, "providers")]
  | .getAttr x a =>
    match x with
    | .var .context =>
      if isHoistedName a && !(g.temporal.contains a) then [(false, a)] else []
    | _ => contextReads g x
  | .hasAttr x a | .extHasAttr x a _ =>
    match x with
    | .var .context => if isHoistedName a then [(false, a)] else []
    | _ => contextReads g x
  | .lit _ | .temporal _ | .provider _ => []
  | .unaryApp _ x => contextReads g x
  | .ite a b c => contextReads g a ++ contextReads g b ++ contextReads g c
  | .and a b | .or a b | .binaryApp _ a b => contextReads g a ++ contextReads g b
  | .set xs | .call _ xs => contextReadsList g xs
  | .record axs => contextReadsRecord g axs

def contextReadsList (g : Generated) : List Expr → List (Bool × String)
  | [] => []
  | x :: xs => contextReads g x ++ contextReadsList g xs

def contextReadsRecord (g : Generated) : List (Attr × Expr) → List (Bool × String)
  | [] => []
  | (_, x) :: axs => contextReads g x ++ contextReadsRecord g axs

end

/-- The reads of the lowered set's rules. -/
def loweredReads (l : Lowered) : List (Bool × String) :=
  let g : Generated := ⟨l.temporal.map (·.id), l.providers.map (·.id)⟩
  l.policies.flatMap fun p => Validate.contextReads g p.toExpr

/-- The reads lowering does not preserve, one finding each: those the crate recorded while it
lowered the authored rules (`Lowered.contextReads`), which include a read of a leaf's own name
that the lowered rules cannot tell from lowering's reference to the leaf, then each read of the
lowered rules that is not one of them. The crate reports the recorded reads only; a lowered rule
reads the request context as its authored rule does, so the second part is empty on a set the
crate lowers, and it is there so that the findings cover every read of the lowered rules, as the
specification's validity reads them. -/
def allReads (l : Lowered) : List (Bool × String) :=
  l.contextReads ++ (loweredReads l).filter fun r => !l.contextReads.contains r

/-- Whether the lowered set has a leaf. -/
def hasLeaves (l : Lowered) : Bool := !l.temporal.isEmpty || !l.providers.isEmpty

/-- The context-read findings (crate `validate_impl`): a whole read only when the set has a
leaf. -/
def contextFindings (l : Lowered) : List Conformance.CrateFinding :=
  (allReads l).filterMap fun (whole, a) =>
    if whole then (if hasLeaves l then some (finding "context" wholeRead) else none)
    else some (finding "context" (reservedRead a))

/-! ## The leaves' facts -/

mutual

/-- Each temporal leaf `context.<id>` an expression reads, with the facts established at its
position, given the facts `here` established before it (crate `facts::walk`). -/
def leafFactsW (isLeaf : String → Bool) (here : List Guard) : Expr → List (String × List Guard)
  | .getAttr x a =>
    match x with
    | .var .context => if isLeaf a then [(a, here)] else []
    | _ => leafFactsW isLeaf here x
  | .and a b => leafFactsW isLeaf here a ++ leafFactsW isLeaf (here ++ Expr.facts a) b
  | .ite c t e =>
    leafFactsW isLeaf here c ++ leafFactsW isLeaf (here ++ Expr.facts c) t ++ leafFactsW isLeaf here e
  | .or a b | .binaryApp _ a b => leafFactsW isLeaf here a ++ leafFactsW isLeaf here b
  | .unaryApp _ a | .hasAttr a _ | .extHasAttr a _ _ => leafFactsW isLeaf here a
  | .set xs | .call _ xs => leafFactsWList isLeaf here xs
  | .record axs => leafFactsWRecord isLeaf here axs
  | .lit _ | .var _ | .temporal _ | .provider _ => []

def leafFactsWList (isLeaf : String → Bool) (here : List Guard) : List Expr → List (String × List Guard)
  | [] => []
  | x :: xs => leafFactsW isLeaf here x ++ leafFactsWList isLeaf here xs

def leafFactsWRecord (isLeaf : String → Bool) (here : List Guard) :
    List (Attr × Expr) → List (String × List Guard)
  | [] => []
  | (_, x) :: axs => leafFactsW isLeaf here x ++ leafFactsWRecord isLeaf here axs

end

/-- Merge each leaf's positions: a leaf read at several positions keeps the facts common to all
(crate `facts::record`). -/
def mergeFacts (xs : List (String × List Guard)) : List (String × List Guard) :=
  xs.foldl (init := []) fun acc (id, here) =>
    match acc.lookup id with
    | some existing =>
      acc.map fun (k, v) => if k == id then (k, existing.filter (here.contains ·)) else (k, v)
    | none => acc ++ [(id, here)]

/-- The facts each temporal leaf's position establishes, by leaf id (crate
`temporal_leaf_facts`): read off each temporal rule's condition; a later rule's entry replaces an
earlier one's. -/
def loweredFacts (l : Lowered) : List (String × List Guard) :=
  let ids := l.temporal.map (·.id)
  (l.temporalRules.eraseDups.mergeSort (· ≤ ·)).foldl (init := []) fun acc k =>
    match l.policies[k]? with
    | some p =>
      let here := mergeFacts (leafFactsW (ids.contains ·) [] (Conditions.toExpr p.condition))
      (acc.filter fun (id, _) => !(here.any (·.1 == id))) ++ here
    | none => acc

end Dogwood.Frontend.Validate
