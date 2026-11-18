import Dogwood.Spec.Decision
import Dogwood.Spec.Temporal.Scopes
import Cedar.Validation.Validator
import Cedar.Validation.EnvironmentValidator

/-!
# Valid policy sets

`PolicySet.Valid P` is what validation requires of a policy set before an authorizer is built
with it. It has two parts.

**The Cedar part.** Lowering replaces each leaf of a rule by an attribute of the request
context: a temporal leaf by a `Bool` attribute, a provider leaf by an attribute of its declared
output type (`PolicySet.lowered`). The *augmented* schema adds each attribute, required, to the
context record type of the actions the leaf's rule can apply to: those its action scope admits
(`PolicySet.augmentedSchema`, `actionScopeAdmits`). Cedar's validator must accept
the lowered rules against the augmented schema (`Cedar.Validation.validate`), and the augmented
schema must be well-formed (`Cedar.Validation.Schema.validateWellFormed`), which Cedar's
soundness result assumes. The Cedar part needs no typing of its own. The crate augments the same
actions (`scope_target_actions`, `cedarify/schema_augment.rs`), which keeps the schema small, up
to two differences that change no verdict: it gives every action a provider rule reaches the whole
shared `providers` record, and it leaves out pure action groups, which have no request
environment.
Adding the attributes to more actions changes nothing: validation against any augmentation that
adds each leaf's attribute at least to the actions its rule's action scope admits, and only leaf
attributes, gives the same verdict, the schema that adds every attribute to every action
(`PolicySet.allAugmentedSchema`) included (`Dogwood.Thm.validate_covers_iff`,
`Dogwood.Thm.valid_iff_validAll`). The lowered rules evaluate as the Dogwood rules do, once the request context
holds the leaves' values
(`Dogwood.Thm.evaluate_lower`), provided that:

* the attribute names lowering gives the leaves are distinct, and no action's context declares
  one of them (`PolicySet.hoistedNames`);
* the Cedar part reads `context` only through attribute accesses and `has` tests of other
  attributes (`Expr.ReadsContext`), when the policy set has a leaf. A policy set without leaves
  is its own lowering, and its request context is the request's, so it may read `context`
  whole, as in Cedar.

**The temporal part.** Every temporal leaf of a rule is well-typed in every request environment
the rule's scope admits (`Formula.WellTyped`, `PolicySet.envsOf`), with the facts its position
in the rule establishes (`Expr.leafFacts`); it is safe (`Formula.IsSafe`); and every monitoring
scope of it varies with the timepoint (`Formula.MonitorsTime`). Every provider leaf names a
declared provider and declared output methods, each method taking the value the stage before it
produces (`Provider.Call.Declared`), and its arguments have their declared types in every
environment the rule admits (`Provider.Call.TypedIn`); an argument may read an optional
attribute without a `has` guard, since an absent argument is part of the provider contract.

The environments a rule admits are those of the action schema its scope can hold of: an action
its action scope admits, and principal and resource types its principal and resource scopes
admit. Under `principal in E`, those are `E`'s type and the types the schema lets be in it
(`scopeAdmitsType`).

The specification's attribute names (`leafAttr`) are its own; the crate's are
`policy_<i>__temporal_<k>` and `providers.<id>`. Only their meaning matters.

`PolicySet.validationFindings` decides validity, reporting what it finds by category
(`Dogwood.Thm.validationFindings_eq_nil_iff`).
-/

namespace Dogwood.Spec

open Cedar.Spec (Attr EntityType EntityUID)
open Cedar.Validation (CedarType Schema TypeEnv QualifiedType Qualified ActionSchemaEntry RecordType)
open Cedar.Data (Map)
open Temporal

/-! ## Lowering -/

/-- The context attribute that lowering gives the `k`-th leaf of a policy set. -/
def leafAttr (k : Nat) : Attr := "__dogwood_leaf_" ++ toString k

mutual

/-- Lower an expression whose first leaf is the `k`-th leaf of its policy set: each leaf becomes
the context attribute of its index. Returns the index after the expression's last leaf. -/
def Expr.lowerFrom : Nat → Expr → Cedar.Spec.Expr × Nat
  | k, .lit p => (.lit p, k)
  | k, .var v => (.var v, k)
  | k, .ite a b c =>
    let ra := Expr.lowerFrom k a
    let rb := Expr.lowerFrom ra.2 b
    let rc := Expr.lowerFrom rb.2 c
    (.ite ra.1 rb.1 rc.1, rc.2)
  | k, .and a b =>
    let ra := Expr.lowerFrom k a
    let rb := Expr.lowerFrom ra.2 b
    (.and ra.1 rb.1, rb.2)
  | k, .or a b =>
    let ra := Expr.lowerFrom k a
    let rb := Expr.lowerFrom ra.2 b
    (.or ra.1 rb.1, rb.2)
  | k, .unaryApp op a =>
    let ra := Expr.lowerFrom k a
    (.unaryApp op ra.1, ra.2)
  | k, .binaryApp op a b =>
    let ra := Expr.lowerFrom k a
    let rb := Expr.lowerFrom ra.2 b
    (.binaryApp op ra.1 rb.1, rb.2)
  | k, .getAttr a x =>
    let ra := Expr.lowerFrom k a
    (.getAttr ra.1 x, ra.2)
  | k, .hasAttr a x =>
    let ra := Expr.lowerFrom k a
    (.hasAttr ra.1 x, ra.2)
  | k, .extHasAttr a x xs =>
    let ra := Expr.lowerFrom k a
    (.extHasAttr ra.1 x xs, ra.2)
  | k, .set xs =>
    let r := Expr.lowerListFrom k xs
    (.set r.1, r.2)
  | k, .record axs =>
    let r := Expr.lowerRecordFrom k axs
    (.record r.1, r.2)
  | k, .call f xs =>
    let r := Expr.lowerListFrom k xs
    (.call f r.1, r.2)
  | k, .temporal _ => (.getAttr (.var .context) (leafAttr k), k + 1)
  | k, .provider _ => (.getAttr (.var .context) (leafAttr k), k + 1)

def Expr.lowerListFrom : Nat → List Expr → List Cedar.Spec.Expr × Nat
  | k, [] => ([], k)
  | k, x :: xs =>
    let r := Expr.lowerFrom k x
    let rs := Expr.lowerListFrom r.2 xs
    (r.1 :: rs.1, rs.2)

def Expr.lowerRecordFrom : Nat → List (Attr × Expr) → List (Attr × Cedar.Spec.Expr) × Nat
  | k, [] => ([], k)
  | k, (a, x) :: axs =>
    let r := Expr.lowerFrom k x
    let rs := Expr.lowerRecordFrom r.2 axs
    ((a, r.1) :: rs.1, rs.2)

end

/-- Lower a rule's conditions, from leaf index `k`. -/
def Conditions.lowerFrom : Nat → Conditions → Cedar.Spec.Conditions × Nat
  | k, [] => ([], k)
  | k, c :: cs =>
    let r := c.body.lowerFrom k
    let rs := Conditions.lowerFrom r.2 cs
    (⟨c.kind, r.1⟩ :: rs.1, rs.2)

/-- Lower a rule, from leaf index `k`: its scope is Cedar's already. -/
def Policy.lowerFrom (k : Nat) (p : Policy) : Cedar.Spec.Policy × Nat :=
  let r := Conditions.lowerFrom k p.condition
  ({ id := p.id, effect := p.effect, principalScope := p.principalScope,
     actionScope := p.actionScope, resourceScope := p.resourceScope, condition := r.1 }, r.2)

/-- Lower rules, numbering their leaves from `k` on. -/
def Policies.lowerFrom : Nat → Policies → Cedar.Spec.Policies × Nat
  | k, [] => ([], k)
  | k, p :: ps =>
    let r := p.lowerFrom k
    let rs := Policies.lowerFrom r.2 ps
    (r.1 :: rs.1, rs.2)

namespace PolicySet

variable (P : PolicySet)

/-- The policy set's rules, lowered to Cedar policies. -/
def lowered : Cedar.Spec.Policies := (Policies.lowerFrom 0 P.policies).1

/-- The leaves of the policy set's rules, in order: the `k`-th is lowered to `leafAttr k`. -/
def leafList : List Leaf := P.policies.flatMap (·.toExpr.leaves)

/-- The attributes lowering adds to the request context. -/
def hoistedNames : List Attr := (List.range P.leafList.length).map leafAttr

/-- The type of a leaf's attribute: `Bool` for a temporal leaf, its declared output type for a
provider leaf. -/
def leafType? : Leaf → Option CedarType
  | .inl _ => some (.bool .anyBool)
  | .inr c => c.outputType? P.providerDecls

/-- The attributes lowering adds to the request context, with their types, in the order of
`leafList`; `none` when a provider leaf has no declared output type. Each is added to the context
record types of the actions its leaf's rule can apply to (`PolicySet.augmentedSchema`). -/
def hoistedTypes? : Option (List (Attr × QualifiedType)) :=
  P.leafList.zipIdx.mapM fun (l, k) => (P.leafType? l).map fun ty => (leafAttr k, .required ty)

end PolicySet

/-- The schema `A` with the attributes `H` added to every action's context record type. -/
def Schema.augment (A : Schema) (H : List (Attr × QualifiedType)) : Schema where
  ets := A.ets
  acts := A.acts.mapOnValues fun entry =>
    { entry with context := Map.make (entry.context.toList ++ H) }

/-- The schema `A` with the attributes `Hsel uid` added to the context record type of each action
`uid`. -/
def Schema.augmentWith (A : Schema) (Hsel : EntityUID → List (Attr × QualifiedType)) : Schema where
  ets := A.ets
  acts := Map.mk (A.acts.toList.map fun (uid, entry) =>
    (uid, { entry with context := Map.make (entry.context.toList ++ Hsel uid) }))

/-- **Every ancestor is a standard entity type**, in each request environment of the schema: no
entity type has an enumerated entity type among its ancestors. Cedar 4.11's well-formedness
required it, checked in each request environment, as this does; Cedar 4.14 allows an enumerated
ancestor, and so does cedar-lean's `validateWellFormed` from release `v4.14.0` on. Dogwood keeps
the rule. -/
def _root_.Cedar.Validation.Schema.standardAncestors (A : Schema) : Bool :=
  A.environments.all fun env => env.ets.toList.all fun (_, e) =>
    e.ancestors.toList.all fun anc => (env.ets.find? anc).all (·.isStandard)

/-! ## The environments a rule admits -/

/-- The schema lets an entity of type `ety` be in an entity of type `ety'`: the two types are the
same, `ety'` is among the declared ancestors of the entity type `ety`, or an action of type `ety`
has an ancestor of type `ety'`. This is Cedar's `TypeEnv.descendentOf`, by which its typechecker
types `in`, without the assumption of a well-formed schema that no action has an entity type. -/
def Schema.memberOfType (A : Schema) (ety ety' : EntityType) : Bool :=
  ety == ety' ||
    (match A.ets.find? ety with
      | some entry => entry.ancestors.contains ety'
      | none => false) ||
    A.acts.maybeDescendentOf ety ety'

/-- The scope can hold of a principal or resource of type `ety`. A membership constraint
`in E` can hold of an entity of `E`'s type, or of a type the schema lets be in `E`'s type: on an
entity store that conforms to the schema, no other entity is in `E` (`scopeAdmitsType_of_eval`).
Cedar's typechecker narrows the same way, and so does the crate. -/
def scopeAdmitsType (A : Schema) : Cedar.Spec.Scope → EntityType → Bool
  | .any, _ => true
  | .mem uid, ety => Schema.memberOfType A ety uid.ty
  | .eq uid, ety => uid.ty == ety
  | .is ety', ety | .isMem ety' _, ety => ety' == ety

/-- The action scope can hold of the action `act`. -/
def actionScopeAdmits (A : Schema) (act : EntityUID) : Cedar.Spec.ActionScope → Bool
  | .actionScope .any => true
  | .actionScope (.eq uid) => act == uid
  | .actionScope (.mem uid) => A.acts.descendentOf act uid
  | .actionScope (.is ety) => act.ty == ety
  | .actionScope (.isMem ety uid) => act.ty == ety && A.acts.descendentOf act uid
  | .actionInAny ls => ls.any (A.acts.descendentOf act ·)

/-! ## The augmented schema -/

/-- The action scope of the rule each leaf belongs to, in the order of `PolicySet.leafList`. -/
def PolicySet.leafScopes (P : PolicySet) : List Cedar.Spec.ActionScope :=
  P.policies.flatMap fun p => p.toExpr.leaves.map fun _ => p.actionScope

/-- Of the attributes `H`, given in the order of `PolicySet.leafList`, those that are added to the
context of the action `uid`: the attributes of the leaves whose rule's action scope admits `uid`.
-/
def PolicySet.targetedAt (P : PolicySet) (H : List (Attr × QualifiedType)) (uid : EntityUID) :
    List (Attr × QualifiedType) :=
  ((H.zip P.leafScopes).filter fun (_, s) => actionScopeAdmits P.actionSchema uid s).map Prod.fst

/-- The action schema with each leaf's attribute of `H` added to the contexts of the actions its
rule's action scope admits, and to no other. -/
def PolicySet.selectiveAugment (P : PolicySet) (H : List (Attr × QualifiedType)) : Schema :=
  Schema.augmentWith P.actionSchema (P.targetedAt H)

/-- **The augmented schema** against which Cedar's validator checks the lowered rules: each
leaf's attribute is added to the context of the actions its rule's action scope admits. This is
the crate's augmentation (`scope_target_actions`), up to the shared provider record and pure action
groups (see the module documentation). -/
def PolicySet.augmentedSchema (P : PolicySet) : Schema :=
  P.selectiveAugment (P.hoistedTypes?.getD [])

/-- The schema with every leaf's attribute added to every action's context. Validation against it
gives the same verdict as against `PolicySet.augmentedSchema`, or against any augmentation in
between (`Dogwood.Thm.valid_iff_validAll`, `Dogwood.Thm.valid_iff_covers`); the proofs
about a valid set's decisions use it, since the request context of a decision holds every leaf's
value. -/
def PolicySet.allAugmentedSchema (P : PolicySet) : Schema :=
  Schema.augment P.actionSchema (P.hoistedTypes?.getD [])

/-- The rule's scope can hold of a request of the environment `env`. -/
def Policy.admits (A : Schema) (env : TypeEnv) (p : Policy) : Bool :=
  match p.principalScope, p.resourceScope with
  | .principalScope ps, .resourceScope rs =>
    scopeAdmitsType A ps env.reqty.principal &&
      actionScopeAdmits A env.reqty.action p.actionScope && scopeAdmitsType A rs env.reqty.resource

/-- The request environments of the action schema that the rule's scope admits: those in which
its leaves are evaluated. -/
def PolicySet.envsOf (P : PolicySet) (p : Policy) : List TypeEnv :=
  P.actionSchema.environments.filter (p.admits P.actionSchema)

/-! ## Validity -/

/-- The typing context of a temporal leaf of `P` at a position with the facts `F`, in the
environment `env`. -/
def PolicySet.typingCtx (P : PolicySet) (env : TypeEnv) (F : List Guard) : TypingCtx :=
  ⟨env, P.schema, P.maxWindow, F⟩

/-- The type of the attribute path `p` in the record type `rty`, when every attribute along it is
declared, whether or not an optional one is present. -/
def declaredPathType? (rty : RecordType) (p : Path) : Option CedarType :=
  pathType? (fun _ => true) rty [] p

/-- The type of a provider argument other than a set, in the typing context: a literal's type;
for a request path, its declared type in the context record or in the attributes of the root's
entity type, `id` and `type` as any other attribute; a bare root, its entity type. An optional attribute along a path needs no `has` guard: the provider
contract tolerates an absent argument, and an attribute the request lacks resolves to one
(`Provider.Arg.resolve`). -/
def Provider.Arg.typeIn? (C : TypingCtx) : Provider.Arg → Option CedarType
  | .context p => declaredPathType? C.env.reqty.context p
  | .scope r [] => some (.entity (C.scopeType r))
  | .scope r p => (C.env.ets.attrs? (C.scopeType r)).bind (declaredPathType? · p)
  | .string _ => some .string
  | .long _ => some .int
  | .decimal _ => some (.ext .decimal)
  | .bool _ => some (.bool .anyBool)
  | .set _ => none

mutual

/-- A provider argument has the type `ty` in the typing context. A set argument has a set type
when each of its elements has the element type; the empty set has every set type. -/
def Provider.Arg.hasTypeIn (C : TypingCtx) : Provider.Arg → CedarType → Bool
  | .set items, .set ty => Provider.Arg.allHaveTypeIn C items ty
  | .set _, _ => false
  | a, ty => a.typeIn? C == some ty

/-- Every element of a set argument has the type `ty`. -/
def Provider.Arg.allHaveTypeIn (C : TypingCtx) : List Provider.Arg → CedarType → Bool
  | [], _ => true
  | x :: xs, ty => Provider.Arg.hasTypeIn C x ty && Provider.Arg.allHaveTypeIn C xs ty

end

/-- The arguments have their declared types in the typing context. -/
def Provider.ArgsTypedIn (C : TypingCtx) (args : List Provider.Arg) (tys : List CedarType) : Prop :=
  args.length = tys.length ∧ ∀ p ∈ args.zip tys, p.1.hasTypeIn C p.2 = true

/-- **A provider invocation is typed** in the typing context: its arguments, and those of each
method of its chain, have their declared types. -/
def Provider.Call.TypedIn (C : TypingCtx) (D : Provider.Declarations) (c : Provider.Call) : Prop :=
  ∃ sig, D.find? c.function = some sig ∧ Provider.ArgsTypedIn C c.args sig.args ∧
    ∀ m ∈ c.methods, ∃ ms ∈ sig.methods, ms.name = m.name ∧ Provider.ArgsTypedIn C m.args ms.args

/-- A temporal leaf of the rule `p`, at a position with the facts `F`, is valid: well-typed in
every environment the rule admits, safe, and every monitoring scope of it varies with the
timepoint. -/
structure PolicySet.LeafValid (P : PolicySet) (p : Policy) (F : List Guard) (φ : Formula) :
    Prop where
  wellTyped : ∀ env ∈ P.envsOf p, φ.WellTyped (P.typingCtx env F) []
  safe : φ.IsSafe
  monitorsTime : φ.MonitorsTime

/-- **Validity.** -/
structure PolicySet.Valid (P : PolicySet) : Prop where
  /-- Every leaf's attribute has a type. -/
  leafTypes : P.hoistedTypes?.isSome = true
  /-- The leaves' attributes are distinct. -/
  namesNodup : P.hoistedNames.Nodup
  /-- No action's context declares a leaf's attribute. -/
  namesFresh : ∀ act ∈ P.actionSchema.acts.toList, ∀ a ∈ P.hoistedNames,
    act.2.context.find? a = none
  /-- The Cedar part reads the request context only through other attributes, when the policy
  set has a leaf. Without one, nothing is hoisted, the lowered rules are the rules, and the
  context is the request's. -/
  readsContext : P.leafList ≠ [] → ∀ p ∈ P.policies, p.toExpr.ReadsContext P.hoistedNames
  /-- The augmented schema is well-formed: every entity type and action it names is declared,
  and every type in it is well-formed. Cedar's soundness theorem assumes it. -/
  wellFormed : P.augmentedSchema.validateWellFormed = .ok ()
  /-- No entity type of the augmented schema has an enumerated ancestor
  (`Schema.standardAncestors`). -/
  standardAncestors : P.augmentedSchema.standardAncestors = true
  /-- The action schema is complete when the policy set has a rule: it declares no name
  `external`. Cedar's validator validates no policy against an incomplete schema. -/
  complete : P.policies ≠ [] → P.externalTypes = [] ∧ P.externalActions = []
  /-- Cedar's validator accepts the lowered rules against the augmented schema. -/
  cedar : Cedar.Validation.validate P.lowered P.augmentedSchema = .ok ()
  /-- Every temporal leaf is valid. -/
  temporal : ∀ p ∈ P.policies, ∀ φ F, (.inl φ, F) ∈ p.toExpr.leafFacts [] → P.LeafValid p F φ
  /-- Every provider leaf names a declared provider and declared methods, and its arguments
  have their declared types in every environment the rule admits. -/
  providers : ∀ p ∈ P.policies, ∀ c F, (.inr c, F) ∈ p.toExpr.leafFacts [] →
    c.Declared P.providerDecls ∧ ∀ env ∈ P.envsOf p, c.TypedIn (P.typingCtx env F) P.providerDecls
  /-- Every temporal leaf looks back at most `max_horizon` in total, when the event schema
  declares one: its horizon, in seconds, is at most the cap (`PolicySet.maxHorizon`). -/
  horizon : ∀ H, P.maxHorizon = some H → ∀ φ ∈ P.temporalLeaves, φ.horizon .seconds ≤ H

end Dogwood.Spec
