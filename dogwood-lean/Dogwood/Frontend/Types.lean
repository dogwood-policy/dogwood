import Dogwood.Frontend.EventSchemaDsl
import Dogwood.Frontend.ProviderDecls
import Dogwood.Frontend.CedarSchema
import Dogwood.Spec.Policy
import Cedar.Validation.Types

/-!
# The frontend's intermediate and output records

The values that pass between the frontend's stages, each the Lean form of the crate's:

* the **derived event schema** (`event_schema/derive.rs`): one event per action and declared
  kind, with its field tree and its pins, and the `max_window` cap;
* the **hoisted fields** cedarify records (`cedarify/mod.rs`): a `ContextField` for each
  temporal block and a `ProviderField` for each provider chain, with the rule's action scope,
  the concrete actions it resolves to, and what its principal and resource scopes admit;
* `Cedarified`, cedarify's whole result, and `Lowered`, the lowered set (`api::Lowered`);
* `Error`: a stage, the crate's error category, and the message.

The lowered Cedar policies are `Dogwood.Spec.Policy`s that keep the crate's names: each hoisted
leaf is the attribute access `context.<id>` (temporal) or `context.providers.<id>` (provider),
and Cedar's desugaring has been applied (`!=` is `!(==)`, `>` is `!(<=)`, …), as Cedar's policy
JSON of the crate's policy shows it.
-/

namespace Dogwood.Frontend

open Surface.Temporal (Interval Block)
open EventSchemaDsl (PinRoot)
open ProviderDecls (ProviderDecl EntityTypeDecl Declarations)

/-! ## The derived event schema -/

/-- The type of a derived field (crate `FieldType`). `cedar` is the type as Cedar's schema
renders it (`Set < String >`); `entityTypes` the `appliesTo` names as written. -/
inductive FieldType where
  | cedar (text : String)
  | entityTypes (names : List String)
deriving Repr, DecidableEq, BEq, Inhabited

/-- A node of an event's field tree (crate `DerivedFieldNode`), members in name order. -/
inductive DerivedFieldNode where
  | leaf (ty : FieldType)
  | group (members : List (String × DerivedFieldNode))
deriving Repr, BEq, Inhabited

/-- A pinned field (crate `Pin`): its full path, and the request-side path it must match, with
the root (`principal`/`resource` heads a `scope` path; a `context` path drops `context`). -/
structure Pin where
  fieldPath : List String
  contextPath : List String
  root : PinRoot
deriving Repr, DecidableEq, BEq, Inhabited

/-- One derived event (crate `DerivedEvent`). `namespace` ends in `Action`. -/
structure DerivedEvent where
  «namespace» : List String
  action : String
  kind : String
  decision : Bool
  fields : List (String × DerivedFieldNode)
  pins : List Pin
deriving Repr, BEq, Inhabited

/-- The derived event schema (crate `DerivedEventSchema`): the events in derivation order
(namespaces in the fragment's order, then actions, then declarations), and the cap, 24h unless
the DSL declares one. -/
structure DerivedEventSchema where
  events : List DerivedEvent
  maxWindow : Interval
  /-- The cap on a temporal leaf's horizon (crate `max_horizon`), if the DSL declares one. -/
  maxHorizon : Option Interval := none
deriving Repr, BEq, Inhabited

/-- A derived event as the crate's public `EventSignature` lists it: its leaf fields, sorted by
the text of their path (`fieldPathJoin`). -/
structure EventSignature where
  «namespace» : List String
  action : String
  kind : String
  decision : Bool
  fields : List (List String × FieldType)
  pins : List Pin
deriving Repr, BEq, Inhabited

/-! ## Hoisted fields -/

/-- The action scope a rule pins, as lowering reads it (crate `ScopedAction`). An action is
`(namespace, id)`, the namespace `""` at the root. -/
inductive ScopedAction where
  | concrete (ns id : String)
  | list (actions : List (String × String))
  | unconstrained
deriving Repr, DecidableEq, BEq, Inhabited

/-- What a principal or resource scope admits on the entity-type axis (crate
`ScopeConstraint`): a slot reads as `any`. -/
inductive ScopeConstraint where
  | any
  | isType (t : String)
  | uid (entityType : String) (membership : Bool)
deriving Repr, DecidableEq, BEq, Inhabited

/-- A hoisted temporal leaf, as cedarify records it (crate `cedarify::ContextField`), before pin
injection. `targetActions` are sorted and free of duplicates. -/
structure ContextField where
  action : ScopedAction
  fieldName : String
  temporal : Block
  targetActions : List (String × String)
  principal : ScopeConstraint
  resource : ScopeConstraint
deriving Repr, BEq, Inhabited

/-- A hoisted provider chain (crate `cedarify::ProviderField`): the invocation, its eager
methods, and the Cedar type text of the bound value. -/
structure ProviderField where
  action : ScopedAction
  targetActions : List (String × String)
  fieldName : String
  cedarType : String
  /-- The start of the provider's enclosing clause body in the policy source. -/
  bodyBase : Nat
  invocation : Provider.Invocation
  methods : List Provider.MethodCall
  principal : ScopeConstraint
  resource : ScopeConstraint
deriving Repr, BEq, Inhabited

/-- Cedarify's result (crate `Cedarified`): the lowered rules, in rule order, and the hoisted
fields, in emission order. -/
structure Cedarified where
  /-- The lowered rules, with the crate's names. -/
  policies : List Dogwood.Spec.Policy
  contextFields : List ContextField
  providerFields : List ProviderField
  /-- The Cedar policy id of each rule. -/
  ruleIds : List String
  /-- The positional key of each rule, the prefix of its hoisted names (`policy_<k>`). -/
  ruleKeys : List String
  /-- The rule index of each context field. -/
  temporalRules : List Nat
  /-- The rule index of each provider field. -/
  providerRules : List Nat
  /-- The declared provider enums the calls reference, sorted. -/
  referencedEnums : List String
  /-- The exported name of each used provider enum, by declared name. -/
  enumNames : List (String × String)
deriving Repr, Inhabited

/-- A provider field's declaration, as merging resolves it: the declaration of its provider, the
enum declarations its call references, and their exported names. -/
structure ResolvedProvider where
  id : String
  declaration : Option ProviderDecl
  entityTypes : List (String × EntityTypeDecl)
  entityTypeNames : List (String × String)
deriving Repr, BEq, Inhabited

/-- A temporal leaf of the lowered set (crate `TemporalField`). -/
structure TemporalField where
  id : String
  action : ScopedAction
  targetActions : List (String × String)
  principal : ScopeConstraint
  resource : ScopeConstraint
  condition : Block
deriving Repr, BEq, Inhabited

/-- The rule identity a lowering computes (`identity.rs`): each rule's canonical Cedar text,
each rule's hoisted leaves as `(canonical name, canonical encoding)`, and each rule's revision. -/
structure Identity where
  ruleCanonical : List String
  leaves : List (List (String × String))
  ruleRevisions : List String
deriving Repr, BEq, Inhabited

/-! ## Errors -/

/-- A stage of the frontend, or one of the parsers before it. -/
inductive Stage where
  /-- The parsers, whose output is the frontend's input. -/
  | policy | library | eventSchema | providers | actionSchema
  | providerCheck | mergeLibrary | expand | rejectArrays
  | derive | signatures | universalPins | decisionKinds | resolveSchema
  | cedarify | injectPins | identity | augment | resolveProviders | compileSchema
  | unorder | relativize | validate | conformance
  /-- The public pipeline, `parse` then `lower`. -/
  | pipeline
  /-- Stable-id assignment (crate `ParsedPolicySet::with_ids`). -/
  | assignIds
  /-- The distincters of a lowering (crate `Distincter::from_str`, and `lower_many`'s checks). -/
  | distincters
  /-- Merging several lowered entries (crate `api::merge`). -/
  | merge
deriving Repr, DecidableEq, BEq, Inhabited

def Stage.name : Stage → String
  | .policy => "policy" | .library => "library" | .eventSchema => "eventSchema"
  | .providers => "providers" | .actionSchema => "actionSchema"
  | .providerCheck => "providerCheck" | .mergeLibrary => "mergeLibrary" | .expand => "expand"
  | .rejectArrays => "rejectArrays" | .derive => "derive" | .signatures => "signatures"
  | .universalPins => "universalPins" | .decisionKinds => "decisionKinds"
  | .resolveSchema => "resolveSchema" | .cedarify => "cedarify" | .injectPins => "injectPins"
  | .identity => "identity" | .augment => "augment" | .resolveProviders => "resolveProviders"
  | .compileSchema => "compileSchema" | .unorder => "unorder" | .relativize => "relativize"
  | .validate => "validate" | .conformance => "conformance" | .pipeline => "pipeline"
  | .assignIds => "assignIds" | .distincters => "distincters" | .merge => "merge"

instance : ToString Stage := ⟨Stage.name⟩

/-- The kind of a lowering error: the crate's `api::Error` variant, or `notImplemented` for a
stage the Lean frontend does not compute yet. -/
inductive Category where
  | parse | «macro» | cedarify | policySet | cedarSchema | eventSchema | providers | policyId
  /-- A distincter that is not a Cedar identifier (crate `Error::InvalidDistincter`). -/
  | invalidDistincter
  /-- Two entries of `lower_many` with one distincter (crate `Error::DuplicateDistincter`). -/
  | duplicateDistincter
  /-- `lower_many` of no entry (crate `Error::NoPolicies`). -/
  | noPolicies
  /-- An error of the export itself, not of the crate. -/
  | export
  | other
  | notImplemented
deriving Repr, DecidableEq, BEq, Inhabited

/-- Which stable-id check failed (crate `PolicyIdErrorKind`). -/
inductive PolicyIdKind where
  | missing | duplicate | invalid | countMismatch | repeatedAnnotation
deriving Repr, DecidableEq, BEq, Inhabited

/-- What a stable-id error is about (crate `PolicyIdError`): its kind, the 0-based position of the
policy (for a duplicate, the second of the two; none for a count mismatch), and the offending
id. -/
structure PolicyIdInfo where
  kind : PolicyIdKind
  policy : Option Nat := none
  id : Option String := none
deriving Repr, DecidableEq, BEq, Inhabited

/-- A stage's error: the stage, the category, the message, and the source span when the crate
reports one. A span points into the macro library's source at the stage `mergeLibrary`, and into
the policy source of entry `entry` (the only one, when there is a single entry) otherwise. A
stable-id error also says what it is about (`policyId`). -/
structure Error where
  stage : Stage
  category : Category
  message : String
  span : Option Span := none
  /-- The entry of a multi-entry lowering the error belongs to; none for the shared inputs and
  the merge. -/
  entry : Option Nat := none
  policyId : Option PolicyIdInfo := none
deriving Repr, BEq, Inhabited

/-- A stage the Lean frontend does not compute yet. -/
def Error.notImplemented (stage : Stage) (what : String) : Error :=
  { stage, category := .notImplemented, message := s!"not implemented: {what}" }

/-- The result of a stage. -/
abbrev Result (α : Type) := Except Error α

/-! ## Stable ids and context reads -/

/-- Where the stable policy ids of a parsed set come from (crate `IdSource`). -/
inductive IdSource where
  /-- Rule `k` is named by its position. -/
  | positional
  /-- Each policy's `@id("…")` annotation. -/
  | annotation
  /-- One id per policy, in source order. -/
  | explicit (ids : List String)
deriving Repr, DecidableEq, BEq, Inhabited

/-- A read of the request context, by the Cedar part of a rule, that lowering does not preserve
(crate `cedarify::ContextRead`): of the context whole, or of an attribute with a reserved name;
`span` is the span of `context` in the rule's source. -/
structure ContextRead where
  rule : Nat
  span : Span
  message : String
  whole : Bool
deriving Repr, DecidableEq, BEq, Inhabited

/-! ## The inputs and the lowered set -/

/-- The frontend's inputs: what the parsers produced from one bundle's sources. `library` is
the macro library's definitions (empty when the library text is blank; the library's own
policies are dropped). -/
structure Inputs where
  policy : Surface.PolicySet
  library : List Surface.MacroDef
  eventSchema : EventSchemaDsl.EventSchema
  providers : Option Declarations
  actionSchema : CedarSchema.Fragment
deriving Repr, Inhabited

/-- A provider leaf of the lowered set (crate `api::ProviderField`). -/
structure LoweredProviderField where
  id : String
  action : ScopedAction
  targetActions : List (String × String)
  principal : ScopeConstraint
  resource : ScopeConstraint
  invocation : Provider.Invocation
  methods : List Provider.MethodCall
  bodyBase : Nat
  declaration : Option ProviderDecl
  entityTypes : List (String × EntityTypeDecl)
  entityTypeNames : List (String × String)
deriving Repr, BEq, Inhabited

instance : Inhabited Cedar.Validation.Schema := ⟨⟨Cedar.Data.Map.empty, Cedar.Data.Map.empty⟩⟩

/-- The lowered set (crate `api::Lowered`). -/
structure Lowered where
  /-- The lowered rules, in rule order, with the crate's names. -/
  policies : List Dogwood.Spec.Policy
  /-- The action schema augmented with the hoisted attributes, as a fragment. -/
  augmentedSchema : CedarSchema.Fragment
  /-- The augmented schema as Cedar compiles it. -/
  schema : Cedar.Validation.Schema
  /-- The temporal leaves as authored, after pin injection. -/
  temporal : List TemporalField
  /-- `temporal` with every comparison that orders a timepoint, or computes with one, replaced
  by a false one. -/
  temporalExecutable : List TemporalField
  /-- `temporalExecutable` after the relativization rewrite. -/
  temporalRewritten : List TemporalField
  /-- The universal symmetric pins, as partition keys. -/
  partitionKeys : List Pin
  providers : List LoweredProviderField
  ruleIds : List String
  temporalRules : List Nat
  providerRules : List Nat
  eventSchema : DerivedEventSchema
  decisionKinds : List String
  enumNames : List (String × String)
  /-- The service schema's provider declarations (the crate keeps them on the service schema;
  the conformance export reads them). -/
  declarations : Option Declarations
  /-- The reads of the request context the authored rules' Cedar parts make that lowering does
  not preserve, as the crate records them while it lowers (`to_ast::note_context_read`): whole
  (`true`), or of a reserved name (`false`, with the name). -/
  contextReads : List (Bool × String) := []
  /-- Each rule's entry, for a set several entries were lowered into (crate `rule_sources`); the
  validator groups its once-per-source warnings by it. Empty for one entry. -/
  ruleSources : List Nat := []
deriving Inhabited

end Dogwood.Frontend
