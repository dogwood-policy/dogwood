//! The crate-private lowering pipeline and runtime helpers behind the
//! public Cedar-parity API.
//!
//! The public surface — [`ServiceSchema`](crate::ServiceSchema) /
//! [`PolicySchema`](crate::PolicySchema),
//! [`ParsedPolicySet`](crate::policy_set::ParsedPolicySet) /
//! [`LoweredPolicySet`](crate::policy_set::LoweredPolicySet),
//! [`Validator`](crate::Validator), [`Authorizer`](crate::Authorizer), and the
//! types they expose — lives in the dedicated modules
//! ([`crate::service_schema`], [`crate::policy_schema`], [`crate::policy_set`],
//! [`crate::authorize`]) and is re-exported at the crate root. This module
//! holds the machinery those types delegate to: the two lowering phases
//! (`parse` then `lower`), building a Cedar request/context from a Dogwood
//! [`Event`], evaluating temporal leaves and information providers, and the
//! shared decision core.
//!
//! It is `pub(crate)`: nothing here is part of the public API except
//! [`Error`], which is re-exported at the crate root as the construction
//! error of the lowering phases
//! ([`ParsedPolicySet::parse`](crate::policy_set::ParsedPolicySet::parse) /
//! [`ParsedPolicySet::lower`](crate::policy_set::ParsedPolicySet::lower)) and
//! of building a [`ServiceSchema`](crate::ServiceSchema). The leaf/reference
//! types [`ExtensionId`], [`ActionRef`], [`ActionScope`], [`TemporalField`],
//! and [`ProviderField`] are re-exported (for the out-of-crate
//! [`TemporalEngine`](crate::engine::TemporalEngine) consumer and the
//! [`LoweredPolicySet`](crate::policy_set::LoweredPolicySet) accessors).

use std::collections::{BTreeMap, BTreeSet};
use std::str::FromStr;

use cedar_policy::{
    Context, Entities, EntityUid, PolicySet as CedarPolicySet, Request, RestrictedExpression,
    Schema,
};
use cedar_policy_core::ast as cedar_ast;

use crate::authorize::DogwoodRuleRef;
use crate::cedarify::cedarify_with_providers;
use crate::error::{
    CedarifyError, MacroError, ParseError, ParseErrors, RawCedarifyError, RawParseError, SourceLoc,
    Span,
};
use crate::event_schema::derive::{DerivedEventSchema, derive};
use crate::extension::temporal::Temporal;
use crate::interpreter::value::{EntityRecord, Event, EventData, Scope, Value, value_uid_string};
use crate::policy_schema::PolicySchema;
use crate::service_schema::ServiceSchema;

// ─── Identifiers / references (re-exported by the public modules) ────

/// Generated id of a hoisted extension leaf — `__temporal_N` (temporal)
/// or `p_N` (provider). The lowered Cedar policy references it as
/// `context.<id>`.
pub type ExtensionId = String;

/// The action a hoisted leaf is attached to. Every extension leaf is
/// under a rule that scopes a specific action, so this is always present.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ActionRef {
    /// `None` = top-level (unnamespaced) action.
    pub namespace: Option<String>,
    pub id: String,
}

/// The action scope a rule pins — the three shapes a Cedar `action` scope can
/// take. A hoisted temporal leaf carries its rule's scope so validation knows
/// which action(s) its `context.input.<field>` paths must resolve against.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ActionScope {
    /// `action == Ns::Action::"X"` — a single action.
    Concrete(ActionRef),
    /// `action in [ … ]` — each listed action.
    List(Vec<ActionRef>),
    /// A bare `action` scope with no action pinned — the leaf may fire on any
    /// action.
    Unconstrained,
}

impl ActionScope {
    /// The single action this scope pins, if it pins exactly one via `==`.
    /// `List` / `Unconstrained` return `None`.
    pub fn concrete(&self) -> Option<&ActionRef> {
        match self {
            ActionScope::Concrete(a) => Some(a),
            ActionScope::List(_) | ActionScope::Unconstrained => None,
        }
    }

    /// The actions a hoisted leaf must be validated against: the one concrete
    /// action, or each listed action. `Unconstrained` yields an empty slice.
    pub fn actions_to_check(&self) -> &[ActionRef] {
        match self {
            ActionScope::Concrete(a) => std::slice::from_ref(a),
            ActionScope::List(v) => v,
            ActionScope::Unconstrained => &[],
        }
    }
}

// ─── Hoisted extension leaves ───────────────────────────────────────

/// A temporal leaf hoisted out of a policy: a stream monitor evaluated
/// against the event history and bound (as a bool) into `context.<id>`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TemporalField {
    pub id: ExtensionId,
    /// The action scope the leaf's rule pins, as written.
    pub action: ActionScope,
    /// The concrete actions [`action`](Self::action) resolves to against the
    /// schema: a group expanded to its transitive members, an unconstrained scope
    /// to every action. This — not [`action`](Self::action) — is what a leaf is
    /// evaluated against, because Cedar validates a policy scoped
    /// `action in [Group]` against the group's MEMBERS. Resolved by the same
    /// expansion the schema augmentation grafts the hoisted field with, so the two
    /// cannot disagree about where the field lives.
    pub target_actions: Vec<ActionRef>,
    /// What the rule's `principal` scope admits on the entity-TYPE axis. A bare
    /// `principal` admits every type the action permits; `is Ns::T` narrows to that
    /// type. This is what decides whether an attribute read in the condition
    /// resolves, since it decides which entity types can arrive.
    pub principal: ScopeConstraint,
    /// The same for the rule's `resource` scope.
    pub resource: ScopeConstraint,
    pub condition: Temporal,
}

/// Re-exported from lowering: what a rule's `principal` / `resource` scope admits.
pub use crate::cedarify::ScopeConstraint;

/// The declared type of an event field — the public projection of the derived
/// event schema's field type. Carried by [`EventFieldPath`].
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum EventFieldType {
    /// A concrete Cedar type, rendered as text (`String`, `Long`,
    /// `Set < String >`). Spliced `input`/`output` fields and concrete-typed
    /// injected fields.
    ///
    /// The string is `cedar-policy-core`'s own rendering of the type (note the
    /// incidental spacing in `Set < String >`). It is intended for **display /
    /// coarse classification** (e.g. "is this `Long`?"), not as a stable
    /// machine-parseable format: the exact spelling may shift with a Cedar
    /// upgrade. A consumer needing a firm contract should match on a prefix /
    /// the leading token rather than the whole string.
    Cedar(String),
    /// A set of candidate entity-type names — an injected `principalType(A)` /
    /// `resourceType(A)` field (e.g. the reserved `callerPrincipal`), kept as
    /// its full declared set rather than collapsed to one type.
    EntityTypes(Vec<String>),
}

/// A declared **leaf** field of a derived event: its dotted path and type.
/// Yielded by [`EventSignature::fields`].
///
/// The path is the full dotted address a temporal predicate uses to match the
/// field (`input.user`, `output.amount`, `callerPrincipal`,
/// `meta.session.id`) — always a scalar leaf, never a group.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct EventFieldPath {
    pub(crate) path: Vec<String>,
    pub(crate) ty: EventFieldType,
}

impl EventFieldPath {
    /// The dotted leaf-path segments (`["input", "user"]`,
    /// `["callerPrincipal"]`, `["meta", "session", "id"]`).
    pub fn path(&self) -> &[String] {
        &self.path
    }

    /// The field's declared type.
    pub fn field_type(&self) -> &EventFieldType {
        &self.ty
    }
}

/// Which request-side root a pin's target path is anchored to. Selects how a
/// pinned field's value is correlated at evaluation. See [`EventPin`].
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum EventPinRoot {
    /// The request **scope**: the target path's head is `principal` / `resource`
    /// (the pinned field must equal that scope entity's uid / an attribute of
    /// it).
    Scope,
    /// The request **context**: the target path addresses the request context
    /// record (the pinned field must equal `context.<target_path>`).
    Context,
}

/// A **pin** the event schema declares on a derived event: a field whose value
/// is forced to equal a request-side value, injected onto every predicate for
/// this event as a correlation. Yielded by [`EventSignature::pins`].
///
/// This is the schema-agnostic description of a correlation: a pin names the
/// injected field carrying it ([`field_path`](EventPin::field_path)) and the
/// request value it must match ([`target_path`](EventPin::target_path) under
/// [`root`](EventPin::root)) — without a client needing to know the schema's
/// naming convention (`callerPrincipal`, `__drupe.session_id`, or a
/// custom name). A client that validates or constructs events uses this to know
/// which fields are correlated to the request (e.g. to fill a pinned field with
/// the current principal's uid, or to check an inbound event's pinned field
/// agrees).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct EventPin {
    pub(crate) field_path: Vec<String>,
    pub(crate) target_path: Vec<String>,
    pub(crate) root: EventPinRoot,
}

impl EventPin {
    /// The dotted path of the **pinned field** on this event — the injected
    /// leaf carrying the correlation (`["callerPrincipal"]`,
    /// `["__drupe", "session_id"]`, or a custom name).
    pub fn field_path(&self) -> &[String] {
        &self.field_path
    }

    /// The request-side path the field is pinned to, **without** a leading
    /// `context`. For a [`Scope`](EventPinRoot::Scope) pin the head is the
    /// `principal` / `resource` root (`["principal"]`); for a
    /// [`Context`](EventPinRoot::Context) pin it is the context path
    /// (`["__drupe", "session_id"]`, i.e. `context.__drupe.session_id`).
    pub fn target_path(&self) -> &[String] {
        &self.target_path
    }

    /// Which request root [`target_path`](EventPin::target_path) is anchored to.
    pub fn root(&self) -> EventPinRoot {
        self.root
    }
}

/// The signature of one derived event — the shape an event of a given
/// `(action, kind)` takes under the event schema. Yielded by
/// [`LoweredPolicySet::event_signatures`](crate::LoweredPolicySet::event_signatures).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct EventSignature {
    pub(crate) namespace: Vec<String>,
    pub(crate) action: String,
    pub(crate) kind: String,
    pub(crate) decision: bool,
    pub(crate) fields: Vec<EventFieldPath>,
    pub(crate) pins: Vec<EventPin>,
}

impl EventSignature {
    /// The qualified action path **including** the trailing `Action` segment
    /// (`["Drupe", "Action"]`) — the shape a temporal predicate's namespace
    /// carries. (Distinct from [`ActionRef::namespace`], which is the bare
    /// `Ns` without `Action`.)
    pub fn namespace(&self) -> &[String] {
        &self.namespace
    }

    /// The action id (e.g. `"Login"`).
    pub fn action(&self) -> &str {
        &self.action
    }

    /// The event kind (e.g. `"request"` / `"response"`).
    pub fn kind(&self) -> &str {
        &self.kind
    }

    /// Whether an event of this kind is a **decision point** (authorization
    /// runs and yields a verdict), as opposed to history-only. Mirrors
    /// [`LoweredPolicySet::is_decision_kind`](crate::LoweredPolicySet::is_decision_kind)
    /// for this event's kind.
    pub fn is_decision(&self) -> bool {
        self.decision
    }

    /// The declared **leaf** fields of this event, each an [`EventFieldPath`].
    /// Nested records are flattened to dotted paths; groups (`input` alone) are
    /// not yielded. Includes schema-injected fields not present in the action's
    /// Cedar `context` (`caller*`, custom injected/pinned fields).
    pub fn fields(&self) -> impl Iterator<Item = &EventFieldPath> {
        self.fields.iter()
    }

    /// The **pins** the event schema declares on this event, each an
    /// [`EventPin`] correlating a field to a request-side value. Empty when the
    /// schema declares no pins; the default schema pins `callerPrincipal` on
    /// every kind. Each pin's
    /// [`field_path`](EventPin::field_path) is also present in
    /// [`fields`](EventSignature::fields) — pins describe *which* declared
    /// fields are request-correlated, not additional fields.
    pub fn pins(&self) -> impl Iterator<Item = &EventPin> {
        self.pins.iter()
    }
}

/// An information-provider invocation hoisted out of a policy: evaluated
/// per request (by running its declared implementation) and bound (as
/// its output value) under `context.providers.<id>`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ProviderField {
    pub id: ExtensionId,
    /// The action scope the provider's rule pins. Informational: the hoisted
    /// `context.providers.<id>` field is declared on EVERY action's context
    /// and the provider is evaluated for every decision event (provider
    /// execution is unconditional — see the provider contract in the guide);
    /// this records which scope the originating rule declared.
    pub action: ActionScope,
    /// The concrete `(namespace, action_id)` actions [`action`](Self::action)
    /// resolves to against the schema. Informational: the reference
    /// implementation evaluates every provider unconditionally, but an
    /// alternative implementation may use this set for as-if optimizations
    /// (skipping evaluations whose result cannot affect the verdicts).
    pub target_actions: Vec<ActionRef>,
    pub invocation: crate::extension::provider::ast::Invocation,
    /// The eager method chain applied to the invocation's output before the
    /// value is bound into `context.providers.<id>`, in order. Empty for a
    /// plain projection-only invocation. Each method is evaluated in Rhai at
    /// authorize time as `fn <name>(input, args…)`.
    pub methods: Vec<crate::extension::provider::ast::MethodCall>,
    /// Start offset of the provider block body in the `.dw` source — the base
    /// for rebasing the invocation's block-relative span to a `.dw` location.
    pub body_base: usize,
    /// The resolved declaration for this provider (arg/output types +
    /// implementation). `None` if the provider was undeclared at parse time.
    pub declaration: Option<crate::extension::provider::declarations::ProviderDecl>,
}

// ─── The lowered artifacts (crate-internal; LoweredPolicySet wraps them) ─

/// The result of lowering Dogwood source to Cedar, against the two schema
/// halves. This is the internal payload of the public
/// [`LoweredPolicySet`](crate::policy_set::LoweredPolicySet) — every field is
/// crate-private, reached only through `LoweredPolicySet`'s accessors.
#[derive(Debug)]
pub(crate) struct Lowered {
    /// The lowered Cedar policies (one static policy per Dogwood rule).
    pub policies: CedarPolicySet,
    /// The action schema augmented with the hoisted `context.<id>` fields
    /// the lowered policies reference — the schema a caller feeds to Cedar /
    /// a Cedar policy store alongside `policies`. Compiled from `augmented_schema_fragment`.
    pub augmented_schema: Schema,
    /// The augmented schema in its lossless `SchemaFragment` form — the single
    /// source of truth from which `augmented_schema` (compiled) and the text /
    /// JSON serializations are derived. A `cedar_policy::Schema` is a compiled,
    /// lossy form with no serializer of its own, so the fragment is what lets
    /// `LoweredPolicySet::cedar_schema_str` / `cedar_schema_json` emit text /
    /// JSON without re-parsing.
    pub augmented_schema_fragment: cedar_policy::SchemaFragment,
    /// Hoisted temporal stream-monitor leaves, **as authored** (post pin
    /// injection, pre relativization). This is what validation runs on, so
    /// findings point at authored structure.
    pub temporal: Vec<TemporalField>,
    /// The same leaves after the pin-relativization rewrite
    /// ([`crate::event_schema::relativize`]) — the executable artifact
    /// handed to temporal engines and exposed to reimplementers. Identical
    /// to `temporal` when the event schema declares no universal symmetric
    /// pin. The default schema declares one (on `callerPrincipal`), so under
    /// the default these differ from `temporal`.
    pub temporal_rewritten: Vec<TemporalField>,
    /// The event schema's universal symmetric pins as engine-facing partition
    /// keys. Non-empty iff the schema declares such a pin. A partitioning
    /// temporal engine keys its per-monitor history on these and runs the
    /// **non-relativized** `temporal` leaves; empty means there is nothing to
    /// partition on (and `temporal == temporal_rewritten`).
    pub partition_keys: Vec<crate::engine::PartitionKey>,
    /// Hoisted information-provider leaves.
    pub providers: Vec<ProviderField>,
    /// `rule_ids[k]` is the synthesized Cedar policy id for Dogwood rule k.
    pub rule_ids: Vec<String>,
    /// `rule_spans[k]` is the originating `.dw` span of Dogwood rule k.
    pub rule_spans: Vec<Span>,
    /// The original `.dw` source, shared so each validation finding can embed
    /// it and self-render (see [`crate::error::SourceLoc`]).
    pub dw_src: std::sync::Arc<str>,
    /// The derived event schema (event kinds + fields per action).
    pub event_schema: DerivedEventSchema,
    /// The event kinds the event schema marks `decision`.
    pub decision_kinds: BTreeSet<String>,
}

impl Lowered {
    /// The declared signature of every event this policy set can see.
    ///
    /// Shared by [`LoweredPolicySet::event_signatures`](crate::LoweredPolicySet::event_signatures)
    /// and by authorizer construction, which hands them to a temporal engine so a
    /// COMPILING engine can resolve each event field's declared type.
    pub(crate) fn event_signatures(&self) -> impl Iterator<Item = EventSignature> + '_ {
        self.event_schema.events.iter().map(|ev| EventSignature {
            namespace: ev.namespace.clone(),
            action: ev.action.clone(),
            kind: ev.kind.clone(),
            decision: ev.decision,
            fields: ev
                .leaf_fields()
                .into_iter()
                .map(|(path, ty)| EventFieldPath {
                    path,
                    ty: match ty {
                        crate::event_schema::derive::FieldType::Cedar(s) => {
                            EventFieldType::Cedar(s)
                        }
                        crate::event_schema::derive::FieldType::EntityTypes(v) => {
                            EventFieldType::EntityTypes(v)
                        }
                    },
                })
                .collect(),
            pins: ev
                .pins
                .iter()
                .map(|p| EventPin {
                    field_path: p.field_path.clone(),
                    target_path: p.context_path.clone(),
                    root: match p.root {
                        crate::event_schema::ast::PinRoot::Scope => EventPinRoot::Scope,
                        crate::event_schema::ast::PinRoot::Context => EventPinRoot::Context,
                    },
                })
                .collect(),
        })
    }

    /// The lowered Cedar policies — handed to a [`PolicyEngine`](crate::engine::PolicyEngine)
    /// at prepare time.
    pub(crate) fn cedar_policies(&self) -> &CedarPolicySet {
        &self.policies
    }

    /// The augmented Cedar schema — handed to both engines at prepare time.
    pub(crate) fn cedar_schema(&self) -> &Schema {
        &self.augmented_schema
    }

    /// The hoisted temporal leaves — handed to a [`TemporalEngine`](crate::engine::TemporalEngine)
    /// at prepare time. These are the **relativized** (executable) leaves;
    /// the authored forms stay in `temporal` for validation.
    pub(crate) fn temporal_leaves(&self) -> &[TemporalField] {
        &self.temporal_rewritten
    }

    /// The **non-relativized** hoisted temporal leaves — handed to a partitioning
    /// [`TemporalEngine`](crate::engine::TemporalEngine) instead of
    /// [`temporal_leaves`](Lowered::temporal_leaves), together with
    /// [`partition_keys`](Lowered::partition_keys). Correct only when the engine
    /// actually partitions by those keys.
    pub(crate) fn temporal_leaves_nonrelativized(&self) -> &[TemporalField] {
        &self.temporal
    }

    /// The partition keys derived from the event schema's universal symmetric
    /// pins. Empty when there is nothing to partition on.
    pub(crate) fn partition_keys(&self) -> &[crate::engine::PartitionKey] {
        &self.partition_keys
    }
}

// ─── Errors ─────────────────────────────────────────────────────────

/// An error from lowering Dogwood source to a
/// [`LoweredPolicySet`](crate::policy_set::LoweredPolicySet) (via
/// [`ParsedPolicySet::parse`](crate::policy_set::ParsedPolicySet::parse) /
/// [`ParsedPolicySet::lower`](crate::policy_set::ParsedPolicySet::lower)) or
/// from building a [`ServiceSchema`](crate::ServiceSchema).
///
/// This is the *fatal prefix*: a syntax / macro / lowering / schema failure
/// means there is nothing well-formed to validate or authorize. Type errors
/// against the schema are not here — they surface as
/// [`ValidationResult`](crate::ValidationResult) findings from
/// [`Validator::validate`](crate::Validator::validate).
/// This is a `miette::Diagnostic`: the spanned variants (`Parse`, `Macro`,
/// `Cedarify`) carry the `.dw` source and render their own underlined snippet
/// (`println!("{:?}", miette::Report::new(err))` — no `with_source_code`
/// needed), and the two wrapped-Cedar variants (`PolicySet`, `CedarSchema`)
/// forward Cedar's own diagnostic. This mirrors Cedar, whose parse errors are
/// likewise self-rendering diagnostics.
///
/// It is `#[non_exhaustive]` (like Cedar's error enums) so new failure kinds
/// can be added without a breaking change.
#[derive(thiserror::Error, miette::Diagnostic, Debug)]
#[non_exhaustive]
pub enum Error {
    /// The `.dw` source was syntactically invalid.
    #[error(transparent)]
    #[diagnostic(transparent)]
    Parse(#[from] ParseErrors),

    /// Macro (`def cedar` / `def temporal`) expansion failed.
    #[error(transparent)]
    #[diagnostic(transparent)]
    Macro(#[from] MacroError),

    /// Lowering Dogwood to Cedar failed.
    #[error(transparent)]
    #[diagnostic(transparent)]
    Cedarify(#[from] CedarifyError),

    /// Cedar could not assemble the lowered policy set. Wraps Cedar's own
    /// diagnostic (boxed: Cedar's error enums are large, and boxing keeps
    /// `Result<_, Error>` small across the pipeline's hot paths).
    #[error(transparent)]
    #[diagnostic(transparent)]
    PolicySet(#[from] Box<cedar_policy::PolicySetError>),

    /// The augmented Cedar schema was invalid. Wraps Cedar's own (self-
    /// rendering) schema diagnostic (boxed, as with `PolicySet`).
    #[error(transparent)]
    #[diagnostic(transparent)]
    CedarSchema(#[from] Box<cedar_policy::CedarSchemaError>),

    /// Serializing the augmented schema back to `.cedarschema` text failed
    /// (from `LoweredPolicySet::cedar_schema_str`).
    #[error("serialize augmented schema: {0}")]
    SchemaSerialize(String),

    /// Generating the Cedar action schema from an MCP manifest failed —
    /// returned by [`PolicySchema::from_mcp_manifest`](crate::PolicySchema::from_mcp_manifest).
    #[error("MCP schema generation: {0}")]
    McpSchema(String),

    /// A `.log` trace could not be parsed.
    #[error("trace parse: {0}")]
    TraceParse(String),

    /// A Cedar `Request` handed to [`Event::from_request`](crate::Event::from_request)
    /// had no action.
    #[error("request has no action")]
    RequestMissingAction,

    /// Reading the context off a Cedar `Request` failed.
    #[error("context read: {0}")]
    ContextRead(String),

    /// The event-schema DSL failed to parse or derive against the action
    /// schema.
    ///
    /// NOTE: this carries no `.dw` span. Several variants here are span-less
    /// (`McpSchema`, `TraceParse`, `ContextRead`, `Leaf`,
    /// `RequestMissingAction`), but most describe a runtime / config / foreign-
    /// source failure that has no `.dw` location to point at. `EventSchema` is
    /// the exception: it parses a *Dogwood-authored* DSL and *could* carry a
    /// location, but its parser does not yet produce a located error — so among
    /// the Dogwood-source parsers, this is the one still below Cedar's
    /// spanned-diagnostic bar. Giving it a location is tracked separately.
    #[error("event schema error: {0}")]
    EventSchema(String),

    /// A hoisted extension leaf could not be prepared.
    #[error("extension leaf `{id}`: {message}")]
    Leaf { id: ExtensionId, message: String },

    /// The `distincter` passed to
    /// [`lower_with_distincter`](crate::policy_set::ParsedPolicySet::lower_with_distincter)
    /// is not a valid Cedar identifier fragment. The distincter is
    /// interpolated into the synthesized Cedar policy ids and the hoisted
    /// `context.<id>` attribute names, so it must be a legal identifier
    /// (`[_A-Za-z][_A-Za-z0-9]*`) — otherwise it would produce an invalid
    /// schema / policy that fails opaquely downstream.
    #[error("invalid distincter `{0}`: must be a Cedar identifier ([_A-Za-z][_A-Za-z0-9]*)")]
    InvalidDistincter(String),

    /// Partitioned temporal evaluation
    /// ([`partition_temporal`](crate::AuthorizerBuilder::partition_temporal)) was
    /// requested, but the installed temporal engine does not support it
    /// ([`supports_partitioning`](crate::engine::TemporalEngine::supports_partitioning)
    /// returned `false`). Failing closed here rather than silently falling back
    /// to global (relativized) semantics: the non-relativized leaves the caller
    /// asked to run are only correct under an engine that actually partitions.
    #[error(
        "partitioned temporal evaluation requested but the temporal engine does not support partitioning"
    )]
    PartitioningUnsupported,
}

// ─── The two lowering phases: parse -> lower ─────────────────────────

/// The output of the first lowering phase ([`parse`]): Dogwood source that has
/// been parsed and macro-expanded, but not yet lowered to Cedar.
///
/// It is the crate-internal payload of the public
/// [`ParsedPolicySet`](crate::policy_set::ParsedPolicySet). It carries the
/// [`ServiceSchema`] it was parsed against (macros + provider declarations +
/// the unbound event-schema DSL) so the second phase, [`lower`], needs only
/// the late input — the [`PolicySchema`] (action schema).
#[derive(Debug)]
pub(crate) struct Parsed {
    /// The parsed, macro-expanded surface policy set (extension leaves not yet
    /// hoisted).
    surface: crate::ast::PolicySet,
    /// The service schema this was parsed against — the second phase reads its
    /// provider declarations and event-schema DSL.
    service_schema: ServiceSchema,
    /// The original `.dw` source, shared so lowered nodes' `Loc`s and each
    /// fatal error can embed it and self-render.
    dw_src: std::sync::Arc<str>,
}

impl Parsed {
    /// The parsed, macro-expanded surface policies — read by the
    /// [`ParsedPolicySet`](crate::policy_set::ParsedPolicySet) diagnostic
    /// accessors to answer pre-lowering queries without exposing the AST.
    pub(crate) fn policies(&self) -> &[crate::ast::Policy] {
        &self.surface.policies
    }

    /// The service schema this set was parsed against — its provider
    /// declarations back the declared-vs-undeclared classification.
    pub(crate) fn service_schema(&self) -> &ServiceSchema {
        &self.service_schema
    }

    /// The shared `.dw` source, so a pre-lowering diagnostic accessor
    /// (e.g. [`ParsedPolicy::provider_invocations`](crate::policy_set::ParsedPolicy::provider_invocations))
    /// can pair an internal span-only error with the source to build a public,
    /// self-rendering [`Error`].
    pub(crate) fn dw_src(&self) -> &std::sync::Arc<str> {
        &self.dw_src
    }
}

/// Phase 1 — parse and macro-expand Dogwood `source` against the
/// [`ServiceSchema`] (macros + provider declarations). Catches syntax, macro,
/// and structural errors. Needs **no** action schema — schema-dependent checks
/// are deferred to [`lower`] / validation.
pub(crate) fn parse(source: &str, service_schema: &ServiceSchema) -> Result<Parsed, Error> {
    // Share the `.dw` source: it both stamps every lowered node's `Loc` (so
    // Cedar validation diagnostics rebase into the original source) and lets
    // each fatal error carry the source for self-rendering.
    let dw_src: std::sync::Arc<str> = std::sync::Arc::from(source);

    let mut surface =
        crate::parser::parse_policies(source).map_err(|errs| parse_errors(errs, &dw_src))?;

    // Merge the schema's macro library into the policy set's own `def`s before
    // expansion, so a policy can call a library macro without re-declaring it.
    // A `def` in the policy source takes precedence: only library macros whose
    // name the policy does not already define are added (so the library can
    // never shadow or duplicate a policy's own macro). The library is checked
    // against its *own* source here, so a library-def error self-renders
    // against the library — after which any error `expand` raises over the
    // merged set is necessarily policy-authored (stamped `dw_src` below).
    merge_macro_library(&mut surface, service_schema.macros())?;

    crate::macros::expand(&mut surface).map_err(|e| {
        Error::Macro(MacroError::new(
            e.message,
            SourceLoc::new(e.span, dw_src.clone()),
        ))
    })?;

    Ok(Parsed {
        surface,
        service_schema: service_schema.clone(),
        dw_src,
    })
}

/// Phase 2 — lower a [`Parsed`] set to Cedar against the [`PolicySchema`]
/// (action schema). This is where the event schema is **derived** against the
/// action schema, the policies are cedarified, the schema is augmented with the
/// hoisted `context.<id>` fields, pins are injected, and decision kinds are
/// computed. Produces the [`Lowered`] artifacts wrapped by
/// [`LoweredPolicySet`](crate::policy_set::LoweredPolicySet).
///
/// `distincter` namespaces this call's synthesized policy ids and hoisted
/// field names (see [`crate::cedarify::rule_key`]). Pass a distinct value per
/// call when the results are to be combined into one Cedar `PolicySet` / policy store
/// store or lowered incrementally over a shared augmented schema; pass `None`
/// for the standalone case (the ids fall back to `policy_<index>`).
pub(crate) fn lower(
    parsed: &Parsed,
    policy_schema: &PolicySchema,
    distincter: Option<&str>,
) -> Result<Lowered, Error> {
    let Parsed {
        surface,
        service_schema,
        dw_src,
    } = parsed;

    // The distincter is interpolated into synthesized policy ids and hoisted
    // `context.<id>` attribute names, so it must be a valid Cedar identifier
    // fragment — otherwise it silently produces an invalid schema / policy that
    // only fails later (at validation, Cedar `PolicySet` construction, or the policy store).
    // Reject a malformed one up front with a clear error. (`AnyId` also admits
    // Cedar keywords, which is harmless here since it is only a name fragment.)
    if let Some(d) = distincter
        && d.parse::<cedar_ast::AnyId>().is_err()
    {
        return Err(Error::InvalidDistincter(d.to_string()));
    }

    let action_schema_src = policy_schema.action_schema_src();
    let provider_declarations = service_schema.provider_declarations();

    // Derive the event schema against the action schema. This binds the
    // symbolic event-schema DSL (carried on the ServiceSchema, unbound) to the
    // concrete action schema — the one lowering step that needs both halves.
    let event_schema =
        derive(service_schema.event_schema(), action_schema_src).map_err(Error::EventSchema)?;

    let mut lowered = cedarify_with_providers(
        surface,
        action_schema_src,
        provider_declarations,
        distincter,
        dw_src,
    )
    .map_err(|e| cedarify_error(e, dw_src))?;

    // Drain the hoisted leaves by type to build the per-dialect leaf vecs.
    let mut context_fields = lowered
        .hoisted
        .take_leaves::<crate::cedarify::ContextField>();
    let provider_fields = lowered
        .hoisted
        .take_leaves::<crate::cedarify::ProviderField>();

    // Inject pinned fields (the schema's `pin f = context.…` correlations)
    // onto every matching predicate, after macro expansion so the pinned
    // field rides on the canonical leaf.
    for leaf in context_fields.iter_mut() {
        crate::event_schema::pin::inject_pins(&mut leaf.temporal.condition, &event_schema);
    }

    // Convert the loc-bearing `ast::PolicySet` into the public
    // `cedar_policy::PolicySet` for validation/authorization. This uses the
    // `#[doc(hidden)]` `TryFrom<ast::PolicySet>` impl. Upstream marks it hidden, so it
    // is not part of Cedar's supported surface and a minor release may remove it. There
    // is NO guard against that beyond the build failing to compile — this comment used
    // to claim a canary test protected it, and no such test has ever existed.
    let policies =
        CedarPolicySet::try_from(lowered.policy_set).map_err(|e| Error::PolicySet(Box::new(e)))?;

    let temporal: Vec<TemporalField> = context_fields
        .into_iter()
        .map(|f| TemporalField {
            id: f.field_name,
            action: action_scope(&f.action),
            target_actions: f
                .target_actions
                .iter()
                .map(|(ns, id)| action_ref(ns.clone(), id.clone()))
                .collect(),
            principal: f.principal.clone(),
            resource: f.resource.clone(),
            condition: f.temporal,
        })
        .collect();

    // Relativize each leaf for the schema's universal symmetric pins (the
    // "pinned ⇒ safe to partition" encoding). A no-op clone when the schema declares
    // no universal symmetric pin. The default is not such a case — it pins
    // `callerPrincipal` on every kind, so its leaves are relativized.
    let pins = crate::event_schema::relativize::universal_pins(&event_schema);
    let temporal_rewritten: Vec<TemporalField> = temporal
        .iter()
        .map(|f| TemporalField {
            id: f.id.clone(),
            action: f.action.clone(),
            target_actions: f.target_actions.clone(),
            principal: f.principal.clone(),
            resource: f.resource.clone(),
            condition: crate::extension::temporal::Temporal {
                condition: crate::event_schema::relativize::relativize_condition(
                    &f.condition.condition,
                    &event_schema,
                    &pins,
                ),
                span: f.condition.span,
            },
        })
        .collect();

    // The same universal symmetric pins expressed as engine-facing partition
    // keys. A partitioning temporal engine routes each event to a monitor keyed
    // by these fields and runs the NON-relativized `temporal` leaves within it —
    // the equivalent-but-cheaper alternative to the relativization rewrite. Empty
    // when the schema declares no universal symmetric pin (nothing to partition
    // on; `temporal` and `temporal_rewritten` are identical there anyway).
    let partition_keys: Vec<crate::engine::PartitionKey> = pins
        .iter()
        .map(|p| crate::engine::PartitionKey {
            // Route on the pinned *logged* field — the dataset μ matches
            // candidates on. `root`/`context_path` are retained for diagnostics
            // but are NOT the routing key (see `PartitionKey`).
            field_path: p.field_path.clone(),
            root: match p.root {
                crate::event_schema::ast::PinRoot::Scope => EventPinRoot::Scope,
                crate::event_schema::ast::PinRoot::Context => EventPinRoot::Context,
            },
            context_path: p.context_path.clone(),
        })
        .collect();

    // Resolve each hoisted provider field's declaration now (so the engine
    // carries the implementation and need not re-consult the declarations
    // file at authorize time).
    let providers = provider_fields
        .into_iter()
        .map(|f| {
            let declaration = provider_declarations
                .and_then(|d| d.get(&f.invocation.key()))
                .cloned();
            ProviderField {
                id: f.field_name,
                action: action_scope(&f.action),
                target_actions: f
                    .target_actions
                    .iter()
                    .map(|(ns, id)| action_ref(ns.clone(), id.clone()))
                    .collect(),
                invocation: f.invocation,
                methods: f.methods,
                body_base: f.body_base,
                declaration,
            }
        })
        .collect();

    // Compile the augmented schema from its fragment — an in-memory conversion
    // (no text re-parse). The fragment is retained on `Lowered` as the source
    // of truth for the text / JSON serializations.
    let augmented_schema_fragment = lowered.schema;
    let augmented_schema: Schema = augmented_schema_fragment
        .clone()
        .try_into()
        // `TryInto<Schema>` yields a `SchemaError`, which converts into a
        // `CedarSchemaError` (its `Schema` variant).
        .map_err(|e: cedar_policy::SchemaError| Error::CedarSchema(Box::new(e.into())))?;

    let decision_kinds = event_schema
        .decision_kinds()
        .into_iter()
        .map(str::to_string)
        .collect();

    Ok(Lowered {
        policies,
        augmented_schema,
        augmented_schema_fragment,
        temporal,
        temporal_rewritten,
        partition_keys,
        providers,
        rule_ids: lowered.rule_ids,
        rule_spans: lowered.rule_spans,
        dw_src: dw_src.clone(),
        event_schema,
        decision_kinds,
    })
}

/// Merge the macro-library `def`s into `surface.defs`, with the policy's own
/// `def`s taking precedence: a library macro is added only if the policy does
/// not already define a macro of that name. This keeps default-on macro
/// libraries safe — the library can neither shadow a policy's macro nor cause
/// a duplicate-definition error against one.
fn merge_macro_library(surface: &mut crate::ast::PolicySet, macros_src: &str) -> Result<(), Error> {
    if macros_src.trim().is_empty() {
        return Ok(());
    }
    // A macro library is Dogwood source with only `def`s (no policies); parse
    // it the same way and take its definitions. Both a parse error and a
    // macro-validity error (reserved / duplicate name, malformed body) carry
    // the *library* source (`lib_src`), not the policy source, so they
    // self-render against the right text. Validating the library here — rather
    // than letting the later `expand` pass fault on the merged set — is what
    // keeps that later error correctly attributable to the policy source.
    let lib_src: std::sync::Arc<str> = std::sync::Arc::from(macros_src);
    let library =
        crate::parser::parse_policies(macros_src).map_err(|errs| parse_errors(errs, &lib_src))?;
    crate::macros::check_defs(&library.defs).map_err(|e| {
        Error::Macro(MacroError::new(
            e.message,
            SourceLoc::new(e.span, lib_src.clone()),
        ))
    })?;
    let defined: std::collections::BTreeSet<&str> =
        surface.defs.iter().map(|d| d.name.as_str()).collect();
    let to_add: Vec<_> = library
        .defs
        .into_iter()
        .filter(|d| !defined.contains(d.name.as_str()))
        .collect();
    surface.defs.extend(to_add);
    Ok(())
}

/// Pair internal, span-only parse errors with the `.dw` source they came from,
/// producing the public self-rendering [`ParseErrors`]. The boundary where the
/// pipeline's shared `Arc<str>` source is injected into the public errors.
fn parse_errors(errs: Vec<RawParseError>, src: &std::sync::Arc<str>) -> Error {
    Error::Parse(ParseErrors::new(
        errs.into_iter()
            .map(|e| ParseError::new(e.message, SourceLoc::new(e.span, src.clone())))
            .collect(),
    ))
}

/// Pair an internal, span-only lowering error with its `.dw` source, producing
/// the public self-rendering [`CedarifyError`].
///
/// `pub(crate)` so a pre-lowering diagnostic accessor that reuses a
/// lowering-time conversion (e.g.
/// [`ParsedPolicy::provider_invocations`](crate::policy_set::ParsedPolicy::provider_invocations),
/// which extracts arguments via `cedar_call_to_invocation`) surfaces a rejected
/// argument through the very same public error channel `lower` uses.
pub(crate) fn cedarify_error(e: RawCedarifyError, src: &std::sync::Arc<str>) -> Error {
    let loc = e.span.map(|span| SourceLoc::new(span, src.clone()));
    Error::Cedarify(CedarifyError::new(e.message, loc))
}

// ─── The stateful decision runtime (behind `Authorizer`) ─────────────

/// Ingest one [`Event`]: hand it to the `temporal` engine (so it observes the
/// history), and — if the event's kind is a decision kind — evaluate the
/// temporal leaves, build the Cedar request, and decide via the `policy`
/// engine. Returns `None` for a history-only event.
///
/// Infallible: an evaluation failure (a provider that cannot run, the
/// temporal engine erroring, a decision event with no principal/resource in
/// scope) does not abort — it is folded into the
/// [`Response`](crate::authorize::Response)'s diagnostics with a fail-closed
/// `Deny`.
pub(crate) fn ingest(
    lowered: &Lowered,
    policy: &dyn crate::engine::PolicyEngine,
    temporal: &mut dyn crate::engine::TemporalEngine,
    resolver: Option<&dyn crate::engine::ProviderResolver>,
    event: &Event,
) -> Option<crate::authorize::Response> {
    // Every event is observed by the temporal engine, in order — this is what
    // maintains the history that temporal leaves see.
    temporal.observe(event);

    // A timepoint is a decision point iff its event kind is one the event
    // schema marked `decision`.
    if !lowered.decision_kinds.contains(&event.data().kind) {
        return None;
    }

    Some(decide_at(lowered, policy, temporal, resolver, event))
}

/// Decide the request for the current decision `event`, collecting any
/// evaluation errors into the response's diagnostics (fail-closed `Deny` on
/// error).
fn decide_at(
    lowered: &Lowered,
    policy: &dyn crate::engine::PolicyEngine,
    temporal: &mut dyn crate::engine::TemporalEngine,
    resolver: Option<&dyn crate::engine::ProviderResolver>,
    event: &Event,
) -> crate::authorize::Response {
    let mut errors: Vec<String> = Vec::new();

    // Temporal leaves: ask the temporal engine for each leaf's boolean at this
    // decision point. A failure fails the decision closed.
    let temporal_bindings = match temporal.evaluate() {
        Ok(b) => b,
        Err(message) => {
            errors.push(format!("temporal evaluation: {message}"));
            return crate::authorize::Response::deny_with_errors(errors);
        }
    };

    // Build the request context (input fields + temporal booleans + provider
    // outputs). A failure here — e.g. an information provider that errors at
    // runtime — is handled by DENYING the request, with the error in
    // diagnostics, rather than authorizing with an incomplete context (a
    // `permit` firing whose guard can no longer be checked). NOTE: this
    // fail-closed handling is this reference implementation's choice, not a
    // semantic guarantee. Under the provider contract (guide,
    // 05-information-providers) an erroring provider is UNDEFINED BEHAVIOR:
    // other implementations may avoid the error entirely (and reach a
    // different verdict), and policy sets must not rely on deny-on-error —
    // provider scripts are required to be defensive instead.
    let context = match build_context(&temporal_bindings, &lowered.providers, resolver, event) {
        Ok(ctx) => ctx,
        Err(message) => {
            errors.push(message);
            return crate::authorize::Response::deny_with_errors(errors);
        }
    };

    let request = match build_request(event.data(), event.scope(), context) {
        Ok(req) => req,
        Err(message) => {
            // No well-formed request — fail closed.
            errors.push(message);
            return crate::authorize::Response::deny_with_errors(errors);
        }
    };

    // Build the Cedar entity store: the scope principal/resource made present
    // (bare), plus any caller-supplied attributed entities validated against
    // the augmented schema. A conformance / attribute-evaluation failure MUST
    // fail closed — a policy evaluated against a store missing a required
    // attribute could mis-decide — so surface it as a Deny with the error in
    // diagnostics rather than authorizing against an ill-formed store.
    let entities = match build_entities(&request, event.data(), &lowered.augmented_schema) {
        Ok(e) => e,
        Err(message) => {
            errors.push(message);
            return crate::authorize::Response::deny_with_errors(errors);
        }
    };

    let mut response = decide(lowered, policy, &request, &entities);
    response.push_errors(errors);
    response
}

/// The shared decision core: authorize `request` through the `policy` engine,
/// mapping the determining policy ids back to Dogwood rule references via the
/// lowered `rule_ids`.
fn decide(
    lowered: &Lowered,
    policy: &dyn crate::engine::PolicyEngine,
    request: &Request,
    entities: &Entities,
) -> crate::authorize::Response {
    // `entities` already carries the caller-supplied attributed entities, the
    // bare scope entities, AND the schema's action-hierarchy entities (all
    // merged by `build_entities`), so `principal.<attr>` reads and
    // `action in [Group]` membership both resolve from one store.
    let decision = policy.is_authorized(crate::engine::AuthorizationRequest { request, entities });

    let determining_policies = decision
        .determining_policy_ids
        .iter()
        .filter_map(|id| {
            lowered
                .rule_ids
                .iter()
                .position(|rid| rid == id)
                .map(|rule_index| DogwoodRuleRef {
                    rule_index,
                    cedar_policy_id: id.clone(),
                })
        })
        .collect();

    crate::authorize::Response::new(decision.decision, determining_policies, decision.errors)
}

/// Build the Cedar entity store for a decision, from two sources with two
/// different trust levels:
///
///   1. **Caller-supplied attributed entities** (`event.entities`, from
///      [`EventBuilder::entity`](crate::EventBuilder::entity) / a `.log`
///      `entities(...)` envelope). These are validated against the augmented
///      `schema` — a wrong-typed or (for a `required`-attr type) incomplete
///      entity is a build-time error, folded into a fail-closed Deny. A caller
///      opting an entity into the attribute channel opts into supplying its
///      required attributes.
///   2. **Bare scope entities** — the request's principal and resource, added
///      attribute-less and **without** schema conformance, *only* for uids the
///      caller did not already supply in (1). A bare uid-only entity cannot
///      satisfy a schema-declared `required` attribute, so conformance-checking
///      it would reject essentially every request; instead it is added
///      unchecked, purely to make the scope entity *present* (so identity
///      comparisons and `.id`/`.type` reads never hit "entity does not exist").
///   3. **Action-hierarchy entities** — the schema's action entities and their
///      `memberOf` edges, so a scope testing action membership
///      (`action in [Group]`) resolves: Cedar reads those edges from the entity
///      store, not the schema, so without them `action in [Group]` never
///      matches a descendant action and the rule silently never fires.
///
/// Returns `Err` on a conformance / attribute-evaluation failure in (1); the
/// caller fails the decision closed.
fn build_entities(
    request: &Request,
    event: &EventData,
    schema: &Schema,
) -> Result<Entities, String> {
    // (1) Caller-supplied attributed entities (with their direct parents),
    // schema-validated.
    let supplied: Vec<cedar_policy::Entity> = event
        .entities
        .iter()
        .map(|(uid, rec)| build_entity(uid, rec))
        .collect::<Result<_, _>>()?;
    let supplied_uids: BTreeSet<&str> = event.entities.keys().map(String::as_str).collect();
    let store = Entities::from_entities(supplied, Some(schema))
        .map_err(|e| format!("entity conformance: {e}"))?;

    // (2) Bare scope entities for any scope uid not already supplied, added
    // without conformance (a uid-only entity cannot satisfy required attrs).
    let bare: Vec<cedar_policy::Entity> = [request.principal(), request.resource()]
        .into_iter()
        .flatten()
        .filter(|uid| !supplied_uids.contains(uid.to_string().as_str()))
        .map(|uid| cedar_policy::Entity::with_uid(uid.clone()))
        .collect();
    let store = store
        .add_entities(bare, None)
        .map_err(|e| format!("scope entities: {e}"))?;

    // (3) The schema's action-hierarchy entities, so `action in [Group]`
    // resolves. Merged into the same store as the supplied/scope entities
    // (rather than replacing it) so attribute reads and action membership both
    // work; falls back to the store as-is on the (unexpected) error path so a
    // decision is still made.
    let action_entities = schema
        .action_entities()
        .map_err(|e| format!("action entities: {e}"))?;
    store
        .add_entities(action_entities, None)
        .map_err(|e| format!("action hierarchy: {e}"))
}

/// Build one caller-supplied [`cedar_policy::Entity`] from its uid string and
/// its [`EntityRecord`] (attributes + direct parents). Attribute values reuse
/// the same `Value -> RestrictedExpression` mapping the context path uses
/// ([`value_to_expr`]); direct parents become the entity's `memberOf` edges so
/// `principal in Group` resolves (Cedar computes the transitive closure).
fn build_entity(uid: &str, rec: &EntityRecord) -> Result<cedar_policy::Entity, String> {
    let uid = EntityUid::from_str(uid).map_err(|e| format!("bad entity uid `{uid}`: {e}"))?;
    let attrs: std::collections::HashMap<String, RestrictedExpression> = rec
        .attrs
        .iter()
        // A caller-supplied `Value::Null` means "not provided": treat it as
        // attribute-absent (drop it) rather than routing it through
        // `value_to_expr`, whose `Null` arm yields an empty string. That
        // coercion would let a `Null` for a schema-declared `String` attribute
        // pass conformance (empty string is a valid String) and be stored as
        // `""`, so `principal.<attr> == ""` would silently match — the
        // fail-closed invariant the entity store is built on. Dropping it lets
        // conformance treat the attribute as it actually is: a missing
        // *required* attribute fails closed; a missing *optional* one is simply
        // absent (`has` is false). (Only `build_entity` filters `Null`;
        // `value_to_expr`'s behavior for the context path is unchanged.)
        .filter(|(_, v)| !matches!(v, Value::Null))
        .map(|(k, v)| (k.clone(), value_to_expr(v)))
        .collect();
    // Direct parents (`memberOf`). Each parent Value is an entity-ref; format it
    // to its uid string and parse to an EntityUid. A malformed/unsupported
    // parent ref fails closed (same policy as a bad attribute).
    let parents: std::collections::HashSet<EntityUid> = rec
        .parents
        .iter()
        .filter_map(value_uid_string)
        .map(|s| EntityUid::from_str(&s).map_err(|e| format!("bad parent uid `{s}`: {e}")))
        .collect::<Result<_, _>>()?;
    cedar_policy::Entity::new(uid, attrs, parents).map_err(|e| format!("entity attribute: {e}"))
}

// ─── Building a Cedar request from a Dogwood event ───────────────────

/// Build the Cedar request context for the current decision `event`: the
/// event's **request-only context** (`request_context` — `input`, `system`,
/// …), the temporal booleans supplied by the temporal engine, and every
/// hoisted provider output.
///
/// Reads *only* `request_context` from the event — **nothing from `logged`**.
/// The two datasets are fully separated: the logged fields are the durable
/// temporal record; the Cedar request is built solely from the request-only
/// context plus the hoisted fields this composes. A field the request and
/// temporal both need (`input`) is supplied in both `request_context` and
/// `logged`, by design.
fn build_context(
    temporal_bindings: &BTreeMap<String, bool>,
    providers: &[ProviderField],
    resolver: Option<&dyn crate::engine::ProviderResolver>,
    event: &Event,
) -> Result<Context, String> {
    let data = event.data();

    // Every request-only context group (`input`, `system`, …) flows to Cedar
    // as `context.<group>`, verbatim.
    let mut pairs: Vec<(String, RestrictedExpression)> = data
        .request_context
        .iter()
        .map(|(k, v)| (k.clone(), value_to_expr(v)))
        .collect();

    for (id, holds) in temporal_bindings {
        pairs.push((id.clone(), RestrictedExpression::new_bool(*holds)));
    }

    if !providers.is_empty() {
        // Provider execution is UNCONDITIONAL: every declared provider field
        // is evaluated for every decision event, whatever the event's action
        // or scope entities. This is the documented semantics (see the
        // provider contract in the guide, 05-information-providers): a
        // provider must be pure and defensive — an argument that does not
        // resolve on this event arrives as Null, and an erroring provider is
        // UB. There is deliberately NO applicability gate here: deciding
        // whether a rule's scope could match the event would re-implement
        // Cedar's scope semantics (the source of the historical `in Group`
        // silent-never-fires bug). Cedar alone decides which policies fire;
        // the hoisted outputs are just context enrichment, declared on every
        // action by `add_provider_context_fields`.
        let mut provider_outputs: BTreeMap<String, Value> = BTreeMap::new();
        for field in providers {
            let value = eval_provider(field, resolver, data)?;
            provider_outputs.insert(field.id.clone(), value);
        }
        pairs.push((
            "providers".to_string(),
            value_to_expr(&Value::Object(provider_outputs)),
        ));
    }

    Context::from_pairs(pairs).map_err(|e| format!("context build: {e}"))
}

/// Evaluate an information-provider invocation against the request `event`.
///
/// A caller-supplied [`ProviderResolver`](crate::engine::ProviderResolver) is
/// consulted first: if it handles this provider it supplies the value (this is
/// how a provider whose value comes from outside the sandbox — a service, a
/// model — is computed). Otherwise the built-in sandboxed Rhai implementation
/// runs.
fn eval_provider(
    field: &ProviderField,
    resolver: Option<&dyn crate::engine::ProviderResolver>,
    event: &EventData,
) -> Result<Value, String> {
    let args: Vec<Value> = field
        .invocation
        .args
        .iter()
        .map(|a| resolve_provider_arg(a, event))
        .collect();

    // Stage 1 — the BASE output. The resolver gets first refusal; otherwise
    // the declared Rhai `evaluate` runs. Either way this is the value the
    // method chain (if any) post-processes.
    let base = if let Some(resolver) = resolver
        && let Some(result) = resolver.resolve(crate::engine::ProviderRequest {
            name: &field.invocation.function,
            args: &args,
        }) {
        result?
    } else {
        // Fall back to the declared, sandboxed Rhai implementation.
        let key = field.invocation.key();
        let decl = field.declaration.as_ref().ok_or_else(|| {
            format!(
                "provider `{key}` was not declared (no entry in the providers declarations), \
                 so it has no implementation to evaluate"
            )
        })?;
        crate::extension::provider::eval::evaluate(&field.invocation, decl, &args)?
    };

    // Stage 2 — the eager method chain, `mₙ(…m₁(base, a₁)…, aₙ)`. Each method
    // is a `fn <name>(input, args…)` in the provider's Rhai script; the value
    // threads left to right. A method-free field returns `base` unchanged
    // (backward compatible). Methods run only via the built-in Rhai
    // implementation — a resolver supplies the base, not the method bodies —
    // so a declaration/script is required once a chain is present.
    if field.methods.is_empty() {
        return Ok(base);
    }
    let key = field.invocation.key();
    let decl = field.declaration.as_ref().ok_or_else(|| {
        format!("provider `{key}` has a method chain but is not declared, so its methods cannot be evaluated")
    })?;
    let resolved: Vec<(&str, Vec<Value>)> = field
        .methods
        .iter()
        .map(|m| {
            let margs = m
                .args
                .iter()
                .map(|a| resolve_provider_arg(a, event))
                .collect();
            (m.name.as_str(), margs)
        })
        .collect();
    crate::extension::provider::eval::run_methods(&field.invocation.key(), decl, base, &resolved)
}

/// Resolve one provider invocation argument to a [`Value`] against the
/// request event.
///
/// An [`Arg::Field`] path is rooted at `context`, `principal`, or `resource`
/// (the parser guarantees this):
///   * `context.<a>.<b>…` reads the request **context** record
///     (`request_context`) by nested field path — the same bag the Cedar
///     request context and temporal `context.<path>` read, never the logged
///     temporal record.
///   * `principal` / `resource` read the request scope entity (carried on the
///     event as the reserved `callerPrincipal` / `callerResource` fields),
///     with attributes from the entity store; a trailing `.id` / `.type`
///     projects that entity's id or type, matching Cedar's entity attributes.
///
/// An unresolvable path yields [`Value::Null`] (a provider that cannot read a
/// field sees an absent value rather than failing the whole decision).
fn resolve_provider_arg(arg: &crate::extension::provider::ast::Arg, event: &EventData) -> Value {
    use crate::extension::provider::ast::Arg;
    match arg {
        Arg::Field(path) => resolve_field_path(path, event),
        Arg::String(s) => Value::String(s.clone()),
        Arg::Integer(n) => Value::Int(*n),
        Arg::Decimal(s) => Value::Decimal(s.clone()),
        Arg::Bool(b) => Value::Bool(*b),
        Arg::Set(items) => Value::Array(
            items
                .iter()
                .map(|a| resolve_provider_arg(a, event))
                .collect(),
        ),
    }
}

/// Resolve an attribute path (`["context","input","x"]`, `["principal","id"]`,
/// …) against the request event.
fn resolve_field_path(path: &[String], event: &EventData) -> Value {
    match path.first().map(String::as_str) {
        Some("principal") => resolve_scope_path("callerPrincipal", &path[1..], event),
        Some("resource") => resolve_scope_path("callerResource", &path[1..], event),
        // `context.<a>.<b>…` — strip the leading `context` root(s) and descend
        // the request **context** record. This reads `request_context`, the same
        // bag the Cedar request context is built from (`build_context`) and the
        // temporal `context.<path>` env resolves against — so all three
        // consumers agree on what "the current request's context" is, never
        // reaching into the logged temporal record. (A bare leaf falls back to a
        // flat request-context lookup, preserving the prior behavior for
        // single-segment paths.)
        _ => {
            let nested: Vec<String> = path
                .iter()
                .skip_while(|seg| seg.as_str() == "context")
                .cloned()
                .collect();
            event
                .request_context_path(&nested)
                .or_else(|| {
                    let leaf = path.last().map(String::as_str).unwrap_or_default();
                    event.request_context_field(leaf)
                })
                .cloned()
                .unwrap_or(Value::Null)
        }
    }
}

/// Resolve a `principal` / `resource` path: read the reserved scope entity
/// field, then project an attribute path off it via the shared
/// [`EventData::resolve_entity_attr`] resolver. A bare root (`principal` with
/// no attribute) returns the whole entity; an attribute path defers to the
/// shared resolver (supplied-attr-wins, `.id`/`.type` uid projection, nested
/// descent, absent → `None`), mapping absent to [`Value::Null`].
pub(crate) fn resolve_scope_path(reserved: &str, rest: &[String], event: &EventData) -> Value {
    let Some(entity) = event.field(reserved) else {
        return Value::Null;
    };
    let Value::Entity { ty, id } = entity else {
        return Value::Null;
    };
    if rest.is_empty() {
        // Bare `principal` / `resource` — the whole entity value.
        return entity.clone();
    }
    // The attribute path shares one resolver with the temporal env seeder
    // (`seed_scope_env`) via [`EventData::resolve_entity_attr`]: supplied
    // attribute wins, `.id`/`.type` project the uid, nested paths descend, and
    // an absent attribute is `None`. A provider that cannot read a field sees
    // an absent value (`Null`) rather than failing the whole decision; the
    // schema-conformance check on the Cedar path is where a genuinely-required
    // attribute surfaces as an error. This leniency is load-bearing under the
    // provider contract (guide, 05-information-providers): providers run
    // unconditionally, so absent fields are an EXPECTED input that defensive
    // scripts turn into a sentinel — not an error path.
    event
        .resolve_entity_attr(ty, id, rest)
        .unwrap_or(Value::Null)
}

/// Build a Cedar `Request` from an event's scope + payload + context.
/// Principal and resource come from the labeled scope (not event fields);
/// the action is reconstructed from the event's stored namespace path and id.
/// A decision-point event without a principal or resource in its scope is an
/// error rather than a silently fabricated request.
fn build_request(event: &EventData, scope: &Scope, context: Context) -> Result<Request, String> {
    use crate::interpreter::value::value_uid_string;
    let principal = scope
        .principal
        .as_ref()
        .and_then(value_uid_string)
        .ok_or_else(|| "decision event has no principal in scope".to_string())?;
    let resource = scope
        .resource
        .as_ref()
        .and_then(value_uid_string)
        .ok_or_else(|| "decision event has no resource in scope".to_string())?;
    let action = qualified_action_uid(&event.namespace, &event.action);

    // A malformed principal / action / resource UID must fail closed: parsing
    // it into a fabricated fallback entity would silently authorize the
    // request against the wrong entity. Surface the parse error instead (the
    // caller turns it into a fail-closed Deny with the error in diagnostics).
    let principal = parse_uid_checked(&principal)?;
    let action = parse_uid_checked(&action)?;
    let resource = parse_uid_checked(&resource)?;

    Request::new(principal, action, resource, context, None)
        .map_err(|e| format!("request build: {e}"))
}

// ─── `.log` trace ingestion (behind `parse_trace` / `replay_log`) ────

/// Build a request-kind [`Event`] by unmarshalling a Cedar `Request`. The
/// principal/resource go into the labeled scope (what `build_request` reads
/// to authorize); copies are also placed in the event's
/// `callerPrincipal` / `callerResource` fields so a policy that binds
/// those to correlate explicitly can read them.
pub(crate) fn request_to_event(ts: i64, request: &Request) -> Result<Event, Error> {
    let action_uid = request.action().ok_or(Error::RequestMissingAction)?;
    let (namespace, action) = split_action_uid(&action_uid.to_string());

    let mut scope = Scope::default();
    // A Cedar `Request`'s context IS request data, so its groups populate
    // `request_context` (what `build_context` reads). The principal/resource
    // aliases are logged (identity/correlation), and the `input` group is
    // mirrored into `logged` too so a replayed request participates in temporal
    // history exactly as a native event would (temporal predicates correlate on
    // `input.*`).
    let mut logged: BTreeMap<String, Value> = BTreeMap::new();
    let mut request_context: BTreeMap<String, Value> = BTreeMap::new();
    if let Some(p) = request.principal()
        && let Some(v) = crate::interpreter::value::uid_to_value(&p.to_string())
    {
        scope.principal = Some(v.clone());
        logged.insert("callerPrincipal".to_string(), v);
    }
    if let Some(r) = request.resource()
        && let Some(v) = crate::interpreter::value::uid_to_value(&r.to_string())
    {
        scope.resource = Some(v.clone());
        logged.insert("callerResource".to_string(), v);
    }
    if let Some(ctx) = request.context() {
        let json = ctx
            .to_json_value()
            .map_err(|e| Error::ContextRead(e.to_string()))?;
        if let serde_json::Value::Object(groups) = &json {
            for (group, val) in groups {
                let converted = json_to_value(val);
                // Every context group is request data.
                request_context.insert(group.clone(), converted.clone());
                // `input` is also logged, for temporal correlation.
                if group == "input" {
                    logged.insert("input".to_string(), converted);
                }
            }
        }
    }

    Ok(Event::from_parts(
        ts,
        scope,
        EventData {
            namespace,
            action,
            kind: "request".to_string(),
            logged,
            request_context,
            // A Cedar `Request` carries no entities (Cedar keeps them in a
            // separate `Entities` store), so this bridge supplies none; the
            // scope principal/resource are still made present at decision time.
            entities: BTreeMap::new(),
        },
    ))
}

// ─── small mappings between cedarify shapes and the public leaf types ─

fn action_ref(namespace: String, id: String) -> ActionRef {
    ActionRef {
        namespace: if namespace.is_empty() {
            None
        } else {
            Some(namespace)
        },
        id,
    }
}

/// Map the lowering's `cedarify::ScopedAction` to [`ActionScope`],
/// preserving all three cases.
fn action_scope(scope: &crate::cedarify::ScopedAction) -> ActionScope {
    use crate::cedarify::ScopedAction;
    let to_ref = |(ns, id): &(String, String)| action_ref(ns.clone(), id.clone());
    match scope {
        ScopedAction::Concrete(a) => ActionScope::Concrete(to_ref(a)),
        ScopedAction::List(v) => ActionScope::List(v.iter().map(to_ref).collect()),
        ScopedAction::Unconstrained => ActionScope::Unconstrained,
    }
}

// ─── small value/uid conversions ────────────────────────────────────

/// Reconstruct the Cedar action UID from an event's stored namespace path
/// and id, e.g. `["Drupe","Action"]` + `Login` => `Drupe::Action::"Login"`.
fn qualified_action_uid(namespace: &[String], action: &str) -> String {
    // Escape the action id to Cedar's canonical form (same `escape_debug` as
    // `entity_uid_string`), so an id with control chars / whitespace / quotes
    // produces a literal `EntityUid::from_str` accepts. Without this a
    // non-canonical action id fails closed ("needs to be normalized") — the
    // dominant residual gap when replaying Cedar-corpus requests.
    let id = action.escape_debug();
    if namespace.is_empty() {
        format!("Action::\"{id}\"")
    } else {
        format!("{}::\"{id}\"", namespace.join("::"))
    }
}

/// Split a Cedar action UID string `Ns::Sub::"Id"` into its namespace path
/// and id, decoding the id with the **same** decoder as the entity path
/// ([`uid_to_value`]) so the action and entity uid round-trips can never drift
/// apart. `uid_to_value` uses `find("::\"")` (the *first* `::"`, so a `::`
/// inside the id body is not mistaken for the type/id separator) and
/// `strip_suffix('"')` (removes *exactly one* closing quote, so an id ending in
/// an escaped quote `\"` keeps its `"`). An earlier hand-rolled variant used
/// `rfind` + `trim_end_matches('"')`, which diverged for ids ending in `::` or
/// `"` — decoding them to the wrong `(namespace, id)` and, once re-rendered by
/// [`qualified_action_uid`], silently mis-matching the action scope. A string
/// that is not of `Ns::"id"` shape falls back to the whole string as a bare id.
fn split_action_uid(s: &str) -> (Vec<String>, String) {
    match crate::interpreter::value::uid_to_value(s) {
        Some(Value::Entity { ty, id }) => {
            let namespace = ty.split("::").map(|p| p.to_string()).collect();
            (namespace, id)
        }
        _ => (Vec::new(), s.to_string()),
    }
}

/// Parse a Cedar entity UID, failing closed on a malformed string. Used for
/// the request's principal / action / resource, where substituting a
/// fabricated fallback would silently authorize against the wrong entity.
fn parse_uid_checked(s: &str) -> Result<EntityUid, String> {
    EntityUid::from_str(s).map_err(|e| format!("malformed entity uid `{s}`: {e}"))
}

/// Parse a Cedar entity UID for a *context attribute value*, substituting a
/// sentinel fallback on a malformed string. Unlike the request's
/// principal/resource (see [`parse_uid_checked`]), a context value cannot
/// fail the whole request closed here — it is one attribute among many — so a
/// bad value degrades to the sentinel and any policy comparing against it
/// simply won't match.
fn parse_uid(s: &str) -> EntityUid {
    EntityUid::from_str(s).unwrap_or_else(|_| {
        EntityUid::from_str("Drupe::Gateway::\"unknown\"").expect("fallback uid parses")
    })
}

fn json_to_value(v: &serde_json::Value) -> Value {
    match v {
        serde_json::Value::Null => Value::Null,
        serde_json::Value::Bool(b) => Value::Bool(*b),
        serde_json::Value::Number(n) => {
            if let Some(i) = n.as_i64() {
                Value::Int(i)
            } else {
                Value::Decimal(n.to_string())
            }
        }
        serde_json::Value::String(s) => Value::String(s.clone()),
        serde_json::Value::Array(a) => Value::Array(a.iter().map(json_to_value).collect()),
        serde_json::Value::Object(o) => {
            // Cedar's JSON value encoding uses reserved single-key escapes for
            // entity refs and extension values (the form `Context::to_json_value`
            // and `entities.json` produce). Recognize them so an entity-typed or
            // decimal context field / attribute round-trips to the right `Value`
            // rather than a plain record (which would make `principal.<attr>`
            // read a record where the policy expects an entity/decimal).
            if let Some(v) = cedar_escape_to_value(o) {
                return v;
            }
            Value::Object(
                o.iter()
                    .map(|(k, v)| (k.clone(), json_to_value(v)))
                    .collect(),
            )
        }
    }
}

/// Recognize Cedar's reserved JSON value escapes, else `None` (a plain record):
///
/// - `{"__entity": {"type": T, "id": I}}` → [`Value::Entity`];
/// - `{"__extn": {"fn": "decimal", "arg": A}}` → [`Value::Decimal`] (its text).
///
/// `ip` / `datetime` / `duration` extension values are NOT yet modeled by
/// [`Value`] (no variant), so they fall through to `None` and are carried as the
/// raw `__extn` record for now — a documented gap until a `Value` extension
/// variant lands. Only a *single-key* object with the exact inner shape is
/// treated as an escape, matching Cedar (a genuine record with a member literally
/// named `__entity`/`__extn` but a different shape stays a record).
fn cedar_escape_to_value(o: &serde_json::Map<String, serde_json::Value>) -> Option<Value> {
    if o.len() != 1 {
        return None;
    }
    if let Some(ent) = o.get("__entity").and_then(|e| e.as_object()) {
        let ty = ent.get("type").and_then(|v| v.as_str())?;
        let id = ent.get("id").and_then(|v| v.as_str())?;
        return Some(Value::Entity {
            ty: ty.to_string(),
            id: id.to_string(),
        });
    }
    if let Some(extn) = o.get("__extn").and_then(|e| e.as_object()) {
        let f = extn.get("fn").and_then(|v| v.as_str())?;
        let arg = extn.get("arg").and_then(|v| v.as_str())?;
        return match f {
            "decimal" => Some(Value::Decimal(arg.to_string())),
            // ip / datetime / duration: no Value variant yet (increment #3).
            _ => None,
        };
    }
    None
}

fn value_to_expr(v: &Value) -> RestrictedExpression {
    match v {
        Value::Bool(b) => RestrictedExpression::new_bool(*b),
        Value::Int(n) => RestrictedExpression::new_long(*n),
        Value::String(s) => RestrictedExpression::new_string(s.clone()),
        Value::Decimal(s) => RestrictedExpression::new_decimal(s.clone()),
        Value::Entity { ty, id } => RestrictedExpression::new_entity_uid(parse_uid(
            &crate::interpreter::value::entity_uid_string(ty, id),
        )),
        Value::Array(items) => RestrictedExpression::new_set(items.iter().map(value_to_expr)),
        Value::Object(map) => {
            let pairs: Vec<(String, RestrictedExpression)> = map
                .iter()
                .map(|(k, v)| (k.clone(), value_to_expr(v)))
                .collect();
            RestrictedExpression::new_record(pairs)
                .unwrap_or_else(|_| RestrictedExpression::new_string(String::new()))
        }
        Value::Null => RestrictedExpression::new_string(String::new()),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// `split_action_uid ∘ qualified_action_uid` is the identity on
    /// `(namespace, id)` for arbitrary ids — including the adversarial shapes
    /// (`"`, `\`, `::`, control chars, empty) Cedar permits as an `EntityId`.
    /// This is the property that the entity path already guards
    /// (`log_parse::unescape_inverts_entity_uid_escaping`); the action path had
    /// no equivalent and so regressed to a divergent hand-rolled decoder.
    #[test]
    fn action_uid_render_split_round_trips() {
        let cases: &[(&[&str], &str)] = &[
            (&["Svc", "Action"], "Read"),
            (&["Action"], "Read"),           // namespace-less
            (&["Svc", "Action"], "a\"b"),    // interior quote
            (&["Svc", "Action"], "a\""),     // TRAILING quote (was buggy)
            (&["Svc", "Action"], "a::b"),    // interior `::`
            (&["Svc", "Action"], "a::"),     // trailing `::` (was buggy)
            (&["Svc", "Action"], "a\\b"),    // backslash
            (&["Svc", "Action"], "a\\"),     // trailing backslash
            (&["Svc", "Action"], "a\u{e}b"), // control char
            (&["Svc", "Action"], ""),        // empty id
            (&["Svc", "Action"], "\""),      // id is a lone quote
        ];
        for (ns, id) in cases {
            let ns_owned: Vec<String> = ns.iter().map(|s| s.to_string()).collect();
            let rendered = qualified_action_uid(&ns_owned, id);
            let (got_ns, got_id) = split_action_uid(&rendered);
            assert_eq!(
                (&got_ns, got_id.as_str()),
                (&ns_owned, *id),
                "action uid round-trip failed for ns={ns:?} id={id:?} (rendered {rendered:?})"
            );
        }
    }

    /// Pin the cross-crate coupling the whole string-keyed entity store rests on:
    /// `entity_uid_string(ty, id)` must be byte-identical to Cedar's own uid
    /// rendering (`EntityUid: Display`), because a decision-time lookup
    /// reconstructs the store key by re-escaping a decoded `(ty, id)`. If a
    /// future `cedar_policy` (or Rust `escape_debug`) changed escaping, the keys
    /// would silently desync and attribute/parent reads would miss — fail-closed
    /// wrong decisions with nothing in diagnostics. Rendering via Cedar's own
    /// `from_type_name_and_id` (the structural constructor) is the source of truth.
    #[test]
    fn entity_uid_string_matches_cedar_rendering() {
        use cedar_policy::{EntityId, EntityTypeName, EntityUid};
        use std::str::FromStr;
        let cases: &[(&str, &str)] = &[
            ("Svc::User", "alice"),
            ("Svc::User", "a\"b"),    // quote
            ("Svc::User", "a\\b"),    // backslash
            ("Svc::User", "a\u{e}b"), // control char
            ("Svc::User", "a b"),     // space
            ("A", ""),                // empty id
        ];
        for (ty, id) in cases {
            let ours = crate::interpreter::value::entity_uid_string(ty, id);
            let cedar = EntityUid::from_type_name_and_id(
                EntityTypeName::from_str(ty).expect("type name"),
                EntityId::new(*id),
            )
            .to_string();
            assert_eq!(
                ours, cedar,
                "entity_uid_string diverged from Cedar's rendering for ty={ty:?} id={id:?}"
            );
        }
    }
}
