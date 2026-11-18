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

use dogwood_syntax::NodeBudget;

use crate::authorize::DogwoodRuleRef;
use crate::cedarify::cedarify_with_providers;
use crate::error::{
    CedarifyError, MacroError, ParseError, ParseErrors, RawCedarifyError, RawParseError, SourceLoc,
};
use crate::event_schema::derive::{DerivedEventSchema, derive};
use crate::extension::temporal::Temporal;
use crate::interpreter::value::{EntityRecord, Event, EventData, Scope, Value, value_uid_string};
use crate::policy_schema::PolicySchema;
use crate::policy_set::Distincter;
use crate::service_schema::ServiceSchema;

/// Which stages of the frontend ran, on each thread (tests only): every stage's
/// function records its name on entry, so that a test can check that a function
/// runs only the stages it should (the export's inputs, the parsers alone).
#[cfg(test)]
pub(crate) mod stage_probe {
    use std::cell::RefCell;

    thread_local! {
        static STAGES: RefCell<Vec<&'static str>> = const { RefCell::new(Vec::new()) };
    }

    /// Record that `stage` ran on this thread.
    pub(crate) fn enter(stage: &'static str) {
        STAGES.with(|s| s.borrow_mut().push(stage));
    }

    /// The stages that ran on this thread since the last call, in order.
    /// Read only by the `frontend_export` tests, so gated like that module.
    #[cfg(any(feature = "frontend-export", feature = "lean-frontend"))]
    pub(crate) fn take() -> Vec<&'static str> {
        STAGES.with(|s| std::mem::take(&mut *s.borrow_mut()))
    }
}

/// The JSON export of the frontend's inputs and stage observables, for
/// differential testing (feature `frontend-export`). A child of this module so
/// that it can run each lowering step on its own.
#[cfg(any(feature = "frontend-export", feature = "lean-frontend"))]
#[cfg_attr(not(feature = "frontend-export"), allow(dead_code))]
pub mod frontend_export;

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

    /// **The scope a leaf of a rule scoped by `self` is sent under for
    /// `action`**, or `None` when the rule cannot apply to it. `groups` are the
    /// groups whose scope resolves to `action`
    /// ([`LoweredPolicySet::action_groups`](crate::LoweredPolicySet::action_groups)),
    /// looked up once per action and shared by every leaf.
    ///
    /// * An unconstrained scope applies, as it is.
    /// * A concrete scope applies when it names `action`, as it is.
    /// * A list applies when it names `action` or one of `groups`, narrowed to
    ///   [`Concrete`](ActionScope::Concrete)`(action)`: a leaf's verdict does
    ///   not depend on its scope, which only says which actions the leaf is
    ///   validated against, and a leaf valid for every action of the list is
    ///   valid for `action` among them.
    ///
    /// [`LoweredPolicySet::temporal_slice`](crate::LoweredPolicySet::temporal_slice)
    /// selects and describes its leaves by this rule, so a caller that holds
    /// leaves and no policies selects the same leaves under the same scopes.
    pub fn narrowed_to(&self, action: &ActionRef, groups: &[ActionRef]) -> Option<ActionScope> {
        match self {
            ActionScope::Unconstrained => Some(ActionScope::Unconstrained),
            ActionScope::Concrete(a) => (a == action).then(|| self.clone()),
            ActionScope::List(listed) => listed
                .iter()
                .any(|a| a == action || groups.contains(a))
                .then(|| ActionScope::Concrete(action.clone())),
        }
    }
}

// ─── Hoisted extension leaves ───────────────────────────────────────

/// A temporal leaf hoisted out of a policy: a stream monitor evaluated
/// against the event history and bound (as a bool) into `context.<id>`.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
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

impl TemporalField {
    /// A **position-free name** for this leaf: the SHA-256 (lowercase hex) of
    /// its canonical content — the condition (with binders alpha-normalized and
    /// spans dropped), the action scope and the concrete actions it resolves
    /// to, and what the principal / resource scopes admit. Excludes the field
    /// name [`id`](TemporalField::id), the rule it came from and the rule's
    /// position.
    ///
    /// Two leaves with equal hashes compute the same verdict over the same
    /// history, so a temporal engine may key its per-leaf state by this hash
    /// rather than by `id`: the state then follows the leaf when rules are
    /// reordered, inserted or removed, and two rules that share a leaf share
    /// its state. (`id` stays positional for compatibility; see
    /// [`IdSource`](crate::IdSource).) The relativized and non-relativized
    /// forms of a leaf have different conditions, hence different hashes.
    pub fn content_hash(&self) -> String {
        crate::identity::temporal_field_hash(self)
    }
}

/// **One temporal leaf as a caller that lowers the policies elsewhere sends it**
/// to an evaluator of temporal fields: the leaf's id, its rule's action scope
/// (narrowed to one action for a rule over an action list), and its condition
/// as authored (after macro expansion, before pin injection)
/// in its canonical text ([`temporal_ast::condition_text`](crate::temporal_ast::condition_text)).
/// The evaluator parses the text ([`temporal_ast::parse_condition`](crate::temporal_ast::parse_condition)),
/// which gives the authored condition again, and injects the event schema's
/// pins itself, as lowering does. [`LoweredPolicySet::temporal_slice`](crate::LoweredPolicySet::temporal_slice)
/// makes them.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TemporalLeafDescriptor {
    /// The leaf's id ([`TemporalField::id`]): the `context.<id>` its rule reads.
    pub id: ExtensionId,
    /// The action scope the leaf is sent under: its rule's scope when that is
    /// [`ActionScope::Concrete`] or [`ActionScope::Unconstrained`]; for a rule
    /// over an action list, [`ActionScope::Concrete`] of the action the slice
    /// was taken for, which the list names or resolves to. Never a list. The
    /// scope does not enter the leaf's verdict: it names the actions the leaf
    /// is validated against.
    pub action: ActionScope,
    /// The authored condition's canonical text.
    pub condition: String,
}

/// Why a lowered set's leaves for an action cannot be described
/// ([`LoweredPolicySet::temporal_slice`](crate::LoweredPolicySet::temporal_slice)).
#[derive(Debug, Clone, PartialEq, Eq, thiserror::Error)]
pub enum SliceError {
    /// **Deprecated: no longer returned.** A leaf that can apply to the action
    /// belongs to a rule over an action list (`action in [...]`, or `action in`
    /// a group). [`LoweredPolicySet::temporal_slice`](crate::LoweredPolicySet::temporal_slice)
    /// used to refuse such a leaf, and now describes it with its scope narrowed
    /// to the action. The variant stays so that code matching on it still
    /// compiles (documented only: no `#[deprecated]` attribute in 1.x).
    #[error("temporal leaf `{leaf}` belongs to a rule over an action list, which a leaf descriptor cannot carry")]
    ActionList { leaf: ExtensionId },
    /// A leaf's condition has no canonical text ([`temporal_ast::condition_text`](crate::temporal_ast::condition_text)).
    #[error("temporal leaf `{leaf}` has no canonical text: {reason}")]
    NoText { leaf: ExtensionId, reason: String },
    /// A leaf's condition does not end its predicates with the pins lowering
    /// injected, so its authored form cannot be recovered. Lowering never
    /// produces such a leaf.
    #[error("temporal leaf `{leaf}` does not carry the pins of its events")]
    Pins { leaf: ExtensionId },
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
#[non_exhaustive]
pub struct ProviderField {
    pub id: ExtensionId,
    /// The action scope the provider's rule pins. Actions reached by at least
    /// one provider policy reference a shared common type containing every
    /// hoisted provider field. The provider is still evaluated for every
    /// decision event (execution is unconditional).
    pub action: ActionScope,
    /// The concrete `(namespace, action_id)` actions [`action`](Self::action)
    /// resolves to against the schema. The union of these targets determines
    /// which actions receive `context.providers`; it may also support as-if
    /// evaluation optimizations in alternative implementations.
    pub target_actions: Vec<ActionRef>,
    /// What the rule's `principal` scope admits on the entity-type axis
    /// (`principal is T` / `== T::"x"` / `in G`, or unconstrained). Recorded so
    /// validation can resolve a `principal.<attr>` argument against the entity
    /// types the rule can actually receive (narrowed by this constraint).
    /// Mirrors [`TemporalField::principal`].
    pub principal: ScopeConstraint,
    /// What the rule's `resource` scope admits. See [`principal`](Self::principal).
    pub resource: ScopeConstraint,
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
    /// The enum entity types this call's types reference (its provider's and
    /// its chained methods'), copied from the declarations' `entityTypes`.
    /// Only those: a large declarations file is not copied into every field.
    /// Used to convert the provider's enum ids into entities at authorize time.
    pub entity_types: BTreeMap<String, crate::extension::provider::declarations::EntityTypeDecl>,
    /// The name each of [`entity_types`](Self::entity_types) is exported
    /// under, in the action schema's namespace, keyed by its declared name
    /// (`GuardDuty::Severity` -> `Drupe::GuardDuty_Severity`). Converted
    /// values are entities of the exported type.
    pub entity_type_names: BTreeMap<String, String>,
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
    /// The executable form of the authored leaves: `temporal` with every
    /// comparison that orders a timepoint, or computes with one, replaced by a
    /// false comparison (`extension::temporal::timepoints`). A partitioning
    /// temporal engine runs these. Identical to `temporal` for every leaf that
    /// validates.
    pub temporal_executable: Vec<TemporalField>,
    /// The executable leaves after the pin-relativization rewrite
    /// ([`crate::event_schema::relativize`]) — the executable artifact
    /// handed to temporal engines and exposed to reimplementers. Identical
    /// to `temporal_executable` when the event schema declares no universal
    /// symmetric pin. The default schema declares one (on `callerPrincipal`),
    /// so under the default these differ from `temporal`.
    pub temporal_rewritten: Vec<TemporalField>,
    /// The event schema's universal symmetric pins as engine-facing partition
    /// keys. Non-empty iff the schema declares such a pin. A partitioning
    /// temporal engine keys its per-monitor history on these and runs the
    /// **non-relativized** `temporal_executable` leaves; empty means there is
    /// nothing to partition on (and `temporal_executable == temporal_rewritten`).
    pub partition_keys: Vec<crate::engine::PartitionKey>,
    /// Hoisted information-provider leaves.
    pub providers: Vec<ProviderField>,
    /// `rule_ids[k]` is the synthesized Cedar policy id for Dogwood rule k.
    pub rule_ids: Vec<String>,
    /// `rule_index[id]` is `k` such that `rule_ids[k] == id`: maps a policy id an engine
    /// reports back to its rule without a scan of every id (`decide`).
    pub rule_index: std::collections::HashMap<String, usize>,
    /// `rule_locs[k]` is the `.dw` span and source text of Dogwood rule k.
    pub rule_locs: Vec<SourceLoc>,
    /// `rule_sources[k]` is the input-entry index of Dogwood rule k, in input order.
    pub rule_sources: Vec<usize>,
    /// `temporal_rules[j]` is the rule index of `temporal[j]` (and of
    /// `temporal_rewritten[j]`).
    pub temporal_rules: Vec<usize>,
    /// `provider_rules[j]` is the rule index of `providers[j]`.
    pub provider_rules: Vec<usize>,
    /// The derived event schema (event kinds + fields per action).
    pub event_schema: DerivedEventSchema,
    /// The event kinds the event schema marks `decision`.
    pub decision_kinds: BTreeSet<String>,
    /// The exported name of each provider enum the policy set uses, keyed by
    /// its declared name. Validation maps exported names in Cedar's messages
    /// back to the declared ones.
    pub enum_names: BTreeMap<String, String>,
    /// The reads of the request context a rule makes that lowering does not
    /// preserve (a read of the whole context, or of an attribute with a hoisted
    /// name). Validation reports each.
    pub context_reads: Vec<crate::cedarify::ContextRead>,
    /// The runtime conformance checks of this set, built from the fields above
    /// on first use ([`Lowered::runtime_checks`]) and shared by everything that
    /// holds the set.
    pub checks: crate::conformance::RuntimeChecksCache,
    /// What the Lean frontend recorded on this set, when the service schema
    /// selects it ([`Frontend::Lean`](crate::Frontend::Lean) or
    /// [`Frontend::Shadow`](crate::Frontend::Shadow)): validation reads it.
    #[cfg(feature = "lean-frontend")]
    pub lean: Option<crate::lean_frontend::LeanRecord>,
}

/// The public signature of one derived event.
fn signature_of(ev: &crate::event_schema::derive::DerivedEvent) -> EventSignature {
    EventSignature {
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
                    crate::event_schema::derive::FieldType::Cedar(s) => EventFieldType::Cedar(s),
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
    }
}

impl Lowered {
    /// The declared signature of every event this policy set can see.
    ///
    /// Shared by [`LoweredPolicySet::event_signatures`](crate::LoweredPolicySet::event_signatures)
    /// and by authorizer construction, which hands them to a temporal engine so a
    /// COMPILING engine can resolve each event field's declared type.
    pub(crate) fn event_signatures(&self) -> impl Iterator<Item = EventSignature> + '_ {
        self.event_schema.events.iter().map(signature_of)
    }

    /// The runtime conformance checks of this set (event, request and
    /// provider-output conformance), built on the first call and kept.
    pub(crate) fn runtime_checks(&self) -> &crate::conformance::RuntimeChecks {
        self.checks.get_or_build(self)
    }

    /// The event conformance an [`Authorizer`](crate::Authorizer) requires of
    /// `event` before it ingests it, under the mirror rule `mirror`: the one
    /// check, which [`ingest`] runs and
    /// [`LoweredPolicySet::check_event_conformance`](crate::LoweredPolicySet::check_event_conformance)
    /// exposes. Reports only [`Rejection::Nonconforming`](crate::conformance::Rejection::Nonconforming).
    pub(crate) fn check_event_conformance(
        &self,
        event: &Event,
        mirror: crate::conformance::MirrorRule,
    ) -> Result<(), crate::conformance::Rejection> {
        match self.runtime_checks().event_nonconformance(event, mirror) {
            Some(reason) => Err(crate::conformance::Rejection::Nonconforming { reason }),
            None => Ok(()),
        }
    }

    /// Check `event` against the pin rules of its signature
    /// ([`EventSignature::check_pins`]). An event of no declared signature is
    /// not checked here.
    pub(crate) fn check_event(
        &self,
        event: &Event,
        rule: crate::conformance::MirrorRule,
    ) -> Result<(), crate::conformance::Rejection> {
        if rule == crate::conformance::MirrorRule::Unchecked {
            return Ok(());
        }
        let data = event.data();
        match self
            .event_schema
            .get(&data.namespace, &data.action, &data.kind)
        {
            Some(ev) => signature_of(ev).check_pins(event, rule),
            None => Ok(()),
        }
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
        &self.temporal_executable
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
    /// returned by `PolicySchema::from_mcp_manifest` (feature `mcp-schema`).
    #[error("MCP schema generation: {0}")]
    McpSchema(String),

    /// The Cedar action schema was refused before Cedar parsed it: it nests
    /// more than twice [`DEFAULT_MAX_DEPTH`](crate::DEFAULT_MAX_DEPTH)
    /// levels (a `Set<{ … }>` level is two brackets), which Cedar's recursive-descent schema parser could not read
    /// without risking a stack overflow. Returned by the
    /// [`PolicySchema`](crate::PolicySchema) constructors.
    #[error("action schema: {0}")]
    ActionSchema(String),

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

    /// The information-provider declarations are inconsistent (an unknown
    /// `paramType`, a malformed `entityTypes` entry, an output entity type
    /// that is not declared, …) — returned by
    /// [`ServiceSchemaBuilder::build`](crate::ServiceSchemaBuilder::build) for
    /// declarations that did not come through
    /// [`ProviderDeclarations::from_json`](crate::ProviderDeclarations::from_json).
    #[error("provider declarations: {0}")]
    Providers(String),

    /// A hoisted extension leaf could not be prepared.
    #[error("extension leaf `{id}`: {message}")]
    Leaf { id: ExtensionId, message: String },

    /// A string given as a [`Distincter`](crate::Distincter) (directly or via
    /// [`lower_with_distincter`](crate::policy_set::ParsedPolicySet::lower_with_distincter))
    /// is not a valid Cedar identifier fragment. The distincter is
    /// interpolated into the synthesized Cedar policy ids and the hoisted
    /// `context.<id>` attribute names, so it must be a legal identifier
    /// (`[_A-Za-z][_A-Za-z0-9]*`) — otherwise it would produce an invalid
    /// schema / policy that fails opaquely downstream.
    #[error("invalid distincter `{0}`: {}", crate::policy_set::distincter_problem(.0))]
    InvalidDistincter(String),

    /// The same distincter was passed for two entries of
    /// [`lower_many`](crate::lower_many). Each entry's ids are namespaced by its
    /// distincter, so a repeat would mint colliding policy ids and field names.
    #[error("duplicate distincter `{0}`: each policy needs its own")]
    DuplicateDistincter(String),

    /// [`lower_many`](crate::lower_many) was given no policies.
    #[error("lower_many needs at least one policy")]
    NoPolicies,

    /// An entry of [`lower_many`](crate::lower_many) was parsed with a
    /// [`ServiceSchema`] that is not a clone of the first entry's.
    #[error(
        "lower_many: entry {0} was parsed with a different ServiceSchema; parse every entry with clones of one value"
    )]
    MismatchedServiceSchema(usize),

    /// A stable policy id could not be assigned
    /// ([`ParsedPolicySet::with_ids`](crate::ParsedPolicySet::with_ids)): an
    /// `@id` is missing or invalid, two policies share an id, or an explicit id
    /// list has the wrong length. Self-rendering; see [`PolicyIdError`].
    ///
    /// [`PolicyIdError`]: crate::PolicyIdError
    #[error(transparent)]
    #[diagnostic(transparent)]
    PolicyId(#[from] crate::error::PolicyIdError),

    /// [`Authorizer::update_policies`](crate::Authorizer::update_policies) was
    /// called, but an installed engine cannot be re-prepared with a new policy
    /// set while keeping its state
    /// ([`TemporalEngine::supports_policy_update`](crate::engine::TemporalEngine::supports_policy_update) /
    /// [`PolicyEngine::supports_policy_update`](crate::engine::PolicyEngine::supports_policy_update)
    /// returned `false`). The authorizer is unchanged.
    #[error(
        "policy update unsupported: the {0} engine cannot be re-prepared with a new policy set"
    )]
    PolicyUpdateUnsupported(&'static str),

    /// [`Authorizer::update_policies`](crate::Authorizer::update_policies) was
    /// given a policy set whose temporal partitioning differs from the
    /// authorizer's (the event schema's universal symmetric pins changed, or
    /// partitioning would switch on or off). Partitioned history cannot be
    /// re-keyed live. The authorizer is unchanged.
    #[error("policy update changes the temporal partition keys; build a new authorizer instead")]
    PartitionKeysChanged,

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

    /// The frontend a [`ServiceSchema`] selects
    /// ([`ServiceSchemaBuilder::frontend`](crate::ServiceSchemaBuilder::frontend))
    /// could not produce a result: it is not in this build, the Lean frontend
    /// failed or rejected the set with an error no other variant carries, or the
    /// two frontends of [`Frontend::Shadow`](crate::Frontend::Shadow) disagree.
    /// See [`FrontendError`](crate::FrontendError).
    #[error(transparent)]
    #[diagnostic(transparent)]
    Frontend(#[from] crate::frontend::FrontendError),
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
    /// The owner-chosen stable id of each policy, in source order, when the set
    /// was given an id source other than positional
    /// ([`ParsedPolicySet::with_ids`](crate::ParsedPolicySet::with_ids)).
    /// Validated and unique. `None` keeps today's positional ids.
    ids: Option<Vec<String>>,
    /// The options this set was parsed under; lowering keeps to the same
    /// node budget ([`ParseOptions::max_nodes`](dogwood_syntax::ParseOptions::max_nodes)).
    options: dogwood_syntax::ParseOptions,
    /// The parser's output, before the macro library is merged and macros are
    /// expanded: what the Lean frontend lowers, kept when the service schema
    /// selects it.
    #[cfg(feature = "lean-frontend")]
    raw: Option<std::sync::Arc<crate::ast::PolicySet>>,
    /// The id source the stable ids were assigned from, which the Lean frontend's
    /// request carries (the Lean frontend assigns them again when it lowers).
    #[cfg(feature = "lean-frontend")]
    id_source: Option<crate::IdSource>,
}

impl Parsed {
    /// The options this set was parsed under (see the field).
    #[cfg(feature = "lean-frontend")]
    pub(crate) fn options(&self) -> &dogwood_syntax::ParseOptions {
        &self.options
    }

    /// The stable policy ids, if any (see the field).
    pub(crate) fn ids(&self) -> Option<&[String]> {
        self.ids.as_deref()
    }

    /// Install (or, with `None`, clear) the stable policy ids. The caller has
    /// validated them.
    pub(crate) fn set_ids(&mut self, ids: Option<Vec<String>>) {
        self.ids = ids;
    }

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

    /// The parser's output, kept for the Lean frontend (see the field).
    #[cfg(feature = "lean-frontend")]
    pub(crate) fn raw(&self) -> Option<&crate::ast::PolicySet> {
        self.raw.as_deref()
    }

    /// The id source of the stable ids, if any (see the field).
    #[cfg(feature = "lean-frontend")]
    pub(crate) fn id_source(&self) -> Option<&crate::IdSource> {
        self.id_source.as_ref()
    }

    /// Record the id source the stable ids were assigned from.
    #[cfg(feature = "lean-frontend")]
    pub(crate) fn set_id_source(&mut self, source: crate::IdSource) {
        self.id_source = Some(source);
    }
}

/// Phase 1 — parse and macro-expand Dogwood `source` against the
/// [`ServiceSchema`] (macros + provider declarations). Catches syntax, macro,
/// and structural errors. Needs **no** action schema — schema-dependent checks
/// are deferred to [`lower`] / validation.
///
/// Macro expansion of the whole set shares one node budget of
/// `options.max_nodes`, and the set keeps `options` for its lowering.
/// `options` bounds every depth: of the source's nesting, of the trees built,
/// and of their macro expansions; the service schema's macro library is
/// parsed under the same options.
pub(crate) fn parse(
    source: &str,
    service_schema: &ServiceSchema,
    options: &dogwood_syntax::ParseOptions,
) -> Result<Parsed, Error> {
    #[cfg(test)]
    crate::api::stage_probe::enter("parse");
    // Share the `.dw` source: it both stamps every lowered node's `Loc` (so
    // Cedar validation diagnostics rebase into the original source) and lets
    // each fatal error carry the source for self-rendering.
    let dw_src: std::sync::Arc<str> = std::sync::Arc::from(source);

    let mut surface = crate::parser::parse_policies_with(source, options)
        .map_err(|errs| parse_errors(errs, &dw_src))?;
    #[cfg(feature = "lean-frontend")]
    let raw = service_schema
        .frontend()
        .runs_lean()
        .then(|| std::sync::Arc::new(surface.clone()));

    // Merge the schema's macro library into the policy set's own `def`s before
    // expansion, so a policy can call a library macro without re-declaring it.
    // A `def` in the policy source takes precedence: only library macros whose
    // name the policy does not already define are added (so the library can
    // never shadow or duplicate a policy's own macro). The library is checked
    // against its *own* source here, so a library-def error self-renders
    // against the library — after which any error `expand` raises over the
    // merged set is necessarily policy-authored (stamped `dw_src` below).
    merge_macro_library(&mut surface, service_schema.macros(), options)?;

    crate::macros::expand(&mut surface, options).map_err(|e| {
        Error::Macro(MacroError::new(
            e.message,
            SourceLoc::new(e.span, dw_src.clone()),
        ))
    })?;

    Ok(Parsed {
        surface,
        service_schema: service_schema.clone(),
        dw_src,
        ids: None,
        options: *options,
        #[cfg(feature = "lean-frontend")]
        raw,
        #[cfg(feature = "lean-frontend")]
        id_source: None,
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
    distincter: Option<&Distincter>,
) -> Result<(Lowered, crate::identity::SetIdentity), Error> {
    let rust = || {
        let base = Base::derive(&parsed.service_schema, policy_schema)?;
        let entry = lower_entry(parsed, &base, distincter)?;
        merge(base, vec![entry])
    };
    #[cfg(feature = "lean-frontend")]
    if parsed.service_schema.frontend().runs_lean() {
        return crate::lean_frontend::lower(&[(parsed, distincter)], policy_schema, false, rust);
    }
    rust()
}

/// [`Error::DuplicateDistincter`] for the first distincter that repeats one before it.
pub(crate) fn check_distincters<'a>(
    distincters: impl IntoIterator<Item = &'a Distincter>,
) -> Result<(), Error> {
    let mut seen = BTreeSet::new();
    for distincter in distincters {
        if !seen.insert(distincter) {
            return Err(Error::DuplicateDistincter(distincter.to_string()));
        }
    }
    Ok(())
}

/// Lower several parsed sets, each under its distincter, and merge them
/// ([`lower_many`](crate::lower_many), after its checks of the entries), with the
/// frontend their service schema selects.
pub(crate) fn lower_many(
    entries: &[(&Parsed, &Distincter)],
    policy_schema: &PolicySchema,
) -> Result<(Lowered, crate::identity::SetIdentity), Error> {
    let rust = || {
        check_distincters(entries.iter().map(|(_, d)| *d))?;
        let (first, _) = entries.first().ok_or(Error::NoPolicies)?;
        let base = Base::derive(first.service_schema(), policy_schema)?;
        let lowered = entries
            .iter()
            .map(|(p, distincter)| lower_entry(p, &base, Some(distincter)))
            .collect::<Result<Vec<_>, Error>>()?;
        merge(base, lowered)
    };
    #[cfg(feature = "lean-frontend")]
    if entries
        .first()
        .is_some_and(|(p, _)| p.service_schema.frontend().runs_lean())
    {
        let entries: Vec<crate::lean_frontend::EntryRef<'_>> =
            entries.iter().map(|(p, d)| (*p, Some(*d))).collect();
        return crate::lean_frontend::lower(&entries, policy_schema, true, rust);
    }
    rust()
}

/// The lowering inputs that depend only on the service schema and the action
/// schema, derived once and shared by every entry lowered against them.
pub(crate) struct Base<'a> {
    provider_declarations:
        Option<&'a crate::extension::provider::declarations::ProviderDeclarations>,
    /// The parsed action schema, before augmentation.
    fragment: crate::cedarify::Fragment,
    event_schema: DerivedEventSchema,
    pins: Vec<crate::event_schema::relativize::UniversalPin>,
    partition_keys: Vec<crate::engine::PartitionKey>,
    decision_kinds: BTreeSet<String>,
}

impl<'a> Base<'a> {
    /// Derive the event schema, its universal pins, partition keys, and
    /// decision kinds, and parse the action schema.
    pub(crate) fn derive(
        service_schema: &'a ServiceSchema,
        policy_schema: &PolicySchema,
    ) -> Result<Self, Error> {
        #[cfg(test)]
        crate::api::stage_probe::enter("base");
        let action_schema_src = policy_schema.action_schema_src();

        // Derive the event schema against the action schema. This binds the
        // symbolic event-schema DSL (carried on the ServiceSchema, unbound) to the
        // concrete action schema — the one lowering step that needs both halves.
        let event_schema =
            derive(service_schema.event_schema(), action_schema_src).map_err(Error::EventSchema)?;
        let fragment = crate::cedarify::parse_base_schema(action_schema_src)
            .map_err(|e| cedarify_error(e, &std::sync::Arc::from("")))?;

        // The schema's universal symmetric pins: the leaves are relativized for
        // them (the "pinned ⇒ safe to partition" encoding), and they are exposed
        // as engine-facing partition keys. A partitioning temporal engine routes
        // each event to a monitor keyed by these fields and runs the
        // NON-relativized `temporal` leaves within it — the equivalent-but-cheaper
        // alternative to the relativization rewrite. Empty when the schema
        // declares no universal symmetric pin. The default is not such a case —
        // it pins `callerPrincipal` on every kind.
        let pins = crate::event_schema::relativize::universal_pins(&event_schema);
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

        let decision_kinds = event_schema
            .decision_kinds()
            .into_iter()
            .map(str::to_string)
            .collect();

        Ok(Base {
            provider_declarations: service_schema.provider_declarations(),
            fragment,
            event_schema,
            pins,
            partition_keys,
            decision_kinds,
        })
    }
}

/// One input lowered against a [`Base`], before schema augmentation.
pub(crate) struct Entry {
    policies: CedarPolicySet,
    context_fields: Vec<crate::cedarify::ContextField>,
    provider_fields: Vec<crate::cedarify::ProviderField>,
    rule_ids: Vec<String>,
    rule_locs: Vec<SourceLoc>,
    temporal_rules: Vec<usize>,
    provider_rules: Vec<usize>,
    referenced_enums: BTreeSet<String>,
    enum_names: BTreeMap<String, String>,
    /// `rule_revisions[k]` is rule `k`'s revision (see [`crate::identity`]).
    rule_revisions: Vec<String>,
    /// Whether this entry's rules carry stable (owner-chosen) ids.
    stable_ids: bool,
    /// The node budget the entry was parsed under. [`merge`] gives the entry
    /// one budget of this many nodes, shared by all its leaves'
    /// relativization.
    max_nodes: usize,
    /// The entry's `.dw` source, for a node-budget error in [`merge`].
    dw_src: std::sync::Arc<str>,
    /// The context reads lowering does not preserve.
    context_reads: Vec<crate::cedarify::ContextRead>,
}

/// The error for a lowering that would create more nodes than `limit` (or a
/// lowered tree with more), at `span` in `src`.
fn lowering_budget_exceeded(
    limit: usize,
    span: crate::error::Span,
    src: &std::sync::Arc<str>,
) -> Error {
    let message = format!("lowering exceeds the node budget of {limit}");
    cedarify_error(
        RawCedarifyError {
            message,
            span: Some(span),
        },
        src,
    )
}

/// Refuse a lowered tree of `nodes` nodes if that is more than `limit`.
fn check_lowered_size(
    nodes: usize,
    limit: usize,
    span: crate::error::Span,
    src: &std::sync::Arc<str>,
) -> Result<(), Error> {
    if nodes > limit {
        return Err(lowering_budget_exceeded(limit, span, src));
    }
    Ok(())
}

/// Reject `parsed` if a temporal predicate contains an array constant.
pub(crate) fn reject_temporal_arrays(parsed: &Parsed) -> Result<(), Error> {
    use crate::extension::temporal::ast::{AggExprKind, Condition, ConditionKind, Term};

    /// Check whether a term is or contains an array constant, inside an
    /// aggregate's body or an operand of a compound.
    fn term_has_array(term: &Term) -> bool {
        match term {
            Term::Array(_) => true,
            Term::Agg(agg) => match &agg.kind {
                AggExprKind::Sum { body, .. } | AggExprKind::Count { body, .. } => {
                    condition_has_array(body)
                }
                AggExprKind::Call(_) => false,
            },
            Term::Arith { left, right, .. } => term_has_array(left) || term_has_array(right),
            _ => false,
        }
    }

    /// Walk a temporal condition tree, returning `true` if any predicate
    /// argument or comparison operand is a `Term::Array`.
    fn condition_has_array(cond: &Condition) -> bool {
        match &cond.kind {
            ConditionKind::And { left, right }
            | ConditionKind::Or { left, right }
            | ConditionKind::Since { left, right, .. } => {
                condition_has_array(left) || condition_has_array(right)
            }
            ConditionKind::Not { inner }
            | ConditionKind::Formerly { body: inner, .. }
            | ConditionKind::Previous { body: inner, .. }
            | ConditionKind::Exists { body: inner, .. } => condition_has_array(inner),
            ConditionKind::Predicate(pred) => {
                pred.args.iter().any(|arg| term_has_array(&arg.value))
            }
            ConditionKind::Comparison { left, right, .. } => {
                term_has_array(left) || term_has_array(right)
            }
            ConditionKind::Tp { .. } | ConditionKind::Call(_) | ConditionKind::SigilRef { .. } => {
                false
            }
            ConditionKind::Refine { base, fields, .. } => {
                condition_has_array(base) || fields.iter().any(|arg| term_has_array(&arg.value))
            }
        }
    }

    for policy in parsed.policies().iter() {
        for (block_idx, temporal_block) in policy.temporal_conditions().into_iter().enumerate() {
            if condition_has_array(temporal_block) {
                // Point the error at the temporal block's span.
                let span = policy.temporal_block_spans().into_iter().nth(block_idx);
                let message = "temporal predicate arguments cannot contain array constants \
                     (e.g. `field: [\"a\", \"b\"]`); use scalar values or \
                     `context` field references instead"
                    .to_string();
                let raw = RawCedarifyError { message, span };
                return Err(cedarify_error(raw, parsed.dw_src()));
            }
        }
    }
    Ok(())
}

/// Cedarify `parsed` against `base` and inject the event schema's pins.
pub(crate) fn lower_entry(
    parsed: &Parsed,
    base: &Base<'_>,
    distincter: Option<&Distincter>,
) -> Result<Entry, Error> {
    #[cfg(test)]
    crate::api::stage_probe::enter("lowerEntry");
    reject_temporal_arrays(parsed)?;
    let Parsed {
        surface,
        dw_src,
        options,
        ..
    } = parsed;
    let max_nodes = options.max_nodes;

    // The backstop: no expanded Cedar expression may be larger than the
    // set's node budget, whatever built it.
    for policy in &surface.policies {
        for cond in &policy.conditions {
            let nodes = crate::parser::expr_size(&cond.body);
            check_lowered_size(nodes, max_nodes, cond.body.span, dw_src)?;
        }
    }

    let mut lowered = cedarify_with_providers(
        surface,
        &base.fragment,
        base.provider_declarations,
        distincter.map(Distincter::as_str),
        parsed.ids(),
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
        crate::event_schema::pin::inject_pins(&mut leaf.temporal.condition, &base.event_schema);
    }
    // The backstop for the pinned leaves (their relativization is charged to
    // the set's budget, and checked again, in `merge`).
    for leaf in &context_fields {
        let nodes = crate::parser::condition_size(&leaf.temporal.condition);
        check_lowered_size(nodes, max_nodes, leaf.temporal.span, dw_src)?;
    }

    // Convert the loc-bearing `ast::PolicySet` into the public
    // `cedar_policy::PolicySet` for validation/authorization. This uses the
    // `#[doc(hidden)]` `From<ast::PolicySet>` impl (infallible since Cedar 4.14;
    // previously `TryFrom`). Upstream marks it hidden, so it
    // is not part of Cedar's supported surface and a minor release may remove it. There
    // is NO guard against that beyond the build failing to compile — this comment used
    // to claim a canary test protected it, and no such test has ever existed.
    let policies = CedarPolicySet::from(lowered.policy_set);

    // Each rule's revision: its canonical Cedar text plus the canonical form
    // of every leaf it hoisted (after pin injection and action resolution, so
    // a schema change that changes what a leaf means changes the revision).
    let mut leaves: Vec<Vec<(String, String)>> = vec![Vec::new(); lowered.rule_ids.len()];
    for (leaf, &k) in context_fields.iter().zip(&lowered.temporal_rules) {
        leaves[k].push((
            crate::identity::canonical_field_name(&lowered.rule_keys[k], &leaf.field_name),
            crate::identity::canonical_context_field(leaf),
        ));
    }
    for (leaf, &k) in provider_fields.iter().zip(&lowered.provider_rules) {
        leaves[k].push((
            crate::identity::canonical_field_name(&lowered.rule_keys[k], &leaf.field_name),
            crate::identity::canonical_provider_field(leaf),
        ));
    }
    let rule_revisions = lowered
        .rule_canonical
        .iter()
        .zip(&leaves)
        .map(|(cedar, leaves)| crate::identity::rule_revision(cedar, leaves))
        .collect();

    Ok(Entry {
        policies,
        context_fields,
        provider_fields,
        rule_ids: lowered.rule_ids,
        rule_locs: lowered.rule_locs,
        temporal_rules: lowered.temporal_rules,
        provider_rules: lowered.provider_rules,
        referenced_enums: lowered.referenced_enums,
        enum_names: lowered.enum_names,
        rule_revisions,
        stable_ids: parsed.ids().is_some(),
        max_nodes,
        dw_src: dw_src.clone(),
        context_reads: lowered.context_reads,
    })
}

/// Combine `entries`, in order, into one [`Lowered`] over `base` augmented
/// once with every entry's hoisted fields.
///
/// Entry `i`'s rule `k` becomes rule `k` plus the rule count of the entries
/// before it. Fails if two entries hoist a field of the same name.
pub(crate) fn merge(
    base: Base<'_>,
    entries: Vec<Entry>,
) -> Result<(Lowered, crate::identity::SetIdentity), Error> {
    #[cfg(test)]
    crate::api::stage_probe::enter("merge");
    let Base {
        provider_declarations,
        fragment,
        event_schema,
        pins,
        partition_keys,
        decision_kinds,
    } = base;

    let mut policies = CedarPolicySet::new();
    let mut context_fields = Vec::new();
    let mut provider_fields = Vec::new();
    let mut rule_ids = Vec::new();
    let mut rule_locs = Vec::new();
    let mut temporal_rules = Vec::new();
    let mut provider_rules = Vec::new();
    let mut rule_sources = Vec::new();
    // Every entry exports an enum under the same name (it depends only on the
    // action schema), so the union is consistent.
    let mut referenced_enums = BTreeSet::new();
    let mut enum_names = BTreeMap::new();
    let mut rule_revisions = Vec::new();
    // One node budget per entry (one parsed set), with its source for the
    // error, shared by all of that entry's temporal leaves; `leaf_entry[j]` is
    // the entry temporal leaf `j` came from. Entries may have been parsed
    // under different options, and no budget spans entries.
    let mut budgets: Vec<(NodeBudget, std::sync::Arc<str>)> = Vec::new();
    let mut leaf_entry: Vec<usize> = Vec::new();
    let mut context_reads = Vec::new();
    // Stable iff every entry is (an empty merge has no positional rule).
    let stable_ids = entries.iter().all(|e| e.stable_ids);
    for (i, entry) in entries.into_iter().enumerate() {
        if i == 0 {
            policies = entry.policies;
        } else {
            for policy in entry.policies.policies() {
                policies
                    .add(policy.clone())
                    .map_err(|e| Error::PolicySet(Box::new(e)))?;
            }
        }
        let offset = rule_ids.len();
        budgets.push((NodeBudget::new(entry.max_nodes), entry.dw_src));
        leaf_entry.extend(std::iter::repeat_n(i, entry.context_fields.len()));
        context_fields.extend(entry.context_fields);
        provider_fields.extend(entry.provider_fields);
        temporal_rules.extend(entry.temporal_rules.into_iter().map(|k| k + offset));
        context_reads.extend(entry.context_reads.into_iter().map(|read| {
            crate::cedarify::ContextRead {
                rule: read.rule + offset,
                ..read
            }
        }));
        provider_rules.extend(entry.provider_rules.into_iter().map(|k| k + offset));
        rule_sources.resize(offset + entry.rule_ids.len(), i);
        rule_ids.extend(entry.rule_ids);
        rule_revisions.extend(entry.rule_revisions);
        rule_locs.extend(entry.rule_locs);
        referenced_enums.extend(entry.referenced_enums);
        enum_names.extend(entry.enum_names);
    }

    let augmented_schema_fragment = crate::cedarify::augment_schema(
        fragment,
        provider_declarations,
        &referenced_enums,
        &context_fields,
        &provider_fields,
    )
    .map_err(|e| cedarify_error(e, &std::sync::Arc::from("")))?;

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

    // The executable form of each authored leaf: timepoints are
    // equality-only, so an authored comparison that orders a timepoint, or
    // computes with one, is false (see `extension::temporal::timepoints`).
    // Validation still sees the authored leaves (`temporal`).
    let temporal_executable: Vec<TemporalField> = temporal
        .iter()
        .map(|f| TemporalField {
            condition: crate::extension::temporal::Temporal {
                condition: crate::extension::temporal::timepoints::unorder_timepoints(
                    &f.condition.condition,
                ),
                span: f.condition.span,
            },
            ..f.clone()
        })
        .collect();

    // Relativize each leaf for the schema's universal symmetric pins. A no-op
    // clone when the schema declares none. Every node the rewrite creates is
    // charged to the budget of the entry the leaf came from, and the
    // backstop refuses a rewritten leaf larger than that budget's limit.
    debug_assert_eq!(temporal_executable.len(), leaf_entry.len());
    let mut temporal_rewritten: Vec<TemporalField> = Vec::with_capacity(temporal_executable.len());
    for (f, &entry) in temporal_executable.iter().zip(&leaf_entry) {
        let (budget, src) = &mut budgets[entry];
        let span = f.condition.span;
        let max_nodes = budget.limit();
        let condition = crate::event_schema::relativize::relativize_condition(
            &f.condition.condition,
            &event_schema,
            &pins,
            budget,
        )
        .map_err(|_| lowering_budget_exceeded(max_nodes, span, src))?;
        let nodes = crate::parser::condition_size(&condition);
        check_lowered_size(nodes, max_nodes, span, src)?;
        temporal_rewritten.push(TemporalField {
            id: f.id.clone(),
            action: f.action.clone(),
            target_actions: f.target_actions.clone(),
            principal: f.principal.clone(),
            resource: f.resource.clone(),
            condition: crate::extension::temporal::Temporal { condition, span },
        });
    }

    // Resolve each hoisted provider field's declaration now (so the engine
    // carries the implementation and need not re-consult the declarations
    // file at authorize time).
    let providers = provider_fields
        .into_iter()
        .map(|f| {
            let declaration = provider_declarations
                .and_then(|d| d.get(&f.invocation.key()))
                .cloned();
            let entity_types = match (provider_declarations, &declaration) {
                (Some(decls), Some(decl)) => decl
                    .referenced_entity_types(f.methods.iter().map(|m| m.name.as_str()))
                    .into_iter()
                    .filter_map(|name| {
                        let enum_decl = decls.entity_type_decls.get(&name)?.clone();
                        Some((name, enum_decl))
                    })
                    .collect(),
                _ => BTreeMap::new(),
            };
            ProviderField {
                id: f.field_name,
                action: action_scope(&f.action),
                target_actions: f
                    .target_actions
                    .iter()
                    .map(|(ns, id)| action_ref(ns.clone(), id.clone()))
                    .collect(),
                principal: f.principal.clone(),
                resource: f.resource.clone(),
                invocation: f.invocation,
                methods: f.methods,
                body_base: f.body_base,
                entity_type_names: entity_types
                    .keys()
                    .filter_map(|name| Some((name.clone(), enum_names.get(name)?.clone())))
                    .collect(),
                declaration,
                entity_types,
            }
        })
        .collect();

    // Compile the augmented schema from its fragment — an in-memory conversion
    // (no text re-parse). The fragment is retained on `Lowered` as the source
    // of truth for the text / JSON serializations.
    let augmented_schema: Schema = augmented_schema_fragment
        .clone()
        .try_into()
        // `TryInto<Schema>` yields a `SchemaError`, which converts into a
        // `CedarSchemaError` (its `Schema` variant).
        .map_err(|e: cedar_policy::SchemaError| Error::CedarSchema(Box::new(e.into())))?;

    // First occurrence wins, as the scan it replaces found the first match.
    let mut rule_index = std::collections::HashMap::with_capacity(rule_ids.len());
    for (k, id) in rule_ids.iter().enumerate() {
        rule_index.entry(id.clone()).or_insert(k);
    }
    Ok((
        Lowered {
            policies,
            augmented_schema,
            augmented_schema_fragment,
            temporal,
            temporal_executable,
            temporal_rewritten,
            partition_keys,
            providers,
            rule_ids,
            rule_index,
            rule_locs,
            rule_sources,
            temporal_rules,
            provider_rules,
            event_schema,
            decision_kinds,
            enum_names,
            context_reads,
            checks: Default::default(),
            #[cfg(feature = "lean-frontend")]
            lean: None,
        },
        crate::identity::SetIdentity::new(rule_revisions, stable_ids),
    ))
}

/// Merge the macro-library `def`s into `surface.defs`, with the policy's own
/// `def`s taking precedence: a library macro is added only if the policy does
/// not already define a macro of that name. This keeps default-on macro
/// libraries safe — the library can neither shadow a policy's macro nor cause
/// a duplicate-definition error against one.
fn merge_macro_library(
    surface: &mut crate::ast::PolicySet,
    macros_src: &str,
    options: &dogwood_syntax::ParseOptions,
) -> Result<(), Error> {
    #[cfg(test)]
    crate::api::stage_probe::enter("mergeLibrary");
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
    let library = crate::parser::parse_policies_with(macros_src, options)
        .map_err(|errs| parse_errors(errs, &lib_src))?;
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

/// Ingest one [`Event`], checking it in the order of the specification's
/// `PolicySet.decideWith` (`dogwood-lean`, `Dogwood.Spec.Decision`).
///
/// * An event that does not conform is not ingested: the temporal engine never
///   observes it, so no later decision sees it. A nonconforming **history**
///   event is rejected (`Err`); a nonconforming **decision** event fails its
///   decision closed (a `Deny`). Conformance is the specification's
///   ([`Lowered::check_event_conformance`], with its pin clauses under the
///   `mirror` rule).
/// * A conforming event is handed to the `temporal` engine
///   ([`try_observe`](crate::engine::TemporalEngine::try_observe)), so it
///   observes the history. An event the engine could not record is not in the
///   history: a history event is reported (`Rejection::Unavailable`, never
///   lost silently), and a decision event's decision fails closed. For a
///   history-only event that is all (`Ok(None)`); for an event of a decision
///   kind the decision is made by [`decide_at`] (`Ok(Some)`).
///
/// A decision is infallible: an evaluation failure (a provider that cannot
/// run, the temporal engine erroring, a decision event with no principal or
/// resource in scope, nonconforming data) does not abort — it is folded into
/// the [`Response`](crate::authorize::Response)'s diagnostics with a
/// fail-closed `Deny`.
pub(crate) fn ingest(
    lowered: &Lowered,
    identity: &crate::identity::SetIdentity,
    policy: &dyn crate::engine::PolicyEngine,
    temporal: &mut dyn crate::engine::TemporalEngine,
    resolver: Option<&dyn crate::engine::ProviderResolver>,
    mirror: crate::conformance::MirrorRule,
    event: &Event,
) -> Result<Option<crate::authorize::Response>, crate::conformance::Rejection> {
    use crate::conformance::Rejection;
    // A timepoint is a decision point iff its event kind is one the event
    // schema marked `decision`.
    let decision = lowered.decision_kinds.contains(&event.data().kind);

    // The specification's ingestion rejects an event that does not conform to
    // the event schema (`Rejection.nonconforming`, `Log.submit`): it never
    // enters the history, whatever its kind. One check, the one
    // `LoweredPolicySet::check_event_conformance` runs: its pin clauses follow
    // the authorizer's mirror rule (strict, the specification's, by default).
    let conformance = lowered.check_event_conformance(event, mirror);

    if !decision {
        conformance?;
        // Every ingested event is observed by the temporal engine, in order —
        // this is what maintains the history that temporal leaves see. An event
        // the engine could not record is reported, never lost silently.
        temporal.try_observe(event)?;
        return Ok(None);
    }

    // A decision event: its checks come in `decideWith`'s order. The scope
    // comes first, then the event's own conformance.
    let nonconformance = conformance.err().map(|rejection| match rejection {
        // `check_event_conformance` reports nonconformance only.
        Rejection::Nonconforming { reason } | Rejection::Unavailable { reason } => reason,
    });
    let deny = |errors: Vec<String>| Ok(Some(crate::authorize::Response::deny_with_errors(errors)));
    match (nonconformance, request_scope(event).err()) {
        (nonconformance, Some(message)) => {
            // A decision event without a principal or resource still enters
            // the history when it conforms. When it does not, the second error
            // says so: the missing scope comes first, and the caller still
            // learns that the event was not ingested.
            let mut errors = vec![message];
            match nonconformance {
                Some(reason) => errors.push(format!("nonconforming decision event: {reason}")),
                None => {
                    if let Err(rejection) = temporal.try_observe(event) {
                        errors.push(format!("temporal engine: {rejection}"));
                    }
                }
            }
            deny(errors)
        }
        (Some(reason), None) => deny(vec![format!("nonconforming decision event: {reason}")]),
        (None, None) => {
            // An event the engine could not record fails its decision closed.
            if let Err(rejection) = temporal.try_observe(event) {
                return deny(vec![format!("temporal engine: {rejection}")]);
            }
            Ok(Some(decide_at(
                lowered, identity, policy, temporal, resolver, event,
            )))
        }
    }
}

/// Decide the request for the current decision `event`, which conforms to the
/// event schema and has a principal and a resource, collecting any evaluation
/// errors into the response's diagnostics (fail-closed `Deny` on error).
///
/// The checks come in the order of the specification's `decideWith`: the
/// request, the entity store, the information providers and their outputs,
/// and then the temporal leaves.
fn decide_at(
    lowered: &Lowered,
    identity: &crate::identity::SetIdentity,
    policy: &dyn crate::engine::PolicyEngine,
    temporal: &mut dyn crate::engine::TemporalEngine,
    resolver: Option<&dyn crate::engine::ProviderResolver>,
    event: &Event,
) -> crate::authorize::Response {
    let deny = |message: String| crate::authorize::Response::deny_with_errors(vec![message]);
    let checks = lowered.runtime_checks();

    let (principal, action, resource) = match request_scope(event) {
        Ok(scope) => scope,
        Err(message) => return deny(message),
    };

    // The request: its principal and resource are of types its action applies
    // to, and its context is an instance of the action's context record type.
    // The Cedar request is built without a schema below, because the decision
    // supplies every hoisted attribute to every action's context; this is
    // where the request is checked instead.
    if let Some(reason) = checks.request_nonconformance(event) {
        return deny(format!("nonconforming request: {reason}"));
    }

    // Build the Cedar entity store: the schema's action entities, the
    // caller-supplied attributed entities validated against the augmented
    // schema, and the scope principal/resource made present (bare). A
    // conformance / attribute-evaluation failure MUST fail closed — a policy
    // evaluated against a store missing a required attribute could mis-decide
    // — so surface it as a Deny with the error in diagnostics rather than
    // authorizing against an ill-formed store.
    let entities = match build_entities(
        &principal,
        &resource,
        event.data(),
        &lowered.augmented_schema,
    ) {
        Ok(e) => e,
        Err(message) => return deny(message),
    };

    // Information providers. Provider execution is UNCONDITIONAL: every
    // declared provider field is evaluated for every decision event, whatever
    // the event's action or scope entities (see `build_context`). An error —
    // e.g. an information provider that errors at runtime — is handled by
    // DENYING the request, with the error in diagnostics, rather than
    // authorizing with an incomplete context (a `permit` firing whose guard
    // can no longer be checked). NOTE: this fail-closed handling is this
    // reference implementation's choice, not a semantic guarantee. Under the
    // provider contract (guide, 05-information-providers) an erroring provider
    // is UNDEFINED BEHAVIOR: other implementations may avoid the error entirely
    // (and reach a different verdict), and policy sets must not rely on
    // deny-on-error — provider scripts are required to be defensive instead.
    let mut provider_outputs: BTreeMap<String, Value> = BTreeMap::new();
    for field in &lowered.providers {
        match eval_provider(field, resolver, event) {
            Ok(value) => {
                provider_outputs.insert(field.id.clone(), value);
            }
            Err(message) => return deny(message),
        }
    }
    // An output that is not a value of its declared type is a broken provider
    // contract too: the decision fails closed. Checked after every provider
    // has run, as the specification orders the two checks.
    for field in &lowered.providers {
        if let Some(value) = provider_outputs.get(&field.id)
            && let Some(reason) =
                checks.provider_output_nonconformance(&field.id, &field.invocation.key(), value)
        {
            return deny(format!("nonconforming provider output: {reason}"));
        }
    }

    // Temporal leaves: ask the temporal engine for each leaf's boolean at this
    // decision point. A failure fails the decision closed, and so does a
    // binding set that does not cover every hoisted leaf: Cedar would report
    // an absent `context.<id>` as an error of the policy reading it, and skip
    // that policy, so a `forbid` whose leaf is missing would stop applying.
    let temporal_bindings = match temporal.evaluate() {
        Ok(b) => b,
        Err(message) => return deny(format!("temporal evaluation: {message}")),
    };
    // A value for a name that is not a leaf fails the decision closed at once;
    // a leaf without a value, when a policy reads it (below).
    let (missing, unknown) = uncovered_leaves(lowered, &temporal_bindings);
    if let Some(unknown) = unknown {
        return deny(format!(
            "temporal evaluation: the temporal engine returned a value for `{unknown}`, which is \
             not a leaf of the policy set"
        ));
    }

    // Build the request context (the request context + temporal booleans +
    // provider outputs) and the request.
    let context = match build_context(
        &temporal_bindings,
        &lowered.providers,
        provider_outputs,
        event,
    ) {
        Ok(ctx) => ctx,
        Err(message) => return deny(message),
    };
    let request = match Request::new(principal, action, resource, context, None) {
        Ok(req) => req,
        // No well-formed request — fail closed.
        Err(e) => return deny(format!("request build: {e}")),
    };

    let response = decide(lowered, identity, policy, &request, &entities);
    // A binding set that does not cover a hoisted leaf a policy read fails the
    // decision closed: Cedar reports an absent `context.<id>` as an error of
    // the policy reading it, and skips that policy, so a `forbid` whose leaf
    // is missing would stop applying.
    if let Some(leaf) = missing_leaf_read(lowered, &missing, &response) {
        return deny(format!(
            "temporal evaluation: the temporal engine returned no value for the leaf `{leaf}`"
        ));
    }
    response
}

/// The temporal engine's `bindings` against the policy set's hoisted temporal
/// leaves: the leaves it gave no value (in leaf order), and the first value it
/// gave for a name that is not a leaf of the set, if any.
fn uncovered_leaves<'a>(
    lowered: &'a Lowered,
    bindings: &crate::engine::TemporalBindings,
) -> (Vec<&'a str>, Option<String>) {
    let leaves: BTreeSet<&str> = lowered.temporal.iter().map(|f| f.id.as_str()).collect();
    let missing = lowered
        .temporal
        .iter()
        .map(|f| f.id.as_str())
        .filter(|id| !bindings.contains_key(*id))
        .collect();
    let unknown = bindings
        .keys()
        .find(|id| !leaves.contains(id.as_str()))
        .cloned();
    (missing, unknown)
}

/// A leaf of `missing` (leaves the temporal engine gave no value) that a policy
/// read in `response`'s evaluation, if one did, or the first of `missing` when
/// the policy engine reported errors without naming the policies that raised
/// them. Cedar reports a policy that reads an absent `context.<leaf>` as
/// erroring and skips it, so a `forbid` whose leaf is missing would stop
/// applying: such a decision fails closed. A policy that never read its leaf
/// (its scope did not match, or an earlier conjunct was false) decided as it
/// would have with any value of the leaf. An engine that binds only the leaves
/// a decision can read (a leaf masker's sparse bindings) therefore decides as
/// one that binds them all.
fn missing_leaf_read<'a>(
    lowered: &Lowered,
    missing: &[&'a str],
    response: &crate::authorize::Response,
) -> Option<&'a str> {
    if missing.is_empty() {
        return None;
    }
    let diagnostics = response.diagnostics();
    let mut erroring = diagnostics.erroring().peekable();
    if erroring.peek().is_none() {
        return diagnostics.errors().next().and(missing.first().copied());
    }
    erroring
        .filter_map(|e| lowered.rule_index.get(e.policy().id()).copied())
        .find_map(|k| {
            lowered
                .temporal
                .iter()
                .zip(&lowered.temporal_rules)
                .filter(|(_, rule)| **rule == k)
                .find_map(|(leaf, _)| missing.iter().copied().find(|m| *m == leaf.id.as_str()))
        })
}

/// The shared decision core: authorize `request` through the `policy` engine,
/// mapping the determining (and erroring) policy ids back to Dogwood rule
/// references via the lowered `rule_ids`.
///
/// An id the set does not contain is an engine fault. With stable ids the
/// decision then fails closed (a `Deny` naming the id in its errors, with no
/// supporting policies). Under positional ids it is dropped, as it always was,
/// so existing deployments keep their behavior.
fn decide(
    lowered: &Lowered,
    identity: &crate::identity::SetIdentity,
    policy: &dyn crate::engine::PolicyEngine,
    request: &Request,
    entities: &Entities,
) -> crate::authorize::Response {
    use crate::authorize::{ErroringPolicy, PolicyRef};

    // `entities` already carries the caller-supplied attributed entities, the
    // bare scope entities, AND the schema's action-hierarchy entities (all
    // merged by `build_entities`), so `principal.<attr>` reads and
    // `action in [Group]` membership both resolve from one store.
    let outcome = policy.authorize(crate::engine::AuthorizationRequest { request, entities });

    let rule_of = |id: &str| lowered.rule_index.get(id).copied();
    let mut unknown: Vec<&str> = Vec::new();

    let mut reason = Vec::new();
    let mut determining = Vec::new();
    for id in &outcome.determining_policy_ids {
        match rule_of(id) {
            Some(rule_index) => {
                reason.push(DogwoodRuleRef {
                    rule_index,
                    cedar_policy_id: id.clone(),
                });
                determining.push(PolicyRef::new(
                    id.clone(),
                    identity.revision(rule_index).to_string(),
                ));
            }
            None => unknown.push(id),
        }
    }
    let mut erroring = Vec::new();
    for (id, message) in &outcome.erroring_policies {
        match rule_of(id) {
            Some(k) => erroring.push(ErroringPolicy::new(
                PolicyRef::new(id.clone(), identity.revision(k).to_string()),
                message.clone(),
            )),
            None => unknown.push(id),
        }
    }

    // Position-free and deterministic: Cedar reports determining policies from
    // a hash set, so sort the new views by id (stable across versions, unlike
    // positions). `reason` keeps the engine's order, as before.
    determining.sort();
    erroring.sort_by(|a, b| a.policy().cmp(b.policy()));

    if identity.stable() && !unknown.is_empty() {
        let mut errors = outcome.errors;
        errors.extend(unknown.iter().map(|id| {
            format!(
                "policy engine reported policy id `{id}`, which is not in this policy set; \
                 failing closed"
            )
        }));
        return crate::authorize::Response::deny_with_errors(errors);
    }

    crate::authorize::Response::new(
        outcome.decision,
        reason,
        outcome.errors,
        determining,
        erroring,
    )
}

/// Build the Cedar entity store for a decision, from three sources with
/// different trust levels:
///
///   1. **Action-hierarchy entities** — the schema's action entities and their
///      `memberOf` edges, so a scope testing action membership
///      (`action in [Group]`) resolves: Cedar reads those edges from the entity
///      store, not the schema, so without them `action in [Group]` never
///      matches a descendant action and the rule silently never fires. The
///      schema's action entities take precedence over supplied data for the
///      same uid, so supplied data cannot change the action hierarchy (the
///      specification's `PolicySet.decisionEntities`): a supplied entity whose
///      uid is a declared action is dropped.
///   2. **Caller-supplied attributed entities** (`event.entities`, from
///      [`EventBuilder::entity`](crate::EventBuilder::entity) / a `.log`
///      `entities(...)` envelope). These are validated against the augmented
///      `schema` — a wrong-typed or (for a `required`-attr type) incomplete
///      entity is a build-time error, folded into a fail-closed Deny. A caller
///      opting an entity into the attribute channel opts into supplying its
///      required attributes.
///   3. **Bare scope entities** — the request's principal and resource, added
///      attribute-less and **without** schema conformance, *only* for uids the
///      caller did not already supply in (2). A bare uid-only entity cannot
///      satisfy a schema-declared `required` attribute, so conformance-checking
///      it would reject essentially every request; instead it is added
///      unchecked, purely to make the scope entity *present* (so identity
///      comparisons never hit "entity does not exist").
///
/// Returns `Err` on a conformance / attribute-evaluation failure in (2); the
/// caller fails the decision closed.
fn build_entities(
    principal: &EntityUid,
    resource: &EntityUid,
    event: &EventData,
    schema: &Schema,
) -> Result<Entities, String> {
    build_entities_cached(principal, resource, event, schema, None)
}

/// Steps (2) and (3) of [`build_entities_cached`] for an event that supplies no entity: the
/// cached store of no supplied entity plus the bare scope entities, without any whose uid is a
/// declared action's (the store holds that action's entity already). They are added without
/// recomputing the transitive closure, which they cannot change: a bare entity has no parents,
/// and no entity of the store (the schema's action entities) names it as a parent. Adding them
/// otherwise as `Entities::add_entities` does (a uid already present with other content is the
/// same duplicate error).
fn bare_on_cached(
    principal: &EntityUid,
    resource: &EntityUid,
    cache: &RequestCache,
) -> Result<Entities, String> {
    use cedar_policy_core::entities::{NoEntitiesSchema, TCComputation};
    let bare = [principal, resource]
        .into_iter()
        .filter(|uid| !cache.action_uids.contains(&uid.to_string()))
        .map(|uid| {
            std::sync::Arc::new(cedar_policy::Entity::with_uid(uid.clone()).as_ref().clone())
        });
    let core: cedar_policy_core::entities::Entities = cache.empty.as_ref().clone();
    core.add_entities(
        bare,
        None::<&NoEntitiesSchema>,
        TCComputation::AssumeAlreadyComputed,
        cedar_policy_core::extensions::Extensions::all_available(),
    )
    .map(Entities::from)
    .map_err(|e| format!("scope entities: {e}"))
}

/// [`build_entities`], taking from `cache` (built for `schema`) the schema's action uids and the
/// store of no supplied entity (`Entities::from_entities` with the schema), which it computes
/// from the schema alone ([`bare_on_cached`]).
///
/// With a cache, the last step (adding the action entities) is skipped, and the store is the
/// same: step (2) builds the store with the schema, and `Entities::from_entities` with a schema
/// adds the schema's action entities, so the store already holds every entity that step adds.
/// Adding an entity deep-equal to one present leaves the present one (and Cedar recomputes the
/// same transitive closure); were they not deep-equal, that step would fail every decision.
/// Step (3)'s bare entities have no parents and are nobody's ancestors, so they change no
/// action's closure.
fn build_entities_cached(
    principal: &EntityUid,
    resource: &EntityUid,
    event: &EventData,
    schema: &Schema,
    cache: Option<&RequestCache>,
) -> Result<Entities, String> {
    // (1) The schema's action entities, whose uids supplied data may not reuse.
    let (action_entities, action_uids): (Option<Entities>, std::borrow::Cow<'_, BTreeSet<String>>) =
        match cache {
            Some(c) => (None, std::borrow::Cow::Borrowed(&c.action_uids)),
            None => {
                let entities = schema
                    .action_entities()
                    .map_err(|e| format!("action entities: {e}"))?;
                let uids = entities.iter().map(|e| e.uid().to_string()).collect();
                (Some(entities), std::borrow::Cow::Owned(uids))
            }
        };

    // (2) Caller-supplied attributed entities (with their direct parents),
    // schema-validated, without any that reuse a declared action's uid.
    let mut supplied: Vec<cedar_policy::Entity> = Vec::new();
    let mut supplied_uids: BTreeSet<String> = BTreeSet::new();
    for (uid, rec) in &event.entities {
        let entity = build_entity(uid, rec)?;
        let canonical = entity.uid().to_string();
        if action_uids.contains(&canonical) {
            continue;
        }
        supplied_uids.insert(canonical);
        supplied.push(entity);
    }
    if let Some(c) = cache
        && supplied.is_empty()
    {
        return bare_on_cached(principal, resource, c);
    }
    let store = Entities::from_entities(supplied, Some(schema))
        .map_err(|e| format!("entity conformance: {e}"))?;

    // (3) Bare scope entities for any scope uid not already supplied, added
    // without conformance (a uid-only entity cannot satisfy required attrs).
    let bare: Vec<cedar_policy::Entity> = [principal, resource]
        .into_iter()
        .filter(|uid| {
            let uid = uid.to_string();
            !supplied_uids.contains(&uid) && !action_uids.contains(&uid)
        })
        .map(|uid| cedar_policy::Entity::with_uid(uid.clone()))
        .collect();
    let store = store
        .add_entities(bare, None)
        .map_err(|e| format!("scope entities: {e}"))?;

    // The action entities, merged into the same store as the supplied/scope
    // entities (rather than replacing it) so attribute reads and action
    // membership both work. With a cache, (2) built the store with the schema:
    // it holds the action hierarchy already.
    let Some(action_entities) = action_entities else {
        return Ok(store);
    };
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
/// hoisted provider output (`provider_outputs`, already evaluated and checked
/// by `decide_at`).
///
/// Reads *only* `request_context` from the event — **nothing from `logged`**.
/// The two datasets are fully separated: the logged fields are the durable
/// temporal record; the Cedar request is built solely from the request-only
/// context plus the hoisted fields this composes. A field the request and
/// temporal both need (`input`) is supplied in both `request_context` and
/// `logged`, by design. A `Null` group is absent.
fn build_context(
    temporal_bindings: &BTreeMap<String, bool>,
    providers: &[ProviderField],
    provider_outputs: BTreeMap<String, Value>,
    event: &Event,
) -> Result<Context, String> {
    let data = event.data();

    // Every request-only context group (`input`, `system`, …) flows to Cedar
    // as `context.<group>`, verbatim (`request_context_pairs`); a group named
    // like a hoisted leaf fails the decision closed.
    let mut pairs = request_context_pairs(data)?;

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
        // silent-never-fires bug). Cedar alone decides which policies fire.
        // The runtime context remains a superset: even an action untouched by
        // provider policies receives these outputs, although its exported
        // schema omits `providers`.
        pairs.push((
            "providers".to_string(),
            value_to_expr(&Value::Object(provider_outputs)),
        ));
    }

    Context::from_pairs(pairs).map_err(|e| format!("context build: {e}"))
}

/// The event's request-only context groups as Cedar context pairs, in the
/// form every decision builds them: each group (`input`, `system`, …) becomes
/// `context.<group>`. A `null` group is absent: Cedar has no null, so it is
/// left out (and `context has <group>` is false).
///
/// A group named like an attribute the crate binds itself
/// ([`is_hoisted_name`]: a hoisted temporal leaf, or the provider record) is
/// refused, with the message the decision fails closed with. Every decision's
/// context ([`build_context`]) and every decision request an engine builds
/// ([`decision_request_with`], [`RequestCache::decision_request`], which the
/// engines' leaf maskers use) comes through here, so no decision is answered
/// over a request that supplies a leaf's value itself.
fn request_context_pairs(data: &EventData) -> Result<Vec<(String, RestrictedExpression)>, String> {
    if let Some(group) = data.request_context.keys().find(|k| is_hoisted_name(k)) {
        return Err(format!(
            "request context group `{group}` has the name of an attribute Dogwood binds itself \
             (a hoisted temporal leaf `<rule>__temporal_<j>`, or the provider record `providers`); \
             a request must not supply it, and the decision fails closed"
        ));
    }
    Ok(data
        .request_context
        .iter()
        .filter(|(_, v)| !v.is_null())
        .map(|(k, v)| (k.clone(), value_to_expr(v)))
        .collect())
}

/// Whether `name` is the name of a context attribute the crate binds itself at
/// a decision, so that a request must not supply it: the provider record
/// `providers` (`context.providers.<id>`), or a hoisted temporal leaf
/// `<rule_key>__temporal_<j>` (`cedarify::to_ast`; also its canonical
/// `dw__temporal_<j>`, and the bare `__temporal_<j>` of older names). The
/// lowered rules read their leaves there: a request that supplied one would
/// decide with its own value wherever the temporal engine binds none (a leaf it
/// does not bind, under sparse bindings), and would make the leaf look known to
/// an engine's leaf masker. The test is by the names' shape, so it needs no
/// policy set ([`decision_request_with`] has only the schema): it refuses
/// every name of that shape, hoisted by this set or not.
pub(crate) fn is_hoisted_name(name: &str) -> bool {
    if name == "providers" {
        return true;
    }
    let marker = format!("__{}_", crate::extension::Dialect::Temporal.marker());
    match name.rfind(&marker) {
        Some(i) => {
            let ordinal = name.get(i.saturating_add(marker.len())..).unwrap_or("");
            !ordinal.is_empty() && ordinal.bytes().all(|b| b.is_ascii_digit())
        }
        None => false,
    }
}

/// The Cedar request and entity store a decision at `event` is made with,
/// before its temporal leaves and its information providers are bound: the
/// request is built exactly as [`decide_at`] builds it (`request_scope`), but
/// its context holds the event's request context only (no `context.<leaf>`
/// booleans, no `context.providers` record); the entity store is the one the
/// decision authorizes against (`build_entities`). An error is the message a
/// decision would fail closed with.
pub(crate) fn decision_request(
    lowered: &Lowered,
    event: &Event,
) -> Result<(Request, Entities), String> {
    decision_request_with(event, &lowered.augmented_schema)
}

/// [`decision_request`] against the augmented Cedar schema `schema` (the one a
/// policy set was lowered to, which engines receive at `prepare`).
pub(crate) fn decision_request_with(
    event: &Event,
    schema: &Schema,
) -> Result<(Request, Entities), String> {
    let context = Context::from_pairs(request_context_pairs(event.data())?)
        .map_err(|e| format!("context build: {e}"))?;
    let (principal, action, resource) = request_scope(event)?;
    let entities = build_entities(&principal, &resource, event.data(), schema)?;
    let request = Request::new(principal, action, resource, context, None)
        .map_err(|e| format!("request build: {e}"))?;
    Ok((request, entities))
}

/// The most parsed uids a [`RequestCache`] keeps; past it, the cache starts over.
const UID_CACHE: usize = 65_536;

/// [`decision_request_with`] for many decisions against one schema
/// (`engine::DecisionRequestCache`): the store `build_entities` computes from the schema alone
/// is computed once, its no-op step (3) skipped (`build_entities_cached`), and parsed entity
/// uids are kept, because parsing one with Cedar's parser costs more than the rest of the
/// request. Every step is otherwise `decision_request_with`'s, so the results are the same.
pub(crate) struct RequestCache {
    schema: Schema,
    /// `Entities::from_entities` of no entity, with the schema (the schema's action entities,
    /// with their closure).
    empty: Entities,
    /// The uids of the schema's action entities (supplied data may not reuse them).
    action_uids: BTreeSet<String>,
    /// Entity uids parsed so far, by their text.
    uids: std::sync::Mutex<std::collections::HashMap<String, EntityUid>>,
}

impl RequestCache {
    /// The cache for `schema`. Errs as a decision against it would: when the schema's
    /// action entities do not build.
    pub(crate) fn new(schema: &Schema) -> Result<Self, String> {
        let empty = Entities::from_entities(Vec::new(), Some(schema))
            .map_err(|e| format!("entity conformance: {e}"))?;
        // Every decision's step (3) adds these; a schema whose action entities do not build
        // fails every decision, and so the cache.
        let actions = schema
            .action_entities()
            .map_err(|e| format!("action entities: {e}"))?;
        let action_uids: BTreeSet<String> = actions.iter().map(|e| e.uid().to_string()).collect();
        // Step (3) is a no-op on a store built with the schema: check it here, once.
        let with_actions = empty
            .clone()
            .add_entities(actions, None)
            .map_err(|e| format!("action hierarchy: {e}"))?;
        // `deep_eq`: `==` on stores compares their entities' uids only.
        if !with_actions.deep_eq(&empty) {
            return Err("the schema's action entities differ from the store built with it".into());
        }
        Ok(RequestCache {
            schema: schema.clone(),
            empty,
            action_uids,
            uids: Default::default(),
        })
    }

    /// The schema the cache was built for.
    pub(crate) fn schema(&self) -> &Schema {
        &self.schema
    }

    /// `parse_uid_checked`, through the cache. (A poisoned lock only bypasses it.)
    fn uid(&self, text: &str) -> Result<EntityUid, String> {
        if let Some(u) = self.uids.lock().ok().and_then(|m| m.get(text).cloned()) {
            return Ok(u);
        }
        let u = parse_uid_checked(text)?;
        if let Ok(mut m) = self.uids.lock() {
            if m.len() >= UID_CACHE {
                m.clear();
            }
            m.insert(text.to_owned(), u.clone());
        }
        Ok(u)
    }

    /// [`decision_request_with`] at `event`, against the cache's schema.
    pub(crate) fn decision_request(&self, event: &Event) -> Result<(Request, Entities), String> {
        let context = Context::from_pairs(request_context_pairs(event.data())?)
            .map_err(|e| format!("context build: {e}"))?;
        let (principal, action, resource) = request_scope_parsing(event, &|s| self.uid(s))?;
        let entities = build_entities_cached(
            &principal,
            &resource,
            event.data(),
            &self.schema,
            Some(self),
        )?;
        let request = Request::new(principal, action, resource, context, None)
            .map_err(|e| format!("request build: {e}"))?;
        Ok((request, entities))
    }
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
    event: &Event,
) -> Result<Value, String> {
    let value = eval_provider_raw(field, resolver, event)?;
    // Type the final value by the LAST stage's declared type (the one the
    // hoisted field is typed by): enum ids become entities, and a value
    // outside its enum is an error, which denies the request. Earlier stages
    // are converted the same way in `run_methods`.
    let Some(decl) = field.declaration.as_ref() else {
        return Ok(value);
    };
    let ty = match field.methods.last() {
        Some(last) => match decl.methods.get(&last.name) {
            Some(m) => &m.output_type,
            None => return Ok(value),
        },
        None => &decl.output_type,
    };
    crate::extension::provider::eval::coerce_to_declared(
        &field.invocation.key(),
        value,
        ty,
        &field.entity_types,
        &field.entity_type_names,
        "",
    )
}

/// The provider's value before conversion to its declared type: the
/// resolver's or Rhai's base output, threaded through the method chain.
fn eval_provider_raw(
    field: &ProviderField,
    resolver: Option<&dyn crate::engine::ProviderResolver>,
    event: &Event,
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
    crate::extension::provider::eval::run_methods(
        &field.invocation.key(),
        decl,
        base,
        &resolved,
        &field.entity_types,
        &field.entity_type_names,
    )
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
///   * `principal` / `resource` read the request scope entity, with
///     attributes from the entity store, matching Cedar's entity attributes
///     (`id` and `type` are attributes like any other).
///
/// An unresolvable path yields [`Value::Null`] (a provider that cannot read a
/// field sees an absent value rather than failing the whole decision).
fn resolve_provider_arg(arg: &crate::extension::provider::ast::Arg, event: &Event) -> Value {
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
fn resolve_field_path(path: &[String], event: &Event) -> Value {
    let scope = event.scope();
    let event = event.data();
    match path.first().map(String::as_str) {
        Some("principal") => resolve_scope_path(scope.principal.as_ref(), &path[1..], event),
        Some("resource") => resolve_scope_path(scope.resource.as_ref(), &path[1..], event),
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

/// Resolve a `principal` / `resource` path: take the request's scope entity,
/// then project an attribute path off it via the shared
/// [`EventData::resolve_entity_attr`] resolver. A bare root (`principal` with
/// no attribute) returns the whole entity; an attribute path defers to the
/// shared resolver (supplied attributes, nested descent, absent → `None`),
/// mapping absent to [`Value::Null`].
///
/// The entity is the request's scope entity, as the specification reads it
/// (`Provider.Call.resolve`), not the event's logged `callerPrincipal` /
/// `callerResource`. Event conformance makes an unpinned logged caller field
/// mirror the scope, so the two agree on every conforming event that logs one
/// and pins no other value into it.
pub(crate) fn resolve_scope_path(
    entity: Option<&Value>,
    rest: &[String],
    event: &EventData,
) -> Value {
    let Some(entity) = entity else {
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
    // (`seed_scope_env`) via [`EventData::resolve_entity_attr`]: attributes
    // (`id` and `type` included) are read off the supplied data, nested paths
    // descend, and an absent attribute is `None`. A provider that cannot read a field sees
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

/// The principal, action, and resource of a decision event's Cedar request.
/// Principal and resource come from the labeled scope (not event fields); the
/// action is reconstructed from the event's stored namespace path and id. A
/// decision-point event without a principal or resource in its scope is an
/// error rather than a silently fabricated request.
fn request_scope(event: &Event) -> Result<(EntityUid, EntityUid, EntityUid), String> {
    request_scope_parsing(event, &parse_uid_checked)
}

/// [`request_scope`], parsing the principal, action and resource uids with `parse` (which
/// must answer as `parse_uid_checked` does: a [`RequestCache`] caches its answers).
fn request_scope_parsing(
    event: &Event,
    parse: &dyn Fn(&str) -> Result<EntityUid, String>,
) -> Result<(EntityUid, EntityUid, EntityUid), String> {
    use crate::interpreter::value::value_uid_string;
    let scope = event.scope();
    let data = event.data();
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
    let action = qualified_action_uid(&data.namespace, &data.action);

    // A malformed principal / action / resource UID must fail closed: parsing
    // it into a fabricated fallback entity would silently authorize the
    // request against the wrong entity. Surface the parse error instead (the
    // caller turns it into a fail-closed Deny with the error in diagnostics).
    let principal = parse(&principal)?;
    let action = parse(&action)?;
    let resource = parse(&resource)?;
    Ok((principal, action, resource))
}

// ─── `.log` trace ingestion (behind `parse_trace` / `replay_log`) ────

/// Build a request-kind [`Event`] by unmarshalling a Cedar `Request`. The
/// principal/resource go into the labeled scope (what `request_scope` reads
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

pub(crate) fn action_ref(namespace: String, id: String) -> ActionRef {
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
pub(crate) fn action_scope(scope: &crate::cedarify::ScopedAction) -> ActionScope {
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
///
/// This is the shared renderer for Cedar requests and leaf-map action keys.
pub(crate) fn qualified_action_uid(namespace: &[String], action: &str) -> String {
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

/// Render an expanded scope action through the shared action UID renderer.
pub(crate) fn action_ref_uid(action: &ActionRef) -> String {
    let ty = match action.namespace.as_deref() {
        Some(namespace) => format!("{namespace}::Action"),
        None => "Action".to_string(),
    };
    qualified_action_uid(std::slice::from_ref(&ty), &action.id)
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
        // A `null` element is absent (Cedar sets hold no null); it is left out
        // rather than rendered as the empty string.
        Value::Array(items) => {
            RestrictedExpression::new_set(items.iter().filter(|v| !v.is_null()).map(value_to_expr))
        }
        Value::Object(_)
            if let Some((function, arg)) = crate::interpreter::value::extension_escape(v) =>
        {
            // Cedar's JSON escape for an extension value: the value itself.
            match function {
                "ip" | "ipaddr" => RestrictedExpression::new_ip(arg),
                "datetime" => RestrictedExpression::new_datetime(arg),
                "duration" => RestrictedExpression::new_duration(arg),
                "decimal" => RestrictedExpression::new_decimal(arg),
                // Not an extension Cedar has: an ordinary record.
                _ => record_expr(v),
            }
        }
        Value::Object(_) => record_expr(v),
        Value::Null => RestrictedExpression::new_string(String::new()),
    }
}

/// A record value as a Cedar record expression. A `Null` member is absent, as
/// it is for the conformance checks (`crate::conformance`) that run before a
/// value reaches Cedar.
fn record_expr(v: &Value) -> RestrictedExpression {
    let Value::Object(map) = v else {
        return value_to_expr(v);
    };
    let pairs: Vec<(String, RestrictedExpression)> = map
        .iter()
        .filter(|(_, v)| !matches!(v, Value::Null))
        .map(|(k, v)| (k.clone(), value_to_expr(v)))
        .collect();
    RestrictedExpression::new_record(pairs)
        .unwrap_or_else(|_| RestrictedExpression::new_string(String::new()))
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

    /// Extended escaping test covering entity IDs with control characters that
    /// can cause divergences between `entity_uid_string` and Cedar's
    /// `EntityUid::Display`.
    ///
    /// The root cause: `entity_uid_string` uses Rust's `escape_debug()` which
    /// may render control characters differently from Cedar's `EntityUid::Display`.
    /// For example, `escape_debug` renders null as `\0` but Cedar may render it
    /// as `\u{0}`. If they disagree, the string-keyed entity store lookup in
    /// `build_entities` silently fails (the `supplied_uids.contains(...)` check
    /// misses) and the entity is re-added bare (no attributes), causing `has` to
    /// return false.
    ///
    /// This test catches such divergences before they reach production. If it
    /// fails, `entity_uid_string` must be updated to match Cedar's rendering.
    #[test]
    fn entity_uid_string_matches_cedar_on_control_chars() {
        use cedar_policy::{EntityId, EntityTypeName, EntityUid};
        use std::str::FromStr;
        let cases: &[(&str, &str)] = &[
            // Regression case: null + bell:
            ("a", "\0\u{7}"),
            // Individual control characters:
            ("a", "\0"),     // null — escape_debug renders as \0
            ("a", "\u{7}"),  // bell — escape_debug renders as \u{7}
            ("a", "\u{8}"),  // backspace — escape_debug renders as \u{8}
            ("a", "\t"),     // tab — escape_debug renders as \t
            ("a", "\n"),     // newline — escape_debug renders as \n
            ("a", "\r"),     // carriage return — escape_debug renders as \r
            ("a", "\u{1b}"), // escape char
            ("a", "\u{7f}"), // DEL
            // Multiple control chars combined:
            ("a", "\0\0\u{4}"),
            ("a", "\u{1}\u{2}\u{3}"), // low controls
            ("a", "\u{10}\u{1f}"),    // upper C0 range
            // Mix of control + printable:
            ("a", "hello\0world"),
            ("a", "\nnewline\n"),
            ("a", "tab\there"),
            // Single printable chars:
            ("a", "e"),
            ("a", "R"),
            // Whitespace that escape_debug may handle differently:
            ("a", " "), // plain space
            ("a", "  leading"),
            ("a", "trailing "),
            // Unicode above BMP (escape_debug passes through, Cedar should too):
            ("a", "emoji\u{1f600}"),
            ("a", "\u{10000}"), // first supplementary char
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
                "entity_uid_string diverged from Cedar's rendering for ty={ty:?} id={id:?}\n  \
                 ours:  {ours:?}\n  cedar: {cedar:?}"
            );
        }
    }

    /// Verify the full round-trip: entity_uid_string → EntityUid::from_str →
    /// EntityUid::to_string produces the same string back. This is the exact
    /// path `build_entities` takes: store key is `entity_uid_string(ty, id)`,
    /// then `build_entity` parses it with `from_str`, and `supplied_uids` is
    /// compared against `request.principal().to_string()`.
    #[test]
    fn entity_uid_string_roundtrips_through_cedar_parser() {
        use cedar_policy::EntityUid;
        use std::str::FromStr;
        let ids: &[&str] = &[
            "\0\u{7}", // null + bell regression case
            "\0",
            "\u{7}",
            "normal",
            "a\"b",
            "a\\b",
            "\t\n\r",
            "\u{1b}[31m", // ANSI escape sequence
            "",
        ];
        for id in ids {
            let uid_str = crate::interpreter::value::entity_uid_string("a", id);
            // Step 1: parse it back (as build_entity does)
            let parsed = EntityUid::from_str(&uid_str).unwrap_or_else(|e| {
                panic!("EntityUid::from_str failed for id={id:?} (uid_str={uid_str:?}): {e}")
            });
            // Step 2: render it (as request.principal().to_string() does)
            let rendered = parsed.to_string();
            assert_eq!(
                uid_str, rendered,
                "round-trip failed for id={id:?}\n  \
                 entity_uid_string: {uid_str:?}\n  \
                 from_str.to_string: {rendered:?}"
            );
        }
    }
}
