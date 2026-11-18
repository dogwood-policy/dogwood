//! Pluggable decision and temporal-evaluation backends.
//!
//! The [`Authorizer`](crate::Authorizer) is assembled from two swappable
//! pieces, each with a built-in default and a trait a caller can implement to
//! replace it:
//!
//!   * a [`PolicyEngine`] — makes the actual authorization decision from a
//!     request + entities against a fixed policy set. The default,
//!     [`CedarPolicyEngine`], evaluates locally with the `cedar-policy`
//!     crate; its shape deliberately matches common policy-engine
//!     `IsAuthorized` APIs, so a caller can implement [`PolicyEngine`] by
//!     delegating to an external authorization service.
//!   * a [`TemporalEngine`] — computes the boolean value of each hoisted
//!     `temporal { … }` leaf for the current decision point. The default,
//!     [`InMemoryTemporalEngine`], keeps the event history in memory and
//!     re-runs the MFOTL interpreter; a caller can implement
//!     [`TemporalEngine`] to *compile* the leaves at `prepare` time and
//!     *evaluate* them against a database.
//!
//! Both are installed by default via [`Authorizer::new`](crate::Authorizer::new);
//! use [`Authorizer::builder`](crate::Authorizer::builder) to substitute
//! either or both.

use std::collections::{BTreeMap, BTreeSet};

use cedar_policy::{Authorizer as CedarAuthorizer, Entities, PolicySet, Request, Schema};

use crate::api::Error;
use crate::authorize::Decision;
use crate::interpreter::eval;
use crate::interpreter::value::{Event, Trace, Value, cedar_decimal_value};
use crate::leaf_map::DecisionLeafMap;

/// The hoisted temporal leaf a [`TemporalEngine`] prepares and evaluates: a
/// generated `id` (the `context.<id>` slot its boolean is bound into), the
/// action scope its rule pins, and the parsed temporal condition. A
/// compiling engine reads `condition` to build its query; the in-memory
/// engine interprets it directly.
pub use crate::api::{ActionRef, ActionScope, EventPinRoot, ExtensionId, TemporalField};
/// The parsed temporal condition carried by a [`TemporalField`].
pub use crate::extension::temporal::Temporal;

// ─── The policy-decision seam ─────────────────────────────────────────

/// One authorization query handed to a [`PolicyEngine`]: the Cedar request
/// (principal / action / resource / context) and the in-line entities it is
/// evaluated against. This is the input to a policy engine's `IsAuthorized`
/// operation.
#[derive(Debug, Clone, Copy)]
pub struct AuthorizationRequest<'a> {
    /// The `<principal, action, resource, context>` tuple.
    pub request: &'a Request,
    /// The entity graph the policies may reference. Dogwood supplies an empty
    /// set (its state lives in the temporal history, not an entity graph),
    /// but the field is here so a [`PolicyEngine`] backed by a remote policy store can forward
    /// whatever entities it manages.
    pub entities: &'a Entities,
}

/// The decision a [`PolicyEngine`] returns — the shape of a policy engine's
/// `IsAuthorized` response: an allow/deny [`Decision`], the ids of the
/// policies that determined it, and any evaluation errors.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct AuthorizationDecision {
    /// `Allow` or `Deny`.
    pub decision: Decision,
    /// The ids of the determining policies (for an implicit `Deny`, empty),
    /// as the underlying engine names them. Dogwood maps these back to the
    /// originating `.dw` rules.
    pub determining_policy_ids: Vec<String>,
    /// Evaluation errors encountered by the engine (folded into the Dogwood
    /// response's diagnostics — evaluation degrades to `Deny`, it does not
    /// throw).
    pub errors: Vec<String>,
}

/// The full outcome of one policy-engine decision: an
/// [`AuthorizationDecision`] plus the **erroring policies** by id. Returned by
/// [`PolicyEngine::authorize`].
///
/// `#[non_exhaustive]`: build one with [`From<AuthorizationDecision>`] and
/// [`with_erroring_policy`](AuthorizationOutcome::with_erroring_policy).
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub struct AuthorizationOutcome {
    /// `Allow` or `Deny`.
    pub decision: Decision,
    /// The ids of the determining policies, as in
    /// [`AuthorizationDecision::determining_policy_ids`].
    pub determining_policy_ids: Vec<String>,
    /// The policies that raised an evaluation error, as `(policy id, error
    /// message)`; the message does not repeat the id. Empty when the engine
    /// does not attribute errors to policies.
    pub erroring_policies: Vec<(String, String)>,
    /// Every evaluation error as text, as in [`AuthorizationDecision::errors`]
    /// (including those also listed in `erroring_policies`).
    pub errors: Vec<String>,
}

impl From<AuthorizationDecision> for AuthorizationOutcome {
    fn from(d: AuthorizationDecision) -> Self {
        AuthorizationOutcome {
            decision: d.decision,
            determining_policy_ids: d.determining_policy_ids,
            erroring_policies: Vec::new(),
            errors: d.errors,
        }
    }
}

impl AuthorizationOutcome {
    /// Record that policy `id` raised `message` while the request was decided.
    pub fn with_erroring_policy(
        mut self,
        id: impl Into<String>,
        message: impl Into<String>,
    ) -> Self {
        self.erroring_policies.push((id.into(), message.into()));
        self
    }
}

/// Makes the authorization decision for a request against a fixed policy set.
///
/// The policy set + schema are supplied once, at [`prepare`](PolicyEngine::prepare)
/// (like creating/populating a policy store); each
/// [`is_authorized`](PolicyEngine::is_authorized) then decides one request.
pub trait PolicyEngine: Send {
    /// Install the (lowered Cedar) policies and their schema. Called once when
    /// the [`Authorizer`](crate::Authorizer) is built, and again by
    /// [`Authorizer::update_policies`](crate::Authorizer::update_policies) for
    /// an engine whose [`supports_policy_update`](PolicyEngine::supports_policy_update)
    /// is `true`. A local engine keeps a reference/clone; a
    /// remote-policy-store-backed engine might upsert them into a policy store
    /// here.
    fn prepare(&mut self, policies: &PolicySet, schema: &Schema) -> Result<(), Error>;

    /// Decide one authorization request. Must not panic — surface problems
    /// through [`AuthorizationDecision::errors`] with a fail-closed `Deny`.
    fn is_authorized(&self, request: AuthorizationRequest<'_>) -> AuthorizationDecision;

    /// Decide one request and also report which policies erred. The
    /// [`Authorizer`](crate::Authorizer) calls this (not
    /// [`is_authorized`](PolicyEngine::is_authorized)) and maps the erroring ids
    /// into [`Diagnostics::erroring`](crate::Diagnostics::erroring).
    ///
    /// The default delegates to `is_authorized` and reports no erroring
    /// policies, so an existing engine behaves exactly as before. Override it
    /// when the engine can attribute errors to policies (the built-in
    /// [`CedarPolicyEngine`] does).
    fn authorize(&self, request: AuthorizationRequest<'_>) -> AuthorizationOutcome {
        AuthorizationOutcome::from(self.is_authorized(request))
    }

    /// Whether [`prepare`](PolicyEngine::prepare) may be called again with a
    /// new policy set, replacing the old one, by
    /// [`Authorizer::update_policies`](crate::Authorizer::update_policies).
    /// Default `false`: an engine bound to a pre-populated remote store, say,
    /// would keep deciding with the old policies. Such an engine is replaced
    /// instead ([`Authorizer::update_policies_with_engine`](crate::Authorizer::update_policies_with_engine)).
    fn supports_policy_update(&self) -> bool {
        false
    }
}

/// The built-in [`PolicyEngine`]: evaluate locally with the `cedar-policy`
/// crate's authorizer. Holds the prepared policy set.
#[derive(Debug, Default)]
pub struct CedarPolicyEngine {
    policies: Option<PolicySet>,
}

impl CedarPolicyEngine {
    pub fn new() -> Self {
        CedarPolicyEngine { policies: None }
    }
}

impl PolicyEngine for CedarPolicyEngine {
    fn prepare(&mut self, policies: &PolicySet, _schema: &Schema) -> Result<(), Error> {
        self.policies = Some(policies.clone());
        Ok(())
    }

    fn is_authorized(&self, request: AuthorizationRequest<'_>) -> AuthorizationDecision {
        let outcome = self.authorize(request);
        AuthorizationDecision {
            decision: outcome.decision,
            determining_policy_ids: outcome.determining_policy_ids,
            errors: outcome.errors,
        }
    }

    fn authorize(&self, request: AuthorizationRequest<'_>) -> AuthorizationOutcome {
        let Some(policies) = self.policies.as_ref() else {
            return AuthorizationOutcome {
                decision: Decision::Deny,
                determining_policy_ids: Vec::new(),
                erroring_policies: Vec::new(),
                errors: vec!["policy engine was not prepared".to_string()],
            };
        };
        let response =
            CedarAuthorizer::new().is_authorized(request.request, policies, request.entities);
        AuthorizationOutcome {
            decision: response.decision(),
            determining_policy_ids: response
                .diagnostics()
                .reason()
                .map(|pid| AsRef::<str>::as_ref(pid).to_string())
                .collect(),
            erroring_policies: response
                .diagnostics()
                .errors()
                .map(|e| match e {
                    cedar_policy::AuthorizationError::PolicyEvaluationError(e) => (
                        AsRef::<str>::as_ref(e.policy_id()).to_string(),
                        e.inner().to_string(),
                    ),
                })
                .collect(),
            errors: response
                .diagnostics()
                .errors()
                .map(|e| e.to_string())
                .collect(),
        }
    }

    fn supports_policy_update(&self) -> bool {
        true
    }
}

// ─── The temporal-evaluation seam ────────────────────────────────────

/// The per-leaf temporal booleans for one decision point, keyed by the
/// leaf's hoisted id (e.g. `__temporal_0`). Bound into `context.<id>` before
/// the [`PolicyEngine`] decides.
pub type TemporalBindings = BTreeMap<ExtensionId, bool>;

/// A field to **partition** temporal history on: one of the event schema's
/// universal symmetric pins. When an [`Authorizer`](crate::Authorizer) runs in
/// partition mode (see
/// [`AuthorizerBuilder::partition_temporal`](crate::AuthorizerBuilder::partition_temporal)),
/// the temporal engine keeps a separate monitor / trace per distinct value of
/// this key tuple and evaluates the **non-relativized** leaves within each
/// partition — the equivalent, and cheaper, alternative to the pin-relativization
/// rewrite (a partition physically contains only its own key's events, so a
/// plain formula already computes the key-local semantics the rewrite otherwise
/// encodes in-formula).
///
/// An engine must key each event's partition on **the pinned field's logged
/// value** — `event.field_path(field_path)` — so that "event E is in decision
/// D's partition" is identical to "E is one of D's μ-events". This is forced by
/// how μ works: a μ-branch is a predicate, and a predicate can only address a
/// candidate event through its **logged** record (`match_args` reads
/// `event.field_path(&arg.field_path())`); the pin's request-side `context_path` only
/// ever names the *decision* event's scope/context on the comparison's other
/// side, never a candidate's field. So the sole μ-addressable handle on a
/// candidate — and thus the only sound partition key — is the logged
/// `field_path`. (Routing on the request-side scope/context value instead would
/// silently send history / `response` events, which carry the logged field but
/// no matching request-side value, to a bogus partition.)
///
/// Candidates are matched identically either way — both μ and this routing read
/// `candidate.logged[field_path]` — so the only place the two could diverge is
/// the *decision* event's own key: μ correlates candidates against the decision
/// event's request-side `context_path` value, while routing keys the decision
/// event by its `logged[field_path]`. These agree when the decision event
/// mirrors the two (`logged[field_path] == request_side[context_path]`). Under
/// the default (strict) mirror rule, event conformance rejects an event that
/// breaks the mirror, so an ingested event always routes by its own key. One
/// public path does not log the pinned field: [`Event::from_request`] mirrors
/// only the `input` context group and `callerPrincipal` / `callerResource` into
/// `logged`, so under a context pin on a non-`input` field, or a scope pin under
/// another name (`pin actor = principal`), the event it builds is rejected.
/// That path is a single-decision (`ts = 0`) interop shim; a partitioned
/// deployment supplies the pinned field to the logged record like any other
/// correlated field. `root` and `context_path` are retained for diagnostics but
/// are **not** the routing key.
///
/// [`Event::from_request`]: crate::Event::from_request
///
/// The built-in [`InMemoryTemporalEngine`] keys on `field_path` via
/// `partition_value_of`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PartitionKey {
    /// The dotted path of the pinned **logged field** on the event — the key
    /// partitions are routed by (`["callerPrincipal"]`, `["sessionId"]`,
    /// `["__drupe", "session_id"]`). This is the field μ matches candidates on.
    /// Mirrors [`EventPin::field_path`](crate::api::EventPin::field_path).
    pub field_path: Vec<String>,
    /// Which request root the pin's `context_path` is anchored to (scope entity
    /// vs context field). Diagnostic only — not used for routing.
    pub root: EventPinRoot,
    /// The pin's request-side path (no leading `context`). Diagnostic only — the
    /// value that, on a well-formed decision event, equals the logged
    /// `field_path`. Not used for routing.
    pub context_path: Vec<String>,
}

/// Computes the boolean value of each hoisted `temporal { … }` leaf.
///
/// The lifecycle has three points:
///   * [`prepare`](TemporalEngine::prepare) — once, when the authorizer is
///     built. A compiling backend turns each leaf into a query and creates
///     its tables here.
///   * [`observe`](TemporalEngine::observe) — for *every* event ingested
///     (decision or history-only), in order. A backend persists the event
///     (in memory, or an insert into a database).
///   * [`evaluate`](TemporalEngine::evaluate) — at each decision point,
///     *after* that point's event has been observed. Returns each leaf's
///     boolean for the current timepoint (an in-memory backend re-runs the
///     interpreter; a database backend queries its compiled functions).
pub trait TemporalEngine: Send {
    /// Prepare (e.g. compile) the temporal `leaves` against the schema. Called
    /// once at authorizer-build time.
    ///
    /// `events` carries the declared signature of every event the policy set can
    /// see, including each field's dotted path and type. A compiling engine needs
    /// those types to emit comparisons that agree with this crate's equality —
    /// notably for `decimal`, where one value has several spellings, so comparing
    /// as text diverges from [`Value::dom_eq`](crate::Value::dom_eq). An engine
    /// that interprets rather than compiles has no use for them.
    fn prepare(
        &mut self,
        leaves: &[TemporalField],
        schema: &Schema,
        events: &[crate::EventSignature],
    ) -> Result<(), Error>;

    /// Record one event into the history the temporal leaves see. Called for
    /// every ingested event, in timestamp order, before any
    /// [`evaluate`](TemporalEngine::evaluate) that includes it.
    fn observe(&mut self, event: &Event);

    /// [`observe`](TemporalEngine::observe), reporting whether the event was
    /// recorded. An `Err` means the engine did not record the event, or cannot
    /// say that it did: [`Rejection::Nonconforming`](crate::Rejection::Nonconforming)
    /// for an event the engine's own checks reject, and
    /// [`Rejection::Unavailable`](crate::Rejection::Unavailable) for a write that
    /// failed (a database out of reach, a retry budget spent, a reading the
    /// engine cannot store, or a commit whose outcome is unknown, which the
    /// reason then says). No later decision can rely on such an event, so the
    /// caller must learn of it: [`Authorizer::submit`](crate::Authorizer::submit)
    /// returns the rejection for a history event, and fails a decision event
    /// closed without evaluating it.
    ///
    /// The authorizer calls this, not `observe`. The default calls `observe` and
    /// reports success, so an engine that cannot fail (or reports its failure at
    /// the next `evaluate`, as engines written against Dogwood 1.1 do) needs no
    /// change; an engine whose writes can fail overrides it.
    fn try_observe(&mut self, event: &Event) -> Result<(), crate::Rejection> {
        self.observe(event);
        Ok(())
    }

    /// The deployment generation of the leaves the next [`prepare`](TemporalEngine::prepare)
    /// installs ([`PolicySetVersion::generation`](crate::PolicySetVersion::generation)): the
    /// builder's [`generation`](crate::AuthorizerBuilder::generation) at build, and one more
    /// at each [`update_policies`](crate::Authorizer::update_policies). The authorizer calls
    /// it before every `prepare`. An engine whose instances share history across processes
    /// uses it to order deployments: a key decided under one generation must never be
    /// decided again under an older one. Default: ignored.
    fn set_generation(&mut self, _generation: u64) {}

    /// Evaluate every leaf at the current decision point (the most recently
    /// observed event). Returns each leaf's boolean keyed by its id. A failure
    /// (e.g. the database is unreachable) fails the decision closed.
    fn evaluate(&mut self) -> Result<TemporalBindings, String>;

    /// Whether this engine can partition its history by a [`PartitionKey`] tuple
    /// (a separate monitor / trace per distinct key value). Default `false`, so
    /// an engine that does not implement partitioning keeps receiving the
    /// relativized leaves and behaves exactly as before. An engine that returns
    /// `true` must honor [`set_partition_keys`](TemporalEngine::set_partition_keys)
    /// and route each observed event to its key's partition.
    ///
    /// The [`Authorizer`](crate::Authorizer) builder consults this: if the caller
    /// asked for partitioned evaluation
    /// ([`partition_temporal`](crate::AuthorizerBuilder::partition_temporal)) but
    /// the engine returns `false`, the build fails closed rather than silently
    /// running global (relativized) semantics.
    fn supports_partitioning(&self) -> bool {
        false
    }

    /// Install the partition keys. Called by the authorizer builder **before**
    /// [`prepare`](TemporalEngine::prepare), and only when the caller opted into
    /// partitioned evaluation against an engine whose
    /// [`supports_partitioning`](TemporalEngine::supports_partitioning) is `true`
    /// and the schema declares at least one universal symmetric pin. When this is
    /// called, the `leaves` subsequently handed to `prepare` are the
    /// **non-relativized** ones. Default no-op (for engines that do not partition).
    fn set_partition_keys(&mut self, _keys: &[PartitionKey]) {}

    /// Install the **authored** leaves: the non-relativized leaves, parallel by position to the
    /// `leaves` the next [`prepare`](TemporalEngine::prepare) receives (the same ids, in the same
    /// order). Called by the [`Authorizer`](crate::Authorizer) **before** every `prepare`, at
    /// build and at a policy update, whether or not evaluation is partitioned. Under partitioned
    /// evaluation they are the leaves `prepare` receives; under global evaluation with universal
    /// symmetric pins, `prepare` receives their relativized form. An engine that compiles the
    /// authored leaf itself, applying the visibility the schema's pins define, reads them here
    /// (the leaf the specification's conformance bridge exports). Default: ignored, so every
    /// other engine behaves exactly as before.
    fn set_authored_leaves(&mut self, _authored: &[TemporalField]) {}

    /// Whether [`prepare`](TemporalEngine::prepare) may be called again, with a
    /// new policy set's leaves, while keeping the history observed so far —
    /// the live update of
    /// [`Authorizer::update_policies`](crate::Authorizer::update_policies).
    /// Default `false`: an engine that keys state by leaf name or position
    /// would misread its history after a reorder, so it must opt in.
    ///
    /// An engine that returns `true` defines what the new leaves see of the
    /// past (its *update reading*) and documents it. Partition keys are never
    /// changed by an update ([`set_partition_keys`](TemporalEngine::set_partition_keys)
    /// is not called again).
    fn supports_policy_update(&self) -> bool {
        false
    }
}

/// The built-in [`TemporalEngine`]: keep the event history in memory and
/// evaluate each leaf with the in-process MFOTL interpreter over the trace so
/// far. `prepare` records the leaves (nothing to compile); `observe` appends to
/// an in-memory event log; `evaluate` runs the interpreter at the last timepoint.
///
/// Two modes (see `Mode`):
///   * **Global** (default) — one trace holding every event; the relativized
///     leaves are evaluated over it.
///   * **Partitioned** — a separate trace per [`PartitionKey`] value; each event
///     is routed to its key's trace, and the **non-relativized** leaves are
///     evaluated within the current event's partition. Because the partition
///     physically contains only its own key's events, a plain leaf computes the
///     same verdict the relativization rewrite computes over the global trace.
///
/// [`slice_leaves`](Self::slice_leaves) optionally avoids interpreting leaves
/// that the current decision cannot read.
#[derive(Debug)]
pub struct InMemoryTemporalEngine {
    leaves: Vec<TemporalField>,
    mode: Mode,
    slicing: bool,
    leaf_map: Option<DecisionLeafMap>,
    computed: BTreeSet<ExtensionId>,
}

enum Plan<'a> {
    All,
    Only(&'a BTreeSet<ExtensionId>),
}

impl Plan<'_> {
    fn includes(&self, id: &str) -> bool {
        match self {
            Plan::All => true,
            Plan::Only(needed) => needed.contains(id),
        }
    }
}

/// The history representation: one global trace, or a trace per partition key.
#[derive(Debug)]
enum Mode {
    Global(Trace),
    Partitioned {
        keys: Vec<PartitionKey>,
        /// One trace per distinct partition-key value (encoded, see
        /// [`InMemoryTemporalEngine::partition_value_of`]).
        traces: BTreeMap<String, Trace>,
        /// The partition the most recently observed event was routed to, so
        /// `evaluate` runs against the right trace.
        last: Option<String>,
    },
}

impl Default for InMemoryTemporalEngine {
    fn default() -> Self {
        InMemoryTemporalEngine {
            leaves: Vec::new(),
            mode: Mode::Global(Trace::default()),
            slicing: false,
            leaf_map: None,
            computed: BTreeSet::new(),
        }
    }
}

impl InMemoryTemporalEngine {
    pub fn new() -> Self {
        InMemoryTemporalEngine::default()
    }

    /// Compute only leaves the decision can read, binding the rest to `false`.
    ///
    /// This is opt-in because direct callers of
    /// [`evaluate`](TemporalEngine::evaluate) may expect every leaf's raw value,
    /// independently of a decision.
    ///
    /// ```no_run
    /// # use dogwood_language::{Authorizer, InMemoryTemporalEngine, LoweredPolicySet};
    /// # fn f(policies: LoweredPolicySet) -> Result<(), Box<dyn std::error::Error>> {
    /// let authorizer = Authorizer::builder(policies)
    ///     .temporal_engine(InMemoryTemporalEngine::new().slice_leaves())
    ///     .build()?;
    /// # Ok(()) }
    /// ```
    ///
    /// Slicing applies in both global and partitioned modes. See
    /// [`crate::leaf_map`] for the selection contract and fallbacks.
    pub fn slice_leaves(mut self) -> Self {
        self.slicing = true;
        self
    }

    /// Return the leaf ids interpreted by the last `evaluate`.
    ///
    /// Empty before the first evaluation.
    pub fn computed_leaves(&self) -> &BTreeSet<ExtensionId> {
        &self.computed
    }

    /// Return the installed leaf map, or `None` when slicing is disabled or the
    /// engine has not been prepared.
    pub fn leaf_map(&self) -> Option<&DecisionLeafMap> {
        self.leaf_map.as_ref()
    }

    /// Replace the map for negative-control testing.
    #[doc(hidden)]
    pub fn install_leaf_map(&mut self, map: DecisionLeafMap) {
        self.leaf_map = Some(map);
    }

    /// Encode one event's partition-key tuple to a stable string. Two events map
    /// to the same partition iff their key values are equal. The per-value
    /// encoding is variant-tagged so distinct [`Value`] variants never collide
    /// (an entity uid and a same-looking string stay in different partitions).
    ///
    /// Reads each key **exactly as the μ-encoding matches candidates**: the
    /// event's **logged** field at `field_path` (the same `event.field_path(..)`
    /// the predicate matcher reads), so a partition is exactly the set of an
    /// event's μ-events — regardless of whether the event also carries a
    /// request-side scope/context value (which history / `response` events do
    /// not). A key whose logged field is absent (a malformed pinned event — μ
    /// cannot match it either) encodes to a distinct `<none>` marker rather than
    /// aliasing onto a real value. Multi-key values are dom-canonicalized before
    /// encoding so `1.5` and `1.50` share a partition, matching μ's `dom_eq`.
    fn partition_value_of(event: &Event, keys: &[PartitionKey]) -> String {
        keys.iter()
            // A logged `null` is an absent field (the specification has no
            // null), so it files under `<none>`, as an unlogged one does.
            .map(|k| match event.data().logged_value(&k.field_path) {
                Some(v) => partition_value_key(v),
                None => "<none>".to_string(),
            })
            .collect::<Vec<_>>()
            .join("\u{1f}") // unit separator — cannot appear in an identifier/uid
    }
}

/// Canonical rendering of a partition-key [`Value`], such that
/// `encode == encode` **iff** the values are equal under [`Value::dom_eq`] — the
/// same equality μ's predicate matcher uses. Three properties make it sound:
///
/// * **set-canonical**: an array is rendered as a set (its element keys sorted
///   and deduplicated, `null` elements left out), and a `null` record member is
///   left out, so `["a", "b"]` and `["b", "a"]` share a partition.
/// * **dom-canonical**: accepted decimals are rendered canonically from Cedar's
///   fixed-point numeric value, while rejected spellings retain exact text under
///   a separate tag. Thus every pair agrees with `dom_eq`, including leading
///   zeroes and signed zero.
/// * **injective / self-delimiting**: every component is length-prefixed
///   (`<tag><byte-len>:<bytes>`), so an arbitrary string, entity id, or nested
///   value — which may contain any character including the multi-key separator —
///   can never be confused with a different decomposition. The leading tag keeps
///   variants disjoint (an entity uid never aliases a same-looking string).
#[doc(hidden)]
#[inline]
pub fn partition_value_key(value: &Value) -> String {
    // Length-prefix a rendered body so concatenations are unambiguous even when
    // the body contains the multi-key separator or nested delimiters.
    fn framed(tag: char, body: &str) -> String {
        format!("{tag}{}:{body}", body.len())
    }
    match value {
        Value::Null => "n0:".to_string(),
        Value::Bool(b) => framed('b', &b.to_string()),
        Value::Int(i) => framed('i', &i.to_string()),
        // Match `dom_eq`: canonicalize the decimal text before framing.
        Value::Decimal(s) => framed('d', &canon_decimal_for_partition(s)),
        Value::String(s) => framed('s', s),
        Value::Entity { ty, id } => framed('e', &format!("{ty}::\"{id}\"")),
        Value::Array(items) => {
            // An array is a set (`Value::dom_eq`): render its elements' keys
            // sorted and deduplicated, so the key depends on the set only. A
            // `null` element is absent. Each element key is self-delimiting, so
            // the concatenation of a sorted, duplicate-free list stays injective.
            let mut keys: Vec<String> = items
                .iter()
                .filter(|v| !v.is_null())
                .map(partition_value_key)
                .collect();
            keys.sort_unstable();
            keys.dedup();
            framed('a', &keys.concat())
        }
        Value::Object(members) => {
            // BTreeMap iterates in key order, so equal objects render identically.
            // A `null` member is absent (`Value::dom_eq`), so it is not rendered.
            let body: String = members
                .iter()
                .filter(|(_, v)| !v.is_null())
                .map(|(k, v)| format!("{}:{}{}", k.len(), k, partition_value_key(v)))
                .collect();
            framed('o', &body)
        }
    }
}

/// Canonicalize accepted decimals to Cedar's fixed-point value. Rejected
/// spellings retain their exact text under a separate tag, matching `dom_eq`:
/// Cedar-equivalent spellings share a key, while rejected text only equals
/// itself and cannot collide with an accepted value.
fn canon_decimal_for_partition(s: &str) -> String {
    match cedar_decimal_value(s) {
        Some(value) => {
            let value = i128::from(value);
            let sign = if value < 0 { "-" } else { "" };
            let magnitude = value.abs();
            let whole = magnitude / 10_000;
            let fraction = magnitude % 10_000;
            if fraction == 0 {
                format!("{sign}{whole}")
            } else {
                let fraction = format!("{fraction:04}");
                format!("{sign}{whole}.{}", fraction.trim_end_matches('0'))
            }
        }
        None => format!("x{s}"),
    }
}

impl TemporalEngine for InMemoryTemporalEngine {
    fn prepare(
        &mut self,
        leaves: &[TemporalField],
        schema: &Schema,
        _events: &[crate::EventSignature],
    ) -> Result<(), Error> {
        self.leaves = leaves.to_vec();
        // A map is valid only for the leaves and schema from this prepare call.
        self.leaf_map = self
            .slicing
            .then(|| DecisionLeafMap::build(&self.leaves, schema));
        self.computed.clear();
        Ok(())
    }

    fn observe(&mut self, event: &Event) {
        match &mut self.mode {
            Mode::Global(trace) => trace.points.push(event.clone()),
            Mode::Partitioned { keys, traces, last } => {
                let key = Self::partition_value_of(event, keys);
                traces
                    .entry(key.clone())
                    .or_default()
                    .points
                    .push(event.clone());
                *last = Some(key);
            }
        }
    }

    fn evaluate(&mut self) -> Result<TemporalBindings, String> {
        // The decision point is the most recently observed event, in the trace
        // it was routed to (the whole global trace, or its own partition).
        let trace = match &self.mode {
            Mode::Global(trace) => trace,
            Mode::Partitioned { traces, last, .. } => {
                let key = last.as_deref().ok_or("no event observed")?;
                traces.get(key).ok_or("no event observed")?
            }
        };
        let i = trace.len().checked_sub(1).ok_or("no event observed")?;
        // Missing map answers conservatively select every leaf.
        let needed = self
            .leaf_map
            .as_ref()
            .and_then(|map| map.needed_for(&trace.points[i]));
        let plan = match &needed {
            Some(ids) => Plan::Only(ids),
            None => Plan::All,
        };
        let env = eval::request_env(trace, i);
        let mut computed = BTreeSet::new();
        let bindings: TemporalBindings = self
            .leaves
            .iter()
            .map(|f| {
                // Cedar requires a binding even for leaves this decision cannot read.
                if !plan.includes(&f.id) {
                    return (f.id.clone(), false);
                }
                computed.insert(f.id.clone());
                let holds = eval::eval_condition(trace, i, &env, &f.condition.condition);
                (f.id.clone(), holds)
            })
            .collect();
        // `trace`/`env` borrow `self` immutably; both are dead by here.
        self.computed = computed;
        Ok(bindings)
    }

    fn supports_partitioning(&self) -> bool {
        true
    }

    fn set_partition_keys(&mut self, keys: &[PartitionKey]) {
        self.mode = Mode::Partitioned {
            keys: keys.to_vec(),
            traces: BTreeMap::new(),
            last: None,
        };
    }

    /// The in-memory engine keeps every observed event and re-runs the
    /// interpreter at each decision, so after an update every leaf — new,
    /// edited or kept — is evaluated over the whole retained history (the
    /// retrospective reading).
    fn supports_policy_update(&self) -> bool {
        true
    }
}

/// The Cedar request and entity store an [`Authorizer`](crate::Authorizer)
/// builds for a decision at `event`, before it binds the temporal leaves and
/// the information providers, against `schema`, the augmented Cedar schema the
/// policy set was lowered to (the one a [`TemporalEngine`] receives at
/// [`prepare`](TemporalEngine::prepare), and
/// [`LoweredPolicySet::cedar_schema`](crate::LoweredPolicySet::cedar_schema)).
///
/// [`LoweredPolicySet::decision_request`](crate::LoweredPolicySet::decision_request)
/// is this with the set's own schema; an engine that holds only the schema (it
/// partially evaluates the policies its [`PolicyEngine`] was prepared with)
/// calls this. The request's context holds the event's request context only;
/// the entity store is the decision's. The error is the message the decision
/// fails closed with; in particular, a request context group named like an
/// attribute the crate binds itself (a hoisted temporal leaf
/// `<rule_key>__temporal_<j>`, or the provider record `providers`) is refused,
/// as every decision refuses it.
pub fn decision_request(
    event: &Event,
    schema: &Schema,
) -> Result<(cedar_policy::Request, cedar_policy::Entities), String> {
    crate::api::decision_request_with(event, schema)
}

/// [`decision_request`] for many decisions against one schema: what the entity store takes
/// from the schema alone (the store of an event that supplies no entity, which holds the
/// schema's action entities) is computed once, at [`new`](Self::new), and parsed entity uids are
/// kept (at most 65,536; then the cache starts over). Parsing a uid costs more than the rest of
/// the request. A store built with the schema already holds its action hierarchy, so the last
/// step of `decision_request`, which adds it again and changes nothing, is skipped (`new`
/// checks that it changes nothing). Otherwise every step is [`decision_request`]'s, and the
/// request and the store are the same. It can be shared between threads. Additive.
pub struct DecisionRequestCache(crate::api::RequestCache);

impl DecisionRequestCache {
    /// The cache for `schema` (the augmented schema an engine receives at
    /// [`prepare`](TemporalEngine::prepare)). Errs, with the message a decision would fail
    /// closed with, when the schema's action entities do not build.
    pub fn new(schema: &Schema) -> Result<Self, String> {
        crate::api::RequestCache::new(schema).map(DecisionRequestCache)
    }

    /// [`decision_request`]`(event, schema)`, `schema` being the cache's.
    pub fn decision_request(
        &self,
        event: &Event,
    ) -> Result<(cedar_policy::Request, cedar_policy::Entities), String> {
        self.0.decision_request(event)
    }

    /// The schema the cache was built for.
    pub fn schema(&self) -> &Schema {
        self.0.schema()
    }
}

impl std::fmt::Debug for DecisionRequestCache {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("DecisionRequestCache")
            .finish_non_exhaustive()
    }
}

// ─── The provider-resolution seam (compute a provider's value yourself) ─

/// One information-provider invocation handed to a [`ProviderResolver`]: the
/// fully-qualified provider name and its already-resolved call arguments.
///
/// The arguments are Dogwood [`Value`]s (request fields resolved, literals as
/// written) — the resolver never touches the Rhai sandbox, so it may do
/// whatever a normal Rust function can (network calls, model invocations, …).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ProviderRequest<'a> {
    /// The provider name as written in the policy and declared in
    /// `providers.json`, e.g. `["BedrockGuardrails", "PromptInjection"]`.
    pub name: &'a [String],
    /// The positional call arguments, already resolved to values.
    pub args: &'a [Value],
}

impl ProviderRequest<'_> {
    /// The provider name joined as `Ns::Fn` — the key used in
    /// `providers.json` and matched by a resolver.
    pub fn key(&self) -> String {
        self.name.join("::")
    }
}

/// Computes an information provider's output value in the caller's own code,
/// instead of the built-in sandboxed Rhai evaluator.
///
/// This is the home for a provider whose value comes from somewhere the
/// deterministic Rhai sandbox deliberately cannot reach — a service call, a
/// model, a database. Declare such a provider with **no `implementation`** in
/// `providers.json` (an interface-only declaration), install a resolver with
/// [`AuthorizerBuilder::provider_resolver`](crate::AuthorizerBuilder::provider_resolver),
/// and Dogwood binds the value you return into `context.providers.<id>`.
///
/// The resolver is consulted **first**, for every provider invocation. Returning
/// `None` declines the call and lets the built-in Rhai path handle it (so a
/// resolver can back just the providers it knows and leave the rest to their
/// declared scripts). `Some(Ok(value))` supplies the output record.
///
/// **The provider contract applies** (see the guide,
/// 05-information-providers): provider execution is unconditional, so a
/// resolver may be invoked for any decision event — including events whose
/// context lacks the fields the provider reads (such arguments arrive as
/// [`Value::Null`]). A resolver must be pure (a deterministic function of the
/// request's arguments, no observable effects) and defensive: return a
/// conforming sentinel for absent arguments rather than erroring. Returning
/// `Some(Err(_))` is **undefined behavior** for the decision outcome; this
/// reference implementation currently denies the request with the error in
/// diagnostics, but callers must not rely on that.
pub trait ProviderResolver: Send {
    /// Resolve one provider invocation. `None` = not handled here (fall back
    /// to the declared Rhai implementation); `Some(Ok(value))` = the output
    /// record; `Some(Err(_))` = undefined behavior for the decision outcome
    /// (see the trait-level doc — do not rely on the reference
    /// implementation's deny tendency).
    fn resolve(&self, request: ProviderRequest<'_>) -> Option<Result<Value, String>>;
}

#[cfg(test)]
mod partition_encoding_tests {
    use super::{Value, partition_value_key};
    use std::collections::BTreeMap;

    /// Partition-key encoding must agree with `Value::dom_eq`: two values encode
    /// equal iff they are dom-equal. The decimal case is the one that matters —
    /// μ matches with `dom_eq`, which canonicalizes decimals, so `1.5`/`1.50`
    /// must share a partition (structural `==` would split them).
    #[test]
    fn encoding_agrees_with_dom_eq_on_decimals() {
        for (a, b) in [
            ("1.5", "1.50"),
            ("2.5", "02.5"),
            ("-2.5", "-02.5000"),
            ("-0.0", "0.0"),
            ("922337203685477.5807", "922337203685477.5807"),
            ("-922337203685477.5808", "-922337203685477.5808"),
        ] {
            let a = Value::Decimal(a.into());
            let b = Value::Decimal(b.into());
            assert!(a.dom_eq(&b), "precondition: `{a:?}` and `{b:?}`");
            assert_eq!(
                partition_value_key(&a),
                partition_value_key(&b),
                "dom-equal decimals must land in the same partition"
            );
        }

        // A genuinely different decimal must NOT collide.
        assert_ne!(
            partition_value_key(&Value::Decimal("1.5".into())),
            partition_value_key(&Value::Decimal("1.6".into()))
        );

        assert_eq!(
            partition_value_key(&Value::Decimal("1.50".into())),
            "d3:1.5",
            "the established key for ordinary decimal spellings remains stable"
        );
    }

    #[test]
    fn rejected_decimal_spellings_use_exact_text_keys() {
        let invalid = Value::Decimal("1".into());
        assert!(invalid.dom_eq(&invalid));
        assert_eq!(
            partition_value_key(&invalid),
            partition_value_key(&Value::Decimal("1".into()))
        );
        assert_ne!(
            partition_value_key(&invalid),
            partition_value_key(&Value::Decimal("01".into())),
            "distinct rejected spellings are not dom-equal"
        );
        assert_ne!(
            partition_value_key(&invalid),
            partition_value_key(&Value::Decimal("1.0".into())),
            "a rejected spelling cannot collide with an accepted decimal"
        );
    }

    #[test]
    fn nested_decimal_keys_follow_recursive_dom_eq() {
        let a = Value::Array(vec![
            Value::Decimal("02.5".into()),
            Value::Decimal("-0.0".into()),
        ]);
        let b = Value::Array(vec![
            Value::Decimal("2.5000".into()),
            Value::Decimal("0.0000".into()),
        ]);
        assert!(a.dom_eq(&b));
        assert_eq!(partition_value_key(&a), partition_value_key(&b));
    }

    /// A tag keeps variants disjoint: an entity uid and a string with the same
    /// text encode differently.
    #[test]
    fn variants_do_not_alias() {
        let s = Value::String("Drupe::OAuthUser::\"a\"".into());
        let e = Value::Entity {
            ty: "Drupe::OAuthUser".into(),
            id: "a".into(),
        };
        assert_ne!(partition_value_key(&s), partition_value_key(&e));
    }

    /// Length-prefixing makes the encoding injective even when a value contains
    /// the multi-key separator (U+001F) or delimiter-looking bytes: two distinct
    /// string values can never produce the same encoding.
    #[test]
    fn separator_in_value_cannot_forge_a_collision() {
        let a = Value::String("x\u{1f}y".into());
        let b = Value::String("x".into());
        assert_ne!(partition_value_key(&a), partition_value_key(&b));
        // Distinct objects with confusable member layouts stay distinct.
        let mut m1 = BTreeMap::new();
        m1.insert("a".to_string(), Value::String("bc".into()));
        let mut m2 = BTreeMap::new();
        m2.insert("ab".to_string(), Value::String("c".into()));
        assert_ne!(
            partition_value_key(&Value::Object(m1)),
            partition_value_key(&Value::Object(m2))
        );
    }

    /// The multi-key text of a partition (`partition_value_of`) is injective:
    /// its `<none>` marker for an unlogged (or `null`) pin field and its U+001F
    /// separator cannot be forged by a value, because every value's key starts
    /// with a one-letter tag and a length (`partition_value_key`), and `<` is no
    /// tag. (The review exporter's `partition_text` had no such framing,
    /// semantics review F1.3; this pins that the crate's has.)
    #[test]
    fn multi_key_partition_text_is_injective() {
        use super::{InMemoryTemporalEngine, PartitionKey};
        use crate::api::EventPinRoot;
        let keys: Vec<PartitionKey> = ["k1", "k2"]
            .iter()
            .map(|k| PartitionKey {
                field_path: vec![k.to_string()],
                root: EventPinRoot::Context,
                context_path: vec![k.to_string()],
            })
            .collect();
        let s = |x: &str| Value::String(x.to_string());
        let event = |k1: Option<Value>, k2: Option<Value>| {
            let mut b = crate::Event::builder("Login", "request");
            if let Some(v) = k1 {
                b = b.logged_field("k1", v);
            }
            if let Some(v) = k2 {
                b = b.logged_field("k2", v);
            }
            b.build()
        };
        let cases = [
            event(None, None),
            event(Some(Value::Null), None),
            event(Some(s("<none>")), None),
            event(None, Some(s("<none>"))),
            event(Some(s("a\u{1f}<none>")), None),
            event(Some(s("a")), Some(s("<none>"))),
            event(Some(s("a")), None),
            event(Some(s("a\u{1f}s1:b")), None),
            event(Some(s("a")), Some(s("b"))),
            event(Some(s("")), Some(s(""))),
            event(Some(s("")), None),
        ];
        let texts: Vec<String> = cases
            .iter()
            .map(|e| InMemoryTemporalEngine::partition_value_of(e, &keys))
            .collect();
        // Only the unlogged field and the logged `null` (an absent value) share a key.
        assert_eq!(texts[0], texts[1]);
        for (i, a) in texts.iter().enumerate().skip(1) {
            for (j, b) in texts.iter().enumerate().skip(i + 1) {
                assert_ne!(a, b, "cases {i} and {j} collide: {a:?}");
            }
        }
    }
}
