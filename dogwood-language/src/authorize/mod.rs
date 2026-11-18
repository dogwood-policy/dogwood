//! Authorization: the stateful [`Authorizer`], the [`Response`] it returns,
//! and the [`Diagnostics`] / [`DogwoodRuleRef`] / re-exported [`Decision`]
//! that describe a decision.
//!
//! This is Dogwood's analog of Cedar's authorization surface. The names
//! mirror `cedar_policy` (`Authorizer`, `Response`, `Diagnostics`,
//! `Decision`) so a Cedar user reads this API with no translation. The one
//! reshaped operation is [`Authorizer::is_authorized`], whose `&mut self` /
//! `Option` signature carries the two things Cedar cannot express:
//! statefulness (each event folds into accumulated history so temporal
//! operators can see the past) and events that do not decide (a
//! history-only event yields no verdict).

use crate::api::{self, Lowered};
use crate::interpreter::value::Event;
use crate::policy_set::LoweredPolicySet;

/// Cedar's authorization decision, re-exported so consumers of the Dogwood
/// API need no direct dependency on `cedar-policy`. It is the type of
/// [`Response::decision`].
pub use cedar_policy::Decision;

/// A reference to a Dogwood rule that contributed to a decision — Dogwood's
/// enriched analog of Cedar's `PolicyId` in `Diagnostics::reason()`. Where
/// Cedar names the (lowered) policy id, Dogwood maps it back to the
/// originating `.dw` rule.
///
/// Superseded by [`PolicyRef`], which names a rule by id and revision rather
/// than by position (`rule_index` names a different rule once the set is
/// reordered); this stays supported throughout 1.x.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DogwoodRuleRef {
    /// 0-based index of the rule in this set (its position in the merged set
    /// for a [`lower_many`](crate::lower_many) result).
    pub rule_index: usize,
    /// The emitted Cedar policy id: synthesized from the position (`policy_0`,
    /// or `<distincter>_0` for a distincter-lowered rule) by default, or the
    /// rule's stable id (`<id>`, or `<distincter>/<id>`) when the set was given
    /// one ([`ParsedPolicySet::with_ids`](crate::ParsedPolicySet::with_ids)).
    pub cedar_policy_id: String,
}

/// A **position-free** reference to a Dogwood rule: its policy id and its
/// revision. Reported for each supporting policy by
/// [`Diagnostics::determining`], and listed by
/// [`LoweredPolicySet::policy_refs`](crate::LoweredPolicySet::policy_refs).
///
/// The pair names one rule exactly: `id` says which rule (its lineage, across
/// versions of the policy set), and `revision` says which text of it.
///
/// - **`id`** is the rule's emitted Cedar policy id. When the set was given
///   stable ids ([`ParsedPolicySet::with_ids`](crate::ParsedPolicySet::with_ids)),
///   it is the owner-chosen id (`<distincter>/<id>` under a distincter) and
///   survives reorders, insertions, removals and edits. Under the default
///   positional ids it is `policy_<k>`, which does not.
/// - **`revision`** is a SHA-256 (lowercase hex) of the canonical lowered rule:
///   its effect, scope and condition, with each hoisted leaf's content (pins
///   included) in place of its positional name. Annotations, spans, comments,
///   formatting and the rule's position are excluded. Equal revisions mean the
///   same rule semantics; a semantic edit changes the revision.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct PolicyRef {
    id: String,
    revision: String,
}

impl PolicyRef {
    pub(crate) fn new(id: String, revision: String) -> Self {
        PolicyRef { id, revision }
    }

    /// The rule's policy id (stable iff the set has stable ids).
    pub fn id(&self) -> &str {
        &self.id
    }

    /// The rule's revision (see the type docs).
    pub fn revision(&self) -> &str {
        &self.revision
    }
}

/// A policy that raised an error while a decision was evaluated, with the
/// error. Cedar skips an erroring policy (it never determines a decision), so
/// these are reported apart from [`Diagnostics::determining`]. Listed by
/// [`Diagnostics::erroring`].
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ErroringPolicy {
    policy: PolicyRef,
    message: String,
}

impl ErroringPolicy {
    pub(crate) fn new(policy: PolicyRef, message: String) -> Self {
        ErroringPolicy { policy, message }
    }

    /// The policy that erred.
    pub fn policy(&self) -> &PolicyRef {
        &self.policy
    }

    /// The evaluation error, as the policy engine reported it (without the
    /// policy id, which [`policy`](ErroringPolicy::policy) carries).
    pub fn message(&self) -> &str {
        &self.message
    }
}

/// The version of the policy set a decision was made under: the deployment
/// generation and a content hash. Carried by [`Response::policy_set`] when the
/// set has stable ids.
///
/// - **`generation`** counts deployments within one [`Authorizer`]: it starts
///   at [`AuthorizerBuilder::generation`] (default `0`) and each successful
///   [`Authorizer::update_policies`] adds one. It orders versions and tells
///   two deployments of identical text apart.
/// - **`hash`** is a SHA-256 (lowercase hex) over the sorted `(policy id,
///   revision)` pairs, the augmented Cedar schema, the decision kinds and the
///   partition keys: equal hashes mean the same rules under the same schema.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct PolicySetVersion {
    generation: u64,
    hash: String,
}

impl PolicySetVersion {
    pub(crate) fn new(generation: u64, hash: String) -> Self {
        PolicySetVersion { generation, hash }
    }

    /// The deployment generation (see the type docs).
    pub fn generation(&self) -> u64 {
        self.generation
    }

    /// The content hash (see the type docs).
    pub fn hash(&self) -> &str {
        &self.hash
    }
}

/// Diagnostics for one authorization decision: the Dogwood rules that
/// determined it and any errors encountered while evaluating. Mirrors
/// Cedar's `Diagnostics` (`reason()` / `errors()`).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Diagnostics {
    reason: Vec<DogwoodRuleRef>,
    errors: Vec<String>,
    /// The determining rules as position-free references, parallel to `reason`.
    determining: Vec<PolicyRef>,
    /// The policies that erred, with their errors.
    erroring: Vec<ErroringPolicy>,
}

impl Diagnostics {
    /// The determining Dogwood rules — those that drove the decision. For an
    /// implicit `Deny` (no rule matched), this is empty, exactly as Cedar's
    /// `reason()` is empty for an implicit deny.
    ///
    /// Superseded by [`determining`](Diagnostics::determining), which names
    /// each rule by id and revision rather than by position; this stays
    /// supported throughout 1.x.
    pub fn reason(&self) -> impl Iterator<Item = &DogwoodRuleRef> {
        self.reason.iter()
    }

    /// The **supporting policies**: each policy that determined the decision,
    /// as a [`PolicyRef`] (id and revision), sorted by id (so the order is
    /// deterministic and does not move when rules are reordered; `reason` keeps
    /// the policy engine's order). The same rules as
    /// [`reason`](Diagnostics::reason). For an `Allow`, every
    /// satisfied `permit`; for an explicit `Deny`, every satisfied `forbid`;
    /// for an implicit `Deny`, and for a fail-closed `Deny`, none.
    ///
    /// The ids are stable when the set has stable ids
    /// ([`ParsedPolicySet::with_ids`](crate::ParsedPolicySet::with_ids)); with
    /// stable ids, a determining policy the engine names but the set does not
    /// contain is an engine fault, and the decision fails closed with an error
    /// in [`errors`](Diagnostics::errors) instead of dropping the id.
    pub fn determining(&self) -> impl Iterator<Item = &PolicyRef> {
        self.determining.iter()
    }

    /// The policies that raised an evaluation error, each with its error,
    /// sorted by policy. Structured counterpart of the per-policy entries in
    /// [`errors`](Diagnostics::errors) (which still lists every error as text).
    /// Filled by policy engines that report erroring policy ids
    /// ([`PolicyEngine::authorize`](crate::PolicyEngine::authorize)); the
    /// built-in Cedar engine does.
    pub fn erroring(&self) -> impl Iterator<Item = &ErroringPolicy> {
        self.erroring.iter()
    }

    /// Errors encountered while evaluating this request — a policy that
    /// referenced a missing attribute, an information provider that could not
    /// run, a decision event with no principal/resource. Mirrors Cedar's
    /// `Diagnostics::errors()`: evaluation degrades rather than aborting, so
    /// these are reported here rather than thrown.
    pub fn errors(&self) -> impl Iterator<Item = &str> {
        self.errors.iter().map(String::as_str)
    }
}

/// The result of authorizing one decision event: the [`Decision`] plus the
/// [`Diagnostics`] describing it. Dogwood's analog of Cedar's `Response`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Response {
    decision: Decision,
    diagnostics: Diagnostics,
    /// The policy-set version, when the set has stable ids.
    policy_set: Option<PolicySetVersion>,
}

impl Response {
    /// The authorization decision, `Allow` or `Deny`.
    pub fn decision(&self) -> Decision {
        self.decision
    }

    /// The diagnostics for this decision.
    pub fn diagnostics(&self) -> &Diagnostics {
        &self.diagnostics
    }

    /// Convenience: `true` iff the decision is `Allow`.
    pub fn allowed(&self) -> bool {
        self.decision == Decision::Allow
    }

    /// The version of the policy set this decision was made under (generation
    /// and hash), so a reported [`PolicyRef`] can be resolved against the
    /// exact deployment. `Some` when the set has stable ids
    /// ([`ParsedPolicySet::with_ids`](crate::ParsedPolicySet::with_ids));
    /// `None` under the default positional ids.
    pub fn policy_set(&self) -> Option<&PolicySetVersion> {
        self.policy_set.as_ref()
    }

    // ─── crate-internal constructors (used by `api::decide`) ─────────

    pub(crate) fn new(
        decision: Decision,
        reason: Vec<DogwoodRuleRef>,
        errors: Vec<String>,
        determining: Vec<PolicyRef>,
        erroring: Vec<ErroringPolicy>,
    ) -> Self {
        Response {
            decision,
            diagnostics: Diagnostics {
                reason,
                errors,
                determining,
                erroring,
            },
            policy_set: None,
        }
    }

    /// A fail-closed `Deny` carrying only evaluation errors (no request was
    /// well-formed enough to reach the policies).
    pub(crate) fn deny_with_errors(errors: Vec<String>) -> Self {
        Response::new(Decision::Deny, Vec::new(), errors, Vec::new(), Vec::new())
    }

    /// Stamp the policy-set version the decision was made under.
    pub(crate) fn set_policy_set(&mut self, version: Option<PolicySetVersion>) {
        self.policy_set = version;
    }
}

/// Why an [`Authorizer`] rejected an event at ingestion, returned by
/// [`Authorizer::submit`]: defined with the pin rules in `crate::conformance`
/// (`Nonconforming`, the specification's `Rejection.nonconforming`, and
/// `Unavailable`, `Rejection.unavailable`).
pub use crate::conformance::Rejection;

/// The Dogwood authorizer: a **stateful** monitor built from a
/// [`LoweredPolicySet`], fed events one at a time with [`is_authorized`].
///
/// It is assembled from two swappable backends (see [`crate::engine`]):
///
///   * a [`PolicyEngine`] that makes the decision — the default
///     [`CedarPolicyEngine`] evaluates locally, but a caller can supply one
///     backed by an external authorization service; and
///   * a [`TemporalEngine`] that evaluates the hoisted `temporal { … }`
///     leaves — the default [`InMemoryTemporalEngine`] keeps history in
///     memory and re-runs the interpreter, but a caller can supply one that
///     compiles the leaves and queries a database.
///
/// It is **stateful**: each ingested [`Event`] is fed to the temporal engine
/// so temporal operators can see the past, and [`is_authorized`] returns
/// `Option<Response>` — `None` for a history-only event whose kind is not a
/// decision kind (e.g. a `response` event). A stateless, single-decision
/// authorization is just a fresh `Authorizer` fed one `request`-kind event.
///
/// Build one with [`Authorizer::new`] (the defaults) or
/// [`Authorizer::builder`] (to substitute either backend).
///
/// [`is_authorized`]: Authorizer::is_authorized
/// [`PolicyEngine`]: crate::engine::PolicyEngine
/// [`CedarPolicyEngine`]: crate::engine::CedarPolicyEngine
/// [`TemporalEngine`]: crate::engine::TemporalEngine
/// [`InMemoryTemporalEngine`]: crate::engine::InMemoryTemporalEngine
pub struct Authorizer {
    /// Shared with every clone of the [`LoweredPolicySet`] it was built from.
    lowered: std::sync::Arc<Lowered>,
    /// Revisions, id stability and the version hash of `lowered`.
    identity: std::sync::Arc<crate::identity::SetIdentity>,
    /// The deployment generation of `lowered` (see [`PolicySetVersion`]).
    generation: u64,
    /// Whether the caller asked for partitioned temporal evaluation
    /// ([`AuthorizerBuilder::partition_temporal`]).
    partition_requested: bool,
    /// The partition keys the temporal engine was prepared with (empty when it
    /// runs global semantics). A live update must keep them.
    partition_keys: Vec<crate::engine::PartitionKey>,
    /// Set when a policy update failed part-way: the engines may hold a mix of
    /// the old and new set, so every decision fails closed until a later update
    /// succeeds.
    poisoned: Option<String>,
    policy_engine: Box<dyn crate::engine::PolicyEngine>,
    temporal_engine: Box<dyn crate::engine::TemporalEngine>,
    provider_resolver: Option<Box<dyn crate::engine::ProviderResolver>>,
    /// The pin rules checked before an event is ingested.
    mirror_rule: crate::MirrorRule,
}

// Manual `Debug` (the engine trait objects are not `Debug`, and requiring it
// on the traits would burden every backend implementer). Shows the lowered
// policy set and marks each pluggable backend as present/opaque, which is what
// a test failure message actually needs.
impl std::fmt::Debug for Authorizer {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Authorizer")
            .field("lowered", &self.lowered)
            .field("policy_engine", &"<dyn PolicyEngine>")
            .field("temporal_engine", &"<dyn TemporalEngine>")
            .field(
                "provider_resolver",
                &self
                    .provider_resolver
                    .as_ref()
                    .map(|_| "<dyn ProviderResolver>"),
            )
            .finish()
    }
}

#[cfg(test)]
impl Authorizer {
    /// The lowered set this authorizer decides with.
    pub(crate) fn lowered(&self) -> &Lowered {
        &self.lowered
    }
}

impl Authorizer {
    /// Build an authorizer from a lowered [`LoweredPolicySet`] with the
    /// built-in backends (local Cedar decisions + in-memory temporal
    /// evaluation). Infallible — the default backends' `prepare` cannot fail;
    /// for backends that can, use [`Authorizer::builder`].
    ///
    /// [`LoweredPolicySet::from_str`]: crate::LoweredPolicySet::from_str
    pub fn new(policies: LoweredPolicySet) -> Self {
        Authorizer::builder(policies)
            .build()
            .expect("the built-in backends never fail to prepare")
    }

    /// Start building an authorizer with custom backends. Install a
    /// [`PolicyEngine`](crate::engine::PolicyEngine) and/or
    /// [`TemporalEngine`](crate::engine::TemporalEngine), then
    /// [`build`](AuthorizerBuilder::build).
    pub fn builder(policies: LoweredPolicySet) -> AuthorizerBuilder {
        AuthorizerBuilder {
            policies,
            policy_engine: None,
            temporal_engine: None,
            provider_resolver: None,
            partition: false,
            generation: 0,
            mirror_rule: crate::MirrorRule::default(),
        }
    }

    /// Ingest one [`Event`] and return the [`Response`] at this timepoint — or
    /// `None` if the event's kind is not a decision kind (a history-only
    /// event, which updates temporal state but produces no verdict).
    ///
    /// A conforming event is handed to the temporal engine (so it observes the
    /// history); a decision-kind event additionally triggers temporal
    /// evaluation, request construction, and the policy engine's decision.
    ///
    /// An event that does not conform is **not ingested** (see
    /// [`Rejection`](crate::Rejection)): one the event schema declares no
    /// signature for, or whose logged record is not an instance of its
    /// signature (a declared field of the wrong type, a required field not
    /// logged), or whose pins do not conform under the authorizer's
    /// [`MirrorRule`](crate::MirrorRule) (a pinned field that is not logged, or
    /// a field that mirrors the request (the field of a symmetric pin, or an
    /// unpinned `callerPrincipal` / `callerResource`) and does not hold the
    /// request's value, or, under the strict rule, is logged by an event that has no request-side value for
    /// it). For such a history event this method returns `None`, as for any
    /// history event; use [`submit`](Self::submit) to learn of the rejection.
    /// Such a decision event yields a fail-closed `Deny`.
    ///
    /// Infallible: an evaluation failure (a provider that cannot run, the
    /// temporal engine erroring, a decision event missing a
    /// principal/resource, data that does not conform to the schemas) does
    /// not abort — it is recorded in [`Response::diagnostics`]`().errors()`
    /// with a fail-closed `Deny`.
    pub fn is_authorized(&mut self, event: &Event) -> Option<Response> {
        self.submit(event).unwrap_or(None)
    }

    /// Submit one [`Event`] for ingestion, and learn whether it was ingested.
    ///
    /// * `Ok(Some(response))` — a decision event, decided. A decision event
    ///   that does not conform is not ingested, and its decision fails closed:
    ///   a `Deny` whose diagnostics say why, as for
    ///   [`is_authorized`](Self::is_authorized).
    /// * `Ok(None)` — a history event, ingested.
    /// * `Err(rejection)` — a history event that was not ingested, so that no
    ///   later decision sees it: one that does not conform
    ///   ([`Rejection::Nonconforming`](crate::Rejection::Nonconforming), the
    ///   specification's `Log.submit` and `Rejection.nonconforming`,
    ///   `dogwood-lean`), or one the temporal engine could not record
    ///   ([`Rejection::Unavailable`](crate::Rejection::Unavailable), through
    ///   [`TemporalEngine::try_observe`](crate::TemporalEngine::try_observe)). A
    ///   decision event in either case is answered with a fail-closed `Deny`.
    ///
    /// The checks follow the specification's ingestion and decision
    /// (`dogwood-lean`, `Dogwood.Spec.Ingest` and `Dogwood.Spec.Decision`),
    /// with the pin rules of event conformance under the authorizer's
    /// [`MirrorRule`](crate::MirrorRule) ([`AuthorizerBuilder::mirror_rule`]).
    /// The timestamp is not checked: the authorizer preserves supplied
    /// timestamps (guide, chapter 4).
    pub fn submit(&mut self, event: &Event) -> Result<Option<Response>, crate::Rejection> {
        let version = self.identity.stable().then(|| self.policy_set_version());
        if let Some(message) = &self.poisoned {
            // A failed update left the engines inconsistent: neither observe
            // nor decide with them, and fail every decision closed.
            if !self.lowered.decision_kinds.contains(&event.data().kind) {
                return Ok(None);
            }
            let mut response = Response::deny_with_errors(vec![format!(
                "the authorizer is unavailable after a failed policy update: {message}"
            )]);
            response.set_policy_set(version);
            return Ok(Some(response));
        }
        // The runtime conformance checks are `lowered`'s own, built once per
        // policy set and shared with `LoweredPolicySet::check_event_conformance`.
        let response = api::ingest(
            &self.lowered,
            &self.identity,
            self.policy_engine.as_ref(),
            self.temporal_engine.as_mut(),
            self.provider_resolver.as_deref(),
            self.mirror_rule,
            event,
        )?;
        Ok(response.map(|mut response| {
            response.set_policy_set(version);
            response
        }))
    }

    /// The [`MirrorRule`](crate::MirrorRule) this authorizer checks before it
    /// ingests an event.
    pub fn mirror_rule(&self) -> crate::MirrorRule {
        self.mirror_rule
    }

    /// The version of the policy set this authorizer currently decides with:
    /// its deployment generation and content hash (see [`PolicySetVersion`]).
    /// Available under every id source; [`Response::policy_set`] carries it
    /// only when the set has stable ids.
    pub fn policy_set_version(&self) -> PolicySetVersion {
        PolicySetVersion::new(
            self.generation,
            self.identity.version_hash(&self.lowered).to_string(),
        )
    }

    /// **Live policy update**: replace the policy set this authorizer decides
    /// with, keeping the temporal history, and advance the deployment
    /// generation by one. Additive; the authorizer's other behavior is
    /// unchanged.
    ///
    /// Both installed engines are re-prepared with `policies`
    /// ([`PolicyEngine::prepare`](crate::engine::PolicyEngine::prepare) and
    /// [`TemporalEngine::prepare`](crate::engine::TemporalEngine::prepare)).
    /// So each must declare that it supports it
    /// ([`supports_policy_update`](crate::engine::TemporalEngine::supports_policy_update));
    /// otherwise this returns [`Error::PolicyUpdateUnsupported`](crate::Error::PolicyUpdateUnsupported)
    /// and changes nothing. To swap the policy engine too (for example, one
    /// bound to a new remote policy store per generation), use
    /// [`update_policies_with_engine`](Authorizer::update_policies_with_engine).
    ///
    /// What the new rules see of the past is the temporal engine's update
    /// reading: the built-in [`InMemoryTemporalEngine`](crate::engine::InMemoryTemporalEngine)
    /// evaluates every leaf over the whole retained history (the
    /// *retrospective* reading).
    ///
    /// The new set must partition temporal history the same way as the current
    /// one (same partition keys, see
    /// [`partition_temporal`](AuthorizerBuilder::partition_temporal));
    /// otherwise this returns [`Error::PartitionKeysChanged`](crate::Error::PartitionKeysChanged)
    /// and changes nothing.
    ///
    /// If an engine's `prepare` fails, the error is returned and the authorizer
    /// **fails closed**: every later decision is a `Deny` with the failure in
    /// its diagnostics (and events are not recorded) until an update succeeds.
    pub fn update_policies(&mut self, policies: LoweredPolicySet) -> Result<(), crate::api::Error> {
        if !self.policy_engine.supports_policy_update() {
            return Err(crate::api::Error::PolicyUpdateUnsupported("policy"));
        }
        self.update(policies, None)
    }

    /// Like [`update_policies`](Authorizer::update_policies), but install
    /// `policy_engine` (prepared with the new set) in place of the current
    /// policy engine. The temporal engine is kept and re-prepared, so it must
    /// support policy updates; the new policy engine need not.
    pub fn update_policies_with_engine(
        &mut self,
        policies: LoweredPolicySet,
        policy_engine: impl crate::engine::PolicyEngine + 'static,
    ) -> Result<(), crate::api::Error> {
        self.update(policies, Some(Box::new(policy_engine)))
    }

    fn update(
        &mut self,
        policies: LoweredPolicySet,
        policy_engine: Option<Box<dyn crate::engine::PolicyEngine>>,
    ) -> Result<(), crate::api::Error> {
        if !self.temporal_engine.supports_policy_update() {
            return Err(crate::api::Error::PolicyUpdateUnsupported("temporal"));
        }
        let (lowered, identity) = policies.into_parts();
        let partitioned = self.partition_requested && !lowered.partition_keys().is_empty();
        let keys: &[crate::engine::PartitionKey] = if partitioned {
            lowered.partition_keys()
        } else {
            &[]
        };
        if keys != self.partition_keys.as_slice() {
            return Err(crate::api::Error::PartitionKeysChanged);
        }

        let result = (|| {
            let mut engine = policy_engine;
            let target: &mut dyn crate::engine::PolicyEngine = match engine.as_mut() {
                Some(e) => e.as_mut(),
                None => self.policy_engine.as_mut(),
            };
            target.prepare(lowered.cedar_policies(), lowered.cedar_schema())?;
            let leaves = if partitioned {
                lowered.temporal_leaves_nonrelativized()
            } else {
                lowered.temporal_leaves()
            };
            let event_signatures: Vec<_> = lowered.event_signatures().collect();
            self.temporal_engine.set_generation(self.generation + 1);
            self.temporal_engine
                .set_authored_leaves(lowered.temporal_leaves_nonrelativized());
            self.temporal_engine
                .prepare(leaves, lowered.cedar_schema(), &event_signatures)?;
            Ok::<_, crate::api::Error>(engine)
        })();

        match result {
            Ok(engine) => {
                if let Some(engine) = engine {
                    self.policy_engine = engine;
                }
                // Build the new set's runtime checks now, as building the
                // authorizer does, rather than at the first event.
                lowered.runtime_checks();
                self.lowered = lowered;
                self.identity = identity;
                self.generation += 1;
                self.poisoned = None;
                Ok(())
            }
            Err(e) => {
                self.poisoned = Some(e.to_string());
                Err(e)
            }
        }
    }
}

/// Builder for an [`Authorizer`] with custom backends. Obtain one from
/// [`Authorizer::builder`].
pub struct AuthorizerBuilder {
    policies: LoweredPolicySet,
    policy_engine: Option<Box<dyn crate::engine::PolicyEngine>>,
    temporal_engine: Option<Box<dyn crate::engine::TemporalEngine>>,
    provider_resolver: Option<Box<dyn crate::engine::ProviderResolver>>,
    partition: bool,
    generation: u64,
    mirror_rule: crate::MirrorRule,
}

impl AuthorizerBuilder {
    /// Install the [`PolicyEngine`](crate::engine::PolicyEngine) that makes
    /// the authorization decision (e.g. one backed by a remote Cedar policy store). Defaults to
    /// [`CedarPolicyEngine`](crate::engine::CedarPolicyEngine).
    pub fn policy_engine(mut self, engine: impl crate::engine::PolicyEngine + 'static) -> Self {
        self.policy_engine = Some(Box::new(engine));
        self
    }

    /// Install the [`TemporalEngine`](crate::engine::TemporalEngine) that
    /// evaluates the temporal leaves (e.g. one that compiles them and queries
    /// a database). Defaults to
    /// [`InMemoryTemporalEngine`](crate::engine::InMemoryTemporalEngine).
    pub fn temporal_engine(mut self, engine: impl crate::engine::TemporalEngine + 'static) -> Self {
        self.temporal_engine = Some(Box::new(engine));
        self
    }

    /// Install a [`ProviderResolver`](crate::engine::ProviderResolver) that
    /// computes information-provider values in your own code (e.g. by calling
    /// a service), instead of the built-in sandboxed Rhai evaluator. The
    /// resolver is consulted first for every provider invocation; providers it
    /// declines fall back to their declared Rhai implementation. Defaults to
    /// none (all providers use the built-in evaluator).
    pub fn provider_resolver(
        mut self,
        resolver: impl crate::engine::ProviderResolver + 'static,
    ) -> Self {
        self.provider_resolver = Some(Box::new(resolver));
        self
    }

    /// Evaluate temporal state **partitioned by the event schema's universal
    /// symmetric pins**, instead of via the pin-relativization rewrite. The
    /// temporal engine keeps a separate monitor / trace per distinct pinned-key
    /// value and runs the **non-relativized** leaves within each partition — an
    /// equivalent, and typically much cheaper, alternative to the rewrite (a
    /// partition physically contains only its own key's events, so a plain
    /// formula already computes the key-local semantics the rewrite would
    /// otherwise encode in-formula, avoiding its per-alternative-action blowup).
    ///
    /// Requires a temporal engine whose
    /// [`supports_partitioning`](crate::engine::TemporalEngine::supports_partitioning)
    /// is `true` (the default [`InMemoryTemporalEngine`](crate::engine::InMemoryTemporalEngine)
    /// qualifies); otherwise [`build`](AuthorizerBuilder::build) fails with
    /// [`Error::PartitioningUnsupported`](crate::api::Error::PartitioningUnsupported)
    /// rather than silently running global semantics. A no-op when the schema
    /// declares no universal symmetric pin (there is nothing to partition on, and
    /// the relativized and non-relativized leaves coincide).
    pub fn partition_temporal(mut self) -> Self {
        self.partition = true;
        self
    }

    /// The form of the **mirror rule** checked before an event is ingested
    /// (default [`MirrorRule::Strict`](crate::MirrorRule::Strict), the
    /// specification's rule). See [`MirrorRule`](crate::MirrorRule) and
    /// [`Authorizer::submit`].
    ///
    /// [`MirrorRule::Unchecked`](crate::MirrorRule::Unchecked) ingests every
    /// event, as Dogwood_Language 1.1 did, including forged history (a
    /// scope-less event logging another principal as its caller).
    pub fn mirror_rule(mut self, rule: crate::MirrorRule) -> Self {
        self.mirror_rule = rule;
        self
    }

    /// The deployment generation of the initial policy set (default `0`), as
    /// reported in [`PolicySetVersion::generation`]. Set it when the
    /// authorizer is rebuilt for a deployment that already has a generation
    /// (for example, after a process restart), so generations keep increasing.
    pub fn generation(mut self, generation: u64) -> Self {
        self.generation = generation;
        self
    }

    /// Build the [`Authorizer`], running each backend's `prepare` against the
    /// policy set and schema. Errors if a backend's `prepare` fails (e.g. a
    /// compiling temporal engine rejects a leaf, or a remote engine cannot reach
    /// its policy store), or if partitioned evaluation was requested against an
    /// engine that does not support it.
    pub fn build(self) -> Result<Authorizer, crate::api::Error> {
        let (lowered, identity) = self.policies.into_parts();
        let mut policy_engine = self
            .policy_engine
            .unwrap_or_else(|| Box::new(crate::engine::CedarPolicyEngine::new()));
        let mut temporal_engine = self
            .temporal_engine
            .unwrap_or_else(|| Box::new(crate::engine::InMemoryTemporalEngine::new()));

        policy_engine.prepare(lowered.cedar_policies(), lowered.cedar_schema())?;

        // Choose the temporal program: partitioned (non-relativized leaves +
        // per-key routing) when the caller opted in AND the schema actually has
        // partition keys; otherwise the relativized leaves over a single monitor.
        // Opting in against a non-partitioning engine fails closed — but only
        // when there is genuinely something to partition on. With no universal
        // symmetric pin, partitioning is a documented no-op (the relativized and
        // non-relativized leaves are identical), so requesting it against any
        // engine, partitioning or not, just runs global rather than erroring.
        let partitioned = self.partition && !lowered.partition_keys().is_empty();
        if partitioned && !temporal_engine.supports_partitioning() {
            return Err(crate::api::Error::PartitioningUnsupported);
        }
        let leaves = if partitioned {
            temporal_engine.set_partition_keys(lowered.partition_keys());
            lowered.temporal_leaves_nonrelativized()
        } else {
            lowered.temporal_leaves()
        };
        let event_signatures: Vec<_> = lowered.event_signatures().collect();
        temporal_engine.set_authored_leaves(lowered.temporal_leaves_nonrelativized());
        temporal_engine.set_generation(self.generation);
        temporal_engine.prepare(leaves, lowered.cedar_schema(), &event_signatures)?;

        let partition_keys = if partitioned {
            lowered.partition_keys().to_vec()
        } else {
            Vec::new()
        };
        // The set's runtime conformance checks, built here (once per set, and
        // shared with its clones) rather than at the first event.
        lowered.runtime_checks();
        Ok(Authorizer {
            lowered,
            identity,
            generation: self.generation,
            partition_requested: self.partition,
            partition_keys,
            poisoned: None,
            policy_engine,
            temporal_engine,
            provider_resolver: self.provider_resolver,
            mirror_rule: self.mirror_rule,
        })
    }
}
