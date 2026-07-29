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
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DogwoodRuleRef {
    /// 0-based index of the rule in the source policy set.
    pub rule_index: usize,
    /// The synthesized Cedar policy id (e.g. `policy0`).
    pub cedar_policy_id: String,
}

/// Diagnostics for one authorization decision: the Dogwood rules that
/// determined it and any errors encountered while evaluating. Mirrors
/// Cedar's `Diagnostics` (`reason()` / `errors()`).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Diagnostics {
    reason: Vec<DogwoodRuleRef>,
    errors: Vec<String>,
}

impl Diagnostics {
    /// The determining Dogwood rules — those that drove the decision. For an
    /// implicit `Deny` (no rule matched), this is empty, exactly as Cedar's
    /// `reason()` is empty for an implicit deny.
    pub fn reason(&self) -> impl Iterator<Item = &DogwoodRuleRef> {
        self.reason.iter()
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

    // ─── crate-internal constructors (used by `api::decide`) ─────────

    pub(crate) fn new(
        decision: Decision,
        reason: Vec<DogwoodRuleRef>,
        errors: Vec<String>,
    ) -> Self {
        Response {
            decision,
            diagnostics: Diagnostics { reason, errors },
        }
    }

    /// A fail-closed `Deny` carrying only evaluation errors (no request was
    /// well-formed enough to reach the policies).
    pub(crate) fn deny_with_errors(errors: Vec<String>) -> Self {
        Response {
            decision: Decision::Deny,
            diagnostics: Diagnostics {
                reason: Vec::new(),
                errors,
            },
        }
    }

    /// Prepend evaluation errors accumulated before the decision core ran.
    pub(crate) fn push_errors(&mut self, mut errors: Vec<String>) {
        if !errors.is_empty() {
            errors.extend(std::mem::take(&mut self.diagnostics.errors));
            self.diagnostics.errors = errors;
        }
    }
}

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
    lowered: Lowered,
    policy_engine: Box<dyn crate::engine::PolicyEngine>,
    temporal_engine: Box<dyn crate::engine::TemporalEngine>,
    provider_resolver: Option<Box<dyn crate::engine::ProviderResolver>>,
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
        }
    }

    /// Ingest one [`Event`] and return the [`Response`] at this timepoint — or
    /// `None` if the event's kind is not a decision kind (a history-only
    /// event, which updates temporal state but produces no verdict).
    ///
    /// The event is always handed to the temporal engine (so it observes the
    /// history); a decision-kind event additionally triggers temporal
    /// evaluation, request construction, and the policy engine's decision.
    ///
    /// Infallible: an evaluation failure (a provider that cannot run, the
    /// temporal engine erroring, a decision event missing a
    /// principal/resource) does not abort — it is recorded in
    /// [`Response::diagnostics`]`().errors()` with a fail-closed `Deny`.
    pub fn is_authorized(&mut self, event: &Event) -> Option<Response> {
        api::ingest(
            &self.lowered,
            self.policy_engine.as_ref(),
            self.temporal_engine.as_mut(),
            self.provider_resolver.as_deref(),
            event,
        )
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

    /// Build the [`Authorizer`], running each backend's `prepare` against the
    /// policy set and schema. Errors if a backend's `prepare` fails (e.g. a
    /// compiling temporal engine rejects a leaf, or a remote engine cannot reach
    /// its policy store), or if partitioned evaluation was requested against an
    /// engine that does not support it.
    pub fn build(self) -> Result<Authorizer, crate::api::Error> {
        let lowered = self.policies.into_lowered();
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
        temporal_engine.prepare(leaves, lowered.cedar_schema(), &event_signatures)?;

        Ok(Authorizer {
            lowered,
            policy_engine,
            temporal_engine,
            provider_resolver: self.provider_resolver,
        })
    }
}
