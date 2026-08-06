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

use std::collections::BTreeMap;

use cedar_policy::{Authorizer as CedarAuthorizer, Entities, PolicySet, Request, Schema};

use crate::api::Error;
use crate::authorize::Decision;
use crate::interpreter::eval;
use crate::interpreter::value::{Event, Trace, Value};

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

/// Makes the authorization decision for a request against a fixed policy set.
///
/// The policy set + schema are supplied once, at [`prepare`](PolicyEngine::prepare)
/// (like creating/populating a policy store); each
/// [`is_authorized`](PolicyEngine::is_authorized) then decides one request.
pub trait PolicyEngine: Send {
    /// Install the (lowered Cedar) policies and their schema. Called once when
    /// the [`Authorizer`](crate::Authorizer) is built. A local engine keeps a
    /// reference/clone; a remote-policy-store-backed engine might upsert them into a policy
    /// store here.
    fn prepare(&mut self, policies: &PolicySet, schema: &Schema) -> Result<(), Error>;

    /// Decide one authorization request. Must not panic — surface problems
    /// through [`AuthorizationDecision::errors`] with a fail-closed `Deny`.
    fn is_authorized(&self, request: AuthorizationRequest<'_>) -> AuthorizationDecision;
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
        let Some(policies) = self.policies.as_ref() else {
            return AuthorizationDecision {
                decision: Decision::Deny,
                determining_policy_ids: Vec::new(),
                errors: vec!["policy engine was not prepared".to_string()],
            };
        };
        let response =
            CedarAuthorizer::new().is_authorized(request.request, policies, request.entities);
        AuthorizationDecision {
            decision: response.decision(),
            determining_policy_ids: response
                .diagnostics()
                .reason()
                .map(|pid| AsRef::<str>::as_ref(pid).to_string())
                .collect(),
            errors: response
                .diagnostics()
                .errors()
                .map(|e| e.to_string())
                .collect(),
        }
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
/// `event.field_path(arg.name)`); the pin's request-side `context_path` only
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
/// mirrors the two (`logged[field_path] == request_side[context_path]`). That
/// mirror is an **authoring invariant** on how decision events are constructed
/// — the normal event-construction paths (a service emitting its own events; the
/// `.log` trace/replay path) populate both — **not** a runtime guarantee. One
/// public path does *not* fully establish it: [`Event::from_request`] mirrors
/// only the `input` context group and the scope aliases into `logged`, so a
/// context pin on a non-`input` field fed a decision event via that bridge would
/// route by an absent `logged` field. That path is a single-decision (`ts = 0`)
/// interop shim with no accumulated history to diverge against; a partitioned
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
#[derive(Debug)]
pub struct InMemoryTemporalEngine {
    leaves: Vec<TemporalField>,
    mode: Mode,
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
        }
    }
}

impl InMemoryTemporalEngine {
    pub fn new() -> Self {
        InMemoryTemporalEngine::default()
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
            .map(|k| match event.field_path(&k.field_path) {
                Some(v) => encode_partition_value(v),
                None => "<none>".to_string(),
            })
            .collect::<Vec<_>>()
            .join("\u{1f}") // unit separator — cannot appear in an identifier/uid
    }
}

/// Canonical rendering of a partition-key [`Value`], such that
/// `encode == encode` **iff** the values are equal under [`Value::dom_eq`] — the
/// same equality μ's predicate matcher uses. Two properties make it sound:
///
/// * **dom-canonical**: decimals are canonicalized (trailing fractional zeros
///   trimmed) exactly as `dom_eq` does, so `1.5` and `1.50` share a partition.
/// * **injective / self-delimiting**: every component is length-prefixed
///   (`<tag><byte-len>:<bytes>`), so an arbitrary string, entity id, or nested
///   value — which may contain any character including the multi-key separator —
///   can never be confused with a different decomposition. The leading tag keeps
///   variants disjoint (an entity uid never aliases a same-looking string).
fn encode_partition_value(value: &Value) -> String {
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
            let body: String = items.iter().map(encode_partition_value).collect();
            framed('a', &body)
        }
        Value::Object(members) => {
            // BTreeMap iterates in key order, so equal objects render identically.
            let body: String = members
                .iter()
                .map(|(k, v)| format!("{}:{}{}", k.len(), k, encode_partition_value(v)))
                .collect();
            framed('o', &body)
        }
    }
}

/// Canonicalize a decimal string the way [`Value::dom_eq`] does — trim trailing
/// fractional zeros (and a bare trailing dot) — so partition keys agree with
/// μ's decimal equality. Kept here (the interpreter's `canon_decimal` is
/// module-private) and covered by a unit test that pins it to `dom_eq`.
fn canon_decimal_for_partition(s: &str) -> String {
    match s.split_once('.') {
        Some((int, frac)) => {
            let frac = frac.trim_end_matches('0');
            if frac.is_empty() {
                int.to_string()
            } else {
                format!("{int}.{frac}")
            }
        }
        None => s.to_string(),
    }
}

impl TemporalEngine for InMemoryTemporalEngine {
    // Interprets the leaves directly, so it needs neither the schema nor the
    // event signatures: its equality is this crate's own.
    fn prepare(
        &mut self,
        leaves: &[TemporalField],
        _schema: &Schema,
        _events: &[crate::EventSignature],
    ) -> Result<(), Error> {
        self.leaves = leaves.to_vec();
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
        let env = eval::request_env(trace, i);
        Ok(self
            .leaves
            .iter()
            .map(|f| {
                let holds = eval::eval_condition(trace, i, &env, &f.condition.condition);
                (f.id.clone(), holds)
            })
            .collect())
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
    use super::{Value, encode_partition_value};
    use std::collections::BTreeMap;

    /// Partition-key encoding must agree with `Value::dom_eq`: two values encode
    /// equal iff they are dom-equal. The decimal case is the one that matters —
    /// μ matches with `dom_eq`, which canonicalizes decimals, so `1.5`/`1.50`
    /// must share a partition (structural `==` would split them).
    #[test]
    fn encoding_agrees_with_dom_eq_on_decimals() {
        let a = Value::Decimal("1.5".into());
        let b = Value::Decimal("1.50".into());
        assert!(a.dom_eq(&b), "precondition: dom_eq treats 1.5 == 1.50");
        assert_eq!(
            encode_partition_value(&a),
            encode_partition_value(&b),
            "dom-equal decimals must land in the same partition"
        );
        // A genuinely different decimal must NOT collide.
        assert_ne!(
            encode_partition_value(&a),
            encode_partition_value(&Value::Decimal("1.6".into()))
        );
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
        assert_ne!(encode_partition_value(&s), encode_partition_value(&e));
    }

    /// Length-prefixing makes the encoding injective even when a value contains
    /// the multi-key separator (U+001F) or delimiter-looking bytes: two distinct
    /// string values can never produce the same encoding.
    #[test]
    fn separator_in_value_cannot_forge_a_collision() {
        let a = Value::String("x\u{1f}y".into());
        let b = Value::String("x".into());
        assert_ne!(encode_partition_value(&a), encode_partition_value(&b));
        // Distinct objects with confusable member layouts stay distinct.
        let mut m1 = BTreeMap::new();
        m1.insert("a".to_string(), Value::String("bc".into()));
        let mut m2 = BTreeMap::new();
        m2.insert("ab".to_string(), Value::String("c".into()));
        assert_ne!(
            encode_partition_value(&Value::Object(m1)),
            encode_partition_value(&Value::Object(m2))
        );
    }
}
