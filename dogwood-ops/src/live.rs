//! The **live** (incremental) authorizer: Dogwood's stateful `Authorizer`
//! behind the event-validation contract every binding exposes as a class
//! (`DogwoodAuthorizer` in JS and Python).
//!
//! This module is host-agnostic: it takes an already-deserialized
//! [`EventInput`] and returns [`OpError`]s. Each binding converts its host's
//! event object into an `EventInput` (after bounding it, see
//! [`bounds`](crate::bounds)) and its errors into host exceptions.
//!
//! [`ops::replay_trace`](crate::ops::replay_trace) answers "what would this
//! policy have decided over this recorded `.log` trace?" — it lowers, drives a
//! fresh authorizer over every event, and returns the whole verdict stream. A
//! host that is *making* decisions (an agent gateway, an MCP proxy) needs the
//! other shape: lower once, then feed events **one at a time** as they happen
//! and get a decision back per event, with the temporal history accumulating
//! across calls. That is what [`LiveAuthorizer`] is.
//!
//! ```js
//! const auth = new DogwoodAuthorizer(policySrc, actionSchemaSrc);
//! const d = auth.isAuthorized({
//!   action: 'Drupe::Action::Read',
//!   principal: { type: 'Drupe::User', id: 'alice' },
//!   resource:  { type: 'Drupe::Gateway', id: 'gw1' },
//!   context:   { input: { document: 'quarterly report', user: 'alice' } },
//! });
//! if (!d.allowed) throw new Error('denied');
//! ```
//!
//! ## Event shape
//!
//! [`EventInput`] mirrors the `.log` wire format's four components — the
//! `scope(...)` (principal/resource), the `entities(...)` store, the
//! `request_context(...)` bag, and the trailing **logged** record — because
//! those are exactly the parts the frontend's `EventBuilder` accepts. Entity
//! references are given **structured** (`{ type, id }`) rather than as
//! `Ns::Type::"id"` literals: the builder's `*_for` methods escape the id
//! canonically exactly once, so a host never has to (and cannot
//! double-)escape an id containing `"` or `\`.
//!
//! `logged` vs `context` is a real distinction, not a convenience split:
//! `logged` is the durable temporal record that future events correlate
//! against, `context` is the ephemeral per-decision Cedar request context. A
//! field both halves need (typically `input`) must be supplied in **both** —
//! the frontend is deliberately explicit about this, and so are these bindings.
//!
//! ## Known gap
//!
//! The event schema declares two top-level *scalar* logged fields
//! (`requestId`, `sessionId`). [`EventInput::logged`] only carries grouped
//! fields (`group -> { name -> value }`), so those two cannot be set here yet;
//! policies that pin on them need the whole-trace [`replay`](crate::replay)
//! path. The frontend now has `EventBuilder::logged_field` for exactly this,
//! so closing the gap is a matter of widening `logged`'s shape.

use std::collections::BTreeMap;

use std::collections::BTreeSet;

use dogwood_language::{
    Authorizer, Decision, Event, EventBuilder, LoweredPolicySet, Value,
};
use serde::{Deserialize, Serialize};

use crate::error::OpError;
use crate::fail_closed::fail_closed;
use crate::ops::{SchemaInputs, Verdict, lower_for_authorizer};
use crate::providers::parse_declarations;

// ─── event input ─────────────────────────────────────────────────────

/// A structured entity reference, deserialized from `{ type, id }`.
#[derive(Debug, Clone, Deserialize)]
pub struct EntityRef {
    /// Entity type, namespace included (`"Drupe::User"`).
    #[serde(rename = "type")]
    pub ty: String,
    /// The raw, un-escaped entity id.
    pub id: String,
}

/// One entity supplied to a decision: its identity plus the attributes and
/// direct parents a policy may read (`principal.dept`, `principal in Group`).
#[derive(Debug, Clone, Deserialize)]
pub struct EntityInput {
    /// Entity type, namespace included (`"Drupe::User"`).
    #[serde(rename = "type")]
    pub ty: String,
    /// The raw, un-escaped entity id.
    pub id: String,
    /// Attributes, `name -> value`. Validated against the action schema at
    /// decision time, so a wrong-typed attribute fails closed.
    #[serde(default)]
    pub attrs: BTreeMap<String, serde_json::Value>,
    /// **Direct** parents (`memberOf` edges). Cedar computes the transitive
    /// closure, so only direct parents are supplied.
    #[serde(default)]
    pub parents: Vec<EntityRef>,
}

/// One event fed to a [`LiveAuthorizer`] — the host-neutral analog of the frontend's
/// `Event`, and a mirror of the `.log` wire format's components.
#[derive(Debug, Clone, Deserialize)]
pub struct EventInput {
    /// The **fully qualified** Cedar action id — `"Drupe::Action::Read"`.
    /// Must be one of [`actions`](LiveAuthorizer::actions), matched as a whole
    /// string: the event is then built from the namespace and bare id the
    /// schema declares, so an id containing `:` or `::` (which Cedar permits)
    /// is addressed exactly. Any other action is rejected — a bare `"Read"`
    /// with the qualified id suggested.
    pub action: String,
    /// The event kind. `"request"` (the default) is a decision point;
    /// `"response"` / `"error"` are history-only — they update temporal state
    /// and return `undefined`. Which kinds exist, and which decide, is set by
    /// the event schema — see [`eventKinds`](LiveAuthorizer::event_kinds) and
    /// [`decisionKinds`](LiveAuthorizer::decision_kinds).
    ///
    /// A kind the schema does not declare is **rejected**, with the declared
    /// kinds listed, so a typo (`"requst"`) fails loudly.
    #[serde(default = "default_kind")]
    pub kind: String,
    /// Wall-clock timestamp, in **seconds** — the unit the temporal windows are
    /// defined in (`1h` is 3600). From JS that means
    /// `Math.floor(Date.now() / 1000)`, *not* `Date.now()`: passing
    /// milliseconds silently inflates every window by 1000×, so a `within 1h`
    /// predicate would match only events from the last 3.6 seconds.
    ///
    /// Timestamps order events for the temporal operators, so this must be
    /// **non-decreasing** across calls on one instance — one instance is one
    /// ordered history. A timestamp before the previous event's is rejected
    /// rather than silently producing wrong temporal answers; see
    /// [`lastTimestamp`](LiveAuthorizer::last_timestamp).
    ///
    /// **Required.** A default (`0`) would let an event with no timestamp
    /// through on a fresh instance and place it at the epoch, silently skewing
    /// every window; a missing timestamp is a deserialize error instead.
    pub timestamp: i64,
    /// The request principal. Setting it makes the event request-wrapping.
    #[serde(default)]
    pub principal: Option<EntityRef>,
    /// The request resource. Setting it makes the event request-wrapping.
    #[serde(default)]
    pub resource: Option<EntityRef>,
    /// The **durable temporal record**: `group -> { name -> value }`, read by
    /// temporal predicates in later events. Distinct from
    /// [`context`](Self::context) — see the module docs.
    #[serde(default)]
    pub logged: BTreeMap<String, BTreeMap<String, serde_json::Value>>,
    /// The **per-decision Cedar request context**: `group -> { name -> value }`,
    /// read by a policy as `context.<group>.<name>`. Never persisted.
    #[serde(default)]
    pub context: BTreeMap<String, BTreeMap<String, serde_json::Value>>,
    /// The entity store for this decision — attributes and hierarchy for any
    /// entity the policy names.
    #[serde(default)]
    pub entities: Vec<EntityInput>,
}

fn default_kind() -> String {
    "request".to_string()
}

// ─── decision output ─────────────────────────────────────────────────

/// The decision for one event: the verdict plus why.
#[derive(Debug, Clone, Serialize)]
pub struct AuthorizerDecision {
    /// 0-based index of this decision in the authorizer's decision stream
    /// (history-only events do not advance it).
    pub index: usize,
    /// The event's timestamp, echoed back.
    pub timestamp: i64,
    pub verdict: Verdict,
    /// `true` exactly when `verdict === "allow"`: the policy allowed **and**
    /// evaluation raised no errors. Stricter than Dogwood's own
    /// `Response::allowed`, which is Cedar's decision alone — Cedar skips a
    /// rule whose condition errors, so an errored `forbid` would otherwise let
    /// a `permit` through.
    pub allowed: bool,
    /// The `.dw` rule indices that determined the decision. Empty for an
    /// implicit deny (no rule matched) and for a fail-closed deny (`errors`
    /// non-empty).
    pub determining_rules: Vec<usize>,
    /// Evaluation errors folded into this decision. Any error forces a deny,
    /// so a non-empty `errors` means *something went wrong*, not *policy said
    /// no*.
    pub errors: Vec<String>,
}

// ─── value conversion ────────────────────────────────────────────────

/// Convert a deserialized host value into a Dogwood [`Value`].
///
/// Integers stay integers; a non-integral number becomes a [`Value::Decimal`]
/// carrying the number's **own** text (not a re-formatted one), so a decimal
/// round-trips as authored wherever JSON preserves it. The two tagged object
/// forms are checked before the plain-record case.
///
/// `depth` is this value's nesting level, counted as the `.log` parser counts
/// it (a `context`/`logged` group is the depth-0 record, so its fields start at
/// 1; an entity attribute starts at 0); past
/// [`MAX_VALUE_DEPTH`](crate::bounds::MAX_VALUE_DEPTH) the conversion fails,
/// exactly as the `.log` parser does, so `replay` and the live path accept the
/// same values.
pub fn to_value(json: &serde_json::Value, depth: usize) -> Result<Value, String> {
    crate::bounds::check_value_depth(depth)?;
    Ok(match json {
        serde_json::Value::Null => Value::Null,
        serde_json::Value::Bool(b) => Value::Bool(*b),
        serde_json::Value::Number(n) => match n.as_i64() {
            Some(i) => Value::Int(i),
            // An integer, but outside the i64 range of a Cedar `Long`. Not a
            // decimal either (Cedar's decimal is narrower still), so an input
            // error rather than a reclassification. Past u64 in either
            // direction serde parses an integer as an integral `f64` (no
            // `arbitrary_precision`), so that is caught here too — the same
            // error for `-100000000000000000000` as for `u64::MAX`, rather
            // than the exponent-form one its `-1e20` rendering would draw.
            None if n.is_u64()
                || n.as_f64().is_some_and(|f| f.fract() == 0.0 && f.abs() >= 2f64.powi(63)) =>
            {
                return Err(format!(
                    "integer {n} is out of range: a Cedar Long is a 64-bit signed integer"
                ));
            }
            // Fractional. Cedar's decimal is text-defined, so keep serde's
            // rendering verbatim — unless that rendering is exponent form
            // (`1e-7`, `-2.5e-10`), which is not decimal text at all.
            None => {
                let text = n.to_string();
                if text.contains(['e', 'E']) {
                    return Err(format!(
                        "number {text} has no decimal rendering (it is in exponent form); \
                         pass an exact decimal as `{{ \"__decimal\": \"…\" }}`"
                    ));
                }
                if text.contains('.') {
                    Value::Decimal(text)
                } else {
                    Value::Decimal(format!("{text}.0"))
                }
            }
        },
        serde_json::Value::String(s) => Value::String(s.clone()),
        serde_json::Value::Array(items) => {
            Value::Array(
                items
                    .iter()
                    .map(|item| to_value(item, depth + 1))
                    .collect::<Result<_, _>>()?,
            )
        }
        serde_json::Value::Object(map) => {
            // `{ __entity: { type, id } }` — a structured entity reference.
            if let Some(entity) = map.get("__entity") {
                if map.len() != 1 {
                    return Err("`__entity` must be the only key of its object".to_string());
                }
                let obj = entity
                    .as_object()
                    .ok_or("`__entity` must be an object `{ type, id }`")?;
                let ty = obj
                    .get("type")
                    .and_then(serde_json::Value::as_str)
                    .ok_or("`__entity` is missing a string `type`")?;
                let id = obj
                    .get("id")
                    .and_then(serde_json::Value::as_str)
                    .ok_or("`__entity` is missing a string `id`")?;
                return Ok(Value::Entity {
                    ty: ty.to_string(),
                    id: id.to_string(),
                });
            }
            // `{ __decimal: "1.50" }` — exact decimal text.
            if let Some(decimal) = map.get("__decimal") {
                if map.len() != 1 {
                    return Err("`__decimal` must be the only key of its object".to_string());
                }
                let text = decimal
                    .as_str()
                    .ok_or("`__decimal` must be a string, e.g. `\"1.50\"`")?;
                return Ok(Value::Decimal(text.to_string()));
            }
            Value::Object(
                map.iter()
                    .map(|(k, v)| to_value(v, depth + 1).map(|v| (k.clone(), v)))
                    .collect::<Result<BTreeMap<_, _>, _>>()?,
            )
        }
    })
}

/// Build a frontend [`Event`] from the host's input, for the action `action`
/// (its namespace and bare id, as the schema declares them).
///
/// The action and every entity reference go through a structured `*_for`
/// builder method, so ids are never re-split and are escaped canonically
/// exactly once at the Cedar boundary.
fn build_event(input: &EventInput, action: &ActionParts) -> Result<Event, String> {
    let namespace: Vec<&str> = action.namespace.iter().map(String::as_str).collect();
    let mut builder: EventBuilder =
        Event::builder_for(&namespace, &action.id, &input.kind).timestamp(input.timestamp);

    if let Some(p) = &input.principal {
        builder = builder.principal_for(&p.ty, &p.id);
    }
    if let Some(r) = &input.resource {
        builder = builder.resource_for(&r.ty, &r.id);
    }

    for (group, fields) in &input.logged {
        for (name, value) in fields {
            // Depth 1: in a `.log` trace the group is itself a record value at
            // depth 0, so its fields sit at 1. Counting the same way keeps the
            // live and replay limits identical.
            builder = builder.field(group, name, to_value(value, 1)?);
        }
    }
    for (group, fields) in &input.context {
        for (name, value) in fields {
            // Depth 1, as for `logged` above.
            builder = builder.request_context(group, name, to_value(value, 1)?);
        }
    }

    for entity in &input.entities {
        // `entity_for` merges on repeat, so attributes and parents for the
        // same (ty, id) compose across the two calls.
        let attrs = entity
            .attrs
            .iter()
            .map(|(name, value)| to_value(value, 0).map(|v| (name.as_str(), v)))
            .collect::<Result<Vec<_>, _>>()?;
        builder = builder.entity_for(&entity.ty, &entity.id, attrs);

        if !entity.parents.is_empty() {
            let parents: Vec<(&str, &str)> = entity
                .parents
                .iter()
                .map(|p| (p.ty.as_str(), p.id.as_str()))
                .collect();
            builder = builder.parents_for(&entity.ty, &entity.id, parents);
        }
    }

    Ok(builder.build())
}

// ─── the event surface an instance accepts ───────────────────────────

/// An action's namespace (the `Action` segment included) and bare id, as the
/// schema declares them.
#[derive(PartialEq, Eq)]
struct ActionParts {
    namespace: Vec<String>,
    id: String,
}

impl ActionParts {
    /// The action's Cedar uid, `Drupe::Action::"Read"` — unambiguous where
    /// the joined qualified id is not.
    fn uid(&self) -> String {
        let id = serde_json::Value::String(self.id.clone());
        format!("`{}::{id}`", self.namespace.join("::"))
    }
}

/// The `(action, kind)` surface a lowered policy set derives — what an inbound
/// event is checked against.
///
/// The engine itself fails an undeclared `(action, kind)` closed, but with a
/// terse cause; capturing the surface at lowering time lets
/// [`LiveAuthorizer::is_authorized`] reject such an event up front, with the
/// declared actions or kinds listed.
struct EventSurface {
    /// Every action, **fully qualified id -> its parts**
    /// (`"Drupe::Action::Read" -> (["Drupe", "Action"], "Read")`). The parts
    /// are kept so the event is built from them: re-splitting the qualified id
    /// on `::` is wrong for the (legal, if rare) id containing `:` or `::`.
    actions: BTreeMap<String, ActionParts>,
    /// Every declared event kind, decision points and history-only alike.
    kinds: BTreeSet<String>,
    /// The subset of [`kinds`](Self::kinds) that are decision points, in the
    /// schema's own order.
    decision_kinds: Vec<String>,
}

impl EventSurface {
    /// Read the surface off a lowered set. `event_signatures` yields one entry
    /// per derived `(action, kind)`; the qualified id is the signature's
    /// namespace (which already carries the trailing `Action` segment) joined
    /// onto its action id.
    ///
    /// Two distinct actions can join to the same qualified id, because Cedar
    /// permits `::` inside an action id: `"Action::Read"` in `Drupe` and
    /// `"Read"` in `Drupe::Action` are both `Drupe::Action::Action::Read`. Such
    /// a schema is rejected, naming both, rather than one action silently
    /// shadowing the other. (The same action recurring once per kind is not a
    /// collision: its parts are identical.)
    fn of(lowered: &LoweredPolicySet) -> Result<EventSurface, String> {
        let mut actions: BTreeMap<String, ActionParts> = BTreeMap::new();
        let mut kinds = BTreeSet::new();
        for sig in lowered.event_signatures() {
            let mut qualified = String::new();
            for segment in sig.namespace() {
                qualified.push_str(segment);
                qualified.push_str("::");
            }
            qualified.push_str(sig.action());
            let parts = ActionParts {
                namespace: sig.namespace().iter().map(|s| s.to_string()).collect(),
                id: sig.action().to_string(),
            };
            match actions.get(&qualified) {
                Some(prev) if *prev != parts => {
                    return Err(format!(
                        "actions {} and {} both have the qualified id `{qualified}`, so an \
                         event naming it is ambiguous. Rename one of them",
                        prev.uid(),
                        parts.uid(),
                    ));
                }
                Some(_) => {}
                None => {
                    actions.insert(qualified, parts);
                }
            }
            kinds.insert(sig.kind().to_string());
        }
        Ok(EventSurface {
            actions,
            kinds,
            decision_kinds: lowered.decision_kinds().map(str::to_string).collect(),
        })
    }
}

/// Render a list for an error message, capped so a schema with a hundred actions
/// does not produce a hundred-line error.
fn listing<'a>(items: impl IntoIterator<Item = &'a str>) -> String {
    const CAP: usize = 8;
    let all: Vec<&str> = items.into_iter().collect();
    let shown = all
        .iter()
        .take(CAP)
        .map(|s| format!("`{s}`"))
        .collect::<Vec<_>>()
        .join(", ");
    match all.len().checked_sub(CAP) {
        Some(rest) if rest > 0 => format!("{shown} (and {rest} more)"),
        _ => shown,
    }
}

// ─── the exported class ──────────────────────────────────────────────

/// A **stateful, live** Dogwood authorizer: lower a policy set once, then feed
/// events as they happen and get a decision per event, with temporal history
/// accumulating across calls.
///
/// This is the counterpart to the one-shot [`replay`](crate::replay): same
/// engine and same lowering, but the caller drives the loop. Because it holds
/// temporal state, one instance corresponds to one history — see
/// [`reset`](LiveAuthorizer::reset).
pub struct LiveAuthorizer {
    authorizer: Authorizer,
    /// The lowered set the authorizer was built from. Kept (a clone is cheap:
    /// the artifacts are shared) to check an event's conformance before it is
    /// submitted, and so [`reset`](Self::reset) starts a fresh history without
    /// lowering again.
    lowered: LoweredPolicySet,
    /// Decision counter — the `index` of the next decision. History-only
    /// events do not advance it.
    decisions: usize,
    /// The `(action, kind)` surface this instance accepts, captured at lowering
    /// time so inbound events can be checked against it.
    surface: EventSurface,
    /// The timestamp of the most recent event observed, or `None` before the
    /// first. Kept to enforce the non-decreasing-timestamp contract, which the
    /// temporal operators depend on and the engine does not check.
    last_timestamp: Option<i64>,
}

impl LiveAuthorizer {
    /// Lower `source` against `actionSchema` and build a fresh authorizer with
    /// empty temporal history. Throws a `DogwoodError` (with `.diagnostic`) on
    /// a parse, macro, lowering, or schema failure — the same error contract as
    /// every other operation in these bindings.
    ///
    /// The trailing arguments are the optional service-schema overrides
    /// (event-schema DSL text, `providers.json` text, macro-library text);
    /// omit them for the defaults.
    pub fn new(
        source: &str,
        action_schema: &str,
        event_schema: Option<String>,
        providers: Option<String>,
        macros: Option<String>,
    ) -> Result<LiveAuthorizer, OpError> {
        // Reject provider declarations that cannot work from text before
        // lowering, so an unresolvable `scriptFile` is a construction-time
        // error rather than a fail-closed deny on every later decision.
        if let Some(json) = providers.as_deref() {
            parse_declarations(json)?;
        }
        let inputs = SchemaInputs {
            event_schema: event_schema.as_deref(),
            providers: providers.as_deref(),
            macros: macros.as_deref(),
        };
        let lowered = lower_for_authorizer(source, &inputs, action_schema)?;
        let surface = EventSurface::of(&lowered).map_err(OpError::message)?;
        Ok(LiveAuthorizer {
            authorizer: Authorizer::new(lowered.clone()),
            lowered,
            decisions: 0,
            surface,
            last_timestamp: None,
        })
    }

    /// Check an inbound event against what this instance can actually decide:
    /// its action and kind must be ones the schema derives, and its timestamp
    /// must not go backwards.
    ///
    /// All three are checked **before** the event is observed, so a rejected
    /// event leaves the temporal history untouched — a failed call is a no-op,
    /// not a partial one. Returns the action's declared parts, from which the
    /// event is built.
    ///
    /// The engine would fail an undeclared action or kind closed by itself;
    /// these checks are for a better error (the declared ids listed, a
    /// qualified id suggested). The timestamp check has no engine counterpart:
    /// the authorizer preserves timestamps as supplied.
    fn check(&self, event: &EventInput) -> Result<&ActionParts, String> {
        let action = match self.surface.actions.get(&event.action) {
            Some(parts) => parts,
            None => {
                // An id whose last segment matches exactly one known action is
                // almost always a missing namespace — the bare-`"Read"` mistake.
                let tail = event.action.rsplit("::").next().unwrap_or(&event.action);
                let mut same_tail = self
                    .surface
                    .actions
                    .keys()
                    .filter(|known| known.rsplit("::").next() == Some(tail));
                let hint = match (same_tail.next(), same_tail.next()) {
                    (Some(only), None) => format!(" — did you mean `{only}`?"),
                    _ => String::new(),
                };
                return Err(format!(
                    "unknown action `{}`: not declared by the action schema, which declares {}. \
                     Action ids are fully qualified, `Ns::Action::Id`{}",
                    event.action,
                    listing(self.surface.actions.keys().map(String::as_str)),
                    hint,
                ));
            }
        };

        if !self.surface.kinds.contains(&event.kind) {
            return Err(format!(
                "unknown event kind `{}`. The event schema declares {} — of which {} \
                 {} a decision point",
                event.kind,
                listing(self.surface.kinds.iter().map(String::as_str)),
                listing(self.surface.decision_kinds.iter().map(String::as_str)),
                if self.surface.decision_kinds.len() == 1 { "is" } else { "are" },
            ));
        }

        if self.last_timestamp.is_some_and(|last| event.timestamp < last) {
            let last = self.last_timestamp.unwrap_or_default();
            return Err(format!(
                "event timestamp {} is before the previous event's {}. Timestamps order \
                 events for the temporal operators, so they must be non-decreasing across \
                 calls on one authorizer — one instance is one ordered history. Feed events \
                 in order, or use a separate instance (or `reset()`) per history.",
                event.timestamp, last,
            ));
        }

        Ok(action)
    }

    /// Authorize one event.
    ///
    /// Returns the [`AuthorizerDecision`] for a decision-kind event (by
    /// default, `kind: "request"`), or `None`/`undefined` for a history-only event —
    /// which still updates temporal history, and is how a host records the
    /// `response` half of a call so later policies can correlate against it.
    ///
    /// Fails with an [`OpError`] if the event is malformed (a bad `__entity`
    /// tag, a value nested deeper than 128 levels), **rejected** by
    /// the event checks — an action or kind the schema does not declare, or
    /// a timestamp before the previous event's — or, for a history event,
    /// rejected by the authorizer at ingestion (it does not conform to the
    /// event schema). Either way the instance is left
    /// **usable** and the temporal history untouched: the event is validated
    /// before it is observed, so a failed call is a no-op and the next call
    /// decides normally.
    ///
    /// A *policy* problem is never thrown: an evaluation failure comes back as a
    /// fail-closed `deny` with the cause in
    /// [`errors`](AuthorizerDecision::errors).
    ///
    /// The binding is responsible for bounding the raw host event (see
    /// [`bounds`](crate::bounds)) and deserializing it into an [`EventInput`]
    /// before calling this.
    pub fn is_authorized(
        &mut self,
        event: &EventInput,
    ) -> Result<Option<AuthorizerDecision>, OpError> {
        let action = self.check(event).map_err(OpError::message)?;
        let built = build_event(event, action).map_err(OpError::message)?;

        // A decision event that does not conform is not ingested, yet `submit`
        // still answers it `Ok` (a fail-closed deny), so `Ok` alone does not
        // say the event entered the history. Ask the same check `submit` runs.
        let conforms = self
            .lowered
            .check_event_conformance(&built, self.authorizer.mirror_rule())
            .is_ok();

        // `submit`, not `is_authorized`: the latter folds a *rejected* history
        // event (one that does not conform to the event schema, so is not
        // ingested) into the same `None` as an ingested one. Here that would be
        // silent data loss — a host logging a malformed `response` would see
        // success while later temporal checks never see the event — so the
        // rejection is reported instead, like every other check above.
        let response = match self.authorizer.submit(&built) {
            Ok(response) => response,
            Err(rejection) => {
                return Err(OpError::message(format!(
                    "event rejected, not recorded in the history: {rejection}"
                )));
            }
        };

        // Record the timestamp for the ordering check on the next call only if
        // the event entered the history. A rejected history event never gets
        // here; a nonconforming decision event does, denied, and must leave
        // the ordering untouched too — otherwise one bad event (say, a
        // timestamp in milliseconds) would block every later one.
        if conforms {
            self.last_timestamp = Some(event.timestamp);
        }

        // `None` is a history-only event: temporal state advanced, no verdict.
        let Some(response) = response else {
            return Ok(None);
        };

        // Fail closed on any evaluation error, exactly as `replay` does (see
        // `fail_closed`). `Response::allowed()` reads only Cedar's decision, so
        // it cannot be used.
        let errors: Vec<String> = response.diagnostics().errors().map(str::to_string).collect();
        let mut verdict = match response.decision() {
            Decision::Allow => Verdict::Allow,
            Decision::Deny => Verdict::Deny,
        };
        let mut determining_rules: Vec<usize> =
            response.diagnostics().reason().map(|r| r.rule_index).collect();
        fail_closed(&mut verdict, &mut determining_rules, &errors);
        let decision = AuthorizerDecision {
            index: self.decisions,
            timestamp: event.timestamp,
            verdict,
            allowed: verdict == Verdict::Allow,
            determining_rules,
            errors,
        };
        self.decisions += 1;
        Ok(Some(decision))
    }

    /// Drop all accumulated temporal history and start over with the same
    /// lowered policy set (no re-lowering). The decision index restarts at 0.
    ///
    /// Infallible today; it keeps its `Result` so the bindings' signature does
    /// not change.
    pub fn reset(&mut self) -> Result<(), OpError> {
        self.authorizer = Authorizer::new(self.lowered.clone());
        self.decisions = 0;
        // A fresh history is a fresh ordering: the next event may carry any
        // timestamp, including one before the last event of the old history.
        self.last_timestamp = None;
        Ok(())
    }

    /// How many decisions this instance has returned — the `index` the next
    /// decision will carry.
    pub fn decision_count(&self) -> usize {
        self.decisions
    }

    /// The event kinds that are decision points under this instance's event
    /// schema (`["request"]` by default) — the kinds for which
    /// [`isAuthorized`](Self::is_authorized) returns a decision rather than
    /// `None`/`undefined`.
    ///
    /// A kind in [`eventKinds`](Self::event_kinds) but not here is history-only:
    /// it is accepted, it updates temporal state, and it yields no verdict.
    pub fn decision_kinds(&self) -> Vec<String> {
        self.surface.decision_kinds.clone()
    }

    /// Every event kind this instance's event schema declares, decision points
    /// and history-only alike (`["error", "request", "response"]` by default).
    /// Any other kind is rejected — see [`isAuthorized`](Self::is_authorized).
    pub fn event_kinds(&self) -> Vec<String> {
        self.surface.kinds.iter().cloned().collect()
    }

    /// Every **fully qualified** action id this instance can decide
    /// (`["Drupe::Action::Read", …]`) — the actions the action schema declares.
    /// An event naming anything else is rejected, so a host that maps its own
    /// operation names onto Cedar actions can check the mapping against this
    /// once at startup rather than discovering a gap one denied request at a
    /// time.
    pub fn actions(&self) -> Vec<String> {
        self.surface.actions.keys().cloned().collect()
    }

    /// The timestamp of the most recent event observed, or `None`/`undefined` before
    /// the first (and after a [`reset`](Self::reset)). The next event's
    /// timestamp must be at least this.
    ///
    pub fn last_timestamp(&self) -> Option<i64> {
        self.last_timestamp
    }
}
