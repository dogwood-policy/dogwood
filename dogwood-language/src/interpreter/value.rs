//! The runtime value and trace model for temporal evaluation.
//!
//! Uses the trace data model the `.log` corpus is written against, so the
//! existing corpus parses verbatim and verdicts match:
//! a trace is a sequence of timepoints, each carrying exactly one
//! flat event (a predicate name plus named fields). Reserved fields
//! `callerPrincipal` / `callerResource` / `requestId` travel as
//! ordinary named fields.

use std::collections::BTreeMap;

/// A runtime value (event field, bound variable, or literal).
/// A Dogwood runtime value.
///
/// `PartialEq`/`Eq` are **structural**: `Value::Decimal` compares its text
/// verbatim (so `"1.5"` != `"1.50"`), which makes `==` a predictable exact
/// comparison for tests and keying. For the domain-correct comparison that
/// canonicalizes decimals, use [`Value::dom_eq`]. (This mirrors Cedar, whose
/// public value type `EvalResult` likewise derives structural equality.)
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Value {
    Null,
    Bool(bool),
    Int(i64),
    /// Decimal kept as canonical text; [`dom_eq`](Value::dom_eq)
    /// canonicalizes, but structural `==` compares the text verbatim.
    Decimal(String),
    String(String),
    Entity {
        ty: String,
        id: String,
    },
    Array(Vec<Value>),
    Object(BTreeMap<String, Value>),
}

impl Value {
    /// Structural equality, with decimals compared the way Cedar compares them.
    ///
    /// A `decimal` is Cedar's extension type, so two decimals are equal exactly
    /// when Cedar says they are — see `cedar_decimal_value`.
    pub fn dom_eq(&self, other: &Value) -> bool {
        match (self, other) {
            (Value::Decimal(a), Value::Decimal(b)) => decimal_eq(a, b),
            (Value::Array(a), Value::Array(b)) => {
                a.len() == b.len() && a.iter().zip(b).all(|(x, y)| x.dom_eq(y))
            }
            (Value::Object(a), Value::Object(b)) => {
                a.len() == b.len()
                    && a.iter()
                        .zip(b)
                        .all(|((ka, va), (kb, vb))| ka == kb && va.dom_eq(vb))
            }
            _ => self == other,
        }
    }

    /// Integer view for numeric comparison; `None` if not an integer.
    pub fn as_int(&self) -> Option<i64> {
        match self {
            Value::Int(n) => Some(*n),
            _ => None,
        }
    }
}

/// Cedar's internal value for a decimal spelling, or `None` when Cedar would not
/// accept it as a decimal at all.
///
/// Cedar represents a decimal as `value / 10^4` held in an `i64`, and DERIVES
/// equality and ordering on that integer — so equality is numeric, and independent
/// of how the value was written. Its parser requires digits on both sides of the
/// point, allows at most four fractional digits, and bounds the result to the `i64`
/// range (which is exactly its documented
/// `-922337203685477.5808 .. 922337203685477.5807`).
///
/// Reproduced here rather than called through Cedar because this sits on the
/// interpreter's equality path, and reaching into an extension function per
/// comparison would be absurd. The reproduction is not trusted on inspection:
/// `tests/decimal_equality_matches_cedar.rs` asks Cedar's own constructor for its
/// verdict on each case and requires this to agree.
fn cedar_decimal_value(s: &str) -> Option<i64> {
    const NUM_DIGITS: u32 = 4;

    // A point is required, with digits on both sides.
    let (int_str, frac_str) = s.split_once('.')?;
    if frac_str.is_empty() || !frac_str.bytes().all(|b| b.is_ascii_digit()) {
        return None;
    }
    let digits = int_str.strip_prefix('-').unwrap_or(int_str);
    if digits.is_empty() || !digits.bytes().all(|b| b.is_ascii_digit()) {
        return None;
    }
    let frac_len: u32 = frac_str.len().try_into().ok()?;
    if frac_len > NUM_DIGITS {
        return None;
    }

    let whole = int_str.parse::<i64>().ok()?;
    let scaled = whole.checked_mul(10_i64.checked_pow(NUM_DIGITS)?)?;
    let frac = frac_str
        .parse::<i64>()
        .ok()?
        .checked_mul(10_i64.checked_pow(NUM_DIGITS - frac_len)?)?;

    // The SIGN comes from the spelling, not from the parsed whole part, so that a
    // negative zero (`-0.5`, whose whole part parses to 0) subtracts its fraction.
    if int_str.starts_with('-') {
        scaled.checked_sub(frac)
    } else {
        scaled.checked_add(frac)
    }
}

/// Whether two decimal spellings denote the same value.
///
/// Spellings Cedar ACCEPTS compare by value, so `1.5`, `1.50`, `02.5` and `-0.0`
/// versus `0.0` all resolve the way a policy would resolve them.
///
/// A spelling Cedar REJECTS is not a decimal, and Cedar defines no equality between
/// values it will not construct — so such text compares only to itself, exactly.
/// That keeps the relation reflexive without inventing an equality: notably `1` is
/// not equated with `1.0`, because Cedar rejects `1` outright rather than reading it
/// as one.
fn decimal_eq(a: &str, b: &str) -> bool {
    match (cedar_decimal_value(a), cedar_decimal_value(b)) {
        (Some(x), Some(y)) => x == y,
        _ => a == b,
    }
}

/// One entity's decision-time data: its attributes and its **direct** parent
/// (`memberOf`) edges. Mirrors Cedar's per-entity representation — both
/// `cedar_policy::Entity::new(uid, attrs, parents)` and the `entities.json`
/// shape `{ uid, attrs, parents: [...] }` — so a Cedar entity round-trips into
/// this record field-for-field. Cedar computes the transitive ancestor closure
/// from these direct edges, so only direct parents are supplied.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct EntityRecord {
    /// Supplied attributes, `attr -> value`. This is the map the whole existing
    /// attribute path (`resolve_entity_attr`, `entity_attributes`, `scope_attr`)
    /// reads; parents are deliberately kept out of it.
    pub attrs: BTreeMap<String, Value>,
    /// Direct parents as entity-refs (`Value::Entity { ty, id }`). Empty is the
    /// back-compat default (no hierarchy). Fed to the Cedar authorizer so
    /// `principal in Group` / `resource in …` resolve; the temporal path does
    /// not read this (temporal predicates have no `in`).
    pub parents: Vec<Value>,
}

/// One event: a structured identity (qualified action + kind) plus its
/// named fields. The event kind (`request` / `response` / …) is a
/// first-class component, not a suffix on a name string.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct EventData {
    /// Qualified action path, e.g. `["Drupe", "Action"]`.
    pub namespace: Vec<String>,
    /// The action id, e.g. `Login`.
    pub action: String,
    /// The event kind, e.g. `request` / `response`.
    pub kind: String,
    /// The **temporal-history** fields: the durable record the temporal engine
    /// persists on `observe` and that future timepoints can correlate against.
    /// Governed by the event schema (a projection): `input`, the reserved
    /// `caller*` scope aliases, pinned correlation fields. This is the
    /// *persisted* subset, distinct from the ephemeral, per-decision
    /// [`request_context`](Self::request_context) the Cedar request is built
    /// from: temporal predicate matching reads *only* `logged`, so a
    /// request-only field is invisible to correlation. A field both need
    /// (`input`) is supplied in both by design.
    pub logged: BTreeMap<String, Value>,
    /// The **request-only** context: fields the action schema declares that are
    /// not part of the logged temporal record (e.g. `system`), supplied to
    /// build the Cedar request for *this* decision and never persisted. The
    /// Cedar request context is composed from this (plus hoisted temporal /
    /// provider fields), reading *nothing* from [`logged`](Self::logged); a
    /// field needed by both (`input`) is supplied in both, by design. Empty
    /// for events that supply no request-only context.
    pub request_context: BTreeMap<String, Value>,
    /// Entity store for this decision: uid string (`Ns::Type::"id"`) -> its
    /// [`EntityRecord`] (attributes + direct parents). Supplied by the caller
    /// (via [`EventBuilder::entity`] / [`EventBuilder::entity_parents`] or a
    /// `.log` `entities(...)` envelope) so a policy can read
    /// `principal.<attr>` / `resource.<attr>` and resolve membership
    /// (`principal in Group`). The scope principal/resource are made *present*
    /// in the Cedar store regardless (bare, attribute-less) so identity
    /// comparisons never see a missing entity; this map adds attributes and
    /// hierarchy. Empty for events that supply neither.
    pub entities: BTreeMap<String, EntityRecord>,
}

impl EventData {
    /// A **logged** field by top-level key (the temporal-history record).
    pub fn field(&self, key: &str) -> Option<&Value> {
        self.logged.get(key)
    }

    /// Look up a possibly-nested **logged** field by dotted path, descending
    /// into [`Value::Object`] at each non-final segment. `["input", "user"]`
    /// reads the `user` member of the `input` sub-record; a single-segment
    /// path (`["requestId"]`) is the flat [`EventData::field`] lookup.
    ///
    /// Returns `None` if any segment is absent or if an intermediate
    /// segment is not an object (so descending through a scalar fails
    /// cleanly rather than panicking). An empty path is `None`. Reads only
    /// `logged` — request-only context is not visible to temporal matching.
    pub fn field_path(&self, path: &[String]) -> Option<&Value> {
        path_descend(&self.logged, path)
    }

    /// A **request-context** field by top-level key. The request-only context
    /// (`input`, `system`, …) the Cedar request is built from; distinct from
    /// the logged temporal record.
    pub fn request_context_field(&self, key: &str) -> Option<&Value> {
        self.request_context.get(key)
    }

    /// Look up a possibly-nested **request-context** field by dotted path — the
    /// request-only analog of [`field_path`](EventData::field_path), descending
    /// [`Value::Object`] at each non-final segment. This is the bag the Cedar
    /// request context and provider arguments read; temporal predicate matching
    /// reads `logged` instead ([`field_path`](EventData::field_path)), keeping
    /// the two datasets separate.
    pub fn request_context_path(&self, path: &[String]) -> Option<&Value> {
        path_descend(&self.request_context, path)
    }

    /// Resolve an **attribute path** off a scope entity (`ty::"id"`) against
    /// this event's [`entities`](Self::entities) store — the single source of
    /// truth for `principal.<attr>` / `resource.<attr>` semantics, shared by the
    /// provider-arg resolver (`resolve_scope_path`) and the temporal env seeder
    /// (`seed_scope_env`) so the two agree by construction:
    ///
    ///   * a **supplied** attribute wins: the first segment is looked up in the
    ///     uid's supplied attributes, then any remaining segments descend nested
    ///     records (a non-record encountered mid-path is unresolvable);
    ///   * failing that, a single-segment `.id` / `.type` **projects the uid**
    ///     (so an identity-only entity still resolves those), but a supplied
    ///     attribute of the same name takes precedence (checked first);
    ///   * anything else — an unsupplied attribute, or a deeper path with no
    ///     supplied root — is `None` (absent).
    ///
    /// An empty `path` is `None` (a bare `principal` is the whole entity, which
    /// the callers handle before descending). Callers map `None` to their own
    /// "absent" (`Value::Null` for a provider arg; an unset env key for
    /// temporal), where a required attribute later surfaces via schema
    /// conformance on the Cedar path.
    pub fn resolve_entity_attr(&self, ty: &str, id: &str, path: &[String]) -> Option<Value> {
        let (attr, deeper) = path.split_first()?;
        let uid = entity_uid_string(ty, id);
        if let Some(start) = self
            .entities
            .get(&uid)
            .and_then(|rec| rec.attrs.get(attr.as_str()))
        {
            let mut cur = start;
            for seg in deeper {
                match cur {
                    Value::Object(map) => cur = map.get(seg.as_str())?,
                    // A non-record encountered mid-path is unresolvable.
                    _ => return None,
                }
            }
            return Some(cur.clone());
        }
        // No supplied attribute: `.id` / `.type` project the uid for a
        // single-segment path (a deeper path has no uid-projection fallback).
        if deeper.is_empty() {
            match attr.as_str() {
                "id" => return Some(Value::String(id.to_string())),
                "type" => return Some(Value::String(ty.to_string())),
                _ => {}
            }
        }
        None
    }
}

/// Walk a logged-field map, emitting `(dotted_path, value)` for every entry:
/// a group/record node ([`Value::Object`]) is emitted whole at its own path
/// AND recursed into; a scalar is emitted as a leaf. Backs
/// [`Event::logged_leaves`]. `prefix` accumulates the path segments; it is
/// pushed/popped in place so no per-level allocation is needed.
fn collect_logged_leaves<'a>(
    map: &'a BTreeMap<String, Value>,
    prefix: &mut Vec<String>,
    out: &mut Vec<(Vec<String>, &'a Value)>,
) {
    for (name, value) in map {
        prefix.push(name.clone());
        out.push((prefix.clone(), value));
        if let Value::Object(members) = value {
            collect_logged_leaves(members, prefix, out);
        }
        prefix.pop();
    }
}

/// Descend a dotted `path` into a top-level map, following [`Value::Object`] at
/// each non-final segment. Shared by [`EventData::field_path`] and
/// [`EventData::request_context_path`]. Returns `None` if any segment is absent
/// or an intermediate segment is not an object; an empty path is `None`.
fn path_descend<'a>(top: &'a BTreeMap<String, Value>, path: &[String]) -> Option<&'a Value> {
    let (head, rest) = path.split_first()?;
    let mut cur = top.get(head)?;
    for seg in rest {
        match cur {
            Value::Object(map) => cur = map.get(seg)?,
            _ => return None,
        }
    }
    Some(cur)
}

/// The request scope of a trace point — principal and resource — kept
/// separate from the event's fields because Cedar models them as
/// distinct positional request arguments, not context. Present on events
/// that are authorized (decision points); absent on history-only events
/// that never build a request.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct Scope {
    pub principal: Option<Value>,
    pub resource: Option<Value>,
}

/// One event fed to an [`crate::Authorizer`]: a timestamped occurrence
/// of an action, of a given *kind*, carrying named input fields and — when
/// the event wraps an authorization request — a principal/resource scope.
///
/// `Event` is Dogwood's analog of a Cedar `Request`, generalized in two
/// ways that Cedar cannot express:
///
///   * **`kind` is first-class.** A `request`-kind event is a decision point
///     (it authorizes); a `response`-kind event is history-only (it
///     updates temporal state but yields no verdict). Which kinds decide is
///     data (the event schema's `decision` flags), not a hardcoded
///     convention.
///   * **the request scope is optional.** Only an event that wraps a request
///     carries a principal/resource; history-only events do not.
///
/// Build one with [`Event::builder`], or lift a Cedar `Request` into a
/// `request`-kind event with [`Event::from_request`].
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Event {
    pub(crate) ts: i64,
    pub(crate) scope: Scope,
    pub(crate) event: EventData,
}

impl Event {
    /// Assemble an `Event` from already-built parts. Crate-internal: used by
    /// the `.log` trace parser and the Cedar-`Request` adapter, which build
    /// the [`EventData`]/[`Scope`] directly.
    pub(crate) fn from_parts(ts: i64, scope: Scope, event: EventData) -> Self {
        Event { ts, scope, event }
    }

    /// Start building an `Event` for `action` of the given `kind`. The
    /// `action` is the qualified Cedar action id — either a bare id
    /// (`"Login"`) or namespaced (`"Drupe::Action::Login"`).
    ///
    /// The id is recovered from the combined string by splitting on the **last**
    /// `::`, so this is safe only when the id is a bare token with no interior
    /// `::`. Cedar permits any string as an action id (an `EntityId` is opaque),
    /// so for an id that contains `:` / `::`, use the structured
    /// [`builder_for`](Event::builder_for), which takes the id as its own
    /// verbatim component.
    pub fn builder(action: &str, kind: &str) -> EventBuilder {
        let (namespace, action) = split_qualified_action(action);
        Self::from_action_parts(namespace, action, kind)
    }

    /// Start building an `Event` from a **structured** action identity: the
    /// qualified action *type* path (`["Drupe", "Action"]`) and the raw
    /// action *id* (`"Login"`), supplied as separate components rather than one
    /// combined `Ns::Action::id` string.
    ///
    /// This is the analog of Cedar's `EntityUid::from_type_name_and_id`, which
    /// joins a parsed type name and an opaque id **structurally** — never by
    /// string concatenation or re-parsing. Prefer it when the id is not a safe
    /// bare token: [`builder`](Event::builder) recovers the id from a combined
    /// string by splitting on the last `::`, so an id that itself contains `:` /
    /// `::` (which Cedar permits — an `EntityId` is any string) is mangled before
    /// it is ever escaped. `builder_for` stores `action_id` verbatim, so any id
    /// round-trips: the downstream Cedar render (`api::qualified_action_uid`)
    /// escapes it canonically at the boundary.
    ///
    /// `namespace` is the action type path exactly as
    /// [`namespace`](Event::namespace) reports it (the `Action` type component
    /// included, e.g. `["Photo", "Action"]` for `Photo::Action::"view"`); an
    /// empty slice is a bare, unnamespaced action.
    pub fn builder_for(namespace: &[&str], action_id: &str, kind: &str) -> EventBuilder {
        let namespace = namespace.iter().map(|s| s.to_string()).collect();
        Self::from_action_parts(namespace, action_id.to_string(), kind)
    }

    /// Assemble a fresh [`EventBuilder`] from already-split action parts (a
    /// namespace path + bare id). Shared by [`builder`](Event::builder) (which
    /// splits a combined string) and [`builder_for`](Event::builder_for) (which
    /// is handed the components directly).
    fn from_action_parts(namespace: Vec<String>, action: String, kind: &str) -> EventBuilder {
        EventBuilder {
            ts: 0,
            scope: Scope::default(),
            event: EventData {
                namespace,
                action,
                kind: kind.to_string(),
                logged: BTreeMap::new(),
                request_context: BTreeMap::new(),
                entities: BTreeMap::new(),
            },
        }
    }

    /// The event kind, e.g. `"request"` or `"response"`.
    pub fn kind(&self) -> &str {
        &self.event.kind
    }

    /// The action id (unqualified), e.g. `"Login"`.
    pub fn action(&self) -> &str {
        &self.event.action
    }

    /// The qualified action namespace path, e.g. `["Drupe", "Action"]`.
    /// Empty for a bare (unnamespaced) action.
    pub fn namespace(&self) -> &[String] {
        &self.event.namespace
    }

    /// The event's wall-clock timestamp.
    pub fn timestamp(&self) -> i64 {
        self.ts
    }

    /// The request principal entity uid (e.g. `Drupe::OAuthUser::"alice"`),
    /// if this event wraps a request. `None` for a history-only event with no
    /// scope. A custom [`TemporalEngine`](crate::TemporalEngine) or
    /// [`PolicyEngine`](crate::PolicyEngine) reads this to persist or forward
    /// the request.
    pub fn principal(&self) -> Option<String> {
        self.scope.principal.as_ref().and_then(value_uid_string)
    }

    /// The request resource entity uid (e.g. `Drupe::Gateway::"gw1"`), if
    /// this event wraps a request; `None` otherwise.
    pub fn resource(&self) -> Option<String> {
        self.scope.resource.as_ref().and_then(value_uid_string)
    }

    /// One field of the event's **logged temporal record**, by `group` and
    /// `name` — the durable history a temporal predicate field-arg matches
    /// against (the `logged` bag), *not* the Cedar request context (the
    /// separate `request_context` bag). `None` if the event has no such logged
    /// field. The legal groups are defined by the event schema (e.g. `input`,
    /// `output`).
    pub fn field(&self, group: &str, name: &str) -> Option<&Value> {
        match self.event.logged.get(group) {
            Some(Value::Object(map)) => map.get(name),
            _ => None,
        }
    }

    /// Every field in a named `group`, as `(name, value)` pairs — what an
    /// engine that persists history outside the process would record on
    /// [`observe`](crate::TemporalEngine::observe).
    pub fn fields(&self, group: &str) -> impl Iterator<Item = (&str, &Value)> {
        let map = match self.event.logged.get(group) {
            Some(Value::Object(map)) => Some(map),
            _ => None,
        };
        map.into_iter()
            .flat_map(|m| m.iter().map(|(k, v)| (k.as_str(), v)))
    }

    /// A field by its full dotted path, descending nested groups. A
    /// single-segment path reads a **top-level** field (e.g. a reserved
    /// correlation field like `["__drupe_sessionid"]` or a scope alias
    /// `["requestId"]`); a multi-segment path descends group records
    /// (`["input", "user"]` reads the `user` member of the `input` group,
    /// the same as [`field`](Event::field)`("input", "user")`).
    ///
    /// This is the general accessor for serializing a policy's correlation
    /// fields into an event's persisted context — including
    /// top-level fields that carry no group prefix, which
    /// [`field`](Event::field) (which requires a group) cannot reach.
    /// Returns `None` if any segment is absent or an intermediate segment is
    /// not a record.
    pub fn field_path(&self, path: &[String]) -> Option<&Value> {
        self.event.field_path(path)
    }

    /// Every logged field as `(dotted_path, value)`, recursively. A group /
    /// record node ([`Value::Object`]) is BOTH emitted whole at its own path
    /// AND descended into: emitting the intermediate object preserves the
    /// whole-value encoding of a record- or set-valued field (a predicate may
    /// match `input.metadata` wholesale or `input.metadata.x` individually —
    /// the interpreter's [`field_path`](Event::field_path) resolves both), and
    /// descending yields the individual leaves.
    ///
    /// This is the schema- and name-free basis for serializing an event to the
    /// temporal engine's wire form: every field the event carries is emitted at its
    /// dotted path, with no privileged treatment of `input`/`output`/`caller*`
    /// — mirroring the interpreter, whose matching is uniform over
    /// [`field_path`](Event::field_path). A consumer reads whatever path a
    /// policy references; an absent path is a NULL read (a non-match), exactly
    /// as `field_path` returns `None`.
    pub fn logged_leaves(&self) -> Vec<(Vec<String>, &Value)> {
        let mut out = Vec::new();
        collect_logged_leaves(&self.event.logged, &mut Vec::new(), &mut out);
        out
    }

    /// A **request-context** field by its full dotted path, descending nested
    /// group records (`["input", "user"]` reads the `user` member of the `input`
    /// group). Reads the `request_context` bag — the Cedar request context, a
    /// deliberately separate dataset from the logged temporal record.
    ///
    /// This is the request-only analog of [`field_path`](Event::field_path): it
    /// serializes a policy's `context.<path>` references into a request-only
    /// channel read at verdict time (never persisted).
    ///
    /// Returns `None` if any segment is absent or an intermediate segment is
    /// not a record.
    pub fn request_context_path(&self, path: &[String]) -> Option<&Value> {
        self.event.request_context_path(path)
    }

    /// Every top-level group of the request context, as `(name, value)` pairs.
    /// A [`TemporalEngine`](crate::TemporalEngine) iterates this to serialize
    /// the whole request-context bag (mirroring [`fields`](Event::fields) for
    /// the logged record). The value is typically a [`Value::Object`] whose
    /// members are the group's fields.
    pub fn request_context_groups(&self) -> impl Iterator<Item = (&str, &Value)> {
        self.event
            .request_context
            .iter()
            .map(|(k, v)| (k.as_str(), v))
    }

    /// The request principal's entity uid (canonically-formatted with the
    /// `Ns::Type::"id"` shape used by [`Value::Entity`] rendering), if this
    /// event wraps a request; `None` otherwise. The uid string form is the
    /// same key format entity attributes are stored under in
    /// [`entity_attributes`](Event::entity_attributes).
    pub fn principal_uid(&self) -> Option<String> {
        self.scope.principal.as_ref().and_then(value_uid_string)
    }

    /// The request resource's entity uid, formatted like
    /// [`principal_uid`](Event::principal_uid); `None` if the event has no
    /// scope resource.
    pub fn resource_uid(&self) -> Option<String> {
        self.scope.resource.as_ref().and_then(value_uid_string)
    }

    /// All supplied attributes for a given entity uid, as `(name, value)`
    /// pairs. The uid is the canonical `Ns::Type::"id"` form as produced by
    /// `entity_uid_string`. Returns an empty iterator if the uid has no
    /// supplied attributes. Serializes the whole entity-attribute store for
    /// the current request.
    pub fn entity_attributes(&self, uid: &str) -> impl Iterator<Item = (&str, &Value)> {
        self.event
            .entities
            .get(uid)
            .into_iter()
            .flat_map(|rec| rec.attrs.iter().map(|(k, v)| (k.as_str(), v)))
    }

    /// The **direct parents** (`memberOf` edges) supplied for an entity uid, as
    /// entity-ref values. The uid is the canonical `Ns::Type::"id"` form. Empty
    /// slice if the uid has no supplied hierarchy. The public read-side
    /// counterpart of [`EventBuilder::entity_parents`]; the analog of
    /// [`entity_attributes`](Event::entity_attributes) for hierarchy.
    pub fn entity_parents(&self, uid: &str) -> &[Value] {
        self.event
            .entities
            .get(uid)
            .map(|rec| rec.parents.as_slice())
            .unwrap_or(&[])
    }

    /// Resolve an entity **attribute path** off a scope entity — the temporal
    /// analog of a Cedar `principal.<attr>` / `resource.<attr>` read. `root`
    /// must be `"principal"` or `"resource"`; `attrs` is the attribute tail
    /// (e.g. `["dept"]` for `principal.dept`).
    ///
    /// Serializes a policy's `principal.<attr>` / `resource.<attr>` references
    /// into a request-only channel read at verdict time.
    ///
    /// A bare `root` (empty `attrs`) returns the entity itself as
    /// [`Value::Entity`]. An attribute tail follows the same response as
    /// `EventData::resolve_entity_attr`: supplied attributes win, then
    /// `.id` / `.type` project the uid, else `None`.
    pub fn scope_attr(&self, root: &str, attrs: &[String]) -> Option<Value> {
        let entity = match root {
            "principal" => self.scope.principal.as_ref()?,
            "resource" => self.scope.resource.as_ref()?,
            _ => return None,
        };
        if attrs.is_empty() {
            return Some(entity.clone());
        }
        let Value::Entity { ty, id } = entity else {
            return None;
        };
        self.event.resolve_entity_attr(ty, id, attrs)
    }

    /// The event's payload (action identity + kind + fields). Crate-internal:
    /// the decision path reads it to build the Cedar request/context.
    pub(crate) fn data(&self) -> &EventData {
        &self.event
    }

    /// The event's request scope (principal / resource). Crate-internal.
    pub(crate) fn scope(&self) -> &Scope {
        &self.scope
    }

    /// Lift a Cedar `Request` into a `request`-kind [`Event`] at timestamp
    /// `0` — the interop bridge for callers coming from the `cedar-policy`
    /// crate. The request's principal/resource become the event's scope, its
    /// action its qualified action, and its `context.input` its input fields.
    ///
    /// A stateless, single-decision authorization is then a fresh
    /// [`crate::Authorizer`] fed this one event.
    ///
    /// **Partitioned evaluation caveat:** only the `input` context group and the
    /// scope aliases (`callerPrincipal` / `callerResource`) are mirrored into the
    /// event's logged record; other context groups populate the request-only
    /// context but not `logged`. Since temporal correlation (and partition
    /// routing) reads the logged record, a **pin on a non-`input` context field**
    /// (e.g. `pin sessionId = context.sessionId`) is not carried into `logged` by
    /// this bridge — supply that field to the logged record too (or construct the
    /// event via [`Event::builder`]) if such an event participates in partitioned
    /// temporal history. Not a concern for the single-decision use above (no
    /// history to correlate against) or for scope / `input.*` pins.
    pub fn from_request(request: &cedar_policy::Request) -> Result<Event, crate::api::Error> {
        crate::api::request_to_event(0, request)
    }
}

/// Builder for an [`Event`]. Setting a principal or resource marks the event
/// as wrapping an authorization request (it gains a principal/resource scope).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct EventBuilder {
    ts: i64,
    scope: Scope,
    event: EventData,
}

impl EventBuilder {
    /// Set the event's wall-clock timestamp (default `0`). Timestamps order
    /// events for temporal operators; the first event of a fresh
    /// [`crate::Authorizer`] can leave it at `0`.
    pub fn timestamp(mut self, ts: i64) -> Self {
        self.ts = ts;
        self
    }

    /// Set the request principal — a Cedar entity uid like
    /// `User::"alice"`. Setting it makes the event request-wrapping.
    pub fn principal(mut self, uid: &str) -> Self {
        let value = uid_to_value(uid);
        if let Some(v) = value.clone() {
            self.event.logged.insert("callerPrincipal".to_string(), v);
        }
        self.scope.principal = value;
        self
    }

    /// Set the request resource — a Cedar entity uid like
    /// `Photo::"vacation.jpg"`. Setting it makes the event request-wrapping.
    pub fn resource(mut self, uid: &str) -> Self {
        let value = uid_to_value(uid);
        if let Some(v) = value.clone() {
            self.event.logged.insert("callerResource".to_string(), v);
        }
        self.scope.resource = value;
        self
    }

    /// Set the request principal from **structured** `(ty, id)` components —
    /// the entity *type* (`"Svc::User"`) and its raw *id* (`"alice"`) — instead
    /// of a combined `Ns::Type::"id"` literal. The analog of Cedar's
    /// `EntityUid::from_type_name_and_id`: the [`Value::Entity`] is built from
    /// the components directly, so nothing is parsed or unescaped and the id
    /// (which Cedar allows to be any string) round-trips verbatim.
    ///
    /// Prefer this over [`principal`](EventBuilder::principal) when the id is
    /// not a plain token — an id containing `"` / `\` / control chars must be
    /// hand-escaped into the literal `principal` expects, and re-escaping an
    /// already-escaped id double-escapes; `principal_for` takes the decoded id
    /// and escapes it exactly once at the Cedar boundary. Setting it makes the
    /// event request-wrapping.
    pub fn principal_for(mut self, ty: &str, id: &str) -> Self {
        let value = Value::Entity {
            ty: ty.to_string(),
            id: id.to_string(),
        };
        self.event
            .logged
            .insert("callerPrincipal".to_string(), value.clone());
        self.scope.principal = Some(value);
        self
    }

    /// Set the request resource from **structured** `(ty, id)` components — the
    /// resource analog of [`principal_for`](EventBuilder::principal_for).
    pub fn resource_for(mut self, ty: &str, id: &str) -> Self {
        let value = Value::Entity {
            ty: ty.to_string(),
            id: id.to_string(),
        };
        self.event
            .logged
            .insert("callerResource".to_string(), value.clone());
        self.scope.resource = Some(value);
        self
    }

    /// Set one field of the **logged temporal record** under a named `group`.
    /// This populates the `logged` bag — the durable history a temporal
    /// predicate *field-arg* matches against (`Login{ input.user: … }`), not the
    /// Cedar request context.
    ///
    /// **This is NOT read by a policy's `context.<group>.<name>` clause.** The
    /// Cedar request context is built from
    /// [`request_context`](EventBuilder::request_context), a deliberately
    /// separate bag. A field a policy reads via `context.<...>` *and* a temporal
    /// predicate correlates on (the common `input` case) must be supplied to
    /// **both**: `.field(group, name, v)` here (for temporal) and
    /// `.request_context(group, name, v)` (for the Cedar request). Supplying
    /// only one leaves the other consumer's read unresolved.
    ///
    /// The set of legal groups (`input`, `output`, and any others) is defined
    /// by the event schema, not by this builder — so this method names the
    /// group explicitly rather than privileging any particular one (there is no
    /// per-group convenience setter; `input` is written as `field("input", …)`
    /// like every other group).
    pub fn field(mut self, group: &str, name: &str, value: Value) -> Self {
        let entry = self
            .event
            .logged
            .entry(group.to_string())
            .or_insert_with(|| Value::Object(BTreeMap::new()));
        if let Value::Object(map) = entry {
            map.insert(name.to_string(), value);
        }
        self
    }

    /// Supply the attributes of an **entity** referenced by this decision,
    /// keyed by its uid (`"Ns::Type::\"id\""`). This is what lets a policy read
    /// an entity attribute — `principal.dept`, `resource.owner` — or a provider
    /// argument resolve one. For membership (`principal in Group::"x"`) supply
    /// the entity's parents via [`entity_parents`](EventBuilder::entity_parents).
    ///
    /// Cedar keeps entity *identity* (the uid, in the request scope) separate
    /// from entity *attributes* (this store); Dogwood mirrors that. The scope
    /// principal/resource are always made present in the store even without a
    /// call here, but attribute-less; call this to give them (or any other
    /// entity a policy names) attributes. Repeated calls for the same uid merge
    /// (last value per attribute wins).
    ///
    /// Supplied attributes are validated against the schema at decision time,
    /// so a wrong-typed or (for a `required`-attr type) incomplete entity fails
    /// closed with a diagnostic rather than silently mis-deciding.
    ///
    /// **`uid` must already be a canonical Cedar literal** (`Ns::Type::"id"`
    /// with the id escaped as `entity_uid_string` produces, e.g. a control
    /// char written `\u{..}`). The store is keyed by this string verbatim, and
    /// lookups reconstruct the key by escaping a *decoded* id — so a non-canonical
    /// key never matches, and, because the escaper is **not idempotent**
    /// (`\` → `\\` → `\\\\`), an *already-escaped* id passed back through the
    /// escaper double-escapes. Build the uid from a decoded `(ty, id)` via
    /// `entity_uid_string` exactly once; do not escape it yourself and do not
    /// pass raw control/whitespace bytes.
    pub fn entity<'a>(
        mut self,
        uid: &str,
        attrs: impl IntoIterator<Item = (&'a str, Value)>,
    ) -> Self {
        let entry = self.event.entities.entry(uid.to_string()).or_default();
        for (name, value) in attrs {
            entry.attrs.insert(name.to_string(), value);
        }
        self
    }

    /// Supply the **direct parents** (`memberOf` edges) of an entity referenced
    /// by this decision, keyed by its uid. This is what lets a policy resolve
    /// membership — `principal in Group::"admins"`, `resource in Folder::"f"`.
    /// Each parent is an entity uid (`"Ns::Type::\"id\""`); Cedar computes the
    /// transitive ancestor closure, so only direct parents are supplied.
    ///
    /// Composes with [`entity`](EventBuilder::entity): call both for an entity
    /// that has attributes *and* parents. Repeated calls for the same uid append
    /// (parents accumulate). A parent whose type the schema forbids as a
    /// `memberOf` fails closed at decision time (Cedar hierarchy validation).
    ///
    /// Both `uid` and each parent **must be canonical Cedar literals** (see the
    /// note on [`entity`](EventBuilder::entity)): `uid` keys the store verbatim,
    /// and each parent is decoded via `uid_to_value` then re-escaped at the
    /// Cedar boundary, so a non-canonical or double-escaped literal will not
    /// resolve.
    pub fn entity_parents<'a>(
        mut self,
        uid: &str,
        parents: impl IntoIterator<Item = &'a str>,
    ) -> Self {
        let entry = self.event.entities.entry(uid.to_string()).or_default();
        for parent in parents {
            if let Some(v) = uid_to_value(parent) {
                entry.parents.push(v);
            }
        }
        self
    }

    /// Supply an entity's attributes from **structured** `(ty, id)` components
    /// plus its attributes — the structured analog of
    /// [`entity`](EventBuilder::entity). Keys the store by
    /// `entity_uid_string``(ty, id)`, which is *exactly* the key the attribute
    /// lookup reconstructs, so there is no uid literal to hand-escape and no way
    /// to double-escape: an id containing `"` / `\` / a control char is escaped
    /// canonically exactly once, here. Repeated calls for the same `(ty, id)`
    /// merge (last value per attribute wins). Composes with
    /// [`parents_for`](EventBuilder::parents_for).
    pub fn entity_for<'a>(
        mut self,
        ty: &str,
        id: &str,
        attrs: impl IntoIterator<Item = (&'a str, Value)>,
    ) -> Self {
        let entry = self
            .event
            .entities
            .entry(entity_uid_string(ty, id))
            .or_default();
        for (name, value) in attrs {
            entry.attrs.insert(name.to_string(), value);
        }
        self
    }

    /// Supply an entity's **direct parents** (`memberOf` edges) from structured
    /// `(ty, id)` components, each parent given as its own `(ty, id)` pair — the
    /// structured analog of [`entity_parents`](EventBuilder::entity_parents).
    /// The subject is keyed by `entity_uid_string``(ty, id)` and each parent
    /// [`Value::Entity`] is built from its components directly, so neither the
    /// subject uid nor any parent uid is parsed or hand-escaped (closing the
    /// double-escape footgun of the literal-taking `entity_parents`). Cedar
    /// computes the transitive closure, so only direct parents are supplied;
    /// repeated calls append. Composes with [`entity_for`](EventBuilder::entity_for).
    pub fn parents_for<'a>(
        mut self,
        ty: &str,
        id: &str,
        parents: impl IntoIterator<Item = (&'a str, &'a str)>,
    ) -> Self {
        let entry = self
            .event
            .entities
            .entry(entity_uid_string(ty, id))
            .or_default();
        for (pty, pid) in parents {
            entry.parents.push(Value::Entity {
                ty: pty.to_string(),
                id: pid.to_string(),
            });
        }
        self
    }

    /// Set one **request-only context** field under a named `group`, read by a
    /// policy as `context.<group>.<name>` — for context the action schema
    /// declares that is *not* part of the logged temporal record (e.g.
    /// `system`). Populates the `request_context` bag, which is what the Cedar
    /// request context is built from; it is never persisted to temporal history.
    ///
    /// A field the request and temporal *both* need (`input`) is not implicit:
    /// supply it here (for the request) *and* via [`field`](EventBuilder::field)
    /// (for the logged record). The two datasets are deliberately separate.
    pub fn request_context(mut self, group: &str, name: &str, value: Value) -> Self {
        let entry = self
            .event
            .request_context
            .entry(group.to_string())
            .or_insert_with(|| Value::Object(BTreeMap::new()));
        if let Value::Object(map) = entry {
            map.insert(name.to_string(), value);
        }
        self
    }

    /// Finish building the event.
    pub fn build(self) -> Event {
        Event {
            ts: self.ts,
            scope: self.scope,
            event: self.event,
        }
    }
}

/// Split a qualified Cedar action id into its namespace path and bare id.
/// `"Drupe::Action::Login"` => `(["Drupe", "Action"], "Login")`;
/// a bare `"Login"` => `([], "Login")`.
fn split_qualified_action(action: &str) -> (Vec<String>, String) {
    match action.rfind("::") {
        Some(sep) => {
            let namespace = action[..sep].split("::").map(str::to_string).collect();
            let id = action[sep + 2..].to_string();
            (namespace, id)
        }
        None => (Vec::new(), action.to_string()),
    }
}

/// Parse a Cedar entity-uid literal `Type::"id"` (possibly namespaced) into a
/// [`Value::Entity`], **unescaping** the id (`\"` → `"`, `\\` → `\`) so
/// `Value::Entity.id` holds the true id, not the escaped source form. The
/// inverse of `entity_uid_string`; the round-trip
/// `entity_uid_string(uid_to_value(s))` reproduces a valid literal, so an id
/// containing `"` / `\` is neither doubly-escaped on the Cedar path nor missed
/// by the entity-store lookup. Returns `None` if the string is not of
/// `Type::"id"` shape.
///
/// The single uid-parse for the crate: `EventBuilder::principal`/`resource`,
/// and the Cedar-`Request` lift (`api::request_to_event`) all go through it, so
/// every `Value::Entity` carries the unescaped id regardless of construction
/// path.
pub(crate) fn uid_to_value(uid: &str) -> Option<Value> {
    let q = uid.find("::\"")?;
    let ty = uid[..q].to_string();
    // Strip the opening `::"` and the final `"`, then unescape the interior.
    let id_span = uid[q + 3..].strip_suffix('"')?;
    Some(Value::Entity {
        ty,
        id: super::log_parse::unescape(id_span),
    })
}

/// Render an entity `(ty, id)` as a **canonical Cedar** uid literal `Ty::"id"`,
/// escaping the id exactly as Cedar does so the result round-trips through
/// `cedar_policy::EntityUid::from_str` (the authorizer path) and is a stable
/// entity-store key.
///
/// Cedar's canonical form (`cedar_policy_core`'s `EntityUID: Display`) is
/// `write!("{}::\"{}\"", ty, eid.escaped())` where `escaped()` is
/// `SmolStr::escape_debug()`. So we escape the id with Rust's [`str::escape_debug`],
/// which is byte-identical: it escapes `"` `\` `'`, `\n`/`\t`/`\r`/`\0`, and
/// every other control / non-printable char as `\u{..}`, leaving printable
/// ASCII and Unicode letters untouched. The previous form escaped only `"`/`\`,
/// which left control chars raw and produced literals `from_str` rejected as
/// "needs to be normalized" — silently failing entity reads for adversarial ids.
/// [`crate::interpreter::log_parse::unescape`] is the exact inverse and must be
/// kept in lockstep (the store is keyed by this escaped literal, but a lookup
/// reconstructs the key from a decoded `(ty, id)`, so `unescape(escape) == id`
/// must hold — see the round-trip tests in `entity_store.rs`).
///
/// NOTE (design): this whole escape↔unescape round-trip exists only because the
/// event entity store is keyed by the uid *string* (`BTreeMap<String, …>`),
/// unlike Cedar, which keys by a structured `EntityUID { ty, eid }` and never
/// re-parses. Keying Dogwood's store structurally would remove this round-trip
/// (and its fragility) entirely; that is the architecturally-correct fix but a
/// wider change (it reaches the temporal engine's encoder + compiler test support),
/// so for now we make the string form faithfully canonical instead.
pub(crate) fn entity_uid_string(ty: &str, id: &str) -> String {
    format!("{ty}::\"{}\"", id.escape_debug())
}

/// Render an entity [`Value`] back to a canonical Cedar uid literal; `None` for
/// a non-entity value. The single `Value` → uid-string for the crate (the scope
/// accessors here and `api::build_request` both use it).
pub(crate) fn value_uid_string(v: &Value) -> Option<String> {
    match v {
        Value::Entity { ty, id } => Some(entity_uid_string(ty, id)),
        _ => None,
    }
}

/// A full event trace.
#[derive(Debug, Clone, Default)]
pub struct Trace {
    pub points: Vec<Event>,
}

impl Trace {
    pub fn len(&self) -> usize {
        self.points.len()
    }

    /// Kept as the idiomatic companion to [`Trace::len`] (a bare `len` without
    /// `is_empty` is itself a clippy lint); not currently called.
    #[allow(dead_code)]
    pub fn is_empty(&self) -> bool {
        self.points.is_empty()
    }

    pub fn ts(&self, i: usize) -> i64 {
        self.points[i].ts
    }

    pub fn event(&self, i: usize) -> &EventData {
        &self.points[i].event
    }

    pub fn scope(&self, i: usize) -> &Scope {
        &self.points[i].scope
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn seg(parts: &[&str]) -> Vec<String> {
        parts.iter().map(|s| s.to_string()).collect()
    }

    /// Build an event with a nested `input` record plus a flat reserved
    /// field, mirroring the post-nesting event shape.
    fn nested_event() -> EventData {
        let mut input = BTreeMap::new();
        input.insert("user".to_string(), Value::String("alice".to_string()));
        input.insert("server".to_string(), Value::String("s1".to_string()));
        let mut logged = BTreeMap::new();
        logged.insert("input".to_string(), Value::Object(input));
        logged.insert("requestId".to_string(), Value::String("u1".to_string()));
        EventData {
            namespace: vec!["Drupe".to_string(), "Action".to_string()],
            action: "Login".to_string(),
            kind: "request".to_string(),
            logged,
            request_context: BTreeMap::new(),
            entities: BTreeMap::new(),
        }
    }

    #[test]
    fn field_path_flat_hit() {
        // A single-segment path is the flat lookup.
        let e = nested_event();
        assert_eq!(
            e.field_path(&seg(&["requestId"])),
            Some(&Value::String("u1".to_string()))
        );
    }

    #[test]
    fn field_path_nested_hit() {
        let e = nested_event();
        assert_eq!(
            e.field_path(&seg(&["input", "user"])),
            Some(&Value::String("alice".to_string()))
        );
        assert_eq!(
            e.field_path(&seg(&["input", "server"])),
            Some(&Value::String("s1".to_string()))
        );
    }

    #[test]
    fn field_path_missing_leaf_is_none() {
        let e = nested_event();
        // Group exists, leaf does not.
        assert_eq!(e.field_path(&seg(&["input", "bogus"])), None);
        // Top-level name does not exist.
        assert_eq!(e.field_path(&seg(&["nope"])), None);
    }

    #[test]
    fn field_path_descend_through_scalar_is_none() {
        // `requestId` is a scalar; descending into it must fail cleanly,
        // not panic.
        let e = nested_event();
        assert_eq!(e.field_path(&seg(&["requestId", "x"])), None);
    }

    #[test]
    fn field_path_stops_at_group_returns_the_object() {
        // A path that names a group (no leaf) returns the object value.
        let e = nested_event();
        assert!(matches!(
            e.field_path(&seg(&["input"])),
            Some(Value::Object(_))
        ));
    }

    #[test]
    fn field_path_empty_is_none() {
        let e = nested_event();
        assert_eq!(e.field_path(&[]), None);
    }

    // ─── resolve_entity_attr: the shared scope-attribute resolver ───────
    //
    // This is the single source of truth both the provider-arg resolver
    // (`api::resolve_scope_path`) and the temporal env seeder
    // (`eval::seed_scope_env`) delegate to, so the two agree by construction.
    // These cases pin the full semantic contract (supplied-attr-wins,
    // `.id`/`.type` uid projection, nested descent, absent → None) in one place.

    /// An event whose `Drupe::OAuthUser::"alice"` entity carries the given
    /// attributes.
    fn event_with_attrs(attrs: &[(&str, Value)]) -> EventData {
        let mut map = BTreeMap::new();
        for (k, v) in attrs {
            map.insert(k.to_string(), v.clone());
        }
        let mut entities = BTreeMap::new();
        entities.insert(
            "Drupe::OAuthUser::\"alice\"".to_string(),
            EntityRecord {
                attrs: map,
                parents: Vec::new(),
            },
        );
        EventData {
            namespace: vec!["Drupe".to_string(), "Action".to_string()],
            action: "Read".to_string(),
            kind: "request".to_string(),
            logged: BTreeMap::new(),
            request_context: BTreeMap::new(),
            entities,
        }
    }

    fn resolve(e: &EventData, path: &[&str]) -> Option<Value> {
        e.resolve_entity_attr("Drupe::OAuthUser", "alice", &seg(path))
    }

    #[test]
    fn resolve_entity_attr_supplied_single_segment() {
        let e = event_with_attrs(&[("dept", Value::String("eng".to_string()))]);
        assert_eq!(
            resolve(&e, &["dept"]),
            Some(Value::String("eng".to_string()))
        );
    }

    #[test]
    fn resolve_entity_attr_nested_descent() {
        let addr = Value::Object(BTreeMap::from([(
            "city".to_string(),
            Value::String("sea".to_string()),
        )]));
        let e = event_with_attrs(&[("address", addr)]);
        assert_eq!(
            resolve(&e, &["address", "city"]),
            Some(Value::String("sea".to_string()))
        );
    }

    #[test]
    fn resolve_entity_attr_mid_path_scalar_is_none() {
        // Descending into a scalar attribute is unresolvable (not a panic).
        let e = event_with_attrs(&[("dept", Value::String("eng".to_string()))]);
        assert_eq!(resolve(&e, &["dept", "x"]), None);
    }

    #[test]
    fn resolve_entity_attr_id_type_project_the_uid() {
        // With no supplied attributes, `.id` / `.type` fall back to the uid.
        let e = event_with_attrs(&[]);
        assert_eq!(
            resolve(&e, &["id"]),
            Some(Value::String("alice".to_string()))
        );
        assert_eq!(
            resolve(&e, &["type"]),
            Some(Value::String("Drupe::OAuthUser".to_string()))
        );
    }

    #[test]
    fn resolve_entity_attr_supplied_id_wins_over_uid_projection() {
        // A supplied attribute named `id`/`type` is looked up before the uid
        // fallback, so it wins.
        let e = event_with_attrs(&[
            ("id", Value::String("override".to_string())),
            ("type", Value::String("Custom".to_string())),
        ]);
        assert_eq!(
            resolve(&e, &["id"]),
            Some(Value::String("override".to_string()))
        );
        assert_eq!(
            resolve(&e, &["type"]),
            Some(Value::String("Custom".to_string()))
        );
    }

    #[test]
    fn resolve_entity_attr_deeper_id_path_has_no_uid_fallback() {
        // The `.id`/`.type` projection is single-segment only: `id.x` does not
        // fall back to the uid (there's nothing to descend into).
        let e = event_with_attrs(&[]);
        assert_eq!(resolve(&e, &["id", "x"]), None);
    }

    #[test]
    fn resolve_entity_attr_unsupplied_is_none() {
        let e = event_with_attrs(&[("dept", Value::String("eng".to_string()))]);
        assert_eq!(resolve(&e, &["missing"]), None);
    }

    #[test]
    fn resolve_entity_attr_empty_path_is_none() {
        let e = event_with_attrs(&[("dept", Value::String("eng".to_string()))]);
        assert_eq!(resolve(&e, &[]), None);
    }

    #[test]
    fn resolve_entity_attr_null_is_preserved_not_coerced() {
        // A supplied `Null` resolves to `Null` (absent-in-Cedar), never coerced
        // to an empty/default that a policy could match.
        let e = event_with_attrs(&[("dept", Value::Null)]);
        assert_eq!(resolve(&e, &["dept"]), Some(Value::Null));
    }

    // ─── Event::logged_leaves: schema-free wire-form basis ──────────────
    //
    // Covers the five field shapes the SQL wire format must round-trip
    // uniformly: a flat field, a group field, a nested record field, a
    // set-valued field, and a renamed reserved field. `logged_leaves` emits
    // every node (a group/record BOTH whole at its path AND descended), so a
    // consumer can read whatever dotted path a policy references.

    /// The `(dotted.path, value)` pairs `logged_leaves` yields, as a lookup
    /// map keyed by the dotted string — order-independent assertions.
    fn leaves_map(e: &Event) -> std::collections::BTreeMap<String, Value> {
        e.logged_leaves()
            .into_iter()
            .map(|(p, v)| (p.join("."), v.clone()))
            .collect()
    }

    #[test]
    fn logged_leaves_flat_field() {
        // A flat top-level field (a renamed reserved slot uses this shape too):
        // present at its single-segment path.
        let mut logged = BTreeMap::new();
        logged.insert("trace_id".to_string(), Value::String("tr-1".to_string()));
        let ev = Event::from_parts(
            0,
            Scope::default(),
            EventData {
                namespace: vec!["Drupe".to_string(), "Action".to_string()],
                action: "Login".to_string(),
                kind: "request".to_string(),
                logged,
                request_context: BTreeMap::new(),
                entities: BTreeMap::new(),
            },
        );
        let m = leaves_map(&ev);
        assert_eq!(m.get("trace_id"), Some(&Value::String("tr-1".to_string())));
    }

    #[test]
    fn logged_leaves_group_and_nested_and_set_and_renamed_reserved() {
        // One event exercising the remaining four shapes at once:
        //  - group field:            input.user
        //  - nested record field:    input.meta.region  (a record under a group)
        //  - set-valued field:       input.tags         (an Array leaf)
        //  - renamed reserved field: actor              (flat, not caller*)
        let mut meta = BTreeMap::new();
        meta.insert("region".to_string(), Value::String("us-east".to_string()));
        let mut input = BTreeMap::new();
        input.insert("user".to_string(), Value::String("alice".to_string()));
        input.insert("meta".to_string(), Value::Object(meta));
        input.insert(
            "tags".to_string(),
            Value::Array(vec![
                Value::String("a".to_string()),
                Value::String("b".to_string()),
            ]),
        );
        let mut logged = BTreeMap::new();
        logged.insert("input".to_string(), Value::Object(input));
        logged.insert(
            "actor".to_string(),
            Value::Entity {
                ty: "Drupe::OAuthUser".to_string(),
                id: "alice".to_string(),
            },
        );
        let ev = Event::from_parts(
            0,
            Scope::default(),
            EventData {
                namespace: vec!["Drupe".to_string(), "Action".to_string()],
                action: "Login".to_string(),
                kind: "request".to_string(),
                logged,
                request_context: BTreeMap::new(),
                entities: BTreeMap::new(),
            },
        );
        let m = leaves_map(&ev);

        // Group field: the leaf is reachable at its dotted path.
        assert_eq!(
            m.get("input.user"),
            Some(&Value::String("alice".to_string()))
        );
        // Nested record field: leaf AND the intermediate record are both emitted.
        assert_eq!(
            m.get("input.meta.region"),
            Some(&Value::String("us-east".to_string()))
        );
        assert!(
            matches!(m.get("input.meta"), Some(Value::Object(_))),
            "the intermediate record node is emitted whole"
        );
        assert!(
            matches!(m.get("input"), Some(Value::Object(_))),
            "the group node is emitted whole (whole-value matches resolve)"
        );
        // Set-valued field: the Array is a single leaf at its path.
        assert!(
            matches!(m.get("input.tags"), Some(Value::Array(a)) if a.len() == 2),
            "the set-valued field is one leaf"
        );
        // Renamed reserved field: a flat leaf keyed by its own name — no
        // caller* privilege, no positional slot.
        assert!(
            matches!(m.get("actor"), Some(Value::Entity { .. })),
            "a renamed reserved field is an ordinary flat leaf"
        );
    }
}
