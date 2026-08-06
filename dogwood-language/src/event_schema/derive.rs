//! Derivation: bind an event-schema DSL to a concrete Cedar action
//! schema, producing the in-memory event signatures.
//!
//! For each action `A` in the Cedar schema and each [`EventDecl`] in the
//! DSL, this produces one derived event keyed by (qualified action path,
//! kind), whose fields come from evaluating the declaration's selectors
//! against `A`:
//!   * `...inputs(A)` / `...outputs(A)` splice the field set of the
//!     action's `context.input` / `context.output` record (resolving a
//!     common-type reference to its record),
//!   * `principalType(A)` / `resourceType(A)` yield the action's declared
//!     `appliesTo` entity-type *set* (kept whole — no collapse),
//!   * a concrete type is taken verbatim.
//!
//! The result is a Dogwood-owned structure (not a Cedar schema): events
//! are a temporal-layer notion, and the derived schema feeds matching /
//! validation / the event→action map, none of which is Cedar.
//!
//! This pass reads the action schema but consults nothing else; it is the
//! only place the symbolic DSL selectors meet a real schema.

use std::collections::BTreeMap;

use cedar_policy_core::extensions::Extensions;
use cedar_policy_core::validator::RawName;
use cedar_policy_core::validator::json_schema::{
    ActionType, Fragment, RecordType, Type, TypeVariant,
};
use smol_str::SmolStr;

use super::ast::{EventSchema, FieldSpec, PinRoot, Selector, TypeExpr};
use crate::extension::temporal::ast::{Interval, TimeUnit};

/// The default maximum look-back window a temporal `within` clause may use
/// when the event schema declares no explicit `max_window`: 24 hours.
pub const DEFAULT_MAX_WINDOW: Interval = Interval {
    amount: 24,
    unit: TimeUnit::Hours,
};

/// The derived event signatures: one entry per (action, kind) pair the
/// DSL produces against the action schema.
#[derive(Debug, Clone)]
pub struct DerivedEventSchema {
    pub events: Vec<DerivedEvent>,
    /// The maximum temporal look-back window any policy `within` clause may
    /// use, enforced by the temporal validator. Resolved at derive time from
    /// the event schema's `max_window` directive, defaulting to
    /// [`DEFAULT_MAX_WINDOW`] when the schema declared none.
    pub max_window: Interval,
}

/// One derived event signature.
#[derive(Debug, Clone)]
pub struct DerivedEvent {
    /// Qualified action path including the action entity-type segment,
    /// e.g. `["Drupe", "Action"]` — what a predicate's namespace must
    /// equal to match, and what the event→action map joins back.
    pub namespace: Vec<String>,
    /// The action id, e.g. `Login`.
    pub action: String,
    /// The event kind, e.g. `request` / `response`.
    pub kind: String,
    /// Whether ingesting an event of this kind runs authorization. The
    /// engine's decision trigger consults the schema's decision kinds.
    pub decision: bool,
    /// The event's field tree: name → node, where a node is either a leaf
    /// (a typed field) or a group (a nested record). Spliced `...inputs(A)`
    /// / `...outputs(A)` fields nest under the groups `input` / `output`;
    /// named fields (`callerPrincipal: …`) are top-level leaves. Field
    /// identity is by dotted path (see [`DerivedEvent::lookup_path`]).
    pub fields: BTreeMap<String, DerivedFieldNode>,
    /// Pinned fields: each declares a leaf whose value the pin-injection
    /// pass ([`crate::event_schema::pin::inject_pins`]) conjoins onto every
    /// predicate for this event (a correlation against the decision request).
    /// Empty when the event schema declares no pins.
    pub pins: Vec<Pin>,
}

/// A pinned field on a derived event: the leaf's full dotted path and the
/// request-side value it is forced to match.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Pin {
    /// The pinned leaf's full dotted path (e.g. `["callerPrincipal"]`,
    /// `["__drupe", "session_id"]`).
    pub field_path: Vec<String>,
    /// The path segments the field must match. For a [`PinRoot::Scope`] pin the
    /// head is the `principal` / `resource` root; for a [`PinRoot::Context`] pin
    /// it is the `context.<...>` path without the leading `context`.
    pub context_path: Vec<String>,
    /// Which request root `context_path` is anchored to — selects the temporal
    /// term the pin lowers to (`ScopeField` vs `ContextField`).
    pub root: PinRoot,
}

/// A node in a derived event's field tree: a typed leaf or a nested group.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum DerivedFieldNode {
    /// A declared field with a concrete type — the addressable leaf a
    /// predicate matches on.
    Leaf(FieldType),
    /// A nested record: the `input` / `output` groups, and (in future)
    /// author-nested named fields. Its members are addressed by extending
    /// the path (`input.user`).
    Group(BTreeMap<String, DerivedFieldNode>),
}

/// The outcome of resolving a dotted path against an event's field tree.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum PathLookup {
    /// The path names a declared field (a leaf) — a valid predicate field.
    Leaf,
    /// The path names a field *group*, not a field (e.g. `input` alone).
    /// A predicate must address a leaf inside it (`input.user`).
    Group,
    /// No such path in the event's field tree.
    Absent,
}

/// The type of a derived field.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum FieldType {
    /// A concrete Cedar type, rendered as text (e.g. `String`, `Long`,
    /// `Set < String >`). Spliced input/output fields and concrete-typed
    /// injected fields use this.
    Cedar(String),
    /// A set of entity type names — `principalType(A)` / `resourceType(A)`.
    /// Kept as the full declared set; no union or supertype is formed
    /// (typed validation later enumerates it).
    EntityTypes(Vec<String>),
}

impl DerivedEvent {
    /// Resolve a dotted field path against this event's field tree,
    /// descending into [`DerivedFieldNode::Group`] at each non-final
    /// segment. A single-segment path names a top-level entry.
    pub fn lookup_path(&self, path: &[String]) -> PathLookup {
        let Some((head, rest)) = path.split_first() else {
            return PathLookup::Absent;
        };
        let mut node = match self.fields.get(head) {
            Some(n) => n,
            None => return PathLookup::Absent,
        };
        for seg in rest {
            match node {
                DerivedFieldNode::Group(members) => match members.get(seg) {
                    Some(n) => node = n,
                    None => return PathLookup::Absent,
                },
                DerivedFieldNode::Leaf(_) => return PathLookup::Absent,
            }
        }
        match node {
            DerivedFieldNode::Leaf(_) => PathLookup::Leaf,
            DerivedFieldNode::Group(_) => PathLookup::Group,
        }
    }

    /// The declared top-level names and group-qualified paths, for error
    /// messages. E.g. `["requestId", "input.user", "output.result"]`.
    pub fn declared_paths(&self) -> Vec<String> {
        let mut out = Vec::new();
        collect_paths(&self.fields, "", &mut out);
        out.sort_unstable();
        out
    }

    /// Every declared **leaf** field as `(dotted path segments, type)`,
    /// descending groups. The typed analog of [`declared_paths`](DerivedEvent::declared_paths):
    /// `input.meta.region` → `(["input", "meta", "region"], Cedar("String"))`.
    /// Groups are not emitted (a predicate matches only leaves). Sorted by the
    /// **joined dotted path** — the exact key [`declared_paths`](DerivedEvent::declared_paths)
    /// sorts by — so the two agree leaf-for-leaf in order, not just as sets.
    /// Backs the public `LoweredPolicySet::event_signatures` projection.
    pub fn leaf_fields(&self) -> Vec<(Vec<String>, FieldType)> {
        let mut out = Vec::new();
        collect_typed_leaves(&self.fields, &[], &mut out);
        // Sort by the joined dotted string (not segment-wise), matching
        // `declared_paths`'s `sort_unstable` on the joined form — a leaf name
        // containing a byte below `.` would otherwise order differently.
        out.sort_by_key(|(path, _)| path.join("."));
        out
    }
}

/// Collect every scalar-leaf field under `map` as `(path segments, type)`,
/// extending `prefix` at each group. The typed counterpart of
/// [`collect_paths`].
fn collect_typed_leaves(
    map: &BTreeMap<String, DerivedFieldNode>,
    prefix: &[String],
    out: &mut Vec<(Vec<String>, FieldType)>,
) {
    for (name, node) in map {
        let mut path = prefix.to_vec();
        path.push(name.clone());
        match node {
            DerivedFieldNode::Leaf(ty) => out.push((path, ty.clone())),
            DerivedFieldNode::Group(members) => collect_typed_leaves(members, &path, out),
        }
    }
}

fn collect_paths(map: &BTreeMap<String, DerivedFieldNode>, prefix: &str, out: &mut Vec<String>) {
    for (name, node) in map {
        let path = if prefix.is_empty() {
            name.clone()
        } else {
            format!("{prefix}.{name}")
        };
        match node {
            DerivedFieldNode::Leaf(_) => out.push(path),
            DerivedFieldNode::Group(members) => collect_paths(members, &path, out),
        }
    }
}

impl DerivedEventSchema {
    /// Look up a derived event by (namespace, action, kind).
    pub fn get(&self, namespace: &[String], action: &str, kind: &str) -> Option<&DerivedEvent> {
        self.events
            .iter()
            .find(|e| e.action == action && e.kind == kind && e.namespace == namespace)
    }

    /// The maximum temporal look-back window any policy `within` clause may
    /// use — the schema's `max_window` directive, or [`DEFAULT_MAX_WINDOW`].
    pub fn max_window(&self) -> Interval {
        self.max_window
    }

    /// The set of kinds marked `decision`. Consumed by `parse` to populate
    /// the bundle's decision-kind set, which gates `process`.
    pub fn decision_kinds(&self) -> std::collections::BTreeSet<&str> {
        self.events
            .iter()
            .filter(|e| e.decision)
            .map(|e| e.kind.as_str())
            .collect()
    }
}

/// Derive the event signatures from `schema` (the DSL) against
/// `action_schema_src` (a `.cedarschema`).
pub fn derive(schema: &EventSchema, action_schema_src: &str) -> Result<DerivedEventSchema, String> {
    let (fragment, _warnings) =
        Fragment::<RawName>::from_cedarschema_str(action_schema_src, Extensions::all_available())
            .map_err(|e| format!("parse action schema: {e}"))?;

    let mut events = Vec::new();
    for (ns_key, ns_def) in &fragment.0 {
        // The namespace path the action entities live under, e.g.
        // `["Drupe"]`; the action entity-type segment (`Action`) is
        // appended below.
        let ns_path: Vec<String> = match ns_key {
            Some(name) => name.to_string().split("::").map(str::to_string).collect(),
            None => Vec::new(),
        };
        for (action_id, action) in &ns_def.actions {
            for decl in &schema.decls {
                let event = derive_one(
                    decl,
                    &ns_path,
                    action_id.as_str(),
                    action,
                    ns_key,
                    &fragment,
                )?;
                events.push(event);
            }
        }
    }
    Ok(DerivedEventSchema {
        events,
        // Resolve the max-window cap: the schema's directive, or the 24h default.
        max_window: schema.max_window.unwrap_or(DEFAULT_MAX_WINDOW),
    })
}

#[allow(clippy::too_many_arguments)]
fn derive_one(
    decl: &super::ast::EventDecl,
    ns_path: &[String],
    action_id: &str,
    action: &ActionType<RawName>,
    home_ns: &Option<cedar_policy_core::ast::Name>,
    fragment: &Fragment<RawName>,
) -> Result<DerivedEvent, String> {
    // The full action-entity path: namespace segments + the `Action`
    // entity-type segment Cedar names actions under.
    let mut namespace = ns_path.to_vec();
    namespace.push("Action".to_string());

    let mut pins: Vec<Pin> = Vec::new();
    let fields = derive_fields(
        &decl.fields,
        &[],
        action_id,
        &decl.kind,
        action,
        home_ns,
        fragment,
        &mut pins,
    )?;

    Ok(DerivedEvent {
        namespace,
        action: action_id.to_string(),
        kind: decl.kind.clone(),
        decision: decl.decision,
        fields,
        pins,
    })
}

/// Build a field tree from a list of field specs. A spread selector nests
/// its fields under a group (`input` / `output`); a named field is a leaf,
/// unless its type is a record — then it is a nested group whose members
/// are derived by recursing. Shared by the event body and any nested
/// record type.
#[allow(clippy::too_many_arguments)]
fn derive_fields(
    specs: &[FieldSpec],
    prefix: &[String],
    action_id: &str,
    kind: &str,
    action: &ActionType<RawName>,
    home_ns: &Option<cedar_policy_core::ast::Name>,
    fragment: &Fragment<RawName>,
    pins: &mut Vec<Pin>,
) -> Result<BTreeMap<String, DerivedFieldNode>, String> {
    let mut fields: BTreeMap<String, DerivedFieldNode> = BTreeMap::new();
    // Which top-level names came from a spread (`input`/`output`), so a
    // later collision can name the culprit precisely. A name is defined at
    // most once at each level — see the collision checks below.
    let mut spread_names: std::collections::BTreeSet<String> = std::collections::BTreeSet::new();

    for spec in specs {
        match spec {
            FieldSpec::Spread { selector, .. } => {
                let (group, members) = match selector {
                    Selector::Inputs => (
                        "input",
                        context_subrecord(action, home_ns, fragment, "input")?,
                    ),
                    Selector::Outputs => (
                        "output",
                        context_subrecord(action, home_ns, fragment, "output")?,
                    ),
                    Selector::PrincipalType | Selector::ResourceType => {
                        return Err(format!(
                            "selector `{}` cannot be spread (it yields entity types, not a \
                             field record); use it as a field type instead",
                            selector.as_str()
                        ));
                    }
                };
                // The spread's group name must not already be taken — by a
                // named field (either order) or a duplicate spread. A spread
                // group and a named field may never share a top-level name,
                // regardless of declaration order.
                if fields.contains_key(group) {
                    return Err(format!(
                        "the `{group}` field group produced by `...{}(A)` (on \
                         `{action_id}::{kind}`) collides with another field named `{group}`; a \
                         spread group and a named field may not share a name",
                        selector.as_str()
                    ));
                }
                // `context_subrecord` already returns the members as a field
                // tree — a record-typed member (`meta: Meta`) is a nested
                // [`DerivedFieldNode::Group`], so `input.meta.region` is a
                // reachable leaf, matching how author-declared nested fields
                // (`meta: { … }`) nest via `TypeExpr::Record` below.
                fields.insert(group.to_string(), DerivedFieldNode::Group(members));
                spread_names.insert(group.to_string());
            }
            FieldSpec::Named { name, ty, pin, .. } => {
                // This field's full dotted path (prefix + name).
                let mut field_path = prefix.to_vec();
                field_path.push(name.clone());

                let node = match ty {
                    TypeExpr::Selector(Selector::PrincipalType) => DerivedFieldNode::Leaf(
                        FieldType::EntityTypes(entity_type_names(&action_principal_types(action)?)),
                    ),
                    TypeExpr::Selector(Selector::ResourceType) => DerivedFieldNode::Leaf(
                        FieldType::EntityTypes(entity_type_names(&action_resource_types(action)?)),
                    ),
                    TypeExpr::Selector(other) => {
                        return Err(format!(
                            "selector `{}` cannot be used as a field type (it yields a field \
                             record, not a type); spread it with `...` instead",
                            other.as_str()
                        ));
                    }
                    TypeExpr::Concrete(path) => {
                        DerivedFieldNode::Leaf(FieldType::Cedar(path.join("::")))
                    }
                    // A record-typed named field nests: recurse to derive
                    // its members into a group (author-chosen hierarchy),
                    // extending the path prefix so a nested pin gets its
                    // full dotted path.
                    TypeExpr::Record(inner) => DerivedFieldNode::Group(derive_fields(
                        inner,
                        &field_path,
                        action_id,
                        kind,
                        action,
                        home_ns,
                        fragment,
                        pins,
                    )?),
                };

                // Collect the pin, if any. The parser guarantees a pin sits
                // only on a leaf (never a record), so `field_path` names a
                // leaf here.
                if let Some(pv) = pin {
                    pins.push(Pin {
                        field_path: field_path.clone(),
                        context_path: pv.context_path.clone(),
                        root: pv.root,
                    });
                }
                // A named field must not collide with an already-defined
                // name. If that name came from a spread it is a shadowed
                // spread group (a record OR a leaf shadow — both rejected);
                // otherwise it is a duplicate field. Either way names are
                // unique at a level.
                if fields.contains_key(name) {
                    if spread_names.contains(name) {
                        return Err(format!(
                            "event-schema field `{name}` (injected on `{action_id}::{kind}`) \
                             collides with the `{name}` field group produced by a spread; a named \
                             field may not shadow a spread group"
                        ));
                    }
                    return Err(format!(
                        "event-schema field `{name}` is defined more than once on \
                         `{action_id}::{kind}`; field names must be unique at each level"
                    ));
                }
                fields.insert(name.clone(), node);
            }
        }
    }
    Ok(fields)
}

/// The principal entity types an action applies to (rendered names).
fn action_principal_types(action: &ActionType<RawName>) -> Result<Vec<RawName>, String> {
    Ok(action
        .applies_to
        .as_ref()
        .map(|a| a.principal_types.clone())
        .unwrap_or_default())
}

fn action_resource_types(action: &ActionType<RawName>) -> Result<Vec<RawName>, String> {
    Ok(action
        .applies_to
        .as_ref()
        .map(|a| a.resource_types.clone())
        .unwrap_or_default())
}

fn entity_type_names(types: &[RawName]) -> Vec<String> {
    types.iter().map(|n| n.to_string()).collect()
}

/// Resolve the field **tree** of the action's `context.<attr>` (e.g.
/// `context.input`) into a `name -> DerivedFieldNode` map, descending
/// record-typed members recursively. A record-typed input member
/// (`input: ReadInput` where `ReadInput = { meta: Meta }`, or an inline
/// `input: { meta: { region } }`) becomes a nested
/// [`DerivedFieldNode::Group`], so `input.meta.region` is a reachable leaf —
/// not a single opaque `input.meta` leaf. This matches how author-declared
/// nested `.dwschema` fields (`meta: { … }`) nest via `TypeExpr::Record`, and
/// how the temporal validator's `context.input.meta.region` path resolution
/// (which reads Cedar's typed context directly) already descends. Returns an
/// empty map if the action has no context, no such attribute, or the
/// attribute resolves to an empty / non-record type.
///
/// `home_ns` is the namespace the action lives in — where bare (unqualified)
/// common-type references resolve; qualified references (`Shared::Addr`)
/// resolve in their named namespace, looked up in `fragment`.
fn context_subrecord(
    action: &ActionType<RawName>,
    home_ns: &Option<cedar_policy_core::ast::Name>,
    fragment: &Fragment<RawName>,
    attr: &str,
) -> Result<BTreeMap<String, DerivedFieldNode>, String> {
    let Some(applies_to) = action.applies_to.as_ref() else {
        return Ok(BTreeMap::new());
    };
    // The context itself is a record (or a common-type ref to one). Its
    // members resolve in the namespace the context record was declared in.
    let Some((ctx_record, ctx_ns)) =
        resolve_to_record(&applies_to.context.0, home_ns, fragment, 0)?
    else {
        return Ok(BTreeMap::new());
    };
    // Find the `input` / `output` attribute within the context.
    let Some(sub_attr) = ctx_record.attributes.get(&SmolStr::from(attr)) else {
        return Ok(BTreeMap::new());
    };
    // Its type is the sub-record (inline or a common-type ref); convert it to
    // a node, recursing into nested records. A non-record `input`/`output`
    // type (unusual) yields no fields. `nodes` is a shared budget across the
    // whole sub-tree (see [`MAX_RECORD_NODES`]).
    let mut nodes = 0usize;
    match type_to_node(&sub_attr.ty, &ctx_ns, fragment, 0, &mut nodes)? {
        DerivedFieldNode::Group(members) => Ok(members),
        DerivedFieldNode::Leaf(_) => Ok(BTreeMap::new()),
    }
}

/// Maximum record / common-type nesting **depth** [`type_to_node`] and
/// [`resolve_to_record`] descend while building a derived event's field tree.
///
/// A schema nested deeper than this is almost certainly **cyclic** — a member
/// cycle (`type A = { x: A }`), an alias cycle (`type A = B; type B = A`), or a
/// mutual cycle (`type A = { b: B }; type B = { a: A }`). Cedar rejects such
/// schemas during typechecking, but derivation runs *before* that (see
/// [`crate::api`]'s `lower`, which derives the raw action-schema source), so
/// without a bound a cycle recurses until the stack overflows and **aborts the
/// process** (a stack overflow is uncatchable). This cap converts that into a
/// clean schema error. No legitimate schema nests anywhere near this deep.
const MAX_RECORD_DEPTH: usize = 64;

/// Maximum total **node count** in a single input/output field sub-tree.
///
/// The depth cap alone does not bound width: an acyclic "diamond" schema
/// (`type Tk = { a: T(k-1), b: T(k-1) }`) is only `k` deep — well under
/// [`MAX_RECORD_DEPTH`] — yet materializes `~2^k` distinct leaf *paths*
/// (`input.a.a…`, `input.a.b…`, …), since the derived tree is owned records,
/// not a shared DAG. Building it would exhaust memory before Cedar's typecheck
/// (which runs after derivation) could reject the schema. A shared node budget,
/// threaded through the whole recursion, caps the materialized tree regardless
/// of shape (deep, wide, or exponential fanout) and turns the blow-up into a
/// clean schema error. Set far above any legitimate event body (real schemas
/// have tens of leaves, not thousands).
const MAX_RECORD_NODES: usize = 10_000;

/// Convert a Cedar member [`Type`] into a [`DerivedFieldNode`]: a record type
/// (inline or a common-type reference to one) becomes a
/// [`DerivedFieldNode::Group`] whose members are converted recursively; any
/// non-record type is a [`DerivedFieldNode::Leaf`] carrying its rendered text.
/// `home_ns` is the namespace this type's common-type references resolve in;
/// as [`resolve_to_record`] chains through a cross-namespace common type it
/// reports the namespace the record was ultimately declared in, so a nested
/// member reference resolves against the right namespace.
///
/// Two bounds guard against pathological schemas that derivation sees before
/// Cedar's typecheck can reject them: `depth` bounds nesting depth against
/// cyclic types ([`MAX_RECORD_DEPTH`]), and `nodes` — a budget shared across
/// the whole sub-tree, incremented once per node produced — bounds the total
/// materialized node count against acyclic exponential fanout
/// ([`MAX_RECORD_NODES`]).
fn type_to_node(
    ty: &Type<RawName>,
    home_ns: &Option<cedar_policy_core::ast::Name>,
    fragment: &Fragment<RawName>,
    depth: usize,
    nodes: &mut usize,
) -> Result<DerivedFieldNode, String> {
    if depth > MAX_RECORD_DEPTH {
        return Err(format!(
            "event-schema field record nests deeper than {MAX_RECORD_DEPTH} levels; \
             the action schema likely has a cyclic type definition"
        ));
    }
    *nodes += 1;
    if *nodes > MAX_RECORD_NODES {
        return Err(format!(
            "event-schema field record expands to more than {MAX_RECORD_NODES} fields; \
             the action schema likely has a type whose nesting fans out exponentially"
        ));
    }
    match resolve_to_record(ty, home_ns, fragment, depth)? {
        Some((record, rec_ns)) => {
            let mut members: BTreeMap<String, DerivedFieldNode> = BTreeMap::new();
            for (name, attr) in record.attributes.iter() {
                members.insert(
                    name.to_string(),
                    type_to_node(&attr.ty, &rec_ns, fragment, depth + 1, nodes)?,
                );
            }
            Ok(DerivedFieldNode::Group(members))
        }
        None => Ok(DerivedFieldNode::Leaf(FieldType::Cedar(render_type(ty)))),
    }
}

/// A resolved record together with the namespace its own member references
/// resolve in — what [`resolve_to_record`] returns. The namespace is threaded
/// out so a cross-namespace common-type chain moves the resolution namespace
/// with it (a member of `Shared::Meta` resolves in `Shared`, not the action's
/// home namespace).
type ResolvedRecord<'a> = (
    &'a RecordType<RawName>,
    Option<cedar_policy_core::ast::Name>,
);

/// Resolve a [`Type`] to a record **and the namespace it was declared in**:
/// either it is an inline record (declared in `home_ns`), or it is a
/// common-type reference that names a record. A bare reference
/// (`LoginInput`) resolves in `home_ns`; a qualified reference
/// (`Shared::Addr`) resolves in the named namespace — Cedar stores the
/// reference fully-qualified iff it is cross-namespace, and keys each
/// namespace's `common_types` by the bare id (verified against
/// cedar-policy 4.11; see the cross-namespace test). The returned namespace
/// is where the resolved record's own member references resolve, which is why
/// it is threaded back out (a cross-namespace chain moves the resolution
/// namespace with it).
///
/// `depth` bounds the common-type-alias chain against a cyclic alias
/// (`type A = B; type B = A`); it is incremented at each alias hop and capped
/// at [`MAX_RECORD_DEPTH`], the same bound [`type_to_node`] applies to member
/// nesting.
///
/// Returns:
/// * `Ok(Some((record, ns)))` — the type is (or aliases to) a record.
/// * `Ok(None)` — the type is **not** a record: a primitive (`String`), a
///   set, or a reference to a declared **entity type** (all of which are leaf
///   fields, not descendable records).
/// * `Err(_)` — a schema error we surface rather than silently treat as empty:
///   a *qualified* reference resolving to neither a common type nor an entity
///   type (a dangling cross-namespace reference), or a cyclic alias chain.
fn resolve_to_record<'a>(
    ty: &'a Type<RawName>,
    home_ns: &Option<cedar_policy_core::ast::Name>,
    fragment: &'a Fragment<RawName>,
    depth: usize,
) -> Result<Option<ResolvedRecord<'a>>, String> {
    if depth > MAX_RECORD_DEPTH {
        return Err(format!(
            "event-schema field type aliases through more than {MAX_RECORD_DEPTH} common \
             types; the action schema likely has a cyclic type definition"
        ));
    }
    // A common-type reference appears in either of two shapes: the ambiguous
    // `EntityOrCommon` (a bare name that may be an entity OR a common type) or
    // the explicit `CommonTypeRef` (a name Cedar has already classified as a
    // common type). In the raw action schemas `derive` runs on (before any
    // `schema_augment` inlining), cedar-policy 4.11 emits `CommonTypeRef` only
    // at the whole-**context** position (`context: ReadCtx`); record members and
    // common-type alias hops are always `EntityOrCommon`. Both shapes must
    // resolve identically — matching only `EntityOrCommon` silently dropped a
    // `CommonTypeRef` context to a non-record, so the derived event lost ALL of
    // the referenced record's fields. Mirrors
    // `cedarify::schema_augment::context_reference_name`.
    let ref_name = match ty {
        Type::CommonTypeRef { type_name, .. } => Some(type_name.to_string()),
        Type::Type {
            ty: TypeVariant::EntityOrCommon { type_name },
            ..
        } => Some(type_name.to_string()),
        _ => None,
    };
    match ty {
        Type::Type {
            ty: TypeVariant::Record(record),
            ..
        } => Ok(Some((record, home_ns.clone()))),
        _ if ref_name.is_some() => {
            let full = ref_name.expect("checked is_some");
            // A reference into Cedar's reserved `__cedar` namespace names a
            // builtin — a primitive (`__cedar::String`, `__cedar::Long`,
            // `__cedar::Bool`) or an extension type (`__cedar::decimal`,
            // `__cedar::ipaddr`, …). `SchemaFragment::to_cedarschema()` renders
            // primitives and builtin extension types with this fully-qualified
            // reserved spelling, so a round-tripped / legacy Cedar schema reaches
            // us with it. None of these are records: they are leaf fields, so we
            // must treat them as "not a record" — exactly like a bare `String`.
            // We return here BEFORE `qualify`, which rightly refuses to parse
            // `__cedar` as a user namespace (it is reserved).
            if full
                .split("::")
                .next()
                .is_some_and(|first| first == "__cedar")
            {
                return Ok(None);
            }
            // Split a qualified reference into (namespace, basename); a bare
            // reference resolves in the action's home namespace.
            let (target_ns, basename) = match full.rsplit_once("::") {
                Some((ns, base)) => (qualify(ns)?, base.to_string()),
                None => (home_ns.clone(), full.clone()),
            };
            let Some(ns_def) = fragment.0.get(&target_ns) else {
                // The reference names a namespace not in the schema. A
                // primitive/entity reference (`String`, an entity type)
                // legitimately has no common-type entry — treat as "not a
                // record" rather than an error.
                return Ok(None);
            };
            match ns_def
                .common_types
                .iter()
                .find(|(id, _)| id.as_ref().to_string() == basename)
            {
                // Resolve the referenced common type's own type — recursing
                // in *its* namespace, so a common type defined in terms of
                // another common type chains correctly. The alias hop counts
                // against the depth cap so a cyclic alias errors cleanly.
                Some((_, ct)) => resolve_to_record(&ct.ty, &target_ns, fragment, depth + 1),
                // Not a declared common type in the target namespace. A
                // reference (bare or qualified) that instead names a declared
                // *entity type* is a legitimate non-record leaf — e.g. an
                // input field typed by an enum entity (`role:
                // Ns::Grant_Input_role`). Only a *qualified* reference that
                // names neither a common type nor an entity type is a dangling
                // reference we surface; a bare unknown is a primitive
                // (`String`) → not a record.
                None if ns_def
                    .entity_types
                    .keys()
                    .any(|id| id.to_string() == basename) =>
                {
                    Ok(None)
                }
                None if full.contains("::") => Err(format!(
                    "type reference `{full}` does not resolve to a declared common type"
                )),
                None => Ok(None),
            }
        }
        _ => Ok(None),
    }
}

/// Parse a namespace string into the `Option<Name>` key Cedar uses
/// (an empty string is the unnamespaced `None` key).
fn qualify(ns: &str) -> Result<Option<cedar_policy_core::ast::Name>, String> {
    use cedar_policy_core::FromNormalizedStr;
    if ns.is_empty() {
        Ok(None)
    } else {
        cedar_policy_core::ast::Name::from_normalized_str(ns)
            .map(Some)
            .map_err(|e| format!("bad namespace `{ns}` in type reference: {e}"))
    }
}

/// Render a [`Type`] to its `.cedarschema` text form (used for field
/// types we keep as strings; names-only validation ignores it, typed
/// validation will parse it later).
fn render_type(ty: &Type<RawName>) -> String {
    ty.to_string()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::event_schema::parse::parse_event_schema;

    const RR_SCHEMA: &str = r#"
        decision event <A>::request {
            ...inputs(A),
            callerPrincipal: principalType(A),
            callerResource:  resourceType(A),
            requestId:       String,
        }
        event <A>::response {
            ...inputs(A),
            ...outputs(A),
            callerPrincipal: principalType(A),
            callerResource:  resourceType(A),
            requestId:       String,
        }
    "#;

    // A small action schema with real input/output records, mirroring the
    // corpus shape (common-type-referenced `input`/`output`).
    const ACTION_SCHEMA: &str = r#"
        namespace Drupe {
            entity OAuthUser = { id: String };
            entity IamEntity = { id: String };
            entity Gateway;
            type LoginInput = { server: String, user: String };
            type LoginOutput = { result: Bool };
            action "Login" appliesTo {
                principal: [OAuthUser, IamEntity],
                resource: [Gateway],
                context: { input: LoginInput, output?: LoginOutput }
            };
        }
    "#;

    #[test]
    fn context_declared_as_common_type_ref_resolves_inputs() {
        // An action whose `context` is a common-type REFERENCE
        // (`context: ReadCtx`), not an inline record. Cedar represents this as a
        // `Type::CommonTypeRef` (distinct from the ambiguous `EntityOrCommon`),
        // so the spread `...inputs(A)` must resolve the ref to reach `input`.
        // Regression: before handling `CommonTypeRef`, `resolve_to_record`
        // dropped it to a non-record and the derived event carried NO input
        // fields (only the reserved ones) — silently wrong for any policy whose
        // decision action uses a common-type-ref context.
        let schema = r#"
            namespace Drupe {
                entity OAuthUser;
                entity Gateway;
                type LoginInput = { user: String };
                type ReadCtx = { input: { document: String, user: String } };
                action "Login" appliesTo { principal: [OAuthUser], resource: [Gateway], context: { input: LoginInput } };
                action "Read" appliesTo { principal: [OAuthUser], resource: [Gateway], context: ReadCtx };
            }
        "#;
        let d = derive_rr(schema);
        let ns = vec!["Drupe".to_string(), "Action".to_string()];
        let read = d.get(&ns, "Read", "request").expect("Read::request");
        assert_leaf(read, &["input", "user"]);
        assert_leaf(read, &["input", "document"]);
    }

    #[test]
    fn context_common_type_ref_chains_cross_namespace() {
        // The chained + cross-namespace form (corpus 5009): `context: Shared::Ctx`
        // where `Shared::Ctx = Inner` and `Inner = { input: {...} }`, both in the
        // `Shared` namespace. The ref must resolve in `Shared` and chain through.
        let schema = r#"
            namespace Shared {
                type Ctx = Inner;
                type Inner = { input: { document: String, user: String } };
            }
            namespace Drupe {
                entity OAuthUser;
                entity Gateway;
                type LoginInput = { user: String };
                action "Login" appliesTo { principal: [OAuthUser], resource: [Gateway], context: { input: LoginInput } };
                action "Read" appliesTo { principal: [OAuthUser], resource: [Gateway], context: Shared::Ctx };
            }
        "#;
        let d = derive_rr(schema);
        let ns = vec!["Drupe".to_string(), "Action".to_string()];
        let read = d.get(&ns, "Read", "request").expect("Read::request");
        assert_leaf(read, &["input", "user"]);
        assert_leaf(read, &["input", "document"]);
    }

    #[test]
    fn common_type_ref_context_splices_output_on_resolution() {
        // A common-type-ref context whose record has BOTH input and output.
        // The `response` event splices `...outputs(A)` through the same
        // `CommonTypeRef` resolution — the `output` sub-record must resolve too,
        // not just `input` (the other ctxref tests assert only `input.*`).
        let schema = r#"
            namespace Drupe {
                entity OAuthUser;
                entity Gateway;
                type ReviewCtx = { input: { user: String }, output: { verdict: String } };
                action "Review" appliesTo { principal: [OAuthUser], resource: [Gateway], context: ReviewCtx };
            }
        "#;
        let d = derive_rr(schema);
        let ns = vec!["Drupe".to_string(), "Action".to_string()];
        let res = d.get(&ns, "Review", "response").expect("Review::response");
        assert_leaf(res, &["input", "user"]);
        assert_leaf(res, &["output", "verdict"]);
    }

    #[test]
    fn common_type_ref_context_deep_nested_member() {
        // A common-type-ref context whose `input` nests a record two deep — the
        // new context arm composes with member recursion (the other ctxref tests
        // only reach depth-2 `input.user`).
        let schema = r#"
            namespace Drupe {
                entity OAuthUser;
                entity Gateway;
                type ReadCtx = { input: { meta: { region: String } } };
                action "Read" appliesTo { principal: [OAuthUser], resource: [Gateway], context: ReadCtx };
            }
        "#;
        let d = derive_rr(schema);
        let ns = vec!["Drupe".to_string(), "Action".to_string()];
        let read = d.get(&ns, "Read", "request").expect("Read::request");
        assert_leaf(read, &["input", "meta", "region"]);
    }

    #[test]
    fn repro_cedar_builtin_namespace_type_ref() {
        // Legacy/round-tripped Cedar schema: `to_cedarschema()` renders
        // primitives with their fully-qualified reserved spelling
        // (`__cedar::String`). derive() must not reject it.
        let schema = r#"
            namespace Drupe {
                entity OAuthUser;
                entity Gateway;
                type ReadCtx = { input: { user: __cedar::String } };
                action "Read" appliesTo { principal: [OAuthUser], resource: [Gateway], context: ReadCtx };
            }
        "#;
        let d = derive_rr(schema);
        let ns = vec!["Drupe".to_string(), "Action".to_string()];
        let read = d.get(&ns, "Read", "request").expect("Read::request");
        assert_leaf(read, &["input", "user"]);
    }

    #[test]
    fn repro_cedar_builtin_set_and_ext_type_refs() {
        // `to_cedarschema()` also renders sets and builtin extension types with
        // the reserved spelling: `__cedar::Set<__cedar::String>`,
        // `__cedar::ipaddr`, `__cedar::decimal`. None are descendable records;
        // each must land as a leaf, not error on the reserved namespace.
        let schema = r#"
            namespace Drupe {
                entity OAuthUser;
                entity Gateway;
                type ReadCtx = { input: {
                    tags: Set<__cedar::String>,
                    ip:   __cedar::ipaddr,
                    amt:  __cedar::decimal,
                } };
                action "Read" appliesTo { principal: [OAuthUser], resource: [Gateway], context: ReadCtx };
            }
        "#;
        let d = derive_rr(schema);
        let ns = vec!["Drupe".to_string(), "Action".to_string()];
        let read = d.get(&ns, "Read", "request").expect("Read::request");
        assert_leaf(read, &["input", "tags"]);
        assert_leaf(read, &["input", "ip"]);
        assert_leaf(read, &["input", "amt"]);
    }

    #[test]
    fn repro_cedar_builtin_set_of_records_stays_leaf() {
        // A set whose element is a RECORD. In Dogwood's dotted-path field model
        // a set is always a leaf (you cannot address `tags.<field>` through a
        // set), so we must NOT descend into the element regardless of what it
        // holds — matching the pre-existing treatment of a bare `Set<...>`.
        let schema = r#"
            namespace Drupe {
                entity OAuthUser;
                entity Gateway;
                type ReadCtx = { input: { rows: Set<{ user: String }> } };
                action "Read" appliesTo { principal: [OAuthUser], resource: [Gateway], context: ReadCtx };
            }
        "#;
        let d = derive_rr(schema);
        let ns = vec!["Drupe".to_string(), "Action".to_string()];
        let read = d.get(&ns, "Read", "request").expect("Read::request");
        assert_leaf(read, &["input", "rows"]);
        // The element's `user` field is NOT a reachable path — a set is a leaf.
        assert_ne!(
            read.lookup_path(&path(&["input", "rows", "user"])),
            PathLookup::Leaf
        );
    }

    #[test]
    fn cyclic_common_type_ref_context_errors_cleanly() {
        // A cycle reached via the CONTEXT position (`context: A; A = B; B = A`)
        // — the new `CommonTypeRef` entry point must NOT bypass the depth cap
        // (the existing cyclic test places the cycle at an `input:` member, an
        // `EntityOrCommon` entry). Must error, not overflow the stack.
        let schema = r#"
            namespace Drupe {
                entity OAuthUser;
                entity Gateway;
                type A = B;
                type B = A;
                action "Read" appliesTo { principal: [OAuthUser], resource: [Gateway], context: A };
            }
        "#;
        let dsl = parse_event_schema(RR_SCHEMA).unwrap();
        let err = derive(&dsl, schema).expect_err("cyclic context ref must error, not overflow");
        assert!(err.contains("cyclic type definition"), "{err}");
    }

    fn derive_rr(action_schema: &str) -> DerivedEventSchema {
        let dsl = parse_event_schema(RR_SCHEMA).expect("dsl parses");
        derive(&dsl, action_schema).expect("derive succeeds")
    }

    fn path(parts: &[&str]) -> Vec<String> {
        parts.iter().map(|s| s.to_string()).collect()
    }

    /// Assert a dotted path resolves to a declared leaf field.
    fn assert_leaf(ev: &DerivedEvent, parts: &[&str]) {
        assert_eq!(
            ev.lookup_path(&path(parts)),
            PathLookup::Leaf,
            "expected `{}` to be a declared leaf; declared: {:?}",
            parts.join("."),
            ev.declared_paths()
        );
    }

    /// Fetch the leaf `FieldType` at a dotted path (panics if not a leaf).
    fn leaf_type<'a>(ev: &'a DerivedEvent, parts: &[&str]) -> &'a FieldType {
        let (head, rest) = path(parts)
            .split_first()
            .map(|(h, r)| (h.clone(), r.to_vec()))
            .unwrap();
        let mut node = ev.fields.get(&head).expect("head present");
        for seg in &rest {
            match node {
                DerivedFieldNode::Group(m) => node = m.get(seg).expect("segment present"),
                DerivedFieldNode::Leaf(_) => panic!("descended into a leaf"),
            }
        }
        match node {
            DerivedFieldNode::Leaf(t) => t,
            DerivedFieldNode::Group(_) => panic!("expected a leaf at {parts:?}"),
        }
    }

    #[test]
    fn request_nests_inputs_and_keeps_reserved_flat() {
        let d = derive_rr(ACTION_SCHEMA);
        let ns = vec!["Drupe".to_string(), "Action".to_string()];
        let req = d
            .get(&ns, "Login", "request")
            .expect("Login::request derived");
        // ...inputs(A) nests server + user under the `input` group.
        assert_leaf(req, &["input", "server"]);
        assert_leaf(req, &["input", "user"]);
        // The bare (un-nested) names must NOT be top-level any more.
        assert_eq!(req.lookup_path(&path(&["user"])), PathLookup::Absent);
        // `input` alone is a group, not a field.
        assert_eq!(req.lookup_path(&path(&["input"])), PathLookup::Group);
        // Reserved fields stay flat (top-level leaves).
        assert_leaf(req, &["callerPrincipal"]);
        assert_leaf(req, &["callerResource"]);
        assert_leaf(req, &["requestId"]);
        // request does NOT splice outputs.
        assert_eq!(req.lookup_path(&path(&["output"])), PathLookup::Absent);
        assert_eq!(
            req.lookup_path(&path(&["output", "result"])),
            PathLookup::Absent
        );
    }

    #[test]
    fn response_nests_both_input_and_output() {
        let d = derive_rr(ACTION_SCHEMA);
        let ns = vec!["Drupe".to_string(), "Action".to_string()];
        let res = d.get(&ns, "Login", "response").expect("response derived");
        assert_leaf(res, &["output", "result"]);
        assert_leaf(res, &["input", "server"]);
        assert_leaf(res, &["input", "user"]);
    }

    #[test]
    fn principal_type_keeps_full_entity_set() {
        let d = derive_rr(ACTION_SCHEMA);
        let ns = vec!["Drupe".to_string(), "Action".to_string()];
        let req = d.get(&ns, "Login", "request").unwrap();
        match leaf_type(req, &["callerPrincipal"]) {
            FieldType::EntityTypes(set) => {
                // Both declared principal types are kept; no collapse.
                assert!(set.iter().any(|t| t.ends_with("OAuthUser")), "{set:?}");
                assert!(set.iter().any(|t| t.ends_with("IamEntity")), "{set:?}");
                assert_eq!(set.len(), 2, "{set:?}");
            }
            other => panic!("expected entity-type set, got {other:?}"),
        }
    }

    #[test]
    fn uid_is_concrete_string() {
        let d = derive_rr(ACTION_SCHEMA);
        let ns = vec!["Drupe".to_string(), "Action".to_string()];
        let req = d.get(&ns, "Login", "request").unwrap();
        assert_eq!(
            leaf_type(req, &["requestId"]),
            &FieldType::Cedar("String".to_string())
        );
    }

    #[test]
    fn input_and_output_may_share_a_field_name() {
        // The headline collision fix: an action whose input AND output both
        // declare a field `x`. Under the old flat model these clobbered each
        // other; nested, they are distinct leaves `input.x` and `output.x`.
        let schema = r#"
            namespace Drupe {
                entity OAuthUser = { id: String };
                entity Gateway;
                type DupInput  = { x: String };
                type DupOutput = { x: Bool };
                action "Dup" appliesTo {
                    principal: [OAuthUser],
                    resource: [Gateway],
                    context: { input: DupInput, output?: DupOutput }
                };
            }
        "#;
        let d = derive_rr(schema);
        let ns = vec!["Drupe".to_string(), "Action".to_string()];
        let res = d.get(&ns, "Dup", "response").expect("Dup::response");
        assert_leaf(res, &["input", "x"]);
        assert_leaf(res, &["output", "x"]);
        // They are genuinely distinct: the input `x` is a String, the output
        // `x` is a Bool.
        assert_eq!(
            leaf_type(res, &["input", "x"]),
            &FieldType::Cedar("String".to_string())
        );
        assert_eq!(
            leaf_type(res, &["output", "x"]),
            &FieldType::Cedar("Bool".to_string())
        );
    }

    #[test]
    fn record_typed_named_field_nests_into_a_group() {
        // A named field with a record type opts into hierarchy: its members
        // are addressed as `group.member`. Here a custom event schema nests
        // a reserved field `__drupe` with a `sessionid` member.
        let dsl = parse_event_schema(
            r#"decision event <A>::request {
                ...inputs(A),
                __drupe: { sessionid: String },
                requestId: String,
            }"#,
        )
        .unwrap();
        let d = derive(&dsl, ACTION_SCHEMA).expect("derive with nested named field");
        let ns = vec!["Drupe".to_string(), "Action".to_string()];
        let req = d.get(&ns, "Login", "request").unwrap();
        // Reachable at the nested path; the group itself is a group.
        assert_leaf(req, &["__drupe", "sessionid"]);
        assert_eq!(req.lookup_path(&path(&["__drupe"])), PathLookup::Group);
        // A flat reserved field is still a top-level leaf.
        assert_leaf(req, &["requestId"]);
        assert_eq!(
            leaf_type(req, &["__drupe", "sessionid"]),
            &FieldType::Cedar("String".to_string())
        );
    }

    #[test]
    fn named_field_shadowing_a_spread_group_is_an_error() {
        // A named field literally called `input` collides with the `input`
        // group the `...inputs(A)` spread produces.
        let dsl = parse_event_schema(r#"event <A>::r { ...inputs(A), input: String }"#).unwrap();
        let err = derive(&dsl, ACTION_SCHEMA).expect_err("expected a group-shadow collision error");
        assert!(err.contains("shadow a spread group"), "{err}");
    }

    #[test]
    fn decision_kind_set_is_request_only() {
        let d = derive_rr(ACTION_SCHEMA);
        let kinds = d.decision_kinds();
        assert!(kinds.contains("request"));
        assert!(!kinds.contains("response"));
    }

    #[test]
    fn inverse_map_drops_kind() {
        // Both kinds of an action share its (namespace, action) identity;
        // recovering the action is just reading those fields.
        let d = derive_rr(ACTION_SCHEMA);
        for e in &d.events {
            assert_eq!(e.action, "Login");
            assert_eq!(e.namespace, vec!["Drupe".to_string(), "Action".to_string()]);
        }
    }

    #[test]
    fn empty_input_and_output_are_handled() {
        // An action with no input/output context: spreads contribute
        // nothing, reserved fields still injected, no error.
        let schema = r#"
            namespace Drupe {
                entity OAuthUser = { id: String };
                entity Gateway;
                action "Ping" appliesTo {
                    principal: [OAuthUser],
                    resource: [Gateway],
                    context: {}
                };
            }
        "#;
        let d = derive_rr(schema);
        let ns = vec!["Drupe".to_string(), "Action".to_string()];
        let req = d
            .get(&ns, "Ping", "request")
            .expect("Ping::request derived");
        // An empty `input` context still produces an (empty) `input` group;
        // the three reserved fields are the leaves. Declared leaf paths are
        // exactly the reserved set.
        assert_eq!(
            req.declared_paths(),
            vec![
                "callerPrincipal".to_string(),
                "callerResource".to_string(),
                "requestId".to_string(),
            ]
        );
        assert_leaf(req, &["callerPrincipal"]);
    }

    #[test]
    fn derives_against_a_real_corpus_schema() {
        // The request/response DSL against a real per-case schema (which
        // uses common-type-referenced input/output records) derives the
        // actual declared fields — exercising the spread resolution on the
        // shapes the corpus actually contains.
        let schema_path = format!(
            "{}/tests/passing/temporal_only/corpus/0407_resolved_agg_request_does_not_contribute/schema.cedarschema",
            env!("CARGO_MANIFEST_DIR")
        );
        let action_schema = std::fs::read_to_string(schema_path).expect("read 0407 schema");
        let dsl = parse_event_schema(RR_SCHEMA).unwrap();
        let d = derive(&dsl, &action_schema).expect("derive against real schema");
        let ns = vec!["Drupe".to_string(), "Action".to_string()];

        // Transfer::response nests TransferInput { user } under `input`
        // and TransferOutput { amount } under `output`.
        let tr = d
            .get(&ns, "Transfer", "response")
            .expect("Transfer::response derived");
        assert_leaf(tr, &["input", "user"]);
        assert_leaf(tr, &["output", "amount"]);

        // Transfer::request has the input but NOT the output group.
        let trq = d.get(&ns, "Transfer", "request").unwrap();
        assert_leaf(trq, &["input", "user"]);
        assert_eq!(
            trq.lookup_path(&path(&["output", "amount"])),
            PathLookup::Absent
        );

        // Read::response: ReadOutput is empty `{}`, so only ReadInput fields
        // (document, user) appear under `input` — empty spread is harmless.
        let rd = d.get(&ns, "Read", "response").unwrap();
        assert_leaf(rd, &["input", "document"]);
    }

    #[test]
    fn spliced_input_record_member_nests_into_a_group() {
        // A record-typed input member (`meta: Meta`) spliced by `...inputs(A)`
        // must nest so `input.meta.region` is a reachable leaf — not a single
        // opaque `input.meta` leaf. This is the fix for the validator
        // asymmetry: a deep predicate arg (`input.meta.region:`) is now a
        // declared leaf, matching the deep `context.input.meta.region` path
        // the temporal validator already resolves.
        let schema = r#"
            namespace Drupe {
                entity OAuthUser = { id: String };
                entity Gateway;
                type Meta = { region: String, level: Long };
                type ReadInput = { user: String, meta: Meta };
                action "Read" appliesTo {
                    principal: [OAuthUser],
                    resource: [Gateway],
                    context: { input: ReadInput }
                };
            }
        "#;
        let dsl = parse_event_schema(RR_SCHEMA).unwrap();
        let d = derive(&dsl, schema).expect("derive succeeds");
        let ns = vec!["Drupe".to_string(), "Action".to_string()];
        let req = d.get(&ns, "Read", "request").unwrap();
        // The record-typed member is a group; its scalars are leaves at depth 3.
        assert_group(req, &["input", "meta"]);
        assert_leaf(req, &["input", "meta", "region"]);
        assert_leaf(req, &["input", "meta", "level"]);
        // The scalar sibling stays a leaf, and the whole path shows the leaves.
        assert_leaf(req, &["input", "user"]);
        assert_eq!(
            leaf_type(req, &["input", "meta", "level"]),
            &FieldType::Cedar("Long".to_string())
        );
        // The intermediate record member is no longer a leaf.
        assert_ne!(req.lookup_path(&path(&["input", "meta"])), PathLookup::Leaf);
    }

    #[test]
    fn spliced_input_inline_nested_record_nests() {
        // Same, but the nested record is declared inline in the input type
        // (`meta: { region: String }`) rather than via a common-type ref.
        let schema = r#"
            namespace Drupe {
                entity OAuthUser = { id: String };
                entity Gateway;
                type ReadInput = { user: String, meta: { region: String, level: Long } };
                action "Read" appliesTo {
                    principal: [OAuthUser],
                    resource: [Gateway],
                    context: { input: ReadInput }
                };
            }
        "#;
        let dsl = parse_event_schema(RR_SCHEMA).unwrap();
        let d = derive(&dsl, schema).expect("derive succeeds");
        let ns = vec!["Drupe".to_string(), "Action".to_string()];
        let req = d.get(&ns, "Read", "request").unwrap();
        assert_leaf(req, &["input", "meta", "region"]);
        assert_leaf(req, &["input", "meta", "level"]);
    }

    #[test]
    fn spliced_input_nested_record_via_cross_namespace_common_type() {
        // A record-typed input member whose type is a common type declared in
        // ANOTHER namespace (`Shared::Meta`). Its own members must resolve in
        // `Shared`, so `input.meta.region` reaches the leaf — the resolution
        // namespace moves with the cross-namespace chain.
        let schema = r#"
            namespace Shared {
                type Meta = { region: String, level: Long };
            }
            namespace App {
                entity U = { id: String };
                entity G;
                type ReadInput = { user: String, meta: Shared::Meta };
                action "Read" appliesTo {
                    principal: [U],
                    resource: [G],
                    context: { input: ReadInput }
                };
            }
        "#;
        let dsl = parse_event_schema(RR_SCHEMA).unwrap();
        let d = derive(&dsl, schema).expect("derive with cross-namespace nested member");
        let ns = vec!["App".to_string(), "Action".to_string()];
        let req = d
            .get(&ns, "Read", "request")
            .expect("Read::request derived");
        assert_group(req, &["input", "meta"]);
        assert_leaf(req, &["input", "meta", "region"]);
        assert_leaf(req, &["input", "meta", "level"]);
    }

    #[test]
    fn cyclic_input_member_type_errors_cleanly_not_crash() {
        // A self-referential record member (`type A = { x: A }`) used as an
        // action input. Cedar rejects this during typechecking, but derivation
        // runs first — without the depth cap `type_to_node` would recurse until
        // the stack overflows and ABORTS the process. Assert a clean error.
        let schema = r#"
            namespace Drupe {
                entity OAuthUser = { id: String };
                entity Gateway;
                type A = { x: A };
                action "Read" appliesTo {
                    principal: [OAuthUser],
                    resource: [Gateway],
                    context: { input: A }
                };
            }
        "#;
        let dsl = parse_event_schema(RR_SCHEMA).unwrap();
        let err = derive(&dsl, schema).expect_err("a cyclic member type must error, not crash");
        assert!(err.contains("cyclic type definition"), "{err}");
    }

    #[test]
    fn mutually_cyclic_member_types_error_cleanly() {
        // A mutual cycle `A = { b: B }; B = { a: A }` reachable from input.
        let schema = r#"
            namespace Drupe {
                entity OAuthUser = { id: String };
                entity Gateway;
                type A = { b: B };
                type B = { a: A };
                action "Read" appliesTo {
                    principal: [OAuthUser],
                    resource: [Gateway],
                    context: { input: A }
                };
            }
        "#;
        let dsl = parse_event_schema(RR_SCHEMA).unwrap();
        let err = derive(&dsl, schema).expect_err("a mutual cycle must error, not crash");
        assert!(err.contains("cyclic type definition"), "{err}");
    }

    #[test]
    fn cyclic_common_type_alias_errors_cleanly() {
        // A pure alias cycle `A = B; B = A` (no record on the chain) reachable
        // as the context/input type. This exhausts the `resolve_to_record`
        // alias-hop chain; the depth cap turns it into a clean error.
        let schema = r#"
            namespace Drupe {
                entity OAuthUser = { id: String };
                entity Gateway;
                type A = B;
                type B = A;
                action "Read" appliesTo {
                    principal: [OAuthUser],
                    resource: [Gateway],
                    context: { input: A }
                };
            }
        "#;
        let dsl = parse_event_schema(RR_SCHEMA).unwrap();
        let err = derive(&dsl, schema).expect_err("an alias cycle must error, not crash");
        assert!(err.contains("cyclic type definition"), "{err}");
    }

    #[test]
    fn exponential_diamond_type_errors_cleanly_not_hang() {
        // An ACYCLIC "diamond" schema: each `Tk` references `T(k-1)` twice, so
        // depth is only ~k (well under MAX_RECORD_DEPTH) but the materialized
        // tree is ~2^k nodes. The depth cap alone would not catch this; the
        // node-count budget must, turning the blow-up into a clean error rather
        // than an OOM/hang. k=40 → 2^40 nodes, so this must error near-instantly
        // (the budget trips after ~10k nodes), never trying to build the tree.
        let mut types = String::from("type T0 = { v: String };\n");
        for k in 1..=40 {
            types.push_str(&format!(
                "type T{k} = {{ a: T{}, b: T{} }};\n",
                k - 1,
                k - 1
            ));
        }
        let schema = format!(
            r#"
            namespace Drupe {{
                entity OAuthUser = {{ id: String }};
                entity Gateway;
                {types}
                action "Read" appliesTo {{
                    principal: [OAuthUser],
                    resource: [Gateway],
                    context: {{ input: T40 }}
                }};
            }}
        "#
        );
        let dsl = parse_event_schema(RR_SCHEMA).unwrap();
        let err = derive(&dsl, &schema).expect_err("exponential fanout must error, not hang");
        assert!(err.contains("fans out exponentially"), "{err}");
    }

    #[test]
    fn optional_nested_record_member_nests() {
        // An OPTIONAL record-typed member (`meta?: Meta`) still nests — the
        // `required` flag does not affect the derived field tree (the
        // synthesizer / matcher treat every declared leaf uniformly).
        let schema = r#"
            namespace Drupe {
                entity OAuthUser = { id: String };
                entity Gateway;
                type Meta = { region: String };
                type ReadInput = { user: String, meta?: Meta };
                action "Read" appliesTo {
                    principal: [OAuthUser],
                    resource: [Gateway],
                    context: { input: ReadInput }
                };
            }
        "#;
        let dsl = parse_event_schema(RR_SCHEMA).unwrap();
        let d = derive(&dsl, schema).expect("derive succeeds");
        let ns = vec!["Drupe".to_string(), "Action".to_string()];
        let req = d.get(&ns, "Read", "request").unwrap();
        assert_leaf(req, &["input", "meta", "region"]);
    }

    #[test]
    fn nested_member_with_entity_leaf_is_a_leaf() {
        // A nested record whose own member is an ENTITY type: the record nests
        // (a group), but the entity member is a LEAF — the runtime cannot
        // descend an entity ref, so this matches evaluation semantics.
        let schema = r#"
            namespace Drupe {
                entity OAuthUser = { id: String };
                entity Gateway;
                type Owner = { who: OAuthUser, tag: String };
                type ReadInput = { user: String, owner: Owner };
                action "Read" appliesTo {
                    principal: [OAuthUser],
                    resource: [Gateway],
                    context: { input: ReadInput }
                };
            }
        "#;
        let dsl = parse_event_schema(RR_SCHEMA).unwrap();
        let d = derive(&dsl, schema).expect("derive succeeds");
        let ns = vec!["Drupe".to_string(), "Action".to_string()];
        let req = d.get(&ns, "Read", "request").unwrap();
        assert_group(req, &["input", "owner"]);
        assert_leaf(req, &["input", "owner", "who"]); // entity → leaf
        assert_leaf(req, &["input", "owner", "tag"]);
    }

    #[test]
    fn spliced_output_record_member_nests() {
        // The same recursion applies to `...outputs(A)`: a record-typed output
        // member (`detail: Detail`) nests so `output.detail.code` is a leaf.
        let schema = r#"
            namespace Drupe {
                entity OAuthUser = { id: String };
                entity Gateway;
                type Detail = { code: Long };
                type ReviewInput  = { user: String };
                type ReviewOutput = { verdict: String, detail: Detail };
                action "Review" appliesTo {
                    principal: [OAuthUser],
                    resource: [Gateway],
                    context: { input: ReviewInput, output?: ReviewOutput }
                };
            }
        "#;
        let dsl = parse_event_schema(RR_SCHEMA).unwrap();
        let d = derive(&dsl, schema).expect("derive succeeds");
        let ns = vec!["Drupe".to_string(), "Action".to_string()];
        let res = d.get(&ns, "Review", "response").unwrap();
        assert_leaf(res, &["output", "verdict"]);
        assert_group(res, &["output", "detail"]);
        assert_leaf(res, &["output", "detail", "code"]);
    }

    #[test]
    fn reserved_field_colliding_with_an_input_field_is_no_longer_a_collision() {
        // Previously, an action input field literally named `callerPrincipal`
        // collided with the injected reserved field (both were flat). Now the
        // input field nests under `input.callerPrincipal`, distinct from the
        // top-level reserved `callerPrincipal` — so they coexist.
        let schema = r#"
            namespace Drupe {
                entity OAuthUser = { id: String };
                entity Gateway;
                type OddInput = { callerPrincipal: String };
                action "Odd" appliesTo {
                    principal: [OAuthUser],
                    resource: [Gateway],
                    context: { input: OddInput }
                };
            }
        "#;
        let dsl = parse_event_schema(RR_SCHEMA).unwrap();
        let d = derive(&dsl, schema).expect("nesting removes the old collision");
        let ns = vec!["Drupe".to_string(), "Action".to_string()];
        let req = d.get(&ns, "Odd", "request").unwrap();
        // The oddly-named input field is reachable at input.callerPrincipal,
        // and the reserved principal is still the top-level leaf.
        assert_leaf(req, &["input", "callerPrincipal"]);
        assert_leaf(req, &["callerPrincipal"]);
    }

    #[test]
    fn cross_namespace_input_type_resolves() {
        // An action in `App` whose `input` is a common type defined in a
        // *different* namespace (`Shared::Addr`). Cedar stores such a
        // reference fully-qualified and keys each namespace's common types
        // by the bare id (confirmed empirically against cedar-policy 4.11),
        // so the spread must look `Addr` up in `Shared`, not in `App`.
        let schema = r#"
            namespace Shared {
                type Addr = { city: String, zip: String };
            }
            namespace App {
                entity U = { id: String };
                entity G;
                action "Act" appliesTo {
                    principal: [U],
                    resource: [G],
                    context: { input: Shared::Addr }
                };
            }
        "#;
        let dsl = parse_event_schema(RR_SCHEMA).unwrap();
        let d = derive(&dsl, schema).expect("derive with cross-namespace input");
        let ns = vec!["App".to_string(), "Action".to_string()];
        let req = d.get(&ns, "Act", "request").expect("Act::request derived");
        // The cross-namespace record's fields are spliced in, under `input`.
        assert_leaf(req, &["input", "city"]);
        assert_leaf(req, &["input", "zip"]);
    }

    #[test]
    fn common_type_chain_resolves() {
        // `input: A` where `A = B` and `B = { … }` — a common type defined
        // in terms of another common type must chain through.
        let schema = r#"
            namespace App {
                entity U = { id: String };
                entity G;
                type Inner = { field_x: String };
                type Outer = Inner;
                action "Act" appliesTo {
                    principal: [U],
                    resource: [G],
                    context: { input: Outer }
                };
            }
        "#;
        let dsl = parse_event_schema(RR_SCHEMA).unwrap();
        let d = derive(&dsl, schema).expect("derive with common-type chain");
        let ns = vec!["App".to_string(), "Action".to_string()];
        let req = d.get(&ns, "Act", "request").unwrap();
        assert_leaf(req, &["input", "field_x"]);
    }

    // ─── Deep hierarchical nesting of injected fields (facet 1) ──────

    /// Derive `event_schema` (a custom DSL) against `ACTION_SCHEMA`, then
    /// return the `Login::request` event.
    fn derive_req(event_schema: &str) -> DerivedEvent {
        let dsl = parse_event_schema(event_schema).expect("event dsl parses");
        let d = derive(&dsl, ACTION_SCHEMA).expect("derive succeeds");
        let ns = vec!["Drupe".to_string(), "Action".to_string()];
        d.get(&ns, "Login", "request")
            .expect("Login::request derived")
            .clone()
    }

    /// Assert a dotted path resolves to a field *group* (not a leaf).
    fn assert_group(ev: &DerivedEvent, parts: &[&str]) {
        assert_eq!(
            ev.lookup_path(&path(parts)),
            PathLookup::Group,
            "expected `{}` to be a group",
            parts.join(".")
        );
    }

    /// Assert a dotted path resolves to nothing.
    fn assert_absent(ev: &DerivedEvent, parts: &[&str]) {
        assert_eq!(
            ev.lookup_path(&path(parts)),
            PathLookup::Absent,
            "expected `{}` to be absent",
            parts.join(".")
        );
    }

    #[test]
    fn injected_field_nests_two_levels() {
        let req = derive_req(
            r#"decision event <A>::request {
                ...inputs(A),
                __drupe: { sessionid: String },
            }"#,
        );
        assert_group(&req, &["__drupe"]);
        assert_leaf(&req, &["__drupe", "sessionid"]);
    }

    #[test]
    fn injected_field_nests_three_levels() {
        let req = derive_req(
            r#"decision event <A>::request {
                ...inputs(A),
                a: { b: { c: String } },
            }"#,
        );
        assert_group(&req, &["a"]);
        assert_group(&req, &["a", "b"]);
        assert_leaf(&req, &["a", "b", "c"]);
        assert_eq!(
            leaf_type(&req, &["a", "b", "c"]),
            &FieldType::Cedar("String".to_string())
        );
    }

    #[test]
    fn injected_field_nests_four_levels() {
        let req = derive_req(
            r#"decision event <A>::request {
                w: { x: { y: { z: Long } } },
            }"#,
        );
        assert_leaf(&req, &["w", "x", "y", "z"]);
        // Every proper prefix is a group.
        assert_group(&req, &["w"]);
        assert_group(&req, &["w", "x"]);
        assert_group(&req, &["w", "x", "y"]);
    }

    #[test]
    fn mixed_depths_coexist() {
        // A flat leaf, a depth-2 group, and a depth-3 group on one event.
        let req = derive_req(
            r#"decision event <A>::request {
                flat: String,
                two: { leaf: String },
                three: { mid: { leaf: String } },
            }"#,
        );
        assert_leaf(&req, &["flat"]);
        assert_leaf(&req, &["two", "leaf"]);
        assert_leaf(&req, &["three", "mid", "leaf"]);
        assert_eq!(
            req.declared_paths(),
            vec![
                "flat".to_string(),
                "three.mid.leaf".to_string(),
                "two.leaf".to_string(),
            ]
        );
    }

    #[test]
    fn leaf_fields_agrees_with_declared_paths_in_order() {
        // `leaf_fields` (typed) must yield the same leaves in the same order as
        // `declared_paths` (untyped) — same set AND same ordering, so the two
        // never disagree. Uses mixed depths so the sort is non-trivial.
        let req = derive_req(
            r#"decision event <A>::request {
                flat: String,
                two: { leaf: String },
                three: { mid: { leaf: String } },
            }"#,
        );
        let typed: Vec<String> = req
            .leaf_fields()
            .into_iter()
            .map(|(path, _)| path.join("."))
            .collect();
        assert_eq!(typed, req.declared_paths());
    }

    #[test]
    fn leaf_fields_carries_types() {
        // The typed leaves carry their declared types (the thing `declared_paths`
        // drops): a `Long` scalar and an entity-type-set reserved field.
        let d = derive_rr(ACTION_SCHEMA);
        let ns = vec!["Drupe".to_string(), "Action".to_string()];
        let req = d.get(&ns, "Login", "request").unwrap();
        let by_path: std::collections::BTreeMap<String, FieldType> = req
            .leaf_fields()
            .into_iter()
            .map(|(p, ty)| (p.join("."), ty))
            .collect();
        // Spliced input scalar → Cedar text.
        assert_eq!(
            by_path.get("input.user"),
            Some(&FieldType::Cedar("String".to_string()))
        );
        // Injected reserved principal → entity-type set (not Cedar text).
        match by_path.get("callerPrincipal") {
            Some(FieldType::EntityTypes(tys)) => {
                assert!(tys.iter().any(|t| t.ends_with("OAuthUser")), "{tys:?}");
            }
            other => panic!("expected EntityTypes for callerPrincipal, got {other:?}"),
        }
    }

    #[test]
    fn sibling_nested_groups_at_same_level() {
        let req = derive_req(
            r#"decision event <A>::request {
                meta: { a: String, b: String },
                audit: { c: String, d: String },
            }"#,
        );
        assert_leaf(&req, &["meta", "a"]);
        assert_leaf(&req, &["meta", "b"]);
        assert_leaf(&req, &["audit", "c"]);
        assert_leaf(&req, &["audit", "d"]);
    }

    #[test]
    fn empty_nested_record_is_a_group_with_no_leaves() {
        let req = derive_req(
            r#"decision event <A>::request {
                ...inputs(A),
                meta: { },
            }"#,
        );
        // `meta` is a group; it has no members.
        assert_group(&req, &["meta"]);
        assert_absent(&req, &["meta", "anything"]);
    }

    #[test]
    fn nested_group_coexists_with_flat_reserved_fields() {
        // The reserved `caller*` set stays flat while a sibling injected
        // field nests — flat-by-default and opt-in hierarchy together.
        let req = derive_req(
            r#"decision event <A>::request {
                ...inputs(A),
                callerPrincipal: principalType(A),
                requestId:       String,
                __drupe:       { session: { id: String } },
            }"#,
        );
        assert_leaf(&req, &["callerPrincipal"]);
        assert_leaf(&req, &["requestId"]);
        assert_leaf(&req, &["__drupe", "session", "id"]);
        assert_group(&req, &["input"]);
    }

    #[test]
    fn spread_inside_a_named_record_nests_under_its_group_name() {
        // A spread always mints its own `input` group, even nested inside a
        // named record — so `meta: { ...inputs(A) }` yields `meta.input.user`,
        // NOT `meta.user`. Pin this so the behavior is intentional, not
        // accidental.
        let req = derive_req(r#"decision event <A>::request { meta: { ...inputs(A) } }"#);
        assert_leaf(&req, &["meta", "input", "user"]);
        assert_leaf(&req, &["meta", "input", "server"]);
        assert_absent(&req, &["meta", "user"]);
    }

    // ─── input/output field-name collisions are now distinct (facet 2) ──

    /// A schema whose input and output share field names, with divergent
    /// types.
    const DUP_ACTION: &str = r#"
        namespace Drupe {
            entity OAuthUser = { id: String };
            entity Gateway;
            type DupInput  = { shared: String, only_in: String };
            type DupOutput = { shared: Long,   only_out: Bool };
            action "Dup" appliesTo {
                principal: [OAuthUser],
                resource: [Gateway],
                context: { input: DupInput, output?: DupOutput }
            };
        }
    "#;

    fn derive_dup_response() -> DerivedEvent {
        let dsl = parse_event_schema(RR_SCHEMA).unwrap();
        let d = derive(&dsl, DUP_ACTION).unwrap();
        let ns = vec!["Drupe".to_string(), "Action".to_string()];
        d.get(&ns, "Dup", "response").unwrap().clone()
    }

    #[test]
    fn input_output_shared_name_keeps_divergent_types() {
        let res = derive_dup_response();
        // Same field name `shared` on both sides, kept distinct WITH their
        // different types — impossible under the old flat model.
        assert_eq!(
            leaf_type(&res, &["input", "shared"]),
            &FieldType::Cedar("String".to_string())
        );
        assert_eq!(
            leaf_type(&res, &["output", "shared"]),
            &FieldType::Cedar("Long".to_string())
        );
    }

    #[test]
    fn input_output_disjoint_names_both_present() {
        let res = derive_dup_response();
        assert_leaf(&res, &["input", "only_in"]);
        assert_leaf(&res, &["output", "only_out"]);
        // The cross-side names do NOT leak across groups.
        assert_absent(&res, &["input", "only_out"]);
        assert_absent(&res, &["output", "only_in"]);
    }

    #[test]
    fn input_field_named_like_a_reserved_field_is_distinct() {
        // An input field literally named `requestId` nests to
        // `input.requestId`, distinct from the top-level reserved
        // `requestId` — no collision (they live at different paths).
        let schema = r#"
            namespace Drupe {
                entity OAuthUser = { id: String };
                entity Gateway;
                type OddInput = { requestId: String, real: String };
                action "Odd" appliesTo {
                    principal: [OAuthUser],
                    resource: [Gateway],
                    context: { input: OddInput }
                };
            }
        "#;
        let dsl = parse_event_schema(RR_SCHEMA).unwrap();
        let d = derive(&dsl, schema).expect("no collision — different paths");
        let ns = vec!["Drupe".to_string(), "Action".to_string()];
        let req = d.get(&ns, "Odd", "request").unwrap();
        assert_leaf(req, &["input", "requestId"]);
        assert_leaf(req, &["requestId"]);
        assert_leaf(req, &["input", "real"]);
    }

    // ─── Collision / shadow rules (facet 4, post-fix) ───────────────

    #[test]
    fn named_record_shadowing_spread_group_errors_spread_first() {
        // Spread first, then a record-typed named field with the same name:
        // must error (previously silently clobbered the spread group).
        let dsl = parse_event_schema(r#"event <A>::r { ...inputs(A), input: { extra: String } }"#)
            .unwrap();
        let err = derive(&dsl, ACTION_SCHEMA)
            .expect_err("record-vs-spread-group collision (spread first)");
        assert!(
            err.contains("shadow a spread group") || err.contains("collides"),
            "{err}"
        );
    }

    #[test]
    fn named_record_shadowing_spread_group_errors_spread_second() {
        // Record-typed named field first, then a spread with the same group
        // name: must error (previously silently merged).
        let dsl = parse_event_schema(r#"event <A>::r { input: { extra: String }, ...inputs(A) }"#)
            .unwrap();
        let err = derive(&dsl, ACTION_SCHEMA)
            .expect_err("record-vs-spread-group collision (spread second)");
        assert!(
            err.contains("collides") || err.contains("share a name"),
            "{err}"
        );
    }

    #[test]
    fn duplicate_named_field_errors() {
        // The same top-level name declared twice is a duplicate, regardless
        // of shape.
        let dsl =
            parse_event_schema(r#"event <A>::r { dup: String, dup: { x: String } }"#).unwrap();
        let err = derive(&dsl, ACTION_SCHEMA).expect_err("duplicate top-level field name");
        assert!(
            err.contains("defined more than once") || err.contains("collides"),
            "{err}"
        );
    }

    #[test]
    fn duplicate_spread_errors() {
        // Two `...inputs(A)` spreads both want the `input` group.
        let dsl = parse_event_schema(r#"event <A>::r { ...inputs(A), ...inputs(A) }"#).unwrap();
        let err = derive(&dsl, ACTION_SCHEMA).expect_err("duplicate spread group");
        assert!(
            err.contains("collides") || err.contains("share a name"),
            "{err}"
        );
    }

    #[test]
    fn duplicate_name_inside_a_nested_record_errors() {
        // Uniqueness is enforced at every level, not just the top.
        let dsl = parse_event_schema(r#"event <A>::r { meta: { x: String, x: Long } }"#).unwrap();
        let err = derive(&dsl, ACTION_SCHEMA).expect_err("duplicate name inside nested record");
        assert!(err.contains("defined more than once"), "{err}");
    }

    // ─── Pin collection ─────────────────────────────────────────────

    #[test]
    fn no_pins_by_default() {
        let d = derive_rr(ACTION_SCHEMA);
        let ns = vec!["Drupe".to_string(), "Action".to_string()];
        assert!(
            d.get(&ns, "Login", "request").unwrap().pins.is_empty(),
            "stock request/response schema declares no pins"
        );
    }

    #[test]
    fn top_level_pin_recorded_with_its_path_and_context() {
        let req = derive_req(
            r#"decision event <A>::request {
                ...inputs(A),
                pin callerPrincipal: principalType(A) = principal,
                requestId: String,
            }"#,
        );
        assert_eq!(req.pins.len(), 1);
        let pin = &req.pins[0];
        assert_eq!(pin.field_path, vec!["callerPrincipal".to_string()]);
        assert_eq!(pin.context_path, vec!["principal".to_string()]);
        assert_eq!(pin.root, PinRoot::Scope);
    }

    #[test]
    fn nested_pin_records_full_dotted_path() {
        // A pin on a leaf inside a record gets the full path to that leaf.
        let req = derive_req(
            r#"decision event <A>::request {
                ...inputs(A),
                __drupe: { pin session_id: String = context.__drupe.session_id },
            }"#,
        );
        assert_eq!(req.pins.len(), 1);
        let pin = &req.pins[0];
        assert_eq!(
            pin.field_path,
            vec!["__drupe".to_string(), "session_id".to_string()]
        );
        assert_eq!(
            pin.context_path,
            vec!["__drupe".to_string(), "session_id".to_string()]
        );
        assert_eq!(pin.root, PinRoot::Context);
        // The pinned leaf is still a declared field of the event.
        assert_leaf(&req, &["__drupe", "session_id"]);
    }

    #[test]
    fn multiple_pins_all_recorded() {
        let req = derive_req(
            r#"decision event <A>::request {
                ...inputs(A),
                pin callerPrincipal: principalType(A) = principal,
                pin callerResource:  resourceType(A)  = resource,
                requestId: String,
            }"#,
        );
        assert_eq!(req.pins.len(), 2);
        let paths: Vec<&str> = req.pins.iter().map(|p| p.field_path[0].as_str()).collect();
        assert!(paths.contains(&"callerPrincipal"));
        assert!(paths.contains(&"callerResource"));
        assert!(req.pins.iter().all(|p| p.root == PinRoot::Scope));
    }
}
