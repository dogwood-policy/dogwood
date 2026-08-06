#![doc = include_str!("../README.md")]

// ─── Public API modules ──────────────────────────────────────────────
//
// The Cedar-parity surface lives in focused modules; everything a consumer
// needs is re-exported at the crate root below, so `dogwood_language::<T>`
// reaches the whole API. These modules are `pub` only so their rustdoc has a
// home; reach their contents through the crate-root re-exports.
pub mod authorize;
pub mod engine;
pub mod policy_schema;
pub mod policy_set;
pub mod policy_view;
pub mod service_schema;
pub mod trace_api;
pub mod validator;

// ─── The embedded regression corpus (feature `corpus`) ───────────────
//
// Exposes the temporal regression cases (policy + schema + trace + expected
// verdicts) so an alternative engine can be checked against the same cases
// this crate's in-memory engine is validated against. Data only — not part of
// the authorization API.
#[cfg(feature = "corpus")]
pub mod corpus;

// ─── Crate-private implementation ────────────────────────────────────
//
// The lowering pipeline (`api`) and the modules it drives. Reached by
// consumers only through the re-exports above.
pub(crate) mod api;
pub(crate) mod ast;
pub(crate) mod cedarify;
pub(crate) mod error;
pub(crate) mod event_schema;
pub(crate) mod extension;
pub(crate) mod interpreter;
pub(crate) mod macros;
pub(crate) mod parser;
pub(crate) mod schema;
pub(crate) mod validate;

// ─── The public surface, re-exported at the crate root ───────────────

/// The **service-provided** schema half (macros, provider declarations, and
/// event-schema DSL) and its builder, plus the built-in default event schema
/// and macro library. The fixed, customer-independent inputs to lowering,
/// available up front (before any action schema).
pub use crate::service_schema::{
    DEFAULT_EVENT_SCHEMA, DEFAULT_MACROS, ServiceSchema, ServiceSchemaBuilder,
    UNPINNED_EVENT_SCHEMA,
};

/// The **action-schema** half (a Cedar `.cedarschema`, or one generated from
/// an MCP tool manifest) — the per-customer input to lowering. Analog of
/// `cedar_policy::Schema`.
pub use crate::policy_schema::PolicySchema;

/// The two policy-set phases: [`ParsedPolicySet`] (parsed + macro-expanded,
/// pre-action-schema) and [`LoweredPolicySet`] (lowered to Cedar). The latter
/// is the analog of `cedar_policy::PolicySet` and the source of the compiled
/// Cedar artifacts for external-service interop. [`ParsedPolicy`] is the opaque per-policy
/// handle from [`ParsedPolicySet::policies`], for pre-lowering diagnostics.
pub use crate::policy_set::{LoweredPolicySet, ParsedPolicy, ParsedPolicySet};

/// The Dogwood-owned **scope view** returned by
/// [`ParsedPolicy::scope`](crate::policy_set::ParsedPolicy::scope): a
/// pre-lowering, read-only projection of a policy head. [`PolicyScope`] holds
/// the three scope constraints, mirroring the shapes `cedar_policy` uses for a
/// template's scope (entity leaves are [`cedar_policy::EntityUid`] /
/// [`cedar_policy::EntityTypeName`]; a `?principal` / `?resource` slot reads as
/// `None`), so crawling a scope needs no dependency on `cedar-policy-core` or
/// on Dogwood's internal AST.
pub use crate::policy_view::{
    ActionConstraint, PolicyScope, PrincipalConstraint, ResourceConstraint,
};

/// A hoisted information-provider leaf and the types it carries, exposed by
/// [`LoweredPolicySet::provider_fields`](crate::LoweredPolicySet::provider_fields).
/// A consumer reimplementing the decision loop (rather than using
/// [`Authorizer`]) reads each field's `context.providers.<id>` key, the
/// [`Invocation`] to evaluate, and its resolved [`ProviderDecl`] (with the
/// [`Implementation`] / [`ParamType`] / [`MethodDecl`] it references).
/// ([`TemporalField`], the temporal counterpart, is re-exported alongside the
/// engine types.)
pub use crate::api::ProviderField;
pub use crate::extension::provider::ast::{Arg, Invocation};

/// The derived event signatures and their declared field paths/types, exposed
/// by [`LoweredPolicySet::event_signatures`](crate::LoweredPolicySet::event_signatures).
/// A client that validates, constructs, or introspects events reads these to
/// see every field an event of a given `(action, kind)` may carry — including
/// schema-injected fields (`caller*`, custom injected/pinned fields) that are
/// not part of the action's Cedar `context` — and the [`EventPin`]s correlating
/// those fields to request-side values (schema-agnostic: no field-naming
/// convention assumed).
pub use crate::api::{EventFieldPath, EventFieldType, EventPin, EventPinRoot, EventSignature};
/// The information-provider declaration types. These make up the full
/// [`ProviderDeclarations`] tree and all have public fields and no
/// `#[non_exhaustive]`, so a caller can build declarations **directly** with
/// struct literals — the alternative to deserializing them from JSON via
/// [`ProviderDeclarations::from_json`] / [`ProviderDeclarations::from_json_file`].
pub use crate::extension::provider::declarations::{
    Implementation, MethodDecl, ParamType, ProviderDecl,
};

/// Schema-aware validation. Analog of `cedar_policy::Validator` and its
/// result / finding types.
pub use crate::validator::{ValidationError, ValidationResult, ValidationWarning, Validator};

/// The stateful authorizer, its builder, and the decision it returns.
pub use crate::authorize::{
    Authorizer, AuthorizerBuilder, Decision, Diagnostics, DogwoodRuleRef, Response,
};

/// The swappable decision and temporal-evaluation backends: the traits a
/// caller implements to replace local Cedar evaluation (e.g. with
/// an external Cedar authorization service) or in-memory temporal evaluation (e.g. with a
/// compiled, database-backed engine), the built-in defaults, and the
/// request/decision types the [`PolicyEngine`] exchanges.
pub use crate::engine::{
    ActionRef, ActionScope, AuthorizationDecision, AuthorizationRequest, CedarPolicyEngine,
    ExtensionId, InMemoryTemporalEngine, PartitionKey, PolicyEngine, ProviderRequest,
    ProviderResolver, Temporal, TemporalBindings, TemporalEngine, TemporalField,
};

/// The parsed temporal condition AST — the tree hanging off every
/// [`TemporalField::condition`](crate::TemporalField). Re-exported **primarily
/// for reading** so an out-of-crate [`TemporalEngine`] (e.g. a compiler that
/// lowers each leaf to SQL) can recursively destructure a leaf's condition (the
/// nodes are also constructible — see below); without this the
/// node types are `pub(crate)` and a leaf's `condition` is an opaque,
/// `Debug`-only handle to any downstream crate.
///
/// The primary use is **reading**: a consumer matches on `Condition::kind` and
/// reads the node fields. When Dogwood produces the tree (via parsing + macro
/// expansion + checking) the post-expansion invariants hold — transient nodes
/// (`Call`/`SigilRef`/`Refine`, `ParamRef`/`BinderRef`) never appear and can be
/// treated as unreachable.
///
/// The node types are also **constructible** by a downstream crate (their fields
/// and variants are public), so an external client can build a `Condition` tree
/// programmatically — e.g. to feed an alternative engine. The one wrinkle is the
/// `span` field: the `Span` type itself is intentionally not part
/// of the public API (source-mapping is a crate-internal detail), so fill that
/// field with [`dummy_span`], which yields a placeholder span
/// without naming the type. A client that only *reads* a Dogwood-produced tree
/// ignores `.span` entirely. Constructing transient/invariant-violating nodes is
/// the caller's responsibility — Dogwood's own guarantees hold only for trees it
/// produced.
///
/// NOTE: this widens the public surface beyond the four lifecycle functions.
/// It is deliberately scoped to callers that consume the temporal AST, and is
/// kept in one module so it can be revisited as a unit.
pub mod temporal_ast {
    pub use crate::extension::temporal::ast::{
        AggExpr, AggExprKind, BinderSlot, CmpOp, Condition, ConditionKind, Interval, NamedArg,
        Predicate, Term, TimeUnit, Type, TypedBinder, WithinSpec,
    };
}

/// The core event input (Dogwood's generalization of `cedar_policy::Request`)
/// and its builder, plus the runtime value type used for event fields.
pub use crate::interpreter::value::{Event, EventBuilder, Value};

/// Whole-trace `.log` replay conveniences.
pub use crate::trace_api::{parse_trace, replay_log};

/// Information-provider declarations (part of the service schema). Built from
/// JSON and supplied to [`ServiceSchemaBuilder::providers`].
pub use crate::extension::provider::declarations::ProviderDeclarations;

/// The construction error returned by the lowering phases
/// ([`ParsedPolicySet::parse`](crate::policy_set::ParsedPolicySet::parse) /
/// [`ParsedPolicySet::lower`](crate::policy_set::ParsedPolicySet::lower)) and
/// [`ServiceSchemaBuilder::build`], plus its self-rendering leaf types (so a
/// consumer can match a variant and inspect its located sub-errors). Each
/// spanned leaf carries its `.dw` source and renders its own underlined
/// snippet.
pub use crate::api::Error;
pub use crate::error::{CedarifyError, MacroError, ParseError, ParseErrors, SourceLoc};

/// A placeholder source span for programmatically-constructed
/// [`temporal_ast`] nodes (the `span` field's type is crate-private, so this is
/// how a downstream crate fills it without naming it). See [`dummy_span`] itself.
pub use crate::error::dummy_span;

/// The `cedar-policy` types that appear in Dogwood's public API, re-exported
/// so a consumer can name them — implement a [`PolicyEngine`], read the
/// artifacts from [`LoweredPolicySet::as_cedar`](crate::LoweredPolicySet::as_cedar) /
/// [`LoweredPolicySet::cedar_schema`](crate::LoweredPolicySet::cedar_schema), or
/// bridge a [`cedar::Request`](cedar_policy::Request) via
/// [`Event::from_request`](crate::Event::from_request) — **without** taking a
/// direct dependency on the `cedar-policy` crate (which would also have to be
/// version-matched to Dogwood's).
pub mod cedar {
    pub use cedar_policy::{Entities, EntityUid, PolicySet, Request, Schema};
}

/// MCP schema generation — a Dogwood action schema *is* an MCP tool
/// manifest; these turn one into the Cedar `.cedarschema` text fed to
/// [`PolicySchema::from_cedarschema_str`].
pub use crate::schema::{DRUPE_TEMPLATE, mcp_to_cedar_schema, mcp_to_cedar_schema_with_template};
