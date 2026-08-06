//! [`ServiceSchema`] and [`ServiceSchemaBuilder`] — the **service-provided,
//! customer-independent** inputs to lowering, available up front (before any
//! action schema exists).
//!
//! Dogwood's schema splits into two halves along the one axis that matters for
//! the lowering phases (see [`crate::policy_set`]):
//!
//!   * the **[`ServiceSchema`]** (this type) — the parts a service fixes once
//!     and reuses across every customer / policy set: the **macro library**,
//!     the **information-provider declarations**, and the **event schema** DSL.
//!     None of these needs an action schema, so they are available before the
//!     customer supplies one, and [`parse`](crate::policy_set::ParsedPolicySet::parse)
//!     (syntax + macro expansion) runs against this half alone.
//!   * the **[`PolicySchema`](crate::PolicySchema)** — the **action schema**
//!     (a Cedar `.cedarschema`, or one generated from an MCP tool manifest),
//!     which typically arrives later and changes per customer. It is the only
//!     input [`lower`](crate::policy_set::ParsedPolicySet::lower) needs beyond
//!     the parsed set.
//!
//! The event schema is *derived against* the action schema, so this half can
//! only carry the **parsed but unbound** event-schema DSL; the derivation
//! itself is deferred to `lower`, where the action schema is present.

use crate::api::Error;
use crate::event_schema::ast::EventSchema;
use crate::extension::provider::declarations::ProviderDeclarations;

/// The built-in default event schema: the request/response convention.
///
/// For every action `A`, it derives a `request` decision event (input fields,
/// `callerPrincipal`, `callerResource`, `requestId`, and `sessionId`), a
/// `response` history event (input and output fields plus the same reserved
/// leaves), and an `error` history event (input fields and reserved leaves).
/// A [`ServiceSchemaBuilder`] with no explicit
/// [`event_schema_str`](ServiceSchemaBuilder::event_schema_str) uses this.
pub const DEFAULT_EVENT_SCHEMA: &str =
    include_str!("../configuration/event-schemas/pinned.dwschema");

/// The built-in **unpinned** event schema: the same request/response/error
/// structure as [`DEFAULT_EVENT_SCHEMA`] but WITHOUT the universal symmetric pin
/// on `callerPrincipal`. Temporal predicates then use global-trace semantics
/// (a leaf can match events from any principal) and, crucially, a leaf is NOT
/// relativized into the pinned `exists`-quantified count/`Or` encoding — it keeps
/// its authored shape (`since` / bare predicate / `&&`).
///
/// Exposed (like [`DEFAULT_EVENT_SCHEMA`]) so downstream test suites can build a
/// [`ServiceSchema`] whose leaves stay in authored form — e.g. operator-mechanics
/// and synthesis-smoke tests that assert on the plain leaf structure rather than
/// the pinned relativization. Mirrors
/// `configuration/event-schemas/unpinned.dwschema`.
pub const UNPINNED_EVENT_SCHEMA: &str =
    include_str!("../configuration/event-schemas/unpinned.dwschema");

/// The built-in default macro library.
///
/// A [`ServiceSchemaBuilder`] with no explicit
/// [`macros_str`](ServiceSchemaBuilder::macros_str) uses this. Its `def cedar`
/// / `def temporal` definitions are merged into every policy set at lowering
/// time (a policy's own `def` of the same name takes precedence). It ships a
/// small standard library of temporal aggregation macros (`count_within`,
/// `sum_within`, `count_distinct_within`, `bind`), embedded into the crate at
/// build time so they are available to every caller regardless of working
/// directory.
pub const DEFAULT_MACROS: &str = include_str!("../configuration/default_macros.dw");

/// The service-provided, customer-independent half of a Dogwood schema: the
/// event schema (parsed but not yet bound to an action schema), the (optional)
/// provider declarations, and the macro library.
///
/// Available up front — [`ParsedPolicySet::parse`](crate::policy_set::ParsedPolicySet::parse)
/// takes it, and the parsed set carries it so
/// [`lower`](crate::policy_set::ParsedPolicySet::lower) needs only the
/// [`PolicySchema`](crate::PolicySchema). Build one with
/// [`ServiceSchema::builder`], or take the all-defaults form with
/// [`ServiceSchema::defaults`].
#[derive(Debug, Clone)]
pub struct ServiceSchema {
    /// The event schema, parsed from its DSL but **not** derived against an
    /// action schema (derivation is deferred to `lower`).
    event_schema: EventSchema,
    /// The information-provider declarations, if any.
    providers: Option<ProviderDeclarations>,
    /// The macro library source (`def` definitions), merged into every policy
    /// set at lowering time.
    macros: String,
}

impl ServiceSchema {
    /// Start building a service schema. The event schema defaults to
    /// [`DEFAULT_EVENT_SCHEMA`] (the request/response convention), the macros
    /// to [`DEFAULT_MACROS`], and the providers to empty.
    pub fn builder() -> ServiceSchemaBuilder {
        ServiceSchemaBuilder {
            event_schema_src: None,
            providers: None,
            macros_src: None,
        }
    }

    /// The all-defaults service schema: the default event schema and macro
    /// library, and no providers. The common pure-Cedar / no-providers case.
    /// Equivalent to `ServiceSchema::builder().build()`.
    pub fn defaults() -> ServiceSchema {
        ServiceSchema::builder()
            .build()
            .expect("the default event schema always parses")
    }

    // ─── crate-internal accessors (used by lowering) ─────────────────

    pub(crate) fn event_schema(&self) -> &EventSchema {
        &self.event_schema
    }

    pub(crate) fn provider_declarations(&self) -> Option<&ProviderDeclarations> {
        self.providers.as_ref()
    }

    pub(crate) fn macros(&self) -> &str {
        &self.macros
    }
}

/// Builder for a [`ServiceSchema`]. Parses (but does not derive) the
/// event-schema DSL in [`build`](ServiceSchemaBuilder::build).
#[derive(Debug, Clone)]
pub struct ServiceSchemaBuilder {
    event_schema_src: Option<String>,
    providers: Option<ProviderDeclarations>,
    macros_src: Option<String>,
}

impl ServiceSchemaBuilder {
    /// Set the event-schema DSL source. Optional — omit to use
    /// [`DEFAULT_EVENT_SCHEMA`] (the request/response convention).
    pub fn event_schema_str(mut self, src: &str) -> Self {
        self.event_schema_src = Some(src.to_string());
        self
    }

    /// Set the information-provider declarations. Optional — omit for a
    /// policy that uses no `provider { … }` clauses (equivalent to empty
    /// declarations).
    pub fn providers(mut self, declarations: ProviderDeclarations) -> Self {
        self.providers = Some(declarations);
        self
    }

    /// Set the macro library source — reusable `def cedar` / `def temporal`
    /// definitions merged into every policy set lowered against this schema.
    /// Optional — omit to use [`DEFAULT_MACROS`]. A policy's own `def` of the
    /// same name takes precedence over a macro from this library.
    pub fn macros_str(mut self, src: &str) -> Self {
        self.macros_src = Some(src.to_string());
        self
    }

    /// Assemble the [`ServiceSchema`]: parse the event-schema DSL (but do
    /// **not** derive it — that needs the action schema and happens in
    /// [`lower`](crate::policy_set::ParsedPolicySet::lower)).
    ///
    /// Errors if the event-schema DSL fails to parse, or if it is explicitly
    /// set to an empty string (which declares no events, so authorization could
    /// never run).
    pub fn build(self) -> Result<ServiceSchema, Error> {
        // An explicitly-supplied event schema is expected to declare events;
        // a blank / whitespace / comment-only string parses to zero
        // declarations, which is almost always a mistake (a caller reading an
        // empty `.dwschema`, or assuming `""` means "use the default"). That
        // silently yields a schema with no decision kinds, so
        // `Authorizer::is_authorized` returns `None` for every event. Reject
        // it, and point at the default. Omitting `event_schema_str` entirely
        // uses `DEFAULT_EVENT_SCHEMA`; the default derives a `decision`
        // `request` event, so this guard never trips on the default path.
        let event_schema_src = match self.event_schema_src.as_deref() {
            Some(src) if src.trim().is_empty() => {
                return Err(Error::EventSchema(
                    "event_schema_str was given an empty event schema, which declares no \
                     events (so authorization could never run); omit event_schema_str to use \
                     the default request/response schema, or pass a schema that declares a \
                     `decision` event"
                        .to_string(),
                ));
            }
            Some(src) => src,
            None => DEFAULT_EVENT_SCHEMA,
        };

        let event_schema = crate::event_schema::parse::parse_event_schema(event_schema_src)
            .map_err(Error::EventSchema)?;

        let macros = self
            .macros_src
            .unwrap_or_else(|| DEFAULT_MACROS.to_string());

        Ok(ServiceSchema {
            event_schema,
            providers: self.providers,
            macros,
        })
    }
}
