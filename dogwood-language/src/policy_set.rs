//! The two policy-set phases: [`ParsedPolicySet`] (parsed + macro-expanded)
//! and [`LoweredPolicySet`] (lowered to Cedar), Dogwood's analog of
//! `cedar_policy::PolicySet`.
//!
//! Lowering Dogwood source to Cedar is split into two phases along the one
//! input that motivates the split — the **action schema**:
//!
//!   1. [`ParsedPolicySet::parse`] takes the source and a
//!      [`ServiceSchema`] (macros + provider declarations + the event-schema
//!      DSL — the fixed, service-provided inputs) and does syntax + macro
//!      expansion. No action schema is needed here.
//!   2. [`ParsedPolicySet::lower`] takes the parsed set and a
//!      [`PolicySchema`] (the action schema, which typically arrives later)
//!      and produces a [`LoweredPolicySet`]: it derives the event schema
//!      against the action schema, lowers to Cedar, and *augments* the schema
//!      with the `context.<id>` fields the lowered policies reference.
//!
//! The augmented Cedar schema is folded into the [`LoweredPolicySet`] and
//! reached via [`LoweredPolicySet::cedar_schema`].
//!
//! A `LoweredPolicySet` is opaque. Its compiled Cedar artifacts are reachable
//! through accessors for interop with the `cedar-policy` crate and with
//! a Cedar policy store: [`as_cedar`](LoweredPolicySet::as_cedar)
//! yields the lowered `cedar_policy::PolicySet`,
//! [`cedar_schema`](LoweredPolicySet::cedar_schema) the augmented
//! `cedar_policy::Schema`, and
//! [`is_self_contained_cedar`](LoweredPolicySet::is_self_contained_cedar)
//! reports whether those artifacts fully reproduce the policy's semantics in
//! Cedar (i.e. the policy hoisted no temporal / provider fields that only
//! Dogwood can compute). The hoisted-leaf and rule mappings are exposed via
//! [`temporal_fields`](LoweredPolicySet::temporal_fields),
//! [`provider_fields`](LoweredPolicySet::provider_fields), and
//! [`rules`](LoweredPolicySet::rules) / [`rule_ref`](LoweredPolicySet::rule_ref).

use crate::api::{self, Error, EventSignature, Lowered, Parsed, ProviderField, TemporalField};
use crate::authorize::DogwoodRuleRef;
use crate::policy_schema::PolicySchema;
use crate::service_schema::ServiceSchema;

/// A parsed, macro-expanded set of Dogwood policies — the first lowering
/// phase, before the action schema is applied.
///
/// Produced by [`ParsedPolicySet::parse`]; lowered to a [`LoweredPolicySet`]
/// by [`ParsedPolicySet::lower`]. It carries the [`ServiceSchema`] it was
/// parsed against, so `lower` needs only the [`PolicySchema`].
///
/// `Debug` is provided for test output; the set is otherwise opaque (no
/// equality — comparing parsed sets would expose the surface representation
/// as a stability contract).
#[derive(Debug)]
pub struct ParsedPolicySet {
    parsed: Parsed,
}

impl ParsedPolicySet {
    /// **Phase 1** — parse and macro-expand Dogwood `source` against
    /// `service_schema` (macros + provider declarations + event-schema DSL).
    ///
    /// This is the schema-independent half: it catches syntax, macro, and
    /// structural errors, but not schema-dependent ones (unknown attributes,
    /// type errors, pin correlation) — those are inherently
    /// [`lower`](ParsedPolicySet::lower) / [`Validator`](crate::Validator)
    /// concerns, because they need the action schema.
    ///
    /// Returns [`Error`] on a syntax / macro failure.
    pub fn parse(source: &str, service_schema: &ServiceSchema) -> Result<ParsedPolicySet, Error> {
        Ok(ParsedPolicySet {
            parsed: api::parse(source, service_schema)?,
        })
    }

    /// **Phase 2** — lower this parsed set to Cedar against `policy_schema`
    /// (the action schema).
    ///
    /// Derives the event schema against the action schema, lowers the policies
    /// to Cedar, and augments the schema with the hoisted `context.<id>`
    /// fields; the augmented Cedar schema is retained on the returned
    /// [`LoweredPolicySet`] (see
    /// [`cedar_schema`](LoweredPolicySet::cedar_schema)).
    ///
    /// The emitted policy ids and hoisted field names use the default
    /// `policy_<index>` namespace. To combine several independently-lowered
    /// sets into one Cedar `PolicySet` / policy store (or to lower incrementally
    /// over a shared augmented schema), give each call a distinct namespace via
    /// [`lower_with_distincter`](ParsedPolicySet::lower_with_distincter).
    ///
    /// Returns [`Error`] on a lowering / schema failure. Type errors against
    /// the schema are *not* returned here — run
    /// [`Validator::validate`](crate::Validator::validate) for those.
    pub fn lower(&self, policy_schema: &PolicySchema) -> Result<LoweredPolicySet, Error> {
        self.reject_temporal_arrays()?;
        Ok(LoweredPolicySet {
            lowered: api::lower(&self.parsed, policy_schema, None)?,
        })
    }

    /// Like [`lower`](ParsedPolicySet::lower), but namespaces this call's
    /// synthesized policy ids and hoisted `context.<id>` field names under
    /// `distincter` (ids become `<distincter>_<index>`).
    ///
    /// Supply a **distinct** `distincter` per call when the results will be
    /// combined — e.g. lowering rules as they arrive and accreting them into a
    /// single policy store, or feeding each call's augmented schema forward
    /// as the next call's input. Distinct distincters guarantee the policy ids
    /// and the hoisted field names never collide across calls. `distincter` is
    /// **not** derived from a source `@id("…")` annotation — distinctness is the
    /// caller's decision.
    ///
    /// The `distincter` must be a valid Cedar identifier
    /// (`[_A-Za-z][_A-Za-z0-9]*`), since it is interpolated into Cedar policy
    /// ids and `context.<id>` attribute names; otherwise this returns
    /// [`Error::InvalidDistincter`].
    ///
    /// Note that the plain [`lower`](ParsedPolicySet::lower) path uses the
    /// namespace `policy`, so it is **not** automatically distinct from a call
    /// that later supplies the distincter `"policy"` — a caller mixing the two
    /// forms must pick distincters that also avoid `"policy"` if the results
    /// will be combined.
    pub fn lower_with_distincter(
        &self,
        policy_schema: &PolicySchema,
        distincter: &str,
    ) -> Result<LoweredPolicySet, Error> {
        self.reject_temporal_arrays()?;
        Ok(LoweredPolicySet {
            lowered: api::lower(&self.parsed, policy_schema, Some(distincter))?,
        })
    }

    // ─── pre-lowering diagnostics ────────────────────────────────────

    /// The number of Dogwood rules in this parsed set.
    ///
    /// Available before the action schema, so a caller can enforce an
    /// "exactly one policy per submission" rule up front:
    /// `if parsed.policy_count() != 1 { … }`. Equivalent to
    /// `self.policies().len()`, named for that common gate.
    pub fn policy_count(&self) -> usize {
        self.parsed.policies().len()
    }

    /// Iterate the parsed policies, each as an opaque [`ParsedPolicy`]
    /// diagnostic handle, in source order.
    ///
    /// These are read-only *views* for pre-lowering diagnostic and quota
    /// queries (policy count, temporal / provider usage, region gating);
    /// they do not expose Dogwood's surface AST and cannot be lowered on
    /// their own. The returned iterator is [`ExactSizeIterator`], so `.len()`
    /// is O(1) and does not construct the handles.
    pub fn policies(&self) -> impl ExactSizeIterator<Item = ParsedPolicy<'_>> + '_ {
        let service = self.parsed.service_schema();
        let dw_src = self.parsed.dw_src();
        self.parsed
            .policies()
            .iter()
            .enumerate()
            .map(move |(index, policy)| ParsedPolicy {
                policy,
                service,
                dw_src,
                index,
            })
    }

    // ─── pre-lowering rejection gates ────────────────────────────────

    /// Reject the policy set if any temporal predicate argument contains an
    /// **array constant** (e.g. `input.tags: ["secret", "pii"]`), returning
    /// an [`Error`] that points at the enclosing `temporal { … }` block.
    ///
    /// Array constants are accepted by the temporal grammar but support for
    /// them is incomplete — they are not handled correctly downstream and
    /// produce confusing errors. This check rejects them early with a clear
    /// message.
    ///
    /// Returns `Ok(())` if no temporal blocks contain array terms.
    ///
    /// # Example
    ///
    /// ```ignore
    /// let parsed = ParsedPolicySet::parse(source, &service)?;
    /// parsed.reject_temporal_arrays()?; // fails fast if arrays in temporal
    /// let lowered = parsed.lower(&policy_schema)?;
    /// ```
    pub fn reject_temporal_arrays(&self) -> Result<(), Error> {
        use crate::extension::temporal::ast::{AggExprKind, Condition, ConditionKind, Term};

        /// Check whether a term is or contains an array constant.
        fn term_has_array(term: &Term) -> bool {
            match term {
                Term::Array(_) => true,
                Term::Agg(agg) => match &agg.kind {
                    AggExprKind::Sum { body, .. } | AggExprKind::Count { body, .. } => {
                        condition_has_array(body)
                    }
                    AggExprKind::Call(_) => false,
                },
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
                ConditionKind::Tp { .. }
                | ConditionKind::Call(_)
                | ConditionKind::SigilRef { .. } => false,
                ConditionKind::Refine { base, fields, .. } => {
                    condition_has_array(base) || fields.iter().any(|arg| term_has_array(&arg.value))
                }
            }
        }

        for (_policy_idx, policy) in self.parsed.policies().iter().enumerate() {
            for (block_idx, temporal_block) in policy.temporal_conditions().into_iter().enumerate()
            {
                if condition_has_array(temporal_block) {
                    // Point the error at the temporal block's span.
                    let span = policy.temporal_block_spans().into_iter().nth(block_idx);
                    let message = format!(
                        "temporal predicate arguments cannot contain array constants \
                         (e.g. `field: [\"a\", \"b\"]`); use scalar values or \
                         `context` field references instead"
                    );
                    let raw = crate::error::RawCedarifyError { message, span };
                    return Err(crate::api::cedarify_error(raw, self.parsed.dw_src()));
                }
            }
        }
        Ok(())
    }
}

/// An opaque, read-only view of one parsed Dogwood policy, for answering
/// diagnostic and quota questions *about* a policy before the action schema
/// is available — without exposing Dogwood's surface AST.
///
/// Produced by [`ParsedPolicySet::policies`]. Every query is a fact about a
/// successful parse (parsing already succeeded, so nothing here is fallible),
/// computed by a lightweight walk of the policy's macro-expanded condition
/// trees on demand.
#[derive(Debug, Clone, Copy)]
pub struct ParsedPolicy<'a> {
    policy: &'a crate::ast::Policy,
    /// The set's service schema — its provider declarations back
    /// [`undeclared_providers`](ParsedPolicy::undeclared_providers).
    service: &'a ServiceSchema,
    /// The shared `.dw` source, so
    /// [`provider_invocations`](ParsedPolicy::provider_invocations) can build a
    /// self-rendering [`Error`] from an internal span-only argument error.
    dw_src: &'a std::sync::Arc<str>,
    index: usize,
}

impl<'a> ParsedPolicy<'a> {
    /// This policy's 0-based position in the set (source order) — the same
    /// index the lowered rule takes in [`LoweredPolicySet::rules`].
    pub fn index(&self) -> usize {
        self.index
    }

    // ── temporal ──────────────────────────────────────────────────────

    /// The number of `temporal { … }` blocks in this policy — one per
    /// temporal leaf, i.e. per hoisted `context.<id>` temporal field the
    /// lowered policy would reference. This is the unit a per-policy
    /// temporal quota is measured in.
    pub fn temporal_count(&self) -> usize {
        self.policy.temporal_block_count()
    }

    /// Whether this policy contains any `temporal { … }` block
    /// (`temporal_count() > 0`). Use for a region gate on temporal support.
    pub fn uses_temporal(&self) -> bool {
        self.temporal_count() > 0
    }

    /// The parsed condition of each `temporal { … }` block in this policy, in
    /// source order — one per block counted by
    /// [`temporal_count`](ParsedPolicy::temporal_count). A read-only view of
    /// the authored (pre-lowering, macro-expanded) temporal AST via
    /// [`temporal_ast`](crate::temporal_ast), for structural diagnostics that
    /// need no action schema. The condition is the block body; its inner spans
    /// are block-relative (see [`Temporal`](crate::TemporalField)).
    pub fn temporal_conditions(
        &self,
    ) -> impl Iterator<Item = &'a crate::temporal_ast::Condition> + use<'a> {
        self.policy.temporal_conditions().into_iter()
    }

    // ── information providers ───────────────────────────────────────────

    /// The number of information-provider invocation sites in this policy
    /// (every `Ns::Fn(…)` call, counted with multiplicity).
    pub fn provider_count(&self) -> usize {
        self.policy.provider_invocation_names().len()
    }

    /// Whether this policy invokes any information provider
    /// (`provider_count() > 0`). Use for a region gate on provider support.
    pub fn uses_providers(&self) -> bool {
        self.provider_count() > 0
    }

    /// The information-provider invocations in this policy, by declaration
    /// key (`Ns::Fn`), in source order. Duplicates are preserved (collect
    /// into a `BTreeSet` for the distinct set — the "which providers are
    /// actually invoked" observability query). Recognized structurally (a
    /// namespace-qualified call), independent of whether the name is declared.
    pub fn provider_invocations(&self) -> impl Iterator<Item = String> {
        self.policy.provider_invocation_names().into_iter()
    }

    /// The subset of [`provider_invocations`](ParsedPolicy::provider_invocations)
    /// whose name is **not** declared in the [`ServiceSchema`] this set was
    /// parsed against, in source order with multiplicity.
    ///
    /// An undeclared name is either a typo or a provider not available in this
    /// configuration/region; Dogwood cannot tell which (it has no global
    /// catalog), so the caller disambiguates against its own. This is the same
    /// fact the validation pass reports as an error, surfaced early as a
    /// neutral query so a caller can fail fast — or craft a region-specific
    /// message — before lowering. It does **not** replace the validation-pass
    /// check, which remains authoritative for the plain `parse → lower →
    /// validate` path.
    pub fn undeclared_providers(&self) -> impl Iterator<Item = String> {
        let declared = self
            .service
            .provider_declarations()
            .map(|d| d.names())
            .unwrap_or_default();
        self.policy
            .provider_invocation_names()
            .into_iter()
            .filter(move |name| !declared.contains(name))
    }

    // ── scope ───────────────────────────────────────────────────────────

    /// This policy's scope (`principal, action, resource`) as a Dogwood-owned
    /// [`PolicyScope`](crate::policy_view::PolicyScope) view.
    ///
    /// A pre-lowering, read-only projection of the policy head — the analog of
    /// reading a `cedar_policy` policy's three scope constraints, but available
    /// before the action schema. The entity leaves are the already-public
    /// [`cedar_policy::EntityUid`](crate::cedar::EntityUid) /
    /// [`EntityTypeName`](cedar_policy::EntityTypeName), and a template slot
    /// (`?principal` / `?resource`) reads as `None` — so no `cedar-policy-core`
    /// or Dogwood-internal AST type is exposed. See [`PolicyScope`](crate::policy_view::PolicyScope).
    pub fn scope(&self) -> crate::policy_view::PolicyScope {
        crate::policy_view::PolicyScope::from_scope(&self.policy.scope)
    }

    // ── information-provider invocations, with arguments ──────────────────

    /// The information-provider invocations in this policy as structured
    /// [`Invocation`](crate::Invocation)s — each carrying its declaration key
    /// (`Ns::Fn`, via [`Invocation::key`](crate::Invocation::key)) **and its
    /// resolved argument list** ([`Arg`](crate::Arg)s) — in source order, with
    /// multiplicity.
    ///
    /// This is the argument-bearing companion to
    /// [`provider_invocations`](ParsedPolicy::provider_invocations): where that
    /// yields only the keys, this exposes what each site passes in. The
    /// arguments are extracted through the exact conversion lowering uses, so
    /// they match what would be hoisted and evaluated (an attribute path rooted
    /// at `context`/`principal`/`resource`, a string/integer/bool/`decimal(…)`
    /// literal, or a set of those).
    ///
    /// Fallible for that same reason: an argument outside the provider-argument
    /// grammar (arbitrary arithmetic, an `if`, …) is reported here as the same
    /// self-rendering [`Error`] lowering would raise, pointing at the offending
    /// call — rather than being silently dropped or reshaped. Recognized
    /// structurally, matching the name-only accessors; a method-chained
    /// invocation (`Ns::Fn(x).m()`) is captured once at its base call, without
    /// the trailing method chain.
    pub fn provider_invocations_with_args(
        &self,
    ) -> Result<Vec<crate::extension::provider::ast::Invocation>, Error> {
        self.policy
            .provider_invocations()
            .map_err(|e| crate::api::cedarify_error(e, self.dw_src))
    }
}

/// A parsed and lowered set of Dogwood policies.
///
/// Produced by [`ParsedPolicySet::lower`] (or the one-call
/// [`LoweredPolicySet::from_str`] shortcut); consumed by
/// [`Validator::validate`](crate::Validator::validate) and
/// [`Authorizer::new`](crate::Authorizer::new).
///
/// `Debug` is provided for test output; the set is otherwise opaque (no
/// equality — equating compiled Cedar artifacts would freeze the internal
/// representation as a stability contract, and a `cedar_policy::Schema` has no
/// `PartialEq` of its own anyway).
#[derive(Debug)]
pub struct LoweredPolicySet {
    lowered: Lowered,
}

impl LoweredPolicySet {
    /// Parse and lower Dogwood `source` in one call, against a
    /// [`ServiceSchema`] and a [`PolicySchema`].
    ///
    /// Dogwood's analog of `cedar_policy::PolicySet::from_str`. It is the
    /// fused form of [`ParsedPolicySet::parse`] followed by
    /// [`ParsedPolicySet::lower`] — reach for the two-phase API directly when
    /// the action schema arrives later than the source, or to lower one parsed
    /// set against several action schemas.
    ///
    /// Because the extra schema arguments cannot fit the `std::str::FromStr`
    /// trait, this is an inherent method named `from_str` (call it as
    /// `LoweredPolicySet::from_str(src, &service, &policy)`, not `src.parse()`).
    ///
    /// Returns [`Error`] on a syntax / macro / lowering failure. Type errors
    /// against the schema are *not* returned here — run
    /// [`Validator::validate`](crate::Validator::validate) for those.
    #[allow(clippy::should_implement_trait)]
    pub fn from_str(
        source: &str,
        service_schema: &ServiceSchema,
        policy_schema: &PolicySchema,
    ) -> Result<LoweredPolicySet, Error> {
        ParsedPolicySet::parse(source, service_schema)?.lower(policy_schema)
    }

    /// Borrow the lowered Cedar policies — a real `cedar_policy::PolicySet`.
    ///
    /// This is the artifact to hand to the `cedar-policy` crate directly, or
    /// (rendered to policy text) to a Cedar policy store. See
    /// [`is_self_contained_cedar`](LoweredPolicySet::is_self_contained_cedar)
    /// for when these policies reproduce Dogwood semantics on their own.
    pub fn as_cedar(&self) -> &cedar_policy::PolicySet {
        &self.lowered.policies
    }

    /// Borrow the augmented Cedar schema — the action schema plus the hoisted
    /// `context.<id>` fields the lowered policies reference. This is the
    /// schema Cedar's validator needs to typecheck the
    /// policies from [`as_cedar`](LoweredPolicySet::as_cedar).
    pub fn cedar_schema(&self) -> &cedar_policy::Schema {
        &self.lowered.augmented_schema
    }

    /// The augmented Cedar schema as **`.cedarschema` source text** — the
    /// action schema plus the hoisted `context.<id>` fields the lowered policies
    /// reference.
    ///
    /// This is the text form, companion to [`cedar_schema`](LoweredPolicySet::cedar_schema)
    /// (the opaque `cedar_policy::Schema`) and
    /// [`cedar_schema_json`](LoweredPolicySet::cedar_schema_json) (the Cedar JSON
    /// schema form). Unlike a `cedar_policy::Schema` — which is a compiled,
    /// lossy form with no serializer of its own — this is round-trippable: a
    /// consumer reproducing the decision loop can validate their computed
    /// context against it, and it can seed a subsequent lowering via
    /// [`PolicySchema::from_cedarschema_str`](crate::PolicySchema::from_cedarschema_str)
    /// (incremental / feed-forward lowering — give each such `lower` call a
    /// distinct namespace via
    /// [`lower_with_distincter`](ParsedPolicySet::lower_with_distincter) so the
    /// carried and new hoisted fields do not collide).
    ///
    /// Serialized on demand from the retained schema fragment; returns
    /// [`Error`] on a serialization failure.
    pub fn cedar_schema_str(&self) -> Result<String, Error> {
        self.lowered
            .augmented_schema_fragment
            .to_cedarschema()
            .map_err(|e| Error::SchemaSerialize(e.to_string()))
    }

    /// The augmented Cedar schema serialized to the **Cedar JSON schema form**
    /// (for compatibility with Cedar-based authorization services).
    ///
    /// [`cedar_schema`](LoweredPolicySet::cedar_schema) returns a
    /// `cedar_policy::Schema`, which has no JSON serializer of its own; this
    /// emits JSON directly from the retained schema fragment. The result
    /// typechecks the policies from [`as_cedar`](LoweredPolicySet::as_cedar),
    /// including the hoisted `context.<id>` fields.
    pub fn cedar_schema_json(&self) -> Result<String, Error> {
        self.lowered
            .augmented_schema_fragment
            .to_json_string()
            // `to_json_string` yields a `SchemaError`, which converts into a
            // `CedarSchemaError` (its `Schema` variant), so the JSON-emit
            // failure rides the same self-rendering channel as other schema errors.
            .map_err(|e| Error::CedarSchema(Box::new(e.into())))
    }

    /// Whether the compiled Cedar artifacts are *self-contained*: `true` iff
    /// lowering hoisted no temporal or provider `context.<id>` fields, so the
    /// policies from [`as_cedar`](LoweredPolicySet::as_cedar) and the schema
    /// from [`cedar_schema`](LoweredPolicySet::cedar_schema) fully reproduce
    /// this policy's semantics in plain Cedar / a policy store with no extra context.
    ///
    /// When `false`, the policy uses `temporal { … }` and/or `provider { … }`
    /// clauses: the policy store can still evaluate the exported policies, but each
    /// `IsAuthorized` call must be supplied the hoisted `context.<id>` values
    /// — and computing those is Dogwood's temporal monitor / provider
    /// evaluation. In that case Dogwood produces the enriched context and the policy store
    /// performs the final Cedar decision.
    pub fn is_self_contained_cedar(&self) -> bool {
        self.lowered.temporal.is_empty() && self.lowered.providers.is_empty()
    }

    // ─── hoisted-leaf and rule mappings ──────────────────────────────

    /// The temporal leaves hoisted out of the policies: one per `temporal { … }`
    /// leaf, each carrying its generated `context.<id>` field name, its rule's
    /// action scope, and the temporal condition to evaluate. A consumer
    /// reimplementing the decision loop (rather than using [`Authorizer`](crate::Authorizer))
    /// computes each leaf's boolean and binds it into `context.<id>`.
    pub fn temporal_fields(&self) -> impl Iterator<Item = &TemporalField> {
        // The relativized (executable) leaves — identical to the authored
        // ones unless the event schema declares a universal symmetric pin
        // (see `event_schema::relativize`). A consumer evaluating leaves
        // must see the same artifact the built-in engines do.
        self.lowered.temporal_rewritten.iter()
    }

    /// The **non-relativized** hoisted temporal leaves — the authored leaves
    /// (post pin injection) *without* the pin-relativization rewrite. These are
    /// the leaves a **partitioning** temporal engine evaluates: paired with
    /// [`partition_keys`](LoweredPolicySet::partition_keys), a plain leaf run
    /// within a per-key partition computes the same verdict the relativized leaf
    /// ([`temporal_fields`](LoweredPolicySet::temporal_fields)) computes over the
    /// global trace.
    ///
    /// A reimplementer driving the decision loop themselves uses this **only** if
    /// they partition history by [`partition_keys`](LoweredPolicySet::partition_keys);
    /// evaluating these over an unpartitioned (global) trace computes the wrong
    /// (cross-key) verdicts. When [`partition_keys`](LoweredPolicySet::partition_keys)
    /// is empty these are identical to [`temporal_fields`](LoweredPolicySet::temporal_fields).
    pub fn nonrelativized_temporal_fields(&self) -> impl Iterator<Item = &TemporalField> {
        self.lowered.temporal.iter()
    }

    /// The partition keys derived from the event schema's universal symmetric
    /// pins: the fields a partitioning temporal engine routes each event's
    /// monitor/trace by. Empty when the schema declares no universal symmetric
    /// pin (so partitioned and relativized evaluation coincide, and there is
    /// nothing to partition on).
    pub fn partition_keys(&self) -> &[crate::engine::PartitionKey] {
        &self.lowered.partition_keys
    }

    /// The information-provider leaves hoisted out of the policies: one per
    /// hoisted provider invocation, each carrying its generated
    /// `context.providers.<id>` field name, its action, the invocation, and
    /// (if declared) its resolved declaration. A consumer reimplementing the
    /// decision loop computes each provider's value and binds it under
    /// `context.providers.<id>`.
    pub fn provider_fields(&self) -> impl Iterator<Item = &ProviderField> {
        self.lowered.providers.iter()
    }

    /// The derived event signatures this policy set's event schema produces —
    /// one per `(action, kind)` the schema derives, each with its declared
    /// **leaf** field paths and types.
    ///
    /// This is the event schema's *derived* view (`...inputs(A)` /
    /// `...outputs(A)` spliced against the action schema, plus every
    /// schema-injected field), so a signature's fields include ones **not** in
    /// the action's Cedar `context`: the reserved `callerPrincipal` /
    /// `callerResource` / `requestId`, and any custom injected or pinned
    /// fields the event schema declares. Each field is a scalar leaf (nested
    /// records flattened to dotted paths, e.g. `meta.session.id`); groups
    /// (`input` alone) are not yielded.
    ///
    /// A client that *reads* events matches fields dynamically and needs no
    /// such enumeration. A client that **validates** inbound events (e.g.
    /// rejecting one that carries a field the schema does not declare),
    /// **constructs** events (test traces, generators), or otherwise
    /// introspects the event surface uses this to see every field an event of
    /// a given kind may carry. Keyed access is a filter on top:
    /// `event_signatures().filter(|s| s.action() == "Login" && s.kind() == "request")`.
    pub fn event_signatures(&self) -> impl Iterator<Item = EventSignature> + '_ {
        self.lowered.event_signatures()
    }

    /// The Dogwood rules in this set, each as a [`DogwoodRuleRef`] pairing the
    /// rule's 0-based source index with the synthesized Cedar policy id it was
    /// lowered to (the id the policy store / Cedar stores it under, and names it by in a
    /// decision). Use [`rule_ref`](LoweredPolicySet::rule_ref) to map a Cedar
    /// policy id from a decision back to its rule.
    pub fn rules(&self) -> impl Iterator<Item = DogwoodRuleRef> + '_ {
        self.lowered
            .rule_ids
            .iter()
            .enumerate()
            .map(|(rule_index, id)| DogwoodRuleRef {
                rule_index,
                cedar_policy_id: id.clone(),
            })
    }

    /// Map a Cedar policy id (as named in an authorization decision, or the id
    /// a policy is stored under) back to the originating Dogwood rule. Returns
    /// `None` if no rule in this set lowered to that id.
    pub fn rule_ref(&self, cedar_policy_id: &str) -> Option<DogwoodRuleRef> {
        self.lowered
            .rule_ids
            .iter()
            .position(|id| id == cedar_policy_id)
            .map(|rule_index| DogwoodRuleRef {
                rule_index,
                cedar_policy_id: cedar_policy_id.to_string(),
            })
    }

    /// The event kinds this policy set treats as **decision points** — the
    /// kinds for which authorization runs and yields a verdict. Any other kind
    /// is history-only: it updates temporal state but produces no decision.
    ///
    /// Determined by the event schema's `decision` flags (see the event-schema
    /// DSL). A consumer reimplementing the decision loop must gate on this:
    /// only run a decision for an event whose kind
    /// [`is_decision_kind`](LoweredPolicySet::is_decision_kind) — this is
    /// exactly the check [`Authorizer::is_authorized`](crate::Authorizer::is_authorized)
    /// makes before returning `Some`/`None`.
    pub fn decision_kinds(&self) -> impl Iterator<Item = &str> {
        self.lowered.decision_kinds.iter().map(String::as_str)
    }

    /// Whether `kind` is a decision-point event kind (see
    /// [`decision_kinds`](LoweredPolicySet::decision_kinds)). A parallel
    /// decision loop runs authorization for an event iff this returns `true`.
    pub fn is_decision_kind(&self, kind: &str) -> bool {
        self.lowered.decision_kinds.contains(kind)
    }

    // ─── crate-internal accessors ────────────────────────────────────

    /// Borrow the lowered artifacts (for [`Validator`](crate::Validator)).
    pub(crate) fn lowered(&self) -> &Lowered {
        &self.lowered
    }

    /// Consume into the lowered artifacts (for [`Authorizer`](crate::Authorizer)).
    pub(crate) fn into_lowered(self) -> Lowered {
        self.lowered
    }
}
