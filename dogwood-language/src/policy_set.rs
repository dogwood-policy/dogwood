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
use crate::extension::temporal::construct_counts::TemporalConstructCounts;
use crate::policy_schema::PolicySchema;
use crate::service_schema::ServiceSchema;

/// A validated distincter: a string that is a Cedar identifier
/// (`[_A-Za-z][_A-Za-z0-9]*`), with nothing around it (no white space, no
/// comment).
///
/// Construct one with [`str::parse`] or [`TryFrom`]; a malformed string is
/// [`Error::InvalidDistincter`].
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Distincter(String);

impl Distincter {
    /// The distincter as given.
    pub fn as_str(&self) -> &str {
        &self.0
    }
}

impl std::str::FromStr for Distincter {
    type Err = Error;

    fn from_str(s: &str) -> Result<Self, Error> {
        // Cedar's parser reads an identifier with white space and comments
        // around it, which the distincter would keep (`" pad"` named rules
        // `" pad_0"`), so the string must be the identifier alone.
        if is_bare_identifier(s) && s.parse::<cedar_policy_core::ast::AnyId>().is_ok() {
            Ok(Distincter(s.to_string()))
        } else {
            Err(Error::InvalidDistincter(s.to_string()))
        }
    }
}

/// Whether `s` is `[_A-Za-z][_A-Za-z0-9]*`.
fn is_bare_identifier(s: &str) -> bool {
    let mut chars = s.chars();
    chars
        .next()
        .is_some_and(|c| c == '_' || c.is_ascii_alphabetic())
        && chars.all(|c| c == '_' || c.is_ascii_alphanumeric())
}

/// Why a string is not a distincter, for [`Error::InvalidDistincter`]'s message.
pub(crate) fn distincter_problem(s: &str) -> &'static str {
    if s != s.trim() && is_bare_identifier(s.trim()) {
        "must be a Cedar identifier ([_A-Za-z][_A-Za-z0-9]*), without white space around it"
    } else {
        "must be a Cedar identifier ([_A-Za-z][_A-Za-z0-9]*)"
    }
}

impl TryFrom<&str> for Distincter {
    type Error = Error;

    fn try_from(s: &str) -> Result<Self, Error> {
        s.parse()
    }
}

impl TryFrom<String> for Distincter {
    type Error = Error;

    fn try_from(s: String) -> Result<Self, Error> {
        s.parse()
    }
}

impl AsRef<str> for Distincter {
    fn as_ref(&self) -> &str {
        &self.0
    }
}

impl std::fmt::Display for Distincter {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(&self.0)
    }
}

/// Where the **stable policy ids** of a parsed set come from. Chosen with
/// [`ParsedPolicySet::with_ids`]; the default is [`Positional`](IdSource::Positional).
///
/// A stable id names a rule across versions of its policy set: it survives
/// reorders, insertions and removals of other rules, edits of the rule itself,
/// and recompiles. Positions do not. With an id source other than
/// `Positional`, lowering emits the stable id as the rule's Cedar `PolicyId`
/// (prefixed `<distincter>/<id>` under a distincter), so every decision names
/// its supporting policies by their stable ids, and each rule also carries a
/// content [revision](crate::PolicyRef::revision).
///
/// Ids use the portable alphabet `[A-Za-z0-9_.:-]`, 1 to 128 characters (UUIDs,
/// policy-store ids and dotted names fit). `/` is reserved for the distincter
/// prefix. Ids must be unique within the parsed set.
///
/// Stable ids change only the emitted Cedar policy ids. The hoisted
/// `context.<rule_key>__temporal_<j>` / `<rule_key>_p_<j>` field names stay
/// positional (`policy_<k>…`, or `<distincter>_<k>…`) under every id source,
/// because consumers bind and store them by name; see the
/// [`TemporalField::content_hash`](crate::TemporalField::content_hash) for a
/// position-free name of a leaf.
#[derive(Debug, Clone, PartialEq, Eq, Default)]
#[non_exhaustive]
pub enum IdSource {
    /// Today's behavior: rule `k` is named by its position, `policy_<k>` (or
    /// `<distincter>_<k>`). Positional ids silently name a different rule after
    /// a reorder.
    #[default]
    Positional,
    /// Each policy's `@id("…")` annotation is its id. A policy without an `@id`
    /// (or with an `@id` that has no value), an invalid id, and two policies
    /// with one id are all rejected ([`Error::PolicyId`]).
    Annotation,
    /// The caller supplies the ids, one per policy in source order:
    /// `ids[k]` names the `k`-th policy (the policy store's record id, for
    /// example). The length must equal the policy count; ids must be valid and
    /// unique. `@id` annotations are ignored.
    Explicit(Vec<String>),
}

/// **Phase 2** for several parsed sets, each under its own distincter, into
/// one [`LoweredPolicySet`].
///
/// Each entry is `(parsed set, Distincter)`. Every entry is lowered
/// independently against `policy_schema` and keeps the ids that call mints:
/// `lower_many(&[(&p, d)], s)` is `p.lower_with_distincter(s, d.as_str())`.
/// The result holds every entry's policies, leaves, and rules in input order
/// ([`DogwoodRuleRef::rule_index`] is a position in the merged set),
/// `policy_schema` augmented once with every entry's hoisted fields, and the
/// event schema derived from `policy_schema`. Each entry's validation findings
/// render against its own text.
///
/// An entry given stable ids ([`ParsedPolicySet::with_ids`]) emits each rule
/// under the Cedar policy id `<distincter>/<id>`, so a system rule keeps one id
/// in every set it is merged into, and the prefixes keep entries apart.
///
/// Every entry must have been parsed with a clone of one [`ServiceSchema`];
/// this is checked by identity, not structure.
///
/// Returns, before lowering anything, [`Error::DuplicateDistincter`] for a
/// repeated distincter, [`Error::NoPolicies`] for an empty `policies`, and
/// [`Error::MismatchedServiceSchema`] for the first entry parsed with a
/// different `ServiceSchema`.
///
/// Each entry is lowered under the node budget it was parsed with
/// ([`ParseOptions::max_nodes`](crate::ParseOptions::max_nodes)), and each
/// entry's budget covers that entry's temporal leaves alone: there is no
/// budget across entries.
///
/// [`LoweredPolicySet::from_many_str`] is the one-call form over policy text.
pub fn lower_many(
    policies: &[(&ParsedPolicySet, Distincter)],
    policy_schema: &PolicySchema,
) -> Result<LoweredPolicySet, Error> {
    // The Lean frontend checks the distincters itself; the Rust frontend's check
    // runs first, as it always has.
    let rust_frontend = policies
        .first()
        .is_none_or(|(p, _)| !p.parsed.service_schema().frontend().runs_lean());
    if rust_frontend {
        api::check_distincters(policies.iter().map(|(_, d)| d))?;
    }
    let Some((first, _)) = policies.first() else {
        return Err(Error::NoPolicies);
    };
    let service_schema = first.parsed.service_schema();
    if let Some(i) = policies
        .iter()
        .position(|(p, _)| !p.parsed.service_schema().same_instance(service_schema))
    {
        return Err(Error::MismatchedServiceSchema(i));
    }

    let entries: Vec<(&Parsed, &Distincter)> =
        policies.iter().map(|(p, d)| (&p.parsed, d)).collect();
    let (lowered, identity) = api::lower_many(&entries, policy_schema)?;
    Ok(LoweredPolicySet {
        lowered: std::sync::Arc::new(lowered),
        identity: std::sync::Arc::new(identity),
        policy_schema: Some(std::sync::Arc::new(policy_schema.clone())),
    })
}

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
    pub(crate) parsed: Parsed,
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
    ///
    /// Parses at the default [`ParseOptions`](crate::ParseOptions); see
    /// [`parse_with`](ParsedPolicySet::parse_with).
    pub fn parse(source: &str, service_schema: &ServiceSchema) -> Result<ParsedPolicySet, Error> {
        Self::parse_with(source, service_schema, &crate::ParseOptions::default())
    }

    /// [`parse`](ParsedPolicySet::parse) under `options`.
    ///
    /// [`ParseOptions::max_nodes`](crate::ParseOptions::max_nodes) bounds the
    /// nodes macro expansion may create for this whole set (exceeding it is
    /// [`Error::Macro`]), and, because the set remembers its options, the
    /// nodes every later lowering of it ([`lower`](ParsedPolicySet::lower),
    /// [`lower_with_distincter`](ParsedPolicySet::lower_with_distincter),
    /// [`lower_many`]) may create for this set's temporal leaves (exceeding it
    /// is [`Error::Cedarify`]). A caller who raises it owns the memory and
    /// time the larger trees need.
    /// [`ParseOptions::max_depth`](crate::ParseOptions::max_depth) bounds the
    /// source's nesting as the generated parsers see it, the measured depth
    /// of every finished tree, and the measured depth of every macro
    /// expansion; exceeding it is [`Error::Parse`] or
    /// [`Error::Macro`]. At the default,
    /// [`DEFAULT_MAX_DEPTH`](crate::DEFAULT_MAX_DEPTH), that error is
    /// guaranteed to come before a stack overflow; a caller who raises the
    /// limit owns the stack that parsing, lowering, and validating the
    /// deeper trees need.
    pub fn parse_with(
        source: &str,
        service_schema: &ServiceSchema,
        options: &crate::ParseOptions,
    ) -> Result<ParsedPolicySet, Error> {
        Ok(ParsedPolicySet {
            parsed: api::parse(source, service_schema, options)?,
        })
    }

    /// Choose where this set's **stable policy ids** come from (see
    /// [`IdSource`]); opt-in, additive.
    ///
    /// With [`IdSource::Annotation`] or [`IdSource::Explicit`], every later
    /// lowering of this set ([`lower`](ParsedPolicySet::lower),
    /// [`lower_with_distincter`](ParsedPolicySet::lower_with_distincter),
    /// [`lower_many`]) emits rule `k` under its stable id instead of
    /// `policy_<k>`, and the [`Authorizer`](crate::Authorizer)'s responses
    /// report it ([`Diagnostics::determining`](crate::Diagnostics::determining)),
    /// with the policy-set version
    /// ([`Response::policy_set`](crate::Response::policy_set)).
    /// [`IdSource::Positional`] restores today's ids.
    ///
    /// The ids are checked here, before the action schema is needed: a missing
    /// or invalid `@id`, a duplicate, or an explicit list of the wrong length
    /// is [`Error::PolicyId`].
    ///
    /// ```
    /// # use dogwood_language::{IdSource, ParsedPolicySet, ServiceSchema};
    /// let src = r#"
    /// @id("allow-read")
    /// permit (principal, action, resource);
    /// "#;
    /// let parsed = ParsedPolicySet::parse(src, &ServiceSchema::defaults())?
    ///     .with_ids(IdSource::Annotation)?;
    /// assert_eq!(parsed.policies().next().unwrap().policy_id(), Some("allow-read"));
    /// # Ok::<(), dogwood_language::Error>(())
    /// ```
    pub fn with_ids(mut self, ids: IdSource) -> Result<ParsedPolicySet, Error> {
        #[cfg(feature = "lean-frontend")]
        let assigned = if self.parsed.service_schema().frontend().runs_lean() {
            let rust = || assign_ids(&self.parsed, ids.clone());
            let assigned = crate::lean_frontend::assign_ids(&self.parsed, &ids, rust)?;
            self.parsed.set_id_source(ids);
            assigned
        } else {
            assign_ids(&self.parsed, ids)?
        };
        #[cfg(not(feature = "lean-frontend"))]
        let assigned = assign_ids(&self.parsed, ids)?;
        self.parsed.set_ids(assigned);
        Ok(self)
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
    /// `policy_<index>` namespace (with stable ids from
    /// [`with_ids`](ParsedPolicySet::with_ids), the policy ids are the stable
    /// ids instead; the field names are unchanged). To combine several independently-lowered
    /// sets into one Cedar `PolicySet` / policy store (or to lower incrementally
    /// over a shared augmented schema), give each call a distinct namespace via
    /// [`lower_with_distincter`](ParsedPolicySet::lower_with_distincter).
    ///
    /// Returns [`Error`] on a lowering / schema failure. Type errors against
    /// the schema are *not* returned here — run
    /// [`Validator::validate`](crate::Validator::validate) for those.
    pub fn lower(&self, policy_schema: &PolicySchema) -> Result<LoweredPolicySet, Error> {
        let (lowered, identity) = api::lower(&self.parsed, policy_schema, None)?;
        Ok(LoweredPolicySet {
            lowered: std::sync::Arc::new(lowered),
            identity: std::sync::Arc::new(identity),
            policy_schema: Some(std::sync::Arc::new(policy_schema.clone())),
        })
    }

    /// Like [`lower`](ParsedPolicySet::lower), but namespaces this call's
    /// synthesized policy ids and hoisted `context.<id>` field names under
    /// `distincter`: rule `k` gets the id `<distincter>_<k>`, and its `j`-th
    /// temporal leaf the field `<distincter>_<k>__temporal_<j>`. With stable
    /// ids ([`with_ids`](ParsedPolicySet::with_ids)), rule `k` gets the id
    /// `<distincter>/<id>` instead; its field names are unchanged.
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
    ///
    /// **Combining sets: a whole-context read breaks once any set has a leaf.**
    /// Each call validates only its own rules. At decision time the authorizer
    /// puts *every* hoisted leaf value of the combined store into *every*
    /// request's context, whatever the action. A rule that reads `context`
    /// whole, such as `context == { input: { user: "alice" } }`, is accepted in
    /// a set without leaves, but once it shares a store with any set that has a
    /// temporal or provider leaf — on its own action or any other — the
    /// request contexts it sees carry extra attributes, so the comparison is
    /// silently `false`. Re-validating the earlier set against the final
    /// schema does **not** catch this when the new leaves target other
    /// actions. Instead, lower the sets together with [`lower_many`] and run
    /// [`Validator::validate`](crate::Validator::validate) on the result: it
    /// checks the combined set and reports a whole-context read whenever the
    /// combination has a leaf. A caller that feeds schemas forward should
    /// apply the same rule: no rule may read `context` whole in a store that
    /// has any leaf.
    ///
    /// A single-entry [`lower_many`] is the same call taking a [`Distincter`].
    pub fn lower_with_distincter(
        &self,
        policy_schema: &PolicySchema,
        distincter: &str,
    ) -> Result<LoweredPolicySet, Error> {
        let distincter: Distincter = distincter.parse()?;
        let (lowered, identity) = api::lower(&self.parsed, policy_schema, Some(&distincter))?;
        Ok(LoweredPolicySet {
            lowered: std::sync::Arc::new(lowered),
            identity: std::sync::Arc::new(identity),
            policy_schema: Some(std::sync::Arc::new(policy_schema.clone())),
        })
    }

    /// The parsed set's internal payload.
    #[cfg(all(test, feature = "lean-frontend"))]
    pub(crate) fn parsed(&self) -> &Parsed {
        &self.parsed
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
                id: self.parsed.ids().map(|ids| ids[index].as_str()),
            })
    }

    /// Informalize the whole set into semi-English: an optional preamble for
    /// the event schema's pins, then one [`Phrase`](crate::Phrase)
    /// tree per rule. With `policy_schema`, a single declared namespace is
    /// dropped from names; a schema that does not compile is treated as
    /// absent. See the `informalize` module for the translation contract.
    pub fn informalize(&self, policy_schema: Option<&PolicySchema>) -> crate::Informalization {
        let facts = schema_facts(policy_schema);
        crate::informalize::informalize_set(
            self.parsed.policies(),
            self.parsed.service_schema().event_schema(),
            &facts,
        )
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
    /// Returns `Ok(())` if no temporal blocks contain array terms. Lowering
    /// runs this check itself; call it directly only to get the error before
    /// the action schema is available.
    ///
    /// # Example
    ///
    /// ```ignore
    /// let parsed = ParsedPolicySet::parse(source, &service)?;
    /// parsed.reject_temporal_arrays()?; // fails fast if arrays in temporal
    /// let lowered = parsed.lower(&policy_schema)?;
    /// ```
    pub fn reject_temporal_arrays(&self) -> Result<(), Error> {
        api::reject_temporal_arrays(&self.parsed)
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
    /// The stable id assigned by [`ParsedPolicySet::with_ids`], if any.
    id: Option<&'a str>,
}

impl<'a> ParsedPolicy<'a> {
    /// This policy's 0-based position in the set (source order) — the same
    /// index the lowered rule takes in [`LoweredPolicySet::rules`].
    pub fn index(&self) -> usize {
        self.index
    }

    /// This policy's stable id, as assigned by
    /// [`ParsedPolicySet::with_ids`] (without any distincter prefix). `None`
    /// under the default [`IdSource::Positional`].
    pub fn policy_id(&self) -> Option<&'a str> {
        self.id
    }

    /// Whether this policy is a `permit` or a `forbid`.
    pub fn effect(&self) -> crate::cedar::Effect {
        crate::cedar::Effect::from(self.policy.effect)
    }

    /// This policy's source, re-rendered from its parsed, macro-expanded form:
    /// valid `.dw` text in which every macro is inlined and no macro reference
    /// remains. Formatting and comments are not preserved; the semantics are —
    /// re-parsing and lowering the result yields the same policy this handle
    /// describes.
    pub fn expanded_source(&self) -> String {
        crate::render::render_policy(self.policy)
    }

    /// This policy as semi-English: an [`Informalization`](crate::Informalization)
    /// holding this one rule, plus the event schema's pin preamble when the
    /// policy has a temporal clause (pins change what its look-back clauses
    /// match, so they are never left out). It reads exactly as the rule does
    /// in [`ParsedPolicySet::informalize`], which describes `policy_schema`.
    pub fn informalize(&self, policy_schema: Option<&PolicySchema>) -> crate::Informalization {
        let facts = schema_facts(policy_schema);
        crate::informalize::informalize_single(
            self.policy,
            self.index,
            self.service.event_schema(),
            &facts,
        )
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

    /// How many times each temporal operator, aggregation and `exists` appears
    /// in this policy after macro expansion, across all of its temporal blocks.
    pub fn temporal_construct_counts(&self) -> TemporalConstructCounts {
        let mut counts = TemporalConstructCounts::default();
        for condition in self.temporal_conditions() {
            counts.tally(condition);
        }
        counts
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
///
/// Cloning is cheap: a clone shares the lowered artifacts (they are immutable), so many
/// [`Authorizer`](crate::Authorizer)s, one per concurrent caller, can decide with one lowered
/// set in memory.
#[derive(Debug, Clone)]
pub struct LoweredPolicySet {
    lowered: std::sync::Arc<Lowered>,
    /// Per-rule revisions, id stability and the version hash.
    identity: std::sync::Arc<crate::identity::SetIdentity>,
    /// The policy schema the set was lowered against, as given; `None` for a set built from
    /// a Lean frontend run's output.
    policy_schema: Option<std::sync::Arc<PolicySchema>>,
}

impl LoweredPolicySet {
    /// Parse and lower Dogwood `source` in one call, against a
    /// [`ServiceSchema`] and a [`PolicySchema`].
    ///
    /// Dogwood's analog of `cedar_policy::PolicySet::from_str`. It is the
    /// fused form of [`ParsedPolicySet::parse`] followed by
    /// [`ParsedPolicySet::lower`] — reach for the two-phase API directly when
    /// the action schema arrives later than the source, or to lower one parsed
    /// set against several action schemas. For several policies, each under a
    /// [`Distincter`], use [`LoweredPolicySet::from_many_str`].
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
        Self::from_str_with(
            source,
            service_schema,
            policy_schema,
            &crate::ParseOptions::default(),
        )
    }

    /// [`from_str`](LoweredPolicySet::from_str) parsing under `options`; see
    /// [`ParsedPolicySet::parse_with`].
    pub fn from_str_with(
        source: &str,
        service_schema: &ServiceSchema,
        policy_schema: &PolicySchema,
        options: &crate::ParseOptions,
    ) -> Result<LoweredPolicySet, Error> {
        ParsedPolicySet::parse_with(source, service_schema, options)?.lower(policy_schema)
    }

    /// The fused form of [`ParsedPolicySet::parse`] on each entry then
    /// [`lower_many`]. Each entry is `(policy text, Distincter)`; the arguments
    /// are in [`from_str`](LoweredPolicySet::from_str) order. See
    /// [`lower_many`] for how ids are minted and entries merged.
    ///
    /// An empty `policies` lowers empty source: no policies over
    /// `policy_schema`. Returns the first parse error in entry order. Never
    /// returns [`Error::MismatchedServiceSchema`] or [`Error::NoPolicies`].
    pub fn from_many_str(
        policies: &[(&str, Distincter)],
        service_schema: &ServiceSchema,
        policy_schema: &PolicySchema,
    ) -> Result<LoweredPolicySet, Error> {
        Self::from_many_str_with(
            policies,
            service_schema,
            policy_schema,
            &crate::ParseOptions::default(),
        )
    }

    /// [`from_many_str`](LoweredPolicySet::from_many_str) parsing every entry
    /// under `options`; see [`ParsedPolicySet::parse_with`].
    pub fn from_many_str_with(
        policies: &[(&str, Distincter)],
        service_schema: &ServiceSchema,
        policy_schema: &PolicySchema,
        options: &crate::ParseOptions,
    ) -> Result<LoweredPolicySet, Error> {
        if policies.is_empty() {
            return ParsedPolicySet::parse_with("", service_schema, options)?.lower(policy_schema);
        }
        let parsed = policies
            .iter()
            .map(|(text, _)| ParsedPolicySet::parse_with(text, service_schema, options))
            .collect::<Result<Vec<_>, Error>>()?;
        let entries: Vec<_> = parsed
            .iter()
            .zip(policies)
            .map(|(p, (_, distincter))| (p, distincter.clone()))
            .collect();
        lower_many(&entries, policy_schema)
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

    /// The policy schema the set was lowered against, **as given**: the action schema passed to
    /// [`ParsedPolicySet::lower`] (or [`lower_with_distincter`](ParsedPolicySet::lower_with_distincter),
    /// [`lower_many`], [`LoweredPolicySet::from_str`], [`LoweredPolicySet::from_many_str`]),
    /// before lowering augmented it. The augmented schema
    /// ([`cedar_schema_json`](LoweredPolicySet::cedar_schema_json)) depends on the policies:
    /// it holds the hoisted `context.<id>` fields, the enumerated entity types the providers
    /// the policies call declare, and an action context written as a record where a field is
    /// hoisted into a context the schema names by a common type. This one does not: two sets
    /// lowered against one policy schema return the same text, whatever their policies.
    ///
    /// `None` for a set built from a Lean frontend run's output
    /// ([`frontend::lowered_from_lean`](crate::frontend::lowered_from_lean)), which does not
    /// carry the schema it was lowered against.
    pub fn policy_schema(&self) -> Option<&PolicySchema> {
        self.policy_schema.as_deref()
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

    /// **The action groups whose scope resolves to `action`**: the groups it is
    /// in, transitively, in this set's action schema, sorted by namespace and
    /// id. Empty when the schema does not declare `action`, and when `action`
    /// applies to no principal or no resource (a pure group): a group's scope
    /// resolves to its members that can receive a request, as
    /// [`TemporalField::target_actions`] does. Depends on the schemas alone, so
    /// a set lowered from no policies answers it too.
    ///
    /// The argument [`ActionScope::narrowed_to`](crate::ActionScope::narrowed_to)
    /// takes, computed once per action.
    pub fn action_groups(&self, action: &crate::ActionRef) -> Vec<crate::ActionRef> {
        use cedar_policy_core::validator::ValidatorSchema;
        use std::str::FromStr;
        let schema: &ValidatorSchema = self.lowered.augmented_schema.as_ref();
        let Ok(uid) = cedar_policy::EntityUid::from_str(&api::action_ref_uid(action)) else {
            return Vec::new();
        };
        let uid: &cedar_policy_core::ast::EntityUID = uid.as_ref();
        let appliable = schema.get_action_id(uid).is_some_and(|a| {
            a.applies_to_principals().next().is_some() && a.applies_to_resources().next().is_some()
        });
        if !appliable {
            return Vec::new();
        }
        let mut groups: Vec<crate::ActionRef> = schema
            .action_ids()
            .filter(|g| g.descendants().any(|d| d == uid))
            .map(|g| {
                let g = cedar_policy::EntityUid::from(g.name().clone());
                api::action_ref(g.type_name().namespace(), g.id().unescaped().to_owned())
            })
            .collect();
        groups.sort_by(|a, b| (&a.namespace, &a.id).cmp(&(&b.namespace, &b.id)));
        groups
    }

    /// **The temporal leaves of the rules that can apply to `action`**, each
    /// described for an evaluator of temporal fields that lowers nothing itself
    /// ([`TemporalLeafDescriptor`](crate::TemporalLeafDescriptor)): its id, the
    /// action scope it is sent under, and its condition as authored, in
    /// canonical text.
    ///
    /// The slice is a function of the set and the action alone, so the same
    /// set and action always give the same leaves in the same order: the
    /// leaves of [`nonrelativized_temporal_fields`](LoweredPolicySet::nonrelativized_temporal_fields),
    /// in that order, whose rule's scope applies to `action` by
    /// [`ActionScope::narrowed_to`](crate::ActionScope::narrowed_to) with the
    /// groups of [`action_groups`](LoweredPolicySet::action_groups), each sent
    /// under the scope it returns. A rule over an action list is sent with its
    /// scope narrowed to `action`, since a descriptor carries one action, so
    /// [`SliceError::ActionList`](crate::SliceError::ActionList) is no longer
    /// returned.
    ///
    /// Each condition is the leaf's pinned condition with the pins lowering
    /// injected taken off again: the evaluator injects them itself, from the
    /// same event schema, and gets this set's leaf back. Its text parses back
    /// to that authored condition
    /// ([`temporal_ast::parse_condition`](crate::temporal_ast::parse_condition)).
    pub fn temporal_slice(
        &self,
        action: &crate::ActionRef,
    ) -> Result<Vec<crate::api::TemporalLeafDescriptor>, crate::api::SliceError> {
        use crate::api::{SliceError, TemporalLeafDescriptor};
        let groups = self.action_groups(action);
        let mut out = Vec::new();
        for leaf in self.nonrelativized_temporal_fields() {
            let Some(scope) = leaf.action.narrowed_to(action, &groups) else {
                continue;
            };
            let authored = crate::event_schema::pin::strip_pins(
                &leaf.condition.condition,
                &self.lowered.event_schema,
            )
            .ok_or_else(|| SliceError::Pins {
                leaf: leaf.id.clone(),
            })?;
            let condition = crate::extension::temporal::text::condition_text(&authored)
                .map_err(|e| SliceError::NoText {
                    leaf: leaf.id.clone(),
                    reason: e.message().to_owned(),
                })?;
            out.push(TemporalLeafDescriptor {
                id: leaf.id.clone(),
                action: scope,
                condition,
            });
        }
        Ok(out)
    }

    /// The partition keys derived from the event schema's universal symmetric
    /// pins: the fields a partitioning temporal engine routes each event's
    /// monitor/trace by. Empty when the schema declares no universal symmetric
    /// pin (so partitioned and relativized evaluation coincide, and there is
    /// nothing to partition on).
    pub fn partition_keys(&self) -> &[crate::engine::PartitionKey] {
        &self.lowered.partition_keys
    }

    /// Build the temporal leaf map for this lowered policy set.
    ///
    /// This is equivalent to calling [`DecisionLeafMap::build`](crate::DecisionLeafMap::build)
    /// with this set's temporal fields and Cedar schema.
    pub fn leaf_map(&self) -> crate::leaf_map::DecisionLeafMap {
        crate::leaf_map::DecisionLeafMap::build(
            &self.lowered.temporal_rewritten,
            &self.lowered.augmented_schema,
        )
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

    /// Check `event` against the pin rules of its signature under `rule`, as
    /// an [`Authorizer`](crate::Authorizer) does before it ingests it: every
    /// pinned field is logged, and every field that mirrors the request holds
    /// the request's value (see [`MirrorRule`](crate::MirrorRule)). An event of
    /// no declared signature is not checked here, and
    /// [`MirrorRule::Unchecked`](crate::MirrorRule::Unchecked) accepts every
    /// event.
    ///
    /// An engine that logs events itself (a database-backed
    /// [`TemporalEngine`](crate::TemporalEngine)) runs this before the write,
    /// so that it logs what the authorizer ingests.
    pub fn check_event(
        &self,
        event: &crate::Event,
        rule: crate::MirrorRule,
    ) -> Result<(), crate::Rejection> {
        self.lowered.check_event(event, rule)
    }

    /// Check `event` as an [`Authorizer`](crate::Authorizer) built from this
    /// set with the mirror rule `rule` checks it before it ingests it, without
    /// ingesting it or changing anything. This is the one event-conformance
    /// check the authorizer runs (the specification's `Event.Conforms`,
    /// `dogwood-lean`): the event schema declares a signature for the event's
    /// action and kind, every logged declared field is a value of its declared
    /// type (an entity among them a valid entity of the schema), every required
    /// field and every pinned field is logged, and every field that mirrors the
    /// request obeys `rule` (see [`MirrorRule`](crate::MirrorRule)). Where
    /// [`check_event`](Self::check_event) checks the pin rules alone, this
    /// checks all of it.
    ///
    /// `Ok(())` exactly when the authorizer ingests the event, unless its
    /// temporal engine then fails to record it
    /// ([`Rejection::Unavailable`](crate::Rejection::Unavailable), which this
    /// method never returns). An `Err` is the
    /// [`Rejection::Nonconforming`](crate::Rejection::Nonconforming) that
    /// [`Authorizer::submit`](crate::Authorizer::submit) returns for a history
    /// event; for a decision event the authorizer instead fails the decision
    /// closed, with the error `nonconforming decision event: <reason>` and the
    /// same reason. The checks a decision makes after ingestion (a principal
    /// and a resource in scope, the request, the entity store, the providers)
    /// are not made here.
    ///
    /// The checks are built from the set on the first call (or when the first
    /// authorizer is built from it) and kept, and every clone of the set and
    /// every authorizer built from it uses the same ones.
    pub fn check_event_conformance(
        &self,
        event: &crate::Event,
        rule: crate::MirrorRule,
    ) -> Result<(), crate::Rejection> {
        self.lowered.check_event_conformance(event, rule)
    }

    /// The Cedar request and entity store an [`Authorizer`](crate::Authorizer)
    /// builds for a decision at `event`, **before** it binds the temporal
    /// leaves and the information providers.
    ///
    /// The request's principal, action and resource are the decision's, and
    /// its context holds the event's request context only: none of the hoisted
    /// `context.<leaf>` booleans and no `context.providers` record. The entity
    /// store is exactly the one the decision is authorized against: the
    /// supplied entities, validated against the augmented schema, the bare
    /// scope entities, and the schema's action entities. A `null` is absent in
    /// both.
    ///
    /// An engine that partially evaluates the policies before the temporal
    /// leaves are known (to skip leaves that cannot affect the decision, for
    /// example) uses this rather than rebuilding them, so the two stay
    /// identical. The error is the message the decision fails closed with
    /// (no principal or resource, a malformed uid, nonconforming entities, a
    /// request context group named like a hoisted leaf or `providers`).
    pub fn decision_request(
        &self,
        event: &crate::Event,
    ) -> Result<(cedar_policy::Request, cedar_policy::Entities), String> {
        crate::api::decision_request(&self.lowered, event)
    }

    /// The Dogwood rules in this set, each as a [`DogwoodRuleRef`] pairing the
    /// rule's 0-based index in this set with the synthesized Cedar policy id it was
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
            .rule_index
            .get(cedar_policy_id)
            .copied()
            .map(|rule_index| DogwoodRuleRef {
                rule_index,
                cedar_policy_id: cedar_policy_id.to_string(),
            })
    }

    // ─── stable identity ─────────────────────────────────────────────

    /// Whether every rule in this set carries a stable, owner-chosen id
    /// (each input was given an [`IdSource`] other than
    /// [`Positional`](IdSource::Positional) via [`ParsedPolicySet::with_ids`]).
    /// When `true`, the emitted Cedar policy ids are the stable ids, responses
    /// carry the policy-set version, and an unknown determining id fails a
    /// decision closed.
    pub fn has_stable_ids(&self) -> bool {
        self.identity.stable()
    }

    /// Every rule in this set as a position-free [`PolicyRef`](crate::PolicyRef)
    /// (its emitted policy id and its revision), in rule order — the same order
    /// as [`rules`](LoweredPolicySet::rules).
    pub fn policy_refs(&self) -> impl Iterator<Item = crate::PolicyRef> + '_ {
        self.lowered
            .rule_ids
            .iter()
            .enumerate()
            .map(|(k, id)| crate::PolicyRef::new(id.clone(), self.identity.revision(k).to_string()))
    }

    /// The [`PolicyRef`](crate::PolicyRef) of the rule emitted under
    /// `cedar_policy_id`, or `None` if no rule in this set has that id.
    pub fn policy_ref(&self, cedar_policy_id: &str) -> Option<crate::PolicyRef> {
        let k = self.lowered.rule_index.get(cedar_policy_id).copied()?;
        Some(crate::PolicyRef::new(
            cedar_policy_id.to_string(),
            self.identity.revision(k).to_string(),
        ))
    }

    /// This set's version hash (see [`PolicySetVersion::hash`](crate::PolicySetVersion::hash)):
    /// SHA-256 over the sorted `(policy id, revision)` pairs, the augmented
    /// Cedar schema, the decision kinds and the partition keys. Computed once,
    /// on first use.
    pub fn version_hash(&self) -> &str {
        self.identity.version_hash(&self.lowered)
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

    /// A lowered set of its artifacts and their identity (for
    /// [`frontend::lowered_from_lean`](crate::frontend::lowered_from_lean)).
    #[cfg(feature = "lean-frontend")]
    pub(crate) fn from_parts(
        lowered: Lowered,
        identity: crate::identity::SetIdentity,
    ) -> LoweredPolicySet {
        LoweredPolicySet {
            lowered: std::sync::Arc::new(lowered),
            identity: std::sync::Arc::new(identity),
            policy_schema: None,
        }
    }

    /// Consume into the lowered artifacts and their identity (for
    /// [`Authorizer`](crate::Authorizer)).
    pub(crate) fn into_parts(
        self,
    ) -> (
        std::sync::Arc<Lowered>,
        std::sync::Arc<crate::identity::SetIdentity>,
    ) {
        (self.lowered, self.identity)
    }
}

/// Resolve an [`IdSource`] against a parsed set: `None` for positional ids,
/// otherwise one validated, unique id per policy in source order.
pub(crate) fn assign_ids(parsed: &Parsed, source: IdSource) -> Result<Option<Vec<String>>, Error> {
    use crate::error::{PolicyIdError, PolicyIdErrorKind as Kind, SourceLoc};

    let policies = parsed.policies();
    let loc = |k: usize| Some(SourceLoc::new(policies[k].span, parsed.dw_src().clone()));
    let ids: Vec<String> = match source {
        IdSource::Positional => return Ok(None),
        IdSource::Annotation => policies
            .iter()
            .enumerate()
            .map(|(k, policy)| {
                let mut ids = policy.annotations.iter().filter(|a| a.key == "id");
                match (ids.next(), ids.next()) {
                    // The stable id would be one of them and Cedar's policy
                    // would keep the last: the policy must say which.
                    (Some(first), Some(second)) => Err(PolicyIdError::new(
                        Kind::RepeatedAnnotation,
                        format!(
                            "policy {k} has a second `@id` annotation, `{}` after `{}`; \
                             IdSource::Annotation takes a policy's id from its one `@id(\"…\")` \
                             annotation",
                            id_annotation_text(second),
                            id_annotation_text(first)
                        ),
                        Some(k),
                        None,
                        loc(k),
                    )),
                    (
                        Some(crate::ast::Annotation {
                            value: Some(id), ..
                        }),
                        None,
                    ) => Ok(id.clone()),
                    _ => Err(PolicyIdError::new(
                        Kind::Missing,
                        format!(
                            "policy {k} has no `@id(\"…\")` annotation, which IdSource::Annotation requires"
                        ),
                        Some(k),
                        None,
                        loc(k),
                    )),
                }
            })
            .collect::<Result<_, _>>()?,
        IdSource::Explicit(ids) => {
            if ids.len() != policies.len() {
                return Err(PolicyIdError::new(
                    Kind::CountMismatch,
                    format!(
                        "IdSource::Explicit gave {} ids for {} policies",
                        ids.len(),
                        policies.len()
                    ),
                    None,
                    None,
                    None,
                )
                .into());
            }
            ids
        }
    };

    let mut seen: std::collections::BTreeMap<&str, usize> = std::collections::BTreeMap::new();
    for (k, id) in ids.iter().enumerate() {
        crate::identity::validate_policy_id(id).map_err(|reason| {
            PolicyIdError::new(
                Kind::Invalid,
                format!(
                    "invalid policy id `{}` for policy {k}: {reason}",
                    id.escape_default()
                ),
                Some(k),
                Some(id.clone()),
                loc(k),
            )
        })?;
        if let Some(first) = seen.insert(id.as_str(), k) {
            return Err(PolicyIdError::new(
                Kind::Duplicate,
                format!("duplicate policy id `{id}`: policies {first} and {k} both use it"),
                Some(k),
                Some(id.clone()),
                loc(k),
            )
            .into());
        }
    }
    Ok(Some(ids))
}

/// An `@id` annotation as a message shows it: `@id("…")`, its value escaped,
/// or `@id` without one.
fn id_annotation_text(a: &crate::ast::Annotation) -> String {
    match &a.value {
        Some(v) => format!("@id(\"{}\")", v.escape_default()),
        None => "@id".to_string(),
    }
}

/// The schema facts the informalizer reads off an optional action schema.
fn schema_facts(policy_schema: Option<&PolicySchema>) -> crate::informalize::SchemaFacts {
    match policy_schema {
        Some(s) => crate::informalize::SchemaFacts::from_cedarschema_str(s.action_schema_src()),
        None => crate::informalize::SchemaFacts::none(),
    }
}

#[cfg(test)]
mod lower_many_tests {
    use cedar_policy::PolicySet as CedarPolicySet;

    use super::*;
    use crate::api::ActionScope;
    use crate::cedarify::{self, ContextField, ScopedAction};
    use crate::error::SourceLoc;

    const DRUPE_SCHEMA: &str = r#"
namespace Drupe {
  type ReadInput = { user: String, amount: Long };
  entity Gateway;
  entity OAuthUser = { id: String };
  action "Login" appliesTo {
    principal: [OAuthUser],
    resource: [Gateway],
    context: { input: ReadInput }
  };
  action "Read" appliesTo {
    principal: [OAuthUser],
    resource: [Gateway],
    context: { input: ReadInput }
  };
}
"#;

    const DRUPE_PARTS: [(&str, &str); 3] = [
        (
            r#"
permit ( principal, action == Drupe::Action::"Read", resource )
when temporal {
    formerly within 1h Drupe::Action::"Login"::request{ input.user: context.input.user }
};
"#,
            "alpha",
        ),
        (
            r#"
forbid ( principal, action == Drupe::Action::"Read", resource )
when temporal {
    count for (a: Long). where (
        formerly within 10m Drupe::Action::"Read"::request{ input.amount: a }
    ) > 3
};

permit ( principal, action == Drupe::Action::"Read", resource )
when { context.input.amount < 100 }
when temporal {
    previous within 1d Drupe::Action::"Login"::request{}
}
unless temporal {
    formerly within 5m Drupe::Action::"Read"::request{ input.user: "mallory" }
};
"#,
            "beta",
        ),
        (
            r#"
permit ( principal, action == Drupe::Action::"Login", resource )
when { context.input.user == "alice" };

permit ( principal, action == Drupe::Action::"Login", resource )
when temporal {
    exists (u: String). (
        formerly within 2h Drupe::Action::"Login"::request{ input.user: u }
    )
};
"#,
            "gamma",
        ),
    ];

    /// A context given as a named reference type.
    const BROKER_SCHEMA: &str = r#"
namespace Brokerage {
  type QuoteInput  = { symbol: String, qty: Long };
  type QuoteOutput = { price: decimal, filled: Bool };
  type SystemContext = { now: datetime };
  type QuoteCtx = { input: QuoteInput, output?: QuoteOutput, system: SystemContext };

  entity Gateway;
  entity Desk;
  entity Trader in [Desk] = { id: String } tags String;

  action "Trade";
  action "GetQuote" in [Action::"Trade"] appliesTo {
    principal: [Trader],
    resource: [Gateway],
    context: QuoteCtx
  };
}
"#;

    const BROKER_PARTS: [(&str, &str); 2] = [
        (
            r#"
permit ( principal, action == Brokerage::Action::"GetQuote", resource )
when temporal {
    formerly within 1h Brokerage::Action::"GetQuote"::request{ input.symbol: context.input.symbol }
};
"#,
            "sym",
        ),
        (
            r#"
forbid ( principal, action == Brokerage::Action::"GetQuote", resource )
when temporal {
    count for (q: Long). where (
        formerly within 10m Brokerage::Action::"GetQuote"::request{ input.qty: q }
    ) > 3
};
"#,
            "qty",
        ),
    ];

    fn lower_part(text: &str, schema: &PolicySchema, distincter: &str) -> Lowered {
        ParsedPolicySet::parse(text, &ServiceSchema::defaults())
            .expect("parses")
            .lower_with_distincter(schema, distincter)
            .expect("lowers")
            .into_parts()
            .0
            .pipe_unwrap()
    }

    /// The lowered set out of its `Arc` (a freshly lowered set is not shared).
    trait PipeUnwrap {
        fn pipe_unwrap(self) -> Lowered;
    }
    impl PipeUnwrap for std::sync::Arc<Lowered> {
        fn pipe_unwrap(self) -> Lowered {
            std::sync::Arc::try_unwrap(self).expect("a freshly lowered set is not shared")
        }
    }

    /// Each Cedar policy as `(id, text)`, sorted: `PolicySet::policies()` has no
    /// documented iteration order, so Cedar policies are compared as a set while
    /// Dogwood's own vectors are compared in order.
    fn sorted_policies<'a>(
        sets: impl IntoIterator<Item = &'a CedarPolicySet>,
    ) -> Vec<(String, String)> {
        let mut out: Vec<_> = sets
            .into_iter()
            .flat_map(|s| s.policies().map(|p| (p.id().to_string(), p.to_string())))
            .collect();
        out.sort();
        out
    }

    fn context_field(leaf: &TemporalField) -> ContextField {
        let action =
            |a: &crate::api::ActionRef| (a.namespace.clone().unwrap_or_default(), a.id.clone());
        ContextField {
            action: match &leaf.action {
                ActionScope::Concrete(a) => ScopedAction::Concrete(action(a)),
                ActionScope::List(v) => ScopedAction::List(v.iter().map(action).collect()),
                ActionScope::Unconstrained => ScopedAction::Unconstrained,
            },
            field_name: leaf.id.clone(),
            temporal: leaf.condition.clone(),
            target_actions: leaf.target_actions.iter().map(action).collect(),
            principal: leaf.principal.clone(),
            resource: leaf.resource.clone(),
        }
    }

    fn assert_lower_many_is_the_standalone_union(schema_src: &str, parts: &[(&str, &str)]) {
        let base = PolicySchema::from_cedarschema_str(schema_src).expect("schema");
        let service = ServiceSchema::defaults();
        let parsed: Vec<ParsedPolicySet> = parts
            .iter()
            .map(|(text, _)| ParsedPolicySet::parse(text, &service).expect("parses"))
            .collect();
        let entries: Vec<(&ParsedPolicySet, Distincter)> = parsed
            .iter()
            .zip(parts)
            .map(|(p, (_, d))| (p, d.parse().expect("distincter")))
            .collect();
        let merged = lower_many(&entries, &base).expect("lower_many").lowered;
        let alone: Vec<Lowered> = parts
            .iter()
            .map(|(text, d)| lower_part(text, &base, d))
            .collect();
        let hoisted: Vec<ContextField> = alone
            .iter()
            .flat_map(|l| {
                assert!(l.providers.is_empty(), "fixtures hoist no provider fields");
                l.temporal.iter().map(context_field)
            })
            .collect();
        let expected_schema = cedarify::augment_schema(
            cedarify::parse_base_schema(schema_src).expect("parses"),
            None,
            &Default::default(),
            &hoisted,
            &[],
        )
        .expect("augments")
        .to_cedarschema()
        .expect("serializes");
        let offsets: Vec<usize> = alone
            .iter()
            .scan(0, |n, l| {
                let at = *n;
                *n += l.rule_ids.len();
                Some(at)
            })
            .collect();
        let concat = |f: fn(&Lowered) -> Vec<usize>| -> Vec<usize> {
            alone
                .iter()
                .zip(&offsets)
                .flat_map(|(l, o)| f(l).into_iter().map(move |k| k + o))
                .collect()
        };

        let Lowered {
            policies,
            // `Schema` has no `PartialEq`; its fragment is checked below.
            augmented_schema: _,
            augmented_schema_fragment,
            temporal,
            temporal_executable,
            temporal_rewritten,
            partition_keys,
            providers,
            rule_ids,
            rule_locs,
            rule_sources,
            temporal_rules,
            provider_rules,
            event_schema,
            decision_kinds,
            // The fixtures call no providers.
            enum_names: _,
            // The fixtures read the context through its attributes.
            context_reads: _,
            // Derived from `rule_ids`.
            rule_index: _,
            // Built from the rest on first use.
            checks: _,
            // The Lean frontend's record: its findings, checked by validation.
            #[cfg(feature = "lean-frontend")]
                lean: _,
        } = std::sync::Arc::try_unwrap(merged).expect("the merged set is not shared");

        assert_eq!(
            sorted_policies([&policies]),
            sorted_policies(alone.iter().map(|l| &l.policies))
        );
        assert_eq!(
            augmented_schema_fragment
                .to_cedarschema()
                .expect("serializes"),
            expected_schema
        );
        assert_eq!(
            temporal,
            alone
                .iter()
                .flat_map(|l| l.temporal.clone())
                .collect::<Vec<_>>()
        );
        assert_eq!(
            temporal_executable,
            alone
                .iter()
                .flat_map(|l| l.temporal_executable.clone())
                .collect::<Vec<_>>()
        );
        assert_eq!(
            temporal_rewritten,
            alone
                .iter()
                .flat_map(|l| l.temporal_rewritten.clone())
                .collect::<Vec<_>>()
        );
        assert_eq!(
            providers,
            alone
                .iter()
                .flat_map(|l| l.providers.clone())
                .collect::<Vec<_>>()
        );
        assert_eq!(
            rule_ids,
            alone
                .iter()
                .flat_map(|l| l.rule_ids.clone())
                .collect::<Vec<_>>()
        );
        let loc = |l: &SourceLoc| (l.span(), l.source().to_string());
        assert_eq!(
            rule_locs.iter().map(loc).collect::<Vec<_>>(),
            alone
                .iter()
                .flat_map(|l| l.rule_locs.iter().map(loc))
                .collect::<Vec<_>>()
        );
        assert_eq!(
            rule_sources,
            alone
                .iter()
                .enumerate()
                .flat_map(|(i, l)| l.rule_sources.iter().map(move |&s| s + i))
                .collect::<Vec<_>>()
        );
        assert_eq!(temporal_rules, concat(|l| l.temporal_rules.clone()));
        assert_eq!(provider_rules, concat(|l| l.provider_rules.clone()));
        for part in &alone {
            assert_eq!(partition_keys, part.partition_keys);
            assert_eq!(event_schema, part.event_schema);
            assert_eq!(decision_kinds, part.decision_kinds);
        }
    }

    #[test]
    fn lower_many_is_the_standalone_union_over_an_inline_context() {
        assert_lower_many_is_the_standalone_union(DRUPE_SCHEMA, &DRUPE_PARTS);
    }

    #[test]
    fn lower_many_is_the_standalone_union_over_a_reference_context() {
        assert_lower_many_is_the_standalone_union(BROKER_SCHEMA, &BROKER_PARTS);
    }
}

#[cfg(test)]
mod shared_clone_tests {
    use super::*;

    const SCHEMA: &str = r#"
namespace Drupe {
  type ReadInput = { user: String };
  entity Gateway;
  entity OAuthUser;
  action "Login" appliesTo { principal: [OAuthUser], resource: [Gateway], context: { input: ReadInput } };
  action "Read" appliesTo { principal: [OAuthUser], resource: [Gateway], context: { input: ReadInput } };
}
"#;

    const POLICIES: &str = r#"
@id("a")
permit ( principal, action == Drupe::Action::"Read", resource )
when temporal { formerly within 1h Drupe::Action::"Login"::request{} };
@id("b")
forbid ( principal == Drupe::OAuthUser::"mallory", action, resource );
"#;

    /// A clone shares the lowered set (one copy in memory), and authorizers built from the
    /// original and the clone decide alike; a policy id maps back to its rule through the
    /// index.
    #[test]
    fn clones_share_the_lowered_set() {
        let service = ServiceSchema::defaults();
        let schema = PolicySchema::from_cedarschema_str(SCHEMA).unwrap();
        let set = ParsedPolicySet::parse(POLICIES, &service)
            .unwrap()
            .with_ids(IdSource::Annotation)
            .unwrap()
            .lower(&schema)
            .unwrap();
        let copy = set.clone();
        assert!(std::sync::Arc::ptr_eq(&set.lowered, &copy.lowered));
        assert!(std::sync::Arc::ptr_eq(&set.identity, &copy.identity));
        assert_eq!(set.rule_ref("b").map(|r| r.rule_index), Some(1));
        assert_eq!(
            copy.policy_ref("a").map(|r| r.id().to_string()),
            Some("a".to_string())
        );
        assert!(set.rule_ref("zz").is_none());
        let mut one = crate::Authorizer::new(set);
        let mut two = crate::Authorizer::new(copy);
        let log = r#"@1 scope(principal: Drupe::OAuthUser::"alice", resource: Drupe::Gateway::"g") Drupe::Action::"Login"::request(input: { user: "alice" }, callerPrincipal: Drupe::OAuthUser::"alice", callerResource: Drupe::Gateway::"g")
@2 scope(principal: Drupe::OAuthUser::"alice", resource: Drupe::Gateway::"g") request_context(input: { user: "alice" }) Drupe::Action::"Read"::request(input: { user: "alice" }, callerPrincipal: Drupe::OAuthUser::"alice", callerResource: Drupe::Gateway::"g")
@3 scope(principal: Drupe::OAuthUser::"mallory", resource: Drupe::Gateway::"g") request_context(input: { user: "m" }) Drupe::Action::"Read"::request(input: { user: "m" }, callerPrincipal: Drupe::OAuthUser::"mallory", callerResource: Drupe::Gateway::"g")"#;
        for e in crate::parse_trace(log).unwrap() {
            let (a, b) = (one.is_authorized(&e), two.is_authorized(&e));
            assert_eq!(
                a.as_ref().map(|r| r.decision()),
                b.as_ref().map(|r| r.decision())
            );
            assert_eq!(
                a.as_ref().map(|r| r
                    .diagnostics()
                    .reason()
                    .map(|x| x.cedar_policy_id.clone())
                    .collect::<Vec<_>>()),
                b.as_ref().map(|r| r
                    .diagnostics()
                    .reason()
                    .map(|x| x.cedar_policy_id.clone())
                    .collect::<Vec<_>>())
            );
        }
    }

    /// A lowered set keeps the policy schema it was lowered against as given, whatever its
    /// policies; its augmented schema is not that text.
    #[test]
    fn the_policy_schema_is_the_one_given() {
        let service = ServiceSchema::defaults();
        let schema = PolicySchema::from_cedarschema_str(&format!("\u{FEFF}{SCHEMA}")).unwrap();
        assert_eq!(schema.cedarschema_str(), SCHEMA);
        let set = LoweredPolicySet::from_str(POLICIES, &service, &schema).unwrap();
        let none = LoweredPolicySet::from_str("", &service, &schema).unwrap();
        let many =
            LoweredPolicySet::from_many_str(&[(POLICIES, "p".parse().unwrap())], &service, &schema)
                .unwrap();
        for s in [&set, &none, &many, &set.clone()] {
            assert_eq!(
                s.policy_schema().map(PolicySchema::cedarschema_str),
                Some(SCHEMA)
            );
        }
        assert_ne!(
            set.cedar_schema_json().unwrap(),
            none.cedar_schema_json().unwrap(),
            "the augmented schemas differ: one holds the hoisted field"
        );
    }

    /// The runtime conformance checks are built once per lowered set: a clone,
    /// `check_event_conformance`, and an authorizer built from either all use
    /// the same ones.
    #[test]
    fn clones_and_authorizers_share_one_set_of_runtime_checks() {
        let service = ServiceSchema::defaults();
        let schema = PolicySchema::from_cedarschema_str(SCHEMA).unwrap();
        let set = LoweredPolicySet::from_str(POLICIES, &service, &schema).unwrap();
        let copy = set.clone();
        let event = crate::Event::builder("Drupe::Action::Login", "error").build();
        assert!(
            copy.check_event_conformance(&event, crate::MirrorRule::Strict)
                .is_err()
        );
        let checks: *const crate::conformance::RuntimeChecks = set.lowered().runtime_checks();
        assert!(std::ptr::eq(copy.lowered().runtime_checks(), checks));
        let authorizer = crate::Authorizer::new(copy);
        assert!(std::ptr::eq(authorizer.lowered().runtime_checks(), checks));
        // `Debug` names the cache without printing the checks it holds.
        assert!(format!("{set:?}").contains("checks: RuntimeChecksCache"));
    }
}
