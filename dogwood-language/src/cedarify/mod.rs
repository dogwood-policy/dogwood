//! `cedarify` — lower a Dogwood [`PolicySet`] to Cedar.
//!
//! This is the keystone of the frontend: validation and authorization
//! are both defined in terms of the Cedar produced here, rather than
//! as independent engines.
//!
//! For each Dogwood rule, `cedarify` builds one loc-bearing
//! `cedar_policy_core::ast::StaticPolicy` (collected into an
//! `ast::PolicySet`, handed to Cedar via `TryFrom` — no string round-trip):
//!
//! * the effect (`permit`/`forbid`) and the scope constraints come
//!   directly from the structured [`crate::ast::Scope`] (which already
//!   holds loc-bearing `cedar_ast` constraints);
//! * each `when`/`unless` clause body — a structured `ast::Expr` — is
//!   lowered to a loc-bearing `cedar_ast::Expr` (`to_ast`);
//! * a **temporal** extension leaf is hoisted: replaced with a
//!   `context.<generated_name>` reference (a pre-evaluated `Bool`), and the
//!   schema is augmented with that field on the rule's action(s);
//! * an **information-provider** extension leaf hoists its invocation to
//!   `context.providers.<name>` and lowers the projection/comparison as
//!   native Cedar `ast::Expr` nodes. The hoisted field is declared on
//!   EVERY action's context and its provider is evaluated for every
//!   decision event — provider execution is unconditional (see the
//!   provider contract in the guide, 05-information-providers).
//!
//! The hoisted field is populated by the extension's evaluator at
//! authorize time; Cedar's validator and authorizer only ever see a
//! boolean in `context`.

mod schema_augment;
mod to_ast;

/// Re-exported for the pre-lowering
/// [`ParsedPolicy`](crate::policy_set::ParsedPolicy) provider-invocation
/// accessor, so it reads invocation arguments through the same conversion
/// lowering uses.
pub(crate) use to_ast::cedar_call_to_invocation;

use std::any::{Any, TypeId};
use std::collections::BTreeMap;
use std::sync::Arc;

use cedar_policy_core::ast as cedar_ast;

use crate::ast::{CondKeyword, Effect, Policy, PolicySet};
use crate::error::{RawCedarifyError, Span};

/// The action scope a rule pins, as seen by extension lowering.
///
/// A concrete `action == Ns::Action::"X"` pins one action; an
/// `action in [ … ]` pins a list; anything else (a bare `action`) is
/// unconstrained. A hoisted extension field attaches to the pinned
/// action(s), or to every action when unconstrained.
#[derive(Debug, Clone)]
pub enum ScopedAction {
    /// `action == Ns::Action::"X"` — a single `(namespace, action_id)`.
    Concrete((String, String)),
    /// `action in [ … ]` — each listed `(namespace, action_id)`.
    List(Vec<(String, String)>),
    /// A bare `action` scope with no action pinned.
    Unconstrained,
}

/// A hoisted boolean context field backing a temporal leaf.
///
/// `cedarify` replaces a `temporal { … }` leaf with a
/// `context.<rule_key>__temporal_N` reference and records this field so that
/// `authorize` can evaluate the original leaf and bind its boolean into
/// the request context. The leaf itself travels here so the evaluation
/// is a direct lookup rather than a re-walk of the policy AST.
#[derive(Debug, Clone)]
pub struct ContextField {
    /// The action scope the field attaches to. A concrete `==` action or an
    /// `in [list]` attaches the field to those action(s); an unconstrained
    /// scope attaches it to every action's context.
    pub action: ScopedAction,
    /// The generated field name, e.g. `policy_0__temporal_0` (the rule key
    /// prefix followed by a per-policy ordinal).
    pub field_name: String,
    /// The temporal leaf this field backs — evaluated at authorize time
    /// to produce the boolean bound to `context.<field_name>`.
    pub temporal: crate::extension::temporal::Temporal,
    /// The concrete actions [`action`](Self::action) resolves to against the
    /// schema — a group expanded to its transitive members, an unconstrained
    /// scope to every action. Resolved by
    /// [`schema_augment::scope_target_actions`], the SAME expansion the schema
    /// augmentation grafts with, so validation and augmentation cannot disagree
    /// about which actions a leaf attaches to.
    pub target_actions: Vec<(String, String)>,
    /// What the rule's `principal` scope admits on the entity-type axis.
    pub principal: ScopeConstraint,
    /// What the rule's `resource` scope admits on the entity-type axis.
    pub resource: ScopeConstraint,
}

/// A type-keyed store of hoisted extension leaves.
///
/// Each dialect's leaves are held under their own leaf type, so a dialect
/// retrieves *its* leaves generically ([`leaves`](HoistedLeaves::leaves) /
/// [`take_leaves`](HoistedLeaves::take_leaves)) without the store — or any
/// shared code — naming the dialect. This is what makes validation
/// parametric in the sublanguage: the lowered bundle no longer has one
/// named `Vec` field per dialect.
#[derive(Debug, Default)]
pub struct HoistedLeaves {
    /// Keyed by the leaf type's `TypeId`; each value is a `Vec<L>` boxed as
    /// `dyn Any`, in emission (rule) order.
    by_type: BTreeMap<TypeId, Box<dyn Any + Send + Sync>>,
}

impl HoistedLeaves {
    /// Store a dialect's full leaf list under its leaf type. Called once per
    /// dialect at the end of lowering.
    pub fn insert<L: Any + Send + Sync>(&mut self, leaves: Vec<L>) {
        self.by_type.insert(TypeId::of::<L>(), Box::new(leaves));
    }

    /// Take the leaves of type `L` by value (emptying that slot), or an empty
    /// `Vec` if this dialect contributed none. Used where an owned list is
    /// needed (building the lowered artifacts, [`Lowered`](crate::api::Lowered)).
    pub fn take_leaves<L: Any + Send + Sync>(&mut self) -> Vec<L> {
        self.by_type
            .remove(&TypeId::of::<L>())
            .and_then(|b| b.downcast::<Vec<L>>().ok())
            .map(|b| *b)
            .unwrap_or_default()
    }
}

/// The result of lowering a Dogwood policy set to Cedar.
///
/// Not `Clone`: the type-keyed [`HoistedLeaves`] store holds `Box<dyn Any>`
/// values, which are not clonable. Nothing clones a `Cedarified` (it is
/// consumed once by `parse`), so this is not a regression.
#[derive(Debug)]
pub struct Cedarified {
    /// The synthesized Cedar policies as a loc-bearing
    /// `cedar_policy_core::ast::PolicySet` (one static policy per Dogwood
    /// rule), built directly rather than rendered to text — `parse` turns
    /// this into a `cedar_policy::PolicySet` via `TryFrom`, with no string
    /// round-trip. Each node carries its `.dw` source location, so Cedar
    /// validation diagnostics rebase into the original `.dw`.
    pub policy_set: cedar_ast::PolicySet,
    /// The augmented Cedar schema the policies validate against — the base
    /// action schema plus the hoisted `context.<name>` fields contributed by
    /// extension leaves. Carried as a `cedar_policy::SchemaFragment` (the
    /// lossless form), from which `parse` derives the compiled
    /// `cedar_policy::Schema`, the cedarschema text, and the JSON — each
    /// without re-parsing text.
    pub schema: cedar_policy::SchemaFragment,
    /// The hoisted extension leaves, keyed by dialect leaf type (temporal
    /// `ContextField`, provider `ProviderField`, …), in emission order.
    /// `parse` drains them by type via `hoisted.take_leaves::<L>()` to build
    /// the lowered artifacts' per-dialect leaf vecs.
    pub hoisted: HoistedLeaves,
    /// The synthesized Cedar policy id for each Dogwood rule, in order:
    /// `rule_ids[k]` is the id of the policy emitted for Dogwood rule
    /// `k`. Lets `authorize` map a Cedar determining-policy id in the
    /// authorization response back to the originating Dogwood rule.
    pub rule_ids: Vec<String>,
    /// The originating `.dw` span of each Dogwood rule, parallel to
    /// `rule_ids`: `rule_spans[k]` is the source span of rule `k`. The lowered
    /// `ast` now carries a `.dw` location on every node, so a Cedar diagnostic's
    /// own label usually pinpoints the offending sub-expression; this whole-rule
    /// span is the validator's fallback when a diagnostic carries no label (it
    /// names only a lowered policy id, mapped back via `rule_ids`).
    pub rule_spans: Vec<Span>,
}

/// The **rule key** minted for the `k`-th Dogwood rule: the string used both
/// as the emitted Cedar `PolicyID` (the Cedar storage key, and the token
/// a decision names) *and* as the namespace prefix on that rule's hoisted
/// `context.<id>` field names.
///
/// When a caller supplies a `distincter`, the key is `<distincter>_<k>`;
/// otherwise it falls back to `policy_<k>`. Two policy sets lowered with
/// distinct distincters therefore mint non-colliding policy ids *and* field
/// names, so they can be combined into one Cedar `PolicySet` / policy store or
/// lowered incrementally over a shared, accreting augmented schema.
///
/// The key is deliberately **not** derived from a source `@id("…")` annotation:
/// distinctness is the caller's decision, and `@id` may be missing or
/// duplicated. `@id` remains an ordinary annotation on the emitted policy.
pub fn rule_key(distincter: Option<&str>, rule_index: usize) -> String {
    match distincter {
        Some(d) => format!("{d}_{rule_index}"),
        None => format!("policy_{rule_index}"),
    }
}

use crate::extension::provider::declarations::ProviderDeclarations;

/// An information-provider context field hoisted by cedarify: the action
/// it attaches to, the generated field name under `context.providers`,
/// the Cedar type of its output (from the provider declarations), and the
/// invocation it backs (evaluated at authorize time by running the
/// provider's implementation, bound into `context.providers.<field_name>`).
#[derive(Debug, Clone)]
pub struct ProviderField {
    /// The action scope the field's rule pins. Informational: the hoisted
    /// field is grafted onto EVERY action's context and evaluated for every
    /// decision event (unconditional provider execution); this records the
    /// originating rule's declared scope. Mirrors [`ContextField::action`].
    pub action: ScopedAction,
    /// The concrete `(namespace, action_id)` actions this field's scope
    /// resolves to against the schema — a group expanded to its descendants,
    /// an unconstrained scope to every action. Informational (see
    /// [`ProviderField::action`]); populated at lowering by
    /// [`schema_augment::scope_target_actions`], and available to
    /// alternative implementations for as-if optimizations.
    pub target_actions: Vec<(String, String)>,
    pub field_name: String,
    /// The Cedar type of the value bound into `context.providers.<field_name>`:
    /// the provider's `outputType`, or — when a method chain is present — the
    /// last method's `outputType` (the pipeline's type after eager evaluation).
    pub cedar_type: String,
    /// Start offset of the provider block body in the `.dw` source — the
    /// base for rebasing the invocation's block-relative span.
    pub body_base: usize,
    /// The provider invocation this field backs, e.g.
    /// `Strings::Matches(context.input.stock, "^[A-Z]+$")`.
    pub invocation: crate::extension::provider::ast::Invocation,
    /// The **eager method chain** applied to the invocation's output before
    /// binding, in order. Empty for a plain projection-only atom (backward
    /// compatible). Each method is evaluated in Rhai at authorize time; the
    /// hoisted value is `mₙ(…m₁(evaluate(args))…)`.
    pub methods: Vec<crate::extension::provider::ast::MethodCall>,
}

/// Mutable cedarify state threaded through the lowering.
struct Ctx<'a> {
    bool_fields: Vec<ContextField>,
    provider_fields: Vec<ProviderField>,
    /// The rule key of the policy currently being emitted — the namespace
    /// prefix for its hoisted field names (see [`rule_key`]).
    rule_key: String,
    /// The current rule's `principal` / `resource` scope constraints, set per policy
    /// in `emit_policy` so a hoisted leaf can record them without threading two more
    /// parameters through every lowering function.
    principal_scope: ScopeConstraint,
    resource_scope: ScopeConstraint,
    /// Ordinal of the next hoisted leaf *within the current policy*, reset to
    /// 0 at each policy boundary. Combined with [`Ctx::rule_key`] it makes each
    /// hoisted field name deterministic and unique across lowering calls.
    field_ordinal: usize,
    provider_declarations: Option<&'a ProviderDeclarations>,
    /// The original `.dw` source, shared into every lowered node's `Loc`
    /// so Cedar diagnostics carry `.dw`-accurate spans.
    dw_src: Arc<str>,
}

/// Lower a Dogwood policy set to Cedar, with information-provider
/// declarations available for typing (and backing) the hoisted
/// `context.providers.<name>` fields.
pub fn cedarify_with_providers(
    policy_set: &PolicySet,
    schema_source: &str,
    provider_declarations: Option<&ProviderDeclarations>,
    distincter: Option<&str>,
    dw_src: &Arc<str>,
) -> Result<Cedarified, RawCedarifyError> {
    let mut ctx = Ctx {
        bool_fields: Vec::new(),
        provider_fields: Vec::new(),
        rule_key: String::new(),
        principal_scope: ScopeConstraint::Any,
        resource_scope: ScopeConstraint::Any,
        field_ordinal: 0,
        provider_declarations,
        dw_src: Arc::clone(dw_src),
    };

    let mut ast_policy_set = cedar_ast::PolicySet::new();
    let mut rule_ids = Vec::with_capacity(policy_set.policies.len());
    let mut rule_spans = Vec::with_capacity(policy_set.policies.len());
    for (i, policy) in policy_set.policies.iter().enumerate() {
        let id = rule_key(distincter, i);
        // Each rule opens a fresh field-ordinal namespace under its own key, so
        // hoisted names are `<rule_key>__temporal_0`, `…__temporal_1`, ….
        ctx.rule_key = id.clone();
        ctx.field_ordinal = 0;
        let static_policy = emit_policy(policy, &id, &mut ctx)?;
        ast_policy_set
            .add_static(static_policy)
            .map_err(|e| RawCedarifyError {
                message: format!("duplicate policy id `{id}`: {e}"),
                span: None,
            })?;
        rule_ids.push(id);
        rule_spans.push(policy.span);
    }

    // Augment the schema with hoisted boolean (temporal) and
    // information-provider context fields. Parse the base schema once into a
    // fragment, mutate it in place through both passes, and hand the fragment
    // out — no serialize/re-parse round-trip between passes or downstream.
    let (mut fragment, _warnings) = schema_augment::Fragment::from_cedarschema_str(
        schema_source,
        cedar_policy_core::extensions::Extensions::all_available(),
    )
    .map_err(|e| RawCedarifyError {
        message: format!("parse base schema: {e}"),
        span: None,
    })?;
    if !ctx.bool_fields.is_empty() {
        // Resolve each temporal leaf's action scope to the concrete actions its
        // rule can match — a group expanded to its transitive members, an
        // unconstrained scope to every action — now, while the fragment carries
        // the action hierarchy. The SAME resolution the augmentation below grafts
        // with, and the one validation consumes, so the two cannot drift.
        for f in ctx.bool_fields.iter_mut() {
            f.target_actions =
                schema_augment::scope_target_actions(&f.action, &fragment).map_err(|message| {
                    RawCedarifyError {
                        message: format!("resolve temporal action scope: {message}"),
                        span: None,
                    }
                })?;
        }
        schema_augment::add_bool_context_fields(&mut fragment, &ctx.bool_fields).map_err(
            |message| RawCedarifyError {
                message: format!("schema augmentation failed: {message}"),
                span: None,
            },
        )?;
    }
    if !ctx.provider_fields.is_empty() {
        // Resolve each provider field's action scope to the concrete set of
        // actions its rule can match (groups expanded to descendants, an
        // unconstrained scope to every action) — now, while the fragment
        // carries the action hierarchy. Informational metadata: evaluation
        // is unconditional and grafting covers every action, but the set is
        // exposed on the public ProviderField for alternative
        // implementations' as-if optimizations.
        for f in ctx.provider_fields.iter_mut() {
            f.target_actions =
                schema_augment::scope_target_actions(&f.action, &fragment).map_err(|message| {
                    RawCedarifyError {
                        message: format!("resolve provider action scope: {message}"),
                        span: None,
                    }
                })?;
        }
        schema_augment::add_provider_context_fields(&mut fragment, &ctx.provider_fields).map_err(
            |message| RawCedarifyError {
                message: format!("provider schema augmentation failed: {message}"),
                span: None,
            },
        )?;
    }

    // Convert the mutated core fragment to the public `SchemaFragment` (the
    // lossless form) in memory — no text round-trip. This is a `#[doc(hidden)]`
    // conversion (private/internal type coupling). Unguarded: a Cedar release that drops
    // the impl breaks the build rather than being caught by a test. This comment used to
    // claim a canary test covered it; none has ever existed.
    let schema: cedar_policy::SchemaFragment =
        fragment.try_into().map_err(|e| RawCedarifyError {
            message: format!("assemble augmented schema fragment: {e}"),
            span: None,
        })?;

    // Deposit each dialect's leaves into the type-keyed store, keyed by leaf
    // type. Schema augmentation above still consumed the concrete
    // accumulators (a lowering concern); the store is what downstream
    // (validation, `Lowered` construction) consumes dialect-agnostically.
    let mut hoisted = HoistedLeaves::default();
    hoisted.insert(ctx.bool_fields);
    hoisted.insert(ctx.provider_fields);

    Ok(Cedarified {
        policy_set: ast_policy_set,
        schema,
        hoisted,
        rule_ids,
        rule_spans,
    })
}

/// Lower one Dogwood rule to a loc-bearing `ast::StaticPolicy` with the
/// given id.
///
/// The scope constraints are already loc-bearing `cedar_ast` (built by the
/// parser), so they go straight in. The condition body is
/// built as loc-bearing `ast::Expr` by [`to_ast`] and the clauses are folded
/// exactly as Cedar does: a `when` clause contributes its body, an `unless`
/// clause contributes its negation, and the clauses are conjoined with `&&`.
fn emit_policy(
    policy: &Policy,
    id: &str,
    ctx: &mut Ctx,
) -> Result<cedar_ast::StaticPolicy, RawCedarifyError> {
    use cedar_policy_core::expr_builder::ExprBuilder as _;

    let effect = match policy.effect {
        Effect::Permit => cedar_ast::Effect::Permit,
        Effect::Forbid => cedar_ast::Effect::Forbid,
    };

    // The scoped action types any hoisted extension field.
    let action = scope_action(&policy.scope.action);
    // The principal/resource scope narrows which entity types the condition can see,
    // which decides whether an attribute read in it resolves.
    ctx.principal_scope = scope_constraint(policy.scope.principal.as_inner());
    ctx.resource_scope = scope_constraint(policy.scope.resource.as_inner());

    // The rule's `.dw` span backs the policy-level `Loc` and the clause-fold
    // nodes (which have no single surface token of their own).
    let rule_loc = cedar_loc(&ctx.dw_src, policy.span);
    let builder = || cedar_ast::ExprBuilder::<()>::new().with_source_loc(&rule_loc);

    // Lower each clause to a loc-bearing `ast::Expr`, negating `unless`.
    let mut clause_exprs = Vec::with_capacity(policy.conditions.len());
    for cond in &policy.conditions {
        let body = to_ast::lower_expr(&cond.body, &action, ctx, &ctx.dw_src.clone())?;
        clause_exprs.push(match cond.keyword {
            CondKeyword::When => body,
            CondKeyword::Unless => builder().not(body),
        });
    }
    // Conjoin the clauses (left-to-right `&&`); an empty rule body is `true`.
    let condition = match clause_exprs
        .into_iter()
        .reduce(|acc, e| builder().and(acc, e))
    {
        Some(e) => e,
        None => builder().val(true),
    };

    // Annotations: `@key` / `@key("value")` (empty string = no value).
    let annotations: cedar_ast::Annotations = policy
        .annotations
        .iter()
        .filter_map(|a| {
            let key = a.key.parse::<cedar_ast::AnyId>().ok()?;
            let value = a.value.clone().map(smol_str::SmolStr::from);
            Some((key, cedar_ast::Annotation::with_optional_value(value, None)))
        })
        .collect();

    let template = cedar_ast::Template::new(
        cedar_ast::PolicyID::from_string(id),
        Some(rule_loc.clone()),
        annotations,
        effect,
        policy.scope.principal.clone(),
        policy.scope.action.clone(),
        policy.scope.resource.clone(),
        Some(condition),
    );

    cedar_ast::StaticPolicy::try_from(template).map_err(|e| RawCedarifyError {
        message: format!("policy is not static (contains a template slot): {e}"),
        span: Some(policy.span),
    })
}

/// A `Loc` into the `.dw` source for the given span.
fn cedar_loc(src: &Arc<str>, span: Span) -> cedar_policy_core::parser::Loc {
    cedar_policy_core::parser::Loc::new(span.start..span.end, Arc::clone(src))
}

/// What a rule's `principal` / `resource` scope admits on the entity-TYPE axis.
///
/// Only the type axis: which INSTANCES arrive is a run-time matter, but which types
/// can arrive is static, and that is what decides whether an attribute read in the
/// condition resolves.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ScopeConstraint {
    /// A bare `principal` / `resource`: every type the action permits.
    Any,
    /// `is Ns::T`, or the `is` half of `is Ns::T in G`.
    IsType(String),
    /// `== Ns::T::"x"`, or `in Ns::T::"x"`. `membership` distinguishes them: `in` also
    /// admits types that can be MEMBERS of that uid's type, which needs the schema's
    /// hierarchy to resolve and so is left to the validator.
    Uid {
        entity_type: String,
        membership: bool,
    },
}

/// Read the [`ScopeConstraint`] a structured principal/resource scope admits.
///
/// Matched exhaustively on purpose. A catch-all would collapse an unrecognised
/// variant to [`ScopeConstraint::Any`], which WIDENS the admitted types — and a
/// wider set means the condition is checked against types the rule cannot see,
/// which is a false rejection. A new Cedar variant must break the build instead.
fn scope_constraint(c: &cedar_ast::PrincipalOrResourceConstraint) -> ScopeConstraint {
    use cedar_ast::{EntityReference, PrincipalOrResourceConstraint as P};
    let uid_type = |r: &EntityReference| match r {
        EntityReference::EUID(uid) => Some(uid.entity_type().to_string()),
        // A template slot names no type; Dogwood does not lower templates.
        EntityReference::Slot(_) => None,
    };
    match c {
        P::Any => ScopeConstraint::Any,
        P::Is(ty) => ScopeConstraint::IsType(ty.to_string()),
        // `is T in G` narrows on the type axis by the `is` half only.
        P::IsIn(ty, _) => ScopeConstraint::IsType(ty.to_string()),
        P::Eq(r) => uid_type(r).map_or(ScopeConstraint::Any, |entity_type| ScopeConstraint::Uid {
            entity_type,
            membership: false,
        }),
        P::In(r) => uid_type(r).map_or(ScopeConstraint::Any, |entity_type| ScopeConstraint::Uid {
            entity_type,
            membership: true,
        }),
    }
}

/// Read the [`ScopedAction`] a structured scope pins: a single action for
/// `action == Ns::Action::"Id"`, the list for `action in [ … ]`, and
/// `Unconstrained` for a bare `action`.
fn scope_action(action: &cedar_ast::ActionConstraint) -> ScopedAction {
    match action {
        cedar_ast::ActionConstraint::Eq(uid) => ScopedAction::Concrete(uid_action(uid)),
        cedar_ast::ActionConstraint::In(uids) => {
            ScopedAction::List(uids.iter().map(|u| uid_action(u)).collect())
        }
        _ => ScopedAction::Unconstrained,
    }
}

/// Split a Cedar action UID into `(namespace, action_id)`; an empty
/// namespace is the top-level (unnamespaced) action. For an action
/// `Ns::Action::"X"`, the entity type is `Ns::Action` (namespace `Ns`) and
/// the eid is `X`.
fn uid_action(uid: &cedar_ast::EntityUID) -> (String, String) {
    let namespace = uid.entity_type().name().as_ref().namespace();
    (namespace, uid.eid().escaped().to_string())
}

#[cfg(test)]
mod tests {
    //! Canaries for the non-stable couplings this lowering relies on — both
    //! `pub` but `#[doc(hidden)]` in the `cedar-policy` crate. If a Cedar
    //! upgrade removes or changes either impl, the corresponding test stops
    //! compiling — a loud signal before the change silently breaks lowering:
    //!
    //! 1. `cedar_policy::PolicySet: TryFrom<cedar_policy_core::ast::PolicySet>`
    //!    — hands the loc-bearing `ast::PolicySet` to validation/authorization.
    //! 2. `cedar_policy::SchemaFragment: TryFrom<json_schema::Fragment<RawName>>`
    //!    — turns the mutated (augmented) core schema fragment into the public
    //!    `SchemaFragment` in memory, from which the compiled `Schema` and the
    //!    text/JSON serializations derive with no text round-trip.

    use std::sync::Arc;

    use cedar_policy_core::ast as cedar_ast;
    use cedar_policy_core::expr_builder::ExprBuilder as _;
    use cedar_policy_core::parser::Loc;

    #[test]
    fn augmented_fragment_converts_to_public_schema_fragment_and_schema() {
        // The load-bearing schema couplings. `schema_augment` mutates a core
        // `json_schema::Fragment<RawName>`; `cedarify` converts it to a public
        // `SchemaFragment` (coupling 2), and `api::lower` compiles that to a
        // `Schema` via `TryInto` — all without re-parsing text. If either line
        // fails to compile, fall back to serialize-then-`from_cedarschema_str`.
        use cedar_policy_core::validator::RawName;
        use cedar_policy_core::validator::json_schema::Fragment;

        let (core_fragment, _warnings) = Fragment::<RawName>::from_cedarschema_str(
            r#"entity User; action "Read" appliesTo { principal: [User], resource: [User] };"#,
            cedar_policy_core::extensions::Extensions::all_available(),
        )
        .expect("base schema parses");

        // Coupling 2: core fragment -> public SchemaFragment (in memory).
        let fragment: cedar_policy::SchemaFragment = core_fragment
            .try_into()
            .expect("json_schema::Fragment -> cedar_policy::SchemaFragment");

        // And the fragment compiles to a Schema and serializes both ways.
        let _schema: cedar_policy::Schema = fragment
            .clone()
            .try_into()
            .expect("SchemaFragment -> Schema");
        fragment
            .to_cedarschema()
            .expect("fragment -> cedarschema text");
        fragment.to_json_string().expect("fragment -> JSON");
    }

    #[test]
    fn ast_policy_set_converts_to_public_policy_set() {
        let src: Arc<str> = Arc::from("permit ( principal, action, resource ) when { true };");
        let loc = Loc::new(0..src.len(), Arc::clone(&src));
        let body = cedar_ast::ExprBuilder::<()>::new()
            .with_source_loc(&loc)
            .val(true);
        let policy = cedar_ast::StaticPolicy::new(
            cedar_ast::PolicyID::from_string("policy0"),
            Some(loc),
            cedar_ast::Annotations::new(),
            cedar_ast::Effect::Permit,
            cedar_ast::PrincipalConstraint::any(),
            cedar_ast::ActionConstraint::any(),
            cedar_ast::ResourceConstraint::any(),
            Some(body),
        )
        .expect("no template slot");
        let mut set = cedar_ast::PolicySet::new();
        set.add_static(policy).expect("add_static");

        // The load-bearing conversion. If this line fails to compile, the
        // `#[doc(hidden)] TryFrom<ast::PolicySet>` is gone.
        let public = cedar_policy::PolicySet::try_from(set)
            .expect("ast::PolicySet -> cedar_policy::PolicySet");
        assert_eq!(public.policies().count(), 1);
    }

    #[test]
    fn hoisted_leaves_take_on_missing_type_returns_empty() {
        let mut leaves = super::HoistedLeaves::default();
        let taken: Vec<super::ContextField> = leaves.take_leaves();
        assert!(
            taken.is_empty(),
            "take_leaves on missing type should be empty"
        );
    }

    #[test]
    fn hoisted_leaves_insert_then_take_returns_items() {
        let mut leaves = super::HoistedLeaves::default();
        leaves.insert(vec![42u64, 99]);
        let taken: Vec<u64> = leaves.take_leaves();
        assert_eq!(taken, vec![42, 99]);
        // Second take is empty (slot was consumed).
        let again: Vec<u64> = leaves.take_leaves();
        assert!(again.is_empty());
    }

    #[test]
    fn rule_key_without_distincter() {
        assert_eq!(super::rule_key(None, 0), "policy_0");
        assert_eq!(super::rule_key(None, 3), "policy_3");
    }

    #[test]
    fn rule_key_with_distincter() {
        assert_eq!(super::rule_key(Some("batch"), 0), "batch_0");
        assert_eq!(super::rule_key(Some("session_1"), 2), "session_1_2");
    }
}
