//! Stable policy identity: id validation, canonical encodings of lowered rules
//! and hoisted leaves, and the revision / version hashes built from them.
//!
//! Crate-private. The public surface is [`IdSource`](crate::IdSource),
//! [`PolicyRef`](crate::PolicyRef), [`PolicySetVersion`](crate::PolicySetVersion)
//! and [`TemporalField::content_hash`](crate::TemporalField::content_hash).
//!
//! # Canonical forms
//!
//! A revision must change exactly when a rule's meaning changes. So every
//! canonical form here excludes what carries no meaning:
//!
//! - **spans** (byte offsets move when other rules are inserted or edited);
//! - **annotations** and **comments** (comments never reach the AST);
//! - **positional names**: the rule's position, its synthesized Cedar policy
//!   id, and the `policy_<k>__temporal_<j>` / `policy_<k>_p_<j>` names of its
//!   hoisted fields (replaced by `dw__temporal_<j>` / `dw_p_<j>`, which keep the
//!   per-rule ordinal and drop the rule key);
//! - **binder spellings**: macro expansion mints binder names from call-site
//!   byte offsets (`t$372`), so binders are renamed to `v0, v1, …` in binding
//!   order (alpha-normalization, with shadowing respected).
//!
//! Strings inside an encoding are JSON-quoted, so the encodings are injective.

use std::collections::BTreeMap;
use std::fmt::Write as _;

use sha2::{Digest, Sha256};

use crate::extension::temporal::ast::{
    AggExpr, AggExprKind, BinderSlot, CallArg, CmpOp, Condition, ConditionKind, Predicate, Term,
    TypedBinder, WithinSpec,
};

/// The prefix a canonical encoding gives a rule's hoisted field names in place
/// of the positional rule key.
pub(crate) const CANONICAL_RULE_KEY: &str = "dw";

/// Version tag mixed into every revision, so a future change of the canonical
/// form cannot silently collide with revisions computed by this one.
const REVISION_TAG: &str = "dogwood-rule-revision/1";

/// Version tag mixed into every policy-set version hash.
const VERSION_TAG: &str = "dogwood-policy-set-version/1";

/// Version tag mixed into every leaf content hash.
const LEAF_TAG: &str = "dogwood-temporal-leaf/1";

/// The longest policy id accepted (before a distincter prefix is added).
pub(crate) const MAX_POLICY_ID_LEN: usize = 128;

/// The separator between a distincter and a stable id in an emitted Cedar
/// policy id (`<distincter>/<id>`). Cedar's `PolicyId` accepts any string, and
/// `/` is outside both the distincter alphabet and the stable-id alphabet, so
/// the split is unambiguous.
pub(crate) const PREFIX_SEPARATOR: char = '/';

/// Check one owner-chosen policy id against the portable id alphabet:
/// 1–128 characters from `[A-Za-z0-9_.:-]`.
///
/// The alphabet admits UUIDs, policy-store ids, other services' rule ids and dotted or
/// colon-separated names, and keeps ids safe to embed in logs, URLs, SQL
/// literals and policy-store names. It excludes `/`, which is reserved for the
/// distincter prefix. Loosening the alphabet later is not a breaking change;
/// tightening it would be.
pub(crate) fn validate_policy_id(id: &str) -> Result<(), String> {
    if id.is_empty() {
        return Err("a policy id must not be empty".to_string());
    }
    if id.len() > MAX_POLICY_ID_LEN {
        return Err(format!(
            "a policy id must be at most {MAX_POLICY_ID_LEN} characters (this one has {})",
            id.len()
        ));
    }
    if let Some(c) = id
        .chars()
        .find(|c| !(c.is_ascii_alphanumeric() || matches!(c, '_' | '.' | ':' | '-')))
    {
        return Err(format!(
            "a policy id may only use the characters [A-Za-z0-9_.:-]; `{}` is not allowed",
            c.escape_default()
        ));
    }
    Ok(())
}

/// The emitted Cedar policy id for a rule with stable id `id`, under an
/// optional distincter: `<distincter>/<id>`, or `<id>` without one.
pub(crate) fn prefixed_policy_id(distincter: Option<&str>, id: &str) -> String {
    match distincter {
        Some(d) => format!("{d}{PREFIX_SEPARATOR}{id}"),
        None => id.to_string(),
    }
}

/// Lowercase hex SHA-256 of `bytes`.
pub(crate) fn sha256_hex(bytes: &[u8]) -> String {
    let digest = Sha256::digest(bytes);
    let mut out = String::with_capacity(64);
    for b in digest.iter() {
        let _ = write!(out, "{b:02x}");
    }
    out
}

/// JSON-quote a string (injective, escape-safe).
fn q(s: &str) -> String {
    serde_json::to_string(s).expect("a string always serializes")
}

/// JSON-quote each segment of a path.
fn qpath(path: &[String]) -> String {
    let parts: Vec<String> = path.iter().map(|p| q(p)).collect();
    format!("[{}]", parts.join(","))
}

// ─── temporal conditions ─────────────────────────────────────────────

/// Alpha-normalizing encoder state: the binder names in scope, innermost last.
#[derive(Default)]
struct Binders {
    /// `(source name, canonical index)`, innermost last, so a lookup from the
    /// end finds the binding that shadows the others.
    scope: Vec<(String, usize)>,
    next: usize,
}

impl Binders {
    fn bind(&mut self, name: &str) -> usize {
        let index = self.next;
        self.next += 1;
        self.scope.push((name.to_string(), index));
        index
    }

    fn lookup(&self, name: &str) -> String {
        match self.scope.iter().rev().find(|(n, _)| n == name) {
            Some((_, index)) => format!("v{index}"),
            // An unbound name cannot occur in a checked leaf; keep it, quoted
            // and tagged, rather than guessing.
            None => format!("(free {})", q(name)),
        }
    }

    fn slot_name(slot: &BinderSlot) -> String {
        match slot {
            BinderSlot::Name(n) => n.clone(),
            // Pre-expansion forms cannot occur after macro expansion; encode
            // them distinctly rather than panicking.
            BinderSlot::ParamRef(p) => format!("?{p}"),
            BinderSlot::BinderRef(b) => format!("${b}"),
        }
    }
}

fn within(w: &WithinSpec) -> String {
    match w {
        WithinSpec::Concrete(i) => format!("{}{}", i.amount, i.unit.token()),
        WithinSpec::ParamRef(p) => format!("(param {})", q(p)),
    }
}

fn cmp(op: CmpOp) -> &'static str {
    match op {
        CmpOp::Le => "<=",
        CmpOp::Lt => "<",
        CmpOp::Ge => ">=",
        CmpOp::Gt => ">",
        CmpOp::Eq => "==",
        CmpOp::NotEq => "!=",
    }
}

fn typed_binder_type(b: &TypedBinder) -> String {
    q(&b.ty.render())
}

fn enc_condition(c: &Condition, env: &mut Binders, out: &mut String) {
    match &c.kind {
        ConditionKind::And { left, right } => {
            out.push_str("(and ");
            enc_condition(left, env, out);
            out.push(' ');
            enc_condition(right, env, out);
            out.push(')');
        }
        ConditionKind::Or { left, right } => {
            out.push_str("(or ");
            enc_condition(left, env, out);
            out.push(' ');
            enc_condition(right, env, out);
            out.push(')');
        }
        ConditionKind::Not { inner } => {
            out.push_str("(not ");
            enc_condition(inner, env, out);
            out.push(')');
        }
        ConditionKind::Formerly { within: w, body } => {
            let _ = write!(out, "(formerly {} ", within(w));
            enc_condition(body, env, out);
            out.push(')');
        }
        ConditionKind::Previous { within: w, body } => {
            let _ = write!(out, "(previous {} ", within(w));
            enc_condition(body, env, out);
            out.push(')');
        }
        ConditionKind::Since {
            left,
            within: w,
            right,
        } => {
            out.push_str("(since ");
            enc_condition(left, env, out);
            let _ = write!(out, " {} ", within(w));
            enc_condition(right, env, out);
            out.push(')');
        }
        ConditionKind::Predicate(p) => enc_predicate(p, env, out),
        ConditionKind::Comparison { op, left, right } => {
            let _ = write!(out, "(cmp {} ", cmp(*op));
            enc_term(left, env, out);
            out.push(' ');
            enc_term(right, env, out);
            out.push(')');
        }
        ConditionKind::Exists { var, body } => {
            let mark = env.scope.len();
            let index = env.bind(&Binders::slot_name(&var.slot));
            let _ = write!(out, "(exists v{index} {} ", typed_binder_type(var));
            enc_condition(body, env, out);
            out.push(')');
            env.scope.truncate(mark);
        }
        ConditionKind::Tp { var } => {
            let _ = write!(out, "(tp {})", env.lookup(&Binders::slot_name(var)));
        }
        // Pre-expansion nodes never reach a lowered leaf. Encode them
        // distinctly (never panic while hashing).
        ConditionKind::Call(call) => {
            let _ = write!(out, "(call {}", q(&call.name));
            for arg in &call.args {
                out.push(' ');
                match arg {
                    CallArg::Condition(c) => enc_condition(c, env, out),
                    CallArg::Within(i) => {
                        let _ = write!(out, "{}{}", i.amount, i.unit.token());
                    }
                    CallArg::Term(t) => enc_term(t, env, out),
                }
            }
            out.push(')');
        }
        ConditionKind::SigilRef { sigil, name } => {
            let _ = write!(out, "(sigil {sigil:?} {})", q(name));
        }
        ConditionKind::Refine { base, fields, .. } => {
            out.push_str("(refine ");
            enc_condition(base, env, out);
            for f in fields {
                let _ = write!(out, " ({} ", q(&f.name));
                enc_term(&f.value, env, out);
                out.push(')');
            }
            out.push(')');
        }
    }
}

fn enc_predicate(p: &Predicate, env: &mut Binders, out: &mut String) {
    let _ = write!(
        out,
        "(pred {} {} {} (",
        qpath(&p.namespace),
        q(&p.action),
        q(&p.kind)
    );
    for (i, arg) in p.args.iter().enumerate() {
        if i > 0 {
            out.push(' ');
        }
        let _ = write!(out, "({} ", q(&arg.name));
        enc_term(&arg.value, env, out);
        out.push(')');
    }
    out.push_str("))");
}

fn enc_term(t: &Term, env: &mut Binders, out: &mut String) {
    match t {
        Term::Entity { ty, id } => {
            let _ = write!(out, "(entity {} {})", q(ty), q(id));
        }
        Term::Integer(n) => {
            let _ = write!(out, "(int {n})");
        }
        Term::Decimal(s) => {
            let _ = write!(out, "(decimal {})", q(s));
        }
        Term::String(s) => {
            let _ = write!(out, "(str {})", q(s));
        }
        Term::Bool(b) => {
            let _ = write!(out, "(bool {b})");
        }
        Term::ContextField(path) => {
            let _ = write!(out, "(context {})", qpath(path));
        }
        Term::ScopeField(path) => {
            let _ = write!(out, "(scope {})", qpath(path));
        }
        Term::Var(v) => out.push_str(&env.lookup(v)),
        Term::Wildcard => out.push('*'),
        Term::Array(items) => {
            out.push_str("(array");
            for item in items {
                out.push(' ');
                enc_term(item, env, out);
            }
            out.push(')');
        }
        Term::Agg(agg) => enc_agg(agg, env, out),
        Term::Arith { op, left, right } => {
            let _ = write!(out, "(arith {} ", op.token());
            enc_term(left, env, out);
            out.push(' ');
            enc_term(right, env, out);
            out.push(')');
        }
        Term::ParamRef(p) => {
            let _ = write!(out, "(param {})", q(p));
        }
        Term::BinderRef(b) => {
            let _ = write!(out, "(binder-ref {})", q(b));
        }
    }
}

fn enc_for_vars(for_vars: &[TypedBinder], env: &mut Binders, out: &mut String) {
    out.push('(');
    for (i, b) in for_vars.iter().enumerate() {
        if i > 0 {
            out.push(' ');
        }
        let index = env.bind(&Binders::slot_name(&b.slot));
        let _ = write!(out, "(v{index} {})", typed_binder_type(b));
    }
    out.push(')');
}

fn enc_agg(agg: &AggExpr, env: &mut Binders, out: &mut String) {
    let mark = env.scope.len();
    match &agg.kind {
        AggExprKind::Sum {
            bound_var,
            for_vars,
            body,
        } => {
            // `sum x for (vars). where body`: `x` and `vars` scope over `body`.
            let x = env.bind(&Binders::slot_name(bound_var));
            let _ = write!(out, "(sum v{x} ");
            enc_for_vars(for_vars, env, out);
            out.push(' ');
            enc_condition(body, env, out);
            out.push(')');
        }
        AggExprKind::Count { for_vars, body } => {
            out.push_str("(count ");
            enc_for_vars(for_vars, env, out);
            out.push(' ');
            enc_condition(body, env, out);
            out.push(')');
        }
        AggExprKind::Call(call) => {
            let _ = write!(out, "(agg-call {})", q(&call.name));
        }
    }
    env.scope.truncate(mark);
}

/// The canonical, span-free, alpha-normalized encoding of a temporal condition.
pub(crate) fn canonical_condition(c: &Condition) -> String {
    let mut out = String::new();
    enc_condition(c, &mut Binders::default(), &mut out);
    out
}

// ─── hoisted leaves ──────────────────────────────────────────────────

/// Canonical action reference `(namespace, id)`.
fn action(ns: &str, id: &str) -> String {
    format!("({} {})", q(ns), q(id))
}

fn scoped_action(a: &crate::cedarify::ScopedAction) -> String {
    use crate::cedarify::ScopedAction as S;
    match a {
        S::Concrete((ns, id)) => format!("(concrete {})", action(ns, id)),
        S::List(v) => {
            let items: Vec<String> = v.iter().map(|(ns, id)| action(ns, id)).collect();
            format!("(list {})", items.join(" "))
        }
        S::Unconstrained => "(unconstrained)".to_string(),
    }
}

fn targets(t: &[(String, String)]) -> String {
    let mut items: Vec<String> = t.iter().map(|(ns, id)| action(ns, id)).collect();
    items.sort();
    items.dedup();
    format!("({})", items.join(" "))
}

fn scope_constraint(c: &crate::cedarify::ScopeConstraint) -> String {
    use crate::cedarify::ScopeConstraint as S;
    match c {
        S::Any => "(any)".to_string(),
        S::IsType(t) => format!("(is {})", q(t)),
        S::Uid {
            entity_type,
            membership,
        } => format!("(uid {} {membership})", q(entity_type)),
    }
}

/// The canonical encoding shared by both views of a temporal leaf.
fn leaf_encoding(
    action: String,
    targets: String,
    principal: String,
    resource: String,
    condition: &Condition,
) -> String {
    format!(
        "(temporal (action {action}) (targets {targets}) (principal {principal}) (resource {resource}) (condition {}))",
        canonical_condition(condition),
    )
}

/// The canonical encoding of one hoisted temporal leaf: its condition (after
/// pin injection), its rule's action scope and the concrete actions that scope
/// resolves to, and what its principal / resource scopes admit. The field name
/// is not part of it.
pub(crate) fn canonical_context_field(f: &crate::cedarify::ContextField) -> String {
    leaf_encoding(
        scoped_action(&f.action),
        targets(&f.target_actions),
        scope_constraint(&f.principal),
        scope_constraint(&f.resource),
        &f.temporal.condition,
    )
}

fn action_scope(a: &crate::api::ActionScope) -> String {
    use crate::api::ActionScope as S;
    match a {
        S::Concrete(r) => format!(
            "(concrete {})",
            action(r.namespace.as_deref().unwrap_or(""), &r.id)
        ),
        S::List(v) => {
            let items: Vec<String> = v
                .iter()
                .map(|r| action(r.namespace.as_deref().unwrap_or(""), &r.id))
                .collect();
            format!("(list {})", items.join(" "))
        }
        S::Unconstrained => "(unconstrained)".to_string(),
    }
}

/// The SHA-256 content hash of a public [`TemporalField`](crate::TemporalField).
/// The encoding is [`canonical_context_field`]'s (the same parts in the same
/// order), so a leaf hashes alike whether read during lowering or from the
/// public field.
pub(crate) fn temporal_field_hash(f: &crate::api::TemporalField) -> String {
    let target_actions: Vec<(String, String)> = f
        .target_actions
        .iter()
        .map(|r| (r.namespace.clone().unwrap_or_default(), r.id.clone()))
        .collect();
    let encoding = leaf_encoding(
        action_scope(&f.action),
        targets(&target_actions),
        scope_constraint(&f.principal),
        scope_constraint(&f.resource),
        &f.condition.condition,
    );
    sha256_hex(format!("{LEAF_TAG}\n{encoding}").as_bytes())
}

/// The canonical encoding of one hoisted provider leaf: the invocation and its
/// method chain (spans dropped), the Cedar type it is bound as, and its rule's
/// scope. The provider's implementation lives in the service schema and is not
/// part of the rule.
pub(crate) fn canonical_provider_field(f: &crate::cedarify::ProviderField) -> String {
    let args = |args: &[crate::extension::provider::ast::Arg]| -> String {
        let items: Vec<String> = args.iter().map(|a| q(&format!("{a:?}"))).collect();
        format!("({})", items.join(" "))
    };
    let methods: Vec<String> = f
        .methods
        .iter()
        .map(|m| format!("({} {})", q(&m.name), args(&m.args)))
        .collect();
    format!(
        "(provider {} {} (methods {}) (type {}) (action {}) (targets {}) (principal {}) (resource {}))",
        qpath(&f.invocation.function),
        args(&f.invocation.args),
        methods.join(" "),
        q(&f.cedar_type),
        scoped_action(&f.action),
        targets(&f.target_actions),
        scope_constraint(&f.principal),
        scope_constraint(&f.resource),
    )
}

/// Rename a hoisted field name minted under `rule_key` to its canonical form:
/// `<rule_key>__temporal_<j>` becomes `dw__temporal_<j>`.
pub(crate) fn canonical_field_name(rule_key: &str, field_name: &str) -> String {
    match field_name.strip_prefix(rule_key) {
        Some(suffix) => format!("{CANONICAL_RULE_KEY}{suffix}"),
        None => field_name.to_string(),
    }
}

/// The revision of one lowered rule: SHA-256 over its canonical Cedar text
/// (emitted under the canonical rule key, with no annotations and no id) and
/// the canonical encodings of the leaves it hoisted, each under its canonical
/// field name.
pub(crate) fn rule_revision(canonical_cedar: &str, leaves: &[(String, String)]) -> String {
    let mut text = String::new();
    let _ = writeln!(text, "{REVISION_TAG}");
    let _ = writeln!(text, "{}", q(canonical_cedar));
    for (name, encoding) in leaves {
        let _ = writeln!(text, "{} {encoding}", q(name));
    }
    sha256_hex(text.as_bytes())
}

/// The policy-set version hash: SHA-256 over the sorted `(policy id, revision)`
/// pairs, the augmented Cedar schema (canonical JSON), the decision kinds and
/// the partition keys.
pub(crate) fn version_hash(
    ids_and_revisions: &[(String, String)],
    schema_json: Option<&str>,
    decision_kinds: &std::collections::BTreeSet<String>,
    partition_keys: &[crate::engine::PartitionKey],
) -> String {
    let mut pairs: Vec<&(String, String)> = ids_and_revisions.iter().collect();
    pairs.sort();
    let mut text = String::new();
    let _ = writeln!(text, "{VERSION_TAG}");
    for (id, rev) in pairs {
        let _ = writeln!(text, "policy {} {rev}", q(id));
    }
    let schema = schema_json
        .and_then(|s| serde_json::from_str::<serde_json::Value>(s).ok())
        .map(|v| canonical_json(&v))
        .unwrap_or_else(|| "null".to_string());
    let _ = writeln!(text, "schema {schema}");
    for kind in decision_kinds {
        let _ = writeln!(text, "decision-kind {}", q(kind));
    }
    for key in partition_keys {
        let _ = writeln!(text, "partition-key {}", qpath(&key.field_path));
    }
    sha256_hex(text.as_bytes())
}

/// Serialize JSON with every object's keys sorted, so the text does not
/// depend on map iteration order anywhere upstream.
fn canonical_json(v: &serde_json::Value) -> String {
    match v {
        serde_json::Value::Object(map) => {
            let sorted: BTreeMap<&String, &serde_json::Value> = map.iter().collect();
            let items: Vec<String> = sorted
                .into_iter()
                .map(|(k, v)| format!("{}:{}", q(k), canonical_json(v)))
                .collect();
            format!("{{{}}}", items.join(","))
        }
        serde_json::Value::Array(items) => {
            let items: Vec<String> = items.iter().map(canonical_json).collect();
            format!("[{}]", items.join(","))
        }
        other => other.to_string(),
    }
}

// ─── per-set identity ────────────────────────────────────────────────

/// The identity facts of one lowered policy set, kept beside its
/// [`Lowered`](crate::api::Lowered) artifacts: each rule's revision, whether
/// its ids are stable, and (computed once, on demand) its version hash.
#[derive(Debug, Clone)]
pub(crate) struct SetIdentity {
    /// `revisions[k]` is rule `k`'s revision, parallel to `Lowered::rule_ids`.
    revisions: Vec<String>,
    /// Whether every rule's emitted id is owner-chosen (not positional).
    stable: bool,
    /// The version hash, computed on first use (it serializes the schema).
    version_hash: std::sync::OnceLock<String>,
}

impl SetIdentity {
    pub(crate) fn new(revisions: Vec<String>, stable: bool) -> Self {
        SetIdentity {
            revisions,
            stable,
            version_hash: std::sync::OnceLock::new(),
        }
    }

    /// An identity whose version hash is already known (the Lean frontend
    /// computes it with the rest of the lowered set).
    #[cfg(feature = "lean-frontend")]
    pub(crate) fn with_version_hash(revisions: Vec<String>, stable: bool, hash: String) -> Self {
        let version_hash = std::sync::OnceLock::new();
        let _ = version_hash.set(hash);
        SetIdentity {
            revisions,
            stable,
            version_hash,
        }
    }

    /// Rule `k`'s revision.
    pub(crate) fn revision(&self, k: usize) -> &str {
        &self.revisions[k]
    }

    /// Whether the set's ids are stable.
    pub(crate) fn stable(&self) -> bool {
        self.stable
    }

    /// The set's version hash over `lowered` (the artifacts this identity
    /// was built with).
    pub(crate) fn version_hash(&self, lowered: &crate::api::Lowered) -> &str {
        self.version_hash.get_or_init(|| {
            let pairs: Vec<(String, String)> = lowered
                .rule_ids
                .iter()
                .cloned()
                .zip(self.revisions.iter().cloned())
                .collect();
            let schema = lowered.augmented_schema_fragment.to_json_string().ok();
            version_hash(
                &pairs,
                schema.as_deref(),
                &lowered.decision_kinds,
                &lowered.partition_keys,
            )
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn ids_follow_the_portable_alphabet() {
        for ok in [
            "a",
            "rule-1",
            "018f7f9e-1b2c-7d3e-8f40-123456789abc",
            "sys.max_reads",
            "ns:rule",
            "_x",
        ] {
            assert!(validate_policy_id(ok).is_ok(), "{ok}");
        }
        for bad in ["", "a/b", "a b", "é", "a\"b", &"x".repeat(129)] {
            assert!(validate_policy_id(bad).is_err(), "{bad}");
        }
        assert!(validate_policy_id(&"x".repeat(128)).is_ok());
    }

    #[test]
    fn prefixes_use_a_slash() {
        assert_eq!(prefixed_policy_id(Some("usr"), "r1"), "usr/r1");
        assert_eq!(prefixed_policy_id(None, "r1"), "r1");
    }

    #[test]
    fn canonical_field_names_drop_the_rule_key() {
        assert_eq!(
            canonical_field_name("policy_3", "policy_3__temporal_1"),
            "dw__temporal_1"
        );
        assert_eq!(canonical_field_name("usr_0", "usr_0_p_2"), "dw_p_2");
    }

    #[test]
    fn canonical_json_sorts_keys() {
        let a: serde_json::Value =
            serde_json::from_str(r#"{"b":1,"a":{"d":[1,2],"c":null}}"#).expect("json");
        assert_eq!(canonical_json(&a), r#"{"a":{"c":null,"d":[1,2]},"b":1}"#);
    }
}
