//! Lowering several policies, each under its own distincter, with `lower_many`:
//!
//! - `lower_many` equals the union of each policy lowered alone against the
//!   same schema, and lowering the policies' concatenation under one
//!   distincter yields the same leaves, event signatures, and schema fields.
//! - Distincter-lowered ids are `<d>_<rule>…`, injective across distincters;
//!   distincter-less ids are unchanged.
//! - Input order changes no id.
//! - The augmented schema declares a `context.<leafId>` Bool for every leaf.
//! - Findings render against each policy's own text, and an `Authorizer`
//!   decides over the result.

use std::collections::BTreeSet;

use dogwood_language::{
    Authorizer, Decision, Distincter, Error, Event, LoweredPolicySet, ParsedPolicySet,
    PolicySchema, ServiceSchema, TemporalField, Validator, Value, lower_many,
};

const SCHEMA: &str = r#"
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

/// One leaf.
const ONE_LEAF: &str = r#"
permit ( principal, action == Drupe::Action::"Read", resource )
when temporal {
    formerly within 1h Drupe::Action::"Login"::request{ input.user: context.input.user }
};
"#;

/// Two rules, the second with two leaves.
const TWO_RULES: &str = r#"
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
"#;

/// A Cedar-only rule beside a temporal one, so a leafless rule sits in the chain.
const MIXED: &str = r#"
permit ( principal, action == Drupe::Action::"Login", resource )
when { context.input.user == "alice" };

permit ( principal, action == Drupe::Action::"Login", resource )
when temporal {
    exists (u: String). (
        formerly within 2h Drupe::Action::"Login"::request{ input.user: u }
    )
};
"#;

thread_local! {
    /// One service schema per test, so every parse uses a clone of it.
    static SERVICE: ServiceSchema = ServiceSchema::defaults();
}

fn service() -> ServiceSchema {
    SERVICE.with(ServiceSchema::clone)
}

fn base_schema() -> PolicySchema {
    PolicySchema::from_cedarschema_str(SCHEMA).expect("action schema")
}

fn inputs() -> Vec<(&'static str, &'static str)> {
    vec![(ONE_LEAF, "alpha"), (TWO_RULES, "beta"), (MIXED, "gamma")]
}

fn lower(policy: &str, schema: &PolicySchema, distincter: &str) -> LoweredPolicySet {
    ParsedPolicySet::parse(policy, &service())
        .expect("parses")
        .lower_with_distincter(schema, distincter)
        .unwrap_or_else(|e| panic!("`{distincter}` lowers: {e}"))
}

/// Lower each entry alone against the base schema.
fn standalone(policies: &[(&str, &str)]) -> Vec<LoweredPolicySet> {
    policies
        .iter()
        .map(|(policy, distincter)| lower(policy, &base_schema(), distincter))
        .collect()
}

/// Each Cedar policy as `(id, text)`, sorted by id.
fn cedar_policies(set: &LoweredPolicySet) -> Vec<(String, String)> {
    let mut out: Vec<_> = set
        .as_cedar()
        .policies()
        .map(|p| (p.id().to_string(), p.to_string()))
        .collect();
    out.sort();
    out
}

fn rule_ids(set: &LoweredPolicySet) -> Vec<String> {
    set.rules().map(|r| r.cedar_policy_id).collect()
}

fn leaves(set: &LoweredPolicySet) -> Vec<TemporalField> {
    set.temporal_fields().cloned().collect()
}

fn nonrelativized_leaves(set: &LoweredPolicySet) -> Vec<TemporalField> {
    set.nonrelativized_temporal_fields().cloned().collect()
}

fn leaf_ids(set: &LoweredPolicySet) -> Vec<String> {
    set.temporal_fields().map(|f| f.id.clone()).collect()
}

#[test]
fn distincter_lowered_ids_have_the_unversioned_shape() {
    let set = lower(ONE_LEAF, &base_schema(), "d");
    assert_eq!(rule_ids(&set), ["d_0"]);
    assert_eq!(leaf_ids(&set), ["d_0__temporal_0"]);

    let set = lower(TWO_RULES, &base_schema(), "beta");
    assert_eq!(rule_ids(&set), ["beta_0", "beta_1"]);
    assert_eq!(
        leaf_ids(&set),
        [
            "beta_0__temporal_0",
            "beta_1__temporal_0",
            "beta_1__temporal_1"
        ]
    );
}

#[test]
fn ids_are_injective_across_adversarial_distincters() {
    let distincters = ["a", "a_0", "a_0__temporal_0", "a__temporal"];
    let parts: Vec<_> = distincters.iter().map(|d| (ONE_LEAF, *d)).collect();
    // `lower_many` succeeding means Cedar accepted every policy id as new.
    let merged = many(&parts);
    // A rule id equal to a leaf id is harmless: they live in different namespaces.
    for ids in [rule_ids(&merged), leaf_ids(&merged)] {
        assert_eq!(ids.len(), distincters.len(), "{ids:?}");
        let distinct: std::collections::BTreeSet<_> = ids.iter().collect();
        assert_eq!(distinct.len(), ids.len(), "{ids:?}");
    }
}

#[test]
fn distincter_less_ids_are_unchanged() {
    let set = ParsedPolicySet::parse(ONE_LEAF, &service())
        .expect("parses")
        .lower(&base_schema())
        .expect("lowers");
    assert_eq!(rule_ids(&set), ["policy_0"]);
    assert_eq!(leaf_ids(&set), ["policy_0__temporal_0"]);
}

#[test]
fn input_order_changes_no_id() {
    let ids = |set: &LoweredPolicySet| {
        let mut ids: Vec<String> = rule_ids(set).into_iter().chain(leaf_ids(set)).collect();
        ids.sort();
        ids
    };
    let mut reversed_inputs = inputs();
    reversed_inputs.reverse();
    assert_eq!(ids(&many(&inputs())), ids(&many(&reversed_inputs)));
}

#[test]
fn augmented_schema_declares_a_bool_for_every_leaf() {
    let merged = many(&inputs());
    let enriched = merged.cedar_schema();
    for leaf in merged.temporal_fields() {
        let action = leaf_action(leaf);
        // Strict validation passes only if `context.<id>` is a Bool.
        let probe: cedar_policy::PolicySet = format!(
            r#"permit (principal, action == Drupe::Action::"{action}", resource)
               when {{ context.{} }};"#,
            leaf.id
        )
        .parse()
        .expect("probe parses");
        let result = cedar_policy::Validator::new(enriched.clone())
            .validate(&probe, cedar_policy::ValidationMode::Strict);
        assert!(
            result.validation_passed(),
            "`context.{}` is not a Bool on `{action}`: {:?}",
            leaf.id,
            result
                .validation_errors()
                .map(ToString::to_string)
                .collect::<Vec<_>>()
        );
    }
}

/// The single action a fixture leaf's rule scopes.
fn leaf_action(leaf: &TemporalField) -> String {
    match &leaf.action {
        dogwood_language::ActionScope::Concrete(a) => a.id.clone(),
        other => panic!("fixture leaves scope one action, got {other:?}"),
    }
}

fn distincter(d: &str) -> Distincter {
    d.parse()
        .unwrap_or_else(|e| panic!("`{d}` is a distincter: {e}"))
}

/// Parse each policy with `service()` and `lower_many` the sets under their
/// distincters.
fn try_many(policies: &[(&str, &str)], schema: &PolicySchema) -> Result<LoweredPolicySet, Error> {
    let parsed: Vec<ParsedPolicySet> = policies
        .iter()
        .map(|(policy, _)| ParsedPolicySet::parse(policy, &service()).expect("parses"))
        .collect();
    let entries: Vec<(&ParsedPolicySet, Distincter)> = parsed
        .iter()
        .zip(policies)
        .map(|(p, (_, d))| (p, distincter(d)))
        .collect();
    lower_many(&entries, schema)
}

fn many(policies: &[(&str, &str)]) -> LoweredPolicySet {
    try_many(policies, &base_schema()).expect("lower_many")
}

/// Every `(action, context attribute)` pair the augmented schema declares,
/// including the `providers.<field>` pairs.
fn context_attributes(set: &LoweredPolicySet) -> BTreeSet<(String, String)> {
    let json: serde_json::Value =
        serde_json::from_str(&set.cedar_schema_json().expect("serializes")).expect("JSON");
    let mut out = BTreeSet::new();
    for (namespace, ns) in json.as_object().expect("namespaces") {
        for (action, decl) in ns["actions"].as_object().into_iter().flatten() {
            let context = &decl["appliesTo"]["context"];
            for (attr, ty) in context["attributes"].as_object().into_iter().flatten() {
                let nested = ty["attributes"].as_object().filter(|_| attr == "providers");
                match nested {
                    Some(fields) => out.extend(
                        fields
                            .keys()
                            .map(|f| (format!("{namespace}::{action}"), format!("providers.{f}"))),
                    ),
                    None => {
                        out.insert((format!("{namespace}::{action}"), attr.clone()));
                    }
                }
            }
        }
    }
    out
}

#[test]
fn lower_many_equals_the_standalone_union() {
    let merged = many(&inputs());
    let alone = standalone(&inputs());

    let mut expected_policies: Vec<_> = alone.iter().flat_map(cedar_policies).collect();
    expected_policies.sort();
    assert_eq!(cedar_policies(&merged), expected_policies, "Cedar policies");

    let expected_rules: Vec<String> = alone.iter().flat_map(rule_ids).collect();
    assert_eq!(
        rule_ids(&merged),
        expected_rules,
        "rule ids, in input order"
    );
    let indices: Vec<usize> = merged.rules().map(|r| r.rule_index).collect();
    assert_eq!(indices, (0..expected_rules.len()).collect::<Vec<_>>());

    let expected_leaves: Vec<TemporalField> = alone.iter().flat_map(leaves).collect();
    assert_eq!(leaves(&merged), expected_leaves, "leaves, in input order");
    assert_eq!(
        expected_leaves.len(),
        5,
        "the fixture must exercise several leaves"
    );
    let expected_nonrel: Vec<TemporalField> =
        alone.iter().flat_map(nonrelativized_leaves).collect();
    assert_eq!(nonrelativized_leaves(&merged), expected_nonrel);
    assert_eq!(
        merged.provider_fields().count(),
        alone
            .iter()
            .map(|s| s.provider_fields().count())
            .sum::<usize>()
    );
    for part in &alone {
        assert_eq!(merged.partition_keys(), part.partition_keys());
    }

    let expected_attributes: BTreeSet<_> = alone.iter().flat_map(context_attributes).collect();
    for leaf in &expected_leaves {
        assert!(
            expected_attributes.iter().any(|(_, attr)| *attr == leaf.id),
            "`{}` is declared",
            leaf.id
        );
    }
    assert_eq!(
        context_attributes(&merged),
        expected_attributes,
        "the base schema augmented with every part's fields"
    );
}

/// A leaf's id without its `<distincter>_<rule>` prefix, and its condition
/// without its absolute source span.
fn unprefixed(leaf: &TemporalField) -> impl PartialEq + std::fmt::Debug {
    let suffix = leaf.id[leaf.id.find("__").expect("leaf id suffix")..].to_string();
    (
        suffix,
        leaf.action.clone(),
        leaf.target_actions.clone(),
        leaf.principal.clone(),
        leaf.resource.clone(),
        leaf.condition.condition.clone(),
    )
}

/// Each `(action, attribute)` with any `<distincter>_<rule>` prefix dropped,
/// sorted, keeping repeats.
fn unprefixed_attributes(set: &LoweredPolicySet) -> Vec<(String, String)> {
    let mut out: Vec<_> = context_attributes(set)
        .into_iter()
        .map(|(action, attr)| match attr.find("__") {
            Some(at) => (action, attr[at..].to_string()),
            None => (action, attr),
        })
        .collect();
    out.sort();
    out
}

#[test]
fn lower_many_matches_lowering_the_concatenation() {
    let (a, b) = (TWO_RULES, MIXED);
    let merged = many(&[(a, "first"), (b, "second")]);
    let concatenated = lower(&format!("{a}\n{b}"), &base_schema(), "both");

    assert_eq!(
        merged.temporal_fields().map(unprefixed).collect::<Vec<_>>(),
        concatenated
            .temporal_fields()
            .map(unprefixed)
            .collect::<Vec<_>>()
    );
    assert_eq!(
        merged.event_signatures().collect::<Vec<_>>(),
        concatenated.event_signatures().collect::<Vec<_>>()
    );
    assert_eq!(
        unprefixed_attributes(&merged),
        unprefixed_attributes(&concatenated)
    );
}

/// An action schema whose context is a named reference type.
const BROKER_REF_CONTEXT_SCHEMA: &str = r#"
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

const BROKER_SYMBOL: &str = r#"
permit ( principal, action == Brokerage::Action::"GetQuote", resource )
when temporal {
    formerly within 1h Brokerage::Action::"GetQuote"::request{ input.symbol: context.input.symbol }
};
"#;

const BROKER_QTY: &str = r#"
forbid ( principal, action == Brokerage::Action::"GetQuote", resource )
when temporal {
    count for (q: Long). where (
        formerly within 10m Brokerage::Action::"GetQuote"::request{ input.qty: q }
    ) > 3
};
"#;

#[test]
fn lower_many_event_signatures_equal_each_standalone_lowering() {
    let base = PolicySchema::from_cedarschema_str(BROKER_REF_CONTEXT_SCHEMA).expect("schema");
    let parts = [(BROKER_SYMBOL, "sym"), (BROKER_QTY, "qty")];
    let merged = try_many(&parts, &base).expect("lower_many");
    let merged_sigs: Vec<_> = merged.event_signatures().collect();
    for (policy, distincter) in parts {
        let alone: Vec<_> = lower(policy, &base, distincter)
            .event_signatures()
            .collect();
        assert_eq!(merged_sigs, alone, "{distincter}: event signatures");
    }
}

/// Two rules that each fail validation.
const SECOND_WITH_ERRORS: &str = r#"
permit ( principal, action == Drupe::Action::"Read", resource )
when { context.input.bogus_in_second == "x" };

permit ( principal, action == Drupe::Action::"Read", resource )
when temporal {
    formerly within 1h Drupe::Action::"Login"::request{ input.nosuch_in_second: "x" }
};
"#;

#[test]
fn findings_render_against_their_own_policy_text() {
    let merged = many(&[(ONE_LEAF, "alpha"), (SECOND_WITH_ERRORS, "beta")]);
    let result = Validator::new().validate(&merged);
    let rendered: Vec<String> = result
        .validation_errors()
        .map(|e| format!("{:?}", miette::Report::new(e.clone())))
        .collect();
    // Both tokens also appear in the error messages, so match source lines.
    for snippet in [
        r#"when { context.input.bogus_in_second == "x" };"#,
        r#"input.nosuch_in_second: "x" }"#,
    ] {
        assert!(
            rendered.iter().any(|r| r.contains(snippet)),
            "a finding should render the second policy's `{snippet}`; got:\n{}",
            rendered.join("\n")
        );
    }
    assert!(
        rendered
            .iter()
            .all(|r| !r.contains("input.user: context.input.user")),
        "no finding renders against the first policy's text"
    );
}

#[test]
fn a_repeated_distincter_is_rejected() {
    let err = try_many(&[(ONE_LEAF, "alpha"), (MIXED, "alpha")], &base_schema())
        .expect_err("repeated distincter");
    assert!(
        matches!(&err, Error::DuplicateDistincter(d) if d == "alpha"),
        "{err:?}"
    );
}

#[test]
fn a_malformed_distincter_is_rejected_at_construction() {
    let parsed = ParsedPolicySet::parse(ONE_LEAF, &service()).expect("parses");
    for bad in ["not valid", "not-an-id", "1leading_digit", ""] {
        let err = bad.parse::<Distincter>().expect_err("malformed distincter");
        assert!(
            matches!(&err, Error::InvalidDistincter(d) if d == bad),
            "{err:?}"
        );
        let alone = parsed
            .lower_with_distincter(&base_schema(), bad)
            .expect_err("malformed distincter");
        assert_eq!(err.to_string(), alone.to_string());
    }
}

#[test]
fn a_distincter_round_trips_its_string() {
    let d = distincter("tenant_42");
    assert_eq!(d.as_str(), "tenant_42");
    assert_eq!(d.to_string(), "tenant_42");
    assert_eq!(
        Distincter::try_from("tenant_42".to_string()).expect("valid"),
        d
    );
}

#[test]
fn empty_input_is_an_error() {
    let err = try_many(&[], &base_schema()).expect_err("no policies");
    assert!(matches!(err, Error::NoPolicies), "{err:?}");
}

#[test]
fn one_entry_equals_lower_with_distincter() {
    let schema = base_schema();
    for (policy, d) in inputs() {
        let p = ParsedPolicySet::parse(policy, &service()).expect("parses");
        let d = distincter(d);
        let many = lower_many(&[(&p, d.clone())], &schema).expect("lower_many");
        let alone = p
            .lower_with_distincter(&schema, d.as_str())
            .expect("lowers");
        let policies = |set: &LoweredPolicySet| -> BTreeSet<(String, String)> {
            cedar_policies(set).into_iter().collect()
        };
        assert_eq!(policies(&many), policies(&alone), "{d}: Cedar policies");
        assert_eq!(
            many.rules().collect::<Vec<_>>(),
            alone.rules().collect::<Vec<_>>(),
            "{d}: rules"
        );
        assert_eq!(leaves(&many), leaves(&alone), "{d}: leaves");
        assert_eq!(
            many.cedar_schema_str().expect("serializes"),
            alone.cedar_schema_str().expect("serializes"),
            "{d}: schema"
        );
    }
}

#[test]
fn mismatched_service_schema_is_an_error() {
    let (first, second) = (ServiceSchema::defaults(), ServiceSchema::defaults());
    let a = ParsedPolicySet::parse(ONE_LEAF, &first).expect("parses");
    let b = ParsedPolicySet::parse(MIXED, &second).expect("parses");
    let err = lower_many(
        &[(&a, distincter("a")), (&b, distincter("b"))],
        &base_schema(),
    )
    .expect_err("different service schemas");
    assert!(matches!(err, Error::MismatchedServiceSchema(1)), "{err:?}");
}

#[test]
fn clones_of_one_service_schema_are_accepted() {
    let service = ServiceSchema::defaults();
    let a = ParsedPolicySet::parse(ONE_LEAF, &service.clone()).expect("parses");
    let b = ParsedPolicySet::parse(MIXED, &service.clone()).expect("parses");
    lower_many(
        &[(&a, distincter("a")), (&b, distincter("b"))],
        &base_schema(),
    )
    .expect("clones of one service schema");
}

#[test]
fn an_authorizer_decides_over_a_lower_many_result() {
    let merged = many(&[(ONE_LEAF, "alpha"), (MIXED, "gamma")]);
    let mut authorizer = Authorizer::new(merged);
    let login = |ts: i64, user: &str| {
        Event::builder("Drupe::Action::Login", "request")
            .timestamp(ts)
            .principal("Drupe::OAuthUser::\"p\"")
            .resource("Drupe::Gateway::\"gw\"")
            .field("input", "user", Value::String(user.to_string()))
            .field("input", "amount", Value::Int(1))
            .request_context("input", "user", Value::String(user.to_string()))
            .request_context("input", "amount", Value::Int(1))
            .build()
    };
    let reasons = |r: &dogwood_language::Response| -> Vec<(usize, String)> {
        r.diagnostics()
            .reason()
            .map(|r| (r.rule_index, r.cedar_policy_id.clone()))
            .collect()
    };

    // Part 2's Cedar-only rule (merged rule 1).
    let first = authorizer
        .is_authorized(&login(0, "alice"))
        .expect("decides");
    assert_eq!(first.decision(), Decision::Allow);
    assert!(
        reasons(&first).contains(&(1, "gamma_0".to_string())),
        "{:?}",
        reasons(&first)
    );

    // Part 2's temporal rule (merged rule 2), satisfied by the earlier login.
    let second = authorizer
        .is_authorized(&login(60, "bob"))
        .expect("decides");
    assert_eq!(second.decision(), Decision::Allow);
    assert_eq!(reasons(&second), [(2, "gamma_1".to_string())]);
}

#[test]
fn lower_many_rejects_arrays_in_temporal_predicates_like_lower() {
    let src = r#"
permit ( principal, action == Drupe::Action::"Read", resource )
when temporal {
    formerly within 1h Drupe::Action::"Login"::request{ input.tags: ["a","b"] }
};
"#;
    let err =
        try_many(&[(src, "d")], &base_schema()).expect_err("array constant in temporal predicate");
    assert!(format!("{err}").contains("array constants"), "{err}");
    let alone = ParsedPolicySet::parse(src, &service())
        .expect("parses")
        .lower_with_distincter(&base_schema(), "d")
        .expect_err("array constant in temporal predicate");
    assert_eq!(format!("{err}"), format!("{alone}"));
}

fn entries(policies: &[(&'static str, &'static str)]) -> Vec<(&'static str, Distincter)> {
    policies.iter().map(|(p, d)| (*p, distincter(d))).collect()
}

#[test]
fn from_many_str_equals_lower_many_over_parsed_input() {
    let schema = base_schema();
    let fused =
        LoweredPolicySet::from_many_str(&entries(&inputs()), &service(), &schema).expect("fused");
    let two_phase = try_many(&inputs(), &schema).expect("lower_many");
    let policies = |set: &LoweredPolicySet| -> BTreeSet<(String, String)> {
        cedar_policies(set).into_iter().collect()
    };
    assert_eq!(policies(&fused), policies(&two_phase), "Cedar policies");
    assert_eq!(
        fused.rules().collect::<Vec<_>>(),
        two_phase.rules().collect::<Vec<_>>(),
        "rules"
    );
    assert_eq!(leaves(&fused), leaves(&two_phase), "leaves");
    assert_eq!(
        fused.cedar_schema_str().expect("serializes"),
        two_phase.cedar_schema_str().expect("serializes"),
        "schema"
    );
}

#[test]
fn from_many_str_of_nothing_is_the_base_schema() {
    let set = LoweredPolicySet::from_many_str(&[], &service(), &base_schema()).expect("lowers");
    assert_eq!(set.as_cedar().policies().count(), 0);
    assert_eq!(set.rules().count(), 0);
    assert_eq!(set.temporal_fields().count(), 0);
    assert_eq!(
        set.cedar_schema_str().expect("serializes"),
        cedar_policy::SchemaFragment::from_cedarschema_str(SCHEMA)
            .expect("fragment")
            .0
            .to_cedarschema()
            .expect("serializes")
    );
}

#[test]
fn from_many_str_returns_the_first_parse_error() {
    let broken = "permit ( principal, action, resource ) when { ;";
    let err = LoweredPolicySet::from_many_str(
        &entries(&[(ONE_LEAF, "alpha"), (broken, "beta")]),
        &service(),
        &base_schema(),
    )
    .expect_err("syntax error");
    let alone =
        LoweredPolicySet::from_str(broken, &service(), &base_schema()).expect_err("syntax error");
    assert!(matches!(alone, Error::Parse(_)), "{alone:?}");
    assert!(matches!(err, Error::Parse(_)), "{err:?}");
    assert_eq!(err.to_string(), alone.to_string());
}

#[test]
fn from_many_str_rejects_a_repeated_distincter() {
    let err = LoweredPolicySet::from_many_str(
        &entries(&[(ONE_LEAF, "alpha"), (MIXED, "alpha")]),
        &service(),
        &base_schema(),
    )
    .expect_err("repeated distincter");
    assert!(
        matches!(&err, Error::DuplicateDistincter(d) if d == "alpha"),
        "{err:?}"
    );
}
