//! Pre-lowering diagnostics on [`ParsedPolicySet`] — the schema-free queries a
//! caller runs to fail fast before an action schema (and expensive
//! schema-generation) is available:
//!
//!   * `policy_count()` / `policies().len()` — enforce "one policy per
//!     submission";
//!   * per-policy `temporal_count()` / `uses_temporal()` — region-gate and
//!     quota temporal usage (counted per `temporal { … }` block);
//!   * per-policy `provider_count()` / `uses_providers()` /
//!     `provider_invocations()` — region-gate and observe provider usage;
//!   * per-policy `undeclared_providers()` — surface, early, the same fact the
//!     validation pass reports, so a caller can classify unavailable-here vs.
//!     typo against its own catalog.
//!
//! All queries run against a [`ServiceSchema`] alone (no action schema), and
//! see the *macro-expanded* tree.

use std::collections::BTreeSet;

use dogwood_language::{ParsedPolicySet, ProviderDeclarations, ServiceSchema};

/// A ServiceSchema whose declarations know `Risk::Score` and `Text::Match`
/// (both zero-typed here — only the *names* matter to these diagnostics).
fn service_with_providers() -> ServiceSchema {
    let providers = ProviderDeclarations::from_json(
        r#"{
          "availableProviders": {
            "Risk::Score": {
              "argumentTypes": [ { "paramType": "string" } ],
              "outputType": { "paramType": "long" }
            },
            "Text::Match": {
              "argumentTypes": [ { "paramType": "string" } ],
              "outputType": { "paramType": "bool" }
            }
          }
        }"#,
    )
    .expect("providers json parses");
    ServiceSchema::builder()
        .providers(providers)
        .build()
        .expect("service schema builds")
}

/// The default ServiceSchema — no provider declarations at all (so every
/// provider invocation is "undeclared").
fn service_no_providers() -> ServiceSchema {
    ServiceSchema::defaults()
}

// ─── policy_count / policies().len() ─────────────────────────────────

#[test]
fn policy_count_reflects_the_number_of_rules() {
    let one = r#"permit ( principal, action == Svc::Action::"Read", resource );"#;
    let three = r#"
        permit ( principal, action == Svc::Action::"Read", resource );
        forbid ( principal, action == Svc::Action::"Write", resource );
        permit ( principal, action == Svc::Action::"List", resource );
    "#;

    let p1 = ParsedPolicySet::parse(one, &service_no_providers()).expect("parses");
    assert_eq!(p1.policy_count(), 1);
    // The iterator is ExactSizeIterator: len() agrees and does not consume.
    assert_eq!(p1.policies().len(), 1);

    let p3 = ParsedPolicySet::parse(three, &service_no_providers()).expect("parses");
    assert_eq!(p3.policy_count(), 3);
    assert_eq!(p3.policies().len(), 3);
    assert_eq!(p3.policies().count(), 3);
}

#[test]
fn policies_are_indexed_in_source_order() {
    let src = r#"
        permit ( principal, action == Svc::Action::"Read", resource );
        forbid ( principal, action == Svc::Action::"Write", resource );
    "#;
    let parsed = ParsedPolicySet::parse(src, &service_no_providers()).expect("parses");
    let indices: Vec<usize> = parsed.policies().map(|p| p.index()).collect();
    assert_eq!(indices, vec![0, 1]);
}

// ─── temporal_count (per block) ──────────────────────────────────────

#[test]
fn temporal_count_is_zero_for_pure_cedar() {
    let src = r#"permit ( principal, action == Svc::Action::"Read", resource )
                 when { context.input.doc == "x" };"#;
    let parsed = ParsedPolicySet::parse(src, &service_no_providers()).expect("parses");
    let p = parsed.policies().next().unwrap();
    assert_eq!(p.temporal_count(), 0);
    assert!(!p.uses_temporal());
}

#[test]
fn temporal_count_counts_one_per_block() {
    // A tagged `when temporal { … }` clause is one block.
    let src = r#"
        permit ( principal, action == Drupe::Action::"SellShares", resource )
        when temporal {
            formerly within 1h Drupe::Action::"ApproveSale"::request{input.stock: context.input.stock}
        };
    "#;
    let parsed = ParsedPolicySet::parse(src, &service_no_providers()).expect("parses");
    let p = parsed.policies().next().unwrap();
    assert_eq!(p.temporal_count(), 1);
    assert!(p.uses_temporal());
}

#[test]
fn temporal_count_sums_multiple_blocks_including_nested() {
    // Two temporal blocks: one nested inside a Cedar `&&` mid-expression, one
    // as a second clause. `temporal { … }` is a valid primary, so it can sit
    // inside an ordinary `when { … }` expression.
    let src = r#"
        permit ( principal, action == Drupe::Action::"SellShares", resource )
        when {
            context.input.shares > 0
            && temporal { formerly within 1h Drupe::Action::"ApproveSale"::request{input.stock: context.input.stock} }
        }
        when temporal {
            formerly within 2h Drupe::Action::"Login"::request{input.user: context.input.user}
        };
    "#;
    let parsed = ParsedPolicySet::parse(src, &service_no_providers()).expect("parses");
    let p = parsed.policies().next().unwrap();
    assert_eq!(p.temporal_count(), 2, "two temporal blocks (one nested)");
    assert!(p.uses_temporal());
}

// ─── temporal_conditions (parsed AST view) ───────────────────────────

#[test]
fn temporal_conditions_is_empty_for_pure_cedar() {
    let src = r#"permit ( principal, action == Svc::Action::"Read", resource )
                 when { context.input.doc == "x" };"#;
    let parsed = ParsedPolicySet::parse(src, &service_no_providers()).expect("parses");
    let p = parsed.policies().next().unwrap();
    assert_eq!(p.temporal_conditions().count(), 0);
}

#[test]
fn temporal_conditions_yields_one_condition_per_block() {
    // Two temporal blocks (one nested in a Cedar `&&`, one a second clause):
    // the parsed-condition view returns one entry per block, agreeing with
    // `temporal_count`.
    let src = r#"
        permit ( principal, action == Drupe::Action::"SellShares", resource )
        when {
            context.input.shares > 0
            && temporal { formerly within 1h Drupe::Action::"ApproveSale"::request{input.stock: context.input.stock} }
        }
        when temporal {
            formerly within 2h Drupe::Action::"Login"::request{input.user: context.input.user}
        };
    "#;
    let parsed = ParsedPolicySet::parse(src, &service_no_providers()).expect("parses");
    let p = parsed.policies().next().unwrap();
    assert_eq!(p.temporal_conditions().count(), p.temporal_count());
    assert_eq!(p.temporal_conditions().count(), 2);
}

// ─── provider counts / invocations ───────────────────────────────────

#[test]
fn provider_queries_are_zero_for_pure_cedar() {
    let src = r#"permit ( principal, action == Svc::Action::"Read", resource )
                 when { context.input.doc == "x" };"#;
    let parsed = ParsedPolicySet::parse(src, &service_with_providers()).expect("parses");
    let p = parsed.policies().next().unwrap();
    assert_eq!(p.provider_count(), 0);
    assert!(!p.uses_providers());
    assert_eq!(p.provider_invocations().count(), 0);
    assert_eq!(p.undeclared_providers().count(), 0);
}

#[test]
fn provider_invocations_lists_names_with_multiplicity() {
    // `Risk::Score` invoked twice, `Text::Match` once — bare-call and
    // method-chained forms both bottom out at the `Ns::Fn(...)` call.
    let src = r#"
        permit ( principal, action == Svc::Action::"Read", resource )
        when {
            Risk::Score(context.input.doc) < 3
            && Text::Match(context.input.doc) == true
            && Risk::Score(context.input.other) < 5
        };
    "#;
    let parsed = ParsedPolicySet::parse(src, &service_with_providers()).expect("parses");
    let p = parsed.policies().next().unwrap();

    assert_eq!(p.provider_count(), 3, "three invocation sites");
    assert!(p.uses_providers());

    let names: Vec<String> = p.provider_invocations().collect();
    assert_eq!(
        names,
        vec![
            "Risk::Score".to_string(),
            "Text::Match".to_string(),
            "Risk::Score".to_string()
        ],
        "source order, with multiplicity"
    );

    // Distinct set — the "which providers are invoked" observability query.
    let distinct: BTreeSet<String> = p.provider_invocations().collect();
    assert_eq!(
        distinct,
        BTreeSet::from(["Risk::Score".to_string(), "Text::Match".to_string()])
    );
}

#[test]
fn provider_invocation_counted_once_through_a_method_chain() {
    // A method-chained provider is a single invocation site.
    let src = r#"
        permit ( principal, action == Svc::Action::"Read", resource )
        when { Risk::Score(context.input.doc).normalized() < 3 };
    "#;
    let parsed = ParsedPolicySet::parse(src, &service_with_providers()).expect("parses");
    let p = parsed.policies().next().unwrap();
    assert_eq!(p.provider_count(), 1);
    assert_eq!(
        p.provider_invocations().collect::<Vec<_>>(),
        vec!["Risk::Score".to_string()]
    );
}

// ─── declared vs. undeclared ─────────────────────────────────────────

#[test]
fn undeclared_providers_is_empty_when_all_declared() {
    let src = r#"
        permit ( principal, action == Svc::Action::"Read", resource )
        when { Risk::Score(context.input.doc) < 3 };
    "#;
    let parsed = ParsedPolicySet::parse(src, &service_with_providers()).expect("parses");
    let p = parsed.policies().next().unwrap();
    // Invoked, but declared in the ServiceSchema -> not flagged undeclared.
    assert!(p.uses_providers());
    assert_eq!(p.undeclared_providers().count(), 0);
}

#[test]
fn undeclared_providers_flags_names_absent_from_the_schema() {
    // `Risk::Score` is declared; `Bogus::Typo` is not. Both parse fine (an
    // undeclared provider is not a parse error), and both are invocations —
    // only the undeclared one is flagged.
    let src = r#"
        permit ( principal, action == Svc::Action::"Read", resource )
        when {
            Risk::Score(context.input.doc) < 3
            && Bogus::Typo(context.input.doc) == true
        };
    "#;
    let parsed = ParsedPolicySet::parse(src, &service_with_providers()).expect("parses");
    let p = parsed.policies().next().unwrap();

    assert_eq!(p.provider_count(), 2, "both are invocation sites");
    let undeclared: Vec<String> = p.undeclared_providers().collect();
    assert_eq!(undeclared, vec!["Bogus::Typo".to_string()]);
}

#[test]
fn all_providers_undeclared_when_schema_declares_none() {
    // With the default (no providers) schema, every invocation is undeclared.
    let src = r#"
        permit ( principal, action == Svc::Action::"Read", resource )
        when { Risk::Score(context.input.doc) < 3 };
    "#;
    let parsed = ParsedPolicySet::parse(src, &service_no_providers()).expect("parses");
    let p = parsed.policies().next().unwrap();
    assert!(p.uses_providers());
    assert_eq!(
        p.undeclared_providers().collect::<Vec<_>>(),
        vec!["Risk::Score".to_string()]
    );
}

// ─── across multiple policies ────────────────────────────────────────

#[test]
fn per_policy_queries_are_scoped_to_each_policy() {
    // Policy 0: temporal only. Policy 1: provider only. Policy 2: pure Cedar.
    let src = r#"
        permit ( principal, action == Drupe::Action::"SellShares", resource )
        when temporal {
            formerly within 1h Drupe::Action::"ApproveSale"::request{input.stock: context.input.stock}
        };

        permit ( principal, action == Svc::Action::"Read", resource )
        when { Risk::Score(context.input.doc) < 3 };

        permit ( principal, action == Svc::Action::"List", resource )
        when { context.input.doc == "x" };
    "#;
    let parsed = ParsedPolicySet::parse(src, &service_with_providers()).expect("parses");
    let policies: Vec<_> = parsed.policies().collect();
    assert_eq!(policies.len(), 3);

    // Policy 0: temporal, no providers.
    assert_eq!(policies[0].temporal_count(), 1);
    assert!(policies[0].uses_temporal());
    assert!(!policies[0].uses_providers());

    // Policy 1: providers, no temporal.
    assert!(!policies[1].uses_temporal());
    assert_eq!(policies[1].provider_count(), 1);
    assert!(policies[1].uses_providers());

    // Policy 2: neither.
    assert!(!policies[2].uses_temporal());
    assert!(!policies[2].uses_providers());

    // Set-level composition of the colleague's quota check #5: how many
    // policies carry temporal terms (this submission's contribution).
    let with_temporal = parsed.policies().filter(|p| p.uses_temporal()).count();
    assert_eq!(with_temporal, 1);

    // Quota check #4: worst per-policy temporal count.
    let worst = parsed.policies().map(|p| p.temporal_count()).max().unwrap();
    assert_eq!(worst, 1);
}

// ─── macro expansion is reflected ────────────────────────────────────

#[test]
fn diagnostics_see_through_macro_expansion() {
    // A provider invocation passed as a macro *argument* is substituted into
    // the macro body during expansion. The diagnostics run on the
    // post-expansion tree, so the substituted `Risk::Score(...)` call is
    // counted. (A `::` call cannot appear *inside* a `def cedar` body — that
    // is rejected as macro-in-macro — so the argument-substitution form is the
    // way a macro contributes a provider invocation.)
    let src = r#"
        def cedar at_least(?x, ?n) { ?x >= ?n };
        permit ( principal, action == Svc::Action::"Read", resource )
        when { at_least(Risk::Score(context.input.doc), 3) };
    "#;
    let parsed = ParsedPolicySet::parse(src, &service_with_providers()).expect("parses");
    let p = parsed.policies().next().unwrap();
    assert_eq!(
        p.provider_count(),
        1,
        "the provider invocation substituted in by expansion is counted"
    );
    assert_eq!(
        p.provider_invocations().collect::<Vec<_>>(),
        vec!["Risk::Score".to_string()]
    );
}

// ─── reject_temporal_arrays gate ─────────────────────────────────────

#[test]
fn reject_temporal_arrays_passes_for_pure_cedar() {
    let src = r#"
        permit ( principal, action == Svc::Action::"Read", resource )
        when { context.input.x == 1 };
    "#;
    let parsed = ParsedPolicySet::parse(src, &service_no_providers()).expect("parses");
    assert!(parsed.reject_temporal_arrays().is_ok());
}

#[test]
fn reject_temporal_arrays_passes_for_temporal_without_arrays() {
    let src = r#"
        forbid (principal, action == Svc::Action::"Write", resource)
        when temporal {
            formerly within 1h Svc::Action::"Write"::request{
                input.doc: context.input.doc
            }
        };
    "#;
    let parsed = ParsedPolicySet::parse(src, &service_no_providers()).expect("parses");
    assert!(
        parsed.reject_temporal_arrays().is_ok(),
        "temporal without arrays should pass"
    );
}

#[test]
fn reject_temporal_arrays_rejects_array_in_predicate_arg() {
    let src = r#"
        forbid (principal, action == Svc::Action::"Write", resource)
        when temporal {
            formerly within 1h Svc::Action::"Write"::request{
                input.user: context.input.user,
                input.tags: ["secret", "pii"]
            }
        };
    "#;
    let parsed = ParsedPolicySet::parse(src, &service_no_providers()).expect("parses");
    let err = parsed.reject_temporal_arrays().unwrap_err();
    let msg = err.to_string();
    assert!(
        msg.contains("array constants"),
        "error should mention array constants, got: {msg}"
    );
    assert!(
        msg.contains("scalar values"),
        "error should suggest scalar values, got: {msg}"
    );
}

#[test]
fn reject_temporal_arrays_rejects_array_in_nested_formerly() {
    let src = r#"
        permit (principal, action == Svc::Action::"Read", resource)
        when temporal {
            formerly within 2h Svc::Action::"Read"::request{
                input.categories: ["a", "b", "c"]
            }
        };
    "#;
    let parsed = ParsedPolicySet::parse(src, &service_no_providers()).expect("parses");
    assert!(
        parsed.reject_temporal_arrays().is_err(),
        "array in predicate arg should be rejected"
    );
}

#[test]
fn reject_temporal_arrays_passes_multiple_temporal_blocks_without_arrays() {
    let src = r#"
        permit (principal, action == Svc::Action::"Write", resource)
        when temporal {
            formerly within 1h Svc::Action::"Read"::request{
                input.doc: context.input.doc
            }
        }
        when temporal {
            formerly within 2h Svc::Action::"Write"::request{
                input.doc: context.input.doc
            }
        };
    "#;
    let parsed = ParsedPolicySet::parse(src, &service_no_providers()).expect("parses");
    assert!(
        parsed.reject_temporal_arrays().is_ok(),
        "temporal without arrays should pass even with multiple blocks"
    );
}
