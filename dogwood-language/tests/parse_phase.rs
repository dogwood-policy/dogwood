//! The schema-free **parse** phase ([`ParsedPolicySet::parse`]).
//!
//! `parse` takes only a [`ServiceSchema`] — no action schema — and checks
//! syntax and macro resolution. These tests pin that contract and its boundary:
//!
//!   1. valid source parses with no action schema, and lowers once one arrives;
//!   2. a syntax error is reported by `parse` (`Error::Parse`);
//!   3. a macro-resolution error is reported by `parse` (`Error::Macro`) — the
//!      other class `parse` resolves without a schema;
//!   4. a *schema-dependent* error (unknown attribute) is **not** caught by
//!      `parse` — it parses fine and only surfaces at `lower` + validation.
//!
//! Every assertion here calls `parse` with a `ServiceSchema` only — no
//! `PolicySchema` is constructed until step 1/4 deliberately lowers.

use dogwood_language::{Error, ParsedPolicySet, PolicySchema, ServiceSchema, Validator};

const SCHEMA: &str = r#"
namespace Drupe {
  type ReadInput = { user: String };
  type TransferInput = {
    amount: Long,
    user: String
  };
  entity Gateway;
  entity OAuthUser = { id: String } tags String;
  action "Read" appliesTo {
    principal: [OAuthUser],
    resource: [Gateway],
    context: { input: ReadInput }
  };
  action "Transfer" appliesTo {
    principal: [OAuthUser],
    resource: [Gateway],
    context: {
      input: TransferInput
    }
  };
}
"#;

fn service() -> ServiceSchema {
    ServiceSchema::defaults()
}

#[test]
fn valid_source_parses_with_no_action_schema_then_lowers() {
    // Parse succeeds against the ServiceSchema alone, with no PolicySchema
    // anywhere. The action schema is only introduced afterward, to show the
    // parsed set lowers cleanly once it arrives.
    let src = r#"permit ( principal, action == Drupe::Action::"Read", resource )
                 when { context.input.user == "alice" };"#;

    let parsed = ParsedPolicySet::parse(src, &service()).expect("valid source parses");

    // Only now does an action schema enter the picture.
    let policy_schema = PolicySchema::from_cedarschema_str(SCHEMA).expect("action schema");
    let lowered = parsed.lower(&policy_schema).expect("parsed set lowers");
    assert!(Validator::new().validate(&lowered).validation_passed());
}

#[test]
fn syntax_error_fails_fast_at_parse() {
    // `permitt` is not a valid effect keyword — a pure syntax error, reported
    // with no action schema needed.
    let src = r#"permitt ( principal, action, resource );"#;

    match ParsedPolicySet::parse(src, &service()) {
        Err(Error::Parse(errs)) => {
            assert!(
                errs.iter().next().is_some(),
                "carries a located parse error"
            );
        }
        Err(e) => panic!("expected a parse error, got: {e}"),
        Ok(_) => panic!("syntactically broken source must not parse"),
    }
}

#[test]
fn unknown_macro_call_fails_fast_at_parse() {
    // A call to a name that is neither a Cedar built-in nor a declared macro is
    // resolved (and rejected) during macro expansion — which `parse` runs, and
    // which needs no action schema, so it is reported here.
    let src = r#"permit ( principal, action == Drupe::Action::"Read", resource )
                 when { not_a_declared_macro(principal) };"#;

    match ParsedPolicySet::parse(src, &service()) {
        Err(Error::Macro(_)) => {}
        Err(e) => panic!("expected a macro-resolution error, got: {e}"),
        Ok(_) => panic!("an unknown macro call must be rejected at parse"),
    }
}

#[test]
fn valid_temporal_exists_expression_parses_lowers_validates() {
    let src = r#"permit( principal, action, resource )
                when temporal { exists (p: Long). (p == 5) };"#;
    let policy_schema = PolicySchema::from_cedarschema_str(SCHEMA).expect("action schema");
    let parsed = ParsedPolicySet::parse(src, &service()).expect("valid source parses");
    let lowered = parsed.lower(&policy_schema).expect("parsed set lowers");
    assert!(Validator::new().validate(&lowered).validation_passed());
}

#[test]
fn stray_macro_sigil_binder_in_temporal_exists_binder_fails_gracefully_no_panic() {
    // A stray macro-sigil binder in the binder of a temporal exists expression should not cause a panic
    // and should be gracefully rejected with an error at some phase, 
    // either during parsing, lowering, or validation.
    let src = r#"permit( principal, action, resource )
                when temporal { exists (?p: Long). (p == 5) };"#;
    let policy_schema = PolicySchema::from_cedarschema_str(SCHEMA).expect("action schema");

    let rejected = match ParsedPolicySet::parse(src, &service()) {
        // Rejected at parse.
        Err(_) => true,
        Ok(parsed) => { 
            match parsed.lower(&policy_schema) {
                // Rejected at lowering.
                Err(_) => true,
                // Otherwise, rejected at validation.
                Ok(lowered) => !Validator::new().validate(&lowered).validation_passed(),
            }
        }
    };
    assert!(
        rejected,
        "a macro-sigil binder outside a macro body must be rejected \
         gracefully during parsing, lowering, or validation"
    );
}

#[test]
fn stray_macro_sigil_binder_in_temporal_exists_no_free_variables_fails_gracefully_no_panic() {
    // A stray macro-sigil binder in the binder of a temporal exists expression should not cause a panic
    // and should be gracefully rejected with an error at some phase, 
    // either during parsing, lowering, or validation.
    let src = r#"permit( principal, action, resource )
                when temporal { exists (?p: Long). (1 == 1) };"#;
    let policy_schema = PolicySchema::from_cedarschema_str(SCHEMA).expect("action schema");

    let rejected = match ParsedPolicySet::parse(src, &service()) {
        // Rejected at parse.
        Err(_) => true,
        Ok(parsed) => { 
            match parsed.lower(&policy_schema) {
                // Rejected at lowering.
                Err(_) => true,
                // Otherwise, rejected at validation.
                Ok(lowered) => !Validator::new().validate(&lowered).validation_passed(),
            }
        }
    };
    assert!(
        rejected,
        "a macro-sigil binder outside a macro body must be rejected \
         gracefully during parsing, lowering, or validation"
    );
}

#[test]
fn stray_macro_sigil_binder_in_temporal_exists_body_fails_gracefully_no_panic() {
    // A stray macro-sigil binder in the body of a temporal exists expression should not cause a panic
    // and should be gracefully rejected with an error at some phase, 
    // either during parsing, lowering, or validation.
    let src = r#"permit( principal, action, resource )
                when temporal { exists (p: Long). (?p == 5) };"#;
    let policy_schema = PolicySchema::from_cedarschema_str(SCHEMA).expect("action schema");

    let rejected = match ParsedPolicySet::parse(src, &service()) {
        // Rejected at parse.
        Err(_) => true,
        Ok(parsed) => { 
            match parsed.lower(&policy_schema) {
                // Rejected at lowering.
                Err(_) => true,
                // Otherwise, rejected at validation.
                Ok(lowered) => !Validator::new().validate(&lowered).validation_passed(),
            }
        }
    };
    assert!(
        rejected,
        "a macro-sigil binder outside a macro body must be rejected \
         gracefully during parsing, lowering, or validation"
    );
}

#[test]
fn stray_macro_sigil_binder_in_temporal_exists_binder_and_body_fails_gracefully_no_panic() {
    // A stray macro-sigil binder in the binder and body of a temporal exists expression should not cause a panic
    // and should be gracefully rejected with an error at some phase, 
    // either during parsing, lowering, or validation.
    let src = r#"permit( principal, action, resource )
                when temporal { exists (?p: Long). (?p == 5) };"#;
    let policy_schema = PolicySchema::from_cedarschema_str(SCHEMA).expect("action schema");

    let rejected = match ParsedPolicySet::parse(src, &service()) {
        // Rejected at parse.
        Err(_) => true,
        Ok(parsed) => { 
            match parsed.lower(&policy_schema) {
                // Rejected at lowering.
                Err(_) => true,
                // Otherwise, rejected at validation.
                Ok(lowered) => !Validator::new().validate(&lowered).validation_passed(),
            }
        }
    };
    assert!(
        rejected,
        "a macro-sigil binder outside a macro body must be rejected \
         gracefully during parsing, lowering, or validation"
    );
}

#[test]
fn valid_temporal_count_expression_parses_lowers_validates() {
    let src = r#"permit( principal, action, resource )
                when temporal { 
                    count for (t: Timepoint), (id: String). where (
                        Drupe::Action::"Read"::request{ input.user: id } && id == "alice" && tp(t)
                    ) >= 2
                };"#;
    let policy_schema = PolicySchema::from_cedarschema_str(SCHEMA).expect("action schema");
    let parsed = ParsedPolicySet::parse(src, &service()).expect("valid source parses");
    let lowered = parsed.lower(&policy_schema).expect("parsed set lowers");
    assert!(Validator::new().validate(&lowered).validation_passed());
}

#[test]
fn stray_macro_sigil_binder_in_timepoint_in_temporal_count_expression_binder_fails_gracefully_no_panic() {
    // A stray macro-sigil binder in the timepoint bound variable binder of a temporal count expression should not cause a panic
    // and should be gracefully rejected with an error at some phase, 
    // either during parsing, lowering, or validation.
    let src = r#"permit( principal, action, resource )
                when temporal { 
                    count for (?t: Timepoint), (id: String). where (
                        Drupe::Action::"Read"::request{ input.user: id } && id == "alice" && tp(t)
                    ) >= 2
                };"#;
    let policy_schema = PolicySchema::from_cedarschema_str(SCHEMA).expect("action schema");

    let rejected = match ParsedPolicySet::parse(src, &service()) {
        // Rejected at parse.
        Err(_) => true,
        Ok(parsed) => { 
            match parsed.lower(&policy_schema) {
                // Rejected at lowering.
                Err(_) => true,
                // Otherwise, rejected at validation.
                Ok(lowered) => !Validator::new().validate(&lowered).validation_passed(),
            }
        }
    };
    assert!(
        rejected,
        "a macro-sigil binder outside a macro body must be rejected \
         gracefully during parsing, lowering, or validation"
    );
}

#[test]
fn stray_macro_sigil_binder_in_timepoint_in_temporal_count_expression_body_fails_gracefully_no_panic() {
    // A stray macro-sigil binder in the timepoint bound variable in the body of a temporal count expression should not cause a panic
    // and should be gracefully rejected with an error at some phase, 
    // either during parsing, lowering, or validation.
    let src = r#"permit( principal, action, resource )
                when temporal { 
                    count for (t: Timepoint), (id: String). where (
                        Drupe::Action::"Read"::request{ input.user: id } && id == "alice" && tp(?t)
                    ) >= 2
                };"#;
    let policy_schema = PolicySchema::from_cedarschema_str(SCHEMA).expect("action schema");

    let rejected = match ParsedPolicySet::parse(src, &service()) {
        // Rejected at parse.
        Err(_) => true,
        Ok(parsed) => { 
            match parsed.lower(&policy_schema) {
                // Rejected at lowering.
                Err(_) => true,
                // Otherwise, rejected at validation.
                Ok(lowered) => !Validator::new().validate(&lowered).validation_passed(),
            }
        }
    };
    assert!(
        rejected,
        "a macro-sigil binder outside a macro body must be rejected \
         gracefully during parsing, lowering, or validation"
    );
}

#[test]
fn stray_macro_sigil_binder_in_timepoint_in_temporal_count_expression_binder_and_body_fails_gracefully_no_panic() {
    // A stray macro-sigil binder in the timepoint bound variable binder and body of a temporal count expression should not cause a panic
    // and should be gracefully rejected with an error at some phase, 
    // either during parsing, lowering, or validation.
    let src = r#"permit( principal, action, resource )
                when temporal { 
                    count for (?t: Timepoint), (id: String). where (
                        Drupe::Action::"Read"::request{ input.user: id } && id == "alice" && tp(?t)
                    ) >= 2
                };"#;
    let policy_schema = PolicySchema::from_cedarschema_str(SCHEMA).expect("action schema");

    let rejected = match ParsedPolicySet::parse(src, &service()) {
        // Rejected at parse.
        Err(_) => true,
        Ok(parsed) => { 
            match parsed.lower(&policy_schema) {
                // Rejected at lowering.
                Err(_) => true,
                // Otherwise, rejected at validation.
                Ok(lowered) => !Validator::new().validate(&lowered).validation_passed(),
            }
        }
    };
    assert!(
        rejected,
        "a macro-sigil binder outside a macro body must be rejected \
         gracefully during parsing, lowering, or validation"
    );
}

#[test]
fn stray_macro_sigil_binder_in_bound_var_in_temporal_count_expression_binder_fails_gracefully_no_panic() {
    // A stray macro-sigil binder in the (non-timepoint) bound variable binder of a temporal count expression should not cause a panic
    // and should be gracefully rejected with an error at some phase, 
    // either during parsing, lowering, or validation.
    let src = r#"permit( principal, action, resource )
                when temporal { 
                    count for (t: Timepoint), (?id: String). where (
                        Drupe::Action::"Read"::request{ input.user: id } && id == "alice" && tp(t)
                    ) >= 2
                };"#;
    let policy_schema = PolicySchema::from_cedarschema_str(SCHEMA).expect("action schema");

    let rejected = match ParsedPolicySet::parse(src, &service()) {
        // Rejected at parse.
        Err(_) => true,
        Ok(parsed) => { 
            match parsed.lower(&policy_schema) {
                // Rejected at lowering.
                Err(_) => true,
                // Otherwise, rejected at validation.
                Ok(lowered) => !Validator::new().validate(&lowered).validation_passed(),
            }
        }
    };
    assert!(
        rejected,
        "a macro-sigil binder outside a macro body must be rejected \
         gracefully during parsing, lowering, or validation"
    );
}

#[test]
fn stray_macro_sigil_binder_in_bound_var_in_temporal_count_expression_body_fails_gracefully_no_panic() {
    // A stray macro-sigil binder in the (non-timepoint) bound variable in the body of a temporal count expression should not cause a panic
    // and should be gracefully rejected with an error at some phase, 
    // either during parsing, lowering, or validation.
    let src = r#"permit( principal, action, resource )
                when temporal { 
                    count for (t: Timepoint), (id: String). where (
                        Drupe::Action::"Read"::request{ input.user: id } && ?id == "alice" && tp(t)
                    ) >= 2
                };"#;
    let policy_schema = PolicySchema::from_cedarschema_str(SCHEMA).expect("action schema");

    let rejected = match ParsedPolicySet::parse(src, &service()) {
        // Rejected at parse.
        Err(_) => true,
        Ok(parsed) => { 
            match parsed.lower(&policy_schema) {
                // Rejected at lowering.
                Err(_) => true,
                // Otherwise, rejected at validation.
                Ok(lowered) => !Validator::new().validate(&lowered).validation_passed(),
            }
        }
    };
    assert!(
        rejected,
        "a macro-sigil binder outside a macro body must be rejected \
         gracefully during parsing, lowering, or validation"
    );
}

#[test]
fn stray_macro_sigil_binder_in_all_bound_var_occurrences_in_temporal_count_expression_fails_gracefully_no_panic() {
    // A stray macro-sigil binder in all occurrences (binder, projection field variable, and body) of a (non-timepoint) bound variable in a temporal count expression 
    // should not cause a panic and should be gracefully rejected with an error at some phase, 
    // either during parsing, lowering, or validation.
    let src = r#"permit( principal, action, resource )
                when temporal { 
                    count for (t: Timepoint), (?id: String). where (
                        Drupe::Action::"Read"::request{ input.user: ?id } && ?id == "alice" && tp(t)
                    ) >= 2
                };"#;
    let policy_schema = PolicySchema::from_cedarschema_str(SCHEMA).expect("action schema");

    let rejected = match ParsedPolicySet::parse(src, &service()) {
        // Rejected at parse.
        Err(_) => true,
        Ok(parsed) => { 
            match parsed.lower(&policy_schema) {
                // Rejected at lowering.
                Err(_) => true,
                // Otherwise, rejected at validation.
                Ok(lowered) => !Validator::new().validate(&lowered).validation_passed(),
            }
        }
    };
    assert!(
        rejected,
        "a macro-sigil binder outside a macro body must be rejected \
         gracefully during parsing, lowering, or validation"
    );
}

#[test]
fn stray_macro_sigil_binder_in_temporal_count_expression_field_name_fails_gracefully_no_panic() {
    // A stray macro-sigil binder in a projection field name in a temporal count expression should not cause a panic
    // and should be gracefully rejected with an error at some phase, 
    // either during parsing, lowering, or validation.
    let src = r#"permit( principal, action, resource )
                when temporal { 
                    count for (t: Timepoint), (id: String). where (
                        Drupe::Action::"Read"::request{ input.?user: id } && id == "alice" && tp(t)
                    ) >= 2
                };"#;
    let policy_schema = PolicySchema::from_cedarschema_str(SCHEMA).expect("action schema");

    let rejected = match ParsedPolicySet::parse(src, &service()) {
        // Rejected at parse.
        Err(_) => true,
        Ok(parsed) => { 
            match parsed.lower(&policy_schema) {
                // Rejected at lowering.
                Err(_) => true,
                // Otherwise, rejected at validation.
                Ok(lowered) => !Validator::new().validate(&lowered).validation_passed(),
            }
        }
    };
    assert!(
        rejected,
        "a macro-sigil binder outside a macro body must be rejected \
         gracefully during parsing, lowering, or validation"
    );
}


#[test]
fn valid_temporal_sum_expression_parses_lowers_validates() {
    let src = r#"permit( principal == Drupe::OAuthUser::"alice", action == Drupe::Action::"Transfer", resource )
                when temporal { 
                    (sum a for (a: Long), (id: String), (t: Timepoint). where (
                        formerly within 1d Drupe::Action::"Transfer"::request{ input.user: id, input.amount: a } && id == "alice" && a > 0 && tp(t)
                    )) <= 1000
                };"#;
    let policy_schema = PolicySchema::from_cedarschema_str(SCHEMA).expect("action schema");
    let parsed = ParsedPolicySet::parse(src, &service()).expect("valid source parses");
    let lowered = parsed.lower(&policy_schema).expect("parsed set lowers");
    assert!(Validator::new().validate(&lowered).validation_passed());
}

#[test]
fn stray_macro_sigil_binder_in_timepoint_in_temporal_sum_expression_binder_fails_gracefully_no_panic() {
    // A stray macro-sigil binder in the timepoint bound variable binder of a temporal sum expression should not cause a panic
    // and should be gracefully rejected with an error at some phase, 
    // either during parsing, lowering, or validation.
    let src = r#"permit( principal == Drupe::OAuthUser::"alice", action == Drupe::Action::"Transfer", resource )
                when temporal { 
                    (sum a for (a: Long), (id: String), (?t: Timepoint). where (
                        formerly within 1d Drupe::Action::"Transfer"::request{ input.user: id, input.amount: a } && id == "alice" && a > 0 && tp(t)
                    )) <= 1000
                };"#;
    let policy_schema = PolicySchema::from_cedarschema_str(SCHEMA).expect("action schema");
    let rejected = match ParsedPolicySet::parse(src, &service()) {
        // Rejected at parse.
        Err(_) => true,
        Ok(parsed) => { 
            match parsed.lower(&policy_schema) {
                // Rejected at lowering.
                Err(_) => true,
                // Otherwise, rejected at validation.
                Ok(lowered) => !Validator::new().validate(&lowered).validation_passed(),
            }
        }
    };
    assert!(
        rejected,
        "a macro-sigil binder outside a macro body must be rejected \
         gracefully during parsing, lowering, or validation"
    );
}

#[test]
fn stray_macro_sigil_binder_in_timepoint_in_temporal_sum_expression_body_fails_gracefully_no_panic() {
    // A stray macro-sigil binder in the timepoint bound variable in the body of a temporal sum expression should not cause a panic
    // and should be gracefully rejected with an error at some phase, 
    // either during parsing, lowering, or validation.
    let src = r#"permit( principal == Drupe::OAuthUser::"alice", action == Drupe::Action::"Transfer", resource )
                when temporal { 
                    (sum a for (a: Long), (id: String), (t: Timepoint). where (
                        formerly within 1d Drupe::Action::"Transfer"::request{ input.user: id, input.amount: a } && id == "alice" && a > 0 && tp(?t)
                    )) <= 1000
                };"#;
    let policy_schema = PolicySchema::from_cedarschema_str(SCHEMA).expect("action schema");
    let rejected = match ParsedPolicySet::parse(src, &service()) {
        // Rejected at parse.
        Err(_) => true,
        Ok(parsed) => { 
            match parsed.lower(&policy_schema) {
                // Rejected at lowering.
                Err(_) => true,
                // Otherwise, rejected at validation.
                Ok(lowered) => !Validator::new().validate(&lowered).validation_passed(),
            }
        }
    };
    assert!(
        rejected,
        "a macro-sigil binder outside a macro body must be rejected \
         gracefully during parsing, lowering, or validation"
    );
}

#[test]
fn stray_macro_sigil_binder_in_temporal_sum_expression_aggregand_fails_gracefully_no_panic() {
    // A stray macro-sigil binder in the aggregand of a temporal sum expression should not cause a panic
    // and should be gracefully rejected with an error at some phase, 
    // either during parsing, lowering, or validation.
    let src = r#"permit( principal == Drupe::OAuthUser::"alice", action == Drupe::Action::"Transfer", resource )
                when temporal { 
                    (sum ?a for (a: Long), (id: String), (t: Timepoint). where (
                        formerly within 1d Drupe::Action::"Transfer"::request{ input.user: id, input.amount: a } && id == "alice" && a > 0 && tp(t)
                    )) <= 1000
                };"#;
    let policy_schema = PolicySchema::from_cedarschema_str(SCHEMA).expect("action schema");
    let rejected = match ParsedPolicySet::parse(src, &service()) {
        // Rejected at parse.
        Err(_) => true,
        Ok(parsed) => { 
            match parsed.lower(&policy_schema) {
                // Rejected at lowering.
                Err(_) => true,
                // Otherwise, rejected at validation.
                Ok(lowered) => !Validator::new().validate(&lowered).validation_passed(),
            }
        }
    };
    assert!(
        rejected,
        "a macro-sigil binder outside a macro body must be rejected \
         gracefully during parsing, lowering, or validation"
    );
}

#[test]
fn stray_macro_sigil_binder_in_bound_var_in_temporal_sum_expression_binder_fails_gracefully_no_panic() {
    // A stray macro-sigil binder in the (non-timepoint) bound variable binder of a temporal sum expression should not cause a panic
    // and should be gracefully rejected with an error at some phase, 
    // either during parsing, lowering, or validation.
    let src = r#"permit( principal == Drupe::OAuthUser::"alice", action == Drupe::Action::"Transfer", resource )
                when temporal { 
                    (sum a for (a: Long), (?id: String), (t: Timepoint). where (
                        formerly within 1d Drupe::Action::"Transfer"::request{ input.user: id, input.amount: a } && id == "alice" && a > 0 && tp(t)
                    )) <= 1000
                };"#;
    let policy_schema = PolicySchema::from_cedarschema_str(SCHEMA).expect("action schema");
    let rejected = match ParsedPolicySet::parse(src, &service()) {
        // Rejected at parse.
        Err(_) => true,
        Ok(parsed) => { 
            match parsed.lower(&policy_schema) {
                // Rejected at lowering.
                Err(_) => true,
                // Otherwise, rejected at validation.
                Ok(lowered) => !Validator::new().validate(&lowered).validation_passed(),
            }
        }
    };
    assert!(
        rejected,
        "a macro-sigil binder outside a macro body must be rejected \
         gracefully during parsing, lowering, or validation"
    );
}

#[test]
fn stray_macro_sigil_binder_in_aggregand_in_temporal_sum_expression_body_fails_gracefully_no_panic() {
    // A stray macro-sigil binder in the aggregand variable in the body of a temporal sum expression should not cause a panic
    // and should be gracefully rejected with an error at some phase, 
    // either during parsing, lowering, or validation.
    let src = r#"permit( principal == Drupe::OAuthUser::"alice", action == Drupe::Action::"Transfer", resource )
                when temporal { 
                    (sum a for (a: Long), (id: String), (t: Timepoint). where (
                        formerly within 1d Drupe::Action::"Transfer"::request{ input.user: id, input.amount: a } && id == "alice" && ?a > 0 && tp(t)
                    )) <= 1000
                };"#;
    let policy_schema = PolicySchema::from_cedarschema_str(SCHEMA).expect("action schema");
    let rejected = match ParsedPolicySet::parse(src, &service()) {
        // Rejected at parse.
        Err(_) => true,
        Ok(parsed) => { 
            match parsed.lower(&policy_schema) {
                // Rejected at lowering.
                Err(_) => true,
                // Otherwise, rejected at validation.
                Ok(lowered) => !Validator::new().validate(&lowered).validation_passed(),
            }
        }
    };
    assert!(
        rejected,
        "a macro-sigil binder outside a macro body must be rejected \
         gracefully during parsing, lowering, or validation"
    );
}

#[test]
fn stray_macro_sigil_binder_in_bound_var_in_temporal_sum_expression_body_fails_gracefully_no_panic() {
    // A stray macro-sigil binder in the (non-timepoint) bound variable in the body of a temporal sum expression should not cause a panic
    // and should be gracefully rejected with an error at some phase, 
    // either during parsing, lowering, or validation.
    let src = r#"permit( principal == Drupe::OAuthUser::"alice", action == Drupe::Action::"Transfer", resource )
                when temporal { 
                    (sum a for (a: Long), (id: String), (t: Timepoint). where (
                        formerly within 1d Drupe::Action::"Transfer"::request{ input.user: id, input.amount: a } && ?id == "alice" && a > 0 && tp(t)
                    )) <= 1000
                };"#;
    let policy_schema = PolicySchema::from_cedarschema_str(SCHEMA).expect("action schema");
    let rejected = match ParsedPolicySet::parse(src, &service()) {
        // Rejected at parse.
        Err(_) => true,
        Ok(parsed) => { 
            match parsed.lower(&policy_schema) {
                // Rejected at lowering.
                Err(_) => true,
                // Otherwise, rejected at validation.
                Ok(lowered) => !Validator::new().validate(&lowered).validation_passed(),
            }
        }
    };
    assert!(
        rejected,
        "a macro-sigil binder outside a macro body must be rejected \
         gracefully during parsing, lowering, or validation"
    );
}

#[test]
fn stray_macro_sigil_binder_in_all_aggregand_occurrences_in_temporal_sum_expression_fails_gracefully_no_panic() {
    // A stray macro-sigil binder in all occurrences (aggregand, binder, projection field variable, and body) of the aggregand variable 
    // in a temporal sum expression should not cause a panic and should be gracefully rejected with an error at some phase, 
    // either during parsing, lowering, or validation.
    let src = r#"permit( principal == Drupe::OAuthUser::"alice", action == Drupe::Action::"Transfer", resource )
                when temporal { 
                    (sum ?a for (?a: Long), (id: String), (t: Timepoint). where (
                        formerly within 1d Drupe::Action::"Transfer"::request{ input.user: id, input.amount: ?a } && id == "alice" && ?a > 0 && tp(t)
                    )) <= 1000
                };"#;
    let policy_schema = PolicySchema::from_cedarschema_str(SCHEMA).expect("action schema");
    let rejected = match ParsedPolicySet::parse(src, &service()) {
        // Rejected at parse.
        Err(_) => true,
        Ok(parsed) => { 
            match parsed.lower(&policy_schema) {
                // Rejected at lowering.
                Err(_) => true,
                // Otherwise, rejected at validation.
                Ok(lowered) => !Validator::new().validate(&lowered).validation_passed(),
            }
        }
    };
    assert!(
        rejected,
        "a macro-sigil binder outside a macro body must be rejected \
         gracefully during parsing, lowering, or validation"
    );
}

#[test]
fn stray_macro_sigil_binder_in_all_bound_var_occurrences_in_temporal_sum_expression_fails_gracefully_no_panic() {
    // A stray macro-sigil binder in all occurrences (binder, projection field variable, and body) of a bound variable in a temporal sum expression 
    // should not cause a panic and should be gracefully rejected with an error at some phase, 
    // either during parsing, lowering, or validation.
    let src = r#"permit( principal == Drupe::OAuthUser::"alice", action == Drupe::Action::"Transfer", resource )
                when temporal { 
                    (sum a for (a: Long), (?id: String), (t: Timepoint). where (
                        formerly within 1d Drupe::Action::"Transfer"::request{ input.user: ?id, input.amount: a } && ?id == "alice" && a > 0 && tp(t)
                    )) <= 1000
                };"#;
    let policy_schema = PolicySchema::from_cedarschema_str(SCHEMA).expect("action schema");
    let rejected = match ParsedPolicySet::parse(src, &service()) {
        // Rejected at parse.
        Err(_) => true,
        Ok(parsed) => { 
            match parsed.lower(&policy_schema) {
                // Rejected at lowering.
                Err(_) => true,
                // Otherwise, rejected at validation.
                Ok(lowered) => !Validator::new().validate(&lowered).validation_passed(),
            }
        }
    };
    assert!(
        rejected,
        "a macro-sigil binder outside a macro body must be rejected \
         gracefully during parsing, lowering, or validation"
    );
}

#[test]
fn stray_macro_sigil_binder_in_temporal_sum_expression_field_name_fails_gracefully_no_panic() {
    // A stray macro-sigil binder in a projection field name in a temporal sum expression should not cause a panic
    // and should be gracefully rejected with an error at some phase, 
    // either during parsing, lowering, or validation.
    let src = r#"permit( principal == Drupe::OAuthUser::"alice", action == Drupe::Action::"Transfer", resource )
                when temporal { 
                    (sum a for (a: Long), (id: String), (t: Timepoint). where (
                        formerly within 1d Drupe::Action::"Transfer"::request{ input.?user: id, input.amount: a } && id == "alice" && a > 0 && tp(t)
                    )) <= 1000
                };"#;
    let policy_schema = PolicySchema::from_cedarschema_str(SCHEMA).expect("action schema");
    let rejected = match ParsedPolicySet::parse(src, &service()) {
        // Rejected at parse.
        Err(_) => true,
        Ok(parsed) => { 
            match parsed.lower(&policy_schema) {
                // Rejected at lowering.
                Err(_) => true,
                // Otherwise, rejected at validation.
                Ok(lowered) => !Validator::new().validate(&lowered).validation_passed(),
            }
        }
    };
    assert!(
        rejected,
        "a macro-sigil binder outside a macro body must be rejected \
         gracefully during parsing, lowering, or validation"
    );
}

#[test]
fn schema_dependent_error_is_not_caught_by_parse() {
    // `parse` checks syntax + macro resolution ONLY. An unknown attribute
    // (`context.input.bogus`) is a schema-dependent error — parse cannot know
    // the field is absent without the action schema, so it parses cleanly and
    // the error surfaces only at validation (after lowering).
    let src = r#"permit ( principal, action == Drupe::Action::"Read", resource )
                 when { context.input.bogus == "x" };"#;

    // Parse succeeds — the schema-dependent problem is invisible here.
    let parsed = ParsedPolicySet::parse(src, &service()).expect("parses (syntax is fine)");

    // It only shows up once the action schema is applied and we validate.
    let policy_schema = PolicySchema::from_cedarschema_str(SCHEMA).expect("action schema");
    let lowered = parsed
        .lower(&policy_schema)
        .expect("lowers (still no type check)");
    assert!(
        !Validator::new().validate(&lowered).validation_passed(),
        "the unknown attribute must surface as a validation error, not at parse"
    );
}

// ─── IN_SCOPE_CONTEXT guard tests ────────────────────────────────────

/// After a parse that hits an error in a scope expression, the next parse
/// (on the same thread) must produce condition-context errors — not
/// scope-context errors. This verifies the RAII guard resets the flag.
#[test]
fn scope_context_resets_after_scope_parse_error() {
    use dogwood_language::{ParsedPolicySet, ServiceSchema};

    let service = ServiceSchema::defaults();

    // First: parse a policy with an invalid name in scope position.
    // This triggers the scope-context error path.
    let scope_err_src = r#"
        permit (principal == Ns::Type, action, resource);
    "#;
    let err1 = ParsedPolicySet::parse(scope_err_src, &service).unwrap_err();
    let msg1 = err1.to_string();
    // In scope context, the error suggests `is Type`
    assert!(
        msg1.contains("is Ns::Type") || msg1.contains("not a valid entity reference"),
        "first parse should give scope-context error, got: {msg1}"
    );

    // Second: parse a policy with an invalid name in condition position.
    // This should give a condition-context error, NOT a scope-context error.
    let cond_err_src = r#"
        permit (principal, action, resource)
        when { Ns::Type };
    "#;
    let err2 = ParsedPolicySet::parse(cond_err_src, &service).unwrap_err();
    let msg2 = err2.to_string();
    // In condition context, it should NOT suggest `is Type`
    assert!(
        !msg2.contains("is Ns::Type"),
        "second parse should NOT give scope-context error, got: {msg2}"
    );
}

/// Simulates the async service scenario: a parse with scope-context error
/// followed immediately by another parse on the same thread. Without the
/// RAII guard, the IN_SCOPE_CONTEXT flag would leak `true` from the first
/// parse into the second, producing incorrect "try `is Type`" suggestions
/// in non-scope positions. The guard ensures each parse starts clean.
#[test]
fn scope_context_does_not_leak_across_sequential_parses() {
    use dogwood_language::{ParsedPolicySet, ServiceSchema};

    let service = ServiceSchema::defaults();

    // Simulate multiple "requests" hitting the parser on the same thread,
    // as would happen in an async runtime with worker thread reuse.
    for _ in 0..10 {
        // Request A: policy with a bad entity ref in scope position
        // (triggers scope-context error path internally)
        let scope_policy = r#"permit (principal == Ns::BadType, action, resource);"#;
        let _ = ParsedPolicySet::parse(scope_policy, &service);

        // Request B: policy with a bad name in condition position
        // This MUST get a condition-context error, not a scope-context one.
        let cond_policy = r#"
            permit (principal, action, resource)
            when { Ns::BadExpr };
        "#;
        let err = ParsedPolicySet::parse(cond_policy, &service).unwrap_err();
        let msg = err.to_string();

        // The key assertion: if the flag leaked from parse A, this would
        // incorrectly suggest `is Ns::BadExpr` (scope advice in a condition).
        assert!(
            !msg.contains("is Ns::BadExpr"),
            "IN_SCOPE_CONTEXT leaked across parses! Got scope-context error \
             in condition position: {msg}"
        );
    }
}
