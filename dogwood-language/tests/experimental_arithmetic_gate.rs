//! EXPERIMENTAL-ARITHMETIC: a default build rejects arithmetic in temporal
//! comparison operands. Arithmetic written in a policy is rejected at parse
//! time; arithmetic inside a macro body is rejected after expansion. The
//! feature-on behaviour (acceptance plus a validation warning) is pinned in
//! `arithmetic_eval.rs`. These tests may be deleted with the gate when the
//! feature is released.
#![cfg(not(feature = "experimental-arithmetic"))]

use dogwood_language::{LoweredPolicySet, PolicySchema, ServiceSchema};

const SCHEMA: &str = r#"namespace Ns {
  type ActInput = { x: Long };
  type ActOutput = { };
  type SystemContext = { now: datetime };
  entity User;
  entity Res;
  action "Act" appliesTo {
    principal: [User], resource: [Res],
    context: { input: ActInput, output?: ActOutput, system: SystemContext }
  };
}"#;

fn lower(policy: &str) -> Result<LoweredPolicySet, String> {
    let schema = PolicySchema::from_cedarschema_str(SCHEMA).expect("schema parses");
    let service = ServiceSchema::defaults();
    LoweredPolicySet::from_str(policy, &service, &schema).map_err(|e| e.to_string())
}

#[test]
fn arithmetic_in_a_policy_is_rejected_at_parse() {
    let err = lower(
        r#"permit (principal, action == Ns::Action::"Act", resource)
when temporal {
    exists (n: Long). (
        (count for (t: Timepoint). where (Ns::Action::"Act"::request{ input.x: * } && tp(t))) == n
        && n - 1 == 0
    )
};"#,
    )
    .expect_err("a default build rejects arithmetic");
    assert!(
        err.contains("not yet supported"),
        "unexpected error: {err}"
    );
}

#[test]
fn arithmetic_in_a_macro_body_is_rejected_after_expansion() {
    // The macro body hides the arithmetic from the parse-time gate; the
    // post-expansion check in macro expansion must reject it instead.
    let err = lower(
        r#"def temporal low(?n) { ?n - 1 == 0 };
permit (principal, action == Ns::Action::"Act", resource)
when temporal {
    exists (n: Long). (
        (count for (t: Timepoint). where (Ns::Action::"Act"::request{ input.x: * } && tp(t))) == n
        && low(n)
    )
};"#,
    )
    .expect_err("a default build rejects macro-carried arithmetic");
    assert!(
        err.contains("not yet supported"),
        "unexpected error: {err}"
    );
}
