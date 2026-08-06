//! Slice 3 verdict test: replaying an event trace reproduces the
//! per-timepoint verdict stream for a temporal policy.
//!
//! New Cedar-parity lifecycle: build a [`PolicySchema`] (action schema) plus a
//! [`ServiceSchema`] (the `request_response` event schema), lower the policy
//! text into a [`LoweredPolicySet`] with [`LoweredPolicySet::from_str`], then
//! [`replay_log`] the trace to obtain the verdict stream string.

use dogwood_language::{LoweredPolicySet, PolicySchema, ServiceSchema};
use std::path::Path;

#[test]
fn authorize_formerly_within_window() {
    let dir = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("tests/docs_as_tests/temporal_cases/documentation_0300_formerly_within_short_window");
    let policy = std::fs::read_to_string(dir.join("policy_1.dw")).unwrap();
    let action_schema = std::fs::read_to_string(dir.join("schema.cedarschema")).unwrap();
    let trace = std::fs::read_to_string(dir.join("trace_1.log")).unwrap();
    let expected = std::fs::read_to_string(dir.join("expected_1.out")).unwrap();
    let event_schema = std::fs::read_to_string(
        Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/request_response.dwschema"),
    )
    .unwrap();

    // Build the policy schema from the action schema plus a service schema
    // from the request/response event schema fixture, then lower the policy
    // into a LoweredPolicySet.
    let policy_schema = PolicySchema::from_cedarschema_str(&action_schema).expect("schema");
    let service = ServiceSchema::builder()
        .event_schema_str(&event_schema)
        .build()
        .expect("schema");
    let policies = LoweredPolicySet::from_str(&policy, &service, &policy_schema).expect("parse");

    // Replay the whole trace to produce the per-timepoint verdict stream.
    let verdicts = dogwood_language::replay_log(policies, &trace).expect("authorizes");

    // Compare line-set (ignoring trailing whitespace / blank lines).
    let norm = |s: &str| {
        s.lines()
            .map(str::trim)
            .filter(|l| !l.is_empty())
            .map(str::to_string)
            .collect::<Vec<_>>()
    };
    assert_eq!(
        norm(&verdicts),
        norm(&expected),
        "verdict mismatch:\n--- got ---\n{verdicts}\n--- expected ---\n{expected}"
    );
}
