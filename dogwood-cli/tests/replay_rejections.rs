//! `dogwood replay` reports a history event the authorizer rejected at
//! ingestion, because it does not conform to the event schema, and a decision
//! that fails closed on a nonconforming decision event.

use std::path::Path;
use std::process::Command;

const SCHEMA: &str = r#"
namespace Drupe {
  type LoginInput = { user: String };
  type ReadInput = { user: String };
  entity Gateway;
  entity OAuthUser;
  action "Login" appliesTo {
    principal: [OAuthUser], resource: [Gateway], context: { input: LoginInput }
  };
  action "Read" appliesTo {
    principal: [OAuthUser], resource: [Gateway], context: { input: ReadInput }
  };
}
"#;

const POLICY: &str = r#"
permit (principal, action == Drupe::Action::"Read", resource)
when temporal {
    formerly within 1h Drupe::Action::"Login"::response{ input.user: context.input.user }
};
"#;

// The first login response logs its user as a Long, so it is rejected and the
// first read is denied; the second is conforming, and the second read is
// allowed. The last read logs its user as a Long: its decision fails closed.
const TRACE: &str = r#"@0 scope(principal: Drupe::OAuthUser::"alice", resource: Drupe::Gateway::"gw") Drupe::Action::"Login"::response(input: { user: 7 }, callerPrincipal: Drupe::OAuthUser::"alice", callerResource: Drupe::Gateway::"gw")
@1 scope(principal: Drupe::OAuthUser::"alice", resource: Drupe::Gateway::"gw") request_context(input: { user: "alice" }) Drupe::Action::"Read"::request(input: { user: "alice" }, callerPrincipal: Drupe::OAuthUser::"alice", callerResource: Drupe::Gateway::"gw")
@2 scope(principal: Drupe::OAuthUser::"alice", resource: Drupe::Gateway::"gw") Drupe::Action::"Login"::response(input: { user: "alice" }, callerPrincipal: Drupe::OAuthUser::"alice", callerResource: Drupe::Gateway::"gw")
@3 scope(principal: Drupe::OAuthUser::"alice", resource: Drupe::Gateway::"gw") request_context(input: { user: "alice" }) Drupe::Action::"Read"::request(input: { user: "alice" }, callerPrincipal: Drupe::OAuthUser::"alice", callerResource: Drupe::Gateway::"gw")
@4 scope(principal: Drupe::OAuthUser::"alice", resource: Drupe::Gateway::"gw") request_context(input: { user: "alice" }) Drupe::Action::"Read"::request(input: { user: 7 }, callerPrincipal: Drupe::OAuthUser::"alice", callerResource: Drupe::Gateway::"gw")
"#;

fn replay(dir: &Path, extra: &[&str]) -> String {
    let file = |name: &str, text: &str| {
        let path = dir.join(name);
        std::fs::write(&path, text).expect("write fixture");
        path
    };
    let schema = file("schema.cedarschema", SCHEMA);
    let policy = file("policy.dw", POLICY);
    let trace = file("trace.log", TRACE);
    let output = Command::new(env!("CARGO_BIN_EXE_dogwood"))
        .arg("replay")
        .arg("--policy-schema")
        .arg(&schema)
        .arg("--trace")
        .arg(&trace)
        .args(extra)
        .arg(&policy)
        .output()
        .expect("run dogwood");
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    String::from_utf8(output.stdout).expect("utf-8 output")
}

fn scratch(name: &str) -> std::path::PathBuf {
    let dir = std::env::temp_dir().join(format!("dogwood-cli-{name}-{}", std::process::id()));
    std::fs::create_dir_all(&dir).expect("create scratch dir");
    dir
}

#[test]
fn replay_reports_a_rejected_history_event_in_trace_order() {
    let dir = scratch("rejections-text");
    let out = replay(&dir, &[]);
    let lines: Vec<&str> = out.lines().collect();
    assert_eq!(
        lines[0], "@0 (event 0 of the trace): REJECTED, not ingested",
        "{out}"
    );
    assert!(
        lines[1]
            .starts_with("    error: nonconforming event: `Drupe::Action::\"Login\"::response`")
            && lines[1].contains("`input.user`"),
        "{out}"
    );
    assert_eq!(lines[2], "@1 (time point 0): DENY", "{out}");
    assert_eq!(lines[3], "@3 (time point 1): ALLOW  [rules: 0]", "{out}");
    assert_eq!(lines[4], "@4 (time point 2): DENY", "{out}");
    assert!(
        lines[5].starts_with("    error: nonconforming decision event:"),
        "{out}"
    );
    assert_eq!(lines.len(), 6, "{out}");
    let _ = std::fs::remove_dir_all(dir);
}

#[test]
fn replay_json_lists_the_rejected_events() {
    let dir = scratch("rejections-json");
    let out = replay(&dir, &["--format", "json"]);
    let report: serde_json::Value = serde_json::from_str(&out).expect("JSON report");
    let rejected = report["rejected"].as_array().expect("a `rejected` array");
    assert_eq!(rejected.len(), 1, "{out}");
    assert_eq!(rejected[0]["position"], 0);
    assert_eq!(rejected[0]["timestamp"], 0);
    assert!(
        rejected[0]["reason"]
            .as_str()
            .is_some_and(|r| r.starts_with("nonconforming event:")),
        "{out}"
    );
    assert_eq!(
        report["verdicts"].as_array().map(Vec::len),
        Some(3),
        "{out}"
    );
    let _ = std::fs::remove_dir_all(dir);
}
