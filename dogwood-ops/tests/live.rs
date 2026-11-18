//! The live authorizer's event contract: decisions, history-only events, and
//! every rejection leaving the history untouched.

use dogwood_ops::{EventInput, LiveAuthorizer, Verdict};
use serde_json::json;

const SCHEMA: &str = r#"namespace Drupe {
  entity Gateway;
  entity OAuthUser = { id: String } tags String;
  type ReadInput = { document: String };
  type ReadOutput = { content: String };
  action "Read" appliesTo {
    principal: [OAuthUser], resource: [Gateway],
    context: { input: ReadInput, output?: ReadOutput }
  };
}"#;

/// Permit a Read only after a Read *response* within the last hour.
const AFTER_RESPONSE: &str = r#"permit(principal, action == Drupe::Action::"Read", resource)
when temporal { formerly within 1h Drupe::Action::"Read"::response{} };"#;

const PERMIT_UNLESS_LARGE: &str = r#"permit(principal, action == Drupe::Action::"Read", resource);
forbid(principal, action == Drupe::Action::"Read", resource)
when { context.input.size > 100 };"#;

const SIZED_SCHEMA: &str = r#"namespace Drupe {
  entity Gateway;
  entity OAuthUser = { id: String } tags String;
  type ReadInput = { document: String, size: Long };
  action "Read" appliesTo {
    principal: [OAuthUser], resource: [Gateway], context: { input: ReadInput }
  };
}"#;

fn event(ts: i64, kind: &str, input: serde_json::Value) -> EventInput {
    serde_json::from_value(json!({
        "action": "Drupe::Action::Read",
        "kind": kind,
        "timestamp": ts,
        "principal": { "type": "Drupe::OAuthUser", "id": "alice" },
        "resource": { "type": "Drupe::Gateway", "id": "gw1" },
        "logged": { "input": input.clone() },
        "context": { "input": input },
    }))
    .expect("a well-formed EventInput")
}

fn read(ts: i64, kind: &str) -> EventInput {
    let mut e = event(ts, kind, json!({ "document": "d" }));
    if kind == "response" {
        // A response's signature requires its output.
        e.logged.insert("output".into(), [("content".to_string(), json!("c"))].into());
    }
    e
}

fn authorizer(policy: &str, schema: &str) -> LiveAuthorizer {
    LiveAuthorizer::new(policy, schema, None, None, None).expect("lowers")
}

#[test]
fn decisions_and_history_only_events() {
    let mut auth = authorizer(AFTER_RESPONSE, SCHEMA);
    assert_eq!(auth.actions(), ["Drupe::Action::Read"]);
    assert_eq!(auth.decision_kinds(), ["request"]);

    let first = auth.is_authorized(&read(0, "request")).unwrap().unwrap();
    assert_eq!(first.verdict, Verdict::Deny);
    assert!(first.errors.is_empty(), "denied by the policy, not an error: {first:?}");
    assert!(auth.is_authorized(&read(1, "response")).unwrap().is_none());
    let second = auth.is_authorized(&read(10, "request")).unwrap().unwrap();
    assert_eq!((second.index, second.verdict), (1, Verdict::Allow), "{second:?}");
    assert!(second.allowed);
    assert_eq!(auth.decision_count(), 2);
    assert_eq!(auth.last_timestamp(), Some(10));

    auth.reset().unwrap();
    assert_eq!((auth.decision_count(), auth.last_timestamp()), (0, None));
    let after_reset = auth.is_authorized(&read(0, "request")).unwrap().unwrap();
    assert_eq!(after_reset.verdict, Verdict::Deny);
}

#[test]
fn rejections_leave_the_history_untouched() {
    let mut auth = authorizer(AFTER_RESPONSE, SCHEMA);

    let mut bare = read(5, "request");
    bare.action = "Read".to_string();
    let e = auth.is_authorized(&bare).unwrap_err().to_string();
    assert!(e.contains("did you mean `Drupe::Action::Read`"), "{e}");

    let e = auth.is_authorized(&read(5, "requst")).unwrap_err().to_string();
    assert!(e.contains("unknown event kind"), "{e}");

    // A history event that does not conform to the event schema is not
    // ingested by the authorizer; the live path reports it rather than
    // returning the same `None` as an ingested event.
    let bad_response = event(5, "response", json!({ "document": 7 }));
    let e = auth.is_authorized(&bad_response).unwrap_err().to_string();
    assert!(e.contains("event rejected, not recorded"), "{e}");

    assert_eq!((auth.decision_count(), auth.last_timestamp()), (0, None));
    // The rejected response is not in the history: a request still denies.
    let d = auth.is_authorized(&read(6, "request")).unwrap().unwrap();
    assert_eq!(d.verdict, Verdict::Deny);

    let e = auth.is_authorized(&read(5, "request")).unwrap_err().to_string();
    assert!(e.contains("before the previous event's 6"), "{e}");
    assert_eq!(auth.decision_count(), 1);
}

#[test]
fn an_errored_forbid_fails_closed() {
    let mut auth = authorizer(PERMIT_UNLESS_LARGE, SIZED_SCHEMA);
    for (ts, input) in [(1, json!({ "document": "d", "size": "huge" })), (2, json!({ "document": "d" }))] {
        let d = auth.is_authorized(&event(ts, "request", input)).unwrap().unwrap();
        assert!(!d.errors.is_empty());
        assert_eq!((d.verdict, d.allowed), (Verdict::Deny, false));
        assert!(d.determining_rules.is_empty());
    }
    let small = auth.is_authorized(&event(3, "request", json!({ "document": "d", "size": 5 })));
    assert!(small.unwrap().unwrap().allowed);
}

#[test]
fn replay_and_live_agree_on_evaluation_errors() {
    let inputs = [
        json!({ "document": "d", "size": "huge" }),
        json!({ "document": "d" }),
        json!({ "document": "d", "size": 5 }),
        json!({ "document": "d", "size": 500 }),
    ];
    let trace: Vec<String> = inputs
        .iter()
        .enumerate()
        .map(|(i, input)| {
            let v = input.to_string().replace("\"document\":", "document: ").replace("\"size\":", "size: ");
            format!(
                "@{} scope(principal: Drupe::OAuthUser::\"alice\", resource: Drupe::Gateway::\"gw1\") \
                 request_context(input: {v}) \
                 Drupe::Action::\"Read\"::request(callerPrincipal: Drupe::OAuthUser::\"alice\", \
                 callerResource: Drupe::Gateway::\"gw1\", input: {v})",
                i + 1
            )
        })
        .collect();
    let schema = dogwood_ops::inputs(None, None, None).unwrap();
    let replayed =
        dogwood_ops::replay(PERMIT_UNLESS_LARGE, &schema, SIZED_SCHEMA, &trace.join("\n")).unwrap();
    assert_eq!(replayed.verdicts.len(), inputs.len());

    let mut auth = authorizer(PERMIT_UNLESS_LARGE, SIZED_SCHEMA);
    for (i, input) in inputs.into_iter().enumerate() {
        let live = auth.is_authorized(&event(i as i64 + 1, "request", input)).unwrap().unwrap();
        let r = &replayed.verdicts[i];
        assert_eq!(r.verdict, live.verdict, "event {i}: replay {r:?} live {live:?}");
        assert_eq!(r.determining_rules, live.determining_rules, "event {i}");
    }
}

#[test]
fn a_script_file_provider_is_rejected_up_front() {
    let providers = json!({ "availableProviders": { "Strings::Matches": {
        "argumentTypes": [{ "paramType": "string" }],
        "outputType": { "paramType": "bool" },
        "implementation": { "kind": "rhai", "scriptFile": "m.rhai" } } } })
    .to_string();
    let e = dogwood_ops::check_providers(&providers).unwrap_err().to_string();
    assert!(e.contains("scriptFile: \"m.rhai\""), "{e}");
    let e = LiveAuthorizer::new(AFTER_RESPONSE, SCHEMA, None, Some(providers), None)
        .err()
        .expect("rejected")
        .to_string();
    assert!(e.contains("scriptFile"), "{e}");
}

#[test]
fn a_missing_timestamp_does_not_deserialize() {
    let e = serde_json::from_value::<EventInput>(json!({ "action": "Drupe::Action::Read" }))
        .unwrap_err()
        .to_string();
    assert!(e.contains("timestamp"), "{e}");
}

#[test]
fn a_nonconforming_decision_event_leaves_the_ordering_untouched() {
    let mut auth = authorizer(AFTER_RESPONSE, SCHEMA);
    // Logged `input.document` is a Long, not the String the schema declares:
    // denied, and not ingested — at a timestamp in milliseconds.
    let bad = event(1_700_000_000_000, "request", json!({ "document": 7 }));
    let d = auth.is_authorized(&bad).unwrap().unwrap();
    assert_eq!(d.verdict, Verdict::Deny);
    assert!(d.errors.iter().any(|e| e.contains("nonconforming decision event")), "{d:?}");
    assert_eq!(auth.last_timestamp(), None, "the bad event did not enter the history");

    // A correctly-timed event is still accepted.
    let ok = auth.is_authorized(&read(1_700_000_000, "request")).unwrap().unwrap();
    assert!(ok.errors.is_empty(), "{ok:?}");
    assert_eq!(auth.last_timestamp(), Some(1_700_000_000));
}

/// Cedar permits any string as an action id; the live path addresses it from
/// the schema's own parts rather than re-splitting the qualified id.
#[test]
fn action_ids_containing_colons_are_addressed_exactly() {
    for id in [":x", "Read::Extra", "x:"] {
        let schema = format!(
            r#"namespace Drupe {{
  entity Gateway;
  entity OAuthUser = {{ id: String }} tags String;
  type ReadInput = {{ document: String }};
  action "{id}" appliesTo {{
    principal: [OAuthUser], resource: [Gateway], context: {{ input: ReadInput }}
  }};
}}"#
        );
        let policy = format!(r#"permit(principal, action == Drupe::Action::"{id}", resource);"#);
        let mut auth = authorizer(&policy, &schema);
        let qualified = format!("Drupe::Action::{id}");
        assert_eq!(auth.actions(), [qualified.clone()]);
        let mut e = read(1, "request");
        e.action = qualified;
        let d = auth.is_authorized(&e).unwrap().unwrap();
        assert_eq!(d.verdict, Verdict::Allow, "id {id:?}: {d:?}");
    }
}

/// Two distinct actions whose namespace and id join to the same qualified id
/// cannot be told apart by `EventInput.action`: construction fails, naming
/// both, instead of one silently shadowing the other.
#[test]
fn actions_with_the_same_qualified_id_are_rejected() {
    let schema = r#"namespace Drupe {
  entity Gateway;
  entity OAuthUser = { id: String } tags String;
  type ReadInput = { document: String };
  action "Action::Read" appliesTo {
    principal: [OAuthUser], resource: [Gateway], context: { input: ReadInput }
  };
}
namespace Drupe::Action {
  action "Read" appliesTo {
    principal: [Drupe::OAuthUser], resource: [Drupe::Gateway],
    context: { input: Drupe::ReadInput }
  };
}"#;
    let policy = r#"permit(principal, action == Drupe::Action::"Action::Read", resource);"#;
    let err = LiveAuthorizer::new(policy, schema, None, None, None)
        .err()
        .expect("a qualified-id collision must fail construction")
        .to_string();
    assert!(err.contains("`Drupe::Action::Action::Read`"), "{err}");
    assert!(err.contains(r#"`Drupe::Action::"Action::Read"`"#), "{err}");
    assert!(err.contains(r#"`Drupe::Action::Action::"Read"`"#), "{err}");
}

#[test]
fn numbers_without_a_cedar_rendering_are_input_errors() {
    let mut auth = authorizer(AFTER_RESPONSE, SCHEMA);
    for (value, expected) in [
        (json!(-2.5e-10), "exponent form"),
        (json!(1e-7), "exponent form"),
        (json!(u64::MAX), "out of range"),
        // Integral but past u64 either way: parsed as an `f64`, still reported
        // as an out-of-range integer, not as exponent form.
        (json!(1e308), "out of range"),
        (serde_json::from_str("-100000000000000000000").unwrap(), "out of range"),
        (serde_json::from_str("-9223372036854775809").unwrap(), "out of range"),
    ] {
        let mut e = read(1, "request");
        e.logged.insert("extra".into(), [("n".to_string(), value)].into());
        let err = auth.is_authorized(&e).unwrap_err().to_string();
        assert!(err.contains(expected), "{err}");
    }
    assert_eq!((auth.decision_count(), auth.last_timestamp()), (0, None));
}
