use dogwood_language::{Event, Value, parse_trace};

#[test]
fn parsed_event_rebuilds_without_losing_contents() {
    let trace = r#"
@17 scope(principal: Svc::User::"a\"b", resource: Svc::Gateway::"gw1") entities(Svc::Group::"admins": {}, Svc::User::"a\"b": { dept: "eng", profile: { level: 5 } } in [Svc::Group::"admins"]) request_context(input: { doc: "x" }, system: { note: "a) { weird" }) Svc::Action::"Read"::request(input: { doc: "x", tags: ["one", "two"] }, callerPrincipal: Svc::User::"a\"b", callerResource: Svc::Gateway::"gw1", requestId: "r-1")
"#;
    let event = parse_trace(trace)
        .expect("trace parses")
        .into_iter()
        .next()
        .expect("one event");

    let rebuilt = event.clone().into_builder().build();

    assert_eq!(rebuilt, event);
}

#[test]
fn builder_can_restore_a_top_level_logged_field() {
    let event = Event::builder("Svc::Action::Read", "request")
        .logged_field("requestId", Value::String("r-1".to_string()))
        .build();

    assert_eq!(
        event.field_path(&["requestId".to_string()]),
        Some(&Value::String("r-1".to_string()))
    );
}
