use std::collections::BTreeMap;

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

#[test]
fn builder_can_restore_complete_top_level_request_context_fields() {
    let empty_metadata = Value::Object(BTreeMap::new());
    let event = Event::builder("Svc::Action::Read", "request")
        .request_context_field("authenticated", Value::Bool(true))
        .request_context_field("metadata", empty_metadata.clone())
        .build();

    assert_eq!(
        event.request_context_path(&["authenticated".to_string()]),
        Some(&Value::Bool(true))
    );
    assert_eq!(
        event.request_context_path(&["metadata".to_string()]),
        Some(&empty_metadata)
    );
}

#[test]
fn request_context_groups_rebuild_losslessly_for_every_value_shape() {
    let trace = r#"@17 request_context(absent: null, authenticated: true, attempts: -17, ratio: 1.2500, message: "quote \" slash \\ newline \n snowman \u{2603}", owner: Svc::User::"a\"b", values: [null, false, 9, 2.50, "x", Svc::User::"id", [], {}], metadata: { nested: { flag: true }, list: ["one", 2], empty: {} }, empty: {}, "quoted.name": "preserved") Svc::Action::"Read"::request()"#;
    let original = parse_trace(trace)
        .expect("trace parses")
        .into_iter()
        .next()
        .expect("one event");

    let namespace = original
        .namespace()
        .iter()
        .map(String::as_str)
        .collect::<Vec<_>>();
    let mut builder = Event::builder_for(&namespace, original.action(), original.kind())
        .timestamp(original.timestamp());
    for (name, value) in original.request_context_groups() {
        builder = builder.request_context_field(name, value.clone());
    }

    assert_eq!(builder.build(), original);
}
