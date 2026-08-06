//! `LoweredPolicySet::event_signatures` — the derived event field surface.
//!
//! The accessor exposes, per `(action, kind)`, the declared **leaf** fields an
//! event may carry — including schema-injected fields (`caller*`, custom
//! injected/pinned/nested fields) that are NOT part of the action's Cedar
//! `context`. This is the field surface a client uses to validate or construct
//! events; the built-in engines read the same fields dynamically.

use dogwood_language::{
    EventFieldType, EventPinRoot, LoweredPolicySet, PolicySchema, ServiceSchema,
};

const SCHEMA: &str = r#"
namespace Drupe {
  type LoginInput = { server: String, user: String };
  type LoginOutput = { code: Long };
  entity Gateway;
  entity OAuthUser = { id: String };
  action "Login" appliesTo {
    principal: [OAuthUser], resource: [Gateway],
    context: { input: LoginInput, output?: LoginOutput }
  };
}
"#;

fn policy() -> String {
    // A trivial temporal policy so the set lowers with an event schema derived.
    "permit (\n  principal,\n  action == Drupe::Action::\"Login\",\n  resource\n)\nwhen temporal {\n  formerly within 1h Drupe::Action::\"Login\"::request{}\n};".to_string()
}

fn lower(service: &ServiceSchema) -> LoweredPolicySet {
    let ps = PolicySchema::from_cedarschema_str(SCHEMA).expect("schema");
    LoweredPolicySet::from_str(&policy(), service, &ps).expect("lower")
}

/// Collect an event's leaf paths (dotted) for a given (action, kind).
fn leaf_paths(lowered: &LoweredPolicySet, action: &str, kind: &str) -> Vec<String> {
    let sig = lowered
        .event_signatures()
        .find(|s| s.action() == action && s.kind() == kind)
        .unwrap_or_else(|| panic!("no signature for {action}::{kind}"));
    let mut ps: Vec<String> = sig.fields().map(|f| f.path().join(".")).collect();
    ps.sort();
    ps
}

#[test]
fn default_schema_surfaces_injected_reserved_fields() {
    let lowered = lower(&ServiceSchema::defaults());
    let req = leaf_paths(&lowered, "Login", "request");
    // Spliced input fields — present in the Cedar context.
    assert!(req.contains(&"input.server".to_string()), "{req:?}");
    assert!(req.contains(&"input.user".to_string()), "{req:?}");
    // Injected reserved fields — NOT in the Cedar context, only on the derived
    // event. This is the surface the solver was missing.
    assert!(req.contains(&"callerPrincipal".to_string()), "{req:?}");
    assert!(req.contains(&"callerResource".to_string()), "{req:?}");
    assert!(req.contains(&"requestId".to_string()), "{req:?}");
    // request does NOT carry output.
    assert!(!req.iter().any(|p| p.starts_with("output.")), "{req:?}");
}

#[test]
fn response_carries_output_leaves() {
    let lowered = lower(&ServiceSchema::defaults());
    let res = leaf_paths(&lowered, "Login", "response");
    assert!(res.contains(&"input.user".to_string()), "{res:?}");
    assert!(res.contains(&"output.code".to_string()), "{res:?}");
}

#[test]
fn namespace_is_qualified_with_action_segment() {
    let lowered = lower(&ServiceSchema::defaults());
    let sig = lowered
        .event_signatures()
        .find(|s| s.action() == "Login" && s.kind() == "request")
        .unwrap();
    assert_eq!(sig.namespace(), ["Drupe".to_string(), "Action".to_string()]);
    assert!(sig.is_decision(), "request is a decision point");
    let res = lowered
        .event_signatures()
        .find(|s| s.action() == "Login" && s.kind() == "response")
        .unwrap();
    assert!(!res.is_decision(), "response is history-only");
}

#[test]
fn field_types_are_projected() {
    let lowered = lower(&ServiceSchema::defaults());
    let sig = lowered
        .event_signatures()
        .find(|s| s.action() == "Login" && s.kind() == "response")
        .unwrap();
    // Look each field up by path and assert its projected type DIRECTLY — a
    // guarded-match loop would pass vacuously if a field were dropped or
    // mis-projected (the arm just wouldn't fire), so resolve-then-assert.
    let ty_of = |dotted: &str| -> EventFieldType {
        sig.fields()
            .find(|f| f.path().join(".") == dotted)
            .unwrap_or_else(|| {
                panic!(
                    "no field {dotted}; have {:?}",
                    sig.fields().map(|f| f.path().join(".")).collect::<Vec<_>>()
                )
            })
            .field_type()
            .clone()
    };
    // A concrete Cedar scalar projects to `Cedar(<rendered type>)`.
    assert_eq!(
        ty_of("output.code"),
        EventFieldType::Cedar("Long".to_string())
    );
    // A `principalType(A)` injected field projects to the declared entity-type
    // SET (not a Cedar-text type).
    match ty_of("callerPrincipal") {
        EventFieldType::EntityTypes(tys) => {
            assert!(tys.iter().any(|t| t.ends_with("OAuthUser")), "{tys:?}");
        }
        other => panic!("callerPrincipal should be EntityTypes, got {other:?}"),
    }
}

#[test]
fn custom_injected_and_nested_fields_are_surfaced() {
    // A custom event schema injecting a nested field (`meta.session.id`)
    // alongside the stock inputs — the general injected-field case.
    let service = ServiceSchema::builder()
        .event_schema_str(
            r#"decision event <A>::request {
                ...inputs(A),
                meta: { session: { id: String } },
                requestId: String,
            }"#,
        )
        .build()
        .expect("event schema");
    let lowered = lower(&service);
    let req = leaf_paths(&lowered, "Login", "request");
    // The deep injected leaf is surfaced at its full dotted path.
    assert!(req.contains(&"meta.session.id".to_string()), "{req:?}");
    // The intermediate group is NOT yielded (only leaves).
    assert!(!req.contains(&"meta".to_string()), "{req:?}");
    assert!(!req.contains(&"meta.session".to_string()), "{req:?}");
}

#[test]
fn common_type_ref_context_input_fields_are_surfaced_end_to_end() {
    // The public-surface guard for the common-type-ref-context derivation fix
    // (corpus 5008/5009): an action whose `context` is a common-type REFERENCE
    // (`context: ReadCtx`) rather than an inline record. Before the fix,
    // `event_signatures()` reported NO input fields for such an action (only the
    // reserved leaves), silently breaking any field-enumerating consumer. This
    // asserts the accessor now surfaces the referenced input fields. (Uses its
    // own schema — the shared `SCHEMA` above declares only inline-record
    // contexts, so it never exercised this path.)
    const CTXREF_SCHEMA: &str = r#"
    namespace Drupe {
      type LoginInput = { user: String };
      type ReadCtx = { input: { document: String, user: String } };
      entity Gateway;
      entity OAuthUser = { id: String };
      action "Login" appliesTo {
        principal: [OAuthUser], resource: [Gateway], context: { input: LoginInput }
      };
      action "Read" appliesTo {
        principal: [OAuthUser], resource: [Gateway], context: ReadCtx
      };
    }
    "#;
    let ps = PolicySchema::from_cedarschema_str(CTXREF_SCHEMA).expect("schema");
    let policy = "permit (\n  principal,\n  action == Drupe::Action::\"Read\",\n  resource\n)\nwhen temporal {\n  formerly within 1h Drupe::Action::\"Login\"::request{ input.user: context.input.user }\n};";
    let lowered =
        LoweredPolicySet::from_str(policy, &ServiceSchema::defaults(), &ps).expect("lower");
    let read = leaf_paths(&lowered, "Read", "request");
    // The common-type-ref context's input fields must be surfaced — the exact
    // thing the fuzzer found missing (an empty `Read` input).
    assert!(read.contains(&"input.user".to_string()), "{read:?}");
    assert!(read.contains(&"input.document".to_string()), "{read:?}");
}

#[test]
fn default_schema_has_principal_pin() {
    let lowered = lower(&ServiceSchema::defaults());
    let mut n = 0;
    for sig in lowered.event_signatures() {
        n += 1;
        // The default schema pins callerPrincipal on every event kind.
        assert_eq!(sig.pins().count(), 1, "default schema pins callerPrincipal");
    }
    assert!(
        n > 0,
        "at least one signature exists (assertion not vacuous)"
    );
}

#[test]
fn scope_pins_surfaced_on_both_kinds_with_custom_names() {
    // Two scope pins with CUSTOM field names (not `caller*`) — a principal pin
    // and a resource pin — declared on BOTH event kinds. This proves: (a) the
    // surface is schema-agnostic (no `caller*` special-casing — a buggy impl
    // keyed on the reserved prefix would miss `owner_uid`/`gw_uid`); (b) a
    // resource-rooted pin is surfaced (target=["resource"]); (c) a pin declared
    // on both kinds appears on each signature; (d) each pinned field is also a
    // declared field of its event.
    let service = ServiceSchema::builder()
        .event_schema_str(
            r#"decision event <A>::request {
                ...inputs(A),
                pin owner_uid: principalType(A) = principal,
                pin gw_uid:    resourceType(A)  = resource,
                requestId: String,
            }
            event <A>::response {
                ...inputs(A),
                ...outputs(A),
                pin owner_uid: principalType(A) = principal,
                pin gw_uid:    resourceType(A)  = resource,
                requestId: String,
            }"#,
        )
        .build()
        .expect("event schema with custom-named scope pins");
    let lowered = lower(&service);
    for kind in ["request", "response"] {
        let sig = lowered
            .event_signatures()
            .find(|s| s.action() == "Login" && s.kind() == kind)
            .unwrap_or_else(|| panic!("no Login::{kind}"));
        let pins: Vec<_> = sig.pins().collect();
        assert_eq!(pins.len(), 2, "two pins on {kind}");
        // Principal pin (custom-named).
        let p = pins
            .iter()
            .find(|p| p.field_path() == ["owner_uid".to_string()])
            .unwrap_or_else(|| panic!("owner_uid pin on {kind}"));
        assert_eq!(p.target_path(), ["principal".to_string()]);
        assert_eq!(p.root(), EventPinRoot::Scope);
        // Resource pin (custom-named).
        let r = pins
            .iter()
            .find(|p| p.field_path() == ["gw_uid".to_string()])
            .unwrap_or_else(|| panic!("gw_uid pin on {kind}"));
        assert_eq!(r.target_path(), ["resource".to_string()]);
        assert_eq!(r.root(), EventPinRoot::Scope);
        // Both pinned fields are declared fields of the event.
        for field in ["owner_uid", "gw_uid"] {
            assert!(
                sig.fields().any(|f| f.path() == [field.to_string()]),
                "pinned field {field} is a declared field on {kind}"
            );
        }
    }
}

#[test]
fn context_pin_on_a_custom_nested_field_is_surfaced() {
    // A CONTEXT-rooted pin on a custom nested field (`__drupe.session_id`),
    // pinned to `context.__drupe.session_id` — proves the surface is
    // schema-agnostic (no `caller*` assumption) and carries Context pins too.
    let service = ServiceSchema::builder()
        .event_schema_str(
            r#"decision event <A>::request {
                ...inputs(A),
                __drupe: { pin session_id: String = context.__drupe.session_id },
                requestId: String,
            }"#,
        )
        .build()
        .expect("event schema with a context pin");
    let lowered = lower(&service);
    let sig = lowered
        .event_signatures()
        .find(|s| s.action() == "Login" && s.kind() == "request")
        .unwrap();
    let pins: Vec<_> = sig.pins().collect();
    assert_eq!(pins.len(), 1, "one pin");
    let pin = pins[0];
    assert_eq!(
        pin.field_path(),
        ["__drupe".to_string(), "session_id".to_string()]
    );
    assert_eq!(
        pin.target_path(),
        ["__drupe".to_string(), "session_id".to_string()]
    );
    assert_eq!(pin.root(), EventPinRoot::Context);
    // The pinned field is also a declared leaf field of the event.
    assert!(
        sig.fields()
            .any(|f| f.path() == ["__drupe".to_string(), "session_id".to_string()]),
        "context-pinned field is a declared field"
    );
}
