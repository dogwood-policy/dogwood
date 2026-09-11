//! Escaped action IDs must retain their decoded identity through lowering and
//! every schema-aware temporal/provider validation lookup.

use dogwood_language::{
    LoweredPolicySet, PolicySchema, ProviderDeclarations, ServiceSchema, Validator,
};

struct ActionIdCase {
    label: &'static str,
    source: &'static str,
}

const ACTION_IDS: &[ActionIdCase] = &[
    ActionIdCase {
        label: "ordinary",
        source: "Event",
    },
    ActionIdCase {
        label: "empty",
        source: "",
    },
    ActionIdCase {
        label: "quote",
        source: r#"a\"b"#,
    },
    ActionIdCase {
        label: "backslash",
        source: r#"a\\b"#,
    },
    ActionIdCase {
        label: "hex quote",
        source: r#"hex\x22quote"#,
    },
    ActionIdCase {
        label: "hex backslash",
        source: r#"hex\x5cslash"#,
    },
    ActionIdCase {
        label: "hex delete",
        source: r#"hex\x7fdelete"#,
    },
    ActionIdCase {
        label: "escaped single quote",
        source: r#"single\'quote"#,
    },
    ActionIdCase {
        label: "newline",
        source: r#"a\nb"#,
    },
    ActionIdCase {
        label: "carriage return",
        source: r#"a\rb"#,
    },
    ActionIdCase {
        label: "tab",
        source: r#"a\tb"#,
    },
    ActionIdCase {
        label: "nul",
        source: r#"a\0b"#,
    },
    ActionIdCase {
        label: "unicode escape",
        source: r#"\u{e}"#,
    },
    ActionIdCase {
        label: "underscored unicode",
        source: r#"u\u{0_1_2_3}"#,
    },
    ActionIdCase {
        label: "underscored unicode control",
        source: r#"\u{0_0_0_e}"#,
    },
    ActionIdCase {
        label: "underscored unicode quote",
        source: r#"u\u{0_0_2_2}q"#,
    },
    ActionIdCase {
        label: "literal escape text",
        source: r#"\\u{e}"#,
    },
    ActionIdCase {
        label: "literal hex escape text",
        source: r#"\\x22"#,
    },
    ActionIdCase {
        label: "printable unicode",
        source: "犬",
    },
];

fn validation_errors(policy: &str, schema_source: &str, service: &ServiceSchema) -> Vec<String> {
    let schema = PolicySchema::from_cedarschema_str(schema_source)
        .unwrap_or_else(|error| panic!("schema should parse: {error:?}\n{schema_source}"));
    let lowered = LoweredPolicySet::from_str(policy, service, &schema)
        .unwrap_or_else(|error| panic!("policy should lower: {error:?}\n{policy}"));
    Validator::new()
        .validate(&lowered)
        .validation_errors()
        .map(|error| error.to_string())
        .collect()
}

fn cedar_validation_errors(policy: &str, schema_source: &str) -> Vec<String> {
    let schema = cedar_policy::Schema::from_cedarschema_str(schema_source)
        .unwrap_or_else(|error| panic!("Cedar schema should parse: {error:?}\n{schema_source}"))
        .0;
    let policies: cedar_policy::PolicySet = policy
        .parse()
        .unwrap_or_else(|error| panic!("Cedar policy should parse: {error:?}\n{policy}"));
    cedar_policy::Validator::new(schema)
        .validate(&policies, cedar_policy::ValidationMode::Strict)
        .validation_errors()
        .map(|error| error.to_string())
        .collect()
}

#[track_caller]
fn assert_cedar_rejects(label: &str, policy: &str, schema_source: &str, expected_fragment: &str) {
    let errors = cedar_validation_errors(policy, schema_source);
    assert!(
        errors.iter().any(|error| error.contains(expected_fragment)),
        "Cedar witness for {label} should reject with {expected_fragment:?}, got {errors:#?}"
    );
}

fn cedar_current_request_policy(scope: &str, body: &str) -> String {
    format!(
        r#"
        permit (principal, {scope}, resource)
        when {{ {body} }};
        "#
    )
}

fn temporal_schema(action_source: &str) -> String {
    format!(
        r#"
        namespace Escaped {{
            entity User;
            entity Doc;
            entity Mode enum ["read", "write"];

            action "Gate" appliesTo {{
                principal: [User], resource: [Doc],
                context: {{ input: {{ mode: Mode }} }}
            }};
            action "{action_source}" appliesTo {{
                principal: [User], resource: [Doc],
                context: {{ input: {{ mode: Mode }} }}
            }};
        }}
        "#
    )
}

#[test]
fn cedar_cross_reference_covers_every_legal_escape_spelling() {
    for case in ACTION_IDS {
        let schema = temporal_schema(case.source);
        let scope = format!(r#"action == Escaped::Action::"{}""#, case.source);
        let errors = cedar_validation_errors(
            &cedar_current_request_policy(&scope, "context.input.mode == 5"),
            &schema,
        );
        assert!(
            errors.len() == 1 && errors[0].contains("not compatible"),
            "Cedar cross-reference for {}: {errors:#?}",
            case.label
        );
    }
}

#[test]
fn cedar_cross_reference_equates_alternate_escape_spellings() {
    let pairs = [
        (r#"a\"b"#, r#"a\x22b"#),
        (r#"a\\b"#, r#"a\x5cb"#),
        (r#"\u{e}"#, r#"\u{0_0_0_e}"#),
        (r#"u\u{123}"#, r#"u\u{0_1_2_3}"#),
        ("single'quote", r#"single\'quote"#),
    ];

    for (declaration, reference) in pairs {
        let schema = temporal_schema(declaration);
        let scope = format!(r#"action == Escaped::Action::"{reference}""#);
        let errors = cedar_validation_errors(
            &cedar_current_request_policy(&scope, "context.input.mode == 5"),
            &schema,
        );
        assert!(
            errors.len() == 1 && errors[0].contains("not compatible"),
            "Cedar should resolve {reference:?} to declaration {declaration:?}: {errors:#?}"
        );
    }
}

#[test]
fn cedar_cross_reference_distinguishes_escape_text_from_its_character() {
    let schema = r#"
        namespace Escaped {
            entity User;
            entity Doc;
            entity Mode enum ["read", "write"];
            action "\u{e}" appliesTo {
                principal: [User], resource: [Doc],
                context: { input: { mode: Mode } }
            };
            action "\\u{e}" appliesTo {
                principal: [User], resource: [Doc],
                context: { input: { mode: Long } }
            };
        }
    "#;
    let control_errors = cedar_validation_errors(
        &cedar_current_request_policy(
            r#"action == Escaped::Action::"\u{0_0_0_e}""#,
            "context.input.mode == 5",
        ),
        schema,
    );
    assert!(
        control_errors.len() == 1 && control_errors[0].contains("not compatible"),
        "U+000E action should retain its enum field: {control_errors:#?}"
    );

    let literal_errors = cedar_validation_errors(
        &cedar_current_request_policy(
            r#"action == Escaped::Action::"\\u{e}""#,
            "context.input.mode == 5",
        ),
        schema,
    );
    assert!(
        literal_errors.is_empty(),
        "literal escape-text action should retain its Long field: {literal_errors:#?}"
    );
}

#[test]
fn cedar_entity_uid_display_escapes_action_ids_canonically() {
    let cases = [
        (r#"Action::"plain""#, r#"Action::"plain""#),
        (r#"Action::"a\"b""#, r#"Action::"a\"b""#),
        (r#"Action::"a\x22b""#, r#"Action::"a\"b""#),
        (r#"Action::"a\\b""#, r#"Action::"a\\b""#),
        (r#"Action::"a\x5cb""#, r#"Action::"a\\b""#),
        (r#"Action::"a\nb""#, r#"Action::"a\nb""#),
        (r#"Action::"a\rb""#, r#"Action::"a\rb""#),
        (r#"Action::"a\tb""#, r#"Action::"a\tb""#),
        (r#"Action::"a\0b""#, r#"Action::"a\0b""#),
        (r#"Action::"\u{e}""#, r#"Action::"\u{e}""#),
        (r#"Action::"\u{0_0_0_e}""#, r#"Action::"\u{e}""#),
        (
            r#"Outer::Inner::Action::"u\u{0_0_2_2}q""#,
            r#"Outer::Inner::Action::"u\"q""#,
        ),
        (r#"Action::"\\u{e}""#, r#"Action::"\\u{e}""#),
    ];

    for (source, expected) in cases {
        let uid: cedar_policy_core::ast::EntityUID = source
            .parse()
            .unwrap_or_else(|error| panic!("{source}: {error}"));
        assert_eq!(uid.to_string(), expected, "{source}");
    }
}

fn namespace_schema(namespace: Option<&str>, action_source: &str) -> String {
    let body = format!(
        r#"
        entity User;
        entity Doc;
        entity Mode enum ["read", "write"];
        action "Gate" appliesTo {{
            principal: [User], resource: [Doc],
            context: {{ input: {{ mode: Mode }} }}
        }};
        action "{action_source}" appliesTo {{
            principal: [User], resource: [Doc],
            context: {{ input: {{ mode: Mode }} }}
        }};
        "#
    );
    match namespace {
        Some(namespace) => format!("namespace {namespace} {{ {body} }}"),
        None => body,
    }
}

fn action_uid(namespace: Option<&str>, action_source: &str) -> String {
    match namespace {
        Some(namespace) => format!(r#"{namespace}::Action::"{action_source}""#),
        None => format!(r#"Action::"{action_source}""#),
    }
}

#[test]
fn temporal_predicate_type_check_is_invariant_under_action_id_escaping() {
    let service = ServiceSchema::defaults();
    let expected = validation_errors(
        r#"
        permit (principal, action == Escaped::Action::"Gate", resource)
        when temporal {
            formerly within 1h Escaped::Action::"Event"::request{ input.mode: 5 }
        };
        "#,
        &temporal_schema("Event"),
        &service,
    );
    assert_eq!(expected.len(), 1);
    assert!(expected[0].contains("expects `Mode` but got `int`"));

    for case in &ACTION_IDS[1..] {
        let schema = temporal_schema(case.source);
        // Cedar has no temporal event-pattern syntax. Its corresponding
        // obligation is a policy scoped to that event action which reads the
        // same declared field with the same incompatible operand.
        assert_cedar_rejects(
            case.label,
            &cedar_current_request_policy(
                &format!(r#"action == Escaped::Action::"{}""#, case.source),
                "context.input.mode == 5",
            ),
            &schema,
            "not compatible",
        );

        let policy = format!(
            r#"
            permit (principal, action == Escaped::Action::"Gate", resource)
            when temporal {{
                formerly within 1h Escaped::Action::"{}"::request{{ input.mode: 5 }}
            }};
            "#,
            case.source
        );
        let errors = validation_errors(&policy, &schema, &service);
        assert!(
            errors.len() == 1 && errors[0].contains("expects `Mode` but got `int`"),
            "{} action ID changed validation: {errors:#?}",
            case.label
        );
    }
}

#[test]
fn temporal_diagnostics_render_action_ids_like_cedar_eids() {
    for source in [r#"a\"b"#, r#"a\\b"#, r#"\u{e}"#] {
        let schema = temporal_schema(source);
        let scope = format!(r#"action == Escaped::Action::"{source}""#);
        assert_cedar_rejects(
            source,
            &cedar_current_request_policy(&scope, "context.input.mode == 5"),
            &schema,
            "not compatible",
        );

        let policy = format!(
            r#"
            permit (principal, action == Escaped::Action::"Gate", resource)
            when temporal {{
                formerly within 1h Escaped::Action::"{source}"::request{{ input.mode: 5 }}
            }};
            "#
        );
        let uid: cedar_policy_core::ast::EntityUID = format!(r#"Escaped::Action::"{source}""#)
            .parse()
            .expect("Cedar action UID");
        let expected = format!(
            "argument `input.mode` of `{}` expects `Mode` but got `int`",
            uid.eid().escaped()
        );
        assert_eq!(
            validation_errors(&policy, &schema, &ServiceSchema::defaults()),
            vec![expected],
            "temporal diagnostic for {source:?}"
        );
    }
}

#[test]
fn public_validation_handles_top_level_and_multisegment_namespaces() {
    for namespace in [None, Some("Outer::Inner")] {
        let source = r#"a\"b"#;
        let schema = namespace_schema(namespace, source);
        let escaped = action_uid(namespace, source);
        let gate = action_uid(namespace, "Gate");
        let scope = format!("action == {escaped}");
        assert_cedar_rejects(
            &format!("namespace {namespace:?}"),
            &cedar_current_request_policy(&scope, "context.input.mode == 5"),
            &schema,
            "not compatible",
        );

        let policy = format!(
            r#"
            permit (principal, action == {gate}, resource)
            when temporal {{
                formerly within 1h {escaped}::request{{ input.mode: 5 }}
            }};
            "#
        );
        let errors = validation_errors(&policy, &schema, &ServiceSchema::defaults());
        assert!(
            errors.len() == 1 && errors[0].contains("expects `Mode` but got `int`"),
            "namespace {namespace:?} skipped escaped action validation: {errors:#?}"
        );
    }
}

#[test]
fn line_continuations_are_rejected_before_schema_lookup() {
    let source = "line\\\n        continued";
    let schema = namespace_schema(Some("Escaped"), source);
    assert!(
        cedar_policy::Schema::from_cedarschema_str(&schema).is_err(),
        "the public Cedar schema lexer rejects a newline inside an action string"
    );
    PolicySchema::from_cedarschema_str(&schema)
        .expect("Dogwood's core-fragment parser accepts Cedar line continuations");

    let policy = format!(
        r#"
        permit (principal, action == Escaped::Action::"Gate", resource)
        when temporal {{
            formerly within 1h Escaped::Action::"{source}"::request{{ input.mode: 5 }}
        }};
        "#
    );
    let schema = PolicySchema::from_cedarschema_str(&schema).expect("initial schema parse");
    let error = LoweredPolicySet::from_str(&policy, &ServiceSchema::defaults(), &schema)
        .expect_err("the complete Dogwood pipeline should reject the same spelling")
        .to_string();
    assert!(
        error.contains("invalid token"),
        "Dogwood should preserve Cedar's lexer rejection: {error}"
    );
}

fn scoped_schema(special_source: &str) -> String {
    format!(
        r#"
        namespace Escaped {{
            entity User;
            entity Doc;
            entity Mode enum ["read", "write"];

            action "Group";
            action "Witness" appliesTo {{
                principal: [User], resource: [Doc],
                context: {{ input: {{ mode: Long, present: String }} }}
            }};
            action "Normal" in [Action::"Group"] appliesTo {{
                principal: [User], resource: [Doc],
                context: {{ input: {{ mode: Long, present: String, only_normal: String }} }}
            }};
            action "{special_source}" in [Action::"Group"] appliesTo {{
                principal: [User], resource: [Doc],
                context: {{ input: {{ mode: Mode, present: String }} }}
            }};
        }}
        "#
    )
}

fn temporal_current_request_policy(scope: &str, body: &str) -> String {
    format!(
        r#"
        permit (principal, {scope}, resource)
        when temporal {{
            formerly within 1h (
                Escaped::Action::"Witness"::request{{}} && {body}
            )
        }};
        "#
    )
}

fn escaped_group_schema(group_source: &str) -> String {
    format!(
        r#"
        namespace Escaped {{
            entity User;
            entity Doc;
            entity Mode enum ["read", "write"];

            action "{group_source}";
            action "Witness" appliesTo {{
                principal: [User], resource: [Doc],
                context: {{ input: {{ mode: Long, present: String }} }}
            }};
            action "Member" in [Action::"{group_source}"] appliesTo {{
                principal: [User], resource: [Doc],
                context: {{ input: {{ mode: Mode, present: String }} }}
            }};
            action "Other" appliesTo {{
                principal: [User], resource: [Doc],
                context: {{ input: {{ mode: Long, present: String }} }}
            }};
        }}
        "#
    )
}

fn escaped_group_scope(group_source: &str) -> String {
    format!(r#"action in [Escaped::Action::"{group_source}"]"#)
}

#[test]
fn escaped_action_group_ids_expand_members_like_cedar() {
    for case in ACTION_IDS {
        let schema = escaped_group_schema(case.source);
        let scope = escaped_group_scope(case.source);
        let cedar_valid = cedar_validation_errors(
            &cedar_current_request_policy(&scope, r#"context.input.present == "x""#),
            &schema,
        );
        assert!(
            cedar_valid.is_empty(),
            "Cedar cross-reference rejected {} group: {cedar_valid:#?}",
            case.label
        );
        assert_cedar_rejects(
            case.label,
            &cedar_current_request_policy(&scope, "context.input.mode == 5"),
            &schema,
            "not compatible",
        );

        let dogwood_valid = validation_errors(
            &temporal_current_request_policy(&scope, r#"context.input.present == "x""#),
            &schema,
            &ServiceSchema::defaults(),
        );
        assert!(
            dogwood_valid.is_empty(),
            "{} group failed temporal expansion: {dogwood_valid:#?}",
            case.label
        );
        let dogwood_invalid = validation_errors(
            &temporal_current_request_policy(&scope, "context.input.mode == 5"),
            &schema,
            &ServiceSchema::defaults(),
        );
        assert!(
            dogwood_invalid
                .iter()
                .any(|error| error.contains("same type")),
            "{} group skipped its member's type mismatch: {dogwood_invalid:#?}",
            case.label
        );
    }
}

#[test]
fn escaped_action_group_lookup_equates_alternate_spellings() {
    let pairs = [
        (r#"a\"b"#, r#"a\x22b"#),
        (r#"a\\b"#, r#"a\x5cb"#),
        (r#"\u{e}"#, r#"\u{0_0_0_e}"#),
        (r#"u\u{123}"#, r#"u\u{0_1_2_3}"#),
        ("single'quote", r#"single\'quote"#),
    ];

    for (declaration, reference) in pairs {
        let schema = escaped_group_schema(declaration);
        let scope = escaped_group_scope(reference);
        assert_cedar_rejects(
            reference,
            &cedar_current_request_policy(&scope, "context.input.mode == 5"),
            &schema,
            "not compatible",
        );
        let errors = validation_errors(
            &temporal_current_request_policy(&scope, "context.input.mode == 5"),
            &schema,
            &ServiceSchema::defaults(),
        );
        assert!(
            errors.iter().any(|error| error.contains("same type")),
            "group declaration {declaration:?} did not resolve reference {reference:?}: \
             {errors:#?}"
        );
    }
}

fn distinct_escaped_group_schema() -> &'static str {
    r#"
        namespace Escaped {
            entity User;
            entity Doc;
            entity Mode enum ["read", "write"];

            action "\u{e}";
            action "\\u{e}";
            action "Witness" appliesTo {
                principal: [User], resource: [Doc],
                context: { input: { mode: Long, present: String } }
            };
            action "ControlMember" in [Action::"\u{0_0_0_e}"] appliesTo {
                principal: [User], resource: [Doc],
                context: { input: { mode: Mode, present: String } }
            };
            action "LiteralMember" in [Action::"\\u{e}"] appliesTo {
                principal: [User], resource: [Doc],
                context: { input: { mode: Long, present: String } }
            };
        }
    "#
}

#[test]
fn escaped_action_group_identity_is_decoded_once() {
    let schema = distinct_escaped_group_schema();
    let cases = [
        ("control", r#"\u{0_0_0_e}"#, true),
        ("literal escape text", r#"\\u{e}"#, false),
    ];

    for (label, group_source, expects_mismatch) in cases {
        let scope = escaped_group_scope(group_source);
        let cedar_errors = cedar_validation_errors(
            &cedar_current_request_policy(&scope, "context.input.mode == 5"),
            schema,
        );
        assert_eq!(
            cedar_errors
                .iter()
                .any(|error| error.contains("not compatible")),
            expects_mismatch,
            "Cedar cross-reference for {label}: {cedar_errors:#?}"
        );

        let dogwood_errors = validation_errors(
            &temporal_current_request_policy(&scope, "context.input.mode == 5"),
            schema,
            &ServiceSchema::defaults(),
        );
        assert_eq!(
            dogwood_errors
                .iter()
                .any(|error| error.contains("same type")),
            expects_mismatch,
            "Dogwood conflated the {label} group: {dogwood_errors:#?}"
        );
        if !expects_mismatch {
            assert!(
                dogwood_errors.is_empty(),
                "literal escape-text group should validate cleanly: {dogwood_errors:#?}"
            );
        }
    }
}

#[test]
fn escaped_action_groups_expand_transitively_across_namespaces() {
    let schema = r#"
        namespace Outer::Inner {
            action "root\"group";
        }
        namespace Escaped {
            entity User;
            entity Doc;
            entity Mode enum ["read", "write"];

            action "middle\\group" in [Outer::Inner::Action::"root\x22group"];
            action "Leaf" in [Action::"middle\x5cgroup"] appliesTo {
                principal: [User], resource: [Doc],
                context: { input: { mode: Mode, present: String } }
            };
            action "Witness" appliesTo {
                principal: [User], resource: [Doc],
                context: { input: { mode: Long, present: String } }
            };
        }
    "#;
    let scope = r#"action in [Outer::Inner::Action::"root\"group"]"#;
    assert_cedar_rejects(
        "cross-namespace escaped group",
        &cedar_current_request_policy(scope, "context.input.mode == 5"),
        schema,
        "not compatible",
    );
    let policy = format!(
        r#"
        permit (principal, {scope}, resource)
        when temporal {{
            formerly within 1h (
                Escaped::Action::"Witness"::request{{}} &&
                context.input.mode == 5
            )
        }};
        "#
    );
    let errors = validation_errors(&policy, schema, &ServiceSchema::defaults());
    assert!(
        errors.iter().any(|error| error.contains("same type")),
        "transitive cross-namespace expansion skipped Leaf: {errors:#?}"
    );
}

#[test]
fn escaped_appliable_group_contributes_itself_and_its_members() {
    let schema = r#"
        namespace Escaped {
            entity User;
            entity Doc;
            entity Mode enum ["read", "write"];

            action "hub\"group" appliesTo {
                principal: [User], resource: [Doc],
                context: { input: { mode: Long, present: String } }
            };
            action "Member" in [Action::"hub\x22group"] appliesTo {
                principal: [User], resource: [Doc],
                context: { input: { mode: Mode, present: String } }
            };
            action "Witness" appliesTo {
                principal: [User], resource: [Doc],
                context: { input: { mode: Long, present: String } }
            };
        }
    "#;
    let scope = r#"action in [Escaped::Action::"hub\"group"]"#;
    assert_cedar_rejects(
        "escaped appliable group",
        &cedar_current_request_policy(scope, "context.input.mode == 5"),
        schema,
        "not compatible",
    );
    let errors = validation_errors(
        &temporal_current_request_policy(scope, "context.input.mode == 5"),
        schema,
        &ServiceSchema::defaults(),
    );
    assert!(
        errors.iter().any(|error| error.contains("same type")),
        "escaped appliable group skipped its differently typed member: {errors:#?}"
    );
}

#[test]
fn temporal_rule_signature_lookup_checks_escaped_action_ids() {
    let source = r#"a\"b"#;
    let schema = scoped_schema(source);
    let scope = format!(r#"action == Escaped::Action::"{source}""#);
    assert_cedar_rejects(
        "quote-containing rule action",
        &cedar_current_request_policy(&scope, "context.input.mode == 5"),
        &schema,
        "not compatible",
    );
    let errors = validation_errors(
        &temporal_current_request_policy(&scope, "context.input.mode == 5"),
        &schema,
        &ServiceSchema::defaults(),
    );
    assert!(
        errors.iter().any(|error| error.contains("same type")),
        "expected current-request type mismatch, got {errors:#?}"
    );
}

#[test]
fn temporal_context_field_lookup_checks_escaped_action_ids() {
    let source = r#"a\\b"#;
    let schema = scoped_schema(source);
    let scope = format!(r#"action == Escaped::Action::"{source}""#);
    assert_cedar_rejects(
        "backslash-containing rule action",
        &cedar_current_request_policy(&scope, "context.input.only_normal == \"x\""),
        &schema,
        "not found",
    );
    let errors = validation_errors(
        &temporal_current_request_policy(&scope, "context.input.only_normal == \"x\""),
        &schema,
        &ServiceSchema::defaults(),
    );
    assert_eq!(
        errors,
        vec!["record has no field `only_normal` in `context.input.only_normal` path".to_string()],
        "missing-field diagnostic"
    );
}

#[test]
fn every_action_scope_form_checks_the_escaped_member() {
    let source = r#"a\"b"#;
    let scopes = [
        format!(r#"action == Escaped::Action::"{source}""#),
        format!(r#"action in [Escaped::Action::"Normal", Escaped::Action::"{source}"]"#),
        r#"action in [Escaped::Action::"Group"]"#.to_string(),
        "action".to_string(),
    ];
    let schema = scoped_schema(source);

    for scope in scopes {
        assert_cedar_rejects(
            &format!("scope {scope:?}"),
            &cedar_current_request_policy(&scope, "context.input.mode == 5"),
            &schema,
            "not compatible",
        );
        let errors = validation_errors(
            &temporal_current_request_policy(&scope, "context.input.mode == 5"),
            &schema,
            &ServiceSchema::defaults(),
        );
        assert!(
            errors.iter().any(|error| error.contains("same type")),
            "scope {scope:?} skipped the escaped member: {errors:#?}"
        );
    }
}

const PROVIDERS: &str = r#"
{
  "availableProviders": {
    "Strings::Matches": {
      "argumentTypes": [{ "paramType": "string" }],
      "outputType": {
        "paramType": "record",
        "fields": { "matched": { "paramType": "bool" } },
        "required": ["matched"]
      }
    }
  }
}
"#;

fn provider_service() -> ServiceSchema {
    let providers = ProviderDeclarations::from_json(PROVIDERS).expect("providers parse");
    ServiceSchema::builder()
        .providers(providers)
        .build()
        .expect("provider service builds")
}

fn provider_policy(scope: &str, argument: &str) -> String {
    format!(
        r#"
        permit (principal, {scope}, resource)
        when guardrails {{
            Strings::Matches({argument}).matched == true
        }};
        "#
    )
}

fn provider_scoped_schema(special_source: &str) -> String {
    format!(
        r#"
        namespace Escaped {{
            entity User;
            entity Doc;
            entity Mode enum ["read", "write"];

            action "Group";
            action "Normal" in [Action::"Group"] appliesTo {{
                principal: [User], resource: [Doc],
                context: {{ input: {{ mode: String, present: String, missing: String }} }}
            }};
            action "{special_source}" in [Action::"Group"] appliesTo {{
                principal: [User], resource: [Doc],
                context: {{ input: {{ mode: Mode, present: String }} }}
            }};
        }}
        "#
    )
}

fn escaped_scopes(source: &str) -> [String; 4] {
    [
        format!(r#"action == Escaped::Action::"{source}""#),
        format!(r#"action in [Escaped::Action::"Normal", Escaped::Action::"{source}"]"#),
        r#"action in [Escaped::Action::"Group"]"#.to_string(),
        "action".to_string(),
    ]
}

#[test]
fn every_provider_scope_form_checks_missing_fields_on_the_escaped_member() {
    let source = r#"a\"b"#;
    let schema = provider_scoped_schema(source);

    for scope in escaped_scopes(source) {
        assert_cedar_rejects(
            &format!("provider missing-field scope {scope:?}"),
            &cedar_current_request_policy(&scope, "context.input.missing == \"x\""),
            &schema,
            "not found",
        );
        let errors = validation_errors(
            &provider_policy(&scope, "context.input.missing"),
            &schema,
            &provider_service(),
        );
        assert!(
            errors.len() == 1 && errors[0].contains("missing") && errors[0].contains("not present"),
            "scope {scope:?} skipped provider missing-field validation: {errors:#?}"
        );
    }
}

#[test]
fn every_provider_scope_form_checks_types_on_the_escaped_member() {
    let source = r#"a\\b"#;
    let schema = provider_scoped_schema(source);

    for scope in escaped_scopes(source) {
        assert_cedar_rejects(
            &format!("provider field-type scope {scope:?}"),
            &cedar_current_request_policy(&scope, "context.input.mode == \"read\""),
            &schema,
            "not compatible",
        );
        let errors = validation_errors(
            &provider_policy(&scope, "context.input.mode"),
            &schema,
            &provider_service(),
        );
        assert!(
            errors.len() == 1 && errors[0].contains("Mode"),
            "scope {scope:?} skipped provider type validation: {errors:#?}"
        );
    }
}

#[test]
fn providers_expand_every_escaped_action_group_like_cedar() {
    for case in ACTION_IDS {
        let schema = escaped_group_schema(case.source);
        let scope = escaped_group_scope(case.source);
        let cedar_valid = cedar_validation_errors(
            &cedar_current_request_policy(&scope, r#"context.input.present == "x""#),
            &schema,
        );
        assert!(
            cedar_valid.is_empty(),
            "Cedar provider witness rejected {} group: {cedar_valid:#?}",
            case.label
        );
        assert_cedar_rejects(
            case.label,
            &cedar_current_request_policy(&scope, r#"context.input.mode == "read""#),
            &schema,
            "not compatible",
        );

        let provider_valid = validation_errors(
            &provider_policy(&scope, "context.input.present"),
            &schema,
            &provider_service(),
        );
        assert!(
            provider_valid.is_empty(),
            "{} group failed valid provider expansion: {provider_valid:#?}",
            case.label
        );
        let provider_invalid = validation_errors(
            &provider_policy(&scope, "context.input.mode"),
            &schema,
            &provider_service(),
        );
        assert!(
            provider_invalid.len() == 1 && provider_invalid[0].contains("Mode"),
            "{} group skipped provider type validation: {provider_invalid:#?}",
            case.label
        );
    }
}

fn canonical_action(source: &str) -> String {
    let uid: cedar_policy_core::ast::EntityUID = format!(r#"Escaped::Action::"{source}""#)
        .parse()
        .expect("Cedar action UID");
    uid.to_string()
}

#[test]
fn provider_diagnostics_render_action_ids_as_canonical_cedar_uids() {
    let cases = [
        ("quote", r#"a\"b"#),
        ("backslash", r#"a\\b"#),
        ("control", r#"\u{e}"#),
    ];

    for (label, source) in cases {
        let schema = provider_scoped_schema(source);
        let scope = format!(r#"action == Escaped::Action::"{source}""#);
        assert_cedar_rejects(
            label,
            &cedar_current_request_policy(&scope, "context.input.missing == \"x\""),
            &schema,
            "not found",
        );
        let errors = validation_errors(
            &provider_policy(&scope, "context.input.missing"),
            &schema,
            &provider_service(),
        );
        let expected_action = canonical_action(source);
        assert_eq!(
            errors,
            vec![format!(
                "provider `Strings::Matches`: argument `context.input.missing` is not present \
                 in the context of action `{expected_action}`"
            )],
            "{label} diagnostic should use Cedar's canonical UID rendering"
        );
    }
}
