//! Enum entity IDs must use decoded identity for validation and Cedar-source
//! escaping only when rendered in diagnostics.

use dogwood_language::{LoweredPolicySet, PolicySchema, ServiceSchema, Validator};

struct EnumIdCase {
    label: &'static str,
    declaration: &'static str,
    reference: &'static str,
}

const ENUM_IDS: &[EnumIdCase] = &[
    EnumIdCase {
        label: "ordinary",
        declaration: "ordinary",
        reference: "ordinary",
    },
    EnumIdCase {
        label: "empty",
        declaration: "",
        reference: "",
    },
    EnumIdCase {
        label: "quote",
        declaration: r#"a\"b"#,
        reference: r#"a\x22b"#,
    },
    EnumIdCase {
        label: "backslash",
        declaration: r#"a\\b"#,
        reference: r#"a\x5cb"#,
    },
    EnumIdCase {
        label: "newline",
        declaration: r#"a\nb"#,
        reference: r#"a\u{0_0_0_a}b"#,
    },
    EnumIdCase {
        label: "carriage return",
        declaration: r#"a\rb"#,
        reference: r#"a\u{0_0_0_d}b"#,
    },
    EnumIdCase {
        label: "tab",
        declaration: r#"a\tb"#,
        reference: r#"a\u{0_0_0_9}b"#,
    },
    EnumIdCase {
        label: "nul",
        declaration: r#"a\0b"#,
        reference: r#"a\u{0_0_0_0}b"#,
    },
    EnumIdCase {
        label: "unicode control",
        declaration: r#"\u{e}"#,
        reference: r#"\u{0_0_0_e}"#,
    },
    EnumIdCase {
        label: "underscored unicode",
        declaration: r#"u\u{0_1_2_3}"#,
        reference: r#"u\u{123}"#,
    },
    EnumIdCase {
        label: "underscored unicode quote",
        declaration: r#"u\u{0_0_2_2}q"#,
        reference: r#"u\"q"#,
    },
    EnumIdCase {
        label: "escaped single quote",
        declaration: r#"single\'quote"#,
        reference: "single'quote",
    },
    EnumIdCase {
        label: "literal unicode escape text",
        declaration: r#"\\u{e}"#,
        reference: r#"\\u{e}"#,
    },
    EnumIdCase {
        label: "literal hex escape text",
        declaration: r#"\\x22"#,
        reference: r#"\\x22"#,
    },
    EnumIdCase {
        label: "printable unicode",
        declaration: "犬",
        reference: "犬",
    },
];

fn entity_type(namespace: Option<&str>) -> String {
    match namespace {
        Some(namespace) => format!("{namespace}::Mode"),
        None => "Mode".to_string(),
    }
}

fn action_uid(namespace: Option<&str>, id: &str) -> String {
    match namespace {
        Some(namespace) => format!(r#"{namespace}::Action::"{id}""#),
        None => format!(r#"Action::"{id}""#),
    }
}

fn enum_schema(namespace: Option<&str>, declaration: &str) -> String {
    let body = format!(
        r#"
        entity User;
        entity Doc;
        entity Mode enum ["{declaration}"];
        action "Gate" appliesTo {{
            principal: [User], resource: [Doc],
            context: {{ input: {{ mode: Mode }} }}
        }};
        action "Check" appliesTo {{
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

fn cedar_policy(namespace: Option<&str>, reference: &str) -> String {
    let check = action_uid(namespace, "Check");
    let mode = entity_type(namespace);
    format!(
        r#"
        permit (principal, action == {check}, resource)
        when {{ context.input.mode == {mode}::"{reference}" }};
        "#
    )
}

fn temporal_policy(namespace: Option<&str>, reference: &str) -> String {
    let gate = action_uid(namespace, "Gate");
    let check = action_uid(namespace, "Check");
    let mode = entity_type(namespace);
    format!(
        r#"
        permit (principal, action == {gate}, resource)
        when temporal {{
            formerly within 1h {check}::request{{
                input.mode: {mode}::"{reference}"
            }}
        }};
        "#
    )
}

fn temporal_comparison_policy(namespace: Option<&str>, reference: &str) -> String {
    let check = action_uid(namespace, "Check");
    let mode = entity_type(namespace);
    format!(
        r#"
        permit (principal, action == {check}, resource)
        when temporal {{
            formerly within 1h (
                {check}::request{{}} &&
                context.input.mode == {mode}::"{reference}"
            )
        }};
        "#
    )
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

fn dogwood_validation_errors(policy: &str, schema_source: &str) -> Vec<String> {
    let schema = PolicySchema::from_cedarschema_str(schema_source)
        .unwrap_or_else(|error| panic!("Dogwood schema should load: {error:?}\n{schema_source}"));
    let lowered = LoweredPolicySet::from_str(policy, &ServiceSchema::defaults(), &schema)
        .unwrap_or_else(|error| panic!("Dogwood policy should lower: {error:?}\n{policy}"));
    Validator::new()
        .validate(&lowered)
        .validation_errors()
        .map(|error| error.to_string())
        .collect()
}

#[test]
fn cedar_cross_reference_accepts_every_enum_escape_spelling() {
    for case in ENUM_IDS {
        let schema = enum_schema(Some("Escaped"), case.declaration);
        let errors =
            cedar_validation_errors(&cedar_policy(Some("Escaped"), case.reference), &schema);
        assert!(
            errors.is_empty(),
            "Cedar rejected {} enum ID: {errors:#?}",
            case.label
        );
    }
}

#[test]
fn cedar_entity_uid_display_pins_enum_id_escaping() {
    let cases = [
        (r#"Mode::"a\x22b""#, r#"Mode::"a\"b""#),
        (r#"Mode::"a\x5cb""#, r#"Mode::"a\\b""#),
        (r#"Mode::"\u{0_0_0_e}""#, r#"Mode::"\u{e}""#),
        (
            r#"Outer::Inner::Mode::"u\u{0_0_2_2}q""#,
            r#"Outer::Inner::Mode::"u\"q""#,
        ),
        (r#"Mode::"\\u{e}""#, r#"Mode::"\\u{e}""#),
    ];

    for (source, expected) in cases {
        let uid: cedar_policy_core::ast::EntityUID = source
            .parse()
            .unwrap_or_else(|error| panic!("{source}: {error}"));
        assert_eq!(uid.to_string(), expected, "{source}");
    }
}

#[test]
fn temporal_validation_accepts_every_enum_escape_spelling() {
    for case in ENUM_IDS {
        let schema = enum_schema(Some("Escaped"), case.declaration);
        let errors =
            dogwood_validation_errors(&temporal_policy(Some("Escaped"), case.reference), &schema);
        assert!(
            errors.is_empty(),
            "Dogwood rejected {} enum ID: {errors:#?}",
            case.label
        );
    }
}

#[test]
fn escaped_enum_ids_work_in_predicate_fields_and_current_request_comparisons() {
    for case in &ENUM_IDS[2..] {
        let schema = enum_schema(Some("Escaped"), case.declaration);
        for policy in [
            temporal_policy(Some("Escaped"), case.reference),
            temporal_comparison_policy(Some("Escaped"), case.reference),
        ] {
            let errors = dogwood_validation_errors(&policy, &schema);
            assert!(
                errors.is_empty(),
                "Dogwood rejected {} enum ID in policy:\n{policy}\n{errors:#?}",
                case.label
            );
        }
    }
}

#[test]
fn temporal_validation_handles_top_level_and_multisegment_namespaces() {
    for namespace in [None, Some("Outer::Inner")] {
        let schema = enum_schema(namespace, r#"a\"b"#);
        assert!(
            cedar_validation_errors(&cedar_policy(namespace, r#"a\x22b"#), &schema).is_empty(),
            "Cedar cross-reference for namespace {namespace:?}"
        );
        let errors = dogwood_validation_errors(&temporal_policy(namespace, r#"a\x22b"#), &schema);
        assert!(
            errors.is_empty(),
            "Dogwood rejected namespace {namespace:?}: {errors:#?}"
        );
    }
}

#[test]
fn escape_text_and_the_character_it_spells_are_distinct_enum_ids() {
    let schema = r#"
        namespace Escaped {
            entity User;
            entity Doc;
            entity Mode enum ["\u{e}", "\\u{e}"];
            action "Gate" appliesTo {
                principal: [User], resource: [Doc],
                context: { input: { mode: Mode } }
            };
            action "Check" appliesTo {
                principal: [User], resource: [Doc],
                context: { input: { mode: Mode } }
            };
        }
    "#;

    for reference in [r#"\u{0_0_0_e}"#, r#"\\u{e}"#] {
        assert!(
            cedar_validation_errors(&cedar_policy(Some("Escaped"), reference), schema).is_empty(),
            "Cedar cross-reference for {reference:?}"
        );
        let errors =
            dogwood_validation_errors(&temporal_policy(Some("Escaped"), reference), schema);
        assert!(
            errors.is_empty(),
            "Dogwood conflated enum ID {reference:?}: {errors:#?}"
        );
    }
}

#[test]
fn escaped_renderings_are_not_accepted_as_different_enum_ids() {
    let cases = [
        ("quote", r#"a\"b"#, r#"a\\\"b"#),
        ("backslash", r#"a\\b"#, r#"a\\\\b"#),
        (
            "control versus literal escape text",
            r#"\u{e}"#,
            r#"\\u{e}"#,
        ),
        (
            "literal escape text versus control",
            r#"\\u{e}"#,
            r#"\u{e}"#,
        ),
    ];

    for (label, declaration, invalid_reference) in cases {
        let schema = enum_schema(Some("Escaped"), declaration);
        let cedar_errors =
            cedar_validation_errors(&cedar_policy(Some("Escaped"), invalid_reference), &schema);
        assert!(
            !cedar_errors.is_empty(),
            "Cedar conflated {label}: {declaration:?} with {invalid_reference:?}"
        );

        let dogwood_errors = dogwood_validation_errors(
            &temporal_policy(Some("Escaped"), invalid_reference),
            &schema,
        );
        assert!(
            !dogwood_errors.is_empty(),
            "Dogwood conflated {label}: {declaration:?} with {invalid_reference:?}"
        );
    }
}

#[test]
fn invalid_enum_id_diagnostic_uses_canonical_cedar_escaping() {
    let schema = enum_schema(Some("Escaped"), r#"a\"b"#);
    let reference = r#"missing\\id"#;
    let cedar_errors = cedar_validation_errors(&cedar_policy(Some("Escaped"), reference), &schema);
    assert!(
        !cedar_errors.is_empty(),
        "Cedar should reject an undeclared enum ID"
    );

    assert_eq!(
        dogwood_validation_errors(&temporal_policy(Some("Escaped"), reference), &schema),
        vec![
            r#"`Escaped::Mode` is an enum entity type; `"missing\\id"` is not one of its permitted ids ("a\"b")"#
                .to_string()
        ]
    );
}
