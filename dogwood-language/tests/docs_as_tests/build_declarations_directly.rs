//! Constructing [`ProviderDeclarations`] **directly** with struct literals,
//! rather than deserializing them from JSON.
//!
//! Every type in the declarations tree — [`ProviderDeclarations`],
//! [`ProviderDecl`], [`ParamType`], [`Implementation`], and [`MethodDecl`] — is
//! re-exported at the crate root with public fields and no `#[non_exhaustive]`,
//! so a caller that computes declarations in code (a control plane wiring up
//! providers programmatically, say) can build them by hand and hand them to
//! [`ServiceSchema`]. This test builds the `Risk::Score` provider from corpus
//! case `0012` — including its `above(decimal) -> bool` output **method**, which
//! exercises [`MethodDecl`] — entirely in code, then replays that case's trace
//! and asserts the verdicts match the JSON-backed corpus run byte-for-byte.

use std::path::Path;

use dogwood_language::{
    Implementation, LoweredPolicySet, MethodDecl, ParamType, PolicySchema, ProviderDecl,
    ProviderDeclarations, ServiceSchema, replay_log,
};

/// A leaf [`ParamType`] (`string` / `integer` / `decimal` / `bool`) — no
/// nested fields, items, or required list.
fn leaf(param_type: &str) -> ParamType {
    ParamType {
        param_type: param_type.to_string(),
        ..Default::default()
    }
}

/// The `Risk::Score` declarations, built by hand — the in-code equivalent of
/// corpus `0012`'s `providers.json`, with `risk.rhai` supplied inline.
fn declarations() -> ProviderDeclarations {
    // outputType: { score: decimal } (required)
    let output_type = ParamType {
        param_type: "record".to_string(),
        fields: [("score".to_string(), leaf("decimal"))]
            .into_iter()
            .collect(),
        required: vec!["score".to_string()],
        ..Default::default()
    };

    // availableMethods: { above: (decimal) -> bool }
    let above = MethodDecl {
        argument_types: vec![leaf("decimal")],
        output_type: leaf("bool"),
        input_type: None,
    };

    let script = r#"
        fn evaluate(text) {
            let score = if text == "safe" {
                parse_decimal("0.10")
            } else if text == "bad" {
                parse_decimal("0.90")
            } else {
                parse_decimal("0.50")
            };
            #{ score: score }
        }
        fn above(o, threshold) { o.score > threshold }
    "#;

    let decl = ProviderDecl {
        argument_types: vec![leaf("string")],
        output_type,
        methods: [("above".to_string(), above)].into_iter().collect(),
        implementation: Some(Implementation::Rhai {
            script: Some(script.to_string()),
            script_file: None,
        }),
    };

    ProviderDeclarations {
        available: [("Risk::Score".to_string(), decl)].into_iter().collect(),
        ..Default::default()
    }
}

#[test]
fn hand_built_declarations_match_the_json_backed_corpus_run() {
    let dir = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("tests/passing/provider_only/corpus/0012_n_arg_score_above_method");
    let policy = std::fs::read_to_string(dir.join("policy_1.dw")).expect("policy");
    let schema = std::fs::read_to_string(dir.join("schema.cedarschema")).unwrap_or_else(|_| {
        std::fs::read_to_string(
            Path::new(env!("CARGO_MANIFEST_DIR"))
                .join("tests/passing/provider_only/shared_schema.cedarschema"),
        )
        .expect("shared schema")
    });
    let trace = std::fs::read_to_string(dir.join("trace_1.log")).expect("trace");
    let expected = std::fs::read_to_string(dir.join("expected_1.out")).expect("expected");
    let event_schema = std::fs::read_to_string(
        Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/request_response.dwschema"),
    )
    .expect("event schema");

    // The service schema carries the *hand-built* declarations — no JSON.
    let service = ServiceSchema::builder()
        .event_schema_str(&event_schema)
        .providers(declarations())
        .build()
        .expect("service schema");
    let policy_schema = PolicySchema::from_cedarschema_str(&schema).expect("policy schema");
    let policies = LoweredPolicySet::from_str(&policy, &service, &policy_schema).expect("lower");

    let got = replay_log(policies, &trace).expect("replay");

    let norm = |s: &str| {
        s.lines()
            .map(str::trim)
            .filter(|l| !l.is_empty())
            .map(str::to_string)
            .collect::<Vec<_>>()
    };
    assert_eq!(
        norm(&got),
        norm(&expected),
        "hand-built declarations must produce the same verdicts as the JSON-backed corpus case"
    );
}

/// Declarations built in code skip `ProviderDeclarations::from_json`, so
/// `ServiceSchemaBuilder::build` runs the same checks. An unknown `paramType`
/// that involves no entity type is the deprecated `String` fallback and is
/// accepted, as it is from JSON.
#[test]
fn hand_built_unknown_param_type_falls_back_to_string() {
    let mut decls = declarations();
    decls
        .available
        .get_mut("Risk::Score")
        .unwrap()
        .output_type
        .fields
        .insert("level".to_string(), leaf("strng"));
    ServiceSchema::builder()
        .providers(decls)
        .build()
        .expect("an unknown paramType without an entity type is accepted");
}

/// A hand-built unknown `paramType` carrying an `entityType` is rejected by
/// the builder: falling back to `String` would hide the enum.
#[test]
fn hand_built_unknown_param_type_with_entity_type_is_rejected() {
    let mut decls = declarations();
    decls
        .available
        .get_mut("Risk::Score")
        .unwrap()
        .output_type
        .fields
        .insert(
            "level".to_string(),
            ParamType {
                entity_type: Some("Risk::Level".to_string()),
                ..leaf("entiy")
            },
        );
    let err = ServiceSchema::builder()
        .providers(decls)
        .build()
        .expect_err("an unknown paramType with an entityType must be rejected");
    assert!(
        err.to_string()
            .contains("provider `Risk::Score` outputType.level: unknown paramType `entiy`"),
        "got: {err}"
    );
}

/// An enum-typed output built in code: `entityTypes` declares the enum, the
/// field references it, and the builder accepts it.
#[test]
fn hand_built_enum_entity_declaration_is_accepted() {
    let mut decls = declarations();
    decls.entity_type_decls.insert(
        "Risk::Level".to_string(),
        dogwood_language::EntityTypeDecl {
            values: vec!["LOW".to_string(), "HIGH".to_string()],
            annotations: Default::default(),
        },
    );
    decls
        .available
        .get_mut("Risk::Score")
        .unwrap()
        .output_type
        .fields
        .insert(
            "level".to_string(),
            ParamType {
                param_type: "entity".to_string(),
                entity_type: Some("Risk::Level".to_string()),
                ..Default::default()
            },
        );
    ServiceSchema::builder()
        .providers(decls)
        .build()
        .expect("a well-formed enum declaration builds");
}
