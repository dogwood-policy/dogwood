use std::fmt::Debug;
use std::fs;
use std::path::{Path, PathBuf};

use dogwood_language::{DEFAULT_MAX_DEPTH, ParsedPolicySet, ProviderDeclarations, ServiceSchema};
use dogwood_lsp::analysis::analyze;
use dogwood_lsp::frontend::{
    BundleInput, DiagnosticLabel, Finding, FrontendOutcome, MAX_FRONTEND_EXPRESSION_CHAIN_TOKENS,
    MAX_FRONTEND_LINEAR_EXPRESSION_CHAIN, MAX_FRONTEND_NESTING, MAX_FRONTEND_SOURCE_BYTES,
    OperationalLimitExceeded, OperationalLimitKind, PolicyParseInput, Severity, SourceKind,
    parse_event_schema, parse_policy, validate_bundle,
};
use serde::Serialize;

const FIXTURE_ROOT: &str = "tests/fixtures/dogwood/m3";

#[derive(Debug)]
struct Fixture {
    policy: String,
    action_schema: String,
    event_schema: Option<String>,
    providers: Option<String>,
    macros: Option<String>,
}

impl Fixture {
    fn load(name: &str) -> Self {
        let directory = fixture_root().join(name);
        Self {
            policy: read_required(&directory.join("policy.dw")),
            action_schema: read_required(&directory.join("schema.cedarschema")),
            event_schema: read_optional(&directory.join("event.dwschema")),
            providers: read_optional(&directory.join("providers.json")),
            macros: read_optional(&directory.join("macros.dw")),
        }
    }

    fn policy_input(&self) -> PolicyParseInput<'_> {
        PolicyParseInput {
            policy: &self.policy,
            event_schema: self.event_schema.as_deref(),
            providers: self.providers.as_deref(),
            macros: self.macros.as_deref(),
        }
    }

    fn bundle_input(&self) -> BundleInput<'_> {
        BundleInput {
            policy: &self.policy,
            action_schema: &self.action_schema,
            event_schema: self.event_schema.as_deref(),
            providers: self.providers.as_deref(),
            macros: self.macros.as_deref(),
        }
    }

    fn source(&self, kind: SourceKind) -> Option<&str> {
        match kind {
            SourceKind::Policy => Some(&self.policy),
            SourceKind::ActionSchema => Some(&self.action_schema),
            SourceKind::EventSchema => self.event_schema.as_deref(),
            SourceKind::Providers => self.providers.as_deref(),
            SourceKind::Macros => self.macros.as_deref(),
        }
    }
}

fn fixture_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join(FIXTURE_ROOT)
}

fn read_required(path: &Path) -> String {
    fs::read_to_string(path).unwrap_or_else(|error| panic!("read {}: {error}", path.display()))
}

fn read_optional(path: &Path) -> Option<String> {
    path.exists().then(|| read_required(path))
}

fn direct_service_schema(fixture: &Fixture) -> Option<ServiceSchema> {
    if fixture.event_schema.is_none() && fixture.providers.is_none() && fixture.macros.is_none() {
        return Some(ServiceSchema::defaults());
    }

    let mut builder = ServiceSchema::builder();
    if let Some(event_schema) = fixture.event_schema.as_deref() {
        builder = builder.event_schema_str(event_schema);
    }
    if let Some(providers) = fixture.providers.as_deref() {
        builder = builder.providers(ProviderDeclarations::from_json(providers).ok()?);
    }
    if let Some(macros) = fixture.macros.as_deref() {
        builder = builder.macros_str(macros);
    }
    builder.build().ok()
}

fn direct_policy_accepts(fixture: &Fixture) -> bool {
    direct_service_schema(fixture)
        .and_then(|service| ParsedPolicySet::parse(&fixture.policy, &service).ok())
        .is_some()
}

fn adapter_policy_accepts(fixture: &Fixture) -> bool {
    matches!(
        parse_policy(&fixture.policy_input()),
        FrontendOutcome::Report(_)
    )
}

fn assert_deterministic<T>(mut operation: impl FnMut() -> T) -> T
where
    T: Debug + Eq + Serialize,
{
    let first = operation();
    let serialized =
        serde_json::to_vec(&first).expect("frontend outcomes must serialize deterministically");
    for _ in 0..5 {
        let next = operation();
        assert_eq!(next, first);
        assert_eq!(
            serde_json::to_vec(&next).expect("repeated outcome must serialize"),
            serialized
        );
    }
    first
}

fn assert_label_in_source(label: &DiagnosticLabel, source: &str) {
    let end = label
        .start
        .checked_add(label.len)
        .expect("diagnostic label end must not overflow");
    assert!(
        end <= source.len(),
        "{label:?} exceeds {} bytes",
        source.len()
    );
    assert!(source.is_char_boundary(label.start), "{label:?}");
    assert!(source.is_char_boundary(end), "{label:?}");
}

fn assert_finding_ranges(finding: &Finding, fixture: &Fixture) {
    if let Some(source_kind) = finding.source_kind {
        let source = fixture
            .source(source_kind)
            .unwrap_or_else(|| panic!("fixture has no {source_kind:?} source"));
        for label in &finding.labels {
            assert_label_in_source(label, source);
        }
    } else {
        assert!(
            finding.labels.is_empty(),
            "labeled findings need a known source for range validation"
        );
    }
    assert_eq!(finding.spanned, !finding.labels.is_empty());
}

fn policy_with_body(body: &str) -> String {
    format!("permit (principal, action, resource) when {{ {body} }};")
}

/// Nine `||`-separated groups of 19 `true`s joined by `&&`, after
/// `leading_bangs` `!`s: `511 + leading_bangs` generic tokens, yet under 30
/// levels deep, so Dogwood accepts it.
fn wide_boolean(leading_bangs: usize) -> String {
    let group = vec!["true"; 19].join(" && ");
    format!(
        "{}{}",
        "!".repeat(leading_bangs),
        vec![group; 9].join(" || ")
    )
}

fn assert_operational_limit<R>(outcome: FrontendOutcome<R>, expected: OperationalLimitExceeded) {
    let FrontendOutcome::OperationalLimit(actual) = outcome else {
        panic!("expected operational limit");
    };
    assert_eq!(actual, expected);
}

fn assert_lexical_fallback(source: &str) {
    let first = analyze(source).expect("tolerant lexical analysis must complete");
    let second = analyze(source).expect("repeated tolerant lexical analysis must complete");
    assert_eq!(first, second);
    for token in &first {
        assert!(token.span.start() < token.span.end());
        assert!(source.is_char_boundary(token.span.start()));
        assert!(source.is_char_boundary(token.span.end()));
    }
    assert!(
        first
            .windows(2)
            .all(|pair| pair[0].span.end() <= pair[1].span.start())
    );
}

#[test]
fn standalone_policy_acceptance_matches_workspace_frontend() {
    let cases = [
        ("all-optional-valid", true),
        ("custom-event-valid", true),
        ("default-valid", true),
        ("event-schema-truncated", false),
        ("macro-invocation-failure", false),
        ("macro-source-failure", false),
        ("macro-valid", true),
        ("malformed-policy-missing-brace", false),
        ("malformed-policy-unclosed-string", false),
        ("parse-multiple-related", false),
        ("provider-type-failure", true),
        ("provider-valid", true),
        ("schema-aware-validation-failure", true),
        ("unicode-truncation", false),
        ("validation-warning", true),
    ];

    for (name, expected) in cases {
        let fixture = Fixture::load(name);
        assert_eq!(
            direct_policy_accepts(&fixture),
            expected,
            "unexpected Dogwood frontend result for {name}"
        );
        assert_eq!(
            adapter_policy_accepts(&fixture),
            expected,
            "adapter disagrees for {name}"
        );
    }
}

#[test]
fn standalone_event_schema_acceptance_matches_workspace_frontend() {
    for (name, expected) in [
        ("all-optional-valid", true),
        ("custom-event-valid", true),
        ("event-schema-truncated", false),
    ] {
        let fixture = Fixture::load(name);
        let source = fixture
            .event_schema
            .as_deref()
            .expect("event-schema fixture must provide event.dwschema");
        let direct = ServiceSchema::builder()
            .event_schema_str(source)
            .build()
            .is_ok();
        let adapter = matches!(parse_event_schema(source), FrontendOutcome::Report(_));
        assert_eq!(direct, expected, "unexpected Dogwood result for {name}");
        assert_eq!(adapter, expected, "adapter disagrees for {name}");
    }
}

#[test]
fn representative_owned_outcomes_and_serialization_are_deterministic() {
    for name in [
        "default-valid",
        "validation-warning",
        "provider-type-failure",
        "all-optional-valid",
    ] {
        let fixture = Fixture::load(name);
        assert_deterministic(|| validate_bundle(&fixture.bundle_input()));
    }

    for name in [
        "parse-multiple-related",
        "unicode-truncation",
        "macro-source-failure",
    ] {
        let fixture = Fixture::load(name);
        assert_deterministic(|| parse_policy(&fixture.policy_input()));
    }

    for name in ["custom-event-valid", "event-schema-truncated"] {
        let fixture = Fixture::load(name);
        let source = fixture.event_schema.as_deref().expect("event schema");
        assert_deterministic(|| parse_event_schema(source));
    }

    let deep = policy_with_body(&format!(
        "{}true",
        "!".repeat(MAX_FRONTEND_LINEAR_EXPRESSION_CHAIN + 1)
    ));
    let input = PolicyParseInput {
        policy: &deep,
        event_schema: None,
        providers: None,
        macros: None,
    };
    assert_deterministic(|| parse_policy(&input));
}

#[test]
fn findings_preserve_order_severity_sources_and_exact_byte_ranges() {
    let related_fixture = Fixture::load("parse-multiple-related");
    let FrontendOutcome::Fatal(related) = parse_policy(&related_fixture.policy_input()) else {
        panic!("fixture must produce fatal related findings");
    };
    assert_eq!(related.diagnostic.severity, Severity::Error);
    assert_eq!(related.diagnostic.source_kind, Some(SourceKind::Policy));
    assert_eq!(
        related.diagnostic.labels,
        vec![DiagnosticLabel {
            start: 8,
            len: 19,
            message: Some(
                "`?other` is not a recognized template slot; did you mean `?principal`?".to_owned()
            ),
        }]
    );
    assert_eq!(related.related.len(), 1);
    assert_eq!(related.related[0].severity, Severity::Error);
    assert_eq!(related.related[0].source_kind, Some(SourceKind::Policy));
    assert_eq!(
        related.related[0].labels,
        vec![DiagnosticLabel {
            start: 75,
            len: 16,
            message: Some(
                "`?foo` is not a recognized template slot; did you mean `?resource`?".to_owned()
            ),
        }]
    );
    assert_finding_ranges(&related.diagnostic, &related_fixture);
    for finding in &related.related {
        assert_finding_ranges(finding, &related_fixture);
    }

    let warning_fixture = Fixture::load("validation-warning");
    let FrontendOutcome::Report(warning_report) = validate_bundle(&warning_fixture.bundle_input())
    else {
        panic!("warning fixture must reach validation");
    };
    assert!(warning_report.errors.is_empty());
    assert_eq!(warning_report.warnings.len(), 1);
    assert_eq!(warning_report.warnings[0].severity, Severity::Warning);
    assert_eq!(
        warning_report.warnings[0].source_kind,
        Some(SourceKind::Policy)
    );
    assert_eq!(
        warning_report.warnings[0].labels[0],
        DiagnosticLabel {
            start: 167,
            len: 11,
            message: None,
        }
    );
    assert_finding_ranges(&warning_report.warnings[0], &warning_fixture);

    let provider_fixture = Fixture::load("provider-type-failure");
    let FrontendOutcome::Report(provider_report) =
        validate_bundle(&provider_fixture.bundle_input())
    else {
        panic!("provider type failure must be a validation report");
    };
    assert_eq!(provider_report.errors.len(), 1);
    assert_eq!(provider_report.errors[0].severity, Severity::Error);
    assert_eq!(provider_report.errors[0].code.as_deref(), Some("extension"));
    assert_eq!(
        provider_report.errors[0].source_kind,
        Some(SourceKind::Policy)
    );
    assert_eq!(
        provider_report.errors[0].labels[0].start, 80,
        "provider finding order/range changed"
    );
    assert_eq!(provider_report.errors[0].labels[0].len, 44);
    assert_finding_ranges(&provider_report.errors[0], &provider_fixture);

    let unicode_fixture = Fixture::load("unicode-truncation");
    let FrontendOutcome::Fatal(unicode) = parse_policy(&unicode_fixture.policy_input()) else {
        panic!("Unicode truncation must be fatal");
    };
    assert_eq!(unicode.diagnostic.source_kind, Some(SourceKind::Policy));
    assert_eq!(unicode.diagnostic.labels.len(), 1);
    // Pinned `dogwood validate --format json` reports this byte offset. It is
    // intentionally not derived from the adapter or from character counts.
    assert_eq!(unicode.diagnostic.labels[0].start, 121);
    assert_eq!(unicode.diagnostic.labels[0].len, 1);
    assert_finding_ranges(&unicode.diagnostic, &unicode_fixture);

    let event_fixture = Fixture::load("event-schema-truncated");
    let event_source = event_fixture.event_schema.as_deref().expect("event schema");
    let FrontendOutcome::Fatal(event) = parse_event_schema(event_source) else {
        panic!("truncated event schema must be fatal");
    };
    assert_eq!(event.diagnostic.source_kind, Some(SourceKind::EventSchema));
    assert!(!event.diagnostic.spanned);
    assert!(event.diagnostic.labels.is_empty());

    let malformed_provider = PolicyParseInput {
        policy: &Fixture::load("default-valid").policy,
        event_schema: None,
        providers: Some("{"),
        macros: None,
    };
    let FrontendOutcome::Fatal(provider) = parse_policy(&malformed_provider) else {
        panic!("malformed provider JSON must be fatal");
    };
    assert_eq!(provider.diagnostic.source_kind, Some(SourceKind::Providers));
    assert!(!provider.diagnostic.spanned);
    assert!(provider.diagnostic.labels.is_empty());

    let macro_fixture = Fixture::load("macro-source-failure");
    let FrontendOutcome::Fatal(macros) = parse_policy(&macro_fixture.policy_input()) else {
        panic!("malformed macro source must be fatal");
    };
    assert_eq!(macros.diagnostic.source_kind, Some(SourceKind::Macros));
    assert_eq!(macros.diagnostic.labels[0].start, 64);
    assert_eq!(macros.diagnostic.labels[0].len, 1);
    assert_finding_ranges(&macros.diagnostic, &macro_fixture);
}

#[test]
fn zero_width_diagnostic_labels_round_trip_without_losing_spanned_state() {
    let source = "cafe\u{96ea}";
    let finding = Finding {
        severity: Severity::Advice,
        code: Some("insertion".to_owned()),
        message: "insert here".to_owned(),
        labels: vec![DiagnosticLabel {
            start: source.len(),
            len: 0,
            message: None,
        }],
        help: None,
        spanned: true,
        source_kind: Some(SourceKind::Policy),
    };

    assert_label_in_source(&finding.labels[0], source);
    let encoded = serde_json::to_vec(&finding).expect("zero-width finding must serialize");
    let decoded: Finding =
        serde_json::from_slice(&encoded).expect("zero-width finding must deserialize");
    assert_eq!(decoded, finding);
    assert!(decoded.spanned);
    assert_eq!(decoded.labels[0].len, 0);
}

#[test]
fn malformed_policy_fixtures_retain_deterministic_lexical_fallback() {
    for name in [
        "malformed-policy-missing-brace",
        "malformed-policy-unclosed-string",
        "parse-multiple-related",
        "unicode-truncation",
    ] {
        let fixture = Fixture::load(name);
        assert!(
            matches!(
                parse_policy(&fixture.policy_input()),
                FrontendOutcome::Fatal(_)
            ),
            "{name} must fail strict parsing"
        );
        assert_lexical_fallback(&fixture.policy);
    }

    for name in [
        "event-schema-truncated",
        "macro-invocation-failure",
        "macro-source-failure",
    ] {
        let fixture = Fixture::load(name);
        assert_lexical_fallback(&fixture.policy);
        if let Some(macros) = fixture.macros.as_deref() {
            assert_lexical_fallback(macros);
        }
    }
}

#[test]
fn source_size_and_structural_nesting_boundaries_preflight_deep_inputs() {
    let exact_size = " ".repeat(MAX_FRONTEND_SOURCE_BYTES);
    let exact_size_input = PolicyParseInput {
        policy: &exact_size,
        event_schema: None,
        providers: None,
        macros: None,
    };
    assert!(matches!(
        parse_policy(&exact_size_input),
        FrontendOutcome::Report(_)
    ));

    let over_size = " ".repeat(MAX_FRONTEND_SOURCE_BYTES + 1);
    let over_size_input = PolicyParseInput {
        policy: &over_size,
        event_schema: None,
        providers: None,
        macros: None,
    };
    assert_operational_limit(
        parse_policy(&over_size_input),
        OperationalLimitExceeded {
            source_kind: SourceKind::Policy,
            kind: OperationalLimitKind::SourceBytes,
            limit: MAX_FRONTEND_SOURCE_BYTES,
            observed: MAX_FRONTEND_SOURCE_BYTES + 1,
        },
    );

    let exact_nesting = policy_with_body(&format!(
        "{}true{}",
        "(".repeat(MAX_FRONTEND_NESTING - 1),
        ")".repeat(MAX_FRONTEND_NESTING - 1)
    ));
    let exact_nesting_input = PolicyParseInput {
        policy: &exact_nesting,
        event_schema: None,
        providers: None,
        macros: None,
    };
    assert!(matches!(
        parse_policy(&exact_nesting_input),
        FrontendOutcome::Report(_)
    ));

    for depth in [MAX_FRONTEND_NESTING, MAX_FRONTEND_NESTING + 256] {
        let deep = policy_with_body(&format!("{}true{}", "(".repeat(depth), ")".repeat(depth)));
        let input = PolicyParseInput {
            policy: &deep,
            event_schema: None,
            providers: None,
            macros: None,
        };
        assert_operational_limit(
            parse_policy(&input),
            OperationalLimitExceeded {
                source_kind: SourceKind::Policy,
                kind: OperationalLimitKind::StructuralNesting,
                limit: MAX_FRONTEND_NESTING,
                observed: MAX_FRONTEND_NESTING + 1,
            },
        );
    }

    let exact_event_nesting = "(".repeat(MAX_FRONTEND_NESTING);
    assert!(!matches!(
        parse_event_schema(&exact_event_nesting),
        FrontendOutcome::OperationalLimit(_)
    ));
    let over_event_nesting = "(".repeat(MAX_FRONTEND_NESTING + 1);
    assert_operational_limit(
        parse_event_schema(&over_event_nesting),
        OperationalLimitExceeded {
            source_kind: SourceKind::EventSchema,
            kind: OperationalLimitKind::StructuralNesting,
            limit: MAX_FRONTEND_NESTING,
            observed: MAX_FRONTEND_NESTING + 1,
        },
    );
}

#[test]
fn expression_chain_boundaries_cover_unary_member_index_and_postfix_shapes() {
    let exact_bodies = [
        format!("{}true", "!".repeat(MAX_FRONTEND_LINEAR_EXPRESSION_CHAIN)),
        format!(
            "context{}",
            ".field".repeat(MAX_FRONTEND_LINEAR_EXPRESSION_CHAIN)
        ),
        format!(
            "context{}",
            r#"["field"]"#.repeat(MAX_FRONTEND_LINEAR_EXPRESSION_CHAIN)
        ),
        format!(
            "context{}",
            ".method()".repeat(MAX_FRONTEND_LINEAR_EXPRESSION_CHAIN)
        ),
    ];
    for body in exact_bodies {
        let policy = policy_with_body(&body);
        let input = PolicyParseInput {
            policy: &policy,
            event_schema: None,
            providers: None,
            macros: None,
        };
        assert!(
            matches!(parse_policy(&input), FrontendOutcome::Report(_)),
            "exact linear-chain boundary must reach Dogwood: {body}"
        );
    }

    let over_bodies = [
        format!(
            "{}true",
            "!".repeat(MAX_FRONTEND_LINEAR_EXPRESSION_CHAIN + 1)
        ),
        format!(
            "context{}",
            ".field".repeat(MAX_FRONTEND_LINEAR_EXPRESSION_CHAIN + 1)
        ),
        format!(
            "context{}",
            r#"["field"]"#.repeat(MAX_FRONTEND_LINEAR_EXPRESSION_CHAIN + 1)
        ),
        format!(
            "context{}",
            ".method()".repeat(MAX_FRONTEND_LINEAR_EXPRESSION_CHAIN + 1)
        ),
    ];
    for body in over_bodies {
        let policy = policy_with_body(&body);
        let input = PolicyParseInput {
            policy: &policy,
            event_schema: None,
            providers: None,
            macros: None,
        };
        assert_operational_limit(
            parse_policy(&input),
            OperationalLimitExceeded {
                source_kind: SourceKind::Policy,
                kind: OperationalLimitKind::ExpressionChain,
                limit: MAX_FRONTEND_LINEAR_EXPRESSION_CHAIN,
                observed: MAX_FRONTEND_LINEAR_EXPRESSION_CHAIN + 1,
            },
        );
    }

    let exact_generic = policy_with_body(&wide_boolean(1));
    let exact_generic_input = PolicyParseInput {
        policy: &exact_generic,
        event_schema: None,
        providers: None,
        macros: None,
    };
    assert!(matches!(
        parse_policy(&exact_generic_input),
        FrontendOutcome::Report(_)
    ));

    let over_generic = policy_with_body(&wide_boolean(2));
    let over_generic_input = PolicyParseInput {
        policy: &over_generic,
        event_schema: None,
        providers: None,
        macros: None,
    };
    assert_operational_limit(
        parse_policy(&over_generic_input),
        OperationalLimitExceeded {
            source_kind: SourceKind::Policy,
            kind: OperationalLimitKind::ExpressionChain,
            limit: MAX_FRONTEND_EXPRESSION_CHAIN_TOKENS,
            observed: MAX_FRONTEND_EXPRESSION_CHAIN_TOKENS + 1,
        },
    );
}

#[test]
fn and_chain_boundary_is_dogwoods_depth_limit() {
    let chain = |terms| policy_with_body(&vec!["true"; terms].join(" && "));
    let exact = chain(DEFAULT_MAX_DEPTH);
    let exact_input = PolicyParseInput {
        policy: &exact,
        event_schema: None,
        providers: None,
        macros: None,
    };
    assert!(matches!(
        parse_policy(&exact_input),
        FrontendOutcome::Report(_)
    ));

    let over = chain(DEFAULT_MAX_DEPTH + 1);
    let over_input = PolicyParseInput {
        policy: &over,
        event_schema: None,
        providers: None,
        macros: None,
    };
    let FrontendOutcome::Fatal(fatal) = parse_policy(&over_input) else {
        panic!("a chain past Dogwood's depth limit is a parse error");
    };
    let messages: Vec<_> = std::iter::once(&*fatal.diagnostic)
        .chain(&fatal.related)
        .map(|finding| finding.message.as_str())
        .collect();
    assert!(
        messages
            .iter()
            .any(|message| message.contains("expression nested deeper than the limit of 32")),
        "{messages:?}"
    );
}

#[test]
fn delimiter_scanning_ignores_comments_strings_and_escaped_quotes() {
    let ignored = "([{".repeat(MAX_FRONTEND_NESTING + 1);
    let policy = format!(
        "permit (principal, action, resource) when {{ \
         \"escaped \\\" {ignored}\" == \"escaped \\\" {ignored}\" }}; \
         // {ignored}\n"
    );
    let input = PolicyParseInput {
        policy: &policy,
        event_schema: None,
        providers: None,
        macros: None,
    };

    assert!(matches!(parse_policy(&input), FrontendOutcome::Report(_)));
    assert_lexical_fallback(&policy);
}
