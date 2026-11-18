#[path = "support/dogwood_cli.rs"]
mod dogwood_cli;

use std::fs;
use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicU64, Ordering};

use dogwood_cli::ValidateInvocation;
use dogwood_lsp::diagnostics::{BundleDocuments, SourceDocument, project_frontend_outcome};
use dogwood_lsp::frontend::{
    BundleInput, DiagnosticLabel, Finding, FrontendOutcome, Severity, validate_bundle,
};
use dogwood_lsp::project::path_to_file_uri;
use lsp_types::{DiagnosticSeverity, NumberOrString, Position, Range};
use serde::Deserialize;

const ACTION_ONLY_POLICY: &str =
    include_str!("fixtures/dogwood/m3/schema-aware-validation-failure/policy.dw");
const ACTION_ONLY_SCHEMA: &str =
    include_str!("fixtures/dogwood/m3/schema-aware-validation-failure/schema.cedarschema");
const ALL_OPTIONAL_POLICY: &str = include_str!("fixtures/dogwood/m3/all-optional-valid/policy.dw");
const ALL_OPTIONAL_SCHEMA: &str =
    include_str!("fixtures/dogwood/m3/all-optional-valid/schema.cedarschema");
const ALL_OPTIONAL_EVENTS: &str =
    include_str!("fixtures/dogwood/m3/all-optional-valid/event.dwschema");
const ALL_OPTIONAL_PROVIDERS: &str =
    include_str!("fixtures/dogwood/m3/all-optional-valid/providers.json");
const ALL_OPTIONAL_MACROS: &str = include_str!("fixtures/dogwood/m3/all-optional-valid/macros.dw");

static TEMP_SEQUENCE: AtomicU64 = AtomicU64::new(0);

#[derive(Debug, Deserialize)]
#[serde(deny_unknown_fields)]
struct CliReport {
    passed: bool,
    passed_without_warnings: bool,
    errors: Vec<CliFinding>,
    warnings: Vec<CliFinding>,
}

#[derive(Debug, Deserialize)]
#[serde(deny_unknown_fields)]
struct CliFinding {
    severity: Severity,
    code: Option<String>,
    message: String,
    #[serde(default)]
    labels: Vec<DiagnosticLabel>,
    help: Option<String>,
    spanned: bool,
}

struct Fixture {
    root: PathBuf,
    policy_path: PathBuf,
    schema_path: PathBuf,
    event_path: Option<PathBuf>,
    providers_path: Option<PathBuf>,
    macros_path: Option<PathBuf>,
    policy: String,
    schema: String,
    event: Option<String>,
    providers: Option<String>,
    macros: Option<String>,
}

impl Fixture {
    fn action_only() -> Self {
        Self::create(
            ACTION_ONLY_POLICY.to_owned(),
            ACTION_ONLY_SCHEMA.to_owned(),
            None,
            None,
            None,
        )
    }

    fn all_optional_invalid() -> Self {
        let policy =
            ALL_OPTIONAL_POLICY.replacen("context.input.document", "context.input.missing", 1);
        Self::create(
            policy,
            ALL_OPTIONAL_SCHEMA.to_owned(),
            Some(ALL_OPTIONAL_EVENTS.to_owned()),
            Some(ALL_OPTIONAL_PROVIDERS.to_owned()),
            Some(ALL_OPTIONAL_MACROS.to_owned()),
        )
    }

    fn create(
        policy: String,
        schema: String,
        event: Option<String>,
        providers: Option<String>,
        macros: Option<String>,
    ) -> Self {
        let root = std::env::temp_dir().join(format!(
            "dogwood-lsp-m4-differential-{}-{}",
            std::process::id(),
            TEMP_SEQUENCE.fetch_add(1, Ordering::Relaxed)
        ));
        fs::create_dir_all(&root).unwrap();
        let policy_path = write(&root, "policy.dw", &policy);
        let schema_path = write(&root, "actions.cedarschema", &schema);
        let event_path = event
            .as_deref()
            .map(|source| write(&root, "events.dwschema", source));
        let providers_path = providers
            .as_deref()
            .map(|source| write(&root, "providers.json", source));
        let macros_path = macros
            .as_deref()
            .map(|source| write(&root, "macros.dw", source));
        Self {
            root,
            policy_path,
            schema_path,
            event_path,
            providers_path,
            macros_path,
            policy,
            schema,
            event,
            providers,
            macros,
        }
    }

    fn input(&self) -> BundleInput<'_> {
        BundleInput {
            policy: &self.policy,
            action_schema: &self.schema,
            event_schema: self.event.as_deref(),
            providers: self.providers.as_deref(),
            macros: self.macros.as_deref(),
        }
    }

    fn invocation<'a>(&'a self, name: &'a str) -> ValidateInvocation<'a> {
        ValidateInvocation {
            fixture: name,
            policy: &self.policy_path,
            policy_schema: &self.schema_path,
            event_schema: self.event_path.as_deref(),
            providers: self.providers_path.as_deref(),
            macros: self.macros_path.as_deref(),
        }
    }
}

impl Drop for Fixture {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.root);
    }
}

#[test]
fn emitted_action_only_findings_match_live_cli_before_and_after_utf16_projection() {
    compare_live_projection("m4-action-only", Fixture::action_only());
}

#[test]
fn emitted_all_optional_findings_match_live_cli_before_and_after_utf16_projection() {
    compare_live_projection("m4-all-optional", Fixture::all_optional_invalid());
}

fn compare_live_projection(name: &str, fixture: Fixture) {
    let oracle = dogwood_cli::validate(&fixture.invocation(name)).unwrap();
    assert_eq!(oracle.exit_code, 2, "{name}: expected invalid fixture");
    let cli: CliReport = serde_json::from_slice(&oracle.stdout)
        .unwrap_or_else(|error| panic!("{name}: invalid CLI report JSON: {error}"));
    assert!(!cli.passed);
    assert!(!cli.passed_without_warnings);

    let local = validate_bundle(&fixture.input());
    let FrontendOutcome::Report(local_report) = &local else {
        panic!("{name}: local frontend did not produce a validation report: {local:?}");
    };
    compare_raw_findings(name, &cli.errors, &local_report.errors);
    compare_raw_findings(name, &cli.warnings, &local_report.warnings);

    let policy_uri = path_to_file_uri(&fixture.policy_path).unwrap();
    let schema_uri = path_to_file_uri(&fixture.schema_path).unwrap();
    let event_uri = fixture
        .event_path
        .as_deref()
        .map(path_to_file_uri)
        .transpose()
        .unwrap();
    let providers_uri = fixture
        .providers_path
        .as_deref()
        .map(path_to_file_uri)
        .transpose()
        .unwrap();
    let macros_uri = fixture
        .macros_path
        .as_deref()
        .map(path_to_file_uri)
        .transpose()
        .unwrap();
    let documents = BundleDocuments {
        policy: SourceDocument {
            uri: &policy_uri,
            text: &fixture.policy,
        },
        action_schema: SourceDocument {
            uri: &schema_uri,
            text: &fixture.schema,
        },
        event_schema: fixture
            .event
            .as_deref()
            .zip(event_uri.as_ref())
            .map(|(text, uri)| SourceDocument { uri, text }),
        providers: fixture
            .providers
            .as_deref()
            .zip(providers_uri.as_ref())
            .map(|(text, uri)| SourceDocument { uri, text }),
        macros: fixture
            .macros
            .as_deref()
            .zip(macros_uri.as_ref())
            .map(|(text, uri)| SourceDocument { uri, text }),
    };
    let published = project_frontend_outcome(11, documents, local);
    let cli_findings: Vec<_> = cli.errors.iter().chain(&cli.warnings).collect();
    assert_eq!(published.diagnostics.len(), cli_findings.len(), "{name}");

    for (index, (diagnostic, finding)) in published.diagnostics.iter().zip(cli_findings).enumerate()
    {
        assert_eq!(
            diagnostic.message, finding.message,
            "{name} finding {index}"
        );
        assert_eq!(
            diagnostic.severity,
            Some(match finding.severity {
                Severity::Error => DiagnosticSeverity::ERROR,
                Severity::Warning => DiagnosticSeverity::WARNING,
                Severity::Advice => DiagnosticSeverity::INFORMATION,
            }),
            "{name} finding {index}"
        );
        assert_eq!(
            diagnostic.code,
            finding.code.clone().map(NumberOrString::String),
            "{name} finding {index}"
        );
        assert_eq!(
            diagnostic.source.as_deref(),
            Some("dogwood"),
            "{name} finding {index}"
        );
        let expected_range = finding.labels.first().map_or_else(zero_range, |label| {
            independent_range(&fixture.policy, label.start, label.len)
        });
        assert_eq!(diagnostic.range, expected_range, "{name} finding {index}");

        let related = diagnostic
            .related_information
            .as_deref()
            .unwrap_or_default();
        assert_eq!(
            related.len(),
            finding.labels.len().saturating_sub(1),
            "{name} finding {index}"
        );
        for (related_index, (actual, label)) in related
            .iter()
            .zip(finding.labels.iter().skip(1))
            .enumerate()
        {
            assert_eq!(actual.location.uri, policy_uri);
            assert_eq!(
                actual.location.range,
                independent_range(&fixture.policy, label.start, label.len),
                "{name} finding {index} related label {related_index}"
            );
            assert_eq!(
                actual.message,
                label.message.as_deref().unwrap_or(&finding.message)
            );
        }
    }
}

fn compare_raw_findings(name: &str, cli: &[CliFinding], local: &[Finding]) {
    assert_eq!(cli.len(), local.len(), "{name}: finding count");
    for (index, (cli, local)) in cli.iter().zip(local).enumerate() {
        assert_eq!(local.severity, cli.severity, "{name} finding {index}");
        assert_eq!(local.code, cli.code, "{name} finding {index}");
        assert_eq!(local.message, cli.message, "{name} finding {index}");
        assert_eq!(local.labels, cli.labels, "{name} finding {index}");
        assert_eq!(local.help, cli.help, "{name} finding {index}");
        assert_eq!(local.spanned, cli.spanned, "{name} finding {index}");
    }
}

fn independent_range(source: &str, start: usize, len: usize) -> Range {
    let end = start
        .checked_add(len)
        .expect("fixture span should not overflow");
    Range::new(
        independent_position(source, start),
        independent_position(source, end),
    )
}

fn independent_position(source: &str, target: usize) -> Position {
    assert!(target <= source.len());
    assert!(source.is_char_boundary(target));
    let mut offset = 0;
    let mut line = 0_u32;
    let mut column = 0_u32;

    while offset < target {
        let tail = &source[offset..];
        if tail.starts_with("\r\n") {
            assert_ne!(target, offset + 1, "span points inside CRLF");
            offset += 2;
            line += 1;
            column = 0;
            continue;
        }
        let character = tail.chars().next().unwrap();
        offset += character.len_utf8();
        if matches!(character, '\r' | '\n') {
            line += 1;
            column = 0;
        } else {
            column += u32::try_from(character.len_utf16()).unwrap();
        }
    }
    assert_eq!(offset, target);
    Position::new(line, column)
}

fn zero_range() -> Range {
    Range::new(Position::new(0, 0), Position::new(0, 0))
}

fn write(root: &Path, name: &str, source: &str) -> PathBuf {
    let path = root.join(name);
    fs::write(&path, source).unwrap();
    path
}
