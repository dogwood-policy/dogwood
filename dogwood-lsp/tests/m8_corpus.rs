// dogwood-lsp handles Unix paths and file URIs only, so its tests run on Unix.
#![cfg(unix)]

#[path = "support/dogwood_cli.rs"]
mod dogwood_cli;
#[path = "support/temp_root.rs"]
mod temp_root;

use std::collections::BTreeSet;
use std::fs;
use std::path::{Path, PathBuf};
use std::str::FromStr;
use std::sync::atomic::{AtomicU64, Ordering};

use dogwood_cli::{OracleOutput, ValidateInvocation};
use dogwood_lsp::analysis::{
    Token, analyze_event_schema, analyze_lexical, analyze_with_input, validate_tokens,
};
use dogwood_lsp::diagnostics::{
    BundleDocuments, SourceDocument, byte_range_to_utf16, project_frontend_outcome,
};
use dogwood_lsp::frontend::{
    BundleInput, DiagnosticLabel, Finding, FrontendOutcome, Severity, SourceKind, ValidationReport,
    validate_bundle,
};
use dogwood_lsp::frontend_event_schema;
use dogwood_lsp::frontend_semantic::{self, SemanticInput};
use dogwood_lsp::legend::{TOKEN_MODIFIERS, TOKEN_TYPES};
use lsp_types::{Position, Uri};
use serde::Deserialize;
use sha2::{Digest, Sha256};

const MANIFEST_SOURCE: &str = include_str!("fixtures/dogwood/m8/manifest.json");
const MUTATION_FIXTURE_ROOT: &str = "tests/fixtures/dogwood/m3/all-optional-valid";
const EXPECTED_VALID_BUNDLES: usize = 3;
const EXPECTED_MUTATIONS: usize = 10;

static TEMP_SEQUENCE: AtomicU64 = AtomicU64::new(0);

#[derive(Debug, Deserialize)]
#[serde(deny_unknown_fields)]
struct Manifest {
    schema_version: u64,
    revision: String,
    mutation_base: MutationBase,
    valid_bundles: Vec<ValidBundle>,
    mutations: Vec<Mutation>,
}

#[derive(Debug, Deserialize)]
#[serde(deny_unknown_fields)]
struct MutationBase {
    directory: String,
    inputs: HashedInputs,
}

#[derive(Debug, Deserialize)]
#[serde(deny_unknown_fields)]
struct HashedInputs {
    policy: HashedInput,
    action_schema: HashedInput,
    event_schema: HashedInput,
    providers: HashedInput,
    macros: HashedInput,
}

#[derive(Debug, Deserialize)]
#[serde(deny_unknown_fields)]
struct HashedInput {
    path: String,
    sha256: String,
}

#[derive(Debug, Deserialize)]
#[serde(deny_unknown_fields)]
struct ValidBundle {
    name: String,
    directory: String,
    inputs: Inputs,
    artifacts: Vec<Artifact>,
}

#[derive(Debug, Deserialize)]
#[serde(deny_unknown_fields)]
struct Inputs {
    policy: String,
    action_schema: String,
    event_schema: Option<String>,
    providers: Option<String>,
    macros: Option<String>,
}

#[derive(Debug, Deserialize)]
#[serde(deny_unknown_fields)]
struct Artifact {
    path: String,
    upstream_path: String,
    sha256: String,
}

#[derive(Clone, Copy, Debug, Deserialize, Eq, Ord, PartialEq, PartialOrd)]
#[serde(rename_all = "snake_case")]
enum Component {
    Policy,
    ActionSchema,
    EventSchema,
    Providers,
    Macros,
}

impl Component {
    const fn source_kind(self) -> SourceKind {
        match self {
            Self::Policy => SourceKind::Policy,
            Self::ActionSchema => SourceKind::ActionSchema,
            Self::EventSchema => SourceKind::EventSchema,
            Self::Providers => SourceKind::Providers,
            Self::Macros => SourceKind::Macros,
        }
    }
}

#[derive(Clone, Copy, Debug, Deserialize, Eq, Ord, PartialEq, PartialOrd)]
#[serde(rename_all = "kebab-case")]
enum MutationKind {
    Replace,
    DropTail,
}

#[derive(Debug, Deserialize)]
#[serde(deny_unknown_fields)]
struct Mutation {
    name: String,
    component: Component,
    kind: MutationKind,
    replacement: Option<String>,
    drop_bytes: Option<usize>,
    sha256: String,
}

#[derive(Clone)]
struct OwnedBundle {
    policy: String,
    action_schema: String,
    event_schema: Option<String>,
    providers: Option<String>,
    macros: Option<String>,
}

impl OwnedBundle {
    fn input(&self) -> BundleInput<'_> {
        BundleInput {
            policy: &self.policy,
            action_schema: &self.action_schema,
            event_schema: self.event_schema.as_deref(),
            providers: self.providers.as_deref(),
            macros: self.macros.as_deref(),
        }
    }

    fn semantic_input(&self) -> SemanticInput<'_> {
        SemanticInput {
            policy: &self.policy,
            event_schema: self.event_schema.as_deref(),
            providers: self.providers.as_deref(),
            macros: self.macros.as_deref(),
        }
    }

    fn source(&self, component: Component) -> &str {
        match component {
            Component::Policy => &self.policy,
            Component::ActionSchema => &self.action_schema,
            Component::EventSchema => self
                .event_schema
                .as_deref()
                .expect("mutation base has an event schema"),
            Component::Providers => self
                .providers
                .as_deref()
                .expect("mutation base has providers"),
            Component::Macros => self.macros.as_deref().expect("mutation base has macros"),
        }
    }

    fn replace(&mut self, component: Component, source: String) {
        match component {
            Component::Policy => self.policy = source,
            Component::ActionSchema => self.action_schema = source,
            Component::EventSchema => self.event_schema = Some(source),
            Component::Providers => self.providers = Some(source),
            Component::Macros => self.macros = Some(source),
        }
    }
}

struct OracleBundle {
    root: PathBuf,
    policy: PathBuf,
    action_schema: PathBuf,
    event_schema: Option<PathBuf>,
    providers: Option<PathBuf>,
    macros: Option<PathBuf>,
}

impl OracleBundle {
    fn create(case: &str, bundle: &OwnedBundle) -> Self {
        let root = std::env::temp_dir().join(format!(
            "dogwood-lsp-m8-corpus-{}-{}",
            std::process::id(),
            TEMP_SEQUENCE.fetch_add(1, Ordering::Relaxed)
        ));
        fs::create_dir(&root)
            .unwrap_or_else(|error| panic!("{case}: cannot create temporary bundle: {error}"));
        let root = temp_root::canonical(&root);
        let policy = write(&root, "policy.dw", &bundle.policy);
        let action_schema = write(&root, "actions.cedarschema", &bundle.action_schema);
        let event_schema = bundle
            .event_schema
            .as_deref()
            .map(|source| write(&root, "events.dwschema", source));
        let providers = bundle
            .providers
            .as_deref()
            .map(|source| write(&root, "providers.json", source));
        let macros = bundle
            .macros
            .as_deref()
            .map(|source| write(&root, "macros.dw", source));
        Self {
            root,
            policy,
            action_schema,
            event_schema,
            providers,
            macros,
        }
    }

    fn invocation<'a>(&'a self, case: &'a str) -> ValidateInvocation<'a> {
        ValidateInvocation {
            fixture: case,
            policy: &self.policy,
            policy_schema: &self.action_schema,
            event_schema: self.event_schema.as_deref(),
            providers: self.providers.as_deref(),
            macros: self.macros.as_deref(),
        }
    }
}

impl Drop for OracleBundle {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.root);
    }
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq)]
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

#[derive(Clone, Debug, Deserialize, Eq, PartialEq)]
#[serde(deny_unknown_fields)]
struct CliValidationReport {
    passed: bool,
    passed_without_warnings: bool,
    errors: Vec<CliFinding>,
    warnings: Vec<CliFinding>,
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq)]
#[serde(deny_unknown_fields)]
struct CliFatalReport {
    severity: Severity,
    code: Option<String>,
    message: String,
    #[serde(default)]
    labels: Vec<DiagnosticLabel>,
    help: Option<String>,
    spanned: bool,
    #[serde(default)]
    related: Vec<CliFinding>,
}

#[test]
fn expanded_documentation_bundles_match_the_workspace_cli_and_are_parser_backed() {
    let manifest = manifest();
    validate_manifest(&manifest);
    let root = fixture_root();

    for case in &manifest.valid_bundles {
        let context = context(&case.name);
        let bundle = load_valid_bundle(&root, case, &context);
        let local = validate_bundle(&bundle.input());
        let oracle_files = OracleBundle::create(&case.name, &bundle);
        let oracle = dogwood_cli::validate(&oracle_files.invocation(&case.name))
            .unwrap_or_else(|error| panic!("{context}: {error}"));
        assert_clean_exact_match(&local, &oracle, &context);

        let repeated_local = validate_bundle(&bundle.input());
        let repeated_oracle = dogwood_cli::validate(&oracle_files.invocation(&case.name))
            .unwrap_or_else(|error| panic!("{context}: repeated oracle failed: {error}"));
        assert_eq!(repeated_local, local, "{context}: local output changed");
        assert_eq!(repeated_oracle, oracle, "{context}: CLI output changed");

        assert_policy_parser_backed(&bundle, &context);
        if let Some(schema) = bundle.event_schema.as_deref() {
            assert_event_schema_parser_backed(schema, &context);
        }
    }
}

#[test]
fn every_all_input_component_mutation_matches_the_cli_and_projects_nonempty_diagnostics() {
    let manifest = manifest();
    validate_manifest(&manifest);
    let base = load_mutation_base(&manifest);
    assert_clean_bundle(&base, "all-input-valid");

    for mutation in &manifest.mutations {
        let context = context(&mutation.name);
        let mut bundle = base.clone();
        let mutated = apply_mutation(bundle.source(mutation.component), mutation, &context);
        assert_eq!(
            sha256(mutated.as_bytes()),
            mutation.sha256,
            "{context}: generated mutation hash differs from the manifest"
        );
        bundle.replace(mutation.component, mutated);

        let local = validate_bundle(&bundle.input());
        let oracle_files = OracleBundle::create(&mutation.name, &bundle);
        let oracle = dogwood_cli::validate(&oracle_files.invocation(&mutation.name))
            .unwrap_or_else(|error| panic!("{context}: {error}"));
        assert_nonclean_exact_match(&local, &oracle, &context);
        assert_primary_source(&local, mutation.component, &context);
        assert_finding_ranges(&bundle, &local, &context);
        assert_nonempty_lsp_projection(&bundle, local.clone(), &context);

        let repeated_local = validate_bundle(&bundle.input());
        let repeated_oracle = dogwood_cli::validate(&oracle_files.invocation(&mutation.name))
            .unwrap_or_else(|error| panic!("{context}: repeated oracle failed: {error}"));
        assert_eq!(repeated_local, local, "{context}: local output changed");
        assert_eq!(repeated_oracle, oracle, "{context}: CLI output changed");

        match mutation.component {
            Component::Policy => assert_complete_policy_fallback(&bundle, &context),
            Component::EventSchema => {
                assert_complete_event_schema_fallback(&bundle, &context);
                assert_complete_policy_fallback(&bundle, &context);
            }
            Component::Providers | Component::Macros => {
                assert_complete_policy_fallback(&bundle, &context);
            }
            Component::ActionSchema => {}
        }
    }
}

#[test]
fn unicode_crlf_and_many_token_sources_preserve_token_and_delta_invariants() {
    let unicode_policy = include_str!("fixtures/dogwood/m5/cedar-crlf-unicode.dw");
    let unicode_schema = include_str!("fixtures/dogwood/m6/unicode-crlf.dwschema");
    assert!(
        frontend_semantic::classify(unicode_policy).is_some(),
        "valid Unicode/CRLF policy must be parser-backed"
    );
    assert!(
        frontend_event_schema::classify(unicode_schema).is_some(),
        "valid Unicode/CRLF event schema must be parser-backed"
    );
    assert_token_invariants(
        unicode_policy,
        analyze_with_input(&SemanticInput::standalone(unicode_policy)).unwrap(),
    );
    assert_token_invariants(
        unicode_schema,
        analyze_event_schema(unicode_schema).unwrap(),
    );

    let mut long_line = String::from("// \u{1f600}\r\n");
    for index in 0..16_384 {
        if index != 0 {
            long_line.push(' ');
        }
        long_line.push_str(if index % 3 == 0 { "true" } else { "123h" });
    }
    let first = analyze_lexical(&long_line).expect("bounded long line should tokenize");
    let second = analyze_lexical(&long_line).expect("bounded long line should retokenize");
    assert_eq!(first, second);
    assert!(first.len() > 16_000);
    assert_token_invariants(&long_line, first);
}

fn manifest() -> Manifest {
    serde_json::from_str(MANIFEST_SOURCE).expect("M8 manifest must be valid JSON")
}

fn fixture_root() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/dogwood/m8")
}

fn validate_manifest(manifest: &Manifest) {
    assert_eq!(manifest.schema_version, 1);
    assert!(!manifest.revision.is_empty());
    assert_eq!(manifest.valid_bundles.len(), EXPECTED_VALID_BUNDLES);
    assert_eq!(manifest.mutations.len(), EXPECTED_MUTATIONS);
    assert_eq!(manifest.mutation_base.directory, MUTATION_FIXTURE_ROOT);

    let mut names = BTreeSet::new();
    let root = fixture_root();
    for bundle in &manifest.valid_bundles {
        assert!(names.insert(bundle.name.as_str()), "duplicate bundle name");
        assert_eq!(bundle.name, bundle.directory);
        let declared = declared_paths(&bundle.inputs);
        let artifacts = bundle
            .artifacts
            .iter()
            .map(|artifact| artifact.path.as_str())
            .collect::<BTreeSet<_>>();
        assert_eq!(artifacts, declared, "{}: artifact inventory", bundle.name);
        for artifact in &bundle.artifacts {
            assert!(!artifact.upstream_path.is_empty());
            assert_eq!(
                sha256(
                    &fs::read(root.join(&bundle.directory).join(&artifact.path))
                        .expect("declared M8 artifact should be readable")
                ),
                artifact.sha256,
                "{}: {}",
                bundle.name,
                artifact.path
            );
        }
    }
    assert!(
        manifest
            .valid_bundles
            .windows(2)
            .all(|pair| pair[0].name < pair[1].name),
        "valid bundle names must be sorted"
    );
    assert!(
        manifest
            .mutations
            .windows(2)
            .all(|pair| pair[0].name < pair[1].name),
        "mutation names must be sorted"
    );
    let components = manifest
        .mutations
        .iter()
        .map(|mutation| (mutation.component, mutation.kind))
        .collect::<BTreeSet<_>>();
    assert_eq!(components.len(), EXPECTED_MUTATIONS);
}

fn declared_paths(inputs: &Inputs) -> BTreeSet<&str> {
    let mut paths = BTreeSet::from([inputs.policy.as_str(), inputs.action_schema.as_str()]);
    paths.extend(inputs.event_schema.as_deref());
    paths.extend(inputs.providers.as_deref());
    paths.extend(inputs.macros.as_deref());
    paths
}

fn load_valid_bundle(root: &Path, case: &ValidBundle, context: &str) -> OwnedBundle {
    let root = root.join(&case.directory);
    OwnedBundle {
        policy: read(root.join(&case.inputs.policy), context),
        action_schema: read(root.join(&case.inputs.action_schema), context),
        event_schema: case
            .inputs
            .event_schema
            .as_ref()
            .map(|path| read(root.join(path), context)),
        providers: case
            .inputs
            .providers
            .as_ref()
            .map(|path| read(root.join(path), context)),
        macros: case
            .inputs
            .macros
            .as_ref()
            .map(|path| read(root.join(path), context)),
    }
}

fn load_mutation_base(manifest: &Manifest) -> OwnedBundle {
    let root = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join(&manifest.mutation_base.directory);
    let inputs = &manifest.mutation_base.inputs;
    let load = |input: &HashedInput| {
        let source = read(root.join(&input.path), "all-input-valid");
        assert_eq!(sha256(source.as_bytes()), input.sha256);
        source
    };
    OwnedBundle {
        policy: load(&inputs.policy),
        action_schema: load(&inputs.action_schema),
        event_schema: Some(load(&inputs.event_schema)),
        providers: Some(load(&inputs.providers)),
        macros: Some(load(&inputs.macros)),
    }
}

fn apply_mutation(source: &str, mutation: &Mutation, context: &str) -> String {
    match mutation.kind {
        MutationKind::Replace => {
            assert_eq!(
                mutation.drop_bytes, None,
                "{context}: replace/drop mismatch"
            );
            mutation
                .replacement
                .clone()
                .unwrap_or_else(|| panic!("{context}: replacement is missing"))
        }
        MutationKind::DropTail => {
            assert_eq!(
                mutation.replacement, None,
                "{context}: replace/drop mismatch"
            );
            let drop_bytes = mutation
                .drop_bytes
                .unwrap_or_else(|| panic!("{context}: drop_bytes is missing"));
            let end = source
                .len()
                .checked_sub(drop_bytes)
                .unwrap_or_else(|| panic!("{context}: truncation exceeds source"));
            assert!(
                source.is_char_boundary(end),
                "{context}: truncation splits UTF-8"
            );
            source[..end].to_owned()
        }
    }
}

fn assert_clean_bundle(bundle: &OwnedBundle, case: &str) {
    let context = context(case);
    let local = validate_bundle(&bundle.input());
    let oracle_files = OracleBundle::create(case, bundle);
    let oracle = dogwood_cli::validate(&oracle_files.invocation(case))
        .unwrap_or_else(|error| panic!("{context}: {error}"));
    assert_clean_exact_match(&local, &oracle, &context);
    assert_empty_lsp_projection(bundle, local, &context);
}

fn assert_clean_exact_match(
    local: &FrontendOutcome<ValidationReport>,
    oracle: &OracleOutput,
    context: &str,
) {
    let cli: CliValidationReport = serde_json::from_slice(&oracle.stdout)
        .unwrap_or_else(|error| panic!("{context}: invalid CLI validation JSON: {error}"));
    assert_eq!(oracle.exit_code, 0, "{context}: CLI exit status");
    assert!(oracle.stderr.is_empty(), "{context}: CLI stderr");
    assert!(cli.passed, "{context}: CLI did not pass");
    assert!(
        cli.passed_without_warnings,
        "{context}: CLI emitted warnings"
    );
    let FrontendOutcome::Report(report) = local else {
        panic!("{context}: local frontend did not return a report: {local:?}");
    };
    compare_validation_reports(report, &cli, context);
}

fn assert_nonclean_exact_match(
    local: &FrontendOutcome<ValidationReport>,
    oracle: &OracleOutput,
    context: &str,
) {
    assert_eq!(oracle.exit_code, 2, "{context}: CLI exit status");
    assert!(oracle.stderr.is_empty(), "{context}: CLI stderr");
    match local {
        FrontendOutcome::Report(report) => {
            let cli: CliValidationReport = serde_json::from_slice(&oracle.stdout)
                .unwrap_or_else(|error| panic!("{context}: invalid CLI validation JSON: {error}"));
            assert!(
                !cli.passed_without_warnings,
                "{context}: mutation unexpectedly passed cleanly"
            );
            compare_validation_reports(report, &cli, context);
        }
        FrontendOutcome::Fatal(fatal) => {
            let cli: CliFatalReport = serde_json::from_slice(&oracle.stdout)
                .unwrap_or_else(|error| panic!("{context}: invalid CLI fatal JSON: {error}"));
            compare_finding(
                &fatal.diagnostic,
                &CliFinding {
                    severity: cli.severity,
                    code: cli.code,
                    message: cli.message,
                    labels: cli.labels,
                    help: cli.help,
                    spanned: cli.spanned,
                },
                context,
                "diagnostic",
            );
            compare_findings(&fatal.related, &cli.related, context, "related");
        }
        FrontendOutcome::OperationalLimit(limit) => {
            panic!("{context}: bounded mutation hit local operational limit: {limit:?}")
        }
    }
}

fn compare_validation_reports(local: &ValidationReport, cli: &CliValidationReport, context: &str) {
    assert_eq!(local.passed, cli.passed, "{context}: passed");
    assert_eq!(
        local.passed_without_warnings, cli.passed_without_warnings,
        "{context}: passed_without_warnings"
    );
    compare_findings(&local.errors, &cli.errors, context, "errors");
    compare_findings(&local.warnings, &cli.warnings, context, "warnings");
}

fn compare_findings(local: &[Finding], cli: &[CliFinding], context: &str, channel: &str) {
    assert_eq!(local.len(), cli.len(), "{context}: {channel} count");
    for (index, (local, cli)) in local.iter().zip(cli).enumerate() {
        compare_finding(local, cli, context, &format!("{channel}[{index}]"));
    }
}

fn compare_finding(local: &Finding, cli: &CliFinding, context: &str, location: &str) {
    assert_eq!(
        local.severity, cli.severity,
        "{context}: {location} severity"
    );
    assert_eq!(local.code, cli.code, "{context}: {location} code");
    assert_eq!(local.message, cli.message, "{context}: {location} message");
    assert_eq!(local.help, cli.help, "{context}: {location} help");
    assert_eq!(local.spanned, cli.spanned, "{context}: {location} spanned");
    assert_eq!(local.labels, cli.labels, "{context}: {location} labels");
}

fn assert_primary_source(
    outcome: &FrontendOutcome<ValidationReport>,
    component: Component,
    context: &str,
) {
    let actual = match outcome {
        FrontendOutcome::Fatal(fatal) => fatal.diagnostic.source_kind,
        FrontendOutcome::Report(report) => report
            .errors
            .first()
            .or_else(|| report.warnings.first())
            .and_then(|finding| finding.source_kind),
        FrontendOutcome::OperationalLimit(limit) => Some(limit.source_kind),
    };
    let expected = if component == Component::ActionSchema {
        // With a custom event schema, Dogwood wraps action-schema parse
        // failures in a spanless EventSchema(String) before exposing a source.
        None
    } else {
        Some(component.source_kind())
    };
    assert_eq!(actual, expected, "{context}: source attribution");
}

fn assert_finding_ranges(
    bundle: &OwnedBundle,
    outcome: &FrontendOutcome<ValidationReport>,
    context: &str,
) {
    let findings: Vec<&Finding> = match outcome {
        FrontendOutcome::Fatal(fatal) => std::iter::once(fatal.diagnostic.as_ref())
            .chain(fatal.related.iter())
            .collect(),
        FrontendOutcome::Report(report) => report.errors.iter().chain(&report.warnings).collect(),
        FrontendOutcome::OperationalLimit(_) => Vec::new(),
    };
    for (finding_index, finding) in findings.into_iter().enumerate() {
        let Some(source_kind) = finding.source_kind else {
            assert!(finding.labels.is_empty(), "{context}: unattributed labels");
            continue;
        };
        let source = bundle.source(match source_kind {
            SourceKind::Policy => Component::Policy,
            SourceKind::ActionSchema => Component::ActionSchema,
            SourceKind::EventSchema => Component::EventSchema,
            SourceKind::Providers => Component::Providers,
            SourceKind::Macros => Component::Macros,
        });
        for (label_index, label) in finding.labels.iter().enumerate() {
            let end = label
                .start
                .checked_add(label.len)
                .unwrap_or_else(|| panic!("{context}: label arithmetic overflow"));
            let synthetic_eof = label.start == source.len() && label.len == 1;
            assert!(
                source.is_char_boundary(label.start)
                    && (synthetic_eof || (end <= source.len() && source.is_char_boundary(end))),
                "{context}: finding {finding_index} label {label_index} is out of bounds: \
                 source={source_kind:?} source_len={} label={label:?}",
                source.len()
            );
            if synthetic_eof {
                assert_eq!(
                    byte_range_to_utf16(source, label.start, 0)
                        .expect("synthetic EOF label start should project")
                        .start,
                    byte_range_to_utf16(source, source.len(), 0)
                        .expect("source EOF should project")
                        .start,
                    "{context}: synthetic EOF label"
                );
            } else {
                byte_range_to_utf16(source, label.start, label.len).unwrap_or_else(|error| {
                    panic!(
                        "{context}: finding {finding_index} label {label_index} has no UTF-16 range: {error}"
                    )
                });
            }
        }
    }
}

fn documents<'a>(
    bundle: &'a OwnedBundle,
    policy_uri: &'a Uri,
    action_uri: &'a Uri,
    event_uri: &'a Uri,
    providers_uri: &'a Uri,
    macros_uri: &'a Uri,
) -> BundleDocuments<'a> {
    BundleDocuments {
        policy: SourceDocument {
            uri: policy_uri,
            text: &bundle.policy,
        },
        action_schema: SourceDocument {
            uri: action_uri,
            text: &bundle.action_schema,
        },
        event_schema: bundle.event_schema.as_deref().map(|text| SourceDocument {
            uri: event_uri,
            text,
        }),
        providers: bundle.providers.as_deref().map(|text| SourceDocument {
            uri: providers_uri,
            text,
        }),
        macros: bundle.macros.as_deref().map(|text| SourceDocument {
            uri: macros_uri,
            text,
        }),
    }
}

fn assert_empty_lsp_projection(
    bundle: &OwnedBundle,
    outcome: FrontendOutcome<ValidationReport>,
    context: &str,
) {
    let uris = projection_uris();
    let publication = project_frontend_outcome(
        7,
        documents(bundle, &uris.0, &uris.1, &uris.2, &uris.3, &uris.4),
        outcome,
    );
    assert!(
        publication.diagnostics.is_empty(),
        "{context}: clean CLI/local result must project an empty LSP diagnostic set"
    );
}

fn assert_nonempty_lsp_projection(
    bundle: &OwnedBundle,
    outcome: FrontendOutcome<ValidationReport>,
    context: &str,
) {
    let uris = projection_uris();
    let publication = project_frontend_outcome(
        7,
        documents(bundle, &uris.0, &uris.1, &uris.2, &uris.3, &uris.4),
        outcome,
    );
    assert!(
        !publication.diagnostics.is_empty(),
        "{context}: non-clean CLI/local result projected a clean LSP diagnostic set"
    );
    assert_eq!(publication.version, Some(7));
}

fn projection_uris() -> (Uri, Uri, Uri, Uri, Uri) {
    (
        uri("file:///bundle/policy.dw"),
        uri("file:///bundle/actions.cedarschema"),
        uri("file:///bundle/events.dwschema"),
        uri("file:///bundle/providers.json"),
        uri("file:///bundle/macros.dw"),
    )
}

fn assert_policy_parser_backed(bundle: &OwnedBundle, context: &str) {
    let semantic_input = bundle.semantic_input();
    let structural = frontend_semantic::classify_with_input(&semantic_input)
        .unwrap_or_else(|| panic!("{context}: valid policy has no structural classifications"));
    assert!(!structural.is_empty(), "{context}: no structural spans");
    let tokens = analyze_with_input(&semantic_input)
        .unwrap_or_else(|error| panic!("{context}: policy analysis failed: {error}"));
    let lexical = analyze_lexical(&bundle.policy)
        .unwrap_or_else(|error| panic!("{context}: lexical analysis failed: {error}"));
    assert_ne!(
        tokens, lexical,
        "{context}: valid corpus policy produced only lexical fallback"
    );
    assert_token_invariants(&bundle.policy, tokens);
}

fn assert_event_schema_parser_backed(source: &str, context: &str) {
    let structural = frontend_event_schema::classify(source).unwrap_or_else(|| {
        panic!("{context}: valid event schema has no structural classifications")
    });
    assert!(
        !structural.is_empty(),
        "{context}: no schema structural spans"
    );
    let tokens = analyze_event_schema(source)
        .unwrap_or_else(|error| panic!("{context}: event schema analysis failed: {error}"));
    let lexical = analyze_lexical(source)
        .unwrap_or_else(|error| panic!("{context}: schema lexical analysis failed: {error}"));
    assert_ne!(
        tokens, lexical,
        "{context}: valid event schema produced only lexical fallback"
    );
    assert_token_invariants(source, tokens);
}

fn assert_complete_policy_fallback(bundle: &OwnedBundle, context: &str) {
    let actual = analyze_with_input(&bundle.semantic_input())
        .unwrap_or_else(|error| panic!("{context}: policy fallback failed: {error}"));
    let lexical = analyze_lexical(&bundle.policy)
        .unwrap_or_else(|error| panic!("{context}: policy lexical analysis failed: {error}"));
    assert_eq!(actual, lexical, "{context}: policy fallback is incomplete");
    assert!(!actual.is_empty(), "{context}: policy fallback is empty");
    assert_token_invariants(&bundle.policy, actual);
}

fn assert_complete_event_schema_fallback(bundle: &OwnedBundle, context: &str) {
    let source = bundle
        .event_schema
        .as_deref()
        .expect("mutation base has an event schema");
    let actual = analyze_event_schema(source)
        .unwrap_or_else(|error| panic!("{context}: schema fallback failed: {error}"));
    let lexical = analyze_lexical(source)
        .unwrap_or_else(|error| panic!("{context}: schema lexical analysis failed: {error}"));
    assert_eq!(actual, lexical, "{context}: schema fallback is incomplete");
    assert!(!actual.is_empty(), "{context}: schema fallback is empty");
    assert_token_invariants(source, actual);
}

fn assert_token_invariants(source: &str, tokens: Vec<Token>) {
    let tokens = validate_tokens(source, tokens.clone()).expect("tokens must validate");
    assert_eq!(
        tokens,
        tokens.clone(),
        "token ordering must be deterministic"
    );
    for token in &tokens {
        assert!(token.span.end() <= source.len());
        assert!(source.is_char_boundary(token.span.start()));
        assert!(source.is_char_boundary(token.span.end()));
        assert!((token.kind.legend_index() as usize) < TOKEN_TYPES.len());
        if let Some(modifier) = token.modifier {
            assert!((modifier.legend_index() as usize) < TOKEN_MODIFIERS.len());
        }
    }
    for pair in tokens.windows(2) {
        assert!(pair[0].span.end() <= pair[1].span.start());
    }

    let encoded = encode_reference(source, &tokens);
    let decoded = decode_reference(&encoded);
    let expected = token_segments(source, &tokens);
    assert_eq!(decoded, expected, "semantic deltas must be lossless");
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct Segment {
    line: u32,
    start: u32,
    length: u32,
    token_type: u32,
    modifiers: u32,
}

fn token_segments(source: &str, tokens: &[Token]) -> Vec<Segment> {
    let lines = source_lines(source);
    let positions = utf16_positions(source);
    let mut segments = Vec::new();
    for token in tokens {
        for (line_index, &(line_start, content_end)) in lines.iter().enumerate() {
            let start = token.span.start().max(line_start);
            let end = token.span.end().min(content_end);
            if start >= end {
                continue;
            }
            let start_position = positions[start].expect("token start must have a UTF-16 position");
            let end_position = positions[end].expect("token end must have a UTF-16 position");
            assert_eq!(start_position.line, line_index as u32);
            assert_eq!(end_position.line, line_index as u32);
            segments.push(Segment {
                line: line_index as u32,
                start: start_position.character,
                length: end_position.character - start_position.character,
                token_type: token.kind.legend_index(),
                modifiers: token.modifier.map_or(0, |modifier| modifier.legend_bit()),
            });
        }
    }
    segments
}

fn encode_reference(source: &str, tokens: &[Token]) -> Vec<[u32; 5]> {
    let mut previous_line = 0;
    let mut previous_start = 0;
    token_segments(source, tokens)
        .into_iter()
        .map(|segment| {
            let delta_line = segment.line - previous_line;
            let delta_start = if delta_line == 0 {
                segment.start - previous_start
            } else {
                segment.start
            };
            previous_line = segment.line;
            previous_start = segment.start;
            [
                delta_line,
                delta_start,
                segment.length,
                segment.token_type,
                segment.modifiers,
            ]
        })
        .collect()
}

fn decode_reference(encoded: &[[u32; 5]]) -> Vec<Segment> {
    let mut line = 0_u32;
    let mut start = 0_u32;
    encoded
        .iter()
        .map(|token| {
            line += token[0];
            start = if token[0] == 0 {
                start + token[1]
            } else {
                token[1]
            };
            Segment {
                line,
                start,
                length: token[2],
                token_type: token[3],
                modifiers: token[4],
            }
        })
        .collect()
}

fn source_lines(source: &str) -> Vec<(usize, usize)> {
    let bytes = source.as_bytes();
    let mut lines = Vec::new();
    let mut start = 0;
    let mut index = 0;
    while index < bytes.len() {
        let terminator = match bytes[index] {
            b'\r' if bytes.get(index + 1) == Some(&b'\n') => 2,
            b'\r' | b'\n' => 1,
            _ => {
                index += 1;
                continue;
            }
        };
        lines.push((start, index));
        index += terminator;
        start = index;
    }
    lines.push((start, source.len()));
    lines
}

fn utf16_positions(source: &str) -> Vec<Option<Position>> {
    let mut positions = vec![None; source.len() + 1];
    let mut byte_offset = 0;
    let mut line = 0_u32;
    let mut character = 0_u32;
    positions[0] = Some(Position::new(line, character));
    while byte_offset < source.len() {
        let tail = &source[byte_offset..];
        if tail.starts_with("\r\n") {
            byte_offset += 2;
            line += 1;
            character = 0;
            positions[byte_offset] = Some(Position::new(line, character));
            continue;
        }
        let scalar = tail.chars().next().expect("source tail is nonempty");
        byte_offset += scalar.len_utf8();
        if matches!(scalar, '\r' | '\n') {
            line += 1;
            character = 0;
        } else {
            character += scalar.len_utf16() as u32;
        }
        positions[byte_offset] = Some(Position::new(line, character));
    }
    positions
}

fn read(path: PathBuf, context: &str) -> String {
    fs::read_to_string(&path)
        .unwrap_or_else(|error| panic!("{context}: cannot read `{}`: {error}", path.display()))
}

fn write(root: &Path, name: &str, source: &str) -> PathBuf {
    let path = root.join(name);
    fs::write(&path, source).unwrap_or_else(|error| {
        panic!(
            "cannot write temporary oracle input `{}`: {error}",
            path.display()
        )
    });
    path
}

fn sha256(bytes: &[u8]) -> String {
    Sha256::digest(bytes)
        .iter()
        .map(|byte| format!("{byte:02x}"))
        .collect()
}

fn uri(value: &str) -> Uri {
    Uri::from_str(value).expect("test URI must be valid")
}

fn context(case: &str) -> String {
    format!("M8 workspace Dogwood bundle/case `{case}`")
}
