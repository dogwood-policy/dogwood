// dogwood-lsp handles Unix paths and file URIs only, so its tests run on Unix.
#![cfg(unix)]

#[path = "support/dogwood_cli.rs"]
mod dogwood_cli;

use std::collections::HashSet;
use std::fs;
use std::path::{Component, Path, PathBuf};

use dogwood_cli::{OracleOutput, ValidateInvocation};
use dogwood_lsp::frontend::{
    BundleInput, DiagnosticLabel, Finding, FrontendOutcome, Severity, validate_bundle,
};
use serde::Deserialize;

const FIXTURE_COUNT: usize = 15;
const REPEATED_CASES: [&str; 3] = [
    "default-valid",
    "parse-multiple-related",
    "validation-warning",
];

#[derive(Debug, Deserialize)]
#[serde(deny_unknown_fields)]
struct Manifest {
    schema_version: u64,
    revision: String,
    cases: Vec<Case>,
}

#[derive(Debug, Deserialize)]
#[serde(deny_unknown_fields)]
struct Case {
    name: String,
    directory: String,
    inputs: Inputs,
    optional_flags: Vec<String>,
    expected: Expected,
    provenance: Provenance,
}

#[derive(Debug, Deserialize)]
#[serde(deny_unknown_fields)]
struct Inputs {
    policy: String,
    policy_schema: String,
    event_schema: Option<String>,
    providers: Option<String>,
    macros: Option<String>,
}

#[derive(Clone, Copy, Debug, Deserialize, Eq, PartialEq)]
#[serde(rename_all = "kebab-case")]
enum JsonShape {
    ValidationReport,
    FatalDiagnostic,
}

#[derive(Clone, Copy, Debug, Deserialize, Eq, PartialEq)]
#[serde(rename_all = "lowercase")]
enum OutputChannel {
    Stdout,
}

#[derive(Clone, Copy, Debug, Deserialize, Eq, PartialEq)]
#[serde(rename_all = "lowercase")]
enum StderrExpectation {
    Empty,
}

#[derive(Debug, Deserialize)]
#[serde(deny_unknown_fields)]
struct Expected {
    exit_code: i32,
    output_channel: OutputChannel,
    stderr: StderrExpectation,
    json_shape: JsonShape,
    passed: Option<bool>,
    error_count: Option<usize>,
    warning_count: Option<usize>,
    related_finding_count: Option<usize>,
}

#[derive(Debug, Deserialize)]
#[serde(deny_unknown_fields)]
struct Provenance {
    revision: String,
    artifacts: Vec<Artifact>,
}

#[derive(Debug, Deserialize)]
#[serde(deny_unknown_fields)]
struct Artifact {
    path: String,
    origin: String,
    upstream_paths: Option<Vec<String>>,
    derivation: String,
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

struct LoadedBundle {
    policy_path: PathBuf,
    policy_schema_path: PathBuf,
    event_schema_path: Option<PathBuf>,
    providers_path: Option<PathBuf>,
    macros_path: Option<PathBuf>,
    policy: String,
    policy_schema: String,
    event_schema: Option<String>,
    providers: Option<String>,
    macros: Option<String>,
}

impl LoadedBundle {
    fn input(&self) -> BundleInput<'_> {
        BundleInput {
            policy: &self.policy,
            action_schema: &self.policy_schema,
            event_schema: self.event_schema.as_deref(),
            providers: self.providers.as_deref(),
            macros: self.macros.as_deref(),
        }
    }

    fn oracle_invocation<'a>(&'a self, fixture: &'a str) -> ValidateInvocation<'a> {
        ValidateInvocation {
            fixture,
            policy: &self.policy_path,
            policy_schema: &self.policy_schema_path,
            event_schema: self.event_schema_path.as_deref(),
            providers: self.providers_path.as_deref(),
            macros: self.macros_path.as_deref(),
        }
    }

    fn assert_unchanged(&self, context: &str) {
        assert_source_unchanged(&self.policy_path, &self.policy, context);
        assert_source_unchanged(&self.policy_schema_path, &self.policy_schema, context);
        assert_optional_source_unchanged(
            self.event_schema_path.as_deref(),
            self.event_schema.as_deref(),
            context,
        );
        assert_optional_source_unchanged(
            self.providers_path.as_deref(),
            self.providers.as_deref(),
            context,
        );
        assert_optional_source_unchanged(
            self.macros_path.as_deref(),
            self.macros.as_deref(),
            context,
        );
    }
}

#[test]
fn local_frontend_matches_workspace_cli_on_all_complete_bundles() {
    let fixture_root = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/dogwood/m3");
    let manifest_path = fixture_root.join("manifest.json");
    let manifest_source = fs::read_to_string(&manifest_path)
        .unwrap_or_else(|error| panic!("cannot read `{}`: {error}", manifest_path.display()));
    let manifest: Manifest = serde_json::from_str(&manifest_source)
        .unwrap_or_else(|error| panic!("invalid manifest JSON: {error}"));
    validate_manifest(&manifest, &fixture_root);

    for case in &manifest.cases {
        let context = context(&case.name, &manifest.revision);
        let bundle = load_bundle(case, &fixture_root, &context);
        let local = validate_bundle(&bundle.input());
        let oracle = dogwood_cli::validate(&bundle.oracle_invocation(&case.name))
            .unwrap_or_else(|error| panic!("{error}"));

        compare_case(case, &local, &oracle, &context);
        bundle.assert_unchanged(&context);

        if REPEATED_CASES.contains(&case.name.as_str()) {
            let repeated_local = validate_bundle(&bundle.input());
            assert_eq!(
                repeated_local, local,
                "{context}: repeated adapter outcome changed"
            );
            let local_bytes = serde_json::to_vec(&local)
                .unwrap_or_else(|error| panic!("{context}: adapter serialization failed: {error}"));
            let repeated_local_bytes = serde_json::to_vec(&repeated_local)
                .unwrap_or_else(|error| panic!("{context}: adapter serialization failed: {error}"));
            assert_eq!(
                repeated_local_bytes, local_bytes,
                "{context}: repeated adapter structured bytes changed"
            );

            let repeated_oracle = dogwood_cli::validate(&bundle.oracle_invocation(&case.name))
                .unwrap_or_else(|error| panic!("{error}"));
            assert_eq!(
                repeated_oracle, oracle,
                "{context}: repeated CLI exit status or raw output changed"
            );
            bundle.assert_unchanged(&context);
        }
    }
}

fn validate_manifest(manifest: &Manifest, fixture_root: &Path) {
    assert_eq!(
        manifest.schema_version, 1,
        "fixture `<manifest>`: unsupported schema version"
    );
    assert_eq!(
        manifest.cases.len(),
        FIXTURE_COUNT,
        "fixture `<manifest>` from source revision `{}`: expected {FIXTURE_COUNT} cases",
        manifest.revision
    );

    let mut previous_name: Option<&str> = None;
    for case in &manifest.cases {
        let context = context(&case.name, &manifest.revision);
        if let Some(previous) = previous_name {
            assert!(
                previous < case.name.as_str(),
                "{context}: case names must be sorted and unique; `{previous}` precedes `{}`",
                case.name
            );
        }
        previous_name = Some(&case.name);

        assert_safe_component(&case.name, "case name", &context);
        assert_safe_component(&case.directory, "case directory", &context);
        assert_eq!(
            case.directory, case.name,
            "{context}: case directory must equal its name"
        );
        let case_root = fixture_root.join(&case.directory);
        let metadata = fs::symlink_metadata(&case_root)
            .unwrap_or_else(|error| panic!("{context}: cannot inspect case directory: {error}"));
        assert!(
            metadata.file_type().is_dir(),
            "{context}: case directory is missing, not a directory, or a symlink"
        );

        let declared = declared_inputs(&case.inputs, &context);
        for file in &declared {
            assert_regular_file(&case_root.join(file), &context);
        }

        let mut expected_flags = Vec::new();
        if case.inputs.event_schema.is_some() {
            expected_flags.push("--event-schema".to_owned());
        }
        if case.inputs.providers.is_some() {
            expected_flags.push("--providers".to_owned());
        }
        if case.inputs.macros.is_some() {
            expected_flags.push("--macros".to_owned());
        }
        assert_eq!(
            case.optional_flags, expected_flags,
            "{context}: optional flags do not match non-null optional inputs"
        );

        assert_eq!(
            case.provenance.revision, manifest.revision,
            "{context}: provenance revision mismatch"
        );
        let mut artifact_paths = HashSet::new();
        for artifact in &case.provenance.artifacts {
            assert_safe_component(&artifact.path, "provenance artifact path", &context);
            assert!(
                artifact_paths.insert(artifact.path.as_str()),
                "{context}: duplicate provenance artifact `{}`",
                artifact.path
            );
            assert!(
                !artifact.origin.is_empty(),
                "{context}: provenance origin is empty for `{}`",
                artifact.path
            );
            assert!(
                !artifact.derivation.is_empty(),
                "{context}: provenance derivation is empty for `{}`",
                artifact.path
            );
            if let Some(upstream_paths) = &artifact.upstream_paths {
                assert!(
                    upstream_paths.iter().all(|path| !path.is_empty()),
                    "{context}: provenance contains an empty upstream path for `{}`",
                    artifact.path
                );
            }
        }
        let declared_set: HashSet<&str> = declared.iter().map(String::as_str).collect();
        assert_eq!(
            artifact_paths, declared_set,
            "{context}: provenance artifacts do not exactly cover declared inputs"
        );

        validate_expected(&case.expected, &context);
    }

    for repeated_case in REPEATED_CASES {
        assert!(
            manifest.cases.iter().any(|case| case.name == repeated_case),
            "fixture `<manifest>` from source revision `{}`: repeated determinism case `{repeated_case}` is missing",
            manifest.revision
        );
    }
}

fn declared_inputs(inputs: &Inputs, context: &str) -> Vec<String> {
    let mut declared = vec![inputs.policy.clone(), inputs.policy_schema.clone()];
    declared.extend(inputs.event_schema.iter().cloned());
    declared.extend(inputs.providers.iter().cloned());
    declared.extend(inputs.macros.iter().cloned());
    let mut unique = HashSet::new();
    for file in &declared {
        assert_safe_component(file, "declared input", context);
        assert!(
            unique.insert(file.as_str()),
            "{context}: duplicate declared input `{file}`"
        );
    }
    declared
}

fn validate_expected(expected: &Expected, context: &str) {
    assert_eq!(
        expected.output_channel,
        OutputChannel::Stdout,
        "{context}: oracle JSON must use stdout"
    );
    assert_eq!(
        expected.stderr,
        StderrExpectation::Empty,
        "{context}: oracle stderr must be empty"
    );
    match expected.json_shape {
        JsonShape::ValidationReport => {
            let passed = expected
                .passed
                .unwrap_or_else(|| panic!("{context}: validation report is missing `passed`"));
            let error_count = expected
                .error_count
                .unwrap_or_else(|| panic!("{context}: validation report is missing `error_count`"));
            expected.warning_count.unwrap_or_else(|| {
                panic!("{context}: validation report is missing `warning_count`")
            });
            assert_eq!(
                expected.related_finding_count, None,
                "{context}: validation report cannot declare related findings"
            );
            assert_eq!(
                expected.exit_code,
                if passed { 0 } else { 2 },
                "{context}: validation report exit code disagrees with `passed`"
            );
            assert_eq!(
                passed,
                error_count == 0,
                "{context}: validation report `passed` disagrees with its error count"
            );
        }
        JsonShape::FatalDiagnostic => {
            assert_eq!(
                expected.exit_code, 2,
                "{context}: fatal diagnostic must expect exit code 2"
            );
            assert_eq!(
                (
                    expected.passed,
                    expected.error_count,
                    expected.warning_count
                ),
                (None, None, None),
                "{context}: fatal diagnostic cannot declare validation-report fields"
            );
            assert!(
                expected.related_finding_count.is_some(),
                "{context}: fatal diagnostic is missing `related_finding_count`"
            );
        }
    }
}

fn load_bundle(case: &Case, fixture_root: &Path, context: &str) -> LoadedBundle {
    let case_root = fixture_root.join(&case.directory);
    let policy_path = case_root.join(&case.inputs.policy);
    let policy_schema_path = case_root.join(&case.inputs.policy_schema);
    let event_schema_path = case
        .inputs
        .event_schema
        .as_ref()
        .map(|path| case_root.join(path));
    let providers_path = case
        .inputs
        .providers
        .as_ref()
        .map(|path| case_root.join(path));
    let macros_path = case.inputs.macros.as_ref().map(|path| case_root.join(path));

    LoadedBundle {
        policy: read_source(&policy_path, context),
        policy_schema: read_source(&policy_schema_path, context),
        event_schema: event_schema_path
            .as_deref()
            .map(|path| read_source(path, context)),
        providers: providers_path
            .as_deref()
            .map(|path| read_source(path, context)),
        macros: macros_path
            .as_deref()
            .map(|path| read_source(path, context)),
        policy_path,
        policy_schema_path,
        event_schema_path,
        providers_path,
        macros_path,
    }
}

fn compare_case(
    case: &Case,
    local: &FrontendOutcome<dogwood_lsp::frontend::ValidationReport>,
    oracle: &OracleOutput,
    context: &str,
) {
    assert_eq!(
        oracle.exit_code, case.expected.exit_code,
        "{context}: CLI exit code differs from the manifest"
    );

    match (case.expected.json_shape, local) {
        (JsonShape::ValidationReport, FrontendOutcome::Report(local_report)) => {
            let cli: CliValidationReport =
                serde_json::from_slice(&oracle.stdout).unwrap_or_else(|error| {
                    panic!(
                        "{context}: invalid validation-report JSON: {error}; stdout: {:?}",
                        String::from_utf8_lossy(&oracle.stdout)
                    )
                });
            assert_eq!(
                cli.passed,
                case.expected.passed.expect("manifest was validated"),
                "{context}: CLI `passed` differs from the manifest"
            );
            assert_eq!(
                cli.errors.len(),
                case.expected.error_count.expect("manifest was validated"),
                "{context}: CLI error count differs from the manifest"
            );
            assert_eq!(
                cli.warnings.len(),
                case.expected.warning_count.expect("manifest was validated"),
                "{context}: CLI warning count differs from the manifest"
            );
            assert_eq!(
                local_report.passed, cli.passed,
                "{context}: adapter and CLI `passed` differ"
            );
            assert_eq!(
                local_report.passed_without_warnings, cli.passed_without_warnings,
                "{context}: adapter and CLI `passed_without_warnings` differ"
            );
            assert_eq!(
                if local_report.passed { 0 } else { 2 },
                oracle.exit_code,
                "{context}: adapter pass state and CLI exit code differ"
            );
            compare_findings(&local_report.errors, &cli.errors, context, "errors");
            compare_findings(&local_report.warnings, &cli.warnings, context, "warnings");
        }
        (JsonShape::FatalDiagnostic, FrontendOutcome::Fatal(local_fatal)) => {
            let cli: CliFatalReport =
                serde_json::from_slice(&oracle.stdout).unwrap_or_else(|error| {
                    panic!(
                        "{context}: invalid fatal-diagnostic JSON: {error}; stdout: {:?}",
                        String::from_utf8_lossy(&oracle.stdout)
                    )
                });
            let primary = CliFinding {
                severity: cli.severity,
                code: cli.code,
                message: cli.message,
                labels: cli.labels,
                help: cli.help,
                spanned: cli.spanned,
            };
            compare_finding(&local_fatal.diagnostic, &primary, context, "diagnostic");
            compare_findings(&local_fatal.related, &cli.related, context, "related");
            assert_eq!(
                cli.related.len(),
                case.expected
                    .related_finding_count
                    .expect("manifest was validated"),
                "{context}: CLI related-finding count differs from the manifest"
            );
            assert_eq!(
                oracle.exit_code, 2,
                "{context}: fatal adapter channel requires CLI exit code 2"
            );
        }
        (_, FrontendOutcome::OperationalLimit(limit)) => {
            panic!("{context}: local adapter returned an operational limit: {limit:?}")
        }
        (expected, actual) => {
            panic!(
                "{context}: adapter/CLI channel mismatch; expected {expected:?}, adapter returned {actual:?}"
            )
        }
    }
}

fn compare_findings(local: &[Finding], cli: &[CliFinding], context: &str, channel: &str) {
    assert_eq!(
        local.len(),
        cli.len(),
        "{context}: adapter and CLI {channel} counts differ"
    );
    for (index, (local, cli)) in local.iter().zip(cli).enumerate() {
        compare_finding(local, cli, context, &format!("{channel}[{index}]"));
    }
}

fn compare_finding(local: &Finding, cli: &CliFinding, context: &str, location: &str) {
    assert_eq!(
        local.severity, cli.severity,
        "{context}: severity differs at {location}"
    );
    assert_eq!(
        local.code, cli.code,
        "{context}: optional code differs at {location}"
    );
    assert_eq!(
        local.message, cli.message,
        "{context}: exact message differs at {location}"
    );
    assert_eq!(
        local.help, cli.help,
        "{context}: optional help differs at {location}"
    );
    assert_eq!(
        local.spanned, cli.spanned,
        "{context}: `spanned` differs at {location}"
    );
    assert_eq!(
        local.labels, cli.labels,
        "{context}: ordered exact labels differ at {location}"
    );
}

fn assert_safe_component(value: &str, description: &str, context: &str) {
    let mut components = Path::new(value).components();
    assert!(
        matches!(components.next(), Some(Component::Normal(_))) && components.next().is_none(),
        "{context}: {description} must be one relative path component, found `{value}`"
    );
}

fn assert_regular_file(path: &Path, context: &str) {
    let metadata = fs::symlink_metadata(path)
        .unwrap_or_else(|error| panic!("{context}: cannot inspect `{}`: {error}", path.display()));
    assert!(
        metadata.file_type().is_file(),
        "{context}: `{}` is missing, not a regular file, or a symlink",
        path.display()
    );
}

fn read_source(path: &Path, context: &str) -> String {
    fs::read_to_string(path)
        .unwrap_or_else(|error| panic!("{context}: cannot read `{}`: {error}", path.display()))
}

fn assert_source_unchanged(path: &Path, original: &str, context: &str) {
    let current = read_source(path, context);
    assert_eq!(
        current,
        original,
        "{context}: immutable fixture source changed during comparison: `{}`",
        path.display()
    );
}

fn assert_optional_source_unchanged(path: Option<&Path>, original: Option<&str>, context: &str) {
    match (path, original) {
        (Some(path), Some(original)) => assert_source_unchanged(path, original, context),
        (None, None) => {}
        _ => panic!("{context}: internal optional source/path mismatch"),
    }
}

fn context(fixture: &str, revision: &str) -> String {
    format!("fixture `{fixture}` from source revision `{revision}`")
}
