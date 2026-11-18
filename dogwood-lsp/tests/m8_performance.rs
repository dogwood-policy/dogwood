#![cfg(feature = "test-control")]

#[path = "support/lsp_process.rs"]
mod lsp_process;

use std::fs;
use std::hint::black_box;
use std::path::PathBuf;
use std::process::Command;
use std::str::FromStr;
use std::sync::atomic::{AtomicU64, Ordering};
use std::time::{Instant, SystemTime, UNIX_EPOCH};

use dogwood_lsp::analysis::{
    SemanticInput, analyze_event_schema, analyze_lexical, analyze_with_input,
};
use dogwood_lsp::diagnostics::{BundleDocuments, SourceDocument, project_frontend_outcome};
use dogwood_lsp::frontend::{BundleInput, validate_bundle};
use dogwood_lsp::project::path_to_file_uri;
use lsp_process::LspProcess;
use lsp_types::Uri;
use serde::Serialize;
use serde_json::json;

const POLICY: &str = include_str!("fixtures/dogwood/m3/all-optional-valid/policy.dw");
const ACTION_SCHEMA: &str =
    include_str!("fixtures/dogwood/m3/all-optional-valid/schema.cedarschema");
const EVENT_SCHEMA: &str = include_str!("fixtures/dogwood/m3/all-optional-valid/event.dwschema");
const PROVIDERS: &str = include_str!("fixtures/dogwood/m3/all-optional-valid/providers.json");
const MACROS: &str = include_str!("fixtures/dogwood/m3/all-optional-valid/macros.dw");
const INVALID_POLICY: &str = "permit(\u{1f600}";
const WARM_UPS: usize = 3;
const SAMPLES: usize = 10;
const TEST_BARRIER: &str = "dogwood/testBarrier";
const CHECK_SCRIPT: &str = include_str!("../scripts/check");
const PERFORMANCE_SCRIPT: &str = include_str!("../scripts/performance");
const CHECK_PERFORMANCE_COMMAND: &str =
    "./scripts/performance --output target/check-performance-report.json";
const DOGWOOD_SOURCE: &str = "workspace";

static TEMP_SEQUENCE: AtomicU64 = AtomicU64::new(0);

#[derive(Serialize)]
struct Report {
    schema_version: u64,
    dogwood_source: &'static str,
    generated_at_utc: String,
    generated_unix_seconds: u64,
    command: &'static str,
    build_profile: &'static str,
    warm_up_count: usize,
    sample_count: usize,
    system: SystemMetadata,
    workloads: Vec<Workload>,
}

#[derive(Serialize)]
struct SystemMetadata {
    os: &'static str,
    architecture: &'static str,
    cpu: String,
    logical_cpu_count: usize,
    rustc: String,
    cargo: String,
}

#[derive(Serialize)]
struct Workload {
    name: &'static str,
    fixture: &'static str,
    bytes: usize,
    lines: usize,
    output_kind: &'static str,
    output_count: usize,
    dependency_count: usize,
    warm_up_count: usize,
    sample_count: usize,
    elapsed_nanoseconds: ElapsedSummary,
}

#[derive(Serialize)]
struct ElapsedSummary {
    minimum: u64,
    median: u64,
    mean: u64,
    maximum: u64,
    total: u64,
}

#[derive(Clone, Copy)]
struct WorkloadMetadata {
    name: &'static str,
    fixture: &'static str,
    bytes: usize,
    lines: usize,
    output_kind: &'static str,
    dependency_count: usize,
}

struct Workspace {
    root: PathBuf,
}

impl Workspace {
    fn create() -> Self {
        let root = std::env::temp_dir().join(format!(
            "dogwood-lsp-m8-performance-{}-{}",
            std::process::id(),
            TEMP_SEQUENCE.fetch_add(1, Ordering::Relaxed)
        ));
        fs::create_dir(&root).expect("performance workspace should be created");
        fs::write(root.join("actions.cedarschema"), ACTION_SCHEMA).unwrap();
        fs::write(root.join("events.dwschema"), EVENT_SCHEMA).unwrap();
        fs::write(root.join("providers.json"), PROVIDERS).unwrap();
        fs::write(root.join("macros.dw"), MACROS).unwrap();
        fs::write(root.join("policy.dw"), POLICY).unwrap();
        Self { root }
    }

    fn uri(&self, relative: &str) -> String {
        path_to_file_uri(&self.root.join(relative))
            .expect("performance path should convert to a URI")
            .as_str()
            .to_owned()
    }

    fn root_uri(&self) -> String {
        path_to_file_uri(&self.root)
            .expect("performance root should convert to a URI")
            .as_str()
            .to_owned()
    }
}

impl Drop for Workspace {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.root);
    }
}

#[test]
fn complete_check_explicitly_runs_the_report_only_performance_suite() {
    assert_eq!(
        CHECK_SCRIPT
            .lines()
            .filter(|line| line.trim() == CHECK_PERFORMANCE_COMMAND)
            .count(),
        1,
        "scripts/check must run the report-only performance suite exactly once"
    );
}

#[test]
fn performance_wrapper_enables_the_test_control_feature() {
    let command = PERFORMANCE_SCRIPT
        .replace("\\\n", " ")
        .split_whitespace()
        .collect::<Vec<_>>()
        .join(" ");
    assert!(
        command.contains(
            "cargo test --manifest-path \"$workspace_root/Cargo.toml\" \
             -p dogwood-lsp --all-features --test m8_performance -j 2 \
             report_only_performance_baselines -- --ignored --exact"
        ),
        "scripts/performance must enable the feature-gated performance test"
    );
    assert!(
        PERFORMANCE_SCRIPT.contains("[[ -s \"$temporary\" ]]"),
        "scripts/performance must reject an empty report"
    );
}

#[test]
#[ignore = "report-only benchmark; run through ./scripts/performance"]
fn report_only_performance_baselines() {
    let output = std::env::var_os("DOGWOOD_PERFORMANCE_REPORT")
        .map(PathBuf::from)
        .expect("DOGWOOD_PERFORMANCE_REPORT must name the report output");
    let bundle = BundleInput {
        policy: POLICY,
        action_schema: ACTION_SCHEMA,
        event_schema: Some(EVENT_SCHEMA),
        providers: Some(PROVIDERS),
        macros: Some(MACROS),
    };
    let semantic = SemanticInput {
        policy: POLICY,
        event_schema: Some(EVENT_SCHEMA),
        providers: Some(PROVIDERS),
        macros: Some(MACROS),
    };
    let mut lexical_source = String::from("// lexical fallback \u{1f600}\r\n");
    for index in 0..16_384 {
        if index != 0 {
            lexical_source.push(' ');
        }
        lexical_source.push_str(if index % 2 == 0 { "+" } else { "123h" });
    }

    let mut workloads = Vec::new();
    workloads.push(benchmark(
        WorkloadMetadata {
            name: "lexical-fallback",
            fixture: "generated-unicode-crlf-long-line",
            bytes: lexical_source.len(),
            lines: line_count(&lexical_source),
            output_kind: "tokens",
            dependency_count: 0,
        },
        || {
            black_box(
                analyze_lexical(black_box(&lexical_source))
                    .expect("lexical workload should remain bounded"),
            )
            .len()
        },
    ));
    workloads.push(benchmark(
        WorkloadMetadata {
            name: "valid-policy-analysis",
            fixture: "m3/all-optional-valid/policy-semantic-inputs",
            bytes: semantic_bytes(&semantic),
            lines: semantic_lines(&semantic),
            output_kind: "tokens",
            dependency_count: 3,
        },
        || {
            black_box(
                analyze_with_input(black_box(&semantic))
                    .expect("policy analysis workload should succeed"),
            )
            .len()
        },
    ));
    workloads.push(benchmark(
        WorkloadMetadata {
            name: "valid-event-schema-analysis",
            fixture: "m3/all-optional-valid/event.dwschema",
            bytes: EVENT_SCHEMA.len(),
            lines: line_count(EVENT_SCHEMA),
            output_kind: "tokens",
            dependency_count: 0,
        },
        || {
            black_box(
                analyze_event_schema(black_box(EVENT_SCHEMA))
                    .expect("event schema workload should succeed"),
            )
            .len()
        },
    ));
    workloads.push(benchmark(
        WorkloadMetadata {
            name: "full-bundle-validation",
            fixture: "m3/all-optional-valid",
            bytes: bundle_bytes(&bundle),
            lines: bundle_lines(&bundle),
            output_kind: "diagnostics",
            dependency_count: 4,
        },
        || diagnostic_count(&black_box(validate_bundle(black_box(&bundle)))),
    ));

    let policy_uri = uri("file:///performance/policy.dw");
    let action_uri = uri("file:///performance/actions.cedarschema");
    let event_uri = uri("file:///performance/events.dwschema");
    let providers_uri = uri("file:///performance/providers.json");
    let macros_uri = uri("file:///performance/macros.dw");
    let invalid_bundle = BundleInput {
        policy: INVALID_POLICY,
        action_schema: ACTION_SCHEMA,
        event_schema: Some(EVENT_SCHEMA),
        providers: Some(PROVIDERS),
        macros: Some(MACROS),
    };
    workloads.push(benchmark(
        WorkloadMetadata {
            name: "invalid-diagnostics",
            fixture: "generated-unicode-eof-policy-with-all-inputs",
            bytes: bundle_bytes(&invalid_bundle),
            lines: bundle_lines(&invalid_bundle),
            output_kind: "diagnostics",
            dependency_count: 4,
        },
        || {
            let outcome = validate_bundle(black_box(&invalid_bundle));
            black_box(project_frontend_outcome(
                1,
                BundleDocuments {
                    policy: SourceDocument {
                        uri: &policy_uri,
                        text: INVALID_POLICY,
                    },
                    action_schema: SourceDocument {
                        uri: &action_uri,
                        text: ACTION_SCHEMA,
                    },
                    event_schema: Some(SourceDocument {
                        uri: &event_uri,
                        text: EVENT_SCHEMA,
                    }),
                    providers: Some(SourceDocument {
                        uri: &providers_uri,
                        text: PROVIDERS,
                    }),
                    macros: Some(SourceDocument {
                        uri: &macros_uri,
                        text: MACROS,
                    }),
                },
                outcome,
            ))
            .diagnostics
            .len()
        },
    ));

    let workspace = Workspace::create();
    let mut server = LspProcess::spawn_with_test_control();
    initialize(&mut server, &workspace);
    let workspace_policy_uri = workspace.uri("policy.dw");
    open(
        &mut server,
        &workspace.uri("actions.cedarschema"),
        "plaintext",
        1,
        ACTION_SCHEMA,
    );
    open(&mut server, &workspace_policy_uri, "dogwood", 1, POLICY);
    open(
        &mut server,
        &workspace.uri("long.dwschema"),
        "dogwood-event-schema",
        1,
        &lexical_source,
    );
    let scratch = format!("//{}\u{1f600}", "a".repeat(32 * 1024 - 6));
    let scratch_uri = workspace.uri("scratch.dwschema");
    open(
        &mut server,
        &scratch_uri,
        "dogwood-event-schema",
        1,
        &scratch,
    );
    barrier(&mut server, 1);
    server.take_queued_notifications();

    let mut request_id = 10_i64;
    workloads.push(benchmark(
        WorkloadMetadata {
            name: "utf16-token-encoding",
            fixture: "generated-unicode-crlf-long-line-over-stdio",
            bytes: lexical_source.len(),
            lines: line_count(&lexical_source),
            output_kind: "tokens",
            dependency_count: 0,
        },
        || {
            let id = request_id;
            request_id += 1;
            server.send_request(
                id,
                "textDocument/semanticTokens/full",
                Some(json!({
                    "textDocument": {"uri": workspace.uri("long.dwschema")}
                })),
            );
            server.receive_response(id)["result"]["data"]
                .as_array()
                .expect("semantic response must contain data")
                .len()
                / 5
        },
    ));

    let mut action_version = 1_i32;
    workloads.push(benchmark(
        WorkloadMetadata {
            name: "dependency-revalidation",
            fixture: "m3/all-optional-valid/action-change-full-bundle",
            bytes: bundle_bytes(&bundle),
            lines: bundle_lines(&bundle),
            output_kind: "diagnostics",
            dependency_count: 4,
        },
        || {
            action_version += 1;
            change_full(
                &mut server,
                &workspace.uri("actions.cedarschema"),
                action_version,
                ACTION_SCHEMA,
            );
            let id = request_id;
            request_id += 1;
            barrier(&mut server, id);
            let notifications = server.take_queued_notifications();
            assert_eq!(notifications.len(), 1);
            assert_eq!(
                notifications[0]["method"],
                "textDocument/publishDiagnostics"
            );
            assert_eq!(notifications[0]["params"]["uri"], workspace_policy_uri);
            assert_eq!(notifications[0]["params"]["version"], 1);
            notifications[0]["params"]["diagnostics"]
                .as_array()
                .expect("diagnostic publication should contain an array")
                .len()
        },
    ));

    let mut scratch_text = scratch;
    let mut scratch_version = 1_i32;
    let mut use_rocket = true;
    let scratch_bytes = scratch_text.len();
    let incremental_edits = benchmark(
        WorkloadMetadata {
            name: "incremental-edits",
            fixture: "generated-32k-event-schema-comment",
            bytes: scratch_text.len(),
            lines: 1,
            output_kind: "publications",
            dependency_count: 0,
        },
        || {
            scratch_version += 1;
            let end = scratch_text.encode_utf16().count() as u32;
            let start = end - 2;
            let replacement = if use_rocket { "\u{1f680}" } else { "\u{1f600}" };
            server.send_notification(
                "textDocument/didChange",
                Some(json!({
                    "textDocument": {
                        "uri": scratch_uri,
                        "version": scratch_version
                    },
                    "contentChanges": [{
                        "range": {
                            "start": {"line": 0, "character": start},
                            "end": {"line": 0, "character": end}
                        },
                        "rangeLength": end - start,
                        "text": replacement
                    }]
                })),
            );
            scratch_text.truncate(scratch_text.len() - '\u{1f600}'.len_utf8());
            scratch_text.push_str(replacement);
            assert_eq!(scratch_text.len(), scratch_bytes);
            use_rocket = !use_rocket;
            let id = request_id;
            request_id += 1;
            barrier(&mut server, id);
            let notifications = server.take_queued_notifications();
            assert_eq!(notifications.len(), 1);
            assert_eq!(
                notifications[0]["method"],
                "textDocument/publishDiagnostics"
            );
            assert_eq!(notifications[0]["params"]["uri"], scratch_uri);
            assert_eq!(notifications[0]["params"]["version"], scratch_version);
            assert!(
                notifications[0]["params"]["diagnostics"]
                    .as_array()
                    .is_some_and(Vec::is_empty)
            );
            notifications.len()
        },
    );
    assert_eq!(incremental_edits.output_count, 1);
    workloads.push(incremental_edits);

    server.send_request(request_id, "shutdown", None);
    server.expect_response(
        request_id,
        json!({"jsonrpc": "2.0", "id": request_id, "result": null}),
    );
    server.send_notification("exit", None);
    server.finish(0);

    let report = Report {
        schema_version: 1,
        dogwood_source: DOGWOOD_SOURCE,
        generated_at_utc: utc_timestamp(),
        generated_unix_seconds: SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .expect("system clock should be after Unix epoch")
            .as_secs(),
        command: "./scripts/performance --output <path>",
        build_profile: "cargo test (unoptimized + debuginfo)",
        warm_up_count: WARM_UPS,
        sample_count: SAMPLES,
        system: SystemMetadata {
            os: std::env::consts::OS,
            architecture: std::env::consts::ARCH,
            cpu: cpu_model(),
            logical_cpu_count: std::thread::available_parallelism()
                .map(usize::from)
                .unwrap_or(1),
            rustc: command_output("rustc", &["--version"]),
            cargo: command_output("cargo", &["--version"]),
        },
        workloads,
    };
    assert_report_metadata(
        &report,
        &[
            WorkloadMetadata {
                name: "lexical-fallback",
                fixture: "generated-unicode-crlf-long-line",
                bytes: lexical_source.len(),
                lines: line_count(&lexical_source),
                output_kind: "tokens",
                dependency_count: 0,
            },
            WorkloadMetadata {
                name: "valid-policy-analysis",
                fixture: "m3/all-optional-valid/policy-semantic-inputs",
                bytes: semantic_bytes(&semantic),
                lines: semantic_lines(&semantic),
                output_kind: "tokens",
                dependency_count: 3,
            },
            WorkloadMetadata {
                name: "valid-event-schema-analysis",
                fixture: "m3/all-optional-valid/event.dwschema",
                bytes: EVENT_SCHEMA.len(),
                lines: line_count(EVENT_SCHEMA),
                output_kind: "tokens",
                dependency_count: 0,
            },
            WorkloadMetadata {
                name: "full-bundle-validation",
                fixture: "m3/all-optional-valid",
                bytes: bundle_bytes(&bundle),
                lines: bundle_lines(&bundle),
                output_kind: "diagnostics",
                dependency_count: 4,
            },
            WorkloadMetadata {
                name: "invalid-diagnostics",
                fixture: "generated-unicode-eof-policy-with-all-inputs",
                bytes: bundle_bytes(&invalid_bundle),
                lines: bundle_lines(&invalid_bundle),
                output_kind: "diagnostics",
                dependency_count: 4,
            },
            WorkloadMetadata {
                name: "utf16-token-encoding",
                fixture: "generated-unicode-crlf-long-line-over-stdio",
                bytes: lexical_source.len(),
                lines: line_count(&lexical_source),
                output_kind: "tokens",
                dependency_count: 0,
            },
            WorkloadMetadata {
                name: "dependency-revalidation",
                fixture: "m3/all-optional-valid/action-change-full-bundle",
                bytes: bundle_bytes(&bundle),
                lines: bundle_lines(&bundle),
                output_kind: "diagnostics",
                dependency_count: 4,
            },
            WorkloadMetadata {
                name: "incremental-edits",
                fixture: "generated-32k-event-schema-comment",
                bytes: scratch_bytes,
                lines: line_count(&scratch_text),
                output_kind: "publications",
                dependency_count: 0,
            },
        ],
    );
    let bytes = serde_json::to_vec_pretty(&report).expect("performance report should serialize");
    fs::write(&output, bytes)
        .unwrap_or_else(|error| panic!("cannot write report `{}`: {error}", output.display()));
}

fn benchmark(metadata: WorkloadMetadata, mut operation: impl FnMut() -> usize) -> Workload {
    let mut output_count = None;
    for _ in 0..WARM_UPS {
        let count = black_box(operation());
        if let Some(expected) = output_count {
            assert_eq!(count, expected, "{} output count changed", metadata.name);
        } else {
            output_count = Some(count);
        }
    }

    let mut samples = Vec::with_capacity(SAMPLES);
    for _ in 0..SAMPLES {
        let started = Instant::now();
        let count = black_box(operation());
        let elapsed = started.elapsed().as_nanos() as u64;
        assert_eq!(
            Some(count),
            output_count,
            "{} output count changed",
            metadata.name
        );
        samples.push(elapsed);
    }
    samples.sort_unstable();
    let total = samples.iter().sum();
    let elapsed_nanoseconds = ElapsedSummary {
        minimum: samples[0],
        median: samples[SAMPLES / 2],
        mean: total / SAMPLES as u64,
        maximum: samples[SAMPLES - 1],
        total,
    };
    Workload {
        name: metadata.name,
        fixture: metadata.fixture,
        bytes: metadata.bytes,
        lines: metadata.lines,
        output_kind: metadata.output_kind,
        output_count: output_count.expect("warmup count should exist"),
        dependency_count: metadata.dependency_count,
        warm_up_count: WARM_UPS,
        sample_count: SAMPLES,
        elapsed_nanoseconds,
    }
}

fn assert_report_metadata(report: &Report, expected: &[WorkloadMetadata]) {
    assert_eq!(report.schema_version, 1);
    assert_eq!(report.dogwood_source, DOGWOOD_SOURCE);
    assert!(!report.generated_at_utc.is_empty());
    assert!(report.generated_unix_seconds > 0);
    assert_eq!(report.command, "./scripts/performance --output <path>");
    assert_eq!(report.build_profile, "cargo test (unoptimized + debuginfo)");
    assert_eq!(report.warm_up_count, WARM_UPS);
    assert_eq!(report.sample_count, SAMPLES);
    assert!(!report.system.os.is_empty());
    assert!(!report.system.architecture.is_empty());
    assert!(!report.system.cpu.is_empty());
    assert!(report.system.logical_cpu_count > 0);
    assert!(!report.system.rustc.is_empty());
    assert!(!report.system.cargo.is_empty());
    assert_eq!(report.workloads.len(), expected.len());

    for (workload, expected) in report.workloads.iter().zip(expected) {
        assert_eq!(workload.name, expected.name);
        assert_eq!(
            workload.fixture, expected.fixture,
            "{} fixture",
            workload.name
        );
        assert_eq!(workload.bytes, expected.bytes, "{} bytes", workload.name);
        assert_eq!(workload.lines, expected.lines, "{} lines", workload.name);
        assert_eq!(
            workload.output_kind, expected.output_kind,
            "{} output kind",
            workload.name
        );
        assert_eq!(
            workload.dependency_count, expected.dependency_count,
            "{} dependency count",
            workload.name
        );
        assert_eq!(workload.warm_up_count, WARM_UPS);
        assert_eq!(workload.sample_count, SAMPLES);
        assert!(workload.elapsed_nanoseconds.minimum > 0);
        assert!(
            workload.elapsed_nanoseconds.minimum <= workload.elapsed_nanoseconds.median
                && workload.elapsed_nanoseconds.median <= workload.elapsed_nanoseconds.maximum
        );
        assert_eq!(
            workload.elapsed_nanoseconds.mean,
            workload.elapsed_nanoseconds.total / SAMPLES as u64
        );
    }
}

fn diagnostic_count(
    outcome: &dogwood_lsp::frontend::FrontendOutcome<dogwood_lsp::frontend::ValidationReport>,
) -> usize {
    match outcome {
        dogwood_lsp::frontend::FrontendOutcome::Report(report) => {
            report.errors.len() + report.warnings.len()
        }
        dogwood_lsp::frontend::FrontendOutcome::Fatal(fatal) => 1 + fatal.related.len(),
        dogwood_lsp::frontend::FrontendOutcome::OperationalLimit(_) => 1,
    }
}

fn bundle_bytes(bundle: &BundleInput<'_>) -> usize {
    bundle.policy.len()
        + bundle.action_schema.len()
        + bundle.event_schema.map_or(0, str::len)
        + bundle.providers.map_or(0, str::len)
        + bundle.macros.map_or(0, str::len)
}

fn bundle_lines(bundle: &BundleInput<'_>) -> usize {
    line_count(bundle.policy)
        + line_count(bundle.action_schema)
        + bundle.event_schema.map_or(0, line_count)
        + bundle.providers.map_or(0, line_count)
        + bundle.macros.map_or(0, line_count)
}

fn semantic_bytes(input: &SemanticInput<'_>) -> usize {
    input.policy.len()
        + input.event_schema.map_or(0, str::len)
        + input.providers.map_or(0, str::len)
        + input.macros.map_or(0, str::len)
}

fn semantic_lines(input: &SemanticInput<'_>) -> usize {
    line_count(input.policy)
        + input.event_schema.map_or(0, line_count)
        + input.providers.map_or(0, line_count)
        + input.macros.map_or(0, line_count)
}

fn line_count(source: &str) -> usize {
    source.bytes().filter(|byte| *byte == b'\n').count() + 1
}

fn initialize(server: &mut LspProcess, workspace: &Workspace) {
    server.send_request(
        0,
        "initialize",
        Some(json!({
            "capabilities": {},
            "rootUri": workspace.root_uri()
        })),
    );
    server.receive_response(0);
    server.send_notification("initialized", Some(json!({})));
}

fn open(server: &mut LspProcess, uri: &str, language_id: &str, version: i32, text: &str) {
    server.send_notification(
        "textDocument/didOpen",
        Some(json!({
            "textDocument": {
                "uri": uri,
                "languageId": language_id,
                "version": version,
                "text": text
            }
        })),
    );
}

fn change_full(server: &mut LspProcess, uri: &str, version: i32, text: &str) {
    server.send_notification(
        "textDocument/didChange",
        Some(json!({
            "textDocument": {"uri": uri, "version": version},
            "contentChanges": [{"text": text}]
        })),
    );
}

fn barrier(server: &mut LspProcess, id: i64) {
    server.send_request(id, TEST_BARRIER, Some(json!({})));
    let response = server.receive_response(id);
    assert_eq!(response["error"]["code"], -32601);
}

fn cpu_model() -> String {
    if let Ok(cpuinfo) = fs::read_to_string("/proc/cpuinfo") {
        for key in ["model name", "Hardware"] {
            if let Some(model) = cpuinfo.lines().find_map(|line| {
                line.strip_prefix(key)
                    .and_then(|rest| rest.split_once(':'))
                    .map(|(_, value)| value.trim().to_owned())
            }) {
                return model;
            }
        }
        let field = |name: &str| {
            cpuinfo.lines().find_map(|line| {
                line.strip_prefix(name)
                    .and_then(|rest| rest.split_once(':'))
                    .map(|(_, value)| value.trim().to_owned())
            })
        };
        if let (Some(implementer), Some(part)) = (field("CPU implementer"), field("CPU part")) {
            return format!("ARM implementer {implementer}, part {part}");
        }
    }
    let model = command_output("sysctl", &["-n", "machdep.cpu.brand_string"]);
    if model.starts_with("<unavailable:") {
        "unknown".to_owned()
    } else {
        model
    }
}

fn utc_timestamp() -> String {
    command_output("date", &["-u", "+%Y-%m-%dT%H:%M:%SZ"])
}

fn command_output(program: &str, arguments: &[&str]) -> String {
    match Command::new(program).args(arguments).output() {
        Ok(output) if output.status.success() => {
            String::from_utf8_lossy(&output.stdout).trim().to_owned()
        }
        Ok(output) => format!("<unavailable: {program} exited {}>", output.status),
        Err(error) => format!("<unavailable: {program}: {error}>"),
    }
}

fn uri(value: &str) -> Uri {
    Uri::from_str(value).expect("performance URI should be valid")
}
