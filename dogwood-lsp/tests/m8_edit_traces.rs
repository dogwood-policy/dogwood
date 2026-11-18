#![cfg(feature = "test-control")]

#[path = "support/lsp_process.rs"]
mod lsp_process;

use std::collections::{BTreeMap, BTreeSet};
use std::fs;
use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicU64, Ordering};

use dogwood_lsp::project::path_to_file_uri;
use lsp_process::LspProcess;
use serde_json::{Value, json};

const POLICY: &str = include_str!("fixtures/dogwood/m3/all-optional-valid/policy.dw");
const ACTION_SCHEMA: &str =
    include_str!("fixtures/dogwood/m3/all-optional-valid/schema.cedarschema");
const EVENT_SCHEMA: &str = include_str!("fixtures/dogwood/m3/all-optional-valid/event.dwschema");
const PROVIDERS: &str = include_str!("fixtures/dogwood/m3/all-optional-valid/providers.json");
const MACROS: &str = include_str!("fixtures/dogwood/m3/all-optional-valid/macros.dw");
const PREFIX: &str = "// seeded trace \u{1f600}\r\n";
const TEST_BARRIER: &str = "dogwood/testBarrier";
const PUBLISH_DIAGNOSTICS: &str = "textDocument/publishDiagnostics";
const TRACE_SEED: u64 = 0xD06D_0008_C623_7C88;

static TEMP_SEQUENCE: AtomicU64 = AtomicU64::new(0);

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
enum Source {
    Policy,
    ActionSchema,
    EventSchema,
    Providers,
    Macros,
}

impl Source {
    const ALL: [Self; 5] = [
        Self::Policy,
        Self::ActionSchema,
        Self::EventSchema,
        Self::Providers,
        Self::Macros,
    ];

    const fn relative(self) -> &'static str {
        match self {
            Self::Policy => "policy.dw",
            Self::ActionSchema => "actions.cedarschema",
            Self::EventSchema => "events.dwschema",
            Self::Providers => "providers.json",
            Self::Macros => "macro-library.txt",
        }
    }

    const fn language_id(self) -> &'static str {
        match self {
            Self::EventSchema => "dogwood-event-schema",
            Self::Policy => "dogwood",
            Self::ActionSchema | Self::Providers | Self::Macros => "plaintext",
        }
    }

    const fn initial(self) -> &'static str {
        match self {
            Self::Policy => POLICY,
            Self::ActionSchema => ACTION_SCHEMA,
            Self::EventSchema => EVENT_SCHEMA,
            Self::Providers => PROVIDERS,
            Self::Macros => MACROS,
        }
    }

    const fn invalid_suffix(self) -> &'static str {
        match self {
            Self::Policy => "\npermit(",
            Self::ActionSchema => "\nnot cedar",
            Self::EventSchema => "\ndecision event <A>::broken {",
            Self::Providers => "\nnot-json",
            Self::Macros => "\ndef cedar broken(x) { true };",
        }
    }
}

struct Workspace {
    root: PathBuf,
}

impl Workspace {
    fn create(label: &str) -> Self {
        let root = std::env::temp_dir().join(format!(
            "dogwood-lsp-m8-trace-{label}-{}-{}",
            std::process::id(),
            TEMP_SEQUENCE.fetch_add(1, Ordering::Relaxed)
        ));
        fs::create_dir(&root).expect("trace workspace should be created");
        for source in Source::ALL {
            fs::write(root.join(source.relative()), source.initial())
                .expect("trace fixture should be written");
        }
        fs::write(
            root.join("unrelated.dwschema"),
            "event <A>::unrelated { value: String, }\n",
        )
        .expect("unrelated schema should be written");
        Self { root }
    }

    fn uri(&self, source: Source) -> String {
        uri(&self.root.join(source.relative()))
    }

    fn root_uri(&self) -> String {
        uri(&self.root)
    }
}

impl Drop for Workspace {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.root);
    }
}

struct Endpoint {
    workspace: Workspace,
    server: LspProcess,
}

impl Endpoint {
    fn start(label: &str) -> Self {
        let workspace = Workspace::create(label);
        let mut server = LspProcess::spawn_with_test_control();
        let root_uri = workspace.root_uri();
        server.send_request(
            0,
            "initialize",
            Some(json!({
                "capabilities": {},
                "rootUri": root_uri,
                "initializationOptions": {
                    "bundles": [{
                        "workspaceFolder": root_uri,
                        "actionSchema": Source::ActionSchema.relative(),
                        "eventSchema": Source::EventSchema.relative(),
                        "providers": Source::Providers.relative(),
                        "macros": Source::Macros.relative()
                    }]
                }
            })),
        );
        let response = server.receive_response(0);
        assert_eq!(
            response["result"]["capabilities"]["textDocumentSync"]["change"],
            2
        );
        server.send_notification("initialized", Some(json!({})));
        Self { workspace, server }
    }

    fn open(&mut self, source: Source, version: i32, text: &str) {
        self.server.send_notification(
            "textDocument/didOpen",
            Some(json!({
                "textDocument": {
                    "uri": self.workspace.uri(source),
                    "languageId": source.language_id(),
                    "version": version,
                    "text": text
                }
            })),
        );
    }

    fn close(&mut self, source: Source) {
        self.server.send_notification(
            "textDocument/didClose",
            Some(json!({
                "textDocument": {"uri": self.workspace.uri(source)}
            })),
        );
    }

    fn full_change(&mut self, source: Source, version: i32, text: &str) {
        self.server.send_notification(
            "textDocument/didChange",
            Some(json!({
                "textDocument": {
                    "uri": self.workspace.uri(source),
                    "version": version
                },
                "contentChanges": [{"text": text}]
            })),
        );
    }

    fn range_change(
        &mut self,
        source: Source,
        version: i32,
        old: &str,
        start: usize,
        end: usize,
        replacement: &str,
    ) {
        let start_position = position(old, start);
        let end_position = position(old, end);
        let range_length = old[start..end].encode_utf16().count() as u32;
        self.server.send_notification(
            "textDocument/didChange",
            Some(json!({
                "textDocument": {
                    "uri": self.workspace.uri(source),
                    "version": version
                },
                "contentChanges": [{
                    "range": {
                        "start": start_position,
                        "end": end_position
                    },
                    "rangeLength": range_length,
                    "text": replacement
                }]
            })),
        );
    }

    fn watched(&mut self, source: Source, typ: i32) {
        self.server.send_notification(
            "workspace/didChangeWatchedFiles",
            Some(json!({
                "changes": [{
                    "uri": self.workspace.uri(source),
                    "type": typ
                }]
            })),
        );
    }
}

struct Model {
    texts: BTreeMap<Source, String>,
    versions: BTreeMap<Source, i32>,
    open: BTreeSet<Source>,
    prefixed: BTreeSet<Source>,
    invalid: BTreeSet<Source>,
}

impl Model {
    fn new() -> Self {
        Self {
            texts: Source::ALL
                .into_iter()
                .map(|source| (source, source.initial().to_owned()))
                .collect(),
            versions: Source::ALL.into_iter().map(|source| (source, 1)).collect(),
            open: BTreeSet::new(),
            prefixed: BTreeSet::new(),
            invalid: BTreeSet::new(),
        }
    }

    fn text(&self, source: Source) -> &str {
        &self.texts[&source]
    }

    fn next_version(&mut self, source: Source) -> i32 {
        let version = self
            .versions
            .get_mut(&source)
            .expect("every source has a version");
        *version += 1;
        *version
    }
}

struct Trace {
    incremental: Endpoint,
    reference: Endpoint,
    model: Model,
    next_request: i64,
}

impl Trace {
    fn start() -> Self {
        Self {
            incremental: Endpoint::start("incremental"),
            reference: Endpoint::start("reference"),
            model: Model::new(),
            next_request: 1,
        }
    }

    fn initialize_documents(&mut self) {
        for source in [
            Source::ActionSchema,
            Source::EventSchema,
            Source::Providers,
            Source::Policy,
            Source::Macros,
        ] {
            let text = self.model.text(source).to_owned();
            self.incremental.open(source, 1, &text);
            self.reference.open(source, 1, &text);
            self.model.open.insert(source);
        }
        self.settle("initial open", None);
        self.compare_tokens();
    }

    fn toggle_prefix(&mut self, source: Source) {
        assert!(self.model.open.contains(&source));
        let old = self.model.text(source).to_owned();
        let (start, end, replacement, new) = if self.model.prefixed.remove(&source) {
            assert!(old.starts_with(PREFIX));
            (0, PREFIX.len(), "", old[PREFIX.len()..].to_owned())
        } else {
            self.model.prefixed.insert(source);
            (0, 0, PREFIX, format!("{PREFIX}{old}"))
        };
        let version = self.model.next_version(source);
        self.incremental
            .range_change(source, version, &old, start, end, replacement);
        self.reference.full_change(source, version, &new);
        self.model.texts.insert(source, new);
        self.settle(
            &format!("prefix {source:?}"),
            Some(expected_publications(source)),
        );
        self.compare_tokens();
    }

    fn toggle_invalid_suffix(&mut self, source: Source) {
        assert!(self.model.open.contains(&source));
        let old = self.model.text(source).to_owned();
        let suffix = source.invalid_suffix();
        let (start, end, replacement, new, now_invalid) = if self.model.invalid.remove(&source) {
            assert!(old.ends_with(suffix));
            let start = old.len() - suffix.len();
            (start, old.len(), "", old[..start].to_owned(), false)
        } else {
            self.model.invalid.insert(source);
            (old.len(), old.len(), suffix, format!("{old}{suffix}"), true)
        };
        let version = self.model.next_version(source);
        self.incremental
            .range_change(source, version, &old, start, end, replacement);
        self.reference.full_change(source, version, &new);
        self.model.texts.insert(source, new);
        let publications = self.settle(
            &format!("invalid suffix {source:?}"),
            Some(expected_publications(source)),
        );
        for publication in publications {
            let relative = publication_relative(&publication);
            let should_be_nonempty =
                now_invalid && matches!(relative, "policy.dw" | "events.dwschema");
            assert_eq!(
                publication["params"]["diagnostics"]
                    .as_array()
                    .expect("diagnostics must be an array")
                    .is_empty(),
                !should_be_nonempty,
                "seed={TRACE_SEED:#x}: invalid/recovery cleanliness for {source:?}/{relative}"
            );
        }
        self.compare_tokens();
    }

    fn close(&mut self, source: Source) {
        assert!(self.model.open.remove(&source));
        self.incremental.close(source);
        self.reference.close(source);
        self.settle(
            &format!("close {source:?}"),
            Some(expected_publications(source)),
        );
        self.compare_tokens();
    }

    fn open(&mut self, source: Source) {
        assert!(self.model.open.insert(source));
        let text = self.model.text(source).to_owned();
        let version = self.model.next_version(source);
        self.incremental.open(source, version, &text);
        self.reference.open(source, version, &text);
        self.settle(
            &format!("reopen {source:?}"),
            Some(expected_publications(source)),
        );
        self.compare_tokens();
    }

    fn delete_disk(&mut self, source: Source) {
        assert!(!self.model.open.contains(&source));
        fs::remove_file(self.incremental.workspace.root.join(source.relative()))
            .expect("incremental dependency should be deleted");
        fs::remove_file(self.reference.workspace.root.join(source.relative()))
            .expect("reference dependency should be deleted");
        self.incremental.watched(source, 3);
        self.reference.watched(source, 3);
        let publications = self.settle(
            &format!("delete disk {source:?}"),
            Some(BTreeSet::from([Source::Policy.relative()])),
        );
        assert!(
            publications[0]["params"]["diagnostics"]
                .as_array()
                .is_some_and(|diagnostics| !diagnostics.is_empty()),
            "required action schema deletion must not produce a clean policy"
        );
        self.compare_tokens();
    }

    fn create_disk(&mut self, source: Source) {
        assert!(!self.model.open.contains(&source));
        fs::write(
            self.incremental.workspace.root.join(source.relative()),
            source.initial(),
        )
        .expect("incremental dependency should be created");
        fs::write(
            self.reference.workspace.root.join(source.relative()),
            source.initial(),
        )
        .expect("reference dependency should be created");
        self.incremental.watched(source, 1);
        self.reference.watched(source, 1);
        self.model.texts.insert(source, source.initial().to_owned());
        self.model.prefixed.remove(&source);
        self.model.invalid.remove(&source);
        let publications = self.settle(
            &format!("create disk {source:?}"),
            Some(BTreeSet::from([Source::Policy.relative()])),
        );
        assert!(
            publications[0]["params"]["diagnostics"]
                .as_array()
                .is_some_and(Vec::is_empty),
            "required action schema recovery must clear policy diagnostics"
        );
        self.compare_tokens();
    }

    fn settle(&mut self, label: &str, expected: Option<BTreeSet<&'static str>>) -> Vec<Value> {
        let request = self.next_request;
        self.next_request += 1;
        barrier(&mut self.incremental.server, request);
        barrier(&mut self.reference.server, request);

        let incremental = self.incremental.server.take_queued_notifications();
        let reference = self.reference.server.take_queued_notifications();
        let incremental = normalize_messages(
            incremental,
            &self.incremental.workspace.root,
            &self.incremental.workspace.root_uri(),
        );
        let reference = normalize_messages(
            reference,
            &self.reference.workspace.root,
            &self.reference.workspace.root_uri(),
        );
        assert_eq!(
            incremental, reference,
            "seed={TRACE_SEED:#x} step={label}: incremental publications differ from full reference"
        );
        for notification in &incremental {
            assert_eq!(
                notification["method"], PUBLISH_DIAGNOSTICS,
                "seed={TRACE_SEED:#x} step={label}: unexpected notification"
            );
            let relative = publication_relative(notification);
            assert_eq!(
                notification["params"]["version"],
                self.expected_version(relative),
                "seed={TRACE_SEED:#x} step={label}: stale diagnostic version for {relative}"
            );
        }
        if let Some(expected) = expected {
            let actual = incremental
                .iter()
                .map(publication_relative)
                .collect::<BTreeSet<_>>();
            assert_eq!(
                actual, expected,
                "seed={TRACE_SEED:#x} step={label}: stale or surplus publications"
            );
            assert_eq!(
                incremental.len(),
                expected.len(),
                "seed={TRACE_SEED:#x} step={label}: duplicate publication"
            );
        }
        self.incremental.server.assert_no_queued_server_messages();
        self.reference.server.assert_no_queued_server_messages();
        incremental
    }

    fn expected_version(&self, relative: &str) -> Value {
        let source = Source::ALL
            .into_iter()
            .find(|source| source.relative() == relative)
            .expect("publication must identify a tracked source");
        Value::from(self.model.versions[&source])
    }

    fn compare_tokens(&mut self) {
        for source in [Source::Policy, Source::EventSchema] {
            if !self.model.open.contains(&source) {
                continue;
            }
            let request = self.next_request;
            self.next_request += 1;
            let incremental = request_tokens(&mut self.incremental, request, source);
            let reference = request_tokens(&mut self.reference, request, source);
            assert_eq!(
                incremental, reference,
                "seed={TRACE_SEED:#x}: incremental tokens differ for {source:?}"
            );
            assert_token_data(&incremental);
        }
    }

    fn finish(mut self) {
        let request = self.next_request;
        shutdown(&mut self.incremental.server, request);
        shutdown(&mut self.reference.server, request);
        self.incremental.server.finish(0);
        self.reference.server.finish(0);
    }
}

#[test]
fn seeded_incremental_and_dependency_trace_matches_a_full_bundle_reference_after_every_step() {
    let mut trace = Trace::start();
    trace.initialize_documents();

    for source in Source::ALL {
        trace.toggle_invalid_suffix(source);
        trace.toggle_invalid_suffix(source);
    }

    trace.close(Source::EventSchema);
    trace.open(Source::EventSchema);
    trace.close(Source::ActionSchema);
    trace.delete_disk(Source::ActionSchema);
    trace.create_disk(Source::ActionSchema);
    trace.open(Source::ActionSchema);

    let mut random = Lcg::new(TRACE_SEED);
    for _ in 0..24 {
        let source = Source::ALL[(random.next() as usize) % Source::ALL.len()];
        trace.toggle_prefix(source);
    }

    trace.close(Source::Macros);
    trace.close(Source::Policy);
    trace.open(Source::Policy);
    trace.open(Source::Macros);
    trace.finish();
}

fn expected_publications(source: Source) -> BTreeSet<&'static str> {
    match source {
        Source::EventSchema => {
            BTreeSet::from([Source::EventSchema.relative(), Source::Policy.relative()])
        }
        Source::Policy | Source::ActionSchema | Source::Providers | Source::Macros => {
            BTreeSet::from([Source::Policy.relative()])
        }
    }
}

fn barrier(server: &mut LspProcess, id: i64) {
    server.send_request(id, TEST_BARRIER, Some(json!({})));
    let response = server.receive_response(id);
    assert_eq!(response["error"]["code"], -32601);
    assert_eq!(response["error"]["message"], "Method not found");
}

fn request_tokens(endpoint: &mut Endpoint, id: i64, source: Source) -> Value {
    endpoint.server.send_request(
        id,
        "textDocument/semanticTokens/full",
        Some(json!({
            "textDocument": {"uri": endpoint.workspace.uri(source)}
        })),
    );
    endpoint.server.receive_response(id)
}

fn assert_token_data(response: &Value) {
    let data = response["result"]["data"]
        .as_array()
        .expect("semantic response must contain data");
    assert_eq!(data.len() % 5, 0);
    let mut line = 0_u64;
    let mut start = 0_u64;
    let mut previous = None;
    for token in data.as_chunks::<5>().0 {
        let delta_line = token[0].as_u64().unwrap();
        let delta_start = token[1].as_u64().unwrap();
        line += delta_line;
        start = if delta_line == 0 {
            start + delta_start
        } else {
            delta_start
        };
        let length = token[2].as_u64().unwrap();
        let token_type = token[3].as_u64().unwrap();
        let modifiers = token[4].as_u64().unwrap();
        assert!(length > 0);
        assert!(token_type < 19);
        assert!(modifiers <= 1);
        if let Some((previous_line, previous_start, previous_length)) = previous {
            assert!(
                line > previous_line
                    || (line == previous_line && start >= previous_start + previous_length)
            );
        }
        previous = Some((line, start, length));
    }
}

fn shutdown(server: &mut LspProcess, id: i64) {
    server.send_request(id, "shutdown", None);
    server.expect_response(id, json!({"jsonrpc": "2.0", "id": id, "result": null}));
    server.send_notification("exit", None);
}

fn normalize_messages(mut messages: Vec<Value>, root: &Path, root_uri: &str) -> Vec<Value> {
    let root = root.to_string_lossy();
    for message in &mut messages {
        normalize_value(message, &root, root_uri);
    }
    messages
}

fn normalize_value(value: &mut Value, root: &str, root_uri: &str) {
    match value {
        Value::String(text) => {
            *text = text.replace(root_uri, "file://<ROOT>");
            *text = text.replace(root, "<ROOT>");
        }
        Value::Array(values) => {
            for value in values {
                normalize_value(value, root, root_uri);
            }
        }
        Value::Object(fields) => {
            for value in fields.values_mut() {
                normalize_value(value, root, root_uri);
            }
        }
        Value::Null | Value::Bool(_) | Value::Number(_) => {}
    }
}

fn publication_relative(notification: &Value) -> &str {
    notification["params"]["uri"]
        .as_str()
        .and_then(|uri| uri.rsplit('/').next())
        .expect("publication URI should have a relative name")
}

fn position(source: &str, offset: usize) -> Value {
    assert!(source.is_char_boundary(offset));
    let prefix = &source[..offset];
    let line = prefix.bytes().filter(|byte| *byte == b'\n').count() as u32;
    let line_start = prefix.rfind('\n').map_or(0, |index| index + 1);
    let character = source[line_start..offset].encode_utf16().count() as u32;
    json!({"line": line, "character": character})
}

fn uri(path: &Path) -> String {
    path_to_file_uri(path)
        .expect("temporary path should convert to a URI")
        .as_str()
        .to_owned()
}

struct Lcg(u64);

impl Lcg {
    const fn new(seed: u64) -> Self {
        Self(seed)
    }

    fn next(&mut self) -> u64 {
        self.0 = self
            .0
            .wrapping_mul(6_364_136_223_846_793_005)
            .wrapping_add(1_442_695_040_888_963_407);
        self.0
    }
}
