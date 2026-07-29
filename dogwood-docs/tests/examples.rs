//! Runs every documentation example bundle through the `dogwood` CLI.
//!
//! Each subdirectory of `examples/` is one bundle. A bundle always has a policy
//! and an action schema; it may additionally carry an event schema, provider
//! declarations, a trace, and an expected verdict stream. The harness:
//!
//!   1. builds the `dogwood` binary once (via escargot — `CARGO_BIN_EXE_*` is
//!      not set for a separate crate's tests);
//!   2. `dogwood validate`s every bundle, asserting a clean exit (the example
//!      parses, lowers, and type-checks);
//!   3. for every bundle that ships a trace, `dogwood replay`s it and asserts
//!      the verdict stream matches `expected.out` byte-for-byte.
//!
//! A documentation example that no longer parses, validates, or replays as
//! written fails this test — the guide cannot drift from the language.
//!
//! ## Bundle layout
//!
//! ```text
//! examples/<name>/
//!   policy.dw          (required) the Dogwood policy
//!   schema.cedarschema (required) the Cedar action schema  → --policy-schema
//!   events.dwschema    (optional) event-schema DSL          → --event-schema
//!   providers.json     (optional) provider declarations     → --providers
//!   macros.dw          (optional) macro library             → --macros
//!   trace.log          (optional) event trace               → replay --trace
//!   expected.out       (required iff trace.log) the verdict stream to match
//!   README.md          (optional) what the example shows (ignored by the harness)
//! ```

use std::path::{Path, PathBuf};
use std::process::Command;
use std::sync::OnceLock;

use escargot::CargoBuild;

/// Build the `dogwood` binary once for the whole test run and cache its path.
/// escargot resolves the binary from the `amzn-dogwood-cli` package regardless
/// of profile or target-dir, which `CARGO_BIN_EXE_*` cannot do across crates.
fn dogwood_bin() -> &'static Path {
    static BIN: OnceLock<PathBuf> = OnceLock::new();
    BIN.get_or_init(|| {
        let run = CargoBuild::new()
            .bin("dogwood")
            .package("amzn-dogwood-cli")
            .run()
            .expect("build the `dogwood` binary");
        run.path().to_path_buf()
    })
}

/// The `examples/` root, resolved from this crate's manifest dir.
fn examples_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("examples")
}

/// One discovered example bundle: its name and the files it carries.
struct Bundle {
    name: String,
    dir: PathBuf,
}

impl Bundle {
    fn policy(&self) -> PathBuf {
        self.dir.join("policy.dw")
    }
    fn schema(&self) -> PathBuf {
        self.dir.join("schema.cedarschema")
    }
    /// An optional bundle file, returned only if it exists on disk.
    fn optional(&self, name: &str) -> Option<PathBuf> {
        let p = self.dir.join(name);
        p.exists().then_some(p)
    }
    fn trace(&self) -> Option<PathBuf> {
        self.optional("trace.log")
    }

    /// Append the optional service-schema flags this bundle carries
    /// (`--event-schema`, `--providers`, `--macros`) to a command. The event
    /// schema is accepted under either `events.dwschema` or `event.dwschema`.
    fn push_schema_flags(&self, cmd: &mut Command) {
        if let Some(p) = self
            .optional("events.dwschema")
            .or_else(|| self.optional("event.dwschema"))
        {
            cmd.arg("--event-schema").arg(p);
        }
        if let Some(p) = self.optional("providers.json") {
            cmd.arg("--providers").arg(p);
        }
        if let Some(p) = self.optional("macros.dw") {
            cmd.arg("--macros").arg(p);
        }
    }
}

/// Discover every bundle: a subdirectory of `examples/` that contains a
/// `policy.dw`. (A bare `examples/README.md` or other files are ignored.)
fn discover() -> Vec<Bundle> {
    let root = examples_root();
    if !root.exists() {
        return Vec::new();
    }
    let mut bundles: Vec<Bundle> = std::fs::read_dir(&root)
        .expect("read examples/")
        .filter_map(|e| e.ok())
        .map(|e| e.path())
        .filter(|p| p.is_dir() && p.join("policy.dw").exists())
        .map(|dir| Bundle {
            name: dir.file_name().unwrap().to_string_lossy().into_owned(),
            dir,
        })
        .collect();
    bundles.sort_by(|a, b| a.name.cmp(&b.name));
    bundles
}

/// Every bundle must at least have the two required files, and a trace and its
/// expected output must come as a pair. Returns a problem string, or `None`.
fn well_formed_problem(b: &Bundle) -> Option<String> {
    if !b.schema().exists() {
        return Some(format!("`{}`: missing schema.cedarschema", b.name));
    }
    let has_trace = b.trace().is_some();
    let has_expected = b.optional("expected.out").is_some();
    if has_trace != has_expected {
        return Some(format!(
            "`{}`: trace.log and expected.out must both be present or both absent",
            b.name
        ));
    }
    None
}

/// `dogwood validate policy.dw --policy-schema schema.cedarschema [flags]` must
/// exit 0 — the example parses, lowers, and type-checks. Returns a failure
/// description, or `None` on success.
fn validate_problem(bin: &Path, b: &Bundle) -> Option<String> {
    let mut cmd = Command::new(bin);
    cmd.arg("validate")
        .arg(b.policy())
        .arg("--policy-schema")
        .arg(b.schema());
    b.push_schema_flags(&mut cmd);
    let out = cmd.output().expect("run dogwood validate");
    if out.status.success() {
        return None;
    }
    Some(format!(
        "`{}`: `dogwood validate` failed (exit {:?})\n--- stdout ---\n{}\n--- stderr ---\n{}",
        b.name,
        out.status.code(),
        String::from_utf8_lossy(&out.stdout),
        String::from_utf8_lossy(&out.stderr),
    ))
}

/// For a bundle with a trace: `dogwood replay …` stdout must equal
/// `expected.out` (after trimming trailing whitespace). Returns a failure
/// description, or `None` on success / no trace.
fn replay_problem(bin: &Path, b: &Bundle) -> Option<String> {
    let trace = b.trace()?;
    let expected = std::fs::read_to_string(b.dir.join("expected.out")).expect("read expected.out");

    let mut cmd = Command::new(bin);
    cmd.arg("replay")
        .arg(b.policy())
        .arg("--policy-schema")
        .arg(b.schema())
        .arg("--trace")
        .arg(trace);
    b.push_schema_flags(&mut cmd);
    let out = cmd.output().expect("run dogwood replay");
    if !out.status.success() {
        return Some(format!(
            "`{}`: `dogwood replay` failed (exit {:?})\n{}",
            b.name,
            out.status.code(),
            String::from_utf8_lossy(&out.stderr),
        ));
    }
    let actual = String::from_utf8_lossy(&out.stdout);
    if actual.trim_end() != expected.trim_end() {
        return Some(format!(
            "`{}`: replay verdict stream does not match expected.out\n--- expected ---\n{}\n--- actual ---\n{}",
            b.name, expected, actual,
        ));
    }
    None
}

/// Per-bundle outcome: the failure (if any) and whether a trace was replayed.
/// Pure per bundle (each spawns its own `dogwood` subprocesses and touches only
/// its own files), so bundles can be checked on worker threads and folded in
/// discovery order.
struct BundleOutcome {
    failure: Option<String>,
    replayed: bool,
}

/// Run all checks for one bundle: well-formedness, `dogwood validate`, and
/// (if it ships a trace) `dogwood replay` vs `expected.out`.
fn check_bundle(bin: &Path, b: &Bundle) -> BundleOutcome {
    if let Some(p) = well_formed_problem(b) {
        // Can't meaningfully run the CLI on a malformed bundle.
        return BundleOutcome {
            failure: Some(p),
            replayed: false,
        };
    }
    if let Some(p) = validate_problem(bin, b) {
        // A bundle that doesn't validate can't be replayed.
        return BundleOutcome {
            failure: Some(p),
            replayed: false,
        };
    }
    match replay_problem(bin, b) {
        Some(p) => BundleOutcome {
            failure: Some(p),
            replayed: false,
        },
        None => BundleOutcome {
            failure: None,
            replayed: b.trace().is_some(),
        },
    }
}

#[test]
fn every_example_bundle_checks_out() {
    let bundles = discover();
    assert!(
        !bundles.is_empty(),
        "no example bundles found under {}",
        examples_root().display()
    );
    // Build the `dogwood` binary once, up front, before fanning out — so worker
    // threads don't race to first-initialize the `OnceLock` (and don't each try
    // to drive a cargo build).
    let bin = dogwood_bin();

    // Each bundle runs independent `dogwood` subprocesses, so check them across
    // worker threads. Split the (sorted) bundle list into contiguous per-thread
    // chunks and fold the per-bundle outcomes back in discovery order, so the
    // failure report is deterministic regardless of scheduling. Uses
    // `std::thread::scope` — no async runtime, no new dependencies.
    let nthreads = std::thread::available_parallelism()
        .map(|n| n.get())
        .unwrap_or(1)
        .min(bundles.len().max(1));
    let chunk_size = bundles.len().div_ceil(nthreads).max(1);
    let outcomes: Vec<BundleOutcome> = std::thread::scope(|scope| {
        let handles: Vec<_> = bundles
            .chunks(chunk_size)
            .map(|chunk| {
                scope.spawn(|| {
                    chunk
                        .iter()
                        .map(|b| check_bundle(bin, b))
                        .collect::<Vec<_>>()
                })
            })
            .collect();
        handles
            .into_iter()
            .flat_map(|h| h.join().unwrap())
            .collect()
    });

    // Fold in discovery order.
    let mut failures: Vec<String> = Vec::new();
    let mut replayed = 0usize;
    for o in outcomes {
        if let Some(f) = o.failure {
            failures.push(f);
        } else if o.replayed {
            replayed += 1;
        }
    }

    eprintln!(
        "dogwood-docs: {} bundle(s) checked, {} replayed, {} failure(s)",
        bundles.len(),
        replayed,
        failures.len()
    );
    assert!(
        failures.is_empty(),
        "{} example bundle(s) failed:\n\n{}",
        failures.len(),
        failures.join("\n\n"),
    );
}
