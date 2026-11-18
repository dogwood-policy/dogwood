use std::env;
use std::fs::{self, File, OpenOptions};
use std::io::{Read, Seek, SeekFrom};
use std::path::{Path, PathBuf};
use std::process::{self, Child, Command, ExitStatus, Stdio};
use std::sync::OnceLock;
use std::sync::atomic::{AtomicU64, Ordering};
use std::thread;
use std::time::{Duration, Instant};

use escargot::CargoBuild;

const ORACLE_TIMEOUT: Duration = Duration::from_secs(10);
const POLL_INTERVAL: Duration = Duration::from_millis(10);
const TEMP_FILE_ATTEMPTS: usize = 1_024;
pub(crate) const MAX_CAPTURE_STREAM_BYTES: u64 = 16 * 1024 * 1024;

static TEMP_FILE_SEQUENCE: AtomicU64 = AtomicU64::new(0);

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct OracleOutput {
    pub exit_code: i32,
    pub stdout: Vec<u8>,
    pub stderr: Vec<u8>,
}

pub struct ValidateInvocation<'a> {
    pub fixture: &'a str,
    pub policy: &'a Path,
    pub policy_schema: &'a Path,
    pub event_schema: Option<&'a Path>,
    pub providers: Option<&'a Path>,
    pub macros: Option<&'a Path>,
}

pub fn validate(invocation: &ValidateInvocation<'_>) -> Result<OracleOutput, String> {
    let context = format!(
        "fixture `{}` against the workspace Dogwood CLI",
        invocation.fixture
    );
    let binary = dogwood_binary()?;
    let metadata = binary.metadata().map_err(|error| {
        format!(
            "{context}: cannot inspect workspace Dogwood CLI `{}`: {error}",
            binary.display()
        )
    })?;
    if !metadata.is_file() {
        return Err(format!(
            "{context}: workspace Dogwood CLI is not a file: `{}`",
            binary.display()
        ));
    }

    let mut stdout_capture = CaptureFile::create("stdout")
        .map_err(|error| format!("{context}: failed to create stdout capture: {error}"))?;
    let mut stderr_capture = CaptureFile::create("stderr")
        .map_err(|error| format!("{context}: failed to create stderr capture: {error}"))?;

    let mut command = Command::new(&binary);
    command
        .arg("validate")
        .arg(invocation.policy)
        .arg("--policy-schema")
        .arg(invocation.policy_schema);
    add_optional_input(&mut command, "--event-schema", invocation.event_schema);
    add_optional_input(&mut command, "--providers", invocation.providers);
    add_optional_input(&mut command, "--macros", invocation.macros);
    command
        .arg("--format")
        .arg("json")
        .stdin(Stdio::null())
        .stdout(
            stdout_capture
                .stdio()
                .map_err(|error| format!("{context}: failed to prepare stdout capture: {error}"))?,
        )
        .stderr(
            stderr_capture
                .stdio()
                .map_err(|error| format!("{context}: failed to prepare stderr capture: {error}"))?,
        );

    let child = command.spawn();
    drop(command);
    let mut child = child.map_err(|error| {
        format!(
            "{context}: failed to launch workspace Dogwood CLI `{}`: {error}",
            binary.display()
        )
    })?;

    let status = match wait_with_deadline(&mut child, ORACLE_TIMEOUT) {
        Ok(status) => status,
        Err(error) => {
            let cleanup = terminate_and_wait(&mut child);
            let stdout = finish_capture(&mut stdout_capture, &context, "stdout");
            let stderr = finish_capture(&mut stderr_capture, &context, "stderr");
            return Err(format!(
                "{context}: {error}; cleanup: {cleanup}; stdout: {}; stderr: {}",
                display_bytes(&stdout),
                display_bytes(&stderr)
            ));
        }
    };
    let stdout = finish_capture(&mut stdout_capture, &context, "stdout");
    let stderr = finish_capture(&mut stderr_capture, &context, "stderr");
    let exit_code = status.code().ok_or_else(|| {
        format!(
            "{context}: workspace Dogwood CLI terminated without an exit code; stdout: {}; stderr: {}",
            display_bytes(&stdout),
            display_bytes(&stderr)
        )
    })?;

    if !stderr.is_empty() {
        return Err(format!(
            "{context}: workspace Dogwood CLI wrote unexpected stderr: {}",
            display_bytes(&stderr)
        ));
    }

    let mut command_paths = vec![
        binary.as_path(),
        invocation.policy,
        invocation.policy_schema,
    ];
    command_paths.extend(invocation.event_schema);
    command_paths.extend(invocation.providers);
    command_paths.extend(invocation.macros);
    for path in command_paths {
        if contains_bytes(&stdout, path.as_os_str().as_encoded_bytes()) {
            return Err(format!(
                "{context}: path-dependent oracle stdout contains command path `{}`: {}",
                path.display(),
                display_bytes(&stdout)
            ));
        }
    }

    Ok(OracleOutput {
        exit_code,
        stdout,
        stderr,
    })
}

fn dogwood_binary() -> Result<PathBuf, String> {
    static BINARY: OnceLock<Result<PathBuf, String>> = OnceLock::new();
    BINARY
        .get_or_init(|| {
            let workspace_manifest = Path::new(env!("CARGO_MANIFEST_DIR")).join("../Cargo.toml");
            CargoBuild::new()
                .manifest_path(workspace_manifest)
                .bin("dogwood")
                .package("dogwood-cli")
                .run()
                .map(|run| run.path().to_path_buf())
                .map_err(|error| format!("failed to build the workspace Dogwood CLI: {error}"))
        })
        .clone()
}

fn add_optional_input(command: &mut Command, flag: &str, path: Option<&Path>) {
    if let Some(path) = path {
        command.arg(flag).arg(path);
    }
}

pub(crate) struct CaptureFile {
    pub(crate) file: File,
    path: PathBuf,
}

impl CaptureFile {
    pub(crate) fn create(stream: &str) -> Result<Self, String> {
        let directory = env::temp_dir();
        for _ in 0..TEMP_FILE_ATTEMPTS {
            let sequence = TEMP_FILE_SEQUENCE.fetch_add(1, Ordering::Relaxed);
            let path = directory.join(format!(
                "dogwood-lsp-oracle-{}-{sequence}-{stream}.capture",
                process::id()
            ));
            match OpenOptions::new()
                .read(true)
                .write(true)
                .create_new(true)
                .open(&path)
            {
                Ok(file) => return Ok(Self { file, path }),
                Err(error) if error.kind() == std::io::ErrorKind::AlreadyExists => continue,
                Err(error) => {
                    return Err(format!("cannot create `{}`: {error}", path.display()));
                }
            }
        }

        Err(format!(
            "could not allocate a unique file in `{}` after {TEMP_FILE_ATTEMPTS} attempts",
            directory.display()
        ))
    }

    fn stdio(&self) -> Result<Stdio, String> {
        self.file
            .try_clone()
            .map(Stdio::from)
            .map_err(|error| format!("cannot clone `{}`: {error}", self.path.display()))
    }

    pub(crate) fn read_snapshot(&mut self) -> Result<Vec<u8>, String> {
        let length = self
            .file
            .metadata()
            .map_err(|error| format!("cannot inspect `{}`: {error}", self.path.display()))?
            .len();
        if length > MAX_CAPTURE_STREAM_BYTES {
            return Err(format!(
                "capture `{}` is {length} bytes, exceeding the per-stream maximum of \
                 {MAX_CAPTURE_STREAM_BYTES} bytes (16 MiB)",
                self.path.display()
            ));
        }

        self.file
            .seek(SeekFrom::Start(0))
            .map_err(|error| format!("cannot seek `{}`: {error}", self.path.display()))?;

        let mut bytes = Vec::new();
        self.file
            .by_ref()
            .take(length)
            .read_to_end(&mut bytes)
            .map_err(|error| format!("cannot read `{}`: {error}", self.path.display()))?;
        Ok(bytes)
    }
}

impl Drop for CaptureFile {
    fn drop(&mut self) {
        let _ = fs::remove_file(&self.path);
    }
}

fn wait_with_deadline(child: &mut Child, timeout: Duration) -> Result<ExitStatus, String> {
    let deadline = Instant::now() + timeout;
    loop {
        match child.try_wait() {
            Ok(Some(status)) => return Ok(status),
            Ok(None) if Instant::now() < deadline => thread::sleep(POLL_INTERVAL),
            Ok(None) => {
                return Err(format!(
                    "workspace Dogwood CLI timed out after {} seconds",
                    timeout.as_secs()
                ));
            }
            Err(error) => return Err(format!("failed to query oracle status: {error}")),
        }
    }
}

fn terminate_and_wait(child: &mut Child) -> String {
    let kill = child
        .kill()
        .map(|()| "kill succeeded".to_owned())
        .unwrap_or_else(|error| format!("kill failed: {error}"));
    let wait = child
        .wait()
        .map(|status| format!("wait returned {status}"))
        .unwrap_or_else(|error| format!("wait failed: {error}"));
    format!("{kill}, {wait}")
}

fn finish_capture(capture: &mut CaptureFile, context: &str, stream: &str) -> Vec<u8> {
    capture
        .read_snapshot()
        .unwrap_or_else(|error| panic!("{context}: failed to capture oracle {stream}: {error}"))
}

fn contains_bytes(haystack: &[u8], needle: &[u8]) -> bool {
    !needle.is_empty()
        && haystack
            .windows(needle.len())
            .any(|window| window == needle)
}

fn display_bytes(bytes: &[u8]) -> String {
    format!("{:?}", String::from_utf8_lossy(bytes))
}
