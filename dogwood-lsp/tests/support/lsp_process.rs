use std::collections::{HashSet, VecDeque};
use std::io::{BufRead, BufReader, Read, Write};
use std::process::{Child, ChildStdin, ChildStdout, Command, ExitStatus, Stdio};
use std::sync::mpsc::{self, Receiver, RecvTimeoutError, Sender};
use std::sync::{Arc, Mutex};
use std::thread::{self, JoinHandle};
use std::time::{Duration, Instant};

use serde_json::{Map, Value};

const TIMEOUT: Duration = Duration::from_secs(5);
pub const MAX_CONTENT_LENGTH: usize = 16 * 1024 * 1024;
#[allow(
    dead_code,
    reason = "only framing-limit integration targets assert the shared header bound"
)]
pub const MAX_HEADER_BYTES: usize = 8 * 1024;

enum StdoutEvent {
    Message(Value),
    Eof,
    Error(String),
}

pub(crate) struct StdinCommand {
    frame: Vec<u8>,
    result: Sender<Result<(), String>>,
}

#[derive(Default)]
struct StderrCapture {
    bytes: Vec<u8>,
    read_error: Option<String>,
}

pub struct LspProcess {
    child: Child,
    stdin_commands: Option<Sender<StdinCommand>>,
    stdin_thread: Option<JoinHandle<()>>,
    stdout_events: Receiver<StdoutEvent>,
    stdout_thread: Option<JoinHandle<()>>,
    stderr_thread: Option<JoinHandle<()>>,
    stderr: Arc<Mutex<StderrCapture>>,
    seen_response_ids: HashSet<String>,
    seen_server_request_ids: HashSet<String>,
    queued_notifications: VecDeque<Value>,
    queued_server_requests: VecDeque<Value>,
}

#[allow(
    dead_code,
    reason = "integration targets intentionally exercise different shared process operations"
)]
impl LspProcess {
    pub fn spawn() -> Self {
        Self::spawn_with_environment(&[])
    }

    pub fn spawn_with_test_control() -> Self {
        Self::spawn_with_environment(&[("DOGWOOD_LSP_TEST_CONTROL", "1")])
    }

    pub fn spawn_with_environment(environment: &[(&str, &str)]) -> Self {
        let mut command = Command::new(env!("CARGO_BIN_EXE_dogwood-lsp"));
        command
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .stderr(Stdio::piped());
        for (name, value) in environment {
            command.env(name, value);
        }
        let mut child = command.spawn().expect("failed to launch dogwood-lsp");

        let stdin = child.stdin.take().expect("server stdin was not piped");
        let stdout = child.stdout.take().expect("server stdout was not piped");
        let stderr = child.stderr.take().expect("server stderr was not piped");

        let (stdin_commands, stdin_receiver) = mpsc::channel();
        let stdin_thread = thread::spawn(move || write_stdin(stdin, &stdin_receiver));

        let (stdout_sender, stdout_events) = mpsc::channel();
        let stdout_thread = thread::spawn(move || read_stdout(stdout, &stdout_sender));

        let stderr_capture = Arc::new(Mutex::new(StderrCapture::default()));
        let thread_capture = Arc::clone(&stderr_capture);
        let stderr_thread = thread::spawn(move || {
            let mut stderr = stderr;
            let mut buffer = [0; 4096];
            loop {
                match stderr.read(&mut buffer) {
                    Ok(0) => break,
                    Ok(count) => thread_capture
                        .lock()
                        .expect("stderr capture lock was poisoned")
                        .bytes
                        .extend_from_slice(&buffer[..count]),
                    Err(error) => {
                        thread_capture
                            .lock()
                            .expect("stderr capture lock was poisoned")
                            .read_error = Some(error.to_string());
                        break;
                    }
                }
            }
        });

        Self {
            child,
            stdin_commands: Some(stdin_commands),
            stdin_thread: Some(stdin_thread),
            stdout_events,
            stdout_thread: Some(stdout_thread),
            stderr_thread: Some(stderr_thread),
            stderr: stderr_capture,
            seen_response_ids: HashSet::new(),
            seen_server_request_ids: HashSet::new(),
            queued_notifications: VecDeque::new(),
            queued_server_requests: VecDeque::new(),
        }
    }

    pub fn send_request(&mut self, id: i64, method: &str, params: Option<Value>) {
        self.send_request_id(Value::from(id), method, params);
    }

    pub fn send_request_id(&mut self, id: Value, method: &str, params: Option<Value>) {
        let mut message = Map::from_iter([
            ("jsonrpc".to_owned(), Value::String("2.0".to_owned())),
            ("id".to_owned(), id),
            ("method".to_owned(), Value::String(method.to_owned())),
        ]);
        if let Some(params) = params {
            message.insert("params".to_owned(), params);
        }
        self.send(Value::Object(message));
    }

    pub fn send_notification(&mut self, method: &str, params: Option<Value>) {
        let mut message = Map::from_iter([
            ("jsonrpc".to_owned(), Value::String("2.0".to_owned())),
            ("method".to_owned(), Value::String(method.to_owned())),
        ]);
        if let Some(params) = params {
            message.insert("params".to_owned(), params);
        }
        self.send(Value::Object(message));
    }

    pub fn send_success_response(&mut self, id: Value, result: Value) {
        self.send(Value::Object(Map::from_iter([
            ("jsonrpc".to_owned(), Value::String("2.0".to_owned())),
            ("id".to_owned(), id),
            ("result".to_owned(), result),
        ])));
    }

    pub fn send_error_response(&mut self, id: Value, code: i32, message: &str) {
        self.send(Value::Object(Map::from_iter([
            ("jsonrpc".to_owned(), Value::String("2.0".to_owned())),
            ("id".to_owned(), id),
            (
                "error".to_owned(),
                Value::Object(Map::from_iter([
                    ("code".to_owned(), Value::from(code)),
                    ("message".to_owned(), Value::String(message.to_owned())),
                ])),
            ),
        ])));
    }

    pub fn expect_response(&mut self, expected_id: i64, expected: Value) {
        let message = self.receive_response(expected_id);
        if message != expected {
            self.fail(&format!(
                "unexpected response\nexpected: {expected}\nreceived: {message}"
            ));
        }
    }

    pub fn receive_response(&mut self, expected_id: i64) -> Value {
        self.receive_response_id(Value::from(expected_id))
    }

    pub fn receive_response_id(&mut self, expected_id: Value) -> Value {
        loop {
            let message = self.receive_message("an LSP response");
            if is_notification(&message) {
                validate_notification(&message)
                    .unwrap_or_else(|error| self.fail(&format!("invalid notification: {error}")));
                self.queued_notifications.push_back(message);
                continue;
            }
            if is_request(&message) {
                self.validate_server_request(&message);
                self.queued_server_requests.push_back(message);
                continue;
            }
            return self.validate_response(&expected_id, message);
        }
    }

    pub fn expect_notification(&mut self, expected_method: &str, expected_params: Value) {
        let message = self.receive_notification(expected_method);
        let actual = message.get("params").cloned().unwrap_or(Value::Null);
        if actual != expected_params {
            self.fail(&format!(
                "unexpected notification params for {expected_method}\n\
                 expected: {expected_params}\nreceived: {actual}"
            ));
        }
    }

    pub fn receive_notification(&mut self, expected_method: &str) -> Value {
        let message = if let Some(message) = self.queued_notifications.pop_front() {
            message
        } else {
            loop {
                let message = self.receive_message("an LSP notification");
                if is_request(&message) {
                    self.validate_server_request(&message);
                    self.queued_server_requests.push_back(message);
                    continue;
                }
                break message;
            }
        };
        validate_notification(&message)
            .unwrap_or_else(|error| self.fail(&format!("invalid notification: {error}")));
        let actual_method = message
            .get("method")
            .and_then(Value::as_str)
            .expect("validated notification has a method");
        if actual_method != expected_method {
            self.fail(&format!(
                "expected notification method {expected_method}, received {actual_method}"
            ));
        }
        message
    }

    pub fn receive_server_request(&mut self, expected_method: &str) -> Value {
        let message = if let Some(message) = self.queued_server_requests.pop_front() {
            message
        } else {
            loop {
                let message = self.receive_message("an LSP server request");
                if is_notification(&message) {
                    validate_notification(&message).unwrap_or_else(|error| {
                        self.fail(&format!("invalid notification: {error}"))
                    });
                    self.queued_notifications.push_back(message);
                    continue;
                }
                self.validate_server_request(&message);
                break message;
            }
        };
        let actual_method = message
            .get("method")
            .and_then(Value::as_str)
            .expect("validated server request has a method");
        if actual_method != expected_method {
            self.fail(&format!(
                "expected server request method {expected_method}, received {actual_method}"
            ));
        }
        message
    }

    pub fn assert_no_queued_notifications(&self) {
        if let Some(notification) = self.queued_notifications.front() {
            self.fail(&format!(
                "expected no queued server notifications, found {notification}"
            ));
        }
    }

    pub fn assert_no_queued_server_requests(&self) {
        if let Some(request) = self.queued_server_requests.front() {
            self.fail(&format!(
                "expected no queued server requests, found {request}"
            ));
        }
    }

    pub fn assert_no_queued_server_messages(&self) {
        self.assert_no_queued_notifications();
        self.assert_no_queued_server_requests();
    }

    pub fn take_queued_notifications(&mut self) -> Vec<Value> {
        self.queued_notifications.drain(..).collect()
    }

    fn validate_response(&mut self, expected_id: &Value, message: Value) -> Value {
        let object = message
            .as_object()
            .unwrap_or_else(|| self.fail("server emitted a non-object JSON-RPC message"));
        if object.get("jsonrpc") != Some(&Value::String("2.0".to_owned())) {
            self.fail("server response omitted jsonrpc 2.0");
        }

        let response_id = object
            .get("id")
            .unwrap_or_else(|| self.fail("server emitted an unsolicited message"));
        let response_id_key = serde_json::to_string(response_id)
            .expect("response IDs should always serialize to JSON");
        if !self.seen_response_ids.insert(response_id_key) {
            self.fail("server emitted a duplicate response ID");
        }
        if response_id != expected_id {
            self.fail(&format!(
                "expected response ID {expected_id}, received {response_id}"
            ));
        }

        let has_result = object.contains_key("result");
        let has_error = object.contains_key("error");
        if has_result == has_error {
            self.fail("server response must contain exactly one of result or error");
        }

        message
    }

    fn validate_server_request(&mut self, message: &Value) {
        let object = message
            .as_object()
            .unwrap_or_else(|| self.fail("server emitted a non-object JSON-RPC message"));
        if object.get("jsonrpc") != Some(&Value::String("2.0".to_owned())) {
            self.fail("server request omitted jsonrpc 2.0");
        }
        if object.get("result").is_some() || object.get("error").is_some() {
            self.fail("server request contains response fields");
        }
        if !object.get("method").is_some_and(Value::is_string) {
            self.fail("server request omitted a string method");
        }
        let request_id = object
            .get("id")
            .unwrap_or_else(|| self.fail("server request omitted an ID"));
        if !request_id.is_i64() && !request_id.is_string() {
            self.fail("server request ID must be an integer or string");
        }
        let request_id_key = serde_json::to_string(request_id)
            .expect("server request IDs should always serialize to JSON");
        if !self.seen_server_request_ids.insert(request_id_key) {
            self.fail("server emitted a duplicate request ID");
        }
    }

    fn receive_message(&self, expected: &str) -> Value {
        match self.stdout_events.recv_timeout(TIMEOUT) {
            Ok(StdoutEvent::Message(message)) => message,
            Ok(StdoutEvent::Eof) => self.fail(&format!(
                "server stdout closed before the expected {expected}"
            )),
            Ok(StdoutEvent::Error(error)) => {
                self.fail(&format!("server stdout framing failed: {error}"))
            }
            Err(RecvTimeoutError::Timeout) => {
                self.fail(&format!("timed out waiting for {expected}"))
            }
            Err(RecvTimeoutError::Disconnected) => self.fail(&format!(
                "server stdout reader stopped before the expected {expected}"
            )),
        }
    }

    pub fn assert_running(&mut self) {
        match self.child.try_wait() {
            Ok(None) => {}
            Ok(Some(status)) => self.fail(&format!("server exited early with {status}")),
            Err(error) => self.fail(&format!("failed to query server status: {error}")),
        }
    }

    pub fn finish(mut self, expected_code: i32) {
        self.finish_and_check_stderr(expected_code, &[]);
    }

    pub fn finish_with_stderr(mut self, expected_code: i32, expected_stderr: &str) {
        self.finish_and_check_stderr(expected_code, &[expected_stderr]);
    }

    pub fn finish_with_stderr_fragments(mut self, expected_code: i32, expected_stderr: &[&str]) {
        self.finish_and_check_stderr(expected_code, expected_stderr);
    }

    pub fn send_raw(&mut self, frame: Vec<u8>) {
        let Some(stdin_commands) = self.stdin_commands.as_ref() else {
            self.fail("cannot send after server stdin was closed");
        };

        if let Err(error) = send_stdin_frame(stdin_commands, frame, TIMEOUT) {
            self.fail(&error);
        }
    }

    pub fn close_stdin(&mut self) {
        self.stdin_commands.take();
    }

    fn finish_and_check_stderr(&mut self, expected_code: i32, expected_stderr: &[&str]) {
        let status = self.wait_for_exit();
        self.stdin_commands.take();
        self.expect_clean_stdout_eof();
        self.join_worker_threads();
        self.assert_no_stderr_read_error();

        if status.code() != Some(expected_code) {
            self.fail(&format!(
                "expected server exit status {expected_code}, received {status}"
            ));
        }
        self.assert_no_queued_notifications();
        self.assert_no_queued_server_requests();
        for expected in expected_stderr {
            if !self.stderr_text().contains(expected) {
                self.fail(&format!("expected server stderr to contain {expected:?}"));
            }
        }
    }

    fn send(&mut self, message: Value) {
        let body = serde_json::to_vec(&message).expect("test message should serialize");
        let mut frame = format!("Content-Length: {}\r\n\r\n", body.len()).into_bytes();
        frame.extend_from_slice(&body);
        self.send_raw(frame);
    }

    fn wait_for_exit(&mut self) -> ExitStatus {
        let deadline = Instant::now() + TIMEOUT;
        loop {
            match self.child.try_wait() {
                Ok(Some(status)) => return status,
                Ok(None) if Instant::now() < deadline => {
                    thread::sleep(Duration::from_millis(10));
                }
                Ok(None) => self.fail("timed out waiting for the server to exit"),
                Err(error) => self.fail(&format!("failed to wait for server exit: {error}")),
            }
        }
    }

    fn expect_clean_stdout_eof(&self) {
        match self.stdout_events.recv_timeout(TIMEOUT) {
            Ok(StdoutEvent::Eof) => {}
            Ok(StdoutEvent::Message(message)) => self.fail(&format!(
                "server emitted a trailing stdout message: {message}"
            )),
            Ok(StdoutEvent::Error(error)) => {
                self.fail(&format!("server stdout did not end cleanly: {error}"))
            }
            Err(RecvTimeoutError::Timeout) => self.fail("timed out waiting for stdout EOF"),
            Err(RecvTimeoutError::Disconnected) => {
                self.fail("stdout reader stopped without reporting EOF")
            }
        }
    }

    fn join_worker_threads(&mut self) {
        if self
            .stdin_thread
            .take()
            .expect("stdin thread should exist")
            .join()
            .is_err()
        {
            self.fail("stdin writer thread panicked");
        }
        if self
            .stdout_thread
            .take()
            .expect("stdout thread should exist")
            .join()
            .is_err()
        {
            self.fail("stdout reader thread panicked");
        }
        if self
            .stderr_thread
            .take()
            .expect("stderr thread should exist")
            .join()
            .is_err()
        {
            self.fail("stderr reader thread panicked");
        }
    }

    fn assert_no_stderr_read_error(&self) {
        let capture = self
            .stderr
            .lock()
            .expect("stderr capture lock was poisoned");
        if let Some(error) = capture.read_error.clone() {
            drop(capture);
            self.fail(&format!("server stderr reader failed: {error}"));
        }
    }

    fn stderr_text(&self) -> String {
        let capture = self
            .stderr
            .lock()
            .expect("stderr capture lock was poisoned");
        let mut text = String::from_utf8_lossy(&capture.bytes).into_owned();
        if let Some(error) = &capture.read_error {
            text.push_str(&format!("\n[stderr read failed: {error}]"));
        }
        text
    }

    fn fail(&self, message: &str) -> ! {
        panic!("{message}\nserver stderr:\n{}", self.stderr_text());
    }
}

fn is_notification(message: &Value) -> bool {
    message.get("method").is_some() && message.get("id").is_none()
}

fn is_request(message: &Value) -> bool {
    message.get("method").is_some() && message.get("id").is_some()
}

fn validate_notification(message: &Value) -> Result<(), String> {
    let object = message
        .as_object()
        .ok_or_else(|| "server emitted a non-object JSON-RPC message".to_owned())?;
    if object.get("jsonrpc") != Some(&Value::String("2.0".to_owned())) {
        return Err("server notification omitted jsonrpc 2.0".to_owned());
    }
    if object.get("id").is_some() || object.get("result").is_some() || object.get("error").is_some()
    {
        return Err("server notification contains response fields".to_owned());
    }
    if !object.get("method").is_some_and(Value::is_string) {
        return Err("server notification omitted a string method".to_owned());
    }
    Ok(())
}

impl Drop for LspProcess {
    fn drop(&mut self) {
        self.stdin_commands.take();
        if self.child.try_wait().ok().flatten().is_none() {
            let _ = self.child.kill();
            let _ = self.child.wait();
        }

        if let Some(thread) = self.stdin_thread.take() {
            let _ = thread.join();
        }
        if let Some(thread) = self.stdout_thread.take() {
            let _ = thread.join();
        }
        if let Some(thread) = self.stderr_thread.take() {
            let _ = thread.join();
        }
    }
}

pub(crate) fn write_stdin(mut stdin: ChildStdin, commands: &Receiver<StdinCommand>) {
    for command in commands {
        let result = stdin
            .write_all(&command.frame)
            .and_then(|()| stdin.flush())
            .map_err(|error| format!("failed to write LSP frame: {error}"));
        let write_failed = result.is_err();
        if command.result.send(result).is_err() || write_failed {
            return;
        }
    }
}

pub(crate) fn send_stdin_frame(
    commands: &Sender<StdinCommand>,
    frame: Vec<u8>,
    timeout: Duration,
) -> Result<(), String> {
    let (result_sender, result_receiver) = mpsc::channel();
    commands
        .send(StdinCommand {
            frame,
            result: result_sender,
        })
        .map_err(|_| "stdin writer stopped before accepting an LSP frame".to_owned())?;

    match result_receiver.recv_timeout(timeout) {
        Ok(result) => result,
        Err(RecvTimeoutError::Timeout) => Err("timed out writing an LSP frame".to_owned()),
        Err(RecvTimeoutError::Disconnected) => {
            Err("stdin writer stopped before completing an LSP frame".to_owned())
        }
    }
}

fn read_stdout(stdout: ChildStdout, sender: &Sender<StdoutEvent>) {
    let mut reader = BufReader::new(stdout);
    loop {
        match read_frame(&mut reader) {
            Ok(Some(message)) => {
                if sender.send(StdoutEvent::Message(message)).is_err() {
                    return;
                }
            }
            Ok(None) => {
                let _ = sender.send(StdoutEvent::Eof);
                return;
            }
            Err(error) => {
                let _ = sender.send(StdoutEvent::Error(error));
                return;
            }
        }
    }
}

pub(crate) fn read_frame(reader: &mut impl BufRead) -> Result<Option<Value>, String> {
    let mut content_length = None;
    let mut saw_header = false;

    loop {
        let mut line = Vec::new();
        let bytes_read = reader
            .read_until(b'\n', &mut line)
            .map_err(|error| format!("failed to read header: {error}"))?;
        if bytes_read == 0 {
            return if saw_header {
                Err("incomplete header at EOF".to_owned())
            } else {
                Ok(None)
            };
        }
        saw_header = true;

        if line == b"\r\n" {
            break;
        }
        if !line.ends_with(b"\r\n") {
            return Err("headers must end with CRLF".to_owned());
        }

        let header = std::str::from_utf8(&line[..line.len() - 2])
            .map_err(|_| "header is not valid UTF-8".to_owned())?;
        let (name, value) = header
            .split_once(':')
            .ok_or_else(|| "malformed header".to_owned())?;
        if name.trim().eq_ignore_ascii_case("content-length") {
            if content_length.is_some() {
                return Err("duplicate Content-Length header".to_owned());
            }
            content_length = Some(
                value
                    .trim()
                    .parse::<usize>()
                    .map_err(|_| "invalid Content-Length header".to_owned())?,
            );
        }
    }

    let content_length =
        content_length.ok_or_else(|| "missing Content-Length header".to_owned())?;
    if content_length > MAX_CONTENT_LENGTH {
        return Err(format!(
            "Content-Length {content_length} exceeds the {MAX_CONTENT_LENGTH}-byte limit"
        ));
    }
    let mut body = vec![0; content_length];
    reader.read_exact(&mut body).map_err(|error| {
        if error.kind() == std::io::ErrorKind::UnexpectedEof {
            "incomplete JSON body at EOF".to_owned()
        } else {
            format!("failed to read JSON body: {error}")
        }
    })?;
    serde_json::from_slice(&body).map(Some).map_err(|error| {
        format!(
            "malformed JSON body: {error}; body={}",
            String::from_utf8_lossy(&body)
        )
    })
}
