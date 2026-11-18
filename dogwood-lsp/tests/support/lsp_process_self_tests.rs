use std::io::Cursor;
use std::process::{Command, Stdio};
use std::sync::mpsc;
use std::thread;
use std::time::Duration;

use serde_json::json;

use crate::lsp_process::{
    MAX_CONTENT_LENGTH, StdinCommand, read_frame, send_stdin_frame, write_stdin,
};

#[test]
fn read_frame_accepts_case_insensitive_content_length() {
    let mut input = Cursor::new(b"content-length: 2\r\n\r\n{}".as_slice());

    assert_eq!(read_frame(&mut input), Ok(Some(json!({}))));
}

#[test]
fn read_frame_rejects_duplicate_content_length() {
    let input = b"Content-Length: 2\r\ncontent-length: 2\r\n\r\n{}";

    assert_frame_error(input, "duplicate Content-Length header");
}

#[test]
fn read_frame_rejects_missing_content_length() {
    let input = b"Content-Type: application/json\r\n\r\n{}";

    assert_frame_error(input, "missing Content-Length header");
}

#[test]
fn read_frame_rejects_invalid_content_length() {
    let input = b"Content-Length: invalid\r\n\r\n{}";

    assert_frame_error(input, "invalid Content-Length header");
}

#[test]
fn read_frame_rejects_oversized_content_length() {
    let input = format!("Content-Length: {}\r\n\r\n", MAX_CONTENT_LENGTH + 1);

    assert_frame_error(
        input.as_bytes(),
        &format!(
            "Content-Length {} exceeds the {MAX_CONTENT_LENGTH}-byte limit",
            MAX_CONTENT_LENGTH + 1
        ),
    );
}

#[test]
fn read_frame_rejects_malformed_json() {
    let input = b"Content-Length: 1\r\n\r\n{";

    assert_frame_error(input, "malformed JSON body");
}

#[test]
fn read_frame_rejects_incomplete_header() {
    let input = b"Content-Length: 2\r\n";

    assert_frame_error(input, "incomplete header at EOF");
}

#[test]
fn read_frame_rejects_incomplete_body() {
    let input = b"Content-Length: 2\r\n\r\n{";

    assert_frame_error(input, "incomplete JSON body at EOF");
}

#[test]
fn read_frame_rejects_trailing_non_frame_bytes() {
    let mut input = Cursor::new(b"Content-Length: 2\r\n\r\n{}trailing".as_slice());

    assert_eq!(read_frame(&mut input), Ok(Some(json!({}))));
    assert_eq!(
        read_frame(&mut input),
        Err("headers must end with CRLF".to_owned())
    );
}

#[cfg(unix)]
#[test]
fn stdin_writer_times_out_when_child_does_not_read() {
    let mut child = Command::new("/bin/sleep")
        .arg("60")
        .stdin(Stdio::piped())
        .spawn()
        .expect("failed to launch non-reading test child");
    let stdin = child.stdin.take().expect("test child stdin was not piped");
    let (commands, receiver) = mpsc::channel::<StdinCommand>();
    let writer = thread::spawn(move || write_stdin(stdin, &receiver));

    let result = send_stdin_frame(
        &commands,
        vec![0; MAX_CONTENT_LENGTH],
        Duration::from_millis(100),
    );

    drop(commands);
    child.kill().expect("failed to kill non-reading test child");
    child.wait().expect("failed to reap non-reading test child");
    writer.join().expect("stdin writer thread panicked");

    assert_eq!(result, Err("timed out writing an LSP frame".to_owned()));
}

fn assert_frame_error(input: &[u8], expected: &str) {
    let error =
        read_frame(&mut Cursor::new(input)).expect_err("invalid frame should have been rejected");
    assert!(
        error.contains(expected),
        "expected error containing {expected:?}, received {error:?}"
    );
}
