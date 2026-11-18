mod protocol;
mod transport;

use std::fmt;
use std::io;
use std::io::BufRead;
use std::process::ExitCode;
use std::thread;

use crossbeam_channel::{Receiver, Sender, bounded, select};
use lsp_server::Message;

use crate::protocol::{DispatchOutcome, Server};
use crate::transport::FrameError;

const INPUT_QUEUE_CAPACITY: usize = 64;
type InputResult = Result<Option<Message>, InputError>;

fn main() -> ExitCode {
    let stdout = io::stdout();
    let mut writer = stdout.lock();
    let mut server = Server::default();
    let input = spawn_input_reader();
    let async_events = server.async_events();
    let mut exit_code = 1;

    loop {
        let outcome = select! {
            recv(input) -> input => {
                match input {
                    Ok(Ok(Some(message))) => server.handle_message(message),
                    Ok(Ok(None)) | Err(_) => break,
                    Ok(Err(error)) => {
                        eprintln!("failed to read LSP message: {error}");
                        break;
                    }
                }
            }
            recv(async_events) -> event => {
                match event {
                    Ok(event) => server.handle_async_event(event),
                    Err(_) => {
                        eprintln!("analysis event channel closed unexpectedly");
                        break;
                    }
                }
            }
        };

        let outcome_exit_code = outcome.exit_code;
        if let Err(error) = write_outcome(outcome, &mut writer) {
            eprintln!("failed to write LSP message: {error}");
            break;
        }

        if let Some(code) = outcome_exit_code {
            exit_code = code;
            break;
        }
    }

    ExitCode::from(exit_code)
}

fn spawn_input_reader() -> Receiver<InputResult> {
    let (sender, receiver) = input_channel();
    thread::Builder::new()
        .name("dogwood-lsp-input".to_owned())
        .spawn(move || {
            let stdin = io::stdin();
            let mut reader = stdin.lock();
            loop {
                let result = read_message(&mut reader);
                let finished = !matches!(result, Ok(Some(_)));
                if sender.send(result).is_err() || finished {
                    return;
                }
            }
        })
        .expect("input reader thread should start");
    receiver
}

fn input_channel() -> (Sender<InputResult>, Receiver<InputResult>) {
    bounded(INPUT_QUEUE_CAPACITY)
}

fn write_outcome(outcome: DispatchOutcome, writer: &mut impl io::Write) -> Result<(), io::Error> {
    for request in outcome.requests {
        Message::Request(request).write(&mut *writer)?;
    }
    for notification in outcome.notifications {
        Message::Notification(notification).write(&mut *writer)?;
    }
    if let Some(response) = outcome.response {
        Message::Response(response).write(&mut *writer)?;
    }
    for response in outcome.responses {
        Message::Response(response).write(&mut *writer)?;
    }
    Ok(())
}

#[derive(Debug)]
enum InputError {
    Frame(FrameError),
    MalformedJson(serde_json::Error),
}

impl fmt::Display for InputError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Frame(error) => error.fmt(formatter),
            Self::MalformedJson(error) => write!(formatter, "malformed LSP JSON body: {error}"),
        }
    }
}

fn read_message(reader: &mut impl BufRead) -> Result<Option<Message>, InputError> {
    let Some(body) = transport::read_frame(reader).map_err(InputError::Frame)? else {
        return Ok(None);
    };
    serde_json::from_slice(&body)
        .map(Some)
        .map_err(InputError::MalformedJson)
}

// dogwood-lsp handles Unix paths and file URIs only, so its tests run on Unix.
#[cfg(all(test, unix))]
mod tests {
    use std::io::Cursor;

    use crossbeam_channel::TrySendError;
    use lsp_server::Message;

    use super::{INPUT_QUEUE_CAPACITY, input_channel, read_message};

    #[test]
    fn production_reader_deserializes_lsp_messages() {
        let body = br#"{"jsonrpc":"2.0","method":"exit"}"#;
        let mut frame = format!("Content-Length: {}\r\n\r\n", body.len()).into_bytes();
        frame.extend_from_slice(body);

        let message = read_message(&mut Cursor::new(frame))
            .unwrap()
            .expect("frame should contain a message");

        assert!(
            matches!(message, Message::Notification(notification) if notification.method == "exit")
        );
    }

    #[test]
    fn production_reader_rejects_malformed_json() {
        let error = read_message(&mut Cursor::new(b"Content-Length: 1\r\n\r\n{"))
            .expect_err("malformed JSON should be rejected");

        assert!(error.to_string().contains("malformed LSP JSON body"));
    }

    #[test]
    fn input_queue_backpressures_after_its_fixed_capacity() {
        let (sender, _receiver) = input_channel();
        for _ in 0..INPUT_QUEUE_CAPACITY {
            sender
                .try_send(Ok(None))
                .expect("messages through the fixed capacity should fit");
        }

        assert!(matches!(
            sender.try_send(Ok(None)),
            Err(TrySendError::Full(_))
        ));
    }
}
