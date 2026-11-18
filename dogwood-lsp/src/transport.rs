use std::fmt;
use std::io::{self, BufRead};

pub(crate) const MAX_CONTENT_LENGTH: usize = 16 * 1024 * 1024;
pub(crate) const MAX_HEADER_BYTES: usize = 8 * 1024;

#[derive(Debug)]
pub(crate) struct FrameError {
    message: String,
}

impl FrameError {
    fn new(message: impl Into<String>) -> Self {
        Self {
            message: message.into(),
        }
    }
}

impl fmt::Display for FrameError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str(&self.message)
    }
}

impl std::error::Error for FrameError {}

pub(crate) fn read_frame(reader: &mut impl BufRead) -> Result<Option<Vec<u8>>, FrameError> {
    let Some(headers) = read_headers(reader)? else {
        return Ok(None);
    };
    let content_length = parse_content_length(&headers)?;

    if content_length > MAX_CONTENT_LENGTH {
        return Err(FrameError::new(format!(
            "Content-Length {content_length} exceeds the {MAX_CONTENT_LENGTH}-byte limit"
        )));
    }

    let mut body = vec![0; content_length];
    reader.read_exact(&mut body).map_err(|error| {
        if error.kind() == io::ErrorKind::UnexpectedEof {
            FrameError::new(format!(
                "incomplete LSP body: expected {content_length} bytes"
            ))
        } else {
            FrameError::new(format!("failed to read LSP body: {error}"))
        }
    })?;

    Ok(Some(body))
}

fn read_headers(reader: &mut impl BufRead) -> Result<Option<Vec<u8>>, FrameError> {
    let mut headers = Vec::with_capacity(MAX_HEADER_BYTES);

    loop {
        let available = reader
            .fill_buf()
            .map_err(|error| FrameError::new(format!("failed to read LSP header: {error}")))?;
        if available.is_empty() {
            return if headers.is_empty() {
                Ok(None)
            } else {
                Err(FrameError::new("incomplete LSP header"))
            };
        }

        let mut consumed = 0;
        let mut complete = false;
        for byte in available {
            if headers.len() == MAX_HEADER_BYTES {
                return Err(FrameError::new(format!(
                    "LSP header exceeds the {MAX_HEADER_BYTES}-byte limit"
                )));
            }

            headers.push(*byte);
            consumed += 1;
            if headers.ends_with(b"\r\n\r\n") {
                complete = true;
                break;
            }
        }
        reader.consume(consumed);

        if complete {
            return Ok(Some(headers));
        }
    }
}

fn parse_content_length(headers: &[u8]) -> Result<usize, FrameError> {
    debug_assert!(headers.ends_with(b"\r\n\r\n"));
    let fields = &headers[..headers.len() - 4];
    if !fields.is_ascii() {
        return Err(FrameError::new("LSP header contains non-ASCII bytes"));
    }

    let fields = std::str::from_utf8(fields).expect("ASCII headers are valid UTF-8");
    let mut content_length = None;

    for field in fields.split("\r\n").filter(|field| !field.is_empty()) {
        let (name, value) = field
            .split_once(':')
            .ok_or_else(|| FrameError::new("malformed LSP header field"))?;
        if !valid_header_name(name) {
            return Err(FrameError::new("malformed LSP header name"));
        }

        if name.eq_ignore_ascii_case("Content-Length") {
            if content_length.is_some() {
                return Err(FrameError::new("duplicate Content-Length header"));
            }

            let value = value.trim_matches([' ', '\t']);
            if value.is_empty() || !value.bytes().all(|byte| byte.is_ascii_digit()) {
                return Err(FrameError::new("invalid Content-Length header"));
            }
            content_length = Some(
                value
                    .parse()
                    .map_err(|_| FrameError::new("invalid Content-Length header"))?,
            );
        } else if !name.eq_ignore_ascii_case("Content-Type") {
            return Err(FrameError::new(format!("unsupported LSP header `{name}`")));
        }
    }

    content_length.ok_or_else(|| FrameError::new("missing Content-Length header"))
}

fn valid_header_name(name: &str) -> bool {
    !name.is_empty()
        && name
            .bytes()
            .all(|byte| byte.is_ascii_alphanumeric() || byte == b'-')
}

#[cfg(test)]
mod tests {
    use std::io::Cursor;

    use super::{MAX_CONTENT_LENGTH, MAX_HEADER_BYTES, read_frame};

    #[test]
    fn accepts_lsp_content_length_framing() {
        let input = b"content-length: 2\r\nContent-Type: application/vscode-jsonrpc; charset=utf-8\r\n\r\n{}";
        let mut reader = Cursor::new(input);

        assert_eq!(read_frame(&mut reader).unwrap(), Some(b"{}".to_vec()));
        assert_eq!(read_frame(&mut reader).unwrap(), None);
    }

    #[test]
    fn preserves_consecutive_frame_boundaries() {
        let input = b"Content-Length: 2\r\n\r\n{}Content-Length: 2\r\n\r\n[]";
        let mut reader = Cursor::new(input);

        assert_eq!(read_frame(&mut reader).unwrap(), Some(b"{}".to_vec()));
        assert_eq!(read_frame(&mut reader).unwrap(), Some(b"[]".to_vec()));
        assert_eq!(read_frame(&mut reader).unwrap(), None);
    }

    #[test]
    fn rejects_missing_content_length() {
        assert_frame_error(
            b"Content-Type: application/vscode-jsonrpc\r\n\r\n",
            "missing Content-Length header",
        );
    }

    #[test]
    fn rejects_duplicate_content_length() {
        assert_frame_error(
            b"Content-Length: 2\r\ncontent-length: 2\r\n\r\n{}",
            "duplicate Content-Length header",
        );
    }

    #[test]
    fn rejects_invalid_content_length() {
        assert_frame_error(
            b"Content-Length: -1\r\n\r\n",
            "invalid Content-Length header",
        );
        assert_frame_error(
            b"Content-Length: invalid\r\n\r\n",
            "invalid Content-Length header",
        );
    }

    #[test]
    fn rejects_oversized_content_length_before_reading_a_body() {
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
    fn rejects_incomplete_header() {
        assert_frame_error(b"Content-Length: 2\r\n", "incomplete LSP header");
    }

    #[test]
    fn rejects_oversized_unterminated_header() {
        let input = vec![b'x'; MAX_HEADER_BYTES + 1];

        assert_frame_error(
            &input,
            &format!("LSP header exceeds the {MAX_HEADER_BYTES}-byte limit"),
        );
    }

    #[test]
    fn rejects_incomplete_body() {
        assert_frame_error(
            b"Content-Length: 2\r\n\r\n{",
            "incomplete LSP body: expected 2 bytes",
        );
    }

    #[test]
    fn rejects_unsupported_framing_header() {
        assert_frame_error(
            b"Transfer-Encoding: chunked\r\n\r\n",
            "unsupported LSP header `Transfer-Encoding`",
        );
    }

    #[test]
    fn seeded_valid_frames_round_trip_without_weakening_bounds() {
        const SEED: u64 = 0xC623_7C88_0000_0008;
        let mut random = Lcg::new(SEED);
        for case_index in 0..512 {
            let body_len = random.next() as usize % 4_096;
            let body = vec![b'x'; body_len];
            let content_length = if random.next().is_multiple_of(2) {
                "Content-Length"
            } else {
                "content-length"
            };
            let content_type = if random.next().is_multiple_of(2) {
                "Content-Type: application/vscode-jsonrpc; charset=utf-8\r\n"
            } else {
                ""
            };
            let mut frame =
                format!("{content_length}: {body_len}\r\n{content_type}\r\n").into_bytes();
            frame.extend_from_slice(&body);
            let mut reader = Cursor::new(frame);
            assert_eq!(
                read_frame(&mut reader).unwrap(),
                Some(body),
                "seed={SEED:#x} case={case_index}"
            );
            assert_eq!(read_frame(&mut reader).unwrap(), None);
        }
    }

    #[test]
    fn exact_header_and_body_limits_are_accepted() {
        let prefix = b"Content-Length: 0\r\nContent-Type:";
        let suffix = b"\r\n\r\n";
        let padding = MAX_HEADER_BYTES - prefix.len() - suffix.len();
        let mut exact_header = Vec::with_capacity(MAX_HEADER_BYTES);
        exact_header.extend_from_slice(prefix);
        exact_header.extend(std::iter::repeat_n(b'x', padding));
        exact_header.extend_from_slice(suffix);
        assert_eq!(exact_header.len(), MAX_HEADER_BYTES);
        assert_eq!(
            read_frame(&mut Cursor::new(exact_header)).unwrap(),
            Some(Vec::new())
        );

        let mut exact_body = format!("Content-Length: {MAX_CONTENT_LENGTH}\r\n\r\n").into_bytes();
        exact_body.resize(exact_body.len() + MAX_CONTENT_LENGTH, b'x');
        assert_eq!(
            read_frame(&mut Cursor::new(exact_body))
                .expect("exact body limit should be accepted")
                .expect("exact body frame should exist")
                .len(),
            MAX_CONTENT_LENGTH
        );
    }

    struct Lcg(u64);

    impl Lcg {
        const fn new(seed: u64) -> Self {
            Self(seed)
        }

        fn next(&mut self) -> u64 {
            self.0 = self
                .0
                .wrapping_mul(2_862_933_555_777_941_757)
                .wrapping_add(3_037_000_493);
            self.0
        }
    }

    fn assert_frame_error(input: &[u8], expected: &str) {
        let error = read_frame(&mut Cursor::new(input))
            .expect_err("invalid frame should have been rejected");
        assert!(
            error.to_string().contains(expected),
            "expected error containing {expected:?}, received {error:?}"
        );
    }
}
