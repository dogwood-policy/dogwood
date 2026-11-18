use std::io::{Seek, SeekFrom, Write};

use crate::dogwood_cli::{CaptureFile, MAX_CAPTURE_STREAM_BYTES};

const WRITE_CHUNK_BYTES: usize = 64 * 1024;

#[test]
fn capture_accepts_exact_per_stream_maximum() {
    let mut capture =
        CaptureFile::create("exact-limit").expect("exact-limit capture should be created");
    let mut chunk = vec![0_u8; WRITE_CHUNK_BYTES];
    let chunk_count = MAX_CAPTURE_STREAM_BYTES as usize / WRITE_CHUNK_BYTES;

    for chunk_index in 0..chunk_count {
        chunk.fill(chunk_index as u8);
        capture
            .file
            .write_all(&chunk)
            .expect("exact-limit chunk should be written");
    }
    capture
        .file
        .flush()
        .expect("exact-limit capture should be flushed");

    let snapshot = capture
        .read_snapshot()
        .expect("exact-limit capture should be accepted");
    assert_eq!(snapshot.len(), MAX_CAPTURE_STREAM_BYTES as usize);
    let (chunks, remainder) = snapshot.as_chunks::<WRITE_CHUNK_BYTES>();
    for (chunk_index, actual) in chunks.iter().enumerate() {
        assert!(
            actual.iter().all(|&byte| byte == chunk_index as u8),
            "chunk {chunk_index} did not preserve its boundary content"
        );
    }
    assert!(remainder.is_empty());
}

#[test]
fn capture_rejects_one_byte_over_per_stream_maximum_before_reading() {
    let mut capture =
        CaptureFile::create("over-limit").expect("over-limit capture should be created");
    let observed_length = MAX_CAPTURE_STREAM_BYTES + 1;
    capture
        .file
        .set_len(observed_length)
        .expect("over-limit sparse capture should be sized");
    capture
        .file
        .seek(SeekFrom::Start(7))
        .expect("over-limit capture cursor should be positioned");

    let error = capture
        .read_snapshot()
        .expect_err("over-limit capture should be rejected");

    assert_eq!(
        capture
            .file
            .stream_position()
            .expect("over-limit capture cursor should be readable"),
        7,
        "over-limit rejection must happen before seeking or reading"
    );
    assert!(
        error.contains(&format!("{observed_length} bytes")),
        "error did not report observed length: {error}"
    );
    assert!(
        error.contains(&format!("{MAX_CAPTURE_STREAM_BYTES} bytes (16 MiB)")),
        "error did not report capture maximum: {error}"
    );
}
