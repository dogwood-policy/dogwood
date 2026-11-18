// dogwood-lsp handles Unix paths and file URIs only, so its tests run on Unix.
#![cfg(unix)]

const MATRIX: &str = include_str!("../docs/protocol-conformance.md");

const REQUIRED_ROWS: [&str; 25] = [
    "CAP-UTF16",
    "CAP-SYNC",
    "CAP-SEMANTIC-LEGEND",
    "CAP-SEMANTIC-FULL",
    "CAP-NO-EXTRA",
    "DYN-WATCH",
    "TEST-GATE",
    "ERR-PREINIT",
    "ERR-DUPINIT",
    "ERR-INVALID-PARAMS",
    "ERR-UNKNOWN",
    "ERR-DOC-UNOPENED",
    "ERR-DOC-CLOSED",
    "ERR-DOC-DEPENDENCY",
    "ERR-TOKEN-LIMIT",
    "ERR-REQUEST-CANCELLED",
    "ERR-CONTENT-MODIFIED",
    "ERR-SERVER-CANCELLED",
    "ERR-SHUTDOWN",
    "LIFE-SHUTDOWN-EXIT",
    "LIFE-EARLY-EXIT",
    "RESP-SINGLE",
    "FRAME-HEADER",
    "FRAME-BODY",
    "FRAME-STDOUT",
];

#[test]
fn protocol_matrix_has_one_evidence_row_for_every_required_contract() {
    for id in REQUIRED_ROWS {
        let marker = format!("| `{id}` |");
        assert_eq!(
            MATRIX.matches(&marker).count(),
            1,
            "protocol matrix must contain exactly one row for {id}"
        );
        let row = MATRIX
            .lines()
            .find(|line| line.starts_with(&marker))
            .expect("the required row was counted above");
        let evidence = row
            .split('|')
            .nth(3)
            .expect("matrix rows must have an evidence column")
            .trim();
        assert!(
            evidence.starts_with("process: "),
            "{id} evidence must begin with the `process:` layer marker"
        );
        let process_evidence = evidence
            .split_once("; supplemental")
            .map_or(evidence, |(process, _)| process);
        let citations = process_evidence
            .strip_prefix("process: ")
            .expect("the process prefix was checked above")
            .split("; ")
            .collect::<Vec<_>>();
        assert!(!citations.is_empty(), "{id} must cite process evidence");
        for citation in citations {
            validate_process_citation(id, citation);
        }
    }
    for excluded in [
        "documentFormattingProvider",
        "completionProvider",
        "hoverProvider",
        "definitionProvider",
        "codeActionProvider",
        "diagnosticProvider",
        "semanticTokens/full/delta",
        "workspace/semanticTokens/refresh",
    ] {
        assert!(
            !MATRIX.contains(&format!("advertises `{excluded}`")),
            "matrix must not claim excluded capability {excluded}"
        );
    }
}

fn validate_process_citation(id: &str, citation: &str) {
    let citation = citation
        .strip_prefix('`')
        .and_then(|citation| citation.strip_suffix('`'))
        .unwrap_or_else(|| {
            panic!("{id} process evidence must be a backtick-quoted test citation, not prose")
        });
    let (target, test) = citation
        .split_once("::")
        .unwrap_or_else(|| panic!("{id} process citation must use `target::test`: {citation}"));
    assert!(
        valid_rust_identifier(test),
        "{id} process citation has an invalid test name: {citation}"
    );

    let source = compiled_process_source(target).unwrap_or_else(|| {
        panic!("{id} process citation names a non-process test target: {target}")
    });
    assert!(
        source.contains(&format!("#[test]\nfn {test}(")),
        "{id} process citation does not resolve to a test in {target}: {test}"
    );
}

fn valid_rust_identifier(identifier: &str) -> bool {
    let mut bytes = identifier.bytes();
    bytes
        .next()
        .is_some_and(|byte| byte == b'_' || byte.is_ascii_alphabetic())
        && bytes.all(|byte| byte == b'_' || byte.is_ascii_alphanumeric())
}

fn compiled_process_source(target: &str) -> Option<&'static str> {
    match target {
        "stdio_black_box" => Some(include_str!("stdio_black_box.rs")),
        "m4_diagnostics" => Some(include_str!("m4_diagnostics.rs")),
        "m6_process" => Some(include_str!("m6_process.rs")),
        "m7_concurrency" => Some(include_str!("m7_concurrency.rs")),
        "m7_incremental" => Some(include_str!("m7_incremental.rs")),
        _ => None,
    }
}
