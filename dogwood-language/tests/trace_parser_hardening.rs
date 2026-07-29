//! Regression tests for the trace-log parser DoS/panic holes found in the
//! security self-audit (findings C2 and C4).
//!
//! `parse_trace` consumes `.log` text, which the threat model designates the
//! most-untrusted input (an attacker who takes actions in the guarded system
//! generates events). A malformed line must produce a clean `Err`, never a
//! process-aborting panic:
//!
//!   * **C4** — a line whose last `)` precedes its first `(` (e.g. `@0 )(`)
//!     sliced a reversed byte range and panicked. Fixed with an ordering guard
//!     (interpreter/log_parse.rs).
//!   * **C2** — a deeply nested logged value (`[[[[…]]]]`) recursed once per
//!     level with no cap and overflowed the stack (an uncatchable abort). Fixed
//!     with a depth limit that returns `Err` (interpreter/log_parse.rs).

use dogwood_language::parse_trace;

/// C4 — a reversed-bracket line returns `Err`, not a panic. (A panic here would
/// be a slice-out-of-bounds, which aborts in every build profile.)
#[test]
fn reversed_brackets_line_is_a_clean_error() {
    let result = parse_trace("@0 )(");
    assert!(
        result.is_err(),
        "a line whose `)` precedes its `(` must be a parse error, not a panic"
    );
}

/// C4 — a couple more malformed shapes that exercise the group-slice path must
/// also be clean errors rather than panics.
#[test]
fn assorted_malformed_group_lines_are_clean_errors() {
    for line in ["@0 )text(", "@5 abc)(def", "@1 ))((", "@2 )"] {
        let result = parse_trace(line);
        assert!(
            result.is_err(),
            "malformed group line {line:?} must be a parse error, not a panic"
        );
    }
}

/// C2 — a pathologically deep logged value returns `Err` instead of
/// overflowing the stack. The depth here (5000) is far past the parser's cap
/// and, before the fix, reliably aborted the process with a stack overflow.
/// If this test *returns at all* (pass or assertion failure) rather than
/// aborting the test binary, the recursion is bounded.
#[test]
fn deeply_nested_value_is_a_clean_error_not_a_stack_overflow() {
    let depth = 5000;
    let nested = format!("{}{}", "[".repeat(depth), "]".repeat(depth));
    let line = format!(r#"@0 Svc::Action::"Read"::request(input: {nested})"#);
    let result = parse_trace(&line);
    assert!(
        result.is_err(),
        "a {depth}-deep nested value must be rejected with an Err, not abort the process"
    );
}

/// C2 — the depth guard also applies to nested objects, and a legitimately
/// shallow value still parses fine (the cap does not reject normal input).
#[test]
fn shallow_nested_value_still_parses() {
    let line = r#"@0 Svc::Action::"Read"::request(input: { a: [1, 2, { b: "x" }] })"#;
    let result = parse_trace(line);
    assert!(
        result.is_ok(),
        "an ordinary shallow nested value must still parse, got: {result:?}"
    );
}
