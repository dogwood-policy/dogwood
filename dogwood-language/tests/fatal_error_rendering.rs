//! The fatal-error channel (`LoweredPolicySet::from_str` / `ServiceSchema::build`)
//! is a self-rendering `miette::Diagnostic`, mirroring Cedar's parse errors.
//!
//! Two guarantees, one per test:
//!   * **matchable** — a caller can match `Error::Parse(_)` and iterate the
//!     located sub-errors (the old flat `String` could not be inspected);
//!   * **self-rendering** — `miette::Report::new(err)` underlines the
//!     offending `.dw` span with **no** `with_source_code`, because each leaf
//!     carries its own source (as Cedar's `ParseError` does).

use dogwood_language::{Error, LoweredPolicySet, PolicySchema, ServiceSchema};

// `LoweredPolicySet` is named only in the return type of
// `LoweredPolicySet::from_str`; the import is used via the associated function
// call below.

/// A syntactically broken policy: `permitt` is not a valid effect keyword.
const BROKEN: &str = r#"permitt (principal, action, resource);"#;

/// Parse the broken source and return the error. `LoweredPolicySet` is
/// intentionally not `Debug`, so we unwrap the `Err` by hand rather than via
/// `expect_err`.
fn broken_error() -> Error {
    let service = ServiceSchema::defaults();
    let policy_schema =
        PolicySchema::from_cedarschema_str("").expect("empty Cedar schema is valid");
    match LoweredPolicySet::from_str(BROKEN, &service, &policy_schema) {
        Ok(_) => panic!("broken source must fail to parse"),
        Err(e) => e,
    }
}

#[test]
fn parse_error_is_matchable_and_located() {
    let err = broken_error();

    // #3: the variant is public and matchable, and its payload is inspectable
    // (the old `Error::Parse(String)` could only be `Display`ed).
    let Error::Parse(errs) = err else {
        panic!("expected a parse error, got: {err}");
    };

    let located: Vec<_> = errs.iter().collect();
    assert!(!located.is_empty(), "ParseErrors is non-empty");

    // Each leaf carries a `.dw` location pointing into the original source.
    let first = located[0];
    let span = first.location().span();
    assert!(
        span.offset() < BROKEN.len(),
        "the parse error's span must point inside the source (offset {} vs len {})",
        span.offset(),
        BROKEN.len()
    );
}

#[test]
fn parse_error_self_renders_without_with_source_code() {
    let err = broken_error();

    // #2: a miette Report over the error renders the underlined snippet using
    // the error's *own* embedded source — no `.with_source_code(BROKEN)`.
    let report = miette::Report::new(err);
    let rendered = format!("{report:?}");

    // The graphical render includes a slice of the offending source line, which
    // is only possible if the error carried its own `source_code`.
    assert!(
        rendered.contains("permitt"),
        "self-rendered diagnostic should include the offending source; got:\n{rendered}"
    );
}
