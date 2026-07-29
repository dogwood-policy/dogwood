//! A macro-expansion error originating in the **macro library** (not the
//! policy) must self-render against the *library* source, not the `.dw` policy
//! source.
//!
//! Regression test for C1: `lower()` runs macro expansion over the merged set
//! of policy-authored and library-authored `def`s, but stamped every macro
//! error with the policy source. A library def's span indexes the *library*
//! text, so the error would underline the wrong region of the policy.

use dogwood_language::{Error, LoweredPolicySet, PolicySchema, ServiceSchema};

/// A macro library that defines a macro under a **reserved** name (`decimal`
/// is a Cedar built-in). This is rejected during macro expansion — an
/// `expand()`-time error, not a parse error — and its span points into *this*
/// library text.
const BROKEN_LIBRARY: &str = r#"def cedar decimal(?x) { ?x > 0 } ;"#;

/// A perfectly valid policy. Deliberately shares no text with the library and
/// is *shorter* than the library up to the offending span, so a span taken
/// against the wrong source lands on different bytes.
const VALID_POLICY: &str = r#"permit (principal, action, resource);"#;

fn lower_with_library(policy: &str, macros: &str) -> Result<LoweredPolicySet, Error> {
    let service = ServiceSchema::builder()
        .macros_str(macros)
        .build()
        .expect("service schema builds");
    let policy_schema = PolicySchema::from_cedarschema_str("").expect("policy schema builds");
    LoweredPolicySet::from_str(policy, &service, &policy_schema)
}

#[test]
fn macro_library_error_renders_against_the_library_source() {
    let err = match lower_with_library(VALID_POLICY, BROKEN_LIBRARY) {
        Ok(_) => panic!("a reserved macro name in the library must be rejected"),
        Err(e) => e,
    };

    let macro_err = match &err {
        Error::Macro(m) => m,
        other => panic!("expected a macro error, got: {other}"),
    };

    let loc = macro_err.location();

    // The error must carry the LIBRARY source, not the policy source.
    assert_eq!(
        loc.source(),
        BROKEN_LIBRARY,
        "macro-library error should embed the library source, not the policy \
         source (got a {}-byte source)",
        loc.source().len()
    );

    // And its span must point at the offending `decimal` token within that
    // library source — proof the span and the embedded source agree.
    let span = loc.span();
    let (start, end) = (span.offset(), span.offset() + span.len());
    assert!(
        end <= BROKEN_LIBRARY.len(),
        "span {start}..{end} is out of range for the library source \
         (len {})",
        BROKEN_LIBRARY.len()
    );
    let sliced = &BROKEN_LIBRARY[start..end];
    assert!(
        sliced.contains("decimal"),
        "span should cover the reserved `decimal` def in the library; \
         got {sliced:?} ({start}..{end})"
    );
}
