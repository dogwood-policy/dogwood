//! Whole-corpus sliced-versus-unsliced differential.
//!
//! Shared checks compare verdicts with committed expectations, require the
//! computed set to match the map exactly, and validate skipped leaves against an
//! independent Cedar action-hierarchy oracle.

#[path = "support/slicing.rs"]
mod support;

use support::{check_all, corpus};

#[test]
fn slicing_never_changes_a_verdict_and_skips_exactly_the_unreadable_leaves() {
    let cases = corpus();
    assert!(
        cases.len() > 100,
        "the corpus did not load — {} cases found",
        cases.len()
    );

    let (totals, failures) = check_all(&cases);
    eprintln!("action-slicing corpus differential: {totals:?}");
    assert!(
        failures.is_empty(),
        "{} failure(s):\n\n{}",
        failures.len(),
        failures.join("\n\n")
    );

    // Ensure the differential exercised real exclusions, including a true leaf.
    assert!(totals.traces > 100, "too few traces replayed: {totals:?}");
    assert!(totals.decisions > 100, "too few decisions: {totals:?}");
    assert!(
        totals.sliced_leaves < totals.unsliced_leaves,
        "slicing computed no fewer leaves than the unsliced run: {totals:?}"
    );
    assert!(
        totals.sliced_decisions > 0,
        "no decision skipped a leaf — the differential proved nothing: {totals:?}"
    );
    assert!(
        totals.zero_leaf_decisions > 0,
        "no decision skipped EVERY leaf, so the zero-compute floor is untested: {totals:?}"
    );
    assert!(
        totals.suppressed_true_decisions > 0,
        "no decision skipped a leaf whose unsliced value was `true`; the verdict \
         comparison never had a suppressed `true` to expose: {totals:?}"
    );
}
