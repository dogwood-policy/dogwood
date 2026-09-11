//! `ParsedPolicy::expanded_source` renders a policy's parsed, macro-expanded
//! form back to valid `.dw` text. The contract is semantic, not textual: the
//! rendered source must re-parse and lower to the *same* policy — same
//! decisions over any trace, with every macro inlined away.
//!
//! These are the behavioural gates for that contract, run over the embedded
//! corpora (so they need the `corpus` feature):
//!
//! - **Re-lower (L0):** the rendered form parses and lowers without error.
//! - **Decision equivalence (L2):** for every corpus trace, the rendered form
//!   decides identically to the original at every timepoint. The strongest,
//!   format-insensitive check — the primary gate.
//! - **No macro residue:** the expanded form re-lowers against a *macro-free*
//!   service, proving no macro reference survived.
//! - **Idempotence / determinism:** rendering is a stable fixed point and
//!   byte-identical across runs.

#![cfg(feature = "corpus")]

use dogwood_language::corpus::{TemporalCategory, macro_cases, temporal_cases};
use dogwood_language::{
    Authorizer, Decision, LoweredPolicySet, ParsedPolicySet, PolicySchema, ServiceSchema,
    parse_trace,
};

/// Build a service schema from an optional event-schema override and an
/// optional macro library.
fn service(event_schema: Option<&str>, macros: Option<&str>) -> ServiceSchema {
    let mut b = ServiceSchema::builder();
    if let Some(e) = event_schema {
        b = b.event_schema_str(e);
    }
    if let Some(m) = macros {
        b = b.macros_str(m);
    }
    b.build().expect("service schema builds")
}

/// Render every policy in `src` to its expanded source, concatenated back into
/// one document (the form a per-policy store would keep and re-lower).
fn expanded_document(src: &str, svc: &ServiceSchema) -> String {
    let parsed = ParsedPolicySet::parse(src, svc).expect("source parses");
    parsed
        .policies()
        .map(|p| p.expanded_source())
        .collect::<Vec<_>>()
        .join("\n\n")
}

/// The per-timepoint decision stream a document produces over one trace, or
/// `None` if the document does not lower or the trace does not parse (the case
/// is then not comparable and is skipped by the caller).
fn decisions(
    doc: &str,
    svc: &ServiceSchema,
    schema: &PolicySchema,
    trace_log: &str,
) -> Option<Vec<Option<Decision>>> {
    let lowered = LoweredPolicySet::from_str(doc, svc, schema).ok()?;
    let events = parse_trace(trace_log).ok()?;
    let mut authorizer = Authorizer::new(lowered);
    Some(
        events
            .iter()
            .map(|e| authorizer.is_authorized(e).map(|r| r.decision()))
            .collect(),
    )
}

/// L0 + L2 over the passing temporal corpus: the rendered form re-lowers and
/// decides identically to the original at every timepoint of every trace.
#[test]
fn expanded_source_roundtrips_over_the_passing_temporal_corpus() {
    let mut fails = Vec::new();
    for case in temporal_cases()
        .into_iter()
        .filter(|c| c.category == TemporalCategory::Passing)
    {
        let svc = service(case.event_schema_src.as_deref(), None);
        let Ok(schema) = PolicySchema::from_cedarschema_str(&case.schema_src) else {
            continue;
        };

        let rendered = expanded_document(&case.policy_src, &svc);

        // L0: the rendered form must re-lower.
        if LoweredPolicySet::from_str(&rendered, &svc, &schema).is_err() {
            fails.push(format!("{}: rendered form does not re-lower", case.name));
            continue;
        }

        // L2: decision streams must match over every trace.
        for tr in &case.traces {
            let Some(orig) = decisions(&case.policy_src, &svc, &schema, &tr.trace_log) else {
                continue; // original not comparable; skip
            };
            if decisions(&rendered, &svc, &schema, &tr.trace_log).as_ref() != Some(&orig) {
                fails.push(format!(
                    "{}/trace_{}: rendered decision stream differs from original",
                    case.name, tr.index
                ));
            }
        }
    }
    assert!(
        fails.is_empty(),
        "{} corpus case(s) failed the expanded-source round-trip:\n{}",
        fails.len(),
        fails.join("\n")
    );
}

/// Over the macro corpus: the expanded form must (a) re-lower against a
/// **macro-free** service — proving no macro reference survived — and (b)
/// decide identically to the original (which is lowered *with* the library).
#[test]
fn expanded_source_leaves_no_macro_residue_over_the_macro_corpus() {
    let mut fails = Vec::new();
    for case in macro_cases() {
        let with_macros = service(case.event_schema_src.as_deref(), case.macros_src.as_deref());
        let macro_free = service(case.event_schema_src.as_deref(), None);
        let Ok(schema) = PolicySchema::from_cedarschema_str(&case.schema_src) else {
            continue;
        };

        let rendered = expanded_document(&case.policy_src, &with_macros);

        // No residue: the expanded form lowers with NO macro library available.
        if LoweredPolicySet::from_str(&rendered, &macro_free, &schema).is_err() {
            fails.push(format!(
                "{}: expanded form is not macro-free (fails to lower without the library)",
                case.name
            ));
            continue;
        }

        for tr in &case.traces {
            let Some(orig) = decisions(&case.policy_src, &with_macros, &schema, &tr.trace_log)
            else {
                continue;
            };
            if decisions(&rendered, &macro_free, &schema, &tr.trace_log).as_ref() != Some(&orig) {
                fails.push(format!(
                    "{}/trace_{}: expanded decision stream differs from original",
                    case.name, tr.index
                ));
            }
        }
    }
    assert!(
        fails.is_empty(),
        "{} macro case(s) failed the expanded-source round-trip:\n{}",
        fails.len(),
        fails.join("\n")
    );
}

/// Rendering is a fixed point: expanding an already-expanded document changes
/// nothing.
#[test]
fn expanded_source_is_idempotent() {
    for case in temporal_cases()
        .into_iter()
        .filter(|c| c.category == TemporalCategory::Passing)
    {
        let svc = service(case.event_schema_src.as_deref(), None);
        let once = expanded_document(&case.policy_src, &svc);
        let twice = expanded_document(&once, &svc);
        assert_eq!(
            once, twice,
            "{}: expanded_source is not idempotent",
            case.name
        );
    }
}

/// Rendering is deterministic: the same input yields byte-identical output.
#[test]
fn expanded_source_is_deterministic() {
    for case in temporal_cases()
        .into_iter()
        .filter(|c| c.category == TemporalCategory::Passing)
    {
        let svc = service(case.event_schema_src.as_deref(), None);
        let a = expanded_document(&case.policy_src, &svc);
        let b = expanded_document(&case.policy_src, &svc);
        assert_eq!(a, b, "{}: expanded_source is not deterministic", case.name);
    }
}
