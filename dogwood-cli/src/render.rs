//! Output rendering for each command, in both human and JSON form.
//!
//! JSON is `serde_json` over the ops modules' `Serialize` reports — one stable
//! object per command. Human output is a compact text summary, and for a fatal
//! [`OpError`] it uses miette's graphical handler so the offending `.dw`
//! (or schema / trace) span is underlined.

use crate::error::OpError;
use crate::ops::{
    CheckParseReport, LowerArtifacts, ReplayReport, SchemaCheckReport, ValidateReport, Verdict,
};
use crate::{Emit, Format};

/// Serialize any report to pretty JSON on stdout.
fn json(value: &impl serde::Serialize) {
    // A report is a plain owned struct of scalars/strings/vecs; serialization
    // cannot fail in practice, but degrade gracefully rather than panic.
    match serde_json::to_string_pretty(value) {
        Ok(s) => println!("{s}"),
        Err(e) => eprintln!("error: could not serialize report: {e}"),
    }
}

/// Render a fatal error. Human mode uses miette's graphical report handler
/// (underlined snippet); JSON mode emits the serializable error.
pub fn error(err: &OpError, format: Format) {
    match format {
        Format::Json => json(err),
        Format::Human => {
            // `miette::Report` renders the diagnostic with its source snippet.
            let report = miette::Report::new(err.clone());
            eprintln!("{report:?}");
        }
    }
}

pub fn check_parse(report: &CheckParseReport, format: Format) {
    if format == Format::Json {
        return json(report);
    }
    println!(
        "OK: parsed {} polic{}.",
        report.policy_count,
        if report.policy_count == 1 { "y" } else { "ies" }
    );
    for (i, p) in report.policies.iter().enumerate() {
        let mut notes = Vec::new();
        if p.uses_temporal {
            notes.push(format!("{} temporal leaf/leaves", p.temporal_count));
        }
        if !p.provider_invocations.is_empty() {
            notes.push(format!("{} provider call(s)", p.provider_invocations.len()));
        }
        if !notes.is_empty() {
            println!("  policy {i}: {}", notes.join(", "));
        }
        for undeclared in &p.undeclared_providers {
            println!("  policy {i}: warning: undeclared provider `{undeclared}`");
        }
    }
}

pub fn validate(report: &ValidateReport, format: Format) {
    if format == Format::Json {
        return json(report);
    }
    for e in &report.errors {
        println!("error: {}", e.message);
    }
    for w in &report.warnings {
        println!("warning: {}", w.message);
    }
    if report.passed_without_warnings {
        println!("OK: validation passed with no errors or warnings.");
    } else if report.passed {
        println!(
            "OK: validation passed ({} warning(s)).",
            report.warnings.len()
        );
    } else {
        println!(
            "FAILED: {} error(s), {} warning(s).",
            report.errors.len(),
            report.warnings.len()
        );
    }
}

pub fn lower(artifacts: &LowerArtifacts, emit: Emit, format: Format) {
    if format == Format::Json {
        return json(artifacts);
    }
    match emit {
        Emit::CedarPolicies => print!("{}", artifacts.cedar_policies),
        Emit::CedarSchema => print!("{}", artifacts.cedar_schema),
        Emit::CedarJson => print!("{}", artifacts.cedar_schema_json),
        Emit::Both => {
            println!("// ─── Cedar policies ───");
            print!("{}", artifacts.cedar_policies);
            println!("\n// ─── Augmented schema ───");
            print!("{}", artifacts.cedar_schema);
        }
    }
    if !artifacts.self_contained {
        eprintln!(
            "note: this Cedar is NOT self-contained — temporal/provider fields were hoisted \
             ({} temporal, {} provider) and need Dogwood at authorize time.",
            artifacts.temporal_fields.len(),
            artifacts.provider_fields.len()
        );
    }
}

pub fn schema_check(report: &SchemaCheckReport, format: Format) {
    if format == Format::Json {
        return json(report);
    }
    for w in &report.warnings {
        println!("warning: {w}");
    }
    if report.warnings.is_empty() {
        println!("OK: {} schema is valid.", report.kind);
    } else {
        println!(
            "OK: {} schema is valid ({} warning(s)).",
            report.kind,
            report.warnings.len()
        );
    }
}

pub fn replay(report: &ReplayReport, format: Format) {
    if format == Format::Json {
        return json(report);
    }
    for v in &report.verdicts {
        let decision = match v.verdict {
            Verdict::Allow => "ALLOW",
            Verdict::Deny => "DENY",
        };
        print!("@{} (time point {}): {decision}", v.timestamp, v.index);
        if !v.determining_rules.is_empty() {
            let rules: Vec<String> = v.determining_rules.iter().map(|r| r.to_string()).collect();
            print!("  [rules: {}]", rules.join(", "));
        }
        println!();
        for e in &v.errors {
            println!("    error: {e}");
        }
    }
}
