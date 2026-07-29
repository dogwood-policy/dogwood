//! Error-message differential test: Dogwood (pest) vs Cedar (lalrpop).
//!
//! For pure-Cedar policies that are syntactically invalid, this test feeds the
//! same broken input through both parsers and compares their error messages.
//! The goal is to identify divergences so we can bring Dogwood's parse errors
//! to parity with Cedar's — same information, same phrasing where possible.
//!
//! The test is structured as a **measurement** (not a hard assertion): it
//! prints a categorized report of which cases match, which diverge, and what
//! both sides said. A companion hard-assertion test (`parity_regressions`)
//! locks in cases where we've already achieved parity so they don't regress.
//!
//! # Error categories exercised
//!
//! 1. **Top-level structure** — effect keyword, parens, semicolons
//! 2. **Scope** — variables, operators, entity UIDs, commas
//! 3. **Conditions** — `when`/`unless` keyword, braces, body
//! 4. **Expressions** — operators, operands, delimiters, if/then/else,
//!    has/like/is, method calls, records, sets
//! 5. **Entity references** — namespace, `::`, quoting, slots
//! 6. **Annotations** — malformed `@` annotations

use cedar_policy_core::parser::parse_policyset;
use dogwood_language::{Error, LoweredPolicySet, PolicySchema, ServiceSchema};

/// Parse through Dogwood's pipeline and return the error message(s), or None
/// if it unexpectedly succeeds.
fn dogwood_error(src: &str) -> Option<Vec<String>> {
    let service = ServiceSchema::defaults();
    let policy_schema = PolicySchema::from_cedarschema_str("").ok()?;
    match LoweredPolicySet::from_str(src, &service, &policy_schema) {
        Ok(_) => None,
        Err(e) => {
            let mut messages = Vec::new();
            match &e {
                Error::Parse(errs) => {
                    for err in errs.iter() {
                        messages.push(err.to_string());
                    }
                }
                other => messages.push(other.to_string()),
            }
            Some(messages)
        }
    }
}

/// Parse through Cedar's own parser and return the error message(s), or None
/// if it unexpectedly succeeds.
fn cedar_error(src: &str) -> Option<Vec<String>> {
    match parse_policyset(src) {
        Ok(_) => None,
        Err(errs) => {
            let messages: Vec<String> = errs.iter().map(|e| e.to_string()).collect();
            Some(messages)
        }
    }
}

/// A single test case: a label, the broken source, and optionally a note
/// about what error position is being exercised.
struct Case {
    label: &'static str,
    src: &'static str,
    category: &'static str,
}

/// All broken pure-Cedar policies, organized by grammar position.
fn cases() -> Vec<Case> {
    vec![
        // ─── 1. Top-level structure ─────────────────────────────────────
        Case {
            label: "invalid_effect_keyword",
            src: r#"permitt (principal, action, resource);"#,
            category: "top-level",
        },
        Case {
            label: "missing_open_paren",
            src: r#"permit principal, action, resource);"#,
            category: "top-level",
        },
        Case {
            label: "missing_close_paren",
            src: r#"permit (principal, action, resource;"#,
            category: "top-level",
        },
        Case {
            label: "missing_semicolon",
            src: r#"permit (principal, action, resource)"#,
            category: "top-level",
        },
        Case {
            label: "trailing_garbage",
            src: r#"permit (principal, action, resource); blah"#,
            category: "top-level",
        },
        Case {
            label: "just_garbage",
            src: r#"@@@ not a policy"#,
            category: "top-level",
        },
        Case {
            label: "double_effect",
            src: r#"permit forbid (principal, action, resource);"#,
            category: "top-level",
        },
        Case {
            label: "effect_is_number",
            src: r#"42 (principal, action, resource);"#,
            category: "top-level",
        },
        // ─── 2. Scope ───────────────────────────────────────────────────
        Case {
            label: "missing_comma_in_scope",
            src: r#"permit (principal action, resource);"#,
            category: "scope",
        },
        Case {
            label: "extra_scope_variable",
            src: r#"permit (principal, action, resource, extra);"#,
            category: "scope",
        },
        Case {
            label: "invalid_scope_operator",
            src: r#"permit (principal > User::"alice", action, resource);"#,
            category: "scope",
        },
        Case {
            label: "malformed_entity_uid_unquoted",
            src: r#"permit (principal == User::alice, action, resource);"#,
            category: "scope",
        },
        Case {
            label: "scope_missing_entity_after_eq",
            src: r#"permit (principal ==, action, resource);"#,
            category: "scope",
        },
        Case {
            label: "scope_double_comma",
            src: r#"permit (principal,, action, resource);"#,
            category: "scope",
        },
        Case {
            label: "scope_in_missing_entity",
            src: r#"permit (principal in, action, resource);"#,
            category: "scope",
        },
        Case {
            label: "scope_in_malformed_set",
            src: r#"permit (principal, action in [Action::"Read" Action::"Write"], resource);"#,
            category: "scope",
        },
        // ─── 3. Conditions ──────────────────────────────────────────────
        Case {
            label: "invalid_condition_keyword",
            src: r#"permit (principal, action, resource) whenn { true };"#,
            category: "condition",
        },
        Case {
            label: "missing_open_brace",
            src: r#"permit (principal, action, resource) when true };"#,
            category: "condition",
        },
        Case {
            label: "missing_close_brace",
            src: r#"permit (principal, action, resource) when { true ;"#,
            category: "condition",
        },
        Case {
            label: "empty_condition_body",
            src: r#"permit (principal, action, resource) when { };"#,
            category: "condition",
        },
        Case {
            label: "condition_body_missing_expr",
            src: r#"permit (principal, action, resource) when { && };"#,
            category: "condition",
        },
        Case {
            label: "multiple_exprs_no_operator",
            src: r#"permit (principal, action, resource) when { true false };"#,
            category: "condition",
        },
        // ─── 4. Expressions — operators & operands ──────────────────────
        Case {
            label: "invalid_operator",
            src: r#"permit (principal, action, resource) when { context.x @ 5 };"#,
            category: "expression",
        },
        Case {
            label: "missing_rhs_operand",
            src: r#"permit (principal, action, resource) when { context.x == };"#,
            category: "expression",
        },
        Case {
            label: "double_operator",
            src: r#"permit (principal, action, resource) when { context.x == == 5 };"#,
            category: "expression",
        },
        Case {
            label: "leading_binary_operator",
            src: r#"permit (principal, action, resource) when { && true };"#,
            category: "expression",
        },
        Case {
            label: "single_equals_hint",
            src: r#"permit (principal, action, resource) when { context.x = 5 };"#,
            category: "expression",
        },
        // ─── 4b. Expressions — delimiters ───────────────────────────────
        Case {
            label: "unclosed_paren",
            src: r#"permit (principal, action, resource) when { (true };"#,
            category: "expression",
        },
        Case {
            label: "unclosed_string",
            src: r#"permit (principal, action, resource) when { "hello };"#,
            category: "expression",
        },
        Case {
            label: "unclosed_set",
            src: r#"permit (principal, action, resource) when { [1, 2 };"#,
            category: "expression",
        },
        Case {
            label: "unclosed_record",
            src: r#"permit (principal, action, resource) when { {"a": 1 };"#,
            category: "expression",
        },
        Case {
            label: "extra_close_paren",
            src: r#"permit (principal, action, resource) when { true) };"#,
            category: "expression",
        },
        // ─── 4c. Expressions — if/then/else ─────────────────────────────
        Case {
            label: "if_missing_then",
            src: r#"permit (principal, action, resource) when { if true 1 else 2 };"#,
            category: "expression",
        },
        Case {
            label: "if_missing_else",
            src: r#"permit (principal, action, resource) when { if true then 1 };"#,
            category: "expression",
        },
        Case {
            label: "if_missing_condition",
            src: r#"permit (principal, action, resource) when { if then 1 else 2 };"#,
            category: "expression",
        },
        // ─── 4d. Expressions — has / like / is ──────────────────────────
        Case {
            label: "has_missing_rhs",
            src: r#"permit (principal, action, resource) when { context has };"#,
            category: "expression",
        },
        Case {
            label: "like_missing_pattern",
            src: r#"permit (principal, action, resource) when { context.x like };"#,
            category: "expression",
        },
        Case {
            label: "is_missing_type",
            src: r#"permit (principal, action, resource) when { principal is };"#,
            category: "expression",
        },
        Case {
            label: "is_in_missing_entity",
            src: r#"permit (principal, action, resource) when { principal is User in };"#,
            category: "expression",
        },
        // ─── 4e. Expressions — member access & method calls ─────────────
        Case {
            label: "dangling_dot",
            src: r#"permit (principal, action, resource) when { context. };"#,
            category: "expression",
        },
        Case {
            label: "dot_number",
            src: r#"permit (principal, action, resource) when { context.42 };"#,
            category: "expression",
        },
        Case {
            label: "method_call_unclosed",
            src: r#"permit (principal, action, resource) when { context.x.contains(1 };"#,
            category: "expression",
        },
        Case {
            label: "method_call_missing_comma",
            src: r#"permit (principal, action, resource) when { context.x.containsAll([1] [2]) };"#,
            category: "expression",
        },
        Case {
            label: "index_access_unclosed",
            src: r#"permit (principal, action, resource) when { context["key" };"#,
            category: "expression",
        },
        // ─── 4f. Expressions — records & sets ───────────────────────────
        Case {
            label: "record_missing_colon",
            src: r#"permit (principal, action, resource) when { {"a" 1} };"#,
            category: "expression",
        },
        Case {
            label: "record_missing_value",
            src: r#"permit (principal, action, resource) when { {"a": } };"#,
            category: "expression",
        },
        Case {
            label: "set_missing_comma",
            src: r#"permit (principal, action, resource) when { [1 2 3] };"#,
            category: "expression",
        },
        Case {
            label: "record_duplicate_key",
            src: r#"permit (principal, action, resource) when { {"a": 1, "a": 2, "a": 3} };"#,
            category: "acceptance-divergence",
        },
        // ─── 5. Entity references ───────────────────────────────────────
        Case {
            label: "entity_missing_namespace",
            src: r#"permit (principal == ::"alice", action, resource);"#,
            category: "entity-ref",
        },
        Case {
            label: "entity_missing_id",
            src: r#"permit (principal == User::, action, resource);"#,
            category: "entity-ref",
        },
        Case {
            label: "entity_triple_colon",
            src: r#"permit (principal == User:::"alice", action, resource);"#,
            category: "entity-ref",
        },
        Case {
            label: "invalid_slot",
            src: r#"permit (?bogus, action, resource);"#,
            category: "entity-ref",
        },
        // ─── 6. Annotations ─────────────────────────────────────────────
        Case {
            label: "annotation_missing_at",
            src: r#"id("policy1") permit (principal, action, resource);"#,
            category: "annotation",
        },
        Case {
            label: "annotation_unclosed_value",
            src: r#"@id("policy1" permit (principal, action, resource);"#,
            category: "annotation",
        },
        Case {
            label: "annotation_no_ident",
            src: r#"@("policy1") permit (principal, action, resource);"#,
            category: "annotation",
        },
        // ─── 7. Numeric & literal edge cases ────────────────────────────
        Case {
            label: "number_overflow",
            src: r#"permit (principal, action, resource) when { 99999999999999999999 > 0 };"#,
            category: "literal",
        },
        Case {
            label: "negative_sign_standalone",
            src: r#"permit (principal, action, resource) when { - };"#,
            category: "literal",
        },
        Case {
            label: "bang_standalone",
            src: r#"permit (principal, action, resource) when { ! };"#,
            category: "literal",
        },
        // ─── 8. Macro definitions (def_decl) ────────────────────────────
        Case {
            label: "def_missing_kind",
            src: r#"def my_macro() { true };"#,
            category: "def",
        },
        Case {
            label: "def_missing_name",
            src: r#"def cedar () { true };"#,
            category: "def",
        },
        Case {
            label: "def_missing_open_paren",
            src: r#"def cedar my_macro) { true };"#,
            category: "def",
        },
        Case {
            label: "def_missing_close_paren",
            src: r#"def cedar my_macro( { true };"#,
            category: "def",
        },
        Case {
            label: "def_missing_open_brace",
            src: r#"def cedar my_macro() true };"#,
            category: "def",
        },
        Case {
            label: "def_missing_close_brace",
            src: r#"def cedar my_macro() { true ;"#,
            category: "def",
        },
        Case {
            label: "def_missing_semicolon",
            src: "def cedar my_macro() { true }\npermit (principal, action, resource);",
            category: "def",
        },
        Case {
            label: "def_invalid_kind",
            src: r#"def python my_macro() { true };"#,
            category: "def",
        },
        // ─── 9. Or / And / Add / Mult operators ────────────────────────
        Case {
            label: "or_double_pipe",
            src: r#"permit (principal, action, resource) when { true || || false };"#,
            category: "operator",
        },
        Case {
            label: "or_missing_rhs",
            src: r#"permit (principal, action, resource) when { true || };"#,
            category: "operator",
        },
        Case {
            label: "and_missing_rhs",
            src: r#"permit (principal, action, resource) when { true && };"#,
            category: "operator",
        },
        Case {
            label: "add_double_plus",
            src: r#"permit (principal, action, resource) when { 1 + + 2 > 0 };"#,
            category: "operator",
        },
        Case {
            label: "add_missing_rhs",
            src: r#"permit (principal, action, resource) when { 1 + };"#,
            category: "operator",
        },
        Case {
            label: "mult_missing_rhs",
            src: r#"permit (principal, action, resource) when { 1 * };"#,
            category: "operator",
        },
        Case {
            label: "mult_trailing_percent",
            src: r#"permit (principal, action, resource) when { 10 % };"#,
            category: "operator",
        },
        // ─── 10. Entity ref_record ──────────────────────────────────────
        Case {
            label: "ref_record_missing_colon",
            src: r#"permit (principal == User::{ name "alice" }, action, resource);"#,
            category: "entity-ref",
        },
        Case {
            label: "ref_record_missing_value",
            src: r#"permit (principal == User::{ name: }, action, resource);"#,
            category: "entity-ref",
        },
        Case {
            label: "ref_record_unclosed",
            src: r#"permit (principal == User::{ name: "alice" , action, resource);"#,
            category: "entity-ref",
        },
        // ─── 11. Record if-key form ─────────────────────────────────────
        Case {
            label: "rec_init_if_missing_colon",
            src: r#"permit (principal, action, resource) when { {if 1} };"#,
            category: "expression",
        },
        Case {
            label: "rec_init_if_missing_value",
            src: r#"permit (principal, action, resource) when { {if: } };"#,
            category: "expression",
        },
    ]
}

/// Outcome of comparing one case.
#[derive(Debug)]
enum Outcome {
    /// Both parsers reject and the first error message matches exactly.
    Match,
    /// Both parsers reject but messages differ.
    Diverge {
        cedar_msg: String,
        dogwood_msg: String,
    },
    /// Cedar rejects but Dogwood accepts (Dogwood is more permissive).
    DogwoodAccepts,
    /// Dogwood rejects but Cedar accepts (Dogwood is more restrictive).
    CedarAccepts,
    /// Both accept (not actually broken — test case is wrong).
    BothAccept,
}

fn compare_case(src: &str) -> Outcome {
    let cedar = cedar_error(src);
    let dogwood = dogwood_error(src);

    match (cedar, dogwood) {
        (None, None) => Outcome::BothAccept,
        (Some(_), None) => Outcome::DogwoodAccepts,
        (None, Some(_)) => Outcome::CedarAccepts,
        (Some(cedar_msgs), Some(dogwood_msgs)) => {
            // Compare the first error message from each side.
            let cedar_first = cedar_msgs.first().cloned().unwrap_or_default();
            let dogwood_first = dogwood_msgs.first().cloned().unwrap_or_default();
            if cedar_first == dogwood_first {
                Outcome::Match
            } else {
                Outcome::Diverge {
                    cedar_msg: cedar_first,
                    dogwood_msg: dogwood_first,
                }
            }
        }
    }
}

/// Measurement test: prints a full report of error-message agreement.
/// Run with `--nocapture` to see the report.
#[test]
fn error_message_differential_report() {
    let cases = cases();
    let mut matches = Vec::new();
    let mut divergences = Vec::new();
    let mut dogwood_accepts = Vec::new();
    let mut cedar_accepts = Vec::new();
    let mut both_accept = Vec::new();

    for case in &cases {
        let outcome = compare_case(case.src);
        match outcome {
            Outcome::Match => matches.push(case),
            Outcome::Diverge {
                cedar_msg,
                dogwood_msg,
            } => divergences.push((case, cedar_msg, dogwood_msg)),
            Outcome::DogwoodAccepts => dogwood_accepts.push(case),
            Outcome::CedarAccepts => cedar_accepts.push(case),
            Outcome::BothAccept => both_accept.push(case),
        }
    }

    let total = cases.len();
    eprintln!("\n{}", "=".repeat(70));
    eprintln!("=== ERROR MESSAGE DIFFERENTIAL REPORT ===");
    eprintln!("{}\n", "=".repeat(70));
    eprintln!(
        "Total cases: {total}  |  Match: {}  |  Diverge: {}  |  DogwoodAccepts: {}  |  CedarAccepts: {}  |  BothAccept: {}",
        matches.len(),
        divergences.len(),
        dogwood_accepts.len(),
        cedar_accepts.len(),
        both_accept.len(),
    );

    if !divergences.is_empty() {
        eprintln!("\n--- DIVERGENCES (both reject, messages differ) ---\n");
        for (case, cedar_msg, dogwood_msg) in &divergences {
            eprintln!(
                "[{}] {} (category: {})",
                case.label,
                case.src.chars().take(60).collect::<String>(),
                case.category
            );
            eprintln!("  Cedar:   {cedar_msg}");
            eprintln!("  Dogwood: {dogwood_msg}");
            eprintln!();
        }
    }

    if !dogwood_accepts.is_empty() {
        eprintln!("\n--- DOGWOOD ACCEPTS (Cedar rejects, Dogwood doesn't) ---\n");
        for case in &dogwood_accepts {
            let cedar_msgs = cedar_error(case.src).unwrap_or_default();
            eprintln!(
                "[{}] {} => Cedar: {:?}",
                case.label,
                case.src.chars().take(60).collect::<String>(),
                cedar_msgs.first().unwrap_or(&String::new())
            );
        }
    }

    if !cedar_accepts.is_empty() {
        eprintln!("\n--- CEDAR ACCEPTS (Dogwood rejects, Cedar doesn't) ---\n");
        for case in &cedar_accepts {
            let dogwood_msgs = dogwood_error(case.src).unwrap_or_default();
            eprintln!(
                "[{}] {} => Dogwood: {:?}",
                case.label,
                case.src.chars().take(60).collect::<String>(),
                dogwood_msgs.first().unwrap_or(&String::new())
            );
        }
    }

    if !both_accept.is_empty() {
        eprintln!("\n--- BOTH ACCEPT (test case is not actually broken) ---\n");
        for case in &both_accept {
            eprintln!(
                "[{}] {}",
                case.label,
                case.src.chars().take(60).collect::<String>()
            );
        }
    }

    if !matches.is_empty() {
        eprintln!("\n--- MATCHES (parity achieved) ---\n");
        for case in &matches {
            eprintln!(
                "[{}] {}",
                case.label,
                case.src.chars().take(60).collect::<String>()
            );
        }
    }

    // Summary by category
    eprintln!("\n--- SUMMARY BY CATEGORY ---\n");
    let categories: Vec<&str> = vec![
        "top-level",
        "scope",
        "condition",
        "expression",
        "entity-ref",
        "annotation",
        "literal",
        "def",
        "operator",
        "acceptance-divergence",
    ];
    for cat in categories {
        let cat_cases: Vec<_> = cases.iter().filter(|c| c.category == cat).collect();
        let cat_match = cat_cases
            .iter()
            .filter(|c| matches!(compare_case(c.src), Outcome::Match))
            .count();
        let cat_diverge = cat_cases
            .iter()
            .filter(|c| matches!(compare_case(c.src), Outcome::Diverge { .. }))
            .count();
        let cat_dogwood = cat_cases
            .iter()
            .filter(|c| matches!(compare_case(c.src), Outcome::DogwoodAccepts))
            .count();
        let cat_cedar = cat_cases
            .iter()
            .filter(|c| matches!(compare_case(c.src), Outcome::CedarAccepts))
            .count();
        eprintln!(
            "  {cat:12} — total: {:2}, match: {:2}, diverge: {:2}, dw-accepts: {:2}, cedar-accepts: {:2}",
            cat_cases.len(),
            cat_match,
            cat_diverge,
            cat_dogwood,
            cat_cedar,
        );
    }

    eprintln!("\n{}\n", "=".repeat(70));
}

/// Hard assertion: both parsers must reject every case (except known
/// acceptance divergences in the "acceptance-divergence" category). If either
/// accepts a case that the other rejects, it's an acceptance-set divergence
/// that needs investigation.
#[test]
fn both_parsers_reject_all_broken_cases() {
    let cases = cases();
    let mut problems = Vec::new();

    for case in &cases {
        // Skip known acceptance divergences (Cedar catches these semantically
        // at parse time; Dogwood defers to validation or lowering).
        if case.category == "acceptance-divergence" {
            continue;
        }

        let cedar = cedar_error(case.src);
        let dogwood = dogwood_error(case.src);

        match (&cedar, &dogwood) {
            (None, Some(_)) => {
                problems.push(format!(
                    "[{}] Cedar accepts but Dogwood rejects: {:?}",
                    case.label,
                    case.src.chars().take(60).collect::<String>()
                ));
            }
            (Some(_), None) => {
                problems.push(format!(
                    "[{}] Dogwood accepts but Cedar rejects: {:?}",
                    case.label,
                    case.src.chars().take(60).collect::<String>()
                ));
            }
            (None, None) => {
                problems.push(format!(
                    "[{}] Both accept (case is not broken): {:?}",
                    case.label,
                    case.src.chars().take(60).collect::<String>()
                ));
            }
            _ => {} // both reject — good
        }
    }

    if !problems.is_empty() {
        panic!(
            "Acceptance-set divergences ({}/{} cases):\n  {}",
            problems.len(),
            cases.len(),
            problems.join("\n  ")
        );
    }
}

/// Spot-check rendering: every Dogwood parse error must self-render (embed
/// its source in the diagnostic) without needing external `with_source_code`.
#[test]
fn dogwood_errors_self_render_with_source() {
    let cases = cases();
    let mut failures = Vec::new();

    for case in &cases {
        let service = ServiceSchema::defaults();
        let policy_schema = match PolicySchema::from_cedarschema_str("") {
            Ok(ps) => ps,
            Err(_) => continue,
        };
        let err = match LoweredPolicySet::from_str(case.src, &service, &policy_schema) {
            Ok(_) => continue,
            Err(e) => e,
        };

        // Render via miette. If the error carries its own source, the
        // rendered output includes the offending source line.
        let report = miette::Report::new(err);
        let rendered = format!("{report:?}");

        // The rendered diagnostic should contain at least a fragment of the
        // original source (not just the error message). Any token from the
        // input should appear in the rendered output if the source is
        // embedded.
        let has_source_fragment = case
            .src
            .split_whitespace()
            .filter(|w| w.len() > 2) // skip tiny tokens like `{` that might not render
            .any(|word| rendered.contains(word));

        if !has_source_fragment && !case.src.is_empty() {
            failures.push(format!(
                "[{}] rendered diagnostic doesn't include source fragment:\n  {}",
                case.label,
                rendered.lines().take(5).collect::<Vec<_>>().join("\n  ")
            ));
        }
    }

    if !failures.is_empty() {
        panic!(
            "Self-rendering failures ({}):\n  {}",
            failures.len(),
            failures.join("\n\n  ")
        );
    }
}
