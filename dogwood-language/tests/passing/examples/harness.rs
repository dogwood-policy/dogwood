//! Regression harness for `dogwood-docs/examples/`.
//!
//! Each subdirectory under `examples/` is one case. A case is testable if it
//! contains both `trace.log` and `expected.out`. The harness reads:
//!
//!   - `policy.dw` (required)
//!   - `macros.dw` (optional — prepended to policy source)
//!   - `schema.cedarschema` (required)
//!   - `trace.log` + `expected.out` (required for verdict testing)
//!   - `providers.json` (optional — provider declarations)
//!   - `event.dwschema` (optional — custom event schema override)
//!
//! Cases without `trace.log` + `expected.out` are parse-only: the harness
//! verifies they parse, lower, and validate without error.
//!
//! Verdict output matches the `dogwood replay` CLI format:
//!   `@<ts> (time point <N>): ALLOW  [rules: 0, 1]`  or  `@<ts> (time point <N>): DENY`

use std::path::{Path, PathBuf};

use dogwood_language::{
    Authorizer, Decision, LoweredPolicySet, PolicySchema, ProviderDeclarations, ServiceSchema,
    parse_trace,
};

fn norm(s: &str) -> Vec<String> {
    s.lines()
        .map(str::trim)
        .filter(|l| !l.is_empty())
        .map(str::to_string)
        .collect()
}

fn example_dirs(root: &Path) -> Vec<PathBuf> {
    let mut v: Vec<_> = std::fs::read_dir(root)
        .unwrap_or_else(|e| panic!("read_dir({}): {e}", root.display()))
        .filter_map(|e| e.ok())
        .map(|e| e.path())
        .filter(|p| p.is_dir())
        .collect();
    v.sort();
    v
}

/// Replay a trace and format output in CLI style.
fn replay_cli_format(policies: LoweredPolicySet, log: &str) -> Result<String, String> {
    let events = parse_trace(log).map_err(|e| format!("{e:?}"))?;
    let mut authorizer = Authorizer::new(policies);
    let mut lines = Vec::new();
    let mut index = 0usize;

    for event in &events {
        let ts = event.timestamp();
        if let Some(response) = authorizer.is_authorized(event) {
            let decision = match response.decision() {
                Decision::Allow => "ALLOW",
                Decision::Deny => "DENY",
            };
            let mut line = format!("@{ts} (time point {index}): {decision}");
            let rules: Vec<usize> = response
                .diagnostics()
                .reason()
                .map(|r| r.rule_index)
                .collect();
            if !rules.is_empty() {
                let rules_str: Vec<String> = rules.iter().map(|r| r.to_string()).collect();
                line.push_str(&format!("  [rules: {}]", rules_str.join(", ")));
            }
            lines.push(line);
            index += 1;
        }
    }
    Ok(lines.join("\n"))
}

#[test]
fn examples_verdicts() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("../dogwood-docs/examples");
    assert!(
        root.exists(),
        "dogwood-docs/examples/ not found at {} — is dogwood-docs in the workspace?",
        root.display(),
    );

    let default_event_schema = std::fs::read_to_string(
        Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/request_response.dwschema"),
    )
    .expect("default event schema fixture");

    let mut verdict_failures: Vec<String> = Vec::new();
    let mut parse_failures: Vec<String> = Vec::new();
    let mut verdict_passed = 0usize;
    let mut parse_only_passed = 0usize;

    for dir in example_dirs(&root) {
        let case = dir.file_name().unwrap().to_string_lossy().to_string();

        // policy.dw is required
        let policy_path = dir.join("policy.dw");
        if !policy_path.exists() {
            continue;
        }

        // Read policy source; prepend macros.dw if present
        let mut policy_src = String::new();
        let macros_path = dir.join("macros.dw");
        if macros_path.exists() {
            policy_src.push_str(&std::fs::read_to_string(&macros_path).unwrap());
            policy_src.push('\n');
        }
        policy_src.push_str(&std::fs::read_to_string(&policy_path).unwrap());

        // schema.cedarschema is required
        let schema_path = dir.join("schema.cedarschema");
        if !schema_path.exists() {
            continue;
        }
        let schema_src = std::fs::read_to_string(&schema_path).unwrap();

        // Event schema: per-case override or default fixture
        let event_schema_src = if dir.join("event.dwschema").exists() {
            std::fs::read_to_string(dir.join("event.dwschema")).unwrap()
        } else {
            default_event_schema.clone()
        };

        // Provider declarations (optional)
        let providers_path = dir.join("providers.json");
        let decls = if providers_path.exists() {
            match ProviderDeclarations::from_json_file(&providers_path) {
                Ok(d) => Some(d),
                Err(e) => {
                    parse_failures.push(format!("{case}: providers.json: {e}"));
                    continue;
                }
            }
        } else {
            None
        };

        // Determine if this is a verdict test or parse-only
        let has_verdict = dir.join("trace.log").exists() && dir.join("expected.out").exists();

        let result: Result<Option<String>, String> =
            std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                let policy_schema = PolicySchema::from_cedarschema_str(&schema_src)
                    .map_err(|e| format!("{e:?}"))?;
                let mut builder = ServiceSchema::builder().event_schema_str(&event_schema_src);
                if let Some(d) = &decls {
                    builder = builder.providers(d.clone());
                }
                let service = builder.build().map_err(|e| format!("{e:?}"))?;
                let policies = LoweredPolicySet::from_str(&policy_src, &service, &policy_schema)
                    .map_err(|e| format!("{e:?}"))?;

                if has_verdict {
                    let trace = std::fs::read_to_string(dir.join("trace.log")).unwrap();
                    let got = replay_cli_format(policies, &trace)?;
                    Ok(Some(got))
                } else {
                    // Parse-only: policy parsed, lowered, and validated via
                    // LoweredPolicySet::from_str. Success means it's correct.
                    Ok(None)
                }
            }))
            .unwrap_or_else(|_| Err("PANIC".to_string()));

        match result {
            Ok(Some(got)) => {
                let expected = std::fs::read_to_string(dir.join("expected.out")).unwrap();
                if norm(&got) == norm(&expected) {
                    verdict_passed += 1;
                } else {
                    verdict_failures.push(format!(
                        "{case}: mismatch\n  got: {:?}\n  exp: {:?}",
                        norm(&got),
                        norm(&expected)
                    ));
                }
            }
            Ok(None) => {
                parse_only_passed += 1;
            }
            Err(e) => {
                if has_verdict {
                    verdict_failures.push(format!("{case}: {e}"));
                } else {
                    parse_failures.push(format!("{case}: {e}"));
                }
            }
        }
    }

    let total_failures = verdict_failures.len() + parse_failures.len();
    eprintln!(
        "examples: {verdict_passed} verdict-passed, {parse_only_passed} parse-only-passed, {total_failures} failed",
    );

    assert!(
        verdict_passed + parse_only_passed > 0,
        "no examples were tested — check that dogwood-docs/examples/ exists"
    );

    let mut all_failures = Vec::new();
    all_failures.extend(verdict_failures);
    all_failures.extend(parse_failures);
    assert!(
        all_failures.is_empty(),
        "failures:\n\n{}",
        all_failures.join("\n\n")
    );
}
