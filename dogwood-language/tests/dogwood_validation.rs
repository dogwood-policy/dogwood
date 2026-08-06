//! Behavior tests for the full schema-aware validator (Cedar core, temporal,
//! and provider). Each test pins one detection (or its absence) by driving the
//! real pipeline — build a [`ServiceSchema`] and [`PolicySchema`], parse a
//! [`LoweredPolicySet`], then run the [`Validator`] — through the
//! `validate_source` helper below, and asserting on the accumulated
//! [`ValidationError`]s.

use dogwood_language::{
    LoweredPolicySet, PolicySchema, ProviderDeclarations, ServiceSchema, ValidationError,
    ValidationResult, Validator,
};

/// Run the full pipeline: build a [`ServiceSchema`] (the request/response
/// event schema + optional providers) and a [`PolicySchema`] (action schema),
/// parse the source into a [`LoweredPolicySet`] (lower + event-schema check),
/// then run the [`Validator`] (Cedar core + temporal + provider dialects).
/// Panics if the schema fails to build or the source fails to parse/lower —
/// every case here is expected to lower cleanly and surface its defect (if
/// any) as a *validation finding*, not a fatal parse error.
fn validate_source(
    source: &str,
    schema_source: &str,
    provider_declarations: Option<&ProviderDeclarations>,
) -> ValidationResult {
    let mut builder = ServiceSchema::builder().event_schema_str(EVENT_SCHEMA);
    if let Some(decls) = provider_declarations {
        builder = builder.providers(decls.clone());
    }
    let service = builder.build().expect("service schema builds");
    let policy_schema =
        PolicySchema::from_cedarschema_str(schema_source).expect("policy schema builds");
    let policies = LoweredPolicySet::from_str(source, &service, &policy_schema)
        .expect("source parses and lowers");
    Validator::new().validate(&policies)
}

/// The byte offset of the first error of `variant`'s rebased span.
fn first_span_offset(
    result: &ValidationResult,
    variant: fn(&ValidationError) -> Option<usize>,
) -> Option<usize> {
    result.validation_errors().find_map(variant)
}

fn temporal_offset(e: &ValidationError) -> Option<usize> {
    match e {
        ValidationError::Extension {
            code: "temporal",
            span,
            ..
        } => Some(span.offset()),
        _ => None,
    }
}

fn provider_offset(e: &ValidationError) -> Option<usize> {
    match e {
        ValidationError::Extension {
            code: "provider",
            span,
            ..
        } => Some(span.offset()),
        _ => None,
    }
}

const SCHEMA: &str = r#"
namespace App {
  type LoginInput = { user: String, server: String };
  type ReadInput = { user: String, document: String, tags: Set<String> };

  entity Gateway;
  entity OAuthUser = { id: String };

  action "Login" appliesTo {
    principal: [OAuthUser], resource: [Gateway],
    context: { input: LoginInput }
  };
  action "Read" appliesTo {
    principal: [OAuthUser], resource: [Gateway],
    context: { input: ReadInput }
  };
}
"#;

/// The standard request/response event schema (the same convention the
/// other temporal tests use): for every action `A`, derive a `request`
/// decision event and a `response` history event from the action's inputs.
/// Temporal predicates here name `<Action>::request{…}`, so `parse` needs this
/// to derive those event signatures.
const EVENT_SCHEMA: &str = r#"
decision event <A>::request {
    ...inputs(A),
    callerPrincipal: principalType(A),
    callerResource:  resourceType(A),
    requestId:       String,
}

event <A>::response {
    ...inputs(A),
    ...outputs(A),
    callerPrincipal: principalType(A),
    callerResource:  resourceType(A),
    requestId:       String,
}
"#;

const DECLARATIONS: &str = r#"{
  "availableProviders": {
    "Strings::Matches": {
      "argumentTypes": [{ "paramType": "string" }, { "paramType": "string" }],
      "outputType": {
        "paramType": "record",
        "fields": { "matched": { "paramType": "bool" } },
        "required": ["matched"]
      }
    }
  }
}"#;

fn decls() -> ProviderDeclarations {
    ProviderDeclarations::from_json(DECLARATIONS).expect("declarations parse")
}

// ─── Cedar core ─────────────────────────────────────────────────────

#[test]
fn when_cedar_clause_uses_unknown_field_then_cedar_error() {
    let src = r#"
permit (principal, action == App::Action::"Read", resource)
when { context.input.bogus == "x" };
"#;
    let result = validate_source(src, SCHEMA, None);
    assert!(
        result
            .validation_errors()
            .any(|e| matches!(e, ValidationError::Cedar { .. })),
        "expected a Cedar variant, got:\n{result:?}"
    );
}

#[test]
fn cedar_error_span_points_at_the_offending_subexpression() {
    // The payoff of lowering to loc-bearing `ast`: a Cedar validation error
    // must point at the precise `.dw` sub-expression that caused it
    // (`context.input.bogus`), NOT the whole rule. Before the `to_ast`
    // rewrite, `pst` carried no locations and this could only resolve to the
    // enclosing rule's span.
    let src = r#"
permit (principal, action == App::Action::"Read", resource)
when { context.input.bogus == "x" };
"#;
    let result = validate_source(src, SCHEMA, None);
    let span = result
        .validation_errors()
        .find_map(|e| match e {
            ValidationError::Cedar { span, .. } => Some(*span),
            _ => None,
        })
        .expect("a Cedar error with a span");

    // The error's span must fall within `context.input.bogus` — the failing
    // attribute access — not span the whole `when { … }` clause or rule.
    let start = span.offset();
    let end = start + span.len();
    let sliced = &src[start..end];
    let needle_start = src.find("context.input.bogus").expect("needle present");
    let needle_end = needle_start + "context.input.bogus".len();
    assert!(
        start >= needle_start && end <= needle_end,
        "Cedar error span ({start}..{end} = {sliced:?}) should be within \
         `context.input.bogus` ({needle_start}..{needle_end}), not the whole rule"
    );
}

#[test]
fn validation_finding_self_renders_without_with_source_code() {
    // A validation finding embeds its `.dw` source, so a `miette::Report` over
    // it underlines the offending snippet with NO `with_source_code` — the same
    // as the fatal `Error` channel and as Cedar's own findings.
    let src = r#"
permit (principal, action == App::Action::"Read", resource)
when { context.input.bogus == "x" };
"#;
    let result = validate_source(src, SCHEMA, None);
    let finding = result
        .validation_errors()
        .find(|e| matches!(e, ValidationError::Cedar { .. }))
        .expect("a Cedar validation error");

    // Render the finding. `miette::Report` wants an owned/'static error, and
    // `ValidationError` is `Clone` (its `source` chain is an `Arc`), so a
    // borrowed finding renders with a plain `.clone()` — no hand-rebuild.
    let report = miette::Report::new(finding.clone());
    let rendered = format!("{report:?}");
    assert!(
        rendered.contains("context.input.bogus"),
        "self-rendered finding should include the offending source; got:\n{rendered}"
    );
}

#[test]
fn scope_error_span_points_at_the_scope_token() {
    // A mistyped scope action (`"Reed"` — no such action in the schema)
    // triggers a Cedar RBAC error. Because the scope constraint's entity UID
    // now carries a `.dw` `Loc` (built loc-bearing in the parser), the error
    // must point at the `App::Action::"Reed"` token, NOT the whole rule.
    let src = r#"
permit (principal, action == App::Action::"Reed", resource)
when { true };
"#;
    let result = validate_source(src, SCHEMA, None);
    let span = result
        .validation_errors()
        .find_map(|e| match e {
            ValidationError::Cedar { span, .. } => Some(*span),
            _ => None,
        })
        .expect("a Cedar scope error with a span");

    let start = span.offset();
    let end = start + span.len();
    // The offending action reference in the source.
    let needle_start = src.find("App::Action::\"Reed\"").expect("needle present");
    let needle_end = needle_start + "App::Action::\"Reed\"".len();
    assert!(
        start >= needle_start && end <= needle_end,
        "scope error span ({start}..{end} = {:?}) should be within the \
         `App::Action::\"Reed\"` token ({needle_start}..{needle_end}), not the whole rule",
        &src[start..end]
    );
}

// ─── Temporal ───────────────────────────────────────────────────────

#[test]
fn when_temporal_clause_is_well_formed_then_no_errors() {
    let src = r#"
permit (principal, action == App::Action::"Read", resource)
when temporal { formerly within 1h App::Action::"Login"::request{input.user: context.input.user} };
"#;
    let result = validate_source(src, SCHEMA, None);
    assert!(
        result.validation_passed(),
        "expected no errors, got:\n{result:?}"
    );
}

#[test]
fn when_temporal_clause_uses_unknown_predicate_then_temporal_error() {
    let src = r#"
permit (principal, action == App::Action::"Read", resource)
when temporal { formerly within 1h App::Action::"DoesNotExist"::request{input.user: context.input.user} };
"#;
    let result = validate_source(src, SCHEMA, None);
    assert!(
        result.validation_errors().any(|e| matches!(
            e,
            ValidationError::Extension {
                code: "temporal",
                ..
            }
        )),
        "expected a Temporal variant, got:\n{result:?}"
    );
}

#[test]
fn when_temporal_clause_uses_unknown_argument_then_temporal_error() {
    let src = r#"
permit (principal, action == App::Action::"Read", resource)
when temporal { formerly within 1h App::Action::"Login"::request{input.bogus: context.input.user} };
"#;
    let result = validate_source(src, SCHEMA, None);
    assert!(
        result.validation_errors().any(|e| matches!(
            e,
            ValidationError::Extension {
                code: "temporal",
                ..
            }
        )),
        "expected a Temporal variant for the unknown argument, got:\n{result:?}"
    );
}

#[test]
fn when_context_field_absent_from_scoped_action_then_temporal_error() {
    // The rule is scoped to `Login`, whose input has no `document` field
    // (only `Read` does). The leaf's `context.input.document` must be caught
    // against the *scoped* action, not accepted because another action
    // happens to declare the field.
    let src = r#"
permit (principal, action == App::Action::"Login", resource)
when temporal { formerly within 1h App::Action::"Login"::request{input.user: context.input.document} };
"#;
    let result = validate_source(src, SCHEMA, None);
    assert!(
        result.validation_errors().any(|e| matches!(
            e,
            ValidationError::Extension {
                code: "temporal",
                ..
            }
        )),
        "expected a Temporal error for the field absent from the scoped action, got:\n{result:?}"
    );
}

#[test]
fn when_temporal_operator_body_is_tp_independent_then_temporal_error() {
    // `formerly within 1h (context.input.user == "x")` monitors nothing: the
    // body has no predicate/tp, so it cannot vary across timepoints.
    let src = r#"
permit (principal, action == App::Action::"Read", resource)
when temporal { formerly within 1h context.input.user == "alice" };
"#;
    let result = validate_source(src, SCHEMA, None);
    assert!(
        result.validation_errors().any(|e| matches!(
            e,
            ValidationError::Extension {
                code: "temporal",
                ..
            }
        )),
        "expected a Temporal error for the tp-independent body, got:\n{result:?}"
    );
}

#[test]
fn when_bare_scope_attribute_conjunct_is_tp_independent_then_temporal_error() {
    // A bare top-level `principal.dept == "eng"` conjunct is tp-independent — a
    // scope attribute is a fixed current-request value (`Term::ScopeField` is
    // `false` in `term_is_tp_dep`, like a context field), so on its own it
    // "monitors nothing" and is rejected. This is the scope-term analog of the
    // `context.input.user` case above; a scope-attr read must sit INSIDE a
    // tp-dependent scope (see corpus 1130), not as a bare conjunct beside a
    // `formerly`.
    let src = r#"
permit (principal, action == App::Action::"Read", resource)
when temporal { formerly within 1h App::Action::"Login"::request{input.user: context.input.user} && principal.dept == "eng" };
"#;
    let result = validate_source(src, SCHEMA, None);
    assert!(
        result.validation_errors().any(|e| matches!(
            e,
            ValidationError::Extension { code: "temporal", message, .. }
                if message.contains("monitors nothing")
        )),
        "expected a tp-dependence error for the bare `principal.dept` conjunct, got:\n{result:?}"
    );
}

#[test]
fn when_temporal_comparison_mixes_types_then_temporal_error() {
    // `context.input.user` is a String; comparing it `<` to an integer is a
    // numeric-operand type error.
    let src = r#"
permit (principal, action == App::Action::"Read", resource)
when temporal { formerly within 1h App::Action::"Read"::request{input.user: context.input.user} && context.input.user < 5 };
"#;
    let result = validate_source(src, SCHEMA, None);
    // Assert specifically on the type-mismatch message so the test can't pass
    // for an unrelated reason (e.g. a tp-dependence error masking a missing
    // type check).
    assert!(
        result.validation_errors().any(|e| matches!(
            e,
            ValidationError::Extension { code: "temporal", message, .. } if message.contains("numeric operands")
        )),
        "expected a Temporal type error mentioning numeric operands, got:\n{result:?}"
    );
}

// ─── Binder type annotations (exists / aggregation `for`) ───────────
//
// A binder's type annotation is mandatory and authoritative: the type
// checker seeds each `exists (x: T)` / `for (v: T)` variable with its
// DECLARED type, then verifies every use is consistent with it — rather
// than reverse-inferring the type from the first use site (which could
// silently contradict the declaration, or leave a variable untyped so its
// uses went unchecked).

#[test]
fn when_exists_binder_type_conflicts_with_use_then_temporal_error() {
    // `x` is declared `Long`, but bound to the String field `input.user`
    // and compared to a string literal. The declared `Long` is authoritative,
    // so `x == "s1"` is an int-vs-string equality mismatch. (Under the old
    // use-site inference, `x` would have been inferred `String` from the
    // predicate field and this would have passed.)
    let src = r#"
permit (principal, action == App::Action::"Read", resource)
when temporal { exists (x: Long). (App::Action::"Login"::request{input.user: x} && x == "s1") };
"#;
    let result = validate_source(src, SCHEMA, None);
    assert!(
        result.validation_errors().any(|e| matches!(
            e,
            ValidationError::Extension { code: "temporal", message, .. }
                if message.contains("same type")
        )),
        "expected a temporal equality type-mismatch from the declared `Long` binder, got:\n{result:?}"
    );
}

#[test]
fn when_exists_binder_type_is_respected_then_no_errors() {
    // The same shape with a consistent annotation: `x: String` bound to the
    // String field `input.user` and compared to a string literal. A correctly
    // annotated binder must still validate cleanly.
    let src = r#"
permit (principal, action == App::Action::"Read", resource)
when temporal { exists (x: String). (App::Action::"Login"::request{input.user: x} && x == "s1") };
"#;
    let result = validate_source(src, SCHEMA, None);
    assert!(
        result.validation_passed(),
        "a consistently-annotated `exists` binder should validate, got:\n{result:?}"
    );
}

#[test]
fn when_aggregation_result_binder_type_conflicts_then_temporal_error() {
    // The `let`-migration shape `(count …) == var`, but the result variable is
    // declared `String` while `count` yields a `Long`. The declared type is
    // authoritative, so the equality is an int-vs-string mismatch.
    //
    // This is the sharpest soundness case: under the old use-site inference,
    // `s` appeared only as an aggregate-equality operand — a position that
    // seeded NO type — so `term_type(s)` was `None` and the comparison check
    // was silently skipped. Seeding from the declaration types `s` and makes
    // the check fire.
    let src = r#"
permit (principal, action == App::Action::"Read", resource)
when temporal { exists (s: String). ((count for (t: Timepoint). where (App::Action::"Login"::request{} && tp(t))) == s) };
"#;
    let result = validate_source(src, SCHEMA, None);
    assert!(
        result.validation_errors().any(|e| matches!(
            e,
            ValidationError::Extension { code: "temporal", message, .. }
                if message.contains("same type")
        )),
        "expected a temporal type mismatch: `count` (Long) compared to a `String`-declared binder, got:\n{result:?}"
    );
}

#[test]
fn when_aggregation_result_binder_type_is_respected_then_no_errors() {
    // The well-formed migration shape: `count` yields a `Long`, the result
    // binder is declared `Long`, and the follow-on filter compares it to an
    // integer. Must validate cleanly with the declared-type environment.
    let src = r#"
permit (principal, action == App::Action::"Read", resource)
when temporal { exists (n: Long). ((count for (t: Timepoint). where (App::Action::"Login"::request{} && tp(t))) == n && n > 0) };
"#;
    let result = validate_source(src, SCHEMA, None);
    assert!(
        result.validation_passed(),
        "a `Long`-declared aggregation result binder should validate, got:\n{result:?}"
    );
}

// ─── Max-window enforcement (event schema `max_window`) ─────────────
//
// The event schema caps how far back any temporal `within` window may look.
// The default cap is 24h; a schema may raise or lower it with a
// `max_window = <interval>` directive. The temporal validator rejects any
// `within` window that exceeds the cap.

/// Run the pipeline with an explicit event-schema source, so a test can set
/// (or omit) the `max_window` directive. Mirrors [`validate_source`] but takes
/// the event schema instead of the fixed `EVENT_SCHEMA`.
fn validate_source_with_event_schema(
    source: &str,
    schema_source: &str,
    event_schema_source: &str,
) -> ValidationResult {
    let service = ServiceSchema::builder()
        .event_schema_str(event_schema_source)
        .build()
        .expect("service schema builds");
    let policy_schema =
        PolicySchema::from_cedarschema_str(schema_source).expect("policy schema builds");
    let policies = LoweredPolicySet::from_str(source, &service, &policy_schema)
        .expect("source parses and lowers");
    Validator::new().validate(&policies)
}

fn max_window_error(result: &ValidationResult) -> bool {
    result.validation_errors().any(|e| {
        matches!(
            e,
            ValidationError::Extension { code: "temporal", message, .. }
                if message.contains("exceeds the maximum allowed window")
        )
    })
}

#[test]
fn when_within_exceeds_default_max_window_then_temporal_error() {
    // No `max_window` directive → the 24h default. A `formerly within 48h`
    // exceeds it and is rejected.
    let src = r#"
permit (principal, action == App::Action::"Read", resource)
when temporal { formerly within 48h App::Action::"Login"::request{input.user: context.input.user} };
"#;
    let result = validate_source(src, SCHEMA, None);
    assert!(
        max_window_error(&result),
        "expected a max-window error for `within 48h` against the 24h default, got:\n{result:?}"
    );
}

#[test]
fn when_within_equals_default_max_window_then_no_error() {
    // Exactly at the cap: the bound is inclusive (`greater than` is the
    // rejection test), so `within 24h` — and `within 1d`, the same duration —
    // are both allowed under the 24h default.
    for window in ["24h", "1d"] {
        let src = format!(
            r#"
permit (principal, action == App::Action::"Read", resource)
when temporal {{ formerly within {window} App::Action::"Login"::request{{input.user: context.input.user}} }};
"#
        );
        let result = validate_source(&src, SCHEMA, None);
        assert!(
            !max_window_error(&result),
            "`within {window}` equals the 24h cap and must be allowed, got:\n{result:?}"
        );
    }
}

#[test]
fn when_within_under_default_max_window_then_no_error() {
    // Well under the cap — the common case — is clean.
    let src = r#"
permit (principal, action == App::Action::"Read", resource)
when temporal { formerly within 1h App::Action::"Login"::request{input.user: context.input.user} };
"#;
    let result = validate_source(src, SCHEMA, None);
    assert!(
        !max_window_error(&result),
        "`within 1h` is well under the 24h cap and must be allowed, got:\n{result:?}"
    );
}

#[test]
fn when_event_schema_raises_max_window_then_larger_within_allowed() {
    // A schema that raises the cap to 30d admits a `within 7d` that the
    // default 24h cap would reject.
    let event_schema = r#"
max_window = 30d
decision event <A>::request {
    ...inputs(A),
    callerPrincipal: principalType(A),
    callerResource:  resourceType(A),
    requestId:       String,
}
"#;
    let src = r#"
permit (principal, action == App::Action::"Read", resource)
when temporal { formerly within 7d App::Action::"Login"::request{input.user: context.input.user} };
"#;
    let result = validate_source_with_event_schema(src, SCHEMA, event_schema);
    assert!(
        !max_window_error(&result),
        "a 30d cap must admit `within 7d`, got:\n{result:?}"
    );
}

#[test]
fn when_event_schema_lowers_max_window_then_smaller_within_rejected() {
    // A schema that lowers the cap to 30m rejects a `within 1h` that the
    // default 24h cap would allow.
    let event_schema = r#"
max_window = 30m
decision event <A>::request {
    ...inputs(A),
    callerPrincipal: principalType(A),
    callerResource:  resourceType(A),
    requestId:       String,
}
"#;
    let src = r#"
permit (principal, action == App::Action::"Read", resource)
when temporal { formerly within 1h App::Action::"Login"::request{input.user: context.input.user} };
"#;
    let result = validate_source_with_event_schema(src, SCHEMA, event_schema);
    assert!(
        max_window_error(&result),
        "a 30m cap must reject `within 1h`, got:\n{result:?}"
    );
}

#[test]
fn when_within_inside_aggregation_exceeds_max_window_then_temporal_error() {
    // The cap applies to a `within` nested inside an aggregation `where` body,
    // not just top-level operators — the whole condition tree is walked.
    let src = r#"
permit (principal, action == App::Action::"Read", resource)
when temporal {
  exists (n: Long). (
    (count for (t: Timepoint). where (
        formerly within 48h (App::Action::"Login"::request{input.user: context.input.user} && tp(t))
    )) == n && n > 0
  )
};
"#;
    let result = validate_source(src, SCHEMA, None);
    assert!(
        max_window_error(&result),
        "expected a max-window error for the `within 48h` inside the aggregation body, got:\n{result:?}"
    );
}

#[test]
fn max_window_error_reports_span_of_the_offending_operator() {
    // The finding must locate the offending temporal operator in the full
    // `.dw` source (rebased from the block body), so the diagnostic underlines
    // the right window.
    let src = r#"
permit (principal, action == App::Action::"Read", resource)
when temporal { formerly within 48h App::Action::"Login"::request{input.user: context.input.user} };
"#;
    let result = validate_source(src, SCHEMA, None);
    let offset = first_span_offset(&result, |e| match e {
        ValidationError::Extension {
            code: "temporal",
            message,
            span,
            ..
        } if message.contains("exceeds the maximum allowed window") => Some(span.offset()),
        _ => None,
    })
    .expect("a max-window error with a span");
    // The span should land at or after the `formerly` operator, inside the
    // block — not at offset 0 (which would mean it failed to rebase).
    let formerly_off = src.find("formerly within 48h").expect("operator present");
    assert!(
        offset >= formerly_off,
        "max-window span offset {offset} should be at/after the `formerly` operator at {formerly_off}"
    );
}

// ─── Scope terms: principal / resource (Cedar-consistent) ───────────

#[test]
fn when_temporal_reads_a_declared_scope_attribute_then_no_errors() {
    // A DECLARED scope entity attribute validates. `id` is declared on
    // `OAuthUser` in this schema. Nested inside the `formerly` scope so the
    // tp-dependence check is satisfied by the predicate, matching the corpus
    // 0735 idiom.
    let src = r#"
permit (principal, action == App::Action::"Read", resource)
when temporal { formerly within 1h (App::Action::"Login"::request{input.user: context.input.user} && principal.id == "eng") };
"#;
    let result = validate_source(src, SCHEMA, None);
    assert!(
        result.validation_passed(),
        "a declared scope attribute read should validate, got:\n{result:?}"
    );
}

#[test]
fn when_temporal_reads_an_undeclared_scope_attribute_then_temporal_error() {
    // This case previously validated cleanly, on the stated grounds that scope
    // attribute paths "resolve at eval time". They do not. Measured with the same
    // policy and trace, varying only whether the schema declares the attribute:
    // declared gives Allow, undeclared gives Deny even when the trace's entity
    // store supplies the attribute. So an undeclared attribute does not resolve
    // late — it makes the comparison permanently false, and a permanently false
    // `forbid` is a cap that can never fire. Rejecting it is the whole point.
    let src = r#"
permit (principal, action == App::Action::"Read", resource)
when temporal { formerly within 1h (App::Action::"Login"::request{input.user: context.input.user} && principal.dept == "eng") };
"#;
    let result = validate_source(src, SCHEMA, None);
    assert!(
        !result.validation_passed(),
        "an undeclared scope attribute can never match and must be rejected, got:\n{result:?}"
    );
}

#[test]
fn when_temporal_uses_context_principal_as_a_context_field_then_temporal_error() {
    // Post-Cedar-parity, `context.principal` is an ordinary context field named
    // `principal` (Cedar's `context` is a plain record), NOT the request scope.
    // The action's context declares no such field, so it is a context-path
    // error — proving the old scope alias is gone and the scope is reached via
    // the bare `principal` root instead.
    let src = r#"
permit (principal, action == App::Action::"Read", resource)
when temporal { formerly within 1h App::Action::"Login"::request{callerPrincipal: context.principal} };
"#;
    let result = validate_source(src, SCHEMA, None);
    assert!(
        result.validation_errors().any(|e| matches!(
            e,
            ValidationError::Extension { code: "temporal", message, .. }
                if message.contains("context field `principal`")
        )),
        "expected a temporal context-field error for `context.principal`, got:\n{result:?}"
    );
}

#[test]
fn when_temporal_correlates_on_the_scope_principal_then_no_errors() {
    // The scope entity is now reached via the bare `principal` root (the
    // migration target of the old `context.principal`). Pinning the reserved
    // `callerPrincipal` field to `principal` validates.
    let src = r#"
permit (principal, action == App::Action::"Read", resource)
when temporal { formerly within 1h App::Action::"Login"::request{input.user: context.input.user, callerPrincipal: principal} };
"#;
    let result = validate_source(src, SCHEMA, None);
    assert!(
        result.validation_passed(),
        "a `callerPrincipal: principal` correlation should validate, got:\n{result:?}"
    );
}

/// An action schema whose context declares a non-`input` group (`system`), for
/// the context-record-widening test below.
const SYSTEM_CTX_SCHEMA: &str = r#"
namespace App {
  type LoginInput = { user: String };
  type SystemContext = { region: String };

  entity Gateway;
  entity OAuthUser = { id: String };

  action "Login" appliesTo {
    principal: [OAuthUser], resource: [Gateway],
    context: { input: LoginInput, system: SystemContext }
  };
  action "Read" appliesTo {
    principal: [OAuthUser], resource: [Gateway],
    context: { input: LoginInput, system: SystemContext }
  };
}
"#;

#[test]
fn when_temporal_reads_a_non_input_context_group_then_no_errors() {
    // Stage 3 widened temporal `context.<path>` validation from `input.*`-only
    // to the action's FULL context record. A `context.system.region` read
    // against an action that declares a `system` context group now resolves and
    // validates — whereas the old `input.*`-only rule would have rejected it.
    // Nested inside the `formerly` scope so tp-dependence is satisfied by the
    // predicate (the comparison itself is a fixed current-request value).
    let src = r#"
permit (principal, action == App::Action::"Read", resource)
when temporal { formerly within 1h (App::Action::"Login"::request{input.user: context.input.user} && context.system.region == "us-east-1") };
"#;
    let result = validate_source(src, SYSTEM_CTX_SCHEMA, None);
    assert!(
        result.validation_passed(),
        "a valid non-input context group should validate after the widening, got:\n{result:?}"
    );
}

#[test]
fn when_temporal_reads_an_undeclared_context_group_then_temporal_error() {
    // The widening still rejects an *undeclared* context head: `context.bogus`
    // names no context field on the scoped action, so it is a context-path
    // error (the widening accepts declared groups, not arbitrary paths).
    let src = r#"
permit (principal, action == App::Action::"Read", resource)
when temporal { formerly within 1h (App::Action::"Login"::request{input.user: context.input.user} && context.bogus.x == "y") };
"#;
    let result = validate_source(src, SYSTEM_CTX_SCHEMA, None);
    assert!(
        result.validation_errors().any(|e| matches!(
            e,
            ValidationError::Extension { code: "temporal", message, .. }
                if message.contains("context field `bogus`")
        )),
        "expected a temporal context-field error for the undeclared `context.bogus`, got:\n{result:?}"
    );
}

// ─── Provider ───────────────────────────────────────────────────────

#[test]
fn when_provider_invocation_is_well_formed_then_no_errors() {
    let src = r#"permit (principal, action == App::Action::"Read", resource) when guardrails {
  Strings::Matches(context.input.document, "^[A-Z]+$").matched == true
};"#;
    let result = validate_source(src, SCHEMA, Some(&decls()));
    assert!(
        result.validation_passed(),
        "expected no errors, got:\n{result:?}"
    );
}

#[test]
fn when_provider_literal_argument_type_mismatches_then_provider_error() {
    // `Strings::Matches` declares two `string` arguments; passing an integer
    // literal where the second string is expected is an argument-type error.
    let src = r#"permit (principal, action == App::Action::"Read", resource) when guardrails {
  Strings::Matches(context.input.document, 42).matched == true
};"#;
    let result = validate_source(src, SCHEMA, Some(&decls()));
    assert!(
        result.validation_errors().any(|e| matches!(
            e,
            ValidationError::Extension {
                code: "provider",
                ..
            }
        )),
        "expected a Provider argument-type error, got:\n{result:?}"
    );
}

#[test]
fn when_provider_argument_count_mismatches_then_provider_error() {
    // `Strings::Matches` declares two arguments; supplying one is a count
    // error.
    let src = r#"permit (principal, action == App::Action::"Read", resource) when guardrails {
  Strings::Matches(context.input.document).matched == true
};"#;
    let result = validate_source(src, SCHEMA, Some(&decls()));
    assert!(
        result.validation_errors().any(|e| matches!(
            e,
            ValidationError::Extension {
                code: "provider",
                ..
            }
        )),
        "expected a Provider argument-count error, got:\n{result:?}"
    );
}

#[test]
fn when_provider_is_undeclared_then_provider_error() {
    // `Strings::Matchez` (typo) is not declared. Lowering defaults its
    // output permissively and raises nothing, so the validator must reject
    // the unknown provider name itself.
    let src = r#"permit (principal, action == App::Action::"Read", resource) when guardrails {
  Strings::Matchez(context.input.document, "^[A-Z]+$").matched == true
};"#;
    let result = validate_source(src, SCHEMA, Some(&decls()));
    assert!(
        result.validation_errors().any(|e| matches!(
            e,
            ValidationError::Extension {
                code: "provider",
                ..
            }
        )),
        "expected a Provider error for the undeclared provider name, got:\n{result:?}"
    );
}

// ─── Provider under non-`==` action scopes ──────────────────────────
// A provider call hoists a typed `context.providers.<id>` field onto the
// action(s) its rule scopes. Historically this required a concrete
// `action == …` scope; these pin that a provider now also lowers cleanly
// under an `action in [list]`, a bare `action`, and an `action in Group`
// scope (the hoisted field is declared on every action's context).

/// A schema with an action group hierarchy: `Sell` and `Approve` are both
/// `in [Trade]`, so `action in [App::Action::"Trade"]` (a group) must reach
/// both leaf actions. `Trade` carries no own input; the leaves do.
const SCHEMA_HIER: &str = r#"
namespace App {
  type SellInput = { document: String };
  type ApproveInput = { document: String };

  entity Gateway;
  entity OAuthUser = { id: String };

  action "Trade" appliesTo {
    principal: [OAuthUser], resource: [Gateway],
    context: { }
  };
  action "Sell" in [Action::"Trade"] appliesTo {
    principal: [OAuthUser], resource: [Gateway],
    context: { input: SellInput }
  };
  action "Approve" in [Action::"Trade"] appliesTo {
    principal: [OAuthUser], resource: [Gateway],
    context: { input: ApproveInput }
  };
}
"#;

#[test]
fn when_provider_under_action_in_list_scope_then_no_errors() {
    // A provider call under an `action in [list]` scope must lower and
    // validate — the hoisted `context.providers.<id>` field is declared on
    // every action's context. (Both `Login` and `Read` declare no `document`?
    // `Read` does; `Login` does not — but the provider argument path is
    // resolved by Dogwood, not type-checked into Cedar, so listing both is
    // fine.) We list only `Read`, whose input has `document`.
    let src = r#"permit (principal, action in [App::Action::"Read"], resource) when guardrails {
  Strings::Matches(context.input.document, "^[A-Z]+$").matched == true
};"#;
    let result = validate_source(src, SCHEMA, Some(&decls()));
    assert!(
        result.validation_passed(),
        "expected a provider under an `action in [list]` scope to validate, got:\n{result:?}"
    );
}

#[test]
fn when_provider_under_bare_action_scope_then_no_errors() {
    // A provider call under a bare `action` scope must lower and validate —
    // the hoisted field is grafted onto every action's context. `Read` and
    // `Login` both exist; the field lands on both.
    let src = r#"permit (principal, action, resource) when guardrails {
  Strings::Matches(context.input.document, "^[A-Z]+$").matched == true
};"#;
    let result = validate_source(src, SCHEMA, Some(&decls()));
    assert!(
        result.validation_passed(),
        "expected a provider under a bare `action` scope to validate, got:\n{result:?}"
    );
}

#[test]
fn when_provider_under_action_in_group_scope_then_no_errors() {
    // A provider call under an `action in Group` scope must lower and
    // validate. The hoisted field is declared on every action's context
    // (the group `Trade` itself carries no appliesTo/input and is skipped);
    // the group scope determines which requests the rule fires for — its
    // descendants `Sell` and `Approve`. `document` exists on both leaves.
    let src = r#"permit (principal, action in [App::Action::"Trade"], resource) when guardrails {
  Strings::Matches(context.input.document, "^[A-Z]+$").matched == true
};"#;
    let result = validate_source(src, SCHEMA_HIER, Some(&decls()));
    assert!(
        result.validation_passed(),
        "expected a provider under an `action in Group` scope to validate (group expanded to \
         descendants), got:\n{result:?}"
    );
}

// ─── Span rebasing ──────────────────────────────────────────────────
// A diagnostic inside a `temporal { … }` / `provider { … }` block must
// report a byte offset into the *whole* `.dw` source, not one relative to
// the block body. The block is pushed deep into the source so a
// block-relative offset would land in the leading comment (well before the
// offending token).

#[test]
fn when_temporal_error_then_span_points_at_token_in_full_source() {
    // A tp-independence defect (a `formerly` body that cannot vary across
    // timepoints) is located by the temporal dialect at the offending
    // sub-expression's span. The block is pushed deep into the source, so a
    // block-relative offset would land in the leading comment; the reported
    // span must be the absolute offset of the tp-independent body.
    let src = r#"// leading comment so the temporal block starts deep in the source.
// padding ...........................................................
permit (
  principal,
  action == App::Action::"Read",
  resource
)
when temporal { formerly within 1h context.input.user == "alice" };
"#;
    let true_body_off = src
        .find("context.input.user == \"alice\"")
        .expect("tp-independent body present");

    let result = validate_source(src, SCHEMA, None);
    let reported = first_span_offset(&result, temporal_offset).expect("a Temporal error");

    assert_eq!(
        reported, true_body_off,
        "temporal span must be the absolute `.dw` offset of the offending body, not block-relative"
    );
}

#[test]
fn when_provider_error_then_span_points_at_invocation_in_full_source() {
    let src = r#"// leading comment so the provider block starts deep in the source.
// padding ...........................................................
permit (
  principal,
  action == App::Action::"Read",
  resource
)
when guardrails { Strings::Matchez(context.input.document, "^[A-Z]+$").matched == true };
"#;
    let true_invocation_off = src.find("Strings::Matchez").expect("invocation present");

    let result = validate_source(src, SCHEMA, Some(&decls()));
    let reported = first_span_offset(&result, provider_offset).expect("a Provider error");

    assert_eq!(
        reported, true_invocation_off,
        "provider span must be the absolute `.dw` offset of the invocation, not block-relative"
    );
}

// ─── Action-list scope ──────────────────────────────────────────────

#[test]
fn when_action_in_list_scope_then_context_field_not_falsely_rejected() {
    // A rule scoped `action in [Read]` reads `context.input.document`, a
    // field only `Read` declares (Login has no `document`). The pre-fix
    // behavior unioned the path over *every* declared action and would
    // reject it (Login lacks `document`); the fix skips the check for any
    // non-`==` scope, leaving typing to Cedar — so no Temporal error. This
    // field choice is what makes the test actually pin the fix: a field
    // present in every action would pass even with the old union behavior.
    let src = r#"
permit (principal, action in [App::Action::"Read"], resource)
when temporal { formerly within 1h App::Action::"Read"::request{input.document: context.input.document} };
"#;
    let result = validate_source(src, SCHEMA, None);
    assert!(
        !result.validation_errors().any(|e| matches!(
            e,
            ValidationError::Extension {
                code: "temporal",
                ..
            }
        )),
        "expected no Temporal error for a list scope whose field is valid for the \
         scoped action, got:\n{result:?}"
    );
}

// ─── Additional check coverage ──────────────────────────────────────

#[test]
fn when_temporal_arg_is_unknown_entity_type_then_temporal_error() {
    // `Nope::"x"` names an entity type not declared in the schema (only
    // `OAuthUser` and `Gateway` exist). `check_entity_types` must reject it.
    let src = r#"
permit (principal, action == App::Action::"Login", resource)
when temporal { formerly within 1h App::Action::"Login"::request{input.user: App::Nope::"x"} };
"#;
    let result = validate_source(src, SCHEMA, None);
    assert!(
        result.validation_errors().any(|e| matches!(
            e,
            ValidationError::Extension { code: "temporal", message, .. } if message.contains("entity type")
        )),
        "expected a Temporal unknown-entity-type error, got:\n{result:?}"
    );
}

#[test]
fn when_temporal_arg_is_known_entity_type_then_no_entity_error() {
    // `App::OAuthUser::"alice"` names a declared entity type, so
    // `check_entity_types` must not complain.
    let src = r#"
permit (principal, action == App::Action::"Login", resource)
when temporal { formerly within 1h App::Action::"Login"::request{input.user: App::OAuthUser::"alice"} };
"#;
    let result = validate_source(src, SCHEMA, None);
    assert!(
        !result.validation_errors().any(|e| matches!(
            e,
            ValidationError::Extension { code: "temporal", message, .. } if message.contains("entity type")
        )),
        "expected no unknown-entity-type error for a declared type, got:\n{result:?}"
    );
}

#[test]
fn when_since_left_var_bound_only_under_negation_then_rejected_at_parse() {
    // The negative `since` form `!left since within … right`: `v` occurs only
    // inside the negated left, and `u` only in the anchor — both free at the
    // leaf level. Historically this shape reached the tp-dependence check,
    // which had to know that a variable bound only under a negated `since`
    // left does not make the trailing `v == "alice"` conjunct tp-dependent.
    // Post-closedness the scenario is caught earlier and uniformly: a leaf
    // with ANY free variable is rejected at parse time (and had `v` been
    // `exists`-bound instead, the range-restriction check would reject it —
    // a negated occurrence restricts nothing). This pins the earlier, parse-
    // time rejection.
    let src = r#"
permit (principal, action == App::Action::"Login", resource)
when temporal {
  (!App::Action::"Login"::request{input.server: v} since within 1h App::Action::"Login"::request{input.user: u})
  && v == "alice"
};
"#;
    let service = ServiceSchema::builder()
        .event_schema_str(EVENT_SCHEMA)
        .build()
        .expect("service schema builds");
    let policy_schema = PolicySchema::from_cedarschema_str(SCHEMA).expect("policy schema builds");
    let err = LoweredPolicySet::from_str(src, &service, &policy_schema)
        .expect_err("a leaf with free variables must be rejected at parse time");
    assert!(
        err.to_string().contains("free in this temporal condition"),
        "expected the closedness rejection, got:\n{err}"
    );
}

// ─── tp() binder typing ─────────────────────────────────────────────
//
// `tp(x)` binds `x` to the current TIMEPOINT index. A binder declared with
// any other type conflates a timepoint with a data value: every use of `x`
// against a data field then never matches, and the whole guard is
// permanently false — a validated dead guard (fail-open on a forbid, by
// vacuity). The type check must require a `tp` variable's declared type to
// be `Timepoint`.

#[test]
fn when_tp_binds_a_non_timepoint_binder_then_temporal_error() {
    // `x` is declared String but bound by `tp(x)` and used against a String
    // field: `tp(x)` yields a timepoint index, so the predicate can never
    // match — a permanently-false condition that previously validated clean.
    let src = r#"
permit (principal, action == App::Action::"Read", resource)
when temporal { exists (x: String). (tp(x) && formerly within 1h App::Action::"Login"::request{input.user: x}) };
"#;
    let result = validate_source(src, SCHEMA, None);
    assert!(
        result.validation_errors().any(|e| matches!(
            e,
            ValidationError::Extension { code: "temporal", message, .. }
                if message.contains("tp(") && message.contains("Timepoint")
        )),
        "expected a tp-binder type error, got:\n{result:?}"
    );
}

#[test]
fn when_tp_binds_a_non_timepoint_for_binder_then_temporal_error() {
    // The aggregation-`for` variant: `for (x: String)` bound by `tp(x)`.
    let src = r#"
permit (principal, action == App::Action::"Read", resource)
when temporal { exists (n: Long). ((count for (x: String). where (formerly within 1h (App::Action::"Login"::request{} && tp(x)))) == n && n >= 1) };
"#;
    let result = validate_source(src, SCHEMA, None);
    assert!(
        result.validation_errors().any(|e| matches!(
            e,
            ValidationError::Extension { code: "temporal", message, .. }
                if message.contains("tp(") && message.contains("Timepoint")
        )),
        "expected a tp-binder type error for the for-binder, got:\n{result:?}"
    );
}

#[test]
fn when_tp_binds_a_timepoint_binder_then_no_error() {
    // Control: the correctly-typed shapes stay clean — an exists binder and
    // a for binder, both declared Timepoint.
    let exists_src = r#"
permit (principal, action == App::Action::"Read", resource)
when temporal { exists (t: Timepoint). (formerly within 1h (App::Action::"Login"::request{input.user: context.input.user} && tp(t))) };
"#;
    let result = validate_source(exists_src, SCHEMA, None);
    assert!(
        result.validation_passed(),
        "a Timepoint-declared exists tp-binder must validate clean, got:\n{result:?}"
    );
    let for_src = r#"
permit (principal, action == App::Action::"Read", resource)
when temporal { exists (n: Long). ((count for (t: Timepoint). where (formerly within 1h (App::Action::"Login"::request{} && tp(t)))) == n && n >= 1) };
"#;
    let result = validate_source(for_src, SCHEMA, None);
    assert!(
        result.validation_passed(),
        "a Timepoint-declared for tp-binder must validate clean, got:\n{result:?}"
    );
}

#[test]
fn when_var_is_positively_bound_in_a_conjunct_then_no_tp_error() {
    // The positive dual of the negation tests: `u` is bound by a positive
    // predicate arg, so the `u == "alice"` conjunct IS tp-dependent through
    // it and must not be flagged. Closedness requires the leaf to bind `u`
    // with an `exists`; the binding equality then reads the positively-bound
    // variable exactly as before.
    let src = r#"
permit (principal, action == App::Action::"Login", resource)
when temporal { exists (u: String). (App::Action::"Login"::request{input.user: u} && u == "alice") };
"#;
    let result = validate_source(src, SCHEMA, None);
    // Assert the whole policy is clean (not merely "no Temporal error"), so
    // the test cannot pass vacuously: `u` is positively bound, so the
    // `u == "alice"` conjunct is tp-dependent and the leaf is well-formed.
    assert!(
        result.validation_passed(),
        "expected no errors: `u` is positively bound, so `u == \"alice\"` is \
         tp-dependent, got:\n{result:?}"
    );
}

#[test]
fn when_temporal_arg_is_action_literal_then_no_unknown_entity_type_error() {
    // An action UID `App::Action::"Login"` used as a term parses to
    // `Term::Entity { ty: "App::Action", id: "Login" }`. `check_entity_types`
    // must recognize the trailing `Action` segment and skip the entity-type
    // lookup (Cedar's own action resolver owns action refs), rather than
    // reporting a spurious `unknown entity type App::Action`. (A genuine
    // type mismatch on the comparison is fine and unrelated; this pins only
    // the absence of the misclassification diagnostic.)
    let src = r#"
permit (principal, action == App::Action::"Read", resource)
when temporal { exists (u: String). (App::Action::"Read"::request{input.user: u} && u == App::Action::"Login") };
"#;
    let result = validate_source(src, SCHEMA, None);
    assert!(
        !result.validation_errors().any(|e| matches!(
            e,
            ValidationError::Extension { code: "temporal", message, .. }
                if message.contains("entity type") && message.contains("App::Action")
        )),
        "expected no spurious unknown-entity-type error for the action literal \
         `App::Action::\"Login\"`, got:\n{result:?}"
    );
}

#[test]
fn when_action_in_list_scope_references_field_absent_from_scoped_action_then_temporal_error() {
    // A rule scoped `action in [Login]` reads `context.input.document`, a
    // field only `Read` declares (`Login` has no `document`). The leaf
    // attaches to `Login`, so the missing field must be caught. Pre-fix,
    // a list scope lowered to `None` and the context-field check was
    // skipped entirely, so this drew no diagnostic (the "monitors nothing"
    // class of silent failure this validator exists to catch).
    let src = r#"
permit (principal, action in [App::Action::"Login"], resource)
when temporal { formerly within 1h App::Action::"Login"::request{input.user: context.input.document} };
"#;
    let result = validate_source(src, SCHEMA, None);
    assert!(
        result.validation_errors().any(|e| matches!(
            e,
            ValidationError::Extension { code: "temporal", message, .. }
                if message.contains("document")
        )),
        "expected a Temporal error for `context.input.document` absent from the \
         list-scoped action `Login`, got:\n{result:?}"
    );
}

#[test]
fn when_action_in_list_scope_field_absent_from_a_later_action_then_temporal_error() {
    // The scope lists two actions, the *first* of which (`Read`) declares
    // `document` while the second (`Login`) does not. The field must be
    // validated against *every* listed action, not just the first — the
    // leaf attaches to each — so `Login` lacking `document` is an error.
    // This distinguishes a correct "check every action" fix from a naive
    // "check the first action" one (which would wrongly pass here).
    let src = r#"
permit (principal, action in [App::Action::"Read", App::Action::"Login"], resource)
when temporal { formerly within 1h App::Action::"Login"::request{input.user: context.input.document} };
"#;
    let result = validate_source(src, SCHEMA, None);
    assert!(
        result.validation_errors().any(|e| matches!(
            e,
            ValidationError::Extension { code: "temporal", message, .. }
                if message.contains("document")
        )),
        "expected a Temporal error: `document` is absent from `Login`, a listed \
         action, even though `Read` (listed first) declares it, got:\n{result:?}"
    );
}
