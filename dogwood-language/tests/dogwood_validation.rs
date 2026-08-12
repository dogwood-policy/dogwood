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

/// A variant of [`SCHEMA`] where `Read`'s `document` is **optional**
/// (`document?`). `Login` still has no `document` at all. Used by the
/// optional-attribute probes to see how Cedar treats a direct (unguarded)
/// read of an optional context attribute, vs. the definitely-absent case.
const SCHEMA_OPTIONAL_DOC: &str = r#"
namespace App {
  type LoginInput = { user: String, server: String };
  type ReadInput = { user: String, document?: String, tags: Set<String> };

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

/// A variant where `document` is **required** in `Read` but **optional**
/// (`document?`) in `Login` — present in BOTH actions, differing only in
/// optionality. Used to ask whether an unguarded read errors when the scope
/// spans a required environment and an optional one.
const SCHEMA_MIXED_DOC: &str = r#"
namespace App {
  type LoginInput = { user: String, server: String, document?: String };
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

// ─── Cedar core: a context field absent from *some* of a rule's scoped
//     actions. The pure-Cedar counterparts of the temporal
//     `when_action_in_list_scope_*` probes above. They pin what Cedar's own
//     schema-aware validator does when a rule's action scope spans request
//     environments with different `context.input` shapes — the analog of the
//     "check every action" temporal behavior, on the path where the attribute
//     access survives into the lowered Cedar (unlike a provider argument, which
//     is hoisted away and never reaches the validator). ─────────────────────

#[test]
fn when_cedar_clause_field_absent_from_eq_scoped_action_then_cedar_error() {
    // Pure-Cedar analog of `when_context_field_absent_from_scoped_action_*`
    // (which exercises the temporal path): the rule is scoped
    // `action == Login` (LoginInput = { user, server }), but the `when` reads
    // `context.input.document`, a field only `Read` declares. The single Login
    // request environment has no `document`, so Cedar's schema-aware validator
    // rejects it — the field being present on *another* action (`Read`) does
    // not excuse its absence from the *scoped* action. (Observed message form:
    // "attribute `input.document` in context for App::Action::\"Login\" not
    // found".)
    let src = r#"
permit (principal, action == App::Action::"Login", resource)
when { context.input.document == "x" };
"#;
    let result = validate_source(src, SCHEMA, None);
    assert!(
        result.validation_errors().any(|e| matches!(
            e,
            ValidationError::Cedar { message, .. }
                if message.contains("input.document")
                    && message.contains("Login")
                    && message.contains("not found")
        )),
        "expected a Cedar error: `context.input.document` is absent from the \
         scoped action `Login`, got:\n{result:?}"
    );
}

#[test]
fn when_cedar_clause_field_present_on_some_listed_actions_not_others_then_cedar_error() {
    // The scope lists two actions with different `context.input` shapes:
    // `Read` declares `document`, `Login` does not. The `when` reads
    // `context.input.document`.
    //
    // OBSERVED: Cedar's validator is *conjunctive over request environments* —
    // it type-checks the condition against EVERY action the scope admits, and
    // rejects if the access is invalid in ANY of them. So being valid under
    // `Read` does not rescue the policy: the `Login` environment lacks
    // `document`, and Cedar reports exactly that (same error as the `==` case).
    // This mirrors the temporal validator's "check every listed action"
    // behavior (`when_action_in_list_scope_field_absent_from_a_later_action_*`)
    // and is the safe/strict direction: a rule may only read a context field
    // guaranteed present in all of its scoped actions.
    let src = r#"
permit (principal, action in [App::Action::"Read", App::Action::"Login"], resource)
when { context.input.document == "x" };
"#;
    let result = validate_source(src, SCHEMA, None);
    assert!(
        !result.validation_passed(),
        "expected validation to fail: `document` is absent from `Login`, a \
         listed action, so the access is not valid in every request \
         environment the scope admits, got:\n{result:?}"
    );
    assert!(
        result.validation_errors().any(|e| matches!(
            e,
            ValidationError::Cedar { message, .. }
                if message.contains("input.document")
                    && message.contains("Login")
                    && message.contains("not found")
        )),
        "expected the Cedar error to name the `Login` environment that lacks \
         `document`, even though `Read` (also listed) declares it, got:\n{result:?}"
    );
}

#[test]
fn when_cedar_clause_field_absent_under_wildcard_action_then_cedar_error() {
    // Wildcard (unconstrained) action scope — the rule applies to EVERY action
    // in the schema, so its request-environment set is the full action set
    // (`Login` and `Read` here). `context.input.document` is declared by `Read`
    // but not `Login`.
    //
    // OBSERVED: the conjunctive-over-environments rule (see the `==` and
    // `action in [...]` probes above) extends to the wildcard case — a bare
    // `action` is just the widest scope, admitting all actions, so the access
    // must be valid in all of them. `Login` lacks `document`, so Cedar rejects
    // with the same `UnsafeAttributeAccess` error (`may_exist: false`) it gives
    // for the narrower scopes. Consequence for authors: a context field read
    // under a wildcard action must be present in the `context.input` of *every*
    // action the schema declares, or the policy fails validation.
    let src = r#"
permit (principal, action, resource)
when { context.input.document == "x" };
"#;
    let result = validate_source(src, SCHEMA, None);
    assert!(
        !result.validation_passed(),
        "expected validation to fail: under a wildcard action the access must \
         hold for every action, and `Login` lacks `document`, got:\n{result:?}"
    );
    assert!(
        result.validation_errors().any(|e| matches!(
            e,
            ValidationError::Cedar { message, .. }
                if message.contains("input.document")
                    && message.contains("Login")
                    && message.contains("not found")
        )),
        "expected a Cedar error naming an action (`Login`) whose context lacks \
         `document` under the wildcard scope, got:\n{result:?}"
    );
}

// ─── Cedar core: an OPTIONAL context attribute (`document?`). The same
//     scope-form suite as above, but now the field is declared optional in the
//     action(s) that have it. The new axis these pin: Cedar treats an UNGUARDED
//     read of an optional attribute as its own distinct error — "unable to
//     guarantee safety of access to optional attribute" (`may_exist: true`) —
//     as opposed to the definitely-absent "not found" (`may_exist: false`) of
//     the required-but-missing case above. A `has` guard resolves it. Both stay
//     in the error channel (warnings empty); nothing is promoted. ───────────

/// Substring of Cedar's error for reading an optional attribute WITHOUT a
/// `has` guard (the `may_exist: true` case).
const OPTIONAL_UNSAFE: &str = "unable to guarantee safety of access to optional attribute";

#[test]
fn when_cedar_clause_reads_optional_field_unguarded_then_cedar_error() {
    // `== Read`, where Read declares `document?` (optional). Read it directly,
    // WITHOUT a `has` guard. OBSERVED: this is a Cedar *error* (not a warning,
    // not a pass) — the optional-attribute safety check. It is a DIFFERENT
    // error than the required-but-absent case: "unable to guarantee safety of
    // access to optional attribute" rather than "not found".
    let src = r#"
permit (principal, action == App::Action::"Read", resource)
when { context.input.document == "x" };
"#;
    let result = validate_source(src, SCHEMA_OPTIONAL_DOC, None);
    assert!(
        !result.validation_passed(),
        "an unguarded optional-attribute read must fail validation, got:\n{result:?}"
    );
    assert!(
        result.validation_errors().any(|e| matches!(
            e,
            ValidationError::Cedar { message, .. }
                if message.contains(OPTIONAL_UNSAFE)
                    && message.contains("input.document")
                    && message.contains("Read")
        )),
        "expected the optional-attribute safety error naming `Read`, got:\n{result:?}"
    );
    // The finding is in the ERROR channel; the warning channel is empty — this
    // is a genuine Cedar error, not a promoted warning.
    assert_eq!(
        result.validation_warnings().count(),
        0,
        "no warnings expected (the finding is a genuine error), got:\n{result:?}"
    );
}

#[test]
fn when_cedar_clause_reads_optional_field_has_guarded_then_ok() {
    // The idiomatic safe form: guard the optional read with `has`. OBSERVED:
    // validation passes cleanly — no errors, no warnings. This is the contrast
    // that shows the unguarded case above is specifically about the missing
    // guard, not about the field being optional per se.
    let src = r#"
permit (principal, action == App::Action::"Read", resource)
when { context.input has document && context.input.document == "x" };
"#;
    let result = validate_source(src, SCHEMA_OPTIONAL_DOC, None);
    assert!(
        result.validation_passed(),
        "a `has`-guarded optional read must validate cleanly, got:\n{result:?}"
    );
}

#[test]
fn when_cedar_clause_optional_field_in_list_scope_reports_each_failing_env() {
    // `in [Read, Login]`: Read declares `document?` (optional), Login has no
    // `document` at all. OBSERVED: Cedar checks every environment and reports a
    // finding PER failing environment, of the appropriate kind:
    //   * `Login` — definitely absent  -> "input.document ... not found"
    //   * `Read`  — optional, unguarded -> the optional-safety error
    // So the two failure modes coexist in one scope, each attributed to its
    // action. Being optional in one environment does not mask being absent in
    // another.
    let src = r#"
permit (principal, action in [App::Action::"Read", App::Action::"Login"], resource)
when { context.input.document == "x" };
"#;
    let result = validate_source(src, SCHEMA_OPTIONAL_DOC, None);
    assert!(!result.validation_passed(), "must fail, got:\n{result:?}");
    let has_login_absent = result.validation_errors().any(|e| {
        matches!(
            e,
            ValidationError::Cedar { message, .. }
                if message.contains("input.document")
                    && message.contains("Login")
                    && message.contains("not found")
        )
    });
    let has_read_optional = result.validation_errors().any(|e| {
        matches!(
            e,
            ValidationError::Cedar { message, .. }
                if message.contains(OPTIONAL_UNSAFE) && message.contains("Read")
        )
    });
    assert!(
        has_login_absent && has_read_optional,
        "expected BOTH the `Login` not-found error and the `Read` optional-safety \
         error, got:\n{result:?}"
    );
}

#[test]
fn when_cedar_clause_optional_field_under_wildcard_reports_each_failing_env() {
    // Wildcard action — all actions. Read has `document?` (optional), Login
    // lacks it entirely. OBSERVED: same as the explicit list — one finding per
    // failing environment, each of its own kind (Login not-found, Read
    // optional-unsafe). The wildcard is just the widest environment set.
    let src = r#"
permit (principal, action, resource)
when { context.input.document == "x" };
"#;
    let result = validate_source(src, SCHEMA_OPTIONAL_DOC, None);
    assert!(!result.validation_passed(), "must fail, got:\n{result:?}");
    let has_login_absent = result.validation_errors().any(|e| {
        matches!(
            e,
            ValidationError::Cedar { message, .. }
                if message.contains("input.document")
                    && message.contains("Login")
                    && message.contains("not found")
        )
    });
    let has_read_optional = result.validation_errors().any(|e| {
        matches!(
            e,
            ValidationError::Cedar { message, .. }
                if message.contains(OPTIONAL_UNSAFE) && message.contains("Read")
        )
    });
    assert!(
        has_login_absent && has_read_optional,
        "expected BOTH the `Login` not-found error and the `Read` optional-safety \
         error under the wildcard scope, got:\n{result:?}"
    );
}

// ─── Cedar core: MIXED optionality across a scope's actions. `document` is
//     REQUIRED in `Read` but OPTIONAL in `Login` (present in both, differing
//     only in optionality). This isolates the question: does an unguarded read
//     error when the scope spans a required (safe) environment AND an optional
//     (unsafe-without-`has`) one? OBSERVED: yes — the optional environment
//     alone forces the error, because Cedar requires the access to be safe in
//     EVERY admitted action; a required, safe environment does not rescue an
//     optional, unguarded one. The finding is attributed to the optional
//     action. A `has` guard makes it safe in every environment at once. ──────

#[test]
fn when_cedar_clause_mixed_optionality_unguarded_then_cedar_error() {
    // `in [Read, Login]`: `document` REQUIRED in Read (safe unguarded),
    // OPTIONAL in Login (unsafe unguarded). The unguarded read errors, and the
    // error names the OPTIONAL environment (`Login`) — not `Read`.
    let src = r#"
permit (principal, action in [App::Action::"Read", App::Action::"Login"], resource)
when { context.input.document == "x" };
"#;
    let result = validate_source(src, SCHEMA_MIXED_DOC, None);
    assert!(
        !result.validation_passed(),
        "the optional environment (Login) must force an error even though Read \
         has `document` required, got:\n{result:?}"
    );
    assert!(
        result.validation_errors().any(|e| matches!(
            e,
            ValidationError::Cedar { message, .. }
                if message.contains(OPTIONAL_UNSAFE)
                    && message.contains("input.document")
                    && message.contains("Login")
        )),
        "expected the optional-attribute safety error attributed to `Login`, \
         got:\n{result:?}"
    );
    assert_eq!(
        result.validation_warnings().count(),
        0,
        "still an error, not a promoted warning, got:\n{result:?}"
    );
}

#[test]
fn when_cedar_clause_required_field_unguarded_is_safe() {
    // Baseline that makes the mixed result meaningful: scoped to `Read` ALONE,
    // where `document` is REQUIRED, an unguarded read validates cleanly. So the
    // error in the mixed case is contributed purely by the optional `Login`
    // environment, not by the read itself.
    let src = r#"
permit (principal, action == App::Action::"Read", resource)
when { context.input.document == "x" };
"#;
    let result = validate_source(src, SCHEMA_MIXED_DOC, None);
    assert!(
        result.validation_passed(),
        "an unguarded read of a REQUIRED attribute must be safe, got:\n{result:?}"
    );
}

#[test]
fn when_cedar_clause_mixed_optionality_has_guarded_then_ok() {
    // The `has` guard makes the access safe in EVERY environment at once —
    // required `Read` and optional `Login` alike — so the mixed scope validates
    // cleanly once guarded.
    let src = r#"
permit (principal, action in [App::Action::"Read", App::Action::"Login"], resource)
when { context.input has document && context.input.document == "x" };
"#;
    let result = validate_source(src, SCHEMA_MIXED_DOC, None);
    assert!(
        result.validation_passed(),
        "a `has`-guarded read must validate across both the required and \
         optional environments, got:\n{result:?}"
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

  action "Trade";
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
    // every action's context. We list only `Read`, whose input declares
    // `document`. (Listing `Login` too would now ERROR: the provider dialect
    // resolves the field-path argument against every listed action, and
    // `Login` declares no `document` — see
    // `when_provider_field_path_arg_absent_from_eq_scope_then_error`.)
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
    // the hoisted field is grafted onto every action's context. The field-path
    // ARGUMENT, however, must resolve on every action the bare scope reaches
    // (`Login` and `Read`), so it uses `user`, which both declare. (Using
    // `document` here would now ERROR: `Login` has no `document` — see
    // `when_provider_field_path_arg_absent_under_wildcard_then_error`.)
    let src = r#"permit (principal, action, resource) when guardrails {
  Strings::Matches(context.input.user, "^[A-Z]+$").matched == true
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
    // validate. The group `Trade` is a PURE group (no `appliesTo`), so the
    // scope resolves to its descendants `Sell` and `Approve` — both of which
    // declare `document`, so the field-path argument resolves on every action
    // the scope reaches.
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
// ═══════════════════════════════════════════════════════════════════
// CROSS-DIALECT MATRIX: how the three dialects validate an UNGUARDED field
// reference `context.input.document` that is absent / optional / mixed across
// a rule's scoped actions. All three lower the SAME schema; the only variable
// is which dialect the reference lives in. Observed behavior (locked below):
//
//   scenario (field reference, unguarded)     | Cedar core | Temporal | Provider
//   ------------------------------------------|-----------|----------|---------
//   REQUIRED, absent from a scoped action     |  ERROR    |  ERROR   |  ERROR
//     (== absent-action / in-list / wildcard) |           |          |
//   OPTIONAL, read without a `has` guard      |  ERROR    |  ok      |  ok
//   MIXED (req in one action, opt in another) |  ERROR    |  ok      |  ok
//   nonexistent field name (e.g. `bogus`)     |  ERROR    |  ERROR   |  ERROR
//
// ONE axis of inconsistency remains (axis (A) was closed — see below):
//
//  (A) [CLOSED] A field ENTIRELY ABSENT from a scoped action is now rejected by
//      all three dialects. The provider dialect resolves its field-path
//      arguments against every scoped action (`extension/provider/validate.rs`)
//      and errors on a definitely-missing context field, exactly as Cedar and
//      Temporal do. This is a VALIDATION-time check only: providers still
//      execute unconditionally at runtime and still receive Null for an absent
//      argument, so the Null-tolerant sentinel contract (corpus 0050/0051, and
//      the relocated ex-0052) is untouched. Before this, a provider argument
//      was the one dereference in the language exempt from the check — keyed
//      invisibly on the call being a provider.
//
//  (B) An OPTIONAL attribute read WITHOUT a `has` guard: Cedar rejects ("unable
//      to guarantee safety of access to optional attribute"); Temporal and
//      Provider both ACCEPT. Cedar is the strict outlier here — the temporal
//      grammar has no `has` guard concept and its context-path resolver treats a
//      declared-optional field as present, and the provider check likewise only
//      rejects a flatly-undeclared field (a present-but-optional one resolves).
//      Closing (B) needs Cedar-style `has`-narrowing over the hoisted leaf
//      (typechecking work), deliberately deferred. So "declared but optional" is
//      a safety error only in pure Cedar.
//
// The shared, consistent point: a field ENTIRELY ABSENT from a scoped action is
// now caught by ALL THREE dialects. The remaining divergence is (B) optionality
// being a Cedar-only safety concern.
//
// These tests LOCK the current behavior so any future convergence (e.g. teaching
// the temporal/provider dialects to require a guard for optionals) is a
// deliberate, visible change.
// ═══════════════════════════════════════════════════════════════════

/// True iff `result` carries a temporal-dialect error mentioning `document`.
fn temporal_document_errors(result: &ValidationResult) -> bool {
    result.validation_errors().any(|e| matches!(
        e,
        ValidationError::Extension { code: "temporal", message, .. } if message.contains("document")
    ))
}

// ─── Temporal dialect ───────────────────────────────────────────────
//
// Vehicle: the RHS `context.input.document` of a predicate named-arg, which
// resolves against the RULE SCOPE's actions (target_actions) — the same
// conjunctive-over-environments resolution Cedar uses. The predicate is
// anchored to `Login` (which declares `user` in every schema variant) purely to
// make the leaf time-point dependent; only the rule scope + schema vary.

#[test]
fn when_temporal_field_absent_from_eq_scoped_action_then_error() {
    // REQUIRED-elsewhere but ABSENT from the scoped action `Login`. Temporal
    // rejects — consistent with Cedar core.
    let src = r#"
permit (principal, action == App::Action::"Login", resource)
when temporal { formerly within 1h App::Action::"Login"::request{input.user: context.input.document} };
"#;
    let r = validate_source(src, SCHEMA, None);
    assert!(
        !r.validation_passed() && temporal_document_errors(&r),
        "temporal must reject a field absent from the scoped action, got:\n{r:?}"
    );
}

#[test]
fn when_temporal_field_absent_under_wildcard_then_error() {
    // Wildcard action reaches every action, including `Login` (no `document`).
    // Temporal rejects — consistent with Cedar core.
    let src = r#"
permit (principal, action, resource)
when temporal { formerly within 1h App::Action::"Login"::request{input.user: context.input.document} };
"#;
    let r = validate_source(src, SCHEMA, None);
    assert!(
        !r.validation_passed() && temporal_document_errors(&r),
        "temporal must reject an absent field under a wildcard scope, got:\n{r:?}"
    );
}

#[test]
fn when_temporal_reads_optional_field_unguarded_then_accepted() {
    // OPTIONAL `document?` in Read; scope == Read; read WITHOUT a `has` guard.
    // DIVERGENCE FROM CEDAR: temporal ACCEPTS (it has no `has`-guard concept and
    // treats a declared-optional field as present). Pure Cedar errors here with
    // "unable to guarantee safety of access to optional attribute".
    let src = r#"
permit (principal, action == App::Action::"Read", resource)
when temporal { formerly within 1h App::Action::"Login"::request{input.user: context.input.document} };
"#;
    let r = validate_source(src, SCHEMA_OPTIONAL_DOC, None);
    assert!(
        r.validation_passed(),
        "temporal accepts an unguarded optional read (no `has` concept); if this \
         now fails, the dialects have CONVERGED — update the matrix. got:\n{r:?}"
    );
}

#[test]
fn when_temporal_reads_optional_field_in_eq_scope_then_accepted() {
    // OPTIONAL `document?` in Login; scope == Login. Same divergence as above.
    let src = r#"
permit (principal, action == App::Action::"Login", resource)
when temporal { formerly within 1h App::Action::"Login"::request{input.user: context.input.document} };
"#;
    let r = validate_source(src, SCHEMA_MIXED_DOC, None);
    assert!(
        r.validation_passed(),
        "temporal accepts an unguarded optional read, got:\n{r:?}"
    );
}

#[test]
fn when_temporal_mixed_optionality_in_list_then_accepted() {
    // MIXED: `document` REQUIRED in Read, OPTIONAL in Login; scope in [Read,
    // Login]. Present (required or optional) in BOTH, so temporal ACCEPTS.
    // DIVERGENCE: Cedar rejects, attributing the optional-safety error to Login.
    let src = r#"
permit (principal, action in [App::Action::"Read", App::Action::"Login"], resource)
when temporal { formerly within 1h App::Action::"Login"::request{input.user: context.input.document} };
"#;
    let r = validate_source(src, SCHEMA_MIXED_DOC, None);
    assert!(
        r.validation_passed(),
        "temporal accepts a field present-but-optional across the scope, got:\n{r:?}"
    );
}

// ─── Provider dialect ───────────────────────────────────────────────
//
// Vehicle: a field-path argument to a declared provider,
// `Strings::Matches(context.input.document, "x").matched == true`. The
// invocation is hoisted to `context.providers.<id>` at lowering. The provider
// dialect now resolves the field-path ARGUMENT against the scoped actions and
// rejects a DEFINITELY-MISSING context field (matching Cedar/temporal) — a
// validation-time check that leaves the unconditional runtime execution and
// Null-tolerant sentinel contract untouched. A present-but-optional field is
// still accepted (divergence axis (B), pending the `has`-narrowing work).

#[test]
fn when_provider_field_path_arg_absent_from_eq_scope_then_error() {
    // `document` is ABSENT from the scoped action `Login`. Providers now MATCH
    // Cedar and temporal: a definitely-missing context field-path argument is a
    // validation error (closes divergence axis (A)). The provider still
    // EXECUTES unconditionally at runtime — this is a validation-time check
    // only — so the Null-tolerant sentinel contract is untouched.
    let src = r#"
permit (principal, action == App::Action::"Login", resource)
when { Strings::Matches(context.input.document, "x").matched == true };
"#;
    let r = validate_source(src, SCHEMA, Some(&decls()));
    assert!(
        r.validation_errors().any(|e| matches!(
            e,
            ValidationError::Extension { code: "provider", message, .. }
                if message.contains("context.input.document")
                    && message.contains("not present")
                    && message.contains("Login")
        )),
        "expected a provider error for a field-path arg absent from the scoped \
         action `Login`, got:\n{r:?}"
    );
}

#[test]
fn when_provider_field_path_arg_absent_under_wildcard_then_error() {
    // Wildcard scope reaches every action, including `Login` (no `document`),
    // so the definitely-missing check fires there — same as Cedar/temporal.
    let src = r#"
permit (principal, action, resource)
when { Strings::Matches(context.input.document, "x").matched == true };
"#;
    let r = validate_source(src, SCHEMA, Some(&decls()));
    assert!(
        r.validation_errors().any(|e| matches!(
            e,
            ValidationError::Extension { code: "provider", message, .. }
                if message.contains("context.input.document") && message.contains("not present")
        )),
        "expected a provider error for an absent field-path arg under a wildcard \
         scope, got:\n{r:?}"
    );
}

#[test]
fn when_provider_field_path_arg_names_nonexistent_field_then_error() {
    // The starkest form: `bogus` is declared by NO action — the exact shape
    // Cedar core rejects in `when_cedar_clause_uses_unknown_field_then_cedar_error`.
    // The provider dialect now rejects it too (it resolves against `Read`'s
    // context and finds no `bogus`).
    let src = r#"
permit (principal, action == App::Action::"Read", resource)
when { Strings::Matches(context.input.bogus, "x").matched == true };
"#;
    let r = validate_source(src, SCHEMA, Some(&decls()));
    assert!(
        r.validation_errors().any(|e| matches!(
            e,
            ValidationError::Extension { code: "provider", message, .. }
                if message.contains("context.input.bogus")
                    && message.contains("not present")
                    && message.contains("Read")
        )),
        "expected a provider error for a field-path arg naming a field no action \
         declares, got:\n{r:?}"
    );
}

#[test]
fn when_provider_wrong_arity_is_still_caught() {
    // CONTROL: provider validation is not a no-op. Arity IS checked — so the
    // acceptance above is specifically about field-path *arguments* being
    // unresolved, not about the provider dialect skipping validation wholesale.
    let src = r#"
permit (principal, action == App::Action::"Read", resource)
when { Strings::Matches(context.input.document).matched == true };
"#;
    let r = validate_source(src, SCHEMA, Some(&decls()));
    assert!(
        r.validation_errors().any(|e| matches!(
            e,
            ValidationError::Extension { code: "provider", message, .. }
                if message.contains("expects 2 argument(s) but got 1")
        )),
        "provider arity must still be caught, got:\n{r:?}"
    );
}

// ═══════════════════════════════════════════════════════════════════
// CROSS-DIALECT WRONG-TYPE MATRIX. Companion to the missing/present matrix
// above, for the case where a field is declared with a DIFFERENT TYPE across
// scoped actions (`amount` is Long on `Read`, String on `Login`) and used in a
// type-specific way (`> 5`, or as a string-typed provider argument). Observed:
//
//   scenario                                      | Cedar core | Temporal | Provider
//   ----------------------------------------------|-----------|----------|---------
//   type matches the scoped action (== Read)      |  ok       |  ok      |  ok
//   type wrong on the scoped action (== Login)    |  ERROR    |  ERROR   |  ERROR
//   type wrong on some listed action (in / bare)  |  ERROR    |  ERROR   |  ERROR
//
// Cedar type-checks per request environment ("unexpected type: expected Long
// but saw String"); the temporal dialect type-checks per action ("comparison
// requires numeric operands ... got `string` and `int`"). Both reject a field
// whose type is wrong on ANY scoped action.
//
// AXIS (C) — CLOSED for scalars. The provider dialect now compares a field-path
// argument's resolved rich type against the declared `paramType` per scoped
// action (`extension/provider/validate.rs::check_field_path_type`), reusing the
// SAME `resolve_context_path` resolution as the existence check. A `Long` field
// passed to a `string`-declared argument is rejected, on any scoped action,
// consistent with Cedar/temporal and with how the provider's LITERAL arguments
// are already type-checked. SCOPE OF THE CLOSURE: only clear scalar-vs-scalar
// mismatches (String/Long/Bool/decimal) are rejected; non-scalar declared types
// (`set`/`record`) and non-scalar resolved types (`array`/`object`/`entity`)
// are still lenient (a documented, deliberate boundary — tightening set element
// types / records / entities is a future step). The optional caveat from axis
// (B) still applies: an optional field resolves as present, so it is
// type-checked when its type is known.
// ═══════════════════════════════════════════════════════════════════

const SCHEMA_TYPEVARIES: &str = r#"
namespace App {
  type ReadInput  = { user: String, amount: Long };
  type LoginInput = { user: String, amount: String };
  entity Gateway;
  entity OAuthUser = { id: String };
  action "Read" appliesTo {
    principal: [OAuthUser], resource: [Gateway], context: { input: ReadInput }
  };
  action "Login" appliesTo {
    principal: [OAuthUser], resource: [Gateway], context: { input: LoginInput }
  };
}
"#;

/// True iff `result` carries a Cedar error whose message contains `needle`.
fn cedar_error_contains(result: &ValidationResult, needle: &str) -> bool {
    result.validation_errors().any(|e| {
        matches!(
            e,
            ValidationError::Cedar { message, .. } if message.contains(needle)
        )
    })
}

// ── Cedar core ──
#[test]
fn when_cedar_wrong_type_on_matching_action_then_ok() {
    // `amount` is Long on `Read`; `> 5` is well-typed there. Baseline.
    let src = r#"permit (principal, action == App::Action::"Read", resource) when { context.input.amount > 5 };"#;
    let r = validate_source(src, SCHEMA_TYPEVARIES, None);
    assert!(
        r.validation_passed(),
        "Long amount `> 5` is well-typed, got:\n{r:?}"
    );
}

#[test]
fn when_cedar_wrong_type_on_scoped_action_then_error() {
    // `amount` is String on `Login`; `> 5` is a Cedar type error.
    let src = r#"permit (principal, action == App::Action::"Login", resource) when { context.input.amount > 5 };"#;
    let r = validate_source(src, SCHEMA_TYPEVARIES, None);
    assert!(
        cedar_error_contains(&r, "expected Long but saw String"),
        "Cedar must reject `String > 5`, got:\n{r:?}"
    );
}

#[test]
fn when_cedar_wrong_type_in_list_then_error() {
    // Read(Long) OK, Login(String) is the type error — per request environment.
    let src = r#"permit (principal, action in [App::Action::"Read", App::Action::"Login"], resource) when { context.input.amount > 5 };"#;
    let r = validate_source(src, SCHEMA_TYPEVARIES, None);
    assert!(
        cedar_error_contains(&r, "expected Long but saw String"),
        "Cedar must reject the type-wrong environment (Login), got:\n{r:?}"
    );
}

#[test]
fn when_cedar_wrong_type_under_wildcard_then_error() {
    let src = r#"permit (principal, action, resource) when { context.input.amount > 5 };"#;
    let r = validate_source(src, SCHEMA_TYPEVARIES, None);
    assert!(
        cedar_error_contains(&r, "expected Long but saw String"),
        "Cedar must reject the type-wrong environment under a wildcard, got:\n{r:?}"
    );
}

// ── Temporal ── (a `> 5` comparison inside a `formerly` body, anchored by a
// predicate so the leaf is time-point dependent). The temporal type checker
// resolves `context.input.amount` per scoped action and rejects the numeric
// comparison where it is a String.
#[test]
fn when_temporal_wrong_type_on_scoped_action_then_error() {
    let src = r#"permit (principal, action == App::Action::"Login", resource)
when temporal { formerly within 1h (App::Action::"Read"::request{} && context.input.amount > 5) };"#;
    let r = validate_source(src, SCHEMA_TYPEVARIES, None);
    assert!(
        r.validation_errors().any(|e| matches!(
            e,
            ValidationError::Extension { code: "temporal", message, .. }
                if message.contains("numeric operands")
        )),
        "temporal must reject a numeric comparison on a String field, got:\n{r:?}"
    );
}

#[test]
fn when_temporal_wrong_type_in_list_then_error() {
    let src = r#"permit (principal, action in [App::Action::"Read", App::Action::"Login"], resource)
when temporal { formerly within 1h (App::Action::"Read"::request{} && context.input.amount > 5) };"#;
    let r = validate_source(src, SCHEMA_TYPEVARIES, None);
    assert!(
        r.validation_errors().any(|e| matches!(
            e,
            ValidationError::Extension { code: "temporal", message, .. }
                if message.contains("numeric operands")
        )),
        "temporal must reject the type-wrong listed action (Login), got:\n{r:?}"
    );
}

// ── Provider ── axis (C) CLOSED for scalars: field-path argument TYPE is
// checked against the declared paramType per scoped action. `Strings::Matches`
// declares arg0 `string`; `amount` is `Long` on `Read` — a mismatch, rejected.
#[test]
fn when_provider_wrong_type_field_path_arg_then_error() {
    // Single action, unambiguous mismatch: a Long field into a string-declared
    // provider argument. Rejected (was accepted before axis (C) closed).
    let src = r#"permit (principal, action == App::Action::"Read", resource)
when { Strings::Matches(context.input.amount, "x").matched == true };"#;
    let r = validate_source(src, SCHEMA_TYPEVARIES, Some(&decls()));
    assert!(
        r.validation_errors().any(|e| matches!(
            e,
            ValidationError::Extension { code: "provider", message, .. }
                if message.contains("context.input.amount")
                    && message.contains("has type `Long`")
                    && message.contains("declares argument type `string`")
                    && message.contains("Read")
        )),
        "provider must reject a Long field-path arg into a string-declared \
         argument, got:\n{r:?}"
    );
}

#[test]
fn when_provider_wrong_type_in_list_then_error() {
    // Read(Long, mismatch) + Login(String, match). The mismatching action
    // (Read) is rejected — "wrong on any", matching Cedar/temporal.
    let src = r#"permit (principal, action in [App::Action::"Read", App::Action::"Login"], resource)
when { Strings::Matches(context.input.amount, "x").matched == true };"#;
    let r = validate_source(src, SCHEMA_TYPEVARIES, Some(&decls()));
    assert!(
        r.validation_errors().any(|e| matches!(
            e,
            ValidationError::Extension { code: "provider", message, .. }
                if message.contains("has type `Long`") && message.contains("Read")
        )),
        "provider must reject the type-mismatched action (Read) in a list scope, \
         got:\n{r:?}"
    );
}

#[test]
fn when_provider_matching_type_field_path_arg_then_ok() {
    // Control: on `Login`, `amount` is String, matching the declared `string`
    // argument — so a single-action scope to Login validates. Confirms the
    // check rejects only genuine mismatches, not the field per se.
    let src = r#"permit (principal, action == App::Action::"Login", resource)
when { Strings::Matches(context.input.amount, "x").matched == true };"#;
    let r = validate_source(src, SCHEMA_TYPEVARIES, Some(&decls()));
    assert!(
        r.validation_passed(),
        "a String field into a string-declared arg must validate, got:\n{r:?}"
    );
}

// ═══════════════════════════════════════════════════════════════════
// CHAIN RESOLUTION, TYPE ALIASES, CROSS-NAMESPACE TYPES, METHOD ARGS, and
// principal/resource typing. These pin that the provider field-path checks
// (existence axis A + scalar type axis C) resolve correctly through:
//   * a DEEP nested record path (`context.input.profile.age`),
//   * a CROSS-NAMESPACE common type (`Core::Profile` used in `App`),
//   * a same-namespace type ALIAS (`type Age = Long`), resolved to Long,
//   * the mid-chain failure modes `NestedMissing` and `NonRecord`,
//   * a provider METHOD-CHAIN argument (`.taggedWith(context.input....)`).
// All of the above resolve via the SAME `resolve_context_path` the temporal
// dialect uses, against the augmented (common-types-inlined) schema.
//
// principal/resource: CLOSED. Cedar (and the temporal dialect, via
// `resolve_scope_path`) type-check a `principal.<attr>` / `resource.<attr>`
// tail. The provider dialect now does the same: `ProviderField` carries the
// rule's `principal`/`resource` scope constraints, and the checks resolve a
// scope-rooted argument via `resolve_scope_path` NARROWED by them — so a
// missing attribute (`principal.bogus`) or a wrong scalar type (`principal.level`
// Long into a string arg) is rejected, while a rule narrowed with
// `principal is T` to a type that HAS the attribute is not falsely rejected
// against sibling types it excludes. `Ambiguous` (attr present on every
// admitted type but at different types) stays lenient, as with context.
// ═══════════════════════════════════════════════════════════════════

// Nested record reached via a CROSS-NAMESPACE common type (`Core::Profile`)
// whose `age` field uses a same-namespace type ALIAS (`type Age = Long`).
const SCHEMA_NESTED: &str = r#"
namespace Core {
  type Age = Long;
  type Profile = { age: Age, name: String };
}
namespace App {
  type ReadInput = { user: String, profile: Core::Profile };
  entity Gateway;
  entity OAuthUser = { id: String, dept: String };
  action "Read" appliesTo {
    principal: [OAuthUser], resource: [Gateway], context: { input: ReadInput }
  };
}
"#;

fn decls_method() -> ProviderDeclarations {
    ProviderDeclarations::from_json(
        r#"{ "availableProviders": {
          "Doc::Check": {
            "argumentTypes": [{ "paramType": "string" }],
            "outputType": { "paramType": "record", "fields": { "ok": { "paramType": "bool" } }, "required": ["ok"] },
            "availableMethods": {
              "taggedWith": {
                "argumentTypes": [{ "paramType": "string" }],
                "outputType": { "paramType": "record", "fields": { "ok": { "paramType": "bool" } }, "required": ["ok"] }
              }
            }
          }
        }}"#,
    )
    .expect("decls_method parse")
}

/// True iff `result` has a provider error whose message contains `needle`.
fn provider_error_contains(result: &ValidationResult, needle: &str) -> bool {
    result.validation_errors().any(|e| {
        matches!(
            e,
            ValidationError::Extension { code: "provider", message, .. } if message.contains(needle)
        )
    })
}

#[test]
fn when_provider_deep_chain_type_matches_then_ok() {
    // context.input.profile.name : String (reached through the cross-namespace
    // common type Core::Profile) into a string-declared arg. Resolves and matches.
    let src = r#"permit (principal, action == App::Action::"Read", resource) when { Strings::Matches(context.input.profile.name, "x").matched == true };"#;
    let r = validate_source(src, SCHEMA_NESTED, Some(&decls()));
    assert!(
        r.validation_passed(),
        "deep cross-namespace String path must resolve, got:\n{r:?}"
    );
}

#[test]
fn when_provider_deep_chain_type_mismatch_via_alias_then_error() {
    // context.input.profile.age : Age = Long (a same-namespace ALIAS resolved to
    // Long) into a string-declared arg. The type check sees through the alias.
    let src = r#"permit (principal, action == App::Action::"Read", resource) when { Strings::Matches(context.input.profile.age, "x").matched == true };"#;
    let r = validate_source(src, SCHEMA_NESTED, Some(&decls()));
    assert!(
        provider_error_contains(&r, "context.input.profile.age")
            && provider_error_contains(&r, "has type `Long`")
            && provider_error_contains(&r, "declares argument type `string`"),
        "aliased Long field must be caught as a type mismatch, got:\n{r:?}"
    );
}

#[test]
fn when_provider_deep_chain_nested_missing_then_error() {
    // context.input.profile.bogus : NestedMissing inside the nested record.
    let src = r#"permit (principal, action == App::Action::"Read", resource) when { Strings::Matches(context.input.profile.bogus, "x").matched == true };"#;
    let r = validate_source(src, SCHEMA_NESTED, Some(&decls()));
    assert!(
        provider_error_contains(&r, "context.input.profile.bogus")
            && provider_error_contains(&r, "not present"),
        "a deep NestedMissing field must be caught, got:\n{r:?}"
    );
}

#[test]
fn when_provider_deep_chain_non_record_then_error() {
    // context.input.profile.age.x : `age` is Long, so `.x` is a NonRecord
    // traversal — caught by the same existence check.
    let src = r#"permit (principal, action == App::Action::"Read", resource) when { Strings::Matches(context.input.profile.age.x, "x").matched == true };"#;
    let r = validate_source(src, SCHEMA_NESTED, Some(&decls()));
    assert!(
        provider_error_contains(&r, "context.input.profile.age.x")
            && provider_error_contains(&r, "not present"),
        "descending into a scalar (NonRecord) must be caught, got:\n{r:?}"
    );
}

#[test]
fn when_provider_method_chain_arg_missing_then_error() {
    // A field-path argument in a METHOD-chain call is checked too.
    let src = r#"permit (principal, action == App::Action::"Read", resource) when { Doc::Check(context.input.profile.name).taggedWith(context.input.profile.bogus).ok == true };"#;
    let r = validate_source(src, SCHEMA_NESTED, Some(&decls_method()));
    assert!(
        provider_error_contains(&r, "context.input.profile.bogus")
            && provider_error_contains(&r, "not present"),
        "a missing field in a method-chain arg must be caught, got:\n{r:?}"
    );
}

#[test]
fn when_provider_method_chain_arg_type_mismatch_then_error() {
    // A method-chain field-path arg is type-checked against the method's
    // declared argumentTypes (Long into taggedWith's string arg).
    let src = r#"permit (principal, action == App::Action::"Read", resource) when { Doc::Check(context.input.profile.name).taggedWith(context.input.profile.age).ok == true };"#;
    let r = validate_source(src, SCHEMA_NESTED, Some(&decls_method()));
    assert!(
        provider_error_contains(&r, "context.input.profile.age")
            && provider_error_contains(&r, "has type `Long`"),
        "a wrong-typed method-chain arg must be caught, got:\n{r:?}"
    );
}

// ── principal/resource typing across dialects ──
#[test]
fn when_cedar_principal_attr_missing_then_error() {
    let src = r#"permit (principal, action == App::Action::"Read", resource) when { principal.bogus == "x" };"#;
    let r = validate_source(src, SCHEMA_NESTED, None);
    assert!(
        cedar_error_contains(&r, "attribute `bogus`") && cedar_error_contains(&r, "not found"),
        "Cedar rejects a missing principal attribute, got:\n{r:?}"
    );
}

#[test]
fn when_cedar_principal_attr_wrong_type_then_error() {
    let src = r#"permit (principal, action == App::Action::"Read", resource) when { principal.dept > 5 };"#;
    let r = validate_source(src, SCHEMA_NESTED, None);
    assert!(
        cedar_error_contains(&r, "expected Long but saw String"),
        "Cedar type-checks a principal attribute, got:\n{r:?}"
    );
}

// A scope with a MULTI-TYPE principal: `OAuthUser` has `dept`(String)/`level`(Long),
// `Bot` has neither; `Gateway` (resource) has `owner`. Exercises scope-attribute
// existence, type, narrowing, and the resource axis.
const SCHEMA_SCOPE: &str = r#"
namespace App {
  type ReadInput = { user: String };
  entity Gateway = { owner: String };
  entity OAuthUser = { id: String, dept: String, level: Long };
  entity Bot;
  action "Read" appliesTo {
    principal: [OAuthUser, Bot], resource: [Gateway], context: { input: ReadInput }
  };
}
"#;

#[test]
fn when_provider_principal_attr_missing_then_error() {
    // CLOSED: the provider now resolves a `principal.<attr>` argument against
    // the entity types the rule's scope admits — `bogus` does not exist on
    // OAuthUser (the only type `Read`'s principal admits here), so it errors,
    // consistent with Cedar (above).
    let src = r#"permit (principal, action == App::Action::"Read", resource) when { Strings::Matches(principal.bogus, "x").matched == true };"#;
    let r = validate_source(src, SCHEMA_NESTED, Some(&decls()));
    assert!(
        provider_error_contains(&r, "principal.bogus")
            && provider_error_contains(&r, "not present"),
        "provider must reject a missing principal attribute, got:\n{r:?}"
    );
}

#[test]
fn when_provider_resource_attr_missing_then_error() {
    let src = r#"permit (principal, action == App::Action::"Read", resource) when { Strings::Matches(resource.bogus, "x").matched == true };"#;
    let r = validate_source(src, SCHEMA_SCOPE, Some(&decls()));
    assert!(
        provider_error_contains(&r, "resource.bogus") && provider_error_contains(&r, "not present"),
        "provider must reject a missing resource attribute, got:\n{r:?}"
    );
}

#[test]
fn when_provider_resource_attr_present_then_ok() {
    // `Gateway.owner` : String into a string-declared arg. Resolves and matches.
    let src = r#"permit (principal, action == App::Action::"Read", resource) when { Strings::Matches(resource.owner, "x").matched == true };"#;
    let r = validate_source(src, SCHEMA_SCOPE, Some(&decls()));
    assert!(
        r.validation_passed(),
        "resource.owner (String) must validate, got:\n{r:?}"
    );
}

#[test]
fn when_provider_principal_attr_missing_on_one_type_then_error() {
    // Multi-type principal, UNNARROWED: `dept` exists on OAuthUser but NOT on
    // Bot, and the rule can fire for a Bot, so the read is rejected — Cedar's
    // per-environment answer.
    let src = r#"permit (principal, action == App::Action::"Read", resource) when { Strings::Matches(principal.dept, "x").matched == true };"#;
    let r = validate_source(src, SCHEMA_SCOPE, Some(&decls()));
    assert!(
        provider_error_contains(&r, "principal.dept") && provider_error_contains(&r, "not present"),
        "an attribute absent from one admitted principal type must be rejected, got:\n{r:?}"
    );
}

#[test]
fn when_provider_principal_narrowing_avoids_false_positive() {
    // KEY CORRECTNESS PIN: with `principal is App::OAuthUser`, the scope narrows
    // to OAuthUser (which HAS `dept`), so `principal.dept` resolves and the rule
    // validates — the narrowing prevents a false rejection against the excluded
    // `Bot` type. This is why ProviderField now carries the principal/resource
    // constraints.
    let src = r#"permit (principal is App::OAuthUser, action == App::Action::"Read", resource) when { Strings::Matches(principal.dept, "x").matched == true };"#;
    let r = validate_source(src, SCHEMA_SCOPE, Some(&decls()));
    assert!(
        r.validation_passed(),
        "narrowing to OAuthUser (which has `dept`) must avoid a false positive, got:\n{r:?}"
    );
}

#[test]
fn when_provider_principal_attr_wrong_type_then_error() {
    // Narrowed to OAuthUser so existence is satisfied; `level` is Long, into a
    // string-declared arg -> type mismatch (scope-path type check).
    let src = r#"permit (principal is App::OAuthUser, action == App::Action::"Read", resource) when { Strings::Matches(principal.level, "x").matched == true };"#;
    let r = validate_source(src, SCHEMA_SCOPE, Some(&decls()));
    assert!(
        provider_error_contains(&r, "principal.level")
            && provider_error_contains(&r, "has type `Long`"),
        "a Long principal attribute into a string arg must be a type error, got:\n{r:?}"
    );
}

// Scope entities with a NESTED record attribute reached via a CROSS-NAMESPACE
// common type (`Core::Profile`) whose `age` field uses a type ALIAS
// (`type Age = Long`). Verifies that principal/resource field-path resolution
// (existence + scalar type) walks deep chains, cross-namespace types, and
// aliases the same way the context path does.
const SCHEMA_SCOPE_NESTED: &str = r#"
namespace Core {
  type Age = Long;
  type Profile = { age: Age, name: String };
}
namespace App {
  entity Gateway = { meta: Core::Profile };
  entity OAuthUser = { id: String, profile: Core::Profile };
  action "Read" appliesTo {
    principal: [OAuthUser], resource: [Gateway], context: { input: { user: String } }
  };
}
"#;

#[test]
fn when_provider_principal_deep_chain_type_matches_then_ok() {
    // principal.profile.name : String (nested via cross-namespace Core::Profile).
    let src = r#"permit (principal, action == App::Action::"Read", resource) when { Strings::Matches(principal.profile.name, "x").matched == true };"#;
    let r = validate_source(src, SCHEMA_SCOPE_NESTED, Some(&decls()));
    assert!(
        r.validation_passed(),
        "deep principal String path must resolve, got:\n{r:?}"
    );
}

#[test]
fn when_provider_principal_deep_chain_type_mismatch_via_alias_then_error() {
    // principal.profile.age : Age = Long (alias) into a string-declared arg.
    let src = r#"permit (principal, action == App::Action::"Read", resource) when { Strings::Matches(principal.profile.age, "x").matched == true };"#;
    let r = validate_source(src, SCHEMA_SCOPE_NESTED, Some(&decls()));
    assert!(
        provider_error_contains(&r, "principal.profile.age")
            && provider_error_contains(&r, "has type `Long`"),
        "an aliased Long nested principal attribute must be a type error, got:\n{r:?}"
    );
}

#[test]
fn when_provider_principal_deep_chain_nested_missing_then_error() {
    let src = r#"permit (principal, action == App::Action::"Read", resource) when { Strings::Matches(principal.profile.bogus, "x").matched == true };"#;
    let r = validate_source(src, SCHEMA_SCOPE_NESTED, Some(&decls()));
    assert!(
        provider_error_contains(&r, "principal.profile.bogus")
            && provider_error_contains(&r, "not present"),
        "a deep NestedMissing principal attribute must be caught, got:\n{r:?}"
    );
}

#[test]
fn when_provider_principal_deep_chain_non_record_then_error() {
    // principal.profile.age.x : `age` is Long, so `.x` is a NonRecord traversal.
    let src = r#"permit (principal, action == App::Action::"Read", resource) when { Strings::Matches(principal.profile.age.x, "x").matched == true };"#;
    let r = validate_source(src, SCHEMA_SCOPE_NESTED, Some(&decls()));
    assert!(
        provider_error_contains(&r, "principal.profile.age.x")
            && provider_error_contains(&r, "not present"),
        "descending into a scalar principal attribute (NonRecord) must be caught, got:\n{r:?}"
    );
}

#[test]
fn when_provider_resource_deep_chain_type_matches_then_ok() {
    // resource.meta.name : String (nested via cross-namespace Core::Profile).
    let src = r#"permit (principal, action == App::Action::"Read", resource) when { Strings::Matches(resource.meta.name, "x").matched == true };"#;
    let r = validate_source(src, SCHEMA_SCOPE_NESTED, Some(&decls()));
    assert!(
        r.validation_passed(),
        "deep resource String path must resolve, got:\n{r:?}"
    );
}

#[test]
fn when_provider_resource_deep_chain_type_mismatch_via_alias_then_error() {
    // resource.meta.age : Age = Long (alias) into a string-declared arg.
    let src = r#"permit (principal, action == App::Action::"Read", resource) when { Strings::Matches(resource.meta.age, "x").matched == true };"#;
    let r = validate_source(src, SCHEMA_SCOPE_NESTED, Some(&decls()));
    assert!(
        provider_error_contains(&r, "resource.meta.age")
            && provider_error_contains(&r, "has type `Long`"),
        "an aliased Long nested resource attribute must be a type error, got:\n{r:?}"
    );
}

#[test]
fn when_provider_resource_deep_chain_nested_missing_then_error() {
    let src = r#"permit (principal, action == App::Action::"Read", resource) when { Strings::Matches(resource.meta.bogus, "x").matched == true };"#;
    let r = validate_source(src, SCHEMA_SCOPE_NESTED, Some(&decls()));
    assert!(
        provider_error_contains(&r, "resource.meta.bogus")
            && provider_error_contains(&r, "not present"),
        "a deep NestedMissing resource attribute must be caught, got:\n{r:?}"
    );
}

// ═══════════════════════════════════════════════════════════════════
// NON-SCALAR TYPE MATRIX (Set, record). Companion to the scalar wrong-type
// matrix, for the case where a field-path reference's type CATEGORY (set /
// record / entity) is used where another category is expected. Observed:
//
//   Cedar rejects EVERY category mismatch, per request environment:
//     Set == String          -> "the types String and Set<String> are not compatible"
//     Set > 5                -> "unexpected type: expected Long but saw Set<String>"
//     record == String       -> "the types String and {age: Long,} are not compatible"
//     String.contains(...)   -> "expected Set<..> but saw String"
//     Set<String>.contains(Long) -> "the types Long and String are not compatible" (element)
//     Set<String>.contains(String) -> ok (baseline)
//
// AXIS (C) non-scalar sub-boundary — CATEGORY (#1) + SET ELEMENT (#2) now
// CLOSED. The provider dialect's type check compares the resolved rich type
// against the declared `paramType` by category (scalar kind / set / record),
// and for a `set` also checks the element type when both are known. So a Set or
// record field into a `string`-declared arg is rejected (the two provider pins
// below), a Set<Long> field into a `Set<String>`-declared arg is rejected on the
// element, etc. — matching Cedar's category and set-element checks. STILL OPEN
// (#3): a record-declared arg accepts any record without comparing FIELDS —
// Cedar records are invariant (probed below), but exact field matching needs
// structured record types (the resolver collapses records to `object`) and is a
// deliberate deferred boundary. These pins lock the behavior.
// ═══════════════════════════════════════════════════════════════════
const SCHEMA_NONSCALAR: &str = r#"
namespace App {
  type ReadInput = {
    scalar: String,
    tags: Set<String>,
    nums: Set<Long>,
    profile: { age: Long }
  };
  entity Gateway;
  entity OAuthUser = { id: String };
  action "Read" appliesTo {
    principal: [OAuthUser], resource: [Gateway], context: { input: ReadInput }
  };
}
"#;

// ── Cedar core: category mismatches ──
#[test]
fn when_cedar_set_compared_to_scalar_then_error() {
    let src = r#"permit (principal, action == App::Action::"Read", resource) when { context.input.tags == "x" };"#;
    let r = validate_source(src, SCHEMA_NONSCALAR, None);
    assert!(
        cedar_error_contains(&r, "not compatible") && cedar_error_contains(&r, "Set<String>"),
        "Cedar rejects Set == String, got:\n{r:?}"
    );
}
#[test]
fn when_cedar_set_in_numeric_op_then_error() {
    let src = r#"permit (principal, action == App::Action::"Read", resource) when { context.input.tags > 5 };"#;
    let r = validate_source(src, SCHEMA_NONSCALAR, None);
    assert!(
        cedar_error_contains(&r, "Set<String>"),
        "Cedar rejects Set in a numeric op, got:\n{r:?}"
    );
}
#[test]
fn when_cedar_record_compared_to_scalar_then_error() {
    let src = r#"permit (principal, action == App::Action::"Read", resource) when { context.input.profile == "x" };"#;
    let r = validate_source(src, SCHEMA_NONSCALAR, None);
    assert!(
        cedar_error_contains(&r, "not compatible"),
        "Cedar rejects record == String, got:\n{r:?}"
    );
}
#[test]
fn when_cedar_scalar_used_as_set_then_error() {
    let src = r#"permit (principal, action == App::Action::"Read", resource) when { context.input.scalar.contains("x") };"#;
    let r = validate_source(src, SCHEMA_NONSCALAR, None);
    assert!(
        cedar_error_contains(&r, "expected Set") && cedar_error_contains(&r, "String"),
        "Cedar rejects `.contains` on a String, got:\n{r:?}"
    );
}
#[test]
fn when_cedar_set_element_type_mismatch_then_error() {
    let src = r#"permit (principal, action == App::Action::"Read", resource) when { context.input.tags.contains(5) };"#;
    let r = validate_source(src, SCHEMA_NONSCALAR, None);
    assert!(
        cedar_error_contains(&r, "not compatible"),
        "Cedar rejects Set<String>.contains(Long) on the element type, got:\n{r:?}"
    );
}
#[test]
fn when_cedar_set_element_type_matches_then_ok() {
    let src = r#"permit (principal, action == App::Action::"Read", resource) when { context.input.tags.contains("x") };"#;
    let r = validate_source(src, SCHEMA_NONSCALAR, None);
    assert!(
        r.validation_passed(),
        "Set<String>.contains(String) is well-typed, got:\n{r:?}"
    );
}

// ── Provider: non-scalar category (#1) + set element (#2) now CLOSED ──
#[test]
fn when_provider_set_into_scalar_arg_then_error() {
    // `tags` is Set<String> into a string-declared provider arg — a category
    // mismatch, now rejected (was accepted before #1).
    let src = r#"permit (principal, action == App::Action::"Read", resource) when { Strings::Matches(context.input.tags, "x").matched == true };"#;
    let r = validate_source(src, SCHEMA_NONSCALAR, Some(&decls()));
    assert!(
        provider_error_contains(&r, "context.input.tags")
            && provider_error_contains(&r, "has type `Set<String>`")
            && provider_error_contains(&r, "declares argument type `string`"),
        "provider must reject a Set into a string-declared arg, got:\n{r:?}"
    );
}
#[test]
fn when_provider_record_into_scalar_arg_then_error() {
    // `profile` is a record into a string-declared provider arg — category mismatch.
    let src = r#"permit (principal, action == App::Action::"Read", resource) when { Strings::Matches(context.input.profile, "x").matched == true };"#;
    let r = validate_source(src, SCHEMA_NONSCALAR, Some(&decls()));
    assert!(
        provider_error_contains(&r, "context.input.profile")
            && provider_error_contains(&r, "has type `record`"),
        "provider must reject a record into a string-declared arg, got:\n{r:?}"
    );
}

// EXPLORATORY: Cedar's record subtyping/compatibility, probed via `==`.
const SCHEMA_RECSUB: &str = r#"
namespace App {
  type RecA = { x: Long };
  type RecB = { x: Long, y: Long };
  type RecC = { x: String };
  type RecD = { x: Long, y?: Long };
  type ReadInput = { a: RecA, b: RecB, c: RecC, d: RecD, flag: Bool };
  entity Gateway;
  entity OAuthUser = { id: String };
  action "Read" appliesTo {
    principal: [OAuthUser], resource: [Gateway], context: { input: ReadInput }
  };
}
"#;
#[test]
fn when_cedar_record_types_are_invariant_for_eq() {
    // Cedar record `==` requires EXACT type equality. `a == a` is fine; any
    // structural difference — an extra required field (b), an extra OPTIONAL
    // field (d), a required-vs-optional flag (b vs d), or a differing attribute
    // type (c) — is "not compatible". Records are invariant: no width or depth
    // (optional) subtyping.
    let eq = |lhs: &str, rhs: &str| {
        let src = format!(
            "permit (principal, action == App::Action::\"Read\", resource) when {{ context.input.{lhs} == context.input.{rhs} }};"
        );
        validate_source(&src, SCHEMA_RECSUB, None)
    };
    assert!(eq("a", "a").validation_passed(), "a == a must validate");
    for (lhs, rhs, why) in [
        ("a", "b", "extra required field"),
        ("a", "d", "extra optional field"),
        ("a", "c", "differing attribute type"),
        ("b", "d", "required vs optional flag"),
    ] {
        let r = eq(lhs, rhs);
        assert!(
            cedar_error_contains(&r, "not compatible"),
            "Cedar must reject `{lhs} == {rhs}` ({why}) as incompatible, got:\n{r:?}"
        );
    }
}

#[test]
fn when_cedar_record_lub_requires_exact_shape() {
    // `if/then/else` computes the least-upper-bound of its branch types. Across
    // a width difference (b vs a) or an extra-optional difference (d vs a), no
    // LUB exists — a type error. Confirms records are invariant even under LUB,
    // not just `==`.
    let lub = |branch: &str| {
        let src = format!(
            "permit (principal, action == App::Action::\"Read\", resource) when {{ (if context.input.flag then context.input.{branch} else context.input.a).x == 1 }};"
        );
        validate_source(&src, SCHEMA_RECSUB, None)
    };
    assert!(!lub("b").validation_passed(), "LUB(b,a) width must fail");
    assert!(!lub("d").validation_passed(), "LUB(d,a) optional must fail");
}

// ═══════════════════════════════════════════════════════════════════
// FULL CATEGORY MATRIX for the provider field-path TYPE check (#1 category +
// #2 set element). A context with a field of every category, and providers
// declaring an argument of every category; each pin feeds one resolved
// category into one declared category and asserts match / mismatch.
// ═══════════════════════════════════════════════════════════════════
const SCHEMA_CATEGORIES: &str = r#"
namespace App {
  type ReadInput = {
    s: String,
    n: Long,
    b: Bool,
    d: decimal,
    set_s: Set<String>,
    set_n: Set<Long>,
    rec: { k: Long },
    ent: OAuthUser
  };
  entity Gateway;
  entity OAuthUser = { id: String };
  action "Read" appliesTo {
    principal: [OAuthUser], resource: [Gateway], context: { input: ReadInput }
  };
}
"#;

fn decls_categories() -> ProviderDeclarations {
    let out = r#"{ "paramType": "record", "fields": { "ok": { "paramType": "bool" } }, "required": ["ok"] }"#;
    let json = format!(
        r#"{{ "availableProviders": {{
          "Cat::Str":  {{ "argumentTypes": [{{ "paramType": "string" }}],  "outputType": {out} }},
          "Cat::Long": {{ "argumentTypes": [{{ "paramType": "long" }}],    "outputType": {out} }},
          "Cat::Bool": {{ "argumentTypes": [{{ "paramType": "bool" }}],    "outputType": {out} }},
          "Cat::Dec":  {{ "argumentTypes": [{{ "paramType": "decimal" }}], "outputType": {out} }},
          "Cat::SetS": {{ "argumentTypes": [{{ "paramType": "set", "items": {{ "paramType": "string" }} }}], "outputType": {out} }},
          "Cat::Rec":  {{ "argumentTypes": [{{ "paramType": "record", "fields": {{ "k": {{ "paramType": "long" }} }}, "required": ["k"] }}], "outputType": {out} }}
        }} }}"#
    );
    ProviderDeclarations::from_json(&json).expect("decls_categories parse")
}

/// Validate `Provider(field).ok == true` against the category schema/decls.
fn cat_case(call: &str) -> ValidationResult {
    let src = format!(
        "permit (principal, action == App::Action::\"Read\", resource) when {{ {call}.ok == true }};"
    );
    validate_source(&src, SCHEMA_CATEGORIES, Some(&decls_categories()))
}
fn cat_ok(call: &str) -> bool {
    cat_case(call).validation_passed()
}
fn cat_type_err(call: &str) -> bool {
    cat_case(call).validation_errors().any(|e| matches!(
        e,
        ValidationError::Extension { code: "provider", message, .. } if message.contains("has type")
    ))
}

#[test]
fn category_scalar_args_accept_only_the_same_scalar() {
    // Diagonal: each scalar-declared arg accepts its own scalar.
    assert!(cat_ok("Cat::Str(context.input.s)"), "string<-String");
    assert!(cat_ok("Cat::Long(context.input.n)"), "long<-Long");
    assert!(cat_ok("Cat::Bool(context.input.b)"), "bool<-Bool");
    assert!(cat_ok("Cat::Dec(context.input.d)"), "decimal<-decimal");
    // Off-diagonal scalar<->scalar: rejected.
    assert!(cat_type_err("Cat::Str(context.input.n)"), "string<-Long");
    assert!(cat_type_err("Cat::Str(context.input.b)"), "string<-Bool");
    assert!(cat_type_err("Cat::Str(context.input.d)"), "string<-decimal");
    assert!(cat_type_err("Cat::Long(context.input.s)"), "long<-String");
    assert!(cat_type_err("Cat::Bool(context.input.n)"), "bool<-Long");
    assert!(cat_type_err("Cat::Dec(context.input.n)"), "decimal<-Long");
}

#[test]
fn category_scalar_arg_rejects_nonscalar() {
    // A scalar-declared arg rejects a Set, a record, and an entity field.
    assert!(cat_type_err("Cat::Str(context.input.set_s)"), "string<-Set");
    assert!(
        cat_type_err("Cat::Str(context.input.rec)"),
        "string<-record"
    );
    assert!(
        cat_type_err("Cat::Str(context.input.ent)"),
        "string<-entity"
    );
}

#[test]
fn category_set_arg_checks_category_and_element() {
    // #1 category: a `set`-declared arg accepts an array, rejects scalars/records.
    assert!(
        cat_ok("Cat::SetS(context.input.set_s)"),
        "set<string><-Set<String>"
    );
    assert!(
        cat_type_err("Cat::SetS(context.input.s)"),
        "set<-String (category)"
    );
    assert!(
        cat_type_err("Cat::SetS(context.input.rec)"),
        "set<-record (category)"
    );
    // #2 element: Set<Long> into a Set<String>-declared arg is an element mismatch.
    assert!(
        cat_type_err("Cat::SetS(context.input.set_n)"),
        "set<string><-Set<Long> (element)"
    );
}

#[test]
fn category_record_arg_checks_category_only() {
    // #1 category: a `record`-declared arg accepts ANY record (fields deferred,
    // #3), rejects scalars and sets.
    assert!(
        cat_ok("Cat::Rec(context.input.rec)"),
        "record<-record (fields not compared, #3)"
    );
    assert!(
        cat_type_err("Cat::Rec(context.input.s)"),
        "record<-String (category)"
    );
    assert!(
        cat_type_err("Cat::Rec(context.input.set_s)"),
        "record<-Set (category)"
    );
}

// ═══════════════════════════════════════════════════════════════════
// `__cedar::` BUILTIN SPELLINGS. Cedar's reserved namespace can name the
// primitives (`__cedar::String`, `__cedar::Long`, …), and Dogwood's own
// common-type inlining pins bare builtins to that capture-proof spelling
// internally — a historical source of bugs. These pins confirm the rich-type
// projection reads Cedar's RESOLVED type (so `__cedar::String` classifies as
// String, NOT an entity named `String`), for a schema that MIXES the `__cedar::`
// and bare spellings, across both the provider and temporal type checks.
// ═══════════════════════════════════════════════════════════════════
const SCHEMA_CEDAR_NS: &str = r#"
namespace App {
  type ReadInput = {
    cedar_s: __cedar::String,
    cedar_n: __cedar::Long,
    cedar_b: __cedar::Bool,
    cedar_tags: Set<__cedar::String>,
    plain_s: String,
    plain_n: Long
  };
  entity Gateway;
  entity OAuthUser = { id: String };
  action "Read" appliesTo {
    principal: [OAuthUser], resource: [Gateway], context: { input: ReadInput }
  };
}
"#;

#[test]
fn when_provider_cedar_ns_string_field_matches_string_arg() {
    // `__cedar::String` must classify as String and match a string-declared arg
    // (not be treated as an entity named `String`).
    let src = r#"permit (principal, action == App::Action::"Read", resource) when { Strings::Matches(context.input.cedar_s, "x").matched == true };"#;
    let r = validate_source(src, SCHEMA_CEDAR_NS, Some(&decls()));
    assert!(
        r.validation_passed(),
        "__cedar::String must match a string arg, got:\n{r:?}"
    );
}

#[test]
fn when_provider_cedar_ns_long_field_mismatches_string_arg() {
    // `__cedar::Long` must classify as Long — a type mismatch against a string
    // arg, proving the `__cedar::` spelling resolved to the primitive.
    let src = r#"permit (principal, action == App::Action::"Read", resource) when { Strings::Matches(context.input.cedar_n, "x").matched == true };"#;
    let r = validate_source(src, SCHEMA_CEDAR_NS, Some(&decls()));
    assert!(
        provider_error_contains(&r, "context.input.cedar_n")
            && provider_error_contains(&r, "has type `Long`"),
        "__cedar::Long must be caught as a Long/String mismatch, got:\n{r:?}"
    );
}

#[test]
fn when_provider_cedar_ns_set_field_mismatches_string_arg() {
    // `Set<__cedar::String>` must classify as a Set (category mismatch vs string).
    let src = r#"permit (principal, action == App::Action::"Read", resource) when { Strings::Matches(context.input.cedar_tags, "x").matched == true };"#;
    let r = validate_source(src, SCHEMA_CEDAR_NS, Some(&decls()));
    assert!(
        provider_error_contains(&r, "context.input.cedar_tags")
            && provider_error_contains(&r, "has type `Set<String>`"),
        "Set<__cedar::String> must be caught as a Set/String mismatch, got:\n{r:?}"
    );
}

#[test]
fn when_provider_mixed_cedar_and_plain_spellings_agree() {
    // The `__cedar::`-spelled field and the bare-spelled field of the same type
    // behave identically — mixed use in one schema is consistent.
    let ok_cedar = r#"permit (principal, action == App::Action::"Read", resource) when { Strings::Matches(context.input.cedar_s, "x").matched == true };"#;
    let ok_plain = r#"permit (principal, action == App::Action::"Read", resource) when { Strings::Matches(context.input.plain_s, "x").matched == true };"#;
    let err_cedar = r#"permit (principal, action == App::Action::"Read", resource) when { Strings::Matches(context.input.cedar_n, "x").matched == true };"#;
    let err_plain = r#"permit (principal, action == App::Action::"Read", resource) when { Strings::Matches(context.input.plain_n, "x").matched == true };"#;
    assert!(validate_source(ok_cedar, SCHEMA_CEDAR_NS, Some(&decls())).validation_passed());
    assert!(validate_source(ok_plain, SCHEMA_CEDAR_NS, Some(&decls())).validation_passed());
    assert!(!validate_source(err_cedar, SCHEMA_CEDAR_NS, Some(&decls())).validation_passed());
    assert!(!validate_source(err_plain, SCHEMA_CEDAR_NS, Some(&decls())).validation_passed());
}

#[test]
fn when_temporal_cedar_ns_string_field_is_typed_as_string() {
    // In the temporal dialect too: `__cedar::String` resolves to String, so a
    // numeric comparison on it is a "numeric operands" type error — confirming
    // the projection is spelling-independent on the temporal path as well.
    let src = r#"permit (principal, action == App::Action::"Read", resource)
when temporal { formerly within 1h (App::Action::"Read"::request{} && context.input.cedar_s > 5) };"#;
    let r = validate_source(src, SCHEMA_CEDAR_NS, None);
    assert!(
        r.validation_errors().any(|e| matches!(
            e,
            ValidationError::Extension { code: "temporal", message, .. }
                if message.contains("numeric operands")
        )),
        "__cedar::String must type as String in temporal (numeric-op error), got:\n{r:?}"
    );
}

#[test]
fn when_temporal_cedar_ns_long_field_valid_numeric_then_ok() {
    // The accept side on the temporal path: `__cedar::Long` types as Long, so a
    // numeric comparison on it is well-typed and validates cleanly (confirming
    // the spelling resolves to the primitive, not a spurious type error).
    let src = r#"permit (principal, action == App::Action::"Read", resource)
when temporal { formerly within 1h (App::Action::"Read"::request{} && context.input.cedar_n > 5) };"#;
    let r = validate_source(src, SCHEMA_CEDAR_NS, None);
    assert!(
        r.validation_passed(),
        "a numeric comparison on a __cedar::Long field must validate, got:\n{r:?}"
    );
}

// ═══════════════════════════════════════════════════════════════════
// FEASIBILITY-AWARE FIELD-PATH VALIDATION (paired Cedar ⟷ provider).
//
// TWO fixes are pinned here, each provider assertion paired with the Cedar
// baseline it must mimic. Both provider dialects validate a field-path against
// the RESOLVED schema type "per environment", exactly as Cedar does; the
// provider dialect was doing it WRONG in two ways these pins expose:
//
//   FIX 1 (BLOCKING over-rejection): the provider checked a `context.*`
//   field-path argument against EVERY action a rule names, even actions the
//   rule's `principal is` / `resource is` scope head makes INFEASIBLE (no
//   valid request environment). Cedar (and the temporal dialect, via
//   `admits_any_env`) skip an infeasible (principal-type, action, resource-type)
//   environment. The provider did not, so it REJECTED policies Cedar accepts.
//
//   FIX 2 (ambiguous divergent type): when a scope attribute exists on every
//   admitted entity type but at DIFFERENT types (Long on one, String on
//   another), Cedar rejects any *use* that is type-incompatible in some
//   environment (while accepting `has` / a use valid in every environment).
//   The provider ACCEPTED such an argument outright — it must instead reject it
//   in the TYPE pass (the value cannot satisfy a single declared arg type in
//   every environment), while still treating the attribute as PRESENT.
//
// Fixtures below are the minimal shapes that isolate these: no pre-existing
// schema has disjoint principal types ACROSS actions (needed to make an action
// infeasible under narrowing) nor a divergent-typed attribute across a
// multi-type scope.
// ═══════════════════════════════════════════════════════════════════

/// Three actions spread over two principal entity types (OAuthUser, Bot) and
/// two resource types (Gateway, Vault), so `principal is` / `resource is`
/// narrowing can make a co-scoped action INFEASIBLE:
///   Read  : principal OAuthUser, resource Gateway, context has `document`(String) + `value`(String)
///   Login : principal Bot,       resource Gateway, context has NO `document`; `value` is Long
///   Admin : principal OAuthUser, resource Vault,   context has neither `document` nor `value`
const SCHEMA_ENV: &str = r#"
namespace App {
  type ReadInput  = { user: String, document: String, value: String };
  type LoginInput = { user: String, value: Long };
  type AdminInput = { user: String };
  entity Gateway;  entity Vault;
  entity OAuthUser = { id: String };  entity Bot = { id: String };
  action "Read"  appliesTo { principal: [OAuthUser], resource: [Gateway], context: { input: ReadInput } };
  action "Login" appliesTo { principal: [Bot],       resource: [Gateway], context: { input: LoginInput } };
  action "Admin" appliesTo { principal: [OAuthUser], resource: [Vault],   context: { input: AdminInput } };
}
"#;

/// A multi-type principal AND a multi-type resource where the SAME attribute
/// has a DIFFERENT type on each admitted type (`level`/`size`: Long vs String),
/// plus a `name` that is String on BOTH (the non-divergent control).
const SCHEMA_AMBIG: &str = r#"
namespace App {
  entity Gateway = { size: Long };
  entity Bucket  = { size: String };
  entity OAuthUser  = { level: Long,   name: String };
  entity ServiceBot = { level: String, name: String };
  action "Read" appliesTo {
    principal: [OAuthUser, ServiceBot], resource: [Gateway, Bucket],
    context: { input: { doc: String } }
  };
}
"#;

// Scope-head fragments reused across the paired tests.
const S_PRIN_READ_LOGIN: &str = r#"principal is App::OAuthUser, action in [App::Action::"Read", App::Action::"Login"], resource"#;
const S_RES_READ_ADMIN: &str =
    r#"principal, action in [App::Action::"Read", App::Action::"Admin"], resource is App::Gateway"#;
const S_PRIN_READ_ADMIN: &str = r#"principal is App::OAuthUser, action in [App::Action::"Read", App::Action::"Admin"], resource"#;

// ─── FIX 1: infeasible-environment gate ─────────────────────────────
// Cedar baselines (GREEN — these DOCUMENT the behavior the provider must mimic).

#[test]
fn cedar_infeasible_principal_env_context_ref_accepted() {
    // `principal is OAuthUser` + `action in [Read, Login]`: Login applies only to
    // Bot, so the (OAuthUser, Login) environment is INFEASIBLE. The one feasible
    // environment (OAuthUser, Read) declares `document`, so Cedar ACCEPTS —
    // even though `Login` has no `document`.
    let src = format!(r#"permit ({S_PRIN_READ_LOGIN}) when {{ context.input.document == "x" }};"#);
    let r = validate_source(&src, SCHEMA_ENV, None);
    assert!(
        r.validation_passed(),
        "Cedar skips the infeasible (OAuthUser, Login) env and accepts, got:\n{r:?}"
    );
}

#[test]
fn cedar_infeasible_principal_env_divergent_type_accepted() {
    // Same infeasible-Login scope, but `value` is String on Read and Long on
    // Login. Only the Read env is feasible (value: String), so `== "x"` is
    // well-typed and Cedar ACCEPTS — the Long-on-Login typing never applies.
    let src = format!(r#"permit ({S_PRIN_READ_LOGIN}) when {{ context.input.value == "x" }};"#);
    let r = validate_source(&src, SCHEMA_ENV, None);
    assert!(
        r.validation_passed(),
        "Cedar ignores the infeasible env's `value: Long` typing and accepts, got:\n{r:?}"
    );
}

#[test]
fn cedar_infeasible_resource_env_context_ref_accepted() {
    // Resource axis: `resource is Gateway` + `action in [Read, Admin]`: Admin
    // applies only to Vault, so (Gateway, Admin) is INFEASIBLE. The feasible
    // (Gateway, Read) env has `document`, so Cedar ACCEPTS.
    let src = format!(r#"permit ({S_RES_READ_ADMIN}) when {{ context.input.document == "x" }};"#);
    let r = validate_source(&src, SCHEMA_ENV, None);
    assert!(
        r.validation_passed(),
        "Cedar skips the infeasible (Gateway, Admin) env and accepts, got:\n{r:?}"
    );
}

#[test]
fn cedar_feasible_env_missing_context_field_rejected() {
    // CONTROL / boundary: `principal is OAuthUser` + `action in [Read, Admin]`.
    // Admin applies to OAuthUser (feasible!) but its context has NO `document`,
    // so Cedar REJECTS. This is the line the gate must NOT cross: skip only
    // INFEASIBLE envs, never a feasible-but-missing one.
    let src = format!(r#"permit ({S_PRIN_READ_ADMIN}) when {{ context.input.document == "x" }};"#);
    let r = validate_source(&src, SCHEMA_ENV, None);
    assert!(
        cedar_error_contains(&r, "input.document")
            && cedar_error_contains(&r, r#"App::Action::"Admin""#),
        "Cedar must reject a field missing on the FEASIBLE Admin env, got:\n{r:?}"
    );
}

// Provider pins. The three "infeasible" pins are RED on current code (the
// provider errors on the infeasible action); the fix makes them pass. The
// feasible-but-missing pin is a GREEN control that must STAY erroring.

#[test]
fn provider_infeasible_principal_env_context_existence_accepted() {
    // FIX 1, existence pass (`check_one_field_path`), principal axis. Mirrors
    // `cedar_infeasible_principal_env_context_ref_accepted`. RED today: the
    // provider errors "`context.input.document` is not present … `Login`",
    // rejecting a policy Cedar accepts because (OAuthUser, Login) is infeasible.
    let src = format!(
        r#"permit ({S_PRIN_READ_LOGIN}) when guardrails {{ Strings::Matches(context.input.document, "x").matched == true }};"#
    );
    let r = validate_source(&src, SCHEMA_ENV, Some(&decls()));
    assert!(
        r.validation_passed(),
        "provider must skip the infeasible (OAuthUser, Login) env (existence), got:\n{r:?}"
    );
}

#[test]
fn provider_infeasible_principal_env_context_type_accepted() {
    // FIX 1, TYPE pass (`check_field_path_type`), principal axis. `value` is
    // String on Read (matches the string-declared arg) and Long on the
    // infeasible Login. Mirrors `cedar_infeasible_principal_env_divergent_type_accepted`.
    // RED today: the provider raises a type error against Login.
    let src = format!(
        r#"permit ({S_PRIN_READ_LOGIN}) when guardrails {{ Strings::Matches(context.input.value, "x").matched == true }};"#
    );
    let r = validate_source(&src, SCHEMA_ENV, Some(&decls()));
    assert!(
        r.validation_passed(),
        "provider must skip the infeasible env's Long typing (type pass), got:\n{r:?}"
    );
}

#[test]
fn provider_infeasible_resource_env_context_existence_accepted() {
    // FIX 1, existence pass, RESOURCE axis. Mirrors
    // `cedar_infeasible_resource_env_context_ref_accepted`. RED today: the
    // provider errors against the infeasible (Gateway, Admin) env.
    let src = format!(
        r#"permit ({S_RES_READ_ADMIN}) when guardrails {{ Strings::Matches(context.input.document, "x").matched == true }};"#
    );
    let r = validate_source(&src, SCHEMA_ENV, Some(&decls()));
    assert!(
        r.validation_passed(),
        "provider must skip the infeasible (Gateway, Admin) env via resource narrowing, got:\n{r:?}"
    );
}

#[test]
fn provider_infeasible_env_method_arg_accepted() {
    // FIX 1 must cover a field-path in a METHOD argument too (method args flow
    // through the same per-action `check_field_path_args` loop). `taggedWith`'s
    // arg `context.input.document` is absent from the infeasible Login. RED today.
    let src = format!(
        r#"permit ({S_PRIN_READ_LOGIN}) when guardrails {{ Doc::Check(context.input.user).taggedWith(context.input.document).ok == true }};"#
    );
    let r = validate_source(&src, SCHEMA_ENV, Some(&decls_method()));
    assert!(
        r.validation_passed(),
        "provider must skip the infeasible env for a METHOD-arg field-path, got:\n{r:?}"
    );
}

#[test]
fn provider_feasible_env_missing_context_field_still_rejected() {
    // GREEN CONTROL (guards against an over-broad fix): Admin is FEASIBLE under
    // `principal is OAuthUser` and has no `document`. This must STAY a provider
    // error after the gate is added — the gate skips only infeasible envs.
    // Mirrors `cedar_feasible_env_missing_context_field_rejected`.
    let src = format!(
        r#"permit ({S_PRIN_READ_ADMIN}) when guardrails {{ Strings::Matches(context.input.document, "x").matched == true }};"#
    );
    let r = validate_source(&src, SCHEMA_ENV, Some(&decls()));
    assert!(
        provider_error_contains(&r, "context.input.document")
            && provider_error_contains(&r, "not present")
            && provider_error_contains(&r, r#"App::Action::"Admin""#),
        "provider must still reject a field missing on the FEASIBLE Admin env, got:\n{r:?}"
    );
}

// ─── FIX 2: ambiguous (divergent) scope-attribute type ──────────────
// Cedar baselines.

#[test]
fn cedar_divergent_type_attr_used_as_string_rejected() {
    // `level` is Long on OAuthUser and String on ServiceBot; both admitted.
    // Comparing to a String literal is incompatible in the OAuthUser env, so
    // Cedar REJECTS — the behavior the provider TYPE pass must mimic.
    let src = r#"permit (principal, action == App::Action::"Read", resource) when { principal.level == "x" };"#;
    let r = validate_source(src, SCHEMA_AMBIG, None);
    assert!(
        cedar_error_contains(&r, "not compatible"),
        "Cedar must reject a divergent-typed attr used as a String, got:\n{r:?}"
    );
}

#[test]
fn cedar_divergent_type_attr_existence_and_reflexive_accepted() {
    // Cedar does NOT reject the mere reference: `has` and a use that is
    // type-valid in EVERY environment (reflexive `==`) both pass. This is why
    // the provider must treat an ambiguous attr as PRESENT (existence pass
    // accepts) and only reject it in the TYPE pass.
    let has = r#"permit (principal, action == App::Action::"Read", resource) when { principal has level };"#;
    let refl = r#"permit (principal, action == App::Action::"Read", resource) when { principal.level == principal.level };"#;
    assert!(
        validate_source(has, SCHEMA_AMBIG, None).validation_passed(),
        "Cedar accepts `principal has level` on a divergent-typed attr"
    );
    assert!(
        validate_source(refl, SCHEMA_AMBIG, None).validation_passed(),
        "Cedar accepts a reflexive use valid in every environment"
    );
}

// Provider pins for FIX 2 (RED today: the provider accepts these).

#[test]
fn provider_ambiguous_principal_attr_type_rejected() {
    // FIX 2, principal axis. `principal.level` is Long/String across the admitted
    // types → the string-declared arg cannot be satisfied in every environment.
    // The error must come from the TYPE pass (mention the attribute + a
    // "different type" diagnosis), NOT the existence pass ("not present"): the
    // attribute IS present, so mimicking Cedar means a type rejection.
    let src = r#"permit (principal, action == App::Action::"Read", resource) when guardrails { Strings::Matches(principal.level, "x").matched == true };"#;
    let r = validate_source(src, SCHEMA_AMBIG, Some(&decls()));
    assert!(
        provider_error_contains(&r, "principal.level")
            && provider_error_contains(&r, "different type")
            && !provider_error_contains(&r, "not present"),
        "provider must reject an ambiguous principal attr in the TYPE pass, got:\n{r:?}"
    );
}

#[test]
fn provider_ambiguous_resource_attr_type_rejected() {
    // FIX 2, resource axis. `resource.size` is Long/String across Gateway/Bucket.
    let src = r#"permit (principal, action == App::Action::"Read", resource) when guardrails { Strings::Matches(resource.size, "x").matched == true };"#;
    let r = validate_source(src, SCHEMA_AMBIG, Some(&decls()));
    assert!(
        provider_error_contains(&r, "resource.size")
            && provider_error_contains(&r, "different type")
            && !provider_error_contains(&r, "not present"),
        "provider must reject an ambiguous resource attr in the TYPE pass, got:\n{r:?}"
    );
}

#[test]
fn provider_resolved_multi_type_attr_accepted() {
    // GREEN CONTROL: `name` is String on BOTH admitted principal types, so the
    // path resolves to a SINGLE type (Resolved, not Ambiguous) and matches the
    // string arg. This distinguishes FIX 2 from a blanket "multi-type ⇒ reject":
    // only a DIVERGENT type is rejected, a consistent one is accepted.
    let src = r#"permit (principal, action == App::Action::"Read", resource) when guardrails { Strings::Matches(principal.name, "x").matched == true };"#;
    let r = validate_source(src, SCHEMA_AMBIG, Some(&decls()));
    assert!(
        r.validation_passed(),
        "a consistently-typed multi-type attr must be accepted, got:\n{r:?}"
    );
}

// ─── FIX 1/2 REGRESSION CONTROLS (green now, must STAY green) ────────
// These guard against an over-broad fix. The infeasible-env gate must skip a
// co-scoped action ONLY because narrowing makes it infeasible — never because
// several actions are listed, and never in a way that drops a FEASIBLE action's
// existence OR type check. And the ambiguous arm must not fire when narrowing
// has already resolved the attribute to a single type.

#[test]
fn cedar_unnarrowed_multi_action_missing_field_rejected() {
    // No narrowing ⇒ both (OAuthUser,Read) and (Bot,Login) are feasible. `document`
    // is absent from Login, so Cedar rejects. Baseline for the provider control.
    let src = r#"permit (principal, action in [App::Action::"Read", App::Action::"Login"], resource) when { context.input.document == "x" };"#;
    let r = validate_source(src, SCHEMA_ENV, None);
    assert!(
        cedar_error_contains(&r, "input.document")
            && cedar_error_contains(&r, r#"App::Action::"Login""#),
        "Cedar must reject a field missing on the feasible Login env, got:\n{r:?}"
    );
}

#[test]
fn provider_unnarrowed_multi_action_missing_field_still_rejected() {
    // EXISTENCE-pass reject guard, NO narrowing. Both actions feasible, so the
    // gate must NOT skip Login; `document` absent there stays an error. Ensures
    // the fix keys on infeasibility, not merely on a multi-action list.
    let src = r#"permit (principal, action in [App::Action::"Read", App::Action::"Login"], resource) when guardrails { Strings::Matches(context.input.document, "x").matched == true };"#;
    let r = validate_source(src, SCHEMA_ENV, Some(&decls()));
    assert!(
        provider_error_contains(&r, "context.input.document")
            && provider_error_contains(&r, "not present")
            && provider_error_contains(&r, r#"App::Action::"Login""#),
        "provider must still reject a field missing on the feasible Login env, got:\n{r:?}"
    );
}

#[test]
fn cedar_unnarrowed_multi_action_divergent_type_rejected() {
    // No narrowing ⇒ Login feasible; `value` is Long there, incompatible with a
    // String literal → Cedar rejects. Baseline for the provider TYPE control.
    let src = r#"permit (principal, action in [App::Action::"Read", App::Action::"Login"], resource) when { context.input.value == "x" };"#;
    let r = validate_source(src, SCHEMA_ENV, None);
    assert!(
        cedar_error_contains(&r, "not compatible"),
        "Cedar must reject the Long typing on the feasible Login env, got:\n{r:?}"
    );
}

#[test]
fn provider_unnarrowed_multi_action_wrong_type_still_rejected() {
    // TYPE-pass reject guard, NO narrowing (the complement of the existence
    // control, and of the feasible-but-missing pin which only exercises the
    // existence loop). Login is feasible and `value` is Long there → the type
    // check must still fire. This is the pin that catches an over-broad gate in
    // `check_field_path_type` specifically.
    let src = r#"permit (principal, action in [App::Action::"Read", App::Action::"Login"], resource) when guardrails { Strings::Matches(context.input.value, "x").matched == true };"#;
    let r = validate_source(src, SCHEMA_ENV, Some(&decls()));
    assert!(
        provider_error_contains(&r, "context.input.value")
            && provider_error_contains(&r, "has type `Long`")
            && provider_error_contains(&r, r#"App::Action::"Login""#),
        "provider must still type-reject on the feasible Login env, got:\n{r:?}"
    );
}

#[test]
fn cedar_narrowing_resolves_ambiguous_type_error() {
    // `principal is OAuthUser` collapses the divergent `level` to a single type
    // (Long), so Cedar's error is the ordinary type incompatibility, not an
    // "ambiguous" one. Baseline for the provider control below.
    let src = r#"permit (principal is App::OAuthUser, action == App::Action::"Read", resource) when { principal.level == "x" };"#;
    let r = validate_source(src, SCHEMA_AMBIG, None);
    assert!(
        cedar_error_contains(&r, "not compatible"),
        "Cedar must reject the narrowed Long `level` as a String, got:\n{r:?}"
    );
}

#[test]
fn provider_narrowing_resolves_ambiguous_to_plain_type_error() {
    // AMBIGUOUS-arm guard: with `principal is OAuthUser`, `level` resolves to a
    // SINGLE type (Long), so the provider must raise the ORDINARY scalar type
    // error ("has type `Long`"), NOT the ambiguous-divergence diagnosis. Ensures
    // the new ambiguous arm only fires on a genuinely divergent (un-narrowed)
    // attribute, and that narrowing still short-circuits to a Resolved type.
    let src = r#"permit (principal is App::OAuthUser, action == App::Action::"Read", resource) when guardrails { Strings::Matches(principal.level, "x").matched == true };"#;
    let r = validate_source(src, SCHEMA_AMBIG, Some(&decls()));
    assert!(
        provider_error_contains(&r, "principal.level")
            && provider_error_contains(&r, "has type `Long`")
            && !provider_error_contains(&r, "different type"),
        "narrowed ambiguous attr must give the ordinary type error, not the ambiguous one, got:\n{r:?}"
    );
}

#[test]
fn cedar_resource_narrowing_nonexcluding_missing_field_rejected() {
    // `resource is Gateway` keeps BOTH Read and Login feasible (both apply to
    // Gateway) — it excludes nothing. `document` is absent from Login, so Cedar
    // rejects. Baseline for the resource-axis provider control below.
    let src = r#"permit (principal, action in [App::Action::"Read", App::Action::"Login"], resource is App::Gateway) when { context.input.document == "x" };"#;
    let r = validate_source(src, SCHEMA_ENV, None);
    assert!(
        cedar_error_contains(&r, "input.document")
            && cedar_error_contains(&r, r#"App::Action::"Login""#),
        "Cedar must reject a field missing on the feasible (Gateway, Login) env, got:\n{r:?}"
    );
}

#[test]
fn provider_resource_narrowing_nonexcluding_missing_field_still_rejected() {
    // RESOURCE-axis narrowed-feasible reject guard — the symmetric complement of
    // the principal-axis `provider_feasible_env_missing_context_field_still_rejected`
    // (pin 9). `resource is Gateway` narrows on the resource axis but keeps Login
    // feasible; `document` absent there must STAY an error. Confirms the gate's
    // resource-axis feasibility check (`admits_any_env(Any, Gateway)` = true for
    // Login) does not drop a feasible action.
    let src = r#"permit (principal, action in [App::Action::"Read", App::Action::"Login"], resource is App::Gateway) when guardrails { Strings::Matches(context.input.document, "x").matched == true };"#;
    let r = validate_source(src, SCHEMA_ENV, Some(&decls()));
    assert!(
        provider_error_contains(&r, "context.input.document")
            && provider_error_contains(&r, "not present")
            && provider_error_contains(&r, r#"App::Action::"Login""#),
        "provider must still reject a field missing on the feasible (Gateway, Login) env, got:\n{r:?}"
    );
}

// ═══════════════════════════════════════════════════════════════════
// SET-LITERAL ARG ELEMENT VALIDATION + GROUP-MEMBER / UNDECLARED coverage.
// The existence pass recurses into a set-literal argument (`Fn([a, b])`); the
// TYPE pass must too, checking each element field-path against the declared
// set's ELEMENT type — and the feasibility gate must apply inside that
// recursion. These also close the previously-deferred set-wrapped and
// group-scope-reject axes.
// ═══════════════════════════════════════════════════════════════════

/// Group `Trade` whose members disagree on `document`: `Sell` has it, `Approve`
/// does not — so a field-path arg resolved over the group's members is rejected.
const SCHEMA_HIER_MIXED: &str = r#"
namespace App {
  type SellInput = { document: String };
  type ApproveInput = { user: String };
  entity Gateway;
  entity OAuthUser = { id: String };
  action "Trade";
  action "Sell" in [Action::"Trade"] appliesTo {
    principal: [OAuthUser], resource: [Gateway], context: { input: SellInput }
  };
  action "Approve" in [Action::"Trade"] appliesTo {
    principal: [OAuthUser], resource: [Gateway], context: { input: ApproveInput }
  };
}
"#;

#[test]
fn provider_set_literal_element_wrong_type_rejected() {
    // NB-1 (context axis): `Cat::SetS([context.input.n])` — element `n` is Long, the
    // declared arg is `set<string>`, so the element mismatches. The type pass must
    // recurse into the set (as the existence pass does) and reject it.
    let src = r#"permit (principal, action == App::Action::"Read", resource) when guardrails { Cat::SetS([context.input.n]).ok == true };"#;
    let r = validate_source(src, SCHEMA_CATEGORIES, Some(&decls_categories()));
    assert!(
        provider_error_contains(&r, "context.input.n")
            && provider_error_contains(&r, "has type `Long`"),
        "a Long element in a set<string> set-literal arg must be a type error, got:\n{r:?}"
    );
}

#[test]
fn provider_set_literal_element_scope_path_wrong_type_rejected() {
    // NB-1 (scope axis): a set-literal element that is a principal attribute of the
    // wrong type. `principal is OAuthUser` narrows so `level` (Long) resolves; as a
    // `set<string>` element it mismatches.
    let src = r#"permit (principal is App::OAuthUser, action == App::Action::"Read", resource) when guardrails { Cat::SetS([principal.level]).ok == true };"#;
    let r = validate_source(src, SCHEMA_SCOPE, Some(&decls_categories()));
    assert!(
        provider_error_contains(&r, "principal.level")
            && provider_error_contains(&r, "has type `Long`"),
        "a Long principal attr as a set<string> element must be a type error, got:\n{r:?}"
    );
}

#[test]
fn provider_set_literal_element_correct_type_accepted() {
    // GREEN control: a String element matches the `set<string>` element type — the
    // recursion must not over-reject.
    let src = r#"permit (principal, action == App::Action::"Read", resource) when guardrails { Cat::SetS([context.input.s]).ok == true };"#;
    let r = validate_source(src, SCHEMA_CATEGORIES, Some(&decls_categories()));
    assert!(
        r.validation_passed(),
        "a String set-literal element must be accepted, got:\n{r:?}"
    );
}

#[test]
fn provider_set_literal_missing_element_rejected() {
    // GREEN control (existence recursion already works): a missing element field-path
    // in a set-literal arg is rejected by the existence pass.
    let src = r#"permit (principal, action == App::Action::"Read", resource) when guardrails { Cat::SetS([context.input.bogus]).ok == true };"#;
    let r = validate_source(src, SCHEMA_CATEGORIES, Some(&decls_categories()));
    assert!(
        provider_error_contains(&r, "context.input.bogus")
            && provider_error_contains(&r, "not present"),
        "a missing set-literal element must be rejected (existence), got:\n{r:?}"
    );
}

#[test]
fn provider_set_literal_element_wrong_type_on_infeasible_action_accepted() {
    // The feasibility gate must apply INSIDE the set recursion (type pass): with
    // `principal is OAuthUser`, `Login` is infeasible; `value` is String on `Read`
    // (matches the `set<string>` element) and Long on the skipped `Login`, so the
    // set-literal arg is accepted. Guards that the new recursion still respects the
    // gate rather than type-checking an infeasible action's element.
    let src = r#"permit (principal is App::OAuthUser, action in [App::Action::"Read", App::Action::"Login"], resource) when guardrails { Cat::SetS([context.input.value]).ok == true };"#;
    let r = validate_source(src, SCHEMA_ENV, Some(&decls_categories()));
    assert!(
        r.validation_passed(),
        "a set-literal element wrong-typed only on an infeasible action must be accepted, got:\n{r:?}"
    );
}

#[test]
fn cedar_action_in_group_scope_field_absent_from_member_rejected() {
    // Baseline: `action in [Trade]` expands to the group's members; `document` is on
    // `Sell` but not `Approve`, so Cedar rejects (per-environment, conjunctive).
    let src = r#"permit (principal, action in [App::Action::"Trade"], resource) when { context.input.document == "x" };"#;
    let r = validate_source(src, SCHEMA_HIER_MIXED, None);
    assert!(
        cedar_error_contains(&r, "input.document")
            && cedar_error_contains(&r, r#"App::Action::"Approve""#),
        "Cedar must reject a field absent from a group member, got:\n{r:?}"
    );
}

#[test]
fn provider_action_in_group_scope_field_absent_from_member_rejected() {
    // Provider counterpart: the field-path arg is resolved against every expanded
    // group member; `Approve` lacks `document`, so it is rejected — matching Cedar.
    let src = r#"permit (principal, action in [App::Action::"Trade"], resource) when guardrails { Strings::Matches(context.input.document, "x").matched == true };"#;
    let r = validate_source(src, SCHEMA_HIER_MIXED, Some(&decls()));
    assert!(
        provider_error_contains(&r, "context.input.document")
            && provider_error_contains(&r, "not present")
            && provider_error_contains(&r, r#"App::Action::"Approve""#),
        "provider must reject a field absent from a group member, got:\n{r:?}"
    );
}

#[test]
fn provider_undeclared_provider_skips_field_path_checks() {
    // A field-path arg to an UNDECLARED provider must not crash or double-report: the
    // undeclared-provider error fires and the field-path checks are skipped (no
    // spurious "context.input.bogus is not present").
    let src = r#"permit (principal, action == App::Action::"Read", resource) when guardrails { Nope::Fn(context.input.bogus).ok == true };"#;
    let r = validate_source(src, SCHEMA_CATEGORIES, Some(&decls_categories()));
    assert!(
        !r.validation_passed() && !provider_error_contains(&r, "context.input.bogus"),
        "an undeclared provider must report only the declaration error, got:\n{r:?}"
    );
}

const SCHEMA_NESTSET: &str = r#"
namespace App {
  type ReadInput = { nss: Set<Set<String>>, nsl: Set<Set<Long>>, s: String };
  entity Gateway;
  entity OAuthUser = { id: String };
  action "Read" appliesTo {
    principal: [OAuthUser], resource: [Gateway], context: { input: ReadInput }
  };
}
"#;
fn decls_nestset() -> ProviderDeclarations {
    ProviderDeclarations::from_json(
        r#"{ "availableProviders": {
          "SS::Chk": {
            "argumentTypes": [{ "paramType": "set", "items": { "paramType": "set", "items": { "paramType": "string" } } }],
            "outputType": { "paramType": "record", "fields": { "ok": { "paramType": "bool" } }, "required": ["ok"] }
          }
        }}"#,
    ).expect("decls_nestset parse")
}

// ─── Nested set types (Set<Set<T>>) — Cedar allows them; the provider's element
// matching recurses (rich_type nests, param_matches_rich + check_arg_type recurse). ───

#[test]
fn cedar_nested_set_type_reflexive_accepted() {
    // Baseline: Cedar accepts a Set<Set<String>> attribute and a use valid in every
    // environment (reflexive). Confirms nested sets are a legal Cedar type.
    let src = r#"permit (principal, action == App::Action::"Read", resource) when { context.input.nss == context.input.nss };"#;
    let r = validate_source(src, SCHEMA_NESTSET, None);
    assert!(
        r.validation_passed(),
        "Cedar must accept a Set<Set<String>> attribute, got:\n{r:?}"
    );
}

#[test]
fn cedar_nested_set_type_mismatch_rejected() {
    // Cedar rejects Set<Set<String>> vs Set<Set<Long>> — the inner element type
    // differs. Baseline for the provider negative below.
    let src = r#"permit (principal, action == App::Action::"Read", resource) when { context.input.nss == context.input.nsl };"#;
    let r = validate_source(src, SCHEMA_NESTSET, None);
    assert!(
        cedar_error_contains(&r, "Set<Set<Long>>") && cedar_error_contains(&r, "not compatible"),
        "Cedar must reject Set<Set<String>> vs Set<Set<Long>>, got:\n{r:?}"
    );
}

#[test]
fn provider_nested_set_field_matching_accepted() {
    // A Set<Set<String>> field into a set<set<string>>-declared arg: the element
    // matching recurses through the nesting and accepts.
    let src = r#"permit (principal, action == App::Action::"Read", resource) when guardrails { SS::Chk(context.input.nss).ok == true };"#;
    let r = validate_source(src, SCHEMA_NESTSET, Some(&decls_nestset()));
    assert!(
        r.validation_passed(),
        "Set<Set<String>> must match a set<set<string>> arg, got:\n{r:?}"
    );
}

#[test]
fn provider_nested_set_field_inner_element_mismatch_rejected() {
    // A Set<Set<Long>> field into a set<set<string>>-declared arg: the INNER element
    // type mismatches, so the recursive match rejects it (Cedar rejects the analogous
    // comparison above).
    let src = r#"permit (principal, action == App::Action::"Read", resource) when guardrails { SS::Chk(context.input.nsl).ok == true };"#;
    let r = validate_source(src, SCHEMA_NESTSET, Some(&decls_nestset()));
    assert!(
        provider_error_contains(&r, "context.input.nsl")
            && provider_error_contains(&r, "Set<Set<Long>>"),
        "Set<Set<Long>> into a set<set<string>> arg must be rejected on the inner element, got:\n{r:?}"
    );
}

#[test]
fn provider_nested_set_literal_matching_accepted() {
    // A nested set LITERAL `[[s]]` (String element) into a set<set<string>> arg
    // exercises `check_arg_type`'s own recursion through nested `Arg::Set`; accepts.
    let src = r#"permit (principal, action == App::Action::"Read", resource) when guardrails { SS::Chk([[context.input.s]]).ok == true };"#;
    let r = validate_source(src, SCHEMA_CATEGORIES, Some(&decls_nestset()));
    assert!(
        r.validation_passed(),
        "nested set-literal [[String]] must be accepted, got:\n{r:?}"
    );
}

#[test]
fn provider_nested_set_literal_inner_element_mismatch_rejected() {
    // A nested set literal whose inner element is Long (`[[n]]`) into a
    // set<set<string>> arg: the recursion reaches the inner field-path and rejects
    // the Long element against the declared `string`.
    let src = r#"permit (principal, action == App::Action::"Read", resource) when guardrails { SS::Chk([[context.input.n]]).ok == true };"#;
    let r = validate_source(src, SCHEMA_CATEGORIES, Some(&decls_nestset()));
    assert!(
        provider_error_contains(&r, "context.input.n")
            && provider_error_contains(&r, "has type `Long`"),
        "nested set-literal [[Long]] must be rejected on the inner element, got:\n{r:?}"
    );
}

/// A multi-type principal whose divergent attribute types render to strings that
/// sort DIFFERENTLY from the `RichType` enum's declaration order (`Long`=`int`
/// before `Bool`=`boolean`, but `"boolean" < "int"` lexicographically). Pins the
/// `Ambiguous` diagnostic's type list to a stable STRING-sorted order.
const SCHEMA_AMBIG_BL: &str = r#"
namespace App {
  entity Gateway;
  entity OAuthUser  = { flag: Long };
  entity ServiceBot = { flag: Bool };
  action "Read" appliesTo {
    principal: [OAuthUser, ServiceBot], resource: [Gateway], context: { input: { doc: String } }
  };
}
"#;

#[test]
fn provider_ambiguous_type_list_is_string_sorted() {
    // `flag` is Long (renders `int`) on one type and Bool (`boolean`) on the other.
    // The ambiguous diagnostic must list them in STRING-sorted order
    // (`boolean`, `int`) — NOT the RichType enum-declaration order (`int`,
    // `boolean`). This keeps the message stable and matches the pre-refactor
    // (stringly-typed) rendering byte-for-byte.
    let src = r#"permit (principal, action == App::Action::"Read", resource) when guardrails { Strings::Matches(principal.flag, "x").matched == true };"#;
    let r = validate_source(src, SCHEMA_AMBIG_BL, Some(&decls()));
    assert!(
        provider_error_contains(&r, "(`boolean`, `int`)"),
        "ambiguous type list must be string-sorted (`boolean`, `int`), got:\n{r:?}"
    );
}
