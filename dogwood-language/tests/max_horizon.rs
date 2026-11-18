//! The event schema's `max_horizon`: a cap on how far back a temporal leaf can look in total.
//!
//! `max_window` caps each `within` window on its own, but nested operators add their windows:
//! `formerly within 24h (formerly within 24h φ)` passes a 24h window cap and looks back 48h. A
//! leaf's horizon is the largest sum of the windows along one chain of `formerly`, `previous`,
//! and `since` (the Lean specification's `Formula.horizon`), and validation rejects a leaf whose
//! horizon exceeds the event schema's `max_horizon`. Events older than `max_horizon` then never
//! matter to any policy the service accepts, so a service can fix its event retention ahead of
//! time.
//!
//! The two directives resolve as follows (`H` the horizon cap, `W` the window cap):
//!
//! | declared            | `H`          | `W`          |
//! |---------------------|--------------|--------------|
//! | neither             | none         | 24h          |
//! | `max_horizon` only  | `max_horizon`| `max_horizon`|
//! | `max_window` only   | none         | `max_window` |
//! | both                | `max_horizon`| `max_window` |
//!
//! Without a declared `max_horizon` there is no horizon cap, so a schema or policy that validated
//! before `max_horizon` existed validates unchanged. A schema that declares both, with `W` longer
//! than `H`, is an error: no window could be used up to its cap.

use dogwood_language::{
    Error, LoweredPolicySet, PolicySchema, ServiceSchema, ValidationError, ValidationResult,
    Validator,
};

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

const EVENTS: &str = r#"
decision event <A>::request {
    ...inputs(A),
    callerPrincipal: principalType(A),
    callerResource:  resourceType(A),
    requestId:       String,
}
"#;

/// The event schema with the given directives in front of the declarations.
fn event_schema(directives: &str) -> String {
    format!("{directives}\n{EVENTS}")
}

fn service(directives: &str) -> Result<ServiceSchema, Error> {
    ServiceSchema::builder()
        .event_schema_str(&event_schema(directives))
        .build()
}

fn validate(directives: &str, policy: &str) -> ValidationResult {
    let service = service(directives).expect("service schema builds");
    let policy_schema = PolicySchema::from_cedarschema_str(SCHEMA).expect("policy schema builds");
    let policies =
        LoweredPolicySet::from_str(policy, &service, &policy_schema).expect("policy lowers");
    Validator::new().validate(&policies)
}

fn temporal_errors(result: &ValidationResult) -> Vec<String> {
    result
        .validation_errors()
        .filter_map(|e| match e {
            ValidationError::Extension {
                code: "temporal",
                message,
                ..
            } => Some(message.clone()),
            _ => None,
        })
        .collect()
}

fn horizon_errors(result: &ValidationResult) -> Vec<String> {
    temporal_errors(result)
        .into_iter()
        .filter(|m| m.contains("max_horizon"))
        .collect()
}

fn window_errors(result: &ValidationResult) -> Vec<String> {
    temporal_errors(result)
        .into_iter()
        .filter(|m| m.contains("exceeds the maximum allowed window"))
        .collect()
}

/// `n` nested `formerly within <window>` around a login predicate.
fn nested(window: &str, n: usize) -> String {
    let mut body =
        r#"App::Action::"Login"::request{input.user: context.input.user}"#.to_string();
    for _ in 0..n {
        body = format!("formerly within {window} ({body})");
    }
    format!(
        r#"permit (principal, action == App::Action::"Read", resource)
when temporal {{ {body} }};"#
    )
}

fn schema_error(directives: &str) -> String {
    match service(directives) {
        Err(Error::EventSchema(m)) => m,
        Err(e) => panic!("expected an event-schema error for {directives:?}, got {e:?}"),
        Ok(_) => panic!("expected an event-schema error for {directives:?}, got Ok"),
    }
}

// ── Parsing and resolving the directives ────────────────────────────────

#[test]
fn max_horizon_directive_parses() {
    assert!(service("max_horizon = 48h").is_ok());
    assert!(service("max_window = 1h\nmax_horizon = 48h").is_ok());
    assert!(service("max_horizon = 48h\nmax_window = 1h").is_ok());
}

#[test]
fn zero_max_horizon_is_an_error() {
    let m = schema_error("max_horizon = 0h");
    assert!(m.contains("max_horizon"), "{m}");
}

#[test]
fn duplicate_directive_is_an_error() {
    let m = schema_error("max_horizon = 24h\nmax_horizon = 48h");
    assert!(m.contains("max_horizon"), "{m}");
    let m = schema_error("max_window = 1h\nmax_window = 2h");
    assert!(m.contains("max_window"), "{m}");
}

#[test]
fn max_horizon_must_precede_event_decls() {
    let src = format!("{EVENTS}\nmax_horizon = 24h");
    let err = ServiceSchema::builder().event_schema_str(&src).build();
    assert!(matches!(err, Err(Error::EventSchema(_))), "{err:?}");
}

#[test]
fn window_larger_than_horizon_is_an_error() {
    let m = schema_error("max_window = 48h\nmax_horizon = 24h");
    assert!(m.contains("max_window") && m.contains("max_horizon"), "{m}");
}

#[test]
fn window_alone_is_fine_at_any_length() {
    // Without `max_horizon` there is no horizon cap for the window to exceed.
    assert!(service("max_window = 30d").is_ok());
    assert!(service("max_window = 8760h").is_ok());
    assert!(service("max_window = 24h").is_ok());
    assert!(service("max_window = 1h").is_ok());
}

#[test]
fn equal_window_and_horizon_is_fine() {
    assert!(service("max_window = 30d\nmax_horizon = 30d").is_ok());
}

// ── The horizon check ───────────────────────────────────────────────────

#[test]
fn undeclared_horizon_is_unbounded() {
    // Each window is within the 24h window cap; together they look back 48h, or 240h. Without a
    // declared `max_horizon` that is fine, as it was before `max_horizon` existed.
    let r = validate("", &nested("24h", 2));
    assert!(r.validation_passed_without_warnings(), "{r:?}");
    let r = validate("", &nested("24h", 10));
    assert!(r.validation_passed_without_warnings(), "{r:?}");
}

#[test]
fn declared_horizon_rejects_nesting_past_it() {
    let r = validate("max_window = 24h\nmax_horizon = 24h", &nested("24h", 2));
    assert!(window_errors(&r).is_empty(), "{r:?}");
    assert_eq!(horizon_errors(&r).len(), 1, "{r:?}");
    let r = validate("max_horizon = 24h", &nested("12h", 2));
    assert!(r.validation_passed(), "{r:?}");
}

#[test]
fn raised_horizon_admits_nesting() {
    let r = validate("max_horizon = 48h", &nested("24h", 2));
    assert!(r.validation_passed(), "{r:?}");
}

#[test]
fn horizon_alone_also_sets_the_window_cap() {
    // `max_horizon = 48h` alone resolves the window cap to 48h: one 48h window is fine.
    let r = validate("max_horizon = 48h", &nested("48h", 1));
    assert!(r.validation_passed(), "{r:?}");
    // And a lower horizon lowers the window cap with it.
    let r = validate("max_horizon = 1h", &nested("2h", 1));
    assert_eq!(window_errors(&r).len(), 1, "{r:?}");
}

#[test]
fn window_alone_leaves_the_horizon_unbounded() {
    // `max_window = 3h` alone: 3h windows, nested past 24h (the parser bounds the depth, not
    // the validator).
    let r = validate("max_window = 3h", &nested("3h", 10));
    assert!(r.validation_passed_without_warnings(), "{r:?}");
    let r = validate("max_window = 3h", &nested("4h", 1));
    assert_eq!(window_errors(&r).len(), 1, "{r:?}");
}

#[test]
fn window_and_horizon_both_declared() {
    let r = validate("max_window = 4h\nmax_horizon = 24h", &nested("4h", 6));
    assert!(r.validation_passed(), "{r:?}");
    let r = validate("max_window = 4h\nmax_horizon = 24h", &nested("4h", 7));
    assert_eq!(horizon_errors(&r).len(), 1, "{r:?}");
    assert!(window_errors(&r).is_empty(), "{r:?}");
}

#[test]
fn horizon_is_inclusive() {
    let r = validate("max_horizon = 2h", &nested("1h", 2));
    assert!(r.validation_passed(), "{r:?}");
    let r = validate("max_horizon = 2h", &nested("1h", 3));
    assert_eq!(horizon_errors(&r).len(), 1, "{r:?}");
}

#[test]
fn horizon_sums_along_the_deepest_chain_not_across_conjuncts() {
    // Under a declared 24h horizon.
    // Two 20h windows side by side look back 20h, not 40h.
    let policy = r#"permit (principal, action == App::Action::"Read", resource)
when temporal {
  (formerly within 20h App::Action::"Login"::request{input.user: context.input.user})
  && (formerly within 20h App::Action::"Login"::request{input.server: "s"})
};"#;
    let r = validate("max_horizon = 24h", policy);
    assert!(horizon_errors(&r).is_empty(), "{r:?}");
}

#[test]
fn since_adds_its_window_to_the_deeper_side() {
    // `since within 12h` with a 13h `formerly` on its right looks back 25h.
    let policy = r#"permit (principal, action == App::Action::"Read", resource)
when temporal {
  !App::Action::"Login"::request{input.user: context.input.user}
    since within 12h
  (formerly within 13h App::Action::"Login"::request{input.user: context.input.user})
};"#;
    let r = validate("max_horizon = 24h", policy);
    assert_eq!(horizon_errors(&r).len(), 1, "{r:?}");
    let r = validate("max_horizon = 25h", policy);
    assert!(horizon_errors(&r).is_empty(), "{r:?}");
}

#[test]
fn previous_counts_toward_the_horizon() {
    let policy = r#"permit (principal, action == App::Action::"Read", resource)
when temporal {
  previous within 20h (formerly within 5h App::Action::"Login"::request{input.user: context.input.user})
};"#;
    let r = validate("max_horizon = 24h", policy);
    assert_eq!(horizon_errors(&r).len(), 1, "{r:?}");
}

#[test]
fn horizon_reaches_into_aggregation_bodies() {
    let policy = r#"permit (principal, action == App::Action::"Read", resource)
when temporal {
  exists (n: Long). (
    (count for (t: Timepoint). where (
        formerly within 20h (formerly within 5h
          (App::Action::"Login"::request{input.user: context.input.user} && tp(t)))
    )) == n && n > 0
  )
};"#;
    let r = validate("max_horizon = 24h", policy);
    assert_eq!(horizon_errors(&r).len(), 1, "{r:?}");
}

#[test]
fn horizon_error_names_the_horizon_and_the_cap() {
    let r = validate("max_horizon = 24h", &nested("24h", 2));
    let errs = horizon_errors(&r);
    assert_eq!(errs.len(), 1, "{r:?}");
    assert!(errs[0].contains("48h") || errs[0].contains("172800"), "{}", errs[0]);
    assert!(errs[0].contains("24h"), "{}", errs[0]);
}

#[test]
fn horizon_is_summed_exactly_past_64_bits() {
    // Two windows of 5e18 seconds each fit the window cap, but together look back 1e19 seconds,
    // past `i64::MAX`; a saturating sum would compare equal to the cap and wrongly pass.
    let r = validate(
        "max_horizon = 9223372036854775807s",
        &nested("5000000000000000000s", 2),
    );
    assert!(window_errors(&r).is_empty(), "{r:?}");
    let errs = horizon_errors(&r);
    assert_eq!(errs.len(), 1, "{r:?}");
    assert!(errs[0].contains("10000000000000000000s"), "{}", errs[0]);
}

// ── Further directive and message cases ──────────────────────────────

#[test]
fn overflowing_directive_is_an_error() {
    let m = schema_error("max_horizon = 9223372036854775807h");
    assert!(m.contains("max_horizon") && m.contains("too large"), "{m}");
    let m = schema_error("max_window = 9223372036854775807h");
    assert!(m.contains("max_window") && m.contains("too large"), "{m}");
}

#[test]
fn zero_directive_messages_say_what_omitting_them_does() {
    let m = schema_error("max_horizon = 0h");
    assert!(m.contains("leave the horizon uncapped"), "{m}");
    assert!(!m.contains("default cap"), "{m}");
    // The `max_window` message is unchanged from before `max_horizon` existed.
    assert_eq!(
        schema_error("max_window = 0h"),
        "max_window must be greater than zero; a zero window would forbid every temporal \
         `within` clause. Omit `max_window` to use the default cap, or set a positive interval \
         like `max_window = 24h`"
    );
}

/// The exact message for a window cap longer than the horizon cap. The Lean frontend port
/// (`Dogwood.Frontend.Derive.limits`) states the same text, and
/// `Dogwood.Examples.MaxHorizon.limits_message` pins it there: change both together.
#[test]
fn window_above_horizon_message_is_exact() {
    assert_eq!(
        schema_error("max_window = 48h\nmax_horizon = 24h"),
        "`max_window = 48h` is longer than `max_horizon = 24h`; a temporal condition can never \
         look back further than `max_horizon`, so no window could use its full cap. Set \
         `max_horizon` to at least `48h`, or lower `max_window`"
    );
}

#[test]
fn horizon_sees_through_negation() {
    let policy = r#"permit (principal, action == App::Action::"Read", resource)
when temporal {
  !(formerly within 24h (formerly within 1h App::Action::"Login"::request{input.user: context.input.user}))
};"#;
    let r = validate("max_horizon = 24h", policy);
    assert_eq!(horizon_errors(&r).len(), 1, "{r:?}");
    let r = validate("max_horizon = 25h", policy);
    assert!(horizon_errors(&r).is_empty(), "{r:?}");
}

#[test]
fn non_positive_window_in_a_nest_counts_as_zero() {
    // The zero window is its own error; it adds nothing to the horizon.
    let policy = r#"permit (principal, action == App::Action::"Read", resource)
when temporal {
  formerly within 24h (formerly within 0h App::Action::"Login"::request{input.user: context.input.user})
};"#;
    let r = validate("max_horizon = 24h", policy);
    assert!(horizon_errors(&r).is_empty(), "{r:?}");
    assert!(
        temporal_errors(&r).iter().any(|m| m.contains("must be positive")),
        "{r:?}"
    );
}

#[cfg(feature = "experimental-arithmetic")]
#[test]
fn horizon_reaches_aggregates_inside_arithmetic() {
    let policy = r#"permit (principal, action == App::Action::"Read", resource)
when temporal {
  ((count for (t: Timepoint). where (formerly within 1h (App::Action::"Login"::request{input.user: context.input.user} && tp(t))))
   + (count for (t: Timepoint). where (formerly within 20h (formerly within 5h
       (App::Action::"Login"::request{input.user: context.input.user} && tp(t)))))) > 0
};"#;
    let r = validate("max_horizon = 24h", policy);
    assert_eq!(horizon_errors(&r).len(), 1, "{r:?}");
    let r = validate("max_horizon = 25h", policy);
    assert!(horizon_errors(&r).is_empty(), "{r:?}");
}
