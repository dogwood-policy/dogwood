//! Parser for the event-schema DSL: text → [`EventSchema`] AST.
//!
//! The grammar (`grammar.pest`) is walked by hand, mirroring the temporal
//! dialect's parser. Spans are byte ranges into the schema source. This
//! pass is schema-independent — it never consults an action schema; it
//! only checks the DSL's own well-formedness (selector binder references
//! must name the enclosing declaration's binder).

use pest::Parser;
use pest_derive::Parser;

use super::ast::{EventDecl, EventSchema, FieldSpec, PinRoot, PinValue, Selector, TypeExpr};
use crate::error::Span;
use crate::extension::temporal::ast::{Interval, TimeUnit};

#[derive(Parser)]
#[grammar = "event_schema/grammar.pest"]
struct EventSchemaParser;

type Pair<'i> = pest::iterators::Pair<'i, Rule>;

fn span_of(p: &Pair<'_>) -> Span {
    let s = p.as_span();
    Span::new(s.start(), s.end())
}

/// Parse event-schema DSL source into an [`EventSchema`].
pub fn parse_event_schema(src: &str) -> Result<EventSchema, String> {
    let src = src.strip_prefix('\u{FEFF}').unwrap_or(src);
    let mut pairs = EventSchemaParser::parse(Rule::schema_entry, src)
        .map_err(|e| format!("event schema parse error: {e}"))?;
    let entry = pairs.next().expect("schema_entry yields one pair");
    let mut max_window = None;
    let mut decls = Vec::new();
    for p in entry.into_inner() {
        match p.as_rule() {
            Rule::max_window_decl => max_window = Some(build_max_window(&p)?),
            Rule::event_decl => decls.push(build_event_decl(p)?),
            _ => {}
        }
    }
    Ok(EventSchema { max_window, decls })
}

/// Build the `max_window = <interval>` directive's [`Interval`]. A zero window
/// is rejected: it would forbid every temporal `within` clause, which is never
/// what an author intends (omit the directive to use the default cap instead).
fn build_max_window(pair: &Pair<'_>) -> Result<Interval, String> {
    let interval = pair
        .clone()
        .into_inner()
        .find(|p| p.as_rule() == Rule::interval)
        .expect("max_window_decl has an interval");
    let mut amount: i64 = 0;
    let mut unit = TimeUnit::Seconds;
    for p in interval.into_inner() {
        match p.as_rule() {
            Rule::integer => {
                amount = p
                    .as_str()
                    .parse()
                    .map_err(|_| format!("max_window amount `{}` is out of range", p.as_str()))?;
            }
            Rule::time_unit => {
                unit = TimeUnit::from_token(p.as_str())
                    .expect("time_unit rule yields a valid unit token");
            }
            _ => {}
        }
    }
    if amount == 0 {
        return Err(
            "max_window must be greater than zero; a zero window would forbid every \
             temporal `within` clause. Omit `max_window` to use the default cap, or \
             set a positive interval like `max_window = 24h`"
                .to_string(),
        );
    }
    Ok(Interval { amount, unit })
}

fn build_event_decl(pair: Pair<'_>) -> Result<EventDecl, String> {
    let span = span_of(&pair);
    let mut decision = false;
    let mut binder = String::new();
    let mut kind = String::new();
    let mut field_pairs: Option<Pair<'_>> = None;

    for p in pair.into_inner() {
        match p.as_rule() {
            Rule::decision_marker => decision = true,
            Rule::binder => binder = p.as_str().to_string(),
            Rule::event_kind => kind = p.as_str().to_string(),
            Rule::field_list => field_pairs = Some(p),
            _ => {}
        }
    }

    let mut fields = Vec::new();
    if let Some(list) = field_pairs {
        for f in list.into_inner() {
            if f.as_rule() == Rule::field {
                fields.push(build_field(f, &binder)?);
            }
        }
    }

    Ok(EventDecl {
        span,
        decision,
        binder,
        kind,
        fields,
    })
}

/// Build a field, checking that any selector's binder reference names the
/// enclosing declaration's `binder`.
fn build_field(pair: Pair<'_>, binder: &str) -> Result<FieldSpec, String> {
    let span = span_of(&pair);
    let inner = pair.into_inner().next().expect("field has one child");
    match inner.as_rule() {
        Rule::spread => {
            let mut selector = None;
            for p in inner.into_inner() {
                match p.as_rule() {
                    Rule::selector => selector = Some(build_selector(&p)),
                    Rule::binder_ref => check_binder_ref(&p, binder, "spread")?,
                    _ => {}
                }
            }
            Ok(FieldSpec::Spread {
                selector: selector.expect("spread has a selector"),
                span,
            })
        }
        Rule::named_field => {
            let mut name = String::new();
            let mut ty = None;
            let mut pinned = false;
            let mut pin: Option<PinValue> = None;
            for p in inner.into_inner() {
                match p.as_rule() {
                    Rule::pin_marker => pinned = true,
                    Rule::ident => name = p.as_str().to_string(),
                    Rule::type_expr => ty = Some(build_type_expr(p, binder)?),
                    Rule::pin_rhs => pin = Some(build_pin_rhs(&p)),
                    _ => {}
                }
            }
            let ty = ty.expect("named_field has a type");
            // `pin` and the `= <rhs>` clause must appear together.
            match (pinned, &pin) {
                (true, None) => {
                    return Err(format!(
                        "pinned field `{name}` is missing its pin value; write \
                         `pin {name}: <type> = context.<...>`"
                    ));
                }
                (false, Some(_)) => {
                    return Err(format!(
                        "field `{name}` has a `= context.<...>` value but is not marked \
                         `pin`; write `pin {name}: <type> = …`"
                    ));
                }
                _ => {}
            }
            // A pin may only sit on a leaf field — pinning a whole record
            // group is out of scope.
            if pin.is_some() && matches!(ty, TypeExpr::Record(_)) {
                return Err(format!(
                    "field `{name}` is a record group and cannot be pinned; pin a \
                     leaf field inside it instead"
                ));
            }
            Ok(FieldSpec::Named {
                name,
                ty,
                pin,
                span,
            })
        }
        other => unreachable!("unexpected field child: {other:?}"),
    }
}

/// Build a `pin_rhs` = `"=" ~ (pin_scope | pin_context)`. A `pin_scope`
/// (`principal` / `resource` ± attribute tail) yields a [`PinRoot::Scope`] path
/// with the root as its head segment; a `pin_context` (`context.<path>`) yields
/// a [`PinRoot::Context`] path without the leading `context`.
fn build_pin_rhs(pair: &Pair<'_>) -> PinValue {
    let span = span_of(pair);
    let inner = pair
        .clone()
        .into_inner()
        .find(|p| matches!(p.as_rule(), Rule::pin_scope | Rule::pin_context))
        .expect("pin_rhs has a pin_scope or pin_context");
    match inner.as_rule() {
        Rule::pin_scope => {
            // The `pin_scope_root` (`principal` / `resource`) is the head; the
            // trailing `ident`s are the attribute tail.
            let context_path: Vec<String> = inner
                .into_inner()
                .filter(|p| matches!(p.as_rule(), Rule::pin_scope_root | Rule::ident))
                .map(|p| p.as_str().to_string())
                .collect();
            PinValue {
                context_path,
                root: PinRoot::Scope,
                span,
            }
        }
        _ => {
            let context_path: Vec<String> = inner
                .into_inner()
                .filter(|p| p.as_rule() == Rule::ident)
                .map(|p| p.as_str().to_string())
                .collect();
            PinValue {
                context_path,
                root: PinRoot::Context,
                span,
            }
        }
    }
}

fn build_type_expr(pair: Pair<'_>, binder: &str) -> Result<TypeExpr, String> {
    let inner = pair.into_inner().next().expect("type_expr has one child");
    match inner.as_rule() {
        Rule::selector_call => {
            let mut selector = None;
            for p in inner.into_inner() {
                match p.as_rule() {
                    Rule::selector => selector = Some(build_selector(&p)),
                    Rule::binder_ref => check_binder_ref(&p, binder, "field type")?,
                    _ => {}
                }
            }
            Ok(TypeExpr::Selector(
                selector.expect("selector_call has a selector"),
            ))
        }
        Rule::record_type => {
            // A nested record: its members are field specs, built exactly
            // like a top-level body (so a spread inside is allowed).
            let mut fields = Vec::new();
            for f in inner.into_inner() {
                if f.as_rule() == Rule::field_list {
                    for entry in f.into_inner() {
                        if entry.as_rule() == Rule::field {
                            fields.push(build_field(entry, binder)?);
                        }
                    }
                }
            }
            Ok(TypeExpr::Record(fields))
        }
        Rule::concrete_type => {
            let path = inner
                .into_inner()
                .filter(|p| p.as_rule() == Rule::ident)
                .map(|p| p.as_str().to_string())
                .collect();
            Ok(TypeExpr::Concrete(path))
        }
        other => unreachable!("unexpected type_expr child: {other:?}"),
    }
}

fn build_selector(pair: &Pair<'_>) -> Selector {
    let inner = pair.clone().into_inner().next().expect("selector child");
    match inner.as_rule() {
        Rule::sel_inputs => Selector::Inputs,
        Rule::sel_outputs => Selector::Outputs,
        Rule::sel_principal_type => Selector::PrincipalType,
        Rule::sel_resource_type => Selector::ResourceType,
        other => unreachable!("unexpected selector child: {other:?}"),
    }
}

/// A selector's argument must name the declaration's binder — `inputs(A)`
/// in `event <A>::…`, not `inputs(B)`.
fn check_binder_ref(pair: &Pair<'_>, binder: &str, ctx: &str) -> Result<(), String> {
    let r = pair.as_str();
    if r != binder {
        return Err(format!(
            "in {ctx}: selector argument `{r}` does not name the declared \
             action binder `{binder}` (write `{binder}`)"
        ));
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    fn parse(src: &str) -> EventSchema {
        parse_event_schema(src).unwrap_or_else(|e| panic!("parse `{src}` failed: {e}"))
    }

    fn parse_err(src: &str) -> String {
        parse_event_schema(src)
            .err()
            .unwrap_or_else(|| panic!("expected parse error for `{src}`"))
    }

    /// The request/response convention from the design doc parses to the
    /// expected shape.
    #[test]
    fn request_response_schema_parses() {
        let s = parse(
            r#"
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
            "#,
        );
        assert_eq!(s.decls.len(), 2);

        let req = &s.decls[0];
        assert!(req.decision, "request is a decision kind");
        assert_eq!(req.binder, "A");
        assert_eq!(req.kind, "request");
        // ...inputs(A) + 3 named fields.
        assert_eq!(req.fields.len(), 4);
        assert!(matches!(
            req.fields[0],
            FieldSpec::Spread {
                selector: Selector::Inputs,
                ..
            }
        ));
        match &req.fields[1] {
            FieldSpec::Named { name, ty, .. } => {
                assert_eq!(name, "callerPrincipal");
                assert!(matches!(ty, TypeExpr::Selector(Selector::PrincipalType)));
            }
            other => panic!("expected named field, got {other:?}"),
        }
        match &req.fields[3] {
            FieldSpec::Named { name, ty, .. } => {
                assert_eq!(name, "requestId");
                match ty {
                    TypeExpr::Concrete(path) => assert_eq!(path, &["String".to_string()]),
                    other => panic!("expected concrete type, got {other:?}"),
                }
            }
            other => panic!("expected named field, got {other:?}"),
        }

        let res = &s.decls[1];
        assert!(!res.decision, "response is not a decision kind");
        assert_eq!(res.kind, "response");
        // ...inputs(A) + ...outputs(A) + 3 named.
        assert_eq!(res.fields.len(), 5);
        assert!(matches!(
            res.fields[1],
            FieldSpec::Spread {
                selector: Selector::Outputs,
                ..
            }
        ));
    }

    #[test]
    fn decision_marker_optional() {
        let s = parse("event <A>::audit { requestId: String }");
        assert!(!s.decls[0].decision);
        assert_eq!(s.decls[0].kind, "audit");
    }

    // ─── max_window directive ───────────────────────────────────────

    #[test]
    fn no_max_window_directive_is_none() {
        // Absent directive → `None`; derivation supplies the default cap.
        let s = parse("event <A>::request { requestId: String }");
        assert!(s.max_window.is_none());
    }

    #[test]
    fn max_window_directive_parses() {
        let s = parse(
            r#"
            max_window = 48h
            decision event <A>::request { requestId: String }
            "#,
        );
        let mw = s.max_window.expect("directive parsed");
        assert_eq!(mw.amount, 48);
        assert_eq!(mw.unit, TimeUnit::Hours);
        // The event decls still parse after the directive.
        assert_eq!(s.decls.len(), 1);
        assert_eq!(s.decls[0].kind, "request");
    }

    #[test]
    fn max_window_accepts_each_time_unit() {
        for (src, unit) in [
            ("max_window = 30s", TimeUnit::Seconds),
            ("max_window = 90m", TimeUnit::Minutes),
            ("max_window = 12h", TimeUnit::Hours),
            ("max_window = 7d", TimeUnit::Days),
        ] {
            let full = format!("{src}\nevent <A>::r {{ requestId: String }}");
            let s = parse(&full);
            assert_eq!(s.max_window.expect("parsed").unit, unit, "for `{src}`");
        }
    }

    #[test]
    fn zero_max_window_is_error() {
        let e = parse_err("max_window = 0h\nevent <A>::r { requestId: String }");
        assert!(e.contains("must be greater than zero"), "{e}");
    }

    #[test]
    fn max_window_must_precede_event_decls() {
        // The directive is only legal at the top of the file; placing it after
        // an event declaration is a parse error.
        let e = parse_err("event <A>::r { requestId: String }\nmax_window = 24h");
        assert!(e.contains("parse error"), "{e}");
    }

    #[test]
    fn max_window_missing_unit_is_error() {
        let e = parse_err("max_window = 24\nevent <A>::r { requestId: String }");
        assert!(e.contains("parse error"), "{e}");
    }

    #[test]
    fn empty_body_ok() {
        let s = parse("event <A>::ping {}");
        assert_eq!(s.decls[0].fields.len(), 0);
    }

    #[test]
    fn qualified_concrete_type_parses() {
        let s = parse("event <A>::r { who: Drupe::OAuthUser }");
        match &s.decls[0].fields[0] {
            FieldSpec::Named {
                ty: TypeExpr::Concrete(path),
                ..
            } => assert_eq!(path, &["Drupe".to_string(), "OAuthUser".to_string()]),
            other => panic!("expected qualified concrete type, got {other:?}"),
        }
    }

    #[test]
    fn record_type_parses_as_nested_fields() {
        // `name: { … }` parses to a `TypeExpr::Record` whose members are
        // themselves field specs.
        let s = parse("event <A>::r { meta: { a: String, b: Long } }");
        match &s.decls[0].fields[0] {
            FieldSpec::Named {
                ty: TypeExpr::Record(inner),
                name,
                ..
            } => {
                assert_eq!(name, "meta");
                assert_eq!(inner.len(), 2);
                assert!(matches!(&inner[0], FieldSpec::Named { name, .. } if name == "a"));
                assert!(matches!(&inner[1], FieldSpec::Named { name, .. } if name == "b"));
            }
            other => panic!("expected record type, got {other:?}"),
        }
    }

    #[test]
    fn deeply_nested_record_type_parses() {
        // A 3-level record nests `TypeExpr::Record` inside `TypeExpr::Record`.
        let s = parse("event <A>::r { a: { b: { c: String } } }");
        let level1 = match &s.decls[0].fields[0] {
            FieldSpec::Named {
                ty: TypeExpr::Record(inner),
                ..
            } => inner,
            other => panic!("expected level-1 record, got {other:?}"),
        };
        let level2 = match &level1[0] {
            FieldSpec::Named {
                ty: TypeExpr::Record(inner),
                ..
            } => inner,
            other => panic!("expected level-2 record, got {other:?}"),
        };
        assert!(
            matches!(&level2[0], FieldSpec::Named { name, ty: TypeExpr::Concrete(_), .. } if name == "c")
        );
    }

    #[test]
    fn record_type_may_contain_a_spread() {
        // `{ ...inputs(A) }` — a spread is a legal member of a nested record.
        let s = parse("event <A>::r { meta: { ...inputs(A) } }");
        match &s.decls[0].fields[0] {
            FieldSpec::Named {
                ty: TypeExpr::Record(inner),
                ..
            } => assert!(matches!(
                &inner[0],
                FieldSpec::Spread {
                    selector: Selector::Inputs,
                    ..
                }
            )),
            other => panic!("expected record with spread, got {other:?}"),
        }
    }

    #[test]
    fn record_type_binder_check_reaches_nested_spread() {
        // A spread inside a nested record still has its binder checked
        // against the declaration's binder.
        let e = parse_err("event <A>::r { meta: { ...inputs(B) } }");
        assert!(
            e.contains("does not name the declared action binder `A`"),
            "{e}"
        );
    }

    #[test]
    fn unknown_selector_is_parse_error() {
        // `tags` is not one of the four selectors.
        let e = parse_err("event <A>::r { ...tags(A) }");
        assert!(e.contains("parse error"), "{e}");
    }

    #[test]
    fn selector_binder_must_match_declaration_binder() {
        // Declared `<A>` but the spread reads `inputs(B)`.
        let e = parse_err("event <A>::r { ...inputs(B) }");
        assert!(
            e.contains("does not name the declared action binder `A`"),
            "{e}"
        );
    }

    #[test]
    fn selector_binder_mismatch_in_field_type() {
        let e = parse_err("event <A>::r { p: principalType(B) }");
        assert!(
            e.contains("does not name the declared action binder `A`"),
            "{e}"
        );
    }

    #[test]
    fn malformed_missing_braces_errors() {
        let e = parse_err("event <A>::r");
        assert!(e.contains("parse error"), "{e}");
    }

    #[test]
    fn missing_binder_angle_brackets_errors() {
        let e = parse_err("event A::r { }");
        assert!(e.contains("parse error"), "{e}");
    }

    // ─── Pinned fields ──────────────────────────────────────────────

    #[test]
    fn pinned_top_level_field_parses() {
        // A scope pin: `= principal` records a `PinRoot::Scope` path headed by
        // the `principal` root (Cedar's request scope, not a context field).
        let s = parse("event <A>::r { pin callerPrincipal: principalType(A) = principal }");
        match &s.decls[0].fields[0] {
            FieldSpec::Named { name, pin, .. } => {
                assert_eq!(name, "callerPrincipal");
                let pin = pin.as_ref().expect("field is pinned");
                assert_eq!(pin.context_path, vec!["principal".to_string()]);
                assert_eq!(pin.root, PinRoot::Scope);
            }
            other => panic!("expected pinned named field, got {other:?}"),
        }
    }

    #[test]
    fn pin_rhs_keeps_full_context_path() {
        // A context pin: `= context.__drupe.session_id` records a
        // `PinRoot::Context` path (leading `context` stripped).
        let s =
            parse("event <A>::r { pin __drupe_sessionid: String = context.__drupe.session_id }");
        match &s.decls[0].fields[0] {
            FieldSpec::Named { pin, .. } => {
                let pin = pin.as_ref().expect("pinned");
                assert_eq!(
                    pin.context_path,
                    vec!["__drupe".to_string(), "session_id".to_string()]
                );
                assert_eq!(pin.root, PinRoot::Context);
            }
            other => panic!("expected pinned field, got {other:?}"),
        }
    }

    #[test]
    fn pin_rhs_scope_with_attribute_tail() {
        // A scope pin may carry an attribute tail: `= principal.dept` records a
        // `PinRoot::Scope` path `["principal", "dept"]`.
        let s = parse("event <A>::r { pin dept: String = principal.dept }");
        match &s.decls[0].fields[0] {
            FieldSpec::Named { pin, .. } => {
                let pin = pin.as_ref().expect("pinned");
                assert_eq!(
                    pin.context_path,
                    vec!["principal".to_string(), "dept".to_string()]
                );
                assert_eq!(pin.root, PinRoot::Scope);
            }
            other => panic!("expected pinned field, got {other:?}"),
        }
    }

    #[test]
    fn unpinned_field_has_no_pin() {
        let s = parse("event <A>::r { requestId: String }");
        match &s.decls[0].fields[0] {
            FieldSpec::Named { pin, .. } => assert!(pin.is_none(), "unpinned"),
            other => panic!("expected named field, got {other:?}"),
        }
    }

    #[test]
    fn pin_may_sit_on_a_leaf_inside_a_record() {
        // A pin on a nested leaf: the record itself is unpinned; its member
        // `session_id` is pinned.
        let s = parse(
            "event <A>::r { __drupe: { pin session_id: String = context.__drupe.session_id } }",
        );
        let inner = match &s.decls[0].fields[0] {
            FieldSpec::Named {
                ty: TypeExpr::Record(inner),
                pin,
                ..
            } => {
                assert!(pin.is_none(), "the record group itself is not pinned");
                inner
            }
            other => panic!("expected record field, got {other:?}"),
        };
        match &inner[0] {
            FieldSpec::Named { name, pin, .. } => {
                assert_eq!(name, "session_id");
                assert!(pin.is_some(), "nested leaf is pinned");
            }
            other => panic!("expected pinned nested leaf, got {other:?}"),
        }
    }

    #[test]
    fn pin_without_value_is_error() {
        let e = parse_err("event <A>::r { pin foo: String }");
        assert!(e.contains("missing its pin value"), "{e}");
    }

    #[test]
    fn value_without_pin_is_error() {
        let e = parse_err("event <A>::r { foo: String = context.foo }");
        assert!(e.contains("not marked"), "{e}");
    }

    #[test]
    fn pinning_a_record_group_is_error() {
        let e = parse_err("event <A>::r { pin meta: { x: String } = context.meta }");
        assert!(e.contains("record group and cannot be pinned"), "{e}");
    }

    #[test]
    fn field_may_be_named_pin() {
        // `pin` is a *contextual* keyword — the pin prefix only when a field
        // declaration follows it. `pin: String` has no following `ident:`, so
        // `pin` is an ordinary field name.
        let s = parse("event <A>::r { pin: String }");
        match &s.decls[0].fields[0] {
            FieldSpec::Named { name, pin, .. } => {
                assert_eq!(name, "pin");
                assert!(pin.is_none(), "not a pinned field");
            }
            other => panic!("expected named field, got {other:?}"),
        }
    }

    #[test]
    fn a_field_named_pin_can_itself_be_pinned() {
        // The contextual-keyword edge case: `pin pin: T = …` is a *pinned
        // field whose name is `pin`` — first `pin` is the prefix, second is
        // the name.
        let s = parse("event <A>::r { pin pin: String = context.pin }");
        match &s.decls[0].fields[0] {
            FieldSpec::Named { name, pin, .. } => {
                assert_eq!(name, "pin");
                let pin = pin.as_ref().expect("pinned");
                assert_eq!(pin.context_path, vec!["pin".to_string()]);
            }
            other => panic!("expected pinned field named pin, got {other:?}"),
        }
    }
}
