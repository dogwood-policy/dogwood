//! Feed-forward (re-augment) robustness.
//!
//! Dogwood exposes a *supported* incremental-lowering workflow: a consumer
//! lowers a policy, takes the augmented schema back out with
//! [`LoweredPolicySet::cedar_schema_str`], and feeds that text in as the
//! action schema for the next lowering (see the `cedar_schema_str` docs on
//! "incremental / feed-forward lowering"). Downstream packages build pipelines
//! on top of this loop, so the property that matters is:
//!
//! > **A schema Dogwood emits must be a schema Dogwood can re-ingest — every
//! > time, for any context shape, iteration after iteration.**
//!
//! That property was under-tested. Only one happy-path case re-lowered an
//! augmented schema (inline context, primitives only, one pass), so the
//! `__cedar` reserved-namespace bug — which only surfaces when augmentation
//! pins a builtin to Cedar's reserved `__cedar::` spelling *inside* an
//! `input`/`output` record (which happens when a **reference-style** context
//! is inlined) and that schema is then RE-derived — slipped through.
//!
//! This module locks the property down as a matrix: a shared N-pass driver
//! ([`feed_forward`]) run over every context shape a generated schema can
//! carry — primitives, each extension type, sets (including sets of
//! extensions), nested sub-records, and a chained common-type reference —
//! plus a provider-augmentation variant and a schema-stability (idempotence)
//! check. Every fixture uses a **reference-style** context on purpose: that is
//! the shape that forces augmentation to inline + type-resolve and thus pins
//! nested builtins to `__cedar::` (an inline context leaves the reserved
//! spelling only on the flat hoisted field, which the deriver skips, so it
//! never reproduces the bug). Each matrix case was confirmed to FAIL on the
//! pre-fix code, so they are genuine regression guards, not just smoke tests.
//!
//! Surviving re-ingestion is necessary but not sufficient: a schema that
//! re-ingests yet silently drops or mistypes a field would still *validate*
//! while *deciding wrong*. The verdict tests at the bottom close that gap —
//! they replay content-sensitive events (a decision that flips on an input
//! value / on prior history) and assert the re-lowered policy returns the
//! **same** verdict stream as the original, so a field lost across the
//! feed-forward round-trip would surface as a changed decision, not just a
//! parse error.
//!
//! The namespace here is deliberately `Svc`, not tied to any particular
//! deployment: the workflow is not tied to any particular schema template.

use dogwood_language::{
    Authorizer, Decision, Event, LoweredPolicySet, ParsedPolicySet, PolicySchema,
    ProviderDeclarations, ServiceSchema, Validator, Value,
};

/// The number of feed-forward iterations each matrix case runs. The bug this
/// module guards only bites on RE-derivation of an already-augmented schema,
/// so a single pass proves nothing — the failure first appears at pass 1 (the
/// second iteration). Several passes also surface any accretion / drift bug
/// that compounds across rounds.
const PASSES: usize = 4;

/// Drive the augment → serialize → re-ingest loop `passes` times against a
/// default service schema, returning the final augmented schema text.
///
/// Each pass gets a distinct distincter (`p0`, `p1`, …) so the field hoisted
/// this pass cannot collide with fields carried forward from earlier passes —
/// exactly how a real incremental consumer keeps independently-lowered
/// sub-policies apart. Any failure is surfaced with the offending pass index
/// so a regression points straight at "first pass that could not re-ingest".
fn feed_forward(schema0: &str, policy: &str, passes: usize) -> Result<String, String> {
    feed_forward_with_service(schema0, policy, passes, &ServiceSchema::defaults())
}

/// [`feed_forward`] against a caller-supplied service schema (so the provider
/// case can wire in its `providers.json`).
fn feed_forward_with_service(
    schema0: &str,
    policy: &str,
    passes: usize,
    service: &ServiceSchema,
) -> Result<String, String> {
    let mut current = schema0.to_string();
    for pass in 0..passes {
        let schema = PolicySchema::from_cedarschema_str(&current)
            .map_err(|e| format!("pass {pass}: augmented schema re-ingests: {e:?}"))?;
        let lowered = ParsedPolicySet::parse(policy, service)
            .map_err(|e| format!("pass {pass}: policy parses: {e:?}"))?
            .lower_with_distincter(&schema, &format!("p{pass}"))
            .map_err(|e| format!("pass {pass}: lowers against fed-forward schema: {e:?}"))?;
        if !Validator::new().validate(&lowered).validation_passed() {
            return Err(format!("pass {pass}: policy failed to validate"));
        }
        current = lowered
            .cedar_schema_str()
            .map_err(|e| format!("pass {pass}: augmented schema serializes: {e:?}"))?;
    }
    Ok(current)
}

/// Assert that the fed-forward loop survives `PASSES` iterations, and that the
/// augmented schema really carried a `__cedar::`-qualified builtin *inside* a
/// descended record — otherwise the case is no longer exercising the bug it
/// was written to guard (the flat hoisted field is always `__cedar::Bool`,
/// which the deriver skips, so we look for the primitive/extension spellings
/// that can only come from an inlined `input`/`output`/`system` record).
fn assert_survives_and_still_bites(schema0: &str, policy: &str) {
    let final_schema =
        feed_forward(schema0, policy, PASSES).unwrap_or_else(|e| panic!("feed-forward: {e}"));
    let bites = [
        "__cedar::String",
        "__cedar::Long",
        "__cedar::decimal",
        "__cedar::datetime",
    ]
    .iter()
    .any(|needle| final_schema.contains(needle));
    assert!(
        bites,
        "the augmented schema never carried a nested `__cedar::`-qualified \
         builtin, so this case no longer exercises the reserved-namespace bug; \
         final augmented schema was:\n{final_schema}"
    );
}

/// The temporal policy every matrix case lowers. `formerly within` hoists one
/// field, which forces the reference context to be inlined (and thus its
/// nested builtins to be pinned to `__cedar::`). It pins `input.symbol`, a
/// field present in every fixture below.
const TEMPORAL_POLICY: &str = r#"
permit ( principal, action == Svc::Action::"Op", resource )
when temporal {
    formerly within 1h Svc::Action::"Op"::request{
        input.symbol: context.input.symbol
    }
};
"#;

// ─── Matrix: one const per context shape a generated schema can carry ────────
//
// Every fixture uses a **reference-style** context (`context: Ctx`) — the
// shape that forces augmentation to inline + type-resolve, pinning the nested
// builtins to `__cedar::`. Each also has a realistic entity hierarchy and an
// `input`/`output`/`system` split, mirroring MCP-generated schemas.

/// Primitives + all three common extension types, split across input/output/system.
const SHAPE_EXTENSIONS: &str = r#"
namespace Svc {
  type OpInput  = { symbol: String, qty: Long, live: Bool };
  type OpOutput = { price: decimal };
  type SystemContext = { now: datetime, caller: ipaddr };
  type Ctx = { input: OpInput, output?: OpOutput, system: SystemContext };
  entity Gateway;
  entity Desk;
  entity Trader in [Desk] = { id: String } tags String;
  action "Trade";
  action "Op" in [Action::"Trade"] appliesTo {
    principal: [Trader], resource: [Gateway], context: Ctx
  };
}
"#;

/// A `Set<String>` field — a set is always a leaf, and its element carries the
/// reserved spelling after resolution (`Set<__cedar::String>`).
const SHAPE_SET_OF_PRIMITIVE: &str = r#"
namespace Svc {
  type OpInput = { symbol: String, tags: Set<String> };
  type Ctx = { input: OpInput, system: { now: datetime } };
  entity Gateway;
  entity Trader = { id: String } tags String;
  action "Op" appliesTo { principal: [Trader], resource: [Gateway], context: Ctx };
}
"#;

/// A `Set<decimal>` — a set of an EXTENSION type, the case that most tempts a
/// naive fix to "descend into the set argument" (it must not).
const SHAPE_SET_OF_EXTENSION: &str = r#"
namespace Svc {
  type OpInput = { symbol: String, amounts: Set<decimal> };
  type Ctx = { input: OpInput, system: { now: datetime } };
  entity Gateway;
  entity Trader = { id: String } tags String;
  action "Op" appliesTo { principal: [Trader], resource: [Gateway], context: Ctx };
}
"#;

/// Nested sub-records two deep (`input.meta.region`) — the reserved spelling
/// must survive record recursion, not just top-level `input` members.
const SHAPE_NESTED_RECORD: &str = r#"
namespace Svc {
  type Meta = { region: String, tier: Long, rate: decimal };
  type OpInput = { symbol: String, meta: Meta };
  type Ctx = { input: OpInput, system: { now: datetime } };
  entity Gateway;
  entity Trader = { id: String } tags String;
  action "Op" appliesTo { principal: [Trader], resource: [Gateway], context: Ctx };
}
"#;

/// A cross-referencing chain of common types (`Ctx` → `Inner` → records),
/// mirroring the corpus's chained context-reference shape.
const SHAPE_CHAINED_REFERENCE: &str = r#"
namespace Svc {
  type OpInput = { symbol: String, qty: Long };
  type Inner = { input: OpInput, output?: { price: decimal }, system: { now: datetime } };
  type Ctx = Inner;
  entity Gateway;
  entity Trader = { id: String } tags String;
  action "Op" appliesTo { principal: [Trader], resource: [Gateway], context: Ctx };
}
"#;

#[test]
fn feed_forward_extensions_survives() {
    assert_survives_and_still_bites(SHAPE_EXTENSIONS, TEMPORAL_POLICY);
}

#[test]
fn feed_forward_set_of_primitive_survives() {
    assert_survives_and_still_bites(SHAPE_SET_OF_PRIMITIVE, TEMPORAL_POLICY);
}

#[test]
fn feed_forward_set_of_extension_survives() {
    assert_survives_and_still_bites(SHAPE_SET_OF_EXTENSION, TEMPORAL_POLICY);
}

#[test]
fn feed_forward_nested_record_survives() {
    assert_survives_and_still_bites(SHAPE_NESTED_RECORD, TEMPORAL_POLICY);
}

#[test]
fn feed_forward_chained_reference_survives() {
    assert_survives_and_still_bites(SHAPE_CHAINED_REFERENCE, TEMPORAL_POLICY);
}

/// Many iterations over the richest shape — a downstream pipeline may re-augment
/// far more than a handful of times, so confirm there is no slow-burn failure
/// or unbounded drift that only appears deep into the loop.
#[test]
fn feed_forward_many_iterations_stays_stable() {
    let sizes: Vec<usize> = {
        let mut current = SHAPE_EXTENSIONS.to_string();
        let service = ServiceSchema::defaults();
        let mut out = Vec::new();
        for pass in 0..10 {
            let schema =
                PolicySchema::from_cedarschema_str(&current).expect("re-ingest augmented schema");
            let lowered = ParsedPolicySet::parse(TEMPORAL_POLICY, &service)
                .expect("parse")
                .lower_with_distincter(&schema, &format!("p{pass}"))
                .unwrap_or_else(|e| panic!("pass {pass}: lower: {e:?}"));
            current = lowered.cedar_schema_str().expect("serialize");
            out.push(current.len());
        }
        out
    };

    // Each pass hoists exactly one new field (distinct distincter), so the
    // schema grows by a constant per pass — linear, never accelerating. A
    // super-linear jump would signal an accretion bug (fields duplicating, or
    // the reserved-spelling normalization re-expanding something each round).
    let deltas: Vec<i64> = sizes
        .windows(2)
        .map(|w| w[1] as i64 - w[0] as i64)
        .collect();
    let first = deltas[0];
    assert!(
        deltas.iter().all(|&d| d == first),
        "augmented-schema growth is not constant across passes (accretion/drift bug?); \
         sizes were {sizes:?}, deltas {deltas:?}"
    );
}

// ─── Provider augmentation is a distinct hoist path from temporal ────────────

/// A provider whose output is a record type, hoisted into a `providers`
/// context group — a different augmentation mechanism than temporal, over the
/// same reference-context schema, so it exercises the reserved-spelling path
/// independently.
const PROVIDERS_JSON: &str = r#"
{
  "availableProviders": {
    "Risk::Score": {
      "argumentTypes": [ { "paramType": "string" } ],
      "outputType": {
        "paramType": "record",
        "fields": { "level": { "paramType": "long" } },
        "required": ["level"]
      },
      "implementation": {
        "kind": "rhai",
        "script": "fn evaluate(symbol) { #{ level: 1 } }"
      }
    }
  }
}
"#;

const PROVIDER_POLICY: &str = r#"
permit ( principal, action == Svc::Action::"Op", resource )
when { Risk::Score(context.input.symbol).level < 5 };
"#;

#[test]
fn feed_forward_provider_augmentation_survives() {
    let decls = ProviderDeclarations::from_json(PROVIDERS_JSON).expect("providers.json parses");
    let service = ServiceSchema::builder()
        .providers(decls)
        .build()
        .expect("service schema builds");

    // Provider hoisting also inlines the reference context, so the same
    // reserved-spelling-in-input situation arises; the loop must survive it.
    let final_schema =
        feed_forward_with_service(SHAPE_EXTENSIONS, PROVIDER_POLICY, PASSES, &service)
            .unwrap_or_else(|e| panic!("provider feed-forward: {e}"));
    assert!(
        final_schema.contains("providers"),
        "the augmented schema should declare the hoisted `providers` group:\n{final_schema}"
    );
    // And the nested builtins still round-tripped through the reserved spelling.
    assert!(
        final_schema.contains("__cedar::"),
        "provider-augmented schema should still carry reserved builtin spellings:\n{final_schema}"
    );
}

/// Sanity companion to [`LoweredPolicySet::cedar_schema_json`]: the JSON export
/// (the Cedar JSON schema form) of a reference-context augmented schema must
/// itself re-parse as a Cedar `SchemaFragment`. We do not have a JSON *ingest*
/// path into `PolicySchema` (only `from_cedarschema_str`), so this guards the
/// half of the round-trip we do own — that the exported JSON schema is valid.
#[test]
fn augmented_json_export_is_valid_cedar_fragment() {
    let ps = PolicySchema::from_cedarschema_str(SHAPE_EXTENSIONS).expect("schema");
    let lowered = LoweredPolicySet::from_str(TEMPORAL_POLICY, &ServiceSchema::defaults(), &ps)
        .expect("lowers");
    let json = lowered.cedar_schema_json().expect("json export");
    cedar_policy::SchemaFragment::from_json_str(&json)
        .expect("augmented JSON export re-parses as a Cedar SchemaFragment");
}

// ─── Verdict preservation across feed-forward ────────────────────────────────
//
// The tests above prove a fed-forward schema RE-LOWERS. These prove the
// re-lowered policy still DECIDES correctly — a schema that re-ingests but
// silently drops or mistypes an `input` field would validate yet return the
// wrong verdict. Each decision is content-sensitive (it flips on an input
// value or on prior history), so a field lost across the round-trip changes
// the verdict stream rather than passing silently.

/// A reference-context trading schema (`Approve` / `Sell`) whose `input`
/// carries a `String` and `Long` and whose `output` carries a `decimal`, so
/// augmentation pins `__cedar::String` / `__cedar::Long` / `__cedar::decimal`
/// inside the inlined context — the failing positions.
const VERDICT_SCHEMA: &str = r#"
namespace Svc {
  type OpInput  = { stock: String, shares: Long };
  type OpOutput = { proceeds: decimal };
  type Ctx = { input: OpInput, output?: OpOutput };
  entity Gateway;
  entity Trader = { id: String } tags String;
  action "Approve" appliesTo { principal: [Trader], resource: [Gateway], context: Ctx };
  action "Sell"    appliesTo { principal: [Trader], resource: [Gateway], context: Ctx };
}
"#;

/// A rule whose decision depends on BOTH prior history and an `input` VALUE:
/// permit a `Sell` only if there was an `Approve` for the same `stock` within
/// the hour AND the trade is small. The temporal guard hoists a field (so the
/// context reference is inlined and `__cedar::` is emitted — the bug trigger),
/// while the `when { … shares < 100 }` clause makes the verdict ride on the
/// `input.shares` value. If the fed-forward schema lost / mistyped either
/// `input.stock` or `input.shares`, the verdict stream would change.
///
/// Deliberately NOT a pure-Cedar `when`: a pure-Cedar rule hoists nothing, so
/// augmentation never inlines the context and never emits `__cedar::` — such a
/// test would pass even on the buggy code and guard nothing.
const VALUE_GATED_POLICY: &str = r#"
permit ( principal, action == Svc::Action::"Sell", resource )
when temporal {
    formerly within 1h Svc::Action::"Approve"::request{ input.stock: context.input.stock }
}
when { context.input.shares < 100 };
"#;

/// Temporal rule whose decision depends on prior HISTORY: permit a `Sell` only
/// if an `Approve` for the same `stock` occurred within the last hour. This
/// both hoists a field (so `__cedar::` is emitted) and reads `input.stock`.
const HISTORY_GATED_POLICY: &str = r#"
permit ( principal, action == Svc::Action::"Sell", resource )
when temporal {
    formerly within 1h Svc::Action::"Approve"::request{ input.stock: context.input.stock }
};
"#;

/// A `request`-kind event for `action` at `ts`, carrying `stock` / `shares` in
/// both the logged fields and the request context (so a policy can read either).
fn sell_event(action: &str, ts: i64, stock: &str, shares: i64) -> Event {
    Event::builder(&format!("Svc::Action::{action}"), "request")
        .timestamp(ts)
        .principal("Svc::Trader::\"alice\"")
        .resource("Svc::Gateway::\"gw1\"")
        .field("input", "stock", Value::String(stock.to_string()))
        .field("input", "shares", Value::Int(shares))
        .request_context("input", "stock", Value::String(stock.to_string()))
        .request_context("input", "shares", Value::Int(shares))
        .build()
}

/// Replay a fixed event sequence through a fresh authorizer and collect the
/// `Sell` decisions in order.
fn sell_decisions(policies: LoweredPolicySet, events: &[Event]) -> Vec<Decision> {
    let mut authorizer = Authorizer::new(policies);
    let mut out = Vec::new();
    for e in events {
        if let Some(response) = authorizer.is_authorized(e) {
            if e.action().ends_with("Sell") {
                out.push(response.decision());
            }
        }
    }
    out
}

/// Lower `policy` once against the original schema, then feed the augmented
/// schema forward `passes` times, returning the policy set lowered against the
/// final (repeatedly re-augmented) schema.
fn lower_after_feed_forward(policy: &str, passes: usize) -> LoweredPolicySet {
    let svc = ServiceSchema::defaults();
    let mut current = VERDICT_SCHEMA.to_string();
    let mut last = None;
    for pass in 0..passes {
        let schema = PolicySchema::from_cedarschema_str(&current)
            .unwrap_or_else(|e| panic!("pass {pass}: re-ingest: {e:?}"));
        let lowered = LoweredPolicySet::from_str(policy, &svc, &schema)
            .unwrap_or_else(|e| panic!("pass {pass}: lower: {e:?}"));
        current = lowered
            .cedar_schema_str()
            .unwrap_or_else(|e| panic!("pass {pass}: serialize: {e:?}"));
        last = Some(lowered);
    }
    last.expect("at least one pass")
}

#[test]
fn value_gated_verdict_is_preserved_after_feed_forward() {
    let svc = ServiceSchema::defaults();
    let ps0 = PolicySchema::from_cedarschema_str(VERDICT_SCHEMA).expect("schema");

    // Approve(AMZN), then: small approved trade -> Allow; large approved trade
    // -> Deny (value gate); unapproved trade -> Deny (history gate). The three
    // outcomes together pin BOTH `input.stock` (history match) and
    // `input.shares` (value gate) surviving the round-trip.
    let events = [
        sell_event("Approve", 0, "AMZN", 5),
        sell_event("Sell", 100, "AMZN", 5),
        sell_event("Sell", 150, "AMZN", 500),
        sell_event("Sell", 200, "MSFT", 5),
    ];

    let baseline = sell_decisions(
        LoweredPolicySet::from_str(VALUE_GATED_POLICY, &svc, &ps0).expect("lower"),
        &events,
    );
    assert_eq!(
        baseline,
        vec![Decision::Allow, Decision::Deny, Decision::Deny],
        "baseline: allowed only when approved AND small"
    );

    // Re-lower against the fed-forward augmented schema (which carries the
    // reserved `__cedar::` spelling) and demand the identical verdict stream.
    let re_lowered = sell_decisions(
        lower_after_feed_forward(VALUE_GATED_POLICY, PASSES),
        &events,
    );
    assert_eq!(
        re_lowered, baseline,
        "value-gated verdicts changed after feed-forward re-lowering"
    );
}

#[test]
fn history_gated_verdict_is_preserved_after_feed_forward() {
    let svc = ServiceSchema::defaults();
    let ps0 = PolicySchema::from_cedarschema_str(VERDICT_SCHEMA).expect("schema");

    // Approve(AMZN) then Sell(AMZN) within the hour (-> Allow), then Sell(MSFT)
    // with no matching approval (-> Deny). The decision rides on prior history
    // keyed by `input.stock`, which must survive the round-trip.
    let events = [
        sell_event("Approve", 0, "AMZN", 5),
        sell_event("Sell", 100, "AMZN", 5),
        sell_event("Sell", 200, "MSFT", 5),
    ];

    let baseline = sell_decisions(
        LoweredPolicySet::from_str(HISTORY_GATED_POLICY, &svc, &ps0).expect("lower"),
        &events,
    );
    assert_eq!(
        baseline,
        vec![Decision::Allow, Decision::Deny],
        "baseline: Sell allowed only when a prior Approve for the same stock exists"
    );

    let re_lowered = sell_decisions(
        lower_after_feed_forward(HISTORY_GATED_POLICY, PASSES),
        &events,
    );
    assert_eq!(
        re_lowered, baseline,
        "history-gated verdicts changed after feed-forward re-lowering"
    );
}
