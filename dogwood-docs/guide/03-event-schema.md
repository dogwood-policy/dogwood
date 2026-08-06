# The Event Schema

This is an Advanced-topics deep dive on Dogwood's event-schema DSL. The core guide takes the event schema as **given** — the default schema that ships out of the box, which declares three event kinds: `request`, `response`, and `error`. The examples in this guide use only `request` and `response`. This page is for authors who need to *customize* the event model: which event kinds exist, what fields each kind carries, and which kinds are decision points that trigger an authorization decision. Everything here is optional; omit an event schema entirely and Dogwood uses the default described at the end.

## The event schema DSL (`.dwschema`)

The event schema is a **generic template** that describes how to derive event signatures from *any* action schema. It is a sequence of event declarations; each one names a kind of event (`request`, `response`, …) for a symbolic action `<A>` and lists the fields that kind carries. Parsing the event schema never looks at your action schema — the two are bound together in a later derivation pass. That is what lets a single event schema (like the default) serve every application.

### The shape of a declaration

Every declaration has the form:

```text
[decision] event <A>::kind {
    field,
    field,
    ...
}
```

- **`<A>` — the binder.** A symbolic name meaning "any action". *Every* selector inside the body must reference this exact binder. Writing `...inputs(B)` inside `event <A>::…` is a parse error: `selector argument \`B\` does not name the declared action binder \`A\``.
- **`kind` — the event kind.** An author-chosen name such as `request`, `response`, `attempt`, `outcome`, or `audit`. Kind names are *not* reserved; you pick them.
- **The angle brackets and body braces are mandatory.** `event A::r { }` (no `<>`) and `event <A>::r` (no body) are both parse errors. An *empty* body is fine: `event <A>::ping {}` declares a kind with zero fields.
- **`decision` prefix** marks the kind as a decision point (see [Decision kinds](#decision-kinds-when-authorization-runs)).

Comments use `//` to end of line; a trailing comma after the last field is allowed.

### The four selectors

Selectors are how a declaration reaches into the bound action. There are exactly four, and each has a fixed role:

| Selector | Spread as `...sel(A)`? | Used as a field *type* `sel(A)`? | Yields |
|---|---|---|---|
| `inputs` | yes → an `input` group | no (error) | the `context.input` field record |
| `outputs` | yes → an `output` group | no (error) | the `context.output` field record |
| `principalType` | no (error) | yes | the action's `appliesTo` principal type set |
| `resourceType` | no (error) | yes | the action's `appliesTo` resource type set |

`inputs` and `outputs` yield a *record of fields*, so they are meant to be **spread**. `principalType` and `resourceType` yield *entity types*, so they are meant to be used as a **field type**. Using one the wrong way is a derive error with a message that tells you which form to use instead — e.g. spreading `principalType` reports "cannot be spread (it yields entity types, not a field record); use it as a field type instead."

### Spread selectors: `...inputs(A)` and `...outputs(A)`

A spread splices every field the selector yields into the event, under a group named for the selector:

- `...inputs(A)` mints a group named **`input`** whose members are the fields of the action's `context.input` record. So a tool with `input: { user: String }` contributes the leaf `input.user`.
- `...outputs(A)` mints a group named **`output`** from `context.output`.

Two rules keep spreads unambiguous:

- The group name (`input` / `output`) must be unique in the declaration. It may not collide with a named field of the same name, nor may you spread the same selector twice.
- A spread always mints *its own* group, even nested inside a named record. Writing `meta: { ...inputs(A) }` produces `meta.input.user`, **not** `meta.user`.

### Named (injected) fields: `name: type`

A named field injects one field with an explicit type. The type can take three forms:

**1. A selector used as a type** — `principalType(A)` or `resourceType(A)`. This yields the action's declared `appliesTo` entity-type set, **kept whole** (no collapsing or unioning). For a two-principal action, both types are retained. (`inputs`/`outputs` may *not* be used as a type — spread them instead.)

**2. A concrete Cedar type** — an ordinary, possibly-qualified type name such as `String`, `Long`, or `Drupe::OAuthUser`.

**3. A nested record** — `{ … }`, a record type whose members are themselves field specs, addressed as `name.member`. This is how you opt a field into hierarchy. Members are derived recursively, so a spread inside a record is legal (`meta: { ...inputs(A) }`) and records nest arbitrarily deep.

Field names must be unique **at every level**, not just the top — a duplicate name inside a nested record is also an error.

### Nested records and deep hierarchy

Records can nest as deeply as you like, and field identity is by *dotted path*:

```text
__drupe: { sessionid: String }          // leaf __drupe.sessionid
a: { b: { c: String } }                      // leaf a.b.c; a and a.b are groups
meta: { }                                    // a group with no leaves
```

Flat fields, depth-2, and depth-3 fields can coexist on one event, and a flat reserved field (like `requestId`) stays flat while a sibling nests. The derived list of a `Login::request` event against the Login/Read action schema from [The policy language](02-policy-language.md) is, for example, `["input.user", "callerPrincipal", "callerResource", "requestId", "sessionId"]`.

### Pins: `pin name: type = <request-reference>`

A **pin** forces a correlation. On *every* predicate that mentions the event, the pinned field is implicitly conjoined to a request reference — the current request's `principal` / `resource` scope entity (± an attribute) or a `context.<path>` field — whether or not the policy author wrote it. This is how a schema author guarantees an invariant that individual policies cannot forget.

```text
pin callerPrincipal: principalType(A) = principal
```

The rules:

- **`pin` and `= <reference>` go together.** `pin foo: String` with no `=` is an error (`pinned field \`foo\` is missing its pin value`), and `foo: String = context.foo` without `pin` is an error (`field \`foo\` has a \`= context.<...>\` value but is not marked \`pin\``). The reference is either a scope entity (`principal`, `resource`, `principal.dept`) or a context field (`context.<path>`).
- **A pin may sit only on a leaf.** Pinning a whole record group is an error; pin a leaf *inside* the group instead.
- **`pin` is a contextual keyword.** It only acts as the pin prefix when a field declaration (`ident :`) follows. So a field can still be *named* `pin` (`pin: String`), and a field named `pin` can itself be pinned (`pin pin: String = context.pin`).

At derivation time each pinned leaf records its full dotted path plus the context path. The engine's pin-injection pass then runs *after* macro expansion and *before* validation: for every predicate naming an event with pins, it appends the correlation. The pin is appended **unconditionally** — even if the policy already wrote that field. A hand-written copy can only *narrow* a pin, never relax it: if it agrees with the pin the appended correlation is a redundant no-op, and if it disagrees the two constraints on the same field make the predicate unsatisfiable. Because injection happens before validation, the pinned field is validated like any authored field, and because it is never skipped, a pin cannot be bypassed — not by omitting the field, and not by writing it with a weaker value (a wildcard, a different `context.<path>`, or a fresh variable).

### Universal symmetric pins: key-local semantics and the partition guarantee

A pin becomes more than a per-predicate correlation when it is **universal**
and **symmetric**:

- **Universal** — the same pin is declared on **every** event kind the
  schema derives (`request`, `response`, and `error` in the default
  layout, plus any custom kinds). If a kind is left out the pin is not
  universal, and the partition guarantee does not apply.
- **Symmetric** — the pin's value is the field's own path on the current
  request (`pin session_id: String = context.session_id`), or one of the
  reserved scope-alias pairs (`pin callerPrincipal: principalType(A) =
  principal`, and likewise `callerResource`/`resource`). The alias uses the
  bare scope reference (`= principal` / `= resource`), **not** `=
  context.principal`: as noted below, `context.principal` is a context field
  literally named `principal`, not the scope entity, so it would *not* be the
  reserved alias and would not qualify. Symmetry is what makes an event's *own*
  field value the key under which it is both stored and looked up.

When at least one universal symmetric pin exists, Dogwood switches every
temporal leaf to **key-local semantics**: the leaf is evaluated *as if the
trace contained only the events agreeing with the current request on every
universally-pinned field* (the request's "slice"). Concretely:

- `formerly`, aggregations, and the negated-left `since` idiom already
  behave this way under pins (a pinned predicate can never match another
  key's event), so their meaning is unchanged.
- **`previous` means "this key's previous event."** Another key's
  interleaved event no longer displaces it — and no longer *satisfies*
  it. The window still measures from the decision point, exactly.
- **The positive left of `since` quantifies over this key's positions
  only.** Another key's interleaved event cannot break the "held at every
  step" continuity; the key's *own* non-matching events still do.

This is implemented by a lowering-time rewrite of the leaf formulas (the
authored form is what validation checks and error messages point at; the
rewritten form is what engines evaluate, so any conforming engine agrees
with the in-memory interpreter). The default event schema carries such a
pin, on `callerPrincipal`, so key-local semantics apply unless
you replace it: every temporal leaf is keyed on the requesting principal,
and events from other principals are invisible to it. With no universal
symmetric pin — an event schema that declares none, or declares one that is
partial or asymmetric — nothing changes: leaves keep the global-trace
semantics described in
[Temporal expressions](04-temporal-expressions.md).

**A pin that is not universal silently keeps global semantics — with no
error.** A pin declared on only *some* event kinds (e.g. on `request` but
not `response`), or one that is not symmetric, is a valid schema: it still
acts as an ordinary per-predicate correlation, but it does **not** activate
key-local semantics and the partition guarantee does **not** apply. Nothing
warns you — the schema builds and evaluates, just without isolation. To buy
the guarantee you must declare the *same* symmetric pin on **every** derived
event kind; otherwise assume global-trace semantics.

The payoff is the **partition guarantee**: with a universal symmetric pin
on field `f`, a verdict for a request with key `f = v` depends *only* on
events whose `f` equals `v`. Events may therefore be stored, evaluated,
and retained **per key** — a per-session or per-principal database is
equivalent to a global one — and no policy, present or future, can write
a temporal expression that escapes the key. One consequence to weigh
before adopting a universal pin: it applies to *every* predicate, so
cross-key policies
("more than N logins by *any* user") become inexpressible under it —
that is the isolation being bought.

### How request references resolve in policies

Both a pin's right-hand side and a policy's request references resolve against the **current decision request**, mirroring Cedar's four request variables:

- `principal` / `resource` are the request scope's principal / resource **entities** — regardless of what the schema happens to *name* its injected principal field. A trailing attribute (`principal.dept`) reads that entity's attribute from the request's entity store; a bare `principal` is the entity itself (for identity), and `principal.id` / `principal.type` project the uid.
- `context.<path>` resolves to a field of the request **context** record at that dotted path (`context.input.user`, `context.__drupe_sessionid`, `context.__drupe.session.id`). This is Cedar's `context` variable — a plain record — so `context.principal` would be a field literally *named* `principal` in that record, **not** the scope entity.

This distinction matters: an injected field can be renamed `actor` and still be correlated against the scope principal with `actor: principal`, while a declared context field like `__drupe_sessionid` is reached by its own name (`context.__drupe_sessionid`).

### Worked examples from the corpus

These are real, passing `event.dwschema` files from the tested corpus. Each case named below is a directory under `dogwood-language/tests/passing/temporal_only/corpus/`.

**Author-defined kinds and a renamed principal field (`1110_custom_event_schema_renamed_reserved`).** Nothing forces the kinds to be `request`/`response`; here they are `attempt` (a decision) and `outcome` (history-only), and the injected principal is renamed `actor`:

```text
decision event <A>::attempt {
    ...inputs(A),
    actor: principalType(A),
}
event <A>::outcome {
    ...inputs(A),
    ...outputs(A),
    actor: principalType(A),
}
```

The policy then correlates `actor: principal`.

**A renamed flat reserved field (`1111_custom_injected_sessionid`).** This replaces the default's `sessionId` with `__drupe_sessionid`, keeping the other three reserved leaves:

```text
decision event <A>::request {
    ...inputs(A),
    callerPrincipal:      principalType(A),
    callerResource:       resourceType(A),
    requestId:            String,
    __drupe_sessionid:  String,
}
event <A>::response {
    ...inputs(A),
    ...outputs(A),
    callerPrincipal:      principalType(A),
    callerResource:       resourceType(A),
    requestId:            String,
    __drupe_sessionid:  String,
}
```

A policy can then reach the field by name: `…::request{ input.user: context.input.user, __drupe_sessionid: context.__drupe_sessionid }`.

**Input/output field-name collision (`1112_input_output_field_name_collision`).** This uses the *default* schema (no custom `event.dwschema`) and relies on the `input` / `output` grouping to keep two same-named fields distinct as `input.x` and `output.x`.

**Nested reserved field (`1113_nested_reserved_field_correlation`).** `__drupe: { sessionid: String }` derives the leaf `__drupe.sessionid`; the policy correlates `__drupe.sessionid: context.__drupe.sessionid`.

**Depth-3 nested fields (`1114_deep_nested_field_correlation` / `1116_injection_onto_deep_path`).** `__drupe: { session: { id: String, region: String } }` derives `__drupe.session.id`. `1114_deep_nested_field_correlation` correlates it directly; `1116_injection_onto_deep_path` injects the same correlation through a `def temporal same_session(?w, ?s)` macro (see [Macros](06-macros.md)).

**Two deep siblings (`1115_multiple_deep_path_constraints`).** Both `__drupe.session.id` and `__drupe.session.region` are carried under the one group and constrained together.

**Top-level pin (`1117_pin_principal_correlation`).** The pin forces every predicate for this event to share the request's principal, even though no policy writes `callerPrincipal`. It is declared on both kinds, which is what makes it universal:

```text
decision event <A>::request {
    ...inputs(A),
    pin callerPrincipal: principalType(A) = principal,
    callerResource:  resourceType(A),
    requestId:       String,
}
event <A>::response {
    ...inputs(A),
    ...outputs(A),
    pin callerPrincipal: principalType(A) = principal,
    callerResource:  resourceType(A),
    requestId:       String,
}
```

**Nested-leaf pin (`1118_pin_nested_session_id`).** A pin can sit on a leaf *inside* a record group; here it conjoins `__drupe.session_id: context.__drupe.session_id` onto every predicate:

```text
decision event <A>::request {
    ...inputs(A),
    callerPrincipal: principalType(A),
    callerResource:  resourceType(A),
    requestId:       String,
    __drupe: { pin session_id: String = context.__drupe.session_id },
}
event <A>::response {
    ...inputs(A),
    ...outputs(A),
    callerPrincipal: principalType(A),
    callerResource:  resourceType(A),
    requestId:       String,
    __drupe: { pin session_id: String = context.__drupe.session_id },
}
```

**A pin cannot be bypassed by a hand-written field (`1119_pin_not_bypassed_by_wildcard`, `1120_pin_agrees_with_author_written_field`, `1121_pin_not_bypassed_by_fresh_binder`, `1122_pin_disagree_denies_despite_author_literal`).** These all have the policy *write* the pinned field, proving the append is unconditional. Three are bypass attempts that fail:

- **`1119_pin_not_bypassed_by_wildcard` — wildcard.** The policy writes `callerPrincipal: _` (accept a Login by any principal). The pin is still injected, so the wildcard adds nothing and the cross-principal Login is still excluded.
- **`1121_pin_not_bypassed_by_fresh_binder` — fresh variable.** The policy writes `callerPrincipal: p` where `p` is used nowhere else — a variable that binds but never constrains, so on its own it too accepts any principal. The pin still forces the correlation.
- **`1122_pin_disagree_denies_despite_author_literal` — disagreeing concrete value.** Using the nested-session schema of `1118_pin_nested_session_id`, the policy hard-codes `__drupe.session_id: "sess-1"` (the historical Login's session). That literal alone would permit every trace; the pin adds `context.__drupe.session_id`, so when the *current* request's session differs the two constraints on the one field disagree, the predicate is unsatisfiable, and the Read is denied. This is the "disagree → unsatisfiable" outcome end to end.

The fourth, **`1120_pin_agrees_with_author_written_field` — agreeing value**, writes the pin's exact value (`callerPrincipal: principal`); the appended pin is then a redundant no-op and the verdicts match `1117_pin_principal_correlation`. Together they cover both documented outcomes of a hand-written pinned field: a weaker one (wildcard, variable, or a disagreeing value) can only narrow the pin, never relax it, and an agreeing one is a no-op.

### How derived fields appear on an ingested event

To make the derivation concrete, here is an event from `1113_nested_reserved_field_correlation`'s trace (against the Login/Read action schema from [The policy language](02-policy-language.md)) — the fields the event schema derived, filled in with real values:

```text
@0  scope(principal: Drupe::OAuthUser::"alice", resource: Drupe::Gateway::"gw1")
    request_context(…)
    Drupe::Action::"Login"::request(
      input: { user: "alice" },
      callerPrincipal: Drupe::OAuthUser::"alice",
      callerResource:  Drupe::Gateway::"gw1",
      requestId: "u1",
      __drupe: { sessionid: "sess-1" })
```

`input.user` came from the `...inputs(A)` spread; `callerPrincipal`, `callerResource`, `requestId` and the nested `__drupe.sessionid` came from the injected fields. The `request_context(…)` bag is elided here because it is not derived from the event schema — it is the request's own context record, which every `context.<path>` reference reads, whether in a Cedar condition or in a temporal correlation like this case's. A real trace line spells it out.

---

## Capping the look-back window: `max_window`

A temporal policy looks back over event history with a `within <interval>`
window (see [Temporal expressions](04-temporal-expressions.md)). The event
schema can put a ceiling on how far back *any* policy may look with an optional
`max_window` directive at the top of the file:

```text
max_window = 24h

decision event <A>::request {
    ...inputs(A),
    callerPrincipal: principalType(A),
    callerResource:  resourceType(A),
    requestId:       String,
}
```

The rules:

- **It goes first, at most once.** The directive precedes all event
  declarations; placing it after one is a parse error.
- **The interval is a positive `<amount><unit>`** using the same four units as
  temporal windows (`s`, `m`, `h`, `d`) — e.g. `24h`, `30m`, `7d`. A zero
  window (`max_window = 0h`) is a parse error, since it would forbid every
  `within` clause; omit the directive instead if you want no custom cap.
- **Absent, the cap defaults to `24h`.** Omitting `max_window` — as
  every schema shown elsewhere in this guide does — uses the 24h default.
- **The bound is inclusive.** A `within` window *equal* to the cap is allowed;
  only a window *strictly greater* than the cap is rejected. So under the
  default, `within 24h` (and the identical `within 1d`) pass, while `within 48h`
  or `within 7d` are rejected.

The validator enforces the cap: any temporal `within` window in a policy that
exceeds `max_window` is a validation error naming both the offending window and
the cap, whether the window sits on a top-level `formerly`/`previous`/`since`
or is nested inside an aggregation. Raise the cap here when a policy genuinely
needs a longer history (`max_window = 30d`), or lower it to tighten what
policies may do (`max_window = 1h`).

---

## Decision kinds: when authorization runs

The `decision` prefix determines when Dogwood authorizes.

Dogwood ingests a stream of events. Ingesting an event of a **decision kind** runs authorization and produces a verdict; ingesting any other (history-only) kind updates the engine's state but yields no verdict. This is the mechanism behind temporal policies: a `response` records that a tool call completed (history), and a later `request` for another tool can ask about it (decision).

- `LoweredPolicySet::decision_kinds()` exposes the set of kinds marked `decision` (with `is_decision_kind(kind)` for a single check).
- The **default** event schema marks **only `request`** as a decision kind. `request` runs authorization; `response` and `error` are history-only.
- A custom schema may mark any kinds — `1110_custom_event_schema_renamed_reserved` makes `attempt` the decision kind and `outcome` history-only.

---

## The default event schema (request / response / error)

If you never supply an event schema, Dogwood uses `DEFAULT_EVENT_SCHEMA`. Here it is in full:

```text
decision event <A>::request {
    ...inputs(A),
    pin callerPrincipal: principalType(A) = principal,
    callerResource:    resourceType(A),
    requestId:         String,
    sessionId:         String,
}

event <A>::response {
    ...inputs(A),
    ...outputs(A),
    pin callerPrincipal: principalType(A) = principal,
    callerResource:    resourceType(A),
    requestId:         String,
    sessionId:         String,
}

event <A>::error {
    ...inputs(A),
    pin callerPrincipal: principalType(A) = principal,
    callerResource:    resourceType(A),
    requestId:         String,
    sessionId:         String,
}
```

Reading it part by part:

- **`decision event <A>::request`** — for every action `A`, a `request` event that is a decision point (runs authorization).
  - `...inputs(A)` — the tool's arguments, nested under the `input` group (`input.user`, `input.document`, …).
  - `pin callerPrincipal: principalType(A) = principal` — a top-level leaf holding the request principal's entity-type set (the full `appliesTo` set, kept whole), pinned to the request's scope principal.
  - `callerResource: resourceType(A)` — the resource entity-type set.
  - `requestId: String` — the event's unique id, a flat leaf.
  - `sessionId: String` — the session this request belongs to.
- **`event <A>::response`** — a history-only event (no `decision`), emitted when the tool call resolves successfully.
  - `...inputs(A)` **and** `...outputs(A)` — both the argument (`input.*`) and result (`output.*`) groups, so a `response` carries the outcome.
  - the same reserved leaves (`callerPrincipal`, `callerResource`, `requestId`, `sessionId`).
- **`event <A>::error`** — a history-only event emitted when the gateway/target returns an error.
  - `...inputs(A)` — the attempted call's arguments, so a policy can correlate on what was attempted.
  - the same reserved leaves (no `...outputs(A)` since the call failed).

So against the `Login`/`Read` schema, `Login::request` derives `input.user`, `callerPrincipal`, `callerResource`, `requestId`, `sessionId`; `request` does **not** splice outputs, while `response` splices both. The `callerPrincipal` pin is declared on every kind and is symmetric, so the default carries a universal symmetric pin: temporal leaves run under [key-local semantics](#universal-symmetric-pins-key-local-semantics-and-the-partition-guarantee), keyed on the requesting principal. To get global-trace semantics instead, supply an event schema without that pin.

---

## See also

- [The policy language](02-policy-language.md) — the action schema these events derive from.
- [Temporal expressions](04-temporal-expressions.md) — how decision-kind and history-kind events power past-looking policies (the consumer of decision kinds).
- [The API and workflow](07-api-and-workflow.md) — assembling `ServiceSchema` + `PolicySchema`.
- [The provider schema](10-provider-schema.md) — how information providers are declared (another input the `ServiceSchema` carries).
- [Macros](06-macros.md) — the macro library the `ServiceSchema` also carries.
