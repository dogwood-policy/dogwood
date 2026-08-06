# Temporal Expressions

This page is the reference and tutorial for Dogwood's **temporal sublanguage** — the code you write inside a `when temporal { … }` (or `unless temporal { … }`) block. Ordinary Cedar authorization decides *this* request from *this* request's attributes. Temporal expressions extend that decision to the **event history**: they let a policy say "allow this only if such-and-such happened (or did not happen) recently." This document motivates why that matters, then builds the sublanguage up operator by operator — the three past operators (`formerly`, `previous`, `since`) and their mandatory windows, conjunction and negation, the `exists` and `tp` binders, aggregations (`count`, `sum`), predicates and field patterns, field-injection refinement, and finally the legality rules that decide which expressions are accepted. It closes with the precise evaluation semantics. If you are new to Dogwood policies overall, read [02-policy-language.md](02-policy-language.md) first; this page assumes you know what `permit`/`forbid`, `when`, and `unless` mean. Every policy example below is backed by a runnable bundle under [`examples/`](../examples/) that the `dogwood` CLI validates (and, where a `trace.log` is present, replays) on each build.

## Why temporal? Authorization over event history

Cedar answers a question about a single moment: given this principal, this action, this resource, and this request context, permit or forbid? That is enough for "can Alice read document X" but not for questions whose answer depends on *what came before*:

- "Allow a write only if the same user read the same document within the last hour."
- "Deny any action after a logout until the next login."
- "Flag a transfer if the user has made more than two logins in the last hour."
- "Require that a heartbeat was seen recently before trusting a session."

Each of these is a statement about a **trace** of events over time, not a single request. Dogwood's temporal sublanguage is a bounded, past-only fragment of Metric First-Order Temporal Logic (MFOTL) for expressing authorization-over-history rules.

A worked scenario: **write-after-read.** Suppose an agent may only write a document it has recently read. In Dogwood you attach a temporal marker to the rule and, inside it, assert that a matching `Read` event occurred in the recent past:

```text
permit(principal, action == Drupe::Action::"Write", resource)
when temporal {
    formerly within 1h Drupe::Action::"Read"::response{
        input.user: context.input.user,
        input.document: context.input.document
    }
};
```

> Runnable: [`examples/write_after_read_formerly/`](../examples/write_after_read_formerly/) — `dogwood validate` and `dogwood replay`.

Read this as: "permit the write only if, at some point in the last hour, this same user successfully read this same document." The `formerly within 1h …` part is the temporal claim; the predicate `Drupe::Action::"Read"::response{ … }` describes the past event to look for; and `input.user: context.input.user` pins the past event's user to the *current* request's user. (This is corpus case `0004_write_after_read`.)

### The `temporal` marker keyword

Dogwood adds one extension sub-language that plugs into a policy's `when`/`unless` clause via a marker keyword: **`temporal`**, which this page is about. (There is a second clause tag, **`guardrails`**, but it is *not* a sub-language — `guardrails { E }` is sugar for a bare `when { E }`, and information providers are invoked as ordinary Cedar calls; see [05-information-providers.md](05-information-providers.md).) Internally the codebase sometimes calls the temporal extension a "dialect," but in a `.dw` file you always write the surface keyword `temporal`, and that is the term this documentation uses throughout.

### What a temporal block *is*, mechanically

The body between the `temporal { … }` braces is parsed as a single **condition** and evaluated at the request's **decision timepoint** against all events up to and including that moment. The whole block yields a boolean: true means the temporal condition held, and the enclosing `when`/`unless` uses that boolean exactly as it would any other clause. `when temporal { φ }` contributes to permitting only when `φ` holds; `unless temporal { φ }` blocks when `φ` holds — which is the idiomatic way to express absence, as we will see with `unless temporal { formerly … }`.

## The building block: predicates

Before the temporal operators, you need the thing they operate on — a **predicate**, which describes a past event to match. Every temporal example is built from predicates, so we cover them first.

### Predicate shape

A predicate names a fully-qualified action, an event *kind*, and a set of field patterns:

```text
Namespace::…::Action::"ActionId"::kind{ field: pattern, … }
```

Decomposing `Drupe::Action::"Login"::request{ input.user: context.input.user }`:

- **namespace** — `Drupe::Action`
- **action** — the quoted id `"Login"`
- **kind** — the trailing `::request`
- **args** — the field patterns `input.user: context.input.user`

The `::kind` suffix is **mandatory**; a predicate is not well-formed without it. The quoted action id acts as an anchor so the parser can tell the namespace `::` segments (before the quote) apart from the kind segment (after the quote).

**Event kinds are author-defined, not a fixed set.** `request` and `response` are merely the conventional kinds — `request` for the invocation, `response` for the result — and a response predicate typically reads `output.*` fields (a `formerly`-gated read-after-successful-login permit built on this is runnable as [`examples/read_after_login_success/`](../examples/read_after_login_success/)):

```text
Drupe::Action::"Login"::response{ input.user: context.input.user, output.result: true }
```

There is no separate "response" AST form; a response is a predicate whose `kind` segment is `response`. Nothing stops a schema from naming other kinds; corpus case `1110_custom_event_schema_renamed_reserved` uses a custom `attempt` kind (runnable as [`examples/login_attempt_custom_kind/`](../examples/login_attempt_custom_kind/)):

```text
formerly within 1h Drupe::Action::"Login"::attempt{ input.user: context.input.user, actor: principal }
```

### Field patterns

Each named argument is `field_path : term`. The field name is a **dotted path** into the event's record — a bare field (`user`), or a path into a nested group (`input.user`, `output.result`). This mirrors how you reference the current request on the right-hand side (`context.input.user`): an event's spliced input/output values nest under the `input` and `output` groups, which stay distinct.

The **term** on the right of the colon is the pattern the field must match. The forms you will use:

- **Value binding** — a bare variable name captures the field's value into a variable for later use: `input.user: u`, `input.amount: a`. The variable is *bound* by the first predicate that mentions it and equality-checked by later ones.
- **Pinned correlation** — a `context.*` reference forces the past event's field to equal the current request's field: `input.user: context.input.user`. It is what expresses "the *same* user" and "the *same* document".
- **Scope correlation** — `principal` and `resource` are the current request's principal and resource entities (Cedar's request variables — the *same* names, and the *same* meaning, you use in a plain `when { … }` Cedar clause), and pin against the reserved event fields `callerPrincipal` / `callerResource`:

  ```text
  formerly within 1h Drupe::Action::"Heartbeat"::request{
      input.server: context.input.server,
      callerPrincipal: principal,
      callerResource: resource
  }
  ```

  (Corpus case `0036_plain_heartbeat`.) A trailing attribute reads that entity's attribute — `principal.dept`, `resource.owner` — resolved against the current request's entity attributes, exactly as a pure-Cedar `when { principal.dept == … }` and a provider argument `principal.dept` do. So `principal` means the same thing in all three surfaces; there is **no** `context.principal` alias (in Cedar, and now here, `context.principal` would be a field literally named `principal` in the context *record*, not the scope entity).
- **Literal values** — a string (`input.server: "s1"`), a boolean (`output.result: true`), or a decimal (`output.score: decimal("0.5")`).
- **Wildcards** — `_` or `*` matches anything and binds nothing: `input.user: _`, `input.amount: *`. Each wildcard is **independent**: in `P{ a: _, b: _ }` the two `_`s do *not* force `a == b`. Use a shared variable name if you want that.

### Terms in general

Beyond field patterns, terms appear on both sides of comparisons and as macro arguments. The full term vocabulary:

| Term | Syntax | Notes |
|---|---|---|
| Entity | `Drupe::OAuthUser::"alice"` | qualified entity reference |
| Integer | `42`, `-1` | |
| Decimal | `decimal("1.5")` | payload kept as text; equality-only at eval time (see semantics) |
| String | `"hello"` | |
| Boolean | `true` / `false` | |
| Context field | `context.input.foo`, `context.system.now` | dotted path into the current request's context record |
| Scope entity | `principal`, `resource`, `principal.dept` | the request principal / resource entity (± an attribute) |
| Variable | a bare identifier | a bound-variable name |
| Wildcard | `*`, or a bare `_` | matches anything, binds nothing; each independent |
| Array | `[a, b, c]` | |
| Aggregate | `count …` / `sum …` | comparison-operand-only (see aggregations) |

## The past operators and their windows

There are exactly **three** temporal operators, and all of them look only into the past: `formerly`, `previous`, and `since`. There are **no future operators** and no unbounded operator — every temporal operator carries a mandatory `within <interval>` window that bounds how far back it looks.

### Intervals and time units

A window is written `within <amount><unit>`. There are exactly **four** time units:

| Unit | Meaning | Seconds |
|---|---|---|
| `s` | seconds | 1 |
| `m` | minutes | 60 |
| `h` | hours | 3600 |
| `d` | days | 86400 |

There is no week, month, or year unit. The amount is an integer. A window boundary is a **closed (inclusive)** interval: a witness exactly `W` seconds back is *in* the window; one second further is *out* (see [Evaluation semantics](#evaluation-semantics)).

**Windows are capped.** How far back a window may look is bounded by the event schema's `max_window` — **24h by default**, adjustable with a `max_window = <interval>` directive at the top of the event schema (see [The event schema](03-event-schema.md#capping-the-look-back-window-max_window)). The validator rejects any `within` window that exceeds the cap. So `within 7d` or `within 30d` require a schema that raised the cap accordingly; under the default they are validation errors. The bound is inclusive, so `within 24h` sits exactly at the default cap and is allowed.

> The `within ?w` form (a `?`-sigil in place of a literal) is legal only inside a macro body, where the window is a parameter resolved at the call site; see [Macros](#macros-def-temporal). Outside a macro body you always write a literal like `1h`.

### `formerly` — happened at least once, recently

**Syntax:** `formerly within <interval> <atom>`

`formerly` is the existential past operator: it holds at the decision timepoint if its body held at **some** timepoint within the window. Think "did this ever happen in the last hour?" The write-after-read policy from the introduction uses it (corpus `0004_write_after_read`; runnable as [`examples/write_after_read/`](../examples/write_after_read/), which adapts it to a `SellShares`/`ApproveSale` permit):

```text
when temporal {
    formerly within 1h Drupe::Action::"Read"::response{
        input.user: context.input.user,
        input.document: context.input.document
    }
};
```

The body of `formerly` (and of `previous`) is an **atom**: a parenthesized condition, a `tp(...)`, a macro call, a predicate (optionally refined), or a comparison. A bare `&&` chain is *not* an atom, so to put a conjunction under `formerly` you must parenthesize it: `formerly within 1h (A && B)`.

A session-correlated example using the scope entities (corpus `0036_plain_heartbeat`; the same pattern is runnable as an `Alert` permit in [`examples/heartbeat_scope_alias/`](../examples/heartbeat_scope_alias/)):

```text
when temporal {
    formerly within 1h Drupe::Action::"Heartbeat"::request{
        input.server: context.input.server,
        callerPrincipal: principal,
        callerResource: resource
    }
};
```

### `previous` — the immediately preceding event

**Syntax:** `previous within <interval> <atom>`

`previous` is stricter than `formerly`: it looks only at the **immediately preceding timepoint** (`i - 1`), not the whole window. It holds when the event directly before the decision point is *both* within the window *and* satisfies the body. At the first timepoint it is `false` (there is no previous event). The window still applies, so `previous within 1h` succeeds only when the preceding event was at most an hour ago.

Corpus `0243_kernel_previous_within` (runnable as a `Read`-after-login permit in [`examples/read_prev_login/`](../examples/read_prev_login/)):

```text
when temporal {
    previous within 1h Drupe::Action::"Login"::request{ input.user: context.input.user }
};
```

With a response predicate and an output-field filter (corpus `0183_previous_at_tp0_no_verdict`; runnable as [`examples/read_prev_login_success/`](../examples/read_prev_login_success/)):

```text
when temporal {
    previous within 1h Drupe::Action::"Login"::response{ input.user: context.input.user, output.result: true }
};
```

Because `previous`'s body is an atom, a conjunction must again be parenthesized (corpus `0268_previous_containing_nested`):

```text
when temporal {
    previous within 2h (
        Drupe::Action::"Login"::request{ input.user: context.input.user }
        && Drupe::Action::"Login"::request{ input.server: "s1" }
    )
};
```

### `since` — held continuously since an anchor

**Syntax:** `<left> since within <interval> <right>`

`since` is **infix**: unlike `formerly` and `previous`, which come before a single body, it sits between its two operands. Each operand is a single item, as with those operators, so a conjunction on either side must be parenthesized. It expresses "`left` has held continuously ever since `right` happened." Formally it holds at the decision point when there is an anchor timepoint `j` in the window where `right` held, and `left` held at **every** step from `j+1` through the decision point. This is MFOTL's `left S right`.

A positive-left example — a login has held continuously since a login (corpus `0034_since_explicit`; runnable as [`examples/read_since_login/`](../examples/read_since_login/)):

```text
when temporal {
    Drupe::Action::"Login"::request{ input.user: context.input.user }
    since within 1h
    Drupe::Action::"Login"::request{ input.user: context.input.user }
};
```

**Negated left — the "open session" idiom.** There is no dedicated "hasn't happened since" operator; you write it with a negated left operand, `!left since …`. Because negation binds tighter than `since` (see [Precedence](#conjunction-negation-and-precedence)), `!A since within W B` negates only `A`. This expresses "no `A` has happened since `B`" — e.g. "the user has not been revoked since they were granted" (corpus `0156_without_since_access_control`; runnable as [`examples/access_not_revoked_since_grant/`](../examples/access_not_revoked_since_grant/)):

```text
when temporal {
    !Drupe::Action::"Revoke"::request{ input.user: context.input.user, input.resource: context.input.resource }
    since within 1h
    Drupe::Action::"Grant"::request{ input.user: context.input.user, input.resource: context.input.resource }
};
```

A `since` with a shorter window unit (corpus `0184_since_window_anchor_too_old`; runnable as [`examples/read_heartbeat_since_login_30s/`](../examples/read_heartbeat_since_login_30s/)):

```text
when temporal {
    Drupe::Action::"Heartbeat"::request{ input.user: context.input.user }
    since within 30s
    Drupe::Action::"Login"::request{ input.user: context.input.user }
};
```

## Conjunction, negation, and precedence

The temporal sublanguage has exactly **one** boolean connective: conjunction, `&&`. There is **no `||`** (disjunction). If you need "A or B," write two separate policy rules — that is how disjunction across authorization outcomes is expressed. Three common patterns follow from just `&&`, `!`, and the binders:

- "A but not B" → `a && !b`
- "X has not held since an anchor" → `!X since …`
- binding a computed value → `exists (n: T). ((A) == n && B)` (see [Binders](#binders-exists-and-tp))

### Negation `!`

Negation is written with a leading `!`. `!a` is boolean negation of `a`. In a relational context (inside `exists` or an aggregation `where` body) it acts as an **anti-join filter**: it keeps a row only when `a` does *not* hold under that row's bindings. Multiple `!`s stack, and an even count cancels (double negation).

### Precedence: `!` > `since` > `&&`

From tightest to loosest binding: negation, then `since`, then conjunction. Consequences:

- `!a && b` parses as `(!a) && b` — negation binds only `a`.
- `!a since within W b` parses as `(!a) since within W b` — negation binds only the since-left.
- To widen a negation's scope, parenthesize: `!(a && b)`.

`&&` is left-associative and is the loosest operator, so a top-level chain like `A && B && C` groups as `((A && B) && C)`. A top-level conjunction combining a `formerly` with an `exists`-guarded count (corpus `0059_count_threshold`; runnable as an `Alert` permit in [`examples/alert_heartbeat_and_login_rate/`](../examples/alert_heartbeat_and_login_rate/)):

```text
when temporal {
    formerly within 1h Drupe::Action::"Heartbeat"::request{ input.server: context.input.server }
    && exists (n: Long). (
        (count for (t: Timepoint). where (
            Drupe::Action::"Login"::request{ input.user: _, input.server: context.input.server } && tp(t)
        )) == n && n > 2
    )
};
```

A top-level `previous && (open-session)` chain (corpus `0462_previous_and_without_since_top_level`; runnable as a `Read` permit in [`examples/read_prev_compute_open_session/`](../examples/read_prev_compute_open_session/)):

```text
when temporal {
    previous within 1h Drupe::Action::"Compute"::request{ input.user: context.input.user }
    && (!Drupe::Action::"Logout"::request{ input.user: context.input.user }
        since within 24h
        Drupe::Action::"Login"::request{ input.user: context.input.user })
};
```

> **Order matters in a `&&` chain** — not for logical truth, but for what is *accepted*. A conjunct that only filters (like `!X` or an ordering comparison) must come *after* a conjunct that binds its variables. See [Writing temporal expressions that are accepted](#writing-temporal-expressions-that-are-accepted).

## Binders: `exists` and `tp`

Predicates capture field values into variables. To *quantify* over those values — "there is some user such that…" — or to reason across distinct timepoints, you use the two binders.

### `exists` — the sole quantifier

**Syntax:** `exists (x: T). φ`

`exists` introduces a single typed variable `x` and asserts that its body `φ` has at least one satisfying assignment. It is the only binding form in the language. A few important rules:

- **The type annotation is mandatory** on the binder. Types are `Timepoint`, or a qualified concrete/entity type (`Long`, `String`, `Drupe::OAuthUser`). The annotation is **authoritative**: validation seeds the binder's declared type into the type environment and then checks every *use* of the variable against it, rather than inferring the type from the first use. A use that contradicts the declaration is a type error — `exists (x: Long). x == "s"` is rejected because the string literal is inconsistent with the declared `Long`. The annotation is only consulted at *validation* time; at *evaluation* time only the binder name matters (candidate values still come from the binding atom, so there is no enumeration of the type).
- **The scope is greedy to the right.** The body is a full condition, so `exists (x: T). φ && ψ` binds `x` over *both* `φ` and `ψ`. To stop the scope early, parenthesize: `(exists (x: T). φ) && ψ`.
- **It is "at least one," not a count.** `exists` is satisfied by one or more witnesses; it does not tell you *how many*. Use `count` for that.
- **The type is not enumerated.** `x`'s candidate values come only from the atom that binds it — a predicate field, a `tp`, or an `(agg) == x` equality. There is no iteration over "all Longs."

Simplest form — some user logged in (corpus `1140_exists_login_no_agg`):

```text
exists (u: String). formerly within 1h Drupe::Action::"Login"::request{ input.user: u, input.server: context.input.server }
```

Correlation — the *same* user both logged in and transferred, by sharing `u` across two `formerly`s (corpus `1142_exists_correlation`; runnable as an `Alert` permit in [`examples/alert_same_user_login_and_transfer/`](../examples/alert_same_user_login_and_transfer/)):

```text
exists (u: String). (
    formerly within 1h Drupe::Action::"Login"::request{ input.user: u }
    && formerly within 1h Drupe::Action::"Transfer"::request{ input.user: u }
)
```

Nested existentials with a value filter — a user who logged in and made a transfer over 100 (corpus `1143_nested_exists_threshold`; runnable as an `Alert` permit in [`examples/alert_login_and_big_transfer/`](../examples/alert_login_and_big_transfer/)):

```text
exists (u: String). (
    formerly within 1h Drupe::Action::"Login"::request{ input.user: u }
    && exists (a: Long). (
        formerly within 1h Drupe::Action::"Transfer"::request{ input.user: u, input.amount: a }
        && a > 100
    )
)
```

Two **independent** existentials (distinct variables, no correlation — different users may satisfy each side) look like `exists (u: …). ( … ) && exists (v: …). ( … )` — contrast that with the shared-`u` binding above. And an entity-typed binder can correlate on the same principal:

```text
exists (pr: Drupe::OAuthUser). (
    formerly within 1h Drupe::Action::"Login"::request{ callerPrincipal: pr }
    && formerly within 1h Drupe::Action::"Deny"::request{ callerPrincipal: pr }
)
```

### `tp` — the timepoint binder

**Syntax:** `tp(t)`

`tp(t)` binds `t` to the timepoint currently being evaluated. It appears inside an aggregation's `where` body, conjoined with a predicate, so the aggregation can range over **distinct timepoints**. Whether `t` is listed in the aggregation's `for` domain determines distinctness:

- Include `t` in the `for` list to keep **one row per timepoint** — this counts occurrences over time.
- Omit `t` from the `for` list to **deduplicate equal values** across time.

The count-over-timepoints idiom — how many logins to this server occurred (corpus `0178_agg_no_temporal_counts_current_tp`; runnable as an `Alert` permit in [`examples/alert_login_current_tp/`](../examples/alert_login_current_tp/)):

```text
when temporal {
    exists (n: Long). (
        (count for (t: Timepoint). where (
            Drupe::Action::"Login"::request{ input.user: _, input.server: context.input.server } && tp(t)
        )) == n && n > 0
    )
};
```

## Aggregations: `count` and `sum`

Aggregations turn a set of matching past events into a number you can compare against a threshold. There are exactly **two** aggregate keywords: `count` and `sum`. There is **no `min`, `max`, or `avg`.**

### Form

```text
count for (g1: T1), …, (gn: Tn). where φ
sum   v for (g1: T1), …, (gn: Tn). where φ
```

- `count` yields the number of matching rows.
- `sum v` yields the sum of column `v` over those rows; `v` must be one of the `for`-declared variables (written as a bare name, no type).

The `for <binders>.` clause names the **aggregation domain**: the satisfying assignments of `where φ` are collected, projected onto the `for` variables, **deduplicated**, then aggregated. Each `for` element is a declaration site, so it carries a mandatory type annotation, and the trailing `.` terminates the list. An aggregate is a numeric term (it yields a `Long`).

### Two rules that shape how you write aggregations

**1. Aggregates may appear only as an immediate comparison operand.** An aggregate is syntactically a term, but it is legal *only* directly on one side of a comparison — never as a predicate-argument value, never nested inside an array or another term. `P{ f: count … }` and `[count …] == x` are both rejected.

**2. Parenthesize an aggregate on the left of a comparison.** The `where` body is a greedy full condition, so `(count …) == n` needs parentheses around the aggregate or the `where` body will swallow the `== n`. On the *right* of a comparison no parentheses are needed, because there is nothing to the right for the greedy body to eat: `0 < count for (t: Timepoint). where φ` parses fine. The parentheses carry no semantics; they only fence the greedy body.

### `count` examples

Exact count — exactly two logins (corpus `0062_count_exact`):

```text
when temporal {
    (count for (t: Timepoint). where (
        Drupe::Action::"Login"::request{ input.user: _, input.server: context.input.server } && tp(t)
    )) == 2
};
```

Count over history using a temporal body (corpus `0179_agg_with_once_counts_history`; runnable as an `Alert` permit in [`examples/alert_login_in_last_hour/`](../examples/alert_login_in_last_hour/)):

```text
when temporal {
    exists (n: Long). (
        (count for (t: Timepoint). where (
            formerly within 1h (Drupe::Action::"Login"::request{ input.user: _, input.server: context.input.server } && tp(t))
        )) == n && n > 0
    )
};
```

Aggregate-vs-aggregate comparison — note the left operand is parenthesized, the right is not (corpus `1144_agg_vs_agg`):

```text
when temporal {
    (count for (t: Timepoint). where (
        formerly within 1h (Drupe::Action::"Transfer"::response{ requestId: _ } && tp(t))
    ))
    < count for (t: Timepoint). where (
        formerly within 1h (Drupe::Action::"Transfer"::request{ requestId: _ } && tp(t))
    )
};
```

Count over a `*`-wildcard field — exactly three transfers, regardless of amount (corpus `1117_count_for_tp`; runnable as an `Alert` permit in [`examples/alert_exactly_three_transfers/`](../examples/alert_exactly_three_transfers/)):

```text
when temporal {
    (count for (t: Timepoint). where (
        formerly within 1h (Drupe::Action::"Transfer"::request{ input.amount: * } && tp(t))
    )) == 3
};
```

### `sum` examples

Simple sum of a bound value column — total transferred exceeds 200 (corpus `0063_sum_threshold`; runnable as an `Alert` permit in [`examples/alert_total_transfer_over_200/`](../examples/alert_total_transfer_over_200/)):

```text
when temporal {
    exists (total: Long). (
        (sum a for (a: Long). where Drupe::Action::"Transfer"::request{ input.amount: a }) == total
        && total > 200
    )
};
```

Sum over a `(value, timepoint)` domain with a filtered temporal body (corpus `0299_sum_resolved_filter`; runnable as a `forbid Read` rule in [`examples/forbid_read_transfers_over_1000/`](../examples/forbid_read_transfers_over_1000/)):

```text
when temporal {
    exists (total: Long). (
        (sum a for (a: Long), (t: Timepoint). where (
            formerly within 1h (
                Drupe::Action::"Transfer"::response{ input.user: context.input.user, output.amount: a }
                && a > 0 && tp(t)
            )
        )) == total
        && total > 1000
    )
};
```

The two-binder domain `for (a: Long), (t: Timepoint).` is what keeps equal amounts made at different timepoints from being deduplicated — `a` is the summed value, `t` distinguishes the timepoints. A range filter on the bound value (corpus `0301_sum_resolved_range_filter`) works the same way, adding `a > 100 && a < 500` inside the temporal body.

## Comparisons

Comparisons filter or bind. The operators are `<`, `<=`, `>`, `>=`, `==`, and `!=`:

```text
term cmp_op term
```

Both operands are terms, and either may be an aggregate (subject to the comparison-operand-only rule above). Semantics:

- `==` and `!=` use domain equality on the resolved values.
- Ordering comparisons (`<`, `<=`, `>`, `>=`) require **both** sides to resolve to integers; otherwise the comparison is `false`. Decimals are kept as text and are effectively equality-only — a `decimal(…)` in an ordering comparison resolves but fails the integer conversion and yields `false`.
- If either operand fails to resolve (an unbound variable, a wildcard), the comparison is `false`.

**`==` doubles as a binder.** In a relational context, an `a == x` (or `x == a`) with exactly one *unbound* variable operand **binds** that variable to the other side's value. This is the mechanism behind `exists (n: Long). ((agg) == n && …)` — the `== n` binds `n` to the aggregate's value so the following `n > 2` can filter it. An `==` with no unbound operand, or any ordering comparison, is a plain filter.

## Field-injection refinement

A predicate (or a macro condition-sigil) may carry trailing `{ … }` blocks that inject *extra* named arguments onto it:

```text
P::kind{ a: 1 }{ b: 2 }   // equivalent to P::kind{ a: 1, b: 2 }
?s{ status: "approved" }  // refine a macro's predicate-valued argument
```

With zero blocks, the predicate is unchanged. With one or more blocks, the injected arguments are concatenated and merged onto the base predicate. The base must resolve to a **single predicate** — refining a conjunction, a `formerly`, or a comparison is a static error. Refinement is resolved at macro expansion time and never reaches the evaluator.

Refinement exists for the **macro path**: a macro whose parameter is a predicate can have extra fields forced onto whatever predicate the caller passes. Corpus case `1116_injection_onto_deep_path` refines a predicate-valued parameter `?s` with a deep session-id field to force a same-session correlation:

```text
def temporal same_session(?w, ?s) {
    formerly within ?w (?s{ __drupe.session.id: context.__drupe.session.id })
};
```

## Macros (`def temporal`)

Macros let you name and parameterize a temporal pattern: you define one *outside* a temporal block with `def temporal name(...) { <body> }` and call it *inside* one. This section covers the call site — for defining a macro (the `?p` / `$t` sigils, hygiene, and the rejection rules), see [Macros](06-macros.md).

A macro **call** looks like an ordinary call, `name(arg, …)`. Each argument may be a bare interval literal, a condition, or a term. A window argument at the call site is a **bare interval literal** (`1h`, `30m`) with **no `within` keyword** — the `within` keyword stays with the temporal operator in the macro body. The call site for the `same_session` macro above (corpus `1116_injection_onto_deep_path`):

```text
when temporal {
    same_session(
        1h,
        Drupe::Action::"Login"::request{ input.user: context.input.user }
    )
};
```

The first argument `1h` fills the `within ?w` window; the second (a predicate condition) fills `?s`. A runnable, `validate`-passing macro that exercises the same `?s{…}` refinement-in-body path (the `same_session` example above uses a deep context path the validator rejects) is [`examples/submit_after_approval_injection/`](../examples/submit_after_approval_injection/).

> Macros are a fully specified part of the language; reach for them when you have a reusable temporal pattern. See [Calling macros](09-calling-macros.md) for call syntax across both sublanguages, and [Macros](06-macros.md) for the general macro system (defining `def temporal`, the sigils, and hygiene).

## Writing temporal expressions that are accepted

A temporal expression is accepted only when it is well-defined as a runtime monitor. That is stricter than "it parses." The rejections all trace back to one requirement: every variable must be **bound** (by an `exists` or an aggregation `for` list) and **range-restricted** — pinned to a finite set of candidate values by a positive atom — before anything tries to filter it or count over it. Below are the rules, framed as what you must do to be accepted.

### Close the condition: bind every variable

A temporal condition must be **closed**: every variable you write must be bound by an `exists (x: T).` binder or an aggregation `for` list. A free variable is rejected at parse time — a temporal leaf is evaluated as a single boolean at the decision point, with no implicit "for some value" reading, so a free variable would silently turn the guard into one that never fires (or correlates the wrong things).

- **Rejected — free variable in a filter:** `formerly … Transfer{ input.amount: a } && a > 100`. Wrap it: `exists (a: Long). (formerly … Transfer{ input.amount: a } && a > 100)`.
- **Rejected — even a single-use free variable:** `formerly … Login{ input.user: u }`. If you mean "any value," write the wildcard: `formerly … Login{ input.user: * }`.
- **Accepted:** every variable `exists`-bound or in a `for` list; field values that are literals, `*`, or `context.…` / `principal.…` / `resource.…` references (those are not variables).

### Range-restrict every `exists` variable

An `exists (x: T). φ` is accepted only if `x` is range-restricted by a **positive** atom somewhere in `φ`: a predicate field (`P{ f: x }`), a `tp(x)`, or an equality (`(term/agg) == x` or `x == (term/agg)`). A restrictor under a negation does *not* count — at **any** negation depth (a doubly-negated atom still restricts nothing: negation is evaluated as an opaque filter that produces no bindings).

- **Rejected — no restrictor, only ordering filters:** `exists (x: Long). (0 < x && x < 2)`. Ordering comparisons filter an infinite domain; nothing pins `x`.
- **Rejected — restrictor under negation:** `exists (x: String). !Login{ input.user: x }`. The only mention of `x` is negated. Likewise `!(!Login{ input.user: x })`.
- **Accepted:** restricted by a predicate field, by `tp`, by an `(agg) == n` equality, by a literal equality (`x == 5`), or restricted under a `formerly` body.

### Order conjuncts so producers come before consumers

Within a `&&` chain, every conjunct may *produce* bindings (a predicate field, `tp`, a binding equality) and may *consume* bindings — variables that must already be bound when it evaluates. A consumer is accepted only when the variables it consumes are restricted by a **preceding** conjunct — in the same chain, or inherited from an enclosing chain (parenthesized sub-chains and nested `exists`/`formerly` bodies see everything already established at their position; an enclosing *binder* alone establishes nothing, and a shadowing binder cuts inherited restrictions of its name). The consumers:

- a **pure filter** — an ordering comparison, a guarded negation `!φ`, or a non-binding `==` (including `x == *`: a wildcard is not a value, so the equality binds nothing) — consumes all its free variables;
- a **binding equality** `x == (aggregate)` produces `x` but consumes the aggregate's *correlated* variables (free in its `where` body, not in its `for` list) — with them unbound, the count/sum would silently de-correlate into a global tally;
- a **`since`** consumes the left operand's variables not restricted by its anchor (the left is checked per step and can bind nothing itself).

**❌ Rejected — filter before its restrictor:**
```text
exists (a: Long). (a > 100 && formerly … Transfer{ input.amount: a })
```
**✓ Fixed — restrictor first:**
```text
exists (a: Long). (formerly … Transfer{ input.amount: a } && a > 100)
```

---

**❌ Rejected — correlated count before its restrictor:**
```text
exists (u: String). exists (n: Long). (
    (count for (t: Timepoint). where (formerly … (Login{ input.user: u } && tp(t))))
    == n && n >= 2 && formerly … Login{ input.user: u }
)
```
**✓ Fixed — move the restrictor before the equality:**
```text
exists (u: String). (
    formerly … Login{ input.user: u }
    && exists (n: Long). (
        (count for (t: Timepoint). where (formerly … (Login{ input.user: u } && tp(t))))
        == n && n >= 2
    )
)
```

---

**❌ Rejected — since-left variable restricted only later:**
```text
exists (u). ((Read{ input.user: u } since … Login{}) && formerly … Transfer{ input.user: u })
```
**✓ Fixed — put the restrictor first, or restrict `u` in the anchor:**
```text
exists (u). (formerly … Transfer{ input.user: u } && (Read{ input.user: u } since … Login{}))
```

---

**✓ Accepted — guarded negation after a restrictor** (runnable as a `Read` permit in [`examples/read_login_not_logout/`](../examples/read_login_not_logout/)):
```text
Login{ input.user: context.input.user } && !Logout{ input.user: context.input.user }
```

**✓ Accepted — standard aggregate shape:**
```text
exists (n: Long). ((agg) == n && n > 0)
```

Binding equalities against a *ground* value (`x == 5`, `x == context.input.limit`) are pure producers, so their order never matters.

### Bind — and range-restrict — every aggregation `for` variable

Every free variable of an aggregation body must be bound — either by the `for` list or by an enclosing binder — and for `sum v`, the summed variable `v` must itself be in the `for` domain. A body variable bound nowhere is a static error, because the projection onto the `for` columns would leave it dangling. Conversely, every `for` variable must **occur** in the body **and** be **range-restricted by a positive atom** of it, exactly like an `exists` binder: an occurrence under a negation, or only in the *left* operand of a `since` (only the anchor restricts), pins nothing — the domain would be infinite, and the count or sum would silently collapse.

- **Rejected — unbound body variable:** `sum a for (a: Long), (t: Timepoint). where (W{user: p, amount: a} && tp(t))` where `p` is free — `p` is neither in the `for` list nor bound by an enclosing binder.
- **Rejected — `for` variable only under a negation:** `count for (x: String). where (!(formerly … Login{ input.user: x }))` — "the users who did *not* log in" is an infinite set.
- **Rejected — `for` variable only in a since-left:** `count for (w: String). where (Read{ input.user: w } since … Login{})` — the anchor `Login{}` restricts nothing about `w`.
- **Accepted:** each `for` variable read from a predicate field (`P{ f: x }`), a `tp(t)`, or an `(agg) == x` equality in positive position — a guarded negation *after* such a restrictor is fine (`P{ f: q } && !exists … { f: q }`).

### Keep aggregates as comparison operands only

As covered above: an aggregate is legal only as the immediate operand of a comparison, never as a predicate argument or nested in another term.

### Every monitoring scope must depend on the timepoint (tp-dependence)

A schema-aware check rejects any **degenerate** monitoring scope — one whose body does not vary with the current timepoint, and therefore "monitors nothing." Only predicate matches and `tp(_)` vary between timepoints that share the same request context; literals, `context.*` references, and entities are timepoint-independent, and an aggregate is *always* timepoint-dependent. Scopes that are individually checked include each top-level `&&` conjunct, a `formerly`/`previous` body, each side of a `since`, an `exists` body, and an aggregation's `where` body. In practice this means every scope must contain at least one real predicate (or `tp`); a conjunct made only of literals and context references is rejected.

### Schema-level checks

Beyond the structural rules, the schema-aware validation pass also requires: every entity type and enum eid you reference is declared; every `context.input.<field>` path resolves in the scoped action's input record; and comparison operands and predicate arguments type-check against the schema. Ordering comparisons need numeric operands on both sides; `==` needs compatible types. (Predicate event-kind and field-name validation is owned by a separate event-schema checker.) See [The policy language](02-policy-language.md) for the action schema (entity/action declarations, the `context` shape) and [The event schema](03-event-schema.md) for the event-kind and field definitions.

### Legality in one sentence

A temporal expression is legal exactly when: it parses under the grammar (only `&&`, `!`, `since`, the three temporal operators, `exists`, `tp`, comparisons, `count`/`sum`, predicates, refinements, and macro calls); it is closed (every variable bound by an `exists` or a `for` list); every aggregation's `for` domain binds every free body variable, includes any summed variable, and each `for` variable occurs in — and is range-restricted by a positive atom of — the body; every `exists` binder is range-restricted by a positive atom; every aggregate appears only as an immediate comparison operand; every consumer (a pure filter, a binding equality's aggregate operand, a since-left) is preceded — in its chain or an enclosing one — by a restrictor of the variables it consumes; and, at the schema stage, every entity/enum reference and `context.input.X` path resolves, every monitoring scope is timepoint-dependent, and all operands type-check.

## Evaluation semantics

This section states precisely how a temporal condition is evaluated. Any conforming temporal engine must produce these verdicts.

**Decision timepoint and history.** A condition is evaluated at a single **decision timepoint `i`** against the trace history `0..=i` — everything up to and including `i`. The language is **past-only**: nothing at any `j > i` is ever read. The request's own fields seed the initial bindings (nested groups flattened to dotted keys), plus the scope aliases `@principal` and `@resource`.

**Key-local semantics under universal pins.** The semantics below are stated over the *whole* trace. When the event schema declares a **universal symmetric pin** (a field pinned on every event kind to its own request-side path — see [The event schema](03-event-schema.md)), every temporal condition is instead evaluated over the **slice** of the trace agreeing with the current request on the pinned field(s): `previous` means "this key's previous event," and the `∀`-side of `since` ranges over this key's positions only. For `formerly`, aggregations, and the negated-left `since` idiom the two readings coincide: a pinned predicate cannot match another key's event, and a body containing no such predicate is guarded so that a foreign position cannot witness it either. The slice reading is what makes per-key storage and evaluation verdict-preserving. **The default event schema declares such a pin**, on `callerPrincipal`, so the key-local reading is the one that applies unless you replace it. Without a universal symmetric pin — a schema that declares none, or one that is partial or asymmetric — the global reading below applies verbatim.

**Windows are closed (inclusive).** A window of `W` is the set of past timepoints `j` with `0 <= ts(i) - ts(j) <= W`. A witness exactly `W` seconds back is *in*; one second further is *out*. The lower bound `>= 0` is what makes the language past-only.

**Operator semantics, "holds at timepoint `i`":**

- **`formerly within W body`** holds iff `body` holds at *some* `j` in `[0, i]` with `ts(i) - ts(j) <= W`. Relationally it collects the body's satisfying rows at *every* in-window timepoint, so an aggregation over a `formerly` body sees one row per satisfying occurrence.
- **`previous within W body`** checks *only* `j = i - 1`: it holds iff the immediately preceding timepoint is in-window and `body` holds there. At `i == 0` it is `false`.
- **`left since within W right`** holds iff there is an anchor `j` in the window where `right` holds and `left` holds at every step `k` in `[j+1, i]` (through the decision point). Range restriction for the whole `since` comes from the anchor `right`.
- **`!a`** is boolean `¬a`; relationally it is an anti-join filter (keep a row iff `a` does not hold under its bindings).
- **`&&`** is evaluated left-to-right, and a binding-producing conjunct on the left extends the environment before the right is evaluated; bindings accumulate. Relationally it is a join on shared columns — this is why the *same* variable in two predicates correlates them.
- **`exists (x: T). φ`** holds iff `φ`'s relation is non-empty (≥ 1), not a count; `x`'s candidate values come only from the atom that binds it, with no enumeration of the type.
- **`tp(t)`** binds or unifies `t` with the current timepoint index `i`.
- **`count` / `sum`** project the `where` body's satisfying rows onto the `for` domain, deduplicate, then count the rows or sum the named column. Distinctness is the visible choice you make in the `for` list. Summation is exact for every total a `Long` can hold, including totals reached by way of partial sums that a `Long` cannot, and does not depend on the order rows are visited. What a total OUTSIDE the `Long` range means is implementation-defined — a conforming implementation may clamp, widen, or report an error, and the shapes that can observe the choice are enumerated in [§5.4 Temporal acceptance](08-formal-specification.md#54-temporal-acceptance-well-formedness). This implementation clamps rather than raising, so a pathological trace cannot overflow into a panic. Only the binder *name* is used at evaluation time; the type annotation is not consulted.
- **Comparisons** — `==` and `!=` are domain equality; ordering requires both sides to be integers, else `false`; an unresolved operand makes the comparison `false`. An `==` with exactly one unbound variable operand binds that variable.

## See also

- [02-policy-language.md](02-policy-language.md) — the core Cedar-derived policy language, the `when`/`unless` clauses that host a `temporal { … }` block, and the action schema (entity/action declarations and the `context` shape) that temporal validation checks against.
- [03-event-schema.md](03-event-schema.md) — how event kinds and their fields are declared (the `::kind` and field names a predicate matches).
- [05-information-providers.md](05-information-providers.md) — information providers (external computed facts), invoked as plain Cedar calls in an ordinary `when { … }`.
- [09-calling-macros.md](09-calling-macros.md) — calling macros (both `def cedar` and `def temporal`) at the sites shown here.
- [06-macros.md](06-macros.md) — the general macro system, including defining `def temporal`.
- [00-introduction.md](00-introduction.md) and [01-getting-started.md](01-getting-started.md) — orientation and setup.
- [07-api-and-workflow.md](07-api-and-workflow.md) — lowering policies and running the monitor.
