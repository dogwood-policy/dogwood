# Information Providers

This page covers **using** Dogwood's **information providers**: values computed at
authorize time by a small piece of sandboxed code, then folded back into a policy as
if they had always been part of the request context. It explains how you call a
provider from an ordinary `when { … }` clause, the arguments a provider can take, how
its output composes with the rest of a condition, and how that output reaches you as
`context.providers.<id>`. Corpus cases named below are directories under
`dogwood-language/tests/passing/provider_only/corpus/`; each complete policy
shown below is also a runnable bundle under [`examples/`](../examples/).

This page takes the providers themselves as **given**. Declaring one — the
`providers.json` format, the Rhai implementation contract (the sandbox, host
functions, decimal support, the off-by-default `net` feature), and the advanced
features (output methods, no-implementation providers, and the `guardrails { … }`
sugar) — is the subject of the Advanced-topics page
[The provider schema](10-provider-schema.md).

---

## What an information provider is, and why

Cedar policies decide on the request they are given. Sometimes the fact you want to
authorize on is not *in* the request — it has to be **computed**: does this document
match a regex? Is this string on a denylist? What is the risk score of this content
according to some classifier? An information provider lets you write that
computation once, declare its shape, and then reference its result inside a policy as
though it were an ordinary context attribute.

A provider is lowering-time sugar over Cedar. When you write a
provider invocation in a policy, Dogwood does *not* invent a new runtime evaluator.
Instead, at lowering time it **hoists** the invocation out of the policy
and rewrites it to a reference into `context.providers.<id>`. The Cedar that the
engine ultimately evaluates contains no provider call at all — just a plain attribute
access and comparison. Then, at authorize time, Dogwood runs the provider's
declared implementation, and binds its output record into
`context.providers.<id>` before handing the request to Cedar.

Because providers are hoisted at lowering time, the hoisted field must be typed and
declared in the schema. A rule that calls a provider may use any action scope —
`action == Ns::Action::"X"`, `action in [list]`, `action in Group`, or a bare
unconstrained `action` — because the hoisted field is grafted onto every action's
context and the provider is evaluated for every decision event (see
[The provider contract](#the-provider-contract) below).

---

## Calling a provider

You call a provider directly inside an ordinary `when { … }` clause, exactly where
you would write any other Cedar condition. There is no special marker: any
namespace-qualified name (`Ns::Fn`) is read as a provider invocation. You invoke it, reach into
its output, and compare — all as part of a normal Cedar expression:

```text
permit ( principal, action == Doc::Action::"read", resource )
when {
    Strings::Matches(context.input.document, "^[A-Z]+$").matched == true
};
```

That reads as: call the `Strings::Matches` provider with the document and a regex,
take the `matched` field of its output, and require it to be `true`.

Because the call sits in ordinary Cedar, only the *call itself* is special — the
projection (`.matched`) and comparison (`== true`) are plain Cedar. That means a
provider's output composes with the full Cedar expression language: arithmetic,
`if`/`then`/`else`, any method, `&&`/`||`/`!`, comparisons against other context
fields — anything Cedar allows.

### The shape of a call

A provider call has three parts, in order:

1. **Invocation** — `Ns::Fn(args)`. The function name must be namespace-qualified:
   it needs at least two `::`-separated segments (like `Strings::Matches`,
   `Content::Risk`, `Lists::Blocked`). A bare single-segment name is not a valid
   provider function. More segments are allowed (`Ns::Sub::Fn`).
2. **Projection** — zero or more accessors that reach into the provider's output
   record: `.field` (field access) or `["key"]` (index access). Because Cedar has no
   positional list indexing, an index must be a **string key**: `record["k"]` reads
   the `k` field. The projection may be empty, in which case the output is compared
   directly.
3. **Comparison** — any Cedar comparison. Against a `bool`/`long`/`string` output you
   use the ordinary operators (`==`, `!=`, `<`, `<=`, `>`, `>=`). A `decimal` output
   supports `==` and `!=`; to *order* one, use Cedar's decimal-extension methods
   (`lessThan`, `lessThanOrEqual`, `greaterThan`, `greaterThanOrEqual`) with a
   `decimal("…")` literal.

### A complete worked example

Here is a provider from the policy author's side. It uses the `Strings::Matches`
provider (corpus case `0001_regex_matches_uppercase`), which asks whether a document matches a regular
expression. The policy (`policy_1.dw`):

```text
permit ( principal, action == Doc::Action::"read", resource )
when {
    Strings::Matches(context.input.document, "^[A-Z]+$").matched == true
};
```

> Runnable: [`examples/provider_regex_matches_uppercase/`](../examples/provider_regex_matches_uppercase/) — `dogwood validate` and `dogwood replay`.

Behind it, `Strings::Matches` is declared in a
`providers.json` (with argument types `[string, string]`, an output record
`{ matched: bool }`, and a small Rhai script) — the declaration side is covered in
[The provider schema](10-provider-schema.md).

What happens: at lowering time, `Strings::Matches(context.input.document, "^[A-Z]+$")`
is hoisted to a `context.providers.<id>` reference, and the policy Cedar becomes
`context.providers.<id>.matched == true`. At authorize time, Dogwood runs the
provider's `evaluate("...the document...", "^[A-Z]+$")`, gets back the record
`{ matched: … }`, binds it into `context.providers.<id>`, and Cedar evaluates
`.matched == true`. So `"ABC"` gives `true` (permit), `"abc"` gives `false`, and
`"AB12"` gives `false`.

### Combining providers with the rest of a condition

Because a provider call is just part of an ordinary Cedar condition, it combines with
`&&`, `||`, `!`, parentheses, other provider calls, and plain Cedar terms — the full
expression language (see [The policy language](02-policy-language.md)).

Two providers combined with `&&` and `!` (the `Strings::Matches` and `Lists::Blocked`
providers of case `0004_two_providers_and_not`) — a fragment; the full rule is the
[`provider_matches_and_not_blocked`](../examples/provider_matches_and_not_blocked/) bundle:

```text
when {
    Strings::Matches(context.input.document, "^[a-z]+$").matched == true
    && !(Lists::Blocked(context.input.document).blocked == true)
};
```

Disjunction and parentheses (the `Lists::Allowed` and `Strings::Length` providers of
case `0007_boolean_or_parens`) — a fragment; the full rule is the
[`provider_allowed_or_short`](../examples/provider_allowed_or_short/) bundle:

```text
when {
    (Lists::Allowed(context.input.document).allowed == true
     || Strings::Length(context.input.document).length < 4)
};
```

Several calls to the same provider, each with plain-Cedar comparisons — case `0005_regex_operations`
(a fragment; the full rule is the
[`provider_regex_analyze_fields`](../examples/provider_regex_analyze_fields/) bundle):

```text
when {
    Regex::Analyze(context.input.document, "^[A-Z]").is_match == true
    && Regex::Analyze(context.input.document, "[0-9]").count >= 3
    && Regex::Analyze(context.input.document, "[0-9]+").first_match == "42"
};
```

Because the output is plain Cedar, it can feed ordinary Cedar expressions — for
instance, an integer output used in **arithmetic** alongside an ordinary context
field — case `0010_unwrapped_mixed_with_cedar` (a fragment; the full rule is the
[`provider_int_arithmetic_trusted`](../examples/provider_int_arithmetic_trusted/) bundle):

```text
when {
    context.input.trusted == true
    && Strings::DigitCount(context.input.document).count + 1 <= 3
};
```

### The comparison, in two forms

The comparison against a provider's output comes in two flavors, depending on the
output's type.

**Operator form** uses one of `<=`, `>=`, `==`, `!=`, `<`, `>`. Verified examples
across the corpus include `.matched == true` (case `0001_regex_matches_uppercase`), `.length < 5`
(case `0002_length_threshold`), and `.count >= 2` (case `0008_greater_than_family`) — this fragment's full rule is the
[`provider_digitcount_operator_ge`](../examples/provider_digitcount_operator_ge/) bundle:

```text
when {
    Strings::DigitCount(context.input.document).count >= 2
};
```

**Method form** uses Cedar's decimal comparison methods —
`lessThan`, `lessThanOrEqual`, `greaterThan`, `greaterThanOrEqual` — to compare a
`decimal` output against a `decimal("…")` literal (the `Content::Risk` provider of
case `0003_decimal_score_method`) — a fragment; the full rule is the
[`provider_risk_decimal_method`](../examples/provider_risk_decimal_method/) bundle:

```text
when {
    Content::Risk(context.input.document).severityScore.lessThan(decimal("0.5"))
};
```

Use the method form to order a `decimal` output; `==` and `!=` work on a `decimal`
directly, and the operators cover `bool` / `long` / `string` outputs.

### Projection: reaching into the output record

The projection is the path between the invocation and the comparison. Field access
(`.field`) and index access (`["key"]`) can be chained. Because Cedar has no
positional list indexing, an index must be a string key: `record["k"]` reads the
`k` field.

The `Content::Filter` provider of case `0006_set_arg_index_projection` chains an index accessor and a field
accessor, then compares with the decimal method form (a fragment; the full rule is the
[`provider_filter_set_index_decimal`](../examples/provider_filter_set_index_decimal/) bundle):

```text
when {
    Content::Filter(context.input.document, ["VIOLENCE", "HATE"])["VIOLENCE"].severityScore.lessThan(decimal("0.5"))
};
```

Here `["VIOLENCE"]` selects the `VIOLENCE` sub-record from the output, `.severityScore`
reads its field, and `.lessThan(decimal("0.5"))` compares.

### Providers work under `permit` and `forbid`

A provider call is independent of the rule's effect: it works the same under `permit`
and `forbid`. Here the `Strings::DigitCount` provider of case `0008_greater_than_family` gates a `forbid`
(with a catch-all `permit` alongside):

```text
forbid ( principal, action == Doc::Action::"post", resource )
when {
    Strings::DigitCount(context.input.document).count >= 2
};
```

> Runnable: [`examples/provider_digitcount_forbid/`](../examples/provider_digitcount_forbid/) — the `forbid` plus a catch-all `permit`; `dogwood validate` and `dogwood replay`.

### A caution on names

A call is read as a provider invocation because of its shape — any
namespace-qualified name — not because it is declared. Declaredness is a separate
check, made at lowering: a namespace-qualified call that matches no declared provider
(and no macro and no Cedar built-in) is a hard error, "unresolved call to `Ns::Fn`
reached lowering — it is not a declared information provider, not a declared macro,
and not a Cedar built-in". So a mistyped provider name is caught, not silently
ignored.

---

## Provider arguments

A provider invocation passes arguments positionally. Because a provider is
resolved *before* Cedar runs (it helps build the context Cedar evaluates
against), an argument must be a value Dogwood can read off the request event
directly. The argument kinds are:

- **Attribute-path reference** — `context.input.x`, `principal.id`,
  `resource.owner`. It begins with one of the roots `context` / `principal` /
  `resource`, followed by one or more `.ident` segments. At authorize time
  Dogwood resolves the path against the decision event: a `context` path is
  looked up on the event's input (leading `context` skipped); `principal` /
  `resource` resolve to the request scope entity, and a trailing `.id` / `.type`
  projects that entity's id or type. A path that does not resolve is null.
- **String literal** — `"…"`.
- **Integer literal** — an optionally-signed integer (`i64`).
- **Decimal literal** — `decimal("0.5")` (chiefly a method threshold, e.g.
  `scoreAbove(decimal("0.5"))`).
- **Bool literals** — `true` / `false`.
- **Set** — `[ arg, … ]`, possibly empty, and possibly nesting other args (a set of
  strings, ints, bools, or nested sets/paths).

Arbitrary Cedar (arithmetic, `if`/`then`/`else`) is **not** a provider argument —
only the value forms above. This mirrors the temporal-logic argument restriction.

Field-and-string arguments — case `0001_regex_matches_uppercase`:

```text
Strings::Matches(context.input.document, "^[A-Z]+$")
```

A principal-rooted argument — case `0015_principal_id_arg` (a fragment; the full rule is the
[`provider_principal_id_allowlist`](../examples/provider_principal_id_allowlist/) bundle):

```text
Access::Allowed(principal.id)
```

A set argument — cases `0006_set_arg_index_projection` / `0009_unwrapped_no_marker`:

```text
Content::Filter(context.input.document, ["VIOLENCE", "HATE"])
```

At authorize time, each argument is resolved to a runtime value (event fields and
scope entities as above, literals as-is, sets recursively), and the values are
passed positionally to the provider's implementation, matched to its declared
argument order.

> **Declaring a provider.** The signature you invoke against — the argument types,
> the output record, and the implementation that computes it — is declared in a
> `providers.json` file, described in full in
> [The provider schema](10-provider-schema.md). This page assumes those
> declarations already exist and focuses on calling them from a policy.

---

## How a provider binds to `context.providers.<id>`

Putting the pieces together, here is what happens to a provider invocation from the
caller's point of view.

**Lowering time.** Every provider invocation is hoisted: the call leaf is replaced
with a reference into `context.providers.<id>`. The surrounding projection and
comparison were already ordinary Cedar, so they lower natively — an index `["k"]`
becomes `.k`, and the comparison stays as whatever Cedar op you wrote. (The
generated field names and the Cedar-schema augmentation this entails are covered in
[The provider schema](10-provider-schema.md).)

**Authorize time.** For each decision event Dogwood builds the Cedar request
context. It passes `context.input` through from the event, evaluates **every**
declared provider field (resolving each argument, then running the provider), and
collects the outputs into a single `context.providers` object keyed by
id. So `context.providers.<id>` holds that provider's evaluated output record, and
Cedar evaluates the (already-lowered) comparison against it.

So you write the *surface* form `Ns::Fn(args).field <cmp> literal`, and
the engine evaluates `context.providers.<id>.field <cmp> literal` against the bound
output. For case `0001_regex_matches_uppercase`, the engine runs the provider, binds `{ matched: … }`, and
Cedar evaluates `.matched == true` — giving `"ABC" → true`, `"abc" → false`,
`"AB12" → false`. For case `0006_set_arg_index_projection`, `document="violent"` scores VIOLENCE at 0.90 so
`.lessThan(0.5)` is false (deny), `document="safe"` scores 0.10 so it is true
(permit), and `document="hateful"` scores VIOLENCE at 0.10 (only HATE is 0.90) so it is
also true (permit).

---

## The provider contract

Provider execution is **unconditional**. A provider invocation belongs to a rule,
but its evaluation is not gated by that rule — not by the rule's action clause, its
principal/resource constraints, its `when`/`unless` conditions, or whether the rule
could fire at all. For every decision event, every provider invocation in the policy set
is evaluated and its output bound into `context.providers`; *Cedar alone* then decides which
policies fire, using its ordinary scope and condition semantics. (Deciding "could
this rule match this event?" before running its provider would mean re-implementing
Cedar's scope semantics inside the provider machinery, so Dogwood does not.)

Three consequences for provider authors:

1. **Providers must be pure.** A provider may run for events its rule has nothing
   to do with, and implementations are free to skip, cache, reorder, or repeat
   evaluations whose results cannot affect the verdicts. A provider must be a
   deterministic function of its arguments with no observable effects. (Replay —
   `dogwood replay` — and checking one engine against another also assume this.)

2. **Any argument may be absent.** On an event whose context or scope entities do
   not carry the fields a provider reads (a different action's input shape, a
   resource type without the attribute), the argument arrives as **Null** — in a
   Rhai script, the unit value `()`. Scripts must be *defensive*: detect unit
   arguments and return a **sentinel** that conforms to the declared `outputType`
   instead of erroring:

   ```text
   fn evaluate(text) {
       if type_of(text) == "()" {
           return #{ length: -1 };
       }
       #{ length: text.len() }
   }
   ```

   Choose the sentinel deliberately, and mind the **polarity trap**: a sentinel
   that makes a guard false is the *restrictive* direction under `permit` (the rule
   doesn't fire) but the *permissive* direction under `forbid` (the denial doesn't
   fire). Pick the sentinel that fails safe for the polarity of the rules reading
   it.

3. **An erroring provider is undefined behavior.** If a provider evaluation errors
   (a script that throws, an external resolver that fails), the decision outcome
   carries no guarantees. This reference interpreter fails closed: it denies the
   request and reports the error in the response's diagnostics. That is an
   implementation choice, not a contract — other implementations, or future
   versions of this one, may avoid the error entirely (and reach a different
   verdict) or handle it differently. A policy set
   whose safety depends on an erroring provider denying is incorrect on **every**
   implementation, including this one. Defensive scripts (point 2) are the only
   defense.

The same contract applies to external providers supplied through a
`ProviderResolver`: pure, tolerant of Null arguments, never relying on error
behavior.

---

## How it composes with the rest of a policy

Providers slot into the same rule structure as everything else. A rule scopes a
principal, action, and resource in the usual
Cedar way (see [The policy language](02-policy-language.md)), and the provider call
lives in an ordinary `when { … }` clause, freely combined with plain Cedar conditions
and with other providers.

The companion feature is temporal expressions, written with `when temporal { … }` —
see [Temporal expressions](04-temporal-expressions.md). Where a provider computes a
value for the *current* request, a temporal expression reasons about the *history* of
requests. Both are lowered into ordinary Cedar the engine can evaluate.

---

## Advanced features

Two provider features exist but most policies do not need them, and both are
documented on the declaration-side page, [The provider schema](10-provider-schema.md):

- **The `guardrails { … }` clause** — `when guardrails { E }` is transparent sugar
  for a bare `when { E }`; the tag carries no semantics and is retained for
  compatibility with existing policies. You can call a provider from an ordinary
  `when` just as well.
- **Output methods and no-implementation providers** — post-processing a provider's
  output with a declared method (`Provider::Fn(args).method(…)`), and declaring a
  provider with *no* implementation so its value is supplied by your own code.

See [The provider schema](10-provider-schema.md#advanced-and-undocumented-features)
for both.

---

## See also

- [The provider schema](10-provider-schema.md) — declaring a provider: the
  `providers.json` format, the Rhai implementation contract, and the advanced
  features above.
- [The policy language](02-policy-language.md) — rule structure and the Cedar
  condition language a provider call lives in.
- [Temporal expressions](04-temporal-expressions.md) — the companion feature,
  reasoning about request history.
- [Calling macros](09-calling-macros.md) — the other way to reuse logic across policies.
- [The API and workflow](07-api-and-workflow.md) — wiring provider declarations
  into a `ServiceSchema` (`ServiceSchemaBuilder::providers`) and the authorize-time
  flow that evaluates providers.
