# The Provider Schema

This page is the advanced deep dive on **defining** an information provider — the
`providers.json` declaration format and the Rhai implementation contract a service
author writes to make a provider available to policies. **Calling** a provider from a
policy (the invocation syntax, arguments, projection, and comparison) is covered in
[Information providers](05-information-providers.md); this page is the other half: what
you write so that such a call resolves. The corpus cases named below are directories
under `dogwood-language/tests/passing/provider_only/corpus/`.

> A note on naming: an information provider is invoked as an ordinary Cedar call (`Provider::Name(args)…`), optionally inside a `guardrails { … }` clause (which is just sugar for a bare `when`). Throughout the docs we call these things *providers* when we mean the declared functions and speak of *guardrails* clauses when we mean the sugar. The internal name "provider" is what the declarations and `context.providers` use; there is no dedicated provider grammar.

---

## The `providers.json` declaration format

Providers are declared in a JSON document — a provider declarations file,
conventionally `providers.json`. It is optional and defaults to empty. Making providers
a *file* — rather than baked-in Rust — is what lets a deployment add a provider by
editing configuration, with no code change. The top level is a single object,
`availableProviders`, whose keys are the fully-qualified provider names (`Ns::Fn`) —
the same names you invoke in policies — and whose values describe each provider's
argument types (`argumentTypes`), output type (`outputType`), and implementation
(`implementation`).

### The declaration of a single provider

Each provider declaration has three parts:

- **`argumentTypes`** — an ordered list of `ParamType` entries, one per positional
  argument. May be empty.
- **`outputType`** — a single `ParamType` describing the record (or scalar) the
  provider returns. This field is **required**.
- **`implementation`** — optional. If omitted, the declaration is interface-only (it
  describes the shape but cannot be evaluated). If present, it currently must be a
  Rhai implementation.

### `paramType` variants and their Cedar types

A `ParamType` always has a `paramType` string, and — depending on its kind — a
`fields` map (for records), an `items` type (for sets), and a `required` list (for
records). The `paramType` values and how they map to Cedar types:

| `paramType`        | Cedar type      | Notes                                             |
|--------------------|-----------------|---------------------------------------------------|
| `string`           | `String`        |                                                   |
| `integer` / `long` | `Long`          | synonyms                                          |
| `bool` / `boolean` | `Bool`          | synonyms                                          |
| `decimal`          | `decimal`       | Cedar decimal extension                           |
| `set`              | `Set<inner>`    | inner comes from `items`, defaults to `String`    |
| `record`           | `{ f?: T, … }`  | each field required-or-optional per `required`    |
| any other (unknown)| `String`        | permissive fallback                               |

For a `record`, each field is rendered as `name: T` if `name` is listed in `required`,
otherwise `name?: T` (optional). Records and sets nest.

### Choosing the implementation: inline `script` vs `scriptFile`

The `implementation` object is tagged by `kind`. The only kind today is `"rhai"`, and
it can carry the script two ways:

- **`script`** — the Rhai source inline as a JSON string.
- **`scriptFile`** — a path to an external `.rhai` file, resolved relative to the
  `providers.json` file's own directory.

You use exactly one of these. The inline form (the same `Http::Fetch` provider used
in [The `net` feature and `http_get`](#the-net-feature-and-http_get) below) looks like:

```json
{
  "availableProviders": {
    "Http::Fetch": {
      "argumentTypes": [
        { "paramType": "string" },
        { "paramType": "string" }
      ],
      "outputType": {
        "paramType": "record",
        "fields": { "body": { "paramType": "string" } },
        "required": ["body"]
      },
      "implementation": {
        "kind": "rhai",
        "script": "fn evaluate(base, key) { if regex_is_match(\"^[a-z0-9_-]+(\\\\.[a-z0-9_-]+)*$\", key) { #{ body: http_get(base + \"/lookup/\" + key) } } else { #{ body: \"\" } } }"
      }
    }
  }
}
```

The `scriptFile` form appears in the `Content::Filter` declaration below (which
points `"scriptFile": "filter.rhai"` at an external script), and in the
`Strings::Matches` provider whose declaration references an external `matches.rhai`.

### `from_json` vs `from_json_file`

How you load `providers.json` determines whether a `scriptFile` reference gets
resolved. (These are API entry points; see
[The API and workflow](07-api-and-workflow.md) for the full loading surface.)

- **`from_json(text)`** parses JSON text only. A `scriptFile` reference is left
  **unresolved** — the inline `script` stays `None`.
- **`from_json_file(path)`** reads the file and then, for every Rhai implementation
  that has a `scriptFile` but no inline `script`, reads that file (relative to the
  declarations file's directory) and folds its contents into the script. After
  loading this way, the resolved script is available regardless of which form was
  used.

This matters at authorize time: if a provider declared with `scriptFile` was loaded
via `from_json` instead of `from_json_file`, evaluating it fails with an error telling
you the `scriptFile` reference was never resolved and to load with `from_json_file`.
Rule of thumb: when your declarations reference external `.rhai` files, load with
`from_json_file`.

### More declaration shapes

The corpus exercises the full range of output types. A few representative shapes:

- **Integer output** (`Strings::Length`, case `0002_length_threshold`): `argumentTypes: [{string}]`,
  `outputType` a record with `length: integer`, required.
- **Decimal output** (`Content::Risk`, case `0003_decimal_score_method`): `outputType` a record with
  `severityScore: decimal`, required.
- **Multi-field record output** (`Regex::Analyze`, case `0005_regex_operations`): a record with
  `is_match: bool`, `first_match: string`, `count: integer`, all required.
- **Two providers in one file** (case `0004_two_providers_and_not`: `Strings::Matches` + `Lists::Blocked`;
  case `0007_boolean_or_parens`: `Lists::Allowed` + `Strings::Length`) — just add more keys under
  `availableProviders`.

The most elaborate is `Content::Filter` (cases `0006_set_arg_index_projection` / `0009_unwrapped_no_marker`), which takes a string
and a set of strings, and returns a nested record whose keys are content categories:

```json
{
  "availableProviders": {
    "Content::Filter": {
      "argumentTypes": [
        { "paramType": "string" },
        { "paramType": "set", "items": { "paramType": "string" } }
      ],
      "outputType": {
        "paramType": "record",
        "fields": {
          "VIOLENCE": {
            "paramType": "record",
            "fields": { "severityScore": { "paramType": "decimal" } },
            "required": ["severityScore"]
          },
          "HATE": {
            "paramType": "record",
            "fields": { "severityScore": { "paramType": "decimal" } },
            "required": ["severityScore"]
          }
        },
        "required": ["VIOLENCE", "HATE"]
      },
      "implementation": { "kind": "rhai", "scriptFile": "filter.rhai" }
    }
  }
}
```

### How invocations are validated against declarations

When Dogwood validates a policy against its declarations, it checks each provider
invocation:

1. The invocation's name (`Ns::Fn`) must be present in `availableProviders`, or you
   get "provider is not present in the provider declarations."
2. The argument **count** must equal the declared `argumentTypes` length, or you get
   "expects N argument(s) but got M."
3. Each **directly-typed** argument's kind must match the declared `paramType`:
   `String` → `string`; `Integer` → `integer`/`long`; `Decimal` → `decimal`;
   `Bool` → `bool`/`boolean`; `Set` → `set`. A mismatch reports the
   actual-vs-declared types.
4. Each **output method** in a chain is checked: it must be declared in the
   provider's `availableMethods`, must not shadow a Cedar extension-method name,
   must be given the declared argument count/types, and — when it declares an
   `inputType` — must be fed a compatible value by the preceding pipeline stage.

Field-path arguments (`context.input.x`, `principal.id`, …) are **not**
type-checked here — they are deferred to Cedar/temporal schema validation, since
their type comes from the schema. Likewise, the output projection and comparison
are not re-checked in this pass: they were lowered to native Cedar, so Cedar's own
schema validator checks them against the synthesized `context.providers` type.

---

## The Rhai implementation contract

A provider's implementation is a script in [Rhai](https://rhai.rs/), evaluated in a
tightly sandboxed engine. The contract is simple.

### The `evaluate` function

The script must define a function `fn evaluate(arg0, arg1, …) { … }` whose parameters
correspond **positionally** to the declared `argumentTypes`. It returns a value
matching the `outputType` — typically a Rhai object map (`#{ … }`), which Dogwood
converts into a Cedar record.

The simplest possible script — `length.rhai` (case `0002_length_threshold`). Note that even the
simplest script carries a **unit-argument guard**; that guard is part of what
"simplest" means here, not an optional refinement:

```rhai
fn evaluate(text) {
    // Defensive per the provider contract: a provider may be evaluated
    // for ANY decision event, so any argument may be absent (unit).
    // Return a conforming sentinel instead of erroring (errors are UB).
    if type_of(text) == "()" {
        return #{ length: -1 };
    }

    #{ length: text.len() }
}
```

### Defensive scripts

Provider execution is **unconditional** (see
[the provider contract](05-information-providers.md#the-provider-contract)):
your script runs for every decision event, including events of actions whose
context has none of the fields your arguments read. On such events the
argument arrives as the Rhai **unit** value `()`. Every script must therefore:

- **detect** absent arguments — `type_of(x) == "()"` — and
- **return a sentinel** conforming to the declared `outputType` instead of
  letting an operation on `()` throw. An erroring provider is *undefined
  behavior* for the decision outcome.

Choose the sentinel deliberately and mind the polarity: a sentinel that makes
a guard false is the restrictive direction under `permit` but the
**permissive** direction under `forbid`. Every corpus script carries this
guard; the examples below **elide it for brevity** with a comment marking
where it belongs.

Note that parameter *order* follows the declared `argumentTypes`, not any host
function's order. In `matches.rhai` the parameters are `(text, pattern)` — matching
the declared arguments (arg0 is the `context.input.document` field, arg1 is the
literal pattern) — even though the host function `regex_is_match` takes its arguments
as `(pattern, text)`:

```rhai
fn evaluate(text, pattern) {
    // … unit-argument guard elided — see "Defensive scripts" above …
    #{ matched: regex_is_match(pattern, text) }
}
```

### The sandbox

Providers run in the request path and may be re-evaluated on replay, so they must be
**deterministic** and side-effect-free. Dogwood enforces this with a locked-down,
shared, immutable engine (built once and reused). The key constraints:

- The engine is built from a **raw** Rhai engine, and only the **pure** subset of
  Rhai's standard library is registered — core operations, logic, basic math, arrays,
  maps, bit fields, and more-string functions.
- The time package is **deliberately excluded**, so clock-reading functions like
  `timestamp()` are not reachable. This keeps the engine deterministic.
- Operation and call-depth caps guard against runaway loops and deep recursion
  (one million operations; 64 call levels).
- Module loading is disabled — a script cannot pull in other code or files.
- There is **no ambient file, network, or process access**. A bare Rhai engine cannot
  do I/O at all; the *only* capabilities a script has are the host functions Dogwood
  explicitly registers.

Pure facilities — arithmetic, strings, arrays, maps, `for` iteration, `len()`, and so
on — are all available.

### Host functions

Three regex host functions are **always** registered (they are pure — no I/O):

- `regex_is_match(pattern, text) -> bool` — does `pattern` match `text`? Returns
  `false` on an invalid pattern.
- `regex_find(pattern, text) -> string` — the first match, or `""` if none (or if the
  pattern is invalid).
- `regex_count(pattern, text) -> i64` — the number of non-overlapping matches (`0` on
  an invalid pattern).

All three appear together in `analyze.rhai` (case `0005_regex_operations`):

```rhai
fn evaluate(text, pattern) {
    // … unit-argument guard elided — see "Defensive scripts" above …
    #{
        is_match:    regex_is_match(pattern, text),
        first_match: regex_find(pattern, text),
        count:       regex_count(pattern, text),
    }
}
```

A provider does not have to call any host function at all — pure Rhai is often enough.
The denylist in `blocked.rhai` (case `0004_two_providers_and_not`) uses only a built-in `contains`:

```rhai
fn evaluate(text) {
    // … unit-argument guard elided — see "Defensive scripts" above …
    let denylist = ["evil", "badword"];
    #{ blocked: denylist.contains(text) }
}
```

### Decimal support

The engine is built with Rhai's decimal feature, so a script can call
`parse_decimal("0.10")` to produce a decimal, which Dogwood converts to a Cedar
decimal. This is what lets a provider return a `severityScore` that the policy then
compares with `.lessThan(decimal("0.5"))`.

The risk-score provider — `risk.rhai` (case `0003_decimal_score_method`):

```rhai
fn evaluate(text) {
    // … unit-argument guard elided — see "Defensive scripts" above …
    let score = if text == "safe" {
        parse_decimal("0.10")
    } else if text == "spam" {
        parse_decimal("0.80")
    } else {
        parse_decimal("0.50")
    };
    #{ severityScore: score }
}
```

Scripts can also build nested records dynamically. `filter.rhai` (cases `0006_set_arg_index_projection` /
`0009_unwrapped_no_marker`) loops over the requested categories and builds a record keyed by category
name:

```rhai
fn score_for(text, category) {
    if text == "violent" && category == "VIOLENCE" {
        parse_decimal("0.90")
    } else if text == "hateful" && category == "HATE" {
        parse_decimal("0.90")
    } else {
        parse_decimal("0.10")
    }
}

fn evaluate(text, categories) {
    // … unit-argument guard elided — see "Defensive scripts" above …
    let out = #{};
    for category in categories {
        out[category] = #{ severityScore: score_for(text, category) };
    }
    out
}
```

### The `net` feature and `http_get`

Everything above keeps providers deterministic. Network access breaks that — so it is
gated behind an **off-by-default `net` feature**. When Dogwood is built with `net`, one
additional host function is registered:

- `http_get(url) -> string` — a blocking HTTP GET that returns the response body on a
  2xx, else `""`. It is deliberately minimal: `http://host[:port]/path` only, with
  **no TLS, no redirects, no chunked decoding**, short (5-second) timeouts, and a 1 MiB
  response cap, on a plain blocking socket.

This is the one thing that makes the engine non-deterministic, which is exactly why it
is opt-in. In spirit it is like OPA/Rego's `http.send`. Use it with care: the same
policy can reach different decisions if the network response changes.

> **Security — SSRF: never build the URL from an untrusted event field.** `http_get`
> performs **no** host validation: it connects to whatever host the URL names,
> including internal/link-local addresses (`169.254.169.254`, `127.0.0.1`, RFC-1918).
> The naive script `fn evaluate(url) { #{ body: http_get(url) } }`, invoked as
> `WebGet(context.input.url)`, hands the *whole URL* to the request — so a caller can
> steer the fetch to *any* endpoint the Dogwood process can reach (a server-side
> request forgery). The safe pattern: **keep the base URL a fixed, deployer-owned
> literal, and let a request field fill only a validated, non-authority path segment.**

The `net` example follows that pattern. It declares `Http::Fetch(base, key) -> { body: String }`
whose script validates the request-supplied `key` against a strict allowlist before
interpolating it into a fixed path, and only then fetches:

```text
fn evaluate(base, key) {
    // Dot-separated allowlisted tokens: ordinary keys like `page.html` are fine,
    // but `/`, `@`, `:`, whitespace, CRLF — and `..` — are rejected, so `key`
    // cannot change the authority or traverse out of the `/lookup/` segment.
    if regex_is_match("^[a-z0-9_-]+(\\.[a-z0-9_-]+)*$", key) {
        #{ body: http_get(base + "/lookup/" + key) }
    } else {
        #{ body: "" }        // reject: fail safe, never fetch
    }
}
```

The policy passes a **literal** base URL (deployer-owned) and only a validated `key`
from the request — never a URL:

```text
when {
    Http::Fetch("http://example.com", context.input.key).body != "BLOCKED"
};
```

Its test starts a loopback mock server (the `base` literal is the mock's runtime
origin): the key `allowed` returns body `"OK"` (permit), the key `blocked` returns
`"BLOCKED"` (deny), and a companion test proves that authority-hijacking keys
(`allowed@attacker.com`, `127.0.0.1:9999`, `allowed/../secret`, CRLF payloads) fail the
allowlist and **never reach the network**.

### Value conversion at the boundary

When Dogwood calls `evaluate`, it converts each resolved argument value into a Rhai
value, and converts the returned value back to a Dogwood value. The mapping is
straightforward: null ↔ unit, bool ↔ bool, integers ↔ int, decimals ↔ decimal (Cedar
decimal text semantics), strings ↔ string, arrays ↔ arrays, and object maps ↔ records
(recursively). A returned value that is none of these — a function pointer, say —
produces the error "script returned an unsupported value type." In practice, return an
object map (`#{ … }`) whose fields match your declared `outputType`.

If a provider has no `implementation`, evaluating it errors ("has no implementation;
cannot evaluate it at authorize time"). Compile errors in the script surface as "script
compile error," and errors thrown while calling `evaluate` surface as "script error
calling evaluate."

---

## How a provider binds to `context.providers.<id>`

Putting the pieces together, here is the full life cycle of a provider invocation.

**At lowering time**, every provider invocation is hoisted. A generated field name
(`p_0`, `p_1`, …) is assigned per invocation, and the call leaf is replaced with
`context.providers.<field>`. The surrounding projection and comparison were already
ordinary Cedar, so they lower natively — an index `["k"]` becomes `.k`, and the
comparison stays as whatever Cedar op you wrote.

Dogwood also **augments the Cedar schema**. EVERY action's `context` record gains
a required `providers` record (matching the unconditional evaluation below — the
declared schema and the runtime context always agree), and each hoisted field is
typed from its provider's declared `outputType`. (The base `schema.cedarschema`
files in the corpus are the un-augmented schemas; the synthetic
`context.providers` record is added during compilation. The base action schema is
described in [The policy language](02-policy-language.md) and the event schema in
[The event schema](03-event-schema.md).)

**At authorize time**, for each decision event Dogwood builds the Cedar request
context. It passes `context.input` through from the event, evaluates **every**
declared provider field (resolving each argument, then running the
Rhai `evaluate`), and collects the outputs into a single `context.providers` object
keyed by field id. So `context.providers.p_N` holds that provider's evaluated output
record, and Cedar evaluates the (already-lowered) comparison against it.

The net effect: you write the *surface* form `Ns::Fn(args).field <cmp> literal`, and
the engine evaluates `context.providers.<id>.field <cmp> literal` against the bound
output. For case `0001_regex_matches_uppercase`, the engine runs `matches.rhai`, binds `{ matched: … }`, and
Cedar evaluates `.matched == true` — giving `"ABC" → true`, `"abc" → false`,
`"AB12" → false`. For case `0006_set_arg_index_projection`, `document="violent"` scores VIOLENCE at 0.90 so
`.lessThan(0.5)` is false (deny), `document="safe"` scores 0.10 so it is true
(permit), and `document="hateful"` scores VIOLENCE at 0.10 (only HATE is 0.90) so it is
also true (permit).

---

## Advanced and undocumented features

Everything above is the supported way to use providers: call them from an ordinary
`when { … }` clause, backed by a Rhai implementation. The two features below exist and
work, but most policies do not need them — treat them as advanced.

### The `guardrails { … }` clause

Besides calling a provider inside an ordinary `when`, Dogwood also accepts a
`when guardrails { … }` clause:

```text
permit ( principal, action == Doc::Action::"read", resource )
when guardrails {
    Strings::Matches(context.input.document, "^[A-Z]+$").matched == true
    && !(Lists::Blocked(context.input.document).blocked == true)
};
```

`guardrails { E }` is **transparent sugar** for a bare `when { E }`: its body is
a full Cedar expression, parsed and lowered identically to an ordinary `when`
clause. The tag adds nothing — it is retained only for surface compatibility
with existing policies. Because the body is
plain Cedar, everything an ordinary `when` can do works here too: arithmetic on
a provider's output, mixing provider calls with plain context conditions,
`if`/`then`/`else`, and so on.

This guide leads with the ordinary `when` form because it is simpler to teach and
there is no reason to prefer the tag. The two forms are exactly equivalent; use
whichever reads better (the tag can document intent — "this clause gates on a
provider" — but carries no semantics).

### Methods on a provider's output

Beyond projecting into a provider's output record (`.field` / `["key"]`), you can call
a **method** on it: `Provider::Fn(args).method(margs)`. A method *post-processes* the
provider's output — the value used in the comparison is `method(output, margs…)` — and
methods **chain** left to right (`.m1().m2()` = `m2(m1(output))`), each producing the
input to the next.

A method is declared on the provider, alongside its output type, in an
`availableMethods` map — each method with its own `argumentTypes` and `outputType`
(exactly mirroring the base invocation):

```json
"BedrockGuardrails::ContentFilter": {
  "argumentTypes": [ { "paramType": "string" } ],
  "outputType": { "paramType": "record", "fields": { "severityScore": { "paramType": "decimal" } } },
  "availableMethods": {
    "maxConfidenceScore": { "argumentTypes": [], "outputType": { "paramType": "decimal" } },
    "scoreAbove":         { "argumentTypes": [ { "paramType": "decimal" } ], "outputType": { "paramType": "bool" } }
  },
  "implementation": { "kind": "rhai", "scriptFile": "content_filter.rhai" }
}
```

and implemented as a `fn <name>(input, args…)` in the provider's single Rhai script —
its first parameter is the previous stage's value (the base output for the first
method), the rest are the method's own arguments:

```text
// content_filter.rhai
fn evaluate(text) { /* … returns the base record … */ }
fn maxConfidenceScore(output)          { /* reduce over output → decimal */ }
fn scoreAbove(output, threshold)       { output.maxConfidenceScore() > threshold }
```

A **zero-argument** method is the common accessor case (`maxConfidenceScore()`); a
method **with arguments** (`scoreAbove(decimal("0.72"))`) is the generalization. In a
policy:

```text
permit ( principal, action == Drupe::Action::"InvokeAgent", resource )
when guardrails {
    BedrockGuardrails::ContentFilter(context.input.prompt).maxConfidenceScore() < 50
};
```

Notes and constraints:

- **Parens distinguish a method from a field.** `.maxConfidenceScore()` (with parens)
  is a method call; `.severityScore` (no parens) is a field projection. A method's name
  may not shadow a Cedar extension method (`lessThan`, `contains`, `isEmpty`, …) —
  those are reserved for the comparison / native forms.
- **Method arguments** use the same forms as invocation arguments — attribute
  paths rooted at `context` / `principal` / `resource`, string / integer /
  decimal / bool literals, and sets — and are resolved against the request
  exactly like the base arguments.
- **Eager vs. Cedar.** A method runs in Rhai at authorize time (it is *not* native
  Cedar), so the value bound into `context.providers.<id>` is the pipeline's result
  after the last method; any field projection *after* the last method (e.g.
  `.classify()["VIOLENCE"].score`) is then plain Cedar over that value. A projection
  may not appear *before* a method in the same chain.
- **Failure is fail-closed.** If a method's Rhai body errors, the decision denies with
  the error in the response diagnostics, like any provider failure.

### Providers with no implementation — plugging in your own code

A provider declaration's `implementation` field is **optional**. If you omit it, the
declaration is **interface-only**: it still names the provider, declares its
`argumentTypes` and `outputType`, and type-checks and lowers exactly like any other
provider — but Dogwood's built-in Rhai evaluator has nothing to run.

```json
{
  "availableProviders": {
    "Risk::Score": {
      "argumentTypes": [ { "paramType": "string" } ],
      "outputType": {
        "paramType": "record",
        "fields": { "severityScore": { "paramType": "decimal" } },
        "required": ["severityScore"]
      }
    }
  }
}
```

This is the hook for supplying the value from **your own code** instead of a Rhai
script. The provider's output is nothing more than a record bound into
`context.providers.<id>` at authorize time; a declaration with no `implementation`
declares the *contract* for that record and leaves the *production* of it to you. If
you evaluate such a provider through the built-in path, you get a clear error —
`provider ... has no implementation; cannot evaluate it at authorize time` — which is
the signal that this provider is meant to be satisfied by a caller-supplied
computation rather than the sandboxed Rhai engine.

Use this when the value comes from somewhere the sandbox deliberately cannot reach — a
service call, a model, a database lookup — and you want to keep that computation in
your own (unsandboxed, non-deterministic-allowed) code while still declaring the
provider's shape so policies can be written and validated against it.

---

## See also

- [Information providers](05-information-providers.md) — calling providers from a
  policy: the invocation syntax, arguments, projection, and comparison.
- [The policy language](02-policy-language.md) — the base action schema and the Cedar
  condition language a provider call lives in.
- [The event schema](03-event-schema.md) — how the base event schema is written before
  Dogwood augments the context with the synthetic `context.providers` record.
- [The API and workflow](07-api-and-workflow.md) — loading declarations (`from_json`
  vs `from_json_file`) and the authorize-time flow that evaluates providers.
- [Macros](06-macros.md) — the other way to reuse logic across policies.
