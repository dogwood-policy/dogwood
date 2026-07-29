# 0001 — A regex information provider

This case shows the whole information-provider feature in one place. Read
the files in this order:

1. **`providers.json`** — the *information-provider schema*. It declares
   one provider, `Strings::Matches`, with its argument types, its output
   type (`{ matched: Bool }`), and — the new part — **how it is
   implemented**: a sandboxed Rhai script referenced by `scriptFile`.

2. **`matches.rhai`** — the provider's implementation (the "external
   code"). It defines `fn evaluate(text, pattern)` and calls the built-in
   `regex_is_match` host function Dogwood exposes to provider scripts.
   Adding or changing a provider is just editing these two files — no
   change to Dogwood itself.

3. **`policy_1.dw`** — a Dogwood policy that *uses* the provider via a
   `when guardrails { … }` clause: it permits `Read` only when the
   `document` matches the regex `^[A-Z]+$` (all uppercase letters).
   (The clause keyword is `guardrails`; the concept is an information
   provider.)

4. **`schema.cedarschema`** — the Cedar schema for the `Read` action.
   (At lower time Dogwood augments this with a synthetic
   `context.providers` record typed from `providers.json`; the file here
   is the un-augmented base.)

5. **`trace_1.log`** — a sequence of request events. Each line is
   `@<ts> <Action>_request(<field>: <value>, …)`. The `document` field is
   what the provider inspects.

6. **`expected_1.out`** — the expected verdict stream: one
   `@<ts> (time point <i>): true` line per Allow. Requests whose document
   is all-uppercase are permitted; the rest are denied (absent).

## What happens at authorize time

For each request, the engine runs `matches.rhai`'s `evaluate` with the
resolved arguments (`document`, then the literal pattern), binds the
returned record into `context.providers.<id>`, and lets Cedar evaluate
the `.matched == true` comparison. So `"ABC"` → permit, `"abc"` → deny,
`"AB12"` → deny.
