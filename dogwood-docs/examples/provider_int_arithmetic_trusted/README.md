# provider_int_arithmetic_trusted

A provider's **integer output used inside arithmetic**, mixed under `&&` with a
plain Cedar condition on `context.input` — something only the *unwrapped* form
allows (the closed `guardrails { … }` grammar cannot express it).

`Strings::DigitCount(context.input.document).count` counts `[0-9]` characters in
the document, and the guard is "trusted **and** at most two digits"
(`count + 1 <= 3` ⇔ `count <= 2`):

| trusted | document | digits | verdict |
|---------|----------|--------|---------|
| true    | `ab`     | 0      | ALLOW   |
| true    | `a1b2`   | 2      | ALLOW   |
| true    | `a1b2c3` | 3      | DENY    |
| false   | `ab`     | 0      | DENY    |

The `Strings::DigitCount` provider is declared in `providers.json`. Because the
`dogwood` CLI parses `providers.json` without resolving external `scriptFile`
references, the Rhai implementation (originally `digits.rhai`) is **inlined**
into the `script` field of the declaration. `digits.rhai` is kept alongside for
readability.

Schema, provider declaration, and Rhai script are lifted from corpus case
`0010_unwrapped_mixed_with_cedar`; the schema's `ReadInput` carries an extra
`trusted: Bool` field so the plain Cedar condition has something to read.

Reproduce:

```
dogwood validate policy.dw --policy-schema schema.cedarschema --providers providers.json
dogwood replay  policy.dw --policy-schema schema.cedarschema --providers providers.json --trace trace.log
```

Run with the bundle directory as the working directory.

Referenced by `guide/05-information-providers.md`.
