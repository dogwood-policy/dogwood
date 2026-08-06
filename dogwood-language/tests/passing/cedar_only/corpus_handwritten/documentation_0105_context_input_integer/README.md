# 0105 — Reading a `Long` from `context.input`

Example 0002 narrowed a permit with `context.input.shares < 100`.
This case is the same shape with two refinements: it uses `<=`
instead of `<`, and it names the type explicitly. `shares` is
declared as `Long` in the `SellShares` tool schema, and `Long`
is Dogwood's integer type.

```
when {
    context.input.shares <= 1000
};
```

## Integer comparisons

A `Long` field supports the full ordered comparison set:

- `<`, `<=`, `>`, `>=` for ordering
- `==`, `!=` for equality

So `context.input.shares <= 1000` permits requests asking to
sell up to and including 1000 shares; a request for 1001 shares
falls through to the default deny.

## Type-mapping cheatsheet

The shared schema exposes five user-facing scalar types. Each
one determines which operators are legal in a `when` body:

| Schema type | What it is        | Legal operators                              |
|-------------|-------------------|----------------------------------------------|
| `String`    | UTF-8 text        | `==`, `!=`, `like`                            |
| `Long`      | 64-bit integer    | `<`, `<=`, `>`, `>=`, `==`, `!=`              |
| `decimal`   | fixed-point value | `==`, `!=` only (no ordered comparisons)      |
| `Bool`      | true / false      | `==`, `!=`, `&&`, `\|\|`, `!`                  |
| `datetime`  | wall-clock time   | `<`, `<=`, `>`, `>=`, `==`, `!=`              |

`decimal` is the odd one out: ordered comparisons on a decimal
field will fail validation. When a tool returns a decimal
(e.g. `proceeds` on `SellShares`), use it for equality only or
feed it into a temporal `sum` aggregation (later examples).
