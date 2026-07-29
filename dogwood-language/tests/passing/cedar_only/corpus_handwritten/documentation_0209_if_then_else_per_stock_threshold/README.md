# 0209 — `if/then/else` picking a numeric threshold

Example 0112 used `if/then/else` to compute a `Bool`. The same
construct can return any type — here we use it to pick a `Long`
threshold per stock symbol, then compare `context.input.shares`
against it.

```
when {
    context.input.shares <=
        (if context.input.stock == "AMZN" then 10
         else if context.input.stock == "MSFT" then 50
         else 1000)
};
```

Reading: AMZN sales are capped at 10 shares, MSFT at 50, and
everything else at 1000. The `if`-chain produces a single `Long`
value, which `<=` then compares with the requested `shares`.

## Branches must agree on type

Every branch of an `if/then/else` has to produce the same type.
Here all three arms return `Long`, so the whole expression is
`Long` and slots into the `<=` comparison. Mixing a `Long` arm
with, say, a `decimal` or `String` arm would fail validation.
The `else` is mandatory — there is no implicit default.
