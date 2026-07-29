# 0002 — Narrowing a permit with `when`

Example 0001 permitted every `GetStockInfo` invocation. Real
policies usually want to permit only *some* invocations of a
tool — those that meet a constraint on the request. That's what
a `when` clause does.

```
permit (
    principal,
    action == Drupe::Action::"SellShares",
    resource
)
when {
    context.input.shares < 100
};
```

It says: permit `SellShares`, but only when the request asks to
sell fewer than 100 shares. Any `SellShares` request asking for
100 or more shares would not be matched by this rule, so the
default deny would apply.

A few new things to notice:

- A rule can carry one or more **clauses** between the scope and
  the terminating semicolon. The first clause we've seen is
  `when { ... }`. Its body is a boolean expression evaluated
  against the request currently being decided.
- **`context.input.X`** is how a clause refers to fields the tool
  was invoked with. The `SellShares` schema declares `shares` as
  an integer input, so `context.input.shares` is an integer.
- **Comparisons** like `<`, `<=`, `==`, `!=`, `>`, `>=` are
  available on numeric and equality-comparable values.

The `when` clause is just one of three condition forms a rule
can carry. The other two — `when temporal { ... }` for
trace-history checks and `when guardrails { ... }` for
classifier-driven checks — appear in later examples.
