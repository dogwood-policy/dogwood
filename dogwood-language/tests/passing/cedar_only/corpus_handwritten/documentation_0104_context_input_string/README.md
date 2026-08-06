# 0104 — Reading `context.input` (String field)

## The new idea

When a rule's scope pins a single action with `action ==
Drupe::Action::"Tool"`, the tool's declared input record
becomes available as `context.input` inside the rule's clauses.
Field names and types come straight from `mcp_tools.json`.

`GetStockInfo` declares `input: { stock: String }`, so inside
this rule we can read `context.input.stock` as a `String`.

## Shape

```dogwood
permit(
    principal,
    action == Drupe::Action::"GetStockInfo",
    resource
) when {
    context.input.stock == "AMZN"
};
```

## Notes

String literals in Cedar bodies are double-quoted. Strings
support `==` and `!=` (and `like` for globs); they don't have an
ordering. For ordered comparisons you need an integer field —
see a later case using `context.input.shares`.

Because the rule's scope already restricts to `GetStockInfo`,
the validator knows the exact shape of `context.input` and will
reject typos like `context.input.symbol`. Compare with 0002,
which reads an integer field (`shares`) on a different tool.
