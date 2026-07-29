# 0009 — Unwrapped provider (no `guardrails { … }` marker)

The information-provider feature **without the block wrapper**. The
provider call sits directly inside an ordinary Cedar `when { … }`:

```
permit (...) when {
    Content::Filter(context.input.document, ["VIOLENCE", "HATE"])["VIOLENCE"].severityScore.lessThan(decimal("0.5"))
};
```

This is byte-for-byte the reference guardrail surface — a bare `Ns::Fn(args)`
call whose name is a **declared** provider (`providers.json`), with the
projection (`["VIOLENCE"].severityScore`) and comparison
(`.lessThan(decimal("0.5"))`) written as plain Cedar. cedarify recognizes
the declared-provider call, hoists just that leaf to
`context.providers.p_N`, and lowers everything around it natively.

The policy, provider, schema, trace, and verdicts are identical to case
0006 (which uses the `guardrails { … }` wrapper) — demonstrating the two
forms are equivalent. `"violent"` → deny, `"safe"` → permit, `"hateful"`
→ permit.

> An **undeclared** `Ns::Fn(...)` call is still an error, so recognition
> is opt-in via the declarations — a typo can't silently become a
> provider reference.
