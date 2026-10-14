# touchless_invoice_within_tolerance

> **EXPERIMENTAL.** This bundle uses arithmetic in temporal comparison
> operands, gated behind the off-by-default Cargo feature
> `experimental-arithmetic`. A default build rejects this policy; the test
> harnesses check this bundle only when built with that feature.

This bundle exercises the `+` operator (tolerance comparisons).

A two-way invoice match with a tolerance: permit `PayInvoice` only when a
completed `CreatePurchaseOrder` (its `response`, not just a request that may
have failed) with the same `po_id` exists in the window and the invoice
amount is at most the PO amount plus 50.

```text
permit (principal, action == Procure::Action::"PayInvoice", resource)
when temporal {
    exists (po_amount: Long). (
        formerly within 24h Procure::Action::"CreatePurchaseOrder"::response{
            input.po_id: context.input.po_id,
            input.amount: po_amount
        }
        && context.input.amount <= po_amount + 50
    )
};
```

Without arithmetic, two correlated event fields can only be compared exactly
(`invoice <= po`); the tolerance constant has nowhere to go.

## Replay

| Decision point | Event | Check | Verdict |
|---|---|---|---|
| `@0` | create po-1 for 1000 | not `PayInvoice` | deny |
| `@10` | invoice po-1 for 1040 | 1040 <= 1000 + 50 | allow |
| `@20` | invoice po-1 for 1100 | 1100 <= 1050 fails | deny |
| `@30` | invoice po-2 for 40 | no po-2 yet, `exists` fails | deny |
| `@40` | create po-2 for 200 | not `PayInvoice` | deny |
| `@50` | invoice po-2 for 240 | 240 <= 200 + 50 | allow |

The history-only responses at `@1` and `@41` record that the two POs were
actually created; they yield no verdicts. Matching the `response` rather
than the `request` means a `CreatePurchaseOrder` call that never completed
would not enable payment.

`@30` shows the tolerance never substitutes for the match: a small invoice
against a nonexistent PO is still denied.

## Files

- `policy.dw`: the permit with the `po_amount + 50` tolerance.
- `schema.cedarschema`: `Procure` action schema (`CreatePurchaseOrder`,
  `PayInvoice`, both with `po_id`/`amount` inputs).
- `trace.log`: two POs (each a request plus its response) and four invoices
  by alice.
- `expected.out`: the per-decision-point verdict stream.

Reproduce (run from this directory):

```
dogwood validate policy.dw --policy-schema schema.cedarschema
dogwood replay   policy.dw --policy-schema schema.cedarschema --trace trace.log
```

World: `procure`. Default event schema; no providers.

Referenced by guide/04-temporal-expressions.md (arithmetic in comparison
operands).
