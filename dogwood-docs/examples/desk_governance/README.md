# desk_governance

A four-policy trading-desk set combining most of the language in one place:

1. `permit_sell_open_session_rate_limited` — a trader may sell only with an
   **open session** (`!Logout since Login`), an **approval** for the same stock
   within the last hour (`formerly`), and at most three sales in the last hour
   (a `count` rate limit).
2. `forbid_insider_notes` — a **provider guardrail**: the `Text::Scan`
   information provider (`providers.json`) flags notes mentioning "insider".
3. `forbid_sell_amzn` — a **deny-overrides** carve-out for AMZN.
4. `permit_admin_approve` — an admin may approve a sale for any stock except
   one they themselves requested to sell in the last hour.

The trace follows alice (all events are hers, as the default event schema
correlates history to the requesting principal):

- `@0` — alice logs in (a `Login` response, history only).
- `@60` — her MSFT sale is approved (an `ApproveSale` response, history only).
- `@120` — alice sells MSFT → **allow** (open session, approved, first sale).
- `@180` — alice sells AMZN → **deny** (`forbid_sell_amzn`; there is also no
  AMZN approval).
- `@240` — alice sells MSFT with notes mentioning an insider tip → **deny**
  (`forbid_insider_notes`).
- `@300` — alice logs out → **deny** (no rule permits `Logout`; the request is
  still recorded in the history).
- `@360` — alice sells MSFT again → **deny**: her session is closed (a `Logout`
  since the `Login`), and this would also be her fourth sale within the hour.
