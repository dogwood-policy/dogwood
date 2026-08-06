# alert_pending_transfers

Aggregate-vs-aggregate comparison (parenthesized left, bare right): permit an
`Alert` when there are **more `Transfer` requests than responses** in the last
hour — i.e. some transfers are still pending.

The left `count for (t: Timepoint). where (…)` aggregate is parenthesized so its
greedy `where` body does not swallow the `<` operator; the right aggregate is
rightmost so it needs no parens.

World: `drupe`. Schema lifted from the `temporal_only` corpus case
`ea_0014_agg_vs_agg` (has the `Transfer` and `Alert` actions). Default event
schema; no trace.

Referenced by `guide/04-temporal-expressions`.
