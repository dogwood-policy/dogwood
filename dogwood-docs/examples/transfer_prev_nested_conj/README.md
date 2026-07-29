# transfer_prev_nested_conj

`previous`'s body must be a single atom, so a conjunction has to be
parenthesized. This policy permits an `Drupe::Action::"Transfer"` only when
the immediately preceding event (within 2h) was a `Login` by the **same user**
(`input.user: context.input.user`) **and** to server `"s1"`
(`input.server: "s1"`) — both conditions grouped inside the parentheses that
form `previous`'s single-atom body.

Schema lifted from the `temporal_only` corpus case
`0268_previous_containing_nested` (`Login` with `user`+`server` input, plus
`Transfer`). Default event schema.

Referenced by `guide/04-temporal-expressions`.
