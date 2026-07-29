# read_login_not_logout

The accepted **"A but not B"** idiom with **restrictor-first conjunct ordering**.
A guarded negation (`!B`) restricts nothing, so it is legal only when a
*preceding* conjunct in the same `&&` chain already range-restricts its free
variables. Here the restrictor comes first:

```
formerly within 1h Login{ input.user: context.input.user }   // restrictor
&& !Logout{ input.user: context.input.user }                 // guarded negation, after
```

Permit a `Read` only if the same user logged in within the last hour and has not
since logged out. (Reversing the two conjuncts — negation before its restrictor —
is the rejected form.)

The `!Logout` conjunct is an anti-join at the *decision timepoint*: the decision
event is always a `Read`, so what drives the verdict in this trace is the
`formerly within 1h Login` restrictor.

The trace shows both an allow and a deny:

- `@0` — alice logs in (a `Login` event; no `Read` permit applies) -> **deny**.
- `@100` — alice reads 100s after login (login still inside the 1h window) -> **allow**.
- `@4000` — alice reads 4000s after login (login now outside the 1h window) -> **deny**.
- `@4100` — bob reads with no prior login -> **deny**.

Referenced by `guide/04-temporal-expressions.md` (line 525, the accepted
restrictor-first example).
