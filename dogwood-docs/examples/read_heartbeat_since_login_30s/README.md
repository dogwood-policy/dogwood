# read_heartbeat_since_login_30s

`since` with a short (seconds) window: the anchor must be recent enough, or the
streak does not count. Permit a `Read` only if a `Heartbeat` by the same user
has held continuously **since** a `Login` anchor within the last **30 seconds**
(`since within 30s`, with the user pinned via `input.user: context.input.user`).

The trace (lifted from corpus `0184_since_window_anchor_too_old`) shows the
anchor aging out of the 30s window:

- `@0` — alice logs in (the `since` anchor).
- `@10`, `@20`, `@30` — alice sends Heartbeats, keeping the streak alive.
- `@32` — alice Reads. The only `Login` is now 32s old, past the 30s window, so
  the anchor no longer counts → **deny**.
- `@50` — another Heartbeat, but still no fresh `Login`.
- `@52` — alice Reads again; the anchor is 52s old → **deny**.

Every timepoint denies. Non-`Read` events (`Login`, `Heartbeat`) deny because
the permit only applies to `action == Read`; the `Read` events deny because the
`Login` anchor has aged past the 30s window. This all-deny outcome is the point
the guide illustrates: a short `since` window makes the anchor's freshness the
deciding factor.

Referenced by `guide/04-temporal-expressions.md`.
