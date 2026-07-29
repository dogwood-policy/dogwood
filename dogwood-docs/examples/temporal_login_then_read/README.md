# temporal_login_then_read

Two `def temporal` **condition** macros joined with `&&` inside a single
`when temporal { … }` block. Permit `Write` only when the same user both
**recently logged in** (`recently_logged_in`) **and** recently read the same
document (`recently_read`) — each a `formerly within 1h` wrapper.

The trace shows both outcomes:

- `@0` — alice `Login` (history-only; not a `Write`, so **deny**).
- `@10` — alice `Read` doc1 (history-only; not a `Write`, so **deny**).
- `@20` — alice `Write` doc1 → **allow** (both macros hold: logged in within 1h
  and read doc1 within 1h).
- `@30` — alice `Write` doc2 → **deny** (logged in, but never read doc2, so
  `recently_read` fails).
- `@40` — bob `Write` doc1 → **deny** (bob never logged in and never read, so
  both macros fail).

Referenced by `guide/06-macros.md`.
