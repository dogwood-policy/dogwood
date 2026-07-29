# 0004 — Combining two providers with `&&` and `!`

Shows that a `guardrails { … }` body is a boolean expression over multiple
provider atoms, not just one. The policy permits `Read` only when the
document **matches** an allowed-name pattern **and is not flagged** by a
blocklist provider:

```
Strings::Matches(context.input.document, "^[a-z]+$").matched == true
&& !(Lists::Blocked(context.input.document).blocked == true)
```

- **`matches.rhai`** — `Strings::Matches(text, pattern) -> { matched }`
  (regex, same host function as case 0001).
- **`blocked.rhai`** — `Lists::Blocked(text) -> { blocked }`, true when the
  document is in a small hard-coded denylist (`"evil"`, `"badword"`).
- **`providers.json`** declares both; each references its own `.rhai`.

So `"hello"` → matches, not blocked → **permit**; `"evil"` → matches but
blocked → **deny** (the `!` rejects it); `"Hello"` → has an uppercase
letter, fails the pattern → **deny**.
