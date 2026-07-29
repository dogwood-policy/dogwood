# 0002 — Integer output + operator comparison

Shows a provider whose output is a **number** compared with an ordinary
operator (`<`), rather than a boolean compared with `==`.

- **`providers.json`** declares `Strings::Length` returning
  `{ length: Long }`.
- **`length.rhai`** returns the string length: `#{ length: text.len() }`
  (`len()` is Rhai's built-in; no host function needed).
- **`policy_1.dw`** permits `Read` only when the document id is short —
  `Strings::Length(context.input.document).length < 5`.

So `"abc"` (3) → permit, `"hello"` (5) → deny, `"hi"` (2) → permit.
