# approve_has_output_guard

The `has` attribute-existence guard before reading an optional Bool output
field. `context has output` tests whether the optional `output` attribute is
present, and because `&&` short-circuits, that guard on the left protects the
`context.output.approved == true` read on the right.

Referenced by `guide/02-policy-language.md` — The Policy Language.
