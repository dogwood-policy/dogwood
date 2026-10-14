# Dogwood CLI

`dogwood-cli` builds the `dogwood` binary: a thin command-line shell over
the `dogwood-language` frontend for checking, validating, lowering, and
replaying Dogwood (`.dw`) policies locally. It renders diagnostics as
underlined source snippets for humans, or as JSON (`--format json`) for tools.

Install from crates.io:

```text
cargo install dogwood-cli
```

## Subcommands

```text
dogwood format     POLICIES                      Pretty-print a .dw policy set.
dogwood check-parse POLICIES                      Report syntax and macro errors only.
dogwood validate   POLICIES --policy-schema FILE Type-check policies against the schema.
dogwood lower      POLICIES --policy-schema FILE Lower a .dw policy set to Cedar.
dogwood replay     POLICIES --policy-schema FILE --trace FILE
                                                  Replay a .log event trace, verdict per timepoint.
dogwood explain    POLICIES                      Explain policies in deterministic semi-English.
dogwood schema     <action|event|providers|mcp> Check a schema artifact, or generate one from MCP.
```

Pass `-` as `POLICIES` to read the policy set from stdin. Run
`dogwood <subcommand> --help` for the full argument list.

## Features

- `experimental-arithmetic` — forward the language crate's off-by-default
  arithmetic feature, so a `dogwood` built with it accepts (and warns on)
  policies using arithmetic in temporal comparison operands.
