# `dogwood-language` integration

`dogwood-lsp` and `dogwood-language` are sibling packages in this
Cargo workspace. The LSP calls the language crate's public parser, lowering,
validator, and `syntax` APIs at the same source revision. The LSP owns project
resolution, resource limits, and projection from UTF-8 byte spans to UTF-16 LSP
ranges. It contains no editor extension or Dogwood grammar files.

## Production boundary

`dogwood-lsp/src/frontend.rs` invokes `dogwood-language` in memory and
never launches the `dogwood` CLI:

1. Build a `ServiceSchema`, using defaults for omitted event schema, providers,
   and macros.
2. Parse the Cedar action schema into a `PolicySchema`.
3. Parse and macro-expand the policy with `ParsedPolicySet::parse`.
4. Lower it against the action schema.
5. Run `Validator` and preserve Dogwood finding order and metadata.

The adapter owns LSP-specific concerns that do not belong in the language
crate:

- source-kind attribution across bundle inputs;
- serializable report data transfer objects;
- the pre-parse resource envelope; and
- later projection from UTF-8 byte labels to UTF-16 LSP ranges.

## Structural syntax spans

`dogwood-language::syntax` is the shared parser-backed syntax boundary. It
returns editor-neutral `SyntaxSpan` values with UTF-8 byte ranges, semantic
kinds, and an optional declaration modifier.

The language crate owns the canonical policy, temporal, and event-schema Pest
grammars. Its syntax walkers consume those grammars directly and do not expose
Pest `Rule` values, parser structs, or private Dogwood AST nodes. Dogwood LSP
maps the neutral kinds to its frozen semantic-token legend.

Some temporal keywords are literals rather than named Pest pairs. The syntax
walker derives their ranges from an already accepted canonical parse tree:

- prefixes such as `formerly`, `previous`, `within`, `exists`, `tp`, `sum`,
  `count`, `for`, `decimal`, and `context`; and
- trivia-aware gaps containing `since` or `where`.

`dogwood-lsp` contains no Pest grammar files. All structural spans derive from
grammars owned by `dogwood-language`, preventing copied grammar files from
drifting from parser acceptance.

Policy syntax spans are used only after the strict frontend accepts the policy
and its resolved service inputs. Event-schema syntax spans are used only after
the public service-schema builder accepts the source. Any strict-frontend
failure, structural parse failure, invalid range, overlap, or token limit
discards the structural result; the tolerant lexical stream remains available.

## Operational resource envelope

Before invoking recursive Dogwood frontend code, the LSP adapter limits:

| Resource | Limit |
|---|---:|
| Bytes in one source | 1 MiB |
| Mixed delimiter nesting | 32 |
| Tokens in one structural expression segment | 512 |
| Unary/member/postfix chain length | 31 |

An exceeded limit is reported as an LSP operational-limit diagnostic, not as a
Dogwood parse or validation finding. The depth limits derive from
`dogwood_language::DEFAULT_MAX_DEPTH` (32), the deepest finished tree Dogwood returns
at the default limit, which the LSP parses with: the
nesting limit equals it, and a chain of 31 nodes puts its operand at depth 32.
Dogwood itself refuses anything deeper, such as a run of 33 `&&` terms, as a
parse error.

## Differential tests

The test suite compares the in-memory adapter with the sibling workspace
`dogwood validate --format json` implementation. The test harness locates the
`dogwood-cli` binary with `escargot`; it does not clone another repository,
pin a detached revision, or require environment variables.

Fixtures retained under `tests/fixtures/` include locally authored edge cases
and historical Dogwood corpus snapshots. Their role is regression coverage,
not a production compatibility pin. Changes to the language and LSP are
validated together by the workspace build.
