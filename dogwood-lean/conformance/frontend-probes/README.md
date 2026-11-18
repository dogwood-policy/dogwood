# Frontend probes

Bundles for the frontend harness (`conformance/frontend-run.sh`, group `FrontendProbes`) that
exercise what the corpus does not: stable policy ids, distincters, several policy sets lowered
together, and Cedar's JSON of annotated schemas. Only the frontend export reads them; the
conformance run (`conformance/run.sh`) does not.

A bundle directory holds the files of a corpus bundle (`policy.dw`, `schema.cedarschema`, …)
and optionally:

- `ids.json`: the stable-id source the public pipeline assigns ids with, `"annotation"` or an
  array of explicit ids (`ParsedPolicySet::with_ids`);
- `distincter.txt`: the distincter it lowers under (`lower_with_distincter`);
- `many.json`: `{"entries": [{"policy": FILE, "distincter": D, "ids": null | "annotation" |
  [ID, …]}, …]}`, several policy sets lowered together over the bundle's schemas
  (`lower_many`), in place of `policy.dw`.

Each `policy.dw` (or entry file) starts with a comment saying what it probes: `ids_*` the id
assignment and each of its errors (two `@id`s on a rule among them), `distincter_*` the
distincters (one with white space around it and one with a comment after it, both rejected, and
one a keyword), `many_*` the multi-entry lowering and each error it can return with the entry it
belongs to, `schema_*` the JSON form of annotations and nested namespaces, `escape_*` strings,
entity and action ids, patterns, annotations and provider arguments with characters Rust's
`escape_debug` and `{:?}` write as `\u{…}` (in the rules' text, their revisions and the
validator's messages).

The groups `ManyTemporal`, `ManyProviders` and `ManyMixed` are made by the bridge from corpus
bundles (`--many K`): each multi-entry bundle takes the schemas of its first directory, one entry
per directory, distincters `e0`, `e1`, …, and explicit ids for every second entry.
