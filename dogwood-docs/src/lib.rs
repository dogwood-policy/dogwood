//! `dogwood-docs` — the Dogwood documentation crate.
//!
//! This crate holds the language guide (`guide/*.md`) and the **complete,
//! runnable example bundles** the guide's policy-level examples are drawn from
//! (`examples/<name>/`). A bundle is a self-contained directory — a `.dw`
//! policy, its `.cedarschema` action schema, and optionally a `.dwschema`
//! event schema, `providers.json` + `.rhai`, a `.log` trace, and an
//! `expected.out` verdict stream.
//!
//! The crate has no code of its own to speak of. Its purpose is the **test
//! harness** in `tests/`, which runs every bundle through the `dogwood` CLI
//! binary: each bundle is `dogwood validate`d (and, when it has a trace,
//! `dogwood replay`ed and compared to `expected.out`). A doc example that stops
//! parsing, validating, or replaying as intended therefore fails the build —
//! the documentation cannot drift from the language.
//!
//! See `guide/README.md` for the guide itself and `examples/README.md` for the
//! bundle format.

/// The relative path (from this crate's manifest dir) to the example-bundle
/// root. The harness joins this with `CARGO_MANIFEST_DIR`.
pub const EXAMPLES_DIR: &str = "examples";

/// The relative path (from this crate's manifest dir) to the guide.
pub const GUIDE_DIR: &str = "guide";
