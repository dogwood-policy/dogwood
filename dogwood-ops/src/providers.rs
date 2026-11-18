//! A guard on provider declarations shared by every binding.
//!
//! An information provider's Rhai script may be given inline (`script`) or as an
//! external file (`scriptFile`) resolved relative to the declarations file. Only
//! `ProviderDeclarations::from_json_file` resolves the latter — it reads the
//! referenced file into `script`. These bindings take declarations as *text*
//! (there is no file to be relative to) — and under `wasm32-unknown-unknown`
//! there is no filesystem at all — so a `scriptFile` reference can never be
//! resolved here.
//!
//! Left alone that is a **false green**: `from_json` accepts the declaration —
//! it is structurally valid — so `checkProviders` reports `ok: true`, and the
//! provider then fails closed at authorize time, turning every policy that calls
//! it into a deny. The check passes and the policy silently stops permitting
//! anything.
//!
//! So every entry point that accepts provider text runs [`parse_declarations`]
//! instead of `from_json` directly, which rejects an unresolvable `scriptFile`
//! up front with an actionable message. This lives outside [`ops`](crate::ops)
//! deliberately: that module is copied from `dogwood-cli`, where `scriptFile`
//! does work.

use dogwood_language::{Implementation, ProviderDeclarations};

use crate::error::OpError;

/// Parse `providers.json` text, rejecting declarations that cannot work when
/// the declarations are given as text.
///
/// Same as `ProviderDeclarations::from_json` plus the `scriptFile` check. The
/// error is an [`OpError`], so callers throw it as an ordinary `DogwoodError`
/// exactly as they already do for malformed provider JSON.
pub fn parse_declarations(json: &str) -> Result<ProviderDeclarations, OpError> {
    let decls = ProviderDeclarations::from_json(json).map_err(OpError::message)?;

    for (name, decl) in &decls.available {
        let Some(Implementation::Rhai { script, script_file }) = &decl.implementation else {
            continue;
        };
        if script.is_some() {
            continue;
        }
        return Err(OpError::message(match script_file {
            // The common, fixable case: porting a `providers.json` written for
            // the CLI. Name the file so the message points at the fix.
            Some(path) => format!(
                "provider `{name}` declares `scriptFile: \"{path}\"`, which these bindings \
                 cannot resolve: they take provider declarations as text, so there is no \
                 declarations file to resolve the path against. Inline the file's contents as \
                 `implementation.script` instead. (Left unresolved the provider would fail closed \
                 at authorize time, denying every policy that calls it.)"
            ),
            // Neither form present. `from_json` allows it because a declaration
            // may legitimately be implementation-less; one tagged `rhai` with no
            // script is just incomplete.
            None => format!(
                "provider `{name}` declares a `rhai` implementation with neither `script` nor \
                 `scriptFile`, so it has no script to run. Supply the script inline as \
                 `implementation.script`."
            ),
        }));
    }

    Ok(decls)
}
