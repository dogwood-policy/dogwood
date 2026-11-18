//! Which implementation of the frontend lowers and validates a policy set: the
//! crate's Rust frontend, or the Lean frontend of `dogwood-lean/` (feature
//! `lean-frontend`), or both, compared.
//!
//! The **frontend** is everything after the parsers: macro expansion, event-schema
//! derivation, lowering to Cedar, schema augmentation, pin injection,
//! relativization, provider resolution, and validation. The parsers are always
//! the crate's. The Lean frontend is a port of the Rust one, proved correct in
//! part (its validator decides the formal specification's validity) and tested
//! against it; with the `lean-frontend` feature the crate links it and a
//! [`ServiceSchema`](crate::ServiceSchema) can select it:
//!
//! ```
//! # use dogwood_language::{Frontend, ServiceSchema};
//! let service = ServiceSchema::builder().frontend(Frontend::Rust).build()?;
//! assert_eq!(service.frontend(), Frontend::Rust);
//! # Ok::<(), dogwood_language::Error>(())
//! ```
//!
//! Every policy set parsed against that service schema is lowered by the selected
//! frontend ([`ParsedPolicySet::lower`](crate::ParsedPolicySet::lower),
//! [`lower_with_distincter`](crate::ParsedPolicySet::lower_with_distincter),
//! [`lower_many`](crate::lower_many), and the one-call forms), and
//! [`Validator::validate`](crate::Validator::validate) validates a lowered set with
//! the frontend that lowered it. See [`Frontend`] for each mode.
//!
//! Without the `lean-frontend` feature only [`Frontend::Rust`] is available: the
//! type and the builder option exist in every build, so that code selecting a
//! frontend compiles either way, but
//! [`ServiceSchemaBuilder::build`](crate::ServiceSchemaBuilder::build) rejects
//! [`Frontend::Lean`] and [`Frontend::Shadow`] with [`Error::Frontend`] (kind
//! [`FrontendErrorKind::Unavailable`]) instead of running another frontend than
//! the one asked for.
//!
//! ## The `DOGWOOD_FRONTEND` environment variable
//!
//! With the `lean-frontend` feature, a service schema built without an explicit
//! [`ServiceSchemaBuilder::frontend`](crate::ServiceSchemaBuilder::frontend) (and
//! [`ServiceSchema::defaults`](crate::ServiceSchema::defaults)) takes its frontend
//! from `DOGWOOD_FRONTEND`: `rust`, `lean`, `shadow` ([`Frontend::Shadow`] with
//! [`OnMismatch::Fail`]) or `shadow-log` (with [`OnMismatch::Log`]); unset or
//! empty is `rust`. Any other value panics, naming the variable, rather than
//! silently running the Rust frontend. This is how the crate's whole test suite
//! runs in each mode unchanged. Without the feature the variable is not read.
//!
//! ## Linking Lean code of your own
//!
//! With the `lean-frontend` feature, the crate's archive is the process's one
//! Lean runtime, and it holds the Lean frontend's library
//! (`dogwood-lean/Dogwood/Frontend/Library.lean` and every module it imports:
//! the pipeline, the validator, the projection onto the specification, the JSON
//! encoding of the parsers' outputs, the identity hashes, and the
//! specification's event schema), Lean's `Init` and `Std` whole, and the parts of
//! Lean's `Lean` library the frontend reaches. A dependent crate can compile Lean
//! modules of its own against that library and link them into the same process,
//! without a second runtime or a second copy of any module.
//!
//! **Its build.** The crate declares `links = "dogwood_lean"`; its build script
//! prints `lean=1`, `LEAN_VERSION`, `SOURCE_SHA256`, `TOOLCHAIN`, `PACKAGES`, and,
//! from source, `CC` and `AR`, which a direct dependent's build script reads as
//! `DEP_DOGWOOD_LEAN_<KEY>` (without the feature it prints `lean=0` alone). The
//! dependent requires the built packages `PACKAGES` names (`DogwoodSpec`, `Cedar`,
//! `batteries`, each a package root with its `lakefile.lean`, sources and
//! `.olean` files) by path from a Lake project of its own, builds only its own
//! modules with the toolchain's `lake`, and links their archive without any Lean
//! runtime or library module; rustc passes the dependent's archive before this
//! crate's, where its references resolve. Its modules may import any module of
//! the library, of `Init` and of `Std`, and should call no code of a module the
//! library leaves out (Batteries' tactics, linters and code actions). The final
//! link must collect unreferenced sections (`--gc-sections`, which rustc passes
//! when it links an executable, unless `-C link-dead-code`): the library keeps
//! one reference into a left-out module of Batteries (`Except.pmap`, from the
//! `ExceptT` instance of `Batteries.Classes.SatisfiesM`), which no code reaches.
//! A dependent's prebuilt archive records the `SOURCE_SHA256` it was compiled
//! against, and must not be linked against a build of another digest. The
//! crate's `build.rs` documents each key.
//!
//! **Initialization.** The crate owns the runtime. Its archive exports three C
//! functions:
//!
//! | function | contract |
//! |---|---|
//! | `int dogwood_lean_init(void)` | initializes once per process; idempotent and thread-safe; 0 on success, and every later call returns the first one's result |
//! | `void dogwood_lean_thread_enter(void)` | registers the calling thread with Lean on its first enter; counts nested enters |
//! | `void dogwood_lean_thread_exit(void)` | finalizes the thread on its last exit; an exit without an enter does nothing |
//!
//! - `dogwood_lean_init`, from whichever thread calls it first, initializes the
//!   runtime (`lean_initialize_runtime_module`), restores the host's `SIGSEGV`,
//!   `SIGBUS` and `SIGPIPE` handlers and its alternate signal stack, runs the
//!   library's root module initializer with `builtin = 1` (and so the
//!   initializer of every module of the library), and ends Lean's initialization
//!   (`lean_io_mark_end_initialization`). The crate's own first Lean call runs it
//!   too. Nothing else may initialize the runtime.
//! - A dependent calls `dogwood_lean_init` first, then initializes its own root
//!   module, once, with `builtin = 1`, on a registered thread. This is safe after
//!   the end of initialization when the dependent's modules declare no
//!   `initialize` or `builtin_initialize` of their own: the initializers of the
//!   library's modules they import have run, and are no-ops.
//! - Every thread runs Lean code between `dogwood_lean_thread_enter` and
//!   `dogwood_lean_thread_exit`. The crate's own calls run on threads of their
//!   own, registered with the same counted functions, so a thread is never
//!   registered twice.
//! - With one runtime, Lean objects may cross between the crate's code and the
//!   dependent's: an owned `lean_object *` is released on a registered thread.
//!
//! To lower with its own Lean code, a dependent sends the parsers' outputs,
//! `frontend_export::inputs` (feature `frontend-export`, which runs the parsers
//! alone), to its module, which can call the library's pipeline
//! (`Dogwood.Frontend.Driver.lowerFull`, `lowerManyFull`) and hand the lowered
//! set's Cedar part back as Cedar prints it (`Full.cedar`); the dependent builds
//! the Cedar policy set and schema from that JSON with
//! `frontend_export::cedar_policy_set` and `cedar_schema`, as this crate builds
//! those of a set its Lean frontend lowers. Or it hands back the pipeline's
//! whole outcome (`Driver.outcomeToJson`), or the lowered set alone
//! (`Full.toJson`), and `lowered_from_lean` (with the feature) builds the crate's
//! whole [`LoweredPolicySet`](crate::LoweredPolicySet) from it, with no Rust
//! lowering. The workspace's `dogwood-language/lean-dependent` crate is such a
//! dependent, tested.

use std::fmt;

use crate::api::Error;

/// The environment variable that selects the default frontend (feature
/// `lean-frontend` only; see the [module documentation](self)).
pub const FRONTEND_ENV_VAR: &str = "DOGWOOD_FRONTEND";

/// Which implementation of the frontend lowers and validates the policy sets
/// parsed against a [`ServiceSchema`](crate::ServiceSchema). Chosen with
/// [`ServiceSchemaBuilder::frontend`](crate::ServiceSchemaBuilder::frontend);
/// [`Rust`](Frontend::Rust) by default.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default, Hash)]
#[non_exhaustive]
pub enum Frontend {
    /// The crate's Rust frontend: today's behavior, and the default in every build.
    #[default]
    Rust,
    /// The Lean frontend (feature `lean-frontend`). Lowering sends the parsers'
    /// outputs to it and rebuilds the crate's [`LoweredPolicySet`](crate::LoweredPolicySet)
    /// from its result; validation reports the Lean validator's findings, computed
    /// when the set is lowered. Where its results differ in form from the Rust
    /// frontend's (findings carry no source span, a Cedar error the crate cannot
    /// rebuild is an [`Error::Frontend`]), the crate's documentation of the
    /// `lean-frontend` feature says so.
    Lean,
    /// Run both frontends and compare: every component of the lowered set the
    /// crate exposes, the lowering error (its kind, message and span) when both
    /// reject the set, the stable ids, and the validator's findings (by category
    /// and dialect code; by message too with `DOGWOOD_SHADOW_FINDINGS=messages`).
    /// On agreement the Rust frontend's result is returned. On a difference,
    /// [`OnMismatch`] decides.
    Shadow(OnMismatch),
}

/// What [`Frontend::Shadow`] does when the two frontends disagree.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default, Hash)]
#[non_exhaustive]
pub enum OnMismatch {
    /// Fail: lowering returns [`Error::Frontend`] (kind
    /// [`FrontendErrorKind::Mismatch`]) naming the first difference, and
    /// validation adds an error finding with code `frontend` that names it.
    #[default]
    Fail,
    /// Log the first difference to standard error (one line, prefixed
    /// `dogwood: frontend mismatch:`) and return the Rust frontend's result.
    Log,
}

impl Frontend {
    /// Whether this build of the crate can run this frontend: [`Rust`](Frontend::Rust)
    /// always, the others only with the `lean-frontend` feature.
    pub fn is_available(self) -> bool {
        matches!(self, Frontend::Rust) || cfg!(feature = "lean-frontend")
    }

    /// The frontend a service schema takes when its builder names none: the one
    /// `DOGWOOD_FRONTEND` selects with the `lean-frontend` feature, else
    /// [`Rust`](Frontend::Rust).
    ///
    /// # Panics
    ///
    /// With the feature, when `DOGWOOD_FRONTEND` holds a value that names no
    /// frontend.
    pub fn from_env() -> Frontend {
        if !cfg!(feature = "lean-frontend") {
            return Frontend::Rust;
        }
        match std::env::var(FRONTEND_ENV_VAR) {
            Ok(v) if v.trim().is_empty() => Frontend::Rust,
            Ok(v) => v.parse().unwrap_or_else(|e: FrontendError| panic!("{e}")),
            Err(std::env::VarError::NotPresent) => Frontend::Rust,
            Err(std::env::VarError::NotUnicode(_)) => {
                panic!("{FRONTEND_ENV_VAR} is not valid Unicode")
            }
        }
    }

    /// Whether the Lean frontend runs in this mode.
    pub(crate) fn runs_lean(self) -> bool {
        !matches!(self, Frontend::Rust)
    }
}

impl std::str::FromStr for Frontend {
    type Err = FrontendError;

    /// `rust`, `lean`, `shadow` or `shadow-log` (case-insensitive), the values
    /// of `DOGWOOD_FRONTEND`.
    fn from_str(s: &str) -> Result<Self, FrontendError> {
        match s.trim().to_ascii_lowercase().as_str() {
            "rust" => Ok(Frontend::Rust),
            "lean" => Ok(Frontend::Lean),
            "shadow" => Ok(Frontend::Shadow(OnMismatch::Fail)),
            "shadow-log" => Ok(Frontend::Shadow(OnMismatch::Log)),
            _ => Err(FrontendError::new(
                FrontendErrorKind::Unavailable,
                format!(
                    "{FRONTEND_ENV_VAR}=`{}` names no frontend; use `rust`, `lean`, `shadow` or \
                     `shadow-log`",
                    s.escape_default()
                ),
            )),
        }
    }
}

impl fmt::Display for Frontend {
    /// The value of `DOGWOOD_FRONTEND` that selects this frontend.
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(match self {
            Frontend::Rust => "rust",
            Frontend::Lean => "lean",
            Frontend::Shadow(OnMismatch::Fail) => "shadow",
            Frontend::Shadow(OnMismatch::Log) => "shadow-log",
        })
    }
}

/// Why the selected frontend could not produce a result: it is not in this build,
/// the Lean frontend failed or reported what the crate cannot represent, or the two
/// frontends of [`Frontend::Shadow`] disagree. Carried by [`Error::Frontend`].
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FrontendError {
    kind: FrontendErrorKind,
    message: String,
}

/// The kind of a [`FrontendError`].
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub enum FrontendErrorKind {
    /// The selected frontend is not in this build (the crate was built without
    /// `lean-frontend`), or `DOGWOOD_FRONTEND` names no frontend.
    Unavailable,
    /// The Lean frontend failed (its runtime, a panic, a reply the crate cannot
    /// decode), or rejected the policy set with an error the crate has no variant
    /// to carry faithfully (a Cedar error, which only Cedar's Rust API constructs);
    /// the message holds the Lean error's category and message.
    Lean,
    /// [`Frontend::Shadow`] with [`OnMismatch::Fail`]: the two frontends disagree;
    /// the message names the first difference.
    Mismatch,
}

impl FrontendError {
    pub(crate) fn new(kind: FrontendErrorKind, message: impl Into<String>) -> Self {
        FrontendError {
            kind,
            message: message.into(),
        }
    }

    /// The kind of failure.
    pub fn kind(&self) -> FrontendErrorKind {
        self.kind
    }

    /// The message, without the prefix [`Display`](fmt::Display) adds.
    pub fn message(&self) -> &str {
        &self.message
    }
}

impl fmt::Display for FrontendError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.kind {
            FrontendErrorKind::Unavailable => write!(f, "frontend unavailable: {}", self.message),
            FrontendErrorKind::Lean => write!(f, "Lean frontend: {}", self.message),
            FrontendErrorKind::Mismatch => write!(f, "frontend mismatch: {}", self.message),
        }
    }
}

impl std::error::Error for FrontendError {}

impl miette::Diagnostic for FrontendError {}

/// The [`LoweredPolicySet`](crate::LoweredPolicySet) of a lowering that a dependent's
/// own Lean code ran with the Lean frontend's library (feature `lean-frontend`; see
/// [Linking Lean code of your own](self#linking-lean-code-of-your-own)), built as
/// [`Frontend::Lean`] builds the set of the crate's own Lean run, with no Rust
/// lowering.
///
/// - `json` is the JSON text of the pipeline's result, as the library encodes it:
///   the outcome of `Dogwood.Frontend.Driver.lowerFull` (one policy set) or
///   `lowerManyFull` (several, lowered together) as `Driver.outcomeToJson` writes
///   it, which is what `Driver.lowerAll` and `lowerManyAll` return and what the
///   crate's own Lean mode decodes (`{"ok": {"lowered": …, "findings": …}}`,
///   `{"error": …, "augmentedSchema": …}`, or `{"bug": …}`); or the lowered set
///   alone, `Full.toJson` of the `Full` the pipeline returns.
/// - `policies` is each entry's policy text, in entry order (one for `lowerFull`),
///   as the dependent passed them to `frontend_export::inputs` or `inputs_many`:
///   the rules' spans, and their findings', point into them.
/// - `macros` is the macro library's text, as passed to the export (`None` for the
///   default library): the location of an error in the library's merge points
///   into it.
///
/// The set holds what `Frontend::Lean` rebuilds: the Cedar policies (built by
/// Cedar's own constructors from their policy JSON, with their ids and
/// annotations), the augmented schema (compiled by Cedar), the temporal and
/// provider leaves, the event schema, the partition keys, the decision kinds, the
/// rule ids and revisions, and the version hash; every method of
/// [`LoweredPolicySet`](crate::LoweredPolicySet) works on it
/// ([`check_event_conformance`](crate::LoweredPolicySet::check_event_conformance),
/// an [`Authorizer`](crate::Authorizer), …). Given the outcome,
/// [`Validator::validate`](crate::Validator::validate) reports the Lean validator's
/// findings on it, as for a set `Frontend::Lean` lowered; given the lowered set
/// alone, it runs the crate's Rust validator. On the crate's test corpora the set
/// is the one `Frontend::Lean` lowers from the same sources, and the Rust
/// frontend's wherever [`Frontend::Shadow`] finds the two frontends agree.
///
/// # Errors
///
/// For an `error` outcome, the crate's error for the Lean frontend's rejection, as
/// `Frontend::Lean` returns it. [`Error::Frontend`], with kind
/// [`FrontendErrorKind::Lean`], for a `bug` outcome, and for JSON that is none of
/// these forms or does not decode (a rule of an entry `policies` has no text for,
/// for example).
#[cfg(feature = "lean-frontend")]
pub fn lowered_from_lean(
    json: &str,
    policies: &[&str],
    macros: Option<&str>,
) -> Result<crate::LoweredPolicySet, Error> {
    let (lowered, identity) = crate::lean_frontend::lowered_from_lean(json, policies, macros)?;
    Ok(crate::LoweredPolicySet::from_parts(lowered, identity))
}

/// The error of a service schema whose frontend this build cannot run.
pub(crate) fn unavailable(frontend: Frontend) -> Error {
    Error::Frontend(FrontendError::new(
        FrontendErrorKind::Unavailable,
        format!(
            "the {frontend} frontend needs the crate's `lean-frontend` feature, and this build \
             does not have it"
        ),
    ))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn the_env_values_round_trip() {
        for f in [
            Frontend::Rust,
            Frontend::Lean,
            Frontend::Shadow(OnMismatch::Fail),
            Frontend::Shadow(OnMismatch::Log),
        ] {
            assert_eq!(f.to_string().parse::<Frontend>().unwrap(), f);
        }
        assert_eq!(" Lean ".parse::<Frontend>().unwrap(), Frontend::Lean);
        let e = "lena".parse::<Frontend>().unwrap_err();
        assert_eq!(e.kind(), FrontendErrorKind::Unavailable);
        assert!(e.to_string().contains("DOGWOOD_FRONTEND=`lena`"), "{e}");
    }

    #[test]
    fn a_schema_selecting_a_frontend_the_build_lacks_is_rejected() {
        for f in [Frontend::Lean, Frontend::Shadow(OnMismatch::Fail)] {
            let built = crate::ServiceSchema::builder().frontend(f).build();
            if cfg!(feature = "lean-frontend") {
                assert_eq!(built.unwrap().frontend(), f);
            } else {
                match built {
                    Err(Error::Frontend(e)) => {
                        assert_eq!(e.kind(), FrontendErrorKind::Unavailable);
                        assert!(e.to_string().contains("lean-frontend"), "{e}");
                    }
                    other => panic!("{other:?}"),
                }
            }
        }
        let rust = crate::ServiceSchema::builder()
            .frontend(Frontend::Rust)
            .build()
            .unwrap();
        assert_eq!(rust.frontend(), Frontend::Rust);
    }

    #[test]
    fn only_the_rust_frontend_is_available_without_the_feature() {
        assert!(Frontend::Rust.is_available());
        assert_eq!(
            Frontend::Lean.is_available(),
            cfg!(feature = "lean-frontend")
        );
        assert_eq!(
            Frontend::Shadow(OnMismatch::Log).is_available(),
            cfg!(feature = "lean-frontend")
        );
    }
}
