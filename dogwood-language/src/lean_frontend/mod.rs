//! The bridge to the Lean frontend (feature `lean-frontend`): it encodes the
//! parsers' outputs, calls the Lean frontend through the C FFI (`runtime`),
//! decodes its result into the crate's own lowered set, findings and errors
//! (`decode`), and, in [`Frontend::Shadow`], compares the two frontends
//! (`observe`).
//!
//! The parsers are always the crate's: [`api::parse`] parses (and, for the
//! pre-lowering diagnostics of a [`ParsedPolicySet`](crate::ParsedPolicySet),
//! expands) the policy text with the Rust frontend, and keeps the parser's
//! output, which is what the Lean frontend lowers. The Lean frontend computes
//! everything after the parsers itself: the macro library merge and expansion,
//! the stable ids, derivation, lowering, augmentation, relativization, provider
//! resolution, the identity hashes, and validation.

mod decode;
mod observe;
mod runtime;
#[cfg(test)]
mod tests;

use std::sync::Arc;

use serde::Deserialize as _;
use serde_json::{Value as Json, json};

use crate::api::frontend_export as ex;
use crate::api::{Error, Lowered, Parsed};
use crate::error::{
    CedarifyError, MacroError, PolicyIdError, PolicyIdErrorKind, SourceLoc, Span, ValidationError,
    ValidationResult, ValidationWarning,
};
use crate::frontend::{Frontend, FrontendError, FrontendErrorKind, OnMismatch};
use crate::identity::SetIdentity;
use crate::policy_schema::PolicySchema;
use crate::policy_set::Distincter;

use decode::{R, get, opt, str_at};

/// One finding of a validator: its dialect code, its message, and whether it is
/// a warning; for a Lean finding, the rule it is about (its index in the lowered
/// set) and its span in that rule's source, where the Lean frontend locates it.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct Finding {
    pub(crate) code: String,
    pub(crate) message: String,
    pub(crate) warning: bool,
    pub(crate) rule: Option<usize>,
    pub(crate) span: Option<Span>,
}

impl Finding {
    /// What the shadow mode compares: the code, the message and the channel.
    fn key(&self) -> (&str, &str, bool) {
        (&self.code, &self.message, self.warning)
    }
}

/// What the Lean frontend recorded on a lowered set: the frontend that lowered it
/// ([`Frontend::Lean`], or [`Frontend::Shadow`] for the Rust frontend's set it was
/// compared with), and the Lean validator's findings, or why there are none.
#[derive(Debug, Clone)]
pub(crate) struct LeanRecord {
    pub(crate) frontend: Frontend,
    pub(crate) findings: Result<Vec<Finding>, String>,
}

/// A rejection by the Lean frontend: its error, as the result format writes it
/// (`stage`, `category`, `message`, `span`, `entry`, `policyId`), and, for a schema
/// Cedar rejects, the augmented schema in Cedar's JSON form.
#[derive(Debug, Clone)]
struct LeanError {
    stage: String,
    category: String,
    message: String,
    span: Option<Span>,
    entry: Option<usize>,
    policy_id: Option<Json>,
    augmented_schema: Option<Json>,
}

impl LeanError {
    fn of_json(e: &Json, augmented_schema: Option<&Json>) -> R<LeanError> {
        Ok(LeanError {
            stage: str_at(e, "stage")?,
            category: str_at(e, "category")?,
            message: str_at(e, "message")?,
            span: opt(e, "span").map(decode::span).transpose()?,
            entry: opt(e, "entry").map(decode::usize_of).transpose()?,
            policy_id: opt(e, "policyId").cloned(),
            augmented_schema: augmented_schema.cloned(),
        })
    }
}

/// The Lean frontend's answer to a lowering.
enum Reply {
    Lowered {
        lowered: Box<Lowered>,
        identity: SetIdentity,
        /// The Lean frontend's own content hash of each authored temporal leaf
        /// (the decoded set's are the crate's computation on the decoded leaves).
        content_hashes: Vec<String>,
        /// The Lean frontend's Cedar part as it printed it (`Full.cedar`): each
        /// rule's id, policy JSON and text, and the augmented schema's JSON. The
        /// decoded set is built from the policy JSON; shadow mode compares all of
        /// it with what Cedar prints of the Rust frontend's set.
        printed: Json,
        findings: Result<Vec<Finding>, String>,
    },
    Rejected(LeanError),
}

/// One entry of a lowering: a parsed set, and its distincter.
pub(crate) type EntryRef<'a> = (&'a Parsed, Option<&'a Distincter>);

/// Lower `entries` (one for [`api::lower`], one or more for `lower_many`) with the
/// frontend their service schema selects, which is not [`Frontend::Rust`]. `rust`
/// is the Rust frontend's lowering of the same entries, run in shadow mode.
pub(crate) fn lower(
    entries: &[EntryRef<'_>],
    policy_schema: &PolicySchema,
    many: bool,
    rust: impl FnOnce() -> Result<(Lowered, SetIdentity), Error>,
) -> Result<(Lowered, SetIdentity), Error> {
    let frontend = entries
        .first()
        .map(|(p, _)| p.service_schema().frontend())
        .unwrap_or_default();
    match frontend {
        Frontend::Rust => rust(),
        Frontend::Lean => match lean_lower(entries, policy_schema, many)? {
            Reply::Lowered {
                mut lowered,
                identity,
                findings,
                ..
            } => {
                lowered.lean = Some(LeanRecord { frontend, findings });
                Ok((*lowered, identity))
            }
            Reply::Rejected(e) => Err(lean_error(&e, entries)),
        },
        Frontend::Shadow(on_mismatch) => {
            let rust = rust();
            let lean = lean_lower(entries, policy_schema, many);
            if let Some(difference) = identity_difference(&rust, &lean) {
                identity_mismatch(on_mismatch, &difference);
            }
            let difference = lowering_difference(&rust, &lean, entries)
                .or_else(|| printing_difference(&rust, &lean));
            let findings = match &lean {
                Ok(Reply::Lowered { findings, .. }) => findings.clone(),
                Ok(Reply::Rejected(e)) => {
                    Err(format!("the Lean frontend rejected the set: {}", e.message))
                }
                Err(e) => Err(e.to_string()),
            };
            if let Some(difference) = difference {
                mismatch(on_mismatch, &format!("lowering: {difference}"))?;
            }
            let (mut lowered, identity) = rust?;
            lowered.lean = Some(LeanRecord { frontend, findings });
            Ok((lowered, identity))
        }
    }
}

/// Act on a difference between the two frontends: an error, or a line on
/// standard error.
fn mismatch(on_mismatch: OnMismatch, difference: &str) -> Result<(), Error> {
    match on_mismatch {
        OnMismatch::Log => {
            eprintln!("dogwood: frontend mismatch: {difference}");
            Ok(())
        }
        _ => Err(Error::Frontend(FrontendError::new(
            FrontendErrorKind::Mismatch,
            difference,
        ))),
    }
}

/// Act on a difference between the two frontends' identity values: a line on
/// standard error, or, in [`OnMismatch::Fail`], a panic. The identity values key
/// what is persisted about a policy set (a rule's id and revision, the version
/// hash, a leaf's content hash), and a caller that tolerates a lowering error (a
/// fuzz harness, say) would not see a `Mismatch` error, so a difference in them
/// cannot be left to the caller.
fn identity_mismatch(on_mismatch: OnMismatch, difference: &str) {
    match on_mismatch {
        OnMismatch::Log => eprintln!("dogwood: frontend mismatch: identity: {difference}"),
        _ => panic!("dogwood: frontend mismatch in an identity value: {difference}"),
    }
}

fn lean_failure(message: impl Into<String>) -> Error {
    Error::Frontend(FrontendError::new(FrontendErrorKind::Lean, message))
}

// ─── Stable ids ─────────────────────────────────────────────────────────

/// The stable ids of `parsed` under `source`
/// ([`ParsedPolicySet::with_ids`](crate::ParsedPolicySet::with_ids)), with the
/// frontend its service schema selects, which is not [`Frontend::Rust`]. `rust` is
/// the Rust frontend's assignment, run in shadow mode.
pub(crate) fn assign_ids(
    parsed: &Parsed,
    source: &crate::IdSource,
    rust: impl FnOnce() -> Result<Option<Vec<String>>, Error>,
) -> Result<Option<Vec<String>>, Error> {
    let frontend = parsed.service_schema().frontend();
    let entries: [EntryRef<'_>; 1] = [(parsed, None)];
    let lean = || -> Result<Result<Option<Vec<String>>, LeanError>, Error> {
        runtime::with_lean(|lean| {
            // The parse phase reads no action schema; the request carries an empty one.
            let shared = shared_inputs(parsed, None)?;
            let raw = parsed.raw().ok_or_else(|| {
                lean_failure("the parsed set kept no parse for the Lean frontend")
            })?;
            let request = ex::single_inputs(&shared, ex::entry_inputs(Ok(raw), None, Some(source)));
            let text = serde_json::to_string(&request).map_err(|e| lean_failure(e.to_string()))?;
            let reply = lean
                .call(runtime::Entry::Parse, &text)
                .map_err(|e| lean_failure(e.to_string()))?;
            let reply = parse_json(&reply)
                .map_err(|e| lean_failure(format!("an unreadable reply: {e}")))?;
            let decoded = (|| -> R<Result<Option<Vec<String>>, LeanError>> {
                if let Some(bug) = opt(&reply, "bug") {
                    return Err(format!(
                        "the Lean frontend failed: {}",
                        bug.as_str().unwrap_or_default()
                    ));
                }
                if let Some(e) = opt(&reply, "error") {
                    return Ok(Err(LeanError::of_json(e, None)?));
                }
                let ids = opt(get(&reply, "ok")?, "ids")
                    .map(|v| decode::list(v, decode::string))
                    .transpose()?;
                Ok(Ok(ids))
            })();
            decoded.map_err(|e| lean_failure(format!("an undecodable reply: {e}")))
        })
        .map_err(|e| lean_failure(e.to_string()))?
    };
    match frontend {
        Frontend::Rust => rust(),
        Frontend::Lean => lean()?.map_err(|e| lean_error(&e, &entries)),
        Frontend::Shadow(on_mismatch) => {
            let rust = rust();
            let lean = lean();
            let difference = match (&rust, &lean) {
                (_, Err(e)) => Some(format!("the Lean frontend failed: {e}")),
                (Ok(a), Ok(Ok(b))) if a == b => None,
                (Ok(a), Ok(Ok(b))) => Some(format!("Rust assigns {a:?}, Lean {b:?}")),
                (Ok(_), Ok(Err(e))) => Some(format!(
                    "the Rust frontend assigns the ids, the Lean frontend rejects them ({})",
                    e.message
                )),
                (Err(e), Ok(Ok(_))) => Some(format!(
                    "the Lean frontend assigns the ids, the Rust frontend rejects them ({e})"
                )),
                (Err(r), Ok(Err(l))) => {
                    let (a, b) = (
                        error_observable(r),
                        error_observable(&lean_error(l, &entries)),
                    );
                    (a != b).then(|| {
                        format!("the frontends reject the ids differently: Rust {a:?}, Lean {b:?}")
                    })
                }
            };
            if let Some(difference) = difference {
                mismatch(on_mismatch, &format!("stable ids: {difference}"))?;
            }
            rust
        }
    }
}

// ─── The request ────────────────────────────────────────────────────────

/// The inputs every entry shares: the service schema's parses and the action
/// schema's (none for the parse phase), encoded by the frontend export's encoder
/// (`frontend_export::shared_inputs`), so that the request is what
/// `frontend_export::inputs` returns for the same sources.
fn shared_inputs(
    parsed: &Parsed,
    policy_schema: Option<&PolicySchema>,
) -> Result<serde_json::Map<String, Json>, Error> {
    let service = parsed.service_schema();
    let macros = service.macros();
    let library = if macros.trim().is_empty() {
        None
    } else {
        // Parsing the policy merged this library, so it parses.
        Some(
            crate::parser::parse_policies_with(macros, parsed.options())
                .map_err(|_| lean_failure("the macro library does not parse"))?,
        )
    };
    let fragment = policy_schema.map(|p| ex::parse_action_schema(p.action_schema_src()));
    Ok(ex::shared_inputs(
        library.as_ref().map(Ok),
        Ok(service.event_schema()),
        service.provider_declarations().map(Ok),
        fragment.as_ref().map(Result::as_ref),
    ))
}

/// One entry's own inputs: the parser's output, the distincter, and the id
/// source the set was given (`frontend_export::entry_inputs`).
fn entry_inputs(
    parsed: &Parsed,
    distincter: Option<&Distincter>,
) -> Result<serde_json::Map<String, Json>, Error> {
    let raw = parsed
        .raw()
        .ok_or_else(|| lean_failure("the parsed set kept no parse for the Lean frontend"))?;
    Ok(ex::entry_inputs(
        Ok(raw),
        distincter.map(Distincter::as_str),
        parsed.id_source(),
    ))
}

/// The request of a lowering, in the Lean frontend's input format: what
/// `frontend_export::inputs` (one entry) or `inputs_many` returns for the same
/// sources.
pub(crate) fn request(
    entries: &[EntryRef<'_>],
    policy_schema: &PolicySchema,
    many: bool,
) -> Result<Json, Error> {
    let (first, _) = entries.first().ok_or(Error::NoPolicies)?;
    let shared = shared_inputs(first, Some(policy_schema))?;
    if many {
        let items = entries
            .iter()
            .map(|(p, d)| entry_inputs(p, *d))
            .collect::<Result<Vec<_>, _>>()?;
        Ok(ex::many_inputs(&shared, items.into_iter()))
    } else {
        Ok(ex::single_inputs(
            &shared,
            entry_inputs(first, entries[0].1)?,
        ))
    }
}

// ─── The call ───────────────────────────────────────────────────────────

/// Parse JSON text of any depth (the caller is on the Lean call's big stack).
fn parse_json(text: &str) -> R<Json> {
    let mut de = serde_json::Deserializer::from_str(text);
    de.disable_recursion_limit();
    let v = Json::deserialize(&mut de).map_err(|e| e.to_string())?;
    de.end().map_err(|e| e.to_string())?;
    Ok(v)
}

/// Lower `entries` with the Lean frontend: its lowered set (decoded) and
/// findings, or its rejection; an `Err` when the Lean frontend itself failed.
fn lean_lower(
    entries: &[EntryRef<'_>],
    policy_schema: &PolicySchema,
    many: bool,
) -> Result<Reply, Error> {
    let sources = decode::Sources {
        entries: entries.iter().map(|(p, _)| p.dw_src()).collect(),
    };
    let entry = if many {
        runtime::Entry::LowerMany
    } else {
        runtime::Entry::Lower
    };
    runtime::with_lean(|lean| {
        let request = request(entries, policy_schema, many)?;
        let text = serde_json::to_string(&request).map_err(|e| lean_failure(e.to_string()))?;
        drop(request);
        let reply = lean
            .call(entry, &text)
            .map_err(|e| lean_failure(e.to_string()))?;
        let reply =
            parse_json(&reply).map_err(|e| lean_failure(format!("an unreadable reply: {e}")))?;
        let decoded = decode_reply(&reply, &sources)
            .map_err(|e| lean_failure(format!("an undecodable reply: {e}")))?;
        drop(reply);
        decoded
    })
    .map_err(|e| lean_failure(e.to_string()))?
}

/// The reply's envelope: `{"ok": payload}`, `{"error": e, "augmentedSchema"?}` or
/// `{"bug": message}`.
fn decode_reply(reply: &Json, sources: &decode::Sources<'_>) -> R<Result<Reply, Error>> {
    if let Some(bug) = opt(reply, "bug") {
        return Ok(Err(lean_failure(format!(
            "the Lean frontend failed: {}",
            bug.as_str().unwrap_or_default()
        ))));
    }
    if let Some(e) = opt(reply, "error") {
        return Ok(Ok(Reply::Rejected(LeanError::of_json(
            e,
            opt(reply, "augmentedSchema"),
        )?)));
    }
    let payload = get(reply, "ok")?;
    let content_hashes = decode::list(
        get(get(payload, "lowered")?, "contentHashes")?,
        decode::string,
    )
    .map_err(|e| format!("lowered.contentHashes: {e}"))?;
    let (lowered, identity) = decode::lowered(get(payload, "lowered")?, sources)?;
    let findings = match opt(payload, "findings") {
        None => Err("the Lean frontend did not validate the set".to_owned()),
        Some(f) => match (opt(f, "ok"), opt(f, "error")) {
            (Some(list), _) => Ok(decode::list(list, |x| {
                Ok(Finding {
                    code: str_at(x, "code")?,
                    message: str_at(x, "message")?,
                    warning: get(x, "warning")?
                        .as_bool()
                        .ok_or("`warning` is not a boolean")?,
                    rule: opt(x, "rule").map(decode::usize_of).transpose()?,
                    span: opt(x, "span").map(decode::span).transpose()?,
                })
            })?),
            (None, Some(e)) => Err(format!(
                "the Lean validator failed: {}",
                LeanError::of_json(e, None)?.message
            )),
            (None, None) => return Err("`findings` is neither `ok` nor `error`".into()),
        },
    };
    let full = get(payload, "lowered")?;
    let printed = json!({
        "policies": get(full, "policies")?.clone(),
        "augmentedSchema": get(full, "augmentedSchema")?.clone(),
    });
    Ok(Ok(Reply::Lowered {
        lowered: Box::new(lowered),
        identity,
        content_hashes,
        printed,
        findings,
    }))
}

// ─── A dependent's own Lean lowering ────────────────────────────────────

/// The lowered set of a lowering a dependent's own Lean code ran with the Lean
/// frontend's library (`frontend::lowered_from_lean`): `json` is the lowered set
/// (`Full.toJson`), or the outcome of the pipeline (`outcomeToJson`: the lowered set
/// and the validator's findings, the error, or a `bug`); `policies` is each entry's
/// policy text, and `macros` the macro library's (`None` for the default one).
pub(crate) fn lowered_from_lean(
    json: &str,
    policies: &[&str],
    macros: Option<&str>,
) -> Result<(Lowered, SetIdentity), Error> {
    // JSON of any depth, decoded and dropped on a thread with the Lean calls' big stack.
    std::thread::scope(|scope| {
        std::thread::Builder::new()
            .name("dogwood-lean-decode".into())
            .stack_size(runtime::STACK_SIZE)
            .spawn_scoped(scope, || decode_lowering(json, policies, macros))
            .map_err(|e| lean_failure(format!("cannot start the decoder's thread: {e}")))?
            .join()
            .unwrap_or_else(|panic| std::panic::resume_unwind(panic))
    })
}

fn decode_lowering(
    json: &str,
    policies: &[&str],
    macros: Option<&str>,
) -> Result<(Lowered, SetIdentity), Error> {
    let reply = parse_json(json).map_err(|e| lean_failure(format!("not JSON: {e}")))?;
    let texts: Vec<Arc<str>> = policies.iter().map(|p| Arc::from(*p)).collect();
    let sources = decode::Sources {
        entries: texts.iter().collect(),
    };
    if opt(&reply, "ruleIds").is_some() {
        // The lowered set alone (`Full.toJson`), which no validator ran on.
        return decode::lowered(&reply, &sources)
            .map_err(|e| lean_failure(format!("an undecodable lowered set: {e}")));
    }
    let decoded = decode_reply(&reply, &sources)
        .map_err(|e| lean_failure(format!("an undecodable outcome: {e}")))?;
    drop(reply);
    match decoded? {
        Reply::Lowered {
            mut lowered,
            identity,
            findings,
            ..
        } => {
            lowered.lean = Some(LeanRecord {
                frontend: Frontend::Lean,
                findings,
            });
            Ok((*lowered, identity))
        }
        Reply::Rejected(e) => {
            let library: Arc<str> =
                Arc::from(macros.unwrap_or(crate::service_schema::DEFAULT_MACROS));
            Err(lean_error_in(
                &e,
                &|k| texts.get(k).cloned().unwrap_or_else(|| Arc::from("")),
                &|| Arc::clone(&library),
            ))
        }
    }
}

// ─── Errors ─────────────────────────────────────────────────────────────

/// The crate's error for a Lean rejection: the variant of the Lean error's
/// category, with its message and location, when the crate can build it; else
/// [`Error::Frontend`] with kind [`FrontendErrorKind::Lean`].
fn lean_error(e: &LeanError, entries: &[EntryRef<'_>]) -> Error {
    lean_error_in(
        e,
        &|k| {
            entries
                .get(k)
                .map(|(p, _)| Arc::clone(p.dw_src()))
                .unwrap_or_else(|| Arc::from(""))
        },
        &|| {
            entries
                .first()
                .map(|(p, _)| Arc::from(p.service_schema().macros()))
                .unwrap_or_else(|| Arc::from(""))
        },
    )
}

/// [`lean_error`], with the source of entry `k` (`entry_src(k)`) and the macro
/// library's (`library_src()`), which the error's location points into.
fn lean_error_in(
    e: &LeanError,
    entry_src: &dyn Fn(usize) -> Arc<str>,
    library_src: &dyn Fn() -> Arc<str>,
) -> Error {
    // A library error points into the library's source.
    let src = || -> Arc<str> {
        if e.stage == "mergeLibrary" {
            library_src()
        } else {
            entry_src(e.entry.unwrap_or(0))
        }
    };
    let loc = || e.span.map(|s| SourceLoc::new(s, src()));
    match e.category.as_str() {
        "macro" => Error::Macro(MacroError::new(
            e.message.clone(),
            SourceLoc::new(e.span.unwrap_or(Span::new(0, 0)), src()),
        )),
        "cedarify" => Error::Cedarify(CedarifyError::new(e.message.clone(), loc())),
        "eventSchema" => Error::EventSchema(e.message.clone()),
        "providers" => Error::Providers(e.message.clone()),
        "invalidDistincter" => Error::InvalidDistincter(e.message.clone()),
        "duplicateDistincter" => Error::DuplicateDistincter(e.message.clone()),
        "noPolicies" => Error::NoPolicies,
        "policyId" => {
            let detail = e.policy_id.as_ref();
            let kind = match detail.and_then(|d| d.get("kind")).and_then(Json::as_str) {
                Some("missing") => PolicyIdErrorKind::Missing,
                Some("duplicate") => PolicyIdErrorKind::Duplicate,
                Some("invalid") => PolicyIdErrorKind::Invalid,
                Some("countMismatch") => PolicyIdErrorKind::CountMismatch,
                Some("repeatedAnnotation") => PolicyIdErrorKind::RepeatedAnnotation,
                other => {
                    return lean_failure(format!(
                        "policyId error of kind {other:?}: {}",
                        e.message
                    ));
                }
            };
            let policy = detail
                .and_then(|d| d.get("policy"))
                .and_then(Json::as_u64)
                .and_then(|n| usize::try_from(n).ok());
            let id = detail
                .and_then(|d| d.get("id"))
                .and_then(Json::as_str)
                .map(str::to_owned);
            Error::PolicyId(PolicyIdError::new(
                kind,
                e.message.clone(),
                policy,
                id,
                loc(),
            ))
        }
        // The merge's one Cedar policy-set error, rebuilt by Cedar itself.
        "policySet" => match e
            .message
            .strip_prefix("duplicate template or policy id `")
            .and_then(|m| m.strip_suffix('`'))
        {
            Some(id) => duplicate_policy_id(id)
                .unwrap_or_else(|| lean_failure(format!("policySet: {}", e.message))),
            None => lean_failure(format!("policySet: {}", e.message)),
        },
        "cedarSchema" => match &e.augmented_schema {
            // Cedar's own error, from Cedar's own compilation of the Lean frontend's
            // augmented schema.
            Some(schema) => match cedar_policy::SchemaFragment::from_json_value(schema.clone()) {
                Err(err) => lean_failure(format!(
                    "the Lean frontend's augmented schema is not Cedar's JSON schema: {err}"
                )),
                Ok(fragment) => {
                    let compiled: Result<cedar_policy::Schema, cedar_policy::SchemaError> =
                        fragment.try_into();
                    match compiled {
                        Err(err) => Error::CedarSchema(Box::new(err.into())),
                        Ok(_) => lean_failure(format!(
                            "the Lean frontend rejects the augmented schema ({}), and Cedar \
                             accepts it",
                            e.message
                        )),
                    }
                }
            },
            None => lean_failure(format!("cedarSchema: {}", e.message)),
        },
        other => lean_failure(format!("{other} error at stage {}: {}", e.stage, e.message)),
    }
}

/// Cedar's error for a second policy with the id `id` in a policy set, which the
/// Rust frontend's merge reports (`Error::PolicySet`).
fn duplicate_policy_id(id: &str) -> Option<Error> {
    let policy = |id: &str| {
        cedar_policy::Policy::parse(
            Some(cedar_policy::PolicyId::new(id)),
            "permit (principal, action, resource);",
        )
        .ok()
    };
    let mut set = cedar_policy::PolicySet::new();
    set.add(policy(id)?).ok()?;
    set.add(policy(id)?)
        .err()
        .map(|e| Error::PolicySet(Box::new(e)))
}

/// A crate error's kind (the export's categories), message and span.
fn error_observable(e: &Error) -> (String, String, Option<Span>) {
    let span_of = |loc: &SourceLoc| {
        let s = loc.span();
        Span::new(s.offset(), s.offset() + s.len())
    };
    match e {
        Error::Parse(p) => ("parse".into(), p.to_string(), None),
        Error::Macro(m) => ("macro".into(), m.to_string(), Some(span_of(m.location()))),
        Error::Cedarify(c) => ("cedarify".into(), c.to_string(), c.location().map(span_of)),
        Error::PolicySet(_) => ("policySet".into(), e.to_string(), None),
        Error::CedarSchema(_) => ("cedarSchema".into(), e.to_string(), None),
        Error::EventSchema(m) => ("eventSchema".into(), m.clone(), None),
        Error::Providers(m) => ("providers".into(), m.clone(), None),
        Error::PolicyId(p) => ("policyId".into(), p.to_string(), p.location().map(span_of)),
        Error::InvalidDistincter(d) => ("invalidDistincter".into(), d.clone(), None),
        Error::DuplicateDistincter(d) => ("duplicateDistincter".into(), d.clone(), None),
        Error::NoPolicies => ("noPolicies".into(), String::new(), None),
        Error::Frontend(f) => ("frontend".into(), f.to_string(), None),
        _ => ("other".into(), e.to_string(), None),
    }
}

/// The observables of the Lean frontend's lowered set, with its own content
/// hashes.
fn lean_observables(lowered: &Lowered, identity: &SetIdentity, content_hashes: &[String]) -> Json {
    let mut j = observe::lowered(lowered, identity);
    j["contentHashes"] = json!(content_hashes);
    j
}

/// The identity values of the observables of a lowered set.
const IDENTITY_KEYS: [&str; 5] = [
    "ruleIds",
    "ruleRevisions",
    "stableIds",
    "versionHash",
    "contentHashes",
];

/// The first difference between the identity values of the two frontends'
/// lowered sets, when both lower the set: a rule's id or revision, whether the
/// ids are stable, the version hash, or a temporal leaf's content hash.
fn identity_difference(
    rust: &Result<(Lowered, SetIdentity), Error>,
    lean: &Result<Reply, Error>,
) -> Option<String> {
    let (
        Ok((rl, ri)),
        Ok(Reply::Lowered {
            lowered,
            identity,
            content_hashes,
            ..
        }),
    ) = (rust, lean)
    else {
        return None;
    };
    let (a, b) = (
        observe::lowered(rl, ri),
        lean_observables(lowered, identity, content_hashes),
    );
    IDENTITY_KEYS.iter().find_map(|key| {
        observe::first_difference(&a[*key], &b[*key]).map(|(path, x, y)| {
            format!(
                "the lowered sets' `{key}{path}` differ: Rust {}, Lean {}",
                decode::short(&x),
                decode::short(&y)
            )
        })
    })
}

/// The first difference between the Lean frontend's Cedar part as it printed it
/// (each rule's policy JSON and text, the augmented schema's JSON) and Cedar's
/// printing of the Rust frontend's set (`Policy::to_json`, `Policy`'s `Display`,
/// `SchemaFragment::to_json_value`), when both lower the set. In `Lean` mode the
/// crate builds the policies from their JSON and reads neither text; a dependent
/// that builds them from the same JSON (`frontend_export::cedar_policy_set`), or
/// shows the text, relies on this agreement.
fn printing_difference(
    rust: &Result<(Lowered, SetIdentity), Error>,
    lean: &Result<Reply, Error>,
) -> Option<String> {
    let (Ok((rl, ri)), Ok(Reply::Lowered { printed, .. })) = (rust, lean) else {
        return None;
    };
    let record = observe::lowered(rl, ri);
    let cedar = json!({
        "policies": record["policies"],
        "augmentedSchema": record["augmentedSchema"],
    });
    observe::first_difference(&cedar, printed).map(|(path, x, y)| {
        format!(
            "the Lean frontend prints `{}` otherwise than Cedar prints the Rust frontend's set: \
             Cedar {}, Lean {}",
            path.trim_start_matches('.'),
            decode::short(&x),
            decode::short(&y)
        )
    })
}

/// The first difference between the two frontends' lowerings, if any.
fn lowering_difference(
    rust: &Result<(Lowered, SetIdentity), Error>,
    lean: &Result<Reply, Error>,
    entries: &[EntryRef<'_>],
) -> Option<String> {
    match (rust, lean) {
        (_, Err(e)) => Some(format!("the Lean frontend failed: {e}")),
        (
            Ok((rl, ri)),
            Ok(Reply::Lowered {
                lowered,
                identity,
                content_hashes,
                ..
            }),
        ) => {
            let (a, b) = (
                observe::lowered(rl, ri),
                lean_observables(lowered, identity, content_hashes),
            );
            observe::first_difference(&a, &b).map(|(path, x, y)| {
                format!(
                    "the lowered sets differ at `{}`: Rust {}, Lean {}",
                    path.trim_start_matches('.'),
                    decode::short(&x),
                    decode::short(&y)
                )
            })
        }
        (Ok(_), Ok(Reply::Rejected(e))) => Some(format!(
            "the Rust frontend lowers the set, the Lean frontend rejects it ({} at stage {}: {})",
            e.category, e.stage, e.message
        )),
        (Err(e), Ok(Reply::Lowered { .. })) => {
            let (category, message, _) = error_observable(e);
            Some(format!(
                "the Lean frontend lowers the set, the Rust frontend rejects it ({category}: {message})"
            ))
        }
        (Err(r), Ok(Reply::Rejected(l))) => {
            let (category, message, span) = error_observable(r);
            let (lcategory, lmessage, lspan) = error_observable(&lean_error(l, entries));
            // Cedar's errors are Cedar's text on the Rust side; they are compared by kind.
            let by_kind = matches!(category.as_str(), "policySet" | "cedarSchema");
            if category != lcategory && !(by_kind && l.category == category) {
                Some(format!(
                    "the frontends reject the set differently: Rust {category} ({message}), Lean {} \
                     ({})",
                    l.category, l.message
                ))
            } else if !by_kind && message != lmessage {
                Some(format!(
                    "the frontends' {category} errors differ: Rust `{message}`, Lean `{lmessage}`"
                ))
            } else if !by_kind && span != lspan {
                Some(format!(
                    "the frontends' {category} errors point at different spans: Rust {span:?}, Lean \
                     {lspan:?}"
                ))
            } else {
                None
            }
        }
    }
}

// ─── Validation ─────────────────────────────────────────────────────────

/// The dialect code of a Lean finding, as the crate's static code.
fn static_code(code: &str) -> &'static str {
    match code {
        "temporal" => "temporal",
        "provider" => "provider",
        "context" => "context",
        "schema" => "schema",
        "cedar" => "cedar",
        _ => "lean",
    }
}

/// The source the Lean findings render against: the first rule's.
fn finding_src(lowered: &Lowered) -> Arc<str> {
    lowered
        .rule_locs
        .first()
        .map_or_else(|| Arc::from(""), |loc| Arc::clone(loc.src()))
}

/// The Lean validator's findings as the crate's [`ValidationResult`], each in the
/// source of the rule it is about, at its span: the span the Lean frontend gives
/// it, else the rule's; a context-read finding at the read the lowering recorded
/// (the Lean frontend reports them in the order it records them); a finding of
/// the whole set at the start of the first rule's source.
fn lean_result(lowered: &Lowered, findings: &Result<Vec<Finding>, String>) -> ValidationResult {
    let first_src = finding_src(lowered);
    let miette = |s: Span| miette::SourceSpan::new(s.start.into(), s.end.saturating_sub(s.start));
    let at_rule = |k: usize, span: Option<Span>| {
        lowered.rule_locs.get(k).map(|loc| {
            let s = loc.span();
            let span = span.map_or_else(
                || miette::SourceSpan::new(s.offset().into(), s.len()),
                miette,
            );
            (span, Arc::clone(loc.src()))
        })
    };
    let has_leaves = !lowered.temporal.is_empty() || !lowered.providers.is_empty();
    let mut reads = lowered
        .context_reads
        .iter()
        .filter(|r| has_leaves || !r.whole);
    let mut place = |f: &Finding| {
        let located = match (f.code.as_str(), f.rule) {
            ("context", None) => reads
                .next()
                .filter(|r| r.message == f.message)
                .and_then(|r| at_rule(r.rule, Some(r.span))),
            (_, Some(k)) => at_rule(k, f.span),
            _ => None,
        };
        located.unwrap_or_else(|| (miette::SourceSpan::new(0.into(), 0), Arc::clone(&first_src)))
    };
    let mut errors = Vec::new();
    let mut warnings = Vec::new();
    match findings {
        Err(why) => errors.push(ValidationError::Extension {
            code: "frontend",
            message: why.clone(),
            span: miette::SourceSpan::new(0.into(), 0),
            label: None,
            help: None,
            src: Arc::clone(&first_src),
            source: None,
        }),
        Ok(findings) => {
            for f in findings {
                let (span, src) = place(f);
                match (f.warning, f.code.as_str()) {
                    (false, "cedar") => errors.push(ValidationError::Cedar {
                        message: f.message.clone(),
                        span,
                        label: None,
                        help: None,
                        src,
                        source: None,
                    }),
                    (false, code) => errors.push(ValidationError::Extension {
                        code: static_code(code),
                        message: f.message.clone(),
                        span,
                        label: None,
                        help: None,
                        src,
                        source: None,
                    }),
                    (true, code) => warnings.push(ValidationWarning::Extension {
                        code: static_code(code),
                        message: f.message.clone(),
                        span,
                        label: None,
                        help: None,
                        src,
                        source: None,
                    }),
                }
            }
        }
    }
    ValidationResult::new(errors, warnings)
}

/// A crate finding as `(code, message, warning)`.
fn rust_findings(result: &ValidationResult) -> Vec<Finding> {
    let mut out = Vec::new();
    for e in result.validation_errors() {
        let (code, message) = match e {
            ValidationError::Cedar { message, .. } => ("cedar", message.clone()),
            ValidationError::Extension { code, message, .. } => (*code, message.clone()),
        };
        out.push(Finding {
            code: code.to_owned(),
            message,
            warning: false,
            rule: None,
            span: None,
        });
    }
    for w in result.validation_warnings() {
        let (code, message) = match w {
            ValidationWarning::Cedar(w) => ("cedar", w.to_string()),
            ValidationWarning::Extension { code, message, .. } => (*code, message.clone()),
        };
        out.push(Finding {
            code: code.to_owned(),
            message,
            warning: true,
            rule: None,
            span: None,
        });
    }
    out
}

/// The category of a finding, from its code and message: the conformance
/// harness's `crateCategory` (`dogwood-lean/Dogwood/Conformance/Harness.lean`),
/// which maps the crate's findings onto the categories of the specification's
/// validator. `None` for a finding no category covers (a warning, say). An
/// impossible policy is a warning of Cedar's Rust validator and an error of
/// cedar-lean's; either counts in the `cedar` category.
fn category(f: &Finding) -> Option<&'static str> {
    let m = f.message.as_str();
    let has = |t: &str| m.contains(t);
    if f.warning {
        return (f.code == "cedar" && (has("policy is impossible") || has("impossiblePolicy")))
            .then_some("cedar");
    }
    Some(match f.code.as_str() {
        "cedar" => "cedar",
        "provider" => "providers",
        "context" => "context reads",
        "schema" => "schema well-formedness",
        _ if has("does not vary with the current timepoint") => "time dependence",
        _ if m.starts_with("predicate `")
            && (has("does not name a declared event")
                || has("which is a field group")
                || has("which is not declared on that event")) =>
        {
            "event names"
        }
        _ if m.starts_with("temporal window `") => "windows",
        _ if m.starts_with("cannot sum `") => "summands",
        _ if has("binds `") && has("to the current timepoint") => "timepoints",
        _ if (has("comparison requires numeric operands")
            || m.starts_with("equality requires both sides"))
            && has("`timepoint`") =>
        {
            "timepoints"
        }
        _ if m.starts_with("equality requires both sides")
            || has("ordering requires")
            || has("comparison requires") =>
        {
            "comparison operands"
        }
        _ if m.starts_with("argument `") && has("expects") => "predicate arguments",
        _ if has("has no context field")
            || has("record has no field")
            || has("does not resolve for every entity")
            || has("accesses a field of a non-record type")
            || has("is an enum entity type")
            || has("unknown entity type")
            || has("is not a declared entity type")
            || has("is not a declared action")
            || has("does not parse as a `decimal`") =>
        {
            "paths"
        }
        _ if has("wildcard") => "placement",
        _ if has("reads the optional attribute") && has("`has` test") => "optional attributes",
        _ if m.starts_with("pin `") => "pins",
        _ if has("binds `") && has("more than once") => "binders",
        _ if has("the binder `") && has("names no declared entity type") => "binders",
        _ => return None,
    })
}

/// How shadow mode compares the two validators' findings: by category (the
/// default), or by message too (`DOGWOOD_SHADOW_FINDINGS=messages`).
fn compare_messages() -> bool {
    std::env::var("DOGWOOD_SHADOW_FINDINGS").is_ok_and(|v| v.trim() == "messages")
}

/// The first difference between the two validators' findings, if any.
///
/// By default the findings are compared as the Lean validator's correctness
/// claim and the conformance harness state their agreement: whether the set
/// validates, the categories of the error findings (the harness's
/// `crateCategory`, impossible policies included), and the dialect codes of the
/// error findings; an error finding no category covers is compared by its code
/// and message. Messages otherwise differ in form (cedar-lean reports Cedar's
/// type errors in its own words, one per rule). With
/// `DOGWOOD_SHADOW_FINDINGS=messages`, the error findings other than Cedar's are
/// compared by code and message, in order, too.
fn findings_difference(rust: &[Finding], lean: &Result<Vec<Finding>, String>) -> Option<String> {
    use std::collections::BTreeSet;
    let lean = match lean {
        Ok(l) => l,
        Err(why) => return Some(format!("the Lean validator did not run: {why}")),
    };
    let passes = |fs: &[Finding]| !fs.iter().any(|f| !f.warning);
    if passes(rust) != passes(lean) {
        let first = |fs: &[Finding]| {
            fs.iter()
                .find(|f| !f.warning)
                .map(|f| format!("{} `{}`", f.code, f.message))
                .unwrap_or_default()
        };
        return Some(if passes(rust) {
            format!(
                "the Rust validator accepts the set, the Lean validator rejects it: {}",
                first(lean)
            )
        } else {
            format!(
                "the Rust validator rejects the set ({}), the Lean validator accepts it",
                first(rust)
            )
        });
    }
    let keys = |fs: &[Finding]| -> BTreeSet<String> {
        fs.iter()
            .filter_map(|f| match (category(f), f.warning) {
                (Some(c), _) => Some(format!("{} finding in the {c} category", f.code)),
                (None, false) => Some(format!("{} finding `{}`", f.code, f.message)),
                (None, true) => None,
            })
            .collect()
    };
    let (r, l) = (keys(rust), keys(lean));
    if let Some(k) = r.difference(&l).next() {
        return Some(format!("only the Rust validator reports a {k}"));
    }
    if let Some(k) = l.difference(&r).next() {
        return Some(format!("only the Lean validator reports a {k}"));
    }
    if !compare_messages() {
        return None;
    }
    let others = |fs: &[Finding]| -> Vec<Finding> {
        fs.iter()
            .filter(|f| f.code != "cedar" && !f.warning)
            .cloned()
            .collect()
    };
    let (r, l) = (others(rust), others(lean));
    for (a, b) in r.iter().zip(&l) {
        if a.key() != b.key() {
            return Some(format!(
                "a finding differs: Rust {} `{}`, Lean {} `{}`",
                a.code, a.message, b.code, b.message
            ));
        }
    }
    (r.len() != l.len()).then(|| {
        format!(
            "the validators report {} and {} findings other than Cedar's",
            r.len(),
            l.len()
        )
    })
}

/// Validate a lowered set the Lean frontend lowered, or compared: its findings
/// ([`Frontend::Lean`]), or the Rust validator's, compared with them
/// ([`Frontend::Shadow`]). `None` for a set the Rust frontend alone lowered.
pub(crate) fn validate(lowered: &Lowered) -> Option<ValidationResult> {
    let record = lowered.lean.as_ref()?;
    match record.frontend {
        Frontend::Shadow(on_mismatch) => {
            let rust = crate::validate::validate_impl(lowered);
            let Some(difference) = findings_difference(&rust_findings(&rust), &record.findings)
            else {
                return Some(rust);
            };
            match mismatch(on_mismatch, &format!("validation: {difference}")) {
                Ok(()) => Some(rust),
                Err(e) => {
                    let (mut errors, warnings): (Vec<_>, Vec<_>) = (
                        rust.validation_errors().cloned().collect(),
                        rust.validation_warnings().cloned().collect(),
                    );
                    errors.push(ValidationError::Extension {
                        code: "frontend",
                        message: e.to_string(),
                        span: miette::SourceSpan::new(0.into(), 0),
                        label: None,
                        help: None,
                        src: finding_src(lowered),
                        source: None,
                    });
                    Some(ValidationResult::new(errors, warnings))
                }
            }
        }
        _ => Some(lean_result(lowered, &record.findings)),
    }
}
