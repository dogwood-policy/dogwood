//! The information-provider evaluator: run a provider's declared
//! implementation to produce its output value.
//!
//! Today the only implementation kind is a **sandboxed Rhai script**.
//! The engine is locked down — operation and call-depth caps, no ambient
//! file/network/process access — and the only capabilities a script has
//! are the host functions registered here ([`register_host_functions`]).
//! A bare Rhai engine cannot do I/O at all; exposing a capability is an
//! explicit, auditable act of registering a Rust function. (When real
//! leaf providers arrive — a content classifier behind an HTTP call —
//! they will be exposed the same way: a registered host function the
//! script orchestrates.)
//!
//! The type contract is enforced at the boundary, independent of the
//! script: arguments are converted from resolved [`Value`]s into Rhai
//! values, and the returned value is converted back into a [`Value`]. A
//! script can only ever produce a [`Value`]; it cannot smuggle an
//! untyped object past this seam. (Checking the produced shape against
//! the declared `outputType` is a separate validation concern, layered
//! on top.)

use std::sync::OnceLock;

use rhai::packages::Package;
use rhai::packages::{
    BasicArrayPackage, BasicMapPackage, BasicMathPackage, BitFieldPackage, CorePackage,
    LogicPackage, MoreStringPackage,
};
use rhai::{Dynamic, Engine, Map, Scope};

use super::ast::Invocation;
use super::declarations::{EntityTypeDecl, Implementation, ParamType, ProviderDecl};
use crate::interpreter::value::Value;

/// Max Rhai operations per evaluation — a runaway-script backstop so a
/// provider cannot hang the authorizer with an unbounded loop.
const MAX_OPERATIONS: u64 = 1_000_000;
/// Max nested function-call depth.
const MAX_CALL_LEVELS: usize = 64;
/// Max size (bytes) of any string a script may build. The operation counter
/// increments once per step regardless of how much a step allocates, so an
/// exponential-growth script (`s += s`) can reach gigabytes in a few hundred
/// operations — well under `MAX_OPERATIONS` — and drive the authorizer to OOM.
/// These data-size caps bound the memory a single evaluation can allocate;
/// 64 KiB / 4096 elements are far above any legitimate provider need.
const MAX_STRING_SIZE: usize = 64 * 1024;
/// Max number of elements in any array a script may build.
const MAX_ARRAY_SIZE: usize = 4096;
/// Max number of entries in any object map a script may build.
const MAX_MAP_SIZE: usize = 4096;

/// A shared, locked-down **deterministic** Rhai engine. Built once;
/// immutable thereafter. `sync` feature makes `Engine` `Send + Sync`, so a
/// single instance can back concurrent evaluations.
///
/// Determinism is a deliberate property: a provider is evaluated in the
/// authorizer's request path and re-evaluated on replay, so the same
/// inputs must always yield the same output. Rhai the language is
/// deterministic (a pure tree-walk); non-determinism can only enter via
/// registered functions or rhai's own stdlib. So instead of
/// `Engine::new()` — which bundles the full `StandardPackage`, including
/// `BasicTimePackage` (`timestamp()` / `.elapsed`, which read the system
/// clock) — we start from a bare `Engine::new_raw()` and register only the
/// *pure* standard packages. This is `StandardPackage` minus
/// `BasicTimePackage`; the guarantee lives here at the construction site
/// rather than depending on a global `no_time` Cargo feature (features are
/// additive across a dependency graph, so another consumer could re-enable
/// time). rhai 1.25's scripting stdlib exposes no RNG, so time is the only
/// impurity to exclude. The only capabilities beyond pure rhai are the
/// host functions registered below, which are themselves pure.
fn engine() -> &'static Engine {
    static ENGINE: OnceLock<Engine> = OnceLock::new();
    ENGINE.get_or_init(|| {
        let mut engine = Engine::new_raw();

        // The pure subset of `StandardPackage` (everything except
        // `BasicTimePackage`). `CorePackage` = language core + arithmetic +
        // strings + iterators + fn basics; the rest add logic, math,
        // arrays, maps, bit-fields, and extended string ops — all
        // deterministic.
        engine.register_global_module(CorePackage::new().as_shared_module());
        engine.register_global_module(LogicPackage::new().as_shared_module());
        engine.register_global_module(BasicMathPackage::new().as_shared_module());
        engine.register_global_module(BasicArrayPackage::new().as_shared_module());
        engine.register_global_module(BasicMapPackage::new().as_shared_module());
        engine.register_global_module(BitFieldPackage::new().as_shared_module());
        engine.register_global_module(MoreStringPackage::new().as_shared_module());

        engine.set_max_operations(MAX_OPERATIONS);
        engine.set_max_call_levels(MAX_CALL_LEVELS);
        // No file/module loading: a script cannot pull in other code.
        engine.set_max_modules(0);
        // Data-size caps: the operation counter alone does not bound memory
        // (one `s += s` step doubles allocation but costs one op), so cap the
        // size of any string / array / map a script can build. Without these a
        // script can OOM the host during an authorization decision.
        engine.set_max_string_size(MAX_STRING_SIZE);
        engine.set_max_array_size(MAX_ARRAY_SIZE);
        engine.set_max_map_size(MAX_MAP_SIZE);
        register_host_functions(&mut engine);
        engine
    })
}

/// Register the built-in host functions available to provider scripts.
/// These are the *only* capabilities a script has beyond pure Rhai. The
/// regex helpers are pure (no I/O) and back simple string-classification
/// providers. Under the off-by-default `net` feature, a networked
/// `http_get` is also registered — see [`register_net_functions`].
fn register_host_functions(engine: &mut Engine) {
    // `regex_is_match(pattern, text) -> bool`
    engine.register_fn("regex_is_match", |pattern: &str, text: &str| -> bool {
        regex::Regex::new(pattern)
            .map(|re| re.is_match(text))
            .unwrap_or(false)
    });

    // `regex_find(pattern, text) -> string` — the first match, or "" if
    // none / the pattern is invalid.
    engine.register_fn("regex_find", |pattern: &str, text: &str| -> String {
        regex::Regex::new(pattern)
            .ok()
            .and_then(|re| re.find(text).map(|m| m.as_str().to_string()))
            .unwrap_or_default()
    });

    // `regex_count(pattern, text) -> i64` — number of non-overlapping
    // matches (0 on an invalid pattern).
    engine.register_fn("regex_count", |pattern: &str, text: &str| -> i64 {
        regex::Regex::new(pattern)
            .map(|re| re.find_iter(text).count() as i64)
            .unwrap_or(0)
    });

    #[cfg(feature = "net")]
    register_net_functions(engine);
}

/// Register the networked host functions (feature `net`). This is what
/// makes the engine non-deterministic, which is why it is opt-in: a
/// provider script's output then depends on a remote server, so the same
/// inputs need not yield the same verdict. In spirit this is OPA/Rego's
/// `http.send` — a policy can pull a value from the web and test it.
#[cfg(feature = "net")]
fn register_net_functions(engine: &mut Engine) {
    // `http_get(url) -> string` — fetch `url` with a blocking HTTP/1.0
    // GET and return the response body (the bytes after the header
    // terminator). Returns "" on any error (bad URL, connect/read failure,
    // non-2xx) so a script can treat "no value" uniformly. Deliberately
    // minimal: `http://host[:port]/path` only — no TLS, no redirects, no
    // chunked decoding. Provider evaluation is synchronous, so the client
    // is a plain blocking `std::net` call (no async runtime). The response is
    // size-capped (see `http_get`) so a hostile server cannot exhaust memory.
    //
    // SECURITY (SSRF): `http_get` performs NO host validation — it connects to
    // whatever host the URL names, including internal/link-local addresses
    // (169.254.169.254, 127.0.0.1, RFC-1918). A provider script MUST NOT build
    // the URL — or its host/authority — from an untrusted event field, or a
    // request-supplied value can steer the fetch to an arbitrary internal
    // endpoint. Instead, keep the base URL fixed (deployer-owned) and let a
    // request field fill only a *validated*, non-authority path segment. See
    // the `net_provider` example and guide 10.
    engine.register_fn("http_get", |url: &str| -> String {
        http_get(url).unwrap_or_default()
    });
}

/// A minimal blocking HTTP/1.0 GET over `std::net`. Returns the response
/// body on a 2xx, or an `Err` describing the failure. No dependency, no
/// TLS, no redirects — enough to fetch a value from a plain-HTTP endpoint.
#[cfg(feature = "net")]
fn http_get(url: &str) -> Result<String, String> {
    use std::io::{Read, Write};
    use std::net::TcpStream;
    use std::time::Duration;

    // Parse `http://host[:port]/path`.
    let rest = url
        .strip_prefix("http://")
        .ok_or_else(|| format!("http_get: only `http://` URLs are supported: {url}"))?;
    let (authority, path) = match rest.find('/') {
        Some(i) => (&rest[..i], &rest[i..]),
        None => (rest, "/"),
    };
    let (host, port) = match authority.rsplit_once(':') {
        Some((h, p)) => (
            h,
            p.parse::<u16>()
                .map_err(|_| format!("http_get: bad port in `{authority}`"))?,
        ),
        None => (authority, 80),
    };

    let mut stream = TcpStream::connect((host, port))
        .map_err(|e| format!("http_get: connect {host}:{port}: {e}"))?;
    stream
        .set_read_timeout(Some(Duration::from_secs(5)))
        .and_then(|()| stream.set_write_timeout(Some(Duration::from_secs(5))))
        .map_err(|e| format!("http_get: set timeout: {e}"))?;

    let request =
        format!("GET {path} HTTP/1.0\r\nHost: {host}\r\nConnection: close\r\nAccept: */*\r\n\r\n");
    stream
        .write_all(request.as_bytes())
        .map_err(|e| format!("http_get: write: {e}"))?;

    // Cap the response size. A malicious or misbehaving server can otherwise
    // stream unbounded data into `read_to_end` and exhaust memory. 1 MiB is far
    // more than any value a provider should be pulling; the body is truncated at
    // the cap (a truncated 2xx body simply yields a shorter string).
    const MAX_RESPONSE_BYTES: u64 = 1 << 20;
    let mut raw = Vec::new();
    stream
        .take(MAX_RESPONSE_BYTES)
        .read_to_end(&mut raw)
        .map_err(|e| format!("http_get: read: {e}"))?;
    let response = String::from_utf8_lossy(&raw);

    // Split header block from body at the first CRLF-CRLF.
    let (headers, body) = response
        .split_once("\r\n\r\n")
        .ok_or_else(|| "http_get: malformed response (no header terminator)".to_string())?;

    // Require a 2xx status on the first line.
    let status_ok = headers
        .lines()
        .next()
        .and_then(|line| line.split_whitespace().nth(1))
        .and_then(|code| code.parse::<u16>().ok())
        .is_some_and(|code| (200..300).contains(&code));
    if !status_ok {
        let status_line = headers.lines().next().unwrap_or("");
        return Err(format!("http_get: non-2xx response: {status_line}"));
    }

    Ok(body.to_string())
}

/// Evaluate a provider invocation, returning its output [`Value`].
///
/// `decl` supplies the implementation; `args` are the already-resolved
/// call-site arguments (request fields / literals), positionally matched
/// to the script's `evaluate(arg0, …)` parameters.
pub fn evaluate(
    invocation: &Invocation,
    decl: &ProviderDecl,
    args: &[Value],
) -> Result<Value, String> {
    let key = invocation.key();
    let implementation = decl.implementation.as_ref().ok_or_else(|| {
        format!("provider `{key}` has no `implementation`; cannot evaluate it at authorize time")
    })?;

    match implementation {
        Implementation::Rhai { .. } => {
            let script = implementation.rhai_script().ok_or_else(|| {
                format!(
                    "provider `{key}`: rhai implementation has no script \
                     (a `scriptFile` reference was not resolved — load the \
                     declarations with `from_json_file`)"
                )
            })?;
            eval_rhai(&key, script, args, &decl.argument_types)
        }
    }
}

/// Run a Rhai provider script: compile it, push the converted arguments,
/// call `evaluate(arg0, …)`, and convert the result back to a [`Value`].
fn eval_rhai(
    key: &str,
    script: &str,
    args: &[Value],
    arg_types: &[ParamType],
) -> Result<Value, String> {
    let engine = engine();
    let ast = engine
        .compile(script)
        .map_err(|e| format!("provider `{key}`: script compile error: {e}"))?;

    let mut scope = Scope::new();
    let rhai_args: Vec<Dynamic> = args
        .iter()
        .enumerate()
        .map(|(i, v)| rhai_arg(v, arg_types.get(i)))
        .collect();

    let result: Dynamic = engine
        .call_fn(&mut scope, &ast, "evaluate", to_arg_tuple(rhai_args))
        .map_err(|e| format!("provider `{key}`: script error calling `evaluate`: {e}"))?;

    dynamic_to_value(&result)
        .ok_or_else(|| format!("provider `{key}`: script returned an unsupported value type"))
}

/// Run a provider's **method chain** over an already-computed base output,
/// threading the value left to right: for methods `[(m₁, a₁), …, (mₙ, aₙ)]`,
/// returns `mₙ(…m₁(base, a₁)…, aₙ)`. Each method `m` is a
/// `fn m(input, args…)` in the same Rhai script (compiled once here); its
/// first parameter is the previous stage's value, the rest its own resolved
/// arguments. A zero-argument method (`fn m(input)`) is the MFOTL-parity
/// accessor case. Any Rhai error (missing function, wrong arity, runtime
/// failure) is surfaced as an `Err` so the decision fails closed.
///
/// Each stage's value is converted to its declared type before the next
/// method runs, as [`coerce_to_declared`] does for the last stage: a value
/// outside its enum is an error here too. Otherwise a `"CRITICAL"` base would
/// reach an `isHigh` method, which returns false, and a `forbid` on it would
/// silently not fire. `entity_types` and `names` are as for
/// [`coerce_to_declared`].
///
/// The declaration's implementation must be Rhai (a resolver supplies only the
/// base, not method bodies); a missing implementation is an error.
pub fn run_methods(
    key: &str,
    decl: &ProviderDecl,
    base: Value,
    methods: &[(&str, Vec<Value>)],
    entity_types: &std::collections::BTreeMap<String, EntityTypeDecl>,
    names: &std::collections::BTreeMap<String, String>,
) -> Result<Value, String> {
    let implementation = decl.implementation.as_ref().ok_or_else(|| {
        format!(
            "provider `{key}` has a method chain but no `implementation`; \
             its methods cannot be evaluated"
        )
    })?;
    let script = match implementation {
        Implementation::Rhai { .. } => implementation.rhai_script().ok_or_else(|| {
            format!(
                "provider `{key}`: rhai implementation has no script \
                 (a `scriptFile` reference was not resolved — load the \
                 declarations with `from_json_file`)"
            )
        })?,
    };

    let engine = engine();
    let ast = engine
        .compile(script)
        .map_err(|e| format!("provider `{key}`: script compile error: {e}"))?;

    let mut current = base;
    // The declared type of `current`, the base output and then each method's
    // output, and where `current` came from, for messages.
    let mut current_ty = Some(&decl.output_type);
    let mut at = String::new();
    for (name, args) in methods {
        let mut scope = Scope::new();
        let method = decl.methods.get(*name);
        if let Some(ty) = current_ty {
            current = coerce_to_declared(key, current, ty, entity_types, names, &at)?;
        }
        // The method receives the previous stage's value first, then its own
        // resolved arguments.
        let mut rhai_args: Vec<Dynamic> = Vec::with_capacity(args.len() + 1);
        rhai_args.push(rhai_arg(&current, current_ty));
        let arg_types = method.map(|m| m.argument_types.as_slice());
        rhai_args.extend(
            args.iter()
                .enumerate()
                .map(|(i, v)| rhai_arg(v, arg_types.and_then(|t| t.get(i)))),
        );

        let result: Dynamic = engine
            .call_fn(&mut scope, &ast, name, to_arg_tuple(rhai_args))
            .map_err(|e| format!("provider `{key}`: script error calling method `{name}`: {e}"))?;

        current = dynamic_to_value(&result).ok_or_else(|| {
            format!("provider `{key}`: method `{name}` returned an unsupported value type")
        })?;
        current_ty = method.map(|m| &m.output_type);
        at = format!(".{name}()");
    }
    Ok(current)
}

/// Rhai's `call_fn` takes the arguments as a tuple-like `impl FuncArgs`.
/// A `Vec<Dynamic>` implements `FuncArgs`, so this is just a passthrough
/// kept as a named seam for clarity.
fn to_arg_tuple(args: Vec<Dynamic>) -> Vec<Dynamic> {
    args
}

/// Convert a provider's final value to its declared type, turning each
/// enum id at an `entity` slot into the entity `Ns::Type::"id"`.
///
/// An enum is closed, as in Cedar: an id that is not one of its values, or a
/// value of the wrong kind at an `entity` slot, is an error, which denies the
/// request. Without this, `"CRITICAL"` would become a well-typed entity that
/// matches nothing, and a `forbid … == HIGH` would silently not fire. Slots
/// that are not entities are left unchanged; sets and records are walked.
///
/// A set or record whose type contains an enum must also have its declared
/// shape: a value of another kind (a bare `"HIGH"` for a record), or a missing
/// required enum field, is an error too. Otherwise Cedar fails on the field,
/// skips the policy reading it, and the `forbid` silently doesn't fire. Types
/// without an enum keep the loose behaviour.
/// `entity_types` holds the enums the field's provider references, and
/// `names` the name each is exported under: the converted entity has the
/// exported type, the one the hoisted field is typed by. Messages use the
/// declared name.
pub(crate) fn coerce_to_declared(
    key: &str,
    value: Value,
    ty: &ParamType,
    entity_types: &std::collections::BTreeMap<String, EntityTypeDecl>,
    names: &std::collections::BTreeMap<String, String>,
    at: &str,
) -> Result<Value, String> {
    match ty.param_type.as_str() {
        "entity" => {
            let name = ty.entity_type.as_deref().unwrap_or_default();
            let decl = entity_types.get(name).ok_or_else(|| {
                format!("provider `{key}`{at}: no declaration for entity type `{name}`")
            })?;
            let exported = names.get(name).map(String::as_str).unwrap_or(name);
            let id = match value {
                Value::String(id) => id,
                // A resolver may return the entity under either name.
                Value::Entity { ty, id } if ty == name || ty == exported => id,
                Value::Entity { ty, .. } => {
                    return Err(format!(
                        "provider `{key}`{at}: expected a `{name}`, got a `{ty}`"
                    ));
                }
                other => {
                    return Err(format!(
                        "provider `{key}`{at}: expected a `{name}` id (a string), got {}",
                        value_kind(&other)
                    ));
                }
            };
            if decl.values.contains(&id) {
                Ok(Value::Entity {
                    ty: exported.to_string(),
                    id,
                })
            } else {
                Err(format!(
                    "provider `{key}`{at}: `{id}` is not a member of `{name}`"
                ))
            }
        }
        "set" => match (value, ty.items.as_deref()) {
            (Value::Array(items), Some(item_ty)) => items
                .into_iter()
                .enumerate()
                .map(|(i, v)| {
                    coerce_to_declared(key, v, item_ty, entity_types, names, &format!("{at}[{i}]"))
                })
                .collect::<Result<_, _>>()
                .map(Value::Array),
            (other, _) if ty.mentions_entity() => Err(format!(
                "provider `{key}`{at}: expected a set, got {}",
                value_kind(&other)
            )),
            (other, _) => Ok(other),
        },
        "record" => match value {
            Value::Object(mut fields) => {
                for (name, field_ty) in &ty.fields {
                    if field_ty.mentions_entity()
                        && ty.required.contains(name)
                        && !fields.contains_key(name)
                    {
                        return Err(format!(
                            "provider `{key}`{at}: missing required field `{name}`"
                        ));
                    }
                    if let Some(v) = fields.remove(name) {
                        let v = coerce_to_declared(
                            key,
                            v,
                            field_ty,
                            entity_types,
                            names,
                            &format!("{at}.{name}"),
                        )?;
                        fields.insert(name.clone(), v);
                    }
                }
                Ok(Value::Object(fields))
            }
            other if ty.mentions_entity() => Err(format!(
                "provider `{key}`{at}: expected a record, got {}",
                value_kind(&other)
            )),
            other => Ok(other),
        },
        _ => Ok(value),
    }
}

/// A short name for a value's kind, for conversion errors.
fn value_kind(v: &Value) -> &'static str {
    match v {
        Value::Null => "no value",
        Value::Bool(_) => "a bool",
        Value::Int(_) => "an integer",
        Value::Decimal(_) => "a decimal",
        Value::String(_) => "a string",
        Value::Entity { .. } => "an entity",
        Value::Array(_) => "a set",
        Value::Object(_) => "a record",
    }
}

/// Convert one argument for a Rhai script, by its declared type: an entity
/// at an `entity` slot is passed as its bare id (`"high"`), the same form a
/// script returns enum values in. Sets and records are walked, so the slot may
/// be nested at any depth. Rhai has no entity type; without a declared
/// `entity` type (an undeclared record field, an untyped argument) an entity
/// is passed as its uid text, as before.
fn rhai_arg(value: &Value, ty: Option<&ParamType>) -> Dynamic {
    match (value, ty) {
        (Value::Entity { id, .. }, Some(t)) if t.param_type == "entity" => {
            Dynamic::from(id.clone())
        }
        (Value::Array(items), Some(t)) if t.param_type == "set" => {
            let item_ty = t.items.as_deref();
            let arr: rhai::Array = items.iter().map(|v| rhai_arg(v, item_ty)).collect();
            Dynamic::from(arr)
        }
        (Value::Object(fields), Some(t)) if t.param_type == "record" => {
            let mut m = Map::new();
            for (k, v) in fields {
                m.insert(k.as_str().into(), rhai_arg(v, t.fields.get(k)));
            }
            Dynamic::from(m)
        }
        _ => value_to_dynamic(value),
    }
}

/// Convert a resolved [`Value`] into a Rhai [`Dynamic`] for passing into
/// a script.
fn value_to_dynamic(v: &Value) -> Dynamic {
    match v {
        Value::Null => Dynamic::UNIT,
        Value::Bool(b) => Dynamic::from(*b),
        Value::Int(n) => Dynamic::from(*n),
        Value::Decimal(s) => match s.parse::<rust_decimal::Decimal>() {
            Ok(d) => Dynamic::from_decimal(d),
            // Fall back to the text so a script can still inspect it.
            Err(_) => Dynamic::from(s.clone()),
        },
        Value::String(s) => Dynamic::from(s.clone()),
        Value::Entity { ty, id } => {
            Dynamic::from(crate::interpreter::value::entity_uid_string(ty, id))
        }
        Value::Array(items) => {
            let arr: rhai::Array = items.iter().map(value_to_dynamic).collect();
            Dynamic::from(arr)
        }
        Value::Object(map) => {
            let mut m = Map::new();
            for (k, val) in map {
                m.insert(k.as_str().into(), value_to_dynamic(val));
            }
            Dynamic::from(m)
        }
    }
}

/// Convert a Rhai [`Dynamic`] returned by a script into a [`Value`].
/// Returns `None` for a type we don't model (so the caller reports a
/// clean error rather than panicking).
fn dynamic_to_value(d: &Dynamic) -> Option<Value> {
    if d.is_unit() {
        return Some(Value::Null);
    }
    if d.is_bool() {
        return Some(Value::Bool(d.as_bool().unwrap()));
    }
    if d.is_int() {
        return Some(Value::Int(d.as_int().unwrap()));
    }
    if d.is_decimal() {
        // Render with Cedar-decimal text semantics (canonicalized on
        // comparison downstream).
        let dec = d.as_decimal().unwrap();
        return Some(Value::Decimal(dec.to_string()));
    }
    if d.is_string() {
        return Some(Value::String(d.clone().into_string().unwrap()));
    }
    if d.is_array() {
        let arr = d.clone().into_array().unwrap();
        let items: Option<Vec<Value>> = arr.iter().map(dynamic_to_value).collect();
        return items.map(Value::Array);
    }
    if d.is_map() {
        let map = d.read_lock::<Map>()?;
        let mut out = std::collections::BTreeMap::new();
        for (k, v) in map.iter() {
            out.insert(k.to_string(), dynamic_to_value(v)?);
        }
        return Some(Value::Object(out));
    }
    None
}

#[cfg(test)]
mod tests {
    use super::engine;

    mod enum_conversion {
        use super::super::coerce_to_declared;
        use crate::extension::provider::declarations::{EntityTypeDecl, ParamType};
        use crate::interpreter::value::Value;
        use std::collections::BTreeMap;

        fn convert(value: Value) -> Result<Value, String> {
            convert_as(
                r#"{ "paramType": "entity", "entityType": "GuardDuty::Severity" }"#,
                value,
            )
        }

        fn convert_as(ty: &str, value: Value) -> Result<Value, String> {
            let ty: ParamType = serde_json::from_str(ty).unwrap();
            let decls = BTreeMap::from([(
                "GuardDuty::Severity".to_string(),
                EntityTypeDecl {
                    values: vec!["LOW".into(), "HIGH".into()],
                    annotations: BTreeMap::new(),
                },
            )]);
            let names = BTreeMap::from([(
                "GuardDuty::Severity".to_string(),
                "Drupe::GuardDuty_Severity".to_string(),
            )]);
            coerce_to_declared("GuardDuty::ThreatDetector", value, &ty, &decls, &names, "")
        }

        const ENUM_RECORD: &str = r#"{ "paramType": "record", "required": ["severity"],
            "fields": { "severity": { "paramType": "entity", "entityType": "GuardDuty::Severity" } } }"#;
        const STRING_RECORD: &str = r#"{ "paramType": "record", "required": ["severity"],
            "fields": { "severity": { "paramType": "string" } } }"#;

        fn exported(id: &str) -> Value {
            Value::Entity {
                ty: "Drupe::GuardDuty_Severity".into(),
                id: id.into(),
            }
        }

        #[test]
        fn ids_convert_to_the_exported_type() {
            assert_eq!(convert(Value::String("HIGH".into())), Ok(exported("HIGH")));
        }

        #[test]
        fn resolvers_may_return_either_name() {
            let declared = Value::Entity {
                ty: "GuardDuty::Severity".into(),
                id: "LOW".into(),
            };
            assert_eq!(convert(declared), Ok(exported("LOW")));
            assert_eq!(convert(exported("LOW")), Ok(exported("LOW")));
        }

        #[test]
        fn messages_use_the_declared_name() {
            assert_eq!(
                convert(Value::String("CRITICAL".into())),
                Err(
                    "provider `GuardDuty::ThreatDetector`: `CRITICAL` is not a member of \
                     `GuardDuty::Severity`"
                        .into()
                )
            );
        }

        #[test]
        fn a_bare_value_for_an_enum_record_is_an_error() {
            assert_eq!(
                convert_as(ENUM_RECORD, Value::String("HIGH".into())),
                Err("provider `GuardDuty::ThreatDetector`: expected a record, got a string".into())
            );
        }

        #[test]
        fn a_missing_required_enum_field_is_an_error() {
            let value = Value::Object(BTreeMap::from([(
                "score".to_string(),
                Value::String("HIGH".into()),
            )]));
            assert_eq!(
                convert_as(ENUM_RECORD, value),
                Err(
                    "provider `GuardDuty::ThreatDetector`: missing required field `severity`"
                        .into()
                )
            );
        }

        #[test]
        fn a_bare_value_for_an_enum_set_is_an_error() {
            let ty = r#"{ "paramType": "set",
                "items": { "paramType": "entity", "entityType": "GuardDuty::Severity" } }"#;
            assert_eq!(
                convert_as(ty, Value::String("HIGH".into())),
                Err("provider `GuardDuty::ThreatDetector`: expected a set, got a string".into())
            );
        }

        #[test]
        fn types_without_an_enum_keep_the_loose_shape() {
            let bare = Value::String("HIGH".into());
            assert_eq!(convert_as(STRING_RECORD, bare.clone()), Ok(bare));
            let empty = Value::Object(BTreeMap::new());
            assert_eq!(convert_as(STRING_RECORD, empty.clone()), Ok(empty));
        }
    }

    /// An enum reaches a script as its bare id at any depth of its declared
    /// type, not as uid text a script comparing against `"high"` misses.
    mod enum_arguments {
        use super::super::{dynamic_to_value, rhai_arg};
        use crate::extension::provider::declarations::ParamType;
        use crate::interpreter::value::Value;
        use std::collections::BTreeMap;

        fn pass(ty: &str, value: &Value) -> Value {
            let ty: ParamType = serde_json::from_str(ty).unwrap();
            dynamic_to_value(&rhai_arg(value, Some(&ty))).unwrap()
        }

        fn level(id: &str) -> Value {
            Value::Entity {
                ty: "Drupe::AlertLevel".into(),
                id: id.into(),
            }
        }

        fn bare(id: &str) -> Value {
            Value::String(id.into())
        }

        fn record(fields: &[(&str, Value)]) -> Value {
            Value::Object(
                fields
                    .iter()
                    .map(|(k, v)| (k.to_string(), v.clone()))
                    .collect::<BTreeMap<_, _>>(),
            )
        }

        const LEVEL: &str = r#"{ "paramType": "entity", "entityType": "Drupe::AlertLevel" }"#;

        #[test]
        fn a_record_field_is_passed_as_its_id() {
            let ty = format!(r#"{{ "paramType": "record", "fields": {{ "level": {LEVEL} }} }}"#);
            assert_eq!(
                pass(&ty, &record(&[("level", level("high"))])),
                record(&[("level", bare("high"))])
            );
        }

        #[test]
        fn nested_sets_and_records_are_walked() {
            // set<record { levels: set<entity>, inner: record { level: entity } }>
            let ty = format!(
                r#"{{ "paramType": "set", "items": {{ "paramType": "record", "fields": {{
                    "levels": {{ "paramType": "set", "items": {LEVEL} }},
                    "inner": {{ "paramType": "record", "fields": {{ "level": {LEVEL} }} }}
                }} }} }}"#
            );
            let value = Value::Array(vec![record(&[
                ("levels", Value::Array(vec![level("low"), level("high")])),
                ("inner", record(&[("level", level("high"))])),
            ])]);
            assert_eq!(
                pass(&ty, &value),
                Value::Array(vec![record(&[
                    ("levels", Value::Array(vec![bare("low"), bare("high")])),
                    ("inner", record(&[("level", bare("high"))])),
                ])])
            );
        }

        #[test]
        fn an_undeclared_field_keeps_the_uid_text() {
            let ty = r#"{ "paramType": "record", "fields": {} }"#;
            assert_eq!(
                pass(ty, &record(&[("level", level("high"))])),
                record(&[("level", bare("Drupe::AlertLevel::\"high\""))])
            );
        }
    }

    /// The provider engine must be deterministic: `timestamp()` (the one
    /// impure function rhai's `StandardPackage` ships) must NOT be
    /// reachable, so a provider script cannot read the wall clock.
    #[test]
    fn timestamp_is_not_reachable() {
        let err = engine()
            .eval::<rhai::Dynamic>("timestamp()")
            .expect_err("timestamp() must not be callable in the deterministic engine");
        // A missing function is a "function not found" evaluation error.
        let msg = err.to_string();
        assert!(
            msg.contains("timestamp"),
            "expected an unresolved-`timestamp` error, got: {msg}"
        );
    }

    /// Positive control: the pure facilities provider scripts rely on
    /// (arithmetic, strings, arrays, maps, `for` iteration) are present, so
    /// pruning to `StandardPackage` minus time didn't remove anything real.
    #[test]
    fn pure_facilities_are_present() {
        let out = engine()
            .eval::<i64>(
                r#"
                let m = #{ a: 1, b: 2 };
                let total = 0;
                for k in m.keys() { total += m[k]; }
                let xs = [10, 20, 30];
                total + xs.len() + "abc".len()
                "#,
            )
            .expect("pure script evaluates");
        // 1 + 2 (map values) + 3 (array len) + 3 ("abc".len) = 9.
        assert_eq!(out, 9);
    }
}
