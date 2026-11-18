//! Tests of the Lean frontend's bridge: the FFI (initialization, threads, panics),
//! the decoder (it inverts the observables' encoding on the crate's own lowered
//! sets), the error and finding mappings, and the three frontend modes.

use super::*;
use crate::{
    Frontend, LoweredPolicySet, OnMismatch, ParsedPolicySet, PolicySchema, ServiceSchema, Validator,
};

const SCHEMA: &str = r#"
namespace Drupe {
  type ReadInput = { user: String, amount: Long };
  entity Gateway;
  entity OAuthUser = { id: String, level?: Long };
  action "Login" appliesTo {
    principal: [OAuthUser],
    resource: [Gateway],
    context: { input: ReadInput }
  };
  action "Read" appliesTo {
    principal: [OAuthUser],
    resource: [Gateway],
    context: { input: ReadInput }
  };
}
"#;

const POLICY: &str = r#"
@id("read-after-login")
permit (principal, action == Drupe::Action::"Read", resource)
when temporal {
    formerly within 1h Drupe::Action::"Login"::response{ input.user: context.input.user }
}
unless { context.input.amount > 10 && principal.id != "root" };
"#;

fn service(frontend: Frontend) -> ServiceSchema {
    ServiceSchema::builder().frontend(frontend).build().unwrap()
}

fn schema() -> PolicySchema {
    PolicySchema::from_cedarschema_str(SCHEMA).unwrap()
}

// ─── The runtime ────────────────────────────────────────────────────────

#[test]
fn ping_round_trips_any_text() {
    for s in ["", "hello", "ünïcödé ✓", &"x".repeat(1 << 20)] {
        assert_eq!(runtime::call(runtime::Entry::Ping, s).unwrap(), s);
    }
}

#[test]
fn a_lean_panic_is_a_bug_reply_not_a_default_value() {
    assert_eq!(
        runtime::call(runtime::Entry::PanicProbe, "fine").unwrap(),
        r#"{"ok":"fine"}"#
    );
    let reply = runtime::call(runtime::Entry::PanicProbe, "panic").unwrap();
    assert!(
        reply.starts_with(r#"{"bug":"the Lean frontend panicked: PANIC"#),
        "{reply}"
    );
    // The runtime is still usable.
    assert_eq!(
        runtime::call(runtime::Entry::Ping, "after").unwrap(),
        "after"
    );
}

#[test]
fn a_malformed_request_is_an_export_error() {
    let reply = runtime::call(runtime::Entry::Lower, "{not json").unwrap();
    let reply = parse_json(&reply).unwrap();
    let e = LeanError::of_json(get(&reply, "error").unwrap(), None).unwrap();
    assert_eq!(e.category, "export");
    // The crate has no variant for it: it is the Lean frontend's failure.
    match lean_error(&e, &[]) {
        Error::Frontend(f) => assert_eq!(f.kind(), FrontendErrorKind::Lean),
        other => panic!("{other:?}"),
    }
}

#[test]
fn many_threads_call_in_at_once() {
    let handles: Vec<_> = (0..16)
        .map(|i| {
            std::thread::spawn(move || {
                for j in 0..20 {
                    let s = format!("{i}-{j}");
                    assert_eq!(runtime::call(runtime::Entry::Ping, &s).unwrap(), s);
                }
            })
        })
        .collect();
    for h in handles {
        h.join().unwrap();
    }
}

// ─── The decoder ────────────────────────────────────────────────────────

/// The crate's own lowering of `policy` against `schema`, its observables, and
/// the observables of its decoding.
fn round_trip(policy: &str, schema_src: &str, service: &ServiceSchema) -> (Json, Json) {
    let parsed = ParsedPolicySet::parse(policy, service).unwrap();
    let schema = PolicySchema::from_cedarschema_str(schema_src).unwrap();
    let (lowered, identity) = crate::api::lower(parsed.parsed(), &schema, None).unwrap();
    let observed = observe::lowered(&lowered, &identity);
    let sources = decode::Sources {
        entries: vec![parsed.parsed().dw_src()],
    };
    let (decoded, decoded_identity) = decode::lowered(&observed, &sources).unwrap();
    (observed, observe::lowered(&decoded, &decoded_identity))
}

#[test]
fn decoding_inverts_the_observables() {
    let (a, b) = round_trip(POLICY, SCHEMA, &service(Frontend::Rust));
    assert_eq!(observe::first_difference(&a, &b), None);
}

/// A sample of the corpus bundles of `group`: each bundle's policy, service
/// schema and action schema, read as the conformance bridge reads them.
fn corpus(group: &str, shared: Option<&str>) -> Vec<(String, ServiceSchema, PolicySchema)> {
    let manifest = std::path::Path::new(env!("CARGO_MANIFEST_DIR"));
    let root = manifest.join("tests").join(group);
    let read = |p: std::path::PathBuf| std::fs::read_to_string(p).ok();
    let shared = shared.and_then(|f| read(root.join(f))).unwrap_or_default();
    let events = read(manifest.join("tests/fixtures/request_response.dwschema")).unwrap();
    let mut dirs: Vec<_> = std::fs::read_dir(root.join("corpus"))
        .unwrap()
        .filter_map(|e| e.ok().map(|e| e.path()))
        .filter(|p| p.is_dir())
        .collect();
    dirs.sort();
    let mut out = Vec::new();
    for dir in dirs.iter().step_by(4) {
        let policy = read(dir.join("policy.dw")).unwrap_or_else(|| {
            let mut parts: Vec<_> = std::fs::read_dir(dir)
                .unwrap()
                .filter_map(|e| e.ok().map(|e| e.path()))
                .filter(|p| {
                    p.extension().is_some_and(|e| e == "dw")
                        && p.file_name()
                            .and_then(|n| n.to_str())
                            .is_some_and(|n| n.starts_with("policy_"))
                })
                .collect();
            parts.sort();
            parts
                .into_iter()
                .filter_map(read)
                .collect::<Vec<_>>()
                .join("\n")
        });
        let schema = read(dir.join("schema.cedarschema")).unwrap_or_else(|| shared.clone());
        let event_schema = read(dir.join("event.dwschema"))
            .or_else(|| read(dir.join("events.dwschema")))
            .unwrap_or_else(|| events.clone());
        let mut builder = ServiceSchema::builder()
            .frontend(Frontend::Rust)
            .event_schema_str(&event_schema);
        if let Some(p) = read(dir.join("providers.json")) {
            match crate::ProviderDeclarations::from_json(&p) {
                Ok(d) => builder = builder.providers(d),
                Err(_) => continue,
            }
        }
        if let Some(m) = read(dir.join("macros.dw")) {
            builder = builder.macros_str(&m);
        }
        let (Ok(service), Ok(schema)) =
            (builder.build(), PolicySchema::from_cedarschema_str(&schema))
        else {
            continue;
        };
        out.push((policy, service, schema));
    }
    out
}

#[test]
fn decoding_inverts_the_observables_on_the_corpora() {
    let mut decoded = 0;
    for (group, shared) in [
        ("passing/temporal_only", Some("shared_schema.cedarschema")),
        ("passing/provider_only", Some("shared_schema.cedarschema")),
        ("passing/macros", None),
        ("passing/mixed", None),
    ] {
        for (policy, service, schema) in corpus(group, shared) {
            let Ok(parsed) = ParsedPolicySet::parse(&policy, &service) else {
                continue;
            };
            let Ok((lowered, identity)) = crate::api::lower(parsed.parsed(), &schema, None) else {
                continue;
            };
            let observed = observe::lowered(&lowered, &identity);
            let sources = decode::Sources {
                entries: vec![parsed.parsed().dw_src()],
            };
            let (back, back_identity) = decode::lowered(&observed, &sources)
                .unwrap_or_else(|e| panic!("{group}: {e}\n{policy}"));
            let again = observe::lowered(&back, &back_identity);
            assert_eq!(
                observe::first_difference(&observed, &again),
                None,
                "{group}\n{policy}"
            );
            decoded += 1;
        }
    }
    assert!(decoded > 100, "only {decoded} bundles decoded");
}

// ─── The modes ──────────────────────────────────────────────────────────

#[test]
fn the_lean_frontend_lowers_and_validates_a_policy() {
    let lean = LoweredPolicySet::from_str(POLICY, &service(Frontend::Lean), &schema()).unwrap();
    let rust = LoweredPolicySet::from_str(POLICY, &service(Frontend::Rust), &schema()).unwrap();
    assert_eq!(lean.as_cedar().to_string(), rust.as_cedar().to_string());
    assert_eq!(
        lean.temporal_fields().collect::<Vec<_>>(),
        rust.temporal_fields().collect::<Vec<_>>()
    );
    assert!(Validator::new().validate(&lean).validation_passed());
}

#[test]
fn the_shadow_frontend_agrees_on_a_policy() {
    let shadow = service(Frontend::Shadow(OnMismatch::Fail));
    let lowered = LoweredPolicySet::from_str(POLICY, &shadow, &schema()).unwrap();
    let result = Validator::new().validate(&lowered);
    assert!(result.validation_passed(), "{result:?}");
}

/// Lower `policy` in every mode: the Lean frontend's set and the Rust frontend's
/// agree on every observable, and shadow mode agrees.
fn agree(policy: &str, schema_src: &str) {
    agree_with(policy, schema_src, &crate::ParseOptions::default());
}

/// [`agree`], parsing under `options`.
fn agree_with(policy: &str, schema_src: &str, options: &crate::ParseOptions) {
    let schema = PolicySchema::from_cedarschema_str(schema_src).unwrap();
    let lower = |frontend| {
        LoweredPolicySet::from_str_with(policy, &service(frontend), &schema, options).unwrap()
    };
    let rust = lower(Frontend::Rust);
    let lean = lower(Frontend::Lean);
    let (r, ri) = rust.into_parts();
    let (l, li) = lean.into_parts();
    let difference =
        observe::first_difference(&observe::lowered(&r, &ri), &observe::lowered(&l, &li));
    assert_eq!(difference, None);
    let shadow = service(Frontend::Shadow(OnMismatch::Fail));
    let lowered = LoweredPolicySet::from_str_with(policy, &shadow, &schema, options).unwrap();
    let result = Validator::new().validate(&lowered);
    assert!(
        !result.validation_errors().any(|e| matches!(
            e,
            ValidationError::Extension {
                code: "frontend",
                ..
            }
        )),
        "{result:?}"
    );
}

#[test]
fn a_deeply_nested_policy_lowers_on_the_big_stack() {
    // 150 nested conjunctions in a temporal block: far deeper than serde_json's
    // default recursion limit once encoded, and than the default depth limit
    // (`ParseOptions::max_depth`), which the test raises. The Rust frontend's
    // side of the comparison recurses too, so the test runs on a big stack of
    // its own.
    let run = || {
        let leaf = |field: &str, value: &str| {
            format!("formerly within 1h Drupe::Action::\"Login\"::response{{ {field}: {value} }}")
        };
        let mut body = leaf("input.user", "context.input.user");
        for _ in 0..150 {
            body = format!("({body} && {})", leaf("input.amount", "1"));
        }
        let policy = format!(
            "permit (principal, action == Drupe::Action::\"Read\", resource) when temporal {{ {body} }};"
        );
        agree_with(&policy, SCHEMA, &crate::ParseOptions::default().max_depth(1024));
    };
    std::thread::Builder::new()
        .stack_size(256 * 1024 * 1024)
        .spawn(run)
        .unwrap()
        .join()
        .unwrap();
}

#[test]
fn lean_errors_become_the_crates_errors() {
    let schema = schema();
    for (policy, check) in [
        // A macro error, located in the policy source.
        (
            "permit (principal, action, resource) when { undefined_macro(1) };",
            (|e: &Error| matches!(e, Error::Macro(_))) as fn(&Error) -> bool,
        ),
        // A lowering error.
        (
            "permit (principal, action == Drupe::Action::\"Read\", resource) when temporal { formerly within 1h Drupe::Action::\"Login\"::response{ input.tags: [\"a\"] } };",
            |e: &Error| matches!(e, Error::Cedarify(_)),
        ),
    ] {
        let lean =
            ParsedPolicySet::parse(policy, &service(Frontend::Lean)).and_then(|p| p.lower(&schema));
        let rust =
            ParsedPolicySet::parse(policy, &service(Frontend::Rust)).and_then(|p| p.lower(&schema));
        let (lean, rust) = (lean.unwrap_err(), rust.unwrap_err());
        assert!(check(&rust), "{rust:?}");
        assert!(check(&lean), "{lean:?}");
        assert_eq!(error_observable(&lean), error_observable(&rust));
    }
    // An action schema Cedar cannot parse fails at derivation, as in the crate.
    let bad = PolicySchema::from_cedarschema_str("namespace {").unwrap();
    let lean = LoweredPolicySet::from_str(POLICY, &service(Frontend::Lean), &bad).unwrap_err();
    let rust = LoweredPolicySet::from_str(POLICY, &service(Frontend::Rust), &bad).unwrap_err();
    assert!(matches!(lean, Error::EventSchema(_)), "{lean:?}");
    assert_eq!(error_observable(&lean), error_observable(&rust));
}

#[test]
fn the_merge_duplicate_id_error_is_cedars_own() {
    match duplicate_policy_id("x") {
        Some(Error::PolicySet(e)) => assert!(e.to_string().contains('x'), "{e}"),
        other => panic!("{other:?}"),
    }
}

#[test]
fn stable_ids_distincters_and_several_sets_agree() {
    use crate::{Distincter, IdSource};
    let schema = schema();
    for frontend in [Frontend::Lean, Frontend::Shadow(OnMismatch::Fail)] {
        let s = service(frontend);
        // Stable ids from the annotation, under a distincter.
        let parsed = ParsedPolicySet::parse(POLICY, &s)
            .unwrap()
            .with_ids(IdSource::Annotation)
            .unwrap();
        assert_eq!(
            parsed.policies().next().unwrap().policy_id(),
            Some("read-after-login")
        );
        let lowered = parsed.lower_with_distincter(&schema, "d").unwrap();
        assert_eq!(
            lowered.rules().next().unwrap().cedar_policy_id,
            "d/read-after-login"
        );
        assert!(lowered.has_stable_ids());
        // A rejected id source: the Lean frontend's error is the crate's.
        let e = ParsedPolicySet::parse("permit (principal, action, resource);", &s)
            .unwrap()
            .with_ids(IdSource::Annotation)
            .unwrap_err();
        assert!(
            matches!(e, Error::PolicyId(ref p) if p.kind() == crate::PolicyIdErrorKind::Missing),
            "{e:?}"
        );
        // Several sets lowered together.
        let a = ParsedPolicySet::parse(POLICY, &s).unwrap();
        let b = ParsedPolicySet::parse(
            "forbid (principal, action, resource) when { context.input.amount > 100 };",
            &s,
        )
        .unwrap();
        let many = crate::lower_many(
            &[
                (&a, Distincter::try_from("a").unwrap()),
                (&b, Distincter::try_from("b").unwrap()),
            ],
            &schema,
        )
        .unwrap();
        assert_eq!(many.rules().count(), 2);
        assert!(Validator::new().validate(&many).validation_passed());
        // A repeated distincter.
        let e = crate::lower_many(
            &[
                (&a, Distincter::try_from("a").unwrap()),
                (&b, Distincter::try_from("a").unwrap()),
            ],
            &schema,
        )
        .unwrap_err();
        assert!(matches!(e, Error::DuplicateDistincter(_)), "{e:?}");
    }
}

#[test]
fn a_frontend_the_build_cannot_run_is_rejected_without_the_feature() {
    // With the feature every frontend builds; the rejection itself is checked by
    // the default build's tests of `frontend`.
    for f in [
        Frontend::Rust,
        Frontend::Lean,
        Frontend::Shadow(OnMismatch::Log),
    ] {
        assert_eq!(
            ServiceSchema::builder()
                .frontend(f)
                .build()
                .unwrap()
                .frontend(),
            f
        );
    }
}

// ─── Escaping ───────────────────────────────────────────────────────────

/// The characters at which Rust's escaping changes: each scalar value where
/// `char::escape_debug` (which escapes a character that is not printable or
/// extends a grapheme) or a string's `escape_debug` after its first character
/// (which escapes one that is not printable) starts or stops writing `\u{…}`,
/// with its neighbours. The Lean frontend's tables decide exactly these.
fn escape_boundaries() -> Vec<char> {
    let unicode = |c: char| c.escape_debug().to_string().starts_with("\\u{");
    let after_first = |c: char| format!("a{c}").escape_debug().to_string()[1..].starts_with("\\u{");
    let mut out = std::collections::BTreeSet::new();
    let mut previous = (false, false);
    for x in 0..=0x10ffffu32 {
        let Some(c) = char::from_u32(x) else { continue };
        let now = (unicode(c), after_first(c));
        if now != previous {
            for y in [x.saturating_sub(1), x, x + 1] {
                out.extend(char::from_u32(y));
            }
            previous = now;
        }
    }
    out.into_iter().collect()
}

/// `chars` in a Dogwood string literal: raw, except what the literal must escape.
fn literal(chars: &[char], pattern: bool) -> String {
    chars
        .iter()
        .map(|&c| match c {
            '"' | '\\' => format!("\\{c}"),
            '*' if pattern => "\\*".to_string(),
            c if (c as u32) < 0x20 || c == '\u{7f}' => format!("\\u{{{:x}}}", c as u32),
            c => c.to_string(),
        })
        .collect()
}

const ESCAPE_PROVIDERS: &str = r#"{
  "availableProviders": {
    "Strings::Matches": {
      "argumentTypes": [{ "paramType": "string" }, { "paramType": "string" }],
      "outputType": {
        "paramType": "record",
        "fields": { "matched": { "paramType": "bool" } },
        "required": ["matched"]
      }
    }
  }
}"#;

/// Lower, in shadow mode (which fails on any difference of the lowered sets, and
/// panics on one of their identity values), rules that print `chars` as Cedar
/// does: in a string, a pattern, an entity id, an attribute name, an annotation,
/// and a provider argument (which a rule's revision prints with `{:?}`), each
/// chunk of the characters first in a string and after another character.
fn escaping_agrees_on(chars: &[char]) {
    let mut policy = String::new();
    for chunk in chars.chunks(512) {
        let s = literal(chunk, false);
        let p = literal(chunk, true);
        policy.push_str(&format!(
            "@note(\"{s}\")\n\
             permit (principal == Drupe::OAuthUser::\"{s}\", action == Drupe::Action::\"Read\", resource)\n\
             when {{ context.input.user == \"{s}\" || context.input.user == \"x{s}\" }}\n\
             when {{ context.input.user like \"{p}\" || context has \"{s}\" }}\n\
             when guardrails {{ Strings::Matches(context.input.user, \"{s}\").matched == true }};\n"
        ));
    }
    let schema = schema();
    let declarations = crate::ProviderDeclarations::from_json(ESCAPE_PROVIDERS).unwrap();
    let lowered = |f| {
        let service = ServiceSchema::builder()
            .frontend(f)
            .providers(declarations.clone())
            .build()
            .unwrap();
        LoweredPolicySet::from_str(&policy, &service, &schema).unwrap()
    };
    let revisions = |set: &LoweredPolicySet| {
        set.policy_refs()
            .map(|r| r.revision().to_string())
            .collect::<Vec<_>>()
    };
    let (rust, lean) = (
        revisions(&lowered(Frontend::Rust)),
        revisions(&lowered(Frontend::Lean)),
    );
    if let Some(k) = (0..rust.len()).find(|&k| rust.get(k) != lean.get(k)) {
        let chunk = chars.chunks(512).nth(k).unwrap_or_default();
        panic!(
            "the Rust and Lean frontends print the strings of rule {k} (code points U+{:04X} to \
             U+{:04X}) differently. The Lean frontend escapes with the Unicode tables of Rust {} \
             (dogwood-lean/Dogwood/Frontend/UnicodeTables.lean), and this crate is compiled with \
             Rust {}. Regenerate the tables for this compiler: set RUST_VERSION in \
             dogwood-lean/scripts/gen_unicode_tables.py to its release, and run \
             `scripts/gen_unicode_tables.py --verify` in dogwood-lean/ with its rustc on PATH. \
             Until then, `scripts/gen_unicode_tables.py --changes <toolchain>` lists the \
             characters the two releases escape differently, which this test leaves out.",
            chunk.first().map_or(0, |&c| u32::from(c)),
            chunk.last().map_or(0, |&c| u32::from(c)),
            env!("DOGWOOD_LEAN_TABLES_RUST"),
            env!("DOGWOOD_LEAN_RUSTC"),
        );
    }
    // Shadow mode compares every other observable, and fails on a difference.
    let shadow = revisions(&lowered(Frontend::Shadow(OnMismatch::Fail)));
    assert_eq!(rust, shadow);
}

#[test]
fn escaping_agrees_at_every_boundary_of_the_unicode_tables() {
    let chars = without_release_changes(escape_boundaries());
    assert!(chars.len() > 3000, "{} boundary characters", chars.len());
    escaping_agrees_on(&chars);
}

/// Every Unicode scalar value (slow in a debug build: run it with `--ignored`).
#[test]
#[ignore]
fn escaping_agrees_on_every_scalar_value() {
    let chars = without_release_changes((0..=0x10ffffu32).filter_map(char::from_u32).collect());
    for block in chars.chunks(1 << 15) {
        escaping_agrees_on(block);
    }
}

/// The scalar values two Rust releases' `escape_debug` writes differently, from
/// `escape_changes.txt` (written by `dogwood-lean/scripts/gen_unicode_tables.py --changes`).
const ESCAPE_CHANGES: &str = include_str!("escape_changes.txt");

/// How `escape_debug` writes `c`, in the classes of [`ESCAPE_CHANGES`]: `u`, as `\u{…}`
/// wherever it is; `g`, as `\u{…}` at the start of a string only; `-`, as itself.
fn escape_class(c: char) -> char {
    let unicode = c.escape_debug().to_string().starts_with("\\u{");
    let after_first = format!("a{c}").escape_debug().to_string()[1..].starts_with("\\u{");
    match (unicode, after_first) {
        (true, true) => 'u',
        (true, false) => 'g',
        (false, false) => '-',
        (false, true) => panic!("U+{:04X} is escaped after a character only", u32::from(c)),
    }
}

/// The ranges of [`ESCAPE_CHANGES`] when it lists the releases `tables` and `rustc` (in
/// either order), each with the class of its scalar values in `rustc`; `None` otherwise.
fn release_changes(tables: &str, rustc: &str) -> Option<Vec<(std::ops::Range<u32>, char)>> {
    let mut lines = ESCAPE_CHANGES
        .lines()
        .filter(|l| !l.is_empty() && !l.starts_with('#'));
    let releases: Vec<&str> = lines.next()?.split_whitespace().collect();
    let rustc_is_second = match releases[..] {
        ["releases", a, b] if (a, b) == (tables, rustc) => true,
        ["releases", a, b] if (a, b) == (rustc, tables) => false,
        _ => return None,
    };
    let hex = |s: &str| u32::from_str_radix(s, 16).expect("a hexadecimal code point");
    Some(
        lines
            .map(|l| match l.split_whitespace().collect::<Vec<_>>()[..] {
                [lo, hi, a, b] => {
                    let class = if rustc_is_second { b } else { a };
                    (hex(lo)..hex(hi), class.chars().next().unwrap())
                }
                _ => panic!("escape_changes.txt: malformed line `{l}`"),
            })
            .collect(),
    )
}

/// `chars`, without the scalar values whose escaping differs between the Rust release of the
/// Lean frontend's Unicode tables and the compiler's, when the two differ and
/// [`ESCAPE_CHANGES`] lists those releases. The two frontends print these characters
/// differently by construction (each with its release's tables) until the tables are
/// regenerated for the compiler: leaving them out keeps a toolchain upgrade from failing every
/// test run of the crate until then. The compiler must write each one as the file says: a file
/// that does not describe the compiler fails here.
fn without_release_changes(chars: Vec<char>) -> Vec<char> {
    let (tables, rustc) = (env!("DOGWOOD_LEAN_TABLES_RUST"), env!("DOGWOOD_LEAN_RUSTC"));
    if tables == rustc {
        return chars;
    }
    let Some(changes) = release_changes(tables, rustc) else {
        // `escaping_agrees_on` fails on the first difference, and names both releases.
        return chars;
    };
    for (range, class) in &changes {
        for c in range.clone().filter_map(char::from_u32) {
            assert_eq!(
                escape_class(c),
                *class,
                "dogwood-language/src/lean_frontend/escape_changes.txt says Rust {rustc} writes \
                 U+{:04X} as `{class}`, and this compiler does not: regenerate it with \
                 `scripts/gen_unicode_tables.py --changes <toolchain>` in dogwood-lean/",
                u32::from(c),
            );
        }
    }
    let changed = |c: &char| changes.iter().any(|(r, _)| r.contains(&u32::from(*c)));
    let left_out = chars.iter().filter(|c| changed(c)).count();
    eprintln!(
        "warning: the Lean frontend's Unicode tables are Rust {tables}'s and this crate is \
         compiled with Rust {rustc}: the comparison of the frontends leaves out the characters \
         the two releases escape differently (escape_changes.txt; {left_out} here); regenerate \
         the tables for Rust {rustc} to compare them again"
    );
    chars.into_iter().filter(|c| !changed(c)).collect()
}

// ─── Identity values in shadow mode ─────────────────────────────────────

/// A difference in an identity value is found, and in `OnMismatch::Fail` it is a
/// panic, which no caller that tolerates a lowering error can take for one.
#[test]
fn an_identity_difference_panics_in_fail_mode() {
    let schema = schema();
    let rust_service = service(Frontend::Rust);
    let parsed = ParsedPolicySet::parse(POLICY, &rust_service).unwrap();
    let rust = crate::api::lower(parsed.parsed(), &schema, None);
    // A set parsed for the Lean frontend keeps the parser's output, which it lowers.
    let shadow_service = service(Frontend::Shadow(OnMismatch::Fail));
    let parsed = ParsedPolicySet::parse(POLICY, &shadow_service).unwrap();
    let entries: [EntryRef<'_>; 1] = [(parsed.parsed(), None)];
    let mut lean = lean_lower(&entries, &schema, false);
    assert_eq!(identity_difference(&rust, &lean), None);

    // Another revision.
    let saved = match &mut lean {
        Ok(Reply::Lowered {
            identity, lowered, ..
        }) => {
            let hash = identity.version_hash(lowered).to_string();
            std::mem::replace(
                identity,
                SetIdentity::with_version_hash(vec!["another revision".into()], false, hash),
            )
        }
        Ok(Reply::Rejected(e)) => panic!("the Lean frontend rejects the policy: {e:?}"),
        Err(e) => panic!("the Lean frontend fails: {e}"),
    };
    let d = identity_difference(&rust, &lean).expect("a revision differs");
    assert!(d.contains("`ruleRevisions[0]`"), "{d}");
    // Another content hash, the Lean frontend's own.
    if let Ok(Reply::Lowered {
        identity,
        content_hashes,
        ..
    }) = &mut lean
    {
        *identity = saved;
        content_hashes[0].push('0');
    }
    let d = identity_difference(&rust, &lean).expect("a content hash differs");
    assert!(d.contains("`contentHashes[0]`"), "{d}");

    identity_mismatch(OnMismatch::Log, &d);
    let failed = std::panic::catch_unwind(|| identity_mismatch(OnMismatch::Fail, &d));
    assert!(failed.is_err(), "OnMismatch::Fail panics");
}

// ─── The shared runtime ─────────────────────────────────────────────────

/// `dogwood_lean_init` is idempotent from any thread, and a thread entered twice
/// stays registered until its last exit (a dependent's registration and the
/// crate's are one).
#[test]
fn the_runtime_initializes_once_and_counts_registrations() {
    runtime::ensure_initialized().unwrap();
    let handles: Vec<_> = (0..8)
        .map(|i| {
            std::thread::spawn(move || {
                assert_eq!(runtime::init_again(), 0);
                let outer = runtime::ThreadRegistration::new();
                let inner = runtime::ThreadRegistration::new();
                let s = format!("{i}");
                assert_eq!(runtime::call_here(runtime::Entry::Ping, &s).unwrap(), s);
                drop(inner);
                // Still registered: the outer enter has not exited.
                assert_eq!(runtime::call_here(runtime::Entry::Ping, &s).unwrap(), s);
                drop(outer);
                // A fresh call registers its own thread.
                assert_eq!(runtime::call(runtime::Entry::Ping, &s).unwrap(), s);
            })
        })
        .collect();
    for h in handles {
        h.join().unwrap();
    }
}

// ─── The request is the export's inputs ─────────────────────────────────

/// The Lean frontend's request for a lowering is, byte for byte, what
/// `frontend_export::inputs` (one set) and `inputs_many` (several) return for the
/// same sources, with the same id sources and distincters: the crate's Lean mode
/// and a dependent that sends the export's inputs to its own Lean code give the
/// Lean frontend the same input.
#[test]
fn the_lean_request_is_the_exports_inputs() {
    use crate::api::frontend_export::{self as fx, test_bundles};
    let text = |j: &Json| serde_json::to_string(j).unwrap();
    let lean_service = |b: &test_bundles::Bundle| {
        let mut builder = ServiceSchema::builder()
            .frontend(Frontend::Lean)
            .event_schema_str(&b.event_schema);
        if let Some(m) = &b.macros {
            builder = builder.macros_str(m);
        }
        if let Some(p) = &b.providers {
            builder = builder.providers(crate::ProviderDeclarations::from_json(p).ok()?);
        }
        builder.build().ok()
    };
    let mut compared = 0;
    for (group, shared) in test_bundles::GROUPS {
        for b in test_bundles::read(group, shared, 4) {
            let (Some(service), Ok(schema)) = (
                lean_service(&b),
                PolicySchema::from_cedarschema_str(&b.action_schema),
            ) else {
                continue;
            };
            let Ok(parsed) = ParsedPolicySet::parse(&b.policy, &service) else {
                continue;
            };
            let request = request(&[(parsed.parsed(), None)], &schema, false).unwrap();
            assert_eq!(
                text(&request),
                text(&fx::inputs(&b.sources())),
                "{}",
                b.dir.display()
            );
            compared += 1;
        }
    }
    assert!(compared > 100, "only {compared} bundles compared");

    // Stable ids and distincters, for one set and for several.
    let lean = service(Frontend::Lean);
    let schema = schema();
    let usr: Distincter = "usr".parse().unwrap();
    let other: Distincter = "other".parse().unwrap();
    let explicit = crate::IdSource::Explicit(vec!["r".into()]);
    for source in [
        crate::IdSource::Annotation,
        explicit.clone(),
        crate::IdSource::Positional,
    ] {
        let parsed = ParsedPolicySet::parse(POLICY, &lean)
            .unwrap()
            .with_ids(source.clone())
            .unwrap();
        let request = request(&[(parsed.parsed(), Some(&usr))], &schema, false).unwrap();
        let inputs = fx::inputs(&fx::BundleSources {
            policy: POLICY,
            event_schema: None,
            providers: None,
            macros: None,
            action_schema: SCHEMA,
            ids: Some(&source),
            distincter: Some("usr"),
        });
        assert_eq!(text(&request), text(&inputs));
    }
    let a = ParsedPolicySet::parse(POLICY, &lean)
        .unwrap()
        .with_ids(crate::IdSource::Annotation)
        .unwrap();
    let b = ParsedPolicySet::parse(POLICY, &lean).unwrap();
    let request = request(
        &[(a.parsed(), Some(&usr)), (b.parsed(), Some(&other))],
        &schema,
        true,
    )
    .unwrap();
    let inputs = fx::inputs_many(&fx::ManySources {
        entries: &[
            fx::ManyEntry {
                policy: POLICY,
                distincter: "usr",
                ids: Some(&crate::IdSource::Annotation),
            },
            fx::ManyEntry {
                policy: POLICY,
                distincter: "other",
                ids: None,
            },
        ],
        event_schema: None,
        providers: None,
        macros: None,
        action_schema: SCHEMA,
    });
    assert_eq!(text(&request), text(&inputs));
}

// ─── The Lean frontend's printing ───────────────────────────────────────

/// Shadow mode compares the Lean frontend's printed Cedar part (each rule's
/// policy JSON and text, the augmented schema's JSON), as it returns it, with
/// Cedar's printing of the Rust frontend's set: they agree, and a difference in
/// any of them is found.
#[test]
fn shadow_mode_checks_the_lean_frontends_printing() {
    let schema = schema();
    let rust_service = service(Frontend::Rust);
    let parsed = ParsedPolicySet::parse(POLICY, &rust_service).unwrap();
    let rust = crate::api::lower(parsed.parsed(), &schema, None);
    let shadow_service = service(Frontend::Shadow(OnMismatch::Fail));
    let parsed = ParsedPolicySet::parse(POLICY, &shadow_service).unwrap();
    let entries: [EntryRef<'_>; 1] = [(parsed.parsed(), None)];
    let mut lean = lean_lower(&entries, &schema, false);
    assert_eq!(printing_difference(&rust, &lean), None);
    let original = match &lean {
        Ok(Reply::Lowered { printed, .. }) => printed.clone(),
        _ => panic!("the Lean frontend does not lower the policy"),
    };
    for (path, doctored) in [
        (
            "policies[0].text",
            json!("permit (principal, action, resource);"),
        ),
        ("policies[0].est.effect", json!("forbid")),
        ("augmentedSchema", json!({})),
    ] {
        if let Ok(Reply::Lowered { printed, .. }) = &mut lean {
            *printed = original.clone();
            let mut at = &mut *printed;
            for key in path.split('.') {
                at = match key.split_once('[') {
                    Some((k, i)) => &mut at[k][i.trim_end_matches(']').parse::<usize>().unwrap()],
                    None => &mut at[key],
                };
            }
            *at = doctored;
        }
        let d = printing_difference(&rust, &lean).expect("a printing differs");
        assert!(
            d.contains(&format!("`{}", path.split('.').next().unwrap())),
            "{d}"
        );
    }
}

// ─── A dependent's own Lean lowering ────────────────────────────────────

/// The observables of a lowered set.
fn observed(set: &LoweredPolicySet) -> Json {
    let (lowered, identity) = set.clone().into_parts();
    observe::lowered(&lowered, &identity)
}

/// What validation reports on a lowered set.
fn findings_of(set: &LoweredPolicySet) -> String {
    format!("{:?}", Validator::new().validate(set))
}

/// The service schema of a corpus bundle, selecting `frontend`.
fn bundle_service(
    b: &crate::api::frontend_export::test_bundles::Bundle,
    frontend: Frontend,
) -> Option<ServiceSchema> {
    let mut builder = ServiceSchema::builder()
        .frontend(frontend)
        .event_schema_str(&b.event_schema);
    if let Some(m) = &b.macros {
        builder = builder.macros_str(m);
    }
    if let Some(p) = &b.providers {
        builder = builder.providers(crate::ProviderDeclarations::from_json(p).ok()?);
    }
    builder.build().ok()
}

/// The set a dependent builds from its own Lean run of the library's pipeline
/// (`frontend::lowered_from_lean`) is the crate's Lean mode's set, from the
/// pipeline's outcome and from the lowered set alone, with the same findings; a
/// rejection is the same error; and the set is the Rust frontend's wherever shadow
/// mode finds the frontends agree. On every bundle of the corpora (the passing
/// groups and the expected failures). The run is the library's `lowerAll` on the
/// export's inputs, the entry point the crate's Lean mode calls
/// (`dogwood-lean-dependent` runs `lowerFull` from Lean code of its own).
#[test]
fn a_dependents_lean_lowering_decodes_to_the_lean_modes_set() {
    use crate::api::frontend_export::test_bundles;
    let bundles: Vec<test_bundles::Bundle> = test_bundles::GROUPS
        .iter()
        .copied()
        .chain([("expected_failures", None)])
        .flat_map(|(group, shared)| test_bundles::read(group, shared, 1))
        .collect();
    let workers = 6;
    let counts: Vec<(usize, usize, usize)> = std::thread::scope(|scope| {
        let handles: Vec<_> = (0..workers)
            .map(|w| {
                let bundles = &bundles;
                std::thread::Builder::new()
                    .stack_size(64 * 1024 * 1024)
                    .spawn_scoped(scope, move || {
                        bundles
                            .iter()
                            .skip(w)
                            .step_by(workers)
                            .map(decodes_to_the_lean_modes_set)
                            .fold((0, 0, 0), |a, b| (a.0 + b.0, a.1 + b.1, a.2 + b.2))
                    })
                    .unwrap()
            })
            .collect();
        handles.into_iter().map(|h| h.join().unwrap()).collect()
    });
    let (decoded, agreeing, rejected) = counts
        .into_iter()
        .fold((0, 0, 0), |a, b| (a.0 + b.0, a.1 + b.1, a.2 + b.2));
    eprintln!(
        "decoded {decoded} sets ({agreeing} agreeing with the Rust frontend), {rejected} rejections"
    );
    assert!(
        decoded > 800 && agreeing > 800 && rejected > 0,
        "{decoded} {agreeing} {rejected}"
    );
}

/// One bundle of [`a_dependents_lean_lowering_decodes_to_the_lean_modes_set`]: (1, 0, 0)
/// for a decoded set, (1, 1, 0) for one the Rust frontend agrees on, (0, 0, 1) for a
/// rejection, and nothing for a bundle the crate's parsers or schemas reject.
fn decodes_to_the_lean_modes_set(
    b: &crate::api::frontend_export::test_bundles::Bundle,
) -> (usize, usize, usize) {
    use crate::api::frontend_export as fx;
    let here = b.dir.display().to_string();
    let (Some(lean), Some(rust), Some(shadow), Ok(schema)) = (
        bundle_service(b, Frontend::Lean),
        bundle_service(b, Frontend::Rust),
        bundle_service(b, Frontend::Shadow(OnMismatch::Fail)),
        PolicySchema::from_cedarschema_str(&b.action_schema),
    ) else {
        return (0, 0, 0);
    };
    // The parsers are the crate's: a set they reject is not the Lean frontend's.
    let Ok(parsed) = ParsedPolicySet::parse(&b.policy, &lean) else {
        return (0, 0, 0);
    };
    let inputs = serde_json::to_string(&fx::inputs(&b.sources())).unwrap();
    let reply = runtime::call(runtime::Entry::Lower, &inputs).unwrap();
    let from_reply = crate::frontend::lowered_from_lean(&reply, &[&b.policy], b.macros.as_deref());
    match (from_reply, parsed.lower(&schema)) {
        (Ok(d), Ok(mode)) => {
            let want = observed(&mode);
            assert_eq!(
                observe::first_difference(&want, &observed(&d)),
                None,
                "{here}"
            );
            assert_eq!(findings_of(&d), findings_of(&mode), "{here}");
            let full = parse_json(&reply).unwrap()["ok"]["lowered"].to_string();
            let bare = crate::frontend::lowered_from_lean(&full, &[&b.policy], b.macros.as_deref())
                .unwrap_or_else(|e| panic!("{here}: {e}"));
            assert_eq!(
                observe::first_difference(&want, &observed(&bare)),
                None,
                "{here}"
            );
            let agree = ParsedPolicySet::parse(&b.policy, &shadow)
                .and_then(|p| p.lower(&schema))
                .is_ok();
            if !agree {
                return (1, 0, 0);
            }
            let r = ParsedPolicySet::parse(&b.policy, &rust)
                .and_then(|p| p.lower(&schema))
                .unwrap();
            assert_eq!(
                observe::first_difference(&observed(&r), &observed(&d)),
                None,
                "{here}"
            );
            (1, 1, 0)
        }
        (Err(d), Err(mode)) => {
            assert_eq!(error_observable(&d), error_observable(&mode), "{here}");
            (0, 0, 1)
        }
        (d, mode) => panic!(
            "{here}: the decoder gives {:?}, Lean mode {:?}",
            d.map(|_| ()),
            mode.map(|_| ())
        ),
    }
}

/// Several sets lowered together: the decoded set of `lowerManyAll`'s outcome is
/// Lean mode's `lower_many`, and the Rust frontend's; an entry the outcome names
/// no policy text for is a decoding error.
#[test]
fn a_dependents_lean_lowering_of_several_sets_decodes_too() {
    use crate::api::frontend_export as fx;
    use crate::{Distincter, IdSource};
    let schema = schema();
    let other = r#"
@id("deny-big")
forbid (principal, action == Drupe::Action::"Read", resource)
when { context.input.amount > 100 };
"#;
    let ids = IdSource::Annotation;
    let inputs = fx::inputs_many(&fx::ManySources {
        entries: &[
            fx::ManyEntry {
                policy: POLICY,
                distincter: "usr",
                ids: Some(&ids),
            },
            fx::ManyEntry {
                policy: other,
                distincter: "other",
                ids: None,
            },
        ],
        event_schema: None,
        providers: None,
        macros: None,
        action_schema: SCHEMA,
    });
    let reply = runtime::call(runtime::Entry::LowerMany, &inputs.to_string()).unwrap();
    let decoded = crate::frontend::lowered_from_lean(&reply, &[POLICY, other], None).unwrap();
    let lowered_with = |frontend| {
        let service = service(frontend);
        let a = ParsedPolicySet::parse(POLICY, &service)
            .unwrap()
            .with_ids(ids.clone())
            .unwrap();
        let b = ParsedPolicySet::parse(other, &service).unwrap();
        let (usr, oth): (Distincter, Distincter) =
            ("usr".parse().unwrap(), "other".parse().unwrap());
        crate::lower_many(&[(&a, usr), (&b, oth)], &schema).unwrap()
    };
    let lean = lowered_with(Frontend::Lean);
    assert_eq!(
        observe::first_difference(&observed(&lean), &observed(&decoded)),
        None
    );
    assert_eq!(findings_of(&lean), findings_of(&decoded));
    let rust = lowered_with(Frontend::Rust);
    assert_eq!(
        observe::first_difference(&observed(&rust), &observed(&decoded)),
        None
    );
    assert_eq!(decoded.rules().count(), 2);
    // The second entry's rule has no policy text.
    match crate::frontend::lowered_from_lean(&reply, &[POLICY], None) {
        Err(Error::Frontend(e)) => {
            assert_eq!(e.kind(), FrontendErrorKind::Lean);
            assert!(e.message().contains("rule source 1"), "{e}");
        }
        other => panic!("{:?}", other.map(|_| ())),
    }
}

/// The other forms of an outcome: a rejection is the crate's error, located in its
/// entry's source (or the macro library's), a `bug` and text that is not an outcome
/// are the Lean frontend's failure, and a decoded set works with the authorizer's
/// checks.
#[test]
fn a_dependents_lean_outcome_of_every_form_decodes() {
    use crate::api::frontend_export as fx;
    let inputs = |policy: &str, macros: Option<&str>| {
        fx::inputs(&fx::BundleSources {
            policy,
            event_schema: None,
            providers: None,
            macros,
            action_schema: SCHEMA,
            ids: None,
            distincter: None,
        })
        .to_string()
    };
    let bad = "permit (principal, action, resource) when { undefined_macro(1) };";
    let reply = runtime::call(runtime::Entry::Lower, &inputs(bad, None)).unwrap();
    let decoded = crate::frontend::lowered_from_lean(&reply, &[bad], None).unwrap_err();
    let mode = LoweredPolicySet::from_str(bad, &service(Frontend::Lean), &schema()).unwrap_err();
    assert!(matches!(decoded, Error::Macro(_)), "{decoded:?}");
    assert_eq!(error_observable(&decoded), error_observable(&mode));

    for (text, why) in [
        (r#"{"bug": "it broke"}"#, "it broke"),
        ("[1, 2]", "neither"),
        ("{not json", "not JSON"),
    ] {
        match crate::frontend::lowered_from_lean(text, &[POLICY], None) {
            Err(Error::Frontend(e)) => {
                assert_eq!(e.kind(), FrontendErrorKind::Lean);
                assert!(e.message().contains(why) || why == "neither", "{e}");
            }
            other => panic!("{text}: {:?}", other.map(|_| ())),
        }
    }

    // The set's runtime checks: a decision event of the set's own event schema conforms.
    let reply = runtime::call(runtime::Entry::Lower, &inputs(POLICY, None)).unwrap();
    let decoded = crate::frontend::lowered_from_lean(&reply, &[POLICY], None).unwrap();
    let mode = LoweredPolicySet::from_str(POLICY, &service(Frontend::Lean), &schema()).unwrap();
    assert_eq!(decoded.version_hash(), mode.version_hash());
    assert!(Validator::new().validate(&decoded).validation_passed());
    let input = |user: Option<&str>| {
        let mut m = std::collections::BTreeMap::new();
        if let Some(u) = user {
            m.insert("user".to_string(), crate::Value::String(u.into()));
            m.insert("amount".to_string(), crate::Value::Int(3));
        }
        crate::Value::Object(m)
    };
    for (kind, user) in [
        ("request", Some("alice")),
        ("response", Some("bob")),
        ("request", None),
    ] {
        let event = crate::Event::builder("Drupe::Action::Read", kind)
            .timestamp(10)
            .principal("Drupe::OAuthUser::\"alice\"")
            .resource("Drupe::Gateway::\"gw\"")
            .logged_field("input", input(user))
            .request_context_field("input", input(user))
            .build();
        for rule in [crate::MirrorRule::Strict, crate::MirrorRule::Current] {
            assert_eq!(
                decoded.check_event_conformance(&event, rule),
                mode.check_event_conformance(&event, rule),
                "{kind} {user:?}"
            );
        }
    }
}
