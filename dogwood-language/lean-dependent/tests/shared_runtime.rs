//! One process, one Lean runtime, two crates of Lean code: this crate's module,
//! compiled against the language crate's Lean library, and the language crate's
//! own Lean frontend, called from several threads at once.
//!
//! For each policy set, the test sends the language crate's inputs-only export
//! (`frontend_export::inputs`) to this crate's module, which lowers it with the
//! library's pipeline and returns the Cedar part as Cedar prints it; it builds the
//! Cedar policy set and schema from that JSON (`frontend_export::cedar_policy_set`,
//! `cedar_schema`), and compares them with the set the language crate's Lean
//! frontend lowers (`Frontend::Lean`) in the same process.

#![cfg(feature = "lean")]

use dogwood_language::frontend_export::{self as fx, BundleSources, ManyEntry, ManySources};
use dogwood_language::{
    Distincter, Event, Frontend, LoweredPolicySet, MirrorRule, PolicySchema, ServiceSchema,
    Validator, Value,
};
use serde_json::Value as Json;

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

const POLICIES: &[&str] = &[
    r#"
@id("read-after-login")
permit (principal, action == Drupe::Action::"Read", resource)
when temporal {
    formerly within 1h Drupe::Action::"Login"::response{ input.user: context.input.user }
}
unless { context.input.amount > 10 && principal.id != "root" };
"#,
    r#"
@note("two rules")
permit (principal, action == Drupe::Action::"Login", resource);
forbid (principal, action == Drupe::Action::"Read", resource)
when { context.input.amount > 100 };
"#,
    r#"
forbid (principal, action == Drupe::Action::"Read", resource)
unless temporal {
    formerly within 10m Drupe::Action::"Login"::request{ input.user: context.input.user }
};
"#,
];

/// Lower `policy` both ways in this process and compare.
fn check(policy: &str) {
    let inputs = fx::inputs(&BundleSources {
        policy,
        event_schema: None,
        providers: None,
        macros: None,
        action_schema: SCHEMA,
        ids: None,
        distincter: None,
    });
    let reply: Json =
        serde_json::from_str(&dogwood_lean_dependent::probe(&inputs.to_string()).unwrap()).unwrap();
    let ok = reply.get("ok").unwrap_or_else(|| panic!("{reply}"));
    let cedar = &ok["cedar"];
    let policies = fx::cedar_policy_set(&cedar["policies"]).unwrap();
    let (fragment, _schema) = fx::cedar_schema(&cedar["augmentedSchema"]).unwrap();

    // The language crate's own Lean frontend, in the same process.
    let service = ServiceSchema::builder()
        .frontend(Frontend::Lean)
        .build()
        .unwrap();
    let schema = PolicySchema::from_cedarschema_str(SCHEMA).unwrap();
    let lowered = LoweredPolicySet::from_str(policy, &service, &schema).unwrap();
    let theirs = lowered.as_cedar();
    assert_eq!(policies.policies().count(), theirs.policies().count());
    let mut permits = 0;
    let mut forbids = 0;
    for p in theirs.policies() {
        let q = policies.policy(p.id()).expect("the same ids");
        assert_eq!(q.to_string(), p.to_string());
        assert_eq!(q.to_json().unwrap(), p.to_json().unwrap());
        assert_eq!(
            q.annotations().collect::<Vec<_>>(),
            p.annotations().collect::<Vec<_>>()
        );
        match p.effect() {
            cedar_policy::Effect::Permit => permits += 1,
            cedar_policy::Effect::Forbid => forbids += 1,
        }
    }
    // The module's own printing of each rule is Cedar's.
    for r in cedar["policies"].as_array().unwrap() {
        let id = cedar_policy::PolicyId::new(r["id"].as_str().unwrap());
        assert_eq!(
            r["text"].as_str().unwrap(),
            policies.policy(&id).unwrap().to_string()
        );
    }
    let augmented: Json = serde_json::from_str(&lowered.cedar_schema_json().unwrap()).unwrap();
    assert_eq!(fragment.to_json_value().unwrap(), augmented);
    assert_eq!(&cedar["augmentedSchema"], &augmented);
    // The module's hash map of Lean's standard library.
    let count = |k: &str| ok["effects"].get(k).and_then(Json::as_u64).unwrap_or(0);
    assert_eq!((count("permit"), count("forbid")), (permits, forbids));
}

#[test]
fn the_dependents_lean_code_and_the_crates_share_one_runtime() {
    assert_eq!(dogwood_lean_dependent::COMPILED_AGAINST.len(), 64);
    let threads: Vec<_> = (0..8)
        .map(|i| {
            std::thread::Builder::new()
                .stack_size(64 * 1024 * 1024)
                .spawn(move || {
                    for k in 0..3 {
                        check(POLICIES[(i + k) % POLICIES.len()]);
                    }
                })
                .unwrap()
        })
        .collect();
    for t in threads {
        t.join().unwrap();
    }
}

#[test]
fn a_rejection_comes_back_from_the_dependents_lean_code() {
    let inputs = fx::inputs(&BundleSources {
        policy: "permit (principal, action, resource) when { undefined_macro(1) };",
        event_schema: None,
        providers: None,
        macros: None,
        action_schema: SCHEMA,
        ids: None,
        distincter: None,
    });
    let reply: Json =
        serde_json::from_str(&dogwood_lean_dependent::probe(&inputs.to_string()).unwrap()).unwrap();
    let message = reply["error"].as_str().unwrap_or_else(|| panic!("{reply}"));
    assert!(message.contains("undefined_macro"), "{message}");
}

/// Everything a lowered set exposes, printed: its Cedar policies and schema, its
/// leaves, partition keys, event signatures, rules, decision kinds and version hash.
fn exposed(set: &LoweredPolicySet) -> String {
    let mut policies: Vec<String> = set
        .as_cedar()
        .policies()
        .map(|p| format!("{} {} {:?}", p.id(), p, p.annotations().collect::<Vec<_>>()))
        .collect();
    policies.sort();
    format!(
        "{policies:?}\n{}\n{:?}\n{:?}\n{:?}\n{:?}\n{:?}\n{:?}\n{:?}\n{} {}",
        set.cedar_schema_json().unwrap(),
        set.temporal_fields().collect::<Vec<_>>(),
        set.nonrelativized_temporal_fields().collect::<Vec<_>>(),
        set.provider_fields().collect::<Vec<_>>(),
        set.partition_keys(),
        set.event_signatures().collect::<Vec<_>>(),
        set.rules().map(|r| format!("{r:?}")).collect::<Vec<_>>(),
        set.decision_kinds().collect::<Vec<_>>(),
        set.version_hash(),
        set.has_stable_ids(),
    )
}

/// A `Read` event of `kind` by alice, with `user` as its input's user (none: no input).
fn read_event(kind: &str, user: Option<&str>) -> Event {
    let mut input = std::collections::BTreeMap::new();
    if let Some(u) = user {
        input.insert("user".to_string(), Value::String(u.into()));
        input.insert("amount".to_string(), Value::Int(3));
    }
    let input = Value::Object(input);
    Event::builder("Drupe::Action::Read", kind)
        .timestamp(10)
        .principal("Drupe::OAuthUser::\"alice\"")
        .resource("Drupe::Gateway::\"gw\"")
        .logged_field("input", input.clone())
        .request_context_field("input", input)
        .build()
}

/// `decoded` is `lean`: it exposes the same, its events conform alike, and (unless it
/// is the lowered set alone, which the crate's own validator validates) it validates
/// alike.
fn same(decoded: &LoweredPolicySet, lean: &LoweredPolicySet, validated: bool) {
    assert_eq!(exposed(decoded), exposed(lean));
    if validated {
        let v = Validator::new();
        assert_eq!(
            format!("{:?}", v.validate(decoded)),
            format!("{:?}", v.validate(lean))
        );
    }
    for (kind, user) in [
        ("request", Some("alice")),
        ("response", Some("bob")),
        ("request", None),
    ] {
        let event = read_event(kind, user);
        for rule in [MirrorRule::Strict, MirrorRule::Current] {
            assert_eq!(
                decoded.check_event_conformance(&event, rule),
                lean.check_event_conformance(&event, rule)
            );
        }
    }
}

/// The dependent's own run of the library's pipeline, from its own Lean code, decoded by
/// the language crate (`frontend::lowered_from_lean`) with no Rust lowering, is the set the
/// crate's Lean frontend lowers in the same process, for one policy set and for several
/// lowered together, from the pipeline's outcome and from the lowered set alone.
#[test]
fn the_dependents_own_lowering_is_the_crates_lowered_set() {
    std::thread::Builder::new()
        .stack_size(64 * 1024 * 1024)
        .spawn(|| {
            let service = ServiceSchema::builder()
                .frontend(Frontend::Lean)
                .build()
                .unwrap();
            let schema = PolicySchema::from_cedarschema_str(SCHEMA).unwrap();
            for policy in POLICIES {
                let inputs = fx::inputs(&BundleSources {
                    policy,
                    event_schema: None,
                    providers: None,
                    macros: None,
                    action_schema: SCHEMA,
                    ids: None,
                    distincter: None,
                })
                .to_string();
                let lean = LoweredPolicySet::from_str(policy, &service, &schema).unwrap();
                for bare in [false, true] {
                    let reply = dogwood_lean_dependent::lower(&inputs, bare).unwrap();
                    let decoded =
                        dogwood_language::frontend::lowered_from_lean(&reply, &[policy], None)
                            .unwrap_or_else(|e| panic!("{e}: {reply}"));
                    same(&decoded, &lean, !bare);
                }
            }
            let (a, b) = (POLICIES[0], POLICIES[1]);
            let inputs = fx::inputs_many(&ManySources {
                entries: &[
                    ManyEntry {
                        policy: a,
                        distincter: "first",
                        ids: None,
                    },
                    ManyEntry {
                        policy: b,
                        distincter: "second",
                        ids: None,
                    },
                ],
                event_schema: None,
                providers: None,
                macros: None,
                action_schema: SCHEMA,
            })
            .to_string();
            let d = |s: &str| s.parse::<Distincter>().unwrap();
            let lean = LoweredPolicySet::from_many_str(
                &[(a, d("first")), (b, d("second"))],
                &service,
                &schema,
            )
            .unwrap();
            let reply = dogwood_lean_dependent::lower(&inputs, false).unwrap();
            let decoded =
                dogwood_language::frontend::lowered_from_lean(&reply, &[a, b], None).unwrap();
            same(&decoded, &lean, true);
            assert_eq!(decoded.rules().count(), 3);

            // A rejection is the crate's error, as its Lean frontend returns it.
            let bad = "permit (principal, action, resource) when { undefined_macro(1) };";
            let inputs = fx::inputs(&BundleSources {
                policy: bad,
                event_schema: None,
                providers: None,
                macros: None,
                action_schema: SCHEMA,
                ids: None,
                distincter: None,
            })
            .to_string();
            let reply = dogwood_lean_dependent::lower(&inputs, false).unwrap();
            let decoded = dogwood_language::frontend::lowered_from_lean(&reply, &[bad], None)
                .map(|_| ())
                .unwrap_err();
            let lean = LoweredPolicySet::from_str(bad, &service, &schema)
                .map(|_| ())
                .unwrap_err();
            assert_eq!(decoded.to_string(), lean.to_string());
        })
        .unwrap()
        .join()
        .unwrap();
}
