//! Web-fetch provider test (feature `net`) — demonstrating the *safe* SSRF
//! pattern for `http_get`.
//!
//! Shows a provider pulling a value from the web and checking it — in the
//! spirit of OPA/Rego's `http.send`. The key best practice this example models:
//! **the untrusted event field never controls the URL's authority.** A request
//! supplies only an opaque `key`; the provider script validates it against a
//! strict allowlist regex and interpolates it into one path segment of a
//! **fixed, deployer-owned base URL** before calling `http_get`. A request
//! cannot steer the fetch to an arbitrary internal endpoint (169.254.169.254,
//! 127.0.0.1, …) — the SSRF risk of passing a request-supplied URL straight to
//! `http_get`. The policy forbids `Read` when the fetched body is `"BLOCKED"`.
//!
//! Hermetic: the "web" is a `std::net::TcpListener` mock server started on a
//! loopback port inside the test, so this makes a *real* HTTP request but needs
//! no external connectivity. The mock's port is unknown until runtime, so the
//! fixed base URL is supplied to the provider as a deployer-controlled *literal*
//! argument in the policy (modeling deployer-owned config) — NOT from the event.
//!
//! Runs only with `--features net` (which is what registers `http_get`);
//! it is a no-op stub otherwise so the default test run stays offline.
//!
//! NOTE on the provider contract: a network-backed provider is inherently
//! IMPURE, and provider execution is unconditional — it fires for every
//! decision event, not just those its rule matches. The contract (guide,
//! 05-information-providers) requires pure, defensive providers; `net` is an
//! off-by-default escape hatch for callers who accept those caveats (the
//! production-shaped seam for external values is a `ProviderResolver`, which
//! carries the same contract obligations).

#![cfg(feature = "net")]

use std::io::{Read, Write};
use std::net::TcpListener;
use std::sync::{Arc, Mutex};
use std::thread;

use dogwood_language::{
    LoweredPolicySet, PolicySchema, ProviderDeclarations, ServiceSchema, replay_log,
};

const SCHEMA: &str = r#"
namespace Drupe {
  type ReadInput = { key: String };
  entity Gateway;
  entity OAuthUser = { id: String } tags String;
  action "Read" appliesTo {
    principal: [OAuthUser],
    resource: [Gateway],
    context: { input: ReadInput }
  };
}
"#;

const EVENT_SCHEMA: &str = r#"
decision event <A>::request {
    ...inputs(A),
    callerPrincipal: principalType(A),
    callerResource:  resourceType(A),
    requestId:       String,
}

event <A>::response {
    ...inputs(A),
    ...outputs(A),
    callerPrincipal: principalType(A),
    callerResource:  resourceType(A),
    requestId:       String,
}
"#;

// `Http::Fetch(base, key) -> { body: String }`. Fetches a value for `key` from
// a fixed service. This is the SAFE web-fetch pattern:
//
//   * `base` is a deployer-owned literal (the service's fixed origin,
//     `http://example.com` — supplied in the *policy*, never from a request),
//     so a caller cannot choose which host is contacted.
//   * `key` comes from the request, so the script treats it as UNTRUSTED: it
//     first validates it against a strict `^[a-z0-9_-]+(\.[a-z0-9_-]+)*$`
//     allowlist and only then interpolates it into one fixed path segment. A
//     value that fails validation yields an empty body (fail-safe), never a
//     fetch.
//
// The allowlist is dot-separated tokens of `[a-z0-9_-]`, so ordinary keys like
// `page.html` are fine, but `/`, `@`, `:`, whitespace, and CRLF are excluded
// (authority/injection) AND `..` is excluded structurally (a `.` must sit
// between two tokens, so `..`, `.foo`, `foo.`, `a..b` all fail) — the key
// cannot traverse out of the intended `/lookup/<key>` segment. The result: the
// request influences only a validated, single non-authority path segment — it
// can neither change the target host nor inject a new authority
// (`evil.com`, `user@evil.com`, `127.0.0.1`, CRLF smuggling) nor traverse.
const PROVIDERS: &str = r#"
{
  "availableProviders": {
    "Http::Fetch": {
      "argumentTypes": [
        { "paramType": "string" },
        { "paramType": "string" }
      ],
      "outputType": {
        "paramType": "record",
        "fields": { "body": { "paramType": "string" } },
        "required": ["body"]
      },
      "implementation": {
        "kind": "rhai",
        "script": "fn evaluate(base, key) { if regex_is_match(\"^[a-z0-9_-]+(\\\\.[a-z0-9_-]+)*$\", key) { #{ body: http_get(base + \"/lookup/\" + key) } } else { #{ body: \"\" } } }"
      }
    }
  }
}
"#;

// Permit `Read` only when the fetched value is NOT "BLOCKED". The base URL is a
// policy-side literal (deployer-owned); only `context.input.key` — a validated
// identifier, not a URL — comes from the request. Unwrapped provider form (no
// `guardrails { … }` block).
//
// NOTE: `{base}` is substituted by the test harness with the loopback mock's
// `http://127.0.0.1:<port>` origin (the port is only known at runtime). In a
// real deployment this is a hardcoded literal such as `"http://example.com"`.
const POLICY_TEMPLATE: &str = r#"
permit (
    principal,
    action == Drupe::Action::"Read",
    resource
)
when {
    Http::Fetch("{base}", context.input.key).body != "BLOCKED"
};
"#;

/// Start a loopback mock lookup service that answers `GET /lookup/<key>` with
/// `BLOCKED` for the key `blocked` and `OK` otherwise. Returns
/// `(base_url, received_paths)`: the base URL
/// (`http://127.0.0.1:<port>`) the deployer would hardcode in the policy, and a
/// shared log of every request-line path the server actually received — so a
/// test can assert a request that *should* have been rejected before the fetch
/// never reached the network. The server thread serves connections until the
/// process exits.
fn start_mock_server() -> (String, Arc<Mutex<Vec<String>>>) {
    let listener = TcpListener::bind("127.0.0.1:0").expect("bind loopback");
    let addr = listener.local_addr().expect("local addr");
    let received: Arc<Mutex<Vec<String>>> = Arc::new(Mutex::new(Vec::new()));
    let received_srv = received.clone();

    thread::spawn(move || {
        for stream in listener.incoming() {
            let Ok(mut stream) = stream else { continue };
            // Read the request line (enough to recover the path).
            let mut buf = [0u8; 1024];
            let n = stream.read(&mut buf).unwrap_or(0);
            let req = String::from_utf8_lossy(&buf[..n]);
            let path = req
                .lines()
                .next()
                .and_then(|line| line.split_whitespace().nth(1))
                .unwrap_or("/")
                .to_string();
            received_srv
                .lock()
                .unwrap_or_else(|e| e.into_inner())
                .push(path.clone());

            let body = if path.ends_with("/blocked") {
                "BLOCKED"
            } else {
                "OK"
            };
            let response = format!(
                "HTTP/1.0 200 OK\r\nContent-Length: {}\r\nConnection: close\r\n\r\n{}",
                body.len(),
                body
            );
            let _ = stream.write_all(response.as_bytes());
        }
    });

    (format!("http://{addr}"), received)
}

fn trace() -> String {
    // Three requests, each carrying only a `key` identifier (NOT a URL): an
    // allowed key and a dotted key `page.html` (both looked up → "OK" → permit,
    // showing a single interior `.` is valid), then a blocked key (looked up →
    // "BLOCKED" → deny). The request never names the lookup service's origin —
    // the policy's literal base does.
    r#"
@0 scope(principal: Drupe::OAuthUser::"alice", resource: Drupe::Gateway::"gw1") request_context(input: { key: "allowed" }) Drupe::Action::"Read"::request(input: { key: "allowed" })
@10 scope(principal: Drupe::OAuthUser::"alice", resource: Drupe::Gateway::"gw1") request_context(input: { key: "page.html" }) Drupe::Action::"Read"::request(input: { key: "page.html" })
@20 scope(principal: Drupe::OAuthUser::"alice", resource: Drupe::Gateway::"gw1") request_context(input: { key: "blocked" }) Drupe::Action::"Read"::request(input: { key: "blocked" })
"#
    .to_string()
}

#[test]
fn provider_fetches_from_the_web() {
    let (base_url, _received) = start_mock_server();
    // The deployer-owned base URL is a literal in the policy (here, the mock's
    // runtime loopback origin). Only the `host` identifier comes from requests.
    let policy = POLICY_TEMPLATE.replace("{base}", &base_url);
    let decls = ProviderDeclarations::from_json(PROVIDERS).expect("providers.json parses");

    // NEW API: build a `ServiceSchema` (explicit event schema + provider
    // declarations) and a `PolicySchema` (action schema), lower the policy
    // into a `LoweredPolicySet`, then replay the whole trace. `replay_log`
    // returns the same verdict stream that the old `authorize_trace` free
    // function produced.
    let service = ServiceSchema::builder()
        .event_schema_str(EVENT_SCHEMA)
        .providers(decls)
        .build()
        .expect("service schema builds");
    let policy_schema = PolicySchema::from_cedarschema_str(SCHEMA).expect("policy schema builds");
    let policies =
        LoweredPolicySet::from_str(&policy, &service, &policy_schema).expect("policy lowers");

    let verdicts = replay_log(policies, &trace()).expect("authorizes");

    // The allowed key (tp 0) and the dotted key `page.html` (tp 1) are
    // permitted (both fetch "OK"); the blocked key (tp 2) fetched "BLOCKED" and
    // is denied.
    let lines: Vec<&str> = verdicts.lines().filter(|l| !l.trim().is_empty()).collect();
    assert_eq!(
        lines,
        vec![
            "@0 (time point 0): true",
            "@10 (time point 1): true",
            "@20 (time point 2): false",
        ],
        "expected allowed + dotted keys permitted and blocked key denied; got: {verdicts:?}"
    );
}

/// The SSRF defense, demonstrated: a request `key` that tries to hijack the
/// URL's authority or inject path traversal fails the script's allowlist regex,
/// so `http_get` is never called at all — proving the fetch cannot be steered
/// by request input. This is the property that makes interpolating a request
/// field into the URL safe *here*, unlike the naive `http_get(input.url)` form.
///
/// We prove "never fetched" directly: the mock server records every path it
/// receives, and we assert it received *nothing* for the malicious payloads.
/// (Asserting the verdict alone would not prove it — an empty body and a
/// successful "OK" fetch both permit; only the empty request log is conclusive.)
#[test]
fn malicious_key_is_rejected_before_fetch() {
    let (base_url, received) = start_mock_server();
    let policy = POLICY_TEMPLATE.replace("{base}", &base_url);
    let decls = ProviderDeclarations::from_json(PROVIDERS).expect("providers.json parses");
    let service = ServiceSchema::builder()
        .event_schema_str(EVENT_SCHEMA)
        .providers(decls)
        .build()
        .expect("service schema builds");
    let policy_schema = PolicySchema::from_cedarschema_str(SCHEMA).expect("policy schema builds");

    // Authority-hijack / traversal / smuggling payloads, all rejected by the
    // `^[a-z0-9_-]+(\.[a-z0-9_-]+)*$` allowlist (forbids `/`, `@`, `:`, `%`,
    // whitespace, CRLF, and — structurally — `..` and leading/trailing dots).
    let payloads = [
        "allowed@attacker.com",   // userinfo authority swap
        "127.0.0.1:9999",         // internal host:port
        "allowed/../secret",      // path traversal / extra segment
        "allowed%0d%0aHost:evil", // CRLF smuggling attempt
        "..",                     // bare parent-dir traversal (dot-run rejected)
        ".secret",                // leading dot (dot must sit between tokens)
    ];

    for key in payloads {
        // `replay_log` consumes the lowered set, so lower once per payload.
        let policies =
            LoweredPolicySet::from_str(&policy, &service, &policy_schema).expect("policy lowers");
        let tr = format!(
            r#"@0 scope(principal: Drupe::OAuthUser::"alice", resource: Drupe::Gateway::"gw1") request_context(input: {{ key: "{key}" }}) Drupe::Action::"Read"::request(input: {{ key: "{key}" }})"#,
        );
        let _ = replay_log(policies, &tr).expect("authorizes");
    }

    // The conclusive assertion: the reputation service was contacted for NONE
    // of the malicious payloads. Validation rejected each before `http_get`, so
    // no request-controlled fetch ever happened.
    let paths = received.lock().unwrap_or_else(|e| e.into_inner());
    assert!(
        paths.is_empty(),
        "a malicious `host` payload reached the network — SSRF validation failed. \
         Server received: {paths:?}"
    );
}
