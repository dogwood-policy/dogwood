# Dogwood

Dogwood is a policy language for authorization decisions that depend on
**history** — not just a single request, but patterns of events over time. It
supports [Cedar](https://www.cedarpolicy.com/) policies and adds temporal
conditions (`since`, `formerly`, `once`, aggregations) and information providers
(computed guardrail facts), then lowers everything back to Cedar for evaluation.

```text
permit(principal, action, resource)
when { context.input.amount < 1000 }
when formerly within 1h {
    Action::"Approve"::request{ approver: context.input.approver }
};
```

This repository contains a **reference interpreter** for the language for the
purpose of understanding the semantics of the language, with simple examples of
the kinds of policies Dogwood supports.  This reference interpreter is **NOT**
intended for production use. Please see the end of this document for a list
of important limitations of the interpreter.

📖 **[Read the full documentation →](https://dogwood-policy.github.io/dogwood/index.html)**


## Key features

- **Cedar-derived syntax** — familiar `permit`/`forbid` with `when`/`unless`
- **Temporal conditions** — express "since login," "formerly approved," rate
  limits, and windowed aggregations over an event history
- **Information providers** — computed facts (Rhai scripts) injected at
  evaluation time as guardrail context fields
- **Compile-to-Cedar** — policies lower to standard Cedar; the temporal and
  provider fields become `context.*` slots filled at runtime
- **Pluggable backends** — swap the policy engine (local Cedar or a remote
  policy store) and the temporal engine (in-memory or database-backed)
  independently

## Repository layout

| Path | Description |
|------|-------------|
| [`dogwood-language/`](dogwood-language/README.md) | The core Rust library — parser, interpreter, lowering, and API |
| [`dogwood-docs/guide/`](dogwood-docs/guide/README.md) | The language guide (syntax, schemas, temporal expressions, providers, formal spec) |
| [`dogwood-cli/`](dogwood-docs/guide/12-cli.md) | The `dogwood` CLI (validate, lower, replay) |
| [`dogwood-docs/examples/`](dogwood-docs/examples/) | Runnable example policies with traces and expected output |
| [`dogwood-language/configuration/`](dogwood-language/configuration/README.md) | Starter action schemas and event schemas |

## Quick start

```bash
# Validate a policy against its schemas:
dogwood validate policy.dw --policy-schema schema.cedarschema

# Lower to Cedar and see the output:
dogwood lower policy.dw --policy-schema schema.cedarschema --emit both

# Replay a trace and see verdicts:
dogwood replay policy.dw --policy-schema schema.cedarschema --trace events.log
```

### Worked example

The [`read_after_login`](dogwood-docs/examples/read_after_login/) example
permits a Read only if the same user logged in within the last hour:

```text
// policy.dw
@id("read_after_login")
permit (
    principal,
    action == Drupe::Action::"Read",
    resource
)
when temporal {
    formerly within 1h Drupe::Action::"Login"::request{ input.user: context.input.user }
};
```

Replay it against a trace of three events (login at t=0, read at t=10s, read at
t=2h):

```bash
$ dogwood replay dogwood-docs/examples/read_after_login/policy.dw \
    --policy-schema dogwood-docs/examples/read_after_login/schema.cedarschema \
    --trace dogwood-docs/examples/read_after_login/trace.log

@0 (time point 0): DENY
@10 (time point 1): ALLOW  [rules: 0]
@7200 (time point 2): DENY
```

The first event is the login itself (no read requested) → DENY. Ten seconds
later Alice reads → ALLOW (she logged in recently). Two hours later she tries
again → DENY (the login has expired from the 1-hour window).

You can also validate and lower to Cedar:

```bash
$ dogwood validate dogwood-docs/examples/read_after_login/policy.dw \
    --policy-schema dogwood-docs/examples/read_after_login/schema.cedarschema
OK: validation passed with no errors or warnings.

$ dogwood lower dogwood-docs/examples/read_after_login/policy.dw \
    --policy-schema dogwood-docs/examples/read_after_login/schema.cedarschema \
    --emit cedar-policies
@id("read_after_login")
permit(principal, action == Drupe::Action::"Read", resource) when { context.policy_0__temporal_0 };
```

The lowered Cedar replaces the temporal condition with a `context.*` slot that
Dogwood fills at runtime from the event history.

See the [Getting Started guide](dogwood-docs/guide/01-getting-started.md) for
full setup instructions and more examples in
[`dogwood-docs/examples/`](dogwood-docs/examples/).

## Using Dogwood as a Rust library

Add the crate to your `Cargo.toml`:

```toml
[dependencies]
dogwood-language = { git = "https://github.com/dogwood-policy/dogwood.git" }
```

See the [library README](dogwood-language/README.md) for the API overview and
the [API and Workflow guide](dogwood-docs/guide/07-api-and-workflow.md) for
detailed usage.

## AI agent integration

This repo ships agent skills that let AI coding assistants author Dogwood
policies from natural-language requirements. See
[AGENTS-README.md](AGENTS-README.md) for setup across Claude Code, Codex CLI,
Cursor, Copilot, and others.

## Security considerations when using the reference interpreter

As mentioned above, the reference interpreter provided here is **NOT** intended
to be used directly as an authorization engine for enforcing Dogwood policies.
The purpose is to provide a way to test and evaluate the semantics of Dogwood
policies.

A production-ready authorization engine needs to deal with several concerns
not addressed by the reference interpreter, including but not limited to:

- **Event timestamp integrity.** The interpreter accepts timestamps as provided
  and does not validate them. Production systems should use timestamps provided
  by a trusted time source or validate them before ingestion.

- **Event authentication.** The reference interpreter does not provide any kind
  of authentication on events. A production implementation should bind the
  authenticated caller identity as the principal before submitting events to an
  engine.

- **Event field consistency.** Fields needed by both temporal predicates
  AND Cedar conditions must be supplied to both the `logged` bag
  (`.field()`) and the `request_context` bag (`.request_context()`).
  Supplying only one silently weakens either temporal or Cedar checks.

- **Action naming consistency.** Events must use the same qualified action
  format as the policies (e.g., `"{ServiceName}::Action::Transfer"` not just
  `"Transfer"`). A mismatch causes temporal predicates to silently not
  match while Cedar may still authorize the action.

- **Trace management.** The built-in `InMemoryTemporalEngine` has no eviction or
  size cap. Production deployments handling sustained event volume should
  consider strategies for bounding and managing store size. Additionally, because
  the reference interpreter is purely in memory, its trace is lost after
  crash/restart. A production deployment ought to manage traces in a durable or
  fault-tolerant way. Keep in mind that depending on the nature of your policies,
  requests/events may contain sensitive data, so some method of protecting and
  purging that data ought to be used.

- **The `net` feature.** When enabled, provider scripts can make outbound
  HTTP requests via `http_get`. This function performs NO host or IP
  validation — it will connect to any address the URL specifies, including
  internal/private endpoints (169.254.169.254, 127.0.0.1, RFC-1918).
  Never construct the URL authority from untrusted event fields. See the
  provider guide for the safe pattern.

- **Policy validation.** Always run `Validator::validate()` on lowered policies
  before authorizing. Skipping validation may allow policies with degenerate
  windows, unresolved references, type mismatches etc. that behave unexpectedly
  at runtime.

- **Audit logging.** Dogwood returns decisions but does not log them.  A
  production implementation should use some form of logging around
  `is_authorized()` for compliance and forensics.

- **Multi-tenancy.** By default, an authorizer instance monitors one event
  history, with no isolation or partitioning between principals. The `pin`
  feature in the interpreter implements a rewriting pass that causes policies to
  be interpreted *as if* they were partitioned along the pinned key fields.
  However, this does not mean that an evaluation engine necessarily stores the
  event history in a partitioned way. A production deployment must consider and
  implement the appropriate level of isolation for their needs, and separate
  authorizer instances and event storage mechanisms may be warranted.

- **Rhai script sandboxing.** Provider scripts run in Rhai's embedded
  interpreter with no CPU/memory limits configured by default. A malicious or
  buggy provider script could infinite-loop or allocate unbounded memory,
  starving the authorizer. Production deployments should configure Rhai's
  `max_operations` / `max_call_levels` limits or run providers with a timeout.

- **Error message information leakage.** Error messages from the
  compiler/validator include policy content, field names, and type details. In a
  multi-tenant deployment where policies are authored by different parties,
  returning raw error details to one tenant could reveal another tenant's policy
  structure if policies are co-loaded. Production systems should sanitize or gate
  error output appropriately.

## Contributing

See [CONTRIBUTING.md](CONTRIBUTING.md).

## Security

See [SECURITY.md](SECURITY.md).

## License

This project is licensed under the Apache-2.0 License. See [LICENSE](LICENSE).
