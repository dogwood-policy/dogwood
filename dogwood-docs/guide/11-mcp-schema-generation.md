# Generating the Action Schema from an MCP Manifest

This is the Advanced-topics page on schema *authoring via MCP*: a Dogwood action schema is, conceptually, a Model Context Protocol (MCP) tool manifest, and Dogwood can generate the Cedar `.cedarschema` for you from one. The hand-written counterpart of what this generation produces — declaring the entity and action types and laying out the `context.input` / `context.output` records yourself — is covered in [The policy language](02-policy-language.md). The *Rust API* for MCP generation (the `from_mcp_manifest` / `mcp_to_cedar_schema` constructors) lives in [The API and workflow](07-api-and-workflow.md); this page covers the manifest format, the JSON→Cedar type mapping, and the Drupe template.

So you often will not hand-write a `.cedarschema`. Because the frontend works in Cedar, Dogwood converts the manifest — a list of tools with their input and output JSON schemas — into a Cedar `.cedarschema` for you, layering the tools on top of the Drupe template.

From the command line, `dogwood schema mcp --manifest tools.json` generates the schema (write it out with `-o schema.cedarschema`); see [The command line](12-cli.md). The Rust equivalents are the `from_mcp_manifest` / `mcp_to_cedar_schema` constructors in [The API and workflow](07-api-and-workflow.md). Generation is behind the off-by-default `mcp-schema` Cargo feature of `dogwood-language` (forwarded by `dogwood-cli`), so build with `--features mcp-schema`.

The policy example on this page is a runnable bundle under `examples/`.

## The manifest

A manifest is a JSON array of MCP tool descriptions (or an MCP `tools/list` payload). Each tool has a name, description, and `inputSchema` / `outputSchema`:

```json
{
  "name": "SellShares",
  "description": "Sell `shares` shares of `stock`. Returns the proceeds in USD.",
  "inputSchema":  { "type": "object",
    "properties": { "stock": {"type":"string"}, "shares": {"type":"integer"} },
    "required": ["stock", "shares"] },
  "outputSchema": { "type": "object",
    "properties": { "proceeds": {"type":"number","format":"decimal"} },
    "required": ["proceeds"] }
}
```

A tool's `inputSchema.properties` becomes the Cedar `context.input` record and `outputSchema` becomes `context.output`. JSON types map to Cedar types as follows.

- `integer` → `Long`, `boolean` → `Bool`, and `number` → `decimal`, whatever its `format`.
- `string` → `String`, except for these formats: `date-time` and `date` → `datetime`, `duration` → `duration`, `ipv4` and `ipv6` → `ipaddr`, and `decimal` → `decimal`.
- A `string` with `enum` → an enumerated entity type. For example, the input field `senum` of the tool `T`, with `"enum": ["a", "b"]`, becomes `entity T_Input_senum enum ["a", "b"]`.

In a trace, write a `datetime`, `duration`, `ipaddr`, or `decimal` value as Cedar writes it, such as `datetime("2026-01-01T10:00:00Z")`, `duration("1h")`, `ip("127.0.0.1")`, or `decimal("1.5")`. A `decimal` can also be written as `1.5`, but not as `1`, which is a `Long`. Write an enumerated value as an entity of its type, such as `Drupe::T_Input_senum::"a"`. If a `request` event gives another value, such as a string, in its request context or its logged record, the decision is `Deny`. If a history event, such as a `response`, gives one in its logged record, the authorizer rejects the event and does not add it to the history.

## How generation works

`mcp_to_cedar_schema(manifest_json)` produces the `.cedarschema` string using the embedded Drupe template; `mcp_to_cedar_schema_with_template(manifest_json, template)` uses a template you supply. Internally the generator:

1. parses the template `.cedarschema`,
2. parses the manifest to a server description,
3. seeds a schema generator with the template and the default config,
4. layers **one Cedar action per MCP tool**, deriving `input`/`output` context records from each tool's JSON schema,
5. serializes the result back to `.cedarschema` text.

The default config `include_outputs(true)` (emit `context.output` from each tool's `outputSchema`), `encode_numbers_as_decimal(true)` (JSON `number` → Cedar `decimal`), and `flatten_namespaces(true)` (so a tool `SellShares` becomes `Drupe::Action::"SellShares"` rather than a deeply qualified name).

## The Drupe template

The template (`dogwood-language/configuration/mcp-template.cedarschema`) supplies the principal type, the resource type, the `system` context, and the two base actions that tool actions are layered onto. It declares the following (reformatted, without its comments).

```text
namespace Drupe {
  @mcp_principal("User")   entity User;
  @mcp_resource("Gateway") entity Gateway;
  @mcp_context("system")   type SystemContext = { now: datetime };

  action Mcp appliesTo {
    principal: [User], resource: [Gateway],
    context: { system: SystemContext, isOutput: Bool, output?: {} }
  };
  @mcp_action("CallTools")
  action CallTool in [Mcp] appliesTo {
    principal: [User], resource: [Gateway],
    context: { system: SystemContext, isOutput: Bool, output?: {} }
  };
}
```

The `@mcp_principal` / `@mcp_resource` / `@mcp_context` / `@mcp_action` annotations tell the generator which entities, types, and actions play each role. Generated tool actions are placed `in [Action::"CallTool"]` — matching the committed corpus schema at case 0407, where `Login`, `Read`, and `Transfer` are all `in [Action::"CallTool"]`.

## What you get

The generated `.cedarschema` combines the template (the principal type `User`, the resource type `Gateway`, and the base actions `Mcp` and `CallTool`) with one action per tool (`SellShares`, `GetStockInfo`, …). For the `SellShares` manifest above, the generated action is `SellShares in [Action::"CallTool"]`, with the context `input: SellSharesInput`, `output?: SellSharesOutput`, and `system: SystemContext`. Because the tool's `stock` argument lands at `context.input.stock`, a plain Cedar policy validates against it:

```text
permit(principal, action == Drupe::Action::"GetStockInfo", resource)
when { context.input.stock == "AMZN" };
```

> Runnable: [`examples/get_amzn_stock_info/`](../examples/get_amzn_stock_info/) — `dogwood validate` and `dogwood replay`.

Feeding the generated schema through `PolicySchema::from_cedarschema_str` and pairing it with a default `ServiceSchema` (so `request` is a decision kind) lets the policy above lower and validate cleanly.

This is also the basis of Dogwood's **MCP-manifest workflow**: point Dogwood at an MCP server's `tools/list`, and it produces the action schema you would otherwise write by hand.

---

## See also

- [The policy language](02-policy-language.md) — the hand-written counterpart: entity/action declarations and the `context.input` / `context.output` convention this generation produces.
- [The API and workflow](07-api-and-workflow.md) — the Rust constructors (`from_mcp_manifest` / `mcp_to_cedar_schema`) that drive MCP generation.
- [The event schema](03-event-schema.md) — how event kinds and their fields derive from the action schema.
