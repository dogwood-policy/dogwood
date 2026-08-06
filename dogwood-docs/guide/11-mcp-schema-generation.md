# Generating the Action Schema from an MCP Manifest

This is the Advanced-topics page on schema *authoring via MCP*: a Dogwood action schema is, conceptually, a Model Context Protocol (MCP) tool manifest, and Dogwood can generate the Cedar `.cedarschema` for you from one. The hand-written counterpart of what this generation produces — declaring the entity and action types and laying out the `context.input` / `context.output` records yourself — is covered in [The policy language](02-policy-language.md). The *Rust API* for MCP generation (the `from_mcp_manifest` / `mcp_to_cedar_schema` constructors) lives in [The API and workflow](07-api-and-workflow.md); this page covers the manifest format, the JSON→Cedar type mapping, and the Drupe template.

So you often will not hand-write a `.cedarschema`. Because the frontend works in Cedar, Dogwood converts the manifest — a list of tools with their input and output JSON schemas — into a Cedar `.cedarschema` for you, layering the tools on top of the Drupe template.

From the command line, `dogwood schema mcp --manifest tools.json` generates the schema (write it out with `-o schema.cedarschema`); see [The command line](12-cli.md). The Rust equivalents are the `from_mcp_manifest` / `mcp_to_cedar_schema` constructors in [The API and workflow](07-api-and-workflow.md).

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

A tool's `inputSchema.properties` becomes the Cedar `context.input` record and `outputSchema` becomes `context.output`. JSON types map to Cedar types as follows: `integer` → `Long`, `string` → `String`, `boolean` → `Bool`, and `number` with `format: decimal` → `decimal`.

## How generation works

`mcp_to_cedar_schema(manifest_json)` produces the `.cedarschema` string using the embedded Drupe template; `mcp_to_cedar_schema_with_template(manifest_json, template)` uses a template you supply. Internally the generator:

1. parses the template `.cedarschema`,
2. parses the manifest to a server description,
3. seeds a schema generator with the template and the default config,
4. layers **one Cedar action per MCP tool**, deriving `input`/`output` context records from each tool's JSON schema,
5. serializes the result back to `.cedarschema` text.

The default config `include_outputs(true)` (emit `context.output` from each tool's `outputSchema`), `encode_numbers_as_decimal(true)` (JSON `number` → Cedar `decimal`), and `flatten_namespaces(true)` (so a tool `SellShares` becomes `Drupe::Action::"SellShares"` rather than a deeply qualified name).

## The Drupe template

The template supplies the principals, resource, base context, and base action hierarchy that tool actions are layered onto. Its key parts:

```text
namespace Drupe {
  @mcp_principal("User")                entity OAuthUser { id: String } tags String;
  @mcp_principal("IamEntity")           entity IamEntity { id: String };
  @mcp_principal("UnauthenticatedUser") entity UnauthenticatedUser;
  @mcp_resource("Gateway")              entity Gateway;
  @mcp_context("system")                type SystemContext = { now: datetime };

  // guardrail leaf types
  type ContentFilterFinding = { severityScore: decimal };
  type PromptAttackFinding  = { severityScore: decimal };
  type SensitiveInfoFinding = { confidenceScore: decimal };

  action Mcp  appliesTo { principal: [/* 3 */], resource: [Gateway], context: { system: SystemContext } };
  action Http appliesTo { /* … */ };
  @mcp_action("CallTools")
  action CallTool    in [Mcp]      appliesTo { /* … */ };
  action UnknownTool in [CallTool] appliesTo { /* … */ };
  action InvokeAgent in [Http]     appliesTo { /* …, */ input?: {} };
  action InvokeLLM   in [Http]     appliesTo { /* …, */ input?: {} };
}
```

The `@mcp_principal` / `@mcp_resource` / `@mcp_context` / `@mcp_action` annotations tell the generator which entities, types, and actions play each role. Generated tool actions are placed `in [Action::"CallTool"]` — matching the committed corpus schema at case 0407, where `Login`, `Read`, and `Transfer` are all `in [Action::"CallTool"]`.

## What you get

The generated `.cedarschema` combines the template (principals like `OAuthUser`, base actions) with one action per tool (`SellShares`, `GetStockInfo`, …). Because the tool's `stock` argument lands at `context.input.stock`, a plain Cedar policy validates against it:

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
