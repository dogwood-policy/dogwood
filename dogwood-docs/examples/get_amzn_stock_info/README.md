# get_amzn_stock_info

A plain (non-temporal) `permit` showing that an MCP-manifest input field
validates at `context.input.stock`. The tool's `stock` argument comes from the
MCP manifest's `inputSchema`, so in the generated Drupe schema it lands at
`context.input.stock` — meaning an ordinary Cedar `when` clause type-checks
against it. The rule allows `GetStockInfo` only when the requested stock is
`AMZN`; everything else is denied.

The trace shows both cases:

- `@0` — alice requests `GetStockInfo` for `AMZN` → **allow**.
- `@100` — bob requests `GetStockInfo` for `MSFT` → **deny**.

Referenced by `guide/11-mcp-schema-generation.md`.
