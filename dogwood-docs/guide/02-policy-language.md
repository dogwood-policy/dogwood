# The Policy Language

This page documents the **core** Dogwood policy language — the Cedar-derived surface
syntax you write in a `.dw` file. It covers the anatomy of a policy rule
(`permit`/`forbid`), the `(principal, action, resource)` scope and every constraint form
it accepts, `when`/`unless` condition clauses, and the *complete* condition-expression
language: every operator, literal, type, built-in method, set/record, and entity
reference.

Every policy example on this page is a runnable bundle under
[`examples/`](../examples/), checked on every build.

Dogwood's core language is an intentional re-implementation of upstream
[Cedar](https://www.cedarpolicy.com/) (the grammar is a faithful translation of
`cedar-policy-core` v4.11.0), so its syntax follows Cedar's. What
Dogwood adds on top is the `temporal { … }` *marker clause* — which hands off to a
dedicated sub-language — plus a thin `guardrails { … }` clause that is sugar for a
bare `when` (it invokes information providers, which are ordinary Cedar calls). This page
only *names* these forms and tells you where they attach; their contents are documented
separately (see the [See also](#see-also) list).

How to read this page: the grammar is deliberately **permissive**, and the real
semantics are enforced by the parser afterward. That means a
number of things *parse* but are then *rejected* with an error. Wherever that matters,
this page tells you the real, current behavior rather than what the grammar alone might
suggest.

Before the syntax, one thing a policy always assumes: an **action schema** that
declares the entities and actions a policy scopes over, and the `context` shape a
policy reads from. That comes first.

---

## The action schema

Every policy authorizes against an **action schema**: the declaration of your
world — the entity types (principals, resources) and the actions (tools,
operations) a policy may name — plus the `context` each action carries. It is a
**standard Cedar schema** (`.cedarschema`). Dogwood parses it with Cedar's own
parser and adds **no** new schema syntax — it is Cedar `.cedarschema` verbatim.
What Dogwood adds is a *convention* about how you lay out the `context` record,
covered below.

(The action schema is the one schema you always write. Dogwood composes two more
schemas — the event schema and the provider declarations — plus a macro library,
and all three have defaults, so the core language takes them as given;
see [The event schema](03-event-schema.md),
[The provider schema](10-provider-schema.md), and [Macros](06-macros.md) when you
need to customize them. You can also *generate* an action schema from an MCP tool
manifest — see
[Generating the action schema from an MCP manifest](11-mcp-schema-generation.md).)

### A real action schema

Here is a trimmed but complete schema from the tested corpus (case `1113`). It declares two tools, `Login` and `Read`:

```text
namespace Drupe {
  type LoginInput  = { user: String };
  type LoginOutput = { };
  type ReadInput   = { document: String, user: String };
  type ReadOutput  = { };
  type SystemContext = { now: datetime };

  entity Gateway;
  entity OAuthUser = { id: String };

  action "Login" appliesTo {
    principal: [OAuthUser],
    resource: [Gateway],
    context: {
      input: LoginInput,
      output?: LoginOutput,
      system: SystemContext
    }
  };

  action "Read" appliesTo {
    principal: [OAuthUser],
    resource: [Gateway],
    context: {
      input: ReadInput,
      output?: ReadOutput,
      system: SystemContext
    }
  };
}
```

The pieces:

- **`namespace Drupe { … }`** is the namespace your actions live under. Dogwood's derivation appends the literal segment `Action` to the namespace path, matching Cedar's rule that all actions live under an implicit `Action` entity type. So the `Login` action is written `Drupe::Action::"Login"` in policies and traces.
- **`entity` declarations** (`OAuthUser`, `Gateway`) are the principal and resource types. They may carry attributes (`= { id: String }`) and, in the fuller template, `tags` (e.g. `entity OAuthUser = { id: String } tags String;`).
- **`type` declarations** are Cedar *common types* — reusable record types (`LoginInput`, `ReadOutput`, …) that the actions reference as their `input` / `output` records. Common types may be cross-namespace (`Shared::Addr`) or chained (`type Outer = Inner;`); Dogwood resolves both.
- **`action "<Id>" appliesTo { principal, resource, context }`** declares one action per tool or operation. Actions may also sit in a group hierarchy with `in [...]` — for example the corpus schema at case `0407` has `CallTool in [Action::"Mcp"]` and `Login in [Action::"CallTool"]`, which is exactly the shape the MCP generator produces (see [Generating the action schema from an MCP manifest](11-mcp-schema-generation.md)).

### The `context.input` / `context.output` convention

`appliesTo.context` is an ordinary Cedar record, but Dogwood expects a specific layout so a policy — and the event stream — can find a tool's arguments and results by a stable path:

- **`input: <Record>`** — the tool's arguments. A policy reads them as `context.input.<field>` (e.g. `context.input.stock`).
- **`output?: <Record>`** — the tool's result. Optional (usually present only after the action resolves), read as `context.output.<field>`.
- **`system: SystemContext`** — the base context every action carries (`{ now: datetime }` in the Drupe template), read as `context.system.now`.

This is *only* a convention: nothing in Cedar forces it. A policy references these fields the same way it references any Cedar record — for instance `context.input.stock == "AMZN"`.

The `input` / `output` grouping also avoids a name collision. Because inputs nest under an `input` group and outputs under an `output` group, an action whose input and output *both* declare a field named `x` produces two distinct leaves, `input.x` and `output.x`, with possibly different types — something a flat context could not represent.

**Rule of thumb:** put a tool's arguments under `context.input` and its result under `context.output`. (This is also what the event schema's spread selectors read when deriving event fields; see [The event schema](03-event-schema.md).)

---

## Policy anatomy

A `.dw` file is a sequence of top-level items — **macro definitions** and **policy
rules** — freely interleaved, each terminated by a semicolon (`;`). Comments are
line-comments introduced by `//` and run to the end of the line; there are no block
comments. By convention every policy in the corpus opens with a `//` doc comment
describing its intent.

Here is the simplest possible policy — a single `permit` with no extra conditions:

```text
// The simplest possible Dogwood policy: a single permit with
// no further condition.
permit ( principal, action == Drupe::Action::"GetStockInfo", resource );
```

> Runnable: [`examples/simplest_permit/`](../examples/simplest_permit/) — `dogwood validate`.

Every policy rule has the same five-part shape, in this order:

1. Zero or more **annotations** (`@id("…")`)
2. An **effect** (`permit` or `forbid`)
3. A parenthesized **scope** triple `( principal, action, resource )`
4. Zero or more **condition clauses** (`when { … }` / `unless { … }`)
5. A terminating semicolon

```text
@id("sell_small_only")                                  // (1) annotation
permit (                                                // (2) effect
    principal,                                          // (3) scope
    action == Drupe::Action::"SellShares",
    resource
)
when { context.input.shares <= 50 };                    // (4) condition, (5) terminator
```

> Runnable: [`examples/sell_small_only/`](../examples/sell_small_only/) — `dogwood validate` and `dogwood replay`.

The sections below take each part in turn.

### Effect: `permit` and `forbid`

The effect is the first keyword of the rule and must be exactly `permit` or `forbid`.
Anything else is rejected with `policy effect must be `permit` or `forbid`, found `{other}``.

Dogwood evaluates a request under **deny-overrides with default-deny** semantics:

- A request is **allowed** if and only if at least one `permit` rule matches **and** no
  `forbid` rule matches.
- If no rule matches at all, the default decision is **deny**.

Because `forbid` always wins, source order does not matter — a `forbid` "carves a hole"
out of whatever the `permit` rules allow, no matter where it appears in the file. This
pair permits selling shares generally, but forbids selling AMZN:

```text
@id("permit-sell-shares")
permit ( principal, action == Drupe::Action::"SellShares", resource );

@id("forbid-sell-amzn")
forbid ( principal, action == Drupe::Action::"SellShares", resource )
when { context.input.stock == "AMZN" };
```

> Runnable: [`examples/deny_overrides_sell_not_amzn/`](../examples/deny_overrides_sell_not_amzn/) — `dogwood validate` and `dogwood replay`.

### Annotations: `@key("value")`

An annotation attaches metadata to a rule. It is written `@` followed by an identifier
key, optionally followed by a parenthesized string value:

```text
@id("sell_small_only")
permit ( principal, action == Drupe::Action::"SellShares", resource )
when { context.input.shares <= 50 };
```

The value string is optional, so both `@id("x")` and a bare `@reviewed` are legal. A rule
may carry any number of annotations. Annotations are purely for diagnostics and reporting
(the `@id` key names a rule so tools can refer to it) — they never change whether a rule
matches.

### Scope and conditions

The scope triple and the condition clauses are where all the matching logic lives; they
each get their own full section below ([The scope triple](#the-scope-triple) and
[Condition clauses](#condition-clauses)). The terminator is the `;` that ends every
top-level item.

---

## The scope triple

Every policy's scope is a parenthesized list of up to three variables: `principal`,
`action`, `resource`. These are the three fixed dimensions of an authorization request —
*who* is acting, *what* they are doing, and *what* they are acting on. The scope is the
fast, coarse filter: a rule can only possibly apply to requests whose principal, action,
and resource all satisfy the scope constraints. A trailing comma after the last variable is
allowed.

The variables may appear in **any order**, and any subset may be omitted — an omitted
variable is treated as unconstrained (matches everything). The following are all valid:

```text
permit ( principal, action, resource );          // all three, standard order
permit ( resource, action, principal );          // any order
permit ( principal, action );                    // resource omitted → any resource
permit ( );                                     // all omitted → matches everything
```

Each variable may appear **at most once** — duplicates are rejected with
`duplicate \`principal\` in scope`. If all three are present and a fourth element appears,
the error is `this policy has an extra element in the scope: \`{other}\``. If a variable
name is unrecognized before all three are seen, the error is
`unexpected scope variable \`{other}\`; expected \`principal\`, \`action\`, or \`resource\``.
Each of the three slots may be left **unconstrained** or given exactly one constraint. The
available constraint forms differ slightly between `principal`/`resource` (which behave
identically) and `action` (which is more restrictive).

### Unconstrained (bare) — matches everything

A bare variable name with no operator imposes no constraint on that dimension. A rule with
all three bare matches *every* request:

```text
@id("allow_anything")
permit (
    principal,
    action,
    resource
);
```

> Runnable: [`examples/allow_anything/`](../examples/allow_anything/) — `dogwood validate`.

### `==` — equality to a specific entity

`== EntityRef` requires the dimension to be exactly that entity. On `principal` and
`resource` the right-hand side must be an entity reference (`Ns::Type::"id"`) or a template
slot; on `action` it must be an action reference (no slots allowed):

```text
permit (
    principal,
    action == Drupe::Action::"SellShares",
    resource
);
```

> Runnable: [`examples/sell_shares_eq_scope/`](../examples/sell_shares_eq_scope/) — `dogwood validate`.

If the operand is not a valid entity reference you get
`` expected an entity reference (`Ns::Type::"id"`) or a template slot (`?principal`) ``
(for principal/resource) or `action scope expects an action reference (`Ns::Action::"id"`)`
(for action).

### `in` — membership in a group or hierarchy

`in` tests membership in an entity hierarchy (a group, a parent entity, etc.). On
`principal` and `resource` the right-hand side is a single entity reference or slot. On
`action` — and only on `action` — `in` may take a **list** of action references, meaning
"any of these actions":

```text
permit (
    principal,
    action in [Drupe::Action::"SellShares", Drupe::Action::"ApproveSale"],
    resource
);
```

> Runnable: [`examples/sell_or_approve_action_in/`](../examples/sell_or_approve_action_in/) — `dogwood validate`.

A single action reference is also accepted after `action in` (i.e. the list brackets are
optional for one element).

### `is Type` and `is Type in Group` — entity-type test

`is Type` matches only when the dimension's entity is of the named entity type;
`is Type in Group` additionally requires membership in a group. This applies to
`principal` and `resource`:

```text
permit (
    principal is Drupe::OAuthUser,
    action == Drupe::Action::"GetStockInfo",
    resource
);
```

> Runnable: [`examples/principal_is_oauth/`](../examples/principal_is_oauth/) — `dogwood validate`.

To combine both, write the type test first and the group after `in`:

```text
permit (
    principal is Drupe::OAuthUser in Drupe::Team::"traders",
    action == Drupe::Action::"GetStockInfo",
    resource
);
```

> Runnable: [`examples/traders_is_in_group_scope/`](../examples/traders_is_in_group_scope/) — `dogwood validate`.

Two restrictions to know:

- `action is Type` is invalid — the `is` form is not allowed on the action slot. You
  will get `` `action is Type` is not valid in the action scope ``.
- Only `is Type in …` may follow an `is` test. Writing `is Type == …` is rejected with
  `` `is Type {op} …` is not valid; only `is Type in …` is allowed ``.

### What the scope rejects

The scope grammar is permissive but the parser only accepts `==` and `in` (plus the
`is`/`is-in` forms above). Everything else is a parse-then-error:

- The legacy colon form `principal : User` is **not** supported — use `principal is User`.
  The error is `` the `principal : Type` scope form is not supported; use `principal is Type` ``.
- Writing `=` gets a targeted hint: `` `=` is not a valid operator in this scope; did you mean `==`? ``.
- Any other operator in a scope gives `` scope only allows `==` or `in`, found `{other}` ``.

---

## Condition clauses

The scope is a coarse filter; **condition clauses** express the fine-grained logic. A rule
may carry any number of `when` and `unless` clauses, in any combination and order. They
are implicitly **conjoined**: the rule fires if and only if *every* `when` body evaluates
true **and** *no* `unless` body evaluates true. Put another way, `unless { B }` is exactly
sugar for `when { !B }`.

Each clause is a keyword (`when` or `unless`) followed by a braced Cedar expression `{ … }`,
optionally preceded by the `temporal` marker or the `guardrails` tag (`temporal { … }` /
`guardrails { … }`, covered at the end of this section). A condition keyword other than
`when`/`unless` is rejected with
`` condition keyword must be `when` or `unless`, found `{other}` ``.

### `when { … }`

A `when` clause must hold for the rule to fire. Here we only permit selling under 100
shares:

```text
permit ( principal, action == Drupe::Action::"SellShares", resource )
when {
    context.input.shares < 100
};
```

> Runnable: [`examples/sell_when_under_100/`](../examples/sell_when_under_100/) — `dogwood validate`.

### `unless { … }`

An `unless` clause blocks the rule when its body holds. Here we permit selling *unless* the
order is enormous:

```text
permit ( principal, action == Drupe::Action::"SellShares", resource )
unless {
    context.input.shares > 10000
};
```

> Runnable: [`examples/sell_unless_huge/`](../examples/sell_unless_huge/) — `dogwood validate`.

### Multiple clauses on one rule

Because clauses are conjoined, you can stack them for readability instead of writing one
giant `&&`. Two `when` clauses both must hold:

```text
permit( principal, action == Drupe::Action::"SellShares", resource )
when { context.input.shares < 100 }
when { context.input.stock == "AMZN" };
```

> Runnable: [`examples/sell_two_when_small_amzn/`](../examples/sell_two_when_small_amzn/) — `dogwood validate`.

You can freely mix `when` and `unless` on the same rule:

```text
permit ( principal, action == Drupe::Action::"SellShares", resource )
when   { context.input.shares <= 1000 }
unless { context.input.stock == "BLOCKED" };
```

> Runnable: [`examples/sell_when_unless_mix/`](../examples/sell_when_unless_mix/) — `dogwood validate`.

The same applies to `forbid` rules — this forbids large sells except for AMZN:

```text
forbid ( principal, action == Drupe::Action::"SellShares", resource )
when   { context.input.shares > 100 }
unless { context.input.stock == "AMZN" };
```

> Runnable: [`examples/forbid_large_except_amzn/`](../examples/forbid_large_except_amzn/) — `dogwood validate` and `dogwood replay`.

### The `temporal { … }` marker and the `guardrails { … }` clause

Dogwood extends Cedar with two clause forms beyond a bare `when { … }`:

- `temporal { … }` — a genuine **marker** into a dedicated sub-language for
  temporal (history-aware) expressions. See
  [Temporal expressions](04-temporal-expressions.md).
- `guardrails { … }` — **not** a sub-language: `guardrails { E }` is transparent
  sugar for a bare `when { E }`, where `E` is ordinary Cedar. An information
  provider is invoked as a plain Cedar call (`Provider::Name(args)…`), recognized
  and hoisted at lowering — it needs no marker, and works in a bare `when` too.
  The tag is retained only for surface compatibility. See
  [Information providers](05-information-providers.md).

The `temporal` marker can appear in two places. First, as an entire clause body (a full permit combining both a `when temporal` and a `when guardrails` clause is runnable at [`examples/sell_after_approval_valid_ticker/`](../examples/sell_after_approval_valid_ticker/)):

```text
when temporal {
    formerly within 1h Drupe::Action::"Login"::response{ input.user: context.input.approver }
}
when guardrails {
    Strings::Matches(context.input.request_id, "^REQ-[0-9]+$").matched == true
};
```

Second, a `temporal` marker is also a primary expression, so it may appear
*inside* an ordinary Cedar expression (a full permit of this shape is runnable at
[`examples/sell_shares_temporal_subexpr/`](../examples/sell_shares_temporal_subexpr/)):

```text
when { context.input.shares > 5 && temporal { /* … */ } }
```

Both `unless temporal { … }` and `unless guardrails { … }` are equally valid.
The temporal marker's braced contents are out of scope for this page — see
the linked docs. All this page records is that these forms exist and where they
attach.

---

## The condition expression language

Everything inside a `when { … }` / `unless { … }` body (and inside a `def cedar` macro
body) is a Cedar expression. The expression grammar is a strict precedence tower — from
loosest to tightest binding: `if/then/else` → `||` → `&&` → relational (`<`, `has`,
`like`, `is`, …) → `+`/`-` → `*` → unary `!`/`-` → member access → primary. All binary
operator chains associate to the **left**. The subsections below walk the tower from the
top.

### `if / then / else`

`if C then A else B` is an expression (not a statement), so it produces a value and can
appear anywhere a value is expected. Both branches must produce the same type.

At the top level of a `when`, it reads like a conditional rule (runnable as a full
rule at [`examples/sell_threshold_by_stock/`](../examples/sell_threshold_by_stock/)):

```text
when {
    if context.input.stock == "AMZN"
    then context.input.shares <= 10
    else context.input.shares <= 1000
};
```

Because it is an expression, you can nest it and use it as an operand — here to pick a
per-stock threshold (runnable as a full rule at
[`examples/sell_nested_if_threshold/`](../examples/sell_nested_if_threshold/)):

```text
when {
    context.input.shares <=
        (if context.input.stock == "AMZN" then 10
         else if context.input.stock == "MSFT" then 50
         else 1000)
};
```

A common idiom pairs `if` with `has` (see [has](#has--attribute-existence)) to guard
an optional field, falling back to `false` when the field is absent (runnable as a full
rule at [`examples/sell_zero_proceeds_if_has/`](../examples/sell_zero_proceeds_if_has/)):

```text
when {
    if context has output
    then context.output.proceeds == decimal("0.0")
    else false
};
```

### Logical operators: `||`, `&&`, `!`

`||` (or) and `&&` (and) are the boolean connectives; `!` is boolean negation (a unary
prefix, covered under [arithmetic and unary operators](#arithmetic-and-unary-operators)).
`&&` binds tighter than `||`, so parenthesize when you want the other grouping (runnable
as a full rule at [`examples/sell_logical_grouping/`](../examples/sell_logical_grouping/)):

```text
when {
    (context.input.shares < 100 || context.input.stock == "AMZN")
    && !(context.input.stock == "BLOCKED")
};
```

### Comparison and relational operators

The relational level covers ordinary comparison operators plus the keyword operators
`has`, `like`, and `is`. The comparison operator set is:

| Operator | Meaning |
|---|---|
| `<`  | less than |
| `<=` | less than or equal |
| `>`  | greater than |
| `>=` | greater than or equal |
| `==` | equal |
| `!=` | not equal |
| `in` | entity-hierarchy membership |

Comparisons chain and fold left, so you can write several in a single `&&` conjunction
(runnable as a full rule at [`examples/sell_comparison_chain/`](../examples/sell_comparison_chain/)):

```text
when {
    context.input.shares >= 1
    && context.input.shares <= 1000
    && context.input.shares != 777
};
```

Note there is **no** `=` operator — writing `=` is rejected with
`` `=` is not a valid operator in this scope; did you mean `==`? ``.

`in` is not only a scope keyword; it is also an expression operator that tests
entity-hierarchy membership, e.g. `principalGroup in someParent`.

Which operators apply to which type matters, and is checked by the validator
downstream (not by the parser). The rules of thumb:

- **Long (integer)** supports the full ordered set: `<`, `<=`, `>`, `>=`, `==`, `!=`.
- **String** supports `==` and `!=` (and `like`, below). Ordered comparison is not
  meaningful. For example: `when { context.input.stock != "BLOCKED" };` (runnable as a
  full rule at [`examples/sell_not_blocked_string/`](../examples/sell_not_blocked_string/)).
- **Bool** is compared with `== true` / `== false`.
- **Decimal** supports **equality only** (`==` / `!=`). Ordered comparison on decimals does
  **not** type-check — use the decimal methods (`.lessThan`, etc.) instead (runnable as a
  full rule at [`examples/sell_nonzero_proceeds_decimal/`](../examples/sell_nonzero_proceeds_decimal/)):

  ```text
  when { context has output && context.output.proceeds != decimal("0.0") };
  ```

- **Datetime** supports the full ordered set, so you can express time windows directly
  (runnable as a full rule at [`examples/sell_datetime_window/`](../examples/sell_datetime_window/)):

  ```text
  when {
      context.system.now >= datetime("2025-01-01T00:00:00Z")
      && context.system.now <  datetime("2026-01-01T00:00:00Z")
  };
  ```

### Arithmetic and unary operators

Dogwood supports integer addition and subtraction (`+`, `-`) and multiplication (`*`):

- `+` and `-` are the additive operators.
- `*` is the **only** multiplicative operator that is accepted. Division (`/`) and modulo
  (`%`) *parse* but are rejected with `` `{other}` is not a supported operator ``.

There are two unary prefixes:

- `!` is boolean negation (`UnaryOp::Not`).
- `-` is arithmetic negation (`UnaryOp::Neg`).

A prefix may be a *run* of the same symbol (`!!x`, `--x`), but you cannot mix them — `!-x`
and `-!x` do not parse (neither `!` nor `-` can begin the value that the other prefix would
apply to). The `!` prefix is what you saw above in `!(context.input.stock == "BLOCKED")`.

One subtlety about negative integer literals: `-N` folds directly into a negative `Long`
value. The one special case is `9223372036854775808` (2^63): a bare `2^63` overflows
`i64` and is rejected, but `-9223372036854775808` is stored exactly as `i64::MIN`, so the
most-negative integer is representable via negation.

Datetime literals compare with the ordinary comparison operators (there is no `+`/`-`
arithmetic *on* datetimes at the operator level — use the `.offset` / `.durationSince`
methods for that, see [method calls](#method-calls)) — runnable as a full rule at
[`examples/sell_after_2024_datetime/`](../examples/sell_after_2024_datetime/):

```text
when { context.system.now > datetime("2024-01-01T00:00:00Z") };
```

### Member access: attributes, indexing, and calls

After a primary expression you can chain member accessors. There are three forms.

**Attribute access** `e.attr` reads a field. Chained attribute access is the
common form in Dogwood conditions:

```text
context.input.shares
context.output.approved
context.system.now
```

`context` is the request context; its `input` / `output` / `system` layout follows
[the convention above](#the-contextinput--contextoutput-convention), with the exact
shape of `context.input` determined by the rule's `action` scope.

**Index access** `e["key"]` reads a field by string key and is equivalent to attribute
access. Cedar requires the key to be a **string literal** — a dynamic index is rejected
with `index access requires a string-literal key, e.g. `record["field"]``:

```text
context.output.categories["VIOLENCE"]
```

**Call syntax** `e(args)` is only meaningful on a bare name (an
[extension function](#extension-functions-decimal-datetime-duration-ip) or macro call) or
after a `.method` ([method call](#method-calls)). A call applied to anything else is
rejected with `unexpected call: only extension functions and methods can be called`.

### `has` — attribute existence

`e has attr` tests whether an optional attribute is present, returning a boolean. It is the
guard you use before reading a field that might not exist. The right-hand side may be a
dotted path (`has a.b.c`), a string-literal name (`has "attr"`), or (per Cedar RFC 62) the
reserved word `if` used as an attribute name (`has if.x`). This guard-then-read pattern is
runnable as a full rule at [`examples/approve_has_output_guard/`](../examples/approve_has_output_guard/):

```text
when {
    context has output && context.output.approved == true
};
```

Because `&&` short-circuits, the `has` guard on the left protects the attribute read on the
right. The `if … then … else false` variant of this pattern was shown under
[if/then/else](#if--then--else).

### `like` — string pattern matching

`s like "pattern"` matches a string against a wildcard pattern. The right-hand side must be
a string literal. Inside the pattern, `*` matches any number of characters, `\*` matches a
literal star, and the usual escapes (including `\u{HEX}`) are supported (runnable as a full rule at
[`examples/sell_like_a_prefix/`](../examples/sell_like_a_prefix/)):

```text
when { context.input.stock like "A*" };
```

A common denylist idiom uses `like` under `unless` to reject a family of values (runnable
as a full rule at [`examples/sell_not_test_tickers_like/`](../examples/sell_not_test_tickers_like/)):

```text
unless { context.input.stock like "TEST_*" };
```

### `is` — entity-type test in a condition

`e is Type` tests whether an entity value has the given entity type, and the optional
`is Type in group` additionally checks hierarchy membership. This is the expression-level
counterpart of the `is` scope constraint (runnable as a full rule at
[`examples/cond_is_oauth_in_team/`](../examples/cond_is_oauth_in_team/)):

```text
principal is Drupe::OAuthUser in Drupe::Team::"traders"
```

The first operand after `is` is read as an entity *type* (not a value); the operand after
`in` is a value expression.

### Extension functions: `decimal`, `datetime`, `duration`, `ip`

A bare name immediately followed by `(args)` is an extension-function call. Dogwood
recognizes four built-in constructors, each taking exactly one string argument, used to
build the non-primitive literal types:

| Call | Type | Meaning |
|---|---|---|
| `decimal("…")`  | decimal  | fixed-point decimal literal |
| `datetime("…")` | datetime | ISO-8601 datetime literal |
| `duration("…")` | duration | duration literal |
| `ip("…")`       | ipaddr   | IP address / CIDR literal |

Examples:

```text
context.output.proceeds == decimal("0.0")
context.system.now > datetime("2024-01-01T00:00:00Z")
duration("1h30m")
ip("10.0.0.0/24")
```

Any *other* name-with-args (not one of these four) is treated as a **macro call** and is
resolved during macro expansion (see [Macros](06-macros.md)); an unresolved call is an
error.

### Method calls

A `.method(args)` after a receiver expression is a method call. Methods come in two arities.

**Zero-argument methods** (`receiver.method()`):

| Method | Domain | Meaning |
|---|---|---|
| `.isEmpty()`        | set      | set is empty |
| `.isIpv4()`         | ipaddr   | address is IPv4 |
| `.isIpv6()`         | ipaddr   | address is IPv6 |
| `.isLoopback()`     | ipaddr   | address is loopback |
| `.isMulticast()`    | ipaddr   | address is multicast |
| `.toDate()`         | datetime | drop the time-of-day |
| `.toTime()`         | datetime | time-of-day component |
| `.toMilliseconds()` | duration | duration as milliseconds |
| `.toSeconds()`      | duration | duration as seconds |
| `.toMinutes()`      | duration | duration as minutes |
| `.toHours()`        | duration | duration as hours |
| `.toDays()`         | duration | duration as days |

**One-argument methods** (`receiver.method(arg)`):

| Method | Domain | Meaning |
|---|---|---|
| `.contains(x)`             | set      | set contains element `x` |
| `.containsAll(s)`          | set      | set ⊇ set `s` |
| `.containsAny(s)`          | set      | set ∩ set `s` is non-empty |
| `.getTag(k)`               | entity   | read entity tag `k` |
| `.hasTag(k)`               | entity   | entity has tag `k` |
| `.isInRange(cidr)`         | ipaddr   | address is within CIDR |
| `.offset(d)`               | datetime | datetime + duration |
| `.durationSince(t)`        | datetime | datetime − datetime |
| `.lessThan(d)`             | decimal  | decimal `<` |
| `.lessThanOrEqual(d)`      | decimal  | decimal `<=` |
| `.greaterThan(d)`          | decimal  | decimal `>` |
| `.greaterThanOrEqual(d)`   | decimal  | decimal `>=` |

Note the decimal comparison methods — since `<`/`<=`/`>`/`>=` do not type-check on
decimals, these methods are how you order decimals (a full rule using `.lessThan` on a decimal output
field is runnable at [`examples/sell_small_proceeds_decimal_method/`](../examples/sell_small_proceeds_decimal_method/)):

```text
context.output.severityScore.lessThan(decimal("0.5"))
context.input.tags.contains("approved")
ip("192.168.1.5").isInRange(ip("192.168.0.0/16"))
```

Calling a method with the wrong number of arguments is rejected
(`` `{m}` takes no arguments… `` / `` `{m}` takes exactly one argument… ``), and an
unrecognized method name gives `` unknown method `{other}` ``.

### Primary expressions: literals, variables, grouping, sets, records

At the base of the tower, a **primary** is one of: a dialect marker, a literal, a template
slot, an entity reference, a variable name, a parenthesized expression, a set literal, or a
record literal.

**Variable names.** A bare name in value position must resolve to one of the four request
variables: `principal`, `action`, `resource`, or `context`. Any other bare identifier is an
error (`` `{other}` is not a valid variable ``).

**Parenthesized expressions** group to override precedence, as shown earlier:
`(context.input.shares < 100 || context.input.stock == "AMZN")`.

**Set literals** are square-bracketed, comma-separated expression lists (a trailing comma
is allowed). They are what an `action in […]` scope list uses, and they are also ordinary
values you can test with the set methods:

```text
["VIOLENCE", "HATE"]
```

**Record literals** are brace-delimited `key: value` pairs. Keys must be string literals or
bare identifiers; as a special case the reserved word `if` is allowed as a key:

```text
{ label: "review", count: 3, if: true }
```

---

## Literals and types

The atomic literal forms are:

| Literal | Type | Notes |
|---|---|---|
| `true` / `false` | Bool | boolean constants |
| `42`, `1000`     | Long | 64-bit signed integer; positive at the token level (`-` is a unary op) |
| `"…"`            | String | double-quoted |

Beyond these three primitive literals, the non-primitive types — decimal, datetime,
duration, and IP address — are constructed with the extension functions
(`decimal("…")`, `datetime("…")`, `duration("…")`, `ip("…")`) covered above. Sets and
records are built with `[ … ]` and `{ … }`, and entity references with the `Ns::Type::"id"`
form covered next.

**Integer range.** An integer literal is parsed as a 64-bit value. The only literal that
does not fit a signed `i64` is `9223372036854775808` (2^63): a bare `2^63` is out of range
and rejected (`` integer literal `…` is out of range ``), but `-9223372036854775808` is exactly
`i64::MIN`.

**String escapes.** Strings (and `like` patterns) support the escapes
`\n \t \r \0 \\ \" \' \*` plus braced unicode `\u{HEX}`:

```text
"line1\nline2"
"a literal quote: \""
"a\u{2764}b"
```

### Entity references: `Ns::Type::"id"`

An **entity reference** names a specific entity by type and id, using one or more `::`-
separated name segments followed by `::"id"`. This is how you refer to actions, users,
groups, and any other entity:

```text
Drupe::Action::"SellShares"     // an action
Drupe::OAuthUser                // just an entity type (no id) — used with `is`
Drupe::Team::"traders"          // a group entity
```

Entity ids are ordinary strings and may contain escaped or special characters, e.g.
`Drupe::Grant_Input_role::"o'admin"`.

Note that the `Type::{ … }` entity-*initializer* syntax (with a record body) **parses but is
rejected**: `` entity initializer syntax `Type::{ … }` is not supported ``. Use the
`Type::"id"` form.

### Template slots: `?principal` and `?resource`

Dogwood supports Cedar template slots, `?principal` and `?resource`, which act as
placeholders in principal/resource scope operands (they are not allowed in an `action`
scope):

```text
permit ( principal == ?principal, action, resource in ?resource );
```

A `?name` that is **not** `?principal` or `?resource` is a **macro parameter reference**,
which is only legal inside a macro body (see [Macros](06-macros.md)); using one anywhere
else is rejected during macro expansion.

---

## What parses but is rejected

Because the grammar is deliberately permissive and the parser enforces the real rules
afterward, several constructs *look* syntactically plausible but are always rejected. Do
not use these:

- **`=`** anywhere an operator is expected — rejected with a
  `did you mean `==`?` hint. There is no assignment operator and no single-`=` comparison.
- **`/` and `%`** — division and modulo parse but are rejected
  (`` `{other}` is not a supported operator ``). Only `+`, `-`, and `*` are supported.
- **The colon scope form `principal : Type`** — rejected; use `principal is Type`.
- **`action is Type`** in a scope — the `is` form is not valid on the action slot.
- **`Type::{ … }`** entity-initializer syntax — parses but is not supported.
- **Ordered comparison on decimals** (`<`, `<=`, `>`, `>=`) does not type-check — use
  the decimal comparison methods. Equality (`==` / `!=`) does work.
- **Integer `2^63`** as a bare literal — out of range (only reachable via negation).

---

## The `temporal` hand-off and the `guardrails` sugar

To recap the boundary of this page: the `temporal` marker hands off to a separate
sub-language, while `guardrails` does not.

- `temporal { … }` — history-aware conditions in a dedicated grammar. Appears either as a
  whole clause body (`when temporal { … }`) or as a primary inside a larger expression. Its
  braced contents are documented in [Temporal expressions](04-temporal-expressions.md).
- `guardrails { … }` — sugar for a bare `when { … }` (the tag carries no semantics); its body
  is ordinary Cedar. Information providers such as content-safety checks are invoked as plain
  Cedar calls (`Provider::Name(args)…`) — the surface tag keyword is `guardrails`, the concept
  is "provider" everywhere else. See [Information providers](05-information-providers.md).

Similarly, macro *definitions* (`def cedar name(?p) { … }` and `def temporal …`) let you
name and reuse expressions. A `def cedar` body is an ordinary core expression (everything on
this page applies), while a `def temporal` body is a temporal expression. Macro authoring —
definition syntax, parameters, expansion, and the default macro standard library — is covered in
[Macros](06-macros.md).

---

## See also

- [Introduction](00-introduction.md) — what Dogwood is and how the pieces fit together.
- [Getting started](01-getting-started.md) — write and evaluate your first policy.
- [The event schema](03-event-schema.md) — the event-kind DSL, and how the `context.input`/`output` records above become event fields.
- [Temporal expressions](04-temporal-expressions.md) — the `temporal { … }` sub-language.
- [Information providers](05-information-providers.md) — providers as plain Cedar calls, and the `guardrails { … }` sugar clause.
- [Macros](06-macros.md) — `def cedar` / `def temporal` definitions and expansion.
- [API and workflow](07-api-and-workflow.md) — parsing, compiling, and evaluating policies from Rust.
