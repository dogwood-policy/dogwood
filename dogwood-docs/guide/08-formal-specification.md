# A formal specification of Dogwood

This chapter is the precise, semi-formal reference for the Dogwood language: its
**concrete syntax** (BNF), its **abstract syntax**, and the three judgments that
give it meaning — **lowering** (Dogwood → Cedar), **validation** (well-formedness
and typing), and **authorization** (the operational semantics of a decision).

Where the rest of the guide (from [Getting started](01-getting-started.md) through
[The API and workflow](07-api-and-workflow.md)) explains *how to use* Dogwood, this
chapter states *what it is*, at the level of detail a second implementation or a
proof would need. Every rule is annotated
with its source of record — the file and function; the code is authoritative, and
this document tracks it.

## Contents

1. [Notation](#1-notation)
2. [Concrete syntax](#2-concrete-syntax)
3. [Abstract syntax](#3-abstract-syntax)
4. [Lowering: Dogwood ⇝ Cedar](#4-lowering-dogwood--cedar)
5. [Validation](#5-validation)
6. [Authorization](#6-authorization)
7. [Meta-properties](#7-meta-properties)

---

## 1. Notation

Dogwood is defined by **translation** into Cedar plus a stateful **monitor**.
A source policy set is first *lowered* to a Cedar `PolicySet` together with an
*augmented* Cedar schema; validation and authorization are then largely defined
in terms of that Cedar artifact, with the temporal sub-language and the
information providers supplying values that Cedar itself cannot compute. Three
judgments capture this:

| Judgment | Read as | Section |
|---|---|---|
| `Γ ⊢ p ⇝ π` | policy `p` **lowers** to Cedar policy `π` (recording hoisted leaves) | [§4](#4-lowering-dogwood--cedar) |
| `Σ ⊢ L ✓` | lowered artifact `L` is **valid** under schema `Σ` (no findings) | [§5](#5-validation) |
| `⟨H, e⟩ ⇓ ⟨H′, r⟩` | ingesting event `e` in history `H` yields history `H′` and result `r` | [§6](#6-authorization) |
| `⟨L, s⟩ ⇓_W ⟨L′, ρ⟩` | submitting `s`, with retry window `W`, to an instance whose log is `L` yields log `L′` and reply `ρ` | [§6.6](#66-the-event-log-contract-and-retries) |

Inference rules are written in the usual style — premises above the line,
conclusion below, name at the right:

```
        premise₁      premise₂
       ───────────────────────── (Rule-Name)
              conclusion
```

A rule with no premises is an axiom. A **side-condition** is written in the
premise position in prose. We write `⟦e⟧` for "the Cedar translation of `e`",
`fv(e)` for the free (unbound) variables of `e`, and `·` for sequence
concatenation. Metavariables: `p` policies, `e` core expressions, `φ` temporal
conditions, `t` terms, `A` actions, `k` event kinds, `H` histories, `β` temporal
bindings, `Σ` a (composite) schema.

Two channels of failure are distinguished throughout, and the distinction is
load-bearing (see [§5.1](#51-the-two-channel-error-model)):

- a **fatal error** (`Error`) aborts lowering — there is nothing well-formed to
  validate or authorize;
- a **finding** (`ValidationError` / `ValidationWarning`) is a validation result
  over an artifact that *did* lower.

---

## 2. Concrete syntax

The grammar is given in EBNF: `{ x }` is zero-or-more, `[ x ]` is optional,
`x | y` is alternation, `"lit"` is a terminal. It is transcribed from the three
`pest` grammars of record:

- core policy — `dogwood-syntax/src/grammar.pest`
- temporal — `dogwood-language/src/extension/temporal/grammar.pest`
- event schema — `dogwood-language/src/event_schema/grammar.pest`

(There is no provider grammar: an information-provider invocation is ordinary
Cedar recognized at lowering — see [§2.5](#25-information-provider-invocations-no-dedicated-grammar).)

Whitespace and `//` line comments are insignificant between tokens (each grammar
declares them implicit). Identifiers are `[A-Za-z_][A-Za-z0-9_]*`.

### 2.1 Policy sets, macros, rules

A `.dw` source is a sequence of macro definitions and policy rules, in any order.

```ebnf
policies    ::= { def_decl | policy }

def_decl    ::= "def" ("cedar" | "temporal") ident "(" [ params ] ")"
                "{" block "}" ";"
params      ::= param { "," param }
param       ::= "?" ident

policy      ::= { annotation } effect "(" scope ")" { cond } ";"
annotation  ::= "@" ident [ "(" string ")" ]
effect      ::= ident                       (* semantically: "permit" | "forbid" *)

scope       ::= [ variable_def { "," variable_def } [ "," ] ]
variable_def::= ident [ ":" name ] [ "is" add ] [ rel_op expr ]
```

Notes. `effect` is any identifier at the grammar level; a later pass requires it
to be `permit` or `forbid` (this yields a better diagnostic than a parse
failure). The `":"` form in `variable_def` (`principal : User`) is legacy and is
accepted only so the semantic pass can emit a "use `is`" hint. `block` is the raw
text between a marker's (or a `def` body's) braces, with balanced inner braces
honored; a string literal and a `//` comment (to the end of the line) are skipped
whole, as the sub-language parsers skip them, so a brace or a quote in either does
not move the block's end. It is dispatched to a sub-language parser.

### 2.2 Condition clauses

```ebnf
cond      ::= cond_kw ( extension_marker | guardrails_tag? "{" expr "}" )
cond_kw   ::= ident                          (* semantically: "when" | "unless" *)

extension_marker ::= dialect_tag "{" block "}"
dialect_tag      ::= "temporal"
guardrails_tag   ::= "guardrails"
```

A rule carries any number of `when` / `unless` clauses in any combination; they
are implicitly conjoined (the rule fires iff every `when` holds and no `unless`
holds — made precise in [§4](#4-lowering-dogwood--cedar)).

`temporal` is a genuine sub-language: the **tagged** form `when temporal { … }`
captures the braced body as raw `block` text dispatched to the temporal parser,
and — because `extension_marker` is also a `primary`
([§2.3](#23-core-expressions-cedar-derived)) — a temporal marker may appear
**inline**, so `when { context.x > 5 && temporal { … } }` is legal (the tagged
form alone cannot express this).

`guardrails`, by contrast, is **not** a sub-language: `guardrails { E }` is
transparent sugar for a bare `{ E }` clause, where `E` is a full Cedar
expression parsed identically to an untagged `when { … }`. An
information-provider invocation inside it (`Ns::Fn(args)…`) is recognized and
hoisted at *lowering* time exactly as in a bare `when { … }`
([§4.4](#44-information-provider-leaves)), so the tag adds nothing semantically
and the parser discards it. It is retained only for backward
compatibility of the surface syntax. ("provider" is the term used
everywhere else; `guardrails` is the surface keyword.) There is no closed
provider grammar.

### 2.3 Core expressions (Cedar-derived)

The core expression grammar is a `pest` transliteration of Cedar's own
(`cedar-policy-core` v4.x); precedence is encoded by the rule layering, exactly
as in Cedar's CST.

```ebnf
expr    ::= if_expr | or
if_expr ::= "if" expr "then" expr "else" expr
or      ::= and { "||" and }
and     ::= rel { "&&" rel }
rel     ::= add [ has_tail | like_tail | is_tail | { rel_op add } ]
has_tail::= "has" ( "if" { mem_access } | add )
like_tail ::= "like" add
is_tail ::= "is" add [ "in" add ]
rel_op  ::= "<=" | ">=" | "!=" | "==" | "<" | ">" | "in" | "="
add     ::= mult { ("+" | "-") mult }
mult    ::= unary { ("*" | "/" | "%") unary }
unary   ::= [ "!"+ | "-"+ ] member
member  ::= primary { mem_access }
mem_access ::= "." ident | "(" [ expr { "," expr } ] ")" | "[" expr "]"

primary ::= extension_marker | literal | slot | ref | name
          | "(" expr ")" | list | record
literal ::= "true" | "false" | number | string
slot    ::= "?principal" | "?resource" | "?" ident
name    ::= ident { "::" ident } | ident
ref     ::= name "::" ( string | "{" [ ref_init { "," ref_init } ] "}" )
list    ::= "[" [ expr { "," expr } ] "]"
record  ::= "{" [ rec_init { "," rec_init } ] "}"
```

`=` is captured by `rel_op` deliberately, so the semantic layer can emit a "did
you mean `==`?" hint rather than a raw parse error. A run of `!` or `-` may not
be mixed (`!-x` is rejected), matching Cedar. The grammar admits a relational
chain `{ rel_op add }` of any length, but more than one `rel_op` is rejected
after parsing (`a == b == c` must be parenthesized), matching Cedar. Likewise the
right-hand side of `has` may be any `add`, but only an attribute path is
accepted, as in Cedar: a name, a name followed by `.field` accesses, or a string
literal on its own (`has a.b`, `has "a b"`); unlike Cedar, a word Cedar reserves
(`if`, `then`, `__cedar`) may be a name of the path. A `number` must fit `i64`,
except a directly negated 2^63 (`-9223372036854775808`), as in Cedar. `/` and `%`
parse but are rejected downstream (Cedar has no division). Surface operators
`!=`, `>`, `>=` are retained here and desugared during lowering
([§4.3](#43-expression-translation)).

### 2.4 Temporal sub-language

The body of a `temporal { … }` block. Past-only; `within` is mandatory on every
temporal operator.

```ebnf
condition   ::= conjunct_or_since { "&&" conjunct_or_since }
conjunct_or_since ::= neg_conjunct [ "since" within atom ]
neg_conjunct::= { "!" } conjunct
conjunct    ::= comparison | parenthesized | temporal_op
              | exists_op | tp_op | call | refinable

temporal_op ::= "formerly" within atom | "previous" within atom
exists_op   ::= "exists" typed_binder "." condition
tp_op       ::= "tp" "(" binder_slot ")"
parenthesized ::= "(" condition ")"
atom        ::= "(" condition ")" | tp_op | call | refinable | comparison

refinable   ::= ( predicate | param_ref ) { field_block }
field_block ::= "{" [ named_args ] "}"
predicate   ::= qualified_action "::" event_kind "{" [ named_args ] "}"
qualified_action ::= ident { "::" ident } "::" string
event_kind  ::= ident
named_args  ::= named_arg { "," named_arg }
named_arg   ::= field_path ":" term
field_path  ::= ident { "." ident }

comparison  ::= arith cmp_op arith
arith       ::= arith_mul { add_op arith_mul }
arith_mul   ::= term { mul_op term }
add_op      ::= "+" | "-"
mul_op      ::= "*"
cmp_op      ::= "<=" | ">=" | "==" | "<" | ">"

agg_expr    ::= sum_expr | count_expr | call
sum_expr    ::= "sum" binder_slot for_binders "where" condition
count_expr  ::= "count" for_binders "where" condition
for_binders ::= "for" typed_binder { "," typed_binder } "."
typed_binder::= "(" binder_slot ":" type_expr ")"
type_expr   ::= ident { "::" ident }

within      ::= "within" ( param_ref | integer time_unit )
time_unit   ::= "s" | "m" | "h" | "d"

call        ::= ident "(" [ call_arg { "," call_arg } ] ")"
call_arg    ::= interval_lit | condition | term
interval_lit::= integer time_unit

term        ::= entity | decimal_lit | paren_agg | paren_arith | agg_expr
              | integer | string | "true" | "false" | array | context_field
              | scope_field | wildcard | param_ref | binder_ref | ident
paren_agg   ::= "(" agg_expr ")"
paren_arith ::= "(" arith ")"
entity      ::= ident { "::" ident } "::" string
decimal_lit ::= "decimal" "(" string ")"
context_field ::= "context" ("." ident)+           (* the context record  *)
scope_field ::= ("principal" | "resource") ("." ident)*  (* scope entity ± attr *)
wildcard    ::= "*"
binder_slot ::= param_ref | binder_ref | ident
param_ref   ::= "?" ident        (* macro value parameter    *)
binder_ref  ::= "$" ident        (* macro fresh binder       *)
```

Precedence and scope. `&&` is loosest; `!` binds tighter than both `since` and
`&&` (so `!a since W b` negates only `a`, and `!a && b` negates only `a`).
`exists` is a binding form with **maximal right scope**: `exists (x: T). φ && ψ`
binds `x` over `φ && ψ`; parenthesize to stop it early. An aggregate is a
*term* syntactically; the rule that an aggregate may appear *only* as a
comparison operand is a validation rule ([§5.4](#54-temporal-acceptance-well-formedness)),
not a grammar rule. `param_ref` (`?p`) and `binder_ref` (`$t`) are legal *only*
inside a macro body; the well-formedness pass rejects them elsewhere. Inside a
`def temporal` body, conversely, a variable or binder must be one of them: a
plain `ident` there is rejected, since expansion renames only `$t` and would keep
it as written. An `integer` (with its sign) must fit `i64`; one that does not is
rejected at parse time.

### 2.5 Information-provider invocations (no dedicated grammar)

An information-provider invocation has **no dedicated syntax**: it is an
ordinary Cedar expression ([§2.3](#23-core-expressions-cedar-derived)) whose
head is a namespace-qualified call, optionally followed by output *methods* and
a field/index projection, then used in any Cedar position (comparison,
arithmetic, boolean combination). All of the following are provider
invocations, recognized *structurally* — a namespaced `Ns::Fn(…)` call — and
hoisted at lowering ([§4.4](#44-information-provider-leaves)):

```text
Strings::Matches(context.input.doc, "^[A-Z]+$").matched == true
Content::Filter(context.input.doc, ["VIOLENCE"])["VIOLENCE"].severityScore.lessThan(decimal("0.5"))
BedrockGuardrails::ContentFilter(context.input.doc).maxConfidenceScore() < 50
Access::Allowed(principal.id).allowed == true
Strings::DigitCount(context.input.doc).count + 1 <= 3
```

Because the invocation is plain Cedar, it composes with the full expression
grammar — arithmetic on outputs, `if`/`then`/`else`, mixing provider and
non-provider terms — with no restriction beyond what Cedar itself allows. This
holds identically whether the invocation sits in a bare `when { … }` or a
`guardrails { … }` clause (the latter is transparent sugar for the former, see
[§2.2](#22-condition-clauses)).

Two surface shapes are relevant to the parser:

- **Arguments.** A provider argument is resolved *before* Cedar runs (it helps
  build the context Cedar evaluates against), so it must be a value the
  resolver can read off the request event: an attribute path rooted at
  `context`, `principal`, or `resource`; a literal (`string` / `integer` /
  `bool` / `decimal("…")`); or a set of those. This mirrors MFOTL's argument
  rule; arbitrary arithmetic / `if` is not a provider argument. A non-conforming
  argument is a lowering error ([§4.4](#44-information-provider-leaves)).

- **Methods.** A method whose name is not a Cedar built-in (`isEmpty`,
  `contains`, `lessThan`, …) is deferred by the parser as a `MethodCall` node
  (Cedar built-ins are still desugared eagerly). At lowering, if the chain's
  base is a provider invocation the method is a **declared output method**;
  otherwise it is a genuine unknown-method error. A method *post-processes* the
  output: `Fn(a).m(b)` binds `m(evaluate(a), b)`, and methods chain
  (`.m1().m2()` = `m2(m1(output))`). Each method has its own `argumentTypes` +
  `outputType` in the provider declaration's `availableMethods` map, and
  resolves to a `fn name(input, args…)` in the provider's Rhai script. The
  method chain is **eager** (evaluated in Rhai at authorize time); a
  field/index projection *after* the last method stays native Cedar over the
  hoisted value, and a projection may not precede a method in the same chain.

### 2.6 Event-schema DSL

A schema-independent description of how event signatures are derived from an
action schema.

```ebnf
schema      ::= { directive } { event_decl }
directive   ::= max_window | max_horizon            (* each at most once *)
max_window  ::= "max_window" "=" interval
max_horizon ::= "max_horizon" "=" interval
interval    ::= integer time_unit                  (* time_unit ∈ {s,m,h,d} *)
event_decl  ::= [ "decision" ] "event" "<" binder ">" "::" event_kind
                "{" [ fields ] "}"
fields      ::= field { "," field } [ "," ]
field       ::= spread | named_field
spread      ::= "..." selector "(" binder_ref ")"
named_field ::= [ "pin" ] ident ":" type_expr [ "=" pin_ref ]
selector    ::= "inputs" | "outputs" | "principalType" | "resourceType"
type_expr   ::= selector_call | record_type | concrete_type
selector_call ::= selector "(" binder_ref ")"
record_type ::= "{" [ fields ] "}"
concrete_type ::= ident { "::" ident }
pin_ref     ::= pin_scope | pin_context
pin_scope   ::= ("principal" | "resource") ("." ident)*
pin_context ::= "context" ("." ident)+
```

`decision` marks the event kind as a **decision kind** (ingesting one runs
authorization). `<A>` is the action binder; `...inputs(A)` splices the action's
`context.input` fields (likewise `outputs`); `principalType(A)` / `resourceType(A)`
yield the action's `appliesTo` entity type set. `pin` marks a field whose value
is forced to a request-side value on every predicate for the event (a
correlation); `pin` and the `= <reference>` clause must appear together, where
the reference is a scope entity (`principal` / `resource`, ± an attribute tail)
or a context field (`context.<path>`), and a pinned field must be a leaf. `pin`, `decision`, `event` are *contextual*
keywords. This grammar is purely syntactic — binding the selectors to a concrete
schema is the **derivation** pass, which runs inside lowering ([§4.5](#45-schema-derivation-and-augmentation)).

The optional leading `max_window = <interval>` directive caps how far back any
policy's temporal `within` window may look, and `max_horizon = <interval>` caps
a temporal leaf's **horizon**: the largest sum of the windows along one chain
of nested `formerly`, `previous` and `since` (`since` adds its window to the
longer of its sides; an aggregation reaches as far as its body). Each must
precede the event declarations, appear at most once, and be a positive
interval (a zero cap is a parse error). They resolve as follows: `max_horizon`
is the directive, and without one there is **no horizon cap**; `max_window` is
the directive, else the declared `max_horizon`, else **24h**. A `max_window`
longer than a declared `max_horizon` is an event-schema error. The caps are enforced by the temporal
dialect ([§5.5](#55-temporal-dialect-validation-against-the-schema),
**TEMP-MaxWindow**, **TEMP-MaxHorizon**). Since no event older than a
condition's horizon can matter, retention of a declared `max_horizon` suffices
for every policy set the event schema lets validate (Lean:
`authorize_drop_maxHorizon`).

---

## 3. Abstract syntax

Parsing produces the surface AST. The core spine and operators are Dogwood's own
(`src/ast.rs`); leaf *values* (literals, entity refs, patterns, entity types)
reuse Cedar's `cedar_policy_core::ast` types verbatim.

```
PolicySet  ::= (defs: MacroDef*,  policies: Policy*)
Policy     ::= (annots: Annotation*, effect: Effect, scope: Scope, conds: Cond*)
Effect     ::= Permit | Forbid
Cond       ::= (kw: When | Unless, body: Expr)
Scope      ::= (principal: PrincipalConstraint,          (* Cedar constraints,   *)
                action:    ActionConstraint,             (* built by the parser, *)
                resource:  ResourceConstraint)           (* carrying .dw Locs     *)

Expr       ::= Lit ℓ | Var v | Slot s | Extension X
             | UnaryApp(UnOp, Expr) | BinaryApp(BinOp, Expr, Expr)
             | GetAttr(Expr, name) | HasAttr(Expr, name⁺) | Like(Expr, pat)
             | Is(Expr, ety, Expr?) | IfThenElse(Expr, Expr, Expr)
             | Set(Expr*) | Record((name × Expr)*)
             | Call(name, Expr*) | MethodCall(Expr, name, Expr*)  (* both residual; see below *)
             | ParamRef(name)                                     (* transient; see below *)
X          ::= Temporal φ
```

`UnOp` = `Not | Neg | IsEmpty` plus the extension constructors
(`decimal | datetime | duration | ip`) and zero-argument extension methods
(`isIpv4 | … | toDays`). `BinOp` = the core relational/boolean/arithmetic
operators (including the surface-only `NotEq | Greater | GreaterEq`), the
set/entity/tag operators, and the one-argument extension methods
(`DecimalLessThan | … | isInRange | offset | durationSince`). `Extension` now
carries only `Temporal` — an information provider is *not* an extension leaf but
a residual `Call`/`MethodCall` recognized at lowering (below). `Call`,
`MethodCall`, and `ParamRef` are **residual**: after macro expansion a `Call`
survives only if it is a namespace-qualified (provider) invocation, a
`MethodCall` survives only as a non-Cedar-builtin method (a provider output
method), and `ParamRef` never survives — lowering hoists the provider forms
([§4.4](#44-information-provider-leaves)) and rejects everything else.

**Temporal abstract syntax** (`src/extension/temporal/ast.rs`):

```
φ  (Condition)  ::= And(φ, φ) | Not(φ)
                  | Formerly(W, φ) | Previous(W, φ) | Since(φ, W, φ)
                  | Predicate P | Comparison(⋈, t, t)
                  | Exists((x:T), φ) | Tp(x)
                  | Call c | SigilRef(σ, name) | Refine(φ, NamedArg*)  (* transient *)
P  (Predicate)  ::= (ns: name*, action: string, kind: string, args: NamedArg*)
NamedArg        ::= (name: field_path, value: t)
t  (Term)       ::= Entity(ty,id) | Int n | Decimal s | Str s | Bool b
                  | ContextField(seg*) | Var x | Wildcard | Array(t*)
                  | Agg a | Arith(⊕, t, t)
                  | ParamRef name | BinderRef name                      (* last two transient *)
a  (AggExpr)    ::= Sum(x, (x:T)*, φ) | Count((x:T)*, φ) | Call c
⊕  (ArithOp)    ::= + | − | ×
                    (* a zero-operator operand is a bare t, never a
                       degenerate Arith *)
⋈  (CmpOp)      ::= ≤ | < | ≥ | > | =
W  (WithinSpec) ::= Concrete(n, unit) | ParamRef name                  (* ParamRef transient *)
T  (Type)       ::= Timepoint | Named(name*)
```

A `NamedArg`'s `name` is the field path `seg*` written as one string
(`src/field_path.rs`): each segment with `\` written `\\` and `.` written `\.`,
and the segments joined by `.`. `NamedArg::field_path` splits the string at its
unescaped dots and drops the escapes, the inverse on every non-empty path, so a
segment that holds a `.` (the Cedar attribute `input["user.id"]`) stays one
segment. A path of identifiers is its plain dotted text.

`Since`'s negative form ("left has *not* held since") is `Not` around the left
operand — there is no dedicated flag. `Tp(x)` binds `x` to the current
timepoint. Binder type annotations are **authoritative**: validation seeds each
declared type into the type environment and checks every use of the variable
against it (see [§5.5](#55-temporal-dialect-validation-against-the-schema)),
rather than inferring the type from a use site. The **transient** nodes (`Call`, `SigilRef`, `Refine`, `Term::ParamRef`,
`Term::BinderRef`, `BinderSlot::{ParamRef,BinderRef}`, `WithinSpec::ParamRef`,
`AggExprKind::Call`) appear only inside an unexpanded macro body and are removed
by macro expansion; a valid post-expansion tree contains none of them.

**Provider data types** (`src/extension/provider/ast.rs`): there is no provider
expression AST — an invocation lives in the core `Expr` tree as a `Call` (with
an optional `MethodCall` chain). The module holds only the data types the
invocation is *lifted into* at lowering: `Invocation = (function: name*,
args: Arg*)`, a `MethodCall = (name, args: Arg*)` for each output method, and
`Arg ::= Field(seg*) | String | Integer | Decimal | Bool | Set(Arg*)`, where a
`Field` path is rooted at `context` / `principal` / `resource`.

---

## 4. Lowering: Dogwood ⇝ Cedar

Lowering is a **translation semantics**: a Dogwood policy set becomes a Cedar
`PolicySet` (one static policy per rule) plus an *augmented* Cedar schema and a
list of *hoisted leaves*. It is the crate-private `parse`/`lower` pipeline
(`src/api.rs`), split into two phases along the one input that motivates the
split — the action schema (see [Chapter 07](07-api-and-workflow.md)):

- **`parse(source, ServiceSchema)`** — pure syntax: parse, merge the macro
  library, macro-expand. No action schema. (`api.rs`, `ParsedPolicySet::parse`, rule **L-Phase-Parse**.)
- **`lower(parsed, PolicySchema, distincter?)`** — derive the event schema
  against the action schema, translate each rule, augment the schema, inject
  pins, and assemble the `Lowered` artifact. (`api.rs`, `lower`, rule **L-Phase-Lower**.)

The translation environment is `Γ = (𝓀, ι, D)` where `𝓀` is the current rule's
**rule key** ([§4.1](#41-rules-policy-ids-and-hoisting)), `ι` a per-rule field
ordinal, and `D` the provider declarations. We write `Γ ⊢ e ⇝ ⟦e⟧ ⊣ Γ′` for
"`e` translates to the Cedar expression `⟦e⟧`, threading state `Γ → Γ′`" (the
state carries the accumulating hoisted-leaf lists and the ordinal counter).

### 4.1 Rules, policy ids, and hoisting

Each Dogwood rule becomes exactly one Cedar static policy.

```
   effect ↦ ε      scope = (P, A, R)      Γ₀ = Γ[𝓀 := key(δ, i), ι := 0]
   Γ₀ ⊢ conds ⇝ γ ⊣ Γ′        id = key(δ, i)      annots ↦ ᾱ
  ───────────────────────────────────────────────────────────────────── (L-EmitPolicy)
   Γ ⊢ (rule i, effect, scope, conds, annots)
        ⇝  StaticPolicy(PolicyID id, ᾱ, ε, P, A, R, γ)  ⊣ Γ′
```

*(`cedarify/mod.rs` `emit_policy`.)* The scope constraints `P, A, R` pass through
**unchanged** — the parser already built them as loc-bearing Cedar constraints
(**L-ScopePassthrough**, `cedarify/mod.rs` `emit_policy`). Effect maps directly, `Permit ↦ Permit`,
`Forbid ↦ Forbid` (**L-Effect**). Annotations map to Cedar annotations; a key
that fails to parse as a Cedar id is silently dropped, and `@id` is **not**
special-cased — it is an ordinary annotation, never the policy's identity
(**L-Annotations**, `cedarify/mod.rs` `emit_policy`). A rule containing an unfilled template slot
(`?principal`/`?resource`) fails: `StaticPolicy::try_from` errors *"policy is not
static"*.

**Rule key.** The `i`-th rule's key — which is simultaneously the emitted Cedar
**PolicyID**, the policy-store key, the decision token returned in a response, and
the **prefix on that rule's hoisted field names** — is

```
key(δ, i)  =  δ "_" i      if a distincter δ is supplied
           =  "policy_" i   otherwise
```

*(`cedarify/mod.rs` `rule_key`, rule **L-RuleKey**.)* It is deliberately **not** derived
from `@id`; distinctness is the caller's decision, so that independently-lowered
sets can be combined without colliding ids (see [Chapter 07](07-api-and-workflow.md)
on `lower_with_distincter`). Two rules that mint the same id are a fatal error
(*"duplicate policy id"*). The field ordinal `ι` resets to `0` at each rule
boundary and is shared by both hoisting schemes below.

### 4.2 Clause folding

A rule's condition `γ` is the conjunction of its clauses, `when` verbatim and
`unless` negated:

```
  ───────────────────────────── (L-Fold-Empty)
   Γ ⊢ [] ⇝ true ⊣ Γ
```
```
   Γ ⊢ e ⇝ ⟦e⟧ ⊣ Γ′
  ────────────────────────────── (L-Fold-When)
   Γ ⊢ (when e) ⇝ ⟦e⟧ ⊣ Γ′
```
```
   Γ ⊢ e ⇝ ⟦e⟧ ⊣ Γ′
  ─────────────────────────────────── (L-Fold-Unless)
   Γ ⊢ (unless e) ⇝ !⟦e⟧ ⊣ Γ′
```
```
   Γ ⊢ cᵢ ⇝ γᵢ ⊣ Γᵢ₊₁  (each clause in source order)       n ≥ 1
  ──────────────────────────────────────────────────────────────── (L-Fold-Cons)
   Γ₁ ⊢ [c₁ … cₙ] ⇝ balanced(γ₁ … γₙ) ⊣ Γₙ₊₁
```

*(`cedarify/mod.rs` `emit_policy`.)* Each clause translates in source order,
threading the context, and the results are conjoined as a **balanced** `&&`
tree over them in that order: adjacent operands are paired left to right, an odd
last operand is carried up a level unchanged, and the pairing repeats until one
operand remains. So `[c₁, c₂]` becomes `And(γ₁, γ₂)`, `[c₁, c₂, c₃]`
`And(And(γ₁, γ₂), γ₃)`, and `[c₁ … c₄]` `And(And(γ₁, γ₂), And(γ₃, γ₄))`. The
tree is ⌈log₂ n⌉ deep instead of n, so a rule with many clauses does not
overflow Cedar's recursive printer, typechecker or evaluator. It decides as the
left-nested chain does: Cedar's `&&` evaluates its left operand first and
returns at the first `false` or error, so any `&&` tree over the same operands
in the same order visits the clauses in clause order and stops at the same one.
A bare rule (no clauses)
has condition literal `true` — note this is `Some(true)`, an explicit condition,
not an absent one. The synthesized `Not` (for `unless`) and `And` (for the
conjunction) nodes carry the **whole-rule** source location, since they
correspond to no surface token; every other node carries its own span
(**L-NodeLoc**).

### 4.3 Expression translation

Non-extension expressions translate by a straightforward syntax-directed map,
each node stamped with its `.dw` span. Leaves: `Lit ℓ ⇝ ℓ`, `Var v ⇝ v`,
`Slot s ⇝ s` (**L-Expr-Leaves**). Structural nodes recurse and rebuild
(`GetAttr`, `HasAttr`, `Like`, `Is`, `IfThenElse`, `Set`, `Record` —
**L-Expr-Structural**). Operators desugar via Cedar's own `ExprBuilder` — the
same primitive Cedar's text parser uses — so the output is identical to
Cedar-parsed text. The **surface-only** operators desugar to negations:

```
   NotEq(l, r)     ⇝  !(⟦l⟧ == ⟦r⟧)
   Greater(l, r)   ⇝  !(⟦l⟧ <= ⟦r⟧)
   GreaterEq(l, r) ⇝  !(⟦l⟧ <  ⟦r⟧)
```

*(`to_ast.rs` `lower_binary`, **L-Binary-Table**.)* Extension constructors and methods
become `ExtensionFunctionApp`s keyed by the unqualified name: unary
`decimal | datetime | duration | ip | isIpv4 | … | toDays`
(**L-Unary-Table**, `to_ast.rs` `lower_unary`) and binary
`isInRange | offset | durationSince | lessThan | lessThanOrEqual | greaterThan | greaterThanOrEqual`.
A `Call` that is not a namespace-qualified (provider) invocation, and any
`ParamRef`, are fatal at this point (**L-Expr-Call**) — a well-formed
post-expansion tree has neither except a provider `Call`/`MethodCall`, which the
provider rules below hoist.

### 4.4 Information-provider leaves

A temporal marker and a provider invocation are the two forms that are not a
pure syntactic map: each is **replaced** by a `context.<id>` reference and its
content **recorded** as a hoisted leaf, evaluated by the monitor at
authorization time. The `.dw` span of the replacement is the original node's
span, so a type error on a hoisted field points back at the source it came from.

```
   name = 𝓀 "__temporal_" ι      Γ′ = Γ[ι := ι+1, bool_fields ⊕ ⟨scope, name, φ⟩]
  ─────────────────────────────────────────────────────────────────────────────── (L-Hoist-Temporal)
   Γ ⊢ Temporal φ  ⇝  context.name  ⊣ Γ′
```

*(`to_ast.rs` `lower_expr`.)* The recorded `ContextField` carries the rule's scoped action
(`Concrete` / `List` / `Unconstrained`, classified off the Cedar action
constraint — **L-ScopeAction-Classification**, `cedarify/mod.rs` `scope_action`), the field name, and
the temporal condition. Semantically the field is a pre-evaluated `Bool`.

A **provider invocation** is a `Call` whose name is namespace-qualified
(**L-Expr-Call-Provider**), or a `MethodCall` chain whose base peels down to such
a `Call` (**L-Expr-Method-Chain**, `to_ast.rs:peel_provider_chain` — a
`MethodCall` whose base is not a provider is the fatal unknown-method error). In
both cases lowering collects the base `Invocation`, its eager output-method chain
(in source order), and any *trailing* field/index projection after the last
method. The rule may use any action scope (`==`, `in [list]`, `in Group`, or a
bare `action`); the hoisted field is typed from the declarations, declared on
one shared all-provider common type, and made available on every action reached
by at least one provider-bearing rule. It is evaluated for every decision event
(execution is unconditional — see the provider contract in
[Information providers](05-information-providers.md#the-provider-contract)). It
hoists to a **two-level** reference `context.providers.<id>`:

```
   name = 𝓀 "_p_" ι      τ = cedarType(D, invocation, methods)      Γ′ = Γ[ι := ι+1, provider_fields ⊕ …]
  ──────────────────────────────────────────────────────────────────────────────────────────────────── (L-Hoist-Provider)
   Γ ⊢ Invocation·methods  ⇝  context.providers.name  ⊣ Γ′
```

*(`to_ast.rs` `lower_provider_invocation`.)* `τ` is the pipeline's tail type: the
last method's `outputType` if the chain is non-empty, else the invocation's
`outputType`, looked up from the declarations `D` and defaulting to `String` when
undeclared (the undeclared case — and an undeclared/misused method — is caught by
validation, [§5.6](#56-provider-dialect)). The invocation's arguments are lifted
to `Arg`s (attribute paths rooted at `context`/`principal`/`resource`, literals,
sets; a non-conforming argument is fatal). The method chain is **eager**
(evaluated in Rhai at authorize time and bound into the field); the trailing
projection (`.field` / `["key"]`) lowers to a chain of native `GetAttr` over the
hoisted value (a string index `r["k"]` is exactly `r.k`), and the surrounding
comparison is ordinary Cedar (**L-Provider-Projection**). A projection may not
precede a method in the same chain (fatal).

Because the field name is prefixed by the rule key `𝓀` and suffixed by the
per-rule ordinal `ι`, hoisted names are deterministic and unique across lowering
calls with distinct distincters — the property that lets independently-lowered
sets share one Cedar `PolicySet` / policy store.

### 4.5 Schema derivation and augmentation

Two schema transformations happen inside `lower`:

1. **Derivation.** The event-schema DSL ([§2.6](#26-event-schema-dsl)) is bound
   against the concrete action schema, yielding, per action `A` and declaration,
   a derived event `(ns(A), A, kind, decision?, fields, pins)`. This is the sole
   place the symbolic selectors (`inputs`/`outputs`/`principalType`/`resourceType`)
   meet a real schema. The set of kinds marked `decision` becomes the
   `decision_kinds` used by the authorizer (`event_schema/derive.rs`).

2. **Augmentation.** The action schema is extended with the hoisted context
   fields the lowered policies reference: for each temporal leaf, a required
   `Bool` attribute `context.<name>` on its action(s); for provider leaves, one
   annotated generated common type per touched namespace (normally
   `DogwoodProviders`, with a collision-avoiding numeric suffix) containing
   every provider field, typed from the declarations. Actions reached by any
   provider rule reference that type. Feed-forward augmentation extends every
   previously generated shared definition, preserving earlier providers
   (`cedarify/schema_augment.rs`).

   A temporal leaf's field is added only to the actions its rule's action scope
   can apply to, and the Lean specification augments the same actions
   (`PolicySet.augmentedSchema`), up to two differences that change no
   verdict: the crate gives each action a provider rule reaches the whole
   shared provider record, and leaves out pure action groups, which have no
   request environment. Adding the fields to more actions gives the same
   validation verdict (`Dogwood.Thm.valid_iff_covers`).

   **Combining sets: a whole-context read breaks once any set has a leaf.**
   The schema adds a hoisted field only to its rule's actions, but at decision
   time the authorizer puts every hoisted value of the store into every
   request's context. So a rule that reads `context` whole, which a set
   without leaves may do, is silently `false` once it shares a store with any
   set that has a leaf, whichever actions that leaf targets; re-validating the
   earlier set against the final schema catches this only when the leaf is on
   the same action. The specification states the rule precisely
   (`Dogwood.Thm.Composition`): two lowerings, each valid, compose into a valid
   set exactly when the combined set passes the context-read check
   (`valid_join_iff_contextReadsOk`), provided the second set's leaves and the
   pins read none of the first set's hoisted attributes. The crate rejects such
   reads. A whole-context read in the first set breaks composition once the
   second has a leaf
   (`not_valid_join_of_whole_context_read`). `Validator::validate` on the
   result of `lower_many` performs that check on the combined set.

Finally the temporal leaves' conditions have schema **pins** injected — a pinned
event field `f` is conjoined `f: context.<pin-path>` onto every matching
predicate, realizing the "same X" correlation (`event_schema/pin.rs`). The
injected argument's name is the text of the pinned field's path, written as
for every `NamedArg`.

After pin injection, leaves are **relativized** when the schema declares at
least one *universal symmetric* pin — a symmetric pin (one whose value is the
request's principal, its resource, or a context attribute, written
`= principal`, `= resource` or `= context.<path>`, whatever the field is
called) present
identically on every derived event kind (**L-Relativize**,
`event_schema/relativize.rs`). Let μ be the disjunction, over every derived
event kind, of a predicate carrying exactly the pinned correlations ("an event
of any kind agreeing with the current request on every universally-pinned
field"). The rewrite guards each temporal-scope body that does not already
contain a positive predicate conjunct with `μ ∧ ·`; replaces
`previous[0,W] φ` by a timepoint-encoded "most recent μ-position satisfies φ,
within W of the decision point" (an anti-join over `tp`-bound positions); and
replaces a `since` whose left is not a μ-confined negation by a
count-equality encoding of "every μ-position in the anchor range satisfies the
left". The rewritten formula's verdict over the global trace equals the
original formula's verdict over the sub-trace agreeing with the request on the
pinned fields — the **partition guarantee**: storage and evaluation may be
sharded by the pinned key without changing any verdict. Every synthesized
binder is fresh (`__pin_*`, with as many `_` after `__pin` as it takes for no
variable of the leaf to start with the prefix) and range-restricted by a
positive atom before any filter uses it. Validation (§5) runs on the **pre-rewrite** leaves, so
findings point at authored structure; engines receive the rewritten leaves
(`Lowered.temporal_rewritten`, surfaced by `temporal_fields()` /
`temporal_leaves()`). With no universal symmetric pin the rewrite is the identity. The default event
schema is not such a case: it pins `callerPrincipal` on every derived kind, so under
the default the rewrite is active.

**Sharding by key, and stamps.** The partition guarantee is stated over a history
whose timestamps are given. An authorizer that assigns the timestamps itself, as
the formal specification's does (`dogwood-lean`, `Dogwood.Spec.Ingest`: an
event's stamp is `max(reading, last + 1)`), and that keeps one log per key,
stamps each key's log on its own: `last` is the stamp of the last event of the
same key. The formal specification defines this partitioned evaluation
(`dogwood-lean`, `Dogwood.Spec.Partitioned`, `PolicySet.PartLeafHolds`): each
temporal leaf of a decision is evaluated over the decision's own key's log,
stamped on its own. It is what `AuthorizerBuilder::partition_temporal()`
([API and workflow](07-api-and-workflow.md)) and an engine that keeps one log
per key compute. It agrees with stamping one log of all events
when the clock readings strictly increase across keys. When they do not, an
event that arrives at the reading of another key's event is stamped one tick
later in the single log than in its own key's log, and at a window's edge that
tick can change a verdict.

The result is the `Lowered` artifact (**L-Lowered-Artifact**, `api.rs`, `struct Lowered`):
the Cedar `policies`, the `augmented_schema` (+ its source text), the hoisted
`temporal` and `provider` leaf lists, the parallel `rule_ids` / `rule_spans`
(where `rule_ids[k]` is rule `k`'s PolicyID), the derived `event_schema`, and
`decision_kinds`.

---

## 5. Validation

Validation is the judgment `Σ ⊢ L ✓`: the lowered artifact `L`, with its
augmented schema `Σ`, produces **no error findings**. It is `Validator::new().validate(&L)`
(`src/validate.rs`, `src/validator.rs`). The validator holds no schema of its
own — the augmented schema travels on `L` — which is why, unlike Cedar's
`Validator::new(schema)`, Dogwood's takes none.

### 5.1 The two-channel error model

```
   parse(src, S) = Ok(𝓅)     lower(𝓅, S′) = Ok(L)
  ────────────────────────────────────────────────── (V-TwoChannel)
   L is a proof object; validate(L) yields only findings, never a fatal Error
```

*(`validate.rs`.)* A **fatal `Error`** — a parse failure, a macro-expansion
failure, a lowering failure, or an augmented-schema failure — aborts before a
`Lowered` exists, so the validator never sees it. The existence of `L` *is* the
proof that those four phases succeeded. Everything `validate` produces is a
**finding** (`ValidationError` / `ValidationWarning`); it never returns a fatal
error and never a syntax/lowering error. `Σ ⊢ L ✓` holds iff the error channel
is empty.

### 5.2 Order of checks

```
   validate_cedar_side(L, Σ) = (E₁, W₁)
   TemporalDialect.run(L.temporal, ctx) = (E₂, W₂)
   ProviderDialect.run(L.providers, ctx) = (E₃, W₃)
  ─────────────────────────────────────────────────────────── (V-Order)
   validate(L) = ValidationResult(E₁·E₂·E₃, W₁·W₂·W₃)
```

*(`validate.rs` `validate_impl`.)* Checks run in a fixed order — **Cedar side, then temporal,
then provider** — accumulating into two channels with no short-circuit across
checks. `ctx = (Σ = L.augmented_schema, event_schema = L.event_schema, dw_src)`.
`Σ ⊢ L ✓ ⟺ E₁·E₂·E₃ = []`.

### 5.3 The Cedar side

```
   L.policies = []                                  L.policies ≠ []
  ──────────────────── (V-Cedar-Empty)      ────────────────────────────────────────── (V-Cedar-Validate)
   Cedar side = ([], [])                     Cedar side = CedarValidator(Σ).validate(
                                                            L.policies, Strict)
```

*(`validate.rs` `validate_impl`.)* Cedar's own validator runs in **strict** mode over the
augmented schema. Its errors become `ValidationError::Cedar` findings and its
warnings pass through verbatim (**V-Cedar-Warnings**), except an impossible policy
(a condition false for every request its scope admits), which is an error, as
cedar-lean's validator reports it (**V-Cedar-Impossible**). The Cedar part of a
rule reads the request context only through attributes lowering does not hoist:
a read of the whole `context` (when the policy set has a temporal or provider
leaf, since lowering then adds the leaves' values to it), or of an attribute
named like a hoisted leaf (`<rule>__temporal_<n>`, `providers`), is an error
with the code `context` (**V-Cedar-ContextRead**). Crucially, this pass is
where several things are *deliberately delegated* rather than re-checked
elsewhere: **provider output/projection typing**, **provider field-path
arguments**, and **context typing under an unconstrained action scope**. Each
finding is located in `.dw`: prefer the Cedar diagnostic's own label span (the
lowered AST carries `.dw` locations), else fall back to the originating rule's
whole span via `rule_ids → rule_spans`, else a 1-byte span at the start
(**V-Cedar-Span**).

### 5.4 Temporal acceptance (well-formedness)

Before a temporal condition is ever validated against a schema, it must pass the
**acceptance** checker (`src/extension/temporal/check.rs`), run at parse time via
`check_condition(φ, ∅)`. This enforces MFOTL-style *safe-range monitorability* —
the conditions under which the condition denotes a finite, computable relation
over the event history. These are the rules most likely to reject a
plausible-looking policy, so they are given in full. All are **conservative**
("reject if unsure") and are **suspended** in the presence of a macro sigil
(re-checked post-expansion — **WF-Sigil-Punt**).

We write `x ∈ RR(φ)` for "`x` is range-restricted by a positive atom of `φ`",
where `RR` collects restrictors from: predicate fields `P{f: x}`, `tp(x)`, a
binding equality `(non-var, non-wildcard term) == x` or the mirror (`x == *`
restricts nothing — a wildcard resolves to no value; a compound arithmetic
side restricts only when it is wildcard-free, a wildcard atom making the
whole expression unresolvable), the bodies of
`formerly`/`previous`, and the **right** operand of `since` — descending through
`&&` and nested `exists` (dropping the inner binder's own fact). A negation
contributes **nothing, at any depth**: `RR` does not descend into `!ψ` —
the ¬-rule *discards* every restriction fact rather than flipping a
parity, so a doubly-negated atom is **not** a positive restrictor (evaluation
treats a negation as an opaque boolean filter whose rows carry no bindings).

**Existential range restriction.**

```
   x ∈ RR(φ)          Γ, x ⊢ φ ✓wf
  ──────────────────────────────────── (WF-Exists)
   Γ ⊢ exists (x : T). φ  ✓wf
```

*(`check.rs` `check_exists_safe`.)* An `exists`-bound variable must be range-restricted by a
positive atom **inside its body**. Otherwise: *"existential variable `x` is not
range-restricted by any positive atom in the `exists` body …"*. (Sigil slot or a
sigil anywhere in the body ⇒ accept, deferring to post-expansion.)

**Ordered conjunction (the demands rule).** Every conjunct is a conditional
restriction fact `demands(c) → RR(c)`: it *produces* the variables in `RR(c)`
and *consumes* the variables in `demands(c)` — bindings that must already be
in the environment when it evaluates. The standard formulation discharges such facts
order-independently; this evaluator binds left-to-right, so the chain must be
a valid discharge order. Flatten a `&&`-chain into `[c₁ … cₙ]` in source
order and walk left to right with an accumulator `ρ`:

```
   for each i:  demands(ci) ⊆ ρ          ρ ⇐ ρ ∪ RR(ci)
  ──────────────────────────────────────────────────────── (WF-Demands)
   c₁ && … && cₙ   ✓wf
```

*(`check.rs` `check_demands`/`check_chain`.)* The demanding conjuncts
(**WF-Demands-Classification**):

- a **pure filter** — an *ordering* comparison (`<`, `<=`, `>`, `>=`), an
  equality that binds nothing (`x == y` with both bare vars, both sides
  ground, or a `*` wildcard side — a wildcard is never a resolvable value),
  or a guarded negation `!ψ` (**WF-Neg-Guarded**) — demands all its free
  variables and produces none. A compound arithmetic operand contributes
  all its variables to the demand (a compound never binds — there is no
  algebraic solving, so `m + 1 == 5` binds nothing). Otherwise: *"variable
  `v` is used in a filter … that is not range-restricted by a preceding
  conjunct …"*.
- a **binding equality** `x == v` — `v` a ground term, an aggregate, or a
  wildcard-free compound expression, against a bare unbound `x` — produces
  `x` and demands the value side's *outward* free variables: for an
  aggregate, `fv(body) ∖ for-list` (a correlated aggregate is only per-`u`
  when `u` is already bound; with `u` unbound the count/sum silently
  de-correlates), and for a compound, every variable in it. Otherwise:
  *"the equality binding `n` reads `u` inside its aggregate operand …"*.
- a **`since`** produces `RR(anchor)` and demands `fv(left) ∖ RR(anchor)`
  (the standard `free(β) ⊆ free(γ)` side condition, relaxed to "or restricted
  earlier": the left is a per-step condition evaluated under the anchor's
  bindings and binds nothing itself). Otherwise: *"variable `u` is used in
  the left operand of a `since` …"*.

Demands propagate through non-chain wrappers (`formerly`/`previous` bodies,
an `exists` body minus its binder). Nested `&&` chains are checked
self-contained, **seeded with `ρ` at their position** (**WF-Demands-Seed**):
the evaluator threads every binding produced by preceding conjuncts into
nested structure, so an enclosing-chain restrictor genuinely discharges a
nested demand — and grouping with parentheses never changes acceptance. An
enclosing **binder** is still never a seed (a binder restricts nothing by
itself), and a shadowing binder removes its name from the inherited seed.
So `exists (a: Long). (a > 100 && P{f: a})` is **rejected** — the restrictor
`P{f: a}` must precede the filter — while
`exists (u). (P{f: u} && exists (n). ((count … u …) == n && n >= 2))` is
accepted: the nested chain inherits `u` from the enclosing one.

**Leaf closedness.** A temporal leaf must be **closed**: every variable bound by
an `exists` binder or an aggregation `for` list.

```
   fv(φ) = ∅
  ──────────────────── (WF-Closed)
   φ   ✓wf as a leaf
```

*(`check.rs` `check_leaf_closed`; run by `Temporal::parse` and again
post-expansion.)* A leaf is evaluated **boolean-ly** at the decision point with
no implicit existential closure, so a free variable's bindings would not thread
across conjuncts — the accepted formula would silently evaluate as an
always-false (or mis-correlated) guard. Violation: *"variable `x` is free in
this temporal condition …"*. Here `fv` is the standard free-variable set (an
aggregate binds its `for` list over its `where` body; `exists` binds its
binder; `tp(t)` outside any binder leaves `t` free). No sigil punt is needed:
an unresolved macro call contributes no visible variables, and macro hygiene
guarantees expansion can never capture a call-site variable (a `def temporal`
body has no plain identifier: it binds `$t` names, renamed at each call, and the
names the caller passes for its binder parameters), so a variable free at parse
time is necessarily still free after expansion.

**Monitoring scope must monitor (tp-dependence).** Every scope that establishes a
timepoint must actually vary with the current timepoint (`is_tp_dep`):

```
   ─────────────────────────── (WF-TpDep-Conjunct)   each top-level when/unless conjunct is tp-dependent
   ─────────────────────────── (WF-TpDep-Op-Body)    the body of formerly/previous is tp-dependent
   ─────────────────────────── (WF-TpDep-Since)       both sides of since are tp-dependent
   ─────────────────────────── (WF-TpDep-Exists-Body) the body of exists is tp-dependent
   ─────────────────────────── (WF-TpDep-Agg-Body)    the where-body of an aggregate is tp-dependent
```

*(`check.rs`, `temporal/validate.rs` `check_tp_dependence`.)* A `Predicate`, a `Tp`, or an `Agg` is
tp-dependent by construction; a `Var` is tp-dependent iff bound in the current
scope; literals, `context` fields, and wildcards are not. Each violated scope
emits a targeted message (e.g. *"this `when`/`unless` conjunct does not vary with
the current timepoint; it monitors nothing"*). Binder harvesting is asymmetric: a
variable bound only in a **negated** position or only inside an aggregation
`for`-domain does not bind for the surrounding scope (**TEMP-TpDep-BinderHarvest**).

**Aggregation binding.** For `sum v for (g₁:T₁) … (gₙ:Tₙ). where ψ` (and `count`,
which has no `v`):

```
   v ∈ {ḡ}       fv(ψ) ⊆ (Γ ∪ {ḡ})       ḡ ⊆ fv(ψ)       ∀g ∈ ḡ:  g ∈ RR(ψ)
  ─────────────────────────────────────────────────────────────────────────── (WF-Agg-Domain)
   sum v for ḡ. where ψ   ✓wf
```

*(`check.rs` `check_aggregation`.)* Four obligations, checked in order:

1. The summed variable must be one of this aggregation's own `for` binders
   (**WF-Agg-BoundVar-InDomain**): the sum is computed over the relation
   projected onto the `for` columns, so a summand outside it would silently
   sum to 0. Otherwise: *"aggregation sums `v`, which is not one of its `for`
   binders …"*.
2. Every free variable of the `where`-body must be bound by the `for`-list or
   an enclosing binder (**WF-Agg-Domain-Binds-FreeVars**). Otherwise:
   *"variable `u` is used in the aggregation body but is bound by neither …"*.
3. Every `for` variable must **occur** in the body (**WF-Agg-Domain-Occurs**;
   the standard safe-range rule presupposes `ḡ ⊆ fv(ψ)`): an unused group key would group
   over an unbounded domain. Otherwise: *"`for`-variable `g` does not occur in
   the aggregation body …"*.
4. Every `for` variable must be **range-restricted** by a positive atom of the
   body (**WF-Agg-Domain-RR**) — the aggregation analogue of WF-Exists, and
   what the monitorable fragment demands: the body must denote a *finite*
   relation over the `for` domain. Occurrence alone is not enough — a variable
   occurring only under a negation, or only in the **left** operand of a
   `since`, denotes an infinite relation (or one that does not range over the
   variable), and evaluation would silently degrade to a 0/1 witness count
   (a `sum` to 0). Otherwise: *"aggregation `for`-variable `g` is not
   range-restricted by any positive atom in the `where` body …"*.

**Aggregate value.** The rest of this section states *acceptance* obligations; the
paragraphs under this heading state **semantics** instead. Nothing here can make a
condition ill-formed, so §7's meta-properties about what passes this section are
unaffected. They sit with the other aggregation rules because that is where a reader
looks for what `sum` means.
*(`src/interpreter/eval.rs` `eval_agg_expr`, `sum_column`.)*

`count` yields the number of rows in the projected relation. `sum` yields the total of
its summand column over that relation, **skipping** any row whose summand is not a
`Long` — which is observable, because `count` over the same relation still counts that
row. Validation rejects the common ways a summand could be non-`Long` — chiefly a
declared type that disagrees with whatever range-restricts it — but it does not rule
the case out: a comparison is only checked where both sides have a type, and an
optional attribute can be declared `Long` and still be absent. The skip is therefore
observable in a validated policy, not only in an unvalidated one. Both aggregates are
`Long`.

Because an aggregate ranges over a *set*, its value does not depend on the order rows
are visited, and it is exact for every total that a `Long` can hold — including totals
reached by way of partial sums that a `Long` cannot hold.

An aggregate value that is **not** representable as a `Long` is
**implementation-defined**. The language does not say what such an aggregate compares
as: a conforming implementation may clamp it to the `Long` range, evaluate the
comparison at a wider precision, report an error, or otherwise yield an unspecified
value. A policy whose verdict depends on which of those an implementation chose is not
portable, and two implementations may disagree on it without either being wrong, so
such a policy is not a sound basis for comparing them.

Which policies those are depends on how the aggregate is used. Taking clamping and
wider precision as the two readings — an erroring implementation differs from both for
*every* comparison, interior thresholds included, so it is not covered by what follows:

- Compared **directly**, only a comparison against an *endpoint* of the `Long` range
  can distinguish the two; a threshold strictly inside the range cannot, whichever way
  the total left it. At the maximum, `==`, `!=`, `>` and `<=` distinguish them while
  `>=` and `<` do not; at the minimum, `==`, `!=`, `<` and `>=` distinguish them while
  `<=` and `>` do not.
- **Bound to a variable**, as `exists (n: Long). ((A) == n && B)` does, the reach is wider. An out-of-range total has *no* `Long` witness at all
  unless the implementation clamps, so a widening implementation empties the
  existential outright. The two readings then differ exactly when `B` holds of the
  clamped endpoint: they agree when it does not, so `B` = `n > <maximum>` agrees
  (no `Long` exceeds the maximum) while most other `B` do not. Note also that emptying
  the existential is not uniformly restrictive — under `forbid` it stops the rule
  firing, so the divergence surfaces as a permit.

If a policy must not depend on any of this, keep window totals inside the `Long` range
— which for the aggregate to be meaningful is normally already true.

**Aggregate and arithmetic position.** An aggregate may appear **only** in
comparison-operand position — as a direct operand, or as a leaf of a compound
arithmetic operand; an arithmetic expression is likewise
comparison-operand-only:

```
  ─────────────────────────────────────────────────────── (WF-Agg-Operand)
   an Agg is well-placed iff it is a direct operand of a Comparison or a
   leaf of an Arith in that position;
   an Agg as a predicate-arg value, an array element, or otherwise nested ⟹ reject

  ─────────────────────────────────────────────────────── (WF-Arith-Operand)
   an Arith is well-placed iff it is a direct operand of a Comparison or
   nested in another well-placed Arith;
   an Arith as a predicate-arg value or an array element ⟹ reject
```

*(`check.rs` `check_operand` / `reject_nested_agg`.)* Violations: *"an aggregate
(`sum`/`count`) may appear only as the immediate operand of a comparison …"* /
*"arithmetic (`+`/`-`/`*`) may appear only as the immediate operand of a
comparison …"*. (The grammar already rejects the bare arithmetic form in those
positions — they take a `term`, not an `arith` — so only the parenthesized
grouping form reaches WF-Arith-Operand.) This makes the aggregate-binding
idiom `exists (n: T). ((A) == n && B)` well-formed: `(A) == n` binds `n`
(restrictor), then `B`'s use of `n` is an already-restricted filter.

**Experimental gate.** Compound (`Arith`) operands are gated behind the
off-by-default Cargo feature `experimental-arithmetic`. A build without the
feature rejects, after the checks above, any condition containing an `Arith`
(*"arithmetic in comparison operands is not yet supported"*); a build with
the feature accepts it, and validation warns that arithmetic operators are
experimental and may change in a future release. The arithmetic rules in
this specification describe builds with the feature on.

**Arithmetic out-of-range results.** A compound operand evaluates over `Long`.
A result outside the `Long` range is **implementation-defined** exactly as an
out-of-range aggregate total is (above): clamp, wider precision, or an error
are all conforming. This implementation clamps (saturates) **per operation,
in tree order**, which is observable against wider-precision evaluation away
from a single endpoint: `0 + MAX + 5 - 10` is `MAX − 10` under per-operation
clamping but `MAX − 5` at wider precision. A policy whose verdict depends on
that difference is not portable; keep intermediate results inside the `Long`
range (for cross-multiplied ratio guards, both products).

### 5.5 Temporal dialect validation (against the schema)

Given an accepted condition, the temporal *dialect* checks it against the derived
event schema and the augmented Cedar schema, per leaf, in order: **event-schema
names → entity types → context paths → tp-dependence → types**
(`temporal/validate.rs`, **TEMP-Order**). Authority is divided: **event/field
name resolution is owned solely by the event-schema checker** ([§5.7](#57-event-schema-name-resolution));
the dialect additionally checks:

- **Entity types** — every `Entity(ty, id)` term must name a declared entity
  type, and an action ref (`…::Action::"X"`) a declared action (Cedar reserves
  `Action`); an enum entity's id must be a permitted eid (**TEMP-EntityType-***).
  A `decimal("…")` literal must be a decimal Cedar accepts (**TEMP-Decimal**). A
  wildcard is not a comparison operand: it resolves to no value, so the
  comparison would always be false (**TEMP-Wildcard**).
- **Context paths** — a `context.<path>` must resolve against the scoped
  action's **full** declared context record (Cedar's `context` variable —
  `context.input.<field>…`, `context.system.<field>…`, etc.), on **every**
  action the leaf's scope resolves to (an unconstrained scope to every action);
  an attribute lowering hoists is not part of the request, and does not resolve
  (**TEMP-ContextPath-***). A `principal` / `resource` **scope** term is
  separate (Cedar's request scope entities, not a context field): the bare root
  types to the environment's principal / resource entity type, and an
  attribute tail (`principal.dept`, `principal.id`) to the type that entity
  type declares.
- **Types** — once per request environment of the rule (an action its scope
  resolves to, and a principal and a resource type the scope admits for it),
  from the variable types **of every binder's declared annotation** (`exists
  (x: T)` and each aggregation `for (v: T)`; the declared type is
  **authoritative**, not reverse-inferred from a use site). A binder's type is
  `Long`, `String`, `Bool`, `decimal`, `Timepoint`, or a declared entity type
  written with its namespace; the body of a binder of another type is not typed
  further (**TEMP-Binder-Type**). Types compare exactly: an entity type by its
  qualified name, and a record by its attributes. A
  predicate arg must match its declared field
  type: the type the predicate action's context declares for a spliced
  `input` / `output` field, and the type the event schema declares for any
  other (`callerPrincipal`, `requestId`); a use of a bound variable must be
  consistent with its declared type; an ordering comparison requires both
  operands **numeric** (only `int` is numeric — an aggregate and a compound
  arithmetic operand type as `int`, decimal is **not** numeric here); an
  equality requires equal types, or two entities when it does not have the
  shape of one that can bind a variable (a bare variable against a term that
  is not a variable and holds no wildcard, under `==` or `!=`): evaluation
  does not consult a binder's declared type, so an equality of this shape that
  binds the variable could give it a value outside its type;
  every atom
  of a compound arithmetic operand must type `int` — decimal, string, bool,
  entity, array, and wildcard atoms are rejected, the wildcard by name
  since it would make the guard silently false (**TEMP-Arith-Long**); and a
  `tp(x)` binder must be declared `Timepoint` — any other declaration conflates a timepoint index with a
  data value, making the condition permanently false (a validated dead
  guard). A check fires only when both types are known (**TEMP-Type-***).
  Temporal conditions do not support Cedar's extension types other than
  `decimal`: a binder declared `datetime`, `duration`, or `ipaddr` is rejected,
  and so is a request-side path whose type is or holds one, as a comparison
  operand (which is then not typed further), an atom of a compound operand, a
  predicate argument, or a pin's request-side path, as in the formal
  specification's typing (`CedarType.temporalSupported`). A predicate that
  leaves such a field out, or matches it with a wildcard, is valid
  (**TEMP-Type-Extension**).
- **Max window** — every `within` window in the leaf (on a `formerly`,
  `previous`, or `since`, at any depth including inside an aggregation `where`
  body) must be **≤** the event schema's `max_window` cap, compared in seconds.
  A window strictly greater than the cap is rejected, located at the offending
  operator (**TEMP-MaxWindow**). The cap is the schema's `max_window` directive
  or its default ([§2.6](#26-event-schema-dsl)); post-expansion every
  window is concrete, so macro-supplied windows are checked too.
- **Max horizon** — the leaf's horizon, in seconds — `formerly`/`previous`
  within `w` add `w` to their body's, `since` within `w` adds `w` to the larger
  of its sides', conjunction, negation, `exists` and comparison take the
  largest of their parts' (an aggregate operand its body's), and a predicate or
  `tp` looks back nothing, with a non-positive window counting as zero — must
  be **≤** the event schema's `max_horizon` cap, when it declares one. The sum
  is exact. A leaf
  whose horizon is strictly greater is rejected, located at the leaf
  (**TEMP-MaxHorizon**; Lean: `Formula.horizon`, `PolicySet.Valid.horizon`).

The type environment is **lexically scoped** (`walk_typed`): a binder's declared
type holds over its own body only, an `exists` over its body and an
aggregation's `for` list over its `where` body. So a name an aggregation rebinds
has its enclosing type again outside the aggregation (**TEMP-Type-Scope**).

Four further rules come from the formal specification's typing relation
(`dogwood-lean`, `Formula.WellTyped`; `temporal/validity.rs`). Each is checked in
every request environment the rule's scope admits: every action the scope
resolves to, and every principal and resource type the scope admits for it.

- **Optional attributes** — a `context.<path>`, `principal.<path>`, or
  `resource.<path>` term reads an optional attribute only where the Cedar part
  of the rule tests it with `has` at the leaf's position (**TEMP-Optional**),
  as in `context.input has amount && temporal { … }`. The facts a position
  establishes are read off the lowered rule (`temporal/facts.rs`): a `has` test
  on an attribute chain rooted at `context`, `principal`, or `resource`
  establishes its path; a conjunction establishes the facts of both operands;
  facts flow from the left operand of `&&` to its right, from the condition of
  `if` to its `then` branch, and from a `when` clause to the clauses after it.
  `principal.id` and `principal.type` are attributes like any other, as in
  Cedar: an optional one needs a guard.
- **Pins** — every pin of an event a predicate names correlates its field with
  a request-side path that is **declared and required** in every environment
  of the rule, of a type the field can hold (**TEMP-Pin**). So a conforming
  request always has the pin's value. A `has` test does not guard a pin: pin
  injection conjoins it onto every predicate of the event.
- **`for` variables** — the `for` variables of one aggregation have distinct
  names (**TEMP-For-Distinct**).
- **Binding fields** — a variable bound by a field the event schema names,
  `P{ callerPrincipal: x }`, has a type every value of the field has
  (**TEMP-Binding-Field**). A field of `principalType(A)` holds an entity of any
  of `A`'s principal types, so `x` must accept every one of them.

### 5.6 Provider dialect

For each hoisted provider leaf (`provider/validate.rs`):

```
   field.declaration = Some(decl)     |decl.argument_types| = |invocation.args|     ∀ (arg,param): accepts(param, arg)
  ────────────────────────────────────────────────────────────────────────────────────────────────────────────────── (PROV-Ok)
   provider leaf ✓
```

An **undeclared** provider is caught only here (lowering defaulted its output
type permissively) — *"provider `k` is not present in the provider
declarations"* (**PROV-DeclaredProvider**). Argument **count** must match
(**PROV-ArgCount**); a directly-typed literal/set argument must match the
declared `paramType` (`string`/`integer`|`long`/`bool`|`boolean`/`decimal`/`set`
— **PROV-ArgType**); a field-path argument (`context`/`principal`/`resource`),
and every element of a set argument, has the declared Cedar type exactly in
every request environment of the rule; an optional attribute along a path needs
no `has` test, since an absent argument reaches the script as null; a bare
`principal` / `resource` is an entity, and the whole `context` is not an argument
(**PROV-ArgPath**). Each **output method** in a chain is likewise checked here
(**PROV-Method-***): it must be declared in `availableMethods`, must not shadow a
Cedar extension-method name, must be given the declared argument count/types,
and — when it declares an `inputType` — must be fed a value of that Cedar type by
the preceding pipeline stage (the running type starts at the invocation's
`outputType` and advances by each method's `outputType`). Provider
**output/projection** typing is not checked here — it was lowered to native Cedar
and is checked by the Cedar side ([§5.3](#53-the-cedar-side), **PROV-Output-Deferred**).

### 5.7 Event-schema name resolution

The authority on predicate names (`event_schema/validate.rs`), applied to every
`Predicate` reachable in the (post-expansion) condition tree:

```
   schema.get(P.ns, P.action, P.kind) = Some(ev)     ∀ arg ∈ P.args:  ev.lookup(arg.path) = Leaf
  ─────────────────────────────────────────────────────────────────────────────────────────────── (EVENT-Predicate)
   Predicate P  ✓names
```

*(`event_schema/validate.rs` `validate_condition`.)* A predicate must name a **declared** derived
event (**EVENT-Predicate-DeclaredEvent**: else *"predicate `…` does not name a
declared event …"*), and every **mentioned** field path must resolve to a
declared **leaf** (**EVENT-Field-Leaf**). *Omitting* a field is legal (omission =
wildcard); only a mentioned name is checked. A mentioned path resolving to a
field **group** rather than a leaf (**EVENT-Field-Group**), or to nothing
(**EVENT-Field-Absent**), is an error.

---

## 6. Authorization

Authorization is **stateful** and event-driven. The judgment is

```
   ⟨H, e⟩ ⇓ ⟨H′, r⟩            r ∈ { None, Rejected } ∪ { Some(ρ) : ρ a Response }
```

where `H` is the temporal engine's observed history and `H′` is `H · e` when `e`
conforms to the event schema, and `H` when it does not ([§6.1](#61-check-observe-then-gate-on-decision-kind)).
A `Response ρ = (decision ∈ {Allow, Deny}, reason: DogwoodRuleRef*,
errors: String*)`. This is `Authorizer::submit` (`authorize/mod.rs`, `api.rs`);
`Authorizer::is_authorized` reports `Rejected` as `None`. The `None` result —
"this event decided nothing" — is the essential difference from Cedar.

An event `e` records a **single occurrence at one point in time**, carrying an
action, event kind, fields, and timestamp. Under the default event schema, a
`request` records an attempt to run an action, and its eventual `response` or
`error` is a separate event recording the operation's result. The authorization
verdict `ρ` is not itself recorded as an event. A `response`-kind event is
therefore distinct from the authorization `Response ρ`.

`H` is ordered by ingestion: its positions follow the order in which events
are passed to the authorizer. This can differ from their creation order or
their arrival order at an enforcement point. Trace positions determine the
ordering used by the temporal operators, and `tp(t)` binds a position index.
Timestamps determine membership in `within` windows. Evaluation at position
`i` reads only positions `j <= i`, including the current event.

Event timestamps are assumed to be **increasing** along `H`:
`ts(i + 1) > ts(i)`, so timestamps are also unique. The reference interpreter
neither sorts events nor checks this assumption. Other authorizer implementations
can assign strictly increasing timestamps at ingestion, as the formal
specification's authorizer does. An authorizer that keeps one log per partition key assigns
them per key, so they increase within each key's log; the formal specification's
partitioned evaluation evaluates a decision over its own key's log
(see **Sharding by key, and stamps** in §4.5). Traces with repeated or decreasing
timestamps are outside the specified semantics. See
[Evaluation semantics](04-temporal-expressions.md#evaluation-semantics).

### 6.1 Check, observe, then gate on decision kind

An event is checked against the event schema first; a conforming event is
observed; then its kind decides whether a verdict is produced.

```
   e ⊨ S        H′ = H · e        e.kind ∉ decision_kinds
  ──────────────────────────────────────────────────────── (A-Ingest-History)
   ⟨H, e⟩ ⇓ ⟨H′, None⟩
```
```
   e ⊭ S        e.kind ∉ decision_kinds
  ──────────────────────────────────────────────── (A-Reject-History)
   ⟨H, e⟩ ⇓ ⟨H, Rejected(nonconforming)⟩
```
```
   e ⊨ S        H′ = H · e        e.kind ∈ decision_kinds        ⟨H′, e⟩ ⇓_d ρ
  ──────────────────────────────────────────────────────────────────────────── (A-Ingest-Decide)
   ⟨H, e⟩ ⇓ ⟨H′, Some(ρ)⟩
```
```
   e ⊭ S        e.kind ∈ decision_kinds        ⟨H, e⟩ ⇓_d ρ
  ─────────────────────────────────────────────────────────── (A-Decide-Nonconforming)
   ⟨H, e⟩ ⇓ ⟨H, Some(ρ)⟩
```

*(`api.rs`, `ingest`; `conformance.rs`, `RuntimeChecks`, `check_pins`.)* `e ⊨ S` is **event conformance**
(**A-Event-Conforms**): the event schema declares a signature for the event's
action and kind, and the event's logged record is an instance of it — every
logged declared field has its declared type, every required field and every
pinned field is logged, and every logged field that mirrors the request holds
the request's value (the field of each symmetric pin, and `callerPrincipal`
and `callerResource` when no pin names them). The pin clauses follow the
authorizer's mirror rule (`MirrorRule`; `conformance.rs`, `check_pins`): under
the default, **strict**, rule a mirrored field is also absent when the event
has no request-side value for it; `Current` drops that case; `Unchecked` checks no pin clause. A field spliced from the action's `context.input` /
`context.output` has the type the context declares at its path, and is required
when every attribute along the path is; any other declared field has the type
the event schema names, and is optional. A `Null` value is absent.
`LoweredPolicySet::check_event_conformance(e, rule)` decides `e ⊨ S` under a
mirror rule without ingesting `e`, through the same function `ingest` calls.

A nonconforming event is **not ingested**: the temporal engine never observes
it, so no later decision sees it. A nonconforming history event is
**rejected** (**A-Reject-History**), which `Authorizer::submit` reports as
`Err(Rejection::Nonconforming)` and `Authorizer::is_authorized` as `None`; a
rejection is not a decision, in particular not a `Deny`. A nonconforming
decision event fails its decision closed ([§6.2](#62-the-decision-pipeline-fail-closed)).
A conforming event is observed (`try_observe`; an event the engine could not
record is not in the history: a history event is rejected as
`Rejection::Unavailable`, a decision event fails closed) for *both* decision
and history-only kinds, so
at a later decision point the temporal leaves see the full prefix history of
conforming events, interleaved history-only events included
(**A-Stateful-Invariant**). `⇓_d` is the decision judgment of
[§6.2](#62-the-decision-pipeline-fail-closed). A stateless single decision is a
fresh authorizer fed one decision-kind event. The authorizer preserves supplied
timestamps; it does not check their order.

### 6.2 The decision pipeline (fail-closed)

`⇓_d` makes its checks in the order of the formal specification's
`PolicySet.decideWith` (`dogwood-lean`, `Dogwood.Spec.Decision`), each a
**fail-closed** short-circuit, then decides. A fail-closed `Response` is always
`(Deny, reason = [], errors = [msg])`.

| # | Check | Fails closed with |
|---|---|---|
| 1 | the event has a principal and a resource in scope, with well-formed uids | `decision event has no principal in scope` (or resource), or the uid's parse error (**FailClosed-Scope**) |
| 2 | the event conforms to the event schema (`e ⊨ S`) | `nonconforming decision event: …` (**FailClosed-Event**) |
| 3 | the request conforms to the action schema: its action is declared, its principal and resource are of types the action applies to, and its context is an instance of the action's context record type, without the hoisted attributes (no undeclared attribute; every required attribute present) | `nonconforming request: …` (**FailClosed-Request**) |
| 4 | the entity store conforms to the augmented schema (Cedar's `Entities::from_entities`) | `entity conformance: …` (**FailClosed-Entities**) |
| 5 | every information provider of the policy set produces a value | the provider's error (**FailClosed-Provider**) |
| 6 | every provider output is a value of its declared output type | `nonconforming provider output: …` (**FailClosed-ProviderOutput**) |
| 7 | the temporal engine values the leaves: it does not fail, and it returns a value for exactly the hoisted leaves | `temporal evaluation: …` (**FailClosed-Temporal**) |

```
   checks 1–7 pass        β, providers, e ⊢ ctx ⇓ Ok(κ)        Request::new(p, a, r, κ) = Ok(q)
  ─────────────────────────────────────────────────────────────────────────────────────────────── (A-Decide-Ok)
   ⟨H, e⟩ ⇓_d decide(q)
```

*(`api.rs`, `ingest` and `decide_at`; `conformance.rs`.)* The Cedar request is
built without a schema, because the decision supplies every hoisted attribute to
every action's context (§6.3); check 3 is where the request is validated
instead. Check 7 matters because Cedar would report an absent `context.<id>` as
an error of the policy that reads it, and skip that policy: a `forbid` whose leaf
is missing would stop applying. **Scope of check 5:** for provider-originated
errors the language-level semantics is *undefined behavior* — an erroring
provider carries no cross-implementation guarantee, and a policy set must not
rely on deny-on-error (see [the provider
contract](05-information-providers.md#the-provider-contract)); the formal
specification fixes this reference implementation's choice, the denial. The
other checks are not so scoped: data that does not conform to the schemas must
fail closed in every implementation.

### 6.3 Context assembly

The Cedar context `κ` is an ordered record with three groups of keys
(`api.rs`, `build_context`, **A-Context-Keys**):

1. every group of the event's request context (`input`, `system`, …), verbatim;
   a `Null` group or record member is absent (**A-Context-Groups**). Check 3 of
   §6.2 has already checked them against the action's context record type.
2. for each `(id, b) ∈ β`: `id → Bool(b)` — the hoisted **temporal** booleans, at
   top level, i.e. `context.<id>`.
3. if any provider leaves exist: `providers → { id → v }` for **every**
   provider invocation in the policy set (**A-Context-Providers**) — i.e.
   `context.providers.<id>`, unconditional. There is no applicability
   filter of any kind: provider execution is not gated by the rule's
   action clause, scope constraints, or conditions (see [the provider
   contract](05-information-providers.md#the-provider-contract)).

Value mapping (`value_to_expr`, **A-Context-ValueMap**) is the obvious one. A
`Null` record member, set element or context group is **absent** and left out
(`Null` stands for an absent value). A record that is Cedar's JSON escape for an
extension value, `{"__extn": {"fn": F, "arg": A}}` (what `Value::extension`
builds and a trace writes `datetime("…")`), becomes that extension value: `ip`,
`datetime`, `duration`, or `decimal` (**A-Context-Extension**). Two lossy cases
remain: a `Null` outside a record and a record-construction failure both
collapse to the **empty string** literal, and an entity *value inside the
context* uses a **sentinel** (`Drupe::Gateway::"unknown"`) on a malformed UID.
Check 3 of §6.2 rejects every context in which a lossy case could arise, so they
never reach a decision (**A-Context-EntityValue-Sentinel**).

### 6.4 Provider evaluation

Each provider's value is computed **resolver-first, Rhai-fallback**
(`api.rs`, `eval_provider`):

```
   resolver present     resolver.resolve(name, args) = Some(res)
  ──────────────────────────────────────────────────────────────── (A-Provider-Resolver)
   eval_provider = res        (res = Ok(v) ⇒ v ; res = Err(m) ⇒ FailClosed-Provider)
```
```
   resolver absent ∨ resolver declines (None)     field.declaration = Some(decl)
  ─────────────────────────────────────────────────────────────────────────────── (A-Provider-Rhai)
   eval_provider = evaluate(invocation, decl, args)
```

A caller-supplied `ProviderResolver` gets first refusal on every invocation; if
it declines, the declared sandboxed Rhai implementation runs. An invocation with
no declaration and no resolver value is an error (⇒ **FailClosed-Provider**):
*"provider `k` was not declared … so it has no implementation to evaluate"*.
Arguments are resolved against the event: a `context.<path>` argument reads the
event's request context at that path (falling back to a bare last-segment
lookup, then `Null`); a `principal` / `resource` argument reads the request's
scope entity, with its attributes (`id` and `type` included, as in Cedar) read
off the supplied entity data; literals and sets map directly
(**A-Provider-ArgResolve**).
The value is then converted to its declared type (an enum id becomes an
entity), and checked against it: a value outside a declared enum is a provider
error, and any other value that is not of the declared type, such as a record
with an undeclared attribute, fails closed (⇒ **FailClosed-ProviderOutput**).
A provider without a declared output type has no conforming output.

### 6.5 The decision core

Once context and request are built, the decision is delegated to the pluggable
`PolicyEngine` (default: local Cedar; alternatively, a remote Cedar-based engine) over the entity store
`E` assembled by `build_entities`: the schema's **action-hierarchy entities** (so
`action in [Group]` membership resolves), any **caller-supplied attributed
entities** from the event's entity store — attributes and direct `memberOf`
parents, validated against the augmented schema — and the request's **scope
entities**, made present bare when the event supplies no data for them. The
schema's action entities take precedence: supplied data for a declared action's
uid is dropped, so it cannot change the action hierarchy (**A-Entities-Actions**).
Cross-event state lives in the temporal history; per-event entity data flows
through `E`:

```
   policy.is_authorized(q, E) = (d, ids, errs)
   reason = [ DogwoodRuleRef(k, id) : id ∈ ids,  rule_ids[k] = id ]
  ──────────────────────────────────────────────────────────────────── (A-Decide-Core)
   decide(q) = (d, reason, errs)
```

*(`api.rs`, `decide`.)* The engine returns a decision, the **determining policy ids**,
and any errors. Each determining id is mapped **back** to its Dogwood rule by
`rule_ids` (rule `k`'s PolicyID); an id not found there is dropped
(**A-Decide-RuleMap**). An implicit `Deny` (no rule matched) has empty `reason`,
exactly as Cedar's does — which means a fail-closed `Deny` and an implicit `Deny`
are indistinguishable in the `reason` channel and differ only in `errors`.

### 6.6 The event-log contract and retries

The crate's `Authorizer` is one instance that ingests events in the order they
are passed to it. An implementation may run several instances, or retry a step
after a conflict, and must still decide as if one instance had built one log.
The formal specification states what every run of an implementation must
guarantee, the **event-log contract** (`dogwood-lean`, `Dogwood.Spec.Contract`,
`Run.Meets`); it is what implementations are measured against. Its log `L`
holds the accepted submissions in one order, each with the entry it became: an
event stamped with its timestamp, or a deployment. A submission `s` carries an
arrival (an event and the clock reading it arrived with, or a deployment) and,
optionally, an **event id** `id(s)` its client chose. A reply `ρ` is
`Accepted(i, o)`, the position `i` in the log and the outcome `o` there, or
`Rejected(why)`, `why ∈ { nonconforming, unavailable, duplicate }`.

The **retry key** of a submission of an event `e` with an event id is
`key(s) = (pkey(e), id(s), action(e), kind(e))`, where `pkey(e)` is the
partition key, the logged values of the universal symmetric pins
(`EventSchema.partitionKey`). A deployment, and an event submitted without an
event id, has no retry key. `s` is a **retry** of the entry `x` under the
retry window `W` (`Submission.RetryOf`) when

```
   retry_W(s, x)  ⟺  key(s) = key(x)  ∧  event(s) = event(x)  ∧  clock(s) ≤ stamp(x) + W
```

`event(s) = event(x)` is identical content: the same action and kind, the same
logged record, and the same request (principal, resource, context, and entity
data), compared as values. The default window is five minutes, in the clock's
ticks (`defaultRetryWindow`). A single instance that receives the submissions in
arrival order (`Sequential.step`) takes these steps, where `decide(L, i)` is the
outcome at position `i` of the log (`Log.decide`), and `keys(L)` the retry keys
of its entries:

```
   L[i] = x        key(s) = key(x)        retry_W(s, x)
  ──────────────────────────────────────────────────────── (C-Retry)
   ⟨L, s⟩ ⇓_W ⟨L, Accepted(i, decide(L, i))⟩
```
```
   L[i] = x        key(s) = key(x)        ¬ retry_W(s, x)
  ──────────────────────────────────────────────────────── (C-Duplicate)
   ⟨L, s⟩ ⇓_W ⟨L, Rejected(duplicate)⟩
```
```
   key(s) ∉ keys(L)        s ⊨ S        y = stamp(s, L)
  ──────────────────────────────────────────────────────────── (C-New)
   ⟨L, s⟩ ⇓_W ⟨L · y, Accepted(|L|, decide(L · y, |L|))⟩
```
```
   key(s) ∉ keys(L)        s ⊭ S
  ────────────────────────────────────────── (C-Nonconforming)
   ⟨L, s⟩ ⇓_W ⟨L, Rejected(nonconforming)⟩
```

`key(s) ∉ keys(L)` holds of every submission without a retry key. `s ⊨ S` is
event conformance (**A-Event-Conforms**), and a deployment always conforms.
`stamp(s, L)` is the entry `s` becomes: its event stamped `max(reading, last + 1)`
after the last stamp of `L`, or its deployment. C-Retry and C-Duplicate leave
the log unchanged, so no two entries of a log share a retry key. C-New and
C-Nonconforming are ingestion (`Log.submit`). A single instance meets the
contract for every `W` (`sequential_meets`).

A run of any number of instances **meets the contract** (`Run.Meets`) when:
every submission is accepted at exactly one position and told it, or is a
retry of an entry, absent from the log, and told that entry's position, or is
rejected, absent from the log, and told why; the entries an instance had
observed when it answered are a prefix of the log that contains the position;
each outcome is `decide` at its position over that prefix, for a retry as for
an accepted submission; no two entries share a retry key; each logged event is
its submission's, stamped at or after its reading and after the event before
it; every logged event conforms; and a rejection as nonconforming or as a
duplicate is truthful. An implementation may reject any submission as
unavailable: availability is not required.

What follows (`Dogwood.Thm.Contract`):

- a retry is not ingested again (`Run.Meets.retry_not_logged`), and leaves a
  single instance's log as it was (`sequential_retry_log`);
- the answer to a retry is its original's, or an unavailability
  (`Run.Meets.retry_reply`, `sequential_retry_reply`). A decision depends only
  on the log up to its position (`decide_append`), so the answer is the
  original's even when a deployment came between the two;
- a submission with the key of an entry that is not a retry of it is rejected
  (`Run.Meets.duplicate_rejected`);
- when no two submissions share a retry key, the contract is the contract
  without retries, in which every resubmission is a new submission, whatever
  `W`, `W = 0` included (`Run.meets_iff_withoutRetries`).

The crate's `Authorizer` has no event ids: each submission is new, so only
C-New and C-Nonconforming apply, as **A-Ingest-History**, **A-Ingest-Decide**,
and **A-Reject-History** of [§6.1](#61-check-observe-then-gate-on-decision-kind),
with the difference that a nonconforming decision event fails its decision
closed (**A-Decide-Nonconforming**) instead of being rejected.

---

## 7. Meta-properties

These follow from the rules above; they are the properties a caller may rely on.

- **Fail-closed.** No evaluation failure produces `Allow`. Every error path in
  `⇓_d` yields `(Deny, [], errors)` (FailClosed-*), and the context is never
  partial when the policy engine runs — an incomplete context denies. Neither
  does data that does not conform to the schemas: a nonconforming decision
  event, request, entity store, or provider output denies, and a nonconforming
  event never enters the history. *(§6.1, §6.2.)*
- **Lowering totality of the syntactic map.** Every non-extension surface form
  has exactly one translation ([§4.3](#43-expression-translation)); the only
  non-structural step is hoisting, which is deterministic given the rule key and
  ordinal. *(§4.4.)*
- **Validation soundness of the proof object.** `validate` presupposes a
  `Lowered`; parse/macro/lower/schema failures are a separate fatal channel and
  can never appear as findings. `Σ ⊢ L ✓` concerns type/dialect findings only.
  *(§5.1.)*
- **Determinism of identity.** A rule's PolicyID and its hoisted field names are
  a pure function of the rule key `key(δ, i)` and the per-rule ordinal — so two
  lowerings with distinct distinguishers never collide, and the same input with
  the same distincter is byte-identical. *(§4.1, §4.4.)*
- **Idempotent retries.** Under the event-log contract, a resubmission of an
  accepted event with its event id, the same content, on the same partition
  key, within the retry window, is not ingested again and gets the answer the
  first submission got; any other reuse of an event id is rejected, and is not
  decided. *(§6.6.)*
- **Statefulness is confined to the temporal engine.** The policy engine is
  invoked per-request over the decision's own entity store; all history-dependence flows
  through `observe`/`evaluate` and the hoisted `context.<id>` booleans. History-only
  events matter precisely because they mutate that state, and so only conforming
  ones are observed. *(§6.1, §6.5.)*
- **Acceptance ⇒ monitorability.** A temporal condition that passes [§5.4](#54-temporal-acceptance-well-formedness)
  denotes a finite, computable relation over the history (safe-range): the
  leaf is closed (every variable `exists`- or `for`-bound), every bound
  variable — existential *and* aggregation `for` — is range-restricted by a
  positive atom (a negation restricts nothing, at any depth; a `since`
  restricts only through its anchor), filters follow their restrictors, and
  every monitoring scope varies with the timepoint.
