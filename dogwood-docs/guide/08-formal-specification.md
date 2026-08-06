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

- core policy — `src/parser/grammar.pest`
- temporal — `src/extension/temporal/grammar.pest`
- event schema — `src/event_schema/grammar.pest`

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
text between a marker's braces, with balanced inner braces honored — it is
dispatched to a sub-language parser.

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
be mixed (`!-x` is rejected), matching Cedar. `/` and `%` parse but are rejected
downstream (Cedar has no division). Surface operators `!=`, `>`, `>=` are
retained here and desugared during lowering ([§4.3](#43-expression-translation)).

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

comparison  ::= term cmp_op term
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

term        ::= entity | decimal_lit | paren_agg | agg_expr | integer
              | string | "true" | "false" | array | context_field
              | scope_field | wildcard | param_ref | binder_ref | ident
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
inside a macro body; the well-formedness pass rejects them elsewhere.

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
schema      ::= [ max_window ] { event_decl }
max_window  ::= "max_window" "=" interval
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
policy's temporal `within` window may look; it must precede the event
declarations, appear at most once, and be a positive interval (a zero window is
a parse error). Absent, derivation supplies a **24h** default. The cap is
enforced by the temporal dialect ([§5.5](#55-temporal-dialect-validation-against-the-schema),
**TEMP-MaxWindow**).

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
                  | Agg a | ParamRef name | BinderRef name              (* last two transient *)
a  (AggExpr)    ::= Sum(x, (x:T)*, φ) | Count((x:T)*, φ) | Call c
⋈  (CmpOp)      ::= ≤ | < | ≥ | > | =
W  (WithinSpec) ::= Concrete(n, unit) | ParamRef name                  (* ParamRef transient *)
T  (Type)       ::= Timepoint | Named(name*)
```

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
   Γ ⊢ c ⇝ γ_c ⊣ Γ₁       Γ₁ ⊢ rest ⇝ γ_r ⊣ Γ₂       rest ≠ []
  ──────────────────────────────────────────────────────────────── (L-Fold-Cons)
   Γ ⊢ (c :: rest) ⇝ (γ_c && γ_r) ⊣ Γ₂
```

*(`cedarify/mod.rs` `emit_policy`.)* Clauses fold **left-associatively in source
order**: `[c₁, c₂, c₃]` becomes `And(And(γ₁, γ₂), γ₃)`. A bare rule (no clauses)
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
**every** action's context by schema augmentation, and evaluated for every
decision event (execution is unconditional — see the provider contract in
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
   `Bool` attribute `context.<name>` on its action(s); for provider leaves, a
   `providers` record grouping the fields, typed from the declarations. The
   augmentation **merges** into an existing `providers` record rather than
   replacing it, so feeding an augmented schema forward (incremental lowering)
   preserves earlier providers (`cedarify/schema_augment.rs`).

Finally the temporal leaves' conditions have schema **pins** injected — a pinned
event field `f` is conjoined `f: context.<pin-path>` onto every matching
predicate, realizing the "same X" correlation (`event_schema/pin.rs`).

After pin injection, leaves are **relativized** when the schema declares at
least one *universal symmetric* pin — a pin present (identically) on every
derived event kind whose context path is the field's own path, or a reserved
scope-alias pair (`callerPrincipal`/`principal`,
`callerResource`/`resource` — the bare scope reference, not
`context.principal`) (**L-Relativize**,
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
binder is fresh (`__pin_*`) and range-restricted by a positive atom before any
filter uses it. Validation (§5) runs on the **pre-rewrite** leaves, so
findings point at authored structure; engines receive the rewritten leaves
(`Lowered.temporal_rewritten`, surfaced by `temporal_fields()` /
`temporal_leaves()`). With no universal symmetric pin the rewrite is the identity. The default event
schema is not such a case: it pins `callerPrincipal` on every derived kind, so under
the default the rewrite is active.

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
warnings pass through verbatim (**V-Cedar-Warnings**). Crucially, this pass is
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
binding equality `(non-var, non-wildcard term) == x` or the mirror (`x == *` restricts nothing — a wildcard resolves to no value), the bodies of
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
  variables and produces none. Otherwise: *"variable `v` is used in a filter
  … that is not range-restricted by a preceding conjunct …"*.
- a **binding equality** `x == v` produces `x` and demands the value side's
  *outward* free variables — for an aggregate operand, `fv(body) ∖ for-list`
  (a correlated aggregate is only per-`u` when `u` is already bound; with
  `u` unbound the count/sum silently de-correlates). Otherwise: *"the
  equality binding `n` reads `u` inside its aggregate operand …"*.
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
guarantees expansion can never capture a call-site variable, so a variable free
at parse time is necessarily still free after expansion.

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

**Aggregate position.** An aggregate may appear **only** as the immediate operand
of a comparison:

```
  ─────────────────────────────────────────────────────── (WF-Agg-Operand)
   an Agg is well-placed iff it is a direct operand of a Comparison;
   an Agg as a predicate-arg value, an array element, or otherwise nested ⟹ reject
```

*(`check.rs` `check_operand`.)* Violation: *"an aggregate (`sum`/`count`) may appear only as
the immediate operand of a comparison …"*. This makes the aggregate-binding idiom `exists (n: T). ((A) == n && B)` well-formed: `(A) == n` binds
`n` (restrictor), then `B`'s use of `n` is an already-restricted filter.

### 5.5 Temporal dialect validation (against the schema)

Given an accepted condition, the temporal *dialect* checks it against the derived
event schema and the augmented Cedar schema, per leaf, in order: **event-schema
names → entity types → context paths → tp-dependence → types**
(`temporal/validate.rs`, **TEMP-Order**). Authority is divided: **event/field
name resolution is owned solely by the event-schema checker** ([§5.7](#57-event-schema-name-resolution));
the dialect additionally checks:

- **Entity types** — every `Entity(ty, id)` term must name a declared entity
  type; an action ref (`…::Action::"X"`) is skipped (Cedar reserves `Action`);
  an enum entity's id must be a permitted eid (**TEMP-EntityType-***).
- **Context paths** — a `context.<path>` must resolve against the scoped
  action's **full** declared context record (Cedar's `context` variable —
  `context.input.<field>…`, `context.system.<field>…`, etc.), on **every**
  action the leaf's scope pins; an unconstrained scope defers to Cedar
  (**TEMP-ContextPath-***). A `principal` / `resource` **scope** term is
  separate (Cedar's request scope entities, not a context field): the bare root
  types to the scoped action's principal / resource entity type, and an
  attribute tail (`principal.dept`) is accepted and resolved at eval time
  against the request's entity store (untyped here, as on the provider surface).
- **Types** (best-effort) — from a monomorphic environment seeded by the concrete
  scoped action's input fields **and every binder's declared annotation**
  (`exists (x: T)` and each aggregation `for (v: T)`; the declared type is
  **authoritative**, not reverse-inferred from a use site). Against that
  environment: a predicate arg must match its declared field type; a use of a
  bound variable must be consistent with its declared type; an ordering
  comparison requires both operands **numeric** (only `int` is numeric — an
  aggregate types as `int`, decimal is **not** numeric here); an equality
  requires compatible types; and a `tp(x)` binder must be declared
  `Timepoint` — any other declaration conflates a timepoint index with a
  data value, making the condition permanently false (a validated dead
  guard). A check fires only when both types are known (**TEMP-Type-***).
- **Max window** — every `within` window in the leaf (on a `formerly`,
  `previous`, or `since`, at any depth including inside an aggregation `where`
  body) must be **≤** the event schema's `max_window` cap, compared in seconds.
  A window strictly greater than the cap is rejected, located at the offending
  operator (**TEMP-MaxWindow**). The cap is the schema's `max_window` directive
  or the 24h default ([§2.6](#26-event-schema-dsl)); post-expansion every
  window is concrete, so macro-supplied windows are checked too.

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
— **PROV-ArgType**); a field-path argument (`context`/`principal`/`resource`) is
deferred to Cedar. Each **output method** in a chain is likewise checked here
(**PROV-Method-***): it must be declared in `availableMethods`, must not shadow a
Cedar extension-method name, must be given the declared argument count/types,
and — when it declares an `inputType` — must be fed a compatible value by the
preceding pipeline stage (the running type starts at the invocation's
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
   ⟨H, e⟩ ⇓ ⟨H′, r⟩            r ∈ { None } ∪ { Some(ρ) : ρ a Response }
```

where `H` is the temporal engine's observed history and `H′ = H · e` (the history
always grows). A `Response ρ = (decision ∈ {Allow, Deny}, reason: DogwoodRuleRef*,
errors: String*)`. This is `Authorizer::is_authorized` (`authorize/mod.rs`,
`api.rs`). The `None` result — "this event decided nothing" — is the essential
difference from Cedar.

### 6.1 Observe, then gate on decision kind

Every event is observed first, unconditionally; then its kind decides whether a
verdict is produced.

```
  ─────────────────────────── (A-Observe)     H′ := H · e   for every ingested e (observe runs first)
```
```
   H′ = H · e        e.kind ∉ decision_kinds
  ─────────────────────────────────────────────── (A-Ingest-History)
   ⟨H, e⟩ ⇓ ⟨H′, None⟩
```
```
   H′ = H · e        e.kind ∈ decision_kinds        ⟨H′, e⟩ ⇓_d ρ
  ────────────────────────────────────────────────────────────────── (A-Ingest-Decide)
   ⟨H, e⟩ ⇓ ⟨H′, Some(ρ)⟩
```

*(`api.rs`, `ingest`.)* `observe(e)` runs for *both* decision and history-only events
(**A-Observe**), so at a later decision point the temporal leaves see the full
prefix history including interleaved history-only events (**A-Stateful-Invariant**).
`⇓_d` is the decision judgment of [§6.2](#62-the-decision-pipeline-fail-closed).
A stateless single decision is a fresh authorizer fed one decision-kind event.

### 6.2 The decision pipeline (fail-closed)

`⇓_d` runs four steps — evaluate temporal leaves, build context, build request,
decide — each of the first three a **fail-closed** short-circuit. There are
exactly three top-level fail-closed points (and `build_request` decomposes into
four sub-causes). A fail-closed `Response` is always `(Deny, reason = [], errors =
[msg…])`.

```
   temporal.evaluate(H) = β        β, providers, e ⊢ ctx ⇓ Ok(κ)        e, κ ⊢ req ⇓ Ok(q)
   decide(q) = ρ₀        ρ = ρ₀ with pre-errors prepended
  ────────────────────────────────────────────────────────────────────────────────────────── (A-Decide-Ok)
   ⟨H, e⟩ ⇓_d ρ
```
```
   temporal.evaluate(H) = Err(m)
  ───────────────────────────────────────────────────────── (FailClosed-Temporal)
   ⟨H, e⟩ ⇓_d (Deny, [], ["temporal evaluation: " · m])
```
```
   β, providers, e ⊢ ctx ⇓ Err(m)
  ─────────────────────────────────────── (FailClosed-Context)
   ⟨H, e⟩ ⇓_d (Deny, [], [m])
```
```
   e, κ ⊢ req ⇓ Err(m)
  ─────────────────────────────────────── (FailClosed-Request)
   ⟨H, e⟩ ⇓_d (Deny, [], [m])
```

*(`api.rs`, `decide_at`.)* The rationale for **FailClosed-Context** is explicit
in the code: authorizing against a *partial* context could let a `permit` fire
whose guard can no longer be checked — a `Deny` silently flipping to `Allow`.
**Scope of this rule:** it describes THIS reference implementation. For
provider-originated errors (the dominant cause of a context-build failure) the
language-level semantics is *undefined behavior* — an erroring provider carries
no cross-implementation guarantee, and a policy set must not rely on
deny-on-error (see [the provider
contract](05-information-providers.md#the-provider-contract)). The
**FailClosed-Request** family below is NOT so scoped: a decision event with a
missing or malformed principal/resource must deny in every implementation. `build_request` fails closed when the event's
labeled scope has **no principal** or **no resource**
(**FailClosed-Request-NoPrincipal/NoResource**), when the principal/action/resource
UID is **malformed** (**FailClosed-Request-MalformedUID** — a fabricated fallback
would silently authorize against the wrong entity), or when Cedar `Request::new`
rejects the request.

### 6.3 Context assembly

The Cedar context `κ` is an ordered record with three groups of keys
(`api.rs`, `build_context`, **A-Context-Keys**):

1. `input` → the event's `input` record. Only a `Value::Object` is taken; any
   other shape (or absence) degrades to an empty record — it does **not** error
   (**A-Context-Input**).
2. for each `(id, b) ∈ β`: `id → Bool(b)` — the hoisted **temporal** booleans, at
   top level, i.e. `context.<id>`.
3. if any provider leaves exist: `providers → { id → v }` for **every**
   provider invocation in the policy set (**A-Context-Providers**) — i.e.
   `context.providers.<id>`, unconditional. There is no applicability
   filter of any kind: provider execution is not gated by the rule's
   action clause, scope constraints, or conditions (see [the provider
   contract](05-information-providers.md#the-provider-contract)).

Value mapping (`value_to_expr`, **A-Context-ValueMap**) is the obvious one, with
two lossy cases worth flagging: `Null` and a record-construction failure both
collapse to the **empty string** literal. An entity *value inside the context*
uses a **sentinel** (`Drupe::Gateway::"unknown"`) on a malformed UID rather
than failing closed — the deliberate counterpart to the fail-closed treatment of
the request's principal/action/resource (**A-Context-EntityValue-Sentinel**).

### 6.4 Provider evaluation

Each provider's value is computed **resolver-first, Rhai-fallback**
(`api.rs`, `eval_provider`):

```
   resolver present     resolver.resolve(name, args) = Some(res)
  ──────────────────────────────────────────────────────────────── (A-Provider-Resolver)
   eval_provider = res        (res = Ok(v) ⇒ v ; res = Err(m) ⇒ FailClosed-Context)
```
```
   resolver absent ∨ resolver declines (None)     field.declaration = Some(decl)
  ─────────────────────────────────────────────────────────────────────────────── (A-Provider-Rhai)
   eval_provider = evaluate(invocation, decl, args)
```

A caller-supplied `ProviderResolver` gets first refusal on every invocation; if
it declines, the declared sandboxed Rhai implementation runs. An invocation with
no declaration and no resolver value is an error (⇒ **FailClosed-Context**):
*"provider `k` was not declared … so it has no implementation to evaluate"*.
Arguments are resolved against the event: a `context.<path>` argument reads the
event's field at that path (falling back to a bare last-segment lookup, then
`Null`); literals and sets map directly (**A-Provider-ArgResolve**).

### 6.5 The decision core

Once context and request are built, the decision is delegated to the pluggable
`PolicyEngine` (default: local Cedar; alternatively, a remote Cedar-based engine) over the entity store
`E` assembled by `build_entities`: the request's **scope entities** (made
present bare), any **caller-supplied attributed entities** from the event's
entity store — attributes and direct `memberOf` parents, validated against the
augmented schema — and the schema's **action-hierarchy entities** (so
`action in [Group]` membership resolves). Cross-event state lives in the
temporal history; per-event entity data flows through `E`:

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

---

## 7. Meta-properties

These follow from the rules above; they are the properties a caller may rely on.

- **Fail-closed.** No evaluation failure produces `Allow`. Every error path in
  `⇓_d` yields `(Deny, [], errors)` (FailClosed-*), and the context is never
  partial when the policy engine runs — an incomplete context denies. *(§6.2.)*
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
- **Statefulness is confined to the temporal engine.** The policy engine is
  invoked per-request over an empty entity set; all history-dependence flows
  through `observe`/`evaluate` and the hoisted `context.<id>` booleans. History-only
  events matter precisely because they mutate that state. *(§6.1, §6.5.)*
- **Acceptance ⇒ monitorability.** A temporal condition that passes [§5.4](#54-temporal-acceptance-well-formedness)
  denotes a finite, computable relation over the history (safe-range): the
  leaf is closed (every variable `exists`- or `for`-bound), every bound
  variable — existential *and* aggregation `for` — is range-restricted by a
  positive atom (a negation restricts nothing, at any depth; a `since`
  restricts only through its anchor), filters follow their restrictors, and
  every monitoring scope varies with the timepoint.
