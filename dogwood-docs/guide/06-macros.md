# Macros

This page is the Advanced-topics deep dive on **defining** Dogwood macros:
lowering-time templates that let you name and reuse a fragment of policy logic. It
explains the two kinds of macro (`def cedar` and `def temporal`), the two
parameter sigils (`?p` value parameters and `$t` fresh binders), how calls are
checked for arity and kind, how hygiene keeps reused macros from capturing each
other's variables, every rule that will get a macro rejected, and
how to ship a reusable macro library alongside a schema.

If you just want to *call* a macro that already exists — where a call may appear
and what shape its arguments take — see [Calling macros](09-calling-macros.md);
this page is what you write to define one.

## What a macro is (and is not)

A Dogwood macro is a lowering-time template, not a runtime function. There is
no call stack, no recursion, and nothing that survives into the lowered
monitor. You declare a macro once at the top of a `.dw` file, and everywhere you
call it expansion splices the macro body in — substituting the call
arguments — before the policy is lowered. By the time the temporal evaluator or
the Cedar backend sees your policy, there are no macro definitions and no calls
left; the definitions have been consumed and every call has been replaced by its
expanded body.

Because macros are templates, they give you two things:

- **Naming.** `is_small(context.input.shares)` names the check
  `context.input.shares < 100`, and the threshold lives in exactly one place.
- **Reuse without duplication.** A temporal pattern like "did this happen in the
  last hour" can be written once and called from many policies. Dogwood's
  hygiene rules (see [Hygiene](#hygiene-t-is-fresh-per-call-site)) make that
  reuse safe even when the pattern introduces its own bound variables.

What macros are *not*: they are not first-class values, they cannot be passed
around at runtime, they cannot call other macros from inside their own body (see
[No macro-in-macro](#no-macro-in-macro)), and they are not scoped blocks — a
macro is always declared at the top level of a file, never inside a policy.

## Declaring a macro: the two kinds

A macro definition looks like a policy rule that starts with `def`, names a
*kind*, gives the macro a name and a parameter list, wraps a body in braces, and
ends with a mandatory semicolon:

```text
def cedar    <name>(?p, ?q, ...) { <cedar expression> } ;
def temporal <name>(?w, ?s, ...) { <temporal condition or aggregation> } ;
```

The kind keyword after `def` — `cedar` or `temporal` — chooses the sub-language
the body is parsed in, and that in turn decides where the macro may be called.
Definitions may be interleaved with policies in any order; all definitions are
collected first, then calls in the policies are expanded.

The trailing `;` is required, exactly as it is on a policy rule. The
parameter list is optional: a zero-argument macro is just `name()`.

### `def cedar` — a pure Cedar expression

A `def cedar` macro's body is an ordinary Cedar expression. Wherever you would
write that expression by hand — inside a `when { ... }` clause, or as part of a
larger expression — you can instead call the macro.

One example names a threshold:

```text
def cedar is_small(?n) { ?n < 100 };
```

and is called as an expression:

```text
permit(principal, action, resource)
when { is_small(context.input.shares) };
```

> Runnable: [`examples/cedar_is_small_threshold/`](../examples/cedar_is_small_threshold/) — `dogwood validate` (the macro library is supplied with `--macros`).

Cedar macros compose with ordinary Cedar operators. Here two of them are joined
with `&&`, and each takes an argument of a different type:

```text
def cedar is_eligible(?shares, ?stock) { ?shares < 100 || ?stock == "FOO" };
def cedar is_not_blocked(?stock) { !(?stock == "BLOCKED") };

permit(principal, action, resource)
when {
    is_eligible(context.input.shares, context.input.stock)
    && is_not_blocked(context.input.stock)
};
```

> Runnable: [`examples/cedar_eligible_not_blocked/`](../examples/cedar_eligible_not_blocked/) — `dogwood validate`.

A Cedar macro body can be any Cedar expression, including `like` patterns and
`if/then/else`:

```text
def cedar starts_with_f(?s) { ?s like "F*" };

def cedar within_cap(?stock, ?shares) {
    if ?stock == "FOO" then ?shares <= 10 else ?shares <= 1000
};
```

> Runnable: [`examples/cedar_starts_with_f_like/`](../examples/cedar_starts_with_f_like/) and [`examples/cedar_within_cap_if_else/`](../examples/cedar_within_cap_if_else/) — each wraps the macro in a full rule; `dogwood validate`.

A Cedar macro can even build a record and be passed as an argument to another
Cedar macro. This is the RFC 0061 `semver` worked example — two macros, where
`semver` constructs a `{ major, minor, patch }` record that `semverGT` compares:

```text
def cedar semver(?major, ?minor, ?patch) {
    { major: ?major, minor: ?minor, patch: ?patch }
};
def cedar semverGT(?a, ?b) {
    if ?a.major == ?b.major
    then (if ?a.minor == ?b.minor then ?a.patch > ?b.patch else ?a.minor > ?b.minor)
    else ?a.major > ?b.major
};

permit(principal, action, resource)
when { semverGT(semver(2, 1, 1), semver(2, 1, 0)) };
```

> Runnable: [`examples/cedar_semver_gt/`](../examples/cedar_semver_gt/) — `dogwood validate`.

This works because call *arguments* are expanded first, and the result is then
spliced into the outer macro's body — nesting one macro call as an argument to
another is fine. (Nesting a call *inside a macro's declared body* is not; see
[No macro-in-macro](#no-macro-in-macro).)

### `def temporal` — a temporal condition or aggregation

A `def temporal` macro's body is written in the temporal sub-language (the same
one you write inside a `when temporal { ... }` clause; see
[Temporal expressions](04-temporal-expressions.md)). Depending on what the body
matches, a `def temporal` macro comes in one of two flavours, chosen
automatically by the parser:

- a **temporal condition** — for example a `formerly within ... ...` predicate,
  which is callable wherever a temporal condition is expected; or
- a **temporal aggregation** — a `count`/`sum` expression, which is callable
  only as an operand of a comparison (the value side of an aggregation), never
  as a standalone condition.

The distinction matters at call sites, because Dogwood enforces which flavour
may appear where (see [Kind checking](#kind-checking)).

A condition-flavoured temporal macro is frequently a wrapper. `once` takes a
window `?w` and a whole condition `?s`, and wraps them in `formerly within`
(`once` only puts a name on `formerly within` and adds no capability of its own;
it is shown here for the shape a temporal macro takes, and the next example puts
a macro to fuller use):

```text
def temporal once(?w, ?s) { formerly within ?w ?s };

permit(principal, action in [Drupe::Action::"Read", Drupe::Action::"Write"], resource)
when temporal {
    once(1h, Drupe::Action::"Read"::request{
        input.user: context.input.user,
        input.document: context.input.document
    })
};
```

> Runnable: [`examples/temporal_once_read_recent/`](../examples/temporal_once_read_recent/) — `dogwood validate` and `dogwood replay`.

Condition macros compose the same way Cedar ones do. Two of them joined with
`&&` inside a single temporal block:

```text
def temporal recently_logged_in(?u) {
    formerly within 1h Drupe::Action::"Login"::response{ input.user: ?u }
};
def temporal recently_read(?u, ?d) {
    formerly within 1h Drupe::Action::"Read"::response{
        input.user: ?u, input.document: ?d
    }
};

permit(principal, action == Drupe::Action::"Write", resource)
when temporal {
    recently_logged_in(context.input.user)
    && recently_read(context.input.user, context.input.document)
};
```

> Runnable: [`examples/temporal_login_then_read/`](../examples/temporal_login_then_read/) — `dogwood validate` and `dogwood replay`.

An aggregation-flavoured temporal macro produces a `count` or `sum`. It is
spliced into a comparison, never called on its own. `count_formerly` counts the
timepoints in a window at which a predicate held:

```text
def temporal count_formerly(?w, ?s) {
    count for ($t: Timepoint). where (formerly within ?w (?s && tp($t)))
};

permit(principal, action == Drupe::Action::"Alert", resource)
when temporal {
    exists (n: Long). (
        (count_formerly(1h, Drupe::Action::"Login"::request{
            input.user: _, input.server: context.input.server
        })) == n
        && n > 0
    )
};
```

> Runnable: [`examples/temporal_count_formerly_login/`](../examples/temporal_count_formerly_login/) — `dogwood validate` and `dogwood replay`.

An aggregate value is always compared inside an `exists` binder — that is what
introduces the `n` the count is compared against (`exists` is the temporal
sublanguage's only binder; see
[Temporal expressions](04-temporal-expressions.md)). The macro call fills
the aggregate slot.

The `$t` in that body is a fresh binder the macro introduces itself,
not a parameter. That is the subject of the next section.

## Parameters: two sigils, two jobs

Dogwood macros use two sigils, and they do different things. The distinction
matters when writing temporal macros.

### `?p` — value / expression parameters

A `?p` parameter is declared in the parameter list and receives an argument at
each call site. Expansion splices the call argument literally into every
occurrence of `?p` in the body. This is ordinary template substitution.

`?p` parameters can stand for several different kinds of thing depending on
where they appear in the body:

- an ordinary term/expression (`is_small(?n)` where `?n` is compared);
- a **window** in a `within` clause (`within ?w`), filled by an interval
  literal like `1h`;
- a **whole condition** (`once(?w, ?s)` where `?s` is an entire temporal
  condition); or
- a **binder** position — see below.

In all of these, the rule is the same: `?p` is declared once in the parameter
list, and each call supplies exactly one argument for it.

The parameter list always stores names *without* the `?` internally, but you
always *write* the `?` — both in the declaration and at every use inside the
body. There is no whitespace allowed between the `?` and the name.

### `$t` — fresh binders (introduced inline, never declared)

A `$t` binder is spelled with a dollar sign and is **not** declared in the
parameter list. It receives no call-site argument. Instead, it is a placeholder
for a fresh bound variable that the macro introduces for its own internal use —
typically the timepoint variable a `count`/`sum` iterates over.

Look again at `count_formerly`:

```text
def temporal count_formerly(?w, ?s) {
    count for ($t: Timepoint). where (formerly within ?w (?s && tp($t)))
};
```

`?w` and `?s` are parameters (declared, filled by the caller). `$t` is a fresh
binder: the macro needs a timepoint variable to count over, so it names one
`$t`. The caller never passes a `$t` argument — it is entirely internal
machinery. At expansion, each `$t` is renamed to a unique concrete name (see
[Hygiene](#hygiene-t-is-fresh-per-call-site)).

The `$` sigil is distinct from `!` (negation) so it can never be
confused with an operator; `$` is used nowhere else in the surface syntax. A
`$t` may appear anywhere a regular identifier or binder can go: a term position,
a binder list, a `tp(...)` argument, or a `sum`'s bound variable. It may **not**
stand for a whole condition (see [Rejection rules](#what-gets-rejected)).

### Binder-position parameters (`?p` used as a binder)

There is one subtle case that ties the two sigils together: a `?p` parameter can
be used in a *binder* position — for example as the bound variable of a `sum`,
or inside a `for (?a: Long)`. When a `?p` is used that way, the argument the
caller passes for it must be a single bare identifier, because that
identifier is going to *become* a bound variable name. Passing anything else (a
literal, a compound expression) is a hard error.

In `sum_formerly`, `?a` is used both as the `sum`
bound variable and inside `for (?a: Long)`, so `?a` is a binder-position
parameter, while `?w` is a window and `?body` is a condition, and `$t` is the
macro's own fresh timepoint binder:

```text
def temporal sum_formerly(?a, ?w, ?body) {
    sum ?a for (?a: Long), ($t: Timepoint). where (formerly within ?w (?body && tp($t)))
};

permit(principal, action == Drupe::Action::"Alert", resource)
when temporal {
    exists (total: Long). (
        (sum_formerly(a, 1h, Drupe::Action::"Transfer"::request{
            input.user: _, input.amount: a
        })) == total
        && total > 100
    )
};
```

> Runnable: [`examples/temporal_sum_formerly_transfer/`](../examples/temporal_sum_formerly_transfer/) — `dogwood validate` and `dogwood replay`.

As with `count_formerly`, the aggregate is compared inside an `exists (total:
Long). (…)` binder, which introduces `total`.

The caller passes the bare identifier `a` for `?a`; that identifier fills the
binder slot. If you called it with a non-identifier such as a literal, the
call is rejected: "parameter `?a` is used in a binder position, so the
call-site argument must be a single identifier".

There is a difference between `?a` (a binder-position *parameter* the caller
names) and `$t` (a binder the *macro* names for itself). Use `?p` when the
caller should choose the variable; use `$t` when the variable is purely internal
and should be hygienically fresh.

## Calling macros

A call is written `name(arg, arg, ...)`. Where it may appear depends on the
macro's kind, and every call is checked in three ways: the call site's kind must
match the macro's kind, the number of arguments must match the number of
parameters, and each argument's shape must match how the corresponding parameter
is used in the body.

### Where each kind is callable

| Macro body kind      | Callable in                                                        |
|----------------------|--------------------------------------------------------------------|
| `def cedar`          | Cedar-expression position (`when { ... }`, or mid-expression)      |
| temporal condition   | Temporal condition slot (`when temporal { ... }`, `&&`, a `formerly` body, etc.) |
| temporal aggregation | Aggregation-value position (an operand of a comparison)           |

A Cedar macro can even be conjoined with a temporal block mid-expression — the
Cedar macro is expanded before the surrounding expression is lowered:

```text
def cedar level_ok(?n) { ?n >= 2 };

permit(principal, action, resource)
when { level_ok(context.input.level) && temporal { /* ... */ } };
```

> Runnable: [`examples/cedar_macro_plus_temporal_leaf/`](../examples/cedar_macro_plus_temporal_leaf/) — the bundle fills the `temporal { … }` leaf with a recent-Login check; `dogwood validate` and `dogwood replay`.

### Arity checking

The number of call arguments must exactly equal the number of declared
parameters. A macro declared `foo(?a, ?b)` called as `foo(principal)` fails with
"macro `foo` expects 2 argument(s), got 1". This is checked on every call path —
Cedar, temporal-condition, and aggregation.

### Kind checking

A call slot demands a specific macro kind, and a mismatch is a hard error, never
a silent coercion. The messages are specific about what went wrong:

- Calling a temporal macro in a Cedar-expression position: "macro `<name>` is a
  temporal macro and cannot be called in a cedar expression position".
- Calling a Cedar macro in a temporal condition position: "macro `<name>` is a
  cedar macro and cannot be called in a temporal condition position".
- Calling an aggregation macro as if it were a condition: rejected — an
  aggregation macro must appear as a comparison operand, not as a standalone
  condition.
- Calling a condition macro in an aggregation-value position: rejected — a
  condition macro cannot be used where an aggregation value is expected.

### Argument-shape checking

Even with the right count and kind, each argument's *shape* must match how the
parameter is used inside the body:

- A whole-condition parameter (`?s` in `once`) must be given a temporal
  condition argument.
- A window parameter (`within ?w`) must be given a bare interval literal such
  as `1h` — not a `within` clause. The body writes `formerly within ?w (...)`,
  and the call supplies just `1h`.
- A term-position parameter must be given a term (an expression), not a
  condition or an interval.
- A binder-position parameter must be given a single bare identifier, as
  described above.

Passing an argument whose shape does not match the parameter's use is a hard
error explaining the expected shape.

## Hygiene: `$t` is fresh per call site

Reusing a macro that introduces its own bound variable would break if the
macro's variable could collide with a variable the caller already has in scope.
Consider `sum_formerly` again: its body binds `$t`, and the caller of
`sum_formerly` might also have a variable named `t` in scope. If the macro's
`$t` and the caller's `t` were the same name after expansion, they would
capture each other and the policy would mean something the author never wrote.

Dogwood prevents this with **hygiene**: at expansion, every distinct `$t` name
in a macro body is renamed to a fresh, unique concrete name of the form
`<name>$<offset>`, where `<offset>` is the byte position of the call site. So a
`$t` becomes something like `t$412`, which cannot collide with a user's `t`.

Two properties make this both safe and predictable:

- **All occurrences of one `$t` name within a single expansion get the same
  gensym.** The binder and its uses stay tied together — `count for ($t: ...)`
  and the `tp($t)` inside it become the same fresh name, so the count still
  iterates over the variable it binds.
- **Different call sites get different gensyms.** Because the fresh name is
  derived from the call site's byte offset, calling the same macro in two
  different policies produces two different fresh names. That is exactly what
  makes reusing a macro across policies safe.

Concretely, if a caller passes its own identifier `t` as a bound-variable
argument and the macro also uses `$t` internally, the macro's `$t` expands to
`t$<offset>`. A source identifier cannot contain `$`, so the fresh name is not
expressible in the surface syntax and cannot collide with the caller's `t`.
And because the gensym is a deterministic function of the source position, the
same source always produces the same name, keeping builds reproducible.

## What gets rejected

The following are all hard errors, caught during the macro-expansion pass.

### Reserved names

A macro name may not shadow a Cedar built-in or a temporal keyword. The reserved
set is:

```text
decimal, datetime, duration, ip,        // Cedar built-in unary calls
let, in, where, for, sum, count, tp,    // temporal keywords / operators
formerly, previous, since,
true, false                             // literals
```

`let` is reserved although the language has no `let` form. Naming a macro
`count`, for example, fails with "macro name `count` is reserved (built-in or
keyword); pick a different name".

### Duplicate definitions

Two `def`s with the same name in the merged set are rejected: "duplicate macro
definition `<name>`". (This does not apply to a library macro and a policy macro
of the same name — see [Precedence](#precedence-a-policys-def-wins). In that case
the library one is silently dropped rather than treated as a duplicate.)

### Undeclared parameters in a body

Every `?p` reference inside a body must name a declared parameter. A `def cedar`
body that references `?x` when `?x` was never declared fails with "in `def cedar`
body: `?x` does not name a declared parameter". The same check applies to
temporal bodies in every position a `?p` can appear (term, window, binder, and
whole-condition positions).

`$t` binder names are the exception: they are *not* checked against the
parameter list (they are never declared there), and are tied together by
name at expansion.

### No macro-in-macro

A macro body may not contain a call to another macro. A `def cedar` body that
calls another macro fails with "in `def cedar` body: macro-in-macro is not
supported"; the temporal equivalent is "in `def temporal` body: macro-in-macro
is not supported".

This is distinct from nesting a call as a call-site *argument*, which is allowed:
`semverGT(semver(2, 1, 1), semver(2, 1, 0))` works because the arguments are
expanded first and then spliced in. The restriction is only on a macro's own
declared body containing a call.

### No `temporal` block inside a Cedar macro body

A `def cedar` body must be a pure Cedar expression; it may not contain a
`temporal { ... }` block. Attempting it fails with a message telling you to
"lift the block to the call site instead". The reason is that Cedar substitution
does not descend into the temporal sub-language, so a `?p` inside one would never
be substituted, and even a self-contained block would be re-evaluated per call
site.

An information-provider invocation (`Provider::Name(args)…`) is a *namespaced
Cedar call*, not a block, so it is subject to the macro-in-macro rule above: a
provider call inside a `def cedar` body fails with "macro-in-macro is not
supported" — lift it to the call site. (There is no `guardrails { … }` to reject
in a macro body: `guardrails` is a clause tag, not an expression form. See
[Information providers](05-information-providers.md).)

### Stray sigils outside a macro body

A `?p` or `$t` that survives expansion outside any macro body is rejected,
because there is nothing to substitute it. Writing `?something` in a policy that
is not inside a macro body fails with "stray macro parameter reference
`?something` outside a macro body"; a top-level `$t` in a `for`-binder fails with
"stray macro binder reference `$t`". (`?principal` and `?resource` in
Cedar templates are a different feature — template slots — and are handled
before the macro pass.)

### A whole-condition `$t` has no meaning

A `$t` cannot stand for an entire condition — a bare binder name is not a
condition. This is rejected both by the grammar (only `?p`, never `$t`, may fill
a whole-condition slot) and, if it somehow reaches expansion, with "macro binder
`$<name>` used as a whole condition has no meaning".

### Unknown macro call

A call whose name is neither a Cedar built-in nor a declared macro is rejected.
In Cedar position: "unknown function or macro `<name>` (not a Cedar built-in and
not a declared macro)". In temporal position: "unknown macro `<name>` (no
declared `def temporal`)". (One exception exists that is not a macro: a
call whose name is a declared information provider is left intact for the Cedar
backend — see [Information providers](05-information-providers.md).)

## The macro library

Macros declared at the top of a `.dw` file are visible only to the policies in
that file. To share macros across many policy files, Dogwood lets you attach a
**macro library** to a schema. Reusable `def cedar` / `def temporal` definitions
in the library are merged into every policy set lowered against that schema.

### `DEFAULT_MACROS`: the built-in standard library

If you build a schema without specifying a library, Dogwood uses a built-in
default, `DEFAULT_MACROS`. It ships a small **standard library** of temporal
aggregation macros, so every policy can call them without redeclaring them:

- `count_within(?w, ?s)` — counts the timepoints within window `?w` at which
  condition `?s` held.
- `sum_within(?a, ?w, ?body)` — sums the numeric value `?a` over occurrences of
  `?body` within window `?w`.
- `count_distinct_within(?k, ?w, ?s)` — counts the distinct key values `?k`
  (a `String`) for which `?s` held within window `?w`.
- `bind(?n, ?A, ?B)` — a "let"-style binder that names an aggregate result `?n`
  and uses it in the predicate `?B`, so an aggregate can be compared or
  thresholded via `?A == ?n`.

The file backing `DEFAULT_MACROS` is embedded into the crate at build time via
`include_str!`, so these macros are available to every caller regardless of
working directory — there is no runtime file lookup. A policy's own `def` of the
same name still takes precedence over a default, so a policy can always override
or shadow a standard-library macro with its own definition.

#### Using the standard-library macros

All four are `def temporal` macros, so they are called inside a
`when temporal { … }` block. Because they expand to an aggregate term, the usual
idiom is to bind the aggregate's value with `exists (n: Long). (… == n && …)`
and then threshold `n` — or let `bind` write that scaffold for you. The examples
below assume an action schema with `Login`, `Transfer`, and `Alert` actions;
each is a runnable corpus case (`tests/passing/macros/corpus/stdlib_default_*`).

**`count_within`** — permit an `Alert` only when more than two `Login`s to the
same server occurred within the last hour:

```text
permit ( principal, action == Drupe::Action::"Alert", resource )
when temporal {
    exists (n: Long). (
        count_within(1h, Drupe::Action::"Login"::request{
            input.user: _, input.server: context.input.server
        }) == n
        && n > 2
    )
};
```

**`sum_within`** — permit an `Alert` when the total amount transferred by any
user exceeds 200 within the last hour. The first argument (`a`) names the value
column to sum; it is bound from the predicate's `input.amount: a`:

```text
permit ( principal, action == Drupe::Action::"Alert", resource )
when temporal {
    exists (total: Long). (
        sum_within(a, 1h, Drupe::Action::"Transfer"::request{
            input.user: _, input.amount: a
        }) == total
        && total > 200
    )
};
```

**`count_distinct_within`** — permit an `Alert` when more than two *distinct*
users logged in to the server within the last hour. The key `u` is a `for`-binder
with no timepoint, so repeated values across timepoints deduplicate (contrast
`count_within`, which counts events):

```text
permit ( principal, action == Drupe::Action::"Alert", resource )
when temporal {
    exists (d: Long). (
        count_distinct_within(u, 1h, Drupe::Action::"Login"::request{
            input.user: u, input.server: context.input.server
        }) == d
        && d > 2
    )
};
```

**`bind`** — writes the `exists (n: Long). (agg == n && pred)` scaffold for you.
It composes with the aggregate macros, so the `count_within` example above can be
written without the hand-rolled `exists`:

```text
permit ( principal, action == Drupe::Action::"Alert", resource )
when temporal {
    bind(
        n,
        count_within(1h, Drupe::Action::"Login"::request{
            input.user: _, input.server: context.input.server
        }),
        n > 2
    )
};
```

`bind`'s value argument is any term-position aggregate, so it accepts a raw
hand-written `count for (t: Timepoint). where (…)` just as readily as a
`count_within(…)` call.

### Supplying your own library with `macros_str`

The macro library is part of the **`ServiceSchema`** — the fixed,
service-provided half of a schema (macros, providers, event schema). Provide the
library source to the `ServiceSchemaBuilder` via `macros_str` (see
[API and workflow](07-api-and-workflow.md) for the full builder). The library
source is ordinary Dogwood source containing `def` definitions:

```rust
let service = ServiceSchema::builder()
    .macros_str(
        "def temporal once(?w, ?s) { formerly within ?w ?s };\n\
         def cedar    is_small(?n) { ?n < 100 };",
    )
    .build()?;
```

Every policy set parsed against this service schema can then call `once` and
`is_small` without redeclaring them (macro expansion runs in the parse phase,
against the `ServiceSchema` alone — no action schema needed). Supplying
`macros_str` **replaces** `DEFAULT_MACROS` entirely, so a custom library does
not automatically include the standard-library macros; if you want them
alongside your own, copy their definitions into your library source. If you omit
`macros_str`, `DEFAULT_MACROS` (the standard library above) is used.

> Runnable: [`examples/macro_library_once_is_small/`](../examples/macro_library_once_is_small/) — the same `once` + `is_small` library as a `macros.dw` file a policy calls via `dogwood validate --macros …` (and `dogwood replay`).

Only the library's *definitions* are used — if the library source happens to
contain policies too, they are ignored. An empty or whitespace-only library
(for example, one supplied via `macros_str` that contains only comments) adds
nothing.

### Precedence: a policy's `def` wins

If a policy file declares a macro with the same name as one in the library, the
policy's own definition takes precedence and the library's same-named
definition is dropped. This is a merge rule, not a duplicate error:
the library can neither shadow a policy's macro nor cause a
duplicate-definition failure against one. So a policy author can always override a
library macro locally by defining their own version of it.

## See also

- [Temporal expressions](04-temporal-expressions.md) — the sub-language that
  `def temporal` macro bodies are written in (`formerly`, `previous`, `since`,
  `count`/`sum`, `tp`, `within`, and binders).
- [Policy language](02-policy-language.md) — the Cedar expressions that
  `def cedar` macro bodies expand into.
- [Calling macros](09-calling-macros.md) — the core counterpart to this page:
  where a call may appear and what shape its arguments take.
- [Information providers](05-information-providers.md) — why a Cedar macro body
  may not contain a provider call, and how provider calls differ from macro calls.
- [The API and workflow](07-api-and-workflow.md) — `ServiceSchemaBuilder::macros_str`, the
  lowering pipeline, and where macro expansion sits (the `ServiceSchema` a macro
  library attaches to).
