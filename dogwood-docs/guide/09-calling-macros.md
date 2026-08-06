# Calling Macros

Macros let you name and reuse a fragment of policy logic — a Cedar sub-expression
or a temporal pattern — so a threshold or a "happened recently" check lives in one
place and reads well at every use. This page covers **calling** a macro: where a
call may appear and what shape its arguments take. It assumes the macros already
exist (declared in your policy file or supplied by a macro library). **Defining**
macros — the `def cedar` / `def temporal` syntax, the `?p` / `$t` sigils, hygiene,
the rejection rules, and the macro library — is the subject of [Macros](06-macros.md).

The complete policies shown on this page are runnable example bundles under
`examples/`.

A macro call looks like an ordinary function call:

```text
name(arg, arg, …)
```

A zero-argument macro is just `name()`. What differs from an ordinary call is
*where* a call is allowed and *what* each argument may be — both determined by the
macro's kind.

## Where each kind is callable

A macro has a kind, fixed by its definition, and each kind may be called only in a
matching position:

| Macro kind | Callable in |
|---|---|
| `def cedar` | a Cedar-expression position (`when { … }` / `unless { … }`, or mid-expression) |
| temporal condition | a temporal condition slot (`when temporal { … }`, a `&&` operand, a `formerly` body, …) |
| temporal aggregation | an aggregation-value position (an operand of a comparison) |

A mismatch is a hard error, never a silent coercion — calling a temporal
macro in a Cedar position (or vice versa) is rejected with a message naming the
macro and the two kinds. The full set of checks (arity, kind, and argument shape)
is documented in [Macros](06-macros.md#calling-macros).

## Calling a Cedar macro

A `def cedar` macro is called wherever you would write the expression it names.
Given `is_small` and `is_eligible` / `is_not_blocked` in scope, they slot into an
ordinary `when` exactly like plain Cedar, and compose with `&&` / `||` / `!`:

```text
permit(principal, action, resource)
when { is_small(context.input.shares) };
```

> Runnable: [`examples/call_cedar_macro_is_small/`](../examples/call_cedar_macro_is_small/) — `dogwood validate`.

```text
permit(principal, action, resource)
when {
    is_eligible(context.input.shares, context.input.stock)
    && is_not_blocked(context.input.stock)
};
```

> Runnable: [`examples/call_cedar_macros_composed/`](../examples/call_cedar_macros_composed/) — `dogwood validate`.

Because a Cedar macro expands before the surrounding expression is lowered, one may
be conjoined with a `temporal { … }` block mid-expression:

```text
permit(principal, action, resource)
when { level_ok(context.input.level) && temporal { /* … */ } };
```

> Runnable: [`examples/call_cedar_macro_with_temporal_leaf/`](../examples/call_cedar_macro_with_temporal_leaf/) — `dogwood validate` and `dogwood replay` (the bundle fills the `/* … */` leaf with a recent-`Login` check).

A macro call may also appear as an argument to another macro call — the arguments
are expanded first, then spliced in — so a record-building macro can feed a
comparing one:

```text
permit(principal, action, resource)
when { semverGT(semver(2, 1, 1), semver(2, 1, 0)) };
```

> Runnable: [`examples/call_cedar_macro_as_argument/`](../examples/call_cedar_macro_as_argument/) — `dogwood validate`.

(Nesting a call *inside a macro's declared body* is a different thing and is not
allowed; see [Macros](06-macros.md#no-macro-in-macro).)

## Calling a temporal macro

A `def temporal` macro is called inside a `when temporal { … }` (or
`unless temporal { … }`) block. A **condition**-flavoured macro is called wherever
a temporal condition is expected. Here `once` wraps a window and a predicate:

```text
permit(principal, action == Drupe::Action::"Write", resource)
when temporal {
    once(1h, Drupe::Action::"Read"::response{
        input.user: context.input.user,
        input.document: context.input.document
    })
};
```

> Runnable: [`examples/call_temporal_condition_macro_once/`](../examples/call_temporal_condition_macro_once/) — `dogwood validate` and `dogwood replay`.

Condition macros compose with `&&` just like the built-in operators:

```text
permit(principal, action == Drupe::Action::"Write", resource)
when temporal {
    recently_logged_in(context.input.user)
    && recently_read(context.input.user, context.input.document)
};
```

> Runnable: [`examples/call_temporal_condition_macros_composed/`](../examples/call_temporal_condition_macros_composed/) — `dogwood validate` and `dogwood replay`.

An **aggregation**-flavoured macro produces a `count` or `sum`, so it is spliced
into a comparison — always inside an `exists` binder, which introduces the variable
the aggregate is compared against — never called on its own:

```text
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

> Runnable: [`examples/call_temporal_aggregation_macro_count/`](../examples/call_temporal_aggregation_macro_count/) — `dogwood validate` and `dogwood replay`.

Argument-nesting works for temporal macros too: because an aggregation macro
expands to a value (a `count`/`sum` term), a call to one may be passed as the
argument to another temporal macro whose parameter sits in a comparison-operand
position — the argument is expanded first, then spliced into that operand slot.
Given `count_within` (an aggregation macro) and `bind` (which names the
`exists … == …` binding scaffold):

```text
def temporal count_within(?w, ?s) {
    count for ($t: Timepoint). where (formerly within ?w (?s && tp($t)))
};
def temporal bind(?n, ?A, ?B) { exists (?n: Long). (?A == ?n && ?B) };

permit(principal, action == Drupe::Action::"Alert", resource)
when temporal {
    bind(n, count_within(1h, Drupe::Action::"Login"::request{
        input.user: _, input.server: context.input.server
    }), n > 2)
};
```

The nested `count_within(...)` fills `bind`'s `?A` parameter, which the body
uses as the left side of `?A == ?n` — a comparison operand, exactly where an
aggregate is legal. This is verdict-equivalent to writing the `exists … == n`
form by hand. (A condition-flavoured macro call cannot be nested this way — it
does not produce a comparison operand — and is rejected with a shape mismatch.)

### Window arguments are bare interval literals

When a macro takes a **window** parameter (the `within ?w` slot in its body), the
call-site argument is a **bare interval literal** — `1h`, `30m`, `24h` — with **no
`within` keyword**. The `within` keyword stays with the temporal operator in the
macro's body; the call supplies only the interval. In the `once` call above, `1h`
fills the window and the predicate fills the condition parameter.

### Binder arguments are bare identifiers

When a macro parameter is used in a *binder* position (for example the bound
variable of a `sum`), the call-site argument for it must be a **single bare
identifier** — that identifier becomes the bound-variable name. Passing a literal
or a compound expression there is a hard error. This is the one case where an
argument must be a plain name rather than a value; see
[Macros](06-macros.md#binder-position-parameters-p-used-as-a-binder) for why.

## What is checked at the call site

Every call is validated three ways — the details (and their exact error messages)
live in [Macros](06-macros.md#calling-macros):

- **Kind** — the call position must match the macro's kind (the table above).
- **Arity** — the number of arguments must equal the number of declared parameters.
- **Argument shape** — each argument must match how its parameter is used in the
  body: a whole-condition parameter takes a temporal condition, a window parameter
  takes a bare interval literal, a term parameter takes an expression, and a
  binder-position parameter takes a bare identifier.

Calling a name that is neither a declared macro nor a Cedar built-in is rejected as
an unknown call.

## See also

- [Macros](06-macros.md) — defining macros (`def cedar` / `def temporal`), the
  `?p` / `$t` sigils, hygiene, the rejection rules, and the macro library.
- [The policy language](02-policy-language.md) — the Cedar expressions a `def cedar`
  call expands into and the `when` / `unless` clauses that host a call.
- [Temporal expressions](04-temporal-expressions.md) — the temporal sublanguage a
  `def temporal` call expands into, and the `when temporal { … }` block a temporal
  call lives in.
- [Information providers](05-information-providers.md) — the other reusable-logic
  feature; providers are ordinary Cedar calls, not macros.
