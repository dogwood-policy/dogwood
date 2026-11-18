"""Bundle families: what each generated bundle targets.

- `temporal`: valid policy sets over random worlds and event schemas, with traces.
- `nearmiss`: one near miss of a validity rule (or its accepted side), in context.
- `macros`: macro definitions, libraries, calls, and expansion errors.
- `schema`: action-schema edge cases (namespaces, common types, enums, hierarchies, names).
- `events`: event-schema edge cases (pins of every kind, universality, kinds, derivation errors).
- `providers`: provider declarations, calls, and their errors.
- `traces`: valid sets with traces at the edges of their windows and with timestamp anomalies.
"""

from __future__ import annotations

import json
import random

from eventschema import (Decl, EventSchema, Named, Spread, builtin_schema, derive, gen_event_schema,
                         render_event_schema, seconds, add_attr)
from model import (BOOL, DECIMAL, LONG, STRING, EntityType, Ty, base_of, ent, is_ident, join_ns,
                   q, rec, render_ty, render_world, setof)
from policy import DEFAULT_LIBRARY, CedarGen, Macro, gen_macros, gen_scope
from providers import Decls, PType, Provider, call_expr, gen_decls
from temporal import TGen, ns_action, path_text
from traces import gen_trace
from worlds import Gen, gen_world

FAMILIES = [("temporal", 30), ("nearmiss", 26), ("macros", 10), ("schema", 8), ("events", 9),
            ("providers", 11), ("traces", 6)]

# Near misses the temporal generator applies (in a leaf), the Cedar generator applies (in a
# clause), and the provider calls apply.
TEMPORAL_MISSES = [
    "window_over", "window_zero", "kind_undeclared", "action_undeclared", "field_undeclared",
    "field_group", "named_arg_type", "arg_type", "arg_principal_wrong", "ctx_path_undeclared",
    "ctx_path_optional", "principal_attr_undeclared", "entity_undeclared_type", "enum_bad_eid",
    "decimal_bad", "array_arg", "binder_dup", "binder_type_undeclared", "binder_type_unqualified",
    "tp_long", "tp_ordered", "tp_eq_long", "operand_string_order", "operand_type_mismatch",
    "operand_entity_types", "operand_bool_order", "operand_decimal_order", "summand_string",
    "wildcard_operand", "timedep_const", "timedep_agg_const", "compound_agg_event",
    "existential_unrestricted", "array_in_arith", "wildcard_underscore",
]
CEDAR_MISSES = ["cedar_type_error", "cedar_unknown_attr", "cedar_context_whole", "cedar_reads_hoisted",
                "cedar_optional_unguarded"]
PROVIDER_MISSES = ["provider_arity", "provider_arg_type", "provider_context_arg", "provider_optional_arg",
                   "provider_undeclared", "provider_method_undeclared"]
TEMPLATE_MISSES = ["names_fresh_bool", "names_fresh_long", "names_fresh_providers", "enum_parent",
                   "impossible_policy", "principal_in_group", "scope_root_env", "entity_type_namespace",
                   "action_literal_undeclared", "optional_guarded", "principal_id_compare",
                   "temporal_reads_hoisted_leaf", "unknown_field_type", "pin_optional_path",
                   "pin_missing_path", "pin_wrong_type", "unless_temporal", "leafless_context_read"]


class Bundle:
    def __init__(self, name, family):
        self.name = name
        self.family = family
        self.files = {}
        self.tags = set()

    def write(self, root):
        import os
        d = os.path.join(root, self.name)
        os.makedirs(d, exist_ok=True)
        for (n, text) in self.files.items():
            with open(os.path.join(d, n), "w", encoding="utf-8") as f:
                f.write(text)
        with open(os.path.join(d, "meta.json"), "w", encoding="utf-8") as f:
            json.dump({"family": self.family, "tags": sorted(self.tags)}, f, indent=1)


def make(seed: int, idx: int, family: str = None) -> Bundle:
    """The bundle of index `idx` of seed `seed`. A draw the generator cannot complete (a world
    with no event to write a predicate on, say) is drawn again from a derived seed, up to ten
    times, so that the bundle is still a function of the seed and the index."""
    last = None
    for attempt in range(10):
        r = random.Random(f"{seed}:{idx}" + (f":{attempt}" if attempt else ""))
        tags = set()
        g = Gen(r, tags)
        fam = family or g.weighted(FAMILIES)
        b = Bundle(f"s{seed}_{idx:05d}_{fam}", fam)
        g.tag(f"family:{fam}")
        if attempt:
            g.tag("gen:redrawn")
        try:
            FUNCS[fam](g, b)
        except (AttributeError, IndexError, KeyError, TypeError, ValueError) as e:
            last = e
            continue
        b.tags = tags
        return b
    raise RuntimeError(f"bundle {seed}:{idx}: no complete draw in ten attempts: {last!r}")


# ─── Assembly ──────────────────────────────────────────────────────────────


class Spec:
    """What a bundle is made of, before rendering."""

    def __init__(self, g, wknobs=None, eknobs=None):
        self.g = g
        self.w = gen_world(g, wknobs or {})
        self.es = gen_event_schema(g, self.w, eknobs or {})
        self.events = derive(self.es, self.w)
        self.decls = None
        self.macros = []  # policy-level Macro definitions
        self.library = None  # macros.dw text (replaces the default library)
        self.lib_macros = dict(DEFAULT_LIBRARY)
        self.rules = []
        self.prefix = []  # text before the rules (defs, comments)
        self.windows = []
        self.schema_text = None
        self.event_text = None
        self.traces = []

    def available_macros(self):
        m = {} if self.library is not None else dict(self.lib_macros)
        for x in self.macros:
            m[x.name] = x
        return m

    def render(self, b: Bundle):
        b.files["schema.cedarschema"] = self.schema_text or render_world(self.w)
        et = self.event_text if self.event_text is not None else render_event_schema(self.es)
        if et is not None:
            b.files["event.dwschema"] = et
        if self.decls is not None:
            b.files["providers.json"] = self.decls.to_json()
            for (n, t) in self.decls.files.items():
                b.files[n] = t
        if self.library is not None:
            b.files["macros.dw"] = self.library
        src = "\n".join(self.prefix + [m.define() for m in self.macros] + self.rules)
        b.files["policy.dw"] = src + "\n"
        for i, t in enumerate(self.traces):
            b.files["trace.log" if len(self.traces) == 1 else f"trace_{i + 1}.log"] = t


def gen_rule(s: Spec, idx, misses=(), miss_rate=0.5, temporal_p=0.85, provider_p=0.0, force_action=None,
             effect=None, extra_clauses=()):
    g, w = s.g, s.w
    shape = gen_scope(g, w, force_action)
    tg = TGen(g, w, s.events, s.es, shape, misses=misses, miss_rate=miss_rate, macros=s.available_macros())
    cg = CedarGen(g, w, shape, misses=misses, miss_rate=miss_rate)
    clauses = []
    if g.p(temporal_p):
        leaf = tg.leaf(depth=g.choice([1, 2, 2, 3]))
        k = g.weighted([("when", 6), ("unless", 2), ("inline", 2), ("inline_unless", 1)])
        g.tag(f"rule:temporal_{k}")
        if k == "when":
            clauses.append(f"when temporal {{\n    {leaf}\n}}")
        elif k == "unless":
            clauses.append(f"unless temporal {{\n    {leaf}\n}}")
        elif k == "inline":
            clauses.append(f"when {{ {cg.expr(1)} && temporal {{ {leaf} }} }}")
        else:
            clauses.append(f"unless {{ temporal {{ {leaf} }} || {cg.expr(0)} }}")
        if g.p(0.15, "rule:two_temporal_leaves"):
            clauses.append(f"when temporal {{ {tg.leaf(depth=1)} }}")
    if g.p(0.35):
        clauses.append(f"{g.choice(['when', 'when', 'unless'])} {{ {cg.expr(2)} }}")
    if s.decls is not None and g.p(provider_p):
        provs = s.decls.providers
        if provs:
            p = g.choice(provs)
            pm = [m for m in misses if m.startswith("provider_")]
            e = call_expr(g, p, s.decls, shape, w, pm)
            kw = g.weighted([("when", 4), ("guardrails", 3), ("unless", 1)])
            g.tag(f"providers:clause_{kw}")
            clauses.append(f"when guardrails {{ {e} }}" if kw == "guardrails" else f"{kw} {{ {e} }}")
            if g.p(0.15, "providers:two_calls"):
                p2 = g.choice(provs)
                clauses.append(f"when {{ {call_expr(g, p2, s.decls, shape, w)} }}")
    clauses.extend(extra_clauses)
    if g.p(0.3):
        g.r.shuffle(clauses)
    s.windows.extend(tg.windows)
    eff = effect or g.weighted([("permit", 7), ("forbid", 3)])
    ann = ""
    if g.p(0.6):
        ann = f'@id("{g.choice(["r", "rule_", "p"])}{idx}")\n'
    elif g.p(0.1, "rule:annotation_other"):
        ann = '@advice("x")\n'
    body = "\n".join(clauses)
    rule = f"{ann}{eff} ({shape.scope_text}){(chr(10) + body) if body else ''};"
    s.rules.append(rule)
    return shape, tg, cg


def base_permit(s: Spec):
    s.rules.append(s.g.choice(["permit (principal, action, resource);",
                               '@id("allow_all")\npermit (principal, action, resource);']))


def add_traces(s: Spec, knobs=None, n=None):
    g = s.g
    n = n if n is not None else g.choice([1, 1, 1, 2])
    if not s.events:
        return
    for _ in range(n):
        s.traces.append(gen_trace(g, s.w, s.events, s.es, s.windows, knobs or {}))


def maybe_macros(s: Spec, p_policy=0.25, p_library=0.08):
    g = s.g
    if g.p(p_library, "macro:library_file"):
        lib = gen_macros(g, s.w, s.events, s.es, s.w.home, True)
        text = "\n".join(m.define() for m in lib)
        if g.p(0.3, "macro:library_copies_default"):
            text += "\ndef temporal count_within(?w, ?s) { count for ($t: Timepoint). where (formerly within ?w (?s && tp($t))) };"
            s.lib_macros = {"count_within": DEFAULT_LIBRARY["count_within"]}
        if g.p(0.15, "macro:library_with_policy"):
            text += "\npermit (principal, action, resource);"
        s.library = text + "\n"
        for m in lib:
            s.lib_macros[m.name] = m
        s.library_macros = lib
    if g.p(p_policy, "macro:policy_defs"):
        s.macros = gen_macros(g, s.w, s.events, s.es, s.w.home, False)
        if s.library is not None and getattr(s, "library_macros", None) and g.p(0.4, "macro:policy_overrides_library"):
            lm = s.library_macros[0]
            s.macros.append(Macro(lm.name, lm.kind, lm.params, lm.body, lm.shape, lm.callable, lm.data))


# ─── Families ──────────────────────────────────────────────────────────────


def fam_temporal(g, b):
    s = Spec(g)
    maybe_macros(s)
    if g.p(0.35, "rule:base_permit"):
        base_permit(s)
    for i in range(g.choice([1, 1, 2, 2, 3, 4])):
        gen_rule(s, i)
    add_traces(s)
    s.render(b)


def fam_traces(g, b):
    s = Spec(g, eknobs={"event_schema": g.choice(["default", "custom", "unpinned"])})
    if g.p(0.5):
        base_permit(s)
    for i in range(g.choice([1, 2])):
        gen_rule(s, i, effect=g.choice(["permit", "forbid"]))
    add_traces(s, {"equal_ts": 0.15, "decreasing_ts": 0.06, "nonconforming": 0.06}, n=g.choice([1, 2, 3]))
    s.render(b)


def fam_nearmiss(g, b):
    kind = g.weighted([(k, 3) for k in TEMPORAL_MISSES] + [(k, 3) for k in CEDAR_MISSES] +
                      [(k, 2) for k in PROVIDER_MISSES] + [(k, 4) for k in TEMPLATE_MISSES])
    g.tag(f"nearmiss:{kind}")
    if kind in TEMPLATE_MISSES:
        TEMPLATES[kind](g, b)
        return
    s = Spec(g)
    if kind in PROVIDER_MISSES:
        s.decls = gen_decls(g, s.w, {})
    n = g.choice([1, 1, 2])
    i = 0
    # Generate rules until the near miss has been applied (its choice point may not come up in a
    # rule), up to six.
    while i < n or (f"miss:{kind}" not in g.tags and i < 6):
        gen_rule(s, i, misses=[kind], miss_rate=0.6, provider_p=1.0 if kind in PROVIDER_MISSES else 0.0)
        i += 1
    if f"miss:{kind}" not in g.tags:
        g.tag("nearmiss:unapplied")
    if g.p(0.4):
        add_traces(s, n=1)
    s.render(b)


def fam_macros(g, b):
    s = Spec(g)
    maybe_macros(s, p_policy=0.9, p_library=0.35)
    k = g.weighted([("calls", 10), ("arity", 2), ("kind", 2), ("reserved", 2), ("duplicate", 2),
                    ("macro_in_macro", 2), ("binder_arg", 2), ("dollar_condition", 1), ("unknown", 2),
                    ("stray_param", 2), ("value_no_agg", 1), ("refine_non_pred", 1), ("wrapped_unsafe", 6),
                    ("cedar_macro_temporal", 2), ("cedar_calls", 3), ("gensym_twice", 2), ("arrays", 3),
                    ("value_body_binding", 2), ("library_errors", 3), ("cedar_macro_temporal_arg", 2),
                    ("multi_refine", 1)])
    g.tag(f"macro:case:{k}")
    av = s.available_macros()
    shape = None
    if k == "arity" and s.macros:
        m = s.macros[0]
        args = ", ".join(["1h"] * (len(m.params) + g.choice([-1, 1])))
        s.rules.append(f"permit (principal, action, resource) when temporal {{ {m.name}({args}) }};")
    elif k == "kind":
        s.macros.append(Macro("small", "cedar", ["n"], "?n < 100", "cedar", callable=False))
        s.rules.append(f"permit (principal, action, resource) when temporal {{ small(context.input.amount) }};")
    elif k == "reserved":
        nm = g.choice(["count", "sum", "formerly", "tp", "decimal", "let", "true", "where", "ip", "datetime"])
        s.prefix.append(f"def temporal {nm}(?w, ?s) {{ formerly within ?w ?s }};")
        gen_rule(s, 0)
    elif k == "duplicate":
        s.prefix.append("def temporal twice(?w, ?s) { formerly within ?w ?s };")
        s.prefix.append("def temporal twice(?w, ?s) { previous within ?w ?s };")
        gen_rule(s, 0)
    elif k == "macro_in_macro":
        s.prefix.append("def temporal inner(?w, ?s) { formerly within ?w ?s };")
        s.prefix.append("def temporal outer(?w, ?s) { inner(?w, ?s) };")
        e = g.choice(s.events)
        s.rules.append(f"permit (principal, action, resource) when temporal {{ outer(1h, {e.action.uid}::{e.kind}{{}}) }};")
    elif k == "binder_arg":
        s.prefix.append("def temporal s_f(?a, ?w, ?body) { sum ?a for (?a: Long), ($t: Timepoint). where (formerly within ?w (?body && tp($t))) };")
        e = g.choice(s.events)
        s.rules.append(f"permit (principal, action, resource) when temporal {{ (s_f({g.choice(['5', 'context.input.amount', '\"a\"'])}, 1h, {e.action.uid}::{e.kind}{{}})) > 1 }};")
    elif k == "dollar_condition":
        s.prefix.append("def temporal bad(?w) { formerly within ?w $t };")
        s.rules.append("permit (principal, action, resource) when temporal { bad(1h) };")
    elif k == "unknown":
        e = g.choice(s.events)
        s.rules.append(f"permit (principal, action, resource) when temporal {{ nosuch(1h, {e.action.uid}::{e.kind}{{}}) }};")
    elif k == "stray_param":
        e = g.choice(s.events)
        s.rules.append(f"permit (principal, action, resource) when temporal {{ formerly within 1h {e.action.uid}::{e.kind}{{}} && ?x > 1 }};")
    elif k == "value_no_agg":
        s.prefix.append("def temporal cap() { 100 };")
        e = g.choice(s.events)
        s.rules.append(f"permit (principal, action, resource) when temporal {{ formerly within 1h {e.action.uid}::{e.kind}{{}} && cap() > 1 }};")
    elif k == "refine_non_pred":
        s.prefix.append("def temporal r(?w, ?s) { formerly within ?w (?s{ requestId: \"x\" }) };")
        e = g.choice(s.events)
        s.rules.append(f"permit (principal, action, resource) when temporal {{ r(1h, formerly within 1h {e.action.uid}::{e.kind}{{}}) }};")
    elif k == "wrapped_unsafe":
        # A condition the parser would reject, behind a macro, so that expansion's check sees it.
        shape = gen_scope(g, s.w)
        tg = TGen(g, s.w, s.events, s.es, shape)
        e1, e2 = g.choice(s.events), g.choice(s.events)
        p1 = tg.pred(e1, n_extra=0)
        long_leaf = next(((l, e) for e in s.events for l in e.leaves if l.single() == LONG and all(is_ident(x) for x in l.path)), None)
        str_leaf = next(((l, e) for e in s.events for l in e.leaves if l.single() == STRING and all(is_ident(x) for x in l.path)), None)
        cases = ["free_var", "unrestricted", "filter_first", "neg_only", "since_left_unrestricted",
                 "for_unrestricted", "sum_not_for", "agg_arg", "reserved_binder", "interleaved", "ordered"]
        c = g.choice(cases)
        g.tag(f"macro:unsafe:{c}")

        def unsafe_body(U, V, A, T, PR):
            body = None
            if str_leaf:
                sl, se = str_leaf
                sp = f"{se.action.uid}::{se.kind}{{ {path_text(sl.path)}: {U} }}"
                sq = f"{se.action.uid}::{se.kind}{{ {path_text(sl.path)}: {V} }}"
                if c == "free_var":
                    body = f"formerly within 1h {sp}"
                elif c == "unrestricted":
                    body = f"exists ({U}: String). {U} == {U}"
                elif c == "filter_first":
                    body = f"exists ({U}: String). ({U} == \"alice\" && formerly within 1h {sp})"
                elif c == "neg_only":
                    body = f"exists ({U}: String). !formerly within 1h {sp}"
                elif c == "since_left_unrestricted":
                    body = f"exists ({U}: String). (({sp} since within 1h {p1}) && formerly within 1h {sp})"
                elif c == "for_unrestricted":
                    body = f"(count for ({U}: String). where !formerly within 1h {sp}) > 0"
                elif c == "reserved_binder":
                    body = f"exists ({PR}: String). formerly within 1h {sp.replace(f': {U}', f': {PR}')}"
                elif c == "interleaved":
                    body = (f"exists ({U}: String). exists ({V}: String). (formerly within 1h ({sp} && !{sq}) && "
                            f"formerly within 1h ({sq} && !{sp}))")
                elif c == "ordered":
                    body = f"exists ({U}: String). (formerly within 1h {sp} && {U} != \"x\")"
            if long_leaf and c in ("sum_not_for", "agg_arg"):
                ll, le = long_leaf
                lp = f"{le.action.uid}::{le.kind}{{ {path_text(ll.path)}: {A} }}"
                if c == "sum_not_for":
                    body = f"exists ({A}: Long). (formerly within 1h {lp} && (sum {A} for ({T}: Timepoint). where (formerly within 1h ({lp} && tp({T})))) > 1)"
                else:
                    body = f"formerly within 1h {le.action.uid}::{le.kind}{{ {path_text(ll.path)}: (count for ({T}: Timepoint). where tp({T})) }}"
            return body if body is not None else f"exists ({U}: String). {U} == {U}"

        # A `def temporal` body may not name a variable plainly (expansion would not rename it),
        # so the macro spells its variables `$x`; their fresh names after expansion leave the
        # condition as unsafe as the direct one. Now and then it keeps the plain names, which the
        # definition check rejects.
        body = unsafe_body("u", "v", "a", "t", "principal")
        if g.p(0.1, "macro:unsafe:plain_ident"):
            mbody = body
        else:
            mbody = unsafe_body("$u", "$v", "$a", "$t", "$principal")
        s.prefix.append(f"def temporal wrapped() {{ {mbody} }};")
        s.rules.append("permit (principal, action, resource) when temporal { wrapped() };")
        if g.p(0.5, "macro:unsafe_direct"):
            s.rules.append(f"permit (principal, action, resource) when temporal {{ {body} }};")
    elif k == "cedar_macro_temporal":
        s.prefix.append("def cedar lvl(?n) { ?n >= 2 };")
        shape, tg, cg = gen_rule(s, 0, temporal_p=0.0)
        ps = [p for (p, t, r) in shape.context_paths() if t == LONG and r]
        arg = f"context.{path_text(ps[0])}" if ps else "3"
        s.rules.append(f"permit ({shape.scope_text}) when {{ lvl({arg}) && temporal {{ {TGen(g, s.w, s.events, s.es, shape, macros=av).leaf(1)} }} }};")
    elif k == "cedar_calls":
        cm = [m for m in s.macros if m.kind == "cedar"]
        shape = gen_scope(g, s.w)
        ps = [p for (p, t, r) in shape.context_paths() if t == LONG and r]
        arg = f"context.{path_text(ps[0])}" if ps else "3"
        if not cm:
            cm = [Macro("is_small", "cedar", ["n"], "?n < 100", "cedar_small", callable=False)]
            s.macros.append(cm[0])
        m = g.choice(cm)
        if m.shape == "cedar_record":
            call = f"{m.name}({arg}, 2).x > 1"
        elif m.shape == "cedar_if":
            call = f"{m.name}(true, {arg})"
        else:
            call = f"{m.name}({arg})"
        if g.p(0.3, "macro:cedar_nested_call"):
            call = f"{m.name}({arg}) && {call}" if m.shape == "cedar_small" else call
        s.rules.append(f"permit ({shape.scope_text}) when {{ {call} }};")
    elif k == "gensym_twice":
        s.prefix.append("def temporal cnt(?w, ?s) { count for ($t: Timepoint). where (formerly within ?w (?s && tp($t))) };")
        e1, e2 = g.choice(s.events), g.choice(s.events)
        s.rules.append(f"permit (principal, action, resource) when temporal {{ (cnt(1h, {e1.action.uid}::{e1.kind}{{}})) - (cnt(2h, {e2.action.uid}::{e2.kind}{{}})) <= 1 }};")
    elif k == "arrays":
        e = g.choice(s.events)
        where = g.choice(["arg", "cmp", "agg_arith", "macro_arg"])
        g.tag(f"macro:array:{where}")
        if where == "arg":
            ls = [l for l in e.leaves if all(is_ident(x) for x in l.path)]
            f = path_text(ls[0].path) if ls else "requestId"
            s.rules.append(f'permit (principal, action, resource) when temporal {{ formerly within 1h {e.action.uid}::{e.kind}{{ {f}: ["a", "b"] }} }};')
        elif where == "cmp":
            s.rules.append(f'permit (principal, action, resource) when temporal {{ formerly within 1h {e.action.uid}::{e.kind}{{}} && [1] == [1] }};')
        elif where == "agg_arith":
            s.rules.append(f'permit (principal, action, resource) when temporal {{ (count for (t: Timepoint). where (formerly within 1h ({e.action.uid}::{e.kind}{{ requestId: ["x"] }} && tp(t)))) * 2 >= 1 }};')
        else:
            s.prefix.append("def temporal has_arr(?w, ?s) { formerly within ?w ?s };")
            s.rules.append(f'permit (principal, action, resource) when temporal {{ has_arr(1h, {e.action.uid}::{e.kind}{{ requestId: ["x", "y"] }}) }};')
    elif k == "value_body_binding":
        s.prefix.append("def temporal bnd(?w, ?s) { exists ($x: Long). ($x == (count for ($y: Long). where formerly within ?w ?s{ amount: $y }) + 1 && $x > 1) };")
        e = g.choice(s.events)
        s.rules.append(f"permit (principal, action, resource) when temporal {{ bnd(1h, {e.action.uid}::{e.kind}{{}}) }};")
    elif k == "library_errors":
        e = g.choice(s.events)
        err = g.choice(["duplicate", "reserved", "macro_in_macro", "parse", "kind_mismatch", "unused_param"])
        g.tag(f"macro:library_error:{err}")
        lib = {"duplicate": "def temporal once(?w, ?s) { formerly within ?w ?s };\ndef temporal once(?w, ?s) { previous within ?w ?s };",
               "reserved": "def temporal tp(?w, ?s) { formerly within ?w ?s };",
               "macro_in_macro": "def temporal a(?w, ?s) { formerly within ?w ?s };\ndef temporal b(?w, ?s) { a(?w, ?s) };",
               "parse": "def temporal once(?w, ?s) { formerly within ?w ?s ;",
               "kind_mismatch": "def cedar once(?w, ?s) { formerly within ?w ?s };",
               "unused_param": "def temporal once(?w, ?s, ?u) { formerly within ?w ?s };"}[err]
        s.library = lib + "\n"
        s.rules.append(f"permit (principal, action, resource) when temporal {{ once(1h, {e.action.uid}::{e.kind}{{}}) }};")
    elif k == "cedar_macro_temporal_arg":
        s.prefix.append("def cedar both(?a, ?b) { ?a && ?b };")
        shape = gen_scope(g, s.w)
        tg = TGen(g, s.w, s.events, s.es, shape, macros=av)
        s.rules.append(f"permit ({shape.scope_text}) when {{ both(true, temporal {{ {tg.leaf(1)} }}) }};")
    elif k == "multi_refine":
        s.prefix.append("def temporal r2(?w, ?s) { formerly within ?w (?s{ requestId: \"x\" }{ requestId: * }) };")
        e = g.choice(s.events)
        s.rules.append(f"permit (principal, action, resource) when temporal {{ r2(1h, {e.action.uid}::{e.kind}{{}}{{}}) }};")
    else:
        for i in range(g.choice([1, 2, 3])):
            gen_rule(s, i)
    if g.p(0.4):
        add_traces(s, n=1)
    s.render(b)


def fam_schema(g, b):
    k = g.weighted([("random_extreme", 6), ("cyclic_common", 2), ("cyclic_behind_context", 2),
                    ("self_ref_entity_attr", 1), ("builtin_named_types", 3), ("same_basename_two_ns", 2),
                    ("root_common_chain", 2), ("enum_principal", 1), ("action_cycle", 1),
                    ("undeclared_type_ref", 2), ("annotations", 1), ("shadow_entity_common", 2),
                    ("empty_namespace", 1), ("odd_names", 2)])
    g.tag(f"schema:case:{k}")
    knobs = {}
    if k == "random_extreme":
        knobs = {"layout": g.choice(["two", "root_commons", "nested", "root"]), "multi_principal": 0.7,
                 "groups": 0.7, "enum": 0.6, "odd_names": 0.4, "context_ref": 0.4, "common_types": 0.8,
                 "action_groups": 0.5}
    if k == "odd_names":
        knobs = {"odd_names": 1.0}
    s = Spec(g, wknobs=knobs)
    w = s.w
    home = w.ns(w.home)
    if k == "cyclic_common":
        home.commons.append(("Loop", "{ next: Loop }") if g.p(0.5) else ("A1", "B1"))
        if not any(c == "B1" for (c, _) in home.commons):
            home.commons.append(("B1", "A1"))
    elif k == "cyclic_behind_context":
        a = g.choice(w.appliable())
        home.commons.append(("Cyc", "{ x: Cyc }"))
        cname = "CycCtx"
        parts = []
        for (an, at, req) in a.context.attrs:
            tt = a.attr_refs.get(an) or render_ty(at, w.home)
            parts.append(f"{an}{'' if req else '?'}: {tt}")
        parts.append("meta: Cyc")
        home.commons.append((cname, "{ " + ", ".join(parts) + " }"))
        a.context_ref = cname
    elif k == "self_ref_entity_attr":
        e = next(iter(w.entities()))
        if e.enum is None:
            e.attrs = list(e.attrs) + [("self", ent(e.fq), False)]
    elif k == "builtin_named_types":
        nm = g.choice(["decimal", "String", "Long", "Bool", "ipaddr", "datetime", "Set", "Record", "Entity"])
        home.commons.append((nm, "{ foo: Long }"))
        g.tag(f"schema:builtin_name:{nm}")
        if g.p(0.5):
            s.decls = Decls([Provider(f"Risk::Score", [PType("string")],
                                      PType("record", fields=[("score", PType("decimal"), True)]),
                                      script='fn evaluate(a0) { #{ score: parse_decimal("0.5") } }\n')])
    elif k == "same_basename_two_ns":
        other = "Other" if w.home != "Other" else "Other2"
        from model import Namespace
        ons = Namespace(other)
        for e in list(w.entities())[:2]:
            ons.entities.append(EntityType(other, e.name, attrs=[("id", LONG, True)]))
        w.namespaces.append(ons)
        w.ids.update({f"{other}::{e.name}": ["alice"] for e in ons.entities})
    elif k == "root_common_chain":
        from model import Namespace
        if not any(n.name == "" for n in w.namespaces):
            w.namespaces.insert(0, Namespace(""))
        root = w.ns("")
        root.commons.append(("Inner", "{ id: String }"))
        root.commons.append(("Outer", "{ inner: Inner, tag: String }"))
        for a in w.appliable():
            if a.context_ref is None and g.p(0.7):
                inp = a.context.attr("input")
                if inp is not None:
                    newin = rec(*(list(inp[0].attrs) + [("wrap", rec(("inner", rec(("id", STRING, True)), True), ("tag", STRING, True)), True)]))
                    a.context = rec(*[(n, newin if n == "input" else t, r) for (n, t, r) in a.context.attrs])
                    a.attr_refs["input"] = None
                    a.attr_refs.pop("input", None)
                    # Write the input inline, with `wrap: Outer` resolved through the root.
                    a.attr_refs["input"] = "{ " + ", ".join(
                        [f"{n}{'' if r else '?'}: {render_ty(t, w.home)}" for (n, t, r) in inp[0].attrs] + ["wrap: Outer"]) + " }"
    elif k == "enum_principal":
        en = EntityType(w.home, "Svc", enum=["a", "b"])
        home.entities.append(en)
        a = g.choice(w.appliable())
        a.principals = a.principals + [en.fq]
    elif k == "action_cycle":
        acts = w.appliable()
        if len(acts) >= 2:
            acts[0].groups = [(w.home, acts[1].id)]
            acts[1].groups = [(w.home, acts[0].id)]
    elif k == "undeclared_type_ref":
        a = g.choice(w.appliable())
        a.attr_refs["input"] = g.choice(["Nope", f"{w.home}::Nope" if w.home else "Nope::X", "Other::In"])
    elif k == "annotations":
        for e in w.entities():
            e.annotations = [("doc", "an entity")]
    elif k == "shadow_entity_common":
        # An entity type and a common type of one name, or a bare name both in the namespace and
        # the root.
        nm = g.choice(["Thing", "In"])
        home.commons.append((nm, "{ a: Long }"))
        if g.p(0.5):
            home.entities.append(EntityType(w.home, nm + "E"))
        else:
            from model import Namespace
            if not any(n.name == "" for n in w.namespaces):
                w.namespaces.insert(0, Namespace(""))
            w.ns("").commons.append((nm, "{ b: String }"))
        a = g.choice(w.appliable())
        inp = a.context.attr("input")
        if inp is not None:
            a.attr_refs["input"] = "{ " + ", ".join(
                [f"{n}{'' if r else '?'}: {render_ty(t, w.home)}" for (n, t, r) in inp[0].attrs] + [f"x: {nm}"]) + " }"
    elif k == "empty_namespace":
        from model import Namespace
        w.namespaces.append(Namespace("Empty"))
    if s.decls is None and g.p(0.2):
        s.decls = gen_decls(g, w, {})
    s.events = derive(s.es, w)
    for i in range(g.choice([1, 2])):
        gen_rule(s, i, provider_p=0.5)
    if g.p(0.4):
        add_traces(s, n=1)
    s.render(b)


def fam_events(g, b):
    k = g.weighted([("random_custom", 8), ("universal_principal", 3), ("partial_pin", 3), ("context_pin", 3),
                    ("resource_pin", 2), ("attr_pin", 2), ("renamed_context_pin", 2), ("no_decision_kind", 1),
                    ("mixed_flags", 1), ("spread_principal", 1), ("selector_as_type", 1), ("dup_field", 1),
                    ("spread_collides", 1), ("pin_no_value", 1), ("value_no_pin", 1), ("max_window_edges", 3),
                    ("unknown_type", 2), ("renamed_reserved", 2), ("named_input", 1), ("deep_pins", 2),
                    ("empty_schema", 1), ("parse_errors", 1)])
    g.tag(f"events:case:{k}")
    s = Spec(g, eknobs={"event_schema": "custom"})
    es, w = s.es, s.w
    d0 = es.decls[0] if es.decls else None
    if k == "universal_principal":
        s.es = EventSchema([Decl(d.kind, d.decision, [f for f in d.fields if not (isinstance(f, Named) and f.name == "callerPrincipal")]
                                 + [Named("callerPrincipal", ("principalType",), ("principal", ()))]) for d in es.decls])
    elif k == "partial_pin" and len(es.decls) > 1:
        for f in es.decls[-1].fields:
            if isinstance(f, Named):
                f.pin = None
    elif k == "context_pin":
        for d in es.decls:
            d.fields.append(Named("tenant", ("concrete", "String", STRING), ("context", ("tenant",))))
        for a in w.appliable():
            if a.context_ref is None:
                add_attr(a, "tenant", STRING, True)
    elif k == "resource_pin":
        for d in es.decls:
            d.fields = [f for f in d.fields if not (isinstance(f, Named) and f.name == "callerResource")]
            d.fields.append(Named("callerResource", ("resourceType",), ("resource", ())))
    elif k == "attr_pin":
        for d in es.decls:
            d.fields.append(Named("dept_of", ("concrete", "String", STRING), ("principal", ("dept",))))
    elif k == "renamed_context_pin":
        for d in es.decls:
            d.fields.append(Named("sid", ("concrete", "String", STRING), ("context", ("sessionId",))))
        for a in w.appliable():
            if a.context_ref is None:
                add_attr(a, "sessionId", STRING, g.p(0.8))
    elif k == "no_decision_kind":
        for d in es.decls:
            d.decision = False
    elif k == "mixed_flags" and d0 is not None:
        es.decls.append(Decl(d0.kind, not d0.decision, list(d0.fields)))
    elif k == "spread_principal" and d0 is not None:
        d0.fields.append(Spread(g.choice(["principalType", "resourceType"])))
    elif k == "selector_as_type" and d0 is not None:
        d0.fields.append(Named("ins", ("concrete", "inputs(A)", STRING)))
        s.event_text = render_event_schema(es).replace("ins: inputs(A)", f"ins: inputs({d0.binder})")
    elif k == "dup_field" and d0 is not None:
        d0.fields.append(Named("requestId", ("concrete", "Long", LONG)))
        d0.fields.append(Named("requestId", ("concrete", "Long", LONG)))
    elif k == "spread_collides" and d0 is not None:
        d0.fields.append(Named("input", ("concrete", "String", STRING)))
    elif k == "pin_no_value" and d0 is not None:
        d0.fields.append(Named("px", ("concrete", "String", STRING), ("context", ("px",)), pin_value=False))
    elif k == "value_no_pin" and d0 is not None:
        d0.fields.append(Named("py", ("concrete", "String", STRING), ("context", ("py",)), pin_marker=False))
    elif k == "max_window_edges":
        es.max_window = g.choice(["1s", "59s", "1m", "3599s", "1h", "25h", "100d", "86400s", "0s", "2d",
                                  "106751d", "106752d", "9223372036s", "9223372037s", "99999999999999d",
                                  "18446744073709551616s"])
    elif k == "unknown_type" and d0 is not None:
        d0.fields.append(Named("weird", ("concrete", g.choice(["Nope", "Drupe::Nope", "Set<String>", "__cedar::String", "decimal"]), Ty("Unknown"))))
    elif k == "renamed_reserved":
        for d in es.decls:
            for f in d.fields:
                if isinstance(f, Named) and f.name == "callerPrincipal":
                    f.name = "actor"
    elif k == "named_input" and d0 is not None:
        d0.fields = [f for f in d0.fields if not isinstance(f, Spread)]
        d0.fields.append(Named("input", ("record", [Named("user", ("concrete", "String", STRING))])))
    elif k == "deep_pins":
        for d in es.decls:
            d.fields.append(Named("__drupe", ("record", [Named("session", ("record", [
                Named("id", ("concrete", "String", STRING), ("context", ("__drupe", "session", "id")))]))])))
        for a in w.appliable():
            if a.context_ref is None:
                add_attr(a, "__drupe", rec(("session", rec(("id", STRING, True)), True)), True)
    elif k == "empty_schema":
        s.es = EventSchema([])
    elif k == "parse_errors":
        s.event_text = g.choice(["event A::r { }", "decision event <A>::request { ...inputs(B) }",
                                 "event <A>::r { pin x: { y: String } = context.x }", "max_window = 0h\n",
                                 "event <A>::r {}\nmax_window = 1h\n", "event <A>::r { a: String, }",
                                 "event <A>::r { pin pin: String = context.pin }"])
    s.events = derive(s.es, w)
    if g.p(0.4):
        base_permit(s)
    for i in range(g.choice([1, 2])):
        gen_rule(s, i)
    if g.p(0.7):
        add_traces(s, n=g.choice([1, 2]))
    s.render(b)


def fam_providers(g, b):
    s = Spec(g)
    k = g.weighted([("random", 10), ("decl_errors", 3), ("enum_two_ns", 2), ("decimal_capture", 1),
                    ("quoted_fields", 2), ("method_chain", 2)])
    g.tag(f"providers:case:{k}")
    s.decls = gen_decls(g, s.w, {})
    if k == "decl_errors":
        p = s.decls.providers[0]
        err = g.choice(["entity_no_type", "entity_undeclared", "enum_empty", "enum_dup", "enum_wrong_ns",
                        "entity_with_fields", "entitytype_on_string", "export_clash", "unknown_entity_kind"])
        g.tag(f"providers:decl_error:{err}")
        if err == "entity_no_type":
            p.output = PType("entity")
        elif err == "entity_undeclared":
            p.output = PType("entity", entity=p.name.rsplit("::", 1)[0] + "::Undeclared")
        elif err == "enum_empty":
            s.decls.enums[p.name.rsplit("::", 1)[0] + "::E"] = []
        elif err == "enum_dup":
            s.decls.enums[p.name.rsplit("::", 1)[0] + "::E"] = ["A", "A"]
        elif err == "enum_wrong_ns":
            s.decls.enums["Elsewhere::E"] = ["A"]
        elif err == "entity_with_fields":
            p.output = PType("entity", entity=None, fields=[("x", PType("string"), True)])
        elif err == "entitytype_on_string":
            p.output = PType("string", entity="X::Y")
        elif err == "export_clash":
            s.decls.enums["A_B::C"] = ["x"]
            s.decls.enums["A::B_C"] = ["y"]
            s.decls.providers.append(Provider("A_B::F", [], PType("string"), script='fn evaluate() { "x" }\n'))
            s.decls.providers.append(Provider("A::G", [], PType("string"), script='fn evaluate() { "x" }\n'))
        else:
            p.output = PType("entitty", entity="X::Y")
    elif k == "enum_two_ns":
        from model import Namespace
        if len(s.w.namespaces) == 1 and s.w.home:
            other = Namespace("Zeta" if g.p(0.5) else "Alpha")
            s.w.namespaces.append(other)
    elif k == "decimal_capture":
        s.w.ns(s.w.home).commons.append(("decimal", "{ foo: Long }"))
    elif k == "quoted_fields":
        p = s.decls.providers[0]
        p.output = PType("record", fields=[(g.choice(["content-type", "in", 'say "hi"', "a.b", "if"]), PType(g.choice(["string", "integer", "bool"])), True)])
        p.script = gen_script_for(g, p, s.decls) if p.script is not None or p.script_file is None else p.script
    elif k == "method_chain":
        p = s.decls.providers[0]
        from providers import Method, gen_script
        p.methods = [Method("first", [], PType("integer"), PType("set", items=PType("long")) if g.p(0.5) else None),
                     Method("second", [PType("integer")], PType("bool"))]
        p.script = gen_script(g, p, s.decls.enums)
        p.script_file = None
    s.events = derive(s.es, s.w)
    if g.p(0.5):
        base_permit(s)
    for i in range(g.choice([1, 2, 3])):
        gen_rule(s, i, provider_p=0.9, temporal_p=0.4)
    add_traces(s, n=1)
    s.render(b)


def gen_script_for(g, p, d):
    from providers import gen_script
    return gen_script(g, p, d.enums)


# ─── Targeted templates (validity rules the random grammar rarely reaches) ─────


def t_names_fresh(kind):
    def f(g, b):
        s = Spec(g)
        shape, tg, cg = gen_rule(s, 0, temporal_p=1.0, provider_p=0.0, force_action="eq")
        for a in shape.actions:
            if kind == "names_fresh_bool":
                add_attr(a, "policy_0__temporal_0", BOOL, True)
            elif kind == "names_fresh_long":
                add_attr(a, "policy_0__temporal_0", LONG, True)
            else:
                add_attr(a, "providers", rec(("x", LONG, True)), g.p(0.5))
        if kind == "names_fresh_providers":
            s.decls = gen_decls(g, s.w, {})
            s.rules = []
            gen_rule(s, 0, temporal_p=0.5, provider_p=1.0, force_action="eq")
        s.render(b)
    return f


def t_enum_parent(g, b):
    s = Spec(g, wknobs={"enum": 1.0})
    w = s.w
    enum = w.entity(w.enum) if w.enum else None
    if enum is not None:
        for e in w.entities():
            if e.fq in w.principals and g.p(0.7):
                e.parents = e.parents + [enum.fq]
    gen_rule(s, 0)
    s.render(b)


def t_impossible_policy(g, b):
    s = Spec(g, wknobs={"multi_principal": 0.0})
    w = s.w
    a = g.choice(w.appliable())
    others = [e.fq for e in w.entities() if e.fq not in a.principals and e.enum is None]
    if not others:
        w.ns(w.home).entities.append(EntityType(w.home, "Bot"))
        others = [join_ns(w.home, "Bot")]
    t = g.choice(others)
    tg_shape = gen_scope(g, w, "eq")
    leaf = TGen(g, w, s.events, s.es, tg_shape).leaf(1)
    if g.p(0.5):
        s.rules.append(f"permit (principal is {t}, action == {a.uid}, resource) when temporal {{ {leaf} }};")
    else:
        s.rules.append(f"permit (principal, action == {a.uid}, resource) when {{ principal is {t} }};")
    s.render(b)


def t_principal_in_group(g, b):
    s = Spec(g, wknobs={"groups": 1.0, "multi_principal": 1.0})
    gen_rule(s, 0)
    w = s.w
    if w.group:
        a = g.choice(w.appliable())
        shape = gen_scope(g, w, "eq")
        tg = TGen(g, w, s.events, s.es, shape)
        attrs = shape.principal_attrs(w)
        lvl = [n for (n, t, r) in attrs if t == LONG]
        leaf = tg.leaf(1)
        cond = f" when {{ principal.{lvl[0]} > 1 }}" if lvl and g.p(0.5) else ""
        s.rules.append(f"permit (principal in {w.group}::{q('staff')}, {shape.scope_text.split(', ', 1)[1]}) when temporal {{ {leaf} }}{cond};")
    s.render(b)


def t_scope_root_env(g, b):
    s = Spec(g, wknobs={"multi_principal": 1.0})
    gen_rule(s, 0, force_action="in_list")
    s.render(b)


def t_entity_type_namespace(g, b):
    s = Spec(g, wknobs={"layout": "single"})
    w = s.w
    from model import Namespace
    other = Namespace("Other")
    for fq in w.principals:
        e = w.entity(fq)
        other.entities.append(EntityType("Other", e.name))
        w.ids[f"Other::{e.name}"] = ["alice"]
    w.namespaces.append(other)
    shape = gen_scope(g, w, "eq")
    tg = TGen(g, w, s.events, s.es, shape)
    ev = [e for e in s.events if e.leaf(("callerPrincipal",)) is not None]
    if ev:
        e = g.choice(ev)
        p = w.entity(w.principals[0])
        lit = f"Other::{p.name}::{q('alice')}" if g.p(0.7) else f"{p.fq}::{q('alice')}"
        s.rules.append(f"permit ({shape.scope_text}) when temporal {{ formerly within 1h {e.action.uid}::{e.kind}{{ callerPrincipal: {lit} }} }};")
    else:
        gen_rule(s, 0)
    s.render(b)


def t_action_literal(g, b):
    s = Spec(g)
    shape = gen_scope(g, s.w, "eq")
    a = shape.actions[0] if shape.actions else s.w.appliable()[0]
    bad = g.choice([True, False])
    lit = f"{ns_action(a.ns)}::{q('Lgoin' if bad else a.id)}"
    e = g.choice(s.events)
    s.rules.append(f"permit ({shape.scope_text}) when temporal {{ exists (x: String). (formerly within 1h "
                   f"{e.action.uid}::{e.kind}{{}} && {lit} == {lit}) }};" if g.p(0.3) else
                   f"permit ({shape.scope_text}) when temporal {{ formerly within 1h {e.action.uid}::{e.kind}{{}} && {lit} == {lit} }};")
    s.render(b)


def t_optional_guarded(g, b):
    s = Spec(g)
    w = s.w
    a = g.choice(w.appliable())
    add_attr(a, "note_ctx", rec(("note", STRING, False), ("user", STRING, True)), True)
    s.events = derive(s.es, w)
    shape = gen_scope(g, w, "eq")
    shape.actions = [a]
    shape.scope_text = f"principal, action == {a.uid}, resource"
    ev = [e for e in s.events if any(l.single() == STRING and all(is_ident(x) for x in l.path) for l in e.leaves)]
    e = g.choice(ev) if ev else g.choice(s.events)
    sl = [l for l in e.leaves if l.single() == STRING and all(is_ident(x) for x in l.path)]
    f = path_text(sl[0].path) if sl else "requestId"
    where = g.choice(["unguarded", "guarded_when", "guarded_inline", "guarded_unless", "guarded_later"])
    g.tag(f"template:optional:{where}")
    leaf = f"formerly within 1h {e.action.uid}::{e.kind}{{ {f}: context.note_ctx.note }}"
    if where == "unguarded":
        s.rules.append(f"permit ({shape.scope_text}) when temporal {{ {leaf} }};")
    elif where == "guarded_when":
        s.rules.append(f"permit ({shape.scope_text}) when {{ context.note_ctx has note }} when temporal {{ {leaf} }};")
    elif where == "guarded_inline":
        s.rules.append(f"permit ({shape.scope_text}) when {{ context.note_ctx has note && temporal {{ {leaf} }} }};")
    elif where == "guarded_unless":
        s.rules.append(f"permit ({shape.scope_text}) unless {{ !(context.note_ctx has note) }} when temporal {{ {leaf} }};")
    else:
        s.rules.append(f"permit ({shape.scope_text}) when temporal {{ {leaf} }} when {{ context.note_ctx has note }};")
    s.render(b)


def t_principal_id_compare(g, b):
    s = Spec(g)
    shape = gen_scope(g, s.w, "eq")
    e = g.choice(s.events)
    rhs = g.choice(["5", '"alice"', "principal.type", "resource.id", '"x"'])
    s.rules.append(f"permit ({shape.scope_text}) when temporal {{ formerly within 1h {e.action.uid}::{e.kind}{{}} && principal.id == {rhs} }};")
    s.render(b)


def t_temporal_reads_hoisted(g, b):
    s = Spec(g)
    shape = gen_scope(g, s.w, "eq")
    e = g.choice(s.events)
    s.rules.append(f"permit ({shape.scope_text}) when temporal {{ formerly within 1h {e.action.uid}::{e.kind}{{ requestId: context.policy_0__temporal_0 }} }};")
    s.render(b)


def t_unknown_field_type(g, b):
    s = Spec(g, eknobs={"event_schema": "custom"})
    for d in s.es.decls:
        d.fields.append(Named("weird", ("concrete", "Nope", Ty("Unknown"))))
    s.events = derive(s.es, s.w)
    shape = gen_scope(g, s.w, "eq")
    e = g.choice(s.events)
    v = g.choice(['"x"', "5", "*", "principal"])
    s.rules.append(f"permit ({shape.scope_text}) when temporal {{ formerly within 1h {e.action.uid}::{e.kind}{{ weird: {v} }} }};")
    s.render(b)


def t_pin(kind):
    def f(g, b):
        s = Spec(g, eknobs={"event_schema": "custom"})
        for d in s.es.decls:
            d.fields.append(Named("tenant", ("concrete", "String", STRING), ("context", ("tenant",))))
        for i, a in enumerate(s.w.appliable()):
            if a.context_ref is not None:
                continue
            if kind == "pin_optional_path":
                add_attr(a, "tenant", STRING, i != 0)
            elif kind == "pin_missing_path":
                if i != 0:
                    add_attr(a, "tenant", STRING, True)
            else:
                add_attr(a, "tenant", LONG if i == 0 else STRING, True)
        s.events = derive(s.es, s.w)
        gen_rule(s, 0)
        if g.p(0.5):
            add_traces(s, n=1)
        s.render(b)
    return f


def t_unless_temporal(g, b):
    s = Spec(g)
    base_permit(s)
    shape = gen_scope(g, s.w)
    tg = TGen(g, s.w, s.events, s.es, shape, macros=s.available_macros())
    s.rules.append(f"forbid ({shape.scope_text}) unless temporal {{ {tg.leaf(2)} }};")
    add_traces(s, n=1)
    s.render(b)


def t_leafless_context_read(g, b):
    s = Spec(g)
    shape = gen_scope(g, s.w)
    s.rules.append(f"permit ({shape.scope_text}) when {{ {g.choice(['context == context', 'context == {}', 'context has input'])} }};")
    if g.p(0.5):
        gen_rule(s, 1, temporal_p=1.0)
    s.render(b)


TEMPLATES = {
    "names_fresh_bool": t_names_fresh("names_fresh_bool"),
    "names_fresh_long": t_names_fresh("names_fresh_long"),
    "names_fresh_providers": t_names_fresh("names_fresh_providers"),
    "enum_parent": t_enum_parent,
    "impossible_policy": t_impossible_policy,
    "principal_in_group": t_principal_in_group,
    "scope_root_env": t_scope_root_env,
    "entity_type_namespace": t_entity_type_namespace,
    "action_literal_undeclared": t_action_literal,
    "optional_guarded": t_optional_guarded,
    "principal_id_compare": t_principal_id_compare,
    "temporal_reads_hoisted_leaf": t_temporal_reads_hoisted,
    "unknown_field_type": t_unknown_field_type,
    "pin_optional_path": t_pin("pin_optional_path"),
    "pin_missing_path": t_pin("pin_missing_path"),
    "pin_wrong_type": t_pin("pin_wrong_type"),
    "unless_temporal": t_unless_temporal,
    "leafless_context_read": t_leafless_context_read,
}

FUNCS = {"temporal": fam_temporal, "nearmiss": fam_nearmiss, "macros": fam_macros, "schema": fam_schema,
         "events": fam_events, "providers": fam_providers, "traces": fam_traces}
