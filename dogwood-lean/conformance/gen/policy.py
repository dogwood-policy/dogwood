"""Rules: scopes, Cedar conditions, temporal clauses, and macros.

A rule is generated against a `RuleShape`: the actions its scope targets and the principal and
resource types it admits, from which the context paths and scope attributes a condition may read
are computed (those present, with one type, in every environment the rule admits).
"""

from __future__ import annotations

from dataclasses import dataclass, field

from model import (BOOL, DECIMAL, LONG, LONG_POOL, STR_POOL, STRING, Ty, cedar_literal, is_ident,
                   join_ns, leaves, lookup, q, render_ty)
from temporal import TGen, ns_action, path_text


@dataclass
class RuleShape:
    actions: list  # model.Action, the actions the scope reaches that apply
    ptypes: list
    rtypes: list
    scope_text: str = ""
    p_member: str = None  # `principal in E` scope: the group uid

    def context_paths(self):
        """Context paths `(path, type, required)` with one type on every target action."""
        if not self.actions:
            return []
        common = None
        for a in self.actions:
            ls = {p: (t, r) for (p, t, r) in leaves(a.context)}
            # Record-typed context attributes are paths too (for whole-record reads).
            if common is None:
                common = ls
            else:
                common = {p: (t, r and ls[p][1]) for (p, (t, r)) in common.items() if p in ls and ls[p][0] == t}
        return [(p, t, r) for (p, (t, r)) in sorted(common.items()) if all(is_ident(s) for s in p)]

    def principal_attrs(self, w):
        return common_attrs(w, self.ptypes)

    def resource_attrs(self, w):
        return common_attrs(w, self.rtypes)


def common_attrs(w, types):
    common = None
    for fq in types:
        e = w.entity(fq)
        attrs = {n: (t, r) for (n, t, r) in (e.attrs if e else [])}
        if common is None:
            common = attrs
        else:
            common = {n: (t, r and attrs[n][1]) for (n, (t, r)) in common.items() if n in attrs and attrs[n][0] == t}
    return [(n, t, r) for (n, (t, r)) in sorted((common or {}).items()) if is_ident(n)]


# ─── Scopes ────────────────────────────────────────────────────────────────


def gen_scope(g, w, force_action=None) -> RuleShape:
    acts = w.appliable()
    # The action constraint.
    k = force_action or g.weighted([("eq", 70), ("in_list", 12), ("in_group", 6 if w.act_group else 0),
                                    ("any", 8), ("eq_group", 2 if w.act_group else 0), ("in_single", 2)])
    g.tag(f"scope:action:{k}")
    if k == "eq":
        a = g.choice(acts)
        targets, atext = [a], f"action == {a.uid}"
    elif k == "in_list":
        ts = g.sample(acts, g.choice([1, 2, 2, 3]))
        targets, atext = ts, "action in [" + ", ".join(a.uid for a in ts) + "]"
    elif k == "in_single":
        a = g.choice(acts)
        targets, atext = [a], f"action in {a.uid}"
    elif k in ("in_group", "eq_group"):
        gns, gid = w.act_group
        grp = w.action(gns, gid)
        targets = [a for a in acts if w.act_group in w.ancestors(a)]
        if k == "eq_group":
            targets = []
        atext = f"action {'in' if k == 'in_group' else '=='} {grp.uid}"
    else:
        targets, atext = list(acts), "action"
    ptypes = sorted({p for a in targets for p in a.principals})
    rtypes = sorted({x for a in targets for x in a.resources})
    # The principal constraint.
    pk = g.weighted([("any", 70), ("is", 10), ("eq", 8), ("in", 6 if w.group else 0),
                     ("is_in", 3 if w.group else 0), ("is_other", 1)])
    g.tag(f"scope:principal:{pk}")
    member = None
    if pk == "is" and ptypes:
        t = g.choice(ptypes)
        ptypes, ptext = [t], f"principal is {t}"
    elif pk == "is_other":
        others = [e.fq for e in w.entities() if e.fq not in ptypes]
        t = g.choice(others) if others else (ptypes[0] if ptypes else "X")
        ptypes, ptext = [t], f"principal is {t}"
    elif pk == "eq" and ptypes:
        t = g.choice(ptypes)
        ptypes, ptext = [t], f"principal == {t}::{q(g.choice(w.ids_of(t)))}"
    elif pk == "in" and w.group:
        member = f"{w.group}::{q('staff')}"
        ptypes = [p for p in ptypes if w.group in w.entity_ancestors(p)] or ptypes
        ptext = f"principal in {member}"
    elif pk == "is_in" and w.group and ptypes:
        t = g.choice(ptypes)
        member = f"{w.group}::{q('staff')}"
        ptypes, ptext = [t], f"principal is {t} in {member}"
    else:
        ptext = "principal"
    rk = g.weighted([("any", 80), ("is", 8), ("eq", 8), ("in", 4)])
    g.tag(f"scope:resource:{rk}")
    if rk == "is" and rtypes:
        t = g.choice(rtypes)
        rtypes, rtext = [t], f"resource is {t}"
    elif rk == "eq" and rtypes:
        t = g.choice(rtypes)
        rtypes, rtext = [t], f"resource == {t}::{q(g.choice(w.ids_of(t)))}"
    elif rk == "in":
        folder = [e for e in w.entities() if e.name == "Folder"]
        if folder:
            rtext = f"resource in {folder[0].fq}::{q('prod')}"
        else:
            rtext = "resource"
    else:
        rtext = "resource"
    # Narrow the targets to the actions that admit the narrowed types.
    targets = [a for a in targets if any(p in a.principals for p in ptypes) and
               any(x in a.resources for x in rtypes)]
    shape = RuleShape(targets, ptypes, rtypes, f"{ptext}, {atext}, {rtext}", member)
    if g.p(0.08, "scope:multiline"):
        shape.scope_text = f"\n    {ptext},\n    {atext},\n    {rtext}\n"
    return shape


# ─── Cedar conditions ──────────────────────────────────────────────────────


class CedarGen:
    """Cedar expressions over a rule's request environment."""

    def __init__(self, g, w, shape, misses=(), miss_rate=0.5):
        self.g, self.w, self.shape = g, w, shape
        self.misses = set(misses)
        self.miss_rate = miss_rate
        self.applied = []
        self.paths = shape.context_paths()

    def miss(self, kind):
        if kind in self.misses and kind not in self.applied and self.g.r.random() < self.miss_rate:
            self.applied.append(kind)
            self.g.tag(f"miss:{kind}")
            return True
        return False

    def expr(self, depth=2) -> str:
        if self.miss("cedar_type_error"):
            ps = [p for (p, t, r) in self.paths if t == STRING and r]
            return f"context.{path_text(ps[0])} > 5" if ps else '"a" > 5'
        if self.miss("cedar_unknown_attr"):
            return "context.input.nosuch == 1"
        if self.miss("cedar_context_whole"):
            return self.g.choice(["context == context", "context == {}", "context has nosuch"])
        if self.miss("cedar_reads_hoisted"):
            return "context.policy_0__temporal_0"
        if self.miss("cedar_optional_unguarded"):
            ps = [(p, t) for (p, t, r) in self.paths if not r]
            if ps:
                p, t = ps[0]
                lit = cedar_literal(self.g.r, t, self.w)
                if lit is not None:
                    return f"context.{path_text(p)} == {lit}"
        k = self.g.weighted([("cmp", 6), ("has", 2), ("and", 2 if depth > 0 else 0),
                             ("or", 1 if depth > 0 else 0), ("not", 1 if depth > 0 else 0),
                             ("pattr", 3), ("in", 1 if self.shape.p_member else 0),
                             ("if", 1 if depth > 0 else 0), ("like", 1), ("contains", 1), ("decimal", 1),
                             ("true", 1), ("is", 1)])
        self.g.tag(f"cedar:{k}")
        if k == "and":
            return f"{self.expr(depth - 1)} && {self.expr(depth - 1)}"
        if k == "or":
            return f"({self.expr(depth - 1)} || {self.expr(depth - 1)})"
        if k == "not":
            return f"!({self.expr(depth - 1)})"
        if k == "if":
            return f"(if {self.expr(depth - 1)} then {self.expr(depth - 1)} else {self.expr(depth - 1)})"
        if k == "has":
            ops = [p for (p, t, r) in self.paths if not r]
            if ops and self.g.p(0.7):
                p = ops[0]
                lit = cedar_literal(self.g.r, lookup_t(self.paths, p), self.w)
                # The record that holds the attribute: `context` itself for a top-level one.
                owner = ".".join(["context", *p[:-1]])
                if lit is not None and self.g.p(0.6):
                    self.g.tag("cedar:guarded_optional_read")
                    return f"({owner} has {p[-1]} && context.{path_text(p)} == {lit})"
                return f"{owner} has {p[-1]}"
            return f"context has input"
        if k == "pattr":
            attrs = self.shape.principal_attrs(self.w)
            ls = [(n, t) for (n, t, r) in attrs if r and t in (LONG, STRING)]
            if ls:
                n, t = self.g.choice(ls)
                if t == LONG:
                    return f"principal.{n} {self.g.choice(['<', '>=', '==', '!='])} {self.g.choice(LONG_POOL[:5])}"
                return f"principal.{n} {self.g.choice(['==', '!='])} {q(self.g.choice(['eng', 'ops', 'alice']))}"
            return "principal == principal"
        if k == "in" and self.shape.p_member:
            return f"principal in {self.shape.p_member}"
        if k == "like":
            ps = [p for (p, t, r) in self.paths if t == STRING and r]
            if ps:
                return f"context.{path_text(self.g.choice(ps))} like {self.g.choice(['\"a*\"', '\"*\"', '\"b*b\"'])}"
            return "true"
        if k == "contains":
            ps = [p for (p, t, r) in self.paths if t.kind == "Set" and r]
            if ps:
                return f"context.{path_text(ps[0])}.contains({q('a')})"
            return f"[1, 2].contains(1)"
        if k == "decimal":
            ps = [p for (p, t, r) in self.paths if t == DECIMAL and r]
            if ps:
                return f'context.{path_text(ps[0])}.lessThan(decimal("{self.g.choice(["1.0", "0.75"])}"))'
            return 'decimal("1.5").greaterThan(decimal("0.5"))'
        if k == "true":
            return self.g.choice(["true", "!false"])
        if k == "is":
            if self.shape.ptypes:
                return f"principal is {self.g.choice(self.shape.ptypes)}"
            return "true"
        ps = [(p, t) for (p, t, r) in self.paths if r and t in (LONG, STRING, BOOL)]
        if not ps:
            return "true"
        p, t = self.g.choice(ps)
        if t == LONG:
            return f"context.{path_text(p)} {self.g.choice(['<', '<=', '>', '>=', '==', '!='])} {self.g.choice(LONG_POOL)}"
        if t == STRING:
            return f"context.{path_text(p)} {self.g.choice(['==', '!='])} {q(self.g.choice(STR_POOL))}"
        return f"context.{path_text(p)} == {self.g.choice(['true', 'false'])}"


def lookup_t(paths, p):
    for (pp, t, r) in paths:
        if pp == p:
            return t
    return STRING


# ─── Macros ────────────────────────────────────────────────────────────────


@dataclass
class Macro:
    name: str
    kind: str  # cedar | temporal
    params: list
    body: str
    shape: str  # what it computes, for calls and tags
    callable: bool = True
    data: dict = field(default_factory=dict)

    def define(self) -> str:
        ps = ", ".join(f"?{p}" for p in self.params)
        return f"def {self.kind} {self.name}({ps}) {{ {self.body} }};"

    def call(self, tg: TGen, depth, env) -> str:
        """A call of this temporal macro inside a temporal block."""
        g = tg.g
        if self.shape == "once":
            return f"{self.name}({tg.window()}, {tg.pred(tg.pick_event(), correlate=env)})"
        if self.shape == "count":
            c = f"{self.name}({tg.window()}, {tg.pred(tg.pick_event(), correlate=env)})"
            if g.p(0.5):
                return f"({c}) {g.choice(['>', '>=', '<', '=='])} {g.choice([0, 1, 2])}"
            n = tg.fresh("n")
            return f"exists ({n}: Long). ({c} == {n} && {n} > {g.choice([0, 1])})"
        if self.shape == "count_within":
            c = f"count_within({tg.window()}, {tg.pred(tg.pick_event(), correlate=env)})"
            if g.p(0.3, "macro:bind_default"):
                n = tg.fresh("n")
                return f"bind({n}, {c}, {n} > {g.choice([0, 1, 2])})"
            return f"{c} >= {g.choice([1, 2])}"
        if self.shape == "sum_within":
            e = tg.pick_event(LONG)
            if e is None:
                return tg.c_formerly(depth, env)
            a, n = tg.fresh("a"), tg.fresh("total")
            return (f"exists ({n}: Long). (sum_within({a}, {tg.window()}, {tg.pred(e, bind=(a, LONG), correlate=env)})"
                    f" == {n} && {n} > {g.choice(LONG_POOL)})")
        if self.shape == "sum_param":
            e = tg.pick_event(LONG)
            if e is None:
                return tg.c_formerly(depth, env)
            a, n = tg.fresh("a"), tg.fresh("total")
            if tg.miss("macro_binder_arg_literal"):
                return f"({self.name}(5, {tg.window()}, {tg.pred(e, correlate=env)})) > 1"
            return (f"exists ({n}: Long). (({self.name}({a}, {tg.window()}, {tg.pred(e, bind=(a, LONG), correlate=env)}))"
                    f" == {n} && {n} > {g.choice(LONG_POOL)})")
        if self.shape == "refine":
            e = self.data["event"]
            return f"{self.name}({tg.window()}, {tg.pred(e, correlate=env)})"
        if self.shape == "value_arith":
            return f"{self.name}({tg.window()}) <= {g.choice([0, 2, 10])}"
        if self.shape == "both":
            return f"{self.name}({tg.c_formerly(depth - 1, env)}, {tg.c_formerly(depth - 1, env)})"
        if self.shape == "recently":
            lt = self.data["type"]
            arg = self.data["arg"]
            return f"{self.name}({arg})"
        if self.shape == "window_prev":
            return f"{self.name}({tg.window()}, {tg.pred(tg.pick_event(), correlate=env)}, {tg.pred(tg.pick_event(), correlate=env)})"
        if self.shape == "wrapped":
            return f"{self.name}()"
        if self.shape == "cedar":
            # A Cedar macro called in a temporal block: a near miss of kind.
            return f"{self.name}(context.input.user)"
        return tg.c_formerly(depth, env)


def gen_macros(g, w, events, es, home_ns, library: bool):
    """Macro definitions for the bundle's own policy source (or its library). Returns `Macro`s."""
    out = []
    ev = [e for e in events if any(all(is_ident(s) for s in l.path) for l in e.leaves)]
    pool = [("once", 4), ("count", 4), ("sum_param", 2), ("refine", 2 if ev else 0),
            ("value_arith", 1 if ev else 0), ("both", 2), ("recently", 2 if ev else 0),
            ("window_prev", 1), ("cedar_small", 3), ("cedar_record", 1), ("cedar_if", 1)]
    names_used = set()
    for _ in range(g.choice([1, 1, 2, 3])):
        k = g.weighted(pool)
        name = g.choice(["once", "recent", "seen", "m", "within_w", "check", "count_formerly",
                         "sum_formerly", "net", "both", "recently", "is_small", "f", "_m"])
        if name in names_used:
            name = name + str(len(names_used))
        names_used.add(name)
        if k == "once":
            out.append(Macro(name, "temporal", ["w", "s"], "formerly within ?w ?s", "once"))
        elif k == "count":
            out.append(Macro(name, "temporal", ["w", "s"],
                             "count for ($t: Timepoint). where (formerly within ?w (?s && tp($t)))", "count"))
        elif k == "sum_param":
            out.append(Macro(name, "temporal", ["a", "w", "body"],
                             "sum ?a for (?a: Long), ($t: Timepoint). where (formerly within ?w (?body && tp($t)))",
                             "sum_param"))
        elif k == "refine":
            e = g.choice(ev)
            ls = [l for l in e.leaves if all(is_ident(s) for s in l.path) and l.single() is not None]
            l = g.choice(ls)
            lit = cedar_literal(g.r, l.single(), w) if l.single().kind in ("String", "Long", "Bool", "Entity") else None
            arg = lit if lit is not None else "*"
            out.append(Macro(name, "temporal", ["w", "s"], f"formerly within ?w (?s{{ {path_text(l.path)}: {arg} }})",
                             "refine", data={"event": e}))
        elif k == "value_arith":
            e1, e2 = g.choice(ev), g.choice(ev)
            out.append(Macro(name, "temporal", ["w"],
                             f"(count for ($t: Timepoint). where (formerly within ?w ({e1.action.uid}::{e1.kind}{{}} && tp($t))))"
                             f" - (count for ($u: Timepoint). where (formerly within ?w ({e2.action.uid}::{e2.kind}{{}} && tp($u))))",
                             "value_arith"))
        elif k == "both":
            out.append(Macro(name, "temporal", ["a", "b"], "?a && ?b", "both"))
        elif k == "recently":
            e = g.choice(ev)
            ls = [l for l in e.leaves if all(is_ident(s) for s in l.path) and l.single() == STRING]
            if not ls:
                continue
            l = g.choice(ls)
            out.append(Macro(name, "temporal", ["u"], f"formerly within 1h {e.action.uid}::{e.kind}{{ {path_text(l.path)}: ?u }}",
                             "recently", data={"type": STRING, "arg": g.choice(['"alice"', "context.input.user", "_"])}))
        elif k == "window_prev":
            out.append(Macro(name, "temporal", ["w", "a", "b"],
                             "previous within ?w ?a && !(?b) since within ?w ?a", "window_prev"))
        elif k == "cedar_small":
            out.append(Macro(name, "cedar", ["n"], "?n < 100", "cedar_small", callable=False))
        elif k == "cedar_record":
            out.append(Macro(name, "cedar", ["a", "b"], "{ x: ?a, y: ?b }", "cedar_record", callable=False))
        elif k == "cedar_if":
            out.append(Macro(name, "cedar", ["c", "n"], "if ?c then ?n <= 10 else ?n <= 1000", "cedar_if", callable=False))
    return out


DEFAULT_LIBRARY = {
    "count_within": Macro("count_within", "temporal", ["w", "s"], "", "count_within"),
    "sum_within": Macro("sum_within", "temporal", ["a", "w", "body"], "", "sum_within"),
    "count_distinct_within": Macro("count_distinct_within", "temporal", ["k", "w", "s"], "", "distinct",
                                   callable=False),
    "bind": Macro("bind", "temporal", ["n", "A", "B"], "", "bind", callable=False),
}
