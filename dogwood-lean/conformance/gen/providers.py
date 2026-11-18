"""Information providers: declarations (`providers.json`), Rhai implementations, and calls.

A provider is modelled by its argument kinds, its output type (a `PType`), and its methods; the
generator writes a deterministic Rhai script for each, and calls in Cedar clauses whose arguments
are context paths, scope attributes, or literals of the declared kinds.
"""

from __future__ import annotations

import json
from dataclasses import dataclass, field

from model import LONG, STRING, BOOL, DECIMAL, is_ident, q, setof, Ty, ent
from temporal import path_text

PROVIDER_NS = ["Strings", "Risk", "Content", "Lists", "Text", "Vendor", "Guard"]
PROVIDER_FN = ["Matches", "Score", "Filter", "Length", "Allowed", "Analyze", "Check", "Scan"]
ODD_FIELDS = ["content-type", "in", 'say "hi"', "x.y", "if", "has", "_ok", "Ä"]


@dataclass
class PType:
    """A declared `paramType`: string, integer, long, bool, boolean, decimal, set (`items`),
    record (`fields`, `required`), entity (`entity`), or an unknown kind."""

    kind: str
    items: "PType" = None
    fields: list = field(default_factory=list)  # (name, PType, required)
    entity: str = None

    def to_json(self):
        j = {"paramType": self.kind}
        if self.items is not None:
            j["items"] = self.items.to_json()
        if self.kind == "record" or self.fields:
            j["fields"] = {n: t.to_json() for (n, t, _) in self.fields}
            j["required"] = [n for (n, _, r) in self.fields if r]
        if self.entity is not None:
            j["entityType"] = self.entity
        return j

    def cedar(self, enum_names=None) -> Ty:
        """The Cedar type the crate gives a hoisted value of this type (when known)."""
        k = self.kind
        if k == "string":
            return STRING
        if k in ("integer", "long"):
            return LONG
        if k in ("bool", "boolean"):
            return BOOL
        if k == "decimal":
            return DECIMAL
        if k == "set":
            return setof(self.items.cedar(enum_names) if self.items else STRING)
        if k == "entity":
            return ent((enum_names or {}).get(self.entity, self.entity))
        if k == "record":
            return Ty("Record", attrs=tuple((n, t.cedar(enum_names), r) for (n, t, r) in self.fields))
        return STRING


@dataclass
class Method:
    name: str
    args: list
    output: PType
    input: PType = None


@dataclass
class Provider:
    name: str
    args: list
    output: PType
    methods: list = field(default_factory=list)
    script: str = None  # None: interface only
    script_file: str = None


@dataclass
class Decls:
    providers: list
    enums: dict = field(default_factory=dict)  # name -> values
    raw: str = None  # verbatim JSON (a near miss the model does not describe)
    files: dict = field(default_factory=dict)  # extra files (script files)

    def to_json(self) -> str:
        if self.raw is not None:
            return self.raw
        j = {}
        if self.enums:
            j["entityTypes"] = {n: {"enum": vs} for (n, vs) in self.enums.items()}
        av = {}
        for p in self.providers:
            d = {"argumentTypes": [a.to_json() for a in p.args], "outputType": p.output.to_json()}
            if p.methods:
                d["availableMethods"] = {}
                for m in p.methods:
                    md = {"argumentTypes": [a.to_json() for a in m.args], "outputType": m.output.to_json()}
                    if m.input is not None:
                        md["inputType"] = m.input.to_json()
                    d["availableMethods"][m.name] = md
            if p.script is not None:
                d["implementation"] = {"kind": "rhai", "script": p.script}
            elif p.script_file is not None:
                d["implementation"] = {"kind": "rhai", "scriptFile": p.script_file}
            av[p.name] = d
        j["availableProviders"] = av
        return json.dumps(j, indent=2, ensure_ascii=False) + "\n"


# ─── Generation ────────────────────────────────────────────────────────────


def gen_ptype(g, depth, enums, allow_entity=True) -> PType:
    k = g.weighted([("string", 4), ("integer", 3), ("long", 1), ("bool", 3), ("boolean", 1),
                    ("decimal", 2), ("set", 1 if depth > 0 else 0), ("record", 1 if depth > 0 else 0),
                    ("entity", 1 if (allow_entity and enums) else 0)])
    if k == "set":
        return PType("set", items=gen_ptype(g, depth - 1, enums, allow_entity) if g.p(0.8) else None)
    if k == "record":
        return PType("record", fields=gen_fields(g, depth - 1, enums))
    if k == "entity":
        return PType("entity", entity=g.choice(list(enums)))
    return PType(k)


def gen_fields(g, depth, enums):
    names = g.sample(["matched", "score", "count", "allowed", "label", "level", "severity", "ok",
                      "total", "flags"], g.choice([1, 1, 2, 3]))
    if g.p(0.15, "providers:odd_field_name"):
        names.append(g.choice(ODD_FIELDS))
    out = []
    for n in names:
        t = gen_ptype(g, depth, enums)
        out.append((n, t, not g.p(0.15, "providers:optional_output_field")))
    return out


def gen_decls(g, w, knobs) -> Decls:
    n = g.choice([1, 1, 2, 3])
    names = set()
    enums = {}
    providers = []
    ns_choices = list(PROVIDER_NS)
    if g.p(0.08, "providers:ns_is_action_ns") and w.home:
        ns_choices = [w.home]
    if g.p(0.05, "providers:nested_ns"):
        ns_choices = ["A::B", "Org::Unit"]
    for _ in range(n):
        ns = g.choice(ns_choices)
        name = f"{ns}::{g.choice(PROVIDER_FN)}"
        if name in names:
            continue
        names.add(name)
        if g.p(0.3, "providers:enum") and not enums:
            ename = f"{ns}::{g.choice(['Severity', 'Level', 'Verdict'])}"
            vals = g.sample(["LOW", "MEDIUM", "HIGH", "CRITICAL"], g.choice([2, 3, 4]))
            if g.p(0.15, "providers:enum_odd_values"):
                vals.append(g.choice(["a b", "x-y", "é"]))
            enums[ename] = vals
        args = [gen_ptype(g, 1, {}, allow_entity=False) for _ in range(g.choice([0, 1, 1, 1, 2, 3]))]
        if g.p(0.1, "providers:unknown_param_kind"):
            args.append(PType("text"))
        if g.p(0.4):
            out = PType("record", fields=gen_fields(g, 1, enums))
        else:
            out = gen_ptype(g, 1, enums)
            g.tag("providers:scalar_output")
        methods = []
        if g.p(0.3, "providers:methods"):
            for mi in range(g.choice([1, 1, 2])):
                mname = g.choice(["max", "normalize", "clamp", "first", "isHigh", "scoreAbove", "pick"])
                if any(m.name == mname for m in methods):
                    continue
                margs = [gen_ptype(g, 0, {}, allow_entity=False) for _ in range(g.choice([0, 0, 1]))]
                mout = gen_ptype(g, 1, enums)
                minput = None
                if g.p(0.3, "providers:method_input_type"):
                    minput = out if g.p(0.7) else gen_ptype(g, 1, {}, allow_entity=False)
                methods.append(Method(mname, margs, mout, minput))
        p = Provider(name, args, out, methods)
        if not g.p(0.08, "providers:interface_only"):
            p.script = gen_script(g, p, enums)
            if g.p(0.15, "providers:script_file"):
                p.script_file = safe_file(name) + ".rhai"
        providers.append(p)
    d = Decls(providers, enums)
    for p in providers:
        if p.script_file is not None:
            d.files[p.script_file] = p.script
            p.script = None
    return d


def safe_file(name):
    return "".join(c if c.isalnum() else "_" for c in name).lower()


def rhai_value(g, t: PType, enums, from_arg=None) -> str:
    """A Rhai expression of declared type `t`; `from_arg` is a Rhai expression the value may
    depend on (an argument), with its declared type."""
    k = t.kind
    dep = from_arg
    if k == "string":
        if dep and dep[1].kind == "string":
            return f'if {dep[0]}.len() > 3 {{ "long" }} else {{ "short" }}'
        return json.dumps(g.choice(["ok", "alice", "x"]))
    if k in ("integer", "long"):
        if dep and dep[1].kind == "string":
            return f"{dep[0]}.len()"
        if dep and dep[1].kind in ("integer", "long"):
            return f"{dep[0]} * 2"
        return str(g.choice([0, 1, 5, 42, 100]))
    if k in ("bool", "boolean"):
        if dep and dep[1].kind == "string":
            return f'{dep[0]}.contains("a")'
        if dep and dep[1].kind in ("integer", "long"):
            return f"{dep[0]} > 3"
        return g.choice(["true", "false"])
    if k == "decimal":
        if dep and dep[1].kind == "string":
            return f'if {dep[0]}.len() > 3 {{ parse_decimal("0.9") }} else {{ parse_decimal("0.1") }}'
        return f'parse_decimal("{g.choice(["0.5", "1.25", "0.1"])}")'
    if k == "set":
        it = t.items or PType("string")
        return "[" + ", ".join(rhai_value(g, it, enums) for _ in range(g.choice([0, 1, 2]))) + "]"
    if k == "record":
        parts = []
        for (n, ft, req) in t.fields:
            if req or g.p(0.5):
                key = n if is_ident(n) else json.dumps(n)
                parts.append(f"{key}: {rhai_value(g, ft, enums, from_arg)}")
        return "#{ " + ", ".join(parts) + " }"
    if k == "entity":
        vals = enums.get(t.entity, ["LOW"])
        if dep and dep[1].kind == "string" and len(vals) > 1:
            return f'if {dep[0]}.contains("a") {{ {json.dumps(vals[0])} }} else {{ {json.dumps(vals[1])} }}'
        return json.dumps(g.choice(vals))
    return '"?"'


def gen_script(g, p: Provider, enums) -> str:
    params = [f"a{i}" for i in range(len(p.args))]
    guard = " || ".join(f'type_of({a}) == "()"' for a in params)
    dep = None
    for (a, t) in zip(params, p.args):
        if t.kind in ("string", "integer", "long"):
            dep = (a, t)
            break
    body = rhai_value(g, p.output, enums, dep)
    lines = [f"fn evaluate({', '.join(params)}) {{"]
    if guard and not g.p(0.1, "providers:script_no_unit_guard"):
        lines.append(f"    if {guard} {{ return {rhai_value(g, p.output, enums)}; }}")
    if g.p(0.05, "providers:script_wrong_output"):
        body = '"not the declared type"'
    lines.append(f"    {body}")
    lines.append("}")
    for m in p.methods:
        mps = ["input"] + [f"b{i}" for i in range(len(m.args))]
        lines.append(f"fn {m.name}({', '.join(mps)}) {{ {rhai_value(g, m.output, enums)} }}")
    return "\n".join(lines) + "\n"


# ─── Calls ─────────────────────────────────────────────────────────────────


def arg_expr(g, t: PType, shape, w, tg_paths):
    """An argument of declared type `t` for a call in a rule of shape `shape`."""
    want = t.cedar()
    cands = []
    for (p, ct, req) in tg_paths:
        if ct == want:
            cands.append(("context." + path_text(p), 4 if req else 1))
    for (n, at, req) in shape.principal_attrs(w):
        if at == want:
            cands.append(("principal." + n, 1))
    lit = literal_for(g, t)
    if lit is not None:
        cands.append((lit, 2))
    if not cands:
        return literal_for(g, t) or '""'
    return g.weighted(cands)


def literal_for(g, t: PType):
    k = t.kind
    if k == "string":
        return json.dumps(g.choice(["alice", "abc", "x"]))
    if k in ("integer", "long"):
        return str(g.choice([0, 1, 7]))
    if k in ("bool", "boolean"):
        return g.choice(["true", "false"])
    if k == "decimal":
        return 'decimal("0.5")'
    if k == "set":
        it = t.items or PType("string")
        e = literal_for(g, it)
        return f"[{e}]" if e is not None else "[]"
    return None


def call_expr(g, p: Provider, d: Decls, shape, w, misses=()):
    """A Cedar expression that calls provider `p` and uses its output."""
    paths = shape.context_paths()
    args = [arg_expr(g, a, shape, w, paths) for a in p.args]
    if "provider_arity" in misses:
        args = args + ['"extra"'] if g.p(0.5) or not args else args[:-1]
        g.tag("miss:provider_arity")
    if "provider_arg_type" in misses and p.args:
        args[0] = g.choice(["principal", "42", "true"]) if p.args[0].kind == "string" else '"wrong"'
        g.tag("miss:provider_arg_type")
    if "provider_context_arg" in misses and p.args:
        args[0] = "context"
        g.tag("miss:provider_context_arg")
    if "provider_optional_arg" in misses and p.args:
        ops = [pp for (pp, ct, req) in paths if not req and ct == p.args[0].cedar()]
        if ops:
            args[0] = "context." + path_text(ops[0])
            g.tag("miss:provider_optional_arg")
    name = p.name
    if "provider_undeclared" in misses:
        name = p.name.rsplit("::", 1)[0] + "::Nope"
        g.tag("miss:provider_undeclared")
    call = f"{name}({', '.join(args)})"
    out = p.output
    if p.methods and g.p(0.6):
        m = g.choice(p.methods)
        margs = [literal_for(g, a) or "1" for a in m.args]
        mname = m.name
        if "provider_method_undeclared" in misses:
            mname = "nosuch"
            g.tag("miss:provider_method_undeclared")
        call += f".{mname}({', '.join(margs)})"
        out = m.output
        g.tag("providers:call_method")
    return use_output(g, call, out, d)


def use_output(g, e, t: PType, d: Decls):
    k = t.kind
    if k == "record" and t.fields:
        (n, ft, req) = g.choice(t.fields)
        if not req:
            g.tag("providers:optional_output_read")
            if g.p(0.6):
                return f"({e} has {attr_access_name(n)} && {use_output(g, project(e, n), ft, d)})"
        return use_output(g, project(e, n), ft, d)
    if k in ("integer", "long"):
        return f"{e} {g.choice(['<', '<=', '>', '>=', '==', '!='])} {g.choice([0, 3, 10, 50])}"
    if k in ("bool", "boolean"):
        return g.choice([e, f"!{e}", f"{e} == true"])
    if k == "string":
        return f"{e} {g.choice(['==', '!='])} {json.dumps(g.choice(['ok', 'long', 'short', 'x']))}"
    if k == "decimal":
        return f'{e}.{g.choice(["lessThan", "greaterThanOrEqual"])}(decimal("0.5"))'
    if k == "set":
        return f"{e}.isEmpty()" if g.p(0.5) else f"{e}.contains({literal_for(g, t.items or PType('string')) or '1'})"
    if k == "entity":
        vals = d.enums.get(t.entity, ["LOW"])
        if g.p(0.3, "providers:enum_in_list"):
            return f"{e} in [{', '.join(f'{t.entity}::{q(v)}' for v in vals[:2])}]"
        return f"{e} == {t.entity}::{q(g.choice(vals))}"
    return f"{e} == {e}"


def project(e, n):
    return f"{e}.{n}" if is_ident(n) and n not in ("in", "if", "has", "like", "is", "then", "else") else f"{e}[{q(n)}]"


def attr_access_name(n):
    return n if is_ident(n) and n not in ("in", "if", "has", "like", "is", "then", "else") else q(n)
