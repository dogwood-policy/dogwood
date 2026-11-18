"""Cedar types, action schemas, and their values, as the bundle generator models them.

A `World` is an action schema: namespaces with common types, entity types and actions. The
generator builds one at random, renders it as `.cedarschema` text, and keeps, for every type it
writes, the type it means (`Ty`), so that policies and traces can be typed against it without a
Cedar name resolver. Where a bundle deliberately writes a schema whose names resolve otherwise
(a near miss), the model may be wrong about that bundle; the harnesses compare the two
implementations on it all the same.
"""

from __future__ import annotations

import json
from dataclasses import dataclass, field
from typing import Optional

PRIMS = ("String", "Long", "Bool")
EXTS = ("decimal", "datetime", "duration", "ipaddr")


@dataclass(frozen=True)
class Ty:
    """A Cedar type. `kind` is one of the primitives and extension types, `Entity` (with the
    entity type's qualified name), `Set` (with its element type), or `Record` (with its
    attributes, `(name, type, required)`)."""

    kind: str
    name: str = ""
    elem: Optional["Ty"] = None
    attrs: tuple = ()

    def is_record(self) -> bool:
        return self.kind == "Record"

    def attr(self, name: str):
        for (n, t, req) in self.attrs:
            if n == name:
                return (t, req)
        return None


def prim(k: str) -> Ty:
    return Ty(k)


def ent(fq: str) -> Ty:
    return Ty("Entity", name=fq)


def setof(t: Ty) -> Ty:
    return Ty("Set", elem=t)


def rec(*attrs) -> Ty:
    return Ty("Record", attrs=tuple(attrs))


STRING, LONG, BOOL, DECIMAL = prim("String"), prim("Long"), prim("Bool"), prim("decimal")


def is_ident(s: str) -> bool:
    if not s or not (s[0].isalpha() or s[0] == "_") or not s.isascii():
        return False
    return all(c.isalnum() or c == "_" for c in s)


CEDAR_RESERVED = {"true", "false", "if", "then", "else", "in", "like", "has", "is", "__cedar"}


def attr_name(n: str) -> str:
    """An attribute name as a Cedar schema writes it: bare, or quoted."""
    return n if is_ident(n) and n not in CEDAR_RESERVED else q(n)


def q(s: str) -> str:
    """A Cedar string literal."""
    out = []
    for c in s:
        if c == '"':
            out.append('\\"')
        elif c == "\\":
            out.append("\\\\")
        elif c == "\n":
            out.append("\\n")
        elif c == "\t":
            out.append("\\t")
        else:
            out.append(c)
    return '"' + "".join(out) + '"'


def ns_of(fq: str) -> str:
    return fq.rsplit("::", 1)[0] if "::" in fq else ""


def base_of(fq: str) -> str:
    return fq.rsplit("::", 1)[-1]


def join_ns(ns: str, name: str) -> str:
    return f"{ns}::{name}" if ns else name


# ─── The schema ────────────────────────────────────────────────────────────


@dataclass
class EntityType:
    ns: str
    name: str
    attrs: list = field(default_factory=list)  # (name, Ty, required)
    tags: Optional[Ty] = None
    parents: list = field(default_factory=list)  # qualified names
    enum: Optional[list] = None
    # How the attribute record is written: inline, or the name of a common type.
    attrs_ref: Optional[str] = None
    annotations: list = field(default_factory=list)

    @property
    def fq(self) -> str:
        return join_ns(self.ns, self.name)


@dataclass
class Action:
    ns: str
    id: str
    groups: list = field(default_factory=list)  # (ns, id) of the action groups it is in
    principals: list = field(default_factory=list)  # qualified entity type names
    resources: list = field(default_factory=list)
    context: Optional[Ty] = None  # the context record (resolved); None: no appliesTo
    # How the context is written: None (inline), or a common-type reference's text.
    context_ref: Optional[str] = None
    # Per context attribute, the text a common type reference writes for it (inline otherwise).
    attr_refs: dict = field(default_factory=dict)

    @property
    def uid(self) -> str:
        return f"{join_ns(self.ns, 'Action')}::{q(self.id)}"

    def applies(self) -> bool:
        return self.context is not None


@dataclass
class Namespace:
    name: str
    commons: list = field(default_factory=list)  # (name, text) in declaration order
    entities: list = field(default_factory=list)
    actions: list = field(default_factory=list)
    extra: list = field(default_factory=list)  # raw declarations appended verbatim


@dataclass
class World:
    namespaces: list
    # Entity ids used for each entity type in policies and traces.
    ids: dict = field(default_factory=dict)
    raw_prefix: str = ""  # text written before the namespaces (verbatim)

    def ns(self, name: str) -> Namespace:
        for n in self.namespaces:
            if n.name == name:
                return n
        raise KeyError(name)

    def entities(self):
        for n in self.namespaces:
            yield from n.entities

    def entity(self, fq: str) -> Optional[EntityType]:
        for e in self.entities():
            if e.fq == fq:
                return e
        return None

    def actions(self):
        for n in self.namespaces:
            yield from n.actions

    def appliable(self):
        return [a for a in self.actions() if a.applies()]

    def action(self, ns: str, id: str) -> Optional[Action]:
        for a in self.actions():
            if a.ns == ns and a.id == id:
                return a
        return None

    def ancestors(self, a: Action) -> list:
        """The action groups `a` is in, transitively, as `(ns, id)` pairs."""
        seen, todo = [], list(a.groups)
        while todo:
            g = todo.pop()
            if g in seen:
                continue
            seen.append(g)
            ga = self.action(*g)
            if ga is not None:
                todo.extend(ga.groups)
        return seen

    def entity_ancestors(self, fq: str) -> list:
        seen, todo = [], list((self.entity(fq).parents if self.entity(fq) else []))
        while todo:
            p = todo.pop()
            if p in seen:
                continue
            seen.append(p)
            e = self.entity(p)
            if e is not None:
                todo.extend(e.parents)
        return seen

    def ids_of(self, fq: str) -> list:
        e = self.entity(fq)
        if e is not None and e.enum is not None:
            return list(e.enum)
        return self.ids.get(fq, ["a", "b"])


def render_ty(t: Ty, home: str) -> str:
    """The text of a type, written in namespace `home`."""
    if t.kind in PRIMS or t.kind in EXTS:
        return t.kind
    if t.kind == "Entity":
        return base_of(t.name) if ns_of(t.name) == home else t.name
    if t.kind == "Set":
        return f"Set<{render_ty(t.elem, home)}>"
    if t.kind == "Record":
        if not t.attrs:
            return "{}"
        parts = [f"{attr_name(n)}{'' if req else '?'}: {render_ty(ty, home)}" for (n, ty, req) in t.attrs]
        return "{ " + ", ".join(parts) + " }"
    if t.kind == "Text":  # a type written verbatim (a common-type reference)
        return t.name
    raise ValueError(t)


def text(s: str) -> Ty:
    """A type written verbatim (a reference), whose meaning the caller tracks separately."""
    return Ty("Text", name=s)


def render_world(w: World) -> str:
    out = [w.raw_prefix] if w.raw_prefix else []
    for n in w.namespaces:
        body = []
        for (cname, ctext) in n.commons:
            body.append(f"type {cname} = {ctext};")
        for e in n.entities:
            ann = "".join(f"@{k}({q(v)}) " for (k, v) in e.annotations)
            if e.enum is not None:
                body.append(f"{ann}entity {e.name} enum [{', '.join(q(v) for v in e.enum)}];")
                continue
            s = f"{ann}entity {e.name}"
            if e.parents:
                s += " in [" + ", ".join(base_of(p) if ns_of(p) == n.name else p for p in e.parents) + "]"
            if e.attrs_ref is not None:
                s += f" = {e.attrs_ref}"
            elif e.attrs:
                s += " = " + render_ty(rec(*e.attrs), n.name)
            if e.tags is not None:
                s += f" tags {render_ty(e.tags, n.name)}"
            body.append(s + ";")
        for a in n.actions:
            s = f"action {q(a.id)}"
            if a.groups:
                gs = []
                for (gns, gid) in a.groups:
                    gs.append(q(gid) if gns == n.name else f"{join_ns(gns, 'Action')}::{q(gid)}")
                s += " in [" + ", ".join(gs) + "]"
            if a.applies():
                ps = ", ".join(base_of(p) if ns_of(p) == n.name else p for p in a.principals)
                rs = ", ".join(base_of(p) if ns_of(p) == n.name else p for p in a.resources)
                if a.context_ref is not None:
                    ctx = a.context_ref
                else:
                    parts = []
                    for (an, at, req) in a.context.attrs:
                        tt = a.attr_refs.get(an) or render_ty(at, n.name)
                        parts.append(f"{attr_name(an)}{'' if req else '?'}: {tt}")
                    ctx = "{ " + ", ".join(parts) + " }" if parts else "{}"
                s += f" appliesTo {{\n    principal: [{ps}],\n    resource: [{rs}],\n    context: {ctx}\n  }}"
            body.append(s + ";")
        body.extend(n.extra)
        inner = "\n".join("  " + line for line in "\n".join(body).split("\n"))
        if n.name:
            out.append(f"namespace {n.name} {{\n{inner}\n}}")
        else:
            out.append("\n".join(body))
    return "\n".join(out) + "\n"


# ─── Leaves of a record, and values ─────────────────────────────────────────


def leaves(t: Ty, prefix=(), required=True):
    """The leaves of a record type: `(path, type, required)`, a record attribute being a group."""
    out = []
    if t is None or not t.is_record():
        return out
    for (n, at, req) in t.attrs:
        p = prefix + (n,)
        if at.is_record():
            out.extend(leaves(at, p, required and req))
        else:
            out.append((p, at, required and req))
    return out


def lookup(t: Ty, path):
    """The type at `path` in record `t`, and whether every attribute along it is required."""
    req = True
    for seg in path:
        if t is None or not t.is_record():
            return None
        a = t.attr(seg)
        if a is None:
            return None
        t, r = a
        req = req and r
    return (t, req)


# The values literals and traces draw from: a few ordinary ones, so that policies and traces
# match often, repeated so that the edge values after them are drawn rarely (each with
# probability about 1/300). Slices from the front (`STR_POOL[:3]`) draw ordinary values only.
_STR = ["alice", "bob", "carol", "s1", "doc1", "x"]
_LONG = [0, 1, 2, 3, 5, 10, 50, 100, 150, 1000]
_DEC = ["0.5", "1.5", "0.1", "2.25", "-1.0"]
STR_EDGES = ["", 'a"b', "back\\slash", "é", "日本", "line\nbreak", " pad ", "*", "x" * 64, "o'brien"]
LONG_EDGES = [-1, 9223372036854775807, -9223372036854775807, 4611686018427387904, -2]
DEC_EDGES = ["922337203685477.5807", "-922337203685477.5807", "0.0000", "1.2345", "-0.0001"]
STR_POOL = _STR + _STR * 49 + STR_EDGES
LONG_POOL = _LONG + _LONG * 29 + LONG_EDGES
DEC_POOL = _DEC + _DEC * 59 + DEC_EDGES


def value_text(r, t: Ty, w: World, strings=None) -> str:
    """A value of type `t`, as a trace writes it."""
    strings = strings or STR_POOL
    k = t.kind
    if k == "String":
        return q(r.choice(strings))
    if k == "Long":
        return str(r.choice(LONG_POOL))
    if k == "Bool":
        return r.choice(["true", "false"])
    if k == "decimal":
        return f'decimal("{r.choice(DEC_POOL)}")'
    if k == "datetime":
        return r.choice(['datetime("2024-01-01T00:00:00Z")', 'datetime("2024-06-01")'])
    if k == "duration":
        return r.choice(['duration("1h")', 'duration("30m")'])
    if k == "ipaddr":
        return r.choice(['ip("10.0.0.1")', 'ip("192.168.0.0/16")'])
    if k == "Entity":
        return f"{t.name}::{q(r.choice(w.ids_of(t.name)))}"
    if k == "Set":
        n = r.choice([0, 1, 1, 2])
        return "[" + ", ".join(value_text(r, t.elem, w, strings) for _ in range(n)) + "]"
    if k == "Record":
        parts = []
        for (n, at, req) in t.attrs:
            if req or r.random() < 0.6:
                parts.append(f"{trace_key(n)}: {value_text(r, at, w, strings)}")
        return "{ " + ", ".join(parts) + " }" if parts else "{}"
    return '"?"'


def trace_key(n: str) -> str:
    return n if is_ident(n) else q(n)


def literal_text(r, t: Ty, w: World, strings=None) -> Optional[str]:
    """A literal of type `t` as the temporal sub-language writes it, if it has one."""
    strings = strings or STR_POOL
    k = t.kind
    if k == "String":
        return q(r.choice(strings))
    if k == "Long":
        return str(r.choice(LONG_POOL))
    if k == "Bool":
        return r.choice(["true", "false"])
    if k == "decimal":
        return f'decimal("{r.choice(DEC_POOL)}")'
    if k == "Entity":
        return f"{t.name}::{q(r.choice(w.ids_of(t.name)))}"
    return None


def cedar_literal(r, t: Ty, w: World) -> Optional[str]:
    """A literal of type `t` in Cedar's syntax, if it has one."""
    k = t.kind
    if k in ("String", "Long", "Bool", "Entity"):
        return literal_text(r, t, w)
    if k == "decimal":
        return f'decimal("{r.choice(DEC_POOL)}")'
    if k == "datetime":
        return 'datetime("2024-01-01")'
    if k == "duration":
        return 'duration("1h")'
    if k == "ipaddr":
        return 'ip("10.0.0.1")'
    if k == "Set":
        e = cedar_literal(r, t.elem, w)
        return f"[{e}]" if e is not None else None
    return None
