"""Event schemas: generation, rendering, and the derivation of event signatures from a world.

The derivation here models the crate's (`event_schema/derive.rs`) on the worlds the generator
builds, so that policies and traces can name the derived fields with their types.
"""

from __future__ import annotations

from dataclasses import dataclass, field
from typing import Optional

from model import (BOOL, LONG, STRING, Ty, World, ent, leaves, lookup, prim, rec)

DEFAULT_KINDS = [("request", True), ("response", False), ("error", False)]


@dataclass
class Named:
    name: str
    ty: tuple  # ("principalType",) | ("resourceType",) | ("concrete", text, Ty) | ("record", [fields])
    pin: Optional[tuple] = None  # ("principal"|"resource", path) | ("context", path)
    pin_marker: bool = True  # write `pin` (a near miss drops it, or keeps `pin` without a value)
    pin_value: bool = True


@dataclass
class Spread:
    sel: str  # inputs | outputs | principalType | resourceType (the last two are near misses)
    binder: Optional[str] = None


@dataclass
class Decl:
    kind: str
    decision: bool
    fields: list
    binder: str = "A"


@dataclass
class EventSchema:
    decls: list
    max_window: Optional[str] = None  # e.g. "1h"
    builtin: Optional[str] = None  # "default": write no file (the bridge's default); "unpinned"
    raw: Optional[str] = None  # verbatim text (a near miss the model does not describe)

    def kinds(self):
        return [d.kind for d in self.decls]

    def decision_kinds(self):
        return sorted({d.kind for d in self.decls if d.decision})

    def window_seconds(self) -> int:
        return seconds(self.max_window) if self.max_window else 86400


UNITS = {"s": 1, "m": 60, "h": 3600, "d": 86400}


def seconds(w: str) -> int:
    return int(w[:-1]) * UNITS[w[-1]]


def default_decls(pinned: bool):
    def fields(kind):
        fs = [Spread("inputs")]
        if kind == "response":
            fs.append(Spread("outputs"))
        fs.append(Named("callerPrincipal", ("principalType",),
                        ("principal", ()) if pinned else None))
        fs.append(Named("callerResource", ("resourceType",)))
        fs.append(Named("requestId", ("concrete", "String", STRING)))
        fs.append(Named("sessionId", ("concrete", "String", STRING)))
        return fs
    return [Decl(k, d, fields(k)) for (k, d) in DEFAULT_KINDS]


def builtin_schema(which: str) -> EventSchema:
    return EventSchema(default_decls(which == "default"), builtin=which)


def render_pin(pin) -> str:
    root, path = pin
    return ".".join((root,) + tuple(path))


def render_fields(fs, binder) -> str:
    out = []
    for f in fs:
        if isinstance(f, Spread):
            out.append(f"...{f.sel}({f.binder or binder})")
            continue
        if f.ty[0] in ("principalType", "resourceType"):
            t = f"{f.ty[0]}({binder})"
        elif f.ty[0] == "concrete":
            t = f.ty[1]
        else:
            t = "{ " + render_fields(f.ty[1], binder) + " }" if f.ty[1] else "{}"
        s = ("pin " if f.pin is not None and f.pin_marker else "") + f"{f.name}: {t}"
        if f.pin is not None and f.pin_value:
            s += " = " + render_pin(f.pin)
        out.append(s)
    return ", ".join(out)


def render_event_schema(es: EventSchema) -> Optional[str]:
    if es.raw is not None:
        return es.raw
    if es.builtin == "default":
        return None
    out = []
    if es.max_window:
        out.append(f"max_window = {es.max_window}")
    for d in es.decls:
        head = f"{'decision ' if d.decision else ''}event <{d.binder}>::{d.kind} "
        if not d.fields:
            out.append(head + "{}")
            continue
        out.append(head + "{\n    " + render_fields(d.fields, d.binder).replace(", ", ",\n    ") + ",\n}")
    return "\n\n".join(out) + "\n"


# ─── Derivation ────────────────────────────────────────────────────────────


@dataclass
class Leaf:
    path: tuple
    ty: object  # a Ty, or ("EntityTypes", [qualified names])
    required: bool
    origin: str  # "input" | "output" | "named"

    def single(self) -> Optional[Ty]:
        """The leaf's type, when it is one Cedar type."""
        if isinstance(self.ty, tuple):
            return ent(self.ty[1][0]) if len(self.ty[1]) == 1 else None
        return self.ty

    def admits_entity(self, fq: str) -> bool:
        if isinstance(self.ty, tuple):
            return fq in self.ty[1]
        return self.ty.kind == "Entity" and self.ty.name == fq


@dataclass
class Event:
    action: object  # model.Action
    kind: str
    decision: bool
    leaves: list
    pins: list  # (field path, root, ref path)

    def leaf(self, path) -> Optional[Leaf]:
        for l in self.leaves:
            if l.path == tuple(path):
                return l
        return None


def concrete_ty(text: str, w: World) -> Ty:
    if text in ("String", "Long", "Bool", "decimal", "datetime", "duration", "ipaddr"):
        return prim(text)
    return ent(text)


def derive(es: EventSchema, w: World) -> list:
    """The derived events: per appliable action (namespaces in the world's order, then actions),
    per declaration. Returns `Event`s."""
    out = []
    for a in w.appliable():
        for d in es.decls:
            ls, pins = [], []
            derive_fields(d.fields, (), a, w, ls, pins, True)
            out.append(Event(a, d.kind, d.decision, ls, pins))
    return out


def derive_fields(fs, prefix, a, w, ls, pins, required):
    for f in fs:
        if isinstance(f, Spread):
            if f.sel not in ("inputs", "outputs"):
                continue
            group = "input" if f.sel == "inputs" else "output"
            sub = a.context.attr(group) if a.context else None
            if sub is None:
                continue
            t, req = sub
            for (p, lt, lreq) in leaves(t):
                ls.append(Leaf(prefix + (group,) + p, lt, req and lreq and required, group))
            continue
        p = prefix + (f.name,)
        if f.ty[0] == "principalType":
            ls.append(Leaf(p, ("EntityTypes", list(a.principals)), required, "named"))
        elif f.ty[0] == "resourceType":
            ls.append(Leaf(p, ("EntityTypes", list(a.resources)), required, "named"))
        elif f.ty[0] == "concrete":
            ls.append(Leaf(p, f.ty[2], required, "named"))
        else:
            derive_fields(f.ty[1], p, a, w, ls, pins, required)
        if f.pin is not None:
            pins.append((p, f.pin[0], tuple(f.pin[1])))


def universal_pins(es: EventSchema):
    """The universal symmetric pins of the schema, as `(field path, root, ref path)`."""
    if not es.decls:
        return []

    def sym(d):
        out = set()
        ls, ps = [], []
        stack = [((), d.fields)]
        while stack:
            pre, fs = stack.pop()
            for f in fs:
                if isinstance(f, Named):
                    p = pre + (f.name,)
                    if f.ty[0] == "record":
                        stack.append((p, f.ty[1]))
                    if f.pin is not None:
                        root, rp = f.pin
                        # A pin to a context attribute, or to the bare principal or resource,
                        # is symmetric whatever the field is called.
                        if root == "context" or not rp:
                            out.add((p, root, tuple(rp)))
        return out
    common = sym(es.decls[0])
    for d in es.decls[1:]:
        common &= sym(d)
    return sorted(common)


def gen_event_schema(g, w: World, knobs: dict) -> EventSchema:
    """A random event schema for world `w`. It may add context attributes to `w`'s actions so
    that its context pins have a request-side value."""
    which = knobs.get("event_schema") or g.weighted([("default", 45), ("unpinned", 15),
                                                      ("custom", 40)])
    g.tag(f"events:{which}")
    if which in ("default", "unpinned"):
        es = builtin_schema(which)
        if which == "unpinned":
            es.builtin = None
            if g.p(0.2, "events:max_window"):
                es.max_window = g.choice(["1h", "2h", "30m", "7d", "48h", "90s", "1d"])
        return es
    kinds = [("request", True)]
    extra = g.sample([("response", False), ("error", False), ("attempt", True), ("outcome", False),
                      ("audit", False), ("ping", g.p(0.3))], g.choice([0, 1, 1, 2, 3]))
    kinds += extra
    if g.p(0.1, "events:request_not_decision"):
        kinds[0] = ("request", False)
    if g.p(0.05, "events:no_request_kind"):
        kinds = kinds[1:] or [("attempt", True)]
    # Which pins, on which kinds.
    pin_principal = g.p(0.55, "events:pin_principal")
    pin_resource = g.p(0.12, "events:pin_resource")
    ctx_pin = None
    if g.p(0.15, "events:pin_context"):
        ctx_pin = g.choice([("sessionId",), ("__drupe", "session_id"), ("tenant",)])
    attr_pin = None
    if g.p(0.08, "events:pin_principal_attr"):
        attr_pin = g.choice([("dept",), ("level",)])
    renamed = g.p(0.08, "events:renamed_principal_field")
    universal = g.p(0.8)
    decls = []
    for i, (k, dec) in enumerate(kinds):
        on = universal or i == 0 or g.p(0.5)
        if not on:
            g.tag("events:non_universal_pin")
        fs = []
        if k != "ping" or g.p(0.5):
            fs.append(Spread("inputs"))
        if k in ("response", "outcome") and g.p(0.9):
            fs.append(Spread("outputs"))
        pname = "actor" if renamed else "callerPrincipal"
        if not (renamed and g.p(0.1)):
            fs.append(Named(pname, ("principalType",),
                            ("principal", ()) if (pin_principal and on) else None))
        if g.p(0.85):
            fs.append(Named("callerResource", ("resourceType",),
                            ("resource", ()) if (pin_resource and on) else None))
        if g.p(0.8):
            fs.append(Named("requestId", ("concrete", "String", STRING)))
        if ctx_pin is not None:
            if len(ctx_pin) == 1:
                fs.append(Named(ctx_pin[0], ("concrete", "String", STRING),
                                ("context", ctx_pin) if on else None))
            else:
                fs.append(Named(ctx_pin[0], ("record", [Named(ctx_pin[1], ("concrete", "String", STRING),
                                                              ("context", ctx_pin) if on else None)])))
        elif g.p(0.5):
            fs.append(Named("sessionId", ("concrete", "String", STRING)))
        if attr_pin is not None and on:
            fs.append(Named("who_" + attr_pin[0], ("concrete", "String" if attr_pin[0] == "dept" else "Long",
                                                    STRING if attr_pin[0] == "dept" else LONG),
                            ("principal", attr_pin)))
        if g.p(0.1, "events:nested_named_record"):
            fs.append(Named("meta", ("record", [Named("region", ("concrete", "String", STRING)),
                                                Named("deep", ("record", [Named("x", ("concrete", "Long", LONG))]))])))
        if g.p(0.06, "events:spread_in_record"):
            fs.append(Named("wrap", ("record", [Spread("inputs")])))
        if g.p(0.05, "events:entity_named_field") and w.principals:
            fs.append(Named("owner", ("concrete", w.principals[0], ent(w.principals[0]))))
        if g.p(0.04, "events:named_field_is_pin"):
            fs.append(Named("pin", ("concrete", "String", STRING)))
        if g.p(0.03, "events:contextual_keyword_fields"):
            fs.append(Named(g.choice(["event", "decision", "max_window", "inputs"]), ("concrete", "String", STRING)))
        if g.p(0.05, "events:empty_decl"):
            fs = []
        binder = g.choice(["A", "A", "A", "Act", "X"])
        decls.append(Decl(k, dec, fs, binder))
    es = EventSchema(decls)
    if g.p(0.25, "events:max_window"):
        es.max_window = g.choice(["1h", "2h", "30m", "7d", "48h", "90s", "1d", "3600s"])
        if g.p(0.1, "events:max_window_huge"):
            es.max_window = g.choice(["106751d", "106752d", "9223372036s", "9223372037s", "999999999d",
                                      "153722867m", "2562047h"])
    # Give the actions the context attributes the context pins read.
    if ctx_pin is not None and not g.p(0.1, "events:context_pin_unbacked"):
        for a in w.appliable():
            if a.context_ref is not None:
                continue
            if len(ctx_pin) == 1:
                add_attr(a, ctx_pin[0], STRING, not g.p(0.05, "events:context_pin_optional"))
            else:
                add_attr(a, ctx_pin[0], rec((ctx_pin[1], STRING, True)), True)
    return es


def add_attr(a, name, ty, required):
    if a.context.attr(name) is None:
        a.context = rec(*(list(a.context.attrs) + [(name, ty, required)]))
