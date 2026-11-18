"""Traces for replay: events of the derived signatures, with several principals, timestamps at
the edges of the policies' windows, and (rarely) equal or decreasing timestamps and nonconforming
events."""

from __future__ import annotations

from model import (LONG_POOL, STR_POOL, Ty, World, is_ident, leaves, q, trace_key, value_text)


def render_value(v) -> str:
    if isinstance(v, dict):
        if not v:
            return "{}"
        return "{ " + ", ".join(f"{trace_key(k)}: {render_value(x)}" for (k, x) in v.items()) + " }"
    return v


def record_value(g, t: Ty, w: World, strings, optional_p=0.6):
    """A nested dict of value texts for record type `t`."""
    out = {}
    for (n, at, req) in t.attrs:
        if not req and g.r.random() > optional_p:
            continue
        if at.is_record():
            out[n] = record_value(g, at, w, strings, optional_p)
        else:
            out[n] = value_text(g.r, at, w, strings)
    return out


def get_path(d, path):
    for s in path:
        if not isinstance(d, dict) or s not in d:
            return None
        d = d[s]
    return d


def set_path(d, path, v):
    for s in path[:-1]:
        d = d.setdefault(s, {})
        if not isinstance(d, dict):
            return
    d[path[-1]] = v


def entity_value(g, w, fq, uid_id, strings):
    e = w.entity(fq)
    if e is None or e.enum is not None:
        return None
    attrs = record_value(g, Ty("Record", attrs=tuple(e.attrs)), w, strings) if e.attrs else {}
    return attrs


def gen_trace(g, w: World, events, es, windows, knobs) -> str:
    """One trace: lines of events."""
    n = g.choice([2, 3, 4, 5, 6, 8, 10, 12])
    if g.p(0.05, "trace:long"):
        n = g.choice([20, 30])
    strings = STR_POOL[:3] if g.p(0.6) else STR_POOL
    decisions = [e for e in events if e.decision]
    history = [e for e in events if not e.decision]
    ts = g.choice([0, 0, 100, 1000000, 1700000000])
    if g.p(0.03, "trace:extreme_timestamps"):
        ts = g.choice([-1000, 9223372036, 9223372030, 10 ** 12, 4102444800, -9223372036])
    gaps = [1, 1, 2, 5, 10, 30, 60, 600]
    if g.p(0.03, "trace:huge_gaps"):
        gaps += [10 ** 9, 86400 * 365, 9223372036]
    for wsec in windows:
        if 0 < wsec < 10 ** 10:
            gaps += [wsec - 1, wsec, wsec + 1, wsec]
    principals = list(w.ids.get(w.principals[0], ["alice"]))[: g.choice([1, 2, 3, 3])] if w.principals else ["alice"]
    lines = []
    equal_p = knobs.get("equal_ts", 0.03)
    decreasing_p = knobs.get("decreasing_ts", 0.015)
    nonconf_p = knobs.get("nonconforming", 0.02)
    for i in range(n):
        if i > 0:
            if g.p(equal_p, "trace:equal_timestamp"):
                pass
            elif g.p(decreasing_p, "trace:decreasing_timestamp"):
                ts -= g.choice([1, 5, 100])
            else:
                ts += g.choice(gaps)
        last = i == n - 1
        pool = decisions if (last or g.p(0.4)) and decisions else (history or decisions)
        if not pool:
            pool = events
        e = g.choice(pool)
        lines.append(gen_event(g, w, e, es, ts, g.choice(principals), strings, nonconf_p))
    if len({ln.split(" ", 1)[0] for ln in lines}) > 1 and len(principals) > 1:
        g.tag("trace:several_principals")
    return "\n".join(lines) + "\n"


def gen_event(g, w: World, e, es, ts, pid, strings, nonconf_p) -> str:
    a = e.action
    ptype = g.choice(a.principals)
    rtype = g.choice(a.resources)
    p_ids = w.ids_of(ptype)
    pid = pid if pid in p_ids else g.choice(p_ids)
    rid = g.choice(w.ids_of(rtype))
    p_uid = f"{ptype}::{q(pid)}"
    r_uid = f"{rtype}::{q(rid)}"
    ctx = record_value(g, a.context, w, strings) if a.context else {}
    scopeless = (not e.decision) and g.p(nonconf_p, "trace:scopeless_history")
    # The logged record.
    logged = {}
    for l in e.leaves:
        v = None
        if l.origin in ("input", "output"):
            v = get_path(ctx, l.path)
            if v is None and l.required:
                v = value_text(g.r, l.ty, w, strings) if isinstance(l.ty, Ty) else p_uid
            if v is None:
                continue
        elif l.path == ("callerPrincipal",):
            if scopeless:
                continue
            v = p_uid
        elif l.path == ("callerResource",):
            if scopeless:
                continue
            v = r_uid
        elif isinstance(l.ty, tuple):
            names = l.ty[1]
            v = p_uid if ptype in names else (r_uid if rtype in names else f"{names[0]}::{q('x')}")
        elif l.path[-1] == "requestId":
            v = q(f"r{ts}")
        elif l.path[-1] in ("sessionId", "session_id"):
            v = q(g.choice(["s1", "s2"]))
        else:
            if not l.required and g.p(0.3):
                continue
            v = value_text(g.r, l.ty, w, strings)
        set_path(logged, l.path, v)
    # Pins: the logged field holds the request-side value.
    for (fp, root, rp) in e.pins:
        if root == "principal":
            if not rp:
                v = p_uid
            else:
                pe = entity_value(g, w, ptype, pid, strings)
                v = None
        elif root == "resource":
            v = r_uid if not rp else None
        else:
            v = get_path(ctx, rp)
            if v is None:
                v = q(g.choice(["s1", "s2"]))
                set_path(ctx, rp, v)
        if v is not None and not scopeless:
            set_path(logged, fp, v)
    # Entities.
    ents = []
    if not g.p(0.04, "trace:no_entity_data"):
        pv = entity_value(g, w, ptype, pid, strings)
        if pv is not None:
            # Pins on principal attributes read the entity's attribute.
            for (fp, root, rp) in e.pins:
                if root == "principal" and rp and rp[0] in pv:
                    set_path(logged, fp, pv[rp[0]])
            parents = ""
            pe = w.entity(ptype)
            if pe is not None and pe.parents and g.p(0.7):
                parents = f" in [{pe.parents[0]}::{q(g.choice(w.ids_of(pe.parents[0])))}]"
                g.tag("trace:entity_parents")
            ents.append(f"{p_uid}: {render_value(pv)}{parents}")
        rv = entity_value(g, w, rtype, rid, strings)
        if rv is not None and (rv or g.p(0.5)):
            parents = ""
            re_ = w.entity(rtype)
            if re_ is not None and re_.parents and g.p(0.7):
                parents = f" in [{re_.parents[0]}::{q(g.choice(w.ids_of(re_.parents[0])))}]"
            ents.append(f"{r_uid}: {render_value(rv)}{parents}")
    # Nonconforming variants, rarely.
    if g.p(nonconf_p, "trace:nonconforming_logged"):
        ls = [l for l in e.leaves if l.origin == "input" and isinstance(l.ty, Ty) and l.ty.kind == "String"]
        if ls:
            set_path(logged, ls[0].path, "7")
    if g.p(nonconf_p / 2, "trace:caller_mismatch"):
        # Log another principal as the caller, under any name a principal pin gives the field.
        callers = [fp for (fp, root, rp) in e.pins if root == "principal" and not rp]
        if "callerPrincipal" in logged:
            callers.append(("callerPrincipal",))
        for fp in callers:
            if get_path(logged, fp) is not None:
                set_path(logged, fp, f"{ptype}::{q('mallory')}")
    if g.p(nonconf_p / 2, "trace:nonconforming_context") and "input" in ctx and isinstance(ctx["input"], dict) and ctx["input"]:
        k = next(iter(ctx["input"]))
        del ctx["input"][k]
    head = f"@{ts}"
    if not scopeless:
        head += f" scope(principal: {p_uid}, resource: {r_uid})"
    if ents and not scopeless:
        head += f" entities({', '.join(ents)})"
    if ctx or g.p(0.5):
        head += f" request_context({', '.join(f'{trace_key(k)}: {render_value(v)}' for (k, v) in ctx.items())})"
    body = ", ".join(f"{trace_key(k)}: {render_value(v)}" for (k, v) in logged.items())
    return f"{head} {a.uid}::{e.kind}({body})"
