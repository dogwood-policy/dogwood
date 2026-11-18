"""Random action schemas (`World`s), with the knobs the bundle families turn.

Each generated world records the tags of the features it uses (`tags`), which the driver counts.
"""

from __future__ import annotations

from model import (BOOL, DECIMAL, LONG, STRING, Action, EntityType, Namespace, Ty, World, base_of,
                   ent, join_ns, ns_of, prim, rec, render_ty, setof)

NS_POOL = ["Drupe", "Acme", "Svc", "Repo", "Shop"]
NESTED_NS_POOL = ["A::B", "Org::Unit", "X::Y::Z"]
PRINCIPAL_POOL = ["User", "OAuthUser", "Bot", "Admin", "Service"]
RESOURCE_POOL = ["Gateway", "Doc", "Bucket", "Server", "Repo"]
ACTION_POOL = ["Login", "Logout", "Read", "Write", "Transfer", "Approve", "Heartbeat", "Compute",
               "Grant", "Revoke", "Open", "Close"]
ODD_ACTION_IDS = ["read file", "get-item", "Ä", "a.b", "x y z", "Read2", "_", 'q"uote', "back\\slash", "::"]
ID_POOL = ["alice", "bob", "carol"]
RESOURCE_IDS = ["gw1", "gw2", "d1"]

INPUT_FIELDS = [
    ("user", STRING), ("document", STRING), ("server", STRING), ("amount", LONG), ("level", LONG),
    ("flag", BOOL), ("doc", STRING), ("count", LONG), ("score", DECIMAL),
]
ODD_INPUT_FIELDS = [("user.id", STRING), ("content-type", STRING), ("in", STRING), ("if", LONG),
                    ("_x", STRING), ("Ä", STRING)]
OUTPUT_FIELDS = [("result", BOOL), ("amount", LONG), ("status", STRING), ("total", LONG)]


class Gen:
    """A random source with the bundle's tags."""

    def __init__(self, r, tags):
        self.r = r
        self.tags = tags

    def p(self, prob: float, tag: str = None) -> bool:
        hit = self.r.random() < prob
        if hit and tag:
            self.tags.add(tag)
        return hit

    def choice(self, xs):
        return self.r.choice(xs)

    def sample(self, xs, k):
        return self.r.sample(xs, min(k, len(xs)))

    def weighted(self, pairs):
        tot = sum(w for (_, w) in pairs)
        x = self.r.random() * tot
        for (v, w) in pairs:
            x -= w
            if x < 0:
                return v
        return pairs[-1][0]

    def tag(self, t: str):
        self.tags.add(t)


def gen_world(g: Gen, knobs: dict) -> World:
    """A random action schema. `knobs` may force: `layout` (single, root, two, root_commons,
    nested), `multi_principal`, `groups`, `enum`, `odd_names`, `context_ref`, `common_types`,
    `n_actions`."""
    layout = knobs.get("layout") or g.weighted([("single", 70), ("root", 8), ("two", 10),
                                                 ("root_commons", 7), ("nested", 5)])
    g.tag(f"schema:layout:{layout}")
    if layout == "single":
        names = [g.choice(NS_POOL)]
    elif layout == "root":
        names = [""]
    elif layout == "two":
        names = g.sample(NS_POOL, 2)
    elif layout == "root_commons":
        names = ["", g.choice(NS_POOL)]
    else:
        names = [g.choice(NESTED_NS_POOL)]
    w = World(namespaces=[Namespace(n) for n in names])
    # The namespace that holds the actions, and the one that holds the entity types.
    act_ns = names[-1]
    ent_ns = names[0] if layout == "two" and g.p(0.5, "schema:entities_in_other_ns") else act_ns
    home = w.ns(act_ns)
    ens = w.ns(ent_ns)

    # Entity types.
    np = 1 + (g.p(knobs.get("multi_principal", 0.25), "schema:multi_principal") and 1) + (
        g.p(0.05, "schema:three_principals") and 1)
    pnames = g.sample(PRINCIPAL_POOL, np)
    rnames = g.sample(RESOURCE_POOL, 1 + (g.p(0.2, "schema:multi_resource") and 1))
    group = None
    if g.p(knobs.get("groups", 0.3), "schema:entity_hierarchy"):
        group = EntityType(ent_ns, g.choice(["Group", "Team"]))
        if g.p(0.3, "schema:group_of_groups"):
            group.parents = [group.fq]
        ens.entities.append(group)
        w.ids[group.fq] = ["staff", "eng"]
    enum = None
    if g.p(knobs.get("enum", 0.2), "schema:enum"):
        enum = EntityType(ent_ns, g.choice(["Level", "Tier", "Color"]), enum=["low", "high", "mid"])
        if g.p(0.2, "schema:enum_odd_eids"):
            enum.enum = ["low", "a b", "é", 'q"t']
        ens.entities.append(enum)
    principals = []
    for pn in pnames:
        e = EntityType(ent_ns, pn)
        attrs = []
        if g.p(0.4, "schema:principal_id_attr"):
            attrs.append(("id", g.choice([STRING, STRING, LONG]), True))
        if g.p(0.6):
            attrs.append(("level", LONG, g.p(0.8) or bool(g.tag("schema:optional_entity_attr"))))
        if g.p(0.4):
            attrs.append(("dept", STRING, True))
        if enum is not None and g.p(0.5, "schema:enum_attr"):
            attrs.append(("tier", ent(enum.fq), True))
        if g.p(0.15, "schema:entity_record_attr"):
            attrs.append(("profile", rec(("age", LONG, True), ("country", STRING, g.p(0.5))), True))
        if g.p(0.15, "schema:entity_set_attr"):
            attrs.append(("roles", setof(STRING), True))
        if g.p(0.1, "schema:entity_decimal_attr"):
            attrs.append(("score", DECIMAL, True))
        e.attrs = attrs
        if g.p(0.3, "schema:tags"):
            e.tags = STRING
        if group is not None and g.p(0.7):
            e.parents = [group.fq]
        principals.append(e)
        ens.entities.append(e)
        w.ids[e.fq] = list(ID_POOL)
        if g.p(0.03, "schema:odd_entity_ids"):
            w.ids[e.fq] = ["alice", 'o"brien', "é"]
    for pe in principals:
        if g.p(0.1, "schema:entity_ref_attr"):
            pe.attrs.append(("manager", ent(principals[0].fq), True))
    if enum is not None and g.p(0.05, "schema:enum_principal"):
        principals.append(enum)
    resources = []
    folder = None
    if g.p(0.15, "schema:resource_hierarchy"):
        folder = EntityType(ent_ns, "Folder")
        ens.entities.append(folder)
        w.ids[folder.fq] = ["prod", "dev"]
    for rn in rnames:
        e = EntityType(ent_ns, rn)
        if g.p(0.4):
            e.attrs = [("owner", STRING, True)]
            if g.p(0.3):
                e.attrs.append(("size", LONG, g.p(0.7)))
        if folder is not None:
            e.parents = [folder.fq]
        resources.append(e)
        ens.entities.append(e)
        w.ids[e.fq] = list(RESOURCE_IDS)

    # Actions.
    n_actions = knobs.get("n_actions") or g.choice([2, 2, 3, 3, 4, 5])
    ids = g.sample(ACTION_POOL, n_actions)
    if g.p(knobs.get("odd_names", 0.08), "schema:odd_action_id"):
        ids[-1] = g.choice(ODD_ACTION_IDS)
    act_group = None
    if g.p(knobs.get("action_groups", 0.2), "schema:action_group"):
        act_group = Action(act_ns, g.choice(["readActions", "all", "writes"]))
        if g.p(0.3, "schema:action_group_nested"):
            top = Action(act_ns, "everything")
            home.actions.append(top)
            act_group.groups = [(act_ns, top.id)]
        home.actions.append(act_group)
    commons_ns = names[0] if layout in ("root_commons", "two") else act_ns
    cns = w.ns(commons_ns)
    for aid in ids:
        a = Action(act_ns, aid)
        a.principals = [p.fq for p in (g.sample(principals, g.choice([1, len(principals)])) if
                                         len(principals) > 1 else principals)]
        a.resources = [x.fq for x in (g.sample(resources, g.choice([1, len(resources)])) if
                                        len(resources) > 1 else resources)]
        fields = g.sample(INPUT_FIELDS, g.choice([1, 2, 2, 3, 4]))
        if not any(n == "user" for (n, _) in fields) and g.p(0.6):
            fields = [("user", STRING)] + fields
        if g.p(knobs.get("odd_names", 0.08), "schema:odd_input_name"):
            fields.append(g.choice(ODD_INPUT_FIELDS))
        in_attrs = []
        for (fn, ft) in fields:
            in_attrs.append((fn, ft, not g.p(0.15, "schema:optional_input")))
        if g.p(0.1, "schema:input_set"):
            in_attrs.append(("items", setof(STRING), True))
        if g.p(0.1, "schema:input_entity"):
            in_attrs.append(("owner", ent(principals[0].fq), True))
        if enum is not None and g.p(0.2, "schema:input_enum"):
            in_attrs.append(("tier", ent(enum.fq), True))
        if g.p(0.12, "schema:input_nested_record"):
            in_attrs.append(("meta", rec(("region", STRING, True), ("id", STRING, g.p(0.8))), True))
        if g.p(0.05, "schema:input_datetime"):
            in_attrs.append(("when", prim("datetime"), True))
        if g.p(0.03, "schema:input_ipaddr"):
            in_attrs.append(("ip", prim("ipaddr"), True))
        in_attrs = dedup(in_attrs)
        input_ty = rec(*in_attrs)
        ctx_attrs = [("input", input_ty, not g.p(0.03, "schema:optional_input_record"))]
        if g.p(0.5):
            out = g.sample(OUTPUT_FIELDS, g.choice([1, 1, 2]))
            ctx_attrs.append(("output", rec(*[(n, t, not g.p(0.1)) for (n, t) in out]),
                              not g.p(0.2, "schema:optional_output")))
        if g.p(0.08, "schema:context_system"):
            ctx_attrs.append(("system", rec(("now", prim("datetime"), True)), True))
        if g.p(0.08, "schema:context_extra_attr"):
            ctx_attrs.append(("level", LONG, g.p(0.7)))
        if g.p(0.03, "schema:no_input"):
            ctx_attrs = [x for x in ctx_attrs if x[0] != "input"]
        a.context = rec(*ctx_attrs)
        # How the input record and the context are written.
        if g.p(knobs.get("common_types", 0.5), "schema:input_common_type") and any(
                n == "input" for (n, _, _) in ctx_attrs):
            cname = f"{safe_ident(aid)}Input"
            if not any(c == cname for (c, _) in cns.commons):
                cns.commons.append((cname, render_ty(input_ty, commons_ns)))
            if commons_ns == act_ns:
                a.attr_refs["input"] = cname
            elif commons_ns == "":
                a.attr_refs["input"] = cname  # bare: resolves in the root namespace
                g.tag("schema:root_common_type_bare")
            else:
                a.attr_refs["input"] = join_ns(commons_ns, cname)
                g.tag("schema:cross_ns_common_type")
        if g.p(knobs.get("context_ref", 0.1), "schema:context_common_type"):
            cname = f"{safe_ident(aid)}Ctx"
            parts = []
            for (an, at, req) in a.context.attrs:
                tt = a.attr_refs.get(an) or render_ty(at, act_ns)
                parts.append(f"{an}{'' if req else '?'}: {tt}")
            home.commons.append((cname, "{ " + ", ".join(parts) + " }"))
            a.context_ref = cname
        if act_group is not None and g.p(0.7):
            a.groups = [(act_ns, act_group.id)]
        home.actions.append(a)
    w.principals = [p.fq for p in principals]
    w.resources = [x.fq for x in resources]
    w.home = act_ns
    w.group = group.fq if group else None
    w.enum = enum.fq if enum else None
    w.act_group = (act_ns, act_group.id) if act_group else None
    return w


def dedup(attrs):
    seen, out = set(), []
    for a in attrs:
        if a[0] not in seen:
            seen.add(a[0])
            out.append(a)
    return out


def safe_ident(s: str) -> str:
    t = "".join(c if (c.isascii() and (c.isalnum() or c == "_")) else "_" for c in s)
    if not t or t[0].isdigit():
        t = "A" + t
    return t[0].upper() + t[1:]
