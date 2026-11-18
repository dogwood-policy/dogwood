#!/usr/bin/env python3
"""Summarize the results of generated runs (`run.py`): outcomes per family, disagreements by
check and kind, and the coverage counts of the generator's tags.

Usage: summarize.py DIR [RESULTS.json...]   (all `DIR/results-*.json` when none are named)

A validation disagreement is a *verdict* disagreement when one side reports no error at all and
the other does (the policy set is valid for one and not for the other), and a *category*
disagreement when both reject it, for findings of different categories. A disagreement is
*known* when it is of a kind the conformance README describes, or a reporting difference this
summary names (see `known`); every other disagreement is new.
"""

import collections
import json
import os
import sys

KNOWN_PARAM_KINDS = ["string", "integer", "long", "bool", "boolean", "decimal", "set", "record", "entity"]
TEMPORAL_CATEGORIES = {"event names", "windows", "binders", "unbound variables", "timepoints",
                       "comparison operands", "predicate arguments", "paths", "optional attributes",
                       "pins", "summands", "placement", "safety", "time dependence",
                       "extension types"}


def policy_text(bdir, name):
    try:
        return open(os.path.join(bdir, name, "policy.dw"), encoding="utf-8").read()
    except Exception:
        return ""


def known(key, tags, cats, bdir, name):
    """Why a disagreement is expected, or None."""
    if key.startswith("stamping:"):
        return "stamping: the crate takes the recorded times as given"
    if key == "runtime: missing scope entity":
        return "missing scope entity: the crate adds a bare entity"
    findings = " ".join((cats or {}).get("findings", []))
    if key == "validation cedar: crate only" and (
            "miss:provider_undeclared" in tags or "miss:provider_method_undeclared" in tags):
        return "a cascading Cedar finding for an undeclared provider or method"
    if key == "validation context reads: specification only":
        text = policy_text(bdir, name)
        if "temporal" not in text and not os.path.exists(os.path.join(bdir, name, "providers.json")):
            return "a leafless set reads the context whole: the crate accepts it, `readsContext` rejects it"
    if ("miss:cedar_reads_hoisted" in tags or "nearmiss:cedar_reads_hoisted" in tags) and \
            key.startswith("validation"):
        return "the Cedar part reads a hoisted name: the bridge maps the read to the leaf"
    category = key.split(":")[0][len("validation "):] if key.startswith("validation") else ""
    spec = set((cats or {}).get("spec", []))
    crate_only = key.endswith(": crate only")
    if crate_only and category == "providers" and any(
            "does not match the declared `" in f and not any(
                f"declared `{k}`" in f for k in KNOWN_PARAM_KINDS) for f in (cats or {}).get("findings", [])):
        return "the crate rejects a literal for a parameter of an unknown kind (its stricter rule, WP6b)"
    if crate_only and category == "context reads" and "reads the request context attribute `providers`" in findings:
        return "the Cedar part reads `context.providers`, a name the crate reserves"
    if crate_only and category == "extension types" and "optional attributes" in spec and \
            "reads the optional attribute" in findings:
        return ("an unguarded optional attribute of an unsupported extension type: the crate reports "
                "both, the specification the optional attribute alone")
    if crate_only and category == "optional attributes" and "paths" in spec:
        return "an undeclared path under an unguarded optional attribute: the crate reports both"
    if crate_only and category == "predicate arguments" and "which is a field group" in findings:
        return "an argument for a field group: the crate also types it against the group"
    if crate_only and category == "predicate arguments" and "does not name a declared event" in findings:
        return "a predicate on an undeclared event: the crate also types its arguments"
    if crate_only and "binders" in spec and "binders" in set((cats or {}).get("crate", [])) and \
            category in TEMPORAL_CATEGORIES:
        return "an aggregate or exists with an ill-formed binder: the crate checks inside, the specification does not"
    if key.endswith(": crate only") and "unknown entity type" in findings and key.split(":")[0][11:] in (
            "predicate arguments", "comparison operands"):
        return "the crate types a literal of an undeclared entity type, a cascading finding"
    if key.endswith(": crate only") and "unable to find an applicable action" in findings and \
            key.split(":")[0][11:] in TEMPORAL_CATEGORIES | {"providers"}:
        return "a rule that admits no request environment: the crate checks its leaves, the specification types them in none"
    return None


def load_meta(bdir, name):
    try:
        return json.load(open(os.path.join(bdir, name, "meta.json")))
    except Exception:
        return {"family": "?", "tags": []}


def summarize(out, files, elapsed=None):
    bdir = os.path.join(out, "bundles")
    results = []
    for f in files:
        results.extend(json.load(open(f)))
    metas, outcomes, cats = {}, {}, {}
    for r in results:
        for n in r["bundles"]:
            metas[n] = load_meta(bdir, n)
        outcomes.update(r.get("outcomes", {}))
        for c in r.get("conformance_categories", []):
            cats[c["bundle"].split("/")[-1]] = c
    fam_outcomes = collections.defaultdict(collections.Counter)
    for (n, m) in metas.items():
        fam_outcomes[m["family"]][outcomes.get(n, "not exported")] += 1
    tags = collections.Counter(t for m in metas.values() for t in m["tags"])
    new, old = [], collections.Counter()
    by_check = collections.Counter()
    verdicts = []
    for r in results:
        for d in r["frontend"]:
            n = d["bundle"].split("/")[-1]
            by_check[f"frontend {d['check']}"] += 1
            new.append(("frontend", d["check"], n, d["diff"]))
        for d in r["undecodable"]:
            n = d["bundle"].split("/")[-1]
            by_check[f"frontend undecodable {d['check']}"] += 1
            new.append(("undecodable", d["check"], n, d["why"]))
        for key in ("conformance", "partitioned"):
            for d in r[key]:
                n = d["bundle"].split("/")[-1]
                c = cats.get(n)
                k = known(d["key"], set(metas.get(n, {}).get("tags", [])), c, bdir, n)
                kind = d["key"].split(":")[0]
                if k:
                    old[f"{key}: {k}"] += 1
                    continue
                level = ""
                if d["key"].startswith("validation") or d["key"].startswith("uncategorized"):
                    if c is not None:
                        spec_err = bool(c["spec"])
                        crate_err = bool(c["crate"]) or bool(c["uncategorized"])
                        level = "verdict" if spec_err != crate_err else "categories"
                        if key == "conformance" and level == "verdict":
                            verdicts.append((n, c))
                by_check[f"{key} {kind}{' (' + level + ')' if level else ''}"] += 1
                new.append((key, d["key"] + (f" [{level}]" if level else ""), n,
                            "" if c is None else f"spec {c['spec']} crate {c['crate']}"))
        for d in r["crashes"]:
            by_check[f"bridge crash ({d['export']})"] += 1
            new.append(("crash", d["export"], d["bundle"], " / ".join(d["why"])))
        for d in r.get("timeouts", []):
            n = d["bundle"].split("/")[-1]
            by_check[f"harness timeout ({d['harness']})"] += 1
            new.append(("timeout", d["harness"], n, ""))
        for e in r["errors"]:
            by_check["harness error"] += 1
            new.append(("error", "", "", e))
    lines = []
    total = len(metas)
    lines.append(f"{total} bundles" + (f", {elapsed:.0f} s" if elapsed else ""))
    lines.append("\nOutcomes of the crate's pipeline, per family:")
    for fam in sorted(fam_outcomes):
        c = fam_outcomes[fam]
        lines.append(f"  {fam:10} {sum(c.values()):6}  " + ", ".join(f"{k} {v}" for (k, v) in c.most_common()))
    lowered = [c for c in cats.values()]
    if lowered:
        both_ok = sum(1 for c in lowered if not c["spec"] and not c["crate"] and not c["uncategorized"])
        lines.append(f"\nValidation of the {len(lowered)} lowered bundles: {both_ok} valid for both, "
                     f"{len(lowered) - both_ok} rejected by at least one side")
        spec_cats = collections.Counter(x for c in lowered for x in c["spec"])
        crate_cats = collections.Counter(x for c in lowered for x in c["crate"])
        lines.append("  bundles with findings, specification/crate: " + ", ".join(
            f"{k} {spec_cats[k]}/{crate_cats[k]}" for k in sorted(set(spec_cats) | set(crate_cats))))
    lines.append(f"\nNew disagreements: {len(new)}")
    for (k, v) in by_check.most_common():
        lines.append(f"  {k}: {v}")
    lines.append(f"Known kinds: {sum(old.values())}")
    for (k, v) in old.most_common():
        lines.append(f"  {k}: {v}")
    if verdicts:
        lines.append("\nVerdict disagreements of validation (one side accepts):")
        for (n, c) in verdicts[:50]:
            lines.append(f"  {n}: spec {c['spec']} crate {c['crate']} uncategorized {c['uncategorized'][:1]}")
    lines.append("\nNew disagreements (first 300):")
    for (src, what, n, d) in new[:300]:
        lines.append(f"  [{src}] {what} {n} {metas.get(n, {}).get('family', '')}: {d[:300]}")
    lines.append("\nCoverage (tag: bundles):")
    for (t, c) in sorted(tags.items()):
        lines.append(f"  {t}: {c}")
    text = "\n".join(lines)
    with open(os.path.join(out, "summary.txt"), "w") as f:
        f.write(text + "\n")
    with open(os.path.join(out, "summary.json"), "w") as f:
        json.dump({"bundles": total, "outcomes": {k: dict(v) for (k, v) in fam_outcomes.items()},
                   "new": new, "known": dict(old), "by_check": dict(by_check), "tags": dict(tags)}, f, indent=1)
    return text, bool(new)


if __name__ == "__main__":
    out = sys.argv[1]
    files = sys.argv[2:] or sorted(os.path.join(out, f) for f in os.listdir(out) if f.startswith("results-"))
    text, bad = summarize(out, files)
    print(text)
    sys.exit(1 if bad else 0)
