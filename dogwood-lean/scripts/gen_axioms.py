#!/usr/bin/env python3
"""Generate Axioms.lean: `#print axioms` for every theorem of the Dogwood library."""
import os, re, sys
root = sys.argv[1]
mods = []
names = []
for dirpath, _, files in os.walk(os.path.join(root, "Dogwood")):
    for f in sorted(files):
        if not f.endswith(".lean"): continue
        path = os.path.join(dirpath, f)
        rel = os.path.relpath(path, root)[:-5].replace(os.sep, ".")
        if rel.startswith("Dogwood.Conformance"): continue
        mods.append(rel)
        ns = []
        depth = 0  # nesting depth of block comments
        for line in open(path):
            if depth > 0 or line.lstrip().startswith("/-"):
                depth += line.count("/-") - line.count("-/")
                if depth < 0: depth = 0
                continue
            m = re.match(r"^namespace\s+(\S+)", line)
            if m: ns.append(m.group(1)); continue
            m = re.match(r"^end\s+(\S+)\s*$", line)
            if m and ns and ns[-1] == m.group(1): ns.pop(); continue
            m = re.match(r"^(?:private\s+)?theorem\s+(\S+)", line)
            if m and not line.startswith("private"):
                n = m.group(1)
                if n.startswith("_root_."): full = n[len("_root_."):]
                else: full = ".".join(ns + [n])
                names.append((rel, full))
out = ["import Dogwood", "",
       "/-!",
       "`lake env lean Axioms.lean` prints the axioms every theorem of the specification rests on.",
       "Only `propext`, `Classical.choice` and `Quot.sound` may appear. The file is generated from",
       "the library (`scripts/gen_axioms.py`): it names every theorem, module by module.",
       "-/", ""]
cur = None
for rel, full in names:
    if rel != cur:
        out.append(""); out.append(f"-- {rel}"); cur = rel
    out.append(f"#print axioms {full}")
open(os.path.join(root, "Axioms.lean"), "w").write("\n".join(out) + "\n")
print(len(names), "theorems")
