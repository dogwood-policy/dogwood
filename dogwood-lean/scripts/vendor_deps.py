#!/usr/bin/env python3
"""Vendor the Lean dependencies of the specification and the Lean frontend (`vendor/`).

The `dogwood-language` crate's `lean-frontend` feature builds the Lean frontend's
library, `Dogwood.Frontend.Library` and every module it imports (the lakefile's
`frontendFfi` target), and `lake build` checks the whole specification, `Dogwood`
and every module it imports (the default target: its proofs and examples too).
Some of those modules are cedar-lean's and Batteries', which Lake clones from the
network into `.lake/packages`. The crate's `build.rs` uses this pinned export
instead when the project has no `.lake/packages`, so that it needs no network
access:

    vendor/cedar-lean/   package Cedar       cedar-spec <rev>, subdirectory cedar-lean
    vendor/batteries/    package batteries   batteries <rev>

The revisions are the ones `lake-manifest.json` records. Each vendored package holds
exactly the modules the two libraries import from it, transitively, and its configuration
(`lakefile.lean` or `lakefile.toml`, `lake-manifest.json`, `lean-toolchain`), its
`LICENSE` and, where the repository has one, its `NOTICE`: each file is the upstream
file at the pinned revision, byte for byte. `vendor/MANIFEST` records the origins and
the SHA-256 digest of every vendored file, and a digest of itself.

Usage:
    scripts/vendor_deps.py write   # re-export the closure (deletes vendored files no longer needed)
    scripts/vendor_deps.py check   # the export is the MANIFEST's and the closure, byte for byte
    scripts/vendor_deps.py check --offline

`check --offline` needs no upstream repository: it checks that every vendored file has
the MANIFEST's digest, that the MANIFEST's pins are `lake-manifest.json`'s, and that
the vendored modules are exactly those the library imports, transitively (reading
the library's modules from `Dogwood/` and the vendored ones from `vendor/`). `write`
and `check` read the upstream repositories with `git show <rev>:<path>` (never their
working trees), from `.lake/packages/<name>` (where Lake clones them), or from
`$DOGWOOD_VENDOR_CEDAR_REPO` and `$DOGWOOD_VENDOR_BATTERIES_REPO`.
"""

import hashlib
import json
import os
import re
import subprocess
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
VENDOR = os.path.join(ROOT, "vendor")
MANIFEST = os.path.join(VENDOR, "MANIFEST")

# The library's root modules: `Dogwood`, which the lakefile's default target builds (the
# specification, its proofs and its examples), and the Lean frontend's library, which its
# `frontendFfi` target builds (the archive).
LIBRARIES = ["Dogwood", "Dogwood.Frontend.Library"]

# The vendored packages: (top-level module, vendored directory, Lake package name, the
# repository override's environment variable, the files of the repository root to vendor
# besides the package's own, if present).
PACKAGES = [
    ("Cedar", "cedar-lean", "Cedar", "DOGWOOD_VENDOR_CEDAR_REPO", ["LICENSE", "NOTICE"]),
    ("Batteries", "batteries", "batteries", "DOGWOOD_VENDOR_BATTERIES_REPO", ["LICENSE", "NOTICE"]),
]

# The package's own configuration files, vendored when the package has them.
CONFIG = ["lakefile.lean", "lakefile.toml", "lake-manifest.json", "lean-toolchain"]

# The toolchain's own libraries, which are not vendored.
TOOLCHAIN = {"Init", "Std", "Lean", "Lake"}

IMPORT = re.compile(r"^(?:(?:public|private|meta)\s+)*import\s+(.*)$")


def fail(message):
    sys.exit(f"vendor_deps: {message}")


def pins():
    """{Lake package name: (revision, subdirectory or "", url)} from lake-manifest.json."""
    with open(os.path.join(ROOT, "lake-manifest.json"), encoding="utf-8") as h:
        manifest = json.load(h)
    out = {}
    for p in manifest["packages"]:
        if p.get("type") != "git":
            fail(f"package {p['name']} of lake-manifest.json is not a git dependency")
        out[p["name"]] = (p["rev"], p.get("subDir") or "", p["url"])
    for pkg in PACKAGES:
        if pkg[2] not in out:
            fail(f"lake-manifest.json has no package {pkg[2]}")
    return out


def strip_comments(text):
    """`text` without its comments (`--` to the end of the line, and nested `/- … -/`)."""
    out = []
    i, depth, n = 0, 0, len(text)
    while i < n:
        if text.startswith("/-", i):
            depth += 1
            i += 2
        elif depth and text.startswith("-/", i):
            depth -= 1
            i += 2
        elif depth:
            if text[i] == "\n":
                out.append("\n")
            i += 1
        elif text.startswith("--", i):
            while i < n and text[i] != "\n":
                i += 1
        else:
            out.append(text[i])
            i += 1
    return "".join(out)


def imports(data):
    """The modules a Lean file's header imports."""
    mods = []
    for line in strip_comments(data.decode("utf-8")).splitlines():
        line = line.strip()
        if not line or line in ("module", "prelude"):
            continue
        m = IMPORT.match(line)
        if not m:
            break  # the header ends at the first command
        mods += [t for t in m.group(1).split() if t != "all"]
    return mods


def mod_path(mod):
    return mod.replace(".", "/") + ".lean"


def package_of(mod):
    top = mod.split(".")[0]
    if top in TOOLCHAIN:
        return None
    if top == "Dogwood":
        return "own"
    for p in PACKAGES:
        if p[0] == top:
            return p
    fail(f"{mod}: a module of no known package")


def repo(pkg):
    return os.path.expanduser(
        os.environ.get(pkg[3], os.path.join(ROOT, ".lake", "packages", pkg[2])))


def git_show(pkg, rev, path):
    out = subprocess.run(["git", "-C", repo(pkg), "show", f"{rev}:{path}"],
                         capture_output=True, check=False)
    return out.stdout if out.returncode == 0 else None


def own(mod):
    with open(os.path.join(ROOT, mod_path(mod)), "rb") as h:
        return h.read()


def closure(read):
    """{(vendored dir, path in the package): bytes} of the modules the library imports,
    transitively, from the vendored packages; `read(pkg, path)` reads a package's file."""
    seen, out, stack = set(), {}, list(LIBRARIES)
    while stack:
        mod = stack.pop()
        if mod in seen:
            continue
        seen.add(mod)
        pkg = package_of(mod)
        if pkg is None:
            continue
        if pkg == "own":
            stack += imports(own(mod))
            continue
        data = read(pkg, mod_path(mod))
        if data is None:
            fail(f"{mod} is not in {pkg[2]}")
        out[(pkg[1], mod_path(mod))] = data
        stack += imports(data)
    return out


def upstream():
    """{(vendored dir, path): bytes} the export must hold: the closure, read from upstream at
    the pins, with each package's configuration, license and notice."""
    pinned = pins()

    def read(pkg, path):
        rev, sub, _ = pinned[pkg[2]]
        return git_show(pkg, rev, f"{sub}/{path}" if sub else path)

    files = closure(read)
    for pkg in PACKAGES:
        rev, _, _ = pinned[pkg[2]]
        for f in CONFIG:
            data = read(pkg, f)
            if data is not None:
                files[(pkg[1], f)] = data
        for f in pkg[4]:
            data = git_show(pkg, rev, f)
            if data is not None:
                files[(pkg[1], f)] = data
        if (pkg[1], "LICENSE") not in files:
            fail(f"{pkg[2]} has no LICENSE at {rev}")
    return files


def manifest_text(files):
    pinned = pins()
    body = [
        "# A pinned export of the Lean packages the specification and the Lean frontend import, for a",
        "# build without network access (written by scripts/vendor_deps.py; see its",
        "# documentation). Each file is the upstream file at the revision, byte for byte.",
        "# origin <vendored dir> <Lake package> <revision> <subdirectory> <repository>",
    ]
    for pkg in PACKAGES:
        rev, sub, url = pinned[pkg[2]]
        body.append(f"origin {pkg[1]} {pkg[2]} {rev} {sub or '.'} {url}")
    body.append("# sha256 <SHA-256> <path under vendor/>")
    for (d, p) in sorted(files):
        body.append(f"sha256 {hashlib.sha256(files[(d, p)]).hexdigest()} {d}/{p}")
    text = "\n".join(body) + "\n"
    return text + f"tree-sha256 {hashlib.sha256(text.encode('utf-8')).hexdigest()}\n"


def on_disk():
    out = {}
    for d, dirs, fs in os.walk(VENDOR):
        dirs[:] = [x for x in dirs if x != ".lake"]
        for f in fs:
            full = os.path.join(d, f)
            rel = os.path.relpath(full, VENDOR)
            if rel == "MANIFEST":
                continue
            top, _, rest = rel.partition(os.sep)
            with open(full, "rb") as h:
                out[(top, rest.replace(os.sep, "/"))] = h.read()
    return out


def write():
    files = upstream()
    have = on_disk()
    for key in sorted(set(have) - set(files)):
        os.remove(os.path.join(VENDOR, key[0], key[1]))
    for (d, p), data in sorted(files.items()):
        path = os.path.join(VENDOR, d, p)
        os.makedirs(os.path.dirname(path), exist_ok=True)
        with open(path, "wb") as h:
            h.write(data)
    with open(MANIFEST, "w", encoding="utf-8") as h:
        h.write(manifest_text(files))
    for pkg in PACKAGES:
        mods = sum(1 for (d, p) in files if d == pkg[1] and p.endswith(".lean")
                   and p not in CONFIG)
        print(f"{pkg[2]}: {mods} modules")


def check(offline):
    with open(MANIFEST, encoding="utf-8") as h:
        text = h.read()
    body, _, last = text.rstrip("\n").rpartition("\n")
    if not last.startswith("tree-sha256 ") or \
            hashlib.sha256((body + "\n").encode("utf-8")).hexdigest() != last.split()[1]:
        fail("MANIFEST's tree digest does not match its body")
    listed, origins = {}, {}
    for line in body.splitlines():
        if line.startswith("sha256 "):
            _, h, path = line.split(" ", 2)
            d, _, p = path.partition("/")
            listed[(d, p)] = h
        elif line.startswith("origin "):
            _, d, name, rev, sub, url = line.split(" ")
            origins[name] = (rev, "" if sub == "." else sub, url)
    have = on_disk()
    bad = sorted(k for k in listed
                 if k not in have or hashlib.sha256(have[k]).hexdigest() != listed[k])
    extra = sorted(k for k in have if k not in listed)
    if bad or extra:
        fail(f"the vendored files are not the MANIFEST's: {(bad + extra)[:20]}")
    if origins != pins():
        fail("the MANIFEST's pins are not lake-manifest.json's; run `vendor_deps.py write`")

    def read(pkg, path):
        return have.get((pkg[1], path))

    needed = set(closure(read))
    modules = {k for k in have if k[1].endswith(".lean") and k[1] not in CONFIG}
    if needed != modules:
        fail(f"the vendored modules are not the library's imports: missing "
             f"{sorted(needed - modules)[:10]}, unused {sorted(modules - needed)[:10]}; "
             "run `vendor_deps.py write`")
    if offline:
        print(f"vendor/: {len(have)} files, the MANIFEST's, and the library's imports")
        return
    files = upstream()
    diff = sorted(k for k in set(files) | set(have) if files.get(k) != have.get(k))
    if diff:
        fail(f"the vendored tree is not upstream's at the pins: {diff[:20]}")
    print(f"vendor/: {len(have)} files, the closure at the pins, byte for byte")


if __name__ == "__main__":
    cmd = sys.argv[1:] or ["check"]
    if cmd[0] == "write":
        write()
    elif cmd[0] == "check":
        check("--offline" in cmd)
    else:
        sys.exit(__doc__)
