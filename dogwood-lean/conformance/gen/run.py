#!/usr/bin/env python3
"""Generate bundles, export them with the bridge, run both harnesses, and summarize.

Usage: run.py --seed S --count N --out DIR [--start I] [--chunk K] [--jobs J] [--keep-json]
              [--family F]... [--no-partitioned] [--timeout S] [--spans]

For each chunk of K bundles (in parallel, J at a time):

1. `gen.py` writes the bundles to `DIR/bundles/`;
2. the bridge exports them twice: with `--frontend` (`DIR/json/F<c>.json`), and in the default mode
   (`DIR/json/C<c>.json`, the crate's verdicts from the crate's own temporal engine); and the
   bridge's `partitioned` binary exports them a third time (`DIR/json/P<c>.json`, the crate's
   verdicts with temporal state partitioned by the universal pins);
3. `frontend-diff` compares the Lean frontend with the crate stage by stage on `F<c>`, and
   `conformance` compares the specification with the crate on `C<c>` and `P<c>`.

A bundle on which the bridge fails (a panic, a stack overflow) is found by bisection, recorded,
and left out of its chunk. The run writes `DIR/summary.txt` and `DIR/summary.json`: per family,
how the crate's pipeline ended (lowered, or the stage that rejected the bundle); every
disagreement, by check and by kind; and the coverage counts of the generator's tags. The
baselines of the repository apply, so a probe's known disagreement is expected here too. Exit
status: 0 when nothing disagrees unexpectedly, 1 otherwise.
"""

import argparse
import concurrent.futures as cf
import json
import os
import re
import shutil
import subprocess
import sys
import time

HERE = os.path.dirname(os.path.abspath(__file__))
LEAN = os.path.dirname(os.path.dirname(HERE))  # dogwood-lean
BRIDGE = os.path.join(LEAN, "bridge", "target", "release", "dogwood-lean-bridge")
PART = os.path.join(LEAN, "bridge", "target", "release", "partitioned")
FDIFF = os.path.join(LEAN, ".lake", "build", "bin", "frontend-diff")
CONF = os.path.join(LEAN, ".lake", "build", "bin", "conformance")


def sh(cmd, log=None, timeout=3600):
    p = subprocess.run(cmd, capture_output=True, text=True, timeout=timeout)
    if log is not None:
        with open(log, "w") as f:
            f.write(p.stdout)
            f.write(p.stderr)
    return p


def export(binary, dirs, out, frontend):
    """Export `dirs` to `out`; returns the dirs the bridge failed on (found by bisection)."""
    cmd = [binary] + (["--frontend"] if frontend else []) + ["--out", out] + dirs
    p = subprocess.run(cmd, capture_output=True, text=True, timeout=3600)
    if p.returncode == 0:
        return []
    if len(dirs) == 1:
        return [(dirs[0], (p.stderr or p.stdout).strip().splitlines()[-3:])]
    mid = len(dirs) // 2
    bad = export(binary, dirs[:mid], out + ".a", frontend) + export(binary, dirs[mid:], out + ".b", frontend)
    good = [d for d in dirs if d not in {b for (b, _) in bad}]
    for suffix in (".a", ".b"):
        if os.path.exists(out + suffix):
            os.remove(out + suffix)
    if good:
        p = subprocess.run([binary] + (["--frontend"] if frontend else []) + ["--out", out] + good,
                           capture_output=True, text=True, timeout=3600)
        if p.returncode != 0:
            return bad + [(d, ["retry failed"]) for d in good]
    return bad


def harness(cmd, path, writes, timeout):
    """Run a harness executable on the group file `path`; on a timeout, split the group and
    run the halves, down to single bundles. `writes` maps an output-file flag of the executable
    (`--write-baseline`, `--write-categories`) to the prefix its lines get in the returned text.
    Returns the output text, those lines, failures prefixed `HARNESS-ERROR `, and the names of
    the bundles on which the harness timed out alone."""
    if not os.path.exists(path):
        return "HARNESS-ERROR missing export " + os.path.basename(path) + "\n", []
    files = {flag: f"{path}.{i}.out" for (i, flag) in enumerate(writes)}
    full = list(cmd) + sum(([flag, f] for (flag, f) in files.items()), []) + [path]
    try:
        p = subprocess.run(full, capture_output=True, text=True, timeout=timeout)
    except subprocess.TimeoutExpired:
        recs = json.load(open(path))
        if len(recs) <= 1:
            return "", [r.get("name", "?") for r in recs]
        mid = len(recs) // 2
        texts, slow = [], []
        for (i, part) in enumerate((recs[:mid], recs[mid:])):
            pp = f"{path[:-5]}_{i}.json"
            with open(pp, "w") as f:
                json.dump(part, f)
            t, sl = harness(cmd, pp, writes, max(60, timeout // 2))
            texts.append(t)
            slow += sl
            os.remove(pp)
        return "\n".join(texts), slow
    text = p.stdout
    if p.returncode == 2:
        text += "\nHARNESS-ERROR " + (p.stderr or "").strip().replace("\n", " / ")[:2000] + "\n"
    elif "does not decode" in (p.stderr or ""):
        text += "\nHARNESS-ERROR " + "; ".join(l for l in p.stderr.splitlines() if "decode" in l)[:2000] + "\n"
    for (flag, f) in files.items():
        if os.path.exists(f):
            text += "\n" + "".join(writes[flag] + " " + l for l in open(f) if l.strip())
            os.remove(f)
    return text, []


DIFF_RE = re.compile(r"^  (\S+) disagrees on (\S+): (.*)$")
UNDEC_RE = re.compile(r"^  (\S+) cannot decode (\S+): (.*)$")


def run_chunk(args, c, start, count, baselines):
    out = args.out
    bdir = os.path.join(out, "bundles")
    jdir = os.path.join(out, "json")
    ldir = os.path.join(out, "logs")
    cmd = [sys.executable, os.path.join(HERE, "gen.py"), "--seed", str(args.seed), "--start", str(start),
           "--count", str(count), "--out", bdir]
    for f in args.family or []:
        cmd += ["--family", f]
    subprocess.run(cmd, check=True)
    names = sorted(n for n in os.listdir(bdir) if n.startswith(f"s{args.seed}_") and
                   start <= int(n.split("_")[1]) < start + count)
    dirs = [os.path.join(bdir, n) for n in names]
    res = {"chunk": c, "bundles": names, "crashes": [], "frontend": [], "undecodable": [],
           "conformance": [], "partitioned": [], "errors": [], "timeouts": []}
    tag = f"{c:04d}"
    fjson, cjson, pjson = (os.path.join(jdir, f"{k}{tag}.json") for k in ("F", "C", "P"))
    for (binary, path, frontend, key) in ((BRIDGE, fjson, True, "F"), (BRIDGE, cjson, False, "C")) + (
            ((PART, pjson, False, "P"),) if args.partitioned else ()):
        for (d, why) in export(binary, dirs, path, frontend):
            res["crashes"].append({"bundle": os.path.basename(d), "export": key, "why": why})
    # The frontend harness.
    out_text, slow = harness([FDIFF, "--diffs", "1000000"] + (["--spans"] if args.spans else []) +
                             sum((["--baseline", b] for b in baselines["frontend"]), []), fjson, {}, args.timeout)
    with open(os.path.join(ldir, f"frontend{tag}.log"), "w") as f:
        f.write(out_text)
    res["timeouts"] = [{"harness": "frontend", "bundle": n} for n in slow]
    for line in out_text.splitlines():
        m = DIFF_RE.match(line)
        if m:
            res["frontend"].append({"check": m.group(1), "bundle": m.group(2), "diff": m.group(3)[:2000]})
        m = UNDEC_RE.match(line)
        if m:
            res["undecodable"].append({"check": m.group(1), "bundle": m.group(2), "why": m.group(3)[:500]})
        if line.startswith("HARNESS-ERROR"):
            res["errors"].append("frontend-diff: " + line[len("HARNESS-ERROR "):][:2000])
    # The conformance harness, on both exports of the verdicts.
    for (path, key) in ((cjson, "conformance"), (pjson, "partitioned")):
        if key == "partitioned" and not args.partitioned:
            continue
        out_text, slow = harness([CONF, "--baseline", baselines["conformance"]], path,
                                 {"--write-baseline": "BASELINE", "--write-categories": "CATEGORIES"},
                                 args.timeout)
        res[key + "_categories"] = []
        with open(os.path.join(ldir, f"{key}{tag}.log"), "w") as f:
            f.write(out_text)
        res["timeouts"] += [{"harness": key, "bundle": n} for n in slow]
        for line in out_text.splitlines():
            if line.startswith("CATEGORIES "):
                res[key + "_categories"].append(json.loads(line[len("CATEGORIES "):]))
            elif line.startswith("BASELINE "):
                parts = line[len("BASELINE "):].strip().split(" | ")
                if len(parts) == 3:
                    res[key].append({"bundle": parts[1], "key": parts[2]})
            elif line.startswith("HARNESS-ERROR"):
                res["errors"].append(f"{key}: " + line[len("HARNESS-ERROR "):][:2000])
    # The crate's outcome per bundle (lowered, or the stage that rejected it), from the export.
    res["outcomes"] = outcomes(fjson)
    if not args.keep_json:
        for path in (fjson, cjson, pjson):
            if os.path.exists(path):
                os.remove(path)
    return res


def outcomes(fjson):
    out = {}
    if not os.path.exists(fjson):
        return out
    try:
        data = json.load(open(fjson))
    except Exception:
        return out
    for rec in data:
        name = rec.get("name", "?").split("/")[-1]
        fe = rec.get("frontend", {})
        oc = fe.get("outcome", {})
        if "rejected" in oc:
            e = oc["rejected"]
            out[name] = f"rejected:{e.get('stage', '?')}:{e.get('category', '?')}"
        elif "lowered" in oc:
            out[name] = "lowered"
        else:
            out[name] = "?"
    return out


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--seed", type=int, required=True)
    ap.add_argument("--count", type=int, required=True)
    ap.add_argument("--start", type=int, default=0)
    ap.add_argument("--chunk", type=int, default=250)
    ap.add_argument("--jobs", type=int, default=4)
    ap.add_argument("--out", required=True)
    ap.add_argument("--keep-json", action="store_true")
    ap.add_argument("--timeout", type=int, default=600, help="seconds a harness may take on one chunk")
    ap.add_argument("--no-partitioned", dest="partitioned", action="store_false")
    ap.add_argument("--spans", action="store_true", help="compare source spans in the frontend harness")
    ap.add_argument("--family", action="append")
    args = ap.parse_args()
    for d in ("bundles", "json", "logs", "bin"):
        os.makedirs(os.path.join(args.out, d), exist_ok=True)
    # Run copies of the executables, so that a rebuild during the run does not change them.
    global BRIDGE, PART, FDIFF, CONF
    copies = []
    for exe in (BRIDGE, PART, FDIFF, CONF):
        dst = os.path.join(args.out, "bin", os.path.basename(exe))
        shutil.copy2(exe, dst)
        copies.append(dst)
    BRIDGE, PART, FDIFF, CONF = copies
    fb = os.path.join(LEAN, "conformance", "frontend-baseline")
    baselines = {"frontend": [os.path.join(fb, f) for f in sorted(os.listdir(fb)) if f.endswith(".txt")],
                 "conformance": os.path.join(LEAN, "conformance", "baseline.txt")}
    extra = os.path.join(args.out, "expected.txt")  # a run's own expected list, if any
    t0 = time.time()
    chunks = []
    i, c = args.start, 0
    while i < args.start + args.count:
        n = min(args.chunk, args.start + args.count - i)
        chunks.append((c, i, n))
        i += n
        c += 1
    results = []
    with cf.ThreadPoolExecutor(max_workers=args.jobs) as ex:
        futs = [ex.submit(run_chunk, args, c, s, n, baselines) for (c, s, n) in chunks]
        for f in cf.as_completed(futs):
            r = f.result()
            results.append(r)
            print(f"chunk {r['chunk']}: {len(r['bundles'])} bundles, {len(r['frontend'])} frontend, "
                  f"{len(r['conformance'])} conformance, {len(r['partitioned'])} partitioned disagreements, "
                  f"{len(r['crashes'])} crashes, {len(r['errors'])} errors", flush=True)
    results.sort(key=lambda r: r["chunk"])
    with open(os.path.join(args.out, f"results-{args.seed}-{args.start}.json"), "w") as f:
        json.dump(results, f, indent=1)
    sys.path.insert(0, HERE)
    from summarize import summarize
    text, bad = summarize(args.out, [os.path.join(args.out, f"results-{args.seed}-{args.start}.json")],
                          elapsed=time.time() - t0)
    print(text)
    sys.exit(1 if bad else 0)


if __name__ == "__main__":
    main()
