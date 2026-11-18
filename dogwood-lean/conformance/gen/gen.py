#!/usr/bin/env python3
"""Write generated bundles for the differential runs of the frontend and the specification.

Usage: gen.py --seed S --count N --out DIR [--start I] [--family F]...

Writes bundles `DIR/s<S>_<I>_<family>/` for I in [start, start + N): a policy (`policy.dw`), an
action schema (`schema.cedarschema`), and, as the bundle needs them, an event schema
(`event.dwschema`), provider declarations (`providers.json`, with script files), a macro library
(`macros.dw`), and traces (`trace.log`, `trace_<n>.log`), in the layout `bridge/` reads. Each
bundle also has `meta.json`: its family and the tags of the features it uses, which
`summarize.py` counts. A bundle is a function of the seed and its index alone, so a disagreement
found in a run can be regenerated with `--start I --count 1`.

The families and what they target are described in `families.py`.
"""

import argparse
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from families import FAMILIES, make  # noqa: E402


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--seed", type=int, required=True)
    ap.add_argument("--count", type=int, required=True)
    ap.add_argument("--start", type=int, default=0)
    ap.add_argument("--out", required=True)
    ap.add_argument("--family", action="append", choices=[f for (f, _) in FAMILIES])
    a = ap.parse_args()
    os.makedirs(a.out, exist_ok=True)
    fams = a.family
    for i in range(a.start, a.start + a.count):
        fam = fams[i % len(fams)] if fams else None
        make(a.seed, i, fam).write(a.out)


if __name__ == "__main__":
    main()
