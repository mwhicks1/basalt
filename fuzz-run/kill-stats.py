#!/usr/bin/env python3
# Copyright (c) 2026 Harrison Goldstein. All rights reserved.
# Released under MIT license as described in the file LICENSE.
# Authors: Michael Hicks
"""Kill table for the Cedar fault-injection experiment: per mutant, property and arm, the trials that
failed, how (`UNSOUND`: an evaluation outside its type; `ill-typed`: the generator's judgment
rejected by `typeOf`), and the median tests to the failure (over failing trials).

  fuzz-run/kill-stats.py OUT_DIR      (trial logs at OUT_DIR/m<K>/<prop>/<arm>/<backend>.<t>.log)
"""
import glob, os, re, statistics, sys

out = sys.argv[1]
rows = {}
for log in glob.glob(f"{out}/m*/*/*/*.log"):
    k, prop, arm = log[len(out) + 1:].split("/")[:3]
    kind, runs = None, None
    with open(log, errors="replace") as f:
        for line in f:
            if line.startswith("BASALT_H"): continue
            if "UNSOUND" in line: kind = kind or "UNSOUND"
            elif "ill-typed:" in line or "disagrees" in line: kind = kind or "ill-typed"
            m = re.match(r"runs\s*:\s*(\d+)", line)
            if m and kind: runs = int(m[1])
    rows.setdefault((int(k[1:]), prop, arm), []).append((kind, runs))
arms = sorted({a for _, _, a in rows})
print(f"{'mutant':>6} {'property':12}" + "".join(f"{a:>26}" for a in arms))
for k, prop in sorted({(k, p) for k, p, _ in rows}):
    cells = []
    for a in arms:
        ts = rows.get((k, prop, a), [])
        kills = [r for kd, r in ts if kd and r]
        kinds = {kd for kd, r in ts if kd}
        tag = "/".join(sorted(x[0] for x in kinds))
        med = f"{statistics.median(kills):,.0f}" if kills else "-"
        cells.append(f"{len(kills)}/{len(ts)} {tag:3} {med:>12}")
    print(f"{k:>6} {prop:12}" + "".join(f"{c:>26}" for c in cells))
