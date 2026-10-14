#!/usr/bin/env python3
# Copyright (c) 2026 Harrison Goldstein. All rights reserved.
# Released under MIT license as described in the file LICENSE.
# Authors: Michael Hicks
"""Why mutated inputs repeat (DESIGN-choice-sequences.md, Phase 0.1), from the logs of campaigns run
with `--diag-mutations` on a property that prints `BASALT_H` and `BASALT_E` lines (`gen-traced-repr`).

For each mutated input: is its expression new to the campaign, its parent's, or another earlier
one's; if its parent's, why — (a) the bytes its parent read are unchanged, (b) they changed but every
draw decodes the same, (c) draws changed but the expression did not. Then the parent–child distance
(token edit distance between the expressions, and edit distance between the drawn values), for all
children and for the ones that reached a new feature, and the expression size over the campaign.

  fuzz-run/mutation-causes.py LOG [LOG ...]
"""
import random, re, statistics, sys

TOK = re.compile(r"[A-Za-z_][A-Za-z_.0-9]*|\d+|\S")
SAMPLE = 3000

def lev(a, b):
    if len(a) < len(b): a, b = b, a
    prev = list(range(len(b) + 1))
    for i, x in enumerate(a, 1):
        cur = [i]
        for j, y in enumerate(b, 1):
            cur.append(min(prev[j] + 1, cur[j - 1] + 1, prev[j - 1] + (x != y)))
        prev = cur
    return prev[-1]

def pct(xs, q): return sorted(xs)[min(len(xs) - 1, int(q * len(xs)))] if xs else float("nan")

def analyse(path):
    he, hi, size, ms = [None], [None], [None], []   # by run index (1-based)
    with open(path, errors="replace") as f:
        for line in f:
            if line.startswith("BASALT_H "):
                p = line.split(); he.append(p[1]); hi.append(p[2] if len(p) > 2 else p[1])
            elif line.startswith("BASALT_E "):
                size.append(len(TOK.findall(line[9:])))
            elif line.startswith("BASALT_M "):
                p = line.split()
                ms.append((int(p[1]), None if p[2] == "-" else int(p[2]), p[3], int(p[4]), int(p[5]),
                           p[6] == "1", int(p[7]), int(p[8]), int(p[9]), int(p[10])))
    first = {}
    for i in range(1, len(he)):
        first.setdefault(he[i], i)
    counts = {k: 0 for k in ("new", "a", "b", "c", "c1", "other", "m", "s", "n")}
    kids = []
    for run, par, cls, k, dist, fresh, nc, cur, off, pcur in ms:
        if run >= len(he): continue
        if cls in "msn": counts[cls] += 1; continue
        if first[he[run]] == run: counts["new"] += 1
        elif he[run] == he[par]:
            counts[cls if cls in "ab" else "c"] += 1
            if cls == "v" and hi[run] != hi[par]: counts["c1"] += 1
        else: counts["other"] += 1
        kids.append((run, par, cls, dist, fresh, off, pcur))
    n = len(kids)
    print(f"## {path}")
    print(f"runs {len(he) - 1:,}; mutated children {n:,} (also: {counts['m']:,} with unknown parent, "
          f"{counts['s']:,} queued seeds, {counts['n']:,} not mutations)")
    rep = n - counts["new"]
    print(f"  new expression          {counts['new']:>9,}  {100 * counts['new'] / n:5.1f}%")
    for key, label in (("a", "(a) parent's, bytes read unchanged"), ("b", "(b) parent's, same draws"),
                       ("c", "(c) parent's, draws changed"), ("other", "an earlier one, not parent's")):
        print(f"  {label:34}{counts[key]:>9,}  {100 * counts[key] / n:5.1f}%  "
              f"({100 * counts[key] / max(rep, 1):.1f}% of repeats)")
    print(f"    of (c), the rest of the input (request, entities) changed: {counts['c1']:,}")
    draws = [nc for (_, _, _, _, _, _, nc, _, _, _) in ms]
    print(f"  draws per test: median {statistics.median(draws):.0f}, mean {statistics.mean(draws):.1f}")
    saved = [kd for kd in kids if kd[4]]
    rng = random.Random(1)
    for label, group in (("all children", kids), ("new-feature children", saved)):
        dd = [kd[3] for kd in group if kd[2] == "v" and kd[3] >= 0]
        print(f"  {label}: {len(group):,}; draw edit distance (changed draws) median {pct(dd, .5)}, "
              f"p90 {pct(dd, .9)}; share with draws changed {100 * len(dd) / max(len(group), 1):.1f}%")
    return he, kids, saved, size, rng

def expr_distance(path, kids, saved, rng):
    sk = rng.sample(kids, min(SAMPLE, len(kids)))
    ss = rng.sample(saved, min(SAMPLE, len(saved)))
    need = {r for kd in sk + ss for r in kd[:2]}
    rep, i = {}, 0
    with open(path, errors="replace") as f:
        for line in f:
            if line.startswith("BASALT_H "): i += 1
            elif line.startswith("BASALT_E ") and i in need:
                rep[i] = TOK.findall(line[9:])[:600]
    for label, group in (("all children", sk), ("new-feature children", ss)):
        ds = [lev(rep[c], rep[p]) for c, p, *_ in group if c in rep and p in rep]
        print(f"  expression token distance, {label} (sample {len(ds)}): median {pct(ds, .5)}, "
              f"mean {statistics.mean(ds) if ds else float('nan'):.1f}, p90 {pct(ds, .9)}")

def sizes(size):
    marks = [10 ** k for k in range(2, 8)]
    row = []
    for m in marks:
        lo = m // 10
        xs = [s for s in size[lo:m] if s is not None]
        if xs: row.append(f"{lo:,}–{m:,}: {statistics.median(xs):.0f}")
    print("  expression size (tokens), median by test range: " + "; ".join(row))

for path in sys.argv[1:]:
    he, kids, saved, size, rng = analyse(path)
    expr_distance(path, kids, saved, rng)
    sizes(size)
    print()
