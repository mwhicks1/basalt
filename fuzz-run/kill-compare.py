#!/usr/bin/env python3
# Copyright (c) 2026 Harrison Goldstein. All rights reserved.
# Released under MIT license as described in the file LICENSE.
# Authors: Michael Hicks
"""Arms compared on time to kill an injected fault: per (fault, property), each arm's kills, median
tests and seconds to the kill (a trial that never kills counts as past the budget, so a median past it
prints as `>budget`), and a two-sided Mann-Whitney test on tests against each reference arm, by
20,000 seeded permutations (the censored ties make the exact tables of `gate-stats.py` wrong here).
Then, per arm, how many pairs it wins and loses at p < 0.05 against each reference.

  fuzz-run/kill-compare.py OUT_DIR BUDGET REF[,REF...] ARM [ARM ...]
"""
import glob, os, random, re, statistics, sys

out, budget = sys.argv[1], int(sys.argv[2])
refs = sys.argv[3].split(",")
arms = sys.argv[4:]

def trial(log):
    killed, runs = False, None
    with open(log, errors="replace") as f:
        for line in f:
            if line.startswith("BASALT_H"): continue
            if line.startswith("counterexample"): killed = True
            m = re.match(r"runs\s*:\s*(\d+)", line)
            if m and killed: runs = int(m[1])
    try: secs = float(open(log + ".secs").read())
    except FileNotFoundError: secs = float("nan")
    return (runs, secs) if runs else (budget + 1, secs)

data = {}
for log in glob.glob(f"{out}/m*/*/*/*.log"):
    k, prop, arm = os.path.relpath(log, out).split("/")[:3]
    data.setdefault((int(k[1:]), prop), {}).setdefault(arm, []).append(trial(log))

def mw(xs, ys, rng):
    def u(a, b): return sum((x < y) + 0.5 * (x == y) for x in a for y in b)
    n, pooled, mid = len(xs), xs + ys, len(xs) * len(ys) / 2
    d0 = abs(u(xs, ys) - mid); hits = 0
    for _ in range(20000):
        rng.shuffle(pooled)
        hits += abs(u(pooled[:n], pooled[n:]) - mid) >= d0 - 1e-9
    return hits / 20000

def med(xs):
    m = statistics.median(xs)
    return f">{budget // 1000}k" if m > budget else f"{m:,.0f}"

rng = random.Random(1)
wins = {(a, r): [0, 0] for a in arms for r in refs}
print(f"{'fault':>5} {'property':12}" + "".join(f"{a:>34}" for a in arms))
print(f"{'':>5} {'':12}" + "".join(f"{'kills  tests   secs ' + ' '.join('p:' + r[:6] for r in refs):>34}" for a in arms))
for (k, prop) in sorted(data):
    cells = []
    for a in arms:
        ts = data[(k, prop)].get(a, [])
        if not ts: cells.append(f"{'-':>34}"); continue
        tests = [t for t, _ in ts]; secs = [s for _, s in ts]
        kills = sum(t <= budget for t in tests)
        ps = []
        for r in refs:
            if r == a or r not in data[(k, prop)]: ps.append(f"{'':>8}"); continue
            rt = [t for t, _ in data[(k, prop)][r]]
            p = mw(tests, rt, rng)
            if p < 0.05: wins[(a, r)][statistics.median(tests) > statistics.median(rt)] += 1
            ps.append(f"{p:>8.3f}")
        cells.append(f"{kills:>3}/{len(ts):<2}{med(tests):>9}{statistics.median(secs):>7.0f}" + "".join(ps))
    print(f"{k:>5} {prop:12}" + "".join(f"{c:>34}" for c in cells))
print()
for r in refs:
    print(f"against {r}: " + ", ".join(f"{a} {w}-{l}" for a in arms if a != r
                                       for w, l in [wins[(a, r)]]) + "  (pairs faster-slower, p < 0.05)")
