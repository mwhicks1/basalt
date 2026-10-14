#!/usr/bin/env python3
# Copyright (c) 2026 Harrison Goldstein. All rights reserved.
# Released under MIT license as described in the file LICENSE.
# Authors: Michael Hicks
"""Cedar coverage and distinct inputs per arm of a `cedar-experiment.sh` run, at fixed budgets of
tests *and* of elapsed time, mean ± SE over trials.

A test's time comes from `<arm>.<t>.cov.time` (milliseconds at every 1000th test), interpolated, so
the time budget charges each arm what its tests actually cost. Trials should each have had a core to
themselves, or the times measure contention instead.

  fuzz-run/budget-table.py OUT_DIR ARM[:BACKEND] [ARM[:BACKEND] ...]
"""
import bisect, math, re, statistics, sys

PREFIX = "lp_Cedar_"
EXCLUDE = re.compile(r"[Rr]epr|[Ff]ormat|[Tt]oString")
out = sys.argv[1]
arms = []
for a in sys.argv[2:]:
    name, _, be = a.partition(":")
    arms.append((name, be or ("io-libfuzzer" if name.startswith("random") else
                         "choice" if name.startswith("choice") else "fuzz")))

addrs, names = [], []
for line in open(f"{out}/syms.txt"):
    a, n = line.split()
    n = n[1:] if n.startswith("_lp_") or n.startswith("__init_") else n
    addrs.append(int(a, 16)); names.append(n)

def cedar(o):
    n = names[bisect.bisect_right(addrs, o) - 1]
    return (n.startswith(PREFIX) or n.startswith("_init_" + PREFIX)) and not EXCLUDE.search(n)

def trial(base):
    firsts = sorted(int(f) for o, f in (l.split() for l in open(f"{base}.cov"))
                    if f != "0" and cedar(int(o, 16)))
    try:
        ticks = [(0, 0)] + [tuple(map(int, l.split())) for l in open(f"{base}.cov.time")]
    except FileNotFoundError:
        ticks = None                                    # a run from before the timestamps
    seen, uniq = set(), []
    for line in open(f"{base}.log", errors="replace"):
        if line.startswith("BASALT_H "):
            seen.add(line.split()[1]); uniq.append(len(seen))
    return firsts, ticks, uniq

def test_at_ms(ticks, ms):
    """The number of tests run by `ms` milliseconds."""
    ts = [t for _, t in ticks]
    i = bisect.bisect_right(ts, ms) - 1
    if i >= len(ticks) - 1: return ticks[-1][0]
    (n0, t0), (n1, t1) = ticks[i], ticks[i + 1]
    return n0 + (n1 - n0) * (ms - t0) // max(t1 - t0, 1)

def fmt(xs):
    if not xs: return "–"
    m = statistics.mean(xs)
    se = statistics.stdev(xs) / math.sqrt(len(xs)) if len(xs) > 1 else 0
    return f"{m:,.0f} ±{se:,.0f}"

data = {}
for name, be in arms:
    ts, t = [], 1
    while True:
        try: ts.append(trial(f"{out}/{name}/{be}.{t}"))
        except FileNotFoundError: break
        t += 1
    data[name] = ts

def table(title, marks, at):
    print(f"\n{title}")
    print(f"{'':>12}" + "".join(f"{n:>22}" for n, _ in arms))
    for m, label in marks:
        row = []
        for n, _ in arms:
            vals = [v for v in (at(tr, m) for tr in data[n]) if v is not None]
            row.append(fmt(vals))
        print(f"{label:>12}" + "".join(f"{r:>22}" for r in row))

maxn = max((len(tr[2]) for n, _ in arms for tr in data[n]), default=0)
tests = [(x, f"{x:,}") for x in (10 ** k for k in range(2, 9)) if x <= maxn]
if maxn and maxn not in (x for x, _ in tests): tests.append((maxn, f"{maxn:,}"))
timed = all(tr[1] for n, _ in arms for tr in data[n])
maxms = min((tr[1][-1][1] for n, _ in arms for tr in data[n]), default=0) if timed else 0
times = [(s * 1000, f"{s // 60} min" if s >= 60 else f"{s} s")
         for s in (10, 60, 300, 900, 1800, 3600, 7200, 14400) if s * 1000 <= maxms]
times.append((maxms, f"{maxms // 60000} min*" if maxms >= 60000 else f"{maxms // 1000} s*"))

edges_n = lambda tr, n: bisect.bisect_right(tr[0], n) if n <= len(tr[2]) else None
uniq_n = lambda tr, n: tr[2][n - 1] if n <= len(tr[2]) else None
edges_t = lambda tr, ms: bisect.bisect_right(tr[0], test_at_ms(tr[1], ms))
uniq_t = lambda tr, ms: tr[2][min(test_at_ms(tr[1], ms), len(tr[2])) - 1]
table("Cedar edges at a budget of tests", tests, edges_n)
if timed: table("Cedar edges at a budget of time (* = when the fastest trial finished)", times, edges_t)
table("Distinct expressions at a budget of tests", tests, uniq_n)
if timed: table("Distinct expressions at a budget of time", times, uniq_t)
