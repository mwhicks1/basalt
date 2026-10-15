#!/usr/bin/env python3
# Copyright (c) 2026 Harrison Goldstein. All rights reserved.
# Released under MIT license as described in the file LICENSE.
# Authors: Michael Hicks
"""A gate's statistics (DESIGN-choice-sequences.md §4): per arm, the median Cedar edges at the
largest common budget of tests and of time, and an exact two-sided Mann-Whitney test of each arm
against the first. Also median throughput (tests/s), distinct expressions at the test budget, and,
where the property reports it, the median expression size over the last tenth of the tests.

  fuzz-run/gate-stats.py OUT_DIR ARM[:BACKEND] [ARM[:BACKEND] ...]
"""
import bisect, itertools, re, statistics, sys

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
    ticks = [(0, 0)] + [tuple(map(int, l.split())) for l in open(f"{base}.cov.time")]
    seen, uniq, sizes = set(), [], []
    for line in open(f"{base}.log", errors="replace"):
        if line.startswith("BASALT_H "):
            p = line.split()
            seen.add(p[1]); uniq.append(len(seen))
            if len(p) > 3 and p[3].isdigit(): sizes.append(int(p[3]))
    return firsts, ticks, uniq, sizes

def test_at_ms(ticks, ms):
    ts = [t for _, t in ticks]
    i = bisect.bisect_right(ts, ms) - 1
    if i >= len(ticks) - 1: return ticks[-1][0]
    (n0, t0), (n1, t1) = ticks[i], ticks[i + 1]
    return n0 + (n1 - n0) * (ms - t0) // max(t1 - t0, 1)

def mann_whitney(xs, ys):
    """Exact two-sided p-value of the U statistic (ties counted half), by enumeration."""
    def u(a, b): return sum((x > y) + 0.5 * (x == y) for x in a for y in b)
    u0 = u(xs, ys); pooled = xs + ys; n = len(xs); mid = n * len(ys) / 2
    extreme = total = 0
    for idx in itertools.combinations(range(len(pooled)), n):
        s = set(idx)
        a = [pooled[i] for i in idx]; b = [pooled[i] for i in range(len(pooled)) if i not in s]
        total += 1
        if abs(u(a, b) - mid) >= abs(u0 - mid) - 1e-9: extreme += 1
    return extreme / total

data = {}
for name, be in arms:
    ts, t = [], 1
    while True:
        try: ts.append(trial(f"{out}/{name}/{be}.{t}"))
        except FileNotFoundError: break
        t += 1
    data[name] = ts
arms = [(n, be) for n, be in arms if data[n]]          # an arm with no finished trial yet

ntests = min(len(tr[2]) or tr[1][-1][0] for n, _ in arms for tr in data[n])
ms = min(tr[1][-1][1] for n, _ in arms for tr in data[n])
ref = arms[0][0]
cols = {}
for name, _ in arms:
    trs = data[name]
    e_n = [bisect.bisect_right(tr[0], ntests) for tr in trs]
    e_t = [bisect.bisect_right(tr[0], test_at_ms(tr[1], ms)) for tr in trs]
    rate = [tr[1][-1][0] / (tr[1][-1][1] / 1000) for tr in trs]
    uniq = [tr[2][ntests - 1] for tr in trs if len(tr[2]) >= ntests]
    size = [statistics.median(tr[3][len(tr[3]) * 9 // 10:]) for tr in trs if tr[3]]
    cols[name] = (e_n, e_t, rate, uniq, size)
print(f"# {out}: {ntests:,} tests; {ms / 60000:.1f} min (the fastest trial's end)")
print(f"{'arm':24}{'n':>3}{'edges@tests':>13}{'p':>7}{'edges@time':>12}{'p':>7}"
      f"{'tests/s':>9}{'ratio':>7}{'distinct':>11}{'size':>6}")
r_rate = statistics.median(cols[ref][2])
for name, _ in arms:
    e_n, e_t, rate, uniq, size = cols[name]
    pn = "" if name == ref else f"{mann_whitney(e_n, cols[ref][0]):.3f}"
    pt = "" if name == ref else f"{mann_whitney(e_t, cols[ref][1]):.3f}"
    m = lambda xs: f"{statistics.median(xs):,.0f}" if xs else "–"
    print(f"{name:24}{len(e_n):>3}{m(e_n):>13}{pn:>7}{m(e_t):>12}{pt:>7}{m(rate):>9}"
          f"{statistics.median(rate) / r_rate:>7.2f}{m(uniq):>11}{m(size):>6}")
