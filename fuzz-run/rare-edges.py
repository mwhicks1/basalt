#!/usr/bin/env python3
# Copyright (c) 2026 Harrison Goldstein. All rights reserved.
# Released under MIT license as described in the file LICENSE.
# Authors: Michael Hicks
"""A gate's Cedar edges weighted by how hard they are to reach, for targets whose total edge count is
saturated: per arm, the median number of *rare* edges a trial reaches (hit by at most RARE of all
trials pooled over the arms) and of edges *beyond random* (in no trial of the first arm), each with an
exact two-sided Mann-Whitney test against the second arm; then each arm's union of such edges.

  fuzz-run/rare-edges.py [--rare=0.25] OUT_DIR BASELINE[:BACKEND] REF[:BACKEND] [ARM[:BACKEND] ...]

The trial layout and the arm names are `gate-stats.py`'s.
"""
import bisect, itertools, re, statistics, sys

PREFIX = "lp_Cedar_"
EXCLUDE = re.compile(r"[Rr]epr|[Ff]ormat|[Tt]oString")
argv = sys.argv[1:]
rare = 0.25
if argv[0].startswith("--rare="): rare = float(argv.pop(0).split("=")[1])
out = argv[0]
arms = []
for a in argv[1:]:
    name, _, be = a.partition(":")
    arms.append((name, be or ("io-libfuzzer" if name.startswith("random") else
                         "choice" if name.startswith("choice") else "fuzz")))

# Edges are named by function and offset within it, so arms from different builds compare.
tables = {}
def namer(arm):
    path = f"{out}/{arm}/syms.txt"
    try: open(path).close()
    except FileNotFoundError: path = f"{out}/syms.txt"
    if path not in tables:
        addrs, names = [], []
        for line in open(path):
            a, n = line.split()
            n = n[1:] if n.startswith("_lp_") or n.startswith("__init_") else n
            addrs.append(int(a, 16)); names.append(n)
        tables[path] = (addrs, names)
    addrs, names = tables[path]
    def name(o):
        i = bisect.bisect_right(addrs, o) - 1
        n = names[i]
        if not (n.startswith(PREFIX) or n.startswith("_init_" + PREFIX)) or EXCLUDE.search(n):
            return None
        return (n, o - addrs[i])
    return name

def edges(path, name):
    s = set()
    for line in open(path):
        o, f = line.split()
        if f != "0":
            e = name(int(o, 16))
            if e: s.add(e)
    return s

def mann_whitney(xs, ys):
    def u(a, b): return sum((x > y) + 0.5 * (x == y) for x in a for y in b)
    u0 = u(xs, ys); pooled = xs + ys; n = len(xs); mid = n * len(ys) / 2
    extreme = total = 0
    for idx in itertools.combinations(range(len(pooled)), n):
        s = set(idx)
        a = [pooled[i] for i in idx]; b = [pooled[i] for i in range(len(pooled)) if i not in s]
        total += 1
        if abs(u(a, b) - mid) >= abs(u0 - mid) - 1e-9: extreme += 1
    return extreme / total

sets = {}
for name, be in arms:
    nm, ts, t = namer(name), [], 1
    while True:
        try: ts.append(edges(f"{out}/{name}/{be}.{t}.cov", nm))
        except FileNotFoundError: break
        t += 1
    sets[name] = ts
arms = [(n, be) for n, be in arms if sets[n]]
pooled = [s for n, _ in arms for s in sets[n]]
count = {}
for s in pooled:
    for e in s: count[e] = count.get(e, 0) + 1
rare_set = {e for e, c in count.items() if c <= rare * len(pooled)}
base = set().union(*sets[arms[0][0]])
ref = arms[1][0]
print(f"# {out}: {len(pooled)} trials; {len(count):,} edges reached, {len(rare_set):,} rare (in at most "
      f"{rare:.0%} of trials), {len(set(count) - base):,} beyond {arms[0][0]}")
print(f"{'arm':24}{'n':>3}{'edges':>8}{'rare':>7}{'p':>7}{'beyond':>8}{'p':>7}{'rare∪':>7}{'beyond∪':>9}")
cols = {n: ([len(s & rare_set) for s in sets[n]], [len(s - base) for s in sets[n]]) for n, _ in arms}
for name, _ in arms:
    r, b = cols[name]
    pr = "" if name == ref else f"{mann_whitney(r, cols[ref][0]):.3f}"
    pb = "" if name == ref else f"{mann_whitney(b, cols[ref][1]):.3f}"
    u = set().union(*sets[name])
    print(f"{name:24}{len(sets[name]):>3}{statistics.median(map(len, sets[name])):>8,.0f}"
          f"{statistics.median(r):>7,.0f}{pr:>7}{statistics.median(b):>8,.0f}{pb:>7}"
          f"{len(u & rare_set):>7,}{len(u - base):>9,}")
