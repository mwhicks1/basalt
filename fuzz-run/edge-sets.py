#!/usr/bin/env python3
# Copyright (c) 2026 Harrison Goldstein. All rights reserved.
# Released under MIT license as described in the file LICENSE.
# Authors: Michael Hicks
"""Which Cedar edges each arm of a `cedar-experiment.sh` run reached, compared as sets.

For every arm: the mean per-trial edge count and the union over its trials. Then, for each arm X,
the edges X reached that no other arm did, and the edges the others' union reached that X did not.

  fuzz-run/edge-sets.py OUT_DIR ARM[:BACKEND] [ARM[:BACKEND] ...]
"""
import bisect, re, sys

PREFIX = "lp_Cedar_"
EXCLUDE = re.compile(r"[Rr]epr|[Ff]ormat|[Tt]oString")
out = sys.argv[1]
arms = []
for a in sys.argv[2:]:
    name, _, be = a.partition(":")
    arms.append((name, be or ("io-libfuzzer" if name == "random" else "fuzz")))

addrs, names = [], []
for line in open(f"{out}/syms.txt"):
    a, n = line.split()
    n = n[1:] if n.startswith("_lp_") or n.startswith("__init_") else n
    addrs.append(int(a, 16)); names.append(n)

def cedar(o):
    n = names[bisect.bisect_right(addrs, o) - 1]
    return (n.startswith(PREFIX) or n.startswith("_init_" + PREFIX)) and not EXCLUDE.search(n)

def edges(path):
    s = set()
    for line in open(path):
        o, f = line.split()
        if f != "0" and cedar(int(o, 16)): s.add(o)
    return s

sets = {}
for name, be in arms:
    trials, t = [], 1
    while True:
        try: trials.append(edges(f"{out}/{name}/{be}.{t}.cov"))
        except FileNotFoundError: break
        t += 1
    sets[name] = trials
    u = set().union(*trials)
    mean = sum(map(len, trials)) / len(trials)
    print(f"{name:14} trials {len(trials)}  mean {mean:8.1f}  union {len(u)}")
print()
for name, _ in arms:
    mine = set().union(*sets[name])
    others = set().union(*(set().union(*sets[o]) for o, _ in arms if o != name))
    print(f"{name:14} only here {len(mine - others):5}"
          f"   missed, reached elsewhere {len(others - mine):5}")
