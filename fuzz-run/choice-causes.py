#!/usr/bin/env python3
# Copyright (c) 2026 Harrison Goldstein. All rights reserved.
# Released under MIT license as described in the file LICENSE.
# Authors: Michael Hicks
"""Phase 0.1's cause log for the choice backend: from a campaign run with `BASALT_CHOICE_DIAG=1` on
a property that prints `BASALT_H` lines, the share of mutated inputs whose expression is new, the
parent's, or another earlier one's, overall and per operator, and how often replay undid the edit
(the child's realized records equal the parent's).

  fuzz-run/choice-causes.py LOG [LOG ...]
"""
import collections, sys

for path in sys.argv[1:]:
    he, kids = [None], []
    for line in open(path, errors="replace"):
        if line.startswith("BASALT_H "):
            he.append(line.split()[1])
        elif line.startswith("BASALT_C "):
            _, run, par, op, same, fresh = line.split()
            kids.append((int(run), int(par), op, same == "1", fresh == "1"))
    first = {}
    for i in range(1, len(he)):
        first.setdefault(he[i], i)
    tot = collections.Counter()
    per = collections.defaultdict(collections.Counter)
    for run, par, op, same, fresh in kids:
        if run >= len(he) or par >= len(he): continue
        cls = ("undone" if same else "new" if first[he[run]] == run
               else "parent" if he[run] == he[par] else "other")
        tot[cls] += 1; per[op][cls] += 1; per[op]["n"] += 1; per[op]["fresh"] += fresh
    n = sum(tot.values())
    print(f"## {path}: {n:,} mutated children")
    for c in ("new", "parent", "other", "undone"):
        print(f"  {c:8} {tot[c]:>10,}  {100 * tot[c] / max(n, 1):5.1f}%")
    print(f"  {'op':10}{'n':>10}{'new':>8}{'parent':>8}{'other':>8}{'undone':>8}{'feature':>9}")
    for op, c in sorted(per.items(), key=lambda kv: -kv[1]["n"]):
        m = c["n"]
        print(f"  {op:10}{m:>10,}" + "".join(f"{100 * c[k] / m:>7.1f}%" for k in
              ("new", "parent", "other", "undone")) + f"{100 * c['fresh'] / m:>8.3f}%")
    print()
