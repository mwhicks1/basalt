import csv, statistics, collections
cls = {"and-true-left":"I","or-false-left":"I","not-not":"I","ite-bool-id":"I","add-zero":"I","and-true-right":"I",
 "mul-zero":"E","eq-refl":"E","ite-same":"E","and-false-right":"E","sub-self":"E","record-access":"E","and-commute":"E",
 "neg-neg":"B","record-last":"D","eq-commute":"O","add-commute":"O"}
d = collections.defaultdict(list)
for b,g,be,t,f,r,ty in csv.reader(open('experiments/minicedar/results-A-V.csv')):
    d[(b,g,be)].append((int(f), int(r) if r else None, ty))
order = list(cls)
cells = [("mc","io"),("mc","fuzz"),("mcv","io"),("mcv","fuzz")]
print(f"{'bug':16}{'cls':4}" + "".join(f"{g+'/'+be:>22}" for g,be in cells))
for b in order:
    row = f"{b:16}{cls[b]:4}"
    for c in cells:
        xs = d.get((b,)+c, [])
        if not xs: row += f"{'-':>22}"; continue
        found = [r for f,r,_ in xs if f]
        typed = sum(1 for f,_,ty in xs if f and ty=="true")
        med = statistics.median(found) if found else None
        s = f"{len(found)}/{len(xs)}"
        if found: s += f" med {int(med):>7} t{typed}"
        row += f"{s:>22}"
    print(row)
