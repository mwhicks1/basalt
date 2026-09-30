"""Grouped bar chart of runs-to-failure per planted bug and arm, from results-A-V.csv.

Emits chart.html (inline SVG, CSS-variable colors, hover tooltips, table view, light/dark) and
chart-light.svg / chart-light.png (literal colors, for a static preview)."""
import csv, json, math, collections, html

CAP = 1_000_000
SRC = "experiments/minicedar/results-A-V.csv"

CLS = {"and-true-left": "I", "or-false-left": "I", "not-not": "I", "ite-bool-id": "I",
       "add-zero": "I", "and-true-right": "I",
       "mul-zero": "E", "eq-refl": "E", "ite-same": "E", "and-false-right": "E", "sub-self": "E",
       "record-access": "E", "and-commute": "E",
       "neg-neg": "B", "record-last": "D", "eq-commute": "O", "add-commute": "O"}
CLASS_NAMES = {"I": "needs ill-typed input", "E": "well-typed + runtime error",
               "B": "extreme integer", "D": "duplicate key", "O": "two different errors"}
ARMS = [("mc", "io", "Unconstrained · random"), ("mc", "fuzz", "Unconstrained · FuzzGen"),
        ("mcv", "io", "Well-typed · random"), ("mcv", "fuzz", "Well-typed · FuzzGen")]

def quantile(xs, q):
    xs = sorted(xs)
    if len(xs) == 1: return xs[0]
    pos = (len(xs) - 1) * q
    lo, hi = math.floor(pos), math.ceil(pos)
    return xs[lo] + (xs[hi] - xs[lo]) * (pos - lo)

rows = collections.defaultdict(list)
for b, g, be, t, f, r, ty in csv.reader(open(SRC)):
    rows[(b, g, be)].append((int(f) == 1, int(r) if r else None, ty == "true"))

bugs = list(CLS)
data = []
for b in bugs:
    for i, (g, be, label) in enumerate(ARMS):
        trials = rows[(b, g, be)]
        found = [r for ok, r, _ in trials if ok]
        vals = [r if ok else CAP for ok, r, _ in trials]   # a miss counts as the cap: a lower bound
        data.append({
            "bug": b, "cls": CLS[b], "arm": i, "armLabel": label, "n": len(trials),
            "found": len(found), "typed": sum(1 for ok, _, ty in trials if ok and ty),
            "mean": sum(vals) / len(vals) if found else None,
            "q1": quantile(vals, .25) if found else None,
            "med": quantile(vals, .5) if found else None,
            "q3": quantile(vals, .75) if found else None,
        })

# ---- geometry ----
W, H = 1180, 600
ML, MR, MT, MB = 70, 20, 64, 160
PW, PH = W - ML - MR, H - MT - MB
YMIN, YMAX = 10, CAP
def y(v): return MT + PH * (1 - (math.log10(v) - math.log10(YMIN)) / (math.log10(YMAX) - math.log10(YMIN)))

CLS_GAP = 18                       # extra space between classes
ngaps = len(set(CLS.values())) - 1
GW = (PW - CLS_GAP * ngaps) / len(bugs)
BAR_GAP = 2
BW = (GW - 10 - BAR_GAP * 3) / 4   # 10px between groups

def gx(k):
    classes_before = len(set(CLS[b] for b in bugs[:k + 1])) - 1
    return ML + k * GW + classes_before * CLS_GAP

def svg(colors, interactive):
    """colors: dict role -> css color string."""
    out = []
    def fill(role): return f'style="fill:{colors[role]}"'
    def stroke(role): return f'style="stroke:{colors[role]}"'
    out.append(f'<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 {W} {H}" width="{W}" height="{H}" '
               f'role="img" aria-labelledby="t d" font-family="system-ui, -apple-system, Segoe UI, sans-serif">')
    out.append('<title id="t">Runs to failure per planted optimizer bug, by generator and search</title>')
    out.append('<desc id="d">Grouped bars on a log scale; bar top is the mean over 5 trials, '
               'whiskers span the 25th to 75th percentile; a trial that did not fail within 1M runs counts as 1M.</desc>')
    out.append(f'<rect x="0" y="0" width="{W}" height="{H}" {fill("surface")}/>')
    # grid + y ticks
    for e in range(1, 7):
        v = 10 ** e
        yy = y(v)
        out.append(f'<line x1="{ML}" x2="{W-MR}" y1="{yy:.1f}" y2="{yy:.1f}" {stroke("grid")} stroke-width="1"/>')
        lab = {10: "10", 100: "100", 1000: "1k", 10**4: "10k", 10**5: "100k", 10**6: "1M"}[v]
        out.append(f'<text x="{ML-8}" y="{yy+4:.1f}" text-anchor="end" font-size="12" '
                   f'style="fill:{colors["muted"]};font-variant-numeric:tabular-nums">{lab}</text>')
    out.append(f'<text x="18" y="{MT+PH/2}" transform="rotate(-90 18 {MT+PH/2})" text-anchor="middle" '
               f'font-size="12" {fill("secondary")}>runs to failure (log scale)</text>')
    # cap line label
    out.append(f'<text x="{W-MR}" y="{y(CAP)-6:.1f}" text-anchor="end" font-size="11" {fill("muted")}>'
               f'budget: 1M runs</text>')
    base = y(YMIN)
    for k, b in enumerate(bugs):
        x0 = gx(k)
        for d in data[k * 4:(k + 1) * 4]:
            i = d["arm"]
            bx = x0 + 5 + i * (BW + BAR_GAP)
            cx = bx + BW / 2
            role = f"s{i+1}"
            tip = (f'{b} ({CLASS_NAMES[d["cls"]]})\n{d["armLabel"]}\n'
                   + (f'found {d["found"]}/{d["n"]} · median {d["med"]:,.0f} · mean {d["mean"]:,.0f}\n'
                      f'quartiles {d["q1"]:,.0f} – {d["med"]:,.0f} – {d["q3"]:,.0f}\n'
                      f'well-typed counterexamples: {d["typed"]}/{d["found"]}'
                      + ('\n(misses counted as 1M)' if d["found"] < d["n"] else '')
                      if d["found"] else f'not found in {d["n"]} trials of 1M runs'))
            if d["found"]:
                top = y(d["med"])
                h = base - top
                r = min(4, BW / 2, h)
                # rounded data-end at the top, square at the baseline
                out.append(f'<path d="M{bx:.1f},{base:.1f} V{top+r:.1f} Q{bx:.1f},{top:.1f} {bx+r:.1f},{top:.1f} '
                           f'H{bx+BW-r:.1f} Q{bx+BW:.1f},{top:.1f} {bx+BW:.1f},{top+r:.1f} V{base:.1f} Z" {fill(role)}/>')
                # quartile whisker
                y1, y3 = y(d["q1"]), y(d["q3"])
                out.append(f'<line x1="{cx:.1f}" x2="{cx:.1f}" y1="{y1:.1f}" y2="{y3:.1f}" {stroke("ink")} stroke-width="1.5"/>')
                for yy in (y1, y3):
                    out.append(f'<line x1="{cx-3:.1f}" x2="{cx+3:.1f}" y1="{yy:.1f}" y2="{yy:.1f}" {stroke("ink")} stroke-width="1.5"/>')
                if d["found"] < d["n"]:
                    out.append(f'<text x="{cx:.1f}" y="{min(top, y3)-5:.1f}" text-anchor="middle" font-size="10" '
                               f'{fill("secondary")}>{d["found"]}/{d["n"]}</text>')
            else:
                out.append(f'<text x="{cx:.1f}" y="{base-6:.1f}" text-anchor="middle" font-size="11" '
                           f'{fill("muted")}>×</text>')
            if interactive:
                out.append(f'<rect class="hit" x="{bx-1:.1f}" y="{MT}" width="{BW+2:.1f}" height="{PH}" '
                           f'fill="transparent" tabindex="0" data-tip="{html.escape(tip)}"/>')
        # bug label, rotated
        lx = x0 + GW / 2
        out.append(f'<text x="{lx:.1f}" y="{base+14:.1f}" text-anchor="end" font-size="12" {fill("primary")} '
                   f'transform="rotate(-40 {lx:.1f} {base+14:.1f})">{b}</text>')
    # baseline
    out.append(f'<line x1="{ML}" x2="{W-MR}" y1="{base:.1f}" y2="{base:.1f}" {stroke("axis")} stroke-width="1"/>')
    # class brackets
    for c in ["I", "E", "B", "D", "O"]:
        ks = [k for k, b in enumerate(bugs) if CLS[b] == c]
        xa, xb = gx(ks[0]) + 4, gx(ks[-1]) + GW - 4
        yb = H - 52
        out.append(f'<line x1="{xa:.1f}" x2="{xb:.1f}" y1="{yb}" y2="{yb}" {stroke("axis")} stroke-width="1"/>')
        words, lines, cur = CLASS_NAMES[c].split(), [], ""
        for w_ in words:
            if cur and (len(cur) + 1 + len(w_)) * 6.2 > (xb - xa):
                lines.append(cur); cur = w_
            else:
                cur = (cur + " " + w_).strip()
        lines.append(cur)
        out.append(f'<text x="{(xa+xb)/2:.1f}" y="{yb+16}" text-anchor="middle" font-size="12" font-weight="600" '
                   f'{fill("primary")}>{c}</text>')
        for j, ln in enumerate(lines):
            out.append(f'<text x="{(xa+xb)/2:.1f}" y="{yb+31+j*14}" text-anchor="middle" font-size="11" '
                       f'{fill("secondary")}>{ln}</text>')
    # legend, one row above the plot
    lx = ML
    for i, (_, _, lab) in enumerate(ARMS):
        out.append(f'<rect x="{lx}" y="18" width="12" height="12" rx="3" {fill("s" + str(i+1))}/>')
        out.append(f'<text x="{lx+18}" y="28" font-size="13" {fill("primary")}>{lab}</text>')
        lx += 18 + len(lab) * 6.9 + 16
    out.append(f'<line x1="{lx}" x2="{lx}" y1="16" y2="32" {stroke("ink")} stroke-width="1.5"/>')
    out.append(f'<line x1="{lx-3}" x2="{lx+3}" y1="16" y2="16" {stroke("ink")} stroke-width="1.5"/>')
    out.append(f'<line x1="{lx-3}" x2="{lx+3}" y1="32" y2="32" {stroke("ink")} stroke-width="1.5"/>')
    out.append(f'<text x="{lx+10}" y="28" font-size="13" {fill("secondary")}>quartiles · bar = median of 5 trials · × never found</text>')
    out.append('</svg>')
    return "\n".join(out)

LIGHT = {"surface": "#fcfcfb", "primary": "#0b0b0b", "secondary": "#52514e", "muted": "#7a7974",
         "grid": "#ecebe8", "axis": "#c9c8c3", "ink": "#0b0b0b",
         "s1": "#2a78d6", "s2": "#eb6834", "s3": "#1baf7a", "s4": "#eda100"}
VARS = {k: f"var(--{k})" for k in LIGHT}

open("experiments/minicedar/chart-light.svg", "w").write(svg(LIGHT, False))

table_rows = "\n".join(
    f'<tr><td>{d["bug"]}</td><td>{d["cls"]}</td><td>{d["armLabel"]}</td><td>{d["found"]}/{d["n"]}</td>'
    + (f'<td>{d["mean"]:,.0f}</td><td>{d["q1"]:,.0f}</td><td>{d["med"]:,.0f}</td><td>{d["q3"]:,.0f}</td>'
       f'<td>{d["typed"]}/{d["found"]}</td>' if d["found"] else '<td colspan="5">not found</td>')
    + '</tr>' for d in data)

legend = "".join(f'<span class="key"><span class="sw" style="background:var(--s{i+1})"></span>{lab}</span>'
                 for i, (_, _, lab) in enumerate(ARMS))

page = f"""<!doctype html>
<html lang="en"><head><meta charset="utf-8">
<title>MiniCedar: runs to failure per planted optimizer bug</title>
<style>
.viz-root {{
  color-scheme: light;
  --surface: #fcfcfb; --primary: #0b0b0b; --secondary: #52514e; --muted: #7a7974;
  --grid: #ecebe8; --axis: #c9c8c3; --ink: #0b0b0b;
  --s1: #2a78d6; --s2: #eb6834; --s3: #1baf7a; --s4: #eda100;
}}
@media (prefers-color-scheme: dark) {{
  :root:where(:not([data-theme="light"])) .viz-root {{
    color-scheme: dark;
    --surface: #1a1a19; --primary: #ffffff; --secondary: #c3c2b7; --muted: #8f8e87;
    --grid: #2a2a28; --axis: #4a4a46; --ink: #ffffff;
    --s1: #3987e5; --s2: #d95926; --s3: #199e70; --s4: #c98500;
  }}
}}
:root[data-theme="dark"] .viz-root {{
  color-scheme: dark;
  --surface: #1a1a19; --primary: #ffffff; --secondary: #c3c2b7; --muted: #8f8e87;
  --grid: #2a2a28; --axis: #4a4a46; --ink: #ffffff;
  --s1: #3987e5; --s2: #d95926; --s3: #199e70; --s4: #c98500;
}}
body {{ margin: 0; }}
.viz-root {{ background: var(--surface); color: var(--primary); padding: 24px 28px;
  font-family: system-ui, -apple-system, "Segoe UI", sans-serif; }}
h1 {{ font-size: 18px; font-weight: 600; margin: 0 0 4px; }}
.sub {{ color: var(--secondary); font-size: 13px; margin: 0 0 14px; max-width: 1100px; line-height: 1.45; }}
.legend {{ display: flex; gap: 18px; flex-wrap: wrap; font-size: 13px; color: var(--primary); margin-bottom: 6px; }}
.key {{ display: inline-flex; align-items: center; gap: 6px; }}
.sw {{ width: 12px; height: 12px; border-radius: 3px; display: inline-block; }}
svg {{ max-width: 100%; height: auto; display: block; }}
.hit:hover, .hit:focus {{ fill: var(--primary); fill-opacity: .06; outline: none; }}
#tip {{ position: fixed; pointer-events: none; background: var(--surface); color: var(--primary);
  border: 1px solid var(--axis); border-radius: 6px; padding: 8px 10px; font-size: 12px; line-height: 1.45;
  white-space: pre; box-shadow: 0 2px 10px rgba(0,0,0,.12); display: none; font-variant-numeric: tabular-nums; }}
details {{ margin-top: 12px; font-size: 13px; }}
table {{ border-collapse: collapse; margin-top: 8px; font-variant-numeric: tabular-nums; }}
th, td {{ padding: 3px 10px; border-bottom: 1px solid var(--grid); text-align: right; }}
th:nth-child(-n+3), td:nth-child(-n+3) {{ text-align: left; }}
th {{ color: var(--secondary); font-weight: 600; }}
</style></head>
<body><div class="viz-root">
<h1>Runs to failure, per planted optimizer bug</h1>
<p class="sub">Property: the optimizer preserves evaluation (<code>prop_optimize_sound</code>). Bar top is the median over
5 trials; whiskers span the 25th–75th percentile. A trial that found nothing within 1M runs counts as 1M, so the bar is a
lower bound, labelled with the fraction found; × means no trial found it. Counts are runs, not time: FuzzGen runs at about
half the rate of random.</p>
{svg(VARS, True)}
<details><summary>Table view</summary>
<table><thead><tr><th>bug</th><th>class</th><th>arm</th><th>found</th><th>mean</th><th>Q1</th><th>median</th><th>Q3</th>
<th>well-typed</th></tr></thead><tbody>
{table_rows}
</tbody></table></details>
<div id="tip" role="tooltip"></div>
</div>
<script>
const tip = document.getElementById('tip');
function show(e, el) {{
  tip.textContent = el.dataset.tip; tip.style.display = 'block';
  const r = el.getBoundingClientRect();
  const x = (e && e.clientX) || (r.left + r.width / 2), y = (e && e.clientY) || r.top + 40;
  const w = tip.offsetWidth;
  tip.style.left = Math.min(x + 14, innerWidth - w - 8) + 'px';
  tip.style.top = (y + 14) + 'px';
}}
document.querySelectorAll('.hit').forEach(el => {{
  el.addEventListener('mousemove', e => show(e, el));
  el.addEventListener('focus', () => show(null, el));
  el.addEventListener('mouseleave', () => tip.style.display = 'none');
  el.addEventListener('blur', () => tip.style.display = 'none');
}});
</script>
</body></html>
"""
open("experiments/minicedar/chart.html", "w").write(page)
print(json.dumps([d for d in data if d["bug"] in ("eq-refl", "record-last")], indent=0)[:600])
