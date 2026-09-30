#!/usr/bin/env python3
# Copyright (c) 2026 Harrison Goldstein. All rights reserved.
# Released under MIT license as described in the file LICENSE.
# Authors: Michael Hicks
"""Coverage and input diversity as a function of tests run, as an HTML page with SVG charts.

Reads `fuzz-run/compare-coverage.sh` output directories whose property printed `BASALT_H` lines
(`wide-traced`, `wide-traced-ef`). Each `<arm>.<t>.cov` gives, per edge, the index of the first test
that hit it, so coverage after n tests is the number of package edges with first-hit index <= n; each
`<arm>.<t>.log` gives the hash of every test's expression, in order.

  fuzz-run/coverage-curves.py OUT.html LABEL=DIR:ARM [LABEL=DIR:ARM ...]
"""
import bisect, html, json, math, re, sys

PREFIX = "lp_Cedar_"
# The traced properties hash `reprStr` of each input, which runs the package's derived printing code;
# that is measurement machinery, not code under test, so it is excluded from the coverage count.
EXCLUDE = re.compile(r"[Rr]epr|[Ff]ormat|[Tt]oString")
out_path = sys.argv[1]
specs = []
for a in sys.argv[2:]:
    label, rest = a.split("=", 1)
    d, arm = rest.rsplit(":", 1)
    specs.append((label, d, arm))

def points(maxn):
    xs, x = [], 1.0
    while x < maxn:
        xs.append(int(x)); x *= 1.25
    xs.append(maxn)
    return sorted(set(xs))

sym_cache = {}
def symbols(d):
    if d not in sym_cache:
        addrs, names = [], []
        for line in open(f"{d}/syms.txt"):
            a, n = line.split(); addrs.append(int(a, 16)); names.append(n)
        sym_cache[d] = (addrs, names)
    return sym_cache[d]

def trials(d, arm):
    ts = []
    t = 1
    while True:
        try:
            open(f"{d}/{arm}.{t}.cov").close()
        except FileNotFoundError:
            return ts
        ts.append(t); t += 1

series = []
for label, d, arm in specs:
    addrs, names = symbols(d)
    cov_curves, uniq_curves = [], []
    for t in trials(d, arm):
        firsts = []
        for line in open(f"{d}/{arm}.{t}.cov"):
            o, f = line.split()
            if f == "0": continue
            i = bisect.bisect_right(addrs, int(o, 16)) - 1
            n = names[i]
            if (n.startswith(PREFIX) or n.startswith("_init_" + PREFIX)) and not EXCLUDE.search(n):
                firsts.append(int(f))
        firsts.sort()
        seen, uniq = set(), []
        for line in open(f"{d}/{arm}.{t}.log", errors="replace"):
            if line.startswith("BASALT_H "):
                seen.add(line.split()[1]); uniq.append(len(seen))
        n = len(uniq)
        xs = points(n)
        cov_curves.append([(x, bisect.bisect_right(firsts, x)) for x in xs])
        uniq_curves.append([(x, uniq[x - 1]) for x in xs])
    def mean(curves):
        m = min(len(c) for c in curves)
        return [(curves[0][i][0], sum(c[i][1] for c in curves) / len(curves)) for i in range(m)]
    series.append({"label": label, "cov": mean(cov_curves), "uniq": mean(uniq_curves),
                   "trials": len(cov_curves)})

COLORS = [f"var(--series-{i})" for i in range(1, 6)]
W, H = 560, 320
ML, MR, MT, MB = 64, 150, 16, 44

def chart(key, title, ylabel, cid):
    maxx = max(s[key][-1][0] for s in series)
    maxy = max(max(y for _, y in s[key]) for s in series)
    top = 10 ** math.ceil(math.log10(maxy)) if maxy > 0 else 1
    step = top / 5
    while top - step >= maxy * 1.02 and top > step: top -= step
    lx0, lx1 = 0.0, math.log10(maxx)
    pw, ph = W - ML - MR, H - MT - MB
    sx = lambda x: ML + (math.log10(x) - lx0) / (lx1 - lx0) * pw
    sy = lambda y: MT + ph - y / top * ph
    g = [f'<svg viewBox="0 0 {W} {H}" role="img" aria-labelledby="{cid}-t" class="chart" id="{cid}">',
         f'<title id="{cid}-t">{html.escape(title)}</title>']
    for k in range(6):
        y = top * k / 5
        g.append(f'<line class="grid" x1="{ML}" x2="{ML+pw}" y1="{sy(y):.1f}" y2="{sy(y):.1f}"/>')
        g.append(f'<text class="tick" x="{ML-8}" y="{sy(y)+4:.1f}" text-anchor="end">{int(y):,}</text>')
    e = 0
    while 10 ** e <= maxx:
        x = 10 ** e
        g.append(f'<text class="tick" x="{sx(x):.1f}" y="{MT+ph+18}" text-anchor="middle">'
                 f'{"1" if e == 0 else ("10" if e == 1 else f"1e{e}")}</text>')
        e += 1
    g.append(f'<line class="axis" x1="{ML}" x2="{ML+pw}" y1="{MT+ph}" y2="{MT+ph}"/>')
    g.append(f'<text class="axis-label" x="{ML+pw/2}" y="{H-6}" text-anchor="middle">tests run (log scale)</text>')
    g.append(f'<text class="axis-label" transform="translate(14,{MT+ph/2}) rotate(-90)" text-anchor="middle">{html.escape(ylabel)}</text>')
    labels = []
    for i, s in enumerate(series):
        pts = " ".join(f"{sx(x):.1f},{sy(y):.1f}" for x, y in s[key])
        g.append(f'<polyline class="line" style="stroke:{COLORS[i]}" points="{pts}"/>')
        lx, ly = s[key][-1]
        labels.append([sy(ly), i, f"{s['label']}: {int(ly):,}"])
    labels.sort()
    for j in range(1, len(labels)):
        if labels[j][0] - labels[j-1][0] < 14: labels[j][0] = labels[j-1][0] + 14
    for yy, i, text in labels:
        g.append(f'<circle cx="{ML+pw:.1f}" cy="{sy(series[i][key][-1][1]):.1f}" r="4" '
                 f'style="fill:{COLORS[i]}" class="endpoint"/>')
        g.append(f'<text class="direct" x="{ML+pw+10}" y="{yy+4:.1f}">{html.escape(text)}</text>')
    g.append(f'<line class="crosshair" id="{cid}-x" x1="0" x2="0" y1="{MT}" y2="{MT+ph}" visibility="hidden"/>')
    g.append(f'<rect class="hit" x="{ML}" y="{MT}" width="{pw}" height="{ph}" '
             f'data-chart="{cid}" data-key="{key}" data-ml="{ML}" data-pw="{pw}" data-lx1="{lx1}"/>')
    g.append('</svg>')
    return "\n".join(g)

def table(key, ylabel):
    xs = [x for x, _ in series[0][key]]
    marks = [x for x in xs if x in (10, 100, 1000, 10000, 100000, 1000000) or x == xs[-1]]
    rows = ["<tr><th>tests</th>" + "".join(f"<th>{html.escape(s['label'])}</th>" for s in series) + "</tr>"]
    for x in sorted(set(marks)):
        cells = []
        for s in series:
            d = dict(s[key]); cells.append(f"<td>{int(d.get(x, float('nan'))):,}</td>" if x in d else "<td>–</td>")
        rows.append(f"<tr><td>{x:,}</td>{''.join(cells)}</tr>")
    return f"<table><caption>{html.escape(ylabel)}</caption>{''.join(rows)}</table>"

legend = "".join(f'<span class="key"><span class="swatch" style="background:{COLORS[i]}"></span>'
                 f'{html.escape(s["label"])} ({s["trials"]} trials)</span>' for i, s in enumerate(series))
data = json.dumps({s["label"]: {"cov": s["cov"], "uniq": s["uniq"]} for s in series})

page = f"""<!doctype html><html><head><meta charset="utf-8">
<title>Cedar coverage and input diversity vs. tests run</title>
<style>
.viz-root {{ color-scheme: light; --surface-1:#fcfcfb; --text-primary:#0b0b0b; --text-secondary:#52514e;
  --text-muted:#8a8984; --grid:#e6e5e0; --series-1:#2a78d6; --series-2:#eb6834; --series-3:#1baf7a;
  --series-4:#eda100; --series-5:#e87ba4; }}
@media (prefers-color-scheme: dark) {{ :root:where(:not([data-theme="light"])) .viz-root {{
  color-scheme: dark; --surface-1:#1a1a19; --text-primary:#ffffff; --text-secondary:#c3c2b7;
  --text-muted:#8f8e86; --grid:#2e2e2c; --series-1:#3987e5; --series-2:#d95926; --series-3:#199e70;
  --series-4:#c98500; --series-5:#d55181; }} }}
:root[data-theme="dark"] .viz-root {{ color-scheme: dark; --surface-1:#1a1a19; --text-primary:#ffffff;
  --text-secondary:#c3c2b7; --text-muted:#8f8e86; --grid:#2e2e2c; --series-1:#3987e5; --series-2:#d95926;
  --series-3:#199e70; --series-4:#c98500; --series-5:#d55181; }}
body {{ margin:0; }}
.viz-root {{ background:var(--surface-1); color:var(--text-primary); font:14px/1.4 system-ui,sans-serif;
  padding:20px; max-width:1200px; }}
h1 {{ font-size:18px; font-weight:600; margin:0 0 4px; }} p.sub {{ color:var(--text-secondary); margin:0 0 12px; }}
.legend {{ display:flex; gap:18px; flex-wrap:wrap; margin:8px 0 12px; color:var(--text-secondary); }}
.swatch {{ display:inline-block; width:12px; height:12px; border-radius:3px; margin-right:6px; vertical-align:-1px; }}
.charts {{ display:grid; grid-template-columns:repeat(auto-fit,minmax(480px,1fr)); gap:24px; }}
figure {{ margin:0; position:relative; }} figcaption {{ font-weight:600; margin-bottom:4px; }}
.chart {{ width:100%; height:auto; overflow:visible; }}
.grid {{ stroke:var(--grid); stroke-width:1; }} .axis {{ stroke:var(--text-muted); stroke-width:1; }}
.tick {{ fill:var(--text-muted); font-size:11px; }} .axis-label {{ fill:var(--text-secondary); font-size:12px; }}
.line {{ fill:none; stroke-width:2; stroke-linejoin:round; stroke-linecap:round; }}
.endpoint {{ stroke:var(--surface-1); stroke-width:2; }}
.direct {{ fill:var(--text-primary); font-size:12px; }}
.crosshair {{ stroke:var(--text-muted); stroke-width:1; stroke-dasharray:3 3; }}
.hit {{ fill:transparent; cursor:crosshair; }}
.tip {{ position:absolute; pointer-events:none; background:var(--surface-1); color:var(--text-primary);
  border:1px solid var(--grid); border-radius:6px; padding:6px 8px; font-size:12px;
  box-shadow:0 2px 8px rgba(0,0,0,.12); display:none; white-space:nowrap; }}
details {{ margin-top:16px; color:var(--text-secondary); }}
table {{ border-collapse:collapse; margin:8px 16px 8px 0; display:inline-table; font-variant-numeric:tabular-nums; }}
caption {{ text-align:left; font-weight:600; color:var(--text-primary); padding-bottom:4px; }}
th, td {{ border-bottom:1px solid var(--grid); padding:3px 10px; text-align:right; }}
</style></head><body><div class="viz-root">
<h1>Cedar coverage and input diversity vs. tests run</h1>
<p class="sub">Property <code>wide-soundness</code> (CedarWide generator). Mean of trials; x axis is the number of tests run.</p>
<div class="legend">{legend}</div>
<div class="charts">
<figure><figcaption>Cedar code coverage</figcaption>{chart("cov", "Cedar edges covered vs. tests run", "Cedar edges covered", "c1")}<div class="tip" id="c1-tip"></div></figure>
<figure><figcaption>Distinct expressions generated</figcaption>{chart("uniq", "Distinct expressions vs. tests run", "distinct expressions", "c2")}<div class="tip" id="c2-tip"></div></figure>
</div>
<details><summary>Table view</summary>{table("cov", "Cedar edges covered")}{table("uniq", "Distinct expressions")}</details>
</div>
<script>
const DATA = {data};
const COLORS = {json.dumps(COLORS)};
document.querySelectorAll('.hit').forEach(r => {{
  const cid = r.dataset.chart, key = r.dataset.key, svg = document.getElementById(cid);
  const tip = document.getElementById(cid + '-tip'), cross = document.getElementById(cid + '-x');
  const ml = +r.dataset.ml, pw = +r.dataset.pw, lx1 = +r.dataset.lx1;
  r.addEventListener('mousemove', ev => {{
    const pt = svg.createSVGPoint(); pt.x = ev.clientX; pt.y = ev.clientY;
    const p = pt.matrixTransform(svg.getScreenCTM().inverse());
    const x = Math.pow(10, Math.max(0, Math.min(1, (p.x - ml) / pw)) * lx1);
    let rows = '', near = null;
    Object.entries(DATA).forEach(([label, s], i) => {{
      const c = s[key]; let best = c[0];
      for (const q of c) if (Math.abs(Math.log(q[0]) - Math.log(x)) < Math.abs(Math.log(best[0]) - Math.log(x))) best = q;
      near = best[0];
      rows += `<div><span class="swatch" style="background:${{COLORS[i]}}"></span>${{label}}: <b>${{Math.round(best[1]).toLocaleString()}}</b></div>`;
    }});
    const sx = ml + Math.log10(near) / lx1 * pw;
    cross.setAttribute('x1', sx); cross.setAttribute('x2', sx); cross.setAttribute('visibility', 'visible');
    tip.innerHTML = `<div>${{near.toLocaleString()}} tests</div>` + rows;
    tip.style.display = 'block';
    const box = svg.getBoundingClientRect(), fb = svg.parentElement.getBoundingClientRect();
    tip.style.left = (ev.clientX - fb.left + 14) + 'px'; tip.style.top = (ev.clientY - fb.top + 10) + 'px';
  }});
  r.addEventListener('mouseleave', () => {{ tip.style.display = 'none'; cross.setAttribute('visibility', 'hidden'); }});
}});
</script></body></html>"""
open(out_path, "w").write(page)
print(f"wrote {out_path}")
print(f"\n{'tests':>10}  " + "  ".join(f"{s['label'][:22]:>22}" for s in series) + "   (Cedar edges / distinct expressions)")
for target in [10, 100, 1000, 10000, 100000, 1000000, 10000000]:
    if target > max(s["cov"][-1][0] for s in series) * 1.01: break
    cells = []
    for s in series:
        c = min(s["cov"], key=lambda p: abs(p[0] - target)); u = min(s["uniq"], key=lambda p: abs(p[0] - target))
        cells.append(f"{int(c[1]):>9,} / {int(u[1]):>10,}")
    print(f"{target:>10,}  " + "  ".join(f"{c:>22}" for c in cells))
print()
for s in series:
    print(f"{s['label']:32} final coverage {s['cov'][-1][1]:8.0f}   distinct expressions {s['uniq'][-1][1]:9.0f}"
          f"   at {s['cov'][-1][0]:,} tests")
