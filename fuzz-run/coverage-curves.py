#!/usr/bin/env python3
# Copyright (c) 2026 Harrison Goldstein. All rights reserved.
# Released under MIT license as described in the file LICENSE.
# Authors: Michael Hicks
"""Coverage and input diversity as a function of tests run, as an HTML page with SVG charts.

Reads `fuzz-run/compare-coverage.sh` output directories whose property printed `BASALT_H` lines
(`wide-traced`, `wide-traced-ef`). Each `<arm>.<t>.cov` gives, per edge, the index of the first test
that hit it, so coverage after n tests is the number of package edges with first-hit index <= n; each
`<arm>.<t>.log` gives the hash of every test's expression, in order. Where `<arm>.<t>.cov.time` exists
(milliseconds at every 1000th test), the same two curves are also drawn against elapsed time. The
page's subtitle names `$PROP`, which `cedar-experiment.sh` exports. `--linear` draws the same panels
on a linear x axis, plus the first 100 seconds of each time panel.

  fuzz-run/coverage-curves.py [--linear] OUT.html LABEL=DIR:ARM [LABEL=DIR:ARM ...]
"""
import bisect, html, json, math, os, re, sys

PREFIX = "lp_Cedar_"
# The traced properties hash `reprStr` of each input, which runs the package's derived printing code;
# that is measurement machinery, not code under test, so it is excluded from the coverage count.
EXCLUDE = re.compile(r"[Rr]epr|[Ff]ormat|[Tt]oString")
args = sys.argv[1:]
LINEAR = args[0] == "--linear"
if LINEAR: args = args[1:]
out_path = args[0]
specs = []
for a in args[1:]:
    label, rest = a.split("=", 1)
    d, arm = rest.rsplit(":", 1)
    specs.append((label, d, arm))

def points(maxn, steps=()):
    """Geometric sample points up to `maxn`, plus every multiple of `step` below `bound` for each
    `(step, bound)`, so that a linear axis is not drawn from a handful of points. The steps must not
    depend on the trial: the mean over trials pairs their points by index."""
    xs, x = [], 1.0
    while x < maxn:
        xs.append(int(x)); x *= 1.25
    for step, bound in steps:
        xs += range(step, min(maxn, bound), step)
    xs.append(maxn)
    return sorted(set(xs))

sym_cache = {}
def symbols(d):
    if d not in sym_cache:
        addrs, names = [], []
        for line in open(f"{d}/syms.txt"):
            a, n = line.split(); addrs.append(int(a, 16)); names.append(n.removeprefix("_") if n.startswith("_lp_") or n.startswith("__init_") else n)
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

RUNS = int(os.environ.get("RUNS", 0)) or 10 ** 6
series = []
for label, d, arm in specs:
    addrs, names = symbols(d)
    cov_curves, uniq_curves, covt_curves, uniqt_curves = [], [], [], []
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
        xs = points(n, [(max(1, RUNS // 500), n)])
        cov_curves.append([(x, bisect.bisect_right(firsts, x)) for x in xs])
        uniq_curves.append([(x, uniq[x - 1]) for x in xs])
        try:
            ticks = [(0, 0)] + [tuple(map(int, l.split())) for l in open(f"{d}/{arm}.{t}.cov.time")]
        except FileNotFoundError:
            continue
        tms = [ms for _, ms in ticks]
        def tests_by(sec):
            i = bisect.bisect_right(tms, sec * 1000) - 1
            if i >= len(ticks) - 1: return min(ticks[-1][0], n)
            (n0, t0), (n1, t1) = ticks[i], ticks[i + 1]
            return min(n, n0 + (n1 - n0) * (sec * 1000 - t0) // max(t1 - t0, 1))
        secs = points(max(1, tms[-1] // 1000), [(1, 100), (10, 10 ** 9)])
        covt_curves.append([(x, bisect.bisect_right(firsts, tests_by(x))) for x in secs])
        uniqt_curves.append([(x, uniq[max(tests_by(x), 1) - 1]) for x in secs])
    def mean(curves):
        if not curves: return []
        m = min(len(c) for c in curves)
        return [(curves[0][i][0], sum(c[i][1] for c in curves) / len(curves)) for i in range(m)]
    series.append({"label": label, "cov": mean(cov_curves), "uniq": mean(uniq_curves),
                   "covt": mean(covt_curves), "uniqt": mean(uniqt_curves),
                   "trials": len(cov_curves)})
timed = all(s["covt"] for s in series)
# Where the zoomed panels start: a tenth of the way through, in log terms — late enough that every arm
# is past its steep early climb.
ZOOM_TESTS = 10 ** max(1, int(math.log10(min(s["cov"][-1][0] for s in series))) - 2)
ZOOM_SECS = 10 ** max(0, int(math.log10(min(s["covt"][-1][0] for s in series))) - 1) if timed else 1

COLORS = [f"var(--series-{i})" for i in range(1, 6)]
W, H = 560, 320
ML, MR, MT, MB = 64, 170, 16, 44

def compact(v):
    """A tick label: `3.2M`, `800k`, or the number itself below 10,000."""
    if v >= 1e6: return f"{v / 1e6:.1f}M".replace(".0M", "M")
    if v >= 1e4: return f"{v / 1e3:.0f}k"
    return f"{int(v):,}"

def axis_ticks(lo, hi, seconds):
    """Linear x ticks: round numbers of tests, or of minutes once a time axis passes 5 minutes."""
    if seconds and hi > 300:
        step = next(m * 60 for m in (1, 2, 5, 10, 15, 20, 30, 60) if m * 60 >= (hi - lo) / 6)
        label = lambda v: f"{v // 60:g} min"
    else:
        raw = (hi - lo) / 6
        step = next(m * 10 ** e for e in range(0, 12) for m in (1, 2, 5) if m * 10 ** e >= raw)
        label = lambda v: f"{v:g} s" if seconds else compact(v)
    v = math.ceil(lo / step) * step
    while v <= hi + 1e-9:
        yield v, label(v); v += step

def chart(key, title, ylabel, cid, xlabel="tests run", xmin=1, xmax=None):
    """A chart of `key`, log-x unless `--linear`. With `xmin` above 1 it is a zoom on the tail: only
    points from `xmin` on, and a y axis fitted to them rather than starting at 0, which is where the
    arms differ. `xmax` cuts it off at the other end, with the y axis fitted the same way."""
    seconds = key.endswith("t")
    curves = [[(x, y) for x, y in s[key] if x >= xmin and (xmax is None or x <= xmax)] for s in series]
    maxx = max(c[-1][0] for c in curves)
    ys = [y for c in curves for _, y in c]
    fit = xmin > 1 or xmax is not None
    lo_y, hi_y = (min(ys), max(ys)) if fit else (0, max(ys))
    raw = (hi_y - lo_y) / 5 or 1
    step = next(m * 10 ** e for e in range(0, 12) for m in (1, 2, 5) if m * 10 ** e >= raw)
    bot = (lo_y // step) * step if fit else 0
    top = bot + step * math.ceil((hi_y - bot) / step + 1e-9)
    tf = (lambda x: x) if LINEAR else math.log10
    x0 = (0 if xmin <= 1 else xmin) if LINEAR else xmin
    lx0, lx1 = tf(x0), tf(maxx)
    pw, ph = W - ML - MR, H - MT - MB
    sx = lambda x: ML + (tf(x) - lx0) / (lx1 - lx0) * pw
    sy = lambda y: MT + ph - (y - bot) / (top - bot) * ph
    g = [f'<svg viewBox="0 0 {W} {H}" role="img" aria-labelledby="{cid}-t" class="chart" id="{cid}">',
         f'<title id="{cid}-t">{html.escape(title)}</title>']
    k = 0
    while bot + k * step <= top + 1e-9:
        y = bot + k * step
        g.append(f'<line class="grid" x1="{ML}" x2="{ML+pw}" y1="{sy(y):.1f}" y2="{sy(y):.1f}"/>')
        g.append(f'<text class="tick" x="{ML-8}" y="{sy(y)+4:.1f}" text-anchor="end">{compact(y)}</text>')
        k += 1
    if LINEAR:
        xticks = list(axis_ticks(x0, maxx, seconds))
    else:
        xticks, e = [], math.ceil(lx0 - 1e-9)
        while 10 ** e <= maxx:
            xticks.append((10 ** e, "1" if e == 0 else ("10" if e == 1 else f"1e{e}"))); e += 1
    for x, text in xticks:
        g.append(f'<text class="tick" x="{sx(x):.1f}" y="{MT+ph+18}" text-anchor="middle">{text}</text>')
    xlabel = f"{xlabel} ({'linear' if LINEAR else 'log'} scale)"
    g.append(f'<line class="axis" x1="{ML}" x2="{ML+pw}" y1="{MT+ph}" y2="{MT+ph}"/>')
    g.append(f'<text class="axis-label" x="{ML+pw/2}" y="{H-6}" text-anchor="middle">{xlabel}</text>')
    g.append(f'<text class="axis-label" transform="translate(12,{MT+ph/2}) rotate(-90)" text-anchor="middle">{html.escape(ylabel)}</text>')
    labels = []
    for i, c in enumerate(curves):
        pts = " ".join(f"{sx(x):.1f},{sy(y):.1f}" for x, y in c)
        g.append(f'<polyline class="line" style="stroke:{COLORS[i]}" points="{pts}"/>')
        lx, ly = c[-1]
        labels.append([sy(ly), i, f"{series[i]['label']}: {int(ly):,}"])
    labels.sort()
    for j in range(1, len(labels)):
        if labels[j][0] - labels[j-1][0] < 14: labels[j][0] = labels[j-1][0] + 14
    for yy, i, text in labels:
        g.append(f'<circle cx="{sx(curves[i][-1][0]):.1f}" cy="{sy(curves[i][-1][1]):.1f}" r="4" '
                 f'style="fill:{COLORS[i]}" class="endpoint"/>')
        g.append(f'<text class="direct" x="{ML+pw+10}" y="{yy+4:.1f}">{html.escape(text)}</text>')
    g.append(f'<line class="crosshair" id="{cid}-x" x1="0" x2="0" y1="{MT}" y2="{MT+ph}" visibility="hidden"/>')
    g.append(f'<rect class="hit" x="{ML}" y="{MT}" width="{pw}" height="{ph}" '
             f'data-chart="{cid}" data-key="{key}" data-ml="{ML}" data-pw="{pw}" data-lx0="{lx0}" '
             f'data-lx1="{lx1}" data-xmin="{xmin}" data-xmax="{maxx}" data-unit="{"s" if seconds else "tests"}"/>')
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
timed_figs = (f'''<figure><figcaption>Cedar code coverage, by time</figcaption>{chart("covt", "Cedar edges covered vs. seconds elapsed", "Cedar edges covered", "c3", "time elapsed")}<div class="tip" id="c3-tip"></div></figure>
<figure><figcaption>Distinct expressions, by time</figcaption>{chart("uniqt", "Distinct expressions vs. seconds elapsed", "distinct expressions", "c4", "time elapsed")}<div class="tip" id="c4-tip"></div></figure>
<figure><figcaption>Cedar code coverage, by time, from {ZOOM_SECS} s on (zoomed)</figcaption>{chart("covt", "Cedar edges covered vs. seconds elapsed, tail", "Cedar edges covered", "c6", "time elapsed", xmin=ZOOM_SECS)}<div class="tip" id="c6-tip"></div></figure>''' if timed else "")
if timed and LINEAR:
    timed_figs += f'''
<figure><figcaption>Cedar code coverage, first 100 s</figcaption>{chart("covt", "Cedar edges covered vs. seconds elapsed, first 100 s", "Cedar edges covered", "c7", "time elapsed", xmax=100)}<div class="tip" id="c7-tip"></div></figure>
<figure><figcaption>Distinct expressions, first 100 s</figcaption>{chart("uniqt", "Distinct expressions vs. seconds elapsed, first 100 s", "distinct expressions", "c8", "time elapsed", xmax=100)}<div class="tip" id="c8-tip"></div></figure>'''

# One entry per arm `cedar-experiment.sh` runs, keyed by its label or label prefix.
ARMS = [
    ("random", "uniform random choices inside libFuzzer's loop (<code>--backend=io-libfuzzer</code>), so "
               "coverage is counted identically: the control."),
    ("fuzz-noramp", "coverage-guided <code>FuzzGen</code> from a cold start, with "
                    "<code>-max_len=65536 -len_control=0</code>."),
    ("fuzz-grow", "coverage-guided <code>FuzzGen</code> with Basalt's <code>--grow</code>."),
    ("fuzz", "coverage-guided <code>FuzzGen</code> with libFuzzer's defaults (its input-length ramp on)."),
    ("warm-", "a fixed random warm-up of N tests (<code>--warmup=N</code>), then coverage-guided fuzzing "
              "seeded with the warm-up runs that reached new coverage, with fuzz-noramp's settings."),
    ("auto-", "a hybrid: random first, switching once to coverage-guided fuzzing when random's coverage "
              "levels off (<code>--warmup-stall=0 --level=φ</code>). The random runs that reached new "
              "coverage seed the fuzzer's corpus; it then fuzzes, with fuzz-noramp's settings, for the "
              "rest of the budget."),
    ("back-", "the same, but the level-off rule applies in both directions (<code>--switch-back "
              "--level=φ</code>): when fuzzing levels off it returns to random, and may switch again. "
              "libFuzzer's corpus stays in memory, so returning to fuzzing loses nothing."),
]
def describe(label):
    return next((d for k, d in ARMS if label == k or (k.endswith("-") and label.startswith(k))), None)
arm_items = "".join(f"<li><b>{html.escape(s['label'])}</b> — {describe(s['label'])}</li>"
                    for s in series if describe(s["label"]))
level_note = ("<p><b>φ</b> is <code>--level</code> (default 1). With <i>F</i> the tests so far that "
              "reached a new feature and <i>H</i> the tests left in the budget, a mode has levelled off "
              "when, over a window of tests, it finds new coverage more slowly than "
              "min(φ·<i>F</i>/<i>H</i>, <i>r</i><sub>other</sub>), where <i>r</i><sub>other</sub> is the "
              "other mode's find rate when it was last left. φ = 1: staying for the rest of the budget "
              "would only about double the finds so far. The <i>r</i><sub>other</sub> term hands over "
              "only to a mode that was doing better, which keeps the campaign from flip-flopping. The "
              "rule is owned by <code>fuzz-run/README.md</code>, “Random warm-up → When to switch”.</p>"
              if any(s["label"].startswith(("auto-", "back-")) for s in series) else "")
arms_block = (f"<details><summary>What the arms are</summary><p>Every arm runs the same instrumented "
              f"binary; only the source of the generator's choices differs.</p><ul>{arm_items}</ul>"
              f"{level_note}</details>" if arm_items else "")
jobs = int(os.environ.get("JOBS", 0))
contended = jobs and sum(s["trials"] for s in series) > jobs
time_note = (f"time elapsed, with trials run {jobs} at a time, so the time panels compare trials "
             f"that ran under different loads" if contended else "time elapsed, each trial on a core of its own")
data = json.dumps({s["label"]: {"cov": s["cov"], "uniq": s["uniq"], "covt": s["covt"],
                                "uniqt": s["uniqt"]} for s in series})

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
<p class="sub">Property <code>{html.escape(os.environ.get("PROP", "?"))}</code>. Mean of trials; the x axis is tests run, or (bottom rows) {time_note}.</p>
<div class="legend">{legend}</div>
<div class="charts">
<figure><figcaption>Cedar code coverage</figcaption>{chart("cov", "Cedar edges covered vs. tests run", "Cedar edges covered", "c1")}<div class="tip" id="c1-tip"></div></figure>
<figure><figcaption>Distinct expressions generated</figcaption>{chart("uniq", "Distinct expressions vs. tests run", "distinct expressions", "c2")}<div class="tip" id="c2-tip"></div></figure>
<figure><figcaption>Cedar code coverage, from {compact(ZOOM_TESTS)} tests on (zoomed)</figcaption>{chart("cov", "Cedar edges covered vs. tests run, tail", "Cedar edges covered", "c5", xmin=ZOOM_TESTS)}<div class="tip" id="c5-tip"></div></figure>
{timed_figs}
</div>
<details><summary>Table view</summary>{table("cov", "Cedar edges covered")}{table("uniq", "Distinct expressions")}</details>
{arms_block}
</div>
<script>
const DATA = {data};
const LIN = {json.dumps(LINEAR)}, tf = LIN ? (v => v) : Math.log10, itf = LIN ? (v => v) : (v => Math.pow(10, v));
const COLORS = {json.dumps(COLORS)};
document.querySelectorAll('.hit').forEach(r => {{
  const cid = r.dataset.chart, key = r.dataset.key, svg = document.getElementById(cid);
  const tip = document.getElementById(cid + '-tip'), cross = document.getElementById(cid + '-x');
  const ml = +r.dataset.ml, pw = +r.dataset.pw, lx0 = +r.dataset.lx0, lx1 = +r.dataset.lx1;
  const xmin = +r.dataset.xmin, xmax = +r.dataset.xmax;
  r.addEventListener('mousemove', ev => {{
    const pt = svg.createSVGPoint(); pt.x = ev.clientX; pt.y = ev.clientY;
    const p = pt.matrixTransform(svg.getScreenCTM().inverse());
    const x = itf(lx0 + Math.max(0, Math.min(1, (p.x - ml) / pw)) * (lx1 - lx0));
    let rows = '', near = null;
    Object.entries(DATA).forEach(([label, s], i) => {{
      const c = s[key].filter(q => q[0] >= xmin * 0.999 && q[0] <= xmax * 1.001); let best = c[0];
      for (const q of c) if (Math.abs(tf(q[0]) - tf(x)) < Math.abs(tf(best[0]) - tf(x))) best = q;
      near = best[0];
      rows += `<div><span class="swatch" style="background:${{COLORS[i]}}"></span>${{label}}: <b>${{Math.round(best[1]).toLocaleString()}}</b></div>`;
    }});
    const sx = ml + (tf(near) - lx0) / (lx1 - lx0) * pw;
    cross.setAttribute('x1', sx); cross.setAttribute('x2', sx); cross.setAttribute('visibility', 'visible');
    tip.innerHTML = `<div>${{near.toLocaleString()}} ${{r.dataset.unit}}</div>` + rows;
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
