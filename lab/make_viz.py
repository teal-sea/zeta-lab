"""Build lab/viz.html, a self-contained page of the lab's results (inline SVG, no network).

Run: lab/.venv/bin/python lab/make_viz.py
Reads lab/results/exp_{a,b,c,d}.json (d is optional and shown as pending if absent) and
lab/data/zeros_T100000.npz for the small visibility-graph illustration.
"""
import json
import sys
from pathlib import Path

import numpy as np

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
sys.path.insert(0, str(HERE.parent))
import hvg  # noqa: E402
from zeta.statistics import riemann_siegel_theta  # noqa: E402


def load(name):
    p = HERE / "results" / name
    return json.loads(p.read_text()) if p.exists() else None


def main() -> int:
    a, b, c, d = (load(f"exp_{x}.json") for x in "abcd")
    missing = [n for n, v in zip("abc", (a, b, c)) if v is None]
    if missing:
        print("MISSING results for experiment(s):", ", ".join(missing), file=sys.stderr)
        return 2
    g = np.load(HERE / "data" / "zeros_T100000.npz")["gammas"]
    s = np.diff(riemann_siegel_theta(g) / np.pi)
    start = 50000
    sample = s[start:start + 36]
    edges = hvg.hvg_edges(sample).tolist()
    t2 = a["tables"]["2000"]
    data = {
        "k": list(range(2, 13)),
        "iid": a["iid_law"][2:13],
        "zeta": t2["zeta"]["p"][2:13], "zeta_se": t2["zeta"]["se"][2:13],
        "gue": t2["gue_tridiag"]["p"][2:13], "gue_se": t2["gue_tridiag"]["se"][2:13],
        "z": t2["z_zeta_vs_gue"][2:13],
        "segments": [t2["zeta"]["segments"], t2["gue_tridiag"]["segments"]],
        "arrow": [{"name": k, "d2": v["d2_mean"], "se": v["d2_se"], "p": v["signflip_p"]}
                  for k, v in b.items() if isinstance(v, dict)],
        "cue": [{"N": e["N"], "pV": e["value"][0], "se": e["se"][0]} for e in c["cue"]],
        "gueC": {"pV": c["gue_tridiag"]["value"][0], "se": c["gue_tridiag"]["se"][0]},
        "zetaC": {"pV": c["zeta_T1e5"]["value"][0], "se": c["zeta_T1e5"]["se"][0]},
        "sample": sample.tolist(), "sample_start": start, "sample_t": float(g[start]),
        "edges": edges,
        "height": None,
    }
    if d is not None:
        data["height"] = {
            "L": [w["log_T_over_2pi"] for w in d["windows"]],
            "lo": [w["t_lo"] for w in d["windows"]], "hi": [w["t_hi"] for w in d["windows"]],
            "n": [w["n_gaps"] for w in d["windows"]],
            "ex": d["excess_pV"], "se": d["excess_pV_se"],
            "fit": d["fits"]["1/log^2, no intercept"],
        }
    html = TEMPLATE.replace("/*DATA*/null", json.dumps(data))
    out = HERE / "viz.html"
    out.write_text(html)
    print("wrote", out.relative_to(HERE.parent), len(html), "bytes; height panel:",
          "present" if d is not None else "PENDING (no exp_d.json)")
    return 0


TEMPLATE = r"""<!doctype html>
<html lang="en"><head><meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1">
<title>Zero Visibility Lab</title>
<style>
:root { color-scheme: light; --surface-1:#fcfcfb; --surface-2:#f2f1ed; --text-primary:#0b0b0b;
  --text-secondary:#52514e; --text-muted:#64635e; --grid:#e3e2de; --axis:#a9a8a2;
  --series-1:#2a78d6; --series-2:#eb6834; --series-3:#1baf7a; --critical:#d03b3b; }
@media (prefers-color-scheme: dark) { :root:where(:not([data-theme="light"])) { color-scheme: dark;
  --surface-1:#1a1a19; --surface-2:#242422; --text-primary:#f0efec; --text-secondary:#c3c2b7;
  --text-muted:#a3a299; --grid:#33332f; --axis:#6b6a64;
  --series-1:#3987e5; --series-2:#d95926; --series-3:#199e70; --critical:#e66767; } }
:root[data-theme="dark"] { color-scheme: dark;
  --surface-1:#1a1a19; --surface-2:#242422; --text-primary:#f0efec; --text-secondary:#c3c2b7;
  --text-muted:#a3a299; --grid:#33332f; --axis:#6b6a64;
  --series-1:#3987e5; --series-2:#d95926; --series-3:#199e70; --critical:#e66767; }
* { box-sizing: border-box; }
body { margin:0; background:var(--surface-1); color:var(--text-primary);
  font: 15px/1.55 ui-sans-serif, system-ui, -apple-system, "Segoe UI", sans-serif; }
main { max-width: 980px; margin: 0 auto; padding: 28px 16px 72px; }
h1 { font-size: 26px; margin: 0 0 4px; letter-spacing: -0.01em; }
h2 { font-size: 18px; margin: 40px 0 6px; }
p { margin: 6px 0; color: var(--text-secondary); max-width: 760px; }
.lede { color: var(--text-secondary); font-size: 16px; }
.tag { display:inline-block; font-size:12px; font-weight:600; padding:1px 8px; border-radius:10px;
  border:1px solid var(--axis); color:var(--text-primary); margin-right:6px; }
figure { margin: 14px 0 0; background: var(--surface-2); border-radius: 10px; padding: 12px 12px 6px; }
svg { width: 100%; height: auto; display: block; overflow: visible; }
svg text { fill: var(--text-secondary); font-size: 12px; }
svg .title { fill: var(--text-primary); font-size: 13px; font-weight: 600; }
.legend { display:flex; gap:16px; flex-wrap:wrap; font-size:13px; color:var(--text-secondary); margin: 2px 4px 8px; }
.legend i { display:inline-block; width:12px; height:12px; border-radius:6px; margin-right:6px; vertical-align:-1px; }
.legend i.dash { border-radius:0; height:0; width:16px; border-top:2px dashed var(--text-muted); vertical-align:3px; }
#tip { position: fixed; pointer-events: none; background: var(--surface-1); color: var(--text-primary);
  border: 1px solid var(--axis); border-radius: 8px; padding: 6px 9px; font-size: 12.5px;
  box-shadow: 0 4px 14px rgba(0,0,0,.18); opacity: 0; transition: opacity .08s; max-width: 280px; z-index: 9; }
details { margin-top: 10px; }
summary { cursor: pointer; color: var(--text-secondary); font-size: 13px; }
table { border-collapse: collapse; font-size: 12.5px; margin: 8px 0; font-variant-numeric: tabular-nums; }
td, th { padding: 3px 10px; border-bottom: 1px solid var(--grid); text-align: right; }
th { color: var(--text-secondary); font-weight: 600; }
.hit { fill: transparent; cursor: default; }
</style></head>
<body><main>
<h1>Zero visibility</h1>
<p class="lede">Each gap between consecutive zeta zeros becomes a node; two gaps are joined when every gap between
them is shorter than both (a horizontal visibility graph). For independent data the degree law is a theorem,
P(k) = (1/3)(2/3)<sup>k&minus;2</sup>. The zeros break it, and they break the random-matrix prediction too.</p>

<h2>1. A piece of the graph</h2>
<p>36 consecutive unfolded gaps starting at zero #<span id="s0"></span> (height &asymp; <span id="st"></span>).
Arcs are visibility edges. Blue bars are local minima: with sentinels at both ends, these are exactly the
degree-2 nodes.</p>
<figure><svg id="g1" viewBox="0 0 940 300" role="img" aria-label="Visibility graph of 36 zeta gaps"></svg></figure>

<h2>2. The degree law <span class="tag">OBSERVED</span></h2>
<p>Fraction of nodes with degree k, zeros up to T = 10<sup>5</sup> (138,068 gaps) against GUE random matrices
(600,000 gaps) and the i.i.d. theorem. Same protocol for both: segments of 2000 gaps, 25 nodes trimmed per end.</p>
<div class="legend"><span><i style="background:var(--series-1)"></i>zeta zeros</span>
<span><i style="background:var(--series-2)"></i>GUE</span><span><i class="dash"></i>i.i.d. theorem</span></div>
<figure><svg id="g2" viewBox="0 0 940 330" role="img" aria-label="HVG degree distributions"></svg></figure>
<figure><svg id="g2z" viewBox="0 0 940 200" role="img" aria-label="z-scores zeta minus GUE"></svg></figure>
<details><summary>Table view</summary><table id="t2"></table></details>

<h2>3. The wrong side of GUE <span class="tag">OBSERVED</span></h2>
<p>Fraction pV of gaps that are local minima. Finite-size CUE(N) random matrices approach the GUE value
from below as N grows. The zeros sit above it, 9 standard errors out, where no CUE(N) goes.</p>
<div class="legend"><span><i style="background:var(--series-3)"></i>CUE(N), x = 1/N&sup2;</span>
<span><i style="background:var(--series-2)"></i>GUE (N = &infin;)</span><span><i style="background:var(--series-1)"></i>zeta, T &le; 10<sup>5</sup></span></div>
<figure><svg id="g3" viewBox="0 0 940 330" role="img" aria-label="pV against 1/N squared"></svg></figure>

<h2>4. Does the excess fade with height?</h2>
<p id="hnote"></p>
<figure id="g4f"><svg id="g4" viewBox="0 0 940 320" role="img" aria-label="pV excess against height"></svg></figure>

<h2>5. No arrow of time <span class="tag">OBSERVED</span></h2>
<p>Signed irreversibility d2 = mean(k<sub>out</sub>&sup2;) &minus; mean(k<sub>in</sub>&sup2;) of the directed graph, mean &plusmn; 2 s.e.
over segments of 2000. A planted irreversible process sits far off; the zeros sit with the reversible controls.</p>
<figure><svg id="g5" viewBox="0 0 940 250" role="img" aria-label="Arrow of time statistic"></svg></figure>
<p style="margin-top:28px;font-size:13px">Generated by <code>lab/make_viz.py</code> from <code>lab/results/</code>.
Float-grade measurements; see <code>lab/RESULTS.md</code> for commands, labels and caveats.</p>
</main><div id="tip"></div>
<script>
const D = /*DATA*/null;
const NS = "http://www.w3.org/2000/svg";
const tip = document.getElementById("tip");
function el(p, name, attrs, text) { const e = document.createElementNS(NS, name);
  for (const [k, v] of Object.entries(attrs || {})) e.setAttribute(k, v);
  if (text !== undefined) e.textContent = text; p.appendChild(e); return e; }
function hover(e, html) { e.addEventListener("mousemove", ev => { tip.innerHTML = html; tip.style.opacity = 1;
  const x = Math.min(ev.clientX + 14, window.innerWidth - 290); tip.style.left = x + "px"; tip.style.top = (ev.clientY + 14) + "px"; });
  e.addEventListener("mouseleave", () => { tip.style.opacity = 0; }); }
function lin(d0, d1, r0, r1) { return v => r0 + (v - d0) * (r1 - r0) / (d1 - d0); }
function axes(svg, x0, x1, y0, y1, yt, yfmt, xt, xfmt, ylab, xlab) {
  for (const t of yt) { const y = t[0]; el(svg, "line", {x1: x0, x2: x1, y1: y, y2: y, stroke: "var(--grid)"});
    el(svg, "text", {x: x0 - 8, y: y + 4, "text-anchor": "end"}, yfmt(t[1])); }
  for (const t of xt) el(svg, "text", {x: t[0], y: y0 + 18, "text-anchor": "middle"}, xfmt(t[1]));
  el(svg, "line", {x1: x0, x2: x1, y1: y0, y2: y0, stroke: "var(--axis)"});
  if (ylab) el(svg, "text", {x: x0 - 52, y: (y0 + y1) / 2, transform: `rotate(-90 ${x0 - 52} ${(y0 + y1) / 2})`, "text-anchor": "middle"}, ylab);
  if (xlab) el(svg, "text", {x: (x0 + x1) / 2, y: y0 + 38, "text-anchor": "middle"}, xlab);
}
const f5 = v => v.toFixed(5);

// 1. graph piece
(() => { const svg = document.getElementById("g1"), s = D.sample, n = s.length;
  document.getElementById("s0").textContent = (D.sample_start + 1).toLocaleString();
  document.getElementById("st").textContent = Math.round(D.sample_t).toLocaleString();
  const x0 = 30, x1 = 920, base = 270, smax = Math.max(...s) * 1.05, X = i => x0 + (i + 0.5) * (x1 - x0) / n;
  const Y = lin(0, smax, base, 120);
  for (const [i, j] of D.edges) { const xa = X(i), xb = X(j), h = Math.min(105, 14 + 9 * (j - i));
    el(svg, "path", {d: `M${xa},${Y(s[i])} C${xa},${Y(s[i]) - h} ${xb},${Y(s[j]) - h} ${xb},${Y(s[j])}`,
      fill: "none", stroke: "var(--axis)", "stroke-width": 1.2, opacity: 0.9}); }
  const deg = new Array(n).fill(0); for (const [i, j] of D.edges) { deg[i]++; deg[j]++; }
  const w = (x1 - x0) / n - 6;
  s.forEach((v, i) => { const mn = i > 0 && i < n - 1 && s[i - 1] > v && v < s[i + 1];
    const r = el(svg, "rect", {x: X(i) - w / 2, y: Y(v), width: w, height: base - Y(v), rx: 4,
      fill: mn ? "var(--series-1)" : "var(--text-muted)", opacity: mn ? 1 : 0.45});
    hover(r, `gap #${D.sample_start + i + 1}<br>unfolded length ${v.toFixed(4)}<br>degree ${deg[i]}${mn ? " (local minimum)" : ""}`); });
  el(svg, "line", {x1: x0, x2: x1, y1: base, y2: base, stroke: "var(--axis)"});
})();

// 2. degree law (log scale)
(() => { const svg = document.getElementById("g2"), k = D.k;
  const x0 = 80, x1 = 900, y0 = 280, y1 = 20, X = lin(2, 12, x0 + 20, x1 - 20);
  const ly = v => Math.log10(v), Y = lin(ly(0.004), ly(0.4), y0, y1);
  const yt = [0.005, 0.01, 0.02, 0.05, 0.1, 0.2, 0.4].map(v => [Y(ly(v)), v]);
  axes(svg, x0, x1, y0, y1, yt, v => v, k.map(v => [X(v), v]), v => v, "fraction of nodes (log)", "degree k");
  const path = (arr, color, dash) => el(svg, "path", {d: arr.map((v, i) => `${i ? "L" : "M"}${X(k[i])},${Y(ly(v))}`).join(""),
    fill: "none", stroke: color, "stroke-width": 2, "stroke-dasharray": dash || ""});
  path(D.iid, "var(--text-muted)", "5 4"); path(D.gue, "var(--series-2)"); path(D.zeta, "var(--series-1)");
  k.forEach((kk, i) => { for (const [arr, col, r] of [[D.gue, "var(--series-2)", 4.5], [D.zeta, "var(--series-1)", 4.5]])
      el(svg, "circle", {cx: X(kk), cy: Y(ly(arr[i])), r, fill: col, stroke: "var(--surface-2)", "stroke-width": 2});
    const hit = el(svg, "rect", {class: "hit", x: X(kk) - 30, y: y1, width: 60, height: y0 - y1});
    hover(hit, `<b>k = ${kk}</b><br>zeta ${f5(D.zeta[i])} &plusmn; ${f5(D.zeta_se[i])}<br>GUE ${f5(D.gue[i])} &plusmn; ${f5(D.gue_se[i])}<br>i.i.d. ${f5(D.iid[i])}<br>z(zeta &minus; GUE) = ${D.z[i].toFixed(1)}`); });
  el(svg, "text", {x: X(12) + 6, y: Y(ly(D.iid[10])) - 6, "text-anchor": "end"}, "i.i.d.");
  const t = document.getElementById("t2");
  t.innerHTML = "<tr><th>k</th><th>zeta</th><th>&plusmn;</th><th>GUE</th><th>&plusmn;</th><th>i.i.d.</th><th>z(zeta&minus;GUE)</th></tr>" +
    k.map((kk, i) => `<tr><td>${kk}</td><td>${f5(D.zeta[i])}</td><td>${f5(D.zeta_se[i])}</td><td>${f5(D.gue[i])}</td><td>${f5(D.gue_se[i])}</td><td>${f5(D.iid[i])}</td><td>${D.z[i].toFixed(1)}</td></tr>`).join("");
})();

// 2b. z-scores
(() => { const svg = document.getElementById("g2z"), k = D.k;
  const x0 = 80, x1 = 900, y0 = 170, y1 = 20, X = lin(2, 12, x0 + 20, x1 - 20), Y = lin(-10, 10, y0, y1);
  axes(svg, x0, x1, y0, y1, [-9, -3, 0, 3, 9].map(v => [Y(v), v]), v => v, [], v => v, "z (zeta − GUE)", "");
  el(svg, "rect", {x: x0, y: Y(3), width: x1 - x0, height: Y(-3) - Y(3), fill: "var(--grid)", opacity: 0.6});
  el(svg, "text", {x: x1 - 4, y: Y(3) - 5, "text-anchor": "end"}, "±3σ band");
  k.forEach((kk, i) => { const z = D.z[i], top = Math.min(Y(z), Y(0)), h = Math.abs(Y(z) - Y(0));
    const r = el(svg, "rect", {x: X(kk) - 9, y: top, width: 18, height: Math.max(h, 1), rx: 4,
      fill: Math.abs(z) > 3 ? "var(--series-1)" : "var(--text-muted)", opacity: Math.abs(z) > 3 ? 1 : 0.5});
    hover(r, `k = ${kk}: z = ${z.toFixed(1)}`);
    el(svg, "text", {x: X(kk), y: y0 + 18, "text-anchor": "middle"}, kk); });
})();

// 3. CUE curve vs GUE vs zeta
(() => { const svg = document.getElementById("g3");
  const x0 = 80, x1 = 900, y0 = 280, y1 = 20, X = lin(-0.003, 0.066, x0, x1), Y = lin(0.3475, 0.3560, y0, y1);
  axes(svg, x0, x1, y0, y1, [0.348, 0.350, 0.352, 0.354, 0.356].map(v => [Y(v), v]), v => v.toFixed(3),
       [0, 1/64, 1/36, 1/16].map(v => [X(v), v]), v => v === 0 ? "0 (GUE)" : "1/" + Math.round(1 / v), "local-minimum fraction pV", "1/N²");
  const z = D.zetaC; el(svg, "rect", {x: x0, y: Y(z.pV + 2 * z.se), width: x1 - x0, height: Y(z.pV - 2 * z.se) - Y(z.pV + 2 * z.se), fill: "var(--series-1)", opacity: 0.16});
  el(svg, "line", {x1: x0, x2: x1, y1: Y(z.pV), y2: Y(z.pV), stroke: "var(--series-1)", "stroke-width": 2});
  el(svg, "text", {x: x1 - 6, y: Y(z.pV) - 8, "text-anchor": "end"}, `zeta zeros, T ≤ 1e5: ${f5(z.pV)} ± ${f5(z.se)}`);
  const g = D.gueC;
  for (const c of D.cue) { const cx = X(1 / c.N ** 2);
    el(svg, "line", {x1: cx, x2: cx, y1: Y(c.pV - 2 * c.se), y2: Y(c.pV + 2 * c.se), stroke: "var(--series-3)", "stroke-width": 2});
    const m = el(svg, "circle", {cx, cy: Y(c.pV), r: 5, fill: "var(--series-3)", stroke: "var(--surface-2)", "stroke-width": 2});
    hover(m, `CUE N = ${c.N}<br>pV ${f5(c.pV)} &plusmn; ${f5(c.se)}`);
    if ([4, 6, 8].includes(c.N)) el(svg, "text", {x: cx + 9, y: Y(c.pV) + 4}, "N = " + c.N); }
  el(svg, "line", {x1: X(0), x2: X(0), y1: Y(g.pV - 2 * g.se), y2: Y(g.pV + 2 * g.se), stroke: "var(--series-2)", "stroke-width": 2});
  const gm = el(svg, "circle", {cx: X(0), cy: Y(g.pV), r: 6, fill: "var(--series-2)", stroke: "var(--surface-2)", "stroke-width": 2});
  hover(gm, `GUE tridiagonal<br>pV ${f5(g.pV)} &plusmn; ${f5(g.se)}`);
  el(svg, "text", {x: X(0) + 10, y: Y(g.pV) + 16}, "GUE");
})();

// 4. height dependence
(() => { const H = D.height, note = document.getElementById("hnote");
  if (!H) { note.textContent = "Pending: the zeros up to 10^6 were still being scanned when this page was built.";
    document.getElementById("g4f").style.display = "none"; return; }
  note.innerHTML = "Excess pV(zeta) &minus; pV(GUE) in height windows of the zeros up to 10<sup>6</sup>, against 1/log&sup2;(T/2&pi;). The line is the weighted fit through the origin.";
  const svg = document.getElementById("g4"), xs = H.L.map(L => 1 / (L * L));
  const x0 = 80, x1 = 900, y0 = 270, y1 = 20, xmax = Math.max(...xs) * 1.08;
  const ymax = Math.max(...H.ex.map((e, i) => e + 2 * H.se[i])) * 1.1, ymin = Math.min(0, ...H.ex.map((e, i) => e - 2 * H.se[i])) * 1.1;
  const X = lin(0, xmax, x0, x1), Y = lin(ymin, ymax, y0, y1);
  const yt = []; for (let v = 0; v <= ymax; v += 0.002) yt.push([Y(v), v]);
  axes(svg, x0, x1, y0, y1, yt, v => v.toFixed(3), [0, 0.005, 0.01, 0.015, 0.02, 0.025, 0.03, 0.035, 0.04].filter(v => v <= xmax).map(v => [X(v), v]), v => v.toFixed(3), "pV excess over GUE", "1 / log²(T/2π)");
  const a = H.fit.coef[0]; el(svg, "line", {x1: X(0), x2: X(xmax), y1: Y(0), y2: Y(a * xmax), stroke: "var(--series-2)", "stroke-width": 2, "stroke-dasharray": "6 4"});
  xs.forEach((x, i) => { el(svg, "line", {x1: X(x), x2: X(x), y1: Y(H.ex[i] - 2 * H.se[i]), y2: Y(H.ex[i] + 2 * H.se[i]), stroke: "var(--series-1)", "stroke-width": 2});
    const m = el(svg, "circle", {cx: X(x), cy: Y(H.ex[i]), r: 5.5, fill: "var(--series-1)", stroke: "var(--surface-2)", "stroke-width": 2});
    hover(m, `T in [${H.lo[i].toExponential(0)}, ${H.hi[i].toExponential(0)})<br>${H.n[i].toLocaleString()} gaps<br>excess ${H.ex[i].toFixed(5)} &plusmn; ${H.se[i].toFixed(5)}`); });
  el(svg, "text", {x: X(xmax) - 6, y: Y(a * xmax) - 8, "text-anchor": "end"}, `fit: excess = ${a.toFixed(3)} / log²(T/2π), χ² = ${H.fit.chi2.toFixed(1)} on ${H.fit.dof} dof`);
})();

// 5. arrow of time
(() => { const svg = document.getElementById("g5"), A = D.arrow;
  const x0 = 250, x1 = 900, rowh = 36, X = lin(-1.5, 0.2, x0, x1);
  const names = {zeta_T1e5: "zeta zeros, T ≤ 1e5", zeta_shuffled: "zeta gaps shuffled", gue_tridiag: "GUE",
    planted_irreversible_ar1_exp: "planted irreversible AR(1)", planted_reversible_ar1_gauss: "planted reversible AR(1)"};
  for (const v of [-1.5, -1, -0.5, 0]) { el(svg, "line", {x1: X(v), x2: X(v), y1: 10, y2: 10 + rowh * A.length, stroke: "var(--grid)"});
    el(svg, "text", {x: X(v), y: 28 + rowh * A.length, "text-anchor": "middle"}, v); }
  A.forEach((r, i) => { const y = 28 + rowh * i, pl = r.name.startsWith("planted_irr");
    el(svg, "text", {x: x0 - 12, y: y + 4, "text-anchor": "end", style: "fill:var(--text-primary)"}, names[r.name] || r.name);
    el(svg, "line", {x1: X(r.d2 - 2 * r.se), x2: X(r.d2 + 2 * r.se), y1: y, y2: y, stroke: pl ? "var(--critical)" : "var(--series-1)", "stroke-width": 2});
    const m = el(svg, "circle", {cx: X(r.d2), cy: y, r: 5.5, fill: pl ? "var(--critical)" : "var(--series-1)", stroke: "var(--surface-2)", "stroke-width": 2});
    hover(m, `${names[r.name] || r.name}<br>d2 = ${r.d2.toFixed(4)} &plusmn; ${r.se.toFixed(4)}<br>sign-flip p = ${r.p < 1e-4 ? "&lt; 1e-4" : r.p.toFixed(3)}`); });
  el(svg, "text", {x: (x0 + x1) / 2, y: 48 + rowh * A.length, "text-anchor": "middle"}, "d2 = mean(k_out²) − mean(k_in²)");
})();
</script></body></html>
"""

if __name__ == "__main__":
    sys.exit(main())
