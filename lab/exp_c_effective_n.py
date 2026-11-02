"""Experiment C: does one effective CUE size explain three local statistics of the zeros?

Run: OPENBLAS_NUM_THREADS=1 lab/.venv/bin/python lab/exp_c_effective_n.py
Writes lab/results/exp_c.json and prints the table.

Three statistics of a gap sequence, none of them needing segments (so no truncation bias):
  pV   = fraction of strict local minima, s_{i-1} > s_i < s_{i+1} (the HVG degree-2 nodes);
  var  = variance of the gaps;
  rho1 = lag-1 autocorrelation of the gaps.
For CUE(N) each is computed on circular gaps; error bars are the spread over matrices. For
zeta and GUE, error bars come from blocks of BLOCK consecutive gaps.

Conjecture C: there is one N at which CUE(N) matches the zeros on all three statistics.
Each statistic is inverted separately through the CUE(N) curve (linear interpolation in
1/N^2 between simulated N) and the three effective sizes are compared.

Controls: raw gaps gamma_{n+1} - gamma_n (no unfolding) must give the same pV as the unfolded
gaps to within error, because unfolding only rescales by a slowly varying factor.
"""
import json
import sys
import time
from pathlib import Path

import numpy as np

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
sys.path.insert(0, str(HERE.parent))
import cue  # noqa: E402
from exp_a_degree_law import gue_tridiag_gaps  # noqa: E402
from zeta.statistics import riemann_siegel_theta  # noqa: E402

BLOCK = 2000
CUE_NS = [4, 6, 8, 12, 16, 24, 32, 48, 64]
CUE_GAPS = 1_200_000


def stats_seq(s: np.ndarray) -> np.ndarray:
    pv = np.mean((s[:-2] > s[1:-1]) & (s[1:-1] < s[2:]))
    v = np.var(s)
    r = np.corrcoef(s[:-1], s[1:])[0, 1]
    return np.array([pv, v, r])


def block_summary(s: np.ndarray) -> dict:
    nb = s.size // BLOCK
    rows = np.array([stats_seq(s[i * BLOCK:(i + 1) * BLOCK]) for i in range(nb)])
    return {"n_gaps": int(s.size), "blocks": int(nb), "dropped": int(s.size - nb * BLOCK),
            "value": stats_seq(s).tolist(),
            "se": (rows.std(axis=0, ddof=1) / np.sqrt(nb)).tolist()}


def cue_summary(n: int, rng: np.random.Generator) -> dict:
    rows = []
    need = CUE_GAPS // n
    while len(rows) < need:
        g = cue.cue_gaps(n, min(2000, need - len(rows)), rng)
        lm = cue.local_min_fraction(g)
        v = g.var(axis=1)
        gc = g - 1.0
        r = np.mean(gc * np.roll(gc, -1, axis=1), axis=1) / np.mean(gc * gc, axis=1)
        rows.extend(np.stack([lm, v, r], axis=1).tolist())
    rows = np.asarray(rows)
    # pooled estimates (ratio of means for rho1 and var), spread over matrices for errors
    return {"N": n, "matrices": int(rows.shape[0]),
            "value": rows.mean(axis=0).tolist(),
            "se": (rows.std(axis=0, ddof=1) / np.sqrt(rows.shape[0])).tolist()}


def invert(curve_n, curve_v, target):
    """N at which the CUE curve (as a function of x = 1/N^2) crosses `target`; None if never."""
    x = 1.0 / np.asarray(curve_n, float) ** 2
    y = np.asarray(curve_v, float)
    order = np.argsort(x)
    x, y = x[order], y[order]
    for i in range(len(x) - 1):
        lo, hi = sorted((y[i], y[i + 1]))
        if lo <= target <= hi and y[i + 1] != y[i]:
            xi = x[i] + (target - y[i]) * (x[i + 1] - x[i]) / (y[i + 1] - y[i])
            return float(1.0 / np.sqrt(xi)) if xi > 0 else float("inf")
    return None


def main() -> int:
    t0 = time.time()
    rng = np.random.default_rng(20261104)
    out = {"block": BLOCK, "cue_gaps_per_N": CUE_GAPS, "names": ["pV", "var", "rho1"]}

    g = np.load(HERE / "data" / "zeros_T100000.npz")["gammas"]
    zs = np.diff(riemann_siegel_theta(g) / np.pi)
    out["zeta_T1e5"] = block_summary(zs)
    out["zeta_T1e5_raw_gaps"] = block_summary(np.diff(g))
    print("zeta done", round(time.time() - t0, 1), "s", flush=True)

    big = HERE / "data" / "zeros_T1000000.npz"
    if big.exists():
        g6 = np.load(big)["gammas"]
        s6 = np.diff(riemann_siegel_theta(g6) / np.pi)
        edges = [0, 1e4, 3e4, 1e5, 2e5, 4e5, 7e5, 1e6]
        wins = []
        for lo, hi in zip(edges[:-1], edges[1:]):
            m = (g6[:-1] >= lo) & (g6[:-1] < hi)
            if m.sum() < 4 * BLOCK:
                continue
            w = block_summary(s6[m])
            w["t_lo"], w["t_hi"] = lo, hi
            w["t_mean"] = float(g6[:-1][m].mean())
            wins.append(w)
        out["zeta_T1e6_windows"] = wins
    else:
        out["zeta_T1e6_windows"] = "MISSING: lab/data/zeros_T1000000.npz not present; windows skipped"
    print("windows:", "done" if big.exists() else "SKIPPED (no T=1e6 file)", flush=True)

    gue = np.concatenate([gue_tridiag_gaps(4002, rng) for _ in range(600)])
    out["gue_tridiag"] = block_summary(gue)
    print("GUE done", round(time.time() - t0, 1), "s", flush=True)

    out["cue"] = []
    for n in CUE_NS:
        out["cue"].append(cue_summary(n, rng))
        print("CUE", n, "done", round(time.time() - t0, 1), "s", flush=True)

    ns = [c["N"] for c in out["cue"]] + [10 ** 6]
    curves = [[c["value"][j] for c in out["cue"]] + [out["gue_tridiag"]["value"][j]] for j in range(3)]

    def neff(entry):
        return {name: invert(ns, curves[j], entry["value"][j]) for j, name in enumerate(out["names"])}

    out["neff_zeta_T1e5"] = neff(out["zeta_T1e5"])
    if isinstance(out["zeta_T1e6_windows"], list):
        for w in out["zeta_T1e6_windows"]:
            w["neff"] = neff(w)
    out["seconds"] = round(time.time() - t0, 1)
    res = HERE / "results"
    res.mkdir(exist_ok=True)
    (res / "exp_c.json").write_text(json.dumps(out, indent=1))

    def row(name, e):
        v, s = e["value"], e["se"]
        return (f"{name:26s} pV {v[0]:.5f}+-{s[0]:.5f}  var {v[1]:.5f}+-{s[1]:.5f}  "
                f"rho1 {v[2]:+.5f}+-{s[2]:.5f}")
    print(row("zeta T<=1e5 (unfolded)", out["zeta_T1e5"]))
    print(row("zeta T<=1e5 (raw gaps)", out["zeta_T1e5_raw_gaps"]))
    print(row("GUE tridiag", out["gue_tridiag"]))
    for c in out["cue"]:
        print(row(f"CUE N={c['N']}", c))
    print("N_eff zeta T<=1e5:", out["neff_zeta_T1e5"])
    if isinstance(out["zeta_T1e6_windows"], list):
        for w in out["zeta_T1e6_windows"]:
            print(row(f"zeta [{w['t_lo']:.0e},{w['t_hi']:.0e})", w), " N_eff", w["neff"])
    print(out["seconds"], "s")
    return 0


if __name__ == "__main__":
    sys.exit(main())
