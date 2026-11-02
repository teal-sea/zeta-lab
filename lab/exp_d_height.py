"""Experiment D: how the local-minimum excess of zeta gaps depends on height.

Run: OPENBLAS_NUM_THREADS=1 lab/.venv/bin/python lab/exp_d_height.py
Needs lab/data/zeros_T1000000.npz (lab/scan_zeros.py 1000000); exits non-zero without it.
Writes lab/results/exp_d.json and prints the table.

For height windows of the zeros up to 10^6 it measures pV (fraction of strict local minima of
the unfolded gaps), the gap variance, and the gap autocorrelations rho1..rho3, with errors
from blocks of BLOCK gaps. The GUE reference is a fresh tridiagonal sample.

Two questions:
1. Decay law. If the zeros are GUE asymptotically, pV - pV_GUE must go to 0. Fit the
   excess against x = 1/log^2(T/2pi) and against x = 1/log(T/2pi), each with and without an
   intercept, by weighted least squares, and report chi^2 for each.
2. Is the excess just the correlations? For a Gaussian sequence with lag correlations
   rho1, rho2, P(local min) = 1/4 + arcsin(r)/(2 pi), r = (1 - 2 rho1 + rho2) / (2 (1 - rho1)).
   That formula is exact only for Gaussian sequences; the gaps are not Gaussian, so it is a
   heuristic. Report it next to the measured pV for every window and for GUE.
"""
import json
import sys
import time
from pathlib import Path

import numpy as np

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
sys.path.insert(0, str(HERE.parent))
from exp_a_degree_law import gue_tridiag_gaps  # noqa: E402
from zeta.statistics import riemann_siegel_theta  # noqa: E402

BLOCK = 2000
EDGES = [0, 1e4, 3e4, 1e5, 2e5, 4e5, 7e5, 1e6]


def acf(s: np.ndarray, k: int) -> float:
    c = s - s.mean()
    return float(np.dot(c[:-k], c[k:]) / np.dot(c, c))


def stats_seq(s: np.ndarray) -> np.ndarray:
    pv = np.mean((s[:-2] > s[1:-1]) & (s[1:-1] < s[2:]))
    return np.array([pv, np.var(s), acf(s, 1), acf(s, 2), acf(s, 3)])


def gauss_pv(r1: float, r2: float) -> float:
    r = (1.0 - 2.0 * r1 + r2) / (2.0 * (1.0 - r1))
    return float(0.25 + np.arcsin(r) / (2.0 * np.pi))


def summarize(s: np.ndarray) -> dict:
    nb = s.size // BLOCK
    if nb < 4:
        raise RuntimeError(f"only {nb} blocks of {BLOCK}: too few for an error bar")
    rows = np.array([stats_seq(s[i * BLOCK:(i + 1) * BLOCK]) for i in range(nb)])
    v = stats_seq(s)
    return {"n_gaps": int(s.size), "blocks": int(nb),
            "value": v.tolist(), "se": (rows.std(axis=0, ddof=1) / np.sqrt(nb)).tolist(),
            "gauss_pV": gauss_pv(v[2], v[3])}


def wls(x, y, se, intercept):
    w = 1.0 / np.asarray(se) ** 2
    X = np.column_stack([x, np.ones_like(x)]) if intercept else np.asarray(x)[:, None]
    A = X.T @ (w[:, None] * X)
    beta = np.linalg.solve(A, X.T @ (w * y))
    cov = np.linalg.inv(A)
    chi2 = float(np.sum(w * (y - X @ beta) ** 2))
    return {"coef": beta.tolist(), "se": np.sqrt(np.diag(cov)).tolist(), "chi2": chi2,
            "dof": int(len(y) - X.shape[1])}


def main() -> int:
    t0 = time.time()
    path = HERE / "data" / "zeros_T1000000.npz"
    if not path.exists():
        print(f"MISSING {path}: run lab/scan_zeros.py 1000000 first", file=sys.stderr)
        return 2
    g = np.load(path)["gammas"]
    s = np.diff(riemann_siegel_theta(g) / np.pi)
    mid = g[:-1]
    out = {"block": BLOCK, "names": ["pV", "var", "rho1", "rho2", "rho3"], "zeros": int(g.size)}
    wins = []
    for lo, hi in zip(EDGES[:-1], EDGES[1:]):
        m = (mid >= lo) & (mid < hi)
        w = summarize(s[m])
        w.update({"t_lo": lo, "t_hi": hi, "t_mean": float(mid[m].mean()),
                  "log_T_over_2pi": float(np.log(mid[m].mean() / (2 * np.pi)))})
        wins.append(w)
    out["windows"] = wins
    print("windows done", round(time.time() - t0, 1), "s", flush=True)

    rng = np.random.default_rng(20261105)
    gue = np.concatenate([gue_tridiag_gaps(4002, rng) for _ in range(400)])
    out["gue"] = summarize(gue)
    print("GUE done", round(time.time() - t0, 1), "s", flush=True)

    p_g, se_g = out["gue"]["value"][0], out["gue"]["se"][0]
    L = np.array([w["log_T_over_2pi"] for w in wins])
    ex = np.array([w["value"][0] - p_g for w in wins])
    ex_se = np.array([np.hypot(w["se"][0], se_g) for w in wins])
    out["excess_pV"] = ex.tolist()
    out["excess_pV_se"] = ex_se.tolist()
    out["fits"] = {
        "1/log^2, no intercept": wls(1 / L ** 2, ex, ex_se, False),
        "1/log^2, intercept": wls(1 / L ** 2, ex, ex_se, True),
        "1/log, no intercept": wls(1 / L, ex, ex_se, False),
        "1/log, intercept": wls(1 / L, ex, ex_se, True),
    }
    out["seconds"] = round(time.time() - t0, 1)
    res = HERE / "results"
    res.mkdir(exist_ok=True)
    (res / "exp_d.json").write_text(json.dumps(out, indent=1))

    print(f"{'window':>16s} {'gaps':>8s} {'log(T/2pi)':>10s} {'pV':>17s} {'excess z':>8s} "
          f"{'gauss pV':>8s} {'var':>8s} {'rho1':>8s} {'rho2':>8s} {'rho3':>8s}")
    for w, e, es in zip(wins, ex, ex_se):
        v, se = w["value"], w["se"]
        print(f"[{w['t_lo']:.0e},{w['t_hi']:.0e}) {w['n_gaps']:8d} {w['log_T_over_2pi']:10.3f} "
              f"{v[0]:.5f}+-{se[0]:.5f} {e / es:8.1f} {w['gauss_pV']:8.5f} {v[1]:8.5f} "
              f"{v[2]:+8.4f} {v[3]:+8.4f} {v[4]:+8.4f}")
    v, se = out["gue"]["value"], out["gue"]["se"]
    print(f"{'GUE':>16s} {out['gue']['n_gaps']:8d} {'inf':>10s} {v[0]:.5f}+-{se[0]:.5f} "
          f"{'':8s} {out['gue']['gauss_pV']:8.5f} {v[1]:8.5f} {v[2]:+8.4f} {v[3]:+8.4f} {v[4]:+8.4f}")
    for name, f in out["fits"].items():
        print(f"fit excess ~ {name:24s} coef {np.round(f['coef'], 5)} +- {np.round(f['se'], 5)} "
              f"chi2 {f['chi2']:.1f} / {f['dof']} dof")
    print(out["seconds"], "s")
    return 0


if __name__ == "__main__":
    sys.exit(main())
