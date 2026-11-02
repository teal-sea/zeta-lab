"""Experiment B: does the zeta-zero gap sequence have an arrow of time?

Run: lab/.venv/bin/python lab/exp_b_arrow_of_time.py
Writes lab/results/exp_b.json and prints the table.

Directed HVG: out-degree counts the nodes a node sees to its right, in-degree to its left.
A time-reversible stationary sequence has the same out- and in-degree laws (Lacasa et al.,
Eur. Phys. J. B 85, 217, 2012). Both laws always have the same mean (each edge is one out
and one in), so the first moment says nothing; the signed statistic used here is

    d2 = mean(k_out^2) - mean(k_in^2)   per segment of SEG gaps, TRIM nodes dropped per end,

plus KL(out || in) on the pooled histograms. Significance comes from a sign-flip test:
reversing a segment swaps out and in, so under reversibility each segment's d2 is as
likely to be -d2. 20000 random sign patterns give the null for the mean of d2.

Controls, so the detector has to prove it can see an arrow:
* planted irreversible: x_{t+1} = 0.6 x_t + Exp(1) (a non-Gaussian linear process; such a
  process is irreversible, Weiss 1975);
* planted reversible: Gaussian AR(1), x_{t+1} = 0.6 x_t + N(0,1);
* zeta gaps shuffled (i.i.d.), and GUE tridiagonal gaps (GUE is reflection symmetric).
"""
import json
import sys
import time
from pathlib import Path

import numpy as np

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
sys.path.insert(0, str(HERE.parent))
import hvg  # noqa: E402
from exp_a_degree_law import gue_tridiag_gaps, zeta_gaps  # noqa: E402

SEG = 2000
TRIM = 25
KMAX = 13
FLIPS = 20000


def directed_stats(x: np.ndarray) -> dict:
    nseg = x.size // SEG
    if nseg < 2:
        raise RuntimeError(f"only {nseg} complete segment(s) of {SEG}: cannot test")
    d2 = np.empty(nseg)
    h_out = np.zeros(KMAX + 1)
    h_in = np.zeros(KMAX + 1)
    for i in range(nseg):
        _, out, inn = hvg.degrees(x[i * SEG:(i + 1) * SEG])
        out = hvg.interior(out, TRIM).astype(float)
        inn = hvg.interior(inn, TRIM).astype(float)
        d2[i] = np.mean(out ** 2) - np.mean(inn ** 2)
        h_out += hvg.degree_histogram(out.astype(int), KMAX)
        h_in += hvg.degree_histogram(inn.astype(int), KMAX)
    rng = np.random.default_rng(7)
    signs = rng.choice([-1.0, 1.0], size=(FLIPS, nseg))
    null = (signs * d2).mean(axis=1)
    obs = float(d2.mean())
    p = float((np.count_nonzero(np.abs(null) >= abs(obs)) + 1) / (FLIPS + 1))
    return {
        "gaps": int(x.size), "segments": int(nseg), "dropped_gaps": int(x.size - nseg * SEG),
        "d2_mean": obs, "d2_se": float(d2.std(ddof=1) / np.sqrt(nseg)),
        "z": float(obs / (d2.std(ddof=1) / np.sqrt(nseg))),
        "signflip_p": p,
        "kl_out_in": hvg.kl_divergence(h_out, h_in),
        "kl_support_mismatch_bins": hvg.kl_support_mismatch(h_out, h_in),
        "p_out": (h_out / h_out.sum()).tolist(), "p_in": (h_in / h_in.sum()).tolist(),
    }


def ar1(n: int, rng: np.random.Generator, noise: str) -> np.ndarray:
    e = rng.exponential(1.0, n) if noise == "exp" else rng.normal(0.0, 1.0, n)
    x = np.empty(n)
    x[0] = e[0]
    for t in range(1, n):
        x[t] = 0.6 * x[t - 1] + e[t]
    return x


def main() -> int:
    t0 = time.time()
    rng = np.random.default_rng(20261103)
    zg = zeta_gaps(100000)
    n = zg.size
    families = {
        "zeta_T1e5": zg,
        "zeta_shuffled": rng.permutation(zg),
        "gue_tridiag": np.concatenate([gue_tridiag_gaps(4002, rng) for _ in range(70)]),
        "planted_irreversible_ar1_exp": ar1(n, rng, "exp"),
        "planted_reversible_ar1_gauss": ar1(n, rng, "gauss"),
    }
    out = {name: directed_stats(x) for name, x in families.items()}
    out["seconds"] = round(time.time() - t0, 1)
    res = HERE / "results"
    res.mkdir(exist_ok=True)
    (res / "exp_b.json").write_text(json.dumps(out, indent=1))
    print(f"{'family':32s} {'gaps':>7s} {'segs':>5s} {'d2 mean':>11s} {'se':>9s} {'z':>6s} "
          f"{'signflip p':>10s} {'KL(out||in)':>12s}")
    for name in families:
        r = out[name]
        print(f"{name:32s} {r['gaps']:7d} {r['segments']:5d} {r['d2_mean']:11.5f} "
              f"{r['d2_se']:9.5f} {r['z']:6.1f} {r['signflip_p']:10.4f} {r['kl_out_in']:12.2e}")
    print(f"{out['seconds']} s")
    return 0


if __name__ == "__main__":
    sys.exit(main())
