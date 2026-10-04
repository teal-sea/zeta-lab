"""K3: orthogonality of the out-of-band term, float64, measured.

For even real f supported in [-L, L], g = f * f~ is supported in [-2L, 2L] and
(1/pi) int_0^inf |F(t)|^2 cos(lambda t) dt = g(lambda) = int f(x) f(x - lambda) dx.
So every H frequency (all >= 2L) must give 0, and a planted in-band frequency
must give the nonzero time-domain value g(lambda). f = (1 - x^2/L^2)^2 * (random
even polynomial), so |F|^2 = O(t^-6) and the t-integral truncates cleanly.

Checks, per L and per random f:
  (a) max over all H frequencies of |freq-side|; (b) full H: (1/pi) int |F|^2 H;
  (c) planted in-band lambda = m_p log p per prime: freq side vs g(lambda);
  (d) a lesion: move one H frequency to just below 2L and watch (b) break.
"""
import json
import math
from fractions import Fraction
from pathlib import Path

import numpy as np

HERE = Path(__file__).resolve().parent
rng = np.random.default_rng(20260927)


def make_f(L, deg=6):
    c = rng.normal(size=deg + 1)
    return lambda x: (1 - (x / L) ** 2) ** 2 * np.polyval(c, (x / L) ** 2)


_GL400 = np.polynomial.legendre.leggauss(400)   # exact for the degree-36 integrand


def g_time(f, L, lam):
    """int f(x) f(x - lam) dx over the overlap, Gauss-Legendre."""
    a, b = max(-L, lam - L), min(L, lam + L)
    if b <= a:
        return 0.0
    x, w = _GL400
    xs = (a + b) / 2 + (b - a) / 2 * x
    return float(np.sum(w * (b - a) / 2 * f(xs) * f(xs - lam)))


def F2_grid(f, L, T=400.0, panels=1600, q=24, nx=400):
    xg, wg = np.polynomial.legendre.leggauss(nx)
    xs, ws = L * xg, L * wg
    fx = f(xs) * ws
    tq, wq = np.polynomial.legendre.leggauss(q)
    edges = np.linspace(0, T, panels + 1)
    t = ((edges[:-1, None] + edges[1:, None]) / 2 + (edges[1:, None] - edges[:-1, None]) / 2 * tq[None, :]).ravel()
    wt = ((edges[1:, None] - edges[:-1, None]) / 2 * wq[None, :]).ravel()
    F = np.concatenate([np.cos(np.outer(t[i:i + 2000], xs)) @ fx for i in range(0, len(t), 2000)])
    return t, wt, F ** 2


def freq_side(t, wt, F2, lam):
    return float(np.sum(wt * F2 * np.cos(lam * t)) / math.pi)


def main():
    env = json.loads((HERE / "envelope.json").read_text())
    out = {}
    for Ls, kind, D in (("4/5", "sine", 32), ("119/100", "sine", 32)):
        L = float(Fraction(Ls))
        run = next(r for r in env["runs"] if r["L"] == Ls and r["kernel"] == kind and r["D"] == D)
        terms = [(pr["p"], pr["m"], [(int(k), float(Fraction(v))) for k, v in pr["b"].items()]) for pr in run["primes"]]
        freqs = sorted({k * math.log(p) for p, _, bs in terms for k, _ in bs})
        rows = []
        for trial in range(3):
            f = make_f(L)
            t, wt, F2 = F2_grid(f, L)
            norm = freq_side(t, wt, F2, 0.0)          # = g(0) = ||f||^2
            g0 = g_time(f, L, 0.0)
            a = max(abs(freq_side(t, wt, F2, lam)) for lam in freqs)
            Hfull = sum(b * freq_side(t, wt, F2, k * math.log(p)) for p, _, bs in terms for k, b in bs)
            inband = [(p, m * math.log(p), freq_side(t, wt, F2, m * math.log(p)), g_time(f, L, m * math.log(p)))
                      for p, m, _ in terms]
            # lesion: first H term of p = 2 moved in band, to 0.95 * 2L
            p2, _, bs2 = terms[0]
            k0, b0 = bs2[0]
            lesion = Hfull - b0 * freq_side(t, wt, F2, k0 * math.log(p2)) + b0 * freq_side(t, wt, F2, 0.95 * 2 * L)
            rows.append({
                "norm_freq": norm, "norm_time": g0,
                "max_abs_Hfreq_rel": a / g0, "H_full_rel": Hfull / g0,
                "inband": [{"p": p, "lam": lam, "freq": fs, "time": gt} for p, lam, fs, gt in inband],
                "lesion_rel": lesion / g0, "lesion_expected_rel": b0 * g_time(f, L, 0.95 * 2 * L) / g0,
            })
            print(f"L={L} trial {trial}: ||f||^2 freq/time = {norm:.12f}/{g0:.12f}; max|H freq| rel = {a / g0:.1e};"
                  f" full H rel = {Hfull / g0:.1e}; lesion rel = {lesion / g0:.3e} (expect {b0 * g_time(f, L, 1.9 * L) / g0:.3e})")
            for p, lam, fs, gt in inband:
                print(f"     in-band p={p} lam={lam:.4f} (2L={2 * L}): freq {fs:+.10f}  time {gt:+.10f}")
        out[Ls] = {"n_freqs": len(freqs), "min_freq_minus_2L": min(freqs) - 2 * L, "trials": rows}
    (HERE / "k3.json").write_text(json.dumps(out, indent=1))


if __name__ == "__main__":
    main()
