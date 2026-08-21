"""Independent cross-check of the m2(1,v), m3(1,v) closed forms: windowed CUE.

The continuum derivation in functional.py is checked here against a model
that shares none of its steps: the exact finite-N circular ensemble.  With
U ~ CUE(N), eigenangles theta_j, band frequencies m in [-M, M], N = 2M + 1,
the windowed Gram matrix over the eigenangle points is

    H = (1/N) sum_m v(m/N) u_m u_m^*,   (u_m)_j = e^{i m theta_j},

so that E tr H^k = N^{-k} sum over m-tuples in [-M, M]^k of
prod_i v(m_i / N) * E prod_j Tr U^{h_j}, with h_j = m_j - m_{j+1} (cyclic).
The joint trace moments E prod Tr U^{h_j} are EXACT integers from the lattice
count engine in ../sine_gram/exact_finite_N.py (read-only import; that arm
owns the file).  As N grows this converges to the sine-process moments at
band lambda = 1, i.e. to m_k(1, v) after normalizing by N l1^k with the
discrete l1 = (1/N) sum_m v(m/N); the discrete normalization makes m_1 = 1
exactly at every N.

Floats are fine here (v is transcendental for the cosine window); the exact
integers are converted once.  Convergence is O(1/N); a polynomial fit in 1/N
through N = 21..41 extrapolates to the limit, and the check is that the
extrapolant matches the closed forms of functional.py to ~1e-8.

Run: .venv/bin/python hunts/rogue_frontier/window_opt/crosscheck_finiteN.py
"""

from __future__ import annotations

import os
import sys

import numpy as np

_HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, _HERE)
sys.path.insert(0, os.path.join(_HERE, os.pardir, "sine_gram"))

from exact_finite_N import exact_tr_Gk, joint_trace_moment  # noqa: E402

import functional  # noqa: E402
from functional import OPT_Q, moments_polyeven_exact, moments_quad  # noqa: E402


def windowed_m2(v, N: int) -> float:
    """E tr H^2 / (N l1^2) in the windowed circular model, N odd."""
    assert N % 2 == 1
    M = (N - 1) // 2
    ms = np.arange(-M, M + 1)
    vv = np.array([v(m / N) for m in ms], dtype=float)
    l1 = vv.sum() / N
    J2 = {}
    tot = 0.0
    for i, m1 in enumerate(ms):
        for j, m2 in enumerate(ms):
            h = int(m1 - m2)
            val = J2.get(h)
            if val is None:
                val = float(joint_trace_moment((h, -h), N))
                J2[h] = val
            tot += vv[i] * vv[j] * val
    return tot / N ** 2 / (N * l1 ** 2)


def windowed_m3(v, N: int) -> float:
    """E tr H^3 / (N l1^3) in the windowed circular model, N odd."""
    assert N % 2 == 1
    M = (N - 1) // 2
    ms = np.arange(-M, M + 1)
    vv = np.array([v(m / N) for m in ms], dtype=float)
    l1 = vv.sum() / N
    J3 = {}
    tot = 0.0
    for i, m1 in enumerate(ms):
        for j, m2 in enumerate(ms):
            h1 = int(m1 - m2)
            acc = 0.0
            for k, m3 in enumerate(ms):
                h2 = int(m2 - m3)
                key = (h1, h2)
                val = J3.get(key)
                if val is None:
                    val = float(joint_trace_moment((h1, h2, -h1 - h2), N))
                    J3[key] = val
                acc += vv[k] * val
            tot += vv[i] * vv[j] * acc
    return tot / N ** 3 / (N * l1 ** 3)


def extrapolate(Ns, vals, deg: int) -> float:
    x = np.array([1.0 / N for N in Ns])
    return float(np.polyval(np.polyfit(x, np.array(vals), deg), 0.0))


def run(tol: float = 5e-8) -> None:
    # plumbing validation: v = 1 must reproduce the unwindowed engine exactly
    N = 21
    e2 = float(exact_tr_Gk(2, N, (N - 1) // 2))
    e3 = float(exact_tr_Gk(3, N, (N - 1) // 2))
    w2 = windowed_m2(lambda x: 1.0, N)
    w3 = windowed_m3(lambda x: 1.0, N)
    assert abs(w2 - e2) < 1e-12 and abs(w3 - e3) < 1e-12, (w2, e2, w3, e3)
    print(f"plumbing check v=1, N={N}: windowed engine == exact_tr_Gk "
          f"(m2 {w2:.12f}, m3 {w3:.12f})")

    Ns = [21, 25, 29, 33, 37, 41]
    windows = []
    rq = moments_quad(lambda s: np.cos(1.6 * s))
    windows.append(("cos(8s/5)", lambda x: float(np.cos(1.6 * x)),
                    rq["m2"], rq["m3"]))
    m2r, m3r, _ = moments_polyeven_exact(OPT_Q)
    q1, q2 = float(OPT_Q[0]), float(OPT_Q[1])
    windows.append((f"1 + ({OPT_Q[0]}) s^2 + ({OPT_Q[1]}) s^4",
                    lambda x: 1.0 + q1 * x ** 2 + q2 * x ** 4,
                    float(m2r), float(m3r)))

    for name, v, m2_target, m3_target in windows:
        print(f"\nwindow v(s) = {name}")
        m2s, m3s = [], []
        for N in Ns:
            a, b = windowed_m2(v, N), windowed_m3(v, N)
            m2s.append(a)
            m3s.append(b)
            print(f"  N={N:2d}  m2={a:.10f}  m3={b:.10f}  2m2-m3={2*a-b:.10f}")
        for lbl, vals, target in (("m2", m2s, m2_target),
                                  ("m3", m3s, m3_target)):
            e4 = extrapolate(Ns, vals, 4)
            e3_ = extrapolate(Ns, vals, 3)
            print(f"  {lbl}: extrapolated {e4:.10f} (deg 3: {e3_:.10f}), "
                  f"closed form {target:.10f}, diff {e4 - target:+.2e}")
            assert abs(e4 - target) < tol, (lbl, e4, target)
    print("\nPASS: exact finite-N windowed CUE agrees with the closed forms "
          f"(deg-4 extrapolation within {tol:g})")


if __name__ == "__main__":
    run()
