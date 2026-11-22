"""Reproduction script for issue 335, the gate regime test on conjugate pairs.

Run from the repo root:

    .venv/bin/python hunts/local_positivity/reproduce_335.py

Every number printed here is computed in this run. Ground truth is read off
two independent routes: the least PSD Toeplitz diagonal on a finite section
(the module's own definition of c_p) and, inside the bound, the closed form
in localpos.satake_kernel. The 2026-08-10 gate is re-simulated from its own
rule (witness when c > d + 10 * old_tail, no regime test) so the claim that
it passed all 60 angles is measured here rather than remembered.
"""

from __future__ import annotations

import cmath
import math
import sys
from pathlib import Path

import numpy as np

sys.path.insert(0, str(Path(__file__).resolve().parents[2]))

from hunts.local_positivity import localpos
from hunts.local_positivity.localpos import (
    DEFAULT_PRIMES,
    gate,
    local_lambdas,
    satake_kernel,
    satake_local,
    threshold,
)


def least_psd_diagonal(s: np.ndarray, n: int) -> float:
    idx = np.abs(np.subtract.outer(np.arange(n), np.arange(n)))
    t = np.where(idx == 0, 0.0, s[idx])
    return float(-np.linalg.eigvalsh(t).min())


def weights(aloc, p: int, top: int) -> np.ndarray:
    return local_lambdas(aloc, p, top) * float(p) ** (-np.arange(top + 1) / 2.0)


def conjugate_pair(radius: float, p: int, phi: float):
    alpha = radius * math.sqrt(p) * cmath.exp(1j * phi)
    return satake_local([alpha, alpha.conjugate()]), [alpha, alpha.conjugate()]


def closed_form_cp(alphas, p: int, degree: int) -> float:
    theta = np.linspace(0.0, 2 * math.pi, 20001)
    k = satake_kernel(alphas, p, theta)
    return float(degree - k.min())


def true_ratio_old(aloc, p: int) -> tuple[float, int, int, float, float]:
    """The two weighted terms the regime test compares, at default tol."""
    m_depth = localpos._depth(p, localpos.DEFAULT_TOL)
    lam = local_lambdas(aloc, p, m_depth)
    w = np.abs(lam[1:] * p ** (-np.arange(1, m_depth + 1) / 2.0))
    nz = np.flatnonzero(w > 0)
    last, prev = int(nz[-1]), int(nz[max(0, nz.size - 1 - max(1, m_depth // 10))])
    ratio = float((w[last] / w[prev]) ** (1.0 / max(1, last - prev)))
    return ratio, last + 1, prev + 1, float(w[last]), float(w[prev])


def report_case(name: str, radius: float, p: int, phi: float, expect: str) -> None:
    aloc, alphas = conjugate_pair(radius, p, phi)
    c, tail, regime = threshold(aloc, p)
    out = gate(aloc, 2, primes=[p])
    ratio, m_last, m_prev, w_last, w_prev = true_ratio_old(aloc, p)
    psd120 = least_psd_diagonal(weights(aloc, p, 119), 120)
    line = (
        f"{name}: radius={radius} p={p} phi={phi} expected={expect} | "
        f"gate={out['verdict']} regime={regime} truncated_c={c:.6f} tail={tail:.6g} | "
        f"two_point_ratio={ratio:.6f} (m_prev={m_prev}, w={w_prev:.6g}; m_last={m_last}, w={w_last:.6g}) | "
        f"least_PSD_diag_N120={psd120:.6f}"
    )
    if radius < 1.0:
        line += f" closed_form_c={closed_form_cp(alphas, p, 2):.6f}"
    print(line)


def old_gate_verdict(aloc, degree: int, primes) -> str:
    """The 2026-08-10 rule, commit e3e4426b4: no regime test."""
    for p in primes:
        m_depth = localpos._depth(p, localpos.DEFAULT_TOL)
        lam = local_lambdas(aloc, p, m_depth)
        wts = lam[1:] * p ** (-np.arange(1, m_depth + 1) / 2.0)
        theta = np.linspace(0.0, np.pi, 4001)
        series = 2 * np.sum(
            wts[:, None] * np.cos(np.outer(np.arange(1, m_depth + 1), theta)), axis=0
        )
        c = float(-series.min())
        old_tail = 2 * float(np.max(np.abs(lam))) * p ** (-(m_depth + 1) / 2.0) / (1 - p ** -0.5)
        if c > degree + 10.0 * old_tail:
            return "FAIL"
    return "PASS"


def main() -> None:
    print("== issue 335 named cases ==")
    report_case("inside_bound", 0.9, 2, 0.2, "PASS, c_p<2")
    report_case("on_bound", 1.0, 2, 0.9, "INDETERMINATE on bound, c_p=d=2")
    report_case("outside_bound", 1.2, 7, 0.4, "FAIL, c_p=+inf")
    report_case("on_bound_phi2", 1.0, 2, 2.0, "INDETERMINATE on bound, c_p=d=2")

    print()
    print("== 60 angle unit-modulus degree-2 family, default 25 primes ==")
    fails = indet = passes = 0
    old_fails = 0
    margins = []
    fail_angles = []
    for phi in np.linspace(0.05, math.pi - 0.05, 60):
        alpha = cmath.exp(1j * float(phi))
        aloc = satake_local([alpha, alpha.conjugate()])
        res = gate(aloc, 2)
        margins.append(2 - res["max_c"])
        if res["verdict"] == "FAIL":
            fails += 1
            fail_angles.append((float(phi), res["divergent_places"][:5]))
        elif res["verdict"] == "INDETERMINATE":
            indet += 1
        else:
            passes += 1
        if old_gate_verdict(aloc, 2, DEFAULT_PRIMES) == "FAIL":
            old_fails += 1
    print(f"current_gate: PASS={passes} FAIL={fails} INDETERMINATE={indet} of 60")
    print(f"old_gate_2026_08_10_resimulated: FAIL={old_fails} of 60")
    print(f"margin 2-max_c: min={min(margins):.6f} max={max(margins):.6f}")
    for phi, places in fail_angles:
        print(f"  FAIL phi={phi:.6f} divergent_places(first5)={places}")


if __name__ == "__main__":
    main()
