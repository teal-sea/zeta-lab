"""T3 sharpened: WHICH kernel the retained mass is measured in.

THE PROBLEM, found by asking what two symbols actually denote.  The
composed reading multiplies a retention fraction by an ordered-gap floor:

    candidate = H_pinned + 2 * theta_full * c_u.

But the two factors were computed with DIFFERENT kernels, and nothing in
the chain had said so:

- **theta_full** retains the on-line internal mass of the paper's
  Frobenius/incidence framework,
      R = sum_{i != j} omega^2(x_i - x_j),   omega = Phi2/Phi2(0),
  where Phi2 = FT(phi^2), the grid bilinear form B(z, w) is
  proportional to Phi2(z - w) (LAW D), so the mass the retention protects
  is measured in **omega^2**;
- **c_u** is the Cheer-Goldston bucket floor, computed with the
  Montgomery-Taylor kernel g, which `transplant_lemma.py` measures to be
  exactly the normalised squared transform of the window itself,
  g = (phihat / phihat(0))^2, i.e. **(FT phi)^2, not (FT phi^2)^2**.

These are not the same function.  FT(phi^2) = phihat * phihat, so omega
is a self-convolution where g is a square; the two agree at 0 by
normalisation and diverge immediately after.  Measured ratio omega^2/g
across the bucket region: 1.02 at u = 0.3, 1.12 at 0.6, 1.70 at 0.9,
0.66 at 1.5.  Their zeros are close but distinct, omega's first zero at
u = 1.1208 against lambda_1 = 1.0573, a 6% difference, and both zero
sets are NON-arithmetic, so both kernels support a live floor (unlike the
hunt window, whose omega is arithmetic to 1e-4 and whose floor is 0).

THE CONSEQUENCE.  The floor that belongs with theta_full is the one
computed in omega^2, not in g.  This module computes both on the same
resolution ladder and reports the conservative reading.  It does not
settle which pairing the upstream chain actually requires, that is the
residual T3, now stated sharply enough to be answerable from the paper:
the base constant H and the coefficient 2 come from the upstream count,
and whether that count's discarded mass is an omega^2 sum or a g sum is a
question about the paper's Theorem D derivation, not about anything
measurable here.

RESOLVED (see ``paper_pin.py``): the paper's Theorem D window carries the
cos(sqrt2 .) profile on **phi squared**, for which FT(phi^2) is the
v*-transform and omega^2 IS the MT kernel g - the two pairings coincide by
construction.  The ambiguity this module measures is real, but it belongs
to the T1 window (phi = cos box), which the functional (7.3) shows is a
strictly weaker member of the paper's class (H = 0.667324).  This module
stays as the record of the discrepancy and of the conservative reading
that was in force while the pairing was unknown.

Run ``.venv/bin/python hunts/frontier_math/kernel_pairing.py`` (~4 min).
"""

from __future__ import annotations

import math
import sys
from pathlib import Path

import numpy as np
from scipy.optimize import brentq

sys.path.insert(0, str(Path(__file__).resolve().parent))
from cg_transplant import (  # noqa: E402
    _GTable, bucket_floor, lambda_roots, lesion_wrong_lambda2, optimize_edges,
)
from reconnect import H_PINNED, HardenedGTable  # noqa: E402
from transplant_lemma import phi2_mt  # noqa: E402

TWO_PI = 2 * math.pi
A_MT = phi2_mt(0).real


def omega(u: float) -> float:
    """The incidence kernel at gap u (in mean gaps): Phi2(2 pi u)/Phi2(0)."""
    return phi2_mt(complex(TWO_PI * u, 0)).real / A_MT


def omega_sq_array(us):
    us = np.atleast_1d(np.asarray(us, float))
    return np.array([omega(float(u)) ** 2 for u in us])


def omega_zeros(kmax: int = 7):
    f = lambda u: omega(u)
    roots, u, prev = [], 0.2, omega(0.2)
    while u < 7 and len(roots) < kmax:
        u += 0.0005
        cur = f(u)
        if prev * cur < 0:
            roots.append(brentq(f, u - 0.0005, u))
        prev = cur
    return roots


class OmegaTable(_GTable):
    """One-sided minimum table for the incidence kernel omega^2."""

    def __init__(self, n: int = 600001, hi: float = 6.0):
        self.x = np.linspace(0.0, hi, n)
        self.v = omega_sq_array(self.x)
        self.roots = omega_zeros()
        self.gprime_max = 1.5 * float(
            np.abs(np.diff(self.v) / np.diff(self.x)).max())
        self.step = float(self.x[1] - self.x[0])

    def minimum(self, lo: float, hi: float) -> float:
        if any(lo <= r <= hi for r in self.roots):
            return 0.0
        i, j = np.searchsorted(self.x, [lo, hi])
        grid_min = float(self.v[max(i - 1, 0): j + 1].min())
        return max(0.0, grid_min - self.gprime_max * self.step)


def kernel_comparison(us=(0.0, 0.3, 0.6, 0.9, 1.5, 3.0)):
    """omega^2 against g at the same gap, plus both zero sets."""
    from cg_transplant import g_kernel
    rows = []
    for u in us:
        g = float(g_kernel(np.array([u]))[0])
        o = omega(u) ** 2
        rows.append({"u": u, "omega_sq": o, "g": g,
                     "ratio": o / g if g > 1e-14 else math.inf})
    return rows, omega_zeros(6), lambda_roots(6)


def floors_on_a_ladder(ns=(600001, 1200001, 2400001)):
    """Both floors at the unconditional density, on one resolution ladder.

    The g-kernel floor is known to need n >= 600001 to be stable (it reads
    3.0e-6 at n = 150001 and 5.02e-6 from 600001 on), so the ladder is
    reported rather than a single value for either kernel.
    """
    out = {"g": {}, "omega": {}}
    edges = {}
    for n in ns:
        tg = HardenedGTable(n=n)
        to = OmegaTable(n=n)
        if "g" not in edges:
            edges["g"] = optimize_edges(H_PINNED, table=tg)[1]
            edges["omega"] = optimize_edges(H_PINNED, table=to)[1]
        out["g"][n] = bucket_floor(H_PINNED, *edges["g"], table=tg)
        out["omega"][n] = bucket_floor(H_PINNED, *edges["omega"], table=to)
    return out, edges


def readings(theta_full: float = 0.995):
    """The candidate under each pairing; the conservative one is reported."""
    out, edges = floors_on_a_ladder()
    cg = out["g"][max(out["g"])]
    co = out["omega"][max(out["omega"])]
    return {
        "c_u_g": cg, "c_u_omega": co, "ratio": co / cg if cg else math.inf,
        "reading_g": H_PINNED + 2 * theta_full * cg,
        "reading_omega": H_PINNED + 2 * theta_full * co,
        "conservative": H_PINNED + 2 * theta_full * min(cg, co),
        "edges": edges, "ladder": out,
    }


def audit():
    print("= the two kernels are different functions =")
    rows, oz, lz = kernel_comparison()
    print("   u      omega^2        g          ratio")
    for r in rows:
        print(f"  {r['u']:4.1f}   {r['omega_sq']:.6f}   {r['g']:.6f}   "
              f"{r['ratio']:.4f}")
    print(f"  omega zeros (mean gaps): {['%.5f' % z for z in oz]}")
    print(f"  g zeros (lambda_k):      {['%.5f' % z for z in lz]}")
    print(f"  first-zero mismatch: {oz[0]:.5f} vs {lz[0]:.5f} "
          f"({100 * (oz[0] / lz[0] - 1):+.1f}%)")
    print("  both zero sets are NON-arithmetic, so both support a live")
    print("  floor (the hunt window's omega is arithmetic and its floor 0)")
    print("= both floors on one resolution ladder =")
    rec = readings()
    for kern in ("g", "omega"):
        vals = rec["ladder"][kern]
        print(f"  {kern:6s}: " + "  ".join(f"n={n}: {v:.6e}"
                                           for n, v in vals.items()))
    print(f"  c_u(g) = {rec['c_u_g']:.6e}   c_u(omega) = "
          f"{rec['c_u_omega']:.6e}   ratio {rec['ratio']:.4f}")
    print("= lesion control on the own-kernel floor =")
    le = lesion_wrong_lambda2(H_PINNED, rec["edges"]["omega"])
    print(f"  lambda_2 -> 2 lambda_1: floor = {le:.3e}  "
          f"({'dies' if le < 1e-9 else 'SURVIVES: BUG'})")
    print("= the reading under each pairing (theta_full = 0.995) =")
    print(f"  with g      (CG's kernel):        {rec['reading_g']:.10f}")
    print(f"  with omega^2 (the mass's kernel): {rec['reading_omega']:.10f}")
    print(f"  CONSERVATIVE reading:             {rec['conservative']:.10f}")
    print("  Which pairing the upstream count requires is the residual T3;")
    print("  it is a question about the paper's Theorem D derivation, not")
    print("  about anything measurable here. No proportion is claimed.")


if __name__ == "__main__":
    audit()
