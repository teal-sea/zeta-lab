"""T3 (kernel half) and T5 answered from the source paper; T3's residue restated.

WHAT WAS READ.  The source paper (2026-08-10; SHA-256 pinned in
PROOF-LEDGER.md), section 7.1 and the Theorem D proof, pages 20-21, and
the (Z)(P)(L) skeleton on pages 4-5.  Four sentences carry everything:

1. "Writing phi^2(u) = v(u/L) with v on [-1/2, 1/2], the constant is the
   scale-free functional (7.3)" - the variational profile v is the profile
   of **phi squared**, not of phi.
2. The maximiser solves v'' + 2 rho^2 v = 0: "v*(s) = cos(sqrt2 s) > 0
   (|s| <= 1/2)", with 1/c*_1 = 1/2 + 2^{-1/2} cot(2^{-1/2}) - the
   Montgomery-Taylor constant - and "(7.3) is Montgomery's functional
   K(0)/(Khat(0) + int |Khat(alpha)| d alpha) for K = |vhat|^2".
3. Theorem D's proof: "Take rho = 1 and the window
   phi(u) := cos(sqrt2 u / l)^{1/2} 1(L/2 - |u|) (the optimal profile,
   mollified at the ends by the fixed-width ramp of section 2.2)"; on the
   support cos(sqrt2 u/l) >= cos(1/sqrt2) > 0 so the square root is
   admissible; "its constants (7.1) differ from those of v*_1 by O(1/L)"
   and c_1 = c*_1 + O(1/l).
4. (P): tr G-tilde and ||G-tilde||_F^2 = tr G-tilde^2 are evaluated
   unconditionally; (L): "(2 tr P - r) + (4 tr Q - 4b) plays the role that
   sum (2m-1) plays in Montgomery's argument".

T5 - ANSWERED.  The upstream window is pinned: rho = 1, box of width L,
phi^2 carrying the cos(sqrt2 .) profile, ends mollified by the fixed-width
ramp.  The external Lean-repo double-check is downgraded to optional.
Two named burdens replace it:

  (a) THE WINDOW MISMATCH.  The T1 chain re-run (mt_chain / band_dual /
      mt_joint, theta* = 0.995) took phi itself = cos(sqrt2 t) on the box,
      i.e. v-profile cos^2.  That window is admissible in the paper's
      class but strictly weaker: the functional below gives it
      H = 0.667324, not 0.672501 - a 5.2e-3 gap, three orders larger than
      the 8e-6 floor gain under negotiation.  Every T1 damage field was
      built from Phi2 = FT(cos^2 box); the paper's chain has
      Phi2 = FT(cos box) = the v*-transform.  The chain re-run at the
      correct field is a new named step (same machinery, one kernel swap).
  (b) THE RAMP.  theta* was measured at the pure box; the paper's window
      is ramp-mollified with O(log l / l) constant corrections.  Either
      re-run with the ramp or carry the O(log l / l) as a named term.

T3, KERNEL HALF - ANSWERED.  tr G-tilde^2 is the pair sum weighted by
B(gamma, gamma')^2, and LAW D makes B proportional to Phi2 = FT(phi^2).
For the paper's window FT(phi^2) is the transform of the cos(sqrt2 .)
box - measured by transplant_lemma.mt_kernel_identity to be exactly the
Montgomery-Taylor kernel's square root (defect 2.5e-16).  So for the
paper's window the incidence weight omega^2 IS the MT kernel g: the mass
kernel and the Cheer-Goldston floor kernel coincide by construction, and
(7.3) says so in words (K = |vhat|^2).  The omega^2-vs-g ambiguity that
kernel_pairing.py surfaced - and the conservative reading it forced - was
an artifact of burden (a), not a feature of the paper's chain: it exists
only because the T1 window put the cos profile on phi instead of phi^2.
Under the paper's window the correctly-paired floor is the g-floor.

T3, MULTIPLICATIVE HALF - RESTATED, STILL OPEN.  The retained-mass
fraction theta multiplying the floor is still underived.  The paper's (L)
consumes ||P + Q||_F^2 whole; a CG-style improvement adds back a floor on
the discarded on-line off-diagonal mass sum_{i != j} m_i m_j g(x_i - x_j).
The chain's theta* bounds the adversarial erosion of that mass by off-line
pairs.  What is not yet derived is that the eroded mass enters (L) as
theta * floor in the paper's units, with the o(1) bookkeeping surviving.
That derivation - not any computation here - is what still separates the
candidate from a reading.

Everything numerical in this module is a pin on the sentences above:
the functional (7.3) is implemented once and must reproduce (i) the
Montgomery-Taylor constant at v*, (ii) Montgomery's 2/3 at v = 1, and
(iii) the strictly weaker constant at the T1 window's profile cos^2.

Run ``.venv/bin/python hunts/frontier_math/paper_pin.py`` (~1 min).
"""

from __future__ import annotations

import math
import sys
from pathlib import Path

import numpy as np

sys.path.insert(0, str(Path(__file__).resolve().parent))
from cg_transplant import MT_CONST, g_kernel  # noqa: E402
from transplant_lemma import phihat_mt  # noqa: E402

S2 = math.sqrt(2.0)


def c_star(v, n: int = 4001) -> float:
    """The paper's scale-free functional (7.3) at rho = 1.

    1/c(v) = (int v^2 + int int |s - s'| v(s) v(s') ds ds') / (int v)^2,
    Montgomery's K(0) / (Khat(0) + int |Khat|) with K = |vhat|^2 and
    Khat = v * v (autocorrelation; v >= 0 makes the modulus free).
    """
    s = np.linspace(-0.5, 0.5, n)
    vs = np.asarray(v(s), float)
    if vs.min() < 0:
        raise ValueError("(7.3) as implemented needs v >= 0")
    i1 = np.trapezoid(vs, s)
    i2 = np.trapezoid(vs * vs, s)
    cross = np.trapezoid(
        vs * np.trapezoid(np.abs(s[:, None] - s[None, :]) * vs[None, :],
                          s, axis=1), s)
    return float(i1 ** 2 / (i2 + cross))


def h_of(v, n: int = 4001) -> float:
    """H = 2 - 1/c*(v), the count constant the window earns."""
    return 2.0 - 1.0 / c_star(v, n)


V_STAR = lambda s: np.cos(S2 * s)            # noqa: E731  the paper's optimum
V_FLAT = lambda s: np.ones_like(s)           # noqa: E731  Montgomery's window
V_T1 = lambda s: np.cos(S2 * s) ** 2         # noqa: E731  the T1 chain's profile


def window_class_card(n: int = 4001) -> dict:
    """H for the three profiles, against their reference values."""
    return {
        "H_star": h_of(V_STAR, n), "H_star_ref": 2.0 - MT_CONST,
        "H_flat": h_of(V_FLAT, n), "H_flat_ref": 2.0 / 3.0,
        "H_t1": h_of(V_T1, n),
        "t1_gap": (2.0 - MT_CONST) - h_of(V_T1, n),
    }


def paper_window_mass_kernel_is_g(us=(0.2, 0.5, 0.9, 1.3, 2.5)) -> float:
    """For the paper's window, omega^2 = (FT phi^2 / A)^2 IS the MT kernel.

    FT(phi^2) for phi^2 = cos(sqrt2 .) box is phihat_mt (the v*-transform);
    worst relative defect of its normalised square against g over the
    bucket region.  This is the identity that dissolves kernel_pairing's
    ambiguity - it holds for the paper's window and fails for the T1 one.
    """
    v0 = phihat_mt(0j).real
    worst = 0.0
    for u in us:
        rhs = float(g_kernel(np.array([u]))[0])
        lhs = (phihat_mt(complex(2 * math.pi * u, 0)).real / v0) ** 2
        worst = max(worst, abs(lhs - rhs) / max(abs(rhs), 1e-30))
    return worst


def t1_window_mass_kernel_is_not_g(us=(0.5, 0.9, 1.5)) -> float:
    """The same identity at the T1 window: smallest relative gap.

    omega^2 there is built from FT(cos^2 box) = phi2_mt; kernel_pairing
    measured ratios 1.02-1.70.  A large gap here is the point: the
    ambiguity was real for the T1 window and is absent for the paper's.
    """
    from transplant_lemma import phi2_mt
    a = phi2_mt(0j).real
    smallest = math.inf
    for u in us:
        g = float(g_kernel(np.array([u]))[0])
        o = (phi2_mt(complex(2 * math.pi * u, 0)).real / a) ** 2
        smallest = min(smallest, abs(o - g) / max(abs(g), 1e-30))
    return smallest


def convergence_ladder(ns=(1001, 2001, 4001)) -> dict:
    """H(v*) on a trapezoid ladder: drift must shrink toward the pin."""
    return {n: h_of(V_STAR, n) for n in ns}


def audit() -> None:
    card = window_class_card()
    print("= the functional (7.3), three profiles =")
    print(f"  v* = cos(sqrt2 s):   H = {card['H_star']:.10f}   "
          f"(2 - MT constant = {card['H_star_ref']:.10f})")
    print(f"  v  = 1 (flat):       H = {card['H_flat']:.10f}   "
          f"(Montgomery 2/3 = {card['H_flat_ref']:.10f})")
    print(f"  v  = cos^2 (T1):     H = {card['H_t1']:.10f}   "
          f"-> the T1 window is {card['t1_gap']:.3e} BELOW the optimum")
    print("= ladder =")
    for n, h in convergence_ladder().items():
        print(f"  n={n}: H(v*) = {h:.10f}  (defect {abs(h - (2 - MT_CONST)):.2e})")
    print("= the mass kernel under each window =")
    d_paper = paper_window_mass_kernel_is_g()
    d_t1 = t1_window_mass_kernel_is_not_g()
    print(f"  paper window: worst |omega^2 - g|/g = {d_paper:.2e}  (identical)")
    print(f"  T1 window:  smallest |omega^2 - g|/g = {d_t1:.2e}  (different)")
    print("= consequences =")
    print("  T5 answered: window pinned (rho=1, phi^2 = cos(sqrt2 .) box, ramped).")
    print("  T3 kernel half answered: for the paper's window the retained mass")
    print("  is measured in the MT kernel itself; the g-floor is the paired one.")
    print("  Named burdens: (a) T1 chain re-run at Phi2 = FT(cos box);")
    print("  (b) ramp mollification O(log l / l); (c) the multiplicative-theta")
    print("  derivation into (L). No proportion is claimed.")


if __name__ == "__main__":
    audit()
