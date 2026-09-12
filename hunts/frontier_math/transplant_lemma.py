"""The transplant lemma, dissected: which window carries which half.

THE QUESTION.  The candidate reading (reconnect.py) composes the retained
fraction theta_full with the Cheer-Goldston ordered-gap floor.  theta_full
was established (levels 1-7) at the hunt's window (L = 8, septic ramp);
the floor was computed with the Montgomery-Taylor kernel g.  The
"transplant lemma" is whatever connects the two.  This module measures
the three windows in play and finds that the lemma DECOMPOSES, there is
no kernel-comparison inequality to prove, but there is a chain re-run to
do, and the degeneracies that force it are exact and now measured.

THE THREE WINDOWS.

1. **The hunt window** (L = 8 septic ramp; levels 1-7, theta_full = 0.02).
   Its kernel omega(r) = Phi2(r)/Phi2(0) has zeros in ratios
   1 : 2.0001 : 3.0003 : ..., arithmetic to 1e-4 (:func:`hunt_zeros`).
   The CG mechanism needs lambda_2 != 2 lambda_1 (the floor's own lesion
   moves lambda_2 to 2 lambda_1 and must die); the smoothed-box sinc
   structure sits essentially ON the lesion.  The bucket LP with omega^2
   returns a floor consistent with zero (:func:`hunt_floor`).  The hunt
   window CANNOT power the ordered-gap mechanism.

2. **The Hann grid window** (phi = cos^2(pi u) on [-1/2, 1/2]; the shape
   of the pinned zero-side regression instrument `blockpos.py`).  Its
   grid form is EXACTLY alias-free: B(z, w) = 2 pi Phi2_h(z - w) to
   machine precision (:func:`hann_law_d`), the satellites are chosen so
   the +-2pi aliases cancel; LAW D transplants verbatim.  But its kernel
   zeros are 6pi, 8pi, 10pi, 12pi: 2 lambda_1 = lambda_4 EXACTLY, again
   CG-degenerate, exactly.  (Its damage field is also essentially
   harmless: min W = -1.7e-5 out to g = 40; retention is nearly free and
   nearly worthless there.)

3. **The MT window** (phi = cos(sqrt2 t) on the width-1 box): the
   Montgomery-Taylor kernel g is EXACTLY its normalised squared Fourier
   transform (:func:`mt_kernel_identity`), Taylor's sqrt2 modulation is
   what breaks the arithmetic degeneracy (lambda_2/lambda_1 = 1.9201),
   and it is the ONLY window of the three whose floor is alive.  The
   grid form at this window has a measured ~0.5% alias defect
   (:func:`mt_law_d`): the box autocorrelation reaches the +-2pi alias,
   so the LAW hierarchy transplants with an explicit alias term to be
   carried one-sidedly, a complication, not a wall.  The retention
   entry card (:func:`mt_entry_card`) is 3x FRIENDLIER than the hunt
   window: min W / sigma^2 = -0.43 (vs -(1+m0) = -1.21), with the
   negative band at g ~ 7 grid units = 1.11 mean gaps, exactly the
   lambda_1 geometry the CG buckets live on.

THE DECOMPOSITION (what "the transplant lemma" actually is):

  T1  Re-run the retention chain (laws D..N, the counting duals, the
      joint cap) at the MT window, carrying the alias term.  Compute,
      not analysis; the machinery is window-parametric and the entry
      constants above suggest theta_full^MT >= the hunt's 0.02.
  T2  The census/normalization claim: grid unit x 2pi = mean gap
      (measured consistent: the damage band at 1.06-1.11 mean gaps).
  T3  The CG plumbing (floor -> constant), calibrated against CG 1993.
  T4  Taper/truncation of the upstream count, restated one-sided.
  T5  The upstream pin: which window the pinned Lean zero-side actually
      carries (the in-repo regression instrument is Hann-shaped; the
      Theorem-D kernel is MT; the external `anthropics/zeta-23-lean`
      file is the arbiter and is outside this session's reach).

Nothing here computes a proportion; the candidate reading's status is
unchanged (candidate).  Run
``.venv/bin/python hunts/frontier_math/transplant_lemma.py`` (~2 min).
"""

from __future__ import annotations

import cmath
import math
import sys
from pathlib import Path

import numpy as np
from scipy.optimize import brentq

sys.path.insert(0, str(Path(__file__).resolve().parent))
from cg_transplant import CG_EDGES, CG_NU, bucket_floor, g_kernel, lambda_roots  # noqa: E402
from gap_consistency import _phi2_hat_f  # noqa: E402
from reconnect import HardenedGTable  # noqa: E402

S2 = math.sqrt(2.0)


# ---------------------------------------------------------------------------
# window transforms
# ---------------------------------------------------------------------------


def sc2(z: complex) -> complex:
    """2 sin(z/2)/z, complex-safe."""
    if abs(z) < 1e-12:
        return 1.0 + 0j
    return 2 * cmath.sin(z / 2) / z


def phi2_hunt(g: float) -> float:
    """The hunt window's Phi2 (L = 8 septic ramp), real offsets."""
    return _phi2_hat_f(complex(g, 0), 8.0, 1.0).real


def phi2_hann(z: complex) -> complex:
    """int cos^4(pi u) e^{izu} du over [-1/2, 1/2]."""
    tp = 2 * math.pi
    return (3 / 8 * sc2(z) + 1 / 4 * (sc2(z + tp) + sc2(z - tp))
            + 1 / 16 * (sc2(z + 2 * tp) + sc2(z - 2 * tp)))


def phi2_mt(z: complex) -> complex:
    """int cos^2(sqrt2 t) e^{izt} dt over [-1/2, 1/2]."""
    return 0.5 * sc2(z) + 0.25 * (sc2(z + 2 * S2) + sc2(z - 2 * S2))


A_MT = phi2_mt(0).real  # = 1/2 + sin(sqrt2)/(2 sqrt2)


def phihat_hann(z: complex) -> complex:
    """FT of cos^2(pi u) on [-1/2, 1/2] (the blockpos.py vector shape)."""
    def s(w):
        if abs(w) < 1e-12:
            return 0.5 + 0j
        return cmath.sin(w / 2) / w
    tp = 2 * math.pi
    return s(z) + 0.5 * (s(z + tp) + s(z - tp))


def phihat_mt(z: complex) -> complex:
    """FT of cos(sqrt2 t) on [-1/2, 1/2]."""
    def s(w):
        if abs(w) < 1e-12:
            return 0.5 + 0j
        return cmath.sin(w / 2) / w
    return s(z + S2) + s(z - S2)


# ---------------------------------------------------------------------------
# finding 1: the hunt window is CG-degenerate
# ---------------------------------------------------------------------------


def hunt_zeros(kmax: int = 6):
    roots = []
    x, prev = 0.1, phi2_hunt(0.1)
    while x < 6 and len(roots) < kmax:
        x += 0.01
        cur = phi2_hunt(x)
        if prev * cur < 0:
            roots.append(brentq(phi2_hunt, x - 0.01, x))
        prev = cur
    return roots


class _OmegaTable(HardenedGTable):
    """The hardened minimum table for the hunt kernel omega^2."""

    def __init__(self, n: int = 600001, hi: float = 6.0):
        a = phi2_hunt(0.0)
        self.x = np.linspace(0.0, hi, n)
        self.v = np.array([(phi2_hunt(float(g)) / a) ** 2 for g in self.x])
        self.roots = hunt_zeros()
        xf = self.x
        self.gprime_max = 1.5 * float(
            np.abs(np.diff(self.v) / np.diff(xf)).max())
        self.step = float(self.x[1] - self.x[0])


def hunt_floor():
    """The CG bucket LP with the hunt kernel: consistent with zero.

    The edges are scaled from CG's by lambda_1^hunt/lambda_1^MT so the
    buckets sit in the same relative geometry.
    """
    a = phi2_hunt(0.0)
    roots = hunt_zeros()
    scale = roots[0] / lambda_roots(1)[0]
    edges = tuple(e * scale for e in CG_EDGES)
    table = _OmegaTable(n=150001)
    om2 = lambda u: (np.array([phi2_hunt(float(x)) for x in
                               np.atleast_1d(u)]) / a) ** 2
    return bucket_floor(CG_NU, *edges, table=table, g=om2), roots


# ---------------------------------------------------------------------------
# finding 2: the Hann grid window, LAW D exact, CG-degenerate exactly
# ---------------------------------------------------------------------------


def hann_law_d(samples=((0.3, 0.0), (0.37, 0.2), (1.9, 0.45))):
    """B(z, 0) = 2 pi Phi2_h(z): measured ratio defect."""
    tau = np.arange(-80, 81, 1.0)
    worst = 0.0
    for x, y in samples:
        z = complex(x, y)
        lhs = sum(phihat_hann(z - t) * phihat_hann(0 - t) for t in tau)
        rhs = 2 * math.pi * phi2_hann(z)
        worst = max(worst, abs(lhs - rhs) / abs(rhs))
    return worst


def hann_zeros(kmax: int = 4):
    f = lambda g: phi2_hann(complex(g, 0)).real
    roots, x, prev = [], 0.1, f(0.1)
    while x < 42 and len(roots) < kmax:
        x += 0.005
        cur = f(x)
        if prev * cur < 0:
            roots.append(brentq(lambda t: phi2_hann(complex(t, 0)).real,
                                x - 0.005, x))
        prev = cur
    return roots


# ---------------------------------------------------------------------------
# finding 3: the MT window, the live kernel, alias defect, entry card
# ---------------------------------------------------------------------------


def mt_kernel_identity(us=(0.2, 0.5, 0.9, 1.3, 2.5)):
    """g_MT(u) = (phihat_mt at 2 pi u)^2 normalised: worst rel defect."""
    worst = 0.0
    for u in us:
        lhs = float(g_kernel(np.array([u]))[0])
        v = phihat_mt(complex(2 * math.pi * u, 0)).real
        v0 = phihat_mt(0j).real
        rhs = (v / v0) ** 2
        worst = max(worst, abs(lhs - rhs) / max(abs(lhs), 1e-30))
    return worst


def mt_law_d(samples=((0.3, 0.0), (0.37, 0.2), (1.9, 0.45))):
    """B_mt(z, 0) vs 2 pi Phi2_mt(z): the measured alias defect (~0.5%)."""
    tau = np.arange(-80, 81, 1.0)
    worst = 0.0
    for x, y in samples:
        z = complex(x, y)
        lhs = sum(phihat_mt(z - t) * phihat_mt(0 - t) for t in tau)
        rhs = 2 * math.pi * phi2_mt(z)
        worst = max(worst, abs(lhs - rhs) / abs(rhs))
    return worst


def mt_entry_card(ys=(0.1, 0.3, 0.45, 0.49)):
    """sigma^2, min W and min W / sigma^2 at the MT window."""
    def W(g, y):
        v = phi2_mt(complex(g, y))
        return 2 * (v.real ** 2 - v.imag ** 2) / A_MT ** 2

    def sigma2(y):
        return (phi2_mt(complex(0, 2 * y)).real - A_MT) / (2 * A_MT)

    card = {}
    for y in ys:
        vals = [(W(g, y), g) for g in np.arange(0.02, 45, 0.01)]
        mn = min(vals)
        s2 = sigma2(y)
        card[y] = {"sigma2": s2, "minW": mn[0], "at_g": mn[1],
                   "ratio": mn[0] / s2}
    return card


def audit():
    print("= finding 1: the hunt window is CG-degenerate =")
    fl, roots = hunt_floor()
    print(f"  omega zeros: {['%.5f' % r for r in roots]}")
    print(f"  ratios: {['%.4f' % (r / roots[0]) for r in roots]}"
          "   (arithmetic to ~1e-4; the floor's own lesion condition)")
    print(f"  bucket LP floor with omega^2: {fl:.2e}  (CG's g gives 1.1e-4 "
          "at the same nu)")
    print("= finding 2: the Hann grid window =")
    print(f"  LAW D grid identity defect: {hann_law_d():.2e}  "
          "(B = 2 pi Phi2_h, alias-free)")
    hz = hann_zeros()
    print(f"  kernel zeros: {['%.5f' % r for r in hz]} = 6pi, 8pi, 10pi, "
          f"12pi; 2 lambda_1 - lambda_4 = {2 * hz[0] - hz[3]:+.2e} "
          "(CG-degenerate EXACTLY)")
    print("= finding 3: the MT window (the live kernel) =")
    print(f"  g_MT = normalised (FT cos(sqrt2 t) box)^2: defect "
          f"{mt_kernel_identity():.2e}")
    print(f"  lambda ratios: "
          f"{['%.4f' % (r / lambda_roots(1)[0]) for r in lambda_roots(4)]} "
          "(non-arithmetic: the floor lives)")
    print(f"  LAW D grid identity defect: {mt_law_d():.2e}  "
          "(the box aliases at +-2pi: carry one-sidedly in the re-run)")
    print("  entry card (retention structure at the MT window):")
    for y, row in mt_entry_card().items():
        print(f"    y={y}: sigma2 {row['sigma2']:.6f}  minW "
              f"{row['minW']:+.6f} at g={row['at_g']:.2f} "
              f"(= {row['at_g'] / (2 * math.pi):.3f} mean gaps)  "
              f"minW/sigma2 = {row['ratio']:+.3f}")
    print("  (hunt window's LAW I constant: -(1+m0) = -1.2137; the MT")
    print("   window's measured envelope is -0.43: 3x friendlier)")


if __name__ == "__main__":
    audit()
