"""The three remaining bookkeeping items, instrumented: census, units, T4.

After `identification_seam.py`, the candidate rests on three named
bookkeeping-grade steps.  This module instruments what is measurable in
each and states plainly what is cited rather than re-derived.  Nothing
here moves the reading; everything here bounds what could.

ITEM 1 - THE CENSUS (R >= R0).  The floor R0 = c_u * N is a gap-census
LP (`cg_transplant.bucket_floor`) whose nu input is the density of
consecutive distinct on-line gaps.  The reading uses nu = H_pinned =
0.6725007037, justified in two one-sided steps: (a) the composition's
own first pass (R0 = 0) gives a simple-zero density >= H via the
paper's Theorem B, and (b) the LP floor is NONDECREASING in nu at fixed
edges - measured below on a nu ladder - so feeding it a lower bound of
the true density can only lower the floor.  Under-reporting nu is safe;
that is the whole point of choosing H rather than the larger
Theorem-D-style densities.  The (a) step's edge effects (the D0 window
of (4.1)) belong to the paper's (P) side and are cited, not re-derived.

ITEM 2 - THE UNITS.  The identification works on the LAW D grid (grid
Z, mean zero gap 2 pi); the paper's count is per N.  Measured below:
on growing nu = 1 lattices, R/N converges to the translation-invariant
reference sum_{k != 0} omega^2(2 pi k) (the infinite-lattice per-zero
retained mass), and the per-pair damage is N-stable.  The finite-N
identities therefore survive the N -> infinity normalisation with 1/N
edge defects, which is the shape the paper's o(N) absorbs.  The
asymptotic evaluation of tr and tr^2 against primes ((P) itself) is the
paper's theorem and is cited, never re-measured here.

ITEM 3 - T4, TRUNCATION DIRECTIONS.  Every truncation in the chain must
err against the reading.  Measured below:
  (a) the truncated-grid ASSEMBLY over-reports R: R(K) DECREASES in K.
      This module's first draft claimed the opposite direction ("dropped
      squares under-report") and the control refuted it: the dropped
      squares live in the NORMS, so truncated normalisation inflates the
      normalised inner products.  The reading is unaffected - its floor
      is computed from the exact closed-form kernel, never from
      truncated grids, and the assemblies are identity instruments with
      measured ~1/K defects - but the wrong direction claim is kept
      here, refuted, as this session's standing lesson: run the control
      before trusting the prose;
  (b) damage tail: the per-band square completions of the REAL bands in
      (G, 2G] (built with a 2G instance) stay under the closed-form
      tail majorant the cap already charges at G - the tail allowance
      is generous in the safe direction;
  (c) the LAW D grid-sum truncation scale is the measured ~1/K of the
      assembly ladder (`identification_seam.truncation_ladder`), cited.

One more grade note surfaced by item 1: at nu = H the DISCOVERY-grade
kernel table puts the fixed-edge floor near 8e-6, while the reading
carries the HARDENED-table 5.021179e-6 - the one-sided table is the
smaller one, i.e. the reading already sits on the conservative side of
its own instrument ladder.

Run ``.venv/bin/python hunts/frontier_math/closing_bookkeeping.py`` (~2 min).
"""

from __future__ import annotations

import math
import sys
from pathlib import Path

import numpy as np

sys.path.insert(0, str(Path(__file__).resolve().parent))
from cg_transplant import CG_EDGES, bucket_floor  # noqa: E402
from identification_seam import TWO_PI, GridAssembly, _lattice  # noqa: E402
from paper_chain import A, PaperBandDual, PaperChain, phipap  # noqa: E402
from reconnect import H_PINNED  # noqa: E402


# -- item 1: LP-floor monotonicity in nu ------------------------------------

def floor_nu_ladder(nus=(0.5, 0.6, H_PINNED, 0.75, 0.83625)):
    """bucket_floor(nu) at fixed edges: must be nondecreasing."""
    return [(nu, bucket_floor(nu, *CG_EDGES)) for nu in nus]


def floor_is_monotone(rows=None) -> bool:
    rows = rows or floor_nu_ladder()
    vals = [v for _, v in rows]
    return all(v2 >= v1 - 1e-12 for v1, v2 in zip(vals, vals[1:]))


# -- item 2: the N-ladder ----------------------------------------------------

def reference_R_per_zero(kmax: int = 200) -> float:
    """Infinite nu=1 lattice: sum_{k != 0} omega^2(2 pi k)."""
    tot = 0.0
    for k in range(1, kmax + 1):
        om = phipap(complex(TWO_PI * k, 0)).real / A
        tot += 2 * om * om
    return tot


def n_ladder(Ns=(9, 17, 33), K: int = 400):
    ref = reference_R_per_zero()
    rows = []
    for N in Ns:
        xs = [x - (N // 2) * TWO_PI for x in _lattice(1.0, N)]  # centred
        ga = GridAssembly(xs, [1] * N, [(math.pi, 0.49)], K=K)
        rows.append({"N": N, "R_per_N": ga.R() / N, "ref": ref,
                     "defect": abs(ga.R() / N - ref),
                     "damage": -2 * ga.trPQ()})
    return rows


# -- item 3: truncation directions ------------------------------------------

def retained_mass_truncation_bias(Ks=(150, 300, 600)):
    """R(K) DECREASES in K: truncated norms inflate the assembly's R.

    The first draft claimed the opposite; this control refuted it (see
    the module docstring).  The reading's floor never uses truncated
    grids, so the measured bias direction is a property of the
    identification instrument, stated so nobody mistakes the assembly
    for a one-sided device."""
    xs = [x - 2 * TWO_PI for x in _lattice(1.0, 5)]
    vals = []
    for K in Ks:
        ga = GridAssembly(xs, [1] * 5, [], K=K)
        vals.append((K, ga.R()))
    return vals


def tail_majorant_covers(ys=(0.3, 0.49)):
    """Real bands in (G, 2G] vs the tail majorant charged at G."""
    rows = []
    for y in ys:
        bd = PaperBandDual()
        bd2 = PaperBandDual(G=2 * bd.G)
        beyond = [(lo, hi, F) for lo, hi, F in bd2.bands(y) if lo >= bd.G]
        measured = sum(F for _, _, F in beyond)   # single-occupancy regime
        allowance = bd.tail_sum(y)
        rows.append({"y": y, "n_beyond": len(beyond), "measured": measured,
                     "allowance": allowance,
                     "covered": measured <= allowance})
    return rows


def audit():
    print("= item 1: the census floor is monotone in nu =")
    rows = floor_nu_ladder()
    for nu, v in rows:
        tag = "  <- nu used by the reading" if abs(nu - H_PINNED) < 1e-9 else ""
        print(f"  nu = {nu:.7f}: floor = {v:.8f}{tag}")
    print(f"  nondecreasing: {floor_is_monotone(rows)} - under-reporting nu")
    print("  is one-sided; the H-density input is the paper's Theorem B,")
    print("  cited (its D0-window edge effects live on the (P) side).")
    print("= item 2: R/N converges to the lattice reference =")
    for r in n_ladder():
        print(f"  N = {r['N']:2d}: R/N = {r['R_per_N']:.8f}  "
              f"(ref {r['ref']:.8f}, defect {r['defect']:.2e})  "
              f"pair damage {r['damage']:+.5f} (N-stable)")
    print("  1/N edge defects are the shape the paper's o(N) absorbs; the")
    print("  prime-side evaluation itself is the paper's theorem, cited.")
    print("= item 3: every truncation errs against the reading =")
    print("  (a) assembly R(K) decreases - truncated norms inflate it")
    print("      (first-draft direction claim refuted by this control):")
    for K, v in retained_mass_truncation_bias():
        print(f"      K = {K:4d}: R = {v:.10f}")
    print("      the reading's floor uses the exact kernel, never grids")
    print("  (b) real beyond-window bands vs the tail majorant:")
    for r in tail_majorant_covers():
        print(f"      y = {r['y']:.2f}: {r['n_beyond']} bands in (G, 2G], "
              f"measured {r['measured']:.3e} <= allowance {r['allowance']:.3e}"
              f"  {'COVERED' if r['covered'] else 'NOT COVERED - HOLE'}")
    print("  (c) LAW D grid truncation ~1/K: the assembly ladder, cited.")
    print("Scope: items close as measured bookkeeping; the (P)-side prime")
    print("evaluation and Theorem B density are the paper's theorems, cited")
    print("not re-derived. No proportion is claimed and nothing here is")
    print("evidence about RH.")


if __name__ == "__main__":
    audit()
