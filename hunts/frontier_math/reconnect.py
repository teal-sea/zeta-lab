"""Level 7, phase 3: the reconnect — the first reading of the decimal.

THE MECHANISM, RESTATED.  The 2026 clean kill (CLEAN-KILL-REPORT.md) proved
that the withdrawn 0.672529 chain broke at exactly one place: the off-line
zero-side blocks are hyperbolic (transpose, not conjugate transpose), so
``tr(P1 Q') >= 0`` is false and the discarded on-line cross mass could not
be retained AT ALL — "controlling the negative interaction would require an
additional unconditional input about off-line blocks."  Levels 1-7 built
that input: theta_full > 0 means a definite fraction of the on-line
internal mass R(P) = tr P1^2 - s_1 survives the worst admissible off-line
configuration, unconditionally within the chain's stated labels.

THE COMPOSITION (the candidate formula).  The withdrawn arithmetic fed the
full cross floor into the count: value = H + 2 c_u.  With retention
theta_full instead of 1, the same plumbing gives the candidate

    proportion_candidate = H_pinned + 2 * theta_full * c_u^{one-sided},

where c_u is the ordered-gap (Cheer-Goldston bucket) floor at the
unconditional gap density nu_on = H (the bootstrap step audited
noncircular in PROOF-LEDGER.md), and H_pinned = 0.6725007037... is the
paper's Theorem D constant.

WHAT IS HARDENED HERE (the withdrawn-run lessons, applied):

- **kernel minima are one-sided**: the sampled `_GTable.minimum` of the
  withdrawn run is replaced by grid minima minus a measured-slope Lipschitz
  margin (`HardenedGTable`), with a resolution ladder;
- **the calibration control** must still reproduce CG's printed floor;
- **the lesion** (lambda_2 moved to 2 lambda_1) must still kill the floor;
- **the census / total-length constraint** is the audited LP (unchanged);
- **the bootstrap** nu_on = H is the audited noncircular first step.

WHAT IS *NOT* CLAIMED.  The reading below is a CANDIDATE, not a theorem.
Its named unproven steps, in severity order:

1. **The transplant lemma** — that the paper's final constant is linear in
   the retained on-line cross mass with coefficient 1 (the withdrawn
   arithmetic's plumbing, audited at every gate except the one theta_full
   now supplies), including the kernel normalization matching between the
   grid form omega^2 and the MT kernel g of the ordered-gap floor.
2. **theta_full's own labels** — the v-certificate (level 7 phase 1) is
   quadrature-measured, not yet arb-hardened; the pair-side of the joint
   cap is exact per configuration but placement-freeness rests on the
   swept families plus the stacking floor.
3. Taper/truncation bookkeeping of the upstream count at the new constant
   (the audit found the old losses asymptotically negligible; they must be
   restated one-sided for the composed value).

Per the operating rules, no proportion is claimed to have moved; this
module records the first reading and its exact conditions.

Run ``.venv/bin/python hunts/frontier_math/reconnect.py`` (~2 min).
"""

from __future__ import annotations

import sys
from pathlib import Path

import numpy as np

sys.path.insert(0, str(Path(__file__).resolve().parent))
from cg_transplant import (  # noqa: E402
    CG_EDGES, CG_FLOOR, CG_NU, H_PAPER, _GTable, bucket_floor, g_kernel,
    lambda_roots, lesion_wrong_lambda2, optimize_edges,
)

#: the pinned upstream Theorem D constant (PROOF-LEDGER.md); the exact MT
#: arithmetic 2 - MT_CONST = 0.6725007233... sits 2e-8 above it, and the
#: reading is taken against the pinned (smaller, conservative) value.
H_PINNED = 0.6725007037

#: level-6a/7 retained fraction of the on-line internal mass
THETA_FULL = 0.02


class HardenedGTable(_GTable):
    """The withdrawn run's sampled minimum, made one-sided.

    Grid minimum minus max|g'| * step, with |g'| measured on a 4x-finer
    grid and inflated x1.5; root cells still return exactly 0 (g >= 0
    everywhere, so 0 is a valid lower bound wherever a root lies).
    """

    def __init__(self, n: int = 600001, hi: float = 6.0):
        super().__init__(n=n, hi=hi)
        xf = np.linspace(0.0, hi, 4 * (n - 1) + 1)
        vf = g_kernel(xf)
        self.gprime_max = 1.5 * float(
            np.abs(np.diff(vf) / np.diff(xf)).max()
        )
        self.step = float(self.x[1] - self.x[0])

    def minimum(self, lo: float, hi: float) -> float:
        if any(lo <= root <= hi for root in self.roots):
            return 0.0
        i, j = np.searchsorted(self.x, [lo, hi])
        grid_min = float(self.v[max(i - 1, 0): j + 1].min())
        return max(0.0, grid_min - self.gprime_max * self.step)


def first_reading(theta_full: float = THETA_FULL, verbose: bool = True):
    """The candidate value and its exact deficit against the target."""
    lam = lambda_roots()
    table = HardenedGTable()
    # calibration control: CG's printed floor from CG's inputs
    fl_cg = bucket_floor(CG_NU, *CG_EDGES, table=table)
    # the floor at the unconditional density, edges optimised, hardened
    nu_on = H_PINNED
    floor, edges = optimize_edges(nu_on, table=table)
    lesion = lesion_wrong_lambda2(nu_on, edges)
    # resolution ladder
    ladder = {}
    for n in (150001, 600001, 2400001):
        t = HardenedGTable(n=n)
        ladder[n] = bucket_floor(nu_on, *edges, table=t)
    candidate = H_PINNED + 2 * theta_full * floor
    reading = {
        "lambda": lam,
        "cg_control": (fl_cg, CG_FLOOR),
        "nu_on": nu_on,
        "floor_one_sided": floor,
        "edges": edges,
        "lesion": lesion,
        "ladder": ladder,
        "theta_full": theta_full,
        "candidate": candidate,
        "target": H_PINNED,
        "improvement": candidate - H_PINNED,
        "strict": candidate > H_PINNED,
    }
    if verbose:
        print("= reconnect: the first reading of the decimal =")
        print(f"  kernel zeros lambda_k: "
              + ", ".join(f"{x:.5f}" for x in lam))
        print(f"  calibration: hardened floor at CG inputs = {fl_cg:.8f}"
              f"  (CG printed {CG_FLOOR}; hardened must be <= printed)")
        print(f"  bootstrap density nu_on = {nu_on:.10f} (audited noncircular)")
        print(f"  one-sided floor c_u = {floor:.8f} at edges "
              f"{tuple(round(x, 5) for x in edges)}")
        print(f"  lesion (lambda_2 -> 2 lambda_1): floor = {lesion:.8f} "
              f"(must be ~0: {'dies' if lesion < 1e-6 else 'SURVIVES: BUG'})")
        for n, fl in ladder.items():
            print(f"  ladder n={n}: floor = {fl:.10f}")
        print(f"  retained fraction theta_full = {theta_full}")
        print(f"  CANDIDATE = {H_PINNED} + 2 * {theta_full} * {floor:.8f}")
        print(f"            = {candidate:.10f}")
        print(f"  first reading: {candidate:.10f} vs target {H_PINNED}"
              f"  ({'+' if reading['strict'] else '-'}"
              f"{abs(reading['improvement']):.2e})")
        print("  STATUS: CANDIDATE — named unproven steps: the transplant")
        print("  lemma (kernel matching + linear plumbing), the v-certificate")
        print("  arb pass, pair-side placement freeness, taper/truncation")
        print("  restated one-sided. No proportion is claimed to have moved.")
    return reading


if __name__ == "__main__":
    first_reading()
