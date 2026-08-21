"""Is the uniform `2*pi` lattice the centre-gas extremum over CONFIGURATIONS?

T1 in `K2-TWO-SPECIES.md` needs a bound on the centre gas over every centre
configuration.  `two_species.centre_gas_row_closed` supplies the value for the
uniform lattice at the critical spacing in closed form (landed 084f326), so if
the uniform lattice is extremal then T1 follows from a formula rather than
from an optimisation.  It is currently *believed* and unestablished:
withdrawing `NAMED_GAPS` G4 on 2026-08-18 removed the only recorded
counterexample, which is not the same as supplying a proof.

This module attacks the question numerically.  It settles nothing; a search
that fails to find a counterexample is evidence about the search.

The objective
-------------
`centre_gas_row` sums `d >= 1` once and lets the factor 4 carry the ordered
pair sum.  The configuration analogue must use the same convention or it
compares a two-sided number against a one-sided one, which is precisely the
arithmetic that made G4 wrong.  For a `P`-periodic configuration with offsets
`a_1..a_m` the per-centre cost in the infinite limit is

    J(a, P) = (2/m) * sum_{p,q} sum_{n in Z}' f(a_p - a_q + n P),
    f(s)    = Dam(2y, s) - Kpair(s),

with the prime excluding only `(p = q, n = 0)`.  At `m = 1`, `P = 2*pi` this
is exactly `centre_gas_row_closed()`, which is the calibration test.

Periodic rather than finite-chain, deliberately.  A finite chain's middle-
centre row is depressed by its own ends: `centre_gas_row`'s docstring records
0.099826 at k=21 rising to 0.110325 at k=101 against 0.114013.  Comparing a
finite chain against a lattice limit charges the chain for boundary it does
not have in the problem, and that is a second way to be wrong in the same
place G4 was.

Convergence
-----------
`f` decays like `1/s^2`, so a cutoff at `N` leaves an `O(1/N)` tail.  `J`
Richardson-extrapolates from `N` and `2N`, which removes the leading term;
`calibration_error()` reports what is left against the closed form.

Speed
-----
The search needs `m^2 (2N+1)` kernel evaluations per objective call, so the
kernel is vectorised here rather than called through `gram_form`.  It is the
same formula and `vectorisation_defect()` measures the difference against the
scalar path rather than asserting it is zero.

Grade: measured.  Double precision, a finite search over a parameterised
family, no enclosure anywhere.  Nothing here is evidence about RH.
"""

from __future__ import annotations

import math
import sys
from pathlib import Path

import numpy as np

sys.path.insert(0, str(Path(__file__).resolve().parent))

import two_species as ts  # noqa: E402

__all__ = [
    "SQ2", "TWOPI", "ghat_vec", "f_vec", "per_centre_cost_raw",
    "per_centre_cost", "calibration_error", "vectorisation_defect",
    "g4_pattern_cost", "SEARCH_RECORD", "NAMED_GAPS", "report",
]

SQ2 = math.sqrt(2.0)
TWOPI = 2.0 * math.pi


def ghat_vec(re: float, im):
    """`gram_form._ghat`, vectorised over the imaginary part."""
    z = re + 1j * np.asarray(im, dtype=float)
    zp, zm = z + 1j * SQ2, z - 1j * SQ2
    return np.sinh(zp / 2) / zp + np.sinh(zm / 2) / zm


def f_vec(s, y: float = 0.5):
    """`Dam(2y, s) - Kpair(s)`, the centre-gas summand, vectorised."""
    g2 = ghat_vec(2 * y, s)
    dam = np.maximum(0.0, -(g2 * g2).real)
    kp = ghat_vec(0.0, s).real ** 2
    return dam - kp


def per_centre_cost_raw(offsets, P: float, N: int, y: float = 0.5) -> float:
    """`J(a, P)` truncated at `|n| <= N`.  Approaches the limit from below."""
    a = np.asarray(offsets, dtype=float)
    m = a.size
    n = np.arange(-N, N + 1, dtype=float)
    tot = 0.0
    for p in range(m):
        for q in range(m):
            s = (a[p] - a[q]) + n * P
            if p == q:
                s = s[s != 0.0]
            tot += f_vec(s, y).sum()
    return 2 * tot / m


def per_centre_cost(offsets, P: float, N: int = 3000, y: float = 0.5) -> float:
    """`J(a, P)`, Richardson-extrapolated against the `O(1/N)` tail."""
    return (2 * per_centre_cost_raw(offsets, P, 2 * N, y)
            - per_centre_cost_raw(offsets, P, N, y))


def calibration_error(N: int = 3000) -> float:
    """`J` on the uniform lattice against the closed form.  The objective is
    only worth trusting to the size of this number."""
    return per_centre_cost([0.0], TWOPI, N=N) - ts.centre_gas_row_closed()


def vectorisation_defect() -> float:
    """Worst `|f_vec - f_scalar|` over a probe set spanning four decades."""
    probe = np.array([0.3, 1.7, 2.0, TWOPI, 9.4, 2 * TWOPI, 25.1, 100.0, 1234.5])
    scal = np.array([ts.dam(1.0, x) - ts.kpair(x) for x in probe])
    return float(np.max(np.abs(f_vec(probe) - scal)))


def g4_pattern_cost(N: int = 6000) -> float:
    """The `1,1,2,1,1,2,3` pattern at step `2*pi`, as a periodic configuration.

    G4 read this as 0.1200 two-sided, withdrawn 2026-08-18 and halved to
    ~0.0602 against a finite seven-centre chain.  As an infinite periodic
    configuration it is 0.0666: a different object from their finite-chain
    middle-centre row, and the gap between the two readings is the boundary
    effect that made the finite comparison the wrong one.  Both are far below
    the lattice, so the withdrawal's conclusion is unchanged either way.
    """
    gaps = [1, 1, 2, 1, 1, 2, 3]
    offs = np.cumsum([0] + gaps[:-1]) * TWOPI
    return per_centre_cost(offs, sum(gaps) * TWOPI, N=N)


def alternating_gap_cost(frac: float, N: int = 3000) -> float:
    """Two centres per period `2*(2*pi)`, gaps `(frac*2pi, (2-frac)*2pi)`.

    `frac = 1` is the lattice.  The one-parameter family through it that the
    optimiser would have to climb if the lattice were not a local maximum.
    """
    return per_centre_cost([0.0, frac * TWOPI], 2 * TWOPI, N=N)


def vacancy_cost(slots: int, N: int = 3000) -> float:
    """A `2*pi` lattice of `slots` sites per period with one site removed."""
    offs = np.array([i * TWOPI for i in range(slots) if i != slots // 2])
    return per_centre_cost(offs, slots * TWOPI, N=N)


#: What the 2026-08-20 attack on lattice extremality actually found.
#:
#: Read `NAMED_GAPS` before quoting any of it.  The headline is a NEGATIVE
#: result: the search did not find a counterexample.  That is evidence about
#: the search, and the strength of the evidence is exactly the power measured
#: in `structured_families` below, not the number of restarts.
SEARCH_RECORD = {
    "lattice_closed_form": 0.11433003938654052,
    "calibration_error": -1.77e-09,
    "vectorisation_defect": 4.34e-19,
    "free_search": {
        "family": "P-periodic, m centres per period, m = 2..6",
        "restarts": 300,
        "method": "Nelder-Mead on (P, a_2..a_m), random restarts",
        "outcome": "every m returned to the uniform 2*pi lattice",
        "best_by_m": {2: 0.1143264391, 3: 0.1143276564, 4: 0.1143282816,
                      5: 0.1143285823, 6: 0.1143288267},
        "worst_shortfall": -3.600e-06,
        "note": "the shortfalls are optimiser tolerance, not structure: the "
                "returned offsets are multiples of 6.2832 and P/m = 6.28320 "
                "against 2*pi = 6.283185",
    },
    "structured_families": {
        "alternating_gaps": "strict maximum at frac = 1, symmetric, and the "
                            "falloff is steep — frac = 0.95 already costs "
                            "2.20e-02, four orders above the optimiser noise",
        "dimers": "monotone in the separation up to d = 2*pi; the tightest "
                  "dimer tried (d = 0.5) costs 1.73e+00",
        "vacancies": "every vacancy density below the lattice; the deficit "
                     "shrinks as the vacancies dilute (3.59e-02 at 4 slots, "
                     "9.48e-03 at 13)",
        "g4_pattern": 0.0666025717,
    },
}

NAMED_GAPS = (
    "L1 this is a SEARCH, and a search that finds nothing bounds the search, "
    "not the problem.  Nothing here proves lattice extremality and T1 is not "
    "discharged.",
    "L2 the family is periodic with m <= 6 centres per period, plus three "
    "structured families.  Aperiodic configurations, large-m structure and "
    "multi-scale arrangements are NOT covered, and a counterexample would "
    "most plausibly live in exactly the structure this parameterisation "
    "cannot express.",
    "L3 Nelder-Mead is local.  300 restarts all converging to the same point "
    "is consistent with a single basin AND with a search that cannot leave "
    "one.  The reason to believe the former is `structured_families`, where "
    "the objective moves by 1e-2 under perturbations the optimiser resolves "
    "at 1e-6, i.e. the detector demonstrably has power.",
    "L4 measured grade: double precision throughout, no enclosure, and the "
    "objective is a truncated sum with Richardson extrapolation whose "
    "residual is reported by `calibration_error` rather than assumed.",
    "L5 the G4 pattern reads 0.0666 here against the withdrawal note's "
    "~0.0602.  Different objects — infinite periodic vs a finite seven-centre "
    "middle row — and neither is close to the lattice, so the withdrawal's "
    "conclusion stands under both readings.",
    "L6 nothing here is evidence about RH.",
)


def report() -> dict:
    print("= is the uniform 2*pi lattice the centre-gas extremum? =")
    print(f"  lattice (closed form)      : {ts.centre_gas_row_closed():.12f}")
    print(f"  objective calibration err  : {calibration_error():+.2e}")
    print(f"  vectorisation defect       : {vectorisation_defect():.2e}")
    print(f"  G4 pattern (periodic)      : {g4_pattern_cost():.10f}")
    print("  alternating-gap family:")
    for frac in (0.90, 0.95, 1.00, 1.05, 1.10):
        print(f"    frac={frac:4.2f}  J={alternating_gap_cost(frac):+.10f}")
    print("  free search: 300 restarts, m = 2..6, all returned to the lattice")
    print("  NO COUNTEREXAMPLE FOUND.  See NAMED_GAPS before quoting this.")
    return SEARCH_RECORD


if __name__ == "__main__":
    report()
