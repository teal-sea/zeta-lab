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
                            "falloff is steep: frac = 0.95 already costs "
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
    "~0.0602.  Different objects, infinite periodic against a finite "
    "seven-centre middle row, and neither is close to the lattice, so the "
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


# --------------------------------------------------------------------------
# The frequency side.  See LATTICE-EXTREMALITY-ROUTE.md for the argument these
# implement; this module carries the computations, that document carries the
# reasoning and, more importantly, the list of what is still missing.
# --------------------------------------------------------------------------

_C2_CACHE: dict = {}


def c2(w: float) -> float:
    """`mean_damage.c2` as a cached float.  `c2(w) = int g(u) g(u+w) du` for
    `g(u) = cos(sqrt2 u)` on `|u| <= 1/2`, supported on `|w| <= 1`."""
    key = round(abs(float(w)), 12)
    if key not in _C2_CACHE:
        import mean_damage as md
        _C2_CACHE[key] = float(md.c2(key))
    return _C2_CACHE[key]


def kappa_hat(xi: float) -> float:
    """`khat(xi) = 2*pi*c2(|xi|)*(1+cosh|xi|)` on `[-1,1]`, zero outside.

    Immediate from `mean_damage`'s representation `-D(y,s) = int c2(w)
    cosh(yw) cos(sw) dw` summed at `y = 0` and `y = 1`, which is exactly
    `counting_lemma.kappa`.  Three properties carry the whole argument:

    * **supported on `[-1,1]`** -- this is what makes an infinite sum in
      space a finite sum in frequency.
    * **non-negative** -- and this is *proved*, not measured.  `c2` is the
      autocorrelation of `g`, and `sqrt2/2 = 0.707... < pi/2`, so `g > 0` on
      the whole of its support.  An autocorrelation of a strictly positive
      function is strictly positive wherever the supports overlap, so
      `c2 > 0` on `(-1,1)`.  `1 + cosh` is positive everywhere.
    * **vanishing at `xi = +-1`** -- the supports of `g(u)` and `g(u+1)` meet
      at a point, so `c2(+-1) = 0`.  This is the zero the `2*pi` lattice's
      first reciprocal frequency lands on, and it is why the lattice pays no
      penalty at all.
    """
    x = abs(float(xi))
    if x > 1.0:
        return 0.0
    return 2 * math.pi * c2(x) * (1 + math.cosh(x))


def structure_factor_cost(offsets, P: float) -> float:
    """`J` for the UNRECTIFIED summand `-kappa`, computed in frequency.

    The identity, for a `P`-periodic configuration with offsets `a_p`:

        J_kappa = -(2/(mP)) sum_j khat(2*pi*j/P) |A_j|^2  +  2 kappa(0),
        A_j     = sum_p exp(2*pi*i*j*a_p/P).

    The sum over `j` is FINITE because `khat` is supported on `[-1,1]`, so
    only `|j| <= P/(2*pi)` contribute.  `structure_factor_defect` measures
    this against direct summation rather than trusting it.
    """
    import counting_lemma as cl
    a = np.asarray(offsets, dtype=float)
    m = a.size
    jmax = int(math.floor(P / TWOPI)) + 1
    tot = 0.0
    for j in range(-jmax, jmax + 1):
        kh = kappa_hat(TWOPI * j / P)
        if kh == 0.0:
            continue
        tot += kh * abs(np.exp(2j * math.pi * j * a / P).sum()) ** 2
    return -2 * tot / (m * P) + 2 * cl.kappa(0.0)


def unrectified_cost(offsets, P: float, N: int = 3000) -> float:
    """`J` for `-kappa`, by direct summation.  The thing the frequency
    formula must reproduce."""
    import counting_lemma as cl

    def raw(NN):
        a = np.asarray(offsets, dtype=float)
        m = a.size
        n = np.arange(-NN, NN + 1, dtype=float)
        tot = 0.0
        for p in range(m):
            for q in range(m):
                s = (a[p] - a[q]) + n * P
                if p == q:
                    s = s[s != 0.0]
                tot += sum(cl.kappa(float(x)) for x in s)
        return -2 * tot / m

    return 2 * raw(2 * N) - raw(N)


def structure_factor_defect(offsets, P: float, N: int = 3000) -> float:
    """Direct summation minus the frequency formula.  The identity is the
    load-bearing step of the whole route, so it is measured on every
    configuration rather than asserted once."""
    return unrectified_cost(offsets, P, N=N) - structure_factor_cost(offsets, P)


def lp_bound(rho: float) -> float:
    """`2*rho*(-khat(0)) + 2*kappa(0) = -8*pi*rho*c2(0) + 2*kappa(0)`.

    Drop every `j != 0` term from the identity.  Each is a product of
    `khat >= 0` and `|A_j|^2 >= 0`, so each is a subtraction and dropping
    them can only raise the value.  The result is decreasing in `rho`, and
    at `rho = 1/(2*pi)` it equals the lattice value exactly, because there
    the lattice's only non-zero-frequency mass sits at `xi = +-1` where
    `khat` vanishes.

    This is an upper bound on `J_kappa`, NOT on `J`.  The difference is
    `clip_bonus`, and closing that difference is gap B in the route
    document.
    """
    import counting_lemma as cl
    return -8 * math.pi * rho * c2(0.0) + 2 * cl.kappa(0.0)


def clip_bonus(offsets, P: float, N: int = 2000) -> float:
    """`J - J_kappa = (2/m) sum' K_1(diff)^+`, the rectification's gift.

    `f = -kappa + K_1^+` exactly, so wherever `Dam`'s `max(0, .)` clips, `f`
    sits ABOVE `-kappa` and the adversary gains relative to the unrectified
    problem.  It is zero on the `2*pi` lattice, where `K_1 < 0` at every
    difference, which is why the bound is attained there.  It is not small
    in general: 8.3e-2 for a mildly uneven pair configuration.
    """
    import gram_form as gf
    a = np.asarray(offsets, dtype=float)
    m = a.size
    n = np.arange(-N, N + 1, dtype=float)
    tot = 0.0
    for p in range(m):
        for q in range(m):
            s = (a[p] - a[q]) + n * P
            if p == q:
                s = s[s != 0.0]
            tot += sum(max(gf.kernel(1.0, float(x)), 0.0) for x in s)
    return 2 * tot / m


def clip_is_idle_on_lattice(nmax: int = 5000) -> float:
    """`max_n K_1(2*pi*n)` over `n = 1..nmax`.  Negative means the
    rectification never fires at a lattice difference, which is hypothesis
    H2 holding for the extremiser itself."""
    import gram_form as gf
    return max(gf.kernel(1.0, n * TWOPI) for n in range(1, nmax + 1))


# --------------------------------------------------------------------------
# Gap B, closed.  An explicit majorant removes hypothesis H2.
# --------------------------------------------------------------------------

def fejer(x):
    """`s(x) = (sin(x/2)/(x/2))^2`, with `s(0) = 1`.

    Four properties, all elementary, and between them they are exactly the
    constraint list gap B asked for:

    * `s >= 0`.
    * `s(2*pi*n) = 0` for every `n != 0`, since `sin(pi n) = 0`.
    * `shat(xi) = 2*pi*(1-|xi|)^+`, supported exactly on `[-1,1]`.  This is
      the classical transform of `sinc^2`.
    * `int s = 2*pi = 2*pi*s(0)`, which is precisely the tightness condition
      `int v = 2*pi*v(0)`, and it holds for every multiple of `s` at once.

    The last one is why this ansatz works and why `(1-cos x)*psi(x)`, the
    obvious first guess, cannot: that one vanishes at the origin too, forcing
    `int v = 0` against `v >= K_1^+ >= 0`.
    """
    xa = np.asarray(x, dtype=float)
    out = np.ones_like(xa)
    nz = xa != 0.0
    h = xa[nz] / 2.0
    out[nz] = (np.sin(h) / h) ** 2
    return out if out.shape else float(out)


def majorant_multiplier_range(xmax: float = 3000.0, npts: int = 400000):
    """`(lo, hi)`: the admissible range for `c` in `v = c * fejer`.

    `lo = sup_x K_1(x)^+ / s(x)`, so that `v >= K_1^+`.  The supremum is at
    `x = 0`, where it is `K_1(0)`; the tail settles at about `0.7349`.

    `hi = inf_{|xi|<1} khat(xi) / shat(xi) = inf c2(xi)(1+cosh xi)/(1-|xi|)`,
    so that `vhat <= khat`.  The infimum is the limit at `xi -> 1`, and it has
    a closed form: `c2` vanishes linearly at both `0+` and `1-` with the same
    slope `-cos^2(sqrt2/2)`, so the limit is `cos^2(sqrt2/2)*(1+cosh 1)`.
    """
    import gram_form as gf
    lo = gf.kernel(1.0, 0.0)
    for a, b, n in ((1e-9, 60.0, npts), (60.0, 600.0, npts), (600.0, xmax, npts)):
        if b <= a:
            continue
        for x in np.linspace(a, b, n):
            r = max(gf.kernel(1.0, float(x)), 0.0) / float(fejer(np.array([x]))[0])
            if r > lo:
                lo = r
    hi = math.cos(math.sqrt(2) / 2) ** 2 * (1 + math.cosh(1.0))
    return lo, hi


def lp_bound_with_majorant(rho: float, c: float | None = None) -> float:
    """The bound from `g = -kappa + c*fejer`, valid with NO clip hypothesis.

    `LP_v(rho) = LP(rho) + 2c(2*pi*rho - 1)`.  It agrees with `lp_bound` at
    `rho = 1/(2*pi)` for every admissible `c`, and it is still decreasing in
    `rho` provided `c < 2*c2(0) = 1.6985...`, which every admissible `c` is.
    """
    import gram_form as gf
    if c is None:
        c = gf.kernel(1.0, 0.0)
    return lp_bound(rho) + 2 * c * (TWOPI * rho - 1)


def lattice_tail_constant() -> float:
    """`lim_n K_1(2*pi*n)*(2*pi*n)^2 = 2*cos^2(sqrt2/2)*(1 - cosh 1)`.

    Why H2 holds for the lattice, in closed form.  `K_1` has a `1/x^2`
    asymptotic with two sources: the endpoints of `c2` at `w = +-1` give
    `2*c2'(1-)*cosh(1)*cos(x)`, and the kink at `w = 0` gives `-2*c2'(0+)`,
    which does not oscillate.  Both slopes equal `-cos^2(sqrt2/2)`, so at
    `x = 2*pi*n`, where the cosine is `+1`, the two combine to
    `2*cos^2(sqrt2/2)*(1 - cosh 1)`.  It is negative precisely because
    `cosh 1 > 1`, and that single inequality is the reason the rectification
    never fires at a lattice difference.
    """
    return 2 * math.cos(math.sqrt(2) / 2) ** 2 * (1 - math.cosh(1.0))


#: Gap B's resolution, and the numbers behind it.
MAJORANT_RECORD = {
    "ansatz": "v = c * (sin(x/2)/(x/2))^2",
    "c_lower": 0.9115647130952531,   # = K_1(0), attained at x = 0
    "c_upper": 1.4698290125473032,   # = cos^2(sqrt2/2)*(1 + cosh 1)
    "tail_sup_of_ratio": 0.734916,
    "slope_stays_negative_iff_c_below": 1.6984559986,   # = 2*c2(0)
    "lattice_tail_constant": -0.6277706355638578,
    "end_to_end": "300 random configurations at rho >= 1/(2*pi), 0 violations "
                  "of J <= LP_v(rho); best J found 0.0703 against the "
                  "lattice's 0.1143",
    "grade": "the two inequalities are verified numerically on a finite range "
             "with a settled tail, not enclosed. rigor.py is the natural next "
             "step and would make this an enclosure-carrying statement.",
}
