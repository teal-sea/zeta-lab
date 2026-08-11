"""The signed on/off incidence law and the exclusion of the obstruction family.

Context.  ``INTERACTION-CONTROL-REPORT.md`` ends with a hierarchy whose level 1
requires "an unconditional zeta constraint that excludes the obstruction
family" before any further decimal search.  The family
(:mod:`interaction_obstruction`) defeats every universal strengthening
``theta R(P)`` of the pinned paper's rank-trace step because the paper's
retained data (rank, trace, positive index, census, Frobenius moments) never
constrain the *signed incidence values* of an off-line pair.  The paper says
so itself (its section 6): "nothing is assumed about the traces of the
individual pair blocks in Q'".

This module derives and measures the missing signed laws.  Everything rests on
one observation: the paper's Lemma 2.2 (Poisson summation for the Gabor system
at critical spacing ``h = 2pi/L``, no aliasing) extends verbatim to *complex*
arguments, because the support argument in its proof never uses reality.  With
``phihat(z) = int phi(u) e^{izu} du`` and ``Phi2 = FT of phi^2``:

  LAW D (diagonal law).  For every ``z, z'`` in C,
        sum_{k in Z} phihat(z - tau_k) phihat(z' - tau_k) = L Phi2(z - z').
  In particular the *bilinear* self-incidence  sum_k phihat(z - tau_k)^2
  equals ``a L^2`` for every zero, at every depth and every position.  In the
  paper's normalisation (its (4.4)) each distinct zero, on-line or off-line,
  carries bilinear diagonal exactly ``m_rho`` per unit multiplicity.

  LAW E (signed envelope).  Write ``z = t - iy`` (depth ``y = beta - 1/2``).
  The imaginary mass is again alias-free:
        sum_{k in Z} (Im phihat(z - tau_k))^2 = L int phi^2 sinh^2(yu) du
                                             =: a L^2 sigma^2(y),
  independent of ``t``.  Consequently, for EVERY subgrid S (any truncation,
  any placement) and every on-line ordinate ``x``:
        Re sum_{k in S} phihat(z - tau_k)^2            >= -a L^2 sigma^2(y),
        |Im sum_{k in S} phihat(x-tau_k) phihat(z-tau_k)| <= a L^2 sigma(y),
  so each normalised on/off cross cell obeys
        2 Re( Bhat(x, z)^2 ) >= -2 sigma^2(y),
  and each pair's truncated bilinear trace is >= ``-2 m_rho sigma^2(y)``.
  Negative incidence mass *requires depth*: ``sigma(0) = 0``.

  LAW F (depth floor and strip cap).  ``sigma^2(y) <= sinh^2(yL/2)`` (convexity
  of sinh through the origin), and all zeta zeros have ``0 < beta < 1``
  unconditionally, so ``y < 1/2``.  An off-line pair whose cross column
  reaches ``|Im Bhat| = m`` therefore needs ``sigma(y) >= m``, hence depth
  ``y >= y_min(m) > 0``, and is impossible at any placement whenever
  ``m >= sigma(1/2^-)`` -- in particular whenever ``m >= sinh(L/4)``.

Exclusion of the obstruction family (every member, both shapes):

  * The bad pair declares bilinear diagonal ``-m^2 <= -1`` per member.  On the
    full grid LAW D pins the value at ``+1``: margin ``2 m^2 + 2`` (exact
    integers, :func:`family_margins`).
  * On any proper subgrid, the family's on-line declarations (self-incidence
    and mutual incidence exactly 1) fail strictly: the omitted tail
    ``sum_{k not in S} phihat(x - tau_k)^2`` is strictly positive
    (:func:`online_subgrid_strictness`), and mutual incidence 1 needs both
    zero tail and proportional evaluation vectors.
  * The cross column forces ``sigma(y) >= m`` at every placement (LAW E/F), so
    the member is unrealisable outright for ``m >= sigma(1/2^-)``; the
    theta -> 0 defeat needed m -> infinity and now pays an explicit,
    strip-capped depth cost: at height T with bandwidth L = lambda log(T/2pi)
    every member with ``m >= sinh(L/4)`` is dead at every placement.

The moment-matched family reuses the identical bad block, so the same walls
apply (:func:`family_margins` checks this via the imported classes).

Scope, stated plainly.  These laws add retained state to the paper's
interface; they do not improve any proportion and they are not evidence about
RH.  They hold for any conjugate-closed multiset in the strip -- the
Davenport-Heilbronn off-line zero satisfies them too (:func:`dh_rival_check`),
as a structural lemma must (a lemma failing on the rival would be a bug, and
passing distinguishes nothing).  What is excluded is the exact pinned
adversary family, not its epsilon-perturbations; making the exclusion robust
to perturbation is the level-2 projective-consistency task in the hierarchy.

All heavy analytic objects here have closed forms (the ramp is polynomial, so
``phihat`` and ``Phi2`` are finite combinations of sin/cos/sinh values); the
identities are then measured with truncation and precision ladders, an
aliasing lesion, and a planted-wrong decoy, per the hunt's standing controls.

Run ``.venv/bin/python hunts/frontier_math/incidence_law.py`` from the repo
root for the full audit.
"""

from __future__ import annotations

import sys
from dataclasses import dataclass
from fractions import Fraction
from pathlib import Path

from mpmath import mp, mpc, mpf

sys.path.insert(0, str(Path(__file__).resolve().parent))
from interaction_obstruction import MomentMatchedFamily, ScalarFamily  # noqa: E402

#: Septic smoothstep 35 x^4 - 84 x^5 + 70 x^6 - 20 x^7: the lowest-degree
#: polynomial ramp with three vanishing derivatives at both ends, so the
#: window is C^3 as the paper's section 2.2 requires.
RAMP = (0, 0, 0, 0, 35, -84, 70, -20)

#: Below this |c| the moments C_n, S_n use the alternating series; above it,
#: the integration-by-parts recursion.  The recursion is forward-unstable for
#: |c| below the top degree (amplification ~ n!/|c|^n), the series is slow far
#: above it; 24 > 2*deg(ramp^2) keeps both regimes comfortable.
_SERIES_CUTOFF = 24


def _poly_sq(coeffs):
    out = [mp.zero] * (2 * len(coeffs) - 1)
    for i, ai in enumerate(coeffs):
        for j, aj in enumerate(coeffs):
            out[i + j] += ai * aj
    return out


def _cs_moments(c, nmax):
    """C_n = int_0^1 x^n cos(cx) dx and S_n = int_0^1 x^n sin(cx) dx.

    Complex ``c`` is allowed (cosh/sinh arise as cos/sin of imaginary
    argument).  Series below the cutoff, stable recursion above it.
    """
    if abs(c) < _SERIES_CUTOFF:
        C, S = [], []
        floor = mpf(10) ** (-mp.dps - 10)
        for n in range(nmax + 1):
            sC = mp.zero
            sS = mp.zero
            term = mp.one  # c^{2j} / (2j)!
            j = 0
            while True:
                sC += (-1) ** j * term / (n + 2 * j + 1)
                sS += (-1) ** j * term * c / ((2 * j + 1) * (n + 2 * j + 2))
                j += 1
                term *= c * c / ((2 * j - 1) * (2 * j))
                if abs(term) < floor:
                    break
            C.append(sC)
            S.append(sS)
        return C, S
    sc, cc = mp.sin(c), mp.cos(c)
    C = [sc / c]
    S = [(1 - cc) / c]
    for n in range(1, nmax + 1):
        C.append(sc / c - n * S[n - 1] / c)
        S.append(-cc / c + n * C[n - 1] / c)
    return C, S


@dataclass(frozen=True)
class Window:
    """The paper's section-2.2 window: flat top, polynomial C^3 ramps.

    ``phi = 1`` on ``[-(L/2 - w), L/2 - w]``, ramp ``rho((L/2 - |u|)/w)`` on
    the two end intervals, ``supp phi = [-L/2, L/2]``, ``1 <= w <= L/8``.
    """

    L: float
    w: float = 1.0

    def __post_init__(self) -> None:
        if not 1 <= self.w <= self.L / 8:
            raise ValueError("need 1 <= w <= L/8 (paper (2.11))")

    def _ft(self, poly, z):
        """int window_poly(u) cos(zu) du, closed form (window even)."""
        L, w = mpf(self.L), mpf(self.w)
        half, inner = L / 2, L / 2 - w
        z = mpc(z)
        if abs(z) < mpf(10) ** (-mp.dps // 2):
            mid = 2 * inner
        else:
            mid = 2 * mp.sin(z * inner) / z
        C, S = _cs_moments(z * w, len(poly) - 1)
        acc = mp.zero
        ch, sh = mp.cos(z * half), mp.sin(z * half)
        for k, coeff in enumerate(poly):
            if coeff:
                acc += coeff * (ch * C[k] + sh * S[k])
        return mid + 2 * w * acc

    def phihat(self, z):
        """FT of phi at complex z (equals ``h_phi`` of the paper's (2.1))."""
        return self._ft([mpf(c) for c in RAMP], z)

    def Phi2(self, z):
        """FT of phi^2 at complex z (the frame kernel ``Phi`` of Lemma 2.2)."""
        return self._ft(_poly_sq([mpf(c) for c in RAMP]), z)

    @property
    def aL(self):
        """int phi^2 = a L, the diagonal normaliser divided by L."""
        return mp.re(self.Phi2(0))

    @property
    def spacing(self):
        """Critical Gabor spacing h = 2 pi / L."""
        return 2 * mp.pi / mpf(self.L)

    def sigma_sq(self, y):
        """sigma^2(y) = int phi^2 sinh^2(yu) du / (a L) -- LAW E's envelope.

        Uses sinh^2 = (cosh(2yu) - 1)/2 and cosh(2yu) = cos(2iyu), so the
        value is a closed form: (Re Phi2(2iy) - Phi2(0)) / (2 Phi2(0)).
        """
        return (mp.re(self.Phi2(mpc(0, 2 * mpf(y)))) - self.aL) / (2 * self.aL)

    def sigma_sq_sinh_bound(self, y):
        """The convexity majorant sinh^2(yL/2) of sigma^2(y) (LAW F)."""
        return mp.sinh(mpf(y) * mpf(self.L) / 2) ** 2

    def depth_floor(self, m, tol=mpf("1e-12")):
        """Smallest depth y with sigma^2(y) >= m^2, or None past the strip.

        This is LAW F's floor: an off-line pair whose cross column reaches
        |Im Bhat| = m must sit at least this deep.  Returns None when even
        y -> 1/2 cannot reach m (the member is unrealisable at this L).
        """
        m2 = mpf(m) ** 2
        hi = mpf("0.5")
        if self.sigma_sq(hi) < m2:
            return None
        lo = mp.zero
        while hi - lo > tol:
            mid = (lo + hi) / 2
            if self.sigma_sq(mid) >= m2:
                hi = mid
            else:
                lo = mid
        return hi

    def m_cap(self):
        """sigma(1/2^-): no member with m >= this cap is realisable at any
        placement with this window (strip + LAW E)."""
        return mp.sqrt(self.sigma_sq(mpf("0.5")))


@dataclass(frozen=True)
class Grid:
    """The tau_k = offset + k*h evaluation grid; h defaults to critical."""

    window: Window
    offset: float = 0.0
    stretch: float = 1.0  # lesion knob: != 1 breaks the no-aliasing identity

    def tau(self, k):
        return mpf(self.offset) + k * self.window.spacing * mpf(self.stretch)

    def bilinear(self, z, zp, kmin, kmax):
        """sum_{kmin <= k <= kmax} phihat(z - tau_k) phihat(zp - tau_k)."""
        ph = self.window.phihat
        return mp.fsum(ph(z - self.tau(k)) * ph(zp - self.tau(k)) for k in range(kmin, kmax + 1))

    def imag_mass(self, z, kmin, kmax):
        """sum over the grid range of (Im phihat(z - tau_k))^2."""
        ph = self.window.phihat
        return mp.fsum(mp.im(ph(z - self.tau(k))) ** 2 for k in range(kmin, kmax + 1))


# ---------------------------------------------------------------------------
# Identity audits (LAW D, LAW E), with ladder, lesion and decoy controls
# ---------------------------------------------------------------------------


def law_d_defect(window, z, zp, K, offset=0.0, stretch=1.0):
    """| sum_{|k| <= K} phihat phihat - L Phi2(z - zp) |."""
    grid = Grid(window, offset=offset, stretch=stretch)
    lhs = grid.bilinear(z, zp, -K, K)
    rhs = mpf(window.L) * window.Phi2(mpc(z) - mpc(zp))
    return abs(lhs - rhs)


def law_e_defect(window, t, y, K, offset=0.0, stretch=1.0):
    """| sum (Im phihat)^2 - a L^2 sigma^2(y) | at z = t - iy."""
    grid = Grid(window, offset=offset, stretch=stretch)
    lhs = grid.imag_mass(mpc(t, -mpf(y)), -K, K)
    rhs = mpf(window.L) * window.aL * window.sigma_sq(y)
    return abs(lhs - rhs)


def audit_identities(L=8, w=1, K_ladder=(150, 300, 600), dps=25):
    """Measure both laws across a truncation ladder, plus lesion and decoy.

    The truncation defects must descend along the ladder (a real identity
    responds to a better approximation).  The lesion stretches the grid
    spacing by 65/64 -- the aliasing term reappears and its defect must NOT
    descend, which is the artifact-vs-real signature this repo standardises.
    The decoy plants a wrong diagonal constant (off by 1/64) and must be
    refuted by measurement.
    """
    with mp.workdps(dps):
        window = Window(L, w)
        z, zp = mpc("0.3", "-0.2"), mpc("1.1", "0.05")
        deep = mpc("-2.2", "-0.45")
        out = {
            "law_d_ladder": [law_d_defect(window, z, zp, K, offset=7.3) for K in K_ladder],
            "law_d_deep_diag_ladder": [
                law_d_defect(window, deep, deep, K, offset=7.3) for K in K_ladder
            ],
            "law_e_ladder": [law_e_defect(window, 2.71, "0.35", K, offset=7.3) for K in K_ladder],
            "lesion_ladder": [
                law_d_defect(window, z, zp, K, offset=7.3, stretch=65 / 64) for K in K_ladder
            ],
        }
        # translation invariance: same defects from a shifted grid
        out["law_d_shifted"] = law_d_defect(window, z, zp, K_ladder[-1], offset=-13.9)
        # decoy: diagonal planted 1/64 too large must be visibly wrong
        grid = Grid(window, offset=7.3)
        diag = grid.bilinear(deep, deep, -K_ladder[-1], K_ladder[-1])
        planted = mpf(window.L) * window.aL * (1 + mpf(1) / 64)
        out["decoy_gap"] = abs(diag - planted)
        out["decoy_wrong_by"] = mpf(window.L) * window.aL / 64
        return out


# ---------------------------------------------------------------------------
# The signed envelope on subgrids (LAW E), scanned
# ---------------------------------------------------------------------------


def envelope_scan(L=8, w=1, trials=60, seed=20260811, K=200, dps=15):
    """Random subgrids, positions and depths: the floors must never fail.

    Checks, for z = t - iy and random contiguous subgrids S:
      Re sum_S phihat(z-tau)^2  in  [-aL^2 sigma^2(y), aL^2 (1 + sigma^2(y))]
      |Im sum_S phihat(x-tau) phihat(z-tau)| <= aL^2 sigma(y)
    Returns the worst (most binding) normalised margins; both must be >= 0.
    """
    import random

    rng = random.Random(seed)
    with mp.workdps(dps):
        window = Window(L, w)
        aL2 = mpf(window.L) * window.aL
        worst_floor = mp.inf
        worst_ceiling = mp.inf
        worst_cross = mp.inf
        for _ in range(trials):
            t = mpf(rng.uniform(-20, 20))
            y = mpf(rng.uniform(0.0, 0.499))
            x = mpf(rng.uniform(-20, 20))
            lo = rng.randint(-K, K - 10)
            hi = rng.randint(lo, K)
            grid = Grid(window, offset=rng.uniform(-3, 3))
            z = mpc(t, -y)
            s2 = window.sigma_sq(y)
            diag = grid.bilinear(z, z, lo, hi)
            worst_floor = min(worst_floor, (mp.re(diag) + aL2 * s2) / aL2)
            worst_ceiling = min(worst_ceiling, (aL2 * (1 + s2) - mp.re(diag)) / aL2)
            cross = grid.bilinear(x, z, lo, hi)
            worst_cross = min(worst_cross, (aL2 * mp.sqrt(s2) - abs(mp.im(cross))) / aL2)
        return {
            "worst_floor_margin": worst_floor,
            "worst_ceiling_margin": worst_ceiling,
            "worst_cross_margin": worst_cross,
        }


def online_subgrid_strictness(L=8, w=1, K=200, dps=20):
    """On a proper subgrid every on-line self-incidence sits strictly below 1.

    The omitted tail sum_{k not in S} phihat(x - tau_k)^2 has strictly
    positive terms (phihat is real-analytic, not eventually zero), so the
    family's declaration "on-line diagonal exactly 1" forces the full grid --
    where LAW D then pins its bad pair at +2 instead of -2m^2.  Measured:
    the deficit 1 - Re(diag)/aL^2 over half grids at several positions.
    """
    with mp.workdps(dps):
        window = Window(L, w)
        aL2 = mpf(window.L) * window.aL
        grid = Grid(window, offset=0.0)
        out = []
        for x in (mpf("0.0"), mpf("3.7"), mpf("-11.25")):
            half = grid.bilinear(x, x, 0, K)
            out.append((x, 1 - mp.re(half) / aL2))
        return out


# ---------------------------------------------------------------------------
# Exclusion of the obstruction family
# ---------------------------------------------------------------------------


def family_margins(m, L=8, w=1, k=None, dps=25):
    """Exact and measured walls against ScalarFamily(m) (and its dilution).

    Returns the integer full-grid margin (LAW D), the depth floor / strip cap
    verdict (LAW E/F), and -- when k is given -- checks that the
    moment-matched member reuses the identical bad block, so the same walls
    apply to it.
    """
    fam = ScalarFamily(m)
    # LAW D at full grid: declared bilinear pair trace -2m^2, law value +2.
    full_grid_margin = Fraction(2 + 2 * m * m)
    assert fam.q == -2 * m * m  # the declared bad-pair block
    with mp.workdps(dps):
        window = Window(L, w)
        cap = window.m_cap()
        floor = window.depth_floor(m)
        result = {
            "m": m,
            "full_grid_margin": full_grid_margin,
            "m_cap_at_this_L": cap,
            "excluded_at_every_placement": mpf(m) >= cap,
            "depth_floor": floor,
            "depth_floor_kernel_units": None if floor is None else floor * mpf(L),
            "sinh_bound_on_cap": mp.sinh(mpf(L) / 4),
        }
    if k is not None:
        matched = MomentMatchedFamily(m=m, k=k, background_simple=0)
        assert matched.bad == fam  # identical bad block: same walls
        result["moment_matched_shares_bad_block"] = True
    return result


def theta_recovery_floor(L, dps=25):
    """The realisable theta-defeat is capped: theta >= 3/(2 sigma_max^2 + 1).

    The family forced theta <= 3/(2 m^2 + 1) for every abstract m.  With
    LAW E/F only members with m < sigma(1/2^-) survive at bandwidth L, so the
    defeat available from this family at height T is bounded away from zero by
    an explicit (exponentially small, but nonzero and named) quantity.  This
    is a statement about the adversary family, not a zeta proportion.
    """
    with mp.workdps(dps):
        cap_sq = Window(L).sigma_sq(mpf("0.5"))
        return 3 / (2 * cap_sq + 1)


def dh_rival_check(L=8, w=1, K=400, dps=20):
    """The laws hold at the Davenport-Heilbronn off-line zero, as they must.

    The laws are kernel identities for any point of the open strip; they do
    not distinguish zeta from the counterexample, and a claim of that kind
    would be a bug (MISSION checklist item 1).  Measured at the lab's pinned
    off-line zero depth y = Re(rho) - 1/2 = 0.30851..., using its true
    ordinate scaled into the window's ordinate units.
    """
    from zeta.epstein import OFFLINE_ZERO_IM, OFFLINE_ZERO_RE

    with mp.workdps(dps):
        y = mpf(OFFLINE_ZERO_RE[: dps + 5]) - mpf("0.5")
        t = mpf(OFFLINE_ZERO_IM[: dps + 5])
        window = Window(L, w)
        grid = Grid(window, offset=float(t))  # grid landing on the ordinate
        z = mpc(t, -y)
        aL2 = mpf(window.L) * window.aL
        diag = grid.bilinear(z, z, -K, K)
        s2 = window.sigma_sq(y)
        return {
            "depth": y,
            "diag_defect": abs(diag - aL2),
            "sigma_sq_at_dh_depth": s2,
            "cross_envelope_at_dh_depth": -2 * s2,
        }


def audit():
    """Run every control and print the measured record."""
    print("= identity audits (LAW D, LAW E) =")
    ident = audit_identities()
    for key, val in ident.items():
        if isinstance(val, list):
            print(f"  {key}: " + "  ".join(mp.nstr(v, 4) for v in val))
        else:
            print(f"  {key}: {mp.nstr(val, 6)}")
    print("= envelope scan (LAW E on subgrids) =")
    scan = envelope_scan()
    for key, val in scan.items():
        print(f"  {key}: {mp.nstr(val, 8)}")
    print("= on-line strictness on proper subgrids =")
    for x, deficit in online_subgrid_strictness():
        print(f"  x = {mp.nstr(x, 6)}: deficit 1 - diag/aL^2 = {mp.nstr(deficit, 8)}")
    print("= family exclusion =")
    for m in (1, 2, 10):
        rec = family_margins(m, k=100_000 if m == 10 else None)
        line = ", ".join(
            f"{key}={mp.nstr(val, 8) if isinstance(val, (mpf, mpc)) else val}"
            for key, val in rec.items()
        )
        print(f"  m={m}: {line}")
    print("= theta recovery floor at L = 8, 16, 24 =")
    for L in (8, 16, 24):
        print(f"  L={L}: theta >= {mp.nstr(theta_recovery_floor(L), 8)}")
    print("= rival check (Davenport-Heilbronn off-line zero) =")
    for key, val in dh_rival_check().items():
        print(f"  {key}: {mp.nstr(val, 8)}")


if __name__ == "__main__":
    audit()
