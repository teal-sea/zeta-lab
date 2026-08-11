"""Level 2: projective gap consistency and the anti-duplication law.

`SIGNED-INCIDENCE-LAW.md` delivered level 1 of the hierarchy in
``INTERACTION-CONTROL-REPORT.md`` and named two things it did not do: the
per-cell envelope is *n-extensive* (n cells may each sit at the floor, so one
off-line pair's budgeted negativity grows with the number of on-line zeros),
and the exclusion of the obstruction family used the exactness of its
declarations, so an epsilon-perturbed family was untouched.  Level 2 of the
hierarchy is exactly the repair: "one off-line pair marked against two
consecutive on-line gaps; projective consistency between one-gap marginals
and marked two-gap words; kill control = duplicate one off-line pair
independently in overlapping cells".

Both defects have one cause and one cure.  LAW D (level 1) says the full-grid
incidence of two points is ``Phi2`` of their *difference*.  Level 1 used only
its diagonal.  Using it off-diagonal turns every incidence value into a
sample of one fixed analytic kernel at an argument that the configuration's
gaps determine:

  LAW G (projective gap consistency).  Write ``omega(g) := Phi2(g)/Phi2(0)``.
  On the full grid the normalised on-line correlation of two zeros separated
  by ``g`` is exactly ``omega(g)``, with ``omega(0) = 1`` and
  ``|omega(g)| < 1`` for ``g != 0``.  Hence a declared correlation IS a
  declared gap; and for three consecutive on-line zeros the marked two-gap
  word is not free -- its outer correlation must be ``omega(g1 + g2)``, not
  any independently chosen value.  Correlations near 1 are only available at
  gaps near 0.

  LAW H (anti-duplication / aggregate caps).  Because the kernel decays
  (the paper's (2.17): ``|Phi2(r)| <= psi(r) = min(L, 2/|r|, c_rho/(w r^2))``)
  while the number of zeros in a unit interval is at most ``nu``
  (unconditional: ``N(t+1) - N(t) <= A_0 log(t+3)``, the same input the
  paper's own Proposition 4.2 uses), the total incidence mass any single
  point can have against a whole configuration is capped *independently of
  the configuration's size*:

      on-line:  sum_{j != i} omega(x_i - x_j)^2  <=  kappa(nu)
      on/off :  sum_j |Bhat(x_j, z)|^2           <=  kappa_cross(nu, y)

  with explicit ``kappa`` and ``kappa_cross`` below.  Consequently the signed
  aggregate interaction of one off-line pair with ALL on-line zeros is
  ``>= -2 kappa_cross(nu, y)`` -- an n-independent floor where level 1 had
  ``-2 n sigma^2(y)``.  One pair cannot be spent twice.

What this excludes, robustly.  The obstruction family's on-line block has
``R(P) = n(n-1)``: every pair of its n on-line labels is fully correlated.
LAW G says full correlation means zero gap, so the family's cross mass is
available only from a single point of multiplicity n -- which the paper
charges to the index side at the flat cost 4, not to the rank side.  LAW H
makes this quantitative and declaration-free: since ``R(P) <= n kappa(nu)``
for ANY real configuration, the family's ``R(P) = n(n-1)`` forces

      n  <=  kappa(nu) + 1  =  O(log T),

so no member with more on-line labels than that is realisable at any depth,
any placement, or any perturbation of its declarations.  This is the
epsilon-robust exclusion level 1 could not give: it bounds the *quantity*,
not the declaration.

The residue for the recovery coefficient.  The family forced
``theta <= 3/(n-1)`` and drove it to zero by taking n large.  Level 1 capped
the realisable members through the depth cap, leaving a floor exponentially
small in the bandwidth L.  Level 2 caps them through the density instead:

      theta  >=  3 / kappa(nu)        (this family shape only)

which is ``~ 1/log T`` rather than ``~ e^{-L/2}``.  Recorded as a statement
about what this adversary family can obstruct -- NOT as a proof that any
particular theta is admissible, which is level 3's telescoping-potential
task and is not attempted here.

Scope.  Nothing here moves a proportion and nothing here is evidence about
RH.  The laws hold for every conjugate-closed multiset in the open strip
with bounded local density; the Davenport-Heilbronn off-line zero satisfies
them too, which is checked in the direction it must hold.

Bulk scans use a float implementation of the same closed forms, cross-checked
against the mpmath one (:func:`float_vs_mpmath_defect`) -- that cross-check is
itself one of the controls.  Run
``.venv/bin/python hunts/frontier_math/gap_consistency.py`` from the repo root.
"""

from __future__ import annotations

import cmath
import math
import random
import sys
from dataclasses import dataclass
from fractions import Fraction
from functools import lru_cache
from pathlib import Path

from mpmath import mp, mpc, mpf

sys.path.insert(0, str(Path(__file__).resolve().parent))
from incidence_law import RAMP, Window  # noqa: E402

#: c_rho = 4||rho'||_inf + 4||rho''||_1 for the septic ramp of `incidence_law`.
#: rho'(x) = 140 x^3 (1-x)^3, so ||rho'||_inf = 140/64 = 35/16 at x = 1/2, and
#: rho'' changes sign only there, giving ||rho''||_1 = 2 rho'(1/2) = 35/8.
#: Hence c_rho = 4(35/16) + 4(35/8) = 105/4, exactly.  The paper's (2.13) then
#: gives ||(phi^2)''||_1 <= c_rho / w.
C_RHO = Fraction(105, 4)


# ---------------------------------------------------------------------------
# Float mirror of the closed forms (bulk scans), cross-checked against mpmath
# ---------------------------------------------------------------------------


def _f_cs_moments(c: complex, nmax: int):
    """Float mirror of `incidence_law._cs_moments`."""
    if abs(c) < 24:
        C, S = [], []
        for n in range(nmax + 1):
            sC = 0j
            sS = 0j
            term = 1 + 0j
            j = 0
            while True:
                sC += (-1) ** j * term / (n + 2 * j + 1)
                sS += (-1) ** j * term * c / ((2 * j + 1) * (n + 2 * j + 2))
                j += 1
                term *= c * c / ((2 * j - 1) * (2 * j))
                if abs(term) < 1e-18:
                    break
            C.append(sC)
            S.append(sS)
        return C, S
    sc, cc = cmath.sin(c), cmath.cos(c)
    C = [sc / c]
    S = [(1 - cc) / c]
    for n in range(1, nmax + 1):
        C.append(sc / c - n * S[n - 1] / c)
        S.append(-cc / c + n * C[n - 1] / c)
    return C, S


def _poly_sq_f(coeffs):
    out = [0.0] * (2 * len(coeffs) - 1)
    for i, ai in enumerate(coeffs):
        for j, aj in enumerate(coeffs):
            out[i + j] += ai * aj
    return out


_RAMP2_F = _poly_sq_f([float(c) for c in RAMP])


@lru_cache(maxsize=1 << 17)
def _phi2_hat_f(z: complex, L: float, w: float) -> complex:
    """Float Phi2(z) = int phi^2(u) cos(zu) du, same closed form as mpmath."""
    half, inner = L / 2, L / 2 - w
    if abs(z) < 1e-12:
        mid = 2 * inner
    else:
        mid = 2 * cmath.sin(z * inner) / z
    C, S = _f_cs_moments(z * w, len(_RAMP2_F) - 1)
    ch, sh = cmath.cos(z * half), cmath.sin(z * half)
    acc = sum(c * (ch * C[k] + sh * S[k]) for k, c in enumerate(_RAMP2_F) if c)
    return mid + 2 * w * acc


@dataclass(frozen=True)
class Kernel:
    """The level-2 view of the level-1 window: incidence as a gap kernel."""

    L: float = 8.0
    w: float = 1.0

    @property
    def window(self) -> Window:
        return Window(self.L, self.w)

    @property
    def aL(self) -> float:
        return _phi2_hat_f(0j, self.L, self.w).real

    # -- LAW G ------------------------------------------------------------

    def omega(self, gap: float) -> float:
        """Normalised on-line correlation of two zeros separated by ``gap``."""
        return _phi2_hat_f(complex(gap, 0.0), self.L, self.w).real / self.aL

    def cross(self, gap: float, depth: float) -> complex:
        """Normalised incidence Bhat(x, z) for z = x - gap - i*depth."""
        return _phi2_hat_f(complex(gap, depth), self.L, self.w) / self.aL

    def max_gap_for_correlation(self, level: float, hi: float = None, tol: float = 1e-12) -> float:
        """Largest gap whose correlation is still >= ``level`` (near g = 0).

        LAW G's one-gap marginal, inverted: a declared correlation ``level``
        buys a gap no larger than this.  ``omega`` decreases from 1 on the
        principal branch, so bisection is exact there.
        """
        hi = hi if hi is not None else self.L
        lo = 0.0
        while hi - lo > tol:
            mid = (lo + hi) / 2
            if self.omega(mid) >= level:
                lo = mid
            else:
                hi = mid
        return lo

    def two_gap_residual(self, g1: float, g2: float) -> float:
        """|omega(g1+g2) - omega(g1) omega(g2)|: words are not free.

        A marked two-gap word that declares its outer correlation
        independently (the natural "multiplicative" guess) is refuted by this
        residual; the true value is pinned to ``omega(g1 + g2)``.
        """
        return abs(self.omega(g1 + g2) - self.omega(g1) * self.omega(g2))

    # -- LAW H: the caps --------------------------------------------------

    def psi(self, r: float) -> float:
        """The paper's (2.17) majorant of |Phi2| on the real axis."""
        r = abs(r)
        if r == 0:
            return self.L
        return min(self.L, 2.0 / r, float(C_RHO) / (self.w * r * r))

    def psi_depth(self, r: float, depth: float) -> float:
        """Majorant of |Phi2(r + i y)|: near field by mass, tail by parts.

        |cos(zu)| <= cosh(yu) gives the flat bound ``aL * E(y)`` with
        ``E(y) = Phi2(iy)/aL``; two integrations by parts give
        ``||(phi^2)''||_1 cosh(yL/2) / r^2 <= (c_rho/w) cosh(yL/2) / r^2``.
        """
        flat = self.aL * self.depth_inflation(depth)
        r = abs(r)
        if r == 0:
            return flat
        tail = float(C_RHO) / self.w * math.cosh(depth * self.L / 2) / (r * r)
        return min(flat, tail)

    def depth_inflation(self, depth: float) -> float:
        """E(y) = Phi2(iy)/Phi2(0) = int phi^2 cosh(yu) du / int phi^2."""
        return _phi2_hat_f(complex(0.0, depth), self.L, self.w).real / self.aL

    def kappa(self, nu: float) -> float:
        """Cap on one on-line zero's cross mass against all the others.

        At most ``2 nu`` zeros lie within distance 1 (an interval of length
        2), each contributing ``omega^2 <= 1``; for ``k <= |r| < k+1`` there
        are at most ``2 nu``, each contributing ``(psi(k)/aL)^2``.
        """
        tail = sum((self.psi(k) / self.aL) ** 2 for k in range(1, 4000))
        return 2.0 * nu * (1.0 + tail)

    def kappa_cross(self, nu: float, depth: float) -> float:
        """Cap on one off-line member's incidence mass against all on-line
        zeros -- the anti-duplication law, independent of their number."""
        flat = self.depth_inflation(depth) ** 2
        tail = sum((self.psi_depth(k, depth) / self.aL) ** 2 for k in range(1, 4000))
        return 2.0 * nu * (flat + tail)


# ---------------------------------------------------------------------------
# Measurement against real configurations
# ---------------------------------------------------------------------------


def local_density(xs) -> int:
    """Max number of points in any unit interval (the unconditional ``nu``)."""
    xs = sorted(xs)
    best = 0
    j = 0
    for i, x in enumerate(xs):
        while xs[j] < x - 1.0:
            j += 1
        best = max(best, i - j + 1)
    return best


def online_cross_mass(kernel: Kernel, xs):
    """(max_i, total) of sum_{j != i} omega(x_i - x_j)^2 -- the R(P) content."""
    worst = 0.0
    total = 0.0
    for i, xi in enumerate(xs):
        row = 0.0
        for j, xj in enumerate(xs):
            if i != j:
                row += kernel.omega(xi - xj) ** 2
        worst = max(worst, row)
        total += row
    return worst, total


def cross_aggregate(kernel: Kernel, xs, gap0: float, depth: float):
    """(sum |Bhat|^2, signed sum 2 Re(Bhat^2)) of one off-line member."""
    mass = 0.0
    signed = 0.0
    for x in xs:
        b = kernel.cross(x - gap0, depth)
        mass += abs(b) ** 2
        signed += 2 * (b * b).real
    return mass, signed


def cap_scan(L=8.0, w=1.0, trials=40, seed=20260811, depth=0.3):
    """Random real configurations: neither cap may ever be exceeded.

    Also reports the slack, so a cap that is merely vacuous is visible.
    """
    rng = random.Random(seed)
    kernel = Kernel(L, w)
    worst_online = -math.inf
    worst_cross = -math.inf
    tightest_online = math.inf
    for _ in range(trials):
        n = rng.randint(12, 90)
        span = n / rng.uniform(0.6, 4.0)
        xs = sorted(rng.uniform(-span / 2, span / 2) for _ in range(n))
        nu = local_density(xs)
        row, _ = online_cross_mass(kernel, xs)
        cap = kernel.kappa(nu)
        worst_online = max(worst_online, row - cap)
        tightest_online = min(tightest_online, cap - row)
        mass, _ = cross_aggregate(kernel, xs, rng.uniform(-2, 2), depth)
        worst_cross = max(worst_cross, mass - kernel.kappa_cross(nu, depth))
    return {
        "worst_online_excess": worst_online,
        "worst_cross_excess": worst_cross,
        "tightest_online_slack": tightest_online,
    }


def collapse_saturation(L=8.0, w=1.0, n=50):
    """The family's R(P)/n = n-1 is attained only as the gaps go to zero."""
    kernel = Kernel(L, w)
    out = []
    for spacing in (0.0, 1e-3, 1e-2, 1e-1):
        xs = [j * spacing for j in range(n)]
        row, _ = online_cross_mass(kernel, xs)
        out.append((spacing, row, local_density(xs)))
    return out


def duplication_cheat(L=8.0, w=1.0, n_values=(10, 40, 160), depth=0.3, nu=3):
    """The level-2 kill control, run explicitly.

    The cheat spends ONE off-line pair independently in n overlapping cells,
    each at the level-1 per-cell floor ``-2 sigma^2(y)``.  Level 1 accepts it
    (every cell is inside its own envelope).  Level 2 rejects it, by a margin
    that grows linearly in n, because the aggregate cap does not.
    """
    kernel = Kernel(L, w)
    sigma_sq = float(kernel.window.sigma_sq(depth))
    cap = kernel.kappa_cross(nu, depth)
    #: Below this many cells the cheat is under BOTH floors, so level 2 adds
    #: nothing; the family's defeat needs n -> infinity, which is why it lands
    #: on the far side.  Stated rather than hidden: the improvement is
    #: asymptotic in n, not universal.
    crossover = cap / sigma_sq
    rows = []
    for n in n_values:
        declared = -2.0 * n * sigma_sq  # level-1-legal total: n cells at the floor
        floor = -2.0 * cap  # level-2 aggregate floor, independent of n
        rows.append(
            {
                "n": n,
                "declared_total": declared,
                "level1_permits": True,  # by construction: each cell is legal
                "level2_floor": floor,
                "rejected_by_level2": declared < floor,
                "margin": floor - declared,
                "crossover_n": crossover,
            }
        )
    return rows


# ---------------------------------------------------------------------------
# The robust exclusion and the residue
# ---------------------------------------------------------------------------


def robust_family_exclusion(m: int, nu: float, L=8.0, w=1.0):
    """The family needs n = 2m^2 + 2 on-line labels; reality allows kappa+1.

    Declaration-free: it compares the family's cross mass per on-line label
    (``n - 1``) with the cap any real configuration obeys, so it survives
    every perturbation of the family's declared numbers.
    """
    kernel = Kernel(L, w)
    n = 2 * m * m + 2
    cap = kernel.kappa(nu)
    return {
        "m": m,
        "n": n,
        "family_cross_mass_per_label": n - 1,
        "cap_kappa": cap,
        "max_labels_allowed": cap + 1,
        "excluded": (n - 1) > cap,
        "excess_factor": (n - 1) / cap,
    }


def theta_floor_level2(nu: float, L=8.0, w=1.0) -> float:
    """3 / kappa(nu): the residue this family shape can still obstruct."""
    return 3.0 / Kernel(L, w).kappa(nu)


def theta_floor_comparison(A0=1.0, lam=1.0, L_values=(8, 16, 24, 32)):
    """Level 1 (depth cap, ~exp(-L/2)) against level 2 (density cap, ~1/L).

    ``nu <= A_0 log T`` and ``L = lambda log(T/2pi)``, so ``nu`` is taken as
    ``A_0 * L / lam`` here; ``A_0`` is the absolute constant of the classical
    local-density bound (Titchmarsh Theorem 9.2), left as a parameter because
    this hunt does not pin its value.
    """
    rows = []
    for L in L_values:
        window = Window(L, max(1.0, L / 8))
        with mp.workdps(25):
            level1 = float(3 / (2 * window.sigma_sq(mpf("0.5")) + 1))
        nu = A0 * L / lam
        rows.append({"L": L, "nu": nu, "level1": level1, "level2": theta_floor_level2(nu, L, max(1.0, L / 8))})
    return rows


# ---------------------------------------------------------------------------
# Controls
# ---------------------------------------------------------------------------


def float_vs_mpmath_defect(L=8.0, w=1.0, dps=25):
    """The float mirror must agree with the mpmath closed form."""
    window = Window(L, w)
    kernel = Kernel(L, w)
    worst = 0.0
    with mp.workdps(dps):
        for g in (0.0, 0.37, 1.9, 7.3, 19.0):
            worst = max(worst, abs(kernel.omega(g) - float(mp.re(window.Phi2(g)) / window.aL)))
        for g, y in ((0.4, 0.3), (2.2, 0.45), (9.0, 0.1)):
            ref = complex(window.Phi2(mpc(g, y)) / window.aL)
            worst = max(worst, abs(kernel.cross(g, y) - ref))
    return worst


def majorant_control(L=8.0, w=1.0, samples=400):
    """psi and psi_depth must really majorise |Phi2|; report the worst slack."""
    kernel = Kernel(L, w)
    worst_real = math.inf
    worst_depth = math.inf
    for i in range(1, samples + 1):
        r = 0.05 * i
        worst_real = min(worst_real, kernel.psi(r) - abs(_phi2_hat_f(complex(r, 0), L, w)))
        for y in (0.1, 0.3, 0.49):
            worst_depth = min(
                worst_depth, kernel.psi_depth(r, y) - abs(_phi2_hat_f(complex(r, y), L, w))
            )
    return {"worst_real_slack": worst_real, "worst_depth_slack": worst_depth}


def decoy_cap(L=8.0, w=1.0, factor=0.25, trials=12, seed=5):
    """A cap planted too small by ``factor`` must be violated by real data.

    Without this the cap-scan could pass by being vacuous.
    """
    rng = random.Random(seed)
    kernel = Kernel(L, w)
    violations = 0
    for _ in range(trials):
        n = rng.randint(20, 60)
        span = n / rng.uniform(1.0, 3.0)
        xs = sorted(rng.uniform(-span / 2, span / 2) for _ in range(n))
        row, _ = online_cross_mass(kernel, xs)
        if row > factor * kernel.kappa(local_density(xs)):
            violations += 1
    return violations, trials


def dh_rival_two_gap(L=8.0, w=1.0):
    """LAW G at the Davenport-Heilbronn depth: the rival obeys it too."""
    from zeta.epstein import OFFLINE_ZERO_RE

    depth = float(OFFLINE_ZERO_RE[:22]) - 0.5
    kernel = Kernel(L, w)
    return {
        "depth": depth,
        "two_gap_residual": kernel.two_gap_residual(0.7, 1.3),
        "cross_cap_at_dh_depth": kernel.kappa_cross(3, depth),
        "depth_inflation": kernel.depth_inflation(depth),
    }


def audit():
    kernel = Kernel()
    print("= LAW G: correlations are gaps =")
    print(f"  omega(0) = {kernel.omega(0.0):.10f}")
    for level in (0.99, 0.9, 0.5):
        print(
            f"  correlation >= {level}: gap <= {kernel.max_gap_for_correlation(level):.6f}"
        )
    print(f"  two-gap residual at (0.7, 1.3) = {kernel.two_gap_residual(0.7, 1.3):.8f}")
    print("= LAW H: caps and their measurement =")
    print(f"  kappa(nu=1) = {kernel.kappa(1):.6f}   kappa(nu=3) = {kernel.kappa(3):.6f}")
    print(f"  kappa_cross(nu=3, y=0.3) = {kernel.kappa_cross(3, 0.3):.6f}")
    for key, val in cap_scan().items():
        print(f"  {key}: {val:+.6f}")
    print("= collapse saturation (the family's declaration needs zero gaps) =")
    for spacing, row, nu in collapse_saturation():
        print(f"  spacing {spacing:<6}: max_i R_i = {row:9.5f}  (n-1 = 49, nu = {nu})")
    print("= kill control: one pair duplicated across overlapping cells =")
    for row in duplication_cheat():
        print(
            f"  n={row['n']:4d}: declared {row['declared_total']:11.4f}  "
            f"level-2 floor {row['level2_floor']:9.4f}  "
            f"rejected={row['rejected_by_level2']}  margin {row['margin']:10.4f}"
        )
    print(f"  (crossover: level 2 bites for n > {duplication_cheat()[0]['crossover_n']:.1f})")
    print("= robust family exclusion (size bound is a function of nu) =")
    for nu in (3, 8):
        for m in (1, 2, 10):
            rec = robust_family_exclusion(m, nu=nu)
            print(
                f"  nu={nu}  m={m:3d}: n={rec['n']:5d}  needs "
                f"{rec['family_cross_mass_per_label']:5d} per label, cap "
                f"{rec['cap_kappa']:.4f}  excluded={rec['excluded']}  "
                f"excess x{rec['excess_factor']:.1f}"
            )
    print("= residue: theta floors, level 1 (depth) vs level 2 (density) =")
    for row in theta_floor_comparison():
        print(
            f"  L={row['L']:3d}  nu={row['nu']:5.1f}   level1 {row['level1']:.3e}   "
            f"level2 {row['level2']:.3e}   ratio {row['level2'] / row['level1']:.1f}x"
        )
    print("= controls =")
    print(f"  float-vs-mpmath defect: {float_vs_mpmath_defect():.3e}")
    for key, val in majorant_control().items():
        print(f"  {key}: {val:+.6f}")
    viol, trials = decoy_cap()
    print(f"  decoy (cap x0.25) violated in {viol}/{trials} configurations")
    print("= rival (Davenport-Heilbronn depth) =")
    for key, val in dh_rival_two_gap().items():
        print(f"  {key}: {val:.8f}")


if __name__ == "__main__":
    audit()
