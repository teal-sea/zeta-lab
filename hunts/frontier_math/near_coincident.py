"""The exactly-solvable limit of the EForm3 retention inequality: coincident points.

`zeta23ext/Zeta23Ext/EForm3/` closes the retention inequality

    (199/200) E[F] + n/200 + 4  <=  E[F + P],
    F(w) = sum_{j<n} exp(i x_j w),   P(w) = 2 cosh(y w) exp(i t w),

for **every** `n` under one hypothesis: consecutive offsets separated by
`d >= 4` (`Retention.retention_separated_of_le`), plus the unconditional case
`n <= 3` (`retention_le_three`).  Separation cannot close the general case,
because real zero gaps have no positive lower bound.  This module attacks the
opposite end, the case where the offsets *coincide*, where everything is in
closed form and nothing has to be estimated.

## The exact objects

With `g(u) = cos(sqrt2 u)` on `|u| <= 1/2` (zero outside), every quantity in
EForm3 is a value of one analytic function

    Q(z) = int g(u) cosh(z u) du
         = sinh((z + i sqrt2)/2)/(z + i sqrt2) + sinh((z - i sqrt2)/2)/(z - i sqrt2),

namely `Qre(y,s) + i Qim(y,s) = Q(y + i s)`, `A = Q(0)`, `phi_r(v) = Q(i v)`
(the Fourier transform of the window, EForm3's `Qre 0 v`) and
`Shq(y) = Q(2y)^2 - A^2`.  Writing `psi(y,s) = Qre^2 - Qim^2 = Re Q(y+is)^2`
and `D(y,s) = -psi(y,s)` (the *damage* of one offset), EForm3's gap identity
plus `energy_F` give the **exact** margin of the retention inequality,

    margin(x, y, t) = E[F+P] - (199/200) E[F] - n/200 - 4
                    = (4/A^2) * slack,
    slack(x, y, t)  = Shq(y)/2 - sum_j D(y, x_j - t)
                                + (1/400) sum_{j<k} phi_r(x_j - x_k)^2.   (*)

The third term is what EForm3 throws away when it uses `E[F] >= n`
(`energy_F_ge`).  It is the **repulsion**: two offsets at distance v relax the
damage budget by `phi_r(v)^2/400`, and a coincident pair by the maximum
`A^2/400 = 2.1101e-03`.  (*) is pure algebra from lemmas that are already in
the Lean tree, see `LEMMA_A` below, and every measurement here is an
evaluation of it.

## What the measurements say

* **Coincidence is locally the most dangerous placement, and globally cheap.**
  Splitting a coincident pair sitting on the damage peak *raises* the margin:
  `g = 0` is a strict local minimum with second-order coefficient
  `kappa2 = psi''(s*)/A^2 - L2/(100 A) = +4.3612e-02` per unit `g^2`, of which
  the repulsion supplies only 1.7% (`-7.7499e-04`); the rest is the curvature
  of the damage peak.  So the repulsion is not what protects the coincident
  case at second order, the smallness of `D` relative to `Shq/2` is.
* **The trade wins at every multiplicity.**  For `m` coincident offsets the
  damage is `m D` (linear) and the repulsion relief is `m(m-1) A^2/800`
  (quadratic), so the slack is a quadratic in `m` with positive leading
  coefficient.  Its discriminant is **negative for every `y <= 1.1264`**, i.e.
  there is no dangerous multiplicity at all in the range `y <= 1/2` that the
  problem allows: `m_0 = 1`.  The minimum over real `m` sits at
  `m* = 2.5835` with margin `0.12659` (`y = 1/2`).
* **The worst case is only half near-coincident.**  Over the prescribed grid
  (`x_j = j g`, `g` in [0,8], `m` in 2..8, worst placement) the worst
  configuration is `(g, m, y) = (0, 3, 1/2)`, total coincidence, inside the
  region the `d >= 4` hypothesis excludes, but it beats the worst member of
  the same grid with `g >= 4` by only 1.95%.  Over *all* configurations the
  worst is a hybrid: triples on the two innermost damage windows plus one
  offset per window elsewhere, which has `0` gaps *and* `2 pi` gaps.  So the
  separation hypothesis is not backwards, it does exclude the true worst
  case, but what it excludes is barely worse than what it keeps.
* **The general case does not need the separation hypothesis.**  Because the
  damage lives in windows of width `<= 0.98601` recurring at spacing `2 pi`,
  the configuration problem decouples window by window, and the resulting
  bound holds for every finite configuration and every `n`: at `y = 1/2`,

      net damage  =  sum_j D_j - (1/400) sum_{j<k} phi_r^2
                  <= 1.95721e-02  <  Shq/2 = 3.37542e-02,
      slack >= 1.41821e-02   (margin >= 6.72091e-02),

  against `2.00321e-02` for the `2 pi`-separated configurations.  In the
  bookkeeping `FAR-FIELD-EXCHANGE.md` uses, the net damage reaches 57.98% of
  the budget with no separation hypothesis at all, against the 40.6% that
  exchange records under separation: a safety factor of **1.7246x** instead
  of 2.4599x.  The separation hypothesis therefore buys a factor 1.43, and
  the inequality does not need it.

## What this hands to a prover

`LEMMA_A`, `LEMMA_B` and `LEMMA_C` below state the three steps as text, with
the constants each one needs.  The load-bearing arithmetic fact is that the
cluster lemma (`LEMMA_B`) closes **with the constants EForm3 already has** as
long as the cluster diameter is at most `rho* = 1.7208`
(`cluster_diameter_threshold`), and would reach `rho* = 4.4859`, past the
separation threshold 4, if the uniform damage cap `383/10000` were sharpened
to `2.19041e-02` (`109/5000` would do; the true maximum is `1.75857e-02`).

Nothing here is a result and nothing here is evidence about RH; this is a
probe (`hunts/README.md`).  Vocabulary is the hunt's: *measured*, *observed*,
*consistent with*.
"""

from __future__ import annotations

import math
from collections import Counter
from dataclasses import dataclass
from functools import lru_cache
from typing import Iterable, Sequence

import numpy as np
from mpmath import mp
from scipy.integrate import quad as _quad
from scipy.optimize import brentq, minimize, minimize_scalar

__all__ = [
    "SQRT2", "A_CONST", "TWO_PI",
    "EFORM3_SEPARATION", "EFORM3_UNIFORM_DAMAGE_CAP", "EFORM3_SHQ_HALF_COEFF",
    "EFORM3_SEPARATED_DAMAGE_CAP", "EFORM3_NEAR_FIELD_RADIUS",
    "LEMMA_A", "LEMMA_B", "LEMMA_C", "RECORD",
    "q_transform", "qre", "qim", "psi", "damage", "phi_r", "q_laplace", "shq",
    "c2", "second_moment",
    "slack_offsets", "slack", "margin", "retention_margin_direct",
    "phi_r_zeros", "damage_windows", "no_damage_radius", "damage_tail_bound",
    "damage_total_one_side", "Window",
    "coincident_slack", "coincident_quadratic", "coincidence_safe_multiplicity",
    "critical_depth", "cluster_diameter_threshold", "damage_cap_for_diameter",
    "peak_damage_coefficient",
    "pair_slack", "second_order_coefficient",
    "ap_worst", "ap_scan", "depth_scan", "marginal_ladder", "greedy_worst_config",
    "worst_over_all_configurations", "unconditional_lower_bound",
    "separated_worst", "separated_consistency",
    "report", "main",
]

# --------------------------------------------------------------------------
# constants
# --------------------------------------------------------------------------

SQRT2 = math.sqrt(2.0)
TWO_PI = 2.0 * math.pi

#: `A = sqrt2 sin(1/sqrt2) = int g`, EForm3's `Aconst`.
A_CONST = 0.9187253698655684

#: the separation EForm3 assumes (`retention_separated_of_le`, `hd : 4 <= d`).
EFORM3_SEPARATION = 4.0
#: `uniform_damage`: `Qim^2 - Qre^2 <= y^2 * 383/10000` for every offset.
EFORM3_UNIFORM_DAMAGE_CAP = 383 / 10000
#: `Shq_half_lower`: `Shq y / 2 >= (187/1440) y^2`.
EFORM3_SHQ_HALF_COEFF = 187 / 1440
#: `separated_damage`: total damage `<= (1228/10000) y^2` when gaps are `>= 4`.
EFORM3_SEPARATED_DAMAGE_CAP = 1228 / 10000
#: `no_damage`: `Qim^2 <= Qre^2` for `|s| <= 28/5`.
EFORM3_NEAR_FIELD_RADIUS = 28 / 5

LEMMA_A = """\
LEMMA A (repulsion-relaxed damage criterion; exact, no estimates).
For every n, x, y, t:  if
    sum_j (Qim y (x j - t)^2 - Qre y (x j - t)^2)
      <= Shq y / 2 + (1/400) * sum_{j<k} Qre 0 (x j - x k)^2
then  (199/200) * Eng (Fsum n x) + n/200 + 4 <= Eng (Fsum n x + Pfun y t).
Route: `retention_gap` gives E[F+P] - E[F] - 4 exactly; `energy_F` gives
E[F] - n = (1/A^2) sum_{j != k} Qre 0 (x j - x k)^2.  Adding the second to
(1/200) of the first is the whole proof, so this is `retention_of_damage`
with `energy_F_ge` replaced by the identity it discards.  Strictly stronger:
the hypothesis of `retention_of_damage` implies this one.
"""

LEMMA_B = """\
LEMMA B (cluster lemma; no separation hypothesis, every n).
Let 0 <= y <= 1/2 and let all n offsets lie in one interval of length rho.
Then every pair relieves at least phi_r(rho)^2/400, and Lemma A's hypothesis
follows from
    n * Dcap * y^2  <=  Sco * y^2 + (n(n-1)/2) * phi_r(rho)^2/400
with Dcap the uniform damage cap (`uniform_damage`, 383/10000) and Sco the
gain coefficient (`Shq_half_lower`, 187/1440).  Since the relief does not
carry a y^2, the binding depth is y = 1/2; writing a = Dcap/4, S = Sco/4 and
c = phi_r(rho)^2/800 the requirement is the single quadratic condition
    c n^2 - (a + c) n + S >= 0   for every n >= 1,
which holds at every n as soon as   (a + c)^2 <= 4 c S.
Besides Lemma A this needs only `phi_r(v) >= phi_r(rho)` for `|v| <= rho`
(`Qre_zero_near` in `Estimates.lean` is the same shape of lemma, with the
weaker constant 0.1483 at 28/5).
Measured thresholds: rho* = 1.7208 with EForm3's current Dcap = 383/10000;
rho* = 4.4859 with the sharp cap 1.75857e-02; rho* = 4 costs a cap of
2.19041e-02, for which the rational 109/5000 = 0.0218 leaves 1% to spare.
"""

LEMMA_C = """\
LEMMA C (window decomposition; the unconditional statement the measurements
support).  For 0 <= y <= 1/2 the damage D(y,.) is positive only on windows
W_k around the zeros of phi_r, with
    (i)   W_k contained in |s| >= 6.0653  (EForm3's `no_damage` gives 28/5),
    (ii)  |W_k| <= w_max = 0.9860008 and the W_k are 2 pi apart,
    (iii) sup_{W_k} D = D_k with sum_k D_k <= T = 6.8610e-03 at y = 1/2,
          the tail past any point by `Qim_far_sq` (D <= y^2 Wt(s^2-2)).
Offsets outside every window have D <= 0; two offsets inside the same window
are at most w_max apart, so each such pair relieves at least gamma^2/400 with
gamma = phi_r(w_max) >= 0.88452.  The problem therefore decouples window by
window, and for EVERY finite configuration, every n, at y = 1/2:
    sum_j D_j - (1/400) sum_{j<k} phi_r(x_j - x_k)^2
      <= sum_k max_{n>=0} [ n D_k - (gamma^2/800) n(n-1) ]  =  1.95721e-02
which is below Shq/2 = 3.37542e-02, so Lemma A applies.  No separation
hypothesis appears anywhere.  The maximising n is 3 on the innermost window
of each side and 1 on every other one; smaller y only helps, because the
relief carries no y^2 and the windows narrow.
"""


# --------------------------------------------------------------------------
# closed forms
# --------------------------------------------------------------------------


def q_transform(y, s):
    """`Q(y + i s) = int g(u) cosh((y + i s) u) du`, in closed form.

    Vectorised in `s`.  `Qre = Re Q`, `Qim = Im Q` are EForm3's `Qre y s`
    and `Qim y s`; the closed form is the one `ClosedForm.lean` derives.
    """
    z = np.asarray(y, dtype=float) + 1j * np.asarray(s, dtype=float)
    zp = z + 1j * SQRT2
    zm = z - 1j * SQRT2
    return np.sinh(zp / 2) / zp + np.sinh(zm / 2) / zm


def qre(y, s):
    """`Qre y s = int g(u) cosh(y u) cos(s u) du`."""
    return np.real(q_transform(y, s))


def qim(y, s):
    """`Qim y s = int g(u) sinh(y u) sin(s u) du`."""
    return np.imag(q_transform(y, s))


def psi(y, s):
    """`psi = Qre^2 - Qim^2 = Re Q(y+is)^2`, the per-offset cross term."""
    q = q_transform(y, s)
    return np.real(q * q)


def damage(y, s):
    """`D(y,s) = Qim^2 - Qre^2`, positive exactly where an offset hurts."""
    return -psi(y, s)


def phi_r(v):
    """`phi_r(v) = Qre 0 v = ghat(v)`, the window's Fourier transform.

    This is the repulsion kernel: `phi_r(0) = A`, and EForm3's `energy_F`
    reads `E[F] = (1/A^2) sum_{j,k} phi_r(x_j - x_k)^2`.
    """
    return np.real(q_transform(0.0, v))


def q_laplace(a):
    """`Qre a 0 = int g(u) cosh(a u) du`, the *other* transform.

    Naming trap: `Shq y = q_laplace(2y)^2 - A^2` uses this one (a real
    argument), while the repulsion uses `phi_r` (an imaginary argument).
    They agree only at 0.
    """
    return np.real(q_transform(a, 0.0))


def shq(y):
    """`Shq y = Qre (2y) 0 ^2 - A^2`, the gain the pulse brings."""
    return float(q_laplace(2.0 * float(y)) ** 2 - A_CONST**2)


def c2(w):
    """The autocorrelation `c2 w = int g(u) g(u+w) du`, closed form.

    `c2 w = (1-|w|) cos(sqrt2 |w|)/2 + sin(sqrt2 (1-|w|))/(2 sqrt2)` on
    `|w| <= 1`, zero outside; `c2(0) = int g^2`, `int c2 = A^2`.
    """
    a = abs(float(w))
    if a >= 1.0:
        return 0.0
    return (1 - a) * math.cos(SQRT2 * a) / 2 + math.sin(SQRT2 * (1 - a)) / (2 * SQRT2)


def second_moment():
    """`L2 = int u^2 g(u) du = -phi_r''(0)`; EForm3's sharp slack constant.

    `int u^2 cos(k u) du` over `|u| <= 1/2` is
    `2 [ sin(k/2) (1/(4k) - 2/k^3) + cos(k/2)/k^2 ]` with `k = sqrt2`;
    `FAR-FIELD-EXCHANGE.md` records the value as `L2 = 0.0712006`, the
    constant that would replace `1/12` in the slack lemma.
    """
    k = SQRT2
    return float(
        2 * (math.sin(k / 2) * (1 / (4 * k) - 2 / k**3) + math.cos(k / 2) / k**2)
    )


def _second_moment_quad() -> float:
    """`L2` again, by quadrature, the closed form above is checked against it."""
    return float(_quad(lambda u: math.cos(SQRT2 * u) * u * u, -0.5, 0.5)[0])


# --------------------------------------------------------------------------
# the margin, in closed form and by direct quadrature
# --------------------------------------------------------------------------


def slack_offsets(offsets: Sequence[float], y: float) -> float:
    """The slack (*) as a function of the offsets `s_j = x_j - t` alone.

    `slack > 0` is exactly the retention inequality; `margin = (4/A^2) slack`.
    Translation invariance is why only the offsets appear.
    """
    s = np.asarray(offsets, dtype=float)
    if s.size == 0:
        return shq(y) / 2
    diff = s[:, None] - s[None, :]
    iu = np.triu_indices(s.size, 1)
    repulsion = float((phi_r(diff[iu]) ** 2).sum()) / 400.0
    return shq(y) / 2 - float(np.sum(damage(y, s))) + repulsion


def slack(xs: Sequence[float], y: float, t: float = 0.0) -> float:
    """The slack of configuration `xs` against a pulse at `t`, depth `y`."""
    return slack_offsets(np.asarray(xs, dtype=float) - float(t), y)


def margin(xs: Sequence[float], y: float, t: float = 0.0) -> float:
    """`E[F+P] - (199/200) E[F] - n/200 - 4`, in closed form."""
    return (4.0 / A_CONST**2) * slack(xs, y, t)


def _c2_mp(w):
    a = abs(w)
    if a >= 1:
        return mp.mpf(0)
    k = mp.sqrt(2)
    return (1 - a) * mp.cos(k * a) / 2 + mp.sin(k * (1 - a)) / (2 * k)


def retention_margin_direct(xs: Sequence[float], y: float, t: float = 0.0, dps: int = 30):
    """The margin again, by quadrature of the energy functional itself.

    Evaluates `Eng G = (1/A^2) int_{-1}^{1} c2(w) |G(w)|^2 dw` on `F + P` and
    on `F` with no algebra in between, so it is an independent evaluation of
    the same number the closed form produces.  Slow; this is the control.
    """
    with mp.workdps(dps + 10):
        yy, tt = mp.mpf(float(y)), mp.mpf(float(t))
        pts = [mp.mpf(float(x)) for x in xs]
        aconst = mp.sqrt(2) * mp.sin(1 / mp.sqrt(2))

        def eng(field):
            integ = mp.quad(lambda w: _c2_mp(w) * abs(field(w)) ** 2, [-1, 0, 1])
            return integ / aconst**2

        def fsum(w):
            return mp.fsum([mp.e ** (1j * (x * w)) for x in pts])

        def pulse(w):
            return 2 * mp.cosh(yy * w) * mp.e ** (1j * (tt * w))

        full = eng(lambda w: fsum(w) + pulse(w))
        bare = eng(fsum)
        return +(full - (mp.mpf(199) / 200) * bare - mp.mpf(len(pts)) / 200 - 4)


# --------------------------------------------------------------------------
# the geometry of the damage
# --------------------------------------------------------------------------


@dataclass(frozen=True)
class Window:
    """One damage window: `D(y, .) > 0` exactly on `(lo, hi)`."""

    index: int
    peak: float
    damage: float
    lo: float
    hi: float

    @property
    def width(self) -> float:
        return self.hi - self.lo


@lru_cache(maxsize=8)
def phi_r_zeros(count: int) -> tuple:
    """The positive zeros of `phi_r`, one per damage window, spacing `~2 pi`."""
    out = []
    guess = 6.6
    for _ in range(count):
        z = brentq(lambda v: float(phi_r(v)), guess - 0.6, guess + 0.6, xtol=1e-14)
        out.append(float(z))
        guess = z + TWO_PI
    return tuple(out)


def _damage_peak(y: float, zero: float) -> tuple:
    """The maximum of `D(y, .)` in the window around one zero of `phi_r`."""
    grid = np.linspace(zero - math.pi + 0.05, zero + math.pi - 0.05, 1201)
    vals = damage(y, grid)
    i = int(vals.argmax())
    i = min(max(i, 1), grid.size - 2)
    res = minimize_scalar(
        lambda s: -float(damage(y, s)),
        bracket=(float(grid[i - 1]), float(grid[i]), float(grid[i + 1])),
        options={"xtol": 1e-14},
    )
    return float(res.x), -float(res.fun)


@lru_cache(maxsize=32)
def damage_windows(y: float, count: int = 40) -> tuple:
    """The first `count` damage windows on the positive side, as `Window`s.

    `D(y, .)` is even, so the negative side is the mirror image.  Each window
    brackets one zero of `phi_r`: that is where `Qre` is small enough for
    `Qim` (which is `O(y)`) to overtake it.  For `y` past about 1 the windows
    widen until they meet, and the edge search says so rather than guessing.
    """
    out = []
    for k, z in enumerate(phi_r_zeros(count)):
        peak, dpk = _damage_peak(y, z)
        lo = _edge(y, peak, -1.0, math.pi)
        hi = _edge(y, peak, +1.0, math.pi)
        out.append(Window(k, peak, dpk, lo, hi))
    return tuple(out)


def _edge(y: float, peak: float, direction: float, reach: float) -> float:
    """Where `D(y, .)` changes sign, walking `direction` from the peak."""
    far = peak + direction * reach
    if float(damage(y, far)) > 0:
        raise ValueError(
            f"damage window around {peak:.4f} is not confined at y={y}: "
            "the windows have merged, so the decomposition does not apply"
        )
    lo, hi = (far, peak) if direction < 0 else (peak, far)
    return float(brentq(lambda s: float(damage(y, s)), lo, hi, xtol=1e-14))


def no_damage_radius(y: float) -> float:
    """The largest `R` with `Qim^2 <= Qre^2` on `|s| <= R`, the true `no_damage`.

    EForm3's `no_damage` establishes the statement for `28/5 = 5.6`; the truth
    at `y = 1/2` is `6.0653`, the left edge of the innermost damage window.
    """
    return float(damage_windows(float(y), 1)[0].lo)


def _wt(w: float) -> float:
    """EForm3's far-field majorant `Wt` (FarField.lean), `Qim^2 <= y^2 Wt(s^2-2)`."""
    return (5 / 8) / w + (611 / 50) / w**2 + (6711 / 100) / w**3 + (2583 / 25) / w**4


def damage_tail_bound(y: float, s_from: float) -> float:
    """Bound for `sum_{windows beyond s_from} D_k`, from `Qim_far_sq`.

    Windows are `2 pi` apart and `Wt` is decreasing, so the sum of the peaks
    past `s_from` is at most `(1/2 pi) int_{s_from}^inf y^2 Wt(t^2-2) dt`.
    """
    val = _quad(lambda t: _wt(t * t - 2), float(s_from), np.inf)[0]
    return float(y) ** 2 * val / TWO_PI


def damage_total_one_side(y: float, count: int = 300) -> dict:
    """`T = sum_k D_k` over one side, with the tail past `count` windows bounded."""
    wins = damage_windows(float(y), count)
    head = float(sum(w.damage for w in wins))
    tail = damage_tail_bound(y, wins[-1].peak)
    return {
        "windows": count,
        "head": head,
        "tail_bound": tail,
        "total_upper": head + tail,
        "last_peak": wins[-1].peak,
        "max_width": max(w.width for w in wins),
    }


# --------------------------------------------------------------------------
# 1-2. coincident points, and the cluster limit
# --------------------------------------------------------------------------


@lru_cache(maxsize=256)
def _worst_offset(y: float) -> float:
    """The offset that damages most: the peak of the innermost window."""
    return _damage_peak(float(y), phi_r_zeros(1)[0])[0]


def coincident_slack(m: int, y: float, s: float | None = None) -> float:
    """Slack of `m` offsets all at `s` (the innermost damage peak by default).

    Exactly `Shq/2 - m D(y,s) + m(m-1) A^2/800`: damage linear in `m`,
    repulsion quadratic.
    """
    ss = _worst_offset(y) if s is None else float(s)
    return (
        shq(y) / 2
        - m * float(damage(y, ss))
        + m * (m - 1) * A_CONST**2 / 800.0
    )


def coincident_quadratic(y: float) -> dict:
    """The quadratic `f(m) = c m^2 - (D + c) m + Shq/2` for coincident offsets.

    `c = A^2/800` is the relief a coincident pair contributes (half of
    `A^2/400`, because `m(m-1)/2` pairs each give `A^2/400`).  A negative
    discriminant means *no* multiplicity is dangerous.
    """
    ss = _worst_offset(y)
    dmax = float(damage(y, ss))
    c = A_CONST**2 / 800.0
    s_half = shq(y) / 2
    disc = (dmax + c) ** 2 - 4 * c * s_half
    m_star = (dmax + c) / (2 * c)
    f_star = s_half - (dmax + c) ** 2 / (4 * c)
    return {
        "y": float(y),
        "peak_offset": ss,
        "peak_damage": dmax,
        "relief_per_pair": A_CONST**2 / 400.0,
        "quadratic_coeff": c,
        "shq_half": s_half,
        "discriminant": float(disc),
        "m_star": float(m_star),
        "slack_at_m_star": float(f_star),
        "margin_at_m_star": float((4 / A_CONST**2) * f_star),
        "safe_for_every_m": bool(disc < 0),
    }


def coincidence_safe_multiplicity(y: float, m_max: int = 4096) -> int:
    """The smallest `m_0` with `coincident_slack(m, y) > 0` for all `m >= m_0`.

    Returns 1 when the trade wins at every multiplicity, which is what is
    measured for every `y <= 1.1264`; past that depth the quadratic dips below
    zero and this returns the far end of the dangerous band (at `y = 1.5` the
    band is `m` in 8..47, so `m_0 = 48`).
    """
    quad_ = coincident_quadratic(y)
    if quad_["discriminant"] < 0:
        return 1
    c = quad_["quadratic_coeff"]
    b = quad_["peak_damage"] + c
    root = (b + math.sqrt(quad_["discriminant"])) / (2 * c)
    upper = min(m_max, int(math.ceil(root)) + 1)
    dangerous = [m for m in range(1, upper + 1) if coincident_slack(m, y) <= 0]
    return max(dangerous) + 1 if dangerous else 1


def critical_depth(lo: float = 0.6, hi: float = 2.0) -> float:
    """The depth `y` at which the coincident quadratic's discriminant vanishes.

    Below it every multiplicity is safe; the problem only ever asks for
    `y <= 1/2`, so the measured `1.1264` is a factor 2.25 of headroom.
    """
    return float(brentq(lambda yy: coincident_quadratic(yy)["discriminant"], lo, hi, xtol=1e-13))


def cluster_diameter_threshold(
    damage_cap: float = EFORM3_UNIFORM_DAMAGE_CAP,
    shq_coeff: float = EFORM3_SHQ_HALF_COEFF,
    y_max: float = 0.5,
) -> dict:
    """Largest cluster diameter `rho` for which LEMMA B closes at every `n`.

    With every offset inside an interval of length `rho`, each pair relieves
    at least `phi_r(rho)^2/400`; the requirement is that the quadratic in `n`
    have no real root, which pins `phi_r(rho)` from below.  Worst `y` is
    `y_max`, because the relief does not scale with `y^2` while the damage
    and the gain both do.
    """
    a = damage_cap * y_max**2
    s_scaled = shq_coeff * y_max**2
    if s_scaled <= a:
        return {"feasible": False, "rho": 0.0, "phi_needed": float("inf")}
    root = math.sqrt(s_scaled) - math.sqrt(s_scaled - a)
    c = root**2                      # = phi_r(rho)^2/800
    needed = math.sqrt(800 * c)
    if needed >= A_CONST:
        return {"feasible": False, "rho": 0.0, "phi_needed": needed}
    rho = brentq(lambda r: float(phi_r(r)) - needed, 0.0, 6.0, xtol=1e-14)
    return {
        "feasible": True,
        "damage_cap": damage_cap,
        "shq_coeff": shq_coeff,
        "rho": float(rho),
        "phi_needed": float(needed),
        "relief_per_pair_needed": float(c * 2),
    }


def damage_cap_for_diameter(rho: float, shq_coeff: float = EFORM3_SHQ_HALF_COEFF,
                            y_max: float = 0.5) -> float:
    """The uniform damage cap LEMMA B needs at cluster diameter `rho`.

    Inverse of `cluster_diameter_threshold`: the cap `Dcap` (as a coefficient
    of `y^2`) for which the cluster quadratic has no real root.
    """
    c = float(phi_r(rho)) ** 2 / 800.0
    s_scaled = shq_coeff * y_max**2
    return float((2 * math.sqrt(c * s_scaled) - c) / y_max**2)


# --------------------------------------------------------------------------
# 1b. the perturbation g -> the second-order expansion
# --------------------------------------------------------------------------


def pair_slack(center: float, gap: float, y: float, anchored: bool = False) -> float:
    """Slack of two offsets a distance `gap` apart.

    `anchored=False` splits them symmetrically about `center` (the adversary's
    centroid stays put); `anchored=True` keeps one at `center` and moves the
    other.  Both are stationary at `gap = 0` when `center` is a damage peak.
    """
    if anchored:
        offs = (center, center + gap)
    else:
        offs = (center - gap / 2, center + gap / 2)
    return slack_offsets(offs, y)


def second_order_coefficient(y: float) -> dict:
    """The `g^2` coefficient of the margin of a split pair at the damage peak.

    Symmetric split: `margin(g) = margin(0) + kappa2 g^2 + O(g^4)` with

        kappa2 = psi''(s*)/A^2 - L2/(100 A),

    the first term the curvature of the damage peak (which the split escapes)
    and the second the repulsion the split gives up.  `kappa2 > 0` says
    `g = 0` is a local *minimum* of the margin: coincidence is locally the
    most dangerous placement.
    """
    ss = _worst_offset(y)
    psi2 = float(_diff2(lambda s: float(psi(y, s)), ss))
    l2 = second_moment()
    damage_part = psi2 / A_CONST**2
    repulsion_part = -l2 / (100 * A_CONST)
    anchored = 2 * psi2 / A_CONST**2 + repulsion_part
    return {
        "y": float(y),
        "peak_offset": ss,
        "psi_second_derivative": psi2,
        "second_moment": l2,
        "damage_part": damage_part,
        "repulsion_part": repulsion_part,
        "kappa2": damage_part + repulsion_part,
        "kappa2_anchored": anchored,
        "repulsion_share": abs(repulsion_part) / (damage_part + abs(repulsion_part)),
        "coincidence_is_local_minimum": bool(damage_part + repulsion_part > 0),
    }


def _diff2(f, x: float, h: float = 1e-4) -> float:
    """Second derivative by a five-point stencil (the closed forms are smooth)."""
    return (
        -f(x + 2 * h) + 16 * f(x + h) - 30 * f(x) + 16 * f(x - h) - f(x - 2 * h)
    ) / (12 * h * h)


# --------------------------------------------------------------------------
# 3. the scans
# --------------------------------------------------------------------------

_TABLE_STEP = 0.01
#: how far past the progression's own span the pulse centre is searched;
#: the damage past `s = 70` is below `2e-05` per window at `y = 1/2`.
_TABLE_MARGIN = 80.0


@lru_cache(maxsize=64)
def _damage_table(y: float, step: float, half_width: float) -> tuple:
    grid = np.arange(-half_width, half_width + step / 2, step)
    return grid, damage(y, grid)


def _ap_relief(gap: float, m: int) -> float:
    d = np.arange(1, m)
    return float(((m - d) * phi_r(d * gap) ** 2).sum()) / 400.0


def ap_worst(gap: float, m: int, y: float, refine: bool = True,
             step: float = _TABLE_STEP) -> dict:
    """Worst placement of the arithmetic progression `x_j = j*gap`, `m` offsets.

    The pulse centre `t` is the adversary's free parameter (the relief does
    not depend on it), so this maximises the total damage over `t` on a
    tabulated grid of step `step` and then refines continuously.  The value
    returned is always an exact evaluation of (*), never a table lookup.
    """
    gap = float(gap)
    half_width = 10.0 * math.ceil(((m - 1) * gap + _TABLE_MARGIN) / 10.0)
    grid, tab = _damage_table(float(y), step, half_width)
    step_index = int(round(gap / step))
    span = (m - 1) * step_index
    total = np.zeros(grid.size - span)
    for j in range(m):
        total += tab[j * step_index: j * step_index + (grid.size - span)]
    i = int(total.argmax())
    t0 = -float(grid[i])
    xs = np.arange(m) * float(gap)

    def objective(t: float) -> float:
        return shq(y) / 2 - float(np.sum(damage(y, xs - t))) + _ap_relief(gap, m)

    best_t, best = t0, objective(t0)
    if refine:
        res = minimize_scalar(
            objective,
            bounds=(t0 - 2 * step, t0 + 2 * step),
            method="bounded",
            options={"xatol": 1e-13},
        )
        if float(res.fun) < best:
            best_t, best = float(res.x), float(res.fun)
    relief = _ap_relief(gap, m)
    return {
        "gap": float(gap),
        "m": int(m),
        "y": float(y),
        "centre": best_t,
        "slack": float(best),
        "margin": float((4 / A_CONST**2) * best),
        "relief": relief,
        "damage_total": float(shq(y) / 2 - best + relief),
        **_ratio_fields(float(best), y),
    }


def _ratio_fields(slack_value: float, y: float) -> dict:
    """The exchange's bookkeeping: net damage as a fraction of `Shq/2`.

    `FAR-FIELD-EXCHANGE.md` reports the separated worst case as "40.6% of
    budget -> margin 2.46x".  With the repulsion in play the comparable
    quantity is the *net* damage `sum_j D_j - (1/400) sum_{j<k} phi_r^2`,
    which is exactly `Shq/2 - slack`; the two agree whenever the repulsion
    vanishes, which is the case the exchange measured.
    """
    s_half = shq(y) / 2
    net = s_half - slack_value
    return {
        "net_damage": float(net),
        "ratio": float(net / s_half),
        "safety_factor": float(s_half / net) if net > 0 else float("inf"),
    }


def ap_scan(
    y: float = 0.5,
    gaps: Iterable[float] | None = None,
    multiplicities: Iterable[int] = range(2, 9),
    joint_refine: bool = True,
    step: float = _TABLE_STEP,
) -> dict:
    """The prescribed scan: `g` in [0,8], `m` in 2..8, worst placement each.

    Deterministic: the gap grid is fixed, the placement grid is fixed, and
    the refinement is a local descent started from the grid winner.  Also
    reports the worst member with `gap >= 4`, i.e. the worst configuration of
    this family that EForm3's separation hypothesis still admits.
    """
    if gaps is None:
        gaps = np.round(np.arange(0.0, 8.0 + 1e-9, 0.02), 3)
    gaps = [float(g) for g in gaps]
    records, separated_records = {}, {}
    for m in multiplicities:
        rows = [ap_worst(g, m, y, refine=False, step=step) for g in gaps]
        rows.sort(key=lambda r: r["slack"])
        best = ap_worst(rows[0]["gap"], m, y, refine=True, step=step)
        if joint_refine and best["gap"] > step:
            best = _ap_joint_refine(best, m, y, step)
        records[int(m)] = best
        above = [r for r in rows if r["gap"] >= EFORM3_SEPARATION]
        if above:
            sep = ap_worst(above[0]["gap"], m, y, refine=True, step=step)
            if joint_refine:
                sep = _ap_joint_refine(sep, m, y, step)
            separated_records[int(m)] = sep
    worst = min(records.values(), key=lambda r: r["slack"])
    separated = min(separated_records.values(), key=lambda r: r["slack"])
    return {
        "y": float(y),
        "records": records,
        "worst": worst,
        "separated_records": separated_records,
        "worst_with_gap_at_least_4": separated,
        "excluded_region_is_worse": bool(worst["slack"] < separated["slack"]),
        "excluded_penalty": float(separated["slack"] / worst["slack"] - 1.0),
    }


def depth_scan(
    depths: Iterable[float] = (0.1, 0.2, 0.3, 0.4, 0.5),
    multiplicities: Iterable[int] = (2, 3, 8),
    gap_step: float = 0.02,
) -> dict:
    """Where in `y` the prescribed family is worst, in the scale-free ratio.

    The slack itself is not the right thing to minimise over `y`: it tends to
    the (nonnegative) repulsion as `y -> 0`, so its infimum in `y` is a
    degenerate zero at infinite separation.  The ratio `net damage / (Shq/2)`
    is the scale-free one, and it is measured to increase with `y`, so the
    binding depth is the top of the allowed range, `y = 1/2`.
    """
    gaps = list(np.round(np.arange(0.0, 8.0 + 1e-9, gap_step), 3))
    rows = []
    for y in depths:
        best = None
        for m in multiplicities:
            for g in gaps:
                rec = ap_worst(g, m, y, refine=False)
                if best is None or rec["ratio"] > best["ratio"]:
                    best = rec
        rows.append(best)
    return {
        "rows": rows,
        "worst": max(rows, key=lambda r: r["ratio"]),
        "ratio_increases_with_depth": bool(
            all(a["ratio"] < b["ratio"] for a, b in zip(rows, rows[1:]))
        ),
    }


def _ap_joint_refine(seed: dict, m: int, y: float, step: float = _TABLE_STEP) -> dict:
    def objective(p):
        g, t = float(p[0]), float(p[1])
        if g < 0:
            return 1e6
        return shq(y) / 2 - float(np.sum(damage(y, np.arange(m) * g - t))) + _ap_relief(g, m)

    res = minimize(
        objective,
        [seed["gap"], seed["centre"]],
        method="Nelder-Mead",
        options={"xatol": 1e-12, "fatol": 1e-16, "maxiter": 5000},
    )
    if float(res.fun) < seed["slack"]:
        return ap_worst(float(res.x[0]), m, y, refine=True, step=step)
    return seed


# --------------------------------------------------------------------------
# the free configuration problem: window decomposition
# --------------------------------------------------------------------------


def marginal_ladder(y: float, count: int = 300, relief_per_pair: float | None = None,
                    level_max: int = 8) -> list:
    """Every negative marginal `-D_k + c (j-1)` of adding a `j`-th offset to window `k`.

    The configuration problem decouples: the cost of the `j`-th offset in a
    window depends only on that window, so the worst configuration of size `m`
    takes the `m` most negative marginals.  Sorted ascending; each entry is
    `(marginal, signed peak, level, window index)`.
    """
    if relief_per_pair is None:
        relief_per_pair = A_CONST**2 / 400.0
    out = []
    for w in damage_windows(float(y), count):
        for level in range(1, level_max + 1):
            marginal = -w.damage + relief_per_pair * (level - 1)
            if marginal >= 0:
                break
            for sign in (1, -1):
                out.append((float(marginal), sign * w.peak, level, w.index))
    out.sort(key=lambda r: r[0])
    return out


def greedy_worst_config(m: int, y: float = 0.5, count: int = 300, polish: bool = True) -> dict:
    """The worst configuration of `m` offsets, by the marginal ladder plus polish.

    The ladder gives the exact optimum of the decoupled problem (damage at the
    window peaks, relief only within windows); the polish is a local descent
    on the exact slack, which restores the cross-window relief.  The two agree
    to ~1e-05, so the ladder is measuring the real optimum, not a caricature.
    """
    ladder = marginal_ladder(y, count)
    positions = np.array([row[1] for row in ladder[:m]], dtype=float)
    ladder_slack = shq(y) / 2 + float(sum(row[0] for row in ladder[:m]))
    attained = slack_offsets(positions, y)
    polished = attained
    if polish and m <= 12:
        res = minimize(
            lambda s: slack_offsets(s, y),
            positions,
            method="Nelder-Mead",
            options={"xatol": 1e-11, "fatol": 1e-15, "maxiter": 40000, "maxfev": 40000},
        )
        if float(res.fun) < polished:
            polished = float(res.fun)
            positions = np.sort(np.asarray(res.x, dtype=float))
    gaps = np.diff(np.sort(positions)) if m > 1 else np.array([])
    return {
        "m": int(m),
        "y": float(y),
        "offsets": np.sort(positions),
        "ladder_slack": float(ladder_slack),
        "attained_slack": float(attained),
        "polished_slack": float(polished),
        "margin": float((4 / A_CONST**2) * polished),
        "min_gap": float(gaps.min()) if gaps.size else float("nan"),
        "max_gap": float(gaps.max()) if gaps.size else float("nan"),
        "multiplicity_profile": _profile(positions, top=4),
    }


def worst_over_all_configurations(y: float = 0.5, count: int = 300,
                                  sizes: Iterable[int] | None = None) -> dict:
    """Minimum of the attained slack over the ladder family, across sizes `m`.

    The ladder bound keeps falling with `m`, but the cross-window relief of a
    real configuration grows like `m^2`, so the attained worst case has a
    finite optimal size, measured at `m = 50` for `y = 1/2`.
    """
    if sizes is None:
        sizes = list(range(1, 41)) + [45, 50, 55, 60, 70, 80, 100, 150, 200]
    ladder = marginal_ladder(y, count)
    best = None
    profile = []
    for m in sizes:
        if m > len(ladder):
            break
        positions = np.array([row[1] for row in ladder[:m]], dtype=float)
        val = slack_offsets(positions, y)
        profile.append((int(m), float(val)))
        if best is None or val < best[1]:
            best = (int(m), float(val), positions)
    m_best, slack_best, positions = best
    dmg = float(np.sum(damage(y, positions)))
    rel = slack_best - shq(y) / 2 + dmg
    return {
        "y": float(y),
        "m": m_best,
        "slack": slack_best,
        "margin": float((4 / A_CONST**2) * slack_best),
        "damage_total": dmg,
        "relief": float(rel),
        "profile": profile,
        "multiplicity_profile": _profile(positions),
        **_ratio_fields(slack_best, y),
    }


def _profile(positions: np.ndarray, top: int = 3) -> dict:
    """How many offsets sit on each window peak (folded onto `|s|`)."""
    counts = Counter(round(float(abs(p)), 3) for p in positions)
    return {k: int(v) for k, v in counts.most_common(top)}


def unconditional_lower_bound(y: float = 0.5, count: int = 300) -> dict:
    """LEMMA C as a number: a lower bound for the slack of EVERY configuration.

    Two offsets in the same window are at most `w_max` apart, so each such
    pair relieves at least `phi_r(w_max)^2/400`; offsets outside every window
    have `D <= 0`; the windows past `count` are covered by the `Qim_far_sq`
    tail bound, charged pessimistically as one offset at each of their peaks.
    """
    wins = damage_windows(float(y), count)
    w_max = max(w.width for w in wins)
    gamma = float(phi_r(w_max))
    relief_pair = gamma**2 / 400.0
    ladder = marginal_ladder(y, count, relief_per_pair=relief_pair)
    worst_sum = float(sum(row[0] for row in ladder))
    tail = damage_tail_bound(y, wins[-1].peak)
    s_half = shq(y) / 2
    excess = -worst_sum + 2 * tail
    bound = s_half - excess
    levels = {}
    for _, _, level, index in ladder:
        levels[index] = max(levels.get(index, 0), level)
    return {
        "y": float(y),
        "windows": count,
        "window_width_max": float(w_max),
        "gamma": gamma,
        "relief_per_pair": relief_pair,
        "shq_half": s_half,
        "worst_net_damage": float(excess),
        "tail_bound": float(tail),
        "slack_lower_bound": float(bound),
        "margin_lower_bound": float((4 / A_CONST**2) * bound),
        "ratio": float(excess / s_half),
        "safety_factor": float(s_half / excess),
        "holds": bool(bound > 0),
        "top_window_multiplicity": levels.get(0, 0),
        "second_window_multiplicity": levels.get(1, 0),
    }


def separated_worst(y: float = 0.5, count: int = 300) -> dict:
    """The worst `2 pi`-separated configuration: one offset per window peak.

    A gap of at least `w_max = 0.986` already forces at most one offset per
    window, so this is the true supremum of the damage over every
    configuration EForm3's `d >= 4` hypothesis admits.
    """
    tot = damage_total_one_side(y, count)
    total_damage = 2 * tot["total_upper"]
    s_half = shq(y) / 2
    return {
        "y": float(y),
        "total_damage": float(total_damage),
        "total_damage_over_y2": float(total_damage / float(y) ** 2),
        "shq_half": s_half,
        "slack": float(s_half - total_damage),
        "margin": float((4 / A_CONST**2) * (s_half - total_damage)),
        "eform3_cap": EFORM3_SEPARATED_DAMAGE_CAP * float(y) ** 2,
        "eform3_cap_slack": float(EFORM3_SEPARATED_DAMAGE_CAP * float(y) ** 2 / total_damage),
        "one_offset_per_window_needs_gap": float(tot["max_width"]),
        **_ratio_fields(float(s_half - total_damage), y),
    }


def peak_damage_coefficient(y: float) -> float:
    """`max_s D(y,s) / y^2`, the sharp version of EForm3's `uniform_damage`.

    Measured to increase with `y` on `(0, 1/2]`, from `1.6473e-02` in the
    limit to `1.7586e-02` at `y = 1/2`, so `y = 1/2` is the binding depth for
    every statement here that compares a damage to a `y^2` budget.
    """
    return float(damage(y, _worst_offset(y))) / float(y) ** 2


def separated_consistency(y: float = 0.5, draws: int = 40, n: int = 12,
                          seed: int = 20260813, separation: float = EFORM3_SEPARATION) -> dict:
    """`d >= 4`-separated configurations against EForm3's own bounds.

    Checks the two Lean statements the separated theorem rests on, as
    measurements: every offset's damage is under `uniform_damage`, and every
    configuration's total damage is under `separated_damage`.  The draws
    include the extremal separated configuration, one offset on each of the
    innermost window peaks, both sides, whose gaps are all `>= 2 pi - 1`, so
    the comparison is not made only against easy cases.
    """
    rng = np.random.default_rng(seed)
    worst_total = -float("inf")
    worst_point = -float("inf")
    min_margin = float("inf")
    peaks = [w.peak for w in damage_windows(y, max(2, n // 2))]
    structured = np.sort(np.array([sgn * p for p in peaks[: n // 2] for sgn in (1, -1)]))
    configs = [(structured, 0.0)]
    for _ in range(draws):
        gaps = separation + rng.exponential(3.0, size=n - 1)
        xs = np.concatenate([[0.0], np.cumsum(gaps)])
        configs.append((xs, float(rng.uniform(0.0, xs[-1]))))
    for xs, t in configs:
        offs = np.asarray(xs, dtype=float) - t
        d = damage(y, offs)
        worst_total = max(worst_total, float(d.sum()))
        worst_point = max(worst_point, float(d.max()))
        min_margin = min(min_margin, margin(xs, y, t))
    cap_total = EFORM3_SEPARATED_DAMAGE_CAP * y**2
    cap_point = EFORM3_UNIFORM_DAMAGE_CAP * y**2
    return {
        "y": float(y),
        "draws": draws + 1,
        "n": n,
        "separation": separation,
        "worst_total_damage": worst_total,
        "eform3_total_cap": cap_total,
        "total_within_cap": bool(worst_total <= cap_total),
        "worst_point_damage": worst_point,
        "eform3_point_cap": cap_point,
        "point_within_cap": bool(worst_point <= cap_point),
        "min_margin": min_margin,
        "all_margins_positive": bool(min_margin > 0),
    }


# --------------------------------------------------------------------------
# the record
# --------------------------------------------------------------------------

#: Measured values at `y = 1/2`, pinned by `test_near_coincident.py`.  Slacks
#: are in damage units; `margin = (4/A^2) * slack` is the retention
#: inequality's own units.  Ratios are net damage over `Shq/2`.
RECORD = {
    "A": 0.9187253698655684,
    "shq_half": 3.375420393031e-02,
    "shq_half_over_y2": 1.350168157e-01,
    "peak_offset": 6.516999776065,
    "peak_damage": 4.396424117822e-03,
    "peak_damage_over_y2": 1.758569647e-02,
    "no_damage_radius": 6.0653187731,
    "window_width_max": 9.860007073e-01,
    "damage_total_one_side": 6.861031164e-03,
    "second_moment": 7.120056968e-02,
    "second_order_kappa2": 4.361245296e-02,
    "second_order_damage_part": 4.438744592e-02,
    "second_order_repulsion_part": -7.749929632e-04,
    "coincident_discriminant": -1.127335e-04,
    "coincident_m_star": 2.583474,
    "coincident_min_margin": 1.2659016e-01,
    "coincidence_safe_multiplicity": 1,
    "critical_depth": 1.126391302,
    "cluster_rho_eform3_constants": 1.720831,
    "cluster_rho_sharp_constants": 4.485925,
    "damage_cap_for_rho_4": 2.19041e-02,
    "ap_worst_gap": 0.0,
    "ap_worst_m": 3,
    "ap_worst_slack": 2.689535e-02,
    "ap_worst_margin": 1.274576e-01,
    "ap_worst_gap_at_least_4_slack": 2.742016e-02,
    "ap_excluded_penalty": 1.95e-02,
    "free_worst_m": 50,
    "free_worst_slack": 1.579343e-02,
    "free_worst_margin": 7.484540e-02,
    "free_worst_safety_factor": 1.87933,
    "unconditional_net_damage": 1.957213e-02,
    "unconditional_slack_bound": 1.418207e-02,
    "unconditional_margin_bound": 6.720913e-02,
    "unconditional_safety_factor": 1.72461,
    "separated_slack": 2.003214e-02,
    "separated_ratio": 4.0653e-01,
    "separated_safety_factor": 2.45985,
    "eform3_separated_cap_looseness": 2.2373,
}


def report(y: float = 0.5, count: int = 300, scan: bool = True) -> dict:
    """Every measurement in this module, as one dict."""
    out = {
        "y": float(y),
        "constants": {
            "A": A_CONST,
            "shq": shq(y),
            "shq_half": shq(y) / 2,
            "shq_half_over_y2": shq(y) / 2 / y**2,
            "eform3_shq_half_coeff": EFORM3_SHQ_HALF_COEFF,
            "second_moment": second_moment(),
            "relief_per_coincident_pair": A_CONST**2 / 400.0,
        },
        "geometry": {
            "no_damage_radius": no_damage_radius(y),
            "eform3_near_field_radius": EFORM3_NEAR_FIELD_RADIUS,
            "windows": [
                {"index": w.index, "peak": w.peak, "damage": w.damage, "width": w.width}
                for w in damage_windows(y, 6)
            ],
            "total": damage_total_one_side(y, count),
        },
        "coincident": coincident_quadratic(y),
        "coincidence_safe_multiplicity": coincidence_safe_multiplicity(y),
        "critical_depth": critical_depth(),
        "second_order": second_order_coefficient(y),
        "cluster_threshold_eform3": cluster_diameter_threshold(),
        "cluster_threshold_sharp": cluster_diameter_threshold(
            damage_cap=peak_damage_coefficient(y)
        ),
        "peak_damage_coefficient": {
            str(v): peak_damage_coefficient(v) for v in (0.05, 0.1, 0.25, 0.4, 0.5)
        },
        "damage_cap_for_rho_4": damage_cap_for_diameter(EFORM3_SEPARATION),
        "free_worst": worst_over_all_configurations(y, count),
        "unconditional": unconditional_lower_bound(y, count),
        "separated": separated_worst(y, count),
        "separated_consistency": separated_consistency(y),
    }
    if scan:
        out["ap_scan"] = ap_scan(y)
        out["depth_scan"] = depth_scan()
    return out


def main() -> None:  # pragma: no cover - console entry point
    y = 0.5
    rep = report(y)
    c = rep["constants"]
    print("=" * 78)
    print("near-coincident limit of the EForm3 retention inequality   (y = 1/2)")
    print("=" * 78)
    print(f"A = {c['A']:.12f}   Shq/2 = {c['shq_half']:.12e}   "
          f"(Shq/2)/y^2 = {c['shq_half_over_y2']:.9f}  [Lean lower bound "
          f"{EFORM3_SHQ_HALF_COEFF:.9f}]")
    print(f"relief per coincident pair = A^2/400 = {c['relief_per_coincident_pair']:.9e}")
    print()
    g = rep["geometry"]
    print(f"no-damage radius {g['no_damage_radius']:.10f}  "
          f"(EForm3's no_damage reaches {g['eform3_near_field_radius']})")
    print("damage windows (positive side):")
    for w in g["windows"]:
        print(f"   k={w['index']}  peak {w['peak']:10.6f}  D {w['damage']:.8e}  "
              f"width {w['width']:.6f}")
    t = g["total"]
    print(f"   sum over {t['windows']} windows = {t['head']:.9e}  "
          f"+ tail bound {t['tail_bound']:.3e}  -> T <= {t['total_upper']:.9e}")
    print()
    q = rep["coincident"]
    print("1. TWO (AND m) COINCIDENT OFFSETS")
    print(f"   f(m) = {q['quadratic_coeff']:.6e} m^2 - {q['peak_damage'] + q['quadratic_coeff']:.6e} m"
          f" + {q['shq_half']:.6e}")
    print(f"   discriminant {q['discriminant']:+.6e}  ->  safe at every m: {q['safe_for_every_m']}")
    print(f"   minimum at m* = {q['m_star']:.6f}, margin {q['margin_at_m_star']:.8f}")
    for m in (1, 2, 3, 4, 8, 16, 64):
        print(f"      m={m:3d}: slack {coincident_slack(m, y):+.8f}   "
              f"margin {(4 / A_CONST**2) * coincident_slack(m, y):+.8f}")
    print(f"   m_0 (safe for every larger m) = {rep['coincidence_safe_multiplicity']}")
    print(f"   discriminant vanishes only at y = {rep['critical_depth']:.9f} "
          f"(the problem needs y <= 0.5)")
    print()
    so = rep["second_order"]
    print("1b. THE PERTURBATION x_2 = x_1 + g")
    print(f"   kappa2 = psi''(s*)/A^2 - L2/(100A) = {so['damage_part']:+.9e} "
          f"{so['repulsion_part']:+.9e} = {so['kappa2']:+.9e}")
    print(f"   g = 0 is a local {'MINIMUM' if so['coincidence_is_local_minimum'] else 'MAXIMUM'}"
          f" of the margin; repulsion supplies {so['repulsion_share'] * 100:.2f}% of it")
    print()
    print("2. THE CLUSTER LEMMA")
    ce, cs = rep["cluster_threshold_eform3"], rep["cluster_threshold_sharp"]
    print(f"   with EForm3 constants (cap {EFORM3_UNIFORM_DAMAGE_CAP}): "
          f"diameter rho <= {ce['rho']:.6f}  (needs phi_r(rho) >= {ce['phi_needed']:.6f})")
    print(f"   with the sharp cap: rho <= {cs['rho']:.6f}")
    print(f"   the cap that would buy rho = 4: {rep['damage_cap_for_rho_4']:.7f} y^2")
    print()
    print("3. THE SCANS")
    if "ap_scan" in rep:
        sc = rep["ap_scan"]
        for m, r in sorted(sc["records"].items()):
            print(f"   m={m}: worst g={r['gap']:8.5f}  slack {r['slack']:.8f}  "
                  f"margin {r['margin']:.7f}  ratio {r['ratio']:.5f}")
        w = sc["worst"]
        print(f"   worst over the grid: (g, m, y) = ({w['gap']:.5f}, {w['m']}, {y})  "
              f"slack {w['slack']:.8f}")
        s4 = sc["worst_with_gap_at_least_4"]
        print(f"   worst with g >= 4:   (g, m)    = ({s4['gap']:.5f}, {s4['m']})  "
              f"slack {s4['slack']:.8f}  -> excluded region worse by "
              f"{sc['excluded_penalty'] * 100:.2f}%")
    if "depth_scan" in rep:
        ds = rep["depth_scan"]
        print("   over depths (scale-free ratio, worst (g,m) at each y):")
        for r in ds["rows"]:
            print(f"      y={r['y']:.2f}: g={r['gap']:7.4f} m={r['m']}  "
                  f"ratio {r['ratio']:.5f}  slack {r['slack']:.8f}")
        print(f"      ratio increases with depth: {ds['ratio_increases_with_depth']}"
              f"  -> binding depth y = {ds['worst']['y']}")
    fw = rep["free_worst"]
    print(f"   free worst configuration: m = {fw['m']}, slack {fw['slack']:.8f}, "
          f"margin {fw['margin']:.8f}, net damage {fw['ratio'] * 100:.2f}% of budget "
          f"({fw['safety_factor']:.5f}x)")
    print(f"      offsets on peaks: {fw['multiplicity_profile']}")
    print()
    print("4. THE UNCONDITIONAL STATEMENT")
    u = rep["unconditional"]
    print(f"   window width max {u['window_width_max']:.9f}, gamma = phi_r(w_max) = {u['gamma']:.9f}")
    print(f"   worst net damage {u['worst_net_damage']:.9e} vs Shq/2 {u['shq_half']:.9e}"
          f"  ({u['ratio'] * 100:.2f}% of budget, {u['safety_factor']:.5f}x)")
    print(f"   slack >= {u['slack_lower_bound']:.9e}  (margin >= {u['margin_lower_bound']:.9e}) "
          f"for every configuration, every n: {u['holds']}")
    sp = rep["separated"]
    print(f"   separated (one per window): slack {sp['slack']:.9e}, net damage "
          f"{sp['ratio'] * 100:.2f}% of budget ({sp['safety_factor']:.5f}x); EForm3's own "
          f"cap is {sp['eform3_cap_slack']:.4f}x looser than the truth")
    sc2 = rep["separated_consistency"]
    print(f"   random d>=4 draws: total damage {sc2['worst_total_damage']:.6e} <= "
          f"{sc2['eform3_total_cap']:.6e} ({sc2['total_within_cap']}), "
          f"min margin {sc2['min_margin']:.6f}")


if __name__ == "__main__":  # pragma: no cover
    main()
