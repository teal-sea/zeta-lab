"""The Riemann–Weil explicit formula as a computable object, and Weil positivity.

This module makes "gate #2" of ``docs/09-new-ontologies.md`` (an ontology must
contain *a home for positivity*) computational: it evaluates both sides of the
Riemann–Weil explicit formula independently, exposes the arithmetic side as the
Weil functional ``W(h)``, and probes how close ``W`` comes to ``0`` over
families of positive-type test functions.

The convention (self-validated, not trusted from memory)
--------------------------------------------------------

Factor placement in the explicit formula varies between sources, so the
convention below was *calibrated numerically*: both sides were computed
independently (zero side from cached, independently verified zero ordinates;
arithmetic side from Γ-factors, primes and quadrature) for four test functions
from three unrelated families, and required to agree.  For an even test
function ``h``, analytic in a strip ``|Im r| <= 1/2 + delta`` and rapidly
decaying, with Fourier partner

    g(u) = (1/2π) ∫ h(r) e^{-iru} dr        (so h(r) = ∫ g(u) e^{iru} du),

the validated statement is

    Σ_ρ h(γ_ρ)  =  h(i/2) + h(-i/2)
                 + (1/2π) ∫ h(r) [Re ψ(1/4 + ir/2) - log π] dr
                 - 2 Σ_{n≥2} Λ(n) n^{-1/2} g(log n),

where ρ = 1/2 + iγ_ρ runs over ALL nontrivial zeros — on RH the ordinates
γ_ρ are real and enter with both signs (+γ and -γ), ψ is the digamma
function, and Λ is the von Mangoldt function.  Measured agreement of the two
sides (see ``tests/test_weil.py``, which re-runs these):

* Gaussian ``h(r) = exp(-a r²)``, a = 0.01 and a = 0.002, dps = 30:
  |zero side - arithmetic side| ≈ 8.3e-32 and 2.8e-31 (limited by the
  precision of the cached zeros).
* Gaussian a = 0.2 at dps = 45: both sides agree to a relative 2e-28 on a
  value of 8.86e-18 built from pieces of size ~2 — the identity survives
  ~18 orders of magnitude of cancellation.
* Fejér ``h(r) = (sin(br)/(br))²``, b = 2, zeros up to 10⁴: difference
  3.331e-5 against a zero-sum truncation-tail *estimate* of 3.331e-5 (the
  slowly decaying 1/(bγ)² envelope makes the truncated tail the dominant
  error, and the density-based estimate accounts for it to ~4 digits).
* Autocorrelation pairs (h = |f̂|²): Fourier partnership checked to ~1e-31
  and formula agreement at the working-precision floor.

Positivity
----------

**Weil positivity criterion** (Weil 1952; refined 1972 — see
``docs/07-equivalences-and-criteria.md`` §7): RH holds if and only if
``W(h) = Σ_ρ h(γ_ρ) >= 0`` for every admissible ``h`` of *positive type*,
i.e. every ``h`` that is ``|f̂|²`` on the real axis (equivalently: ``g`` is a
self-correlation ``f ⋆ f~``) for ``f`` in a suitable dense class of test
functions.  *Hedge*: the exact admissible class differs between formulations
(compactly supported smooth ``f`` vs. analyticity-in-a-strip conditions); every
pair constructed by this module is of positive type under any of the usual
formulations.  ``weil_functional`` evaluates ``W(h)`` from the *arithmetic*
side (no zeros used), and ``positivity_probe`` / ``near_tightness_report``
measure the margin.  Honest scope (``docs/08``): observed positivity reflects
the computationally verified zeros and is **not** evidence for RH; the
reconnaissance value is in *where* the functional is tightest — the zero-free
gap below γ₁ = 14.1347… is what controls it.

Error accounting (nothing is hand-waved)
----------------------------------------

* Zero-sum truncation: bounded by partial summation against
  N(t) ≤ RvM(t) + Q(t) with Backlund's explicit envelope
  Q(t) = 0.137 log t + 0.443 log log t + 4.35 (commonly cited constants,
  Backlund 1918; the tests re-verify |N(t) - RvM(t)| < Q(t) empirically over
  the cached range, where the observed gap never exceeds ~1).  The bound is
  2[env(T)·2Q(T) + ∫_T^∞ env(t)(RvM'(t) + Q'(t)) dt] for a nonincreasing
  envelope env ≥ |h|.
* Prime-sum truncation: bounded via ψ(x) < 1.04·x (Rosser–Schoenfeld's
  1.03883…, commonly cited; re-verified empirically for x ≤ 10⁵ in the
  tests), giving Σ_{n>N} Λ(n)φ(n) ≤ 1.04(Nφ(N) + ∫_N^∞ φ) for nonincreasing
  φ.  For Fejér pairs g has compact support, the prime sum is *finite* and
  the bound is exactly 0.
* Archimedean integral: tanh-sinh quadrature on oscillation-aligned
  subintervals; for Fejér the oscillatory tail is integrated by parts
  analytically (polygamma derivatives), cross-checked against ``mp.quadosc``
  to ~1e-17 in the tests.
"""

from __future__ import annotations

import math
from typing import Callable, Iterable, Sequence

import numpy as np
from mpmath import mp, mpf

__all__ = [
    "gaussian_pair",
    "fejer_pair",
    "legendre_pair",
    "autocorrelation_pair",
    "explicit_formula_sides",
    "weil_functional",
    "positivity_probe",
    "near_tightness_report",
]

# γ₁, used by near_tightness_report; pinned by tests against zeta.zeros.
GAMMA1 = 14.134725141734693790

_PARAM_DPS = 60  # decimal parameters parse at 60 digits, not the ambient dps


def _param(x) -> mpf:
    """Parse a pair parameter at high fixed precision.

    A parameter like "0.01" defines *which* test function is meant; parsing
    it at the ambient dps would silently substitute a nearby function and
    break closed-form cross-checks (e.g. pole = 2e^{a/4}) at that dps."""
    with mp.workdps(_PARAM_DPS):
        return mp.mpf(x)


# ---------------------------------------------------------------------------
# Test-function pairs (h, g).  Each callable carries a ``weil_hints`` dict so
# that the quadrature/tail machinery can use exact structure; user-supplied
# pairs without hints fall back to generic (slower, hedged) code paths.
# ---------------------------------------------------------------------------


def gaussian_pair(a) -> tuple[Callable, Callable]:
    """Gaussian pair ``h(r) = exp(-a r²)``, ``g(u) = e^{-u²/4a} / (2√(πa))``.

    ``h`` is entire, positive, and of positive type: h = |f̂|² for the Gaussian
    f(u) = (2πa)^{-1/4}·... (any Gaussian f works up to normalisation), so it
    is admissible for the Weil criterion.  ``g`` is the exact Fourier partner
    under g(u) = (1/2π)∫ h(r) e^{-iru} dr (checked to ~1e-31 in the tests).
    """
    a = _param(a)
    if a <= 0:
        raise ValueError("gaussian_pair needs a > 0")

    def h(r):
        return mp.e ** (-a * r * r)

    def g(u):
        # 1/(2√(πa)) is recomputed per call: it must match the working
        # precision of the caller, not the precision at construction time
        # (a itself is a fixed mpf — exact by definition of the pair).
        return mp.e ** (-u * u / (4 * a)) / (2 * mp.sqrt(mp.pi * a))

    def envelope(t):  # = |h| on t >= 0, nonincreasing
        return mp.e ** (-a * t * t)

    def u_cut(L):  # u with  u²/(4a) - u/2 >= L  (prime-sum cutoff)
        return a + mp.sqrt(a * a + 4 * a * L)

    hints = {
        "kind": "gaussian",
        "a": a,
        "envelope": envelope,
        "env_avg": envelope,
        "u_cut": u_cut,
        "g_abs": g,
    }
    h.weil_hints = g.weil_hints = hints
    return h, g


def fejer_pair(b) -> tuple[Callable, Callable]:
    """Fejér pair ``h(r) = (sin(br)/(br))²`` with triangle partner ``g``.

    g(u) = (1 - |u|/2b)/(2b) for |u| < 2b, else 0 — *compact support*, so the
    prime sum in the explicit formula is FINITE: only n < e^{2b} contribute.
    ``h`` is of positive type: the triangle is the self-correlation of the box
    f = 1_{[-b,b]}/(2b), i.e. h = |f̂|² on the real axis.  ``h`` extends to an
    entire function (h(i/2) = (sinh(b/2)/(b/2))²).
    """
    b = _param(b)
    if b <= 0:
        raise ValueError("fejer_pair needs b > 0")

    def h(r):
        if r == 0:
            return mp.mpf(1)
        x = b * r
        s = mp.sin(x) / x
        return s * s

    def g(u):
        au = abs(u)
        if au >= 2 * b:
            return mp.mpf(0)
        return (1 - au / (2 * b)) / (2 * b)

    def envelope(t):  # min(1, 1/(bt)²): nonincreasing majorant of |h|
        if t <= 1 / b:
            return mp.mpf(1)
        return 1 / (b * t) ** 2

    def env_avg(t):  # average of sin² is 1/2: mean-density tail estimate
        if t <= 1 / b:
            return mp.mpf("0.5")
        return 1 / (2 * (b * t) ** 2)

    hints = {
        "kind": "fejer",
        "b": b,
        "envelope": envelope,
        "env_avg": env_avg,
        "support": 2 * b,
        "g_abs": g,
    }
    h.weil_hints = g.weil_hints = hints
    return h, g


def legendre_pair(n: int) -> tuple[Callable, Callable]:
    """Shifted-triangle pair localising the prime sum to a Legendre interval.

    ``g(u)`` is a unit-height triangle supported exactly on
    ``[log n², log (n+1)²]`` (and its mirror on the negative axis), so the
    prime term of the explicit formula sees only ``Λ(k)`` for
    ``n² < k < (n+1)²`` — the interval of Legendre's conjecture.  With
    centre ``C = log(n(n+1))`` and half-width ``W = log(1 + 1/n)``,

        g(u) = (1 - ||u| - C|/W)⁺ ,
        h(r) = 2 W cos(C r) (sin(W r/2)/(W r/2))² ,

    the exact Fourier partner under h(r) = ∫ g(u) e^{iru} du (a triangle is a
    modulated Fejér kernel; partnership is re-verified numerically in the
    tests).  ``h`` extends to an entire function, with
    h(i/2) = 2 W cosh(C/2) (sinh(W/4)/(W/4))².

    Unlike :func:`fejer_pair` this pair is **not** of positive type (the
    cosine factor changes sign), so it is an explicit-formula instrument, not
    a Weil-criterion one.  ``h`` decays only like 1/r² — g is merely C⁰ — so
    zero-side truncation tails dominate every budget; the tail machinery is
    given the exact envelope.
    """
    m = int(n)
    if m < 2:
        # n = 1 puts the inner edge at log 1 = 0: the mirror triangles touch
        # at the origin and the "interval" [1, 4] contains k = 2, 3 only.
        # Nothing breaks numerically, but the pair stops being the Legendre
        # localisation it claims to be; refuse rather than hedge.
        raise ValueError("legendre_pair needs n >= 2")
    with mp.workdps(_PARAM_DPS):
        A = 2 * mp.log(m)
        B = 2 * mp.log(m + 1)
        C = (A + B) / 2
        W = (B - A) / 2

    def g(u):
        au = abs(u)
        if au <= A or au >= B:
            return mp.mpf(0)
        return 1 - abs(au - C) / W

    def h(r):
        if r == 0:
            return 2 * W
        x = W * r / 2
        s = mp.sin(x) / x
        return 2 * W * s * s * mp.cos(C * r)

    def envelope(t):  # nonincreasing majorant of |h| on t >= 0
        if t <= 2 / W:
            return 2 * W
        return 2 * W / (W * t / 2) ** 2

    def env_avg(t):  # sin² averages to 1/2, |cos| to 2/π
        if t <= 2 / W:
            return 2 * W / mp.pi
        return 2 * W / (W * t / 2) ** 2 / mp.pi

    hints = {
        "kind": "legendre",
        "n": m,
        "support": B,
        "envelope": envelope,
        "env_avg": env_avg,
        "g_abs": g,
    }
    h.weil_hints = g.weil_hints = hints
    return h, g


def autocorrelation_pair(
    coeffs: Sequence, spacing=2.0, sigma=0.35
) -> tuple[Callable, Callable]:
    """Positive-type pair from an explicit autocorrelation, h = |f̂|².

    f(u) = Σ_j c_j exp(-(u - j·s)²/(2σ²))  (a small parametrised family:
    Gaussian bumps at 0, s, 2s, … with real weights ``coeffs``).  Then

        h(r) = |f̂(r)|² = 2πσ² e^{-σ²r²} Σ_{j,k} c_j c_k cos(r s (j-k)) ≥ 0,
        g(u) = σ√π       Σ_{j,k} c_j c_k exp(-(u - s(j-k))²/(4σ²)),

    both in closed form; ``h`` extends to an entire function of r (the cos
    terms become cosh on the imaginary axis), and h = |f̂|² makes the pair
    admissible for the Weil criterion by construction.  Fourier partnership
    and h ≥ 0 are re-verified numerically in the tests.
    """
    s = _param(spacing)
    sg = _param(sigma)
    if sg <= 0:
        raise ValueError("autocorrelation_pair needs sigma > 0")
    c = [_param(x) for x in coeffs]
    if not c or all(x == 0 for x in c):
        raise ValueError("autocorrelation_pair needs a nonzero coefficient")
    J = len(c)
    D = s * (J - 1)  # largest frequency |s(j-k)|

    # π-derived prefactors are recomputed inside each callable so they track
    # the caller's working precision (constants frozen at construction time
    # would cap the h↔g Fourier partnership at the construction dps).

    def h(r):
        tot = mp.fsum(
            c[j] * c[k] * mp.cos(r * s * (j - k))
            for j in range(J)
            for k in range(J)
        )
        return 2 * mp.pi * sg * sg * mp.e ** (-((sg * r) ** 2)) * tot

    def g(u):
        tot = mp.fsum(
            c[j] * c[k] * mp.e ** (-((u - s * (j - k)) ** 2) / (4 * sg * sg))
            for j in range(J)
            for k in range(J)
        )
        return mp.sqrt(mp.pi) * sg * tot  # = 2πσ² · 1/(2σ√π) · Σ…

    csum = mp.fsum(abs(x) for x in c)
    c2sum = mp.fsum(x * x for x in c)

    def envelope(t):  # |h(t)| <= 2πσ² (Σ|c_j|)² e^{-σ²t²}
        return 2 * mp.pi * sg * sg * csum * csum * mp.e ** (-((sg * t) ** 2))

    def env_avg(t):  # cos terms average to 0: diagonal only
        return 2 * mp.pi * sg * sg * c2sum * mp.e ** (-((sg * t) ** 2))

    def g_abs(u):
        au = abs(u)
        x = (au - D) if au > D else mp.mpf(0)
        return mp.sqrt(mp.pi) * sg * csum * csum * mp.e ** (-(x * x) / (4 * sg * sg))

    def u_cut(L):  # u with (u-D)²/(4σ²) - u/2 >= L
        return (D + sg * sg) + mp.sqrt(2 * D * sg * sg + sg**4 + 4 * sg * sg * L)

    hints = {
        "kind": "autocorr",
        "sigma": sg,
        "D": D,
        "envelope": envelope,
        "env_avg": env_avg,
        "u_cut": u_cut,
        "g_abs": g_abs,
    }
    h.weil_hints = g.weil_hints = hints
    return h, g


# ---------------------------------------------------------------------------
# Zero data (cached; see zeta.zeros / zeta.statistics for the verification
# story: mpmath.zetazero oracle, N(T) completeness certificates).
# ---------------------------------------------------------------------------

_HP_ZEROS: list | None = None  # first 1000 ordinates as mpf (dps 30 cache)


def _hp_zeros() -> list:
    global _HP_ZEROS
    if _HP_ZEROS is None:
        from zeta.zeros import first_n_zeros

        _HP_ZEROS = first_n_zeros(1000)
    return _HP_ZEROS


def _float_zeros(t_max: float) -> np.ndarray:
    from zeta.statistics import zero_ordinates

    return zero_ordinates(t_max=float(t_max))


def _zeros_upto(gamma_max: float) -> Iterable:
    """Ascending ordinates 0 < γ <= gamma_max: mpf where available (first
    1000, ~30 digits), float64 (RS-scan, |err| <= ~5.4e-9) beyond."""
    hp = _hp_zeros()
    for z in hp:
        if z > gamma_max:
            return
        yield z
    if gamma_max > hp[-1]:
        t_max = 10000.0 if gamma_max <= 10000.0 else float(gamma_max)
        floats = _float_zeros(t_max)
        # Margin against double-counting the hand-off zero: the RS-scan
        # float64 value of zero #1000 can land on either side of
        # float(hp[-1]) (|err| ~ 1e-11, and the .npz cache regenerates on
        # fresh clones), so a strict `z <= top` could re-yield it.  1e-6 is
        # ~5 orders above the RS error and ~5 below the local gap (~0.16).
        top = float(hp[-1]) + 1e-6
        for z in floats:
            if z <= top:
                continue
            if z > gamma_max:
                return
            yield mp.mpf(z)


# ---------------------------------------------------------------------------
# The four pieces of the formula
# ---------------------------------------------------------------------------


def _zero_side(h, gamma_max: float, dps: int):
    """(Σ_{0<γ<=γmax} [h(γ) + h(-γ)], zeros used, skipped-tail slack).

    Early exit once a (hint-provided, nonincreasing) envelope certifies that
    every remaining term is below 10^-(dps+10); the slack term returned is an
    upper bound on everything skipped and is folded into the tail bound.
    """
    hints = getattr(h, "weil_hints", {})
    env = hints.get("envelope")
    thresh = mp.mpf(10) ** (-(dps + 10))
    terms = []
    used = 0
    skipped_slack = mp.mpf(0)
    for z in _zeros_upto(gamma_max):
        if env is not None and env(z) * 2 < thresh:
            # everything from here on is certified negligible
            from zeta.zeros import riemann_von_mangoldt

            # N(gamma_max) <= RvM(gamma_max) + Q(gamma_max) (Backlund; the
            # empirical gap over the cached range is < 1.2, but the bound
            # must not lean on that out of range), +1 for the floor.
            n_left = (
                max(riemann_von_mangoldt(gamma_max) - used, 0)
                + float(_backlund_Q(gamma_max))
                + 1
            )
            skipped_slack = mp.mpf(n_left) * thresh
            break
        terms.append(h(z) + h(-z))
        used += 1
    return mp.fsum(terms), used, skipped_slack


def _pole_term(h):
    tol = mp.mpf(10) ** (-mp.dps + 8)
    # Evenness must be checked on the real axis: for any h that is
    # real-valued on the reals, h(i/2) + h(-i/2) = h(i/2) + conj(h(i/2)) is
    # real by Schwarz reflection, so the imaginary-part check below can
    # never catch a non-even h — without this spot check a non-even h would
    # produce a silently wrong formula (the zero side symmetrises h, the
    # arithmetic side does not).
    for r0 in (mp.mpf(1) / 3, mp.mpf("1.7")):
        hp_, hm_ = h(r0), h(-r0)
        if abs(hp_ - hm_) > tol * (1 + abs(hp_)):
            raise ValueError(
                f"h is not even: h({r0}) != h(-{r0}); the explicit formula "
                "here is stated for even test functions"
            )
    v = mp.mpc(h(mp.mpc(0, "0.5")) + h(mp.mpc(0, "-0.5")))
    if abs(v.imag) > tol * (1 + abs(v.real)):
        raise ValueError(
            "h(i/2) + h(-i/2) is not real — h must take real values on the "
            "real axis and be analytic in |Im r| <= 1/2"
        )
    return v.real


def _w(r):
    """The archimedean density  Re ψ(1/4 + ir/2) - log π."""
    return mp.re(mp.digamma(mp.mpf(1) / 4 + mp.mpc(0, 1) * r / 2)) - mp.log(mp.pi)


def _w_deriv(j: int, r):
    """d^j/dr^j Re ψ(1/4 + ir/2) = Re[(i/2)^j ψ^(j)(1/4 + ir/2)]."""
    z = mp.mpf(1) / 4 + mp.mpc(0, 1) * r / 2
    return mp.re(mp.mpc(0, "0.5") ** j * mp.polygamma(j, z))


def _phi_deriv(k: int, A):
    """d^k/dr^k [ (Re ψ(1/4+ir/2) - log π) / r² ]  at r = A (Leibniz)."""
    tot = mp.mpf(0)
    for j in range(k + 1):
        wj = _w(A) if j == 0 else _w_deriv(j, A)
        m = k - j
        inv = (-1) ** m * mp.factorial(m + 1) / A ** (m + 2)
        tot += mp.binomial(k, j) * wj * inv
    return tot


def _fejer_osc_tail(b, A, M: int = 6):
    """∫_A^∞ cos(2br)·w(r)/r² dr for A a multiple of π/b, by M analytic
    double-integrations-by-parts (each boundary sits at sin(2bA)=0,
    cos(2bA)=1):  C_m = -φ^{(2m+1)}(A)/(4b²) - C_{m+1}/(4b²).

    Validated against mp.quadosc to ~1e-17 (tests, slow tier); the last
    retained term is an empirical proxy for the truncation error and is
    ~10x larger than the observed error.
    """
    fourb2 = 4 * b * b
    total = mp.mpf(0)
    coef = mp.mpf(1)
    for m_ in range(M):
        coef /= fourb2
        total += (-1) ** (m_ + 1) * coef * _phi_deriv(2 * m_ + 1, A)
    return total


def _arch_term(h, dps: int):
    """(1/2π) ∫_{-∞}^{∞} h(r)[Re ψ(1/4+ir/2) - log π] dr  (even ⇒ 2·∫_0^∞)."""
    hints = getattr(h, "weil_hints", {})
    kind = hints.get("kind")
    f = lambda r: h(r) * _w(r)
    if kind == "gaussian":
        L = 1 / mp.sqrt(hints["a"])
        I = mp.quad(f, [0, L, 4 * L, 16 * L, mp.inf])
    elif kind == "fejer":
        b = hints["b"]
        P = mp.pi / b
        A_target = max(45.0, 25.0 / float(b))
        K = int(mp.ceil(A_target / P))
        A = K * P
        # main region on sin-aligned humps, then the exact 1/(2b²r²) tail:
        # h = (1 - cos 2br)/(2b²r²) for the smooth + oscillatory pieces.
        I_main = mp.quad(f, [k * P for k in range(K + 1)])
        I_smooth = mp.quad(
            lambda r: _w(r) / (r * r), [A, 2 * A, 8 * A, 32 * A, mp.inf]
        )
        I_osc = _fejer_osc_tail(b, A)
        I = I_main + (I_smooth - I_osc) / (2 * b * b)
    elif kind == "autocorr":
        R = int(math.ceil(float(hints["D"]) + 8.0 / float(hints["sigma"]))) + 2
        I = mp.quad(f, [*range(R + 1), mp.inf])
    else:
        # generic fallback: dyadic panels; fine for smooth rapidly decaying h,
        # hedged for anything oscillatory (build a pair with hints instead).
        I = mp.quad(f, [0, 1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, mp.inf])
    return I / mp.pi  # = 2·I / (2π)


_PRIME_POWER_TABLE: list[tuple[int, int]] = []  # (n = p^k, p), n ascending
_PRIME_POWER_MAX = 0


def _prime_powers(n_max: int) -> list[tuple[int, int]]:
    global _PRIME_POWER_TABLE, _PRIME_POWER_MAX
    if n_max > _PRIME_POWER_MAX:
        sieve = np.ones(n_max + 1, dtype=bool)
        sieve[:2] = False
        for p in range(2, int(n_max**0.5) + 1):
            if sieve[p]:
                sieve[p * p :: p] = False
        table = []
        for p in np.nonzero(sieve)[0]:
            p = int(p)
            pk = p
            while pk <= n_max:
                table.append((pk, p))
                pk *= p
        table.sort()
        _PRIME_POWER_TABLE = table
        _PRIME_POWER_MAX = n_max
    return [t for t in _PRIME_POWER_TABLE if t[0] <= n_max]


_N_MAX_CAP = 2_000_000


def _resolve_n_max(g, n_max, dps: int) -> int:
    if n_max is not None:
        return int(n_max)
    hints = getattr(g, "weil_hints", {})
    if "support" in hints:  # g vanishes for |u| >= support: exact finite sum
        # capped: a wide support (fejer_pair(b) with b >= ~7.3) would demand
        # e^{2b} > 2e6 prime powers; beyond the cap the sum is truncated and
        # _prime_term reports the (then nonzero) Rosser-Schoenfeld tail bound.
        return min(int(mp.floor(mp.e ** hints["support"])), _N_MAX_CAP)
    if "u_cut" in hints:
        L = mp.log(10) * (dps + 8)
        return min(int(mp.e ** hints["u_cut"](L)) + 1, _N_MAX_CAP)
    return 50_000  # generic fallback; the reported tail bound covers it


def _prime_term(g, n_max: int):
    """(-2 Σ_{2<=n<=n_max} Λ(n) n^{-1/2} g(log n),  tail bound >= 0).

    Tail bound via ψ(x) < 1.04x (Rosser–Schoenfeld; see module docstring):
    2·1.04·(N φ(N) + ∫_N^∞ φ dt), φ(t) = t^{-1/2}|g(log t)| — valid when φ is
    nonincreasing beyond N, which holds for every pair built here (and is an
    assumption, documented, for user-supplied g).  Zero when g has compact
    support inside [0, log n_max]."""
    hints = getattr(g, "weil_hints", {})
    total = mp.fsum(
        mp.log(p) / mp.sqrt(n) * g(mp.log(n)) for n, p in _prime_powers(n_max)
    )
    # tail bound
    if "support" in hints and mp.log(n_max + 1) >= hints["support"]:
        tail = mp.mpf(0)
    else:
        g_abs = hints.get("g_abs", lambda u: abs(g(u)))
        N = mp.mpf(n_max)
        lo = mp.log(N)
        phi_N = g_abs(lo) / mp.sqrt(N)
        integral = mp.quad(
            lambda u: mp.e ** (u / 2) * g_abs(u), [lo, lo + 2, lo + 8, mp.inf]
        )
        tail = 2 * mp.mpf("1.04") * (N * phi_N + integral)
    return -2 * total, tail


def _backlund_Q(t):
    """Explicit envelope with |N(t) - RvM(t)| <= Q(t) (Backlund 1918 as
    commonly cited; re-verified empirically over the cached zeros in the
    tests, where the observed gap stays below ~1 ≪ Q ≈ 6)."""
    lt = mp.log(t)
    return mp.mpf("0.137") * lt + mp.mpf("0.443") * mp.log(lt) + mp.mpf("4.35")


def _zero_tail_bound(h, gamma_max: float, dps: int):
    """Upper bound for |Σ_{|γ|>γmax} h(γ)| given a nonincreasing envelope.

    Partial summation against N(t) <= RvM(t) + Q(t):
        Σ_{γ>T} env(γ) <= env(T)·2Q(T) + ∫_T^∞ env(t)·(RvM'(t) + Q'(t)) dt,
    doubled for the two signs ±γ.  Falls back to |h| as its own envelope
    (documented assumption: |h| nonincreasing past γmax) when no hint exists.
    """
    hints = getattr(h, "weil_hints", {})
    env = hints.get("envelope", lambda t: abs(h(t)))
    T = mp.mpf(gamma_max)

    def density(t):
        lt = mp.log(t)
        return (
            mp.log(t / (2 * mp.pi)) / (2 * mp.pi)
            + mp.mpf("0.137") / t
            + mp.mpf("0.443") / (t * lt)
        )

    integral = mp.quad(lambda t: env(t) * density(t), [T, 2 * T, 8 * T, mp.inf])
    return 2 * (env(T) * 2 * _backlund_Q(T) + integral)


def _zero_tail_estimate(h, gamma_max: float):
    """Density-based *estimate* (not bound) of the discarded zero-sum tail:
    2 ∫_T^∞ env_avg(t) · RvM'(t) dt with the mean envelope (e.g. sin² → 1/2
    for Fejér).  Empirically accurate to ~4 significant digits at T = 10⁴."""
    hints = getattr(h, "weil_hints", {})
    env = hints.get("env_avg")
    if env is None:
        return None
    T = mp.mpf(gamma_max)
    integral = mp.quad(
        lambda t: env(t) * mp.log(t / (2 * mp.pi)) / (2 * mp.pi),
        [T, 2 * T, 8 * T, mp.inf],
    )
    return 2 * integral


# ---------------------------------------------------------------------------
# Public evaluators
# ---------------------------------------------------------------------------


def _arithmetic_pieces(h, g, n_max, dps: int) -> dict:
    with mp.workdps(dps + 10):
        n_max_used = _resolve_n_max(g, n_max, dps)
        pole = _pole_term(h)
        arch = _arch_term(h, dps)
        prime, prime_tail = _prime_term(g, n_max_used)
        arith = pole + arch + prime
    with mp.workdps(dps):
        return {
            "pole_term": +pole,
            "arch_term": +arch,
            "prime_term": +prime,
            "prime_tail_bound": +prime_tail,
            "arithmetic_side": +arith,
            "n_max": n_max_used,
        }


def explicit_formula_sides(
    h, g, gamma_max: float = 10000.0, n_max: int | None = None, dps: int = 25
) -> dict:
    """Evaluate both sides of the Riemann–Weil explicit formula independently.

    Zero side: Σ_{|γ| <= gamma_max} h(γ) over ordinates of both signs, from
    cached verified zeros (mpf precision for the first 1000, float64 RS-scan
    beyond — see :func:`zeta.statistics.zero_ordinates` for the completeness
    certificates).  Arithmetic side: pole + archimedean + prime terms in the
    convention of the module docstring, no zeros used anywhere.

    Returns a dict:

    ``zero_side``             Σ h(γ) + h(-γ) over 0 < γ <= gamma_max
    ``zero_side_tail_bound``  bound on everything discarded (see docstring;
                              includes early-exit slack)
    ``zero_side_tail_estimate``  density-based estimate of the same tail
                              (None without an ``env_avg`` hint)
    ``pole_term``             h(i/2) + h(-i/2)
    ``arch_term``             (1/2π)∫ h(r)[Re ψ(1/4+ir/2) - log π] dr
    ``prime_term``            -2 Σ_{n<=n_max} Λ(n) n^{-1/2} g(log n)  (signed)
    ``prime_tail_bound``      bound on the discarded prime tail (0 for Fejér)
    ``arithmetic_side``       pole_term + arch_term + prime_term
    ``agreement``             |zero - arithmetic| / max(|zero|, |arithmetic|)
    ``abs_diff``              |zero - arithmetic|
    ``n_zeros_used``, ``n_max``, ``gamma_max``   bookkeeping

    The residual ``abs_diff`` should be explained by ``zero_side_tail_bound``
    + ``prime_tail_bound`` + quadrature noise at the working precision; the
    tests assert exactly that.
    """
    pieces = _arithmetic_pieces(h, g, n_max, dps)
    with mp.workdps(dps + 10):
        zs, used, slack = _zero_side(h, float(gamma_max), dps)
        tail = _zero_tail_bound(h, float(gamma_max), dps) + slack
        est = _zero_tail_estimate(h, float(gamma_max))
        arith = pieces["arithmetic_side"]
        diff = abs(zs - arith)
        scale = max(abs(zs), abs(arith))
        agreement = diff / scale if scale > 0 else mp.mpf(0)
    with mp.workdps(dps):
        out = {
            "zero_side": +zs,
            "zero_side_tail_bound": +tail,
            "zero_side_tail_estimate": None if est is None else +est,
            "agreement": +agreement,
            "abs_diff": +diff,
            "n_zeros_used": used,
            "gamma_max": float(gamma_max),
        }
    out.update(pieces)
    return out


def weil_functional(h, g, n_max: int | None = None, dps: int = 25) -> mpf:
    """THE object: Weil's functional W(h), evaluated from the arithmetic side.

    W(h) = h(i/2) + h(-i/2)
         + (1/2π)∫ h(r)[Re ψ(1/4+ir/2) - log π] dr
         - 2 Σ_{n>=2} Λ(n) n^{-1/2} g(log n)

    — no zeros enter the computation; by the explicit formula (self-validated
    in this module) W(h) = Σ_ρ h(γ_ρ) over all nontrivial zeros.

    **Weil positivity criterion** (Weil 1952; refined 1972): RH holds if and
    only if W(h) >= 0 for every admissible h of positive type — h = |f̂|² on
    the real axis (g a self-correlation f ⋆ f~) with f ranging over a suitable
    dense class of test functions.  *Hedge*: the precise admissible class
    (compactly supported smooth f vs. analytic-in-a-strip formulations)
    varies between statements of the theorem; all pairs constructed by this
    module are admissible under any of the usual formulations.  See
    ``docs/07-equivalences-and-criteria.md`` §7.  A computed W(h) > 0 reflects
    the verified zeros and is not evidence for RH (``docs/08``); a computed
    W(h) < 0 beyond the numerical noise floor would, per the house rule,
    almost certainly be a bug — but a *true* such value would disprove RH.

    This is the *accurate* W(h).  For an enclosure-carrying one (Gaussian and
    Fejér pairs, Arb backend) see :func:`zeta.rigor.enclose_weil_functional`.
    """
    return _arithmetic_pieces(h, g, n_max, dps)["arithmetic_side"]


_FAMILIES = {
    "gaussian": (lambda p: gaussian_pair(p), (0.005, 0.2), "log"),
    "fejer": (lambda p: fejer_pair(p), (0.75, 3.0), "linear"),
    "autocorrelation": (
        lambda p: autocorrelation_pair([1, -1], spacing=2.0, sigma=p),
        (0.15, 0.45),
        "linear",
    ),
}


def positivity_probe(
    family="gaussian",
    n_points: int = 5,
    param_range: tuple[float, float] | None = None,
    dps: int = 20,
    n_max: int | None = None,
) -> list[dict]:
    """Scan a parametrised family of positive-type pairs; report W and margin.

    ``family`` is ``'gaussian'`` (h = e^{-ar²}, a log-spaced), ``'fejer'``
    (h = (sin br/br)², b linear), ``'autocorrelation'`` (two-bump |f̂|² with
    h(0) = 0, σ linear), or any callable param -> (h, g) built with hints
    (then ``param_range`` is required).

    Each entry: ``param``, ``W`` (the functional, arithmetic side),
    ``scale`` = |pole| + |arch| + |prime| (size of what cancels), ``margin``
    = W/scale (dimensionless distance from 0), ``noise_floor`` (10^-(dps-6)
    · scale, a conservative estimate of quadrature/cancellation noise),
    ``positive`` = W > noise_floor, and ``dps_used``.  When W hides below the
    noise floor at the requested dps (the interesting near-tight members),
    the precision escalates automatically (+15 digits at a time, up to 50)
    until the sign is *resolved above that floor* — W for e.g. the Gaussian
    a = 0.2 member is ~9e-18 out of pieces of size ~2, and still comes back
    positive.  Note the word: ``noise_floor`` is a conservative *estimate*, so
    ``positive`` is an ordinary floating-point verdict, not a ball-arithmetic
    certificate.  :func:`zeta.rigor.enclose_weil_functional` is the certified
    version of the same quantity (and confirms that a = 0.2 sign).  The
    minimum-margin entry is flagged ``is_tightest`` — for these families that
    is always the member whose h is most concentrated inside the zero-free
    gap (-γ₁, γ₁).
    """
    if callable(family):
        make, rng, scale_kind, name = family, param_range, "linear", "custom"
        if rng is None:
            raise ValueError("param_range is required for a callable family")
    else:
        try:
            make, default_rng, scale_kind = _FAMILIES[family]
        except KeyError:
            raise ValueError(
                f"unknown family {family!r}: expected one of "
                f"{sorted(_FAMILIES)} or a callable"
            ) from None
        rng, name = param_range or default_rng, family
    lo, hi = float(rng[0]), float(rng[1])
    if scale_kind == "log":
        params = list(np.geomspace(lo, hi, n_points))
    else:
        params = list(np.linspace(lo, hi, n_points))
    out = []
    for p in params:
        h, g = make(p)
        dps_used = dps
        while True:
            pieces = _arithmetic_pieces(h, g, n_max, dps_used)
            with mp.workdps(dps_used):
                W = pieces["arithmetic_side"]
                scale = (
                    abs(pieces["pole_term"])
                    + abs(pieces["arch_term"])
                    + abs(pieces["prime_term"])
                )
                noise = mp.mpf(10) ** (-(dps_used - 6)) * scale
            if abs(W) > noise or dps_used >= 50:
                break
            dps_used = min(dps_used + 15, 50)  # escalate: lift W above the floor
        with mp.workdps(dps_used):
            out.append(
                {
                    "family": name,
                    "param": float(p),
                    "W": W,
                    "scale": +scale,
                    "margin": +(W / scale),
                    "noise_floor": +noise,
                    "positive": bool(W > noise),
                    "dps_used": dps_used,
                    "is_tightest": False,
                }
            )
    min(out, key=lambda d: d["margin"])["is_tightest"] = True
    return out


def near_tightness_report(
    gaussian_a: Sequence[float] = (0.02, 0.05, 0.08, 0.12, 0.16, 0.2),
    fejer_b: Sequence[float] = (1.0, 1.5, 2.0, 2.5),
    dps: int = 40,
    include_fejer: bool = True,
) -> dict:
    """Which test functions bring W closest to 0, and what controls it.

    Research-reconnaissance output.  Findings this function measures (and the
    tests pin):

    * Along the Gaussian family the margin collapses *exponentially*:
      log W(a) has slope ≈ -γ₁² = -199.79… in a, because
      W = 2h(γ₁)(1 + o(1)) = 2e^{-aγ₁²}(1+o(1)) as h concentrates on the
      zero-free gap (-γ₁, γ₁).  The report returns the fitted slope, the
      prediction -γ₁², and the share of the zero side carried by γ₁ alone.
    * Along the Fejér family W·b² tends to (a b-oscillating neighbourhood
      of) Σ_γ γ⁻² ≈ 0.02310 — of which the single lowest zero contributes
      1/γ₁² ≈ 22% (measured: 0.2179), and whose per-b share oscillates as
      sin²(bγ₁) — b = 2 nearly annihilates γ₁ since 2γ₁ ≈ 9π.  Tightness
      is again a story about γ₁.
    * The arithmetic side keeps agreeing with 2Σ_{γ>0}h(γ) even where W is
      ~10⁻¹⁷ built from pieces of size ~2 (``max_cancellation_digits``) —
      the explicit formula holds through the entire collapse, which is
      exactly what makes W a *functional-analytic* probe of the lowest zero
      rather than a numerical accident.

    Honest scope: the infimum 0 is approached, never attained; positivity of
    every computed W reflects the verified zeros and is not evidence for RH.
    """
    gamma1 = mp.mpf(GAMMA1)
    gauss = []
    for a in gaussian_a:
        h, g = gaussian_pair(a)
        pieces = _arithmetic_pieces(h, g, None, dps)
        with mp.workdps(dps + 10):
            W = pieces["arithmetic_side"]
            zs, _, _ = _zero_side(h, 1400.0, dps)
            share = 2 * h(gamma1) / zs if zs > 0 else mp.mpf("nan")
            scale = abs(pieces["pole_term"]) + abs(pieces["arch_term"]) + abs(
                pieces["prime_term"]
            )
            gauss.append(
                {
                    "a": float(a),
                    "W": +W,
                    "zero_side": +zs,
                    "rel_agreement": float(abs(W - zs) / zs) if zs > 0 else None,
                    "gamma1_share": float(share),
                    "cancellation_digits": float(mp.log10(scale / abs(W)))
                    if W != 0
                    else float("inf"),
                }
            )
    # least-squares slope of ln W against a
    xs = np.array([d["a"] for d in gauss])
    ys = np.array([float(mp.log(abs(d["W"]))) for d in gauss])
    slope = float(np.polyfit(xs, ys, 1)[0])

    fejer = []
    sum_inv_gamma_sq = None
    if include_fejer:
        for b in fejer_b:
            h, g = fejer_pair(b)
            res = explicit_formula_sides(h, g, gamma_max=10000.0, dps=20)
            with mp.workdps(20):
                W = res["arithmetic_side"]
                zs = res["zero_side"]
                hb = h(gamma1)
                fejer.append(
                    {
                        "b": float(b),
                        "W": +W,
                        "W_times_b2": float(W * b * b),
                        "gamma1_share": float(2 * hb / zs) if zs > 0 else None,
                    }
                )
        floats = _float_zeros(10000.0)
        sum_inv_gamma_sq = float(np.sum(1.0 / floats**2))

    tight = min(gauss, key=lambda d: abs(d["W"]))
    report = {
        "gamma1": float(gamma1),
        "gaussian_scan": gauss,
        "gaussian_log_margin_slope": slope,
        "predicted_slope": -float(gamma1**2),
        "slope_rel_error": abs(slope / float(gamma1**2) + 1.0),
        "gamma1_share_at_tightest": tight["gamma1_share"],
        "max_cancellation_digits": max(d["cancellation_digits"] for d in gauss),
        "tightest_member": {"family": "gaussian", "a": tight["a"], "W": tight["W"]},
        "fejer_scan": fejer,
        "sum_inv_gamma_sq_partial": sum_inv_gamma_sq,
        "gamma1_share_of_sum": (
            float(1.0 / GAMMA1**2 / sum_inv_gamma_sq) if sum_inv_gamma_sq else None
        ),
        "narrative": (
            "The infimum of W over each family is 0, approached as the test "
            "function concentrates on the zero-free gap (-gamma1, gamma1): "
            "for Gaussians the margin collapses like 2*exp(-a*gamma1^2) "
            "(fitted log-slope matches -gamma1^2), and for Fejer W*b^2 "
            "hovers around sum 1/gamma^2, ~22% of which is the single "
            "lowest zero. The lowest zero gamma1 = 14.1347... is the "
            "controlling feature in both regimes. Positivity of every "
            "computed W reflects the computationally verified zeros on the "
            "line; per docs/08 it is not evidence for RH."
        ),
    }
    return report
