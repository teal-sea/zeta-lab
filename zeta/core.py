"""Foundational special functions for the Riemann zeta laboratory.

This module is the bedrock of the package.  Everything else (zero hunting,
explicit formulae, heat-flow experiments) imports from here.

The guiding narrative, in the order the functions appear:

1.  **Dirichlet series and its alternating cousin.**
    ζ(s) = Σ_{n≥1} n^{-s}  converges only for Re(s) > 1.
    η(s) = Σ_{n≥1} (-1)^{n-1} n^{-s}  converges (conditionally) for Re(s) > 0,
    and  ζ(s) = η(s) / (1 − 2^{1−s})  pushes us into the critical strip.

2.  **Euler–Maclaurin.**  A hand-rolled continuation of ζ to the whole plane,
    obtained by comparing the Riemann *sum* Σ n^{-s} with the *integral*
    ∫ x^{-s} dx and correcting with Bernoulli numbers.  This is the
    "Riemann sums ↔ zeta" story made explicit, and it is what actually
    produces ζ(−1) = −1/12 and ζ(0) = −1/2 from finite arithmetic.

3.  **Theta functions.**  θ(x) = Σ_{n∈ℤ} e^{−π n² x} obeys the modular
    relation θ(1/x) = √x · θ(x).  Its heat-kernel avatar on the circle ℝ/ℤ,
    θ_heat(x,t) = Σ_n e^{−4π²n²t} e^{2πinx}, is literally the fundamental
    solution of ∂_t u = ∂_x² u, and the modular relation is Poisson
    summation, i.e. the equality of the spectral and real-space forms.

4.  **Mellin transforms.**  Γ(s)ζ(s) = ∫_0^∞ x^{s−1}/(e^x−1) dx, and, the
    deep one: Riemann's

        π^{−s/2} Γ(s/2) ζ(s) = 1/(s(s−1)) + ∫_1^∞ (x^{s/2−1} + x^{(1−s)/2−1}) ω(x) dx

    with ω(x) = Σ_{n≥1} e^{−π n² x} = (θ(x) − 1)/2.  The right-hand side is
    *visibly* invariant under s ↦ 1 − s.  That invariance IS the functional
    equation, and it descends directly from the theta modular relation.

5.  **ξ, Ξ, and Hardy's Z.**  The completed zeta ξ(s) = ½s(s−1)π^{−s/2}Γ(s/2)ζ(s)
    is entire and satisfies ξ(s) = ξ(1−s).  Ξ(t) = ξ(½+it) is real for real t.
    Hardy's Z(t) = e^{iϑ(t)} ζ(½+it) is real for real t and |Z(t)| = |ζ(½+it)|,
    so the zeros on the critical line are exactly the real sign changes of Z.

Conventions
-----------
Every public function takes an optional ``dps`` (decimal places) argument and
computes at ``dps`` plus an internal guard, returning a result rounded to
``dps``.  No global mpmath state is left modified: all precision changes go
through ``mpmath.mp.workdps`` / ``mpmath.mp.workprec``.
"""

from __future__ import annotations

import json
import math
import os
from functools import lru_cache

import mpmath
from mpmath import mp

__all__ = [
    "DPS_DEFAULT",
    "DATA_DIR",
    # --- zeta and friends -------------------------------------------------
    "zeta",
    "eta",
    "zeta_via_eta",
    "zeta_euler_maclaurin",
    "euler_maclaurin_suggest_N",
    # --- theta ------------------------------------------------------------
    "theta",
    "omega",
    "theta_modular_defect",
    "theta_heat",
    "theta_heat_gaussian",
    "theta_heat_poisson_defect",
    "theta_heat_residual",
    "HEAT_DIFFUSIVITY",
    # --- completed zeta ---------------------------------------------------
    "xi",
    "Xi",
    "completed_zeta",
    "functional_equation_defect",
    # --- Riemann-Siegel / Hardy ------------------------------------------
    "rs_theta",
    "Z",
    "hardy_Z_sign_changes",
    # --- Mellin -----------------------------------------------------------
    "mellin_gamma_zeta",
    "mellin_gamma_zeta_defect",
    "theta_mellin_xi",
    "theta_mellin_xi_defect",
]

#: Default working precision (decimal digits) for the whole laboratory.
DPS_DEFAULT: int = 30

#: Extra guard digits carried internally and discarded before returning.
_GUARD: int = 10

#: Cache directory for expensive scans.
DATA_DIR: str = os.path.join(
    os.path.dirname(os.path.dirname(os.path.abspath(__file__))), "data"
)


# ---------------------------------------------------------------------------
# small helpers
# ---------------------------------------------------------------------------

def _num(s):
    """Coerce ``s`` (int/float/complex/str/mpf/mpc) to an mpmath number."""
    return mpmath.mpmathify(s)


def _shrink(value, dps: int):
    """Round an mpf/mpc computed at high precision down to ``dps`` digits."""
    with mp.workdps(dps):
        return +value


def _is_real(s) -> bool:
    """True if ``s`` is real (an mpf, or an mpc whose imaginary part vanishes)."""
    return mp.im(s) == 0


def _real_arg(v, label: str):
    """Coerce ``v`` to an ``mpf``, accepting an ``mpc`` only when Im(v) == 0.

    Every public function of a *real* variable funnels its argument through
    here, so that genuinely complex input raises ``ValueError``, the
    documented contract, rather than the ``TypeError`` that a bare
    ``mp.mpf(mpc(...))`` throws, and so that an ``mpc`` with exactly zero
    imaginary part (a common by-product of upstream complex arithmetic) is
    accepted rather than crashing.
    """
    v = mpmath.mpmathify(v)
    if mp.im(v) != 0:
        raise ValueError(f"{label} expects a real argument, got {v}")
    return mp.mpf(mp.re(v))


def _real_part_checked(value, dps: int, tol_digits: int, label: str):
    """Return Re(value) after verifying the imaginary part is pure round-off.

    ``value`` is a quantity that is real *by theory* (Ξ(t), Z(t)) but arrives
    from complex arithmetic carrying a numerical imaginary residue.  We require

        |Im value| < 10^{−dps+tol_digits} · max(|Re value|, 1)

    and raise otherwise.  A failure means the working precision was too low,
    not that the mathematics is wrong.  This is a plain ``raise`` rather than an
    ``assert`` so that it survives ``python -O``.
    """
    re, im = mp.re(value), mp.im(value)
    scale = max(abs(re), mp.mpf(1))
    tol = mp.mpf(10) ** (-dps + tol_digits) * scale
    if abs(im) >= tol:
        raise ValueError(
            f"{label}: imaginary residue {mp.nstr(im, 8)} exceeds {mp.nstr(tol, 8)}; "
            "increase dps"
        )
    return re


def _is_trivial_zero(s) -> bool:
    """True if s ∈ {−2, −4, −6, …}, the trivial zeros of ζ.

    These are exactly the points where Γ(s/2), equivalently Γ(s/2+1), has a
    pole that is cancelled by a zero of ζ, so ξ and Λ are perfectly finite there
    while the naive product ``gamma(...) * zeta(...)`` cannot be evaluated.
    """
    if not _is_real(s):
        return False
    r = mp.re(s)
    if r > -1 or r != mp.floor(r):
        return False
    return int(r) % 2 == 0


def _cauchy_mean(f, s0, radius, n_points: int):
    """Value of an analytic ``f`` at ``s0`` as a mean over a circle:

        f(s₀) = (1/2πi) ∮_{|z−s₀|=r} f(z)/(z−s₀) dz
              = (1/2π) ∫_0^{2π} f(s₀ + r e^{iθ}) dθ
              ≈ (1/N) Σ_{j=0}^{N−1} f(s₀ + r e^{2πij/N}).

    The equispaced trapezoid rule applied to a periodic analytic integrand
    converges geometrically: the error is exactly Σ_{k≥1} a_{kN} r^{kN}, where
    a_n are the Taylor coefficients of f at s₀.  For entire f (ξ is entire) that
    is spectral accuracy, measured below the round-off floor with N ≈ 1.5·dps.

    Note that ``f`` is never called at ``s₀`` itself, only on a circle around
    it, which is what makes this a legitimate way to evaluate a *removable*
    singularity.
    """
    total = mp.mpc(0)
    for j in range(n_points):
        total += f(s0 + radius * mp.expjpi(mp.mpf(2 * j) / n_points))
    return total / n_points


def _removable(f, s0, dps: int, radius=None):
    """Evaluate ``f`` at a removable singularity ``s0`` via :func:`_cauchy_mean`.

    ``radius`` defaults to ½, which keeps the sample circle clear of the
    neighbouring exceptional points (consecutive trivial zeros are 2 apart), and
    the node count grows with both the requested precision and |s₀|, ξ grows
    like exp(|s| log|s| / 2), so a circle further out needs more nodes.
    """
    r = mp.mpf(1) / 2 if radius is None else mp.mpf(radius)
    n_points = max(48, int(math.ceil(1.5 * dps)) + int(abs(float(mp.re(s0)))))
    value = _cauchy_mean(f, mp.mpmathify(s0), r, n_points)
    return mp.re(value) if _is_real(s0) else value


# ---------------------------------------------------------------------------
# 1.  zeta, eta
# ---------------------------------------------------------------------------

def zeta(s, dps: int = DPS_DEFAULT):
    """Riemann zeta function ζ(s), valid on the whole plane (pole at s = 1).

        ζ(s) = Σ_{n≥1} n^{-s}   for Re(s) > 1,  continued elsewhere.

    This is the *workhorse* used throughout the package; it delegates to
    mpmath's Riemann–Siegel / Euler–Maclaurin implementation, which is fast
    and rigorously tested.  The hand-rolled continuation that shows the actual
    machinery is :func:`zeta_euler_maclaurin`, the two agree to full
    precision, and the test-suite checks that.

    Parameters
    ----------
    s : real or complex (anything ``mpmath.mpmathify`` accepts)
    dps : decimal digits of the returned value.

    Returns
    -------
    mpf if ``s`` is real, mpc if ``s`` is complex.
    """
    with mp.workdps(dps + _GUARD):
        value = mp.zeta(_num(s))
    return _shrink(value, dps)


@lru_cache(maxsize=64)
def _borwein_d(n: int, prec: int) -> tuple:
    """Borwein's d_k coefficients, cached by (n, binary precision).

        d_k = n · Σ_{i=0}^{k}  (n+i−1)! · 4^i / ( (n−i)! · (2i)! )

    Computed with a running ratio so the whole vector costs O(n) big-float
    operations rather than O(n) factorial evaluations:

        term_i / term_{i−1} = 4 (n+i−1)(n−i+1) / ((2i)(2i−1)),   term_0 = 1/n.
    """
    with mp.workprec(prec):
        out = []
        acc = mp.mpf(0)
        term = mp.mpf(1) / n          # i = 0:  (n-1)!/n! = 1/n
        for i in range(0, n + 1):
            if i > 0:
                term = term * 4 * (n + i - 1) * (n - i + 1) / (mp.mpf(2 * i) * (2 * i - 1))
            acc += term
            out.append(n * acc)
        return tuple(out)


#: Digits gained per Borwein term where his bound is proven, log10(3+√8).
_BORWEIN_RATE: float = math.log10(3 + math.sqrt(8))  # ≈ 0.7655

#: Observed digits gained per term to the *left* of Re(s) = 1/2, where Borwein's
#: bound no longer applies.  Measured from |η_n − η| at n = 58…800 for
#: s = −6 … −20 (see the docstring of :func:`eta`).
_BORWEIN_RATE_LEFT: float = 0.5

#: Observed extra digits of error per unit of (1/2 − Re s), same measurements.
_BORWEIN_LEFT_PENALTY: float = 3.0


def _eta_workload(s, dps: int) -> tuple[int, int]:
    """Choose (n_terms, working dps) for Borwein's alternating-series algorithm.

    Borwein (Algorithm 2) bounds the error of the n-term approximation by

        |err| ≤ 3 / (3 + √8)^n · (1 + 2|y|) e^{π|y|/2} / |Γ(s)| ,   s = x + iy,

    **for Re(s) ≥ 1/2**.  We solve that for n (log10(3+√8) ≈ 0.7655, i.e. ~0.77
    digits gained per term) and carry the same number of guard digits, because
    the partial sums themselves are large and cancel.

    Two corrections that the naive reading of the bound gets wrong:

    1.  ``1/|Γ(s)|`` must be bounded, not evaluated, for Re(s) ≤ 0: at the poles
        of Γ the reciprocal *vanishes*, which would make the bound claim zero
        error.  We use the reflection formula
        1/|Γ(s)| = |sin πs|·|Γ(1−s)|/π ≤ |Γ(1−s)|/π,
        which is finite and continuous across the poles.
    2.  Left of Re(s) = 1/2 the bound is simply not proven, and it is not true:
        measured shortfall grows by ≈ 3 digits per unit of (1/2 − Re s) and the
        observed convergence rate drops from 0.77 to ≈ 0.5 digits per term.
        Both constants are applied here.  (Without them, η(−20) came out as
        6.7e+8 instead of 0.)
    """
    s = _num(s)
    x = float(mp.re(s))
    y = float(abs(mp.im(s)))
    with mp.workdps(30):
        if x > 0:
            g = abs(mp.gamma(s))
            inv_gamma = float(mp.log10(1 / g)) if g > 0 else 0.0
        else:
            # |sin(pi s)| <= 1 in the reflection formula: a finite upper bound
            # for 1/|Gamma(s)| that stays valid at the poles of Gamma.
            inv_gamma = float(mp.log10(abs(mp.gamma(1 - s)) / mp.pi))
    blowup = max(
        math.log10(1 + 2 * y) + y * (math.pi / 2) / math.log(10) + inv_gamma, 0.0
    )
    if x < 0.5:
        blowup += _BORWEIN_LEFT_PENALTY * (0.5 - x)
        rate = _BORWEIN_RATE_LEFT
    else:
        rate = _BORWEIN_RATE
    target = dps + _GUARD + blowup
    n = int(math.ceil(target / rate)) + 5
    work = int(math.ceil(target)) + 10
    return n, work


def eta(s, dps: int = DPS_DEFAULT):
    """Dirichlet eta (alternating zeta) function

        η(s) = Σ_{n≥1} (−1)^{n−1} n^{-s} = 1 − 2^{-s} + 3^{-s} − …

    The naive series converges only for Re(s) > 0 and then only conditionally,
    so we use **Borwein's algorithm**: with

        d_k = n · Σ_{i=0}^{k} (n+i−1)! 4^i / ((n−i)! (2i)!),

        η(s) ≈ −(1/d_n) · Σ_{k=0}^{n−1} (−1)^k (d_k − d_n) / (k+1)^s ,

    whose error decays like (3+√8)^{−n} ≈ 5.83^{−n}, i.e. ~0.77 digits per
    term.  The number of terms and the working precision are chosen from
    Borwein's error bound plus two empirical corrections (see
    :func:`_eta_workload`).

    **Honest range.**  Borwein proves his bound only for Re(s) ≥ 1/2.  Measured
    error of this implementation against (1 − 2^{1−s})ζ(s) at ``dps=30``:

    Worst case over the grid Re s ∈ [−20.5, 3] × Im s ∈ {0, 1, 10, 30, 50}:
    **8.9e-32** (attained at s = −20.5 + 30i).  On the critical line the term
    count grows with the height, n = 60 at t = 1, n = 328 at t = 150, and the
    error stays ≤ 5.4e-32 out to t = 150.

    The left half plane is the part that needed repair: the unpatched workload
    estimator returned 1.2e-15 for η(−10) and **−6.7e+08 for η(−20)**, both of
    which are 0.

    The required guard digits grow like e^{π|Im s|} (≈ 1.36 digits per unit of
    |Im s|), so this is a *small-|t|* tool, usable to |Im s| ≈ 150, hopeless at
    |Im s| = 10⁴.  For large heights use :func:`zeta` / :func:`Z`.
    """
    s = _num(s)
    n, work = _eta_workload(s, dps)
    with mp.workdps(work):
        s_w = _num(s)
        d = _borwein_d(n, mp.prec)
        dn = d[n]
        total = mp.mpf(0)
        for k in range(0, n):
            term = (d[k] - dn) / mp.power(k + 1, s_w)
            total = total - term if (k & 1) else total + term
        value = -total / dn
    return _shrink(value, dps)


def zeta_via_eta(s, dps: int = DPS_DEFAULT):
    """ζ(s) recovered from the alternating series:

        η(s) = (1 − 2^{1−s}) ζ(s)   ⟹   ζ(s) = η(s) / (1 − 2^{1−s}).

    Proof of the identity (Re(s) > 1, then continue):
        Σ (−1)^{n−1} n^{-s} = Σ n^{-s} − 2 Σ_{n even} n^{-s}
                            = ζ(s) − 2·2^{-s} ζ(s) = (1 − 2^{1−s}) ζ(s).

    This is the cheapest honest continuation of ζ into the critical strip: the
    left-hand side converges for Re(s) > 0, so the right-hand side *defines* ζ
    there.

    **The zeros of the denominator.**  1 − 2^{1−s} vanishes at
    s = 1 + 2πik/log 2 (k ∈ ℤ).  Only k = 0 is a pole of ζ; at the k ≠ 0
    points ζ is perfectly finite and η has a matching zero, so the quotient
    has a *removable* singularity, but a numerically treacherous one, because
    Borwein's algorithm computes η to a fixed **absolute** accuracy while both
    η(s) and the denominator are O(|s − s_k|).  Unguarded, an s within 10⁻⁴¹
    of s_k returned ~10⁻⁶ instead of ζ(s) ≈ 1.35 + 0.11i, with no warning.
    The guard digits now grow with −log₁₀|1 − 2^{1−s}|, so the quotient stays
    accurate to ``dps`` arbitrarily close to the k ≠ 0 zeros (measured:
    rel. error 3e-33 at the 45-digit rounding of s = 1 + 2πi/log 2).

    Raises ``ZeroDivisionError`` if 1 − 2^{1−s} evaluates to exactly zero
    (in exact arithmetic that means s = 1, the genuine pole) or if s sits so
    close to a denominator zero that the required guard digits exceed
    max(1000, 20·dps).
    """
    s = _num(s)
    # How close is s to a zero of 1 - 2^{1-s}?  Iterate because the denominator
    # itself needs |denom| >> 10^{-work} to be computed with any relative
    # accuracy: each pass recomputes it with the guard digits the previous
    # pass discovered were needed, until the estimate stops growing.
    extra = 0
    for _ in range(64):
        with mp.workdps(dps + _GUARD + extra):
            s_w = _num(s)
            denom = 1 - mp.power(2, 1 - s_w)
        if denom == 0:
            raise ZeroDivisionError(
                f"1 - 2^(1-s) vanishes at s={s}; use zeta() or zeta_euler_maclaurin()"
            )
        with mp.workdps(30):
            need = int(mp.ceil(-mp.log10(abs(denom)))) + 5 if abs(denom) < 1 else 0
        if need > max(1000, 20 * dps):
            raise ZeroDivisionError(
                f"s={s} is too close to a zero of 1 - 2^(1-s) "
                f"(would need {need} guard digits); use zeta()"
            )
        if need <= extra:
            break
        extra = need
    with mp.workdps(dps + _GUARD + extra):
        s_w = _num(s)
        denom = 1 - mp.power(2, 1 - s_w)
        value = eta(s_w, dps + _GUARD + extra) / denom
    return _shrink(value, dps)


def euler_maclaurin_suggest_N(s, dps: int = DPS_DEFAULT, M: int = 20) -> int:
    """A safe truncation point N for :func:`zeta_euler_maclaurin`.

    The Euler–Maclaurin remainder behaves like
    |B_{2M}/(2M)!|·|(s)_{2M−1}|·N^{−σ−2M+1}; the series is genuinely
    asymptotic and only starts to help once N ≳ |s|.  We take
    N = max(2M, ⌈|s|⌉+2, ⌈dps/2⌉).
    """
    s = _num(s)
    return int(max(2 * M, math.ceil(float(abs(s))) + 2, math.ceil(dps / 2)))


def zeta_euler_maclaurin(s, N: int = 20, M: int = 20, dps: int = DPS_DEFAULT):
    """Hand-rolled Euler–Maclaurin continuation of ζ to the whole s-plane.

        ζ(s) =  Σ_{n=1}^{N−1} n^{-s}
              +  N^{1−s}/(s−1)
              +  N^{-s}/2
              +  Σ_{k=1}^{M}  B_{2k}/(2k)! · (s)_{2k−1} · N^{−s−2k+1}
              +  error,

    where (s)_m = s(s+1)···(s+m−1) is the rising factorial (Pochhammer symbol)
    and B_{2k} are the Bernoulli numbers.

    **Where it comes from.**  Euler–Maclaurin compares a Riemann *sum* with the
    corresponding *integral*:

        Σ_{n=N}^{∞} f(n) = ∫_N^∞ f(x) dx + f(N)/2 − Σ_k B_{2k}/(2k)! f^{(2k−1)}(N).

    Apply it to f(x) = x^{-s}.  Then ∫_N^∞ x^{-s} dx = N^{1−s}/(s−1) supplies
    the single pole at s = 1, and f^{(2k−1)}(N) = −(s)_{2k−1} N^{−s−2k+1}.
    Every term on the right is entire in s apart from that one explicit pole,
    so this expression *is* the analytic continuation, manufactured out of
    finite arithmetic, with no contour integral in sight.

    Landmarks it reproduces **exactly** (all Pochhammer factors with k ≥ 2
    vanish, because (s)_{2k−1} then contains the factor (s+1) = 0 resp. s = 0):

        s = −1 :  Σ_{n<N} n − N²/2 + N/2 + B₂/2!·(−1)·N⁰  =  −1/12
        s =  0 :  (N−1) − N + 1/2                          =  −1/2

    Parameters
    ----------
    s : point of evaluation (s ≠ 1).
    N : where the explicit Dirichlet sum is cut off.  Accuracy needs N ≳ |Im s|;
        see :func:`euler_maclaurin_suggest_N`.
    M : number of Bernoulli correction terms.  The series is asymptotic, so
        more is not unconditionally better; M ≈ 20 with N ≈ 20 delivers ≳ 30
        digits for |s| ≲ 20.
    dps : digits of the returned value.

    **Cancellation guard.**  For Re(s) = σ < 1 the intermediate quantities are
    huge while the answer is small: the truncated sum and the integral term
    N^{1−s}/(s−1) both grow like N^{1−σ} and cancel almost completely (at
    s = −19.5, N = 40 the intermediates are ~10³², the answer is 33.2).  A
    fixed number of guard digits therefore loses ⌈(1−σ)·log₁₀N⌉ digits of the
    result, measured before the fix: rel. error 1.7e-26 at s = −15.5 (N=20)
    and 1.2e-17 at s = −19.5 (N=40) for dps = 30.  The working precision now
    carries those extra digits explicitly.  Measured after the fix at dps=30:
    ≤ 4.6e-32 relative at s = −10.5, −15.5, −19.5 and −12+5i with the
    suggested N (=40); the landmarks s = −1, 0 remain exact.  The guard fixes
    *round-off*, not the asymptotics: N ≳ |s| is still required (at s = −19.5
    with N = 20 the remaining 3.6e-27 is the genuine series remainder).
    """
    s = _num(s)
    if N < 2:
        raise ValueError("N must be at least 2")
    if M < 0:
        raise ValueError("M must be non-negative")
    sigma = float(mp.re(s))
    #: digits destroyed by the N^{1-σ} cancellation between sum and integral
    cancel = int(math.ceil((1.0 - sigma) * math.log10(N))) if sigma < 1 else 0
    with mp.workdps(dps + _GUARD + 5 + cancel):
        s_w = _num(s)
        if s_w == 1:
            raise ValueError("zeta has a pole at s = 1")

        # (a) the truncated Dirichlet sum  Σ_{n=1}^{N-1} n^{-s}
        total = mp.fsum(mp.power(n, -s_w) for n in range(1, N))

        # (b) the integral  ∫_N^∞ x^{-s} dx = N^{1-s}/(s-1)   (carries the pole)
        total += mp.power(N, 1 - s_w) / (s_w - 1)

        # (c) the trapezoid half-term  f(N)/2
        total += mp.power(N, -s_w) / 2

        # (d) Bernoulli corrections  B_{2k}/(2k)! · (s)_{2k-1} · N^{-s-2k+1}
        poch = mp.mpf(1)  # will hold (s)_{2k-1}
        for k in range(1, M + 1):
            if k == 1:
                poch = s_w                                   # (s)_1 = s
            else:
                poch = poch * (s_w + 2 * k - 3) * (s_w + 2 * k - 2)
            total += (
                mp.bernoulli(2 * k)
                / mp.factorial(2 * k)
                * poch
                * mp.power(N, -s_w - 2 * k + 1)
            )
        value = total
    return _shrink(value, dps)


# ---------------------------------------------------------------------------
# 2.  Theta functions
# ---------------------------------------------------------------------------

def _theta_terms(x, dps: int) -> int:
    """Smallest n with e^{−π n² x} < 10^{−dps−5}."""
    xf = float(x)
    if xf <= 0:
        raise ValueError("theta requires x > 0")
    need = (dps + 5) * math.log(10) / math.pi / xf
    return max(1, int(math.ceil(math.sqrt(max(need, 1.0)))) + 2)


def theta(x, dps: int = DPS_DEFAULT, terms: int | None = None):
    """Jacobi theta (θ₃-type) function on the positive real axis:

        θ(x) = Σ_{n∈ℤ} e^{−π n² x} = 1 + 2 Σ_{n≥1} e^{−π n² x},   x > 0.

    Summed **directly**, term by term, deliberately *not* via the modular
    relation, so that :func:`theta_modular_defect` is a genuine numerical test
    rather than a tautology.  The term count is chosen so the first dropped
    term is below 10^{−dps−5}; for x ≥ 10⁻⁴ that is at most a few hundred
    terms, so honesty here is cheap.
    """
    with mp.workdps(dps + _GUARD):
        xv = _real_arg(x, "theta")
        if xv <= 0:
            raise ValueError("theta requires x > 0")
        n_max = terms if terms is not None else _theta_terms(xv, dps + _GUARD)
        total = mp.mpf(1)
        for n in range(1, n_max + 1):
            total += 2 * mp.exp(-mp.pi * n * n * xv)
        value = total
    return _shrink(value, dps)


def omega(x, dps: int = DPS_DEFAULT, terms: int | None = None):
    """Riemann's ω(x) = Σ_{n≥1} e^{−π n² x} = (θ(x) − 1)/2,  x > 0.

    The modular relation θ(1/x) = √x θ(x) becomes

        2ω(1/x) + 1 = √x (2ω(x) + 1),
        i.e.   ω(1/x) = −½ + √x/2 + √x · ω(x),

    which is precisely the form used to split Riemann's Mellin integral in
    :func:`theta_mellin_xi`.
    """
    with mp.workdps(dps + _GUARD):
        xv = _real_arg(x, "omega")
        if xv <= 0:
            raise ValueError("omega requires x > 0")
        n_max = terms if terms is not None else _theta_terms(xv, dps + _GUARD)
        total = mp.mpf(0)
        for n in range(1, n_max + 1):
            total += mp.exp(-mp.pi * n * n * xv)
        value = total
    return _shrink(value, dps)


def theta_modular_defect(x, dps: int = DPS_DEFAULT):
    """θ(1/x) − √x · θ(x), which is identically 0 for x > 0.

    This is the modular transformation of the Jacobi theta function, and it is
    Poisson summation applied to the Gaussian: the Fourier transform of
    e^{−π x y²} is x^{−1/2} e^{−π ξ²/x}, so

        Σ_n e^{−π n² x}  =  x^{−1/2} Σ_n e^{−π n²/x}.

    Everything in Riemann's 1859 memoir, the functional equation included,
    is downstream of this one line.  Both sides are computed here by *direct
    summation*, so a small return value is real evidence, not an identity
    baked into the implementation.
    """
    with mp.workdps(dps + 2 * _GUARD):
        d = dps + 2 * _GUARD
        xv = _real_arg(x, "theta_modular_defect")
        value = theta(1 / xv, d) - mp.sqrt(xv) * theta(xv, d)
    return _shrink(value, dps)


# ---------------------------------------------------------------------------
# 2b.  The heat kernel on the circle
# ---------------------------------------------------------------------------

#: Diffusivity D in ∂_t u = D ∂_x² u for the normalisation used by
#: :func:`theta_heat`.  Derived, not guessed, see that function's docstring.
HEAT_DIFFUSIVITY: int = 1


def _theta_heat_terms(t, dps: int) -> int:
    """Smallest K with e^{−4π² K² t} < 10^{−dps−5}."""
    tf = float(t)
    if tf <= 0:
        raise ValueError("theta_heat requires t > 0")
    need = (dps + 5) * math.log(10) / (4 * math.pi ** 2) / tf
    return max(1, int(math.ceil(math.sqrt(max(need, 1.0)))) + 2)


def theta_heat(x, t, terms: int | None = None, dps: int = DPS_DEFAULT):
    """Heat kernel on the circle ℝ/ℤ, spectral (Fourier) form:

        Θ(x,t) = Σ_{n∈ℤ} e^{−4π² n² t} e^{2πinx}
               = 1 + 2 Σ_{n≥1} e^{−4π² n² t} cos(2πnx).

    The imaginary parts cancel in the ±n pairs, so Θ is real for real x and
    t > 0; we sum the manifestly real second form.

    **Which PDE does this solve?**  Differentiate the series term by term:

        ∂_t Θ  = Σ_n (−4π² n²) e^{−4π²n²t} e^{2πinx}
        ∂_x² Θ = Σ_n (2πin)²  e^{−4π²n²t} e^{2πinx} = Σ_n (−4π²n²) e^{…}

    These are the *same series*.  Hence, with this normalisation,

        ∂_t Θ = ∂_x² Θ,   i.e.  diffusivity D = 1  (``HEAT_DIFFUSIVITY``),

    **not** 1/(4π²).  The 4π² sits in the exponent precisely so that D = 1: it
    is the eigenvalue of −∂_x² on e^{2πinx} when the circle has period 1.  A
    diffusivity of 1/(4π²) belongs to the *other* common normalisation,
    Σ_n e^{−n²t} e^{inx} on ℝ/2πℤ.  :func:`theta_heat_residual` checks the
    claim numerically rather than taking it on trust.

    Relation to :func:`theta`:  Θ(0,t) = θ(4πt), since 4π²n²t = π n² (4πt).

    Parameters
    ----------
    x : position on the circle (period 1).
    t : time > 0.
    terms : number of positive frequencies kept (default: adaptive from ``dps``).
    dps : digits of the returned value.
    """
    with mp.workdps(dps + _GUARD):
        xv = _real_arg(x, "theta_heat")
        tv = _real_arg(t, "theta_heat")
        if tv <= 0:
            raise ValueError("theta_heat requires t > 0")
        K = terms if terms is not None else _theta_heat_terms(tv, dps + _GUARD)
        two_pi = 2 * mp.pi
        total = mp.mpf(1)
        for n in range(1, K + 1):
            total += 2 * mp.exp(-(two_pi * n) ** 2 * tv) * mp.cos(two_pi * n * xv)
        value = total
    return _shrink(value, dps)


def theta_heat_gaussian(x, t, terms: int | None = None, dps: int = DPS_DEFAULT):
    """Heat kernel on ℝ/ℤ, real-space (periodised Gaussian) form:

        Θ(x,t) = Σ_{m∈ℤ} (4πt)^{−1/2} exp(−(x−m)²/(4t)).

    Each summand is the free heat kernel on ℝ with diffusivity 1, so the sum
    solves ∂_t u = ∂_x² u and is 1-periodic.  Poisson summation turns it into
    the spectral form of :func:`theta_heat`, because the Fourier transform of
    (4πt)^{−1/2} e^{−y²/(4t)} is e^{−4π² ξ² t}.

    The two forms are computationally complementary: this one converges fast
    for *small* t (few images matter), the spectral one for *large* t (few
    frequencies survive).  That trade-off is exactly the modular relation
    x ↔ 1/x.
    """
    with mp.workdps(dps + _GUARD):
        xv = _real_arg(x, "theta_heat_gaussian")
        tv = _real_arg(t, "theta_heat_gaussian")
        if tv <= 0:
            raise ValueError("theta_heat_gaussian requires t > 0")
        if terms is None:
            reach = mp.sqrt(4 * tv * (dps + _GUARD + 5) * mp.log(10))
            terms = int(math.ceil(float(reach) + abs(float(xv)))) + 2
        total = mp.mpf(0)
        for m in range(-terms, terms + 1):
            total += mp.exp(-(xv - m) ** 2 / (4 * tv))
        value = total / mp.sqrt(4 * mp.pi * tv)
    return _shrink(value, dps)


def theta_heat_poisson_defect(x, t, dps: int = DPS_DEFAULT):
    """theta_heat(x,t) − theta_heat_gaussian(x,t): Poisson summation, checked.

    Identically zero.  This is the *same* identity as
    :func:`theta_modular_defect`, wearing heat-equation clothing.
    """
    with mp.workdps(dps + 2 * _GUARD):
        d = dps + 2 * _GUARD
        value = theta_heat(x, t, dps=d) - theta_heat_gaussian(x, t, dps=d)
    return _shrink(value, dps)


def theta_heat_residual(x, t, h=None, dps: int = DPS_DEFAULT, diffusivity=None):
    """Numerically verify the heat equation obeyed by :func:`theta_heat`:

        residual = ∂_t Θ(x,t) − D · ∂_x² Θ(x,t),      with  D = 1.

    The diffusivity is *derived*, not assumed.  With
    Θ = Σ_n e^{−4π²n²t} e^{2πinx}, term-by-term differentiation gives
    ∂_tΘ = Σ_n (−4π²n²)(…) and ∂_x²Θ = Σ_n (2πin)²(…) = Σ_n (−4π²n²)(…).
    Identical series ⟹ D = 1.  Pass ``diffusivity`` explicitly to experiment
    with other normalisations (e.g. 1/(4π²), which will *not* vanish here).

    Derivatives use 4th-order-accurate central stencils

        f'(a)  ≈ (−f(a+2h) + 8f(a+h) − 8f(a−h) + f(a−2h)) / (12h)
        f''(a) ≈ (−f(a+2h) + 16f(a+h) − 30f(a) + 16f(a−h) − f(a−2h)) / (12h²)

    evaluated at working precision dps + 30, so both the O(h⁴) truncation
    error and the O(ε/h²) round-off sit far below the reported digits.  The
    frequency cut-off K is frozen across all stencil points so that the
    truncated series differentiates consistently.

    Step size: the default h = 10⁻¹⁰ sits in the truncation-dominated regime
    at 60 working digits (round-off floor ε/h² ≈ 10⁻⁶⁰/10⁻²⁰ = 10⁻⁴⁰), which is
    why the absolute residual never falls below ~4e-42 no matter how large t is.
    Measured residuals are then 4e-42 … 1.3e-28 **absolute**, at every (x, t)
    tried.  Relative to |∂_x²Θ|, computed independently by term-by-term
    differentiation of the series, the picture depends on t, because ∂_x²Θ
    itself decays like e^{−4π²t}:

    ========  ==================  =============  =============
    t         |∂_x²Θ| at x=0.42   |residual|     relative
    ========  ==================  =============  =============
    0.005     0.98                1.7e-30        1.7e-30
    0.02      24.3                1.2e-32        4.9e-34
    0.05      9.55                5.3e-35        5.5e-36
    0.1–0.3   1.34 … 5.0e-4       1.1e-35 …4e-39 ≈ 8.1e-36
    0.5       1.9e-07             7.7e-42        4.2e-35
    1.0       5.0e-16             4.4e-42        **8.9e-27**
    ========  ==================  =============  =============

    So: the heat equation with D = 1 is confirmed to **≥ 34 significant digits
    for 0.02 ≲ t ≲ 0.3**, and to ≥ 30 digits at t = 0.005 (there the O(h⁴)
    truncation of ∂_t, which scales as t^{−5}, dominates).  For **t ≳ 0.5 the
    relative figure degrades**, not because the identity is any less true, but
    because ∂_x²Θ has decayed to within sight of the round-off floor
    ε_work/h² ≈ 10^{−(dps+30)}/h².  Raising ``dps`` restores it: at t = 1 the
    relative residual is 8.9e-27 at dps=30 and 8.1e-36 at dps=45.  The residual scales as
    h⁴ exactly, as it must for these stencils (verified: 10⁻⁶ → 2.2e-18,
    10⁻⁸ → 2.2e-26, 10⁻¹⁰ → 2.2e-34 at x = 0.3, t = 0.05).

    Returns the raw (signed) residual as an ``mpf``.
    """
    work = dps + 30
    D = HEAT_DIFFUSIVITY if diffusivity is None else diffusivity
    with mp.workdps(work):
        xv = _real_arg(x, "theta_heat_residual")
        tv = _real_arg(t, "theta_heat_residual")
        hv = mp.mpf("1e-10") if h is None else _real_arg(h, "theta_heat_residual")
        Dv = _num(D)
        if hv <= 0:
            raise ValueError("require h > 0")
        if tv - 2 * hv <= 0:
            raise ValueError("require t > 2h so the stencil stays in t > 0")
        # freeze the term count so every stencil point truncates identically
        K = _theta_heat_terms(tv - 2 * hv, work)

        def f(xx, tt):
            return theta_heat(xx, tt, terms=K, dps=work)

        u_t = (
            -f(xv, tv + 2 * hv) + 8 * f(xv, tv + hv)
            - 8 * f(xv, tv - hv) + f(xv, tv - 2 * hv)
        ) / (12 * hv)
        u_xx = (
            -f(xv + 2 * hv, tv) + 16 * f(xv + hv, tv) - 30 * f(xv, tv)
            + 16 * f(xv - hv, tv) - f(xv - 2 * hv, tv)
        ) / (12 * hv * hv)
        value = u_t - Dv * u_xx
    return _shrink(value, dps)


# ---------------------------------------------------------------------------
# 3.  Completed zeta: xi, Xi, functional equation
# ---------------------------------------------------------------------------

def _completed_zeta_raw(s):
    """π^{−s/2} Γ(s/2) ζ(s), evaluated literally (assumes s is not exceptional)."""
    return mp.power(mp.pi, -s / 2) * mp.gamma(s / 2) * mp.zeta(s)


def completed_zeta(s, dps: int = DPS_DEFAULT):
    """Λ(s) = π^{−s/2} Γ(s/2) ζ(s), the "completed" zeta.

    Λ has simple poles at **s = 0 and s = 1 only**, and satisfies Λ(s) = Λ(1−s).
    Multiplying by ½s(s−1) kills both poles and yields the entire ξ.

    Exceptional points handled here:

    * s = 0, 1, genuine poles; ``ValueError``.
    * s = −2, −4, −6, …, the trivial zeros.  Γ(s/2) has a pole there and ζ(s)
      a zero, so Λ is finite (Λ(−2m) = Λ(2m+1)) but the literal product is
      0·∞ and mpmath raises "gamma function pole".  We evaluate the removable
      singularity with :func:`_cauchy_mean`, a circle average of the *same*
      literal expression, which uses no functional equation and is therefore
      not circular when the result is compared against Λ(1−s).
    """
    with mp.workdps(dps + _GUARD):
        s_w = _num(s)
        if s_w == 0 or s_w == 1:
            raise ValueError(
                f"Lambda(s) = pi^(-s/2) Gamma(s/2) zeta(s) has a simple pole at s={s}"
            )
        if _is_trivial_zero(s_w):
            value = _removable(_completed_zeta_raw, s_w, dps + _GUARD)
        else:
            value = _completed_zeta_raw(s_w)
    return _shrink(value, dps)


def _xi_raw(s):
    """(s−1) π^{−s/2} Γ(s/2+1) ζ(s), evaluated literally (s not exceptional)."""
    return (s - 1) * mp.power(mp.pi, -s / 2) * mp.gamma(s / 2 + 1) * mp.zeta(s)


def xi(s, dps: int = DPS_DEFAULT):
    """Riemann's ξ function, entire, with ξ(s) = ξ(1−s):

        ξ(s) = ½ · s · (s−1) · π^{−s/2} · Γ(s/2) · ζ(s).

    The prefactor ½s(s−1) cancels the pole of ζ at s = 1 and the pole of
    Γ(s/2) at s = 0; the trivial zeros of ζ at s = −2,−4,… are cancelled by
    the remaining poles of Γ(s/2).  What survives are exactly the non-trivial
    zeros, all inside 0 ≤ Re s ≤ 1, and the Riemann Hypothesis is the
    assertion that every one of them has Re s = ½.

    **Implementation note.**  The generic branch evaluates the algebraically
    identical but numerically better-behaved form

        ξ(s) = (s − 1) · π^{−s/2} · Γ(s/2 + 1) · ζ(s),

    using ½·s·Γ(s/2) = (s/2)·Γ(s/2) = Γ(s/2 + 1).  That removes the s = 0
    singularity *analytically* instead of asking the machine to cancel a pole
    of Γ against a zero of the prefactor.

    Being entire, ξ must return a finite value at **every** s.  Three families
    of points defeat the generic branch and are handled separately:

    * s = 1, (s−1)ζ(s) → 1 (the residue), so ξ(1) = π^{−1/2}Γ(3/2) = ½.
    * s = 0, already fine in this form: ξ(0) = (−1)·1·Γ(1)·ζ(0) = ½.
    * **s = −2, −4, −6, …**: the trivial zeros.  Γ(s/2+1) has a pole and ζ(s)
      a zero; the product is 0·∞ and mpmath raises "gamma function pole".
      (Note the *literal* formula ½s(s−1)π^{−s/2}Γ(s/2)ζ(s) has exactly the
      same problem here, shifting Γ(s/2) to Γ(s/2+1) fixes s = 0 and nothing
      else.)  We evaluate the removable singularity as a circle average of the
      generic branch, :func:`_cauchy_mean`.  No functional equation is used, so
      comparing the result against ξ(1−s), computed by the generic branch, is
      a genuine test rather than a tautology.  Measured agreement at dps = 40:
      ξ(−2m) − ξ(2m+1) is **exactly 0.0** for m = 1, 2, 5, 10, 20.

    Landmarks:  ξ(0) = ξ(1) = ½,   ξ(½) = Ξ(0) ≈ 0.4971207781…,
                ξ(−2) = ξ(3) = 3ζ(3)/(2π) ≈ 0.5739398940…
    """
    with mp.workdps(dps + _GUARD):
        s_w = _num(s)
        if s_w == 1:
            # (s-1)ζ(s) → 1 (the residue), so ξ(1) = π^{-1/2} Γ(3/2) = 1/2.
            value = mp.power(mp.pi, mp.mpf(-1) / 2) * mp.gamma(mp.mpf(3) / 2)
        elif _is_trivial_zero(s_w):
            value = _removable(_xi_raw, s_w, dps + _GUARD)
        else:
            value = _xi_raw(s_w)
    return _shrink(value, dps)


def Xi(t, dps: int = DPS_DEFAULT, tol_digits: int = 8):
    """Ξ(t) = ξ(½ + it), which is **real** for real t.

    Reality follows from ξ(s) = ξ(1−s) combined with Schwarz reflection
    ξ(s̄) = conj ξ(s): for s = ½+it we have 1−s = ½−it = s̄, hence
    ξ(s) = ξ(s̄) = conj ξ(s), so ξ(s) ∈ ℝ.

    Ξ is even, Ξ(−t) = Ξ(t), and its real zeros are precisely the ordinates γ
    of the zeta zeros lying on the critical line.  Ξ(0) = ξ(½) ≈ 0.4971207781…

    The residual numerical imaginary part is *checked* to be negligible
    (below 10^{−(dps+guard)+tol_digits} times max(|Re|, 1)) and then discarded;
    a ``ValueError`` here means the working precision was insufficient, not that
    Ξ failed to be real.  Because the bound is scaled by max(|Re|, 1) it is a
    round-off check on an O(1) computation, not a relative-accuracy certificate
    for the exponentially small values of Ξ at large t.
    """
    with mp.workdps(dps + _GUARD):
        tv = _real_arg(t, "Xi")   # ValueError on complex t; use xi(1/2+1j*t) instead
        val = xi(mp.mpc(mp.mpf(1) / 2, tv), dps + _GUARD)
        value = _real_part_checked(val, dps + _GUARD, tol_digits, f"Xi({t})")
    return _shrink(value, dps)


def functional_equation_defect(s, dps: int = DPS_DEFAULT):
    """ξ(s) − ξ(1−s), identically zero: Riemann's functional equation.

    Equivalent classical forms:
        π^{−s/2}Γ(s/2)ζ(s) = π^{−(1−s)/2}Γ((1−s)/2)ζ(1−s)
        ζ(s) = 2^s π^{s−1} sin(πs/2) Γ(1−s) ζ(1−s)

    See :func:`theta_mellin_xi` for *why* it is true: the theta modular
    relation makes Riemann's Mellin representation manifestly symmetric under
    s ↦ 1−s.
    """
    with mp.workdps(dps + 2 * _GUARD):
        d = dps + 2 * _GUARD
        s_w = _num(s)
        value = xi(s_w, d) - xi(1 - s_w, d)
    return _shrink(value, dps)


# ---------------------------------------------------------------------------
# 4.  Riemann-Siegel theta and Hardy's Z
# ---------------------------------------------------------------------------

def rs_theta(t, dps: int = DPS_DEFAULT):
    """Riemann–Siegel theta function

        ϑ(t) = arg Γ(¼ + it/2) − (t/2) log π
             = Im log Γ(¼ + it/2) − (t/2) log π,

    evaluated on the branch that is continuous with ϑ(0) = 0.  We use
    ``loggamma`` rather than ``arg`` precisely because the latter would wrap
    at ±π and destroy the continuity that makes ϑ a useful phase counter.

    Asymptotically
        ϑ(t) ≈ (t/2) log(t/2π) − t/2 − π/8 + 1/(48t) + 7/(5760 t³) + …,
    which is what makes the Riemann–von Mangoldt count N(T) ≈ ϑ(T)/π + 1 work,
    and what defines the Gram points ϑ(g_n) = nπ.
    """
    with mp.workdps(dps + _GUARD):
        tv = _real_arg(t, "rs_theta")
        value = mp.im(mp.loggamma(mp.mpc(mp.mpf(1) / 4, tv / 2))) - tv / 2 * mp.log(mp.pi)
    return _shrink(value, dps)


def Z(t, dps: int = DPS_DEFAULT, tol_digits: int = 8):
    """Hardy's function

        Z(t) = e^{iϑ(t)} ζ(½ + it),

    which is **real** for real t, with |Z(t)| = |ζ(½+it)|.

    The rotation by e^{iϑ} exactly undoes the phase that the functional
    equation forces on ζ along the critical line, so all the information about
    critical-line zeros survives as *sign changes of a real function of a real
    variable*.  That is the single most useful fact in computational zeta:
    zero-finding becomes bisection.

    Ξ and Z carry the same real zeros; Z is the numerically convenient
    normalisation (Ξ decays like e^{−πt/4} and underflows, Z does not).

    The residual imaginary part is checked to be negligible (``ValueError`` if
    not) and discarded.

    Measured against ``mpmath.siegelz``: |Z − siegelz| ≤ 1.2e-41 at dps = 40 for
    t ∈ {0.5, 1, 10, 20, 50, 100, 1000} and t = −4.
    """
    with mp.workdps(dps + _GUARD):
        tv = _real_arg(t, "Z")
        th = rs_theta(tv, dps + _GUARD)
        val = mp.expjpi(th / mp.pi) * mp.zeta(mp.mpc(mp.mpf(1) / 2, tv))
        value = _real_part_checked(val, dps + _GUARD, tol_digits, f"Z({t})")
    return _shrink(value, dps)


def _scan_cache_path(t0: float, t1: float, n_samples: int, dps: int) -> str:
    """Cache filename for one Z-scan.

    Uses ``repr`` of the endpoints, not a fixed number of decimals: a ``%.6f``
    key silently merges e.g. t1 = 100.0 with t1 = 100.0000001 and hands one
    scan's answer to the other.
    """
    return os.path.join(
        DATA_DIR,
        f"hardy_Z_scan_{t0!r}_{t1!r}_{int(n_samples)}_{int(dps)}.json",
    )


def hardy_Z_sign_changes(
    t0,
    t1,
    n_samples: int,
    dps: int = 15,
    cache: bool = True,
) -> list[tuple[float, float]]:
    """Bracket the sign changes of Hardy's Z on [t0, t1].

    Samples Z at ``n_samples`` equally spaced points and returns the list of
    consecutive pairs (a, b) with Z(a)·Z(b) < 0.  Each such bracket contains an
    odd number of zeros of Z, hence of ζ on the critical line, so feeding
    them to bisection or Brent's method produces the ordinates γ_n.

    The sampling has to be fine enough to see them: consecutive zeros are
    spaced ≈ 2π/log(t/2π), so take
        n_samples ≳ 5 (t1−t0) log(t1/2π) / 2π
    to have a good chance of resolving every zero.  This routine makes **no
    claim of completeness**, a pair of zeros inside one sample interval is
    invisible to it.  Use the argument principle / Backlund's N(T) to certify
    counts.

    Results are cached to ``data/hardy_Z_scan_<t0>_<t1>_<n>_<dps>.json`` so
    repeated demos are instant; pass ``cache=False`` to force recomputation.

    Returns
    -------
    list of (float, float) brackets, in increasing order of t.
    """
    t0f, t1f = float(t0), float(t1)
    if n_samples < 2:
        raise ValueError("n_samples must be >= 2")
    if not t1f > t0f:
        raise ValueError("require t1 > t0")

    path = _scan_cache_path(t0f, t1f, n_samples, dps)
    if cache and os.path.exists(path):
        try:
            with open(path, "r") as fh:
                payload = json.load(fh)
            # Never trust a cache file's *name*: check that its contents really
            # describe the scan that was asked for, and recompute if not.
            if (
                float(payload["t0"]) == t0f
                and float(payload["t1"]) == t1f
                and int(payload["n_samples"]) == int(n_samples)
                and int(payload["dps"]) == int(dps)
            ):
                return [(float(a), float(b)) for a, b in payload["brackets"]]
        except (ValueError, KeyError, OSError, TypeError):  # pragma: no cover
            pass

    step = (t1f - t0f) / (n_samples - 1)
    brackets: list[tuple[float, float]] = []
    prev_t = t0f
    prev_v = Z(prev_t, dps=dps)
    for i in range(1, n_samples):
        cur_t = t1f if i == n_samples - 1 else t0f + i * step
        cur_v = Z(cur_t, dps=dps)
        if prev_v != 0 and cur_v != 0 and (prev_v > 0) != (cur_v > 0):
            brackets.append((prev_t, cur_t))
        prev_t, prev_v = cur_t, cur_v

    if cache:
        try:
            os.makedirs(DATA_DIR, exist_ok=True)
            with open(path, "w") as fh:
                json.dump(
                    {
                        "t0": t0f,
                        "t1": t1f,
                        "n_samples": int(n_samples),
                        "dps": int(dps),
                        "brackets": [list(b) for b in brackets],
                    },
                    fh,
                )
        except OSError:  # pragma: no cover - read-only fs
            pass
    return brackets


# ---------------------------------------------------------------------------
# 5.  Mellin transforms
# ---------------------------------------------------------------------------

#: Largest |Re s| the regularised Mellin form is allowed to reach.  Beyond this
#: the number of subtracted Bernoulli terms (and the quadrature cost) is silly.
_MELLIN_SIGMA_MIN: float = -20.0


def _bose_tail_scaled(x, J: int, dps: int):
    """R_J(x) / x^{2J+1}, where R_J is the Bose factor with its first 2J+2 terms
    of the Bernoulli expansion removed:

        1/(e^x − 1) = 1/x − ½ + Σ_{j=1}^{J} B_{2j} x^{2j−1}/(2j)! + R_J(x),
        R_J(x) = Σ_{j>J} B_{2j} x^{2j−1}/(2j)!   =  O(x^{2J+1}).

    (The expansion is 1/(e^x−1) = Σ_{k≥0} B_k x^{k−1}/k! with B₁ = −½, radius
    2π; all odd B_k with k ≥ 3 vanish.)

    Returning the *scaled* tail keeps the quadrature integrand bounded: the
    caller integrates x^{s+2J} · (R_J/x^{2J+1}) rather than x^{s−1}·R_J, which
    for very negative Re(s) would multiply an enormous factor by a tiny one.

    For |x| ≤ 1 the series is used directly (strictly decreasing terms, no
    cancellation whatsoever); its leading term is B_{2J+2}/(2J+2)!.
    """
    if abs(x) <= 1:
        total = mp.mpf(0)
        eps = mp.mpf(10) ** (-dps - 10)
        xsq = x * x
        power = mp.mpf(1)                       # x^{2j-2J-2} at j = J+1
        for j in range(J + 1, J + 401):
            term = mp.bernoulli(2 * j) * power / mp.factorial(2 * j)
            total += term
            if abs(term) < eps:
                break
            power = power * xsq
        return total
    tail = 1 / mp.expm1(x) - 1 / x + mp.mpf(1) / 2
    for j in range(1, J + 1):
        tail -= mp.bernoulli(2 * j) * mp.power(x, 2 * j - 1) / mp.factorial(2 * j)
    return tail / mp.power(x, 2 * J + 1)


def _gamma_zeta_is_pole(s) -> bool:
    """True at the poles of Γ(s)ζ(s): s = 1, s = 0, and s = −1, −3, −5, …

    Γ(s) has simple poles at 0, −1, −2, …; ζ has one at s = 1.  The Γ poles at
    the *even* negative integers are cancelled by the trivial zeros of ζ, so
    what survives is s = 1, 0 and the negative odd integers.
    """
    if s == 0 or s == 1:
        return True
    if not _is_real(s):
        return False
    r = mp.re(s)
    if r > 0 or r != mp.floor(r):
        return False
    return int(r) % 2 != 0


def _mellin_subtractions(sigma: float) -> int:
    """How many Bernoulli terms to remove so ∫_0^1 x^{s−1}R_J(x)dx behaves.

    The integrand is x^{Re s + 2J} up to a bounded factor, so convergence needs
    Re s + 2J > −1; we ask for Re s + 2J ≥ 1 plus one term of margin, i.e.
    J = max(1, ⌈(1 − Re s)/2⌉ + 1).
    """
    return int(max(1, math.ceil((1.0 - sigma) / 2) + 1))


def mellin_gamma_zeta(
    s, dps: int = DPS_DEFAULT, regularized: bool = True, n_subtract: int | None = None
):
    """Compute, numerically, the Mellin (Laplace-type) integral

        I(s) = ∫_0^∞ x^{s−1} / (e^x − 1) dx        ( = Γ(s) ζ(s) for Re s > 1 ).

    **Why the identity holds.**  Expand the Bose factor as a geometric series
    and integrate term by term:

        1/(e^x − 1) = Σ_{n≥1} e^{−nx},
        ∫_0^∞ x^{s−1} e^{−nx} dx = Γ(s) n^{−s},
        ⟹  I(s) = Γ(s) Σ_{n≥1} n^{−s} = Γ(s) ζ(s).

    This is exactly the Bose–Einstein integral of statistical mechanics: ζ is
    the Mellin transform of the photon-gas occupation number, which is why
    Γ(4)ζ(4) = π⁴/15 shows up inside the Stefan–Boltzmann constant.

    ``regularized=True`` (default) removes the singular *and* the first few
    regular terms of the integrand at x = 0 analytically.  With

        1/(e^x−1) = 1/x − ½ + Σ_{j=1}^{J} B_{2j}x^{2j−1}/(2j)! + R_J(x),
        R_J(x) = O(x^{2J+1}),

    and ∫_0^1 x^{s−2}dx = 1/(s−1),  ∫_0^1 x^{s−1}dx = 1/s,
    ∫_0^1 x^{s+2j−2}dx = 1/(s+2j−1) all in closed form:

        I(s) = 1/(s−1) − 1/(2s) + Σ_{j=1}^{J} B_{2j}/((2j)!(s+2j−1))
             + ∫_0^1 x^{s−1} R_J(x) dx
             + ∫_1^∞ x^{s−1}/(e^x−1) dx.

    Every term is meromorphic in s and the last two integrals converge for
    Re(s) > −(2J+1), so this **is** the analytic continuation of Γ(s)ζ(s), with
    its poles displayed explicitly: s = 1 (from ζ), s = 0 and s = −1, −3, …,
    1−2J (from Γ).  Note the even negative integers carry *no* pole, exactly
    because ζ vanishes there, the trivial zeros, visible in the arithmetic.

    ``J`` is chosen by :func:`_mellin_subtractions` so that the remaining
    integrand is x^{Re s + 2J} with Re s + 2J ≥ 3; override with ``n_subtract``
    (``n_subtract=0`` reproduces the naive "remove only the singular terms"
    regularisation).  **The choice of J is what makes this work.**  Measured
    relative error against Γ(s)ζ(s) at ``dps=35``:

    ======  ==========  ==========  ==========  ==========
    Re s    J = 0       J = 1       J = 2       J = 3
    ======  ==========  ==========  ==========  ==========
    1.5     6.3e-37     6.3e-37     6.3e-37     6.3e-37
    −0.5    9.9e-30     3.9e-39     3.9e-39     3.9e-39
    −0.9    **2.7e-06** 1.9e-37     1.9e-37     1.9e-37
    −0.99   **0.278**   2.3e-37     2.3e-37     2.3e-37
    −2.5    rejected    1.5e-29     7.2e-37     7.2e-37
    −4.5    rejected    rejected    1.6e-29     4.3e-37
    ======  ==========  ==========  ==========  ==========

    Two things to read off.  The naive J = 0 form silently returns rubbish as
    Re(s) ↓ −1, exactly the regime it was advertised for.  And the *smallest*
    admissible J (the one that merely makes the integral converge) still leaves
    the integrand only barely integrable and costs ~8 digits; hence the "+1" of
    margin in :func:`_mellin_subtractions`.

    Measured relative error of the *default* path against Γ(s)ζ(s) at
    ``dps=40``: **worst case 8.7e-42** over
    s ∈ {1.05, 1.2, 1.5, 2, 3, 10, 0.5, −0.5, −0.9, −0.99, −1.5, −2.5, −4.5,
    −6.5, −10.5, −19.5, 2+i, ½+3i, ½+14.13i, −½+2i, −3+i, −8+2i, −15+5i}.
    At the trivial zeros s = −2m the value agrees with ζ'(−2m)/(2m)!, the limit
    of the 0·∞ product, which mpmath cannot form at all, to ≥ 36 digits.

    ``regularized=False`` performs the raw quadrature on [0,∞): faithful to the
    literal statement of the identity, but it requires Re(s) > 1 and degrades
    badly as Re(s) ↓ 1.  Measured relative error at ``dps=40``: 4e-42 at s = 2,
    1.7e-30 at s = 1.5, 1.3e-12 at s = 1.2, **1.1e-03 at s = 1.05**.
    """
    s = _num(s)
    work = dps + _GUARD + 5
    with mp.workdps(work):
        s_w = _num(s)
        sigma = float(mp.re(s_w))
        if regularized:
            if sigma < _MELLIN_SIGMA_MIN:
                raise ValueError(
                    f"regularized Mellin form is capped at Re(s) >= {_MELLIN_SIGMA_MIN}"
                )
            J = _mellin_subtractions(sigma) if n_subtract is None else int(n_subtract)
            if J < 0:
                raise ValueError("n_subtract must be non-negative")
            if sigma <= -(2 * J + 1):
                raise ValueError(
                    f"n_subtract={J} only continues to Re(s) > {-(2 * J + 1)}"
                )
            if _gamma_zeta_is_pole(s_w):
                raise ValueError(
                    f"Gamma(s)zeta(s) has a pole at s={s} "
                    "(s = 1, s = 0 and the negative odd integers)"
                )
            closed = 1 / (s_w - 1) - 1 / (2 * s_w)
            for j in range(1, J + 1):
                closed += mp.bernoulli(2 * j) / (
                    mp.factorial(2 * j) * (s_w + 2 * j - 1)
                )
            half = mp.mpf(1) / 2
            inner = mp.quad(
                lambda x: mp.power(x, s_w + 2 * J) * _bose_tail_scaled(x, J, work),
                [0, half, 1],
            )
            outer = mp.quad(
                lambda x: mp.power(x, s_w - 1) / mp.expm1(x), [1, 10, mp.inf]
            )
            value = closed + inner + outer
        else:
            if sigma <= 1:
                raise ValueError(
                    "the raw integral ∫_0^∞ x^{s-1}/(e^x-1) dx needs Re(s) > 1"
                )
            value = mp.quad(
                lambda x: mp.power(x, s_w - 1) / mp.expm1(x), [0, 1, 10, mp.inf]
            )
    return _shrink(value, dps)


def mellin_gamma_zeta_defect(s, dps: int = DPS_DEFAULT, regularized: bool = True):
    """∫_0^∞ x^{s−1}/(e^x−1) dx − Γ(s)·ζ(s).  Identically zero.

    Not available at s = −2, −4, … : the integral is perfectly finite there, but
    the *reference* Γ(s)ζ(s) is a 0·∞ product that mpmath refuses to form.  Use
    ``mellin_gamma_zeta(-2m)`` against ζ'(−2m)/(2m)! instead.
    """
    work = dps + _GUARD
    with mp.workdps(work):
        s_w = _num(s)
        if _is_trivial_zero(s_w):
            raise ValueError(
                f"Gamma(s)*zeta(s) is a 0*inf product at the trivial zero s={s}; "
                "compare mellin_gamma_zeta(s) with zeta'(s)/(-s)! directly"
            )
        value = mellin_gamma_zeta(s_w, work, regularized=regularized) - (
            mp.gamma(s_w) * mp.zeta(s_w)
        )
    return _shrink(value, dps)


def theta_mellin_xi(s, dps: int = DPS_DEFAULT):
    """Riemann's theta–Mellin representation of the completed zeta:

        Λ(s) := π^{−s/2} Γ(s/2) ζ(s)
              = 1/(s(s−1)) + ∫_1^∞ (x^{s/2−1} + x^{(1−s)/2−1}) ω(x) dx,

    where ω(x) = Σ_{n≥1} e^{−π n² x} = (θ(x) − 1)/2.

    **Derivation.**  For Re(s) > 1,
        π^{−s/2} Γ(s/2) n^{−s} = ∫_0^∞ x^{s/2−1} e^{−π n² x} dx,
    so summing over n ≥ 1 gives Λ(s) = ∫_0^∞ x^{s/2−1} ω(x) dx.  Split the
    integral at x = 1 and substitute x → 1/x on (0,1), using the theta modular
    relation in the form
        ω(1/x) = −½ + √x/2 + √x ω(x)
    (which is just θ(1/x) = √x θ(x) rewritten).  The elementary pieces
    integrate to −1/s − 1/(1−s) = 1/(s(s−1)), and what is left is the
    displayed integral.

    **Why this *is* the functional equation.**  The right-hand side is visibly
    unchanged under s ↦ 1−s: the term 1/(s(s−1)) is symmetric, and the two
    powers x^{s/2−1} and x^{(1−s)/2−1} simply trade places.  Since ω(x) decays
    like e^{−πx}, the integral converges for every s and is entire.  Therefore
    Λ(s) = Λ(1−s) everywhere, i.e. ξ(s) = ξ(1−s).  The functional equation is
    the modular relation of a theta function, and nothing more.

    This function computes the **right-hand side** numerically (tanh–sinh
    quadrature on [1,∞), with ω summed term by term) and returns it.  Compare
    against :func:`completed_zeta` for the left-hand side, or call
    :func:`theta_mellin_xi_defect`.

    Valid for all s ≠ 0, 1.
    """
    work = dps + _GUARD + 5
    with mp.workdps(work):
        s_w = _num(s)
        if s_w == 0 or s_w == 1:
            raise ValueError("theta_mellin_xi has poles at s = 0 and s = 1")

        def integrand(x):
            return (
                mp.power(x, s_w / 2 - 1) + mp.power(x, (1 - s_w) / 2 - 1)
            ) * omega(x, work)

        integral = mp.quad(integrand, [1, 2, 5, 20, mp.inf])
        value = 1 / (s_w * (s_w - 1)) + integral
    return _shrink(value, dps)


def theta_mellin_xi_defect(s, dps: int = DPS_DEFAULT):
    """theta_mellin_xi(s) − π^{−s/2}Γ(s/2)ζ(s).  Identically zero."""
    work = dps + _GUARD
    with mp.workdps(work):
        s_w = _num(s)
        value = theta_mellin_xi(s_w, work) - completed_zeta(s_w, work)
    return _shrink(value, dps)
