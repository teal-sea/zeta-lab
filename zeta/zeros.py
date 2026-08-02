"""Locating and counting the non-trivial zeros of the Riemann zeta function.

This module is the "zero hunting" half of the laboratory.  Everything here is
built on Hardy's function

    Z(t) = e^{i θ(t)} ζ(1/2 + i t),          θ(t) = arg Γ(1/4 + i t/2) − (t/2) log π

which is **real** for real t and satisfies |Z(t)| = |ζ(1/2 + i t)|.  Hence the
real zeros of Z are exactly the ordinates of the zeros of ζ that lie on the
critical line, and a sign change of Z is a certificate that a zero of ζ sits
there.

The counting side uses the Riemann–von Mangoldt formula in its *exact* form

    N(T) = 1 + θ(T)/π + S(T),      S(T) = (1/π) arg ζ(1/2 + iT)

where N(T) = #{ρ = β + iγ : ζ(ρ) = 0, 0 < γ < T} counted with multiplicity and
the argument is obtained by continuous variation along the broken line
2 → 2 + iT → 1/2 + iT starting from arg ζ(2) = 0.  This is an *identity*, not an
asymptotic: it counts every zero in the strip, wherever it is.

Putting the two together gives the Turing-style verification in
:func:`verify_rh_up_to`: if Z exhibits N(T) sign changes in (0, T), then all
N(T) zeros of ζ below height T are simple and lie on the critical line.

Conventions
-----------
* All index ranges ``(n0, n1)`` in this module are **inclusive** on both ends.
* ``dps`` arguments set mpmath's working precision for that call only
  (via ``mp.workdps``); no global precision state is mutated.
* θ and Z are taken from :mod:`zeta.core` when that module provides them at the
  requested precision, and from the local implementations here otherwise; the
  choice is made once at import time by :func:`_resolve_core` and is verified
  against the local code at 25 *and* 45 digits.
"""

from __future__ import annotations

import inspect
import json
import math
import os
import re
from typing import Callable, Sequence

from mpmath import mp, mpf
from mpmath.libmp import repr_dps

__all__ = [
    "rs_theta",
    "Z",
    "gram_point",
    "gram_points",
    "zeros_by_sign_change",
    "first_n_zeros",
    "zeros_from_scratch",
    "N_of_T",
    "riemann_von_mangoldt",
    "S_of_T",
    "gram_law_violations",
    "verify_rh_up_to",
    "DATA_DIR",
    "THETA_ARGMIN",
]

# ---------------------------------------------------------------------------
# paths
# ---------------------------------------------------------------------------

DATA_DIR = os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))), "data")

#: t where θ attains its minimum θ(t) = −3.5309728290166…; θ is strictly
#: increasing for t > THETA_ARGMIN, which is why Gram points are well defined
#: on the branch t > 7.
THETA_ARGMIN = 6.28983598883690278


# ---------------------------------------------------------------------------
# θ and Z  —  prefer zeta.core, fall back to a local implementation
# ---------------------------------------------------------------------------


def _rs_theta_local(t) -> mpf:
    """Riemann–Siegel theta, θ(t) = Im log Γ(1/4 + i t/2) − (t/2) log π.

    Using ``loggamma`` (rather than ``arg gamma``) gives the branch that is
    continuous in t, which is what the Gram-point and N(T) formulas require.
    """
    t = mp.mpf(t)
    return mp.im(mp.loggamma(mp.mpf(1) / 4 + mp.mpc(0, 1) * t / 2)) - t * mp.log(mp.pi) / 2


def _Z_local(t) -> mpf:
    """Hardy's function Z(t) = e^{i θ(t)} ζ(1/2 + i t)  (real for real t)."""
    t = mp.mpf(t)
    return mp.re(mp.exp(mp.mpc(0, 1) * _rs_theta_local(t)) * mp.zeta(mp.mpc(mp.mpf(1) / 2, t)))


def _ambient(fn: Callable) -> Callable:
    """Adapt ``fn(t, dps=…)`` into ``g(t)`` that honours the *ambient* ``mp.dps``.

    :mod:`zeta.core` exposes ``rs_theta(t, dps=30)`` / ``Z(t, dps=30)`` whose
    precision is fixed by a *default argument*, not by the surrounding
    ``mp.workdps``.  Calling such a function bare would silently truncate every
    result in this module to 30 digits no matter what ``dps`` the caller asked
    for, so the adapter forwards ``dps=mp.dps`` explicitly.
    """
    try:
        takes_dps = "dps" in inspect.signature(fn).parameters
    except (TypeError, ValueError):  # builtins / C functions
        takes_dps = False
    if not takes_dps:
        return fn

    def adapted(t):
        return fn(t, dps=mp.dps)

    adapted.__name__ = getattr(fn, "__name__", "adapted")
    adapted.__doc__ = getattr(fn, "__doc__", None)
    adapted.__wrapped__ = fn  # type: ignore[attr-defined]
    return adapted


def _honours_precision(cand: Callable, ref: Callable, points: Sequence) -> bool:
    """True iff ``cand`` reproduces ``ref`` to (nearly) full working precision.

    Checked at **two** precisions — 25 and 45 digits.  One precision is not
    enough: a backend that always returns 30 digits passes a 25-digit test and
    still destroys every ``dps > 30`` request downstream.  The 45-digit leg is
    what actually detects that.
    """
    for d in (25, 45):
        with mp.workdps(d):
            for p in points:
                try:
                    got = mp.mpf(cand(p))
                except Exception:
                    return False
                want = ref(p)
                scale = max(abs(want), mp.mpf(1))
                if not abs(got - want) < scale * mp.mpf(10) ** (-(d - 3)):
                    return False
    return True


def _resolve_core() -> tuple[Callable, Callable]:
    """Bind θ and Z from :mod:`zeta.core` when available, else use the local ones.

    The imported functions are adapted to the ambient precision by
    :func:`_ambient` and then *validated* by :func:`_honours_precision` at both
    25 and 45 digits (θ at t = 7, 100; Z at t = 3, 20).  Anything that
    disagrees — or that quietly caps its own precision — is rejected and the
    local implementations are used instead, so this module is never wrong and
    never silently less accurate than it claims.

    Note the deliberate absence of a ``core.theta`` fallback: in
    :mod:`zeta.core` the name ``theta`` is the **Jacobi** theta function, an
    entirely different object, and picking it up here would be a bug.
    """
    theta_fn, z_fn = _rs_theta_local, _Z_local
    try:  # pragma: no cover - depends on the sibling module existing
        from zeta import core as _core  # type: ignore

        cand_theta = getattr(_core, "rs_theta", None)
        cand_z = getattr(_core, "Z", None) or getattr(_core, "hardy_Z", None)
        if callable(cand_theta):
            adapted = _ambient(cand_theta)
            if _honours_precision(adapted, _rs_theta_local, (7, 100)):
                theta_fn = adapted
        if callable(cand_z):
            adapted = _ambient(cand_z)
            if _honours_precision(adapted, _Z_local, (3, 20)):
                z_fn = adapted
    except Exception:
        pass
    return theta_fn, z_fn


_THETA, _Z = _resolve_core()


def rs_theta(t, dps: int = 30) -> mpf:
    """Riemann–Siegel theta function.

        θ(t) = arg Γ(1/4 + i t/2) − (t/2) log π

    taken on the branch that is continuous in t with θ(0) = 0.  Asymptotically
    θ(t) ≈ (t/2) log(t/2π) − t/2 − π/8.  θ decreases to θ(6.28983…) = −3.53097…
    and is strictly increasing thereafter.
    """
    with mp.workdps(dps):
        return +mp.mpf(_THETA(mp.mpf(t)))


def Z(t, dps: int = 30) -> mpf:
    """Hardy's function Z(t) = e^{i θ(t)} ζ(1/2 + i t).

    Z is real-valued for real t and |Z(t)| = |ζ(1/2 + i t)|, so the real zeros
    of Z are exactly the ordinates γ of the critical-line zeros of ζ.
    """
    with mp.workdps(dps):
        return +mp.mpf(_Z(mp.mpf(t)))


# ---------------------------------------------------------------------------
# Gram points
# ---------------------------------------------------------------------------


def gram_point(n: int, dps: int = 30) -> mpf:
    """The n-th Gram point g_n: the unique t > 7 with θ(t) = n·π.

    θ is strictly increasing on (6.28983…, ∞) with θ(6.28983…) = −3.53097… =
    −1.12394·π, so a solution with t > 7 exists exactly for n ≥ −1.

    The initial guess inverts the asymptotic θ(t) ≈ (t/2)log(t/2π) − t/2 − π/8
    in closed form with the Lambert W function,

        g_n ≈ 2π · exp(1 + W((8n + 1) / (8e))),

    and Newton's method on θ(t) − nπ polishes it, using the **exact** derivative

        θ′(t) = ½·[ Re ψ(¼ + i t/2) − log π ],      ψ = Γ′/Γ,

    which follows from θ(t) = Im log Γ(¼ + i t/2) − (t/2) log π by
    d/dt Im log Γ(¼ + i t/2) = Im[ ψ(¼ + i t/2)·(i/2) ] = ½ Re ψ(¼ + i t/2).
    θ′ > 0 for t > 6.28983…, so Newton is monotone-safe once it is on that
    branch; a step that would leave the branch is damped back onto it, and a
    guaranteed sign-change bisection is the fallback.

    Examples: g_{-1} = 9.66690805613019…, g_0 = 17.8455995404108…,
    g_126 = 282.454720823462… (the first Gram point where Gram's law fails).
    """
    n = int(n)
    if n < -1:
        raise ValueError(
            f"gram_point: no solution of θ(t) = {n}π with t > 7 "
            "(min θ = −3.53097… = −1.12394π, so n ≥ −1 is required)"
        )
    with mp.workdps(dps + 10):
        target = n * mp.pi
        branch = mp.mpf("6.28984")  # just right of the minimum of θ

        def f(t):
            return _THETA(t) - target

        def fprime(t):
            return (mp.re(mp.digamma(mp.mpc(mp.mpf(1) / 4, mp.mpf(t) / 2))) - mp.log(mp.pi)) / 2

        # residual we can honestly demand: θ is delivered to ~dps+10 digits
        scale = max(mp.mpf(1), abs(target))
        tol = scale * mp.mpf(10) ** (-(dps + 4))

        guess = 2 * mp.pi * mp.exp(1 + mp.re(mp.lambertw((8 * n + 1) / (8 * mp.e))))
        if not mp.isfinite(guess) or guess <= branch:
            guess = mp.mpf(10)

        root = mp.mpf(guess)
        for _ in range(80):
            ft = f(root)
            if abs(ft) <= tol:
                break
            nxt = root - ft / fprime(root)
            if not mp.isfinite(nxt) or nxt <= branch:  # damp back onto θ′ > 0
                nxt = (root + branch) / 2
            if nxt == root:
                break
            root = nxt

        if not (root > 7) or abs(f(root)) > tol:
            lo, hi = branch, max(mp.mpf(guess) * 2, mp.mpf(20))
            while f(hi) < 0:  # θ → ∞, so this terminates
                hi *= 2
            for _ in range(mp.prec + 10):  # bisection: cannot fail on a bracket
                mid = (lo + hi) / 2
                if mid == lo or mid == hi:
                    break
                if f(mid) < 0:
                    lo = mid
                else:
                    hi = mid
            root = (lo + hi) / 2
    with mp.workdps(dps):
        return +root


def gram_points(n0: int, n1: int, dps: int = 30) -> list[mpf]:
    """Gram points g_{n0}, …, g_{n1} — the range is **inclusive** at both ends."""
    return [gram_point(n, dps=dps) for n in range(int(n0), int(n1) + 1)]


# ---------------------------------------------------------------------------
# zero location by sign change
# ---------------------------------------------------------------------------


def _mean_spacing(t) -> mpf:
    """Mean gap between consecutive zero ordinates near height t: 2π / log(t/2π)."""
    t = mp.mpf(t)
    if t < 10:
        t = mp.mpf(10)
    return 2 * mp.pi / mp.log(t / (2 * mp.pi))


def _refine_bracket(a, b, fa, tol) -> mpf:
    """Polish a sign-change bracket [a, b] of Z to a root, robustly."""
    for solver in ("anderson", "illinois", "bisect"):
        try:
            r = mp.mpf(mp.re(mp.findroot(_Z, (a, b), solver=solver, tol=tol)))
            if a <= r <= b:
                return r
        except Exception:
            continue
    lo, hi, flo = mp.mpf(a), mp.mpf(b), fa  # last resort: plain bisection
    for _ in range(4 * mp.prec):
        mid = (lo + hi) / 2
        if mid == lo or mid == hi:
            break
        fm = _Z(mid)
        if fm == 0:
            return mid
        if (fm > 0) == (flo > 0):
            lo, flo = mid, fm
        else:
            hi = mid
    return (lo + hi) / 2


def zeros_by_sign_change(t0, t1, n_samples: int | None = None, dps: int = 25) -> list[mpf]:
    """Ordinates of the zeros of Hardy's Z in [t0, t1], found by bracketing.

    Z is sampled on a uniform grid; every sign change ``Z(t_k)·Z(t_{k+1}) < 0``
    brackets a zero of Z, i.e. a zero ρ = 1/2 + iγ of ζ on the critical line,
    and the bracket is polished with ``mpmath.findroot``.

    If ``n_samples`` is None the grid step is set to 1/20 of the mean zero
    spacing 2π/log(t1/2π) at the top of the range, which is comfortably fine at
    the heights this laboratory works at.

    A sign-change scan can only *miss* zeros, never invent them, so the count it
    returns is a rigorous lower bound for the number of critical-line zeros;
    :func:`verify_rh_up_to` turns that bound into a proof by comparing it with
    the exact count N(T).

    Returns the roots in increasing order.
    """
    with mp.workdps(dps):
        a, b = mp.mpf(t0), mp.mpf(t1)
        if b <= a:
            return []
        if n_samples is None:
            step = _mean_spacing(b) / 20
            n_samples = int(mp.floor((b - a) / step)) + 2
        n_samples = max(int(n_samples), 2)

        ts = [a + (b - a) * mp.mpf(k) / (n_samples - 1) for k in range(n_samples)]
        vals = [_Z(t) for t in ts]
        tol = mp.mpf(10) ** (-(dps - 3))

        roots: list[mpf] = []
        for k in range(n_samples - 1):
            f0, f1 = vals[k], vals[k + 1]
            if f0 == 0:
                roots.append(ts[k])
                continue
            if (f0 > 0) != (f1 > 0):
                roots.append(_refine_bracket(ts[k], ts[k + 1], f0, tol))
        if vals[-1] == 0:
            roots.append(ts[-1])
        return [+r for r in roots]


def _zeros_adaptive(a, b, init: int = 9, max_samples: int = 4097, dps: int = 25) -> list[mpf]:
    """Zeros of Z in [a, b], doubling the grid until the count stops changing."""
    n = init
    prev = zeros_by_sign_change(a, b, n_samples=n, dps=dps)
    while n < max_samples:
        n = 2 * (n - 1) + 1
        cur = zeros_by_sign_change(a, b, n_samples=n, dps=dps)
        if len(cur) == len(prev):
            return cur
        prev = cur
    return prev


# ---------------------------------------------------------------------------
# N(T): the exact zero count
# ---------------------------------------------------------------------------


def _principal(d) -> mpf:
    """Reduce an angle difference to (−π, π]."""
    two_pi = 2 * mp.pi
    return d - two_pi * mp.nint(d / two_pi)


def _arg_variation(f: Callable, x0, x1, depth: int = 0, max_depth: int = 45) -> mpf:
    """Continuous variation of arg f along the straight segment x0 → x1.

    Adaptive bisection: the principal-value difference between the endpoints is
    accepted only once it is below π/3, which makes it safe to assume that no
    multiple of 2π was lost across that sub-segment.
    """
    d = _principal(mp.arg(f(x1)) - mp.arg(f(x0)))
    if abs(d) < mp.pi / 3 or depth >= max_depth:
        return d
    xm = (x0 + x1) / 2
    return _arg_variation(f, x0, xm, depth + 1, max_depth) + _arg_variation(
        f, xm, x1, depth + 1, max_depth
    )


def S_of_T(T, dps: int = 25) -> mpf:
    """The fluctuating term S(T) = N(T) − 1 − θ(T)/π = (1/π) arg ζ(1/2 + iT).

    The argument is taken by continuous variation of arg ζ(s) along the broken
    line 2 → 2 + iT → 1/2 + iT, starting from arg ζ(2) = 0.

    On the vertical leg no unwrapping is needed: |ζ(2 + iy) − 1| ≤ ζ(2) − 1 =
    0.6449… < 1, so ζ(2 + iy) stays in a disc about 1 that misses the origin and
    arg never leaves (−π/2, π/2).  On the horizontal leg the variation is
    accumulated by adaptive bisection (:func:`_arg_variation`).

    S(T) is O(log T) and is almost always tiny — S(100) = −0.00240990227…,
    S(1000) = 0.383758055… — but it is exactly what makes N(T) an integer.
    Independent oracle: ``mpmath.backlunds(T)`` returns the same quantity.

    T must not itself be a zero ordinate: ζ(1/2 + iT) = 0 makes arg undefined,
    and S jumps by exactly 1 across every ordinate (mpmath returns arg(0) = 0,
    so an *exact* hit would silently give a value that is neither side).  In
    floating point one always lands on one side or the other; the returned value
    is then S(γ⁻) or S(γ⁺), correct for that side.
    """
    with mp.workdps(dps):
        Tm = mp.mpf(T)
        if Tm == 0:
            return mp.mpf(0)
        vertical = mp.arg(mp.zeta(mp.mpc(2, Tm)))
        horizontal = _arg_variation(lambda x: mp.zeta(mp.mpc(x, Tm)), mp.mpf(2), mp.mpf(1) / 2)
        return +((vertical + horizontal) / mp.pi)


def N_of_T(T, dps: int = 25) -> int:
    """Exact number of zeros ρ = β + iγ of ζ with 0 < γ < T (with multiplicity).

        N(T) = 1 + θ(T)/π + S(T),     S(T) = (1/π) arg ζ(1/2 + iT)

    This is the argument principle applied to ξ(s) on the rectangle with
    vertices 2 − iT, 2 + iT, −1 + iT, −1 − iT: the functional equation
    ξ(s) = ξ(1 − s) and the reflection ζ(s̄) = conj ζ(s) collapse the contour
    integral onto the quarter path 2 → 2 + iT → 1/2 + iT, whose Γ- and π-part is
    the explicit θ(T) and whose ζ-part is π·S(T).

    It counts *every* zero in the critical strip, on or off the line — which is
    exactly what makes it usable as the yardstick in :func:`verify_rh_up_to`.

    The right-hand side is an integer up to rounding error; the value is rounded
    and the residual is checked to be < 1e-6.  Known values: N(100) = 29,
    N(1000) = 649, N(10000) = 10142.

    Caveat, honestly stated: that residual check detects a *lost branch* in the
    argument variation, **not** proximity to a zero.  If T sits within ~1e-6 of
    an ordinate γ the right-hand side is still within 1e-6 of an integer — of
    ``N(γ⁻)`` or ``N(γ⁺)`` depending on which side of γ the floating-point T
    landed — and the value is returned without complaint.  N(T) genuinely has a
    jump discontinuity at every ordinate; no guard can repair that.
    """
    with mp.workdps(dps):
        Tm = mp.mpf(T)
        if Tm <= 0:
            return 0
        raw = 1 + _THETA(Tm) / mp.pi + S_of_T(Tm, dps=dps)
        n = int(mp.nint(raw))
        if abs(raw - n) > mp.mpf("1e-6"):
            raise ArithmeticError(
                f"N({T}) = {mp.nstr(raw, 15)} is not within 1e-6 of an integer; "
                "the continuous variation of arg ζ along 2 → 2+iT → 1/2+iT lost "
                "a multiple of 2π (try a larger dps)"
            )
        return max(n, 0)


def riemann_von_mangoldt(T) -> float:
    """Main term of the Riemann–von Mangoldt formula,

        N(T) ≈ (T/2π) log(T/2π) − T/2π + 7/8

    i.e. 1 + θ(T)/π with θ replaced by its asymptotic expansion and the O(1/T)
    tail dropped.  The error against the true N(T) is S(T) + O(1/T), which is
    O(log T) in theory and well under 1 in practice at moderate heights:

        T = 100    →  29.002344…   vs N = 29      (error 0.0023)
        T = 1000   →  648.616235…  vs N = 649     (error 0.3838)
        T = 10000  →  10142.965348… vs N = 10142  (error 0.9653)
    """
    Tf = float(T)
    if Tf <= 0:
        return 0.0
    x = Tf / (2.0 * math.pi)
    return x * math.log(x) - x + 0.875


# ---------------------------------------------------------------------------
# Gram's law
# ---------------------------------------------------------------------------


def gram_law_violations(n0: int, n1: int, dps: int = 25) -> list[int]:
    """Gram indices n in [n0, n1] (**inclusive**) where Gram's law fails.

    Gram's *law* (an empirical observation, not a theorem) is

        (−1)^n Z(g_n) > 0                     for every n ≥ −1,

    equivalently: each Gram interval [g_{n−1}, g_n) contains exactly one zero
    ordinate.  Since θ(g_n) = nπ we have Z(g_n) = e^{i n π} ζ(1/2 + i g_n) =
    (−1)^n ζ(1/2 + i g_n), so the law says ζ(1/2 + i g_n) is a positive real.

    The law fails infinitely often.  The first failures are n = 126
    (g_126 = 282.4547…) and n = 134 (g_134 = 295.5839…), then 195, 211, ….
    """
    out: list[int] = []
    for n in range(int(n0), int(n1) + 1):
        if n < -1:
            continue
        g = gram_point(n, dps=dps)
        with mp.workdps(dps):
            v = _Z(g)
        if (-1) ** n * v <= 0:
            out.append(n)
    return out


# ---------------------------------------------------------------------------
# the first n zeros
# ---------------------------------------------------------------------------


def _cache_path(n: int) -> str:
    return os.path.join(DATA_DIR, f"zeros_{n}.json")


def _load_cache(n: int, dps: int) -> list[mpf] | None:
    """Return the first n ordinates from any cached file holding at least n."""
    if not os.path.isdir(DATA_DIR):
        return None
    candidates: list[tuple[int, str]] = []
    for name in os.listdir(DATA_DIR):
        m = re.fullmatch(r"zeros_(\d+)\.json", name)
        if m and int(m.group(1)) >= n:
            candidates.append((int(m.group(1)), os.path.join(DATA_DIR, name)))
    for _, path in sorted(candidates):  # smallest adequate cache first
        try:
            with open(path) as fh:
                blob = json.load(fh)
            if int(blob.get("dps", 0)) < dps:
                continue
            vals = blob["zeros"]
            if len(vals) < n:
                continue
            with mp.workdps(dps):
                return [+mp.mpf(v) for v in vals[:n]]
        except Exception:
            continue
    return None


def _save_cache(zeros: Sequence[mpf], dps: int, source: str) -> str:
    """Write the ordinates as decimal strings that round-trip *bit-exactly*.

    ``repr_dps(prec)`` is mpmath's guaranteed round-trip digit count for the
    working precision, so ``mpf(str)`` at the same dps reproduces the value
    identically rather than to within a last-bit rounding.
    """
    os.makedirs(DATA_DIR, exist_ok=True)
    path = _cache_path(len(zeros))
    with mp.workdps(dps):
        digits = repr_dps(mp.prec)
        payload = {
            "n": len(zeros),
            "dps": dps,
            "source": source,
            "description": "Ordinates gamma_n of the non-trivial zeros 1/2 + i*gamma_n of zeta(s).",
            "zeros": [mp.nstr(mp.mpf(z), digits) for z in zeros],
        }
    tmp = path + ".tmp"
    with open(tmp, "w") as fh:
        json.dump(payload, fh, indent=1)
    os.replace(tmp, path)
    return path


def first_n_zeros(n: int, cache: bool = True, dps: int = 30) -> list[mpf]:
    """The first n zero ordinates γ_1 < γ_2 < … < γ_n, in increasing order.

    Engine: ``mpmath.zetazero`` (Riemann–Siegel plus a Gram-point search
    internally), which is the sane choice up to a few thousand zeros.  The
    from-scratch sign-change path is :func:`zeros_from_scratch`; the two agree —
    see the cross-check of the first 50 in ``tests/test_zeros.py``.

    Results are cached to ``data/zeros_<n>.json`` as decimal strings; a cached
    file holding *more* zeros than requested is reused (truncated).

    γ_1  = 14.134725141734693790…
    γ_10 = 49.773832477672302182…
    """
    n = int(n)
    if n <= 0:
        return []
    if cache:
        hit = _load_cache(n, dps)
        if hit is not None:
            return hit
    with mp.workdps(dps + 10):
        zeros = [mp.mpf(mp.im(mp.zetazero(k))) for k in range(1, n + 1)]
    with mp.workdps(dps):
        zeros = [+z for z in zeros]
    if cache:
        _save_cache(zeros, dps, "mpmath.zetazero")
    return zeros


def zeros_from_scratch(n: int, dps: int = 25, verify: bool = True) -> list[mpf]:
    """The first n zero ordinates using only sign changes of Z and a Gram walk.

    No ``mpmath.zetazero`` anywhere.  The algorithm is the classical one:

    1. θ(g_m) = mπ, so Z(g_m) = (−1)^m ζ(1/2 + i g_m); Gram's law predicts
       exactly one zero of Z per Gram interval [g_{m−1}, g_m).
    2. Walk the Gram intervals upward from g_{−1} = 9.6669….  In each one, sample
       Z on a grid and bracket every sign change, doubling the grid until the
       number of sign changes stops changing — this is what catches the
       intervals where Gram's law fails and two zeros (or none) appear.
    3. Below g_{−1} the same scan is run on [0, g_{−1}]; it finds nothing, since
       γ_1 = 14.13… and Z < 0 throughout [0, 9.67…].

    With ``verify=True`` the running total is checked against the exact count
    N(g_m) from the argument principle as the walk passes Gram points, so a
    missed zero raises ``ArithmeticError`` rather than silently returning a
    wrong list.
    """
    n = int(n)
    if n <= 0:
        return []

    zeros: list[mpf] = []
    g_prev = gram_point(-1, dps=dps)
    zeros.extend(_zeros_adaptive(0, g_prev, dps=dps))  # empty in practice

    m = -1
    while len(zeros) < n:
        g_next = gram_point(m + 1, dps=dps)
        zeros.extend(_zeros_adaptive(g_prev, g_next, dps=dps))
        g_prev, m = g_next, m + 1
        if verify and (m % 25 == 0 or len(zeros) >= n):
            exact = N_of_T(g_prev, dps=dps)
            if len(zeros) != exact:
                raise ArithmeticError(
                    f"zeros_from_scratch: found {len(zeros)} sign changes below "
                    f"g_{m} = {mp.nstr(g_prev, 12)} but N(g_{m}) = {exact}; the "
                    "grid missed a zero (or a zero is off the critical line!)"
                )
    return zeros[:n]


# ---------------------------------------------------------------------------
# Turing-style verification of RH up to height T
# ---------------------------------------------------------------------------


def verify_rh_up_to(T, verbose: bool = False, dps: int = 25, max_samples: int = 200_001) -> dict:
    """Verify that every zero of ζ with 0 < γ < T is simple and on the line.

    Why "number of sign changes == N(T)" proves RH up to height T
    ------------------------------------------------------------
    Let N(T) be the number of zeros of ζ in the critical strip with 0 < γ < T,
    counted **with multiplicity** and with **no assumption whatsoever about
    their real parts**.  :func:`N_of_T` computes it exactly from the argument
    principle, N(T) = 1 + θ(T)/π + S(T).

    Now suppose Z changes sign at m distinct points 0 < t_1 < … < t_m < T.  Z is
    real-analytic and |Z(t)| = |ζ(1/2 + it)|, so Z(t_j) = 0 forces
    ζ(1/2 + i t_j) = 0: each t_j is the ordinate of a zero **on the critical
    line**.  The t_j are distinct, so they use up at least m of the count:

        m ≤ N(T).

    If m = N(T) the inequality is saturated and every unit of the count is
    accounted for by the t_j.  Therefore:

    * there is **no zero off the critical line** below height T — such a zero ρ
      would (together with its mirror 1 − ρ̄) contribute to N(T) without
      contributing to m;
    * there is **no zero of even order** on the line below T — Z does not change
      sign at one, so it too would add to N(T) but not to m;
    * each t_j has multiplicity exactly 1, i.e. **all the zeros are simple**.

    That is the Backlund/Turing method, and for the finite interval (0, T) it is
    a genuine proof, not statistical evidence.  A sign-change scan can only miss
    zeros, never invent them, so the grid can safely be refined until m = N(T);
    the procedure cannot produce a false positive.  (This routine does exactly
    that refinement, doubling the grid until the counts agree or ``max_samples``
    is reached.)

    Returns
    -------
    dict with keys ``'T'``, ``'n_sign_changes'``, ``'N_T'``, ``'all_on_line'``,
    ``'gram_violations'``, plus ``'zeros'``, ``'S_T'``, ``'n_samples'`` and
    ``'n_gram_max'`` (the largest Gram index n with g_n ≤ T; −2 when there is
    none, since g_{−1} = 9.6669… is the lowest Gram point).
    """
    with mp.workdps(dps):
        Tm = mp.mpf(T)

    exact = N_of_T(Tm, dps=dps)
    s_t = S_of_T(Tm, dps=dps)

    with mp.workdps(dps):
        step = _mean_spacing(Tm) / 20
        n_samples = max(int(mp.floor(Tm / step)) + 2, 16)

    zs: list[mpf] = []
    while True:
        zs = zeros_by_sign_change(0, Tm, n_samples=n_samples, dps=dps)
        if verbose:
            print(f"  grid of {n_samples} points -> {len(zs)} sign changes (need {exact})")
        if len(zs) >= exact or n_samples >= max_samples:
            break
        n_samples = 2 * (n_samples - 1) + 1

    # Largest Gram index with g_n ≤ T.  θ(g_n) = nπ and θ is increasing, so
    # g_n ≤ T ⇔ n ≤ θ(T)/π — but *only* on the branch t > THETA_ARGMIN.  Below
    # the minimum θ is decreasing and θ(T)/π is not an inverse at all:
    # θ(3)/π = −0.953 would "admit" g_{−1} = 9.6669 > 3.
    with mp.workdps(dps):
        if Tm > mp.mpf(THETA_ARGMIN):
            n_max_gram = int(mp.floor(_THETA(Tm) / mp.pi))
        else:
            n_max_gram = -2
    while n_max_gram >= -1 and gram_point(n_max_gram, dps=dps) > Tm:
        n_max_gram -= 1  # rounding guard when T sits on a Gram point
    violations = gram_law_violations(-1, n_max_gram, dps=dps) if n_max_gram >= -1 else []

    result = {
        "T": float(Tm),
        "n_sign_changes": len(zs),
        "N_T": exact,
        "all_on_line": len(zs) == exact,
        "gram_violations": violations,
        "zeros": zs,
        "S_T": s_t,
        "n_samples": n_samples,
        "n_gram_max": n_max_gram,
    }

    if verbose:
        print(f"verify_rh_up_to(T={float(Tm)}) at dps={dps}")
        print(f"  N(T) = 1 + θ(T)/π + S(T) = {exact}    [S(T) = {mp.nstr(s_t, 10)}]")
        print(f"  sign changes of Z on (0,T) : {len(zs)}")
        print(f"  Riemann–von Mangoldt main term: {riemann_von_mangoldt(Tm):.6f}")
        if violations:
            print(f"  Gram's law fails at n = {violations}")
        else:
            print("  Gram's law holds on every Gram point below T")
        if result["all_on_line"]:
            print(
                f"  ==> ALL {exact} zeros with 0 < γ < {float(Tm)} are SIMPLE "
                "and lie ON the critical line."
            )
        else:
            print(
                f"  ==> counts disagree ({len(zs)} vs {exact}); the grid missed "
                "zeros, nothing is proved."
            )
    return result
