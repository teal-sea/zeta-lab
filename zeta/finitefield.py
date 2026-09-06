"""The blueprint universe: curves over finite fields, where RH is a THEOREM.

**This module is the reference implementation of the one Riemann Hypothesis
that has actually been proved.**  Everywhere else in this laboratory RH is a
conjecture probed by instruments; here it is a theorem (Hasse in the 1930s for
elliptic curves, Weil 1948 for all curves, Deligne 1974 in every dimension),
and, the point of the module, it is a theorem you can *check by counting*.
See ``docs/09-new-ontologies.md`` section 1 and ``docs/11-f1-and-the-missing-
geometry.md`` section 1 for the narrative; this file is that narrative made
executable.

The object
----------
For a prime ``p > 3`` and ``a, b in F_p`` with ``4a^3 + 27b^2 != 0`` (so the
curve is nonsingular), let

    E : y^2 = x^3 + a x + b        over F_p,
    N_n = #E(F_{p^n})              (points with coordinates in F_{p^n},
                                    plus the one point at infinity),
    a_p = p + 1 - N_1              (the trace of Frobenius).

The zeta function of the curve packages *all* the counts N_1, N_2, N_3, ...
into one generating function,

    Z(T) = exp( sum_{n>=1} N_n T^n / n ),

and the theorem (Weil) is that this transcendental-looking object is in fact a
rational function with integer coefficients:

    Z(T) = (1 - a_p T + p T^2) / ((1 - T)(1 - p T)).

:func:`zeta_function_values` computes the right-hand side and
:func:`point_counts_over_extensions` the counts on the left;
:func:`zeta_log_series_defect` measures the gap, and it is exactly 0.0 at
dps = 30 and dps = 50 for every curve tested (the series is truncated at
``n_max = 60``; at the default ``T = 1/(10p)`` the first omitted term is
``10^{-61}/61 = 1.6e-63``).

The Riemann Hypothesis for E
----------------------------
Factor the numerator, ``1 - a_p T + p T^2 = (1 - alpha T)(1 - alphabar T)``.
Then ``alpha + alphabar = a_p`` and ``alpha * alphabar = p``.  RH for this
curve is the single statement

    |alpha| = sqrt(p)          <=>          |a_p| <= 2 sqrt(p)   (Hasse),

and the equivalence is elementary: the roots of ``x^2 - a_p x + p`` are a
genuine complex-conjugate pair exactly when ``a_p^2 < 4p``, and a conjugate
pair with product ``p`` has modulus ``sqrt(p)``.  :func:`hasse_check` reports
the bound, :func:`curve_survey` sweeps a seeded sample of curves over many
primes, and :func:`traces_mod_p` sweeps *every* curve mod p.  The test suite
runs both: 1 279 678 curves (all of them, for p = 101, 503, 1009) and an
862-curve seeded survey up to p = 10007.  Zero violations, and not because
the sample was lucky: this is not evidence, it is a theorem being exercised.
A violation here would mean a bug in this module.

**Why "critical line".**  The substitution ``T = p^{-s}`` turns Z(T) into a
Dirichlet-series-shaped object, and a numerator root ``T_0 = 1/alpha`` sits at

    s = log(alpha) / log(p),      so      Re(s) = log|alpha| / log(p) = 1/2.

The ``sqrt`` in the point-count bound *is* the ``1/2`` in ``Re s = 1/2``.
:func:`critical_line_check` performs that conversion in mpmath and returns the
measured deviation of ``Re(s)`` from ``1/2``.  Over an 862-curve sweep across
18 primes from 5 to 10007 the worst deviation is 1.1e-41 at ``dps = 30`` and
9.9e-32 at ``dps = 20``, pure round-off, thirty orders of magnitude inside
the 1e-12 the test suite demands.

Lefschetz: the counts are traces of powers of an operator
---------------------------------------------------------
The reason this universe has an RH at all is that its zeros come from an
*operator*.  Frobenius ``phi : x -> x^p`` acts on the etale cohomology of the
curve; its fixed points on E(Fbar_p) are exactly the F_p-points, and the
Lefschetz fixed-point formula reads

    N_n = p^n + 1 - (alpha^n + alphabar^n) = sum_i (-1)^i Tr(Frob^n | H^i).

``alpha^n + alphabar^n`` is computed here as an exact integer recursion
``t_0 = 2, t_1 = a_p, t_n = a_p t_{n-1} - p t_{n-2}`` (:func:`frobenius_power_traces`),
so :func:`point_counts_over_extensions` returns exact integers with no
floating point anywhere.

**This module refuses to leave that as formalism.**  :func:`count_points_fp2`
implements F_{p^2} = F_p[t]/(t^2 - n) arithmetic explicitly (n a quadratic
non-residue) and counts the solutions of ``y^2 = x^3 + a x + b`` over that
field by literal enumeration, using no zeta function, no eigenvalues and no
Weil theory.  The result equals ``p^2 + 1 - (alpha^2 + alphabar^2)`` on the
nose, for every curve tested.  That equality is the module's most valuable
test: it demonstrates that the operator interpretation is REAL, not formal,
a number obtained by brute-force counting in a field with p^2 elements is
predicted, exactly, by the second power sum of two complex eigenvalues.

What exists here, and what is missing over Z
--------------------------------------------
The checklist of ``docs/11`` section 1, space, operator, positivity:

* **a space**: the curve E over F_p, an honest geometric object with a ground
  field F_p underneath it, so that E x E over F_p is a genuine *surface*;
* **an operator**: Frobenius, acting as a matrix on finite-dimensional
  cohomology, with the point counts as its traces (verified here);
* **a positivity input**: the Castelnuovo-Severi inequality applied to the
  graph of Frobenius on the surface E x E, this, not the functional equation,
  is what pins ``|alpha| = sqrt(p)``.  Symmetry alone never suffices; that is
  exactly what :mod:`zeta.epstein` demonstrates on the analytic side.

Over ``Spec Z`` the first item is missing and the third has nowhere to live:
``Z (x)_Z Z = Z``, so the "square" of Spec Z is one-dimensional and there is no
staging area for a positivity argument (``docs/11`` section 2).  There is no
known category in which zeta(s) is the zeta function of a curve over a base.
**Nothing in this module is evidence for RH over the integers.**  It is the
blueprint the F1 / Connes / Deninger programs are trying to reproduce, made
concrete so the size of the gap is visible.

Conventions
-----------
Integer arithmetic is exact Python ``int`` throughout (point counts, traces,
power sums, ``N_n``).  mpmath, with explicit ``dps``, appears only where genuine
transcendence enters: eigenvalues, ``Z(T)``, and the ``log/log`` conversion to
s-coordinates.  numpy appears only in the bulk sweep behind
:func:`traces_mod_p` / :func:`sato_tate_histogram`.  That sweep does use
float64, a length-p FFT is what makes "all p^2 curves at once" affordable,
but every quantity it produces is an integer bounded by p, recovered with
``np.rint``.  Rounding alone is *not* a proof of correctness (an error of 0.9
would round to the wrong integer while leaving a residual of only 0.1), so the
recovered integers are additionally checked against two **exact** identities
that hold row by row, derived in :func:`_row_invariants` and computed from the
integer multiplicity vector, not from the FFT:

    sum_b a_p(a, b) = 0,     sum_b a_p(a, b)^2 = p * sum_v c_v^2 - p^2.

Any single mis-rounded entry breaks the second identity (changing one value m
by +/-1 changes the sum of squares by +/-2m+1, never 0), so the sweep raises
rather than return wrong integers.  The recovered traces are further checked
against the per-curve integer routine, exhaustively at p = 53 and by sampling
at p = 1009, and against a second FFT-free O(p^3) integer method at p = 23 and
p = 101.  No global mpmath state is modified.
"""

from __future__ import annotations

import json
import math
import random
from fractions import Fraction
from functools import lru_cache
from pathlib import Path
from typing import Any, Iterable, Sequence

import mpmath
import numpy as np
from mpmath import mp

from .core import DPS_DEFAULT

__all__ = [
    # field and curve basics
    "legendre_symbol",
    "quadratic_nonresidue",
    "discriminant",
    "is_singular",
    # counting
    "count_points",
    "count_points_bruteforce",
    "trace_of_frobenius",
    # the zeta function of the curve
    "zeta_numerator",
    "frobenius_eigenvalues",
    "zeta_function_values",
    "zeta_functional_equation_defect",
    "zeta_log_series_defect",
    # RH, twice
    "hasse_check",
    "critical_line_check",
    # Lefschetz
    "frobenius_power_traces",
    "point_counts_over_extensions",
    "fp2_mul",
    "count_points_fp2",
    # sweeps and statistics
    "random_curve",
    "curve_survey",
    "survey_summary",
    "traces_mod_p",
    "sato_tate_histogram",
    "gauss_trace",
    # prose
    "weil_conjecture_facts",
]

#: Extra guard digits carried internally by the mpmath routines and discarded
#: before returning (house convention, cf. :mod:`zeta.core`).
_GUARD: int = 10

_REPO_ROOT = Path(__file__).resolve().parent.parent
_DATA_DIR = _REPO_ROOT / "data"


def _data_dir() -> Path:
    """The repo's ``data/`` cache directory, created on demand."""
    _DATA_DIR.mkdir(parents=True, exist_ok=True)
    return _DATA_DIR


# ---------------------------------------------------------------------------
# validation
# ---------------------------------------------------------------------------

def _is_prime(n: int) -> bool:
    """Deterministic Miller-Rabin for 64-bit n (exact for all n < 3.3e24)."""
    n = int(n)
    if n < 2:
        return False
    for q in (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37):
        if n % q == 0:
            return n == q
    d, r = n - 1, 0
    while d % 2 == 0:
        d //= 2
        r += 1
    for base in (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37):
        x = pow(base, d, n)
        if x == 1 or x == n - 1:
            continue
        for _ in range(r - 1):
            x = x * x % n
            if x == n - 1:
                break
        else:
            return False
    return True


def _check_p(p: int) -> int:
    """Validate the characteristic: a prime ``p > 3``.

    ``p = 2, 3`` are excluded because the short Weierstrass form
    ``y^2 = x^3 + ax + b`` does not classify elliptic curves there (completing
    the square/cube needs 2 and 3 invertible).  Everything in this module
    assumes the short form, so the restriction is enforced rather than papered
    over.
    """
    p = int(p)
    if p <= 3:
        raise ValueError(f"p must be a prime > 3 (short Weierstrass form); got {p}")
    if not _is_prime(p):
        raise ValueError(f"p must be prime; {p} is composite")
    return p


def _check_curve(a: int, b: int, p: int) -> tuple[int, int, int]:
    """Validate ``(a, b, p)`` and return them reduced mod p.

    Raises :class:`ValueError` if p is not a prime > 3, or if the curve is
    singular (``4a^3 + 27b^2 == 0`` in F_p), a singular cubic is not an
    elliptic curve, its point count does not satisfy the Hasse bound, and its
    zeta function is not the one implemented here.
    """
    p = _check_p(p)
    a, b = int(a) % p, int(b) % p
    if (4 * a ** 3 + 27 * b ** 2) % p == 0:
        raise ValueError(
            f"singular curve: 4a^3 + 27b^2 = 0 mod {p} for a={a}, b={b} "
            "(not an elliptic curve)"
        )
    return a, b, p


# ---------------------------------------------------------------------------
# 1. the finite field: Legendre symbols and F_{p^2}
# ---------------------------------------------------------------------------

def legendre_symbol(a: int, p: int) -> int:
    """The Legendre symbol ``(a|p)`` in {-1, 0, +1}, by Euler's criterion.

    Returns 0 if ``p | a``, +1 if a is a nonzero quadratic residue mod p, and
    -1 otherwise.  Computed as ``a^{(p-1)/2} mod p``, the definition, not a
    table lookup, so it is an independent implementation from the cached
    residue table used by :func:`count_points`.

    ``p`` must be an odd prime (``p > 3`` is enforced, as everywhere in this
    module).  Cross-checked against :func:`sympy.legendre_symbol` in the tests.
    """
    p = _check_p(p)
    a = int(a) % p
    if a == 0:
        return 0
    return 1 if pow(a, (p - 1) // 2, p) == 1 else -1


@lru_cache(maxsize=64)
def _chi_table(p: int) -> tuple[int, ...]:
    """``(chi(0), ..., chi(p-1))`` with chi the quadratic character mod p.

    Built by squaring every residue (O(p)), which is a different route from
    :func:`legendre_symbol`'s Euler criterion; ``test_chi_table_matches_the_
    euler_criterion`` asserts the two agree for every residue of six primes up
    to 10007, and ``test_count_points_equals_brute_force_exhaustively`` checks
    the consequence for every curve over every prime up to 43.
    """
    chi = [-1] * p
    chi[0] = 0
    for x in range(1, (p + 1) // 2):
        chi[x * x % p] = 1
    return tuple(chi)


def quadratic_nonresidue(p: int) -> int:
    """The least ``n`` in ``2 <= n < p`` with ``(n|p) = -1``.

    Used to build F_{p^2} = F_p[t]/(t^2 - n).  (n = 1 is never a non-residue,
    so the search starts at 2; a non-residue always exists because exactly
    (p-1)/2 of the nonzero residues are squares.)
    """
    p = _check_p(p)
    chi = _chi_table(p)
    for n in range(2, p):
        if chi[n] == -1:
            return n
    raise RuntimeError(f"no quadratic non-residue mod {p} -- impossible")  # pragma: no cover


def fp2_mul(
    u: tuple[int, int], v: tuple[int, int], p: int, n: int
) -> tuple[int, int]:
    """Multiply in ``F_{p^2} = F_p[t]/(t^2 - n)``.

    Elements are pairs ``(u0, u1)`` meaning ``u0 + u1 * t`` with ``t^2 = n``,
    n a quadratic non-residue mod p (so ``t^2 - n`` is irreducible).  Then

        (u0 + u1 t)(v0 + v1 t) = (u0 v0 + n u1 v1) + (u0 v1 + u1 v0) t.

    Pure integer arithmetic; no validation, this is the inner loop of
    :func:`count_points_fp2`.
    """
    return ((u[0] * v[0] + n * u[1] * v[1]) % p, (u[0] * v[1] + u[1] * v[0]) % p)


# ---------------------------------------------------------------------------
# 2. the curve: discriminant and point counting
# ---------------------------------------------------------------------------

def discriminant(a: int, b: int, p: int) -> int:
    """The discriminant ``Delta = -16(4a^3 + 27b^2)`` of ``y^2 = x^3+ax+b``, mod p.

    Zero exactly when the curve is singular.  (The factor -16 is a unit mod any
    ``p > 3``, so ``Delta == 0`` and ``4a^3 + 27b^2 == 0`` are the same
    condition; both forms appear in the literature and this module tests that
    they agree.)  Accepts singular ``(a, b)``, it is the function that detects
    them.
    """
    p = _check_p(p)
    return (-16 * (4 * int(a) ** 3 + 27 * int(b) ** 2)) % p


def is_singular(a: int, b: int, p: int) -> bool:
    """``True`` when ``y^2 = x^3 + ax + b`` is singular over F_p."""
    return discriminant(a, b, p) == 0


def count_points(a: int, b: int, p: int) -> int:
    """``N_1 = #E(F_p)``, including the point at infinity.

    For each ``x in F_p`` the equation ``y^2 = f(x)`` has ``1 + chi(f(x))``
    solutions y (2 if f(x) is a nonzero square, 1 if f(x) = 0, 0 otherwise), so

        N_1 = 1 + sum_{x in F_p} (1 + chi(f(x))) = p + 1 + sum_x chi(f(x)),

    the leading 1 being the point at infinity.  Cost O(p) with a cached
    character table.  :func:`count_points_bruteforce` recomputes the same
    number by enumerating all ``p^2`` pairs (x, y) with no character theory at
    all; the tests assert they agree for every nonsingular curve over every
    prime up to 61.

    Raises :class:`ValueError` for singular curves and for ``p <= 3``/composite.
    """
    a, b, p = _check_curve(a, b, p)
    chi = _chi_table(p)
    total = p + 1
    for x in range(p):
        total += chi[(x * x % p * x + a * x + b) % p]
    return total


def count_points_bruteforce(a: int, b: int, p: int) -> int:
    """``N_1`` by literal enumeration of all ``p^2`` pairs ``(x, y)`` in F_p^2.

    The independent oracle for :func:`count_points`: no Legendre symbols, no
    Euler criterion, just "is ``y^2 - f(x)`` zero mod p".  O(p^2), intended
    for p up to a few hundred.
    """
    a, b, p = _check_curve(a, b, p)
    total = 1  # the point at infinity
    for x in range(p):
        rhs = (x * x % p * x + a * x + b) % p
        for y in range(p):
            if y * y % p == rhs:
                total += 1
    return total


def trace_of_frobenius(a: int, b: int, p: int) -> int:
    """``a_p = p + 1 - N_1``, the trace of Frobenius on the curve.

    Exact integer.  This is the single number that determines the whole zeta
    function of E, and the whole RH statement for it.
    """
    a, b, p = _check_curve(a, b, p)
    return p + 1 - count_points(a, b, p)


# ---------------------------------------------------------------------------
# 3. the zeta function of the curve
# ---------------------------------------------------------------------------

def zeta_numerator(a: int, b: int, p: int) -> list[int]:
    """The numerator ``P(T) = 1 - a_p T + p T^2`` as coefficients ``[1, -a_p, p]``.

    Ascending powers of T: ``[c0, c1, c2]`` means ``c0 + c1 T + c2 T^2``.  This
    is ``det(1 - Frob * T | H^1_et)``, the only interesting factor of the zeta
    function; the ``H^0`` and ``H^2`` factors give the trivial denominator
    ``(1 - T)(1 - pT)``.
    """
    a, b, p = _check_curve(a, b, p)
    return [1, -(p + 1 - count_points(a, b, p)), p]


def frobenius_eigenvalues(
    a: int, b: int, p: int, dps: int = DPS_DEFAULT
) -> tuple[mpmath.mpc, mpmath.mpc]:
    """The Frobenius eigenvalue pair ``(alpha, alphabar)``.

    The roots of ``x^2 - a_p x + p`` (reciprocals of the roots of the zeta
    numerator).  Since ``|a_p| <= 2 sqrt(p)`` with equality impossible for a
    prime p (it would force p to be a perfect square), the discriminant
    ``4p - a_p^2`` is a positive integer and the eigenvalues are a genuine
    complex-conjugate pair

        alpha = a_p/2 + i sqrt(4p - a_p^2)/2,    alphabar = conj(alpha),

    with ``alpha * alphabar = p`` and hence ``|alpha| = sqrt(p)``: RH for E.
    Returned as mpmath ``mpc`` at the requested ``dps`` (guard digits used
    internally).  ``alpha`` is the root in the upper half-plane.
    """
    a, b, p = _check_curve(a, b, p)
    ap = p + 1 - count_points(a, b, p)
    disc = 4 * p - ap * ap
    if disc <= 0:  # pragma: no cover - impossible for prime p (Hasse + p non-square)
        raise RuntimeError(
            f"4p - a_p^2 = {disc} <= 0 for a={a}, b={b}, p={p}: "
            "this would be a Hasse violation, i.e. a bug"
        )
    with mp.workdps(dps + _GUARD):
        half = mp.mpf(ap) / 2
        imag = mp.sqrt(mp.mpf(disc)) / 2
        alpha = mp.mpc(half, imag)
    with mp.workdps(dps):
        return +alpha, mp.conj(+alpha)


def zeta_function_values(a: int, b: int, p: int, T, dps: int = DPS_DEFAULT):
    """``Z(T) = (1 - a_p T + p T^2) / ((1 - T)(1 - p T))`` evaluated at ``T``.

    ``T`` may be any real or complex value (Python or mpmath); the result is an
    mpmath ``mpf``/``mpc`` at the requested ``dps``.  The two poles ``T = 1``
    and ``T = 1/p`` (the H^0 and H^2 contributions) raise :class:`ValueError`.

    Pole detection is *exact*, never a tolerance: an ``int``, ``float`` or
    ``fractions.Fraction`` argument is converted to an exact rational and
    compared with 1 and 1/p, and any other argument is caught only if the
    denominator evaluates to exactly zero.  So ``Fraction(1, p)`` raises while
    the float ``1/p``, which is a *different* rational number, returns the
    (large, finite, correct) value of Z there.  That is deliberate: silently
    treating "close to the pole" as "at the pole" would hide real numerics.

    The defining identity ``Z(T) = exp(sum_n N_n T^n / n)`` is checked by
    :func:`zeta_log_series_defect`, and the functional equation
    ``Z(1/(pT)) = Z(T)`` by :func:`zeta_functional_equation_defect`.
    """
    a, b, p = _check_curve(a, b, p)
    ap = p + 1 - count_points(a, b, p)
    try:
        q = Fraction(T)
    except (TypeError, ValueError, OverflowError):
        q = None
    if q is not None and (q == 1 or q * p == 1):
        raise ValueError(
            f"T = {T} is a pole of Z (T = 1 and T = 1/p are the H^0/H^2 poles)"
        )
    with mp.workdps(dps + _GUARD):
        t = mp.mpmathify(T)
        den = (1 - t) * (1 - p * t)
        if den == 0:
            raise ValueError(
                f"T = {T} is a pole of Z (T = 1 and T = 1/p are the H^0/H^2 poles)"
            )
        val = (1 - ap * t + p * t ** 2) / den
    with mp.workdps(dps):
        return +val


def zeta_functional_equation_defect(
    a: int, b: int, p: int, T, dps: int = DPS_DEFAULT
):
    """``|Z(1/(pT)) - Z(T)|``, the curve's functional equation, as a defect.

    For a genus-1 curve the functional equation is ``Z(1/(pT)) = Z(T)``, which
    under ``T = p^{-s}`` reads ``s <-> 1 - s``: the exact analogue of
    ``xi(s) = xi(1-s)``, mirror axis ``Re(s) = 1/2``.  It is an *algebraic
    identity* here (the numerator is self-reciprocal, ``p T^2 P(1/(pT)) = P(T)``),
    so the returned number is pure round-off at the *requested* working
    precision: both sides are evaluated at ``dps`` and subtracted at ``dps``,
    which is a few ulp of ``|Z(T)|``.  Measured worst case over six curves and
    five values of T (real, negative and complex): 2.487e-14 at dps = 15,
    9.466e-30 at dps = 30, 3.421e-49 at dps = 50, pinned two-sided in the
    tests, to within a factor of three, so a silent loss of precision *or* a
    silently vacuous zero would both fail.

    Reported as a measured defect rather than asserted, in the house style.
    """
    a, b, p = _check_curve(a, b, p)
    with mp.workdps(dps):
        t = mp.mpmathify(T)
        if t == 0:
            raise ValueError("T = 0 is not in the domain of T -> 1/(pT)")
        lhs = zeta_function_values(a, b, p, 1 / (p * t), dps=dps)
        rhs = zeta_function_values(a, b, p, t, dps=dps)
        return abs(lhs - rhs)


def zeta_log_series_defect(
    a: int, b: int, p: int, n_max: int = 60, T=None, dps: int = DPS_DEFAULT
):
    """``|Z(T) - exp(sum_{n<=n_max} N_n T^n / n)|`` at a small ``T``.

    This is the *definition* of the zeta function of a variety (left) checked
    against Weil's rational formula (right).  ``N_n`` comes from
    :func:`point_counts_over_extensions`, i.e. from the Frobenius power sums,
    so the identity being measured is "counting solutions in every extension
    == a rational function of one integer a_p".

    Default ``T = 1/(10p)``, well inside the radius of convergence ``1/p``.
    Because ``N_n ~ p^n``, the terms are ``N_n T^n / n ~ 10^{-n}/n``, the
    truncation tail is ``~10^{-(n_max+1)}/(n_max+1)``, *independent of p*, so
    ``n_max`` must be raised in step with ``dps``.  Everything is evaluated at
    the requested ``dps``, so the number returned describes that precision
    honestly.  Measured over six curves (p = 7 .. 10007): exactly 0.0 at
    dps = 30 and dps = 50 with ``n_max = 60``; 2.2e-16 at dps = 15; and
    3.0e-43 at dps = 50 with ``n_max = 40``, which is the predicted truncation
    ``10^{-41}/41 = 2.4e-43`` and not round-off.
    """
    a, b, p = _check_curve(a, b, p)
    with mp.workdps(dps):
        t = mp.mpf(1) / (10 * p) if T is None else mp.mpmathify(T)
        counts = point_counts_over_extensions(a, b, p, n_max)
        series = mp.fsum(mp.mpf(counts[n - 1]) * t ** n / n for n in range(1, n_max + 1))
        return abs(zeta_function_values(a, b, p, t, dps=dps) - mp.exp(series))


# ---------------------------------------------------------------------------
# 4. RH for the curve, stated twice: Hasse bound and critical line
# ---------------------------------------------------------------------------

def hasse_check(a: int, b: int, p: int) -> dict[str, Any]:
    """RH for E in its counting form: ``|a_p| <= 2 sqrt(p)``.

    Returns a dict with

    ``a_p``        the trace of Frobenius (exact int),
    ``bound``      ``2 sqrt(p)`` (float),
    ``satisfied``  ``|a_p| <= bound``: always ``True``; it is a theorem,
    ``ratio``      ``|a_p| / (2 sqrt(p))`` in [0, 1), how close this curve
                   comes to the bound (0 = supersingular),

    plus ``p``, ``a``, ``b``, ``N_1`` for provenance.

    The comparison is done in exact integers (``a_p^2 <= 4p``) and the float
    ``ratio`` is reported for information only, so ``satisfied`` can never be
    a floating-point artefact.
    """
    a, b, p = _check_curve(a, b, p)
    n1 = count_points(a, b, p)
    ap = p + 1 - n1
    bound = 2.0 * math.sqrt(p)
    return {
        "p": p,
        "a": a,
        "b": b,
        "N_1": n1,
        "a_p": ap,
        "bound": bound,
        "satisfied": ap * ap <= 4 * p,  # exact integer comparison
        "ratio": abs(ap) / bound,
    }


def critical_line_check(
    a: int, b: int, p: int, dps: int = DPS_DEFAULT
) -> dict[str, Any]:
    """RH for E in its *critical-line* form: the numerator roots have Re(s) = 1/2.

    Substituting ``T = p^{-s}`` into the zeta numerator sends a root
    ``T_0 = 1/alpha`` to ``s = log(alpha)/log(p)``, so

        Re(s) = log|alpha| / log(p) = log(sqrt p)/log p = 1/2.

    Returns a dict with

    ``re_s``                      the two real parts, as mpf,
    ``im_s``                      the two imaginary parts, as mpf,
    ``max_deviation_from_half``   ``max |Re(s) - 1/2|`` as a Python float,
    ``roots_T``                   the numerator roots ``1/alpha, 1/alphabar``,
    ``eigenvalues``               ``(alpha, alphabar)``,
    ``abs_alpha_defect``          ``max | |alpha| - sqrt(p) |``,

    plus ``p``, ``a``, ``b``, ``a_p``, ``dps``.

    ``max_deviation_from_half`` is measured on the *unrounded* internal values,
    at the internal working precision ``dps + 10``, rounding to ``dps`` first
    would return a vacuous 0.0 every time, since the true value is 1/2 and the
    error is far below the last returned digit.  So the number is genuine
    ``log``/``sqrt`` round-off, and a bug in the s-coordinate conversion would
    inflate it.  Measured worst case over an 862-curve sweep (18 primes from 5
    to 10007): 8.5e-22 at dps = 10, 9.9e-32 at dps = 20, 1.1e-41 at dps = 30,
    7.8e-62 at dps = 50, i.e. about ``10^{-(dps+11)}``, far inside the 1e-12
    the tests demand.  The ``re_s`` values as returned, rounded to ``dps``
    digits, are exactly ``mpf('0.5')``.

    The two ``im_s`` values are ``+/- arg(alpha)/log(p)``; they are defined only
    modulo
    ``2 pi / log p``, because ``p^{-s}`` is periodic, the finite-field zeros
    live on a *circle*, not a line, which is precisely the structure the
    integers are missing (``docs/11``).
    """
    a, b, p = _check_curve(a, b, p)
    ap = p + 1 - count_points(a, b, p)
    with mp.workdps(dps + _GUARD):
        alpha, alphabar = frobenius_eigenvalues(a, b, p, dps=dps + _GUARD)
        logp = mp.log(p)
        s = [mp.log(alpha) / logp, mp.log(alphabar) / logp]
        re_s = [mp.re(z) for z in s]
        im_s = [mp.im(z) for z in s]
        sqrtp = mp.sqrt(p)
        adef = max(abs(abs(z) - sqrtp) for z in (alpha, alphabar))
        roots = [1 / alpha, 1 / alphabar]
        # Measured on the UNROUNDED guard-precision values: rounding to dps
        # first would send the deviation to a vacuous 0.0 every time.
        half = mp.mpf(1) / 2
        dev = max(abs(r - half) for r in re_s)
    with mp.workdps(dps):
        return {
            "p": p,
            "a": a,
            "b": b,
            "a_p": ap,
            "dps": dps,
            "re_s": [+r for r in re_s],
            "im_s": [+i for i in im_s],
            "max_deviation_from_half": float(dev),
            "roots_T": [+r for r in roots],
            "eigenvalues": (+alpha, +alphabar),
            "abs_alpha_defect": float(adef),
        }


# ---------------------------------------------------------------------------
# 5. Lefschetz: solution counts as traces of powers of an operator
# ---------------------------------------------------------------------------

def frobenius_power_traces(a: int, b: int, p: int, n_max: int) -> list[int]:
    """``[t_1, ..., t_{n_max}]`` with ``t_n = alpha^n + alphabar^n``, exact integers.

    Newton's recursion for the power sums of ``x^2 - a_p x + p``:

        t_0 = 2,   t_1 = a_p,   t_n = a_p * t_{n-1} - p * t_{n-2}.

    These are ``Tr(Frob^n | H^1_et)``.  They are integers even though alpha is
    not real, and computing them by the recursion instead of by exponentiating
    a complex number keeps :func:`point_counts_over_extensions` exact.
    """
    a, b, p = _check_curve(a, b, p)
    n_max = int(n_max)
    if n_max < 1:
        raise ValueError(f"n_max must be >= 1; got {n_max}")
    ap = p + 1 - count_points(a, b, p)
    t = [2, ap]
    for n in range(2, n_max + 1):
        t.append(ap * t[n - 1] - p * t[n - 2])
    return t[1 : n_max + 1]


def point_counts_over_extensions(a: int, b: int, p: int, n_max: int) -> list[int]:
    """``[N_1, ..., N_{n_max}]`` with ``N_n = #E(F_{p^n})``, exact integers.

    The Lefschetz fixed-point formula for the curve:

        N_n = p^n + 1 - (alpha^n + alphabar^n)
            = Tr(Frob^n|H^0) - Tr(Frob^n|H^1) + Tr(Frob^n|H^2)

    with ``Tr(Frob^n|H^0) = 1``, ``Tr(Frob^n|H^2) = p^n``.  *Counting solutions
    became linear algebra*, this list is a signed sum of traces of powers of
    one 2x2 operator, and it is the whole content of the curve's zeta function.

    ``N_1`` is verified against brute force by :func:`count_points_bruteforce`
    and ``N_2`` against an independent enumeration over F_{p^2} by
    :func:`count_points_fp2`; both are standing tests.
    """
    traces = frobenius_power_traces(a, b, p, n_max)
    p = int(p)
    return [p ** n + 1 - traces[n - 1] for n in range(1, n_max + 1)]


def count_points_fp2(a: int, b: int, p: int, method: str = "table") -> int:
    """``N_2 = #E(F_{p^2})`` by brute-force enumeration over F_{p^2}.

    **No zeta function, no eigenvalues, no Weil theory is used here.**  F_{p^2}
    is built explicitly as ``F_p[t]/(t^2 - n)`` with ``n =
    quadratic_nonresidue(p)``, arithmetic by :func:`fp2_mul`, and the points of
    ``y^2 = x^3 + ax + b`` are counted directly; the point at infinity is added
    by hand.

    ``method``:

    ``"pairs"``  the literal double loop over all ``p^4`` pairs ``(x, y)``,
                 unambiguous, O(p^4), usable to about p = 13;
    ``"table"``  (default) tabulate ``y -> y^2`` once over the ``p^2`` elements
                 of the field, then look up ``f(x)`` for each of the ``p^2``
                 values of x.  Same enumeration, O(p^2), usable to p ~ 200.

    The tests assert both agree with each other *and* with
    ``point_counts_over_extensions(a, b, p, 2)[1]``: the Lefschetz prediction
    from the two complex Frobenius eigenvalues.  That agreement is this
    module's central demonstration that the operator picture is real.

    Both methods share one presentation of F_{p^2}, so a mistake in the
    reduction rule would corrupt them together; the test suite therefore repeats
    the count in a *second* presentation ``F_p[t]/(t^2 - c t - d)`` built by
    code outside this module (all 328 curves for p = 5, 7, 11, 13), and a third
    time via ``N_2 = N_1 * N_1(twist)`` with the twist counted over F_p rather
    than deduced from a_p.
    """
    a, b, p = _check_curve(a, b, p)
    n = quadratic_nonresidue(p)

    def rhs(x0: int, x1: int) -> tuple[int, int]:
        x = (x0, x1)
        x3 = fp2_mul(fp2_mul(x, x, p, n), x, p, n)
        return ((x3[0] + a * x0 + b) % p, (x3[1] + a * x1) % p)

    if method == "pairs":
        total = 1
        for x0 in range(p):
            for x1 in range(p):
                r = rhs(x0, x1)
                for y0 in range(p):
                    for y1 in range(p):
                        if fp2_mul((y0, y1), (y0, y1), p, n) == r:
                            total += 1
        return total
    if method != "table":
        raise ValueError(f"method must be 'pairs' or 'table'; got {method!r}")

    squares: dict[tuple[int, int], int] = {}
    for y0 in range(p):
        for y1 in range(p):
            s = fp2_mul((y0, y1), (y0, y1), p, n)
            squares[s] = squares.get(s, 0) + 1
    total = 1
    for x0 in range(p):
        for x1 in range(p):
            total += squares.get(rhs(x0, x1), 0)
    return total


# ---------------------------------------------------------------------------
# 6. sweeps: RH checked on many curves at once
# ---------------------------------------------------------------------------

def random_curve(p: int, rng: random.Random | None = None) -> tuple[int, int]:
    """A uniformly random *nonsingular* ``(a, b)`` over F_p (rejection sampling).

    Exactly ``p^2 - p`` of the ``p^2`` pairs are nonsingular (an identity the
    tests verify), so the acceptance rate is ``1 - 1/p`` and the loop is short.
    """
    p = _check_p(p)
    rng = rng or random.Random()
    while True:
        a, b = rng.randrange(p), rng.randrange(p)
        if (4 * a ** 3 + 27 * b ** 2) % p != 0:
            return a, b


def curve_survey(
    p_list: Sequence[int] | Iterable[int] = (5, 13, 101, 1009),
    n_curves_per_p: int = 12,
    seed: int = 20260801,
    dps: int = DPS_DEFAULT,
) -> list[dict[str, Any]]:
    """Sweep many curves over many primes and check RH on each one.

    For every ``p`` in ``p_list``, ``n_curves_per_p`` *distinct* nonsingular
    curves are drawn (seeded from ``seed`` and ``p``, hence reproducible and
    stable when other primes are added to ``p_list``; if ``n_curves_per_p`` is
    at least the number ``p^2 - p`` of nonsingular curves mod p, *all* of them
    are used instead of sampling).  Each row is a dict:

    ``p, a, b, N_1, a_p``          the counting data (exact ints),
    ``bound, satisfied, ratio``    from :func:`hasse_check`,
    ``re_s``                       the two ``Re(s)`` values as floats,
    ``max_deviation_from_half``    from :func:`critical_line_check`,
    ``alpha_abs``                  ``|alpha|`` as a float (should be sqrt p).

    **Every row has ``satisfied = True``.**  Not because the sample was lucky:
    Hasse's theorem forbids anything else.  Use :func:`survey_summary` to
    reduce the rows to counts of violations and worst-case deviations.
    """
    rows: list[dict[str, Any]] = []
    for p in p_list:
        p = _check_p(p)
        # per-prime stream, derived from the seed: reproducible, and independent
        # across primes (so adding a prime to p_list does not reshuffle others).
        rng = random.Random(seed * 1000003 + p)
        n_total = p * p - p
        if n_curves_per_p >= n_total:
            curves = [
                (a, b)
                for a in range(p)
                for b in range(p)
                if (4 * a ** 3 + 27 * b ** 2) % p != 0
            ]
        else:
            seen: set[tuple[int, int]] = set()
            curves = []
            while len(curves) < n_curves_per_p:
                ab = random_curve(p, rng)
                if ab in seen:
                    continue
                seen.add(ab)
                curves.append(ab)
        for a, b in curves:
            h = hasse_check(a, b, p)
            c = critical_line_check(a, b, p, dps=dps)
            rows.append(
                {
                    "p": p,
                    "a": a,
                    "b": b,
                    "N_1": h["N_1"],
                    "a_p": h["a_p"],
                    "bound": h["bound"],
                    "satisfied": h["satisfied"],
                    "ratio": h["ratio"],
                    "re_s": [float(r) for r in c["re_s"]],
                    "max_deviation_from_half": c["max_deviation_from_half"],
                    "alpha_abs": float(abs(c["eigenvalues"][0])),
                }
            )
    return rows


def survey_summary(rows: Sequence[dict[str, Any]]) -> dict[str, Any]:
    """Reduce :func:`curve_survey` rows to the headline numbers.

    Returns ``n_curves``, ``primes``, ``violations`` (count of rows with
    ``satisfied = False``: always 0), ``max_ratio`` (the closest any curve came
    to the Hasse bound), ``max_deviation_from_half`` (worst ``|Re s - 1/2|``
    over the whole sweep) and ``max_alpha_abs_relative_defect``
    (worst ``| |alpha|/sqrt(p) - 1 |``).
    """
    rows = list(rows)
    if not rows:
        raise ValueError("empty survey")
    return {
        "n_curves": len(rows),
        "primes": sorted({r["p"] for r in rows}),
        "violations": sum(1 for r in rows if not r["satisfied"]),
        "max_ratio": max(r["ratio"] for r in rows),
        "max_deviation_from_half": max(r["max_deviation_from_half"] for r in rows),
        "max_alpha_abs_relative_defect": max(
            abs(r["alpha_abs"] / math.sqrt(r["p"]) - 1.0) for r in rows
        ),
    }


# ---------------------------------------------------------------------------
# 7. the vertical Sato-Tate law: "GUE statistics" in the proven universe
# ---------------------------------------------------------------------------

def _row_invariants(counts: np.ndarray, p: int) -> tuple[np.ndarray, np.ndarray]:
    """Exact ``(sum_b a_p(a,b), sum_b a_p(a,b)^2)`` for each row ``a``.

    ``counts[i, v]`` is ``c_v = #{x in F_p : x^3 + a x = v}`` for the i-th row.
    With ``a_p(a, b) = -sum_x chi(x^3 + a x + b)`` and ``sum_{c in F_p} chi(c) = 0``:

    * ``sum_b a_p(a,b) = -sum_x sum_b chi(x^3+ax+b) = 0``, because for fixed x
      the argument runs over all of F_p as b does;
    * ``sum_b a_p(a,b)^2 = sum_{x,y} sum_b chi((u_x+b)(u_y+b))`` with
      ``u_x = x^3+ax``.  The inner sum is ``p - 1`` when ``u_x = u_y`` and
      ``-1`` otherwise (a standard evaluation of ``sum_b chi(b^2 + sb + t)``),
      so the total is ``p * #{(x,y) : u_x = u_y} - p^2 = p * sum_v c_v^2 - p^2``.

    Both are pure integer identities, derived here and verified against a
    straight O(p^2) integer computation in the tests.  They are what makes the
    float64 FFT in :func:`traces_mod_p` safe: a rounding error big enough to
    land on the wrong integer changes the sum of squares (moving one value m by
    +/-1 changes it by +/-2m+1, which is never 0), so the check below fires.
    """
    sq = (counts.astype(np.int64) ** 2).sum(axis=1)
    return np.zeros(counts.shape[0], dtype=np.int64), p * sq - p * p


def _verify_trace_rows(rows: np.ndarray, counts: np.ndarray, p: int) -> int:
    """Raise unless every row of ``rows`` satisfies both exact identities.

    Returns the number of rows verified; raises :class:`RuntimeError`, naming
    the offending row, on any mismatch.  All comparisons are integer equality,
    there is no tolerance to tune and nothing that can be passed vacuously.
    """
    want_sum, want_sq = _row_invariants(counts, p)
    got_sum = rows.sum(axis=1)
    got_sq = (rows.astype(np.int64) ** 2).sum(axis=1)
    bad = np.flatnonzero((got_sum != want_sum) | (got_sq != want_sq))
    if bad.size:
        i = int(bad[0])
        raise RuntimeError(
            f"integer recovery failed at p = {p}: row {i} has "
            f"sum {int(got_sum[i])} (want {int(want_sum[i])}) and sum of squares "
            f"{int(got_sq[i])} (want {int(want_sq[i])}); the float64 FFT did not "
            "reproduce the exact character sums"
        )
    return int(rows.shape[0])


def traces_mod_p(p: int) -> np.ndarray:
    """``a_p`` for *every* nonsingular curve ``y^2 = x^3+ax+b`` over F_p.

    Returns a 1-D ``int64`` array of length ``p^2 - p`` (all pairs (a, b) minus
    the p singular ones), in row-major (a, b) order with the singular pairs
    dropped.

    Vectorised: for each ``a``, ``sum_x chi(x^3 + ax + b)`` for *all* b at once
    is a cyclic correlation of the multiplicity vector of ``x -> x^3 + ax``
    with the character table, evaluated by FFT.  Total cost O(p^2 log p).

    Every value being recovered is an integer of size at most p, restored from
    the float64 FFT with ``np.rint``.  Rounding by itself proves nothing, an
    error of 0.9 rounds to the *wrong* integer while leaving a residual of only
    0.1, so the recovered rows are checked against two exact integer
    identities (:func:`_row_invariants`), ``sum_b a_p = 0`` and
    ``sum_b a_p^2 = p sum_v c_v^2 - p^2``, computed from the integer
    multiplicity vector and not from the FFT.  A mis-rounded entry breaks the
    second identity, and the function raises rather than return wrong integers.
    A loose residual guard (0.25) is kept as an early diagnostic.  The residual
    observed here was 1.8e-14 at p = 101 rising to 3.8e-13 at p = 4001, twelve
    orders of magnitude below the 0.5 that would matter, but that is a
    platform-dependent float64 measurement and is deliberately *not* pinned by
    a test; the exact identities above are what guarantee the output.

    The result is further cross-checked in the tests against
    :func:`trace_of_frobenius` (exhaustively at p = 53) and against an FFT-free
    O(p^3) integer matmul (p = 23, 101).

    Timing on the machine this was written on (indicative only, not pinned by a
    test): 0.04 s at p = 503, 0.15 s at p = 1009, 0.8 s at p = 2003, 2.9 s at
    p = 4001 (16 004 000 curves).
    """
    p = _check_p(p)
    x = np.arange(p, dtype=np.int64)
    chi = np.array(_chi_table(p), dtype=np.int64)
    cube = (x * x % p * x) % p
    # S(a, b) = sum_v c_a[v] * chi[(v + b) mod p] = (c_a * h)[(-b) mod p]
    # with h[k] = chi[(-k) mod p] and * cyclic convolution.
    h = chi[(-x) % p].astype(np.float64)
    H = np.fft.rfft(h)
    idx = (-x) % p
    block = max(1, min(p, 2_000_000 // p + 1))
    out = np.empty((p, p), dtype=np.int64)
    for a0 in range(0, p, block):
        a1 = min(a0 + block, p)
        nb = a1 - a0
        aa = np.arange(a0, a1, dtype=np.int64).reshape(-1, 1)
        u = (cube.reshape(1, -1) + aa * x.reshape(1, -1)) % p
        # row-offset trick: one bincount instead of a slow np.add.at
        flat = (u + (np.arange(nb, dtype=np.int64) * p).reshape(-1, 1)).ravel()
        counts = np.bincount(flat, minlength=nb * p).reshape(nb, p)
        c = counts.astype(np.float64)
        conv = np.fft.irfft(np.fft.rfft(c, axis=1) * H, n=p, axis=1)[:, idx]
        rounded = np.rint(conv)
        slack = float(np.abs(conv - rounded).max())
        if slack > 0.25:  # pragma: no cover - would need p ~ 1e6+
            raise RuntimeError(
                f"FFT round-off {slack:.3g} too large to recover exact integers "
                f"at p = {p}; use the direct O(p^3) route instead"
            )
        block_out = -rounded.astype(np.int64)
        _verify_trace_rows(block_out, counts, p)  # exact, not a tolerance
        out[a0:a1, :] = block_out
    aa = np.arange(p, dtype=np.int64).reshape(-1, 1)
    bb = np.arange(p, dtype=np.int64).reshape(1, -1)
    nonsingular = (4 * aa ** 3 + 27 * bb ** 2) % p != 0
    return out[nonsingular]


def _sato_tate_cache_path(p: int) -> Path:
    return _data_dir() / f"finitefield_ap_counts_p{p}.json"


def _trace_counts_are_consistent(value_counts: dict[int, int], p: int) -> bool:
    """Exact integrity check on a loaded ``a_p`` value-count table.

    ``data/`` caches are keyed on ``p`` alone, so a cache written by earlier
    code would otherwise be trusted forever (the failure mode AGENTS.md warns
    about: "stale numbers will pass").  Four *proved* identities pin the
    multiset tightly enough that a stale or corrupt table is rejected and
    recomputed rather than used:

    * ``sum of the counts = p^2 - p``      (the number of nonsingular curves),
    * ``max |a_p| <= 2 sqrt p``            (Hasse),
    * ``sum a_p = 0``                      (quadratic twisting is an involution
      of the curve set that negates a_p),
    * ``sum a_p^2 = (p-1)^2 (p+1)``        (the closed form verified in the
      tests against a per-curve integer computation up to p = 53 and against
      the sweep up to p = 503).

    All arithmetic is exact ``int``; there is no tolerance anywhere.
    """
    if not value_counts:
        return False
    if any(c <= 0 for c in value_counts.values()):
        return False
    if sum(value_counts.values()) != p * p - p:
        return False
    if any(t * t > 4 * p for t in value_counts):
        return False
    if sum(t * c for t, c in value_counts.items()) != 0:
        return False
    return sum(t * t * c for t, c in value_counts.items()) == (p - 1) ** 2 * (p + 1)


def sato_tate_histogram(
    p: int, n_bins: int = 20, cache: bool = True
) -> dict[str, Any]:
    """The vertical Sato-Tate law: ``a_p / (2 sqrt p)`` over ALL curves mod p.

    This is the finite-field analogue of the GUE story in
    :mod:`zeta.statistics`: the statistics of "the zeros" in the universe where
    RH is proved.  Every curve's normalised trace lies in ``[-1, 1]`` (that is
    RH), and as ``p -> infinity`` the empirical distribution over all
    ``p^2 - p`` curves converges to the **semicircle** density
    ``(2/pi) sqrt(1 - x^2)``.

    This is *vertical* Sato-Tate, fixed p, all curves, a THEOREM (Birch,
    *How the number of points of an elliptic curve over a fixed prime field
    varies*, J. London Math. Soc. 43 (1968), 57-60, via the Eichler-Selberg
    trace formula).  It is not the horizontal Sato-Tate conjecture (one curve,
    varying p), which needed Taylor et al. 2008-11.  Do not conflate them.

    Returns a dict with

    ``p, n_curves, n_bins``      the setup (``n_curves = p^2 - p``),
    ``bin_edges, counts``        histogram of ``a_p/(2 sqrt p)`` on [-1, 1],
    ``density``                  counts normalised to a probability density,
    ``semicircle``               ``(2/pi) sqrt(1-x^2)`` at the bin midpoints,
    ``sup_deviation, l1_deviation``  density vs semicircle,
    ``moments``                  measured ``mean(x^{2k})`` for k = 1, 2, 3,
    ``semicircle_moments``       their limits ``C_k/4^k`` = 1/4, 1/8, 5/64
                                 (Catalan numbers 1, 2, 5), approached like
                                 ``1/(4p^2)``: measured deviations
                                 (2.45e-5, 1.84e-5, 1.39e-5) at p = 101 and
                                 (6.23e-8, 4.67e-8, 3.51e-8) at p = 2003,
    ``second_moment_exact``      ``sum a_p^2`` as an exact int, and
    ``second_moment_closed_form``  ``(p-1)^2 (p+1)``: an identity that holds
                                 *exactly*, verified for every prime tested
                                 (so ``mean(x^2) = (p^2-1)/(4p^2)``, which is
                                 why the measured second moment is 1/4 to
                                 ~1e-6 already at p = 503),
    ``sum_a_p``                  0, exactly: quadratic twisting ``(a,b) ->
                                 (d^2 a, d^3 b)`` with d a non-residue is a
                                 bijection of curves that negates ``a_p``, so
                                 the whole multiset is symmetric,
    ``max_abs_a_p``, ``hasse_violations`` (0),
    ``distinct_traces``, ``hasse_interval_size``: equal, because *every*
                                 integer t with ``|t| <= 2 sqrt p`` occurs as
                                 some curve's trace (Deuring 1941).

    Cost is O(p^2 log p) plus O(p^2) memory; ``p = 1009`` takes ~0.2 s.  The
    ``a_p`` value-counts are cached to ``data/finitefield_ap_counts_p{p}.json``.

    Measured convergence (n_bins = 20): sup deviation of the density from the
    semicircle is 0.2183 at p = 503, 0.1224 at p = 1009, **0.1404 at p = 2003**
    and 0.0540 at p = 4001.  Note the p = 2003 entry: the sup deviation is *not*
    monotone in p, because with 20 bins over ``[-1, 1]`` each bin holds only
    ``~ 0.1 * 2 sqrt p`` of the integer trace values and the lattice lands
    differently for each p.  Convergence is genuinely slow; the moments converge
    much faster (see ``second_moment_closed_form``).
    """
    p = _check_p(p)
    n_bins = int(n_bins)
    if n_bins < 1:
        raise ValueError(f"n_bins must be >= 1; got {n_bins}")

    path = _sato_tate_cache_path(p)
    value_counts: dict[int, int] | None = None
    if cache and path.exists():
        try:
            raw = json.loads(path.read_text())
            if int(raw.get("p", -1)) == p:
                value_counts = {int(k): int(v) for k, v in raw["counts"].items()}
        except (ValueError, KeyError, OSError, TypeError):  # corrupt cache
            value_counts = None
        # a cache that fails the exact identities is stale or damaged: drop it
        # and recompute rather than silently return old numbers.
        if value_counts is not None and not _trace_counts_are_consistent(value_counts, p):
            value_counts = None
    if value_counts is None:
        traces = traces_mod_p(p)
        vals, cnts = np.unique(traces, return_counts=True)
        value_counts = {int(v): int(c) for v, c in zip(vals, cnts)}
        if cache:
            try:
                path.write_text(
                    json.dumps(
                        {"p": p, "counts": {str(k): v for k, v in value_counts.items()}},
                        indent=1,
                    )
                )
            except OSError:  # pragma: no cover
                pass

    ts = np.array(sorted(value_counts), dtype=np.int64)
    ws = np.array([value_counts[int(t)] for t in ts], dtype=np.int64)
    n_curves = int(ws.sum())

    scale = 2.0 * math.sqrt(p)
    xs = ts.astype(np.float64) / scale
    counts, bin_edges = np.histogram(xs, bins=n_bins, range=(-1.0, 1.0), weights=ws)
    width = 2.0 / n_bins
    density = counts.astype(np.float64) / (n_curves * width)
    mids = (bin_edges[:-1] + bin_edges[1:]) / 2.0
    semicircle = (2.0 / math.pi) * np.sqrt(np.maximum(0.0, 1.0 - mids ** 2))

    moments = [float((ws * xs ** (2 * k)).sum() / n_curves) for k in (1, 2, 3)]
    s2 = int(sum(int(t) ** 2 * int(c) for t, c in zip(ts, ws)))

    return {
        "p": p,
        "n_curves": n_curves,
        "n_bins": n_bins,
        "bin_edges": bin_edges,
        "counts": counts,
        "density": density,
        "bin_midpoints": mids,
        "semicircle": semicircle,
        "sup_deviation": float(np.abs(density - semicircle).max()),
        "l1_deviation": float(np.abs(density - semicircle).sum() * width),
        "moments": moments,
        "semicircle_moments": [0.25, 0.125, 5.0 / 64.0],
        "second_moment_exact": s2,
        "second_moment_closed_form": (p - 1) ** 2 * (p + 1),
        "sum_a_p": int(sum(int(t) * int(c) for t, c in zip(ts, ws))),
        "max_abs_a_p": int(np.abs(ts).max()),
        "hasse_violations": int((ts.astype(np.int64) ** 2 > 4 * p).sum()),
        "distinct_traces": int(ts.size),
        "hasse_interval_size": 2 * math.isqrt(4 * p) + 1,
    }


# ---------------------------------------------------------------------------
# 8. an independent oracle: Gauss's theorem for y^2 = x^3 - x
# ---------------------------------------------------------------------------

def gauss_trace(p: int) -> int:
    """``a_p`` for ``y^2 = x^3 - x`` from Gauss, with no point counting at all.

    The curve ``y^2 = x^3 - x`` has complex multiplication by ``Z[i]``, and its
    trace is given by a classical theorem (Gauss; see e.g. Ireland-Rosen,
    *A Classical Introduction to Modern Number Theory*, ch. 18):

    * if ``p = 3 mod 4`` the curve is supersingular and ``a_p = 0``;
    * if ``p = 1 mod 4`` write ``p = A^2 + B^2`` with ``A`` odd and ``B`` even
      (unique up to signs), fix the sign of A by ``A + B = 1 mod 4``, well
      posed, since B even means ``B mod 4`` does not depend on B's sign, and
      then ``a_p = 2A``.

    This is a completely independent route to ``a_p``: no curve, no Legendre
    symbols, just a sum of two squares.  The tests assert it equals
    ``trace_of_frobenius(-1, 0, p)`` for every prime ``p < 2000`` (300 primes)
    and at ``p = 10009``.  Both give ``a_p = -30`` at ``p = 1009``, the value
    quoted in ``docs/09`` section 1.1.
    """
    p = _check_p(p)
    if p % 4 == 3:
        return 0
    for A in range(1, math.isqrt(p) + 1, 2):
        r = p - A * A
        B = math.isqrt(r)
        if B * B == r:
            if (A + B) % 4 != 1:
                A = -A
            return 2 * A
    raise RuntimeError(f"no representation p = A^2 + B^2 for p = {p}")  # pragma: no cover


# ---------------------------------------------------------------------------
# 9. prose: what was proved, by whom, and what it does not give us
# ---------------------------------------------------------------------------

def weil_conjecture_facts() -> dict[str, Any]:
    """The theorems this module exercises, and the gap to RH over ``Z``.

    Every entry is a *published theorem* or an explicitly labelled gap; nothing
    here is computed.  Companion to :func:`zeta.heatflow.lambda_facts`.
    """
    return {
        "statement": (
            "For a smooth projective curve C of genus g over F_q, Z(T) is a "
            "rational function P(T)/((1-T)(1-qT)) with P of degree 2g and "
            "integer coefficients, P(T) = prod (1 - alpha_i T) with "
            "|alpha_i| = sqrt(q) for every i -- 'all zeros on Re(s) = 1/2' "
            "after T = q^{-s}."
        ),
        "elliptic_case": "g = 1: |a_q| <= 2 sqrt(q), the Hasse bound.",
        "status": "THEOREM (not conjecture, not numerical evidence).",
        "history": [
            {
                "result": "|a_p| <= 2 sqrt(p) for elliptic curves over F_p",
                "who": "H. Hasse",
                "where": "Abstrakte Begruendung der komplexen Multiplikation "
                "und Riemannsche Vermutung in Funktionenkoerpern, "
                "Abh. Math. Sem. Univ. Hamburg 10 (1934), 325-348",
            },
            {
                "result": "RH for all curves over finite fields",
                "who": "A. Weil",
                "where": "Sur les courbes algebriques et les varietes qui s'en "
                "deduisent, Hermann, Paris, 1948",
            },
            {
                "result": "the Weil conjectures for varieties of any dimension "
                "(rationality, functional equation, RH)",
                "who": "A. Weil (conjectures, 1949)",
                "where": "Numbers of solutions of equations in finite fields, "
                "Bull. Amer. Math. Soc. 55 (1949), 497-508",
            },
            {
                "result": "rationality of Z(T) in general (p-adic method)",
                "who": "B. Dwork",
                "where": "Amer. J. Math. 82 (1960), 631-648",
            },
            {
                "result": "etale cohomology; Lefschetz trace formula for Frobenius",
                "who": "A. Grothendieck, M. Artin, J.-L. Verdier and others",
                "where": "SGA 4, SGA 4 1/2, SGA 5 (c. 1963-1977)",
            },
            {
                "result": "RH part of the Weil conjectures, all dimensions",
                "who": "P. Deligne",
                "where": "La conjecture de Weil I, Publ. Math. IHES 43 (1974), "
                "273-307",
            },
            {
                "result": "vertical Sato-Tate: a_p/(2 sqrt p) over all curves "
                "mod p tends to the semicircle law",
                "who": "B. J. Birch",
                "where": "J. London Math. Soc. 43 (1968), 57-60",
            },
            {
                "result": "every t with |t| <= 2 sqrt p occurs as a trace",
                "who": "M. Deuring",
                "where": "Abh. Math. Sem. Univ. Hamburg 14 (1941), 197-272",
            },
        ],
        "ingredients": {
            "space": "the curve C over F_q, with a ground field beneath it, so "
            "that C x_{F_q} C is a genuine surface",
            "operator": "Frobenius x -> x^q acting on H^i_et; its fixed points "
            "are the F_q-points, so N_n = sum_i (-1)^i Tr(Frob^n | H^i)",
            "positivity": "Castelnuovo-Severi (a Hodge-index inequality) applied "
            "to the graph of Frobenius on C x C -- symmetry alone never "
            "suffices (Deligne 1974 replaced this with a different "
            "analytic amplification, but still symmetry + positivity)",
        },
        "what_is_missing_over_Z": (
            "Spec Z has no base: Z (x)_Z Z = Z, so the square of Spec Z is "
            "one-dimensional and Weil's positivity argument has no staging "
            "area.  No category is known in which zeta(s) is the zeta function "
            "of a curve over a base field.  See docs/09-new-ontologies.md "
            "section 1 and section 4, and docs/11-f1-and-the-missing-geometry.md."
        ),
        "honest_scope": (
            "Nothing in zeta.finitefield is evidence for RH over the integers.  "
            "It is a proved theorem being exercised, shipped as the reference "
            "against which the F1 / Connes / Deninger programs of docs/11 are "
            "to be measured."
        ),
    }
