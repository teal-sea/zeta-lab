"""Four *equivalence faces* of the Riemann Hypothesis, made executable.

``docs/07-equivalences-and-criteria.md`` catalogues the statements known to be
exactly equivalent to RH.  A catalogue is not an instrument, so this module
turns four of them into code that runs.  The Kadison--Singer lesson is the
motivation: a problem can die through a reformulation nobody expected, so every
face should be in reach of a keyboard.

The four faces, with the label the repository insists on:

1.  **Mertens / Mobius** (:func:`mobius`, :func:`mertens_M`,
    :func:`mertens_ratio`, :func:`mertens_ratio_extremes`).

    THEOREM.  For 1/2 <= theta < 1, ``M(x) = O(x^{theta+eps})`` for every
    eps > 0 **iff** zeta has no zero with Re(s) > theta.  In particular

        RH  <=>  M(x) = O(x^{1/2 + eps})   for every eps > 0,

    where ``M(x) = sum_{n <= x} mu(n)``.  The bridge is one partial summation,
    ``1/zeta(s) = s * int_1^inf M(x) x^{-s-1} dx`` for Re(s) > 1.

    THEOREM (Odlyzko and te Riele, *Disproof of the Mertens conjecture*,
    J. reine angew. Math. 357 (1985) 138--160).  The **strong Mertens
    conjecture** ``|M(x)| < sqrt(x)`` for all x > 1 is **FALSE**.  Their proof
    is non-constructive -- lattice reduction on the almost-periodic wave sum
    for ``M(x)/sqrt(x)`` -- and no explicit counterexample is known; the
    published bounds on the first one are astronomical.  Consequently
    :func:`mertens_ratio_extremes` is a *demonstration that numerics cannot
    see this*: over the range we can sieve, ``|M(x)|/sqrt(x)`` stays far below
    1, which is exactly what it did for the century in which the conjecture was
    believed.  Nothing in our range is evidence either way.

2.  **Nyman--Beurling / Baez-Duarte** (:func:`baez_duarte_basis`,
    :func:`baez_duarte_gram`, :func:`baez_duarte_d2`).  The linear-algebra
    face; see the long note on :func:`baez_duarte_d2`.

3.  **Robin / Lagarias** (:func:`divisor_sigma`, :func:`robin_ratio`,
    :func:`lagarias_ratio`, :func:`colossally_abundant`, :func:`robin_search`).

    THEOREM (Robin, J. Math. Pures Appl. 63 (1984) 187--213).

        RH  <=>  sigma(n) < e^gamma * n * log log n   for every n > 5040.

    THEOREM (Lagarias, Amer. Math. Monthly 109 (2002) 534--543).

        RH  <=>  sigma(n) <= H_n + exp(H_n) * log(H_n)   for every n >= 1,

    with equality only at n = 1 (``H_n`` the n-th harmonic number).

4.  **Speiser** (:func:`zeta_prime`, :func:`zeta_prime_zeros`,
    :func:`speiser_scan`).

    THEOREM (Speiser, Math. Ann. 110 (1934/35) 514--521 -- the year is cited
    both ways in the literature).

        RH  <=>  zeta'(s) has no zeros in the strip 0 < Re(s) < 1/2.

    Levinson and Montgomery (1974) proved the quantitative companion, which is
    the engine of Levinson's method.  This is the one criterion on the list
    that ever paid.

Honest scope
------------
Nothing computed here is evidence for RH (``docs/08``, Littlewood).  Every
routine reports what it *found in a finite range*; the tests are phrased as
"no violation found in range", never as support.  The Mertens face is in the
module precisely because it is the standing counterexample to reading numerics
as evidence.

Conventions
-----------
Arbitrary-precision work goes through ``mpmath.mp.workdps`` and leaves no
global state modified, as elsewhere in the package.  Bulk integer sieving is
numpy.  Expensive results cache under ``data/`` with the parameters in the
filename.
"""

from __future__ import annotations

import json
import math
import re as _re
from collections import defaultdict
from functools import lru_cache
from math import gcd
from pathlib import Path
from typing import Any, Iterator, Sequence

import mpmath
import numpy as np
from mpmath import mp

from .core import DPS_DEFAULT

__all__ = [
    "DPS_DEFAULT",
    "DATA_DIR",
    # --- 1. Mertens / Mobius --------------------------------------------
    "mobius",
    "mobius_sieve",
    "mertens_array",
    "mertens_M",
    "mertens_ratio",
    "mertens_ratio_extremes",
    "MERTENS_PINNED",
    "mertens_facts",
    # --- 2. Nyman-Beurling / Baez-Duarte --------------------------------
    "baez_duarte_basis",
    "baez_duarte_gram",
    "baez_duarte_rhs",
    "baez_duarte_d2",
    "baez_duarte_table",
    "BD_CONSTANT",
    # --- 3. Robin / Lagarias --------------------------------------------
    "divisor_sigma",
    "sigma_sieve",
    "harmonic_number",
    "robin_ratio",
    "robin_ratio_from_log",
    "lagarias_ratio",
    "lagarias_ratio_from_log",
    "robin_violations",
    "lagarias_violations",
    "colossally_abundant",
    "superabundant_candidates",
    "robin_search",
    "ROBIN_THRESHOLD",
    "ROBIN_EXCEPTIONS",
    # --- 4. Speiser ------------------------------------------------------
    "zeta_prime",
    "zeta_prime_zeros",
    "speiser_scan",
    "ZETA_PRIME_ZEROS_PINNED",
    # --- summary ----------------------------------------------------------
    "criteria_report",
]

#: Cache directory for expensive scans (derived from this file, never absolute
#: in a committed artefact).
DATA_DIR: Path = Path(__file__).resolve().parent.parent / "data"

#: Extra guard digits carried internally and discarded before returning.
_GUARD: int = 10


def _data_dir() -> Path:
    DATA_DIR.mkdir(parents=True, exist_ok=True)
    return DATA_DIR


def _shrink(value, dps: int):
    """Round a value computed at high precision down to ``dps`` digits."""
    with mp.workdps(dps):
        return +value


# ===========================================================================
# 1.  MERTENS / MOBIUS
# ===========================================================================

def mobius(n: int) -> int:
    """The Mobius function mu(n), by trial-division factorisation.

    mu(n) = 1 if n is a squarefree product of an even number of primes,
    -1 if squarefree with an odd number, 0 if n is divisible by a square.
    mu(1) = 1.  Cross-checked against :func:`sympy.mobius` in the tests for
    every n up to 2000 and for random n up to 10^7.

    Raises ``ValueError`` for n < 1 (mu is not defined there).
    """
    n = int(n)
    if n < 1:
        raise ValueError(f"mobius expects n >= 1, got {n}")
    if n == 1:
        return 1
    result = 1
    d = 2
    while d * d <= n:
        if n % d == 0:
            n //= d
            if n % d == 0:          # d^2 | original n
                return 0
            result = -result
        d += 1 if d == 2 else 2
    if n > 1:                        # a leftover prime factor
        result = -result
    return result


def _mobius_cache_path(limit: int) -> Path:
    return _data_dir() / f"mobius_sieve_{limit}.npz"


def mobius_sieve(limit: int, use_cache: bool = True) -> np.ndarray:
    """``mu(0..limit)`` as an ``int8`` array, by a vectorised sieve.

    The sieve removes every prime p <= sqrt(limit) from a running cofactor
    array; whatever survives is either 1 or a single prime > sqrt(limit) (two
    such primes would exceed ``limit``), which contributes one further sign
    flip.  So the outer loop runs over pi(sqrt(limit)) primes -- 446 of them at
    limit = 10^7, pinned in the tests -- rather than over all pi(limit) =
    664 579 primes below the bound; each iteration costs a handful of strided
    numpy passes (the sign flip, the prime-power divisions, the square kill).

    Cost measured in this environment: 0.76 s at limit = 10^7.  The output is
    10 MB of int8, but the transient ``rem`` cofactor array is int64, so the
    peak footprint is about 90 MB -- that, not time, is what bounds ``limit``
    here.  Results for ``limit >= 10^6`` are cached to
    ``data/mobius_sieve_{limit}.npz`` (compressed; ``data/*.npz`` is gitignored
    and regenerates on first use).
    """
    limit = int(limit)
    if limit < 1:
        raise ValueError(f"mobius_sieve expects limit >= 1, got {limit}")
    path = _mobius_cache_path(limit)
    if use_cache and limit >= 10**6 and path.exists():
        with np.load(path) as fh:
            return fh["mu"]

    mu = np.ones(limit + 1, dtype=np.int8)
    mu[0] = 0
    rem = np.arange(limit + 1, dtype=np.int64)
    root = int(math.isqrt(limit))
    small = np.ones(root + 1, dtype=bool)
    if root >= 1:
        small[:min(2, root + 1)] = False
    for i in range(2, int(math.isqrt(root)) + 1):
        if small[i]:
            small[i * i:: i] = False
    for p in np.flatnonzero(small):
        p = int(p)
        mu[p:: p] = -mu[p:: p]
        pk = p
        while pk <= limit:
            rem[pk:: pk] //= p
            pk *= p
        if p * p <= limit:
            mu[p * p:: p * p] = 0
    leftover = rem > 1                       # a prime > sqrt(limit) survives
    mu[leftover] = -mu[leftover]
    mu[0] = 0
    if limit >= 1:
        mu[1] = 1
    if use_cache and limit >= 10**6:
        np.savez_compressed(path, mu=mu)
    return mu


def mertens_array(limit: int, use_cache: bool = True) -> np.ndarray:
    """``M(0..limit)`` as an ``int32`` array, ``M(x) = sum_{n <= x} mu(n)``.

    A cumulative sum of :func:`mobius_sieve`.  ``int32`` is ample: measured
    here, the largest ``|M(x)|`` for ``x <= 10^7`` is **1143**, attained at
    x = 9 993 034 (pinned in the tests), and ``|M(x)| <= x`` always.
    """
    mu = mobius_sieve(limit, use_cache=use_cache)
    # dtype= is not optional: numpy promotes an int32 accumulation to the
    # platform integer unless told otherwise, which silently doubled the
    # footprint (80 MB at limit = 10^7) and contradicted the line above.
    return np.cumsum(mu, dtype=np.int32)


def mertens_M(x, use_cache: bool = True) -> int:
    """The Mertens function ``M(x) = sum_{n <= x} mu(n)`` at a single point.

    ``x`` may be any real >= 0; only ``floor(x)`` matters.  ``M(x) = 0`` for
    x < 1.  For x below 4096 this sums :func:`mobius` directly (no sieve
    allocation); above that it goes through :func:`mertens_array`.

    Pinned values, all reproduced by the tests and matching the standard
    tables: ``M(10^3) = 2``, ``M(10^4) = -23``, ``M(10^5) = -48``,
    ``M(10^6) = 212``, ``M(10^7) = 1037``.
    """
    n = int(math.floor(float(x)))
    if n < 1:
        return 0
    if n < 4096:
        return int(sum(mobius(k) for k in range(1, n + 1)))
    return int(mertens_array(n, use_cache=use_cache)[n])


def mertens_ratio(x, use_cache: bool = True) -> float:
    """``M(x)/sqrt(x)`` -- the quantity the Mertens conjecture bounded by 1.

    RH is equivalent to this being ``O(x^eps)`` for every eps > 0 (THEOREM);
    the *bounded* version, ``|M(x)| < sqrt(x)``, is FALSE (Odlyzko--te Riele
    1985), so a small value here means nothing at all.
    """
    n = int(math.floor(float(x)))
    if n < 1:
        return 0.0
    return mertens_M(n, use_cache=use_cache) / math.sqrt(n)


#: Values of M(x) at powers of ten, checked by the tests against a direct sum
#: (up to 10^5) and against the sieve (10^6, 10^7).
MERTENS_PINNED: dict[int, int] = {
    10**1: -1,
    10**2: 1,
    10**3: 2,
    10**4: -23,
    10**5: -48,
    10**6: 212,
    10**7: 1037,
}


def mertens_ratio_extremes(
    limit: int = 10**6,
    x_min: int = 1,
    use_cache: bool = True,
) -> dict[str, Any]:
    """Extremes of ``M(x)/sqrt(x)`` over ``x_min <= x <= limit``.

    Returns a dict with ``max_ratio``/``argmax``, ``min_ratio``/``argmin``,
    ``max_abs_ratio``/``argmax_abs``, plus ``M_at_limit`` and the range.

    **Read this before reading the numbers.**  The strong Mertens conjecture
    ``|M(x)| < sqrt(x)`` is FALSE (Odlyzko--te Riele 1985): the limsup of
    ``M(x)/sqrt(x)`` exceeds 1.06 and the liminf is below -1.009 (the usually
    quoted constants; Kotnik--te Riele later pushed both past 1.2 in absolute
    value -- hedged).  The disproof is non-constructive and the first
    counterexample is not known and is believed astronomically large.  So a
    scan finding ``max |M(x)|/sqrt(x)`` well under 1 -- which is what this
    function does -- reproduces exactly the numerical evidence that misled
    Mertens in 1897.  It shows nothing either way, about the conjecture or
    about RH.

    Measured in this environment at ``limit = 10^7``:
    ``max = 1.0`` at x = 1 (degenerate: M(1) = 1),
    ``min = -0.894427 = -2/sqrt(5)`` at x = 5, and with ``x_min = 100`` the
    largest absolute ratio is ``0.567105`` at x = 199.
    """
    limit = int(limit)
    x_min = max(1, int(x_min))
    if x_min > limit:
        raise ValueError(f"x_min={x_min} exceeds limit={limit}")
    M = mertens_array(limit, use_cache=use_cache)
    idx = np.arange(x_min, limit + 1, dtype=np.float64)
    ratio = M[x_min:limit + 1] / np.sqrt(idx)
    i_max = int(np.argmax(ratio))
    i_min = int(np.argmin(ratio))
    i_abs = int(np.argmax(np.abs(ratio)))
    return {
        "limit": limit,
        "x_min": x_min,
        "max_ratio": float(ratio[i_max]),
        "argmax": x_min + i_max,
        "min_ratio": float(ratio[i_min]),
        "argmin": x_min + i_min,
        "max_abs_ratio": float(abs(ratio[i_abs])),
        "argmax_abs": x_min + i_abs,
        "M_at_limit": int(M[limit]),
        "strong_mertens_conjecture": "FALSE (Odlyzko-te Riele 1985)",
        "note": (
            "|M(x)|/sqrt(x) staying below 1 in a finite range is not evidence: "
            "the bound is a disproved conjecture and the disproof is "
            "non-constructive"
        ),
    }


def mertens_facts() -> dict[str, str]:
    """The Mertens face in words, with each claim labelled."""
    return {
        "criterion": "RH <=> M(x) = O(x^{1/2+eps}) for every eps > 0",
        "criterion_status": "THEOREM",
        "general_form": (
            "for 1/2 <= theta < 1: M(x) = O(x^{theta+eps}) for all eps > 0 "
            "iff zeta has no zero with Re(s) > theta"
        ),
        "bridge": "1/zeta(s) = s * int_1^inf M(x) x^{-s-1} dx  (Re s > 1)",
        "strong_mertens_conjecture": "|M(x)| < sqrt(x) for all x > 1",
        "strong_mertens_status": (
            "FALSE -- Odlyzko and te Riele, 'Disproof of the Mertens "
            "conjecture', J. reine angew. Math. 357 (1985) 138-160; "
            "limsup M(x)/sqrt(x) > 1.06 and liminf < -1.009 "
            "(usually quoted constants; later improvements hedged). "
            "Non-constructive: no explicit counterexample is known and the "
            "bounds on the first one are astronomical."
        ),
        "still_open": (
            "whether M(x) = O(sqrt(x)) holds without the eps; widely believed "
            "FALSE (Ng and others, under a linear-independence hypothesis on "
            "the ordinates) -- CONJECTURE, hedged"
        ),
        "honest_scope": (
            "no finite sieve can distinguish O(x^{1/2+eps}) from O(x^{0.6}); "
            "the range reachable here shows nothing either way"
        ),
    }


# ===========================================================================
# 2.  NYMAN-BEURLING and the BAEZ-DUARTE STRENGTHENING
# ===========================================================================
#
# Convention, derived here rather than remembered (house rule).  For
# 0 < theta <= 1 put
#
#       rho_theta(x) = {theta/x} - theta * {1/x}          on (0, 1),
#
# with {y} the fractional part.  The Mellin transform on 0 < Re(s) < 1 is
#
#       int_0^1 rho_theta(x) x^{s-1} dx = (zeta(s)/s) * (theta - theta^s),
#
# which is *why* the second term is there: it cancels the pole part of
# int_0^1 {theta/x} x^{s-1} dx = theta/(s-1) - theta^s zeta(s)/s.  Two
# consequences pin the convention numerically and are asserted in the tests:
#
#       int_0^1 {1/x} dx = 1 - gamma,      int_0^1 rho_theta dx = -theta log theta.
#
# Both are asserted in the tests, at the accuracy each route actually reaches:
# the second to 28 digits (it has a closed form, (log k)/k), the first only to
# 1e-5, because the series that evaluates it is truncated at 200000 terms and
# its tail is ~1/(2N) = 2.5e-6.  The test asserts *both* an upper and a lower
# bound on that error, so the truncation stays visible and the tolerance
# cannot be passed by accident.

#: The constant in the Baez-Duarte--Balazard--Landreau--Saias asymptotic
#: ``d_N^2 ~ C / log N``:  C = sum_rho 1/|rho|^2 = 2 + gamma - log(4 pi)
#: under RH (the same number as 2*lambda_1 in Li's criterion, docs/07 section 4).
#: CONJECTURE for the asymptotic; the value of C is a closed form.
BD_CONSTANT: str = "0.046191417932242067628620495813"


def baez_duarte_basis(k: int, x, dps: int = DPS_DEFAULT):
    """``A_k(x) = {1/(k x)} - (1/k) {1/x}`` on (0, 1) -- i.e. ``rho_{1/k}``.

    Note ``A_1 == 0`` identically; the Baez-Duarte family is really indexed by
    k >= 2, and including k = 1 changes no span and no residual.

    The step form used by :func:`baez_duarte_gram` is

        A_k(x) = {n/k}   for   1/(n+1) < x < 1/n,   n = 1, 2, 3, ...

    which follows from ``rho_theta(x) = theta*floor(1/x) - floor(theta/x)``.
    The tests check the two forms agree to working precision.
    """
    k = int(k)
    if k < 1:
        raise ValueError(f"baez_duarte_basis expects k >= 1, got {k}")
    with mp.workdps(dps + _GUARD):
        xx = mpmath.mpmathify(x)
        if mp.im(xx) != 0:
            raise ValueError("baez_duarte_basis expects a real argument")
        xx = mp.mpf(mp.re(xx))
        if not (0 < xx < 1):
            raise ValueError(f"baez_duarte_basis expects 0 < x < 1, got {xx}")
        val = mp.frac(1 / (k * xx)) - mp.frac(1 / xx) / k
    return _shrink(val, dps)


def _bd_gram_block(L: int, pairs: Sequence[tuple[int, int, int, int]]):
    """Gram entries for every (j, k) pair sharing ``lcm(j, k) = L``.

    The exact identity behind this (derived, then confirmed against an
    independent Mellin--Parseval integral over the critical line and against a
    Monte-Carlo of the raw definition):

        <A_j, A_k> = sum_{n >= 1} {n/j} {n/k} / (n (n+1)),

    because ``A_k`` is the step function ``{n/k}`` on ``(1/(n+1), 1/n)`` and
    ``int_{1/(n+1)}^{1/n} dx = 1/(n(n+1))``.  The summand is periodic in n with
    period ``L = lcm(j, k)``, so the series is summed in closed form,

        <A_j, A_k> = (1/L) sum_{r=1}^{L-1} {r/j}{r/k} [psi(( r+1)/L) - psi(r/L)],

    from ``sum_{m >= 0} 1/((mL+r)(mL+r+1)) = (1/L)[psi((r+1)/L) - psi(r/L)]``.
    Exact to full working precision -- no quadrature, no truncation.
    """
    # psis[i] = psi((i+1)/L) for i = 0 .. L-1, so psi(r/L) = psis[r-1].
    psis = [mp.psi(0, mp.mpf(r) / L) for r in range(1, L + 1)]
    delta = [(psis[r] - psis[r - 1]) / L for r in range(1, L)]  # delta[r-1] <-> r
    out = []
    for (a, b, j, k) in pairs:
        terms = []
        for r in range(1, L):
            rj = r % j
            if not rj:
                continue
            rk = r % k
            if not rk:
                continue
            terms.append((rj * rk, delta[r - 1]))
        out.append((a, b, mp.fdot(terms) / (j * k)))
    return out


def _bd_cache_path(N: int, dps: int) -> Path:
    return _data_dir() / f"baez_duarte_gram_N{N}_dps{dps}.json"


_BD_CACHE_RE = _re.compile(r"^baez_duarte_gram_N(\d+)_dps(\d+)\.json$")


def _bd_load_cache(N: int, dps: int):
    """The smallest cached Gram matrix that covers ``(N, dps)``, or None.

    A cached matrix for N' >= N at dps' >= dps contains ours as a leading
    principal submatrix, so it can be reused (this is the same
    "reuse-a-bigger-table" pattern as ``zeta.zeros._load_cache``).
    """
    if not DATA_DIR.is_dir():
        return None
    best = None
    for path in DATA_DIR.iterdir():
        m = _BD_CACHE_RE.match(path.name)
        if not m:
            continue
        n_c, dps_c = int(m.group(1)), int(m.group(2))
        if n_c >= N and dps_c >= dps and (best is None or n_c < best[0]):
            best = (n_c, dps_c, path)
    if best is None:
        return None
    try:
        payload = json.loads(best[2].read_text())
    except (OSError, json.JSONDecodeError):
        return None
    entries = payload.get("upper")
    if not entries:
        return None
    with mp.workdps(dps + _GUARD):
        table = {}
        for j, k, s in entries:
            if j <= N and k <= N:
                table[(int(j), int(k))] = mp.mpf(s)
    return table


def _bd_save_cache(N: int, dps: int, table: dict) -> Path:
    payload = {
        "N": N,
        "dps": dps,
        "description": (
            "Gram matrix <A_j, A_k> of the Baez-Duarte basis "
            "A_k(x) = {1/(kx)} - (1/k){1/x} in L^2(0,1), j,k = 2..N; "
            "exact digamma closed form, zeta.criteria._bd_gram_block"
        ),
        "upper": [[j, k, mp.nstr(v, dps + 10)] for (j, k), v in sorted(table.items())],
    }
    path = _bd_cache_path(N, dps)
    path.write_text(json.dumps(payload, indent=1))
    return path


def baez_duarte_gram(N: int, dps: int = 50, use_cache: bool = True):
    """The Gram matrix ``G[a][b] = <A_{j}, A_{k}>`` for j, k in ``2..N``.

    Returns ``(G, index)`` with ``G`` an ``mp.matrix`` of size ``N-1`` and
    ``index = [2, 3, ..., N]`` the basis labels.  ``A_1`` is identically zero
    and is dropped: keeping it would only make ``G`` singular for no gain.

    Entries come from the exact closed form in :func:`_bd_gram_block`, so the
    only error is rounding at ``dps`` digits.  Results cache to
    ``data/baez_duarte_gram_N{N}_dps{dps}.json``.
    """
    N = int(N)
    if N < 2:
        raise ValueError(f"baez_duarte_gram expects N >= 2, got {N}")
    index = list(range(2, N + 1))
    table = _bd_load_cache(N, dps) if use_cache else None
    if table is None or any(
        (j, k) not in table for a, j in enumerate(index) for k in index[a:]
    ):
        with mp.workdps(dps + _GUARD):
            groups: dict[int, list[tuple[int, int, int, int]]] = defaultdict(list)
            for a, j in enumerate(index):
                for b in range(a, len(index)):
                    k = index[b]
                    groups[j * k // gcd(j, k)].append((a, b, j, k))
            table = {}
            for L in sorted(groups):
                for (a, b, value) in _bd_gram_block(L, groups[L]):
                    table[(index[a], index[b])] = value
        if use_cache:
            _bd_save_cache(N, dps, table)
    with mp.workdps(dps + _GUARD):
        G = mp.zeros(len(index), len(index))
        for a, j in enumerate(index):
            for b in range(a, len(index)):
                k = index[b]
                G[a, b] = G[b, a] = +table[(j, k)]
    return G, index


def baez_duarte_rhs(N: int, dps: int = 50):
    """``b_k = <1, A_k> = (log k)/k`` for k = 2..N, as an ``mp.matrix``.

    Closed form: ``int_0^1 rho_theta = -theta log theta`` (derived from the
    Mellin transform at s = 1, where the pole of zeta meets the zero of
    ``theta - theta^s``).  The step-function series
    ``sum_n {n/k}/(n(n+1))`` reproduces it to 30 digits -- asserted in the
    tests, and the cheapest available check that the whole Gram machinery
    is normalised correctly.
    """
    N = int(N)
    if N < 2:
        raise ValueError(f"baez_duarte_rhs expects N >= 2, got {N}")
    with mp.workdps(dps + _GUARD):
        return mp.matrix([mp.log(k) / k for k in range(2, N + 1)])


def baez_duarte_d2(
    N: int,
    dps: int = 50,
    use_cache: bool = True,
    with_condition: bool = True,
) -> dict[str, Any]:
    """The Baez-Duarte residual ``d_N^2`` -- the linear-algebra face of RH.

    Definition.  With ``A_k(x) = {1/(kx)} - (1/k){1/x}`` on (0, 1),

        d_N^2 = inf over c_1..c_N of || 1 - sum_{k=1}^N c_k A_k ||^2_{L^2(0,1)}.

    THEOREM (Nyman 1950, Beurling 1955).  RH holds iff the constant function 1
    lies in the closed span of ``{rho_theta : 0 < theta <= 1}`` in ``L^2(0,1)``.

    THEOREM (Baez-Duarte, Rend. Mat. Acc. Lincei 14 (2003) 5--11).  It is
    enough to take ``theta = 1/k`` over the positive integers:

        RH  <=>  d_N -> 0   as   N -> infinity.

    ``d_N`` is non-increasing in N (extra basis vectors can only help) -- this
    is checked, not assumed, in the tests.

    CONJECTURE (Baez-Duarte, Balazard, Landreau, Saias, c. 2000):
    ``d_N^2 ~ C/log N`` with ``C = sum_rho 1/|rho|^2 = 2 + gamma - log(4 pi)``
    ``= 0.0461914179...`` under RH.  I am hedging on the matching lower bound
    they are usually credited with.

    Returns a dict: ``N``, ``d2`` (mpf), ``coefficients`` (the minimising
    ``c_k`` for k = 2..N), ``condition_number`` of the Gram matrix,
    ``residual_check`` (the quadratic form ``1 - 2 b.c + c^T G c`` recomputed
    independently of the ``1 - b.c`` shortcut -- they must agree), ``dps``.

    **Conditioning, measured rather than repeated.**  ``docs/07`` calls this
    problem "severely ill-conditioned", which is the folklore.  In *this*
    basis, with the Gram entries in exact closed form, it is not: the measured
    ``cond(G)`` is 98.7 at N = 10, 534.6 at N = 20, 1365.2 at N = 30, 4774.5 at
    N = 50 -- growth like a small power of N, and comfortably inside float64
    (an independent float64 Cholesky solve after Jacobi scaling, and numpy's
    ``lstsq``, both reproduce ``d_N^2`` to 14 digits at every N up to 50; that
    cross-check is a test).  ``d_N^2`` at
    N = 12 computed at dps 25 differs from the dps 90 value by 1.3e-28, i.e.
    the dps 25 answer is already good to 26 significant digits; dps 40 and 60
    agree with dps 90 to 43 and 64 digits.  The obstruction is therefore *not*
    conditioning at reachable N; it is the ``1/log N`` decay itself, which
    needs N ~ 10^20 to push ``d_N^2`` to 10^-3.  Reporting the conditioning as
    mild is the honest outcome of measuring it.
    """
    N = int(N)
    G, index = baez_duarte_gram(N, dps=dps, use_cache=use_cache)
    b = baez_duarte_rhs(N, dps=dps)
    with mp.workdps(dps + _GUARD):
        c = mp.lu_solve(G, b)
        d2 = 1 - mp.fdot(zip(b, c))
        quad = mp.fdot(zip(c, G * c))
        residual = 1 - 2 * mp.fdot(zip(b, c)) + quad
        cond = None
        if with_condition:
            eig = mp.eigsy(G, eigvals_only=True)
            lo, hi = min(eig), max(eig)
            cond = hi / lo if lo > 0 else mp.inf
        out = {
            "N": N,
            "index": index,
            "d2": _shrink(d2, dps),
            "coefficients": [_shrink(v, dps) for v in c],
            "condition_number": None if cond is None else _shrink(cond, 12),
            "residual_check": _shrink(residual, dps),
            "dps": dps,
        }
    return out


def baez_duarte_table(
    N_values: Sequence[int],
    dps: int = 50,
    use_cache: bool = True,
) -> list[dict[str, Any]]:
    """``d_N^2`` for several N, with the ratio to the conjectured ``C/log N``.

    Measured here at dps = 50 (``d2 * log N / C``, C = 0.0461914...), all four
    pinned in the tests:
    N = 10 -> 1.1890203, N = 20 -> 1.0725840, N = 30 -> 1.0718511,
    N = 50 -> 1.0067260.
    Consistent with the BBLS asymptotic; *not* a test of it -- 1/log N cannot
    be distinguished from a small positive limit by any finite computation,
    and the ratio is not even monotone (N = 20 and N = 30 differ in the third
    decimal only, in the wrong direction for a clean trend).
    """
    rows = []
    with mp.workdps(dps + _GUARD):
        C = mp.mpf(BD_CONSTANT)
    for N in sorted(int(n) for n in N_values):
        rec = baez_duarte_d2(N, dps=dps, use_cache=use_cache, with_condition=True)
        with mp.workdps(dps + _GUARD):
            rec["d2_times_logN_over_C"] = _shrink(rec["d2"] * mp.log(N) / C, 10)
        rows.append(rec)
    return rows


# ===========================================================================
# 3.  ROBIN / LAGARIAS
# ===========================================================================

#: Robin's threshold: the criterion quantifies over n > 5040.
ROBIN_THRESHOLD: int = 5040

#: The complete list of n >= 3 with sigma(n) >= e^gamma n log log n.  Under RH
#: this list is final (Robin 1984); unconditionally it is "every exception
#: below the search bound".  Reproduced by :func:`robin_violations` up to
#: 10^5 in the tests, and matching docs/07 section 6.
ROBIN_EXCEPTIONS: tuple[int, ...] = (
    3, 4, 5, 6, 8, 9, 10, 12, 16, 18, 20, 24, 30, 36, 48, 60, 72, 84,
    120, 180, 240, 360, 720, 840, 2520, 5040,
)


def divisor_sigma(n: int) -> int:
    """``sigma(n)``, the sum of the divisors of n, exactly (a Python int).

    Trial-division factorisation and the multiplicative formula
    ``sigma(p^a) = (p^{a+1} - 1)/(p - 1)``.  Cross-checked against
    :func:`sympy.divisor_sigma` in the tests.
    """
    n = int(n)
    if n < 1:
        raise ValueError(f"divisor_sigma expects n >= 1, got {n}")
    total = 1
    d = 2
    while d * d <= n:
        if n % d == 0:
            power = 1
            term = 1
            while n % d == 0:
                n //= d
                power *= d
                term += power
            total *= term
        d += 1 if d == 2 else 2
    if n > 1:
        total *= 1 + n
    return total


def sigma_sieve(limit: int) -> np.ndarray:
    """``sigma(0..limit)`` as an ``int64`` array (divisor-sum sieve)."""
    limit = int(limit)
    if limit < 1:
        raise ValueError(f"sigma_sieve expects limit >= 1, got {limit}")
    sig = np.zeros(limit + 1, dtype=np.int64)
    for d in range(1, limit + 1):
        sig[d:: d] += d
    return sig


def harmonic_number(n: int, dps: int = DPS_DEFAULT):
    """``H_n = 1 + 1/2 + ... + 1/n``, via ``psi(n+1) + gamma``.

    Exact-rational for tiny n would be pointless here; the digamma route is
    correct for n far beyond any n we can factor, and the tests pin it against
    a direct sum at n = 2, 10, 100 and 2000, and against ``H_1 = 1`` exactly.
    """
    n = int(n)
    if n < 1:
        raise ValueError(f"harmonic_number expects n >= 1, got {n}")
    with mp.workdps(dps + _GUARD):
        val = mp.psi(0, mp.mpf(n) + 1) + mp.euler
    return _shrink(val, dps)


def robin_ratio(n: int, dps: int = DPS_DEFAULT):
    """``sigma(n) / (n log log n)`` -- Robin's ratio.

    THEOREM (Robin 1984): RH <=> this is < ``e^gamma = 1.7810724...`` for every
    n > 5040.  Defined for n >= 3 (``log log n <= 0`` for n <= 2).

    Unconditionally (Gronwall 1913) the limsup over all n *is* ``e^gamma``, so
    ``e^gamma`` is exactly the right constant and the only question is whether
    it is ever exceeded above 5040.
    """
    n = int(n)
    if n < 3:
        raise ValueError(f"robin_ratio needs n >= 3 (log log n > 0), got {n}")
    with mp.workdps(dps + _GUARD):
        val = mp.mpf(divisor_sigma(n)) / (mp.mpf(n) * mp.log(mp.log(n)))
    return _shrink(val, dps)


def robin_ratio_from_log(log_n, sigma_over_n, dps: int = DPS_DEFAULT):
    """Robin's ratio from ``log n`` and ``sigma(n)/n``.

    The colossally abundant numbers reach ``log n`` in the thousands within a
    few hundred steps, so ``n`` itself is a number with thousands of digits and
    ``sigma(n)`` likewise.  Both ``log n`` and ``sigma(n)/n`` stay small and
    well-conditioned (a sum and a product over the prime support), so the
    search runs in that representation.
    """
    with mp.workdps(dps + _GUARD):
        ln = mpmath.mpmathify(log_n)
        if ln <= 1:
            raise ValueError("robin_ratio_from_log needs log n > 1")
        val = mpmath.mpmathify(sigma_over_n) / mp.log(ln)
    return _shrink(val, dps)


def lagarias_ratio(n: int, dps: int = DPS_DEFAULT):
    """``sigma(n) / (H_n + exp(H_n) log H_n)`` -- Lagarias' elementary form.

    THEOREM (Lagarias 2002): RH <=> ``sigma(n) <= H_n + exp(H_n) log(H_n)`` for
    all n >= 1, with equality only at n = 1.  So this ratio is <= 1 for all n
    iff RH, and equals exactly 1 at n = 1.

    This is Robin in elementary clothing: ``H_n = log n + gamma + O(1/n)``, so
    ``exp(H_n) ~ e^gamma n`` and ``log H_n ~ log log n``; the extra ``H_n`` and
    the lower-order corrections supply exactly the slack that absorbs all 26
    values in :data:`ROBIN_EXCEPTIONS`, which is why Lagarias' form needs no
    "n > 5040" clause.
    """
    n = int(n)
    if n < 1:
        raise ValueError(f"lagarias_ratio expects n >= 1, got {n}")
    with mp.workdps(dps + _GUARD):
        H = mp.psi(0, mp.mpf(n) + 1) + mp.euler
        rhs = H + mp.e**H * mp.log(H)
        val = mp.mpf(divisor_sigma(n)) / rhs
    return _shrink(val, dps)


def lagarias_ratio_from_log(log_n, sigma_over_n, dps: int = DPS_DEFAULT):
    """Lagarias' ratio from ``log n`` and ``sigma(n)/n``, for astronomical n.

    Dividing numerator and denominator by n,

        sigma(n)/(H_n + e^{H_n} log H_n)
            = (sigma(n)/n) / ( H_n/n + exp(H_n - log n) * log H_n ),

    and ``H_n = log n + gamma + 1/(2n) - 1/(12 n^2) + 1/(120 n^4) - ...`` so
    ``exp(H_n - log n) -> e^gamma`` with no overflow anywhere.  Those four
    correction terms are carried; the first omitted one is ``1/(252 n^6)``,
    which is ``2.4e-25`` at n = 5040 and falls below the working precision
    (not to *exactly* zero -- it is never zero) at every colossally abundant
    number the search reaches.  Measured agreement with the exact
    :func:`lagarias_ratio`, and pinned in the tests: relative ``2.54e-25`` at
    n = 5040 -- matching the ``1/(252 n^6)`` prediction to one significant
    figure -- and ``1.0e-31`` (the dps = 30 rounding floor, i.e. no visible
    truncation left) at n = 55440 and beyond.
    """
    with mp.workdps(dps + _GUARD):
        ln = mpmath.mpmathify(log_n)
        sn = mpmath.mpmathify(sigma_over_n)
        if ln <= 1:
            raise ValueError("lagarias_ratio_from_log needs log n > 1")
        inv_n = mp.e ** (-ln)          # 1/n, evaluated from log n
        H = (
            ln
            + mp.euler
            + inv_n / 2
            - inv_n**2 / 12
            + inv_n**4 / 120
        )
        val = sn / (H * inv_n + mp.e ** (H - ln) * mp.log(H))
    return _shrink(val, dps)


def robin_violations(limit: int = 20000) -> list[int]:
    """Every ``3 <= n <= limit`` with ``sigma(n) >= e^gamma n log log n``.

    A direct sieve, not a clever search: this is the ground truth against which
    the superabundant search is calibrated.  Up to 20000 the answer is exactly
    :data:`ROBIN_EXCEPTIONS` -- 26 values, largest 5040, with
    ``sigma(5040) = 19344`` against ``e^gamma * 5040 * log log 5040 = 19237.06``
    (ratio 1.005559).  Every one is <= 5040, i.e. no violation of *Robin's
    criterion* was found in this range.

    The comparison is done in float64.  A test re-runs **all 19 998 verdicts**
    at dps = 30 and reports the smallest relative margin
    ``|ratio - e^gamma| / e^gamma`` over the whole range: it is
    ``8.7432e-4``, at n = 720 (which exceeds ``e^gamma``, so 720 is an
    exception); the tightest *non*-exception is n = 420 at ``9.874e-4``.
    Eleven orders of magnitude above float64 noise, so no float64 verdict in
    this range can be wrong.
    """
    limit = int(limit)
    sig = sigma_sieve(limit)
    e_gamma = float(mp.e**mp.euler)
    n = np.arange(limit + 1, dtype=np.float64)
    with np.errstate(divide="ignore", invalid="ignore"):
        bound = e_gamma * n * np.log(np.log(n))
    idx = np.arange(3, limit + 1)
    mask = sig[3:] >= bound[3:]
    return [int(v) for v in idx[mask]]


def lagarias_violations(limit: int = 20000) -> list[int]:
    """Every ``1 <= n <= limit`` with ``sigma(n) > H_n + exp(H_n) log H_n``.

    Expected to be empty (n = 1 gives equality, 1 <= 1, not a violation).
    The check runs in float64; a test redoes **all 20 000 comparisons** at
    dps = 30 and reports the smallest relative slack ``(rhs - sigma)/rhs``
    over 2 <= n <= 20000: it is ``1.1364e-2``, at n = 12.  Lagarias' form is
    far less tight than Robin's -- an order of magnitude more slack at its
    worst point -- so no float64 verdict here is in doubt either.
    """
    limit = int(limit)
    sig = sigma_sieve(limit)
    n = np.arange(limit + 1, dtype=np.float64)
    H = np.zeros(limit + 1, dtype=np.float64)
    np.cumsum(1.0 / np.arange(1, limit + 1), out=H[1:])
    with np.errstate(divide="ignore", invalid="ignore", over="ignore"):
        rhs = H + np.exp(H) * np.log(H)
    out = []
    for k in range(1, limit + 1):
        if sig[k] > rhs[k]:
            out.append(k)
    return out


def colossally_abundant(
    steps: int = 200,
    dps: int = DPS_DEFAULT,
    max_prime: int = 10**5,
) -> list[dict[str, Any]]:
    """The first ``steps`` colossally abundant numbers, generated greedily.

    n is *colossally abundant* if for some eps > 0, ``sigma(n)/n^{1+eps}`` is
    maximal over all positive integers.  Alaoglu and Erdos' construction makes
    them a chain: raising the exponent of p from ``a-1`` to ``a`` multiplies
    ``sigma(n)/n`` by ``(p^{a+1}-1)/(p(p^a-1))`` while multiplying ``n`` by p,
    so the critical parameter of that step is

        eps_p(a) = log[ (p^{a+1}-1) / (p (p^a - 1)) ] / log p,

    and taking the largest ``eps`` available at each step walks the CA numbers
    in increasing order.  The first fourteen produced here are
    2, 6, 12, 60, 120, 360, 2520, 5040, 55440, 720720, 1441440, 4324320,
    21621600, 367567200 -- matching the published sequence (OEIS A004490), a
    check the tests make.

    Ties (two primes with the same critical eps) are broken by the heap order;
    at a tie both orders give the same set of CA numbers a step later, so this
    only affects which of two equally valid chains is walked.

    ``eps`` is deliberately reduced to float64 before it enters the heap (only
    the *ordering* matters, and float keys make the heap cheap).  That is a
    precision drop inside an ``mp.workdps`` block, so it is checked rather than
    assumed: a test rebuilds the chain with mpf keys at dps = 40 and asserts
    the two chains agree step for step over 300 steps.  The gaps being resolved
    are ~1e-9 at the deepest step reached here, seven orders above float64
    noise.  Robin proved
    that *if* RH fails the counterexamples occur among the superabundant
    numbers, which is why this family is the only plausible place to look.

    Each record is a dict with ``step``, ``prime``/``exponent`` just raised,
    ``exponents`` (the full factorisation), ``log_n``, ``sigma_over_n``,
    ``n`` (the exact integer while it fits in 10^18, else ``None``),
    ``robin_ratio`` and ``lagarias_ratio`` (both ``None`` while ``log n <= 1``).
    """
    import heapq

    steps = int(steps)
    if steps < 1:
        raise ValueError(f"colossally_abundant expects steps >= 1, got {steps}")
    with mp.workdps(dps + _GUARD):
        primes = _primes_upto(max_prime)
        if steps > len(primes):
            raise ValueError(
                f"colossally_abundant: {steps} steps needs more than "
                f"{len(primes)} primes below {max_prime}"
            )

        def eps(p: int, a: int) -> float:
            P = mp.mpf(p)
            return float(mp.log((P ** (a + 1) - 1) / (P * (P**a - 1))) / mp.log(P))

        heap = [(-eps(p, 1), p, 1) for p in primes]
        heapq.heapify(heap)
        log_n = mp.mpf(0)
        sigma_over_n = mp.mpf(1)
        exps: dict[int, int] = {}
        n_exact: int | None = 1
        out: list[dict[str, Any]] = []
        for step in range(1, steps + 1):
            _, p, a = heapq.heappop(heap)
            P = mp.mpf(p)
            sigma_over_n *= (P ** (a + 1) - 1) / (P * (P**a - 1))
            log_n += mp.log(P)
            exps[p] = a
            if n_exact is not None and n_exact <= 10**18 // p:
                n_exact *= p
            else:
                n_exact = None
            heapq.heappush(heap, (-eps(p, a + 1), p, a + 1))
            rec: dict[str, Any] = {
                "step": step,
                "prime": p,
                "exponent": a,
                "exponents": dict(sorted(exps.items())),
                "log_n": _shrink(log_n, dps),
                "sigma_over_n": _shrink(sigma_over_n, dps),
                "n": n_exact,
            }
            if log_n > 1:
                rec["robin_ratio"] = robin_ratio_from_log(log_n, sigma_over_n, dps=dps)
                rec["lagarias_ratio"] = lagarias_ratio_from_log(
                    log_n, sigma_over_n, dps=dps
                )
            else:
                rec["robin_ratio"] = None
                rec["lagarias_ratio"] = None
            out.append(rec)
    return out


@lru_cache(maxsize=8)
def _primes_upto(limit: int) -> tuple[int, ...]:
    """Primes <= ``limit`` by a numpy sieve of Eratosthenes."""
    limit = int(limit)
    if limit < 2:
        return ()
    flags = np.ones(limit + 1, dtype=bool)
    flags[:2] = False
    for i in range(2, int(math.isqrt(limit)) + 1):
        if flags[i]:
            flags[i * i:: i] = False
    return tuple(int(p) for p in np.flatnonzero(flags))


def superabundant_candidates(max_log_n: float = 60.0) -> Iterator[tuple[int, ...]]:
    """Exponent patterns of every *superabundant-shaped* n with log n <= bound.

    A superabundant number ``n = prod p_i^{a_i}`` (primes in increasing order)
    necessarily has ``a_1 >= a_2 >= ... >= a_k >= 1`` -- equivalently, n is a
    product of primorials (Alaoglu and Erdos 1944).  That is a *necessary*
    condition, so enumerating all such patterns is a strictly wider net than
    enumerating the superabundant numbers themselves.

    Yields tuples ``(a_1, ..., a_k)``.  Counts measured here: 27055 patterns for
    ``log n <= 40``, 288457 for ``<= 60``, 2023242 for ``<= 80``.  The bound is
    applied to a float64 ``log n``, so a pattern sitting within 1e-13 of the
    bound may fall either side of it; nothing downstream depends on which.
    """
    bound = float(max_log_n)
    primes = _primes_upto(4096)
    logp = [math.log(p) for p in primes]
    if bound >= sum(logp):
        raise ValueError(
            f"superabundant_candidates: max_log_n={bound} exceeds the primorial "
            f"of all primes below 4096 (log = {sum(logp):.1f}); the enumeration "
            "would silently truncate"
        )
    exps: list[int] = []

    def rec(i: int, max_exp: int, log_n: float) -> Iterator[tuple[int, ...]]:
        if i > 0:
            yield tuple(exps)
        if i >= len(primes):
            return
        a = 1
        while a <= max_exp:
            ln = log_n + a * logp[i]
            if ln > bound:
                break
            exps.append(a)
            yield from rec(i + 1, a, ln)
            exps.pop()
            a += 1

    yield from rec(0, 4096, 0.0)


def robin_search(
    max_log_n: float = 60.0,
    ca_steps: int = 500,
    dps: int = DPS_DEFAULT,
) -> dict[str, Any]:
    """Search the only plausible violators of Robin's inequality above 5040.

    Two nets are cast:

    * **exhaustive** over every superabundant-shaped ``n`` (non-increasing
      prime exponents) with ``log n <= max_log_n``.  Two facts make this the
      right net.  Superabundant numbers have non-increasing prime exponents
      (Alaoglu and Erdos 1944), so the enumeration contains every superabundant
      number of that size; and the *least* counterexample to Robin's
      inequality, if one exists, is superabundant -- usually credited to Akbary
      and Friggstad, Amer. Math. Monthly 116 (2009) 273--275; I am confident in
      the statement and hedging on the reference.  Together: no counterexample
      at all below ``e^{max_log_n}`` if none is found here.  (Robin's own
      companion result is weaker in form -- if RH fails there are infinitely
      many counterexamples, and they occur among the superabundant numbers.)
    * **deep** along the colossally abundant chain for ``ca_steps`` steps,
      which reaches ``log n`` in the thousands -- integers with thousands of
      digits -- where the ratio is climbing towards ``e^gamma``.

    Results measured in this environment:

    * exhaustive to ``log n <= 80`` (2023242 patterns): **no violation**; the
      largest ratio above 5040 is ``1.755814338925`` at
      ``n = 2^5 * 3^2 * 5 * 7 = 10080``, i.e. ``e^gamma - max = 2.53e-02``;
    * CA chain to step 2000 (``log n = 16674``, n of about 7242 digits): **no
      violation**; the ratio climbs to ``1.779881``, i.e. within ``1.19e-03``
      of ``e^gamma = 1.7810724...`` -- and by Gronwall's theorem it must keep
      climbing towards ``e^gamma`` forever without (under RH) ever reaching it.
      The climb is *not* monotone: measured dips occur when a new large prime
      enters -- exactly at chain steps 10, 11, 12, 13, 17, 18, 21, 28, 29, 52,
      126, 129 among the steps with ``log n > log 5040`` (that list is pinned
      by a test) -- so the reported maximum is a genuine max over the chain,
      not its last term.

    Both headline results above are pinned by ``test_criteria.py``
    (``test_robin_search_to_log_n_80_and_2000_ca_steps``, ~3 s).

    The exhaustive scan runs in float64 and every reported extremum is
    recomputed at ``dps`` digits before it is returned.  The "no violation"
    conclusion is safe in float64 by a wide margin, not by luck: the largest
    ratio anywhere in the net is 1.7558, which is 2.5e-2 below ``e^gamma``,
    while the float64 error in ``sigma(n)/n`` accumulated over the ~60
    multiplications of a pattern is ~1e-14.  Returns a dict with the counts,
    the two maxima, the gaps to ``e^gamma``, and the (expected empty)
    violation lists.
    """
    primes = _primes_upto(4096)
    logp = [math.log(p) for p in primes]
    if float(max_log_n) >= sum(logp):
        raise ValueError(
            f"robin_search: max_log_n={max_log_n} exceeds the primorial of all "
            f"primes below 4096 (log = {sum(logp):.1f}); the exhaustive scan "
            "would silently truncate"
        )
    e_gamma = float(mp.e**mp.euler)
    log_thresh = math.log(ROBIN_THRESHOLD)

    best_ratio = -1.0
    best_pattern: tuple[int, ...] = ()
    violations: list[tuple[int, ...]] = []
    scanned = 0
    exps: list[int] = []

    def rec(i: int, max_exp: int, log_n: float, sig: float) -> None:
        nonlocal best_ratio, best_pattern, scanned
        if i > 0:
            scanned += 1
            if log_n > log_thresh:
                ratio = sig / math.log(log_n)
                if ratio > best_ratio:
                    best_ratio, best_pattern = ratio, tuple(exps)
                if ratio >= e_gamma:
                    violations.append(tuple(exps))
        if i >= len(primes):
            return
        p = primes[i]
        a, pk, s = 1, p, 1.0 + 1.0 / p
        while a <= max_exp:
            ln = log_n + a * logp[i]
            if ln > max_log_n:
                break
            exps.append(a)
            rec(i + 1, a, ln, sig * s)
            exps.pop()
            a += 1
            pk *= p
            s += 1.0 / pk

    rec(0, 4096, 0.0, 1.0)

    # Re-derive the exhaustive-scan maximum at `dps`, from the *pattern* rather
    # than by re-factoring n: n can have tens of digits and trial division on it
    # would be hopeless, whereas log n and sigma(n)/n are a sum and a product
    # over the (known) prime support and are exact to working precision.
    n_best = 1
    for i, a in enumerate(best_pattern):
        n_best *= primes[i] ** a
    best_exact = lagarias_best = None
    if best_pattern:
        with mp.workdps(dps + _GUARD):
            log_best = mp.fsum(a * mp.log(primes[i]) for i, a in enumerate(best_pattern))
            sig_best = mp.mpf(1)
            for i, a in enumerate(best_pattern):
                p = mp.mpf(primes[i])
                sig_best *= (p ** (a + 1) - 1) / (p**a * (p - 1))
        best_exact = robin_ratio_from_log(log_best, sig_best, dps=dps)
        lagarias_best = lagarias_ratio_from_log(log_best, sig_best, dps=dps)
        if n_best < 10**12:
            # small enough to factor: cross-check the pattern arithmetic against
            # the trial-division sigma, which is the sympy-verified path
            with mp.workdps(dps + _GUARD):
                if abs(robin_ratio(n_best, dps=dps) - best_exact) > mp.mpf(10) ** (-dps + 5):
                    raise ArithmeticError(
                        "robin_search: pattern arithmetic disagrees with "
                        f"divisor_sigma at n = {n_best}"
                    )

    chain = colossally_abundant(ca_steps, dps=dps)
    ca_above = [r for r in chain if r["robin_ratio"] is not None and r["log_n"] > log_thresh]
    with mp.workdps(dps + _GUARD):
        eg = mp.e**mp.euler
        ca_best = max(ca_above, key=lambda r: r["robin_ratio"]) if ca_above else None
        ca_violations = [r["step"] for r in ca_above if r["robin_ratio"] >= eg]
        lag_violations = [
            r["step"]
            for r in chain
            if r["lagarias_ratio"] is not None and r["lagarias_ratio"] > 1
        ]
        e_gamma_mp = _shrink(eg, dps)
        gap_exhaustive = _shrink(eg - best_exact, dps) if best_exact is not None else None
        gap_ca = _shrink(eg - ca_best["robin_ratio"], dps) if ca_best else None

    return {
        "criterion": "RH <=> sigma(n) < e^gamma n log log n for all n > 5040",
        "criterion_status": "THEOREM (Robin 1984)",
        "e_gamma": e_gamma_mp,
        # exhaustive superabundant-shaped scan
        "max_log_n": float(max_log_n),
        "patterns_scanned": scanned,
        "exhaustive_max_ratio": best_exact,
        "exhaustive_argmax_n": n_best,
        "exhaustive_argmax_pattern": best_pattern,
        "exhaustive_gap_to_e_gamma": gap_exhaustive,
        "exhaustive_lagarias_ratio_at_argmax": lagarias_best,
        "exhaustive_violations": violations,
        # colossally abundant chain
        "ca_steps": ca_steps,
        "ca_max_ratio": None if ca_best is None else ca_best["robin_ratio"],
        "ca_argmax_step": None if ca_best is None else ca_best["step"],
        "ca_argmax_log_n": None if ca_best is None else ca_best["log_n"],
        "ca_gap_to_e_gamma": gap_ca,
        "ca_violations": ca_violations,
        "lagarias_violations_on_chain": lag_violations,
        "honest_scope": (
            "no violation found in the range scanned; Gronwall's theorem "
            "guarantees the ratio approaches e^gamma, so closeness to e^gamma "
            "is expected and is not evidence for or against RH"
        ),
    }


# ===========================================================================
# 4.  SPEISER
# ===========================================================================

#: The two zeros of zeta' of smallest positive imaginary part, as located here
#: at dps = 25 (the default of :func:`zeta_prime_zeros`) and agreeing to all
#: 15 quoted digits with the values in docs/07 (which come from Spira's
#: tables).  Strings, parsed inside a workdps context by the tests.
ZETA_PRIME_ZEROS_PINNED: tuple[tuple[str, str], ...] = (
    ("2.46316186945432", "23.2983204927629"),
    ("1.28649682226905", "31.7082500831159"),
)


def zeta_prime(s, dps: int = DPS_DEFAULT):
    """``zeta'(s)``, the derivative of the Riemann zeta function.

    A thin wrapper on ``mpmath.zeta(s, derivative=1)``; it exists so that the
    Speiser routines have a single evaluation point to memoise and so that the
    working precision is handled the same way as everywhere else in the
    package.  ``zeta'`` has a double pole at s = 1 and is analytic elsewhere.
    """
    with mp.workdps(dps + _GUARD):
        z = mpmath.mpmathify(s)
        val = mp.zeta(z, derivative=1)
    return _shrink(val, dps)


def _zp_counter():
    """A memoised ``zeta'`` for the argument-principle contours.

    Recursive box subdivision revisits shared edges constantly; memoising cuts
    the wall time of the whole scan by a factor of about six (measured: 950
    distinct ``zeta'`` evaluations for ``0.001 <= Re <= 6, 1 <= Im <= 60``,
    2543 for the same strip up to ``Im = 100``; both pinned in the tests).

    Deliberately takes no ``dps``: every call is made from inside the
    ``mp.workdps(count_dps)`` context of :func:`zeta.epstein.count_zeros_box`,
    so the memoised values are all at the counting precision.  An earlier
    version accepted a ``dps`` argument and silently ignored it.
    """
    memo: dict[tuple, Any] = {}

    def f(z):
        key = (mp.re(z), mp.im(z))
        v = memo.get(key)
        if v is None:
            v = mp.zeta(z, derivative=1)
            memo[key] = v
        return v

    f.memo = memo  # type: ignore[attr-defined]
    return f


def _count_zp(fn, a, b, c, d, dps: int, step) -> int:
    from .epstein import count_zeros_box

    return count_zeros_box(mp.mpc(a, c), mp.mpc(b, d), dps=dps, fn=fn, step=step)


def _polish_zp(a, b, c, d, dps: int):
    """Locate the single zero of ``zeta'`` inside a box, or return None.

    **Both solvers are load-bearing** -- measured, not assumed.  Over the 25
    boxes the ``Im <= 100`` scan actually bisects down to, a Muller-only
    ``_polish_zp`` fails on 5 of them (including the zero at
    ``0.8646228644 + 76.3628078965i``) and a secant-only one fails on 3
    (including ``1.8959597625 + 57.1347531990i``).  Neither ordering alone
    finds all 19 zeros, so secant is tried first and Muller second, from a
    3x3 grid of seeds; two representative failures are pinned in the tests.
    A candidate is accepted only if it lies inside the box *and* ``|zeta'|``
    is below ``10^{-dps+5}``.
    """
    with mp.workdps(dps + _GUARD):
        f = lambda z: mp.zeta(z, derivative=1)  # noqa: E731
        tol = mp.mpf(10) ** (-dps + 5)
        for i in (2, 1, 3):
            for j in (2, 1, 3):
                seed = mp.mpc(a + (b - a) * i / 4, c + (d - c) * j / 4)
                for solver in ("secant", "muller"):
                    try:
                        r = mp.findroot(f, seed, solver=solver)
                    except Exception:
                        # mpmath raises a plain ValueError ("Could not find root
                        # within given tolerance") as well as ZeroDivisionError
                        # and libmp.NoConvergence from inside the solvers; a
                        # failed seed is ordinary here, not an error.
                        continue
                    if a <= mp.re(r) <= b and c <= mp.im(r) <= d and abs(f(r)) < tol:
                        return +r
    return None


def _zp_zeros_path(t_min, t_max, sigma_min, sigma_max, dps: int,
                   count_dps: int, step) -> Path:
    """Cache path with *every* parameter that can change the answer in the name.

    ``count_dps`` and ``step`` control the argument-principle counting and so
    control which zeros are reported; leaving them out of the key would let a
    changed counting scheme be silently served a stale table (AGENTS.md:
    "cache keys encode parameters in filenames").
    """
    tag = "_".join(
        mp.nstr(mp.mpf(v), 8) for v in (sigma_min, sigma_max, t_min, t_max)
    ).replace(" ", "")
    stp = mp.nstr(mp.mpf(step), 8).replace(" ", "")
    return _data_dir() / f"zeta_prime_zeros_{tag}_dps{dps}_c{count_dps}_s{stp}.json"


def zeta_prime_zeros(
    t_min=1,
    t_max=60,
    sigma_min="0.001",
    sigma_max=6,
    dps: int = 25,
    count_dps: int = 15,
    step="0.4",
    max_depth: int = 16,
    use_cache: bool = True,
) -> dict[str, Any]:
    """Every zero of ``zeta'`` in the rectangle, with a counting cross-check.

    Method: the argument principle on the rectangle (reusing
    ``zeta.epstein.count_zeros_box``, which is generic in its ``fn``) gives the
    number of zeros; the box is then bisected in both directions until each
    piece holds exactly one, which is polished by :func:`_polish_zp`.  The
    returned ``box_count`` and ``len(zeros)`` must agree, and a mismatch
    raises.

    **How much that cross-check is worth -- stated plainly.**  It is *not* a
    rigorous certificate.  ``box_count`` is a floating-point evaluation of
    ``(1/2 pi) * (variation of arg zeta')`` along the boundary, accepted when
    it lands within 1e-6 of an integer; no interval arithmetic is involved and
    an undersampled edge could in principle lose a full turn.  What backs it
    up here is measurement: the count is invariant when the forced subdivision
    ``step`` is halved from 0.4 to 0.2 to 0.1, and an entirely separate
    uniform-grid winding sum -- one with no adaptivity at all, which
    *verifies* that every consecutive phase increment stays under pi/2 (the
    largest is 0.13 rad at a grid of 0.05) -- returns 3 for ``Im <= 40`` and
    19 for ``Im <= 100``, and 0 for the Speiser strip in both.  Both checks
    are tests.  Two independent schemes agreeing, plus ``len(zeros)``
    matching, is strong evidence and nothing more.

    ``sigma_min`` defaults to 0.001 rather than 0: a zero *on* the contour makes
    the winding ill-posed, and the sliver ``0 < Re(s) < 0.001`` is therefore not
    covered (say so, do not paper over it).  ``t_min`` defaults to 1 so the
    contour never approaches the double pole of ``zeta'`` at s = 1.

    Measured here (dps = 25, count_dps = 15, step = 0.4):
    ``0.001 <= Re <= 6, 1 <= Im <= 60``: 7 zeros, 5.8 s, 950 distinct ``zeta'``
    evaluations, leftmost Re = 0.964685622705686;
    ``0.001 <= Re <= 6, 1 <= Im <= 100``: 19 zeros, 35.5 s, 2543 evaluations,
    leftmost Re = 0.780628004724645 (at t = 95.2929682713522).  The largest
    residual ``|zeta'(z)|`` at the 19 located zeros is 8.2e-25.
    The two lowest are ``2.46316186945432 + 23.2983204927629i`` and
    ``1.28649682226905 + 31.7082500831159i``, matching docs/07.

    Results cache to ``data/zeta_prime_zeros_*.json`` (committed, like the
    zero tables of :mod:`zeta.zeros`); the filename carries the window, ``dps``,
    ``count_dps`` and ``step``, so changing any of them cannot be served a
    stale table.
    """
    with mp.workdps(dps + _GUARD):
        if mp.mpf(sigma_min) <= 0:
            raise ValueError("sigma_min must be > 0 (the contour must miss Re(s)=0)")
        if mp.mpf(t_min) <= 0:
            raise ValueError("t_min must be > 0 (the contour must miss the pole at s=1)")
    path = _zp_zeros_path(t_min, t_max, sigma_min, sigma_max, dps, count_dps, step)
    if use_cache and path.exists():
        try:
            payload = json.loads(path.read_text())
            with mp.workdps(dps + _GUARD):
                zeros = [mp.mpc(mp.mpf(re_), mp.mpf(im_)) for re_, im_ in payload["zeros"]]
            payload["zeros"] = zeros
            return payload
        except (OSError, json.JSONDecodeError, KeyError):
            pass

    with mp.workdps(dps + _GUARD):
        a0, b0 = mp.mpf(sigma_min), mp.mpf(sigma_max)
        c0, d0 = mp.mpf(t_min), mp.mpf(t_max)
        stp = mp.mpf(step)
        fn = _zp_counter()
        total = _count_zp(fn, a0, b0, c0, d0, count_dps, stp)

        def find(a, b, c, d, depth: int) -> list:
            n = _count_zp(fn, a, b, c, d, count_dps, stp)
            if n == 0:
                return []
            if n == 1:
                r = _polish_zp(a, b, c, d, dps)
                if r is not None:
                    return [r]
            if depth >= max_depth:
                raise ArithmeticError(
                    "zeta_prime_zeros: could not separate "
                    f"{n} zero(s) in [{mp.nstr(a, 10)},{mp.nstr(b, 10)}] x "
                    f"[{mp.nstr(c, 10)},{mp.nstr(d, 10)}] within {max_depth} levels"
                )
            am, cm = (a + b) / 2, (c + d) / 2
            out: list = []
            for (x0, x1) in ((a, am), (am, b)):
                for (y0, y1) in ((c, cm), (cm, d)):
                    out += find(x0, x1, y0, y1, depth + 1)
            return out

        zeros = sorted(find(a0, b0, c0, d0, 0), key=lambda z: mp.im(z))
        if len(zeros) != total:
            raise ArithmeticError(
                f"zeta_prime_zeros: located {len(zeros)} zeros but the argument "
                f"principle counts {total} in the box"
            )
        zeros = [_shrink(z, dps) for z in zeros]
        evaluations = len(fn.memo)  # type: ignore[attr-defined]

    result = {
        "sigma_min": mp.nstr(mp.mpf(sigma_min), 10),
        "sigma_max": mp.nstr(mp.mpf(sigma_max), 10),
        "t_min": mp.nstr(mp.mpf(t_min), 10),
        "t_max": mp.nstr(mp.mpf(t_max), 10),
        "dps": dps,
        "box_count": total,
        "zeros": zeros,
        "zeta_prime_evaluations": evaluations,
    }
    if use_cache:
        serial = dict(result)
        serial["zeros"] = [
            [mp.nstr(mp.re(z), dps + 5), mp.nstr(mp.im(z), dps + 5)] for z in zeros
        ]
        path.write_text(json.dumps(serial, indent=1))
    return result


def speiser_scan(
    t_max=60,
    t_min=1,
    sigma_max=6,
    sigma_min="0.001",
    dps: int = 25,
    count_dps: int = 15,
    step="0.4",
    use_cache: bool = True,
) -> dict[str, Any]:
    """Speiser's criterion, executed on a window.

    THEOREM (Speiser 1934/35).  RH <=> ``zeta'`` has no zeros in the strip
    ``0 < Re(s) < 1/2``.

    Three separate argument-principle counts, so the conclusion does not rest
    on the root finder:

    * ``left_strip_count``  -- zeros of ``zeta'`` with ``sigma_min < Re < 1/2``
      in the height window.  Speiser says this is 0 for every window iff RH.
    * ``right_tail_count``  -- zeros with ``sigma_max < Re < 30``, checked to be
      0 so that ``sigma_max`` is not hiding anything.  (Spira is usually cited
      for ``zeta'(s) != 0`` when ``Re(s) >= 2.93``; I am hedging on the constant
      and measuring instead.)  Beyond Re = 30 no contour is needed: from
      ``zeta'(s) = -sum_{n>=2} (log n) n^{-s}`` the n = 2 term dominates all
      the rest for ``Re(s) >= 30`` -- ``(log 2) 2^{-30} = 6.5e-10`` against
      ``sum_{n>=3} (log n) n^{-30} = 5.3e-15``, a ratio of 10^5 -- so ``zeta'``
      cannot vanish there.  That inequality is checked in the tests.
    * the located zeros themselves, whose count must match the box count.

    Measured here for ``1 <= Im <= 100``: 19 zeros, all with ``Re > 1/2``, the
    leftmost at ``Re = 0.780628004725`` (t = 95.2929682714); the strip
    ``0.001 < Re < 0.5`` is **empty**, and so is ``6 < Re < 30``.

    Honest scope: this is a statement about one finite window, reached by
    floating-point argument-principle counts, not by certified arithmetic --
    see the paragraph on that in :func:`zeta_prime_zeros`.  It is what
    Speiser's criterion *predicts* under RH and would falsify RH if violated;
    finding no violation is not evidence for RH.
    """
    found = zeta_prime_zeros(
        t_min=t_min,
        t_max=t_max,
        sigma_min=sigma_min,
        sigma_max=sigma_max,
        dps=dps,
        count_dps=count_dps,
        step=step,
        use_cache=use_cache,
    )
    with mp.workdps(dps + _GUARD):
        fn = _zp_counter()
        stp = mp.mpf(step)
        a0 = mp.mpf(sigma_min)
        left = _count_zp(fn, a0, mp.mpf(0.5), mp.mpf(t_min), mp.mpf(t_max), count_dps, stp)
        right = _count_zp(
            fn, mp.mpf(sigma_max), mp.mpf(30), mp.mpf(t_min), mp.mpf(t_max), count_dps, stp
        )
        zeros = found["zeros"]
        res = [mp.re(z) for z in zeros]
        leftmost = min(res) if res else None
        leftmost_at = None
        if leftmost is not None:
            leftmost_at = mp.im(zeros[res.index(leftmost)])
    return {
        "criterion": "RH <=> zeta'(s) has no zeros in 0 < Re(s) < 1/2",
        "criterion_status": "THEOREM (Speiser, Math. Ann. 110, 1934/35)",
        "window": {
            "sigma_min": found["sigma_min"],
            "sigma_max": found["sigma_max"],
            "t_min": found["t_min"],
            "t_max": found["t_max"],
        },
        "box_count": found["box_count"],
        "zeros": zeros,
        "n_zeros": len(zeros),
        "left_strip_count": left,
        "right_tail_count": right,
        "leftmost_re": None if leftmost is None else _shrink(leftmost, dps),
        "leftmost_at_t": None if leftmost_at is None else _shrink(leftmost_at, dps),
        "all_right_of_critical_line": all(r > mp.mpf(0.5) for r in res),
        "uncovered_sliver": f"0 < Re(s) <= {found['sigma_min']} is not scanned",
        "honest_scope": (
            "no zero of zeta' found left of the critical line in this window; "
            "a finite window is not evidence for RH (docs/08)"
        ),
    }


# ===========================================================================
# summary
# ===========================================================================

def criteria_report(
    mertens_limit: int = 10**6,
    bd_N: int = 20,
    bd_dps: int = 50,
    robin_max_log_n: float = 40.0,
    robin_ca_steps: int = 200,
    speiser_t_max: float = 40.0,
) -> dict[str, Any]:
    """All four faces in one dict -- the module's ``battery``.

    Defaults are chosen to run in a few seconds; every argument scales the
    corresponding face.  Nothing here is evidence for RH: each entry reports
    what was found in a stated finite range.
    """
    ext = mertens_ratio_extremes(mertens_limit, x_min=1)
    ext100 = mertens_ratio_extremes(mertens_limit, x_min=100)
    bd = baez_duarte_d2(bd_N, dps=bd_dps)
    robin = robin_search(max_log_n=robin_max_log_n, ca_steps=robin_ca_steps)
    speiser = speiser_scan(t_max=speiser_t_max)
    return {
        "mertens": {
            "criterion": "RH <=> M(x) = O(x^{1/2+eps})  [THEOREM]",
            "strong_mertens_conjecture": "FALSE (Odlyzko-te Riele 1985)",
            "limit": mertens_limit,
            "M_at_limit": ext["M_at_limit"],
            "max_abs_ratio": ext["max_abs_ratio"],
            "argmax_abs": ext["argmax_abs"],
            "max_abs_ratio_from_100": ext100["max_abs_ratio"],
            "argmax_abs_from_100": ext100["argmax_abs"],
        },
        "baez_duarte": {
            "criterion": "RH <=> d_N -> 0  [THEOREM, Baez-Duarte 2003]",
            "N": bd["N"],
            "d2": bd["d2"],
            "condition_number": bd["condition_number"],
        },
        "robin": {
            "criterion": "RH <=> sigma(n) < e^gamma n log log n for n > 5040  [THEOREM]",
            "patterns_scanned": robin["patterns_scanned"],
            "exhaustive_max_ratio": robin["exhaustive_max_ratio"],
            "exhaustive_argmax_n": robin["exhaustive_argmax_n"],
            "ca_max_ratio": robin["ca_max_ratio"],
            "gap_to_e_gamma": robin["ca_gap_to_e_gamma"],
            "violations": robin["exhaustive_violations"] + robin["ca_violations"],
        },
        "speiser": {
            "criterion": "RH <=> zeta' has no zero in 0 < Re(s) < 1/2  [THEOREM]",
            "n_zeros": speiser["n_zeros"],
            "left_strip_count": speiser["left_strip_count"],
            "leftmost_re": speiser["leftmost_re"],
        },
        "honest_scope": (
            "four exactly-equivalent reformulations, each checked on a finite "
            "range; no finite range is evidence for RH (docs/08, Littlewood), "
            "and the Mertens face is here precisely because it is the standing "
            "counterexample to reading numerics as evidence"
        ),
    }
