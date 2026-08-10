"""``localpos`` — the place-local Toeplitz gate, and what it does *not* decide.

An attempt at ``docs/09`` §5.1's Requirement C ("structural positivity") at one
place at a time, run to its wall. The construction is real and closes exactly;
the honest verdict is in :func:`scope` and in ``docs/24`` — it factors the
prime side of the explicit formula into a manifest norm, and that is provably
not enough to reach RH.

What is built
-------------

For a Dirichlet series ``f(s) = Σ aₙ n^{-s}`` with ``a₁ = 1``, write
``−f′/f = Σ bₙ Λ-style`` and set ``λ_m = b_{p^m}/log p`` at the place ``p``.
The **place-p kernel** is the Toeplitz form

    K_p^{(d)}(θ) = d + 2 Σ_{m≥1} λ_m p^{−m/2} cos(mθ),

and the object this module computes is the *normalization-free* threshold

    c_p := − min_θ 2 Σ_{m≥1} λ_m p^{−m/2} cos(mθ),

so that ``K_p^{(d)} ≥ 0 ⟺ c_p ≤ d``. Nothing is chosen: ``d`` is the degree
read off the object's own gamma factors, and ``c_p`` is a minimum, not a fit.

The theorem behind it (proved by the closed form, checked numerically in
:func:`satake_check`): if the place has a genuine Euler factor with Satake
parameters ``α_j``, then ``λ_m = Σ_j α_j^m`` and the series sums to

    K_p^{(d)}(θ) = Σ_j (1 − |α_j|²/p) / |1 − α_j p^{−1/2} e^{iθ}|²,

which is a sum of manifestly nonnegative terms exactly when ``|α_j| ≤ √p``.
So ``c_p ≤ d`` is *equivalent* to the local Selberg-class bound at ``p`` —
not to "has an Euler product", which is the trap this module is built to
avoid asserting (see :func:`ramanujan_violator`).

Why the kernel is the thing
---------------------------

``K_p`` is not decoration. Writing ``Φ_p f = Σ_{m≥0} p^{−m/2} f(· − m log p)``
(the one-sided local shift-average), the prime side of the Riemann–Weil
explicit formula decomposes place by place as

    prime term = − Σ_p log p · (Q_p(f) − ‖f‖²),   Q_p(f) = (1 − 1/p)‖Φ_p f‖²,

measured against ``zeta.weil.explicit_formula_sides`` and agreeing to 22
digits. Each ``Q_p ≥ 0`` *by construction* — it is a norm — which is
Requirement C's norm identity, achieved locally.

And the wall, stated in the same breath: ``Q_p − ‖f‖²`` is **not** of definite
sign (measured: 52 of 60 places positive, 8 negative, for the autocorrelation
pair). The local norms do not assemble into a global one. Positivity of every
``Q_p`` is therefore compatible with either sign of ``W(h)``, and this
construction does not decide RH. It never could: Requirement A forbids
importing zeros, and ``c_p`` is a coefficient functional, while by ``docs/18``
§6 no coefficient functional can read the *position* of the critical line —
``ζ(s−δ)`` has the same ``a_n`` up to a shift and its zeros are nowhere near
``Re s = ½``.

Provenance (``docs/09`` §5.1 Requirement A)
-------------------------------------------

Every quantity here is a function of ``{a_{p^k}}`` alone. No zeros, no
``ξ``-phases, no zero-counting functions enter any definition. That is
mechanically checkable and :func:`provenance_report` states it.

Honest scope
------------

Nothing here is evidence for RH, and a PASS is not a certificate: the
detector's blindness threshold is measured (``eps*`` in :func:`lesion_sweep`,
≈ 0.184 on the ζ→DH interpolation), so a PASS means "no violation above that
magnitude at the tested places". See :func:`scope`.
"""

from __future__ import annotations

import math
from functools import lru_cache
from typing import Callable, Iterable, Sequence

import numpy as np

__all__ = [
    "DEFAULT_PRIMES",
    "local_lambdas",
    "threshold",
    "kernel",
    "satake_kernel",
    "gate",
    "periodic_local",
    "satake_local",
    "epstein_local",
    "epstein_local_check",
    "lesion_sweep",
    "null_distribution",
    "reference_table",
    "provenance_report",
    "scope",
]

#: The places scanned by default. Small primes carry the signal: c_p → 0 like
#: 2d/√p, so a violation that is invisible at p = 2, 3 is invisible everywhere.
DEFAULT_PRIMES: tuple[int, ...] = (
    2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47,
    53, 59, 61, 67, 71, 73, 79, 83, 89, 97,
)

#: Series truncation target. The tail is *bounded*, not hoped for: see the
#: ``tail`` return of :func:`threshold`.
DEFAULT_TOL: float = 1e-14


# ---------------------------------------------------------------------------
# local coefficient interfaces
# ---------------------------------------------------------------------------


def periodic_local(period: Sequence[float]) -> Callable[[int, int], float]:
    """``a_{p^k}`` for a sequence periodic mod ``q = len(period)``.

    ``period[r]`` is ``a_n`` for ``n ≡ r (mod q)``; index 0 is the ``q | n``
    slot. Exact by modular exponentiation — no coefficient array, so no
    ceiling on ``k`` (the p^k overflow that a truncated array imposes is the
    reason this indirection exists).
    """
    q = len(period)
    if q == 0:
        raise ValueError("period must be non-empty")
    return lambda p, k: float(period[pow(int(p), int(k), q)])


def satake_local(alphas: Sequence[complex]) -> Callable[[int, int], float]:
    """``a_{p^k} = h_k(α)``, the complete homogeneous symmetric polynomial —
    i.e. the genuine degree-``len(alphas)`` Euler factor ``Π (1 − α_j x)^{-1}``.

    Used for the reference PASS cases and for :func:`ramanujan_violator`.
    """
    a = tuple(complex(x) for x in alphas)

    def coeff(p: int, k: int) -> float:
        if k == 0:
            return 1.0
        # h_k by Newton-free expansion: coefficients of Π 1/(1-α_j x)
        series = np.zeros(k + 1, dtype=complex)
        series[0] = 1.0
        for al in a:
            acc = np.zeros(k + 1, dtype=complex)
            power = 1.0 + 0j
            for j in range(k + 1):
                acc[j:] += series[: k + 1 - j] * power
                power *= al
            series = acc
        return float(series[k].real)

    return coeff


def epstein_local(principal: bool = True, disc: int = -23) -> Callable[[int, int], float]:
    """``a_{p^k}`` for an Epstein zeta function of discriminant ``disc``.

    Specialised to ``disc = -23`` (class number 3, unit group ±1), the pair of
    rivals the zeta department already uses. ``principal=True`` gives the form
    ``x²+xy+6y²``; ``False`` gives ``2x²+xy+3y²``.

    Counted through ideal classes rather than by enumerating lattice points:
    ``zeta.epstein.epstein_representation_count`` is exact but enumerates, so it
    cannot reach the ``p^k`` with ``k ≈ 90`` that the ``p = 2`` truncation needs.
    The two agree on every ``p^k`` small enough for both — asserted in
    :func:`epstein_local_check`, which is the reason this shortcut is allowed.
    """
    if disc != -23:
        raise NotImplementedError(
            "only disc = -23 (h = 3) is implemented; other discriminants need their "
            "own class-group bookkeeping"
        )

    def kronecker(p: int) -> int:
        if p == 2:
            return 0 if disc % 2 == 0 else (1 if disc % 8 in (1, 7) else -1)
        a = disc % p
        if a == 0:
            return 0
        return 1 if pow(a, (p - 1) // 2, p) == 1 else -1

    @lru_cache(maxsize=None)
    def represented_by_principal(p: int) -> bool:
        for y in range(0, int(math.isqrt(int(4 * p / abs(disc)))) + 2):
            for x in range(-int(math.isqrt(p)) - 2, int(math.isqrt(p)) + 3):
                if x * x + x * y + 6 * y * y == p:
                    return True
        return False

    def coeff(p: int, k: int) -> float:
        if k == 0:
            return 1.0
        chi = kronecker(p)
        if chi == -1:                      # inert: only even k, and (p)^{k/2} is principal
            n_ideals = 1 if k % 2 == 0 else 0
            return float(n_ideals if principal else 0)
        if chi == 0:                       # ramified: [P]^2 principal, h = 3 odd => [P] principal
            return float(1 if principal else 0)
        # split: P^i Pbar^{k-i}, class [P]^{2i-k}; ord([P]) is 1 or 3
        if represented_by_principal(p):
            return float((k + 1) if principal else 0)
        n_principal = sum(1 for i in range(k + 1) if (2 * i - k) % 3 == 0)
        return float(n_principal if principal else (k + 1 - n_principal) // 2)

    return coeff


def epstein_local_check(max_n: int = 5000) -> dict:
    """Cross-check :func:`epstein_local` against the laboratory's own counter.

    ``r_Q(n) = 2·#{ideals of norm n in the class}`` for disc −23 (units ±1), so
    the comparison is exact, not approximate. Returns the prime powers tested
    and any disagreement; an empty ``mismatches`` is the licence to use the
    class-group route at the depths the gate needs.
    """
    from zeta import epstein as _ep

    tested, mismatches = 0, []
    principal, nonprincipal = epstein_local(True), epstein_local(False)
    for p in (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 59):
        for k in (1, 2, 3):
            n = p**k
            if n > max_n:
                continue
            tested += 1
            got = (2 * principal(p, k), 2 * nonprincipal(p, k))
            want = (
                float(_ep.epstein_representation_count(n, (1, 1, 6))),
                float(_ep.epstein_representation_count(n, (2, 1, 3))),
            )
            if got != want:
                mismatches.append({"n": n, "got": got, "want": want})
    return {"tested": tested, "mismatches": mismatches}


def local_lambdas(aloc: Callable[[int, int], float], p: int, M: int) -> np.ndarray:
    """``λ_0..λ_M`` at the place ``p`` from the log-derivative recursion.

    ``λ_m = m·a_{p^m} − Σ_{j<m} a_{p^j} λ_{m−j}``, with ``λ_0 = 1``. For a
    genuine Euler factor this returns the power sums ``Σ_j α_j^m`` (checked in
    :func:`satake_check`); for ζ it returns all ones.
    """
    a = [float(aloc(p, k)) for k in range(M + 1)]
    lam = np.zeros(M + 1)
    lam[0] = 1.0
    for m in range(1, M + 1):
        lam[m] = m * a[m] - sum(a[j] * lam[m - j] for j in range(1, m))
    return lam


# ---------------------------------------------------------------------------
# the statistic
# ---------------------------------------------------------------------------


def _depth(p: int, tol: float) -> int:
    return max(8, math.ceil(2 * math.log(1 / tol) / math.log(p)))


def threshold(
    aloc: Callable[[int, int], float],
    p: int,
    *,
    tol: float = DEFAULT_TOL,
    ngrid: int = 4001,
) -> tuple[float, float]:
    """``(c_p, tail_bound)`` at the place ``p``.

    ``c_p = − min_θ 2 Σ_{m≥1} λ_m p^{−m/2} cos(mθ)`` — the least diagonal for
    which the place-``p`` Toeplitz kernel is positive semidefinite. No
    normalization is chosen; compare it against the degree ``d``.

    The second entry bounds the truncation:
    ``2·max|λ|·p^{−(M+1)/2}/(1 − p^{−1/2})``. A verdict is only reported when
    the excess clears it by an order of magnitude (:func:`gate`).
    """
    M = _depth(p, tol)
    lam = local_lambdas(aloc, p, M)
    weights = lam[1:] * p ** (-np.arange(1, M + 1) / 2.0)
    theta = np.linspace(0.0, np.pi, ngrid)
    series = 2 * np.sum(weights[:, None] * np.cos(np.outer(np.arange(1, M + 1), theta)), axis=0)
    tail = 2 * float(np.max(np.abs(lam))) * p ** (-(M + 1) / 2.0) / (1 - p ** -0.5)
    return float(-series.min()), float(tail)


def kernel(
    aloc: Callable[[int, int], float],
    p: int,
    theta: float | np.ndarray,
    degree: int,
    *,
    tol: float = DEFAULT_TOL,
) -> np.ndarray:
    """``K_p^{(d)}(θ)`` itself, for plotting and for the closed-form check."""
    M = _depth(p, tol)
    lam = local_lambdas(aloc, p, M)
    th = np.atleast_1d(np.asarray(theta, dtype=float))
    weights = lam[1:] * p ** (-np.arange(1, M + 1) / 2.0)
    return degree + 2 * np.sum(weights[:, None] * np.cos(np.outer(np.arange(1, M + 1), th)), axis=0)


def satake_kernel(alphas: Sequence[complex], p: int, theta: float | np.ndarray) -> np.ndarray:
    """The closed form ``Σ_j (1 − |α_j|²/p)/|1 − α_j p^{−1/2}e^{iθ}|²``.

    This is what makes the gate a theorem rather than a statistic: it is
    nonnegative for all ``θ`` exactly when every ``|α_j| ≤ √p``.
    """
    th = np.atleast_1d(np.asarray(theta, dtype=float))
    out = np.zeros_like(th)
    for al in alphas:
        al = complex(al)
        out += (1 - abs(al) ** 2 / p) / np.abs(1 - al * p**-0.5 * np.exp(1j * th)) ** 2
    return out


def gate(
    aloc: Callable[[int, int], float],
    degree: int,
    *,
    primes: Iterable[int] = DEFAULT_PRIMES,
    tol: float = DEFAULT_TOL,
    margin: float = 10.0,
) -> dict:
    """Run the gate over the places. Returns verdict, witnesses, and margins.

    A place is a **witness** only when ``c_p > d + margin·tail`` — the
    truncation bound has to be cleared before a FAIL is spoken.
    """
    primes = list(primes)
    cs, tails = [], []
    for p in primes:
        c, t = threshold(aloc, p, tol=tol)
        cs.append(c)
        tails.append(t)
    cs_a, tails_a = np.array(cs), np.array(tails)
    witnesses = [
        (int(p), float(c))
        for p, c, t in zip(primes, cs_a, tails_a)
        if c > degree + margin * t
    ]
    return {
        "verdict": "PASS" if not witnesses else "FAIL",
        "degree": degree,
        "max_c": float(cs_a.max()),
        "excess": float(cs_a.max() - degree),
        "witnesses": witnesses,
        "c_by_prime": {int(p): float(c) for p, c in zip(primes, cs_a)},
        "max_tail": float(tails_a.max()),
    }


# ---------------------------------------------------------------------------
# controls — the reason this is a gate and not a decoration
# ---------------------------------------------------------------------------


def satake_check(alphas: Sequence[complex], p: int, theta: float = 1.1) -> dict:
    """Series vs. closed form at one point: the identity the gate rests on."""
    aloc = satake_local(alphas)
    return {
        "series": float(kernel(aloc, p, theta, len(alphas))[0]),
        "closed_form": float(satake_kernel(alphas, p, theta)[0]),
    }


def ramanujan_violator(alpha: float = 2.3, p: int = 5) -> dict:
    """A **genuine** Euler product the gate rejects — the honest boundary.

    ``α, 1/α`` with ``α`` large is a legitimate degree-2 Euler factor (real
    coefficients, functional equation intact) that violates the Ramanujan
    bound. The gate fails it at small ``p``. So the gate does *not* test
    "has an Euler product"; it tests the local Selberg bound ``|α_j| ≤ √p``,
    and a report that claimed the former would be overclaiming.
    """
    aloc = satake_local([alpha, 1 / alpha])
    c, tail = threshold(aloc, p)
    return {
        "alpha": alpha,
        "p": p,
        "c_p": c,
        "degree": 2,
        "verdict": "PASS" if c <= 2 + 10 * tail else "FAIL",
        "sqrt_p": math.sqrt(p),
        "note": "genuine Euler product; rejected because |alpha| > sqrt(p) is allowed in the Selberg class",
    }


def lesion_sweep(
    epsilons: Sequence[float] = (0.0, 0.01, 0.05, 0.1, 0.15, 0.2, 0.4, 0.7, 1.0),
    *,
    kappa: float | None = None,
    primes: Iterable[int] = (2, 3, 5, 7, 11, 13, 17, 19, 23),
) -> dict:
    """Plant a graded violation and find where the detector goes blind.

    Interpolates ζ → Davenport–Heilbronn coefficientwise. The returned
    ``eps_star`` is the smallest interpolation parameter the gate can see; a
    PASS means nothing below it. A detector whose blindness is unmeasured
    reports power it does not have (``harness/README.md``).
    """
    if kappa is None:  # the repo's own value; imported lazily to keep this module standalone
        from zeta import epstein

        kappa = float(epstein.kappa(dps=25))
    zeta_per = [0.0, 1.0, 1.0, 1.0, 1.0]
    dh_per = [0.0, 1.0, kappa, -kappa, -1.0]

    def blend(eps: float):
        return periodic_local([(1 - eps) * z + eps * d for z, d in zip(zeta_per, dh_per)])

    rows = []
    for eps in epsilons:
        res = gate(blend(eps), 1, primes=primes)
        rows.append({"eps": float(eps), "excess": res["excess"], "detected": res["verdict"] == "FAIL"})
    lo, hi = 0.0, 1.0
    for _ in range(40):
        mid = (lo + hi) / 2
        if gate(blend(mid), 1, primes=primes)["verdict"] == "FAIL":
            hi = mid
        else:
            lo = mid
    return {"rows": rows, "eps_star": float((lo + hi) / 2), "kappa": float(kappa)}


def null_distribution(
    n_samples: int = 400,
    seed: int = 20260810,
    *,
    primes: Iterable[int] = (2, 3, 5, 7, 11, 13, 17, 19, 23),
) -> dict:
    """What a *generic* non-factoring period-5 real sequence scores.

    A nonzero excess means nothing until the null is known. Reports the null
    band and Davenport–Heilbronn's percentile within it.
    """
    from zeta import epstein

    rng = np.random.default_rng(seed)
    scores = []
    for _ in range(n_samples):
        t = rng.normal(0, 1, 2)
        per = [0.0, 1.0, float(t[0]), float(t[1]), 0.0]
        scores.append(gate(periodic_local(per), 1, primes=primes)["excess"])
    scores_a = np.array(scores)
    kappa = float(epstein.kappa(dps=25))
    dh = gate(periodic_local([0.0, 1.0, kappa, -kappa, -1.0]), 1, primes=primes)["excess"]
    return {
        "median": float(np.median(scores_a)),
        "p05": float(np.percentile(scores_a, 5)),
        "p95": float(np.percentile(scores_a, 95)),
        "fraction_failing": float((scores_a > 0).mean()),
        "dh_excess": float(dh),
        "dh_percentile": float(100 * (scores_a < dh).mean()),
    }


# ---------------------------------------------------------------------------
# the two statements that keep this honest
# ---------------------------------------------------------------------------


def reference_table(primes: Iterable[int] = DEFAULT_PRIMES) -> list[dict]:
    """The department's reference claims, re-derived rather than remembered.

    Degrees are read off each object's own gamma factors — never chosen to make
    a verdict come out. Every row states the expected verdict; a row whose
    ``verdict`` and ``expected`` disagree is a failure of the gate, not of the
    subject, which is the calibration rule of ``harness/README.md``.
    """
    from zeta import epstein as _ep

    kappa = float(_ep.kappa(dps=25))
    cases = [
        ("zeta", periodic_local([1.0]), 1, "pi^{-s/2}Gamma(s/2)", "PASS"),
        ("L(chi quad mod 5)", periodic_local([0.0, 1.0, -1.0, -1.0, 1.0]), 1,
         "Gamma(s/2), even chi", "PASS"),
        ("degree-2 Euler factor (phi=0.9)",
         satake_local([complex(math.cos(0.9), math.sin(0.9)),
                       complex(math.cos(0.9), -math.sin(0.9))]), 2,
         "genuine degree-2 control", "PASS"),
        ("Davenport-Heilbronn", periodic_local([0.0, 1.0, kappa, -kappa, -1.0]), 1,
         "(pi/5)^{-(s+1)/2}Gamma((s+1)/2)", "FAIL"),
        ("DH-family t=0", periodic_local([0.0, 1.0, 0.0, 0.0, -1.0]), 1,
         "same gamma factor", "FAIL"),
        ("Epstein (1,1,6) principal", epstein_local(True), 2,
         "(2pi/sqrt23)^{-s}Gamma(s)", "FAIL"),
        ("Epstein (2,1,3) non-principal", epstein_local(False), 2,
         "(2pi/sqrt23)^{-s}Gamma(s)", "FAIL"),
    ]
    rows = []
    for name, aloc, degree, gamma, expected in cases:
        res = gate(aloc, degree, primes=primes)
        rows.append({
            "subject": name, "degree": degree, "gamma_factor": gamma,
            "max_c": res["max_c"], "excess": res["excess"],
            "verdict": res["verdict"], "expected": expected,
            "witnesses": res["witnesses"][:3],
            "agrees": res["verdict"] == expected,
        })
    return rows


def provenance_report() -> dict:
    """Requirement A, stated mechanically: what enters the definitions."""
    return {
        "inputs": "a_{p^k} only (local Dirichlet coefficients)",
        "zeros_used": False,
        "xi_phases_used": False,
        "zero_counting_used": False,
        "note": (
            "c_p is a functional of the coefficient sequence alone. By docs/18 §6 no such "
            "functional can read the position of the critical line: zeta(s-delta) has the same "
            "coefficients up to a shift and its zeros lie nowhere near Re s = 1/2."
        ),
    }


def scope() -> dict:
    """What a verdict from this module does and does not mean."""
    return {
        "is": (
            "an exact local criterion: c_p <= d at p is equivalent to the Selberg-class bound "
            "|alpha_j| <= sqrt(p) at p, and the place-p kernel is then a manifest norm."
        ),
        "is_not": [
            "evidence for RH (docs/08); nothing computed here could be",
            "a test for 'has an Euler product' — see ramanujan_violator()",
            "a global positivity statement: Q_p - ||f||^2 is not of definite sign, so the "
            "local norms do not assemble into a global one",
        ],
        "pass_means": (
            "no violation above the measured blindness threshold at the tested places; "
            "see lesion_sweep()['eps_star']"
        ),
        "requirement_C_status": (
            "achieved locally (Q_p = (1-1/p)||Phi_p f||^2, a norm at every place) and NOT "
            "globally — which is exactly where docs/09 §5.1 predicts an attempt bleeds"
        ),
    }
