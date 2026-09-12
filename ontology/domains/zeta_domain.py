"""ontology.domains.zeta_domain, the only module that knows what is studied.

Everything above this file in ``discovery/`` is domain-agnostic: it counts
candidates, verdicts and conversion rates and would work unchanged for a
chemistry lab. This file is where the laboratory is allowed to be named. It
registers seven **generators** (which mine the lab's own computed objects for
candidate observations), six **screens** (which try to kill them) and a
**catalogue** of already-established facts, all through
:mod:`ontology.registry`.

Honest scope, restated because this is the file where it would be easiest to
lose. Nothing here is evidence for the Riemann Hypothesis. A candidate that
survives every screen is a *lead*: a number that a finite computation failed to
kill, whose ``proof_gap`` field says in words what is missing before it could be
a theorem. The expected outcome, the one the funnel exists to measure, is
``known``, and the second most likely is ``trivial``.

What the generators mine
------------------------
========================  =====================================================
``zeta_constants``        measured numbers with honest error bars: the Li
                          coefficients, the Jensen/Taylor coefficients of Xi,
                          Xi(0), and spacing statistics of the zero ordinates
``zeta_asymptotics``      growth rates fitted in two or more windows spanning a
                          factor of four or more: lambda_n, N(T), the running
                          maximum of |M(x)|
``zeta_relations``        binary relations, including an integer-relation
                          (PSLQ) hunt for closed forms, with a significance
                          guard against the classic PSLQ false positive
``zeta_extremal``         record holders over explicitly bounded searches: the
                          tightest Weil margin, the smallest normalised zero
                          gap, the largest Mertens ratio, the most nearly
                          degenerate Jensen polynomial
``zeta_finite_field``     the universe where RH is a theorem: Hasse ratios and
                          Sato-Tate moments over curves mod p, so a "discovery"
                          is checkable against known truth
``zeta_structural``       universal claims over enumerated families, each with a
                          control the predicate *fails*, these are the ones the
                          counterexample battery must adjudicate
``zeta_legendre_weil``    the Riemann-Weil explicit formula localised to
                          Legendre intervals [n², (n+1)²]: the identity
                          instance, the prime-detection inequality, and (on
                          request, via ``legendre_mass_constant``) the
                          interval's Λ-mass as a measured constant
========================  =====================================================

The mandatory gate
------------------
``AGENTS.md`` makes the counterexample battery a standing test: any claimed
structural property that would "explain" RH must be run through
:func:`zeta.epstein.battery`, because a property the Davenport-Heilbronn
function also satisfies distinguishes nothing (docs/09 gate #3). The screen
:class:`CounterexampleBatteryScreen` is that gate, and it refuses to let a
structural claim past silently: either it adjudicates the claim through the
battery, or it records ``inconclusive`` with reason ``dependency_unavailable``
naming the missing analogue.

Re-derivation
-------------
Every candidate carries a ``route`` in its provenance parameters, naming an
entry of :data:`ROUTES`: a callable ``(parameters, dps) -> number`` that
recomputes the quantity from scratch. That is what makes the precision-stability
screen, the high-precision recomputation and the closed-form escalation possible
at all, and it is why "enough provenance for exact re-derivation" is a testable
property here rather than a promise.

Nothing is dropped without a trace
----------------------------------
A payload a generator builds and does not emit never enters the funnel, so it
appears in no conversion rate, the pipeline can only count what it is shown.
Every generator therefore inherits :class:`_RecordingGenerator` and keeps the
reasons in ``refused``, cleared at the start of each pass: schema refusals, ties
in an extremal search, integer-relation hunts that found nothing significant.
"""

from __future__ import annotations

import datetime as _dt
import json
import math
import random
import re
import time
from collections.abc import Callable, Iterator, Mapping, Sequence
from dataclasses import dataclass
from functools import lru_cache
from pathlib import Path
from typing import Any, Final

import numpy as np
from mpmath import mp

from ontology.knownness import (
    GENERAL_FACTS,
    FactMatch,
    KnownFact,
    KnownFactRegistry,
    screen_known,
)
from ontology.registry import (
    BaseGenerator,
    BaseKnownnessDetector,
    BaseScreen,
    Domain,
    ScreenResult,
    register_domain,
)
from ontology.schema import (
    Candidate,
    CandidateKind,
    InconclusiveReason,
    Precision,
    Verdict,
    VerdictStatus,
    capture_provenance,
    kind_reasons,
)

__all__ = [
    "DOMAIN_NAME",
    "DOMAIN_VERSION",
    "DEFAULT_DPS",
    "DEFAULT_SEED",
    "ROUTES",
    "Route",
    "ZETA_FACTS",
    "FACT_REGISTRY",
    "BATTERY_CLAIMS",
    "TRIVIALITY_RULES",
    "RANGE_RULES",
    "RANGE_TOLERANCE",
    "ConstantsGenerator",
    "AsymptoticsGenerator",
    "RelationsGenerator",
    "ExtremalGenerator",
    "FiniteFieldGenerator",
    "StructuralGenerator",
    "LegendreWeilGenerator",
    "NumericSanityScreen",
    "PrecisionStabilityScreen",
    "TrivialityScreen",
    "HighPrecisionScreen",
    "IndependentMethodScreen",
    "CounterexampleBatteryScreen",
    "CatalogueDetector",
    "DOMAIN",
    "build_domain",
]

DOMAIN_NAME: Final[str] = "zeta"
DOMAIN_VERSION: Final[str] = "1.0"

#: Working precision the generators harvest at. Screens escalate above it; the
#: schema will not let anything be called a survivor unless they did.
DEFAULT_DPS: Final[int] = 25

#: Everything here is deterministic given this seed. Only the finite-field
#: structural generator actually draws random numbers; it records the seed and
#: marks itself stochastic, and the rest record it for the sake of a uniform
#: replay recipe.
DEFAULT_SEED: Final[int] = 20260802

#: Guard digits between the working precision and the error bar a constant
#: candidate claims. Measured accuracy of the Cauchy route for lambda_n is
#: ~1e-(dps+3); claiming 1e-(dps-5) leaves eight digits of headroom, which is
#: what stops a candidate splitting from its own re-discovery.
UNCERTAINTY_GUARD: Final[int] = 5

#: Extra digits every comparison is carried out at. ``mpmath`` re-rounds to the
#: *ambient* precision, so subtracting two values that agree to 25 digits at the
#: default 15 gives exactly zero, a screen that runs at ambient precision
#: cannot fail, and a screen that cannot fail is a defect, not a reassurance.
GUARD_DIGITS: Final[int] = 25

_NUMERIC_RE: Final[re.Pattern[str]] = re.compile(
    r"^[+-]?(?:\d+\.?\d*|\.\d+)(?:[eE][+-]?\d+)?$"
)


def _utc_now() -> str:
    return _dt.datetime.now(_dt.UTC).replace(microsecond=0).isoformat()


# ---------------------------------------------------------------------------
# Number formatting: the schema wants JSON-shaped values, not mpf or numpy
# ---------------------------------------------------------------------------


def _num(value: Any, digits: int = 17) -> str:
    """A measured number as a decimal string the schema accepts.

    Decimal *text* rather than a float, so a high-precision measurement keeps
    its digits in the record while still hashing at the shared resolution. The
    result is validated against the schema's own numeric grammar rather than
    trusted.
    """
    with mp.workdps(max(int(digits) + 10, 20)):
        text = mp.nstr(mp.mpf(value), int(digits), strip_zeros=True)
    text = text.strip()
    if not _NUMERIC_RE.match(text):
        raise ValueError(f"{value!r} did not render as a decimal literal: {text!r}")
    return text


def _f(value: Any) -> float:
    """A plain Python float. ``numpy`` scalars must not reach the schema.

    ``numpy.float64`` passes ``isinstance(x, float)`` but ``repr`` renders it as
    ``np.float64(0.5)``, which the schema's decimal parser cannot read. Every
    number leaving this module goes through here or :func:`_num`.
    """
    out = float(value)
    if not math.isfinite(out):
        raise ValueError(f"non-finite number cannot be recorded: {value!r}")
    return out


def _i(value: Any) -> int:
    """A plain Python int (``numpy.int64`` is not an ``int``)."""
    return int(value)


def _dedup_digits(value: Any, uncertainty: Any, ceiling: int = 9) -> int:
    """Identity resolution the error bar actually supports.

    The schema refuses ``dedup_digits`` above the digits a constant's error
    bound determines, you may not hash digits you did not measure. This is the
    domain side of that contract.
    """
    with mp.workdps(60):
        val, unc = abs(mp.mpf(value)), abs(mp.mpf(uncertainty))
        if unc <= 0 or val == 0:
            return ceiling
        determined = int(mp.floor(mp.log10(val / unc)))
    return max(1, min(int(ceiling), determined))


def _loglog_exponent(xs: Sequence[float], ys: Sequence[float]) -> float:
    """Least-squares slope of ``log y`` against ``log x``, the fitted exponent."""
    lx = np.log(np.asarray(xs, dtype=float))
    ly = np.log(np.asarray(ys, dtype=float))
    design = np.vstack([lx, np.ones_like(lx)]).T
    solution, *_ = np.linalg.lstsq(design, ly, rcond=None)
    return _f(solution[0])


# ---------------------------------------------------------------------------
# Re-derivation routes: (parameters, dps) -> number
# ---------------------------------------------------------------------------


@dataclass(frozen=True, slots=True)
class Route:
    """How to recompute one recorded quantity from scratch.

    ``compute`` returns the *claimed* number: the value for a ``constant``, the
    defect for a ``relation``. ``escalates`` says whether raising ``dps`` buys
    real digits, a float64 statistic does not, and pretending otherwise would
    make the stability screen vacuous. ``cross_check`` is a second, genuinely
    independent route where the laboratory has one.
    """

    name: str
    lab_object: str
    compute: Callable[[Mapping[str, Any], int], Any]
    escalates: bool = True
    cross_check: Callable[[Mapping[str, Any], int], Any] | None = None
    cross_check_note: str = ""


# -- the underlying laboratory calls, memoised so a test run pays once ------


@lru_cache(maxsize=64)
def _lambda_table(n_max: int, dps: int) -> tuple[Any, ...]:
    from zeta.li import li_coefficients

    return tuple(li_coefficients(n_max, method="cauchy", dps=dps, radius="0.5"))


@lru_cache(maxsize=64)
def _gamma_table(n_max: int, dps: int, method: str) -> tuple[Any, ...]:
    from zeta.li import xi_taylor_coefficients

    return tuple(xi_taylor_coefficients(n_max, dps=dps, method=method))


@lru_cache(maxsize=32)
def _unfolded_spacings(n_zeros: int) -> np.ndarray:
    from zeta.statistics import nearest_neighbour_spacings, zero_ordinates

    return nearest_neighbour_spacings(zero_ordinates(n=n_zeros))


@lru_cache(maxsize=8)
def _weil_probe(n_points: int, dps: int) -> tuple[dict[str, Any], ...]:
    from zeta.weil import positivity_probe

    rows = positivity_probe(family="gaussian", n_points=n_points, dps=dps)
    return tuple(
        {
            "param": _f(row["param"]),
            "W": _f(row["W"]),
            "scale": _f(row["scale"]),
            "margin": _f(row["margin"]),
            # absolute, on W, *not* on the (dimensionless) margin
            "noise_floor": _f(row["noise_floor"]),
            "dps_used": _i(row["dps_used"]),
        }
        for row in rows
    )


@lru_cache(maxsize=8)
def _mertens_running_max(limit: int) -> np.ndarray:
    from zeta.criteria import mertens_array

    return np.maximum.accumulate(np.abs(mertens_array(limit)))


@lru_cache(maxsize=8)
def _mertens_ratios(limit: int) -> np.ndarray:
    from zeta.criteria import mertens_array

    x = np.arange(limit + 1, dtype=float)
    x[0] = 1.0
    return mertens_array(limit).astype(float) / np.sqrt(x)


@lru_cache(maxsize=32)
def _sato_tate(p: int) -> Mapping[str, Any]:
    from zeta.finitefield import sato_tate_histogram

    return sato_tate_histogram(p)


@lru_cache(maxsize=16)
def _level_repulsion(n_zeros: int) -> Mapping[str, Any]:
    from zeta.statistics import level_repulsion_report, zero_ordinates

    return level_repulsion_report(zero_ordinates(n=n_zeros))


@lru_cache(maxsize=16)
def _jensen_min_gaps(d_max: int, n_max: int, dps: int) -> tuple[tuple[int, int, float], ...]:
    """``(d, n, min_gap)`` for every Jensen polynomial of degree >= 2 on the grid."""
    from zeta.li import is_hyperbolic, jensen_polynomial

    out: list[tuple[int, int, float]] = []
    for d in range(2, d_max + 1):
        for n in range(0, n_max + 1):
            report = is_hyperbolic(
                jensen_polynomial(d, n, dps=dps), dps=dps, method="roots"
            )
            gap = report["min_gap"]
            if gap is not None and math.isfinite(float(gap)):
                out.append((d, n, _f(gap)))
    return tuple(out)


# -- the routes themselves --------------------------------------------------


def _route_li_lambda(params: Mapping[str, Any], dps: int) -> Any:
    n = int(params["n"])
    return _lambda_table(n, dps)[n - 1]


@lru_cache(maxsize=64)
def _li_generating_defect(n: int, dps: int) -> Any:
    from zeta.li import li_generating_function_defect

    return li_generating_function_defect(n, dps=dps)


def _route_li_lambda_cross(params: Mapping[str, Any], dps: int) -> Any:
    """lambda_n by the literal n-th-derivative definition.

    ``li_generating_function_defect`` is (Cauchy route) - (literal definition),
    so subtracting it from the Cauchy value returns the other route's answer.
    The two share nothing but xi itself.
    """
    n = int(params["n"])
    with mp.workdps(dps + GUARD_DIGITS):
        return _lambda_table(n, dps)[n - 1] - _li_generating_defect(n, dps)


def _route_xi_gamma(params: Mapping[str, Any], dps: int) -> Any:
    n = int(params["n"])
    return _gamma_table(max(n, 1), dps, "integral")[n]


def _route_xi_gamma_cross(params: Mapping[str, Any], dps: int) -> Any:
    n = int(params["n"])
    return _gamma_table(max(n, 1), dps, "cauchy")[n]


def _route_Xi_at(params: Mapping[str, Any], dps: int) -> Any:
    from zeta.core import Xi

    return Xi(mp.mpf(str(params["t"])), dps=dps)


def _route_Xi_at_cross(params: Mapping[str, Any], dps: int) -> Any:
    from zeta.heatflow import Xi_reference

    with mp.workdps(dps):
        return Xi_reference(mp.mpf(str(params["t"])))


def _route_spacing_variance(params: Mapping[str, Any], dps: int) -> Any:
    return mp.mpf(_f(_unfolded_spacings(int(params["n_zeros"])).var(ddof=1)))


def _route_mean_spacing(params: Mapping[str, Any], dps: int) -> Any:
    return mp.mpf(_f(_unfolded_spacings(int(params["n_zeros"])).mean()))


def _route_defect_lambda1_closed_form(params: Mapping[str, Any], dps: int) -> Any:
    from zeta.li import li_closed_form_lambda1

    # Two rules, both load-bearing. The subtraction happens at a precision that
    # can *see* the difference, at the ambient 15 digits two values agreeing to
    # 25 differ by exactly zero, and a defect that cannot be nonzero is not a
    # measurement. And the reference side is evaluated with guard digits, so the
    # recorded defect is the error of the route under test rather than the
    # rounding both sides happen to share.
    with mp.workdps(dps + GUARD_DIGITS):
        return abs(
            _lambda_table(1, dps)[0] - li_closed_form_lambda1(dps=dps + GUARD_DIGITS)
        )


def _route_defect_gamma0_vs_Xi0(params: Mapping[str, Any], dps: int) -> Any:
    from zeta.core import Xi

    with mp.workdps(dps + GUARD_DIGITS):
        return abs(
            _gamma_table(1, dps, "integral")[0]
            - 8 * Xi(mp.mpf(0), dps=dps + GUARD_DIGITS)
        )


def _lambda1_pslq_closed_form(dps: int) -> Any:
    """(2 + gamma - 2 log 2 - log pi) / 2, the expression PSLQ returns."""
    with mp.workdps(dps + 10):
        return (2 + mp.euler - 2 * mp.log(2) - mp.log(mp.pi)) / 2


def _route_defect_lambda1_pslq(params: Mapping[str, Any], dps: int) -> Any:
    with mp.workdps(dps + GUARD_DIGITS):
        return abs(_lambda_table(1, dps)[0] - _lambda1_pslq_closed_form(dps))


def _route_defect_gue_beats_poisson(params: Mapping[str, Any], dps: int) -> Any:
    report = _level_repulsion(int(params["n_zeros"]))
    gue = _f(report["ks_gue_exact"]["statistic"])
    poisson = _f(report["ks_poisson"]["statistic"])
    return mp.mpf(max(0.0, gue - poisson))


def _route_defect_ff_second_moment(params: Mapping[str, Any], dps: int) -> Any:
    hist = _sato_tate(int(params["p"]))
    return mp.mpf(abs(_i(hist["second_moment_exact"]) - _i(hist["second_moment_closed_form"])))


def _route_defect_ff_trace_surjectivity(params: Mapping[str, Any], dps: int) -> Any:
    hist = _sato_tate(int(params["p"]))
    return mp.mpf(abs(_i(hist["distinct_traces"]) - _i(hist["hasse_interval_size"])))


#: Where evaluated explicit-formula sides persist between processes. The
#: archimedean quadrature at escalated precision costs ~15 s per interval, and
#: every funnel-running test in every xdist worker would otherwise pay it
#: again; this is the repo's standard data/ cache pattern. **If zeta/weil.py's
#: numerical internals change, delete this file**, stale sides would let the
#: screens "pass" against numbers the code no longer produces.
_LEGENDRE_SIDES_CACHE: Final[Path] = (
    Path(__file__).resolve().parents[2] / "data" / "legendre_weil_sides.json"
)

_LEGENDRE_SIDES_INTS: Final[tuple[str, ...]] = ("n_zeros_used", "n_max")


def _legendre_sides_from_disk(key: str) -> Mapping[str, Any] | None:
    try:
        table = json.loads(_LEGENDRE_SIDES_CACHE.read_text())
        return table.get(key)
    except (OSError, ValueError):
        return None


def _legendre_sides_to_disk(key: str, sides: Mapping[str, Any], dps: int) -> None:
    """Append one entry, atomically; a lost race costs a recompute, never data."""
    row: dict[str, Any] = {}
    with mp.workdps(dps + 15):
        for name, value in sides.items():
            if value is None or isinstance(value, (int, str)):
                row[name] = value
            else:
                row[name] = mp.nstr(mp.mpf(value), dps + 15, strip_zeros=False)
    try:
        table = json.loads(_LEGENDRE_SIDES_CACHE.read_text())
    except (OSError, ValueError):
        table = {}
    table[key] = row
    tmp = _LEGENDRE_SIDES_CACHE.with_suffix(".json.tmp")
    tmp.write_text(json.dumps(table, indent=1, sort_keys=True))
    tmp.replace(_LEGENDRE_SIDES_CACHE)


@lru_cache(maxsize=64)
def _legendre_sides(n: int, gamma_max: float, dps: int) -> Mapping[str, Any]:
    """One evaluation of the explicit formula on the n-th Legendre bump.

    Memoised twice: per process (one evaluation feeds three candidates and
    every screen escalation) and on disk (decimal strings at dps+15, which
    every consumer parses back at its own working precision). The cache key
    carries the dps, so an escalated recompute is a genuine recompute, paid
    once ever rather than once per process.
    """
    key = f"n={int(n)}|gamma_max={float(gamma_max)!r}|dps={int(dps)}"
    cached = _legendre_sides_from_disk(key)
    if cached is not None:
        return cached

    from zeta.weil import explicit_formula_sides, legendre_pair

    h, g = legendre_pair(n)
    sides = explicit_formula_sides(
        h, g, gamma_max=gamma_max, n_max=(n + 1) ** 2 + 1, dps=dps
    )
    _legendre_sides_to_disk(key, sides, dps)
    return sides


def _route_legendre_weil_defect(params: Mapping[str, Any], dps: int) -> Any:
    sides = _legendre_sides(int(params["n"]), float(params["gamma_max"]), dps)
    return sides["abs_diff"]


def _route_legendre_lambda_mass(params: Mapping[str, Any], dps: int) -> Any:
    """The Λ-mass of the Legendre interval: prime_term = -2 Σ Λ(k) k^{-1/2} g(log k)."""
    sides = _legendre_sides(int(params["n"]), float(params["gamma_max"]), dps)
    with mp.workdps(dps + GUARD_DIGITS):
        return -mp.mpf(sides["prime_term"]) / 2


def _route_legendre_lambda_mass_cross(params: Mapping[str, Any], dps: int) -> Any:
    """The same Λ-mass by direct re-summation over the interval.

    Shares only the definitions of Λ and g with the route under test: prime
    powers come from sympy's factorisation, not from zeta.weil's prime loop.
    """
    from sympy import factorint

    from zeta.weil import legendre_pair

    n = int(params["n"])
    _, g = legendre_pair(n)
    with mp.workdps(dps + GUARD_DIGITS):
        total = mp.mpf(0)
        for k in range(n * n + 1, (n + 1) ** 2):
            factors = factorint(k)
            if len(factors) == 1:
                (p,) = factors
                total += mp.log(p) * g(mp.log(k)) / mp.sqrt(k)
        return total


def _route_legendre_detection_defect(params: Mapping[str, Any], dps: int) -> Any:
    """max(0, -mass): zero exactly when the formula detects the interval's primes."""
    with mp.workdps(dps + GUARD_DIGITS):
        mass = mp.mpf(_route_legendre_lambda_mass(params, dps))
        return max(mp.mpf(0), -mass)


ROUTES: Final[Mapping[str, Route]] = {
    "li_lambda": Route(
        name="li_lambda",
        lab_object="zeta.li.li_coefficients",
        compute=_route_li_lambda,
        cross_check=_route_li_lambda_cross,
        cross_check_note=(
            "the literal n-th-derivative definition, via "
            "zeta.li.li_generating_function_defect"
        ),
    ),
    "xi_gamma": Route(
        name="xi_gamma",
        lab_object="zeta.li.xi_taylor_coefficients",
        compute=_route_xi_gamma,
        cross_check=_route_xi_gamma_cross,
        cross_check_note="the Cauchy route of the same coefficients (method='cauchy')",
    ),
    "Xi_at": Route(
        name="Xi_at",
        lab_object="zeta.core.Xi",
        compute=_route_Xi_at,
        cross_check=_route_Xi_at_cross,
        cross_check_note="zeta.heatflow.Xi_reference, the sibling implementation",
    ),
    "spacing_variance": Route(
        name="spacing_variance",
        lab_object="zeta.statistics.nearest_neighbour_spacings",
        compute=_route_spacing_variance,
        escalates=False,
    ),
    "mean_spacing": Route(
        name="mean_spacing",
        lab_object="zeta.statistics.unfold",
        compute=_route_mean_spacing,
        escalates=False,
    ),
    "defect_lambda1_closed_form": Route(
        name="defect_lambda1_closed_form",
        lab_object="zeta.li.li_closed_form_lambda1",
        compute=_route_defect_lambda1_closed_form,
    ),
    "defect_gamma0_vs_Xi0": Route(
        name="defect_gamma0_vs_Xi0",
        lab_object="zeta.li.xi_taylor_coefficients",
        compute=_route_defect_gamma0_vs_Xi0,
    ),
    "defect_lambda1_pslq": Route(
        name="defect_lambda1_pslq",
        lab_object="zeta.li.li_coefficients",
        compute=_route_defect_lambda1_pslq,
    ),
    "defect_gue_beats_poisson": Route(
        name="defect_gue_beats_poisson",
        lab_object="zeta.statistics.level_repulsion_report",
        compute=_route_defect_gue_beats_poisson,
        escalates=False,
    ),
    "defect_ff_second_moment": Route(
        name="defect_ff_second_moment",
        lab_object="zeta.finitefield.sato_tate_histogram",
        compute=_route_defect_ff_second_moment,
        escalates=False,
    ),
    "defect_ff_trace_surjectivity": Route(
        name="defect_ff_trace_surjectivity",
        lab_object="zeta.finitefield.sato_tate_histogram",
        compute=_route_defect_ff_trace_surjectivity,
        escalates=False,
    ),
    "legendre_weil_defect": Route(
        name="legendre_weil_defect",
        lab_object="zeta.weil.explicit_formula_sides",
        compute=_route_legendre_weil_defect,
    ),
    "legendre_lambda_mass": Route(
        name="legendre_lambda_mass",
        lab_object="zeta.weil.legendre_pair",
        compute=_route_legendre_lambda_mass,
        cross_check=_route_legendre_lambda_mass_cross,
        cross_check_note=(
            "direct re-summation over the interval via sympy's factorisation, "
            "sharing only the definitions of Lambda and g"
        ),
    ),
    "legendre_detection_defect": Route(
        name="legendre_detection_defect",
        lab_object="zeta.weil.explicit_formula_sides",
        compute=_route_legendre_detection_defect,
    ),
}


def _route_of(candidate: Candidate) -> Route | None:
    name = candidate.provenance.parameters.get("route")
    return ROUTES.get(str(name)) if name else None


def _route_params(candidate: Candidate) -> dict[str, Any]:
    return {
        k: v for k, v in candidate.provenance.parameters.items() if k != "route"
    }


def _claimed_number(candidate: Candidate) -> Any | None:
    """The number a route is supposed to reproduce, as an ``mpf``."""
    if candidate.kind is CandidateKind.CONSTANT:
        return mp.mpf(str(candidate.claim["value"]))
    if candidate.kind is CandidateKind.RELATION:
        return mp.mpf(str(candidate.evidence["defect"]))
    return None


def _claim_tolerance(candidate: Candidate) -> Any | None:
    """How far the recomputation may move before it is a problem."""
    if candidate.kind is CandidateKind.CONSTANT:
        return mp.mpf(str(candidate.evidence["uncertainty"]))
    if candidate.kind is CandidateKind.RELATION:
        return mp.mpf(str(candidate.evidence["tolerance"]))
    return None


# ---------------------------------------------------------------------------
# Provenance
# ---------------------------------------------------------------------------


def _provenance(
    *,
    generator: str,
    version: str,
    route: str | None,
    lab_object: str,
    parameters: Mapping[str, Any],
    precision: Precision,
    seed: int,
    stochastic: bool = False,
    duration_s: float | None = None,
):
    import mpmath
    import numpy

    params = dict(parameters)
    if route is not None:
        params["route"] = route
    return capture_provenance(
        generator=generator,
        generator_version=version,
        lab_object=lab_object,
        parameters=params,
        precision=precision,
        seed=seed,
        stochastic=stochastic,
        duration_s=duration_s,
        runtime={"mpmath": mpmath.__version__, "numpy": numpy.__version__},
    )


# ---------------------------------------------------------------------------
# The generator base: nothing is dropped without a trace
# ---------------------------------------------------------------------------


class _RecordingGenerator(BaseGenerator):
    """A generator that keeps every payload it built and did not emit.

    The rule, which :class:`AsymptoticsGenerator` states and which used to hold
    for that generator alone: **a generator that drops its failures silently
    has a wrong denominator.** A payload the schema refuses, or one killed by an
    internal guard (a tie in an extremal search, a search space with fewer than
    two members), is real work that produced no candidate, and the funnel cannot
    see it, a candidate that was never yielded never enters the pipeline, so it
    appears in no conversion rate at all.

    Every such drop is appended to :attr:`refused` with its reason, and the list
    is cleared at the start of every :meth:`generate`, so it always describes
    the pass that just ran.
    """

    def __init__(self) -> None:
        #: ``"<label>: <reason>; <reason>"`` for every payload built and not
        #: emitted during the most recent :meth:`generate`.
        self.refused: list[str] = []

    def _refuse(self, label: str, reasons: Sequence[str]) -> None:
        """Record one payload that was built and not emitted, and why."""
        self.refused.append(f"{label}: " + "; ".join(str(r) for r in reasons))


# ---------------------------------------------------------------------------
# Generator 1, constants
# ---------------------------------------------------------------------------


class ConstantsGenerator(_RecordingGenerator):
    """Harvest computed constants as closed-form candidates.

    Every number is emitted with an error bar the laboratory can defend: the
    high-precision routes claim ``1e-(dps-5)`` against a measured accuracy of
    ``1e-(dps+3)``, and the float64 statistics claim their own standard error.

    Nothing is pre-filtered here. A quantity indistinguishable from zero is not
    a constant candidate, the schema is right that a vanishing measurement is a
    relation, but the honest place for that refusal is the funnel, which counts
    the payload ``invalid`` *against this generator*. Silently declining to emit
    it would hide a generator defect instead of measuring it.
    """

    name = "zeta_constants"
    version = "1.0"

    def generate(self, context: Mapping[str, Any]) -> Iterator[Candidate]:
        self.refused = []
        dps = int(context.get("dps", DEFAULT_DPS))
        seed = int(context.get("seed", DEFAULT_SEED))
        n_lambda = int(context.get("n_lambda", 3))
        n_zeros = int(context.get("n_zeros", 2000))
        unc_text = _num(mp.mpf(10) ** -(dps - UNCERTAINTY_GUARD), 3)
        precision = Precision(kind="dps", value=dps, backend="mpmath")

        for n in range(1, n_lambda + 1):
            started = time.perf_counter()
            value = _lambda_table(n, dps)[n - 1]
            yield self._constant(
                subject=f"zeta.li.lambda_{n}",
                value=value,
                uncertainty=unc_text,
                dps=dps,
                route="li_lambda",
                parameters={"n": n, "method": "cauchy", "radius": "0.5", "dps": dps},
                lab_object=ROUTES["li_lambda"].lab_object,
                precision=precision,
                seed=seed,
                duration_s=time.perf_counter() - started,
                label=f"Li coefficient lambda_{n}",
            )

        started = time.perf_counter()
        gamma0 = _gamma_table(1, dps, "integral")[0]
        yield self._constant(
            subject="zeta.li.xi_taylor_gamma_0",
            value=gamma0,
            uncertainty=unc_text,
            dps=dps,
            route="xi_gamma",
            parameters={"n": 0, "method": "integral", "dps": dps},
            lab_object=ROUTES["xi_gamma"].lab_object,
            precision=precision,
            seed=seed,
            duration_s=time.perf_counter() - started,
            label="Jensen/Taylor coefficient gamma(0) of 8 xi(1/2+z)",
        )

        # Xi is sampled at a configurable set of points. The default is the one
        # point with a catalogued value; asking for more is how an operator
        # deliberately generates observations the catalogue does not cover.
        for point in tuple(str(t) for t in context.get("xi_points", ("0",))):
            started = time.perf_counter()
            value = _route_Xi_at({"t": point}, dps)
            yield self._constant(
                subject=f"zeta.core.Xi_at_{point.replace('-', 'minus_')}",
                value=value,
                uncertainty=unc_text,
                dps=dps,
                route="Xi_at",
                parameters={"t": point, "dps": dps},
                lab_object=ROUTES["Xi_at"].lab_object,
                precision=precision,
                seed=seed,
                duration_s=time.perf_counter() - started,
                label=f"Xi({point})",
            )

        # -- float64 statistics: honest standard errors, honest precision kind
        started = time.perf_counter()
        spacings = _unfolded_spacings(n_zeros)
        n = int(spacings.size)
        variance = _f(spacings.var(ddof=1))
        fourth = _f(((spacings - spacings.mean()) ** 4).mean())
        se_var = math.sqrt(max(fourth - variance**2, 0.0) / n)
        yield self._constant(
            subject="zeta.statistics.unfolded_spacing_variance",
            value=variance,
            uncertainty=_num(se_var, 4),
            dps=None,
            route="spacing_variance",
            parameters={"n_zeros": n_zeros, "n_spacings": n},
            lab_object=ROUTES["spacing_variance"].lab_object,
            precision=Precision(kind="float64", backend="numpy"),
            seed=seed,
            duration_s=time.perf_counter() - started,
            label="variance of the unfolded nearest-neighbour spacings",
        )

        started = time.perf_counter()
        mean = _f(spacings.mean())
        se_mean = math.sqrt(variance / n)
        yield self._constant(
            subject="zeta.statistics.mean_unfolded_spacing",
            value=mean,
            uncertainty=_num(se_mean, 4),
            dps=None,
            route="mean_spacing",
            parameters={"n_zeros": n_zeros, "n_spacings": n},
            lab_object=ROUTES["mean_spacing"].lab_object,
            precision=Precision(kind="float64", backend="numpy"),
            seed=seed,
            duration_s=time.perf_counter() - started,
            label="mean of the unfolded nearest-neighbour spacings",
        )

    # -- helper ------------------------------------------------------------
    def _constant(
        self,
        *,
        subject: str,
        value: Any,
        uncertainty: str,
        dps: int | None,
        route: str,
        parameters: Mapping[str, Any],
        lab_object: str,
        precision: Precision,
        seed: int,
        duration_s: float,
        label: str,
    ) -> Candidate:
        digits = 17 if dps is None else dps
        claim = {"subject": subject, "value": _num(value, digits)}
        evidence = {
            "uncertainty": uncertainty,
            "working_precision": "float64" if dps is None else f"dps={dps}",
        }
        return Candidate(
            kind=CandidateKind.CONSTANT,
            claim=claim,
            evidence=evidence,
            provenance=_provenance(
                generator=self.name,
                version=self.version,
                route=route,
                lab_object=lab_object,
                parameters=parameters,
                precision=precision,
                seed=seed,
                duration_s=duration_s,
            ),
            dedup_digits=_dedup_digits(claim["value"], uncertainty),
            label=label,
        )


# ---------------------------------------------------------------------------
# Generator 2, asymptotics
# ---------------------------------------------------------------------------

#: Sample grids are module constants so that a fit is reproducible to the point,
#: not merely to the method.
MERTENS_GRID: Final[tuple[int, ...]] = (
    1000, 2000, 5000, 10000, 20000, 50000, 100000, 200000, 500000, 1000000,
)
ZERO_HEIGHT_GRID: Final[tuple[float, ...]] = (
    200.0, 400.0, 800.0, 1600.0, 3200.0, 6400.0, 12800.0, 25600.0,
)
#: Height of the Riemann-Siegel scan the counting fit reads. Chosen to match a
#: committed cache key: an off-by-a-little height silently re-runs an hour of
#: arithmetic (``AGENTS.md``, cached data).
ZERO_SCAN_HEIGHT: Final[float] = 30000.0


class AsymptoticsGenerator(_RecordingGenerator):
    """Fit growth rates of computed sequences in two or more windows.

    The schema refuses a rate fitted over a range that never quadruples, which
    is the single commonest way a numerical search fools itself, and it refuses
    windows whose fitted exponents disagree. Both refusals are load-bearing
    here: this generator proposes only the fits that survive them, and reports
    the rest as examined-and-refused rather than quietly dropping them.
    """

    name = "zeta_asymptotics"
    version = "1.1"

    def generate(self, context: Mapping[str, Any]) -> Iterator[Candidate]:
        dps = int(context.get("dps", DEFAULT_DPS))
        seed = int(context.get("seed", DEFAULT_SEED))
        self.refused = []
        yield from self._lambda_growth(dps, seed, context)
        yield from self._zero_counting(seed)
        yield from self._mertens_growth(seed)

    # -- lambda_n ~ (n/2)(log n - log 2pi + gamma - 1) + 1 ------------------
    def _lambda_growth(
        self, dps: int, seed: int, context: Mapping[str, Any]
    ) -> Iterator[Candidate]:
        from zeta.li import li_asymptotic

        n_max = int(context.get("lambda_n_max", 300))
        bounds = tuple(context.get("lambda_windows", ((20, 80), (80, n_max))))
        started = time.perf_counter()
        table = _lambda_table(n_max, dps)
        ns = np.arange(1, n_max + 1)
        values = np.array([_f(x) for x in table])
        scale = np.array([li_asymptotic(int(n)) for n in ns], dtype=float)
        windows = []
        for lo, hi in bounds:
            mask = (ns >= lo) & (ns <= hi) & (values > 0) & (scale > 0)
            windows.append(
                {
                    "index_min": int(lo),
                    "index_max": int(hi),
                    "exponent": _f(_loglog_exponent(scale[mask], values[mask])),
                    "n_points": int(mask.sum()),
                }
            )
        yield from self._emit(
            claim={
                "subject": "zeta.li.lambda_n",
                "index": "n",
                "limit": "+inf",
                "scale": "zeta.li.li_asymptotic",
                "exponent": 1.0,
            },
            evidence={
                "windows": windows,
                "tolerance": 0.02,
                "fit": "least squares on log(lambda_n) against log(li_asymptotic(n))",
                "note": (
                    "the RH-predicted scale is used as the reference function; the "
                    "fit measures agreement with it and is not evidence for RH"
                ),
            },
            route=None,
            lab_object="zeta.li.li_coefficients",
            parameters={"n_max": n_max, "dps": dps, "windows": "20-80, 80-n_max"},
            precision=Precision(kind="dps", value=dps, backend="mpmath"),
            seed=seed,
            duration_s=time.perf_counter() - started,
            label="lambda_n against its RH-predicted scale",
        )

    # -- N(T) against the Riemann-von Mangoldt main term --------------------
    def _zero_counting(self, seed: int) -> Iterator[Candidate]:
        from zeta.statistics import zero_ordinates
        from zeta.zeros import riemann_von_mangoldt

        started = time.perf_counter()
        gammas = zero_ordinates(t_max=ZERO_SCAN_HEIGHT)
        heights = np.array(ZERO_HEIGHT_GRID, dtype=float)
        counts = np.array(
            [float(np.searchsorted(gammas, T)) for T in heights], dtype=float
        )
        main = np.array([_f(riemann_von_mangoldt(float(T))) for T in heights])
        windows = []
        for lo, hi in ((200.0, 1600.0), (1600.0, 25600.0)):
            mask = (heights >= lo) & (heights <= hi)
            windows.append(
                {
                    "index_min": _f(lo),
                    "index_max": _f(hi),
                    "exponent": _f(_loglog_exponent(main[mask], counts[mask])),
                    "n_points": int(mask.sum()),
                }
            )
        yield from self._emit(
            claim={
                "subject": "zeta.zeros.N_of_T",
                "index": "T",
                "limit": "+inf",
                "scale": "zeta.zeros.riemann_von_mangoldt",
                "exponent": 1.0,
            },
            evidence={
                "windows": windows,
                "tolerance": 0.005,
                "fit": "least squares on log N(T) against log of the main term",
                "counts": [int(c) for c in counts],
            },
            route=None,
            lab_object="zeta.statistics.zero_ordinates",
            parameters={"t_max": _f(ZERO_HEIGHT_GRID[-1] * 1.2), "grid": "octaves 200..25600"},
            precision=Precision(kind="float64", backend="numpy"),
            seed=seed,
            duration_s=time.perf_counter() - started,
            label="the zero-counting staircase against Riemann-von Mangoldt",
        )

    # -- running maximum of |M(x)| -----------------------------------------
    def _mertens_growth(self, seed: int) -> Iterator[Candidate]:
        started = time.perf_counter()
        limit = int(MERTENS_GRID[-1])
        running = _mertens_running_max(limit)
        xs = np.array(MERTENS_GRID, dtype=float)
        ys = np.array([float(running[int(x)]) for x in MERTENS_GRID], dtype=float)
        windows = []
        for lo, hi in ((1000.0, 10000.0), (10000.0, 1000000.0)):
            mask = (xs >= lo) & (xs <= hi)
            windows.append(
                {
                    "index_min": _f(lo),
                    "index_max": _f(hi),
                    "exponent": _f(_loglog_exponent(xs[mask], ys[mask])),
                    "n_points": int(mask.sum()),
                }
            )
        yield from self._emit(
            claim={
                "subject": "zeta.criteria.running_max_abs_mertens",
                "index": "x",
                "limit": "+inf",
                "scale": "x",
                "exponent": 0.5,
            },
            evidence={
                "windows": windows,
                "tolerance": 0.06,
                "fit": "least squares on log(max_{y<=x}|M(y)|) against log x",
                "note": (
                    "an exponent near 1/2 over a finite range says nothing about "
                    "the true order: the Mertens conjecture is false and its "
                    "disproof is non-constructive (Odlyzko-te Riele 1985)"
                ),
                "values": [int(v) for v in ys],
                "note_precision": (
                    "the sampled maxima are exact integers; the fitted exponents "
                    "are a float64 least-squares solve, which is what the "
                    "recorded precision refers to"
                ),
            },
            route=None,
            lab_object="zeta.criteria.mertens_array",
            parameters={"limit": limit, "grid": "1e3..1e6 in 1-2-5 steps"},
            # The M(x) values are exact, but the *claim* is a log-log slope
            # computed by numpy's least squares in float64. Calling it exact
            # would report an infinite effort for a float64 fit.
            precision=Precision(kind="float64", backend="numpy"),
            seed=seed,
            duration_s=time.perf_counter() - started,
            label="growth of the running maximum of |M(x)|",
        )

    # -- helper ------------------------------------------------------------
    def _emit(
        self,
        *,
        claim: Mapping[str, Any],
        evidence: Mapping[str, Any],
        route: str | None,
        lab_object: str,
        parameters: Mapping[str, Any],
        precision: Precision,
        seed: int,
        duration_s: float,
        label: str,
    ) -> Iterator[Candidate]:
        refusals = kind_reasons(CandidateKind.ASYMPTOTIC, claim, evidence)
        if refusals:
            self._refuse(label, refusals)
            return
        yield Candidate(
            kind=CandidateKind.ASYMPTOTIC,
            claim=dict(claim),
            evidence=dict(evidence),
            provenance=_provenance(
                generator=self.name,
                version=self.version,
                route=route,
                lab_object=lab_object,
                parameters=parameters,
                precision=precision,
                seed=seed,
                duration_s=duration_s,
            ),
            label=label,
        )


# ---------------------------------------------------------------------------
# Generator 3, relations, including an integer-relation hunt
# ---------------------------------------------------------------------------

#: The basis the PSLQ hunt searches over, as ``(name, value factory)``.
PSLQ_BASIS: Final[tuple[tuple[str, Callable[[], Any]], ...]] = (
    ("1", lambda: mp.mpf(1)),
    ("euler_gamma", lambda: mp.euler),
    ("log(2)", lambda: mp.log(2)),
    ("log(pi)", lambda: mp.log(mp.pi)),
)


def pslq_relation(
    value: Any, *, dps: int, maxcoeff: int = 10**4, min_surplus_digits: float = 8.0
) -> tuple[tuple[int, ...] | None, str]:
    """Search for integers ``c`` with ``c0*value + sum(ci*bi) = 0``.

    Returns ``(coefficients, note)``; ``coefficients is None`` means *nothing
    significant was found*, which is the honest and common answer.

    **The significance guard.** With ``k`` basis terms and coefficients bounded
    by ``H``, an integer relation appears by accident once the precision falls
    below about ``k*log10(H)`` digits, so a "relation" found at 12 digits with
    coefficients in the hundreds is arithmetic, not mathematics. A relation is
    reported only when the digits actually available exceed that threshold by
    ``min_surplus_digits``.
    """
    with mp.workdps(dps + 10):
        basis = [mp.mpf(value)] + [factory() for _, factory in PSLQ_BASIS]
        found = mp.pslq(
            basis,
            tol=mp.mpf(10) ** -(dps - 5),
            maxcoeff=maxcoeff,
            maxsteps=20000,
        )
        if not found:
            return None, f"no integer relation at {dps} digits (maxcoeff={maxcoeff})"
        if found[0] == 0:
            return None, "the relation does not involve the measured quantity"
        largest = max(abs(int(c)) for c in found)
        needed = len(found) * math.log10(max(largest, 2)) + min_surplus_digits
        if dps < needed:
            return None, (
                f"a relation with coefficients up to {largest} needs about "
                f"{needed:.0f} digits to be significant; only {dps} were available"
            )
        residual = sum(mp.mpf(int(c)) * b for c, b in zip(found, basis))
        return tuple(int(c) for c in found), (
            f"coefficients {tuple(int(c) for c in found)}, residual "
            f"{mp.nstr(abs(residual), 3)}, significant at {dps} digits "
            f"(threshold {needed:.0f})"
        )


class RelationsGenerator(_RecordingGenerator):
    """Look for simple relations between pairs of computed quantities.

    Two sources. First, defects the laboratory already exposes as measured
    quantities (two routes to lambda_1, the Jensen normalisation against Xi(0)).
    Second, an integer-relation hunt with :func:`mpmath.pslq` over a small basis
    of standard constants, guarded against the false positive that PSLQ produces
    by construction when it is given more coefficients than digits.
    """

    name = "zeta_relations"
    version = "1.0"

    def __init__(self) -> None:
        super().__init__()
        #: ``(subject, coefficients, note)`` for every quantity the integer
        #: relation hunt looked at, including the ones where it found nothing.
        #: Initialised here, not in ``generate``, so a consumer that reads it
        #: before the first pass gets an empty list rather than an
        #: ``AttributeError``.
        self.pslq_notes: list[tuple[str, tuple[int, ...] | None, str]] = []

    def generate(self, context: Mapping[str, Any]) -> Iterator[Candidate]:
        self.refused = []
        dps = int(context.get("dps", DEFAULT_DPS))
        seed = int(context.get("seed", DEFAULT_SEED))
        n_zeros = int(context.get("n_zeros", 2000))
        precision = Precision(kind="dps", value=dps, backend="mpmath")
        tol = _num(mp.mpf(10) ** -(dps - UNCERTAINTY_GUARD), 3)

        # 1. two independent routes to lambda_1
        started = time.perf_counter()
        defect = _route_defect_lambda1_closed_form({}, dps)
        yield from self._emit(
            claim={
                "lhs": "zeta.li.li_coefficients(1, method='cauchy')",
                "rhs": "zeta.li.li_closed_form_lambda1",
                "relation": "eq",
            },
            evidence={
                "defect": _num(defect, 6),
                "tolerance": tol,
                "defect_definition": "abs(lhs - rhs)",
            },
            route="defect_lambda1_closed_form",
            lab_object=ROUTES["defect_lambda1_closed_form"].lab_object,
            parameters={"n": 1, "dps": dps},
            precision=precision,
            seed=seed,
            duration_s=time.perf_counter() - started,
            label="lambda_1 by Cauchy integral versus its closed form",
        )

        # 2. the Jensen normalisation against Xi(0), true, and trivially so
        started = time.perf_counter()
        defect = _route_defect_gamma0_vs_Xi0({}, dps)
        yield from self._emit(
            claim={
                "lhs": "zeta.li.xi_taylor_gamma_0",
                "rhs": "8 * zeta.core.Xi_at_0",
                "relation": "eq",
            },
            evidence={
                "defect": _num(defect, 6),
                "tolerance": tol,
                "defect_definition": "abs(gamma(0) - 8*Xi(0))",
            },
            route="defect_gamma0_vs_Xi0",
            lab_object=ROUTES["defect_gamma0_vs_Xi0"].lab_object,
            parameters={"n": 0, "dps": dps},
            precision=precision,
            seed=seed,
            duration_s=time.perf_counter() - started,
            label="gamma(0) against 8*Xi(0)",
        )

        # 3. the integer-relation hunt. Three quantities are searched; only the
        #    ones where a *significant* relation is found and where this module
        #    can re-derive the residual become candidates. The other two are the
        #    honest common case: PSLQ finds nothing that survives its own
        #    significance threshold.
        self.pslq_notes = []
        for subject, route, params, available, getter in (
            ("zeta.li.lambda_1", "defect_lambda1_pslq", {"n": 1, "dps": dps}, dps,
             lambda: _lambda_table(1, dps)[0]),
            ("zeta.core.Xi_at_0", None, {"t": "0", "dps": dps}, dps,
             lambda: _route_Xi_at({"t": "0"}, dps)),
            ("zeta.statistics.unfolded_spacing_variance", None, {"n_zeros": n_zeros}, 15,
             lambda: _route_spacing_variance({"n_zeros": n_zeros}, dps)),
        ):
            started = time.perf_counter()
            coefficients, note = pslq_relation(getter(), dps=available)
            self.pslq_notes.append((subject, coefficients, note))
            if coefficients is None or route is None:
                # Nothing significant, or nothing this module can re-derive.
                # Either way it is work that produced no candidate, and it is
                # recorded rather than dropped.
                self._refuse(
                    f"integer-relation hunt on {subject}",
                    (note if coefficients is None
                     else "a significant relation was found but this module has "
                          "no route that re-derives its defect",),
                )
                continue
            expression = self._render(coefficients)
            defect = _route_defect_lambda1_pslq({}, dps)
            yield from self._emit(
                claim={
                    "lhs": subject,
                    "rhs": expression,
                    "relation": "eq",
                },
                evidence={
                    "defect": _num(defect, 6),
                    "tolerance": tol,
                    "defect_definition": "abs(lhs - rhs) with rhs evaluated at the same dps",
                    "pslq_coefficients": [int(c) for c in coefficients],
                    "pslq_basis": ["<measured>"] + [name for name, _ in PSLQ_BASIS],
                    "pslq_note": note,
                },
                route=route,
                lab_object=ROUTES[route].lab_object,
                parameters=params,
                precision=precision,
                seed=seed,
                duration_s=time.perf_counter() - started,
                label=f"{subject} identified by an integer-relation search",
            )

        # 4. the spacings are closer to GUE than to Poisson
        started = time.perf_counter()
        report = _level_repulsion(n_zeros)
        gue = _f(report["ks_gue_exact"]["statistic"])
        poisson = _f(report["ks_poisson"]["statistic"])
        yield from self._emit(
            claim={
                "lhs": "KS(unfolded spacings, GUE Gaudin law)",
                "rhs": "KS(unfolded spacings, Poisson law)",
                "relation": "lt",
            },
            evidence={
                "defect": _f(max(0.0, gue - poisson)),
                "tolerance": 1e-12,
                "defect_definition": "max(0, KS_GUE - KS_Poisson)",
                "ks_gue_exact": gue,
                "ks_poisson": poisson,
                "ratio": _f(report["ks_ratio_poisson_over_gue"]),
                "n_spacings": _i(report["n_spacings"]),
                "note": (
                    "the same sample rejects exact agreement with GUE at this "
                    "height (p = %.2g); the claim recorded here is only the "
                    "ordering of the two distances"
                    % _f(report["ks_gue_exact"]["pvalue"])
                ),
            },
            route="defect_gue_beats_poisson",
            lab_object=ROUTES["defect_gue_beats_poisson"].lab_object,
            parameters={"n_zeros": n_zeros},
            precision=Precision(kind="float64", backend="scipy"),
            seed=seed,
            duration_s=time.perf_counter() - started,
            label="zero spacings sit closer to GUE than to Poisson",
        )

    @staticmethod
    def _render(coefficients: Sequence[int]) -> str:
        """``c0*x + c1 + c2*g + ... = 0`` solved for ``x``, as readable text."""
        head = int(coefficients[0])
        parts: list[str] = []
        for coeff, (name, _) in zip(coefficients[1:], PSLQ_BASIS):
            c = -int(coeff)
            if c == 0:
                continue
            term = name if name != "1" else "1"
            parts.append(f"{c:+d}*{term}")
        body = " ".join(parts) if parts else "0"
        return f"({body}) / {head}"

    def _emit(
        self,
        *,
        claim: Mapping[str, Any],
        evidence: Mapping[str, Any],
        route: str | None,
        lab_object: str,
        parameters: Mapping[str, Any],
        precision: Precision,
        seed: int,
        duration_s: float,
        label: str,
    ) -> Iterator[Candidate]:
        refusals = kind_reasons(CandidateKind.RELATION, claim, evidence)
        if refusals:
            self._refuse(label, refusals)
            return
        yield Candidate(
            kind=CandidateKind.RELATION,
            claim=dict(claim),
            evidence=dict(evidence),
            provenance=_provenance(
                generator=self.name,
                version=self.version,
                route=route,
                lab_object=lab_object,
                parameters=parameters,
                precision=precision,
                seed=seed,
                duration_s=duration_s,
            ),
            label=label,
        )


# ---------------------------------------------------------------------------
# Generator 4, extremal records
# ---------------------------------------------------------------------------


class ExtremalGenerator(_RecordingGenerator):
    """Record holders, each with the runner-up that makes the record falsifiable.

    ``n_searched`` sits in the claim, so extending a search produces a *new*
    candidate rather than silently overwriting the old one, a record over a
    larger set is a different and stronger statement.
    """

    name = "zeta_extremal"
    version = "1.1"

    def generate(self, context: Mapping[str, Any]) -> Iterator[Candidate]:
        self.refused = []
        dps = int(context.get("dps", DEFAULT_DPS))
        seed = int(context.get("seed", DEFAULT_SEED))
        n_zeros = int(context.get("n_zeros", 2000))
        yield from self._weil_margin(context, seed)
        yield from self._smallest_gap(n_zeros, seed)
        yield from self._mertens_record(seed)
        yield from self._jensen_degeneracy(dps, seed, context)

    def _weil_margin(self, context: Mapping[str, Any], seed: int) -> Iterator[Candidate]:
        n_points = int(context.get("weil_points", 5))
        probe_dps = int(context.get("weil_dps", 15))
        started = time.perf_counter()
        rows = _weil_probe(n_points, probe_dps)
        margins = sorted(row["margin"] for row in rows)
        best, runner_up = margins[0], margins[1]
        # The record is about *one* member of the family, so the noise floor
        # recorded beside it must be that member's own, and it must be on the
        # same scale as the number it is compared with. ``positivity_probe``
        # reports ``margin = W/scale`` (dimensionless) but ``noise_floor`` as an
        # absolute bound on ``W``; pairing them directly compares two different
        # quantities, and taking ``min`` over the family used to attach a
        # *different* member's floor to this member's record.
        best_row = min(rows, key=lambda r: r["margin"])
        floor_absolute = best_row["noise_floor"]
        floor_relative = floor_absolute / best_row["scale"]
        argopt = best_row["param"]
        yield from self._emit(
            claim={
                "subject": "zeta.weil.min_positivity_margin_gaussian",
                "direction": "min",
                "space": (
                    f"gaussian pairs h(r)=exp(-a r^2), {n_points} values of a "
                    "log-spaced over [0.005, 0.2]"
                ),
                "n_searched": n_points,
                "argopt": _num(argopt, 12),
                "value": _num(best, 12),
            },
            evidence={
                "runner_up": _num(runner_up, 12),
                # comparable with ``value``: both are W divided by the scale
                "noise_floor": _num(floor_relative, 6),
                "noise_floor_absolute_on_W": _num(floor_absolute, 6),
                "scale": _num(best_row["scale"], 6),
                "dps_used": _i(best_row["dps_used"]),
                "resolved_above_noise": bool(best_row["W"] > floor_absolute),
                "all_margins": [_num(m, 12) for m in margins],
                "note": (
                    "Weil positivity holding on a finite family is not evidence "
                    "for RH; the margin is how close the tested pair came to the "
                    "boundary. 'noise_floor' is this member's own quadrature "
                    "noise estimate divided by its scale, so it is directly "
                    "comparable with 'value'; the raw bound on W is recorded "
                    "separately"
                ),
            },
            lab_object="zeta.weil.positivity_probe",
            parameters={"family": "gaussian", "n_points": n_points, "dps": probe_dps},
            precision=Precision(kind="dps", value=probe_dps, backend="mpmath"),
            seed=seed,
            duration_s=time.perf_counter() - started,
            label="the tightest Weil positivity margin in the tested family",
        )

    def _smallest_gap(self, n_zeros: int, seed: int) -> Iterator[Candidate]:
        started = time.perf_counter()
        spacings = _unfolded_spacings(n_zeros)
        order = np.argsort(spacings)
        best = _f(spacings[order[0]])
        runner_up = _f(spacings[order[1]])
        yield from self._emit(
            claim={
                "subject": "zeta.statistics.min_unfolded_spacing",
                "direction": "min",
                "space": f"the first {n_zeros} zero ordinates, unfolded",
                "n_searched": int(spacings.size),
                "argopt": _i(order[0]) + 1,
                "value": best,
            },
            evidence={
                "runner_up": runner_up,
                "mean_spacing": _f(spacings.mean()),
                "note": "level repulsion makes small gaps rare but not forbidden",
            },
            lab_object="zeta.statistics.nearest_neighbour_spacings",
            parameters={"n_zeros": n_zeros},
            precision=Precision(kind="float64", backend="numpy"),
            seed=seed,
            duration_s=time.perf_counter() - started,
            label="the smallest normalised gap between consecutive zeros",
        )

    def _mertens_record(self, seed: int) -> Iterator[Candidate]:
        started = time.perf_counter()
        limit = int(MERTENS_GRID[-1])
        x_min = 100
        ratios = np.abs(_mertens_ratios(limit))[x_min : limit + 1]
        order = np.argsort(ratios)[::-1]
        best_x = _i(order[0]) + x_min
        best = _f(ratios[order[0]])
        runner_up = _f(ratios[order[1]])
        if not best > runner_up:  # a tie is an extremal set, not a record
            self._refuse(
                "the largest |M(x)|/sqrt(x) below one million",
                (f"the record ties its runner-up at {best!r}: a tie is an "
                 "extremal set and the schema has no way to say which element "
                 "is the record",),
            )
            return
        yield from self._emit(
            claim={
                "subject": "zeta.criteria.max_abs_mertens_ratio",
                "direction": "max",
                "space": f"integers {x_min} <= x <= {limit}",
                "n_searched": int(limit - x_min + 1),
                "argopt": best_x,
                "value": best,
            },
            evidence={
                "runner_up": runner_up,
                "runner_up_x": _i(order[1]) + x_min,
                "note": (
                    "|M(x)|/sqrt(x) staying below 1 on a finite range is not "
                    "evidence: the Mertens conjecture is false"
                ),
            },
            lab_object="zeta.criteria.mertens_ratio_extremes",
            parameters={"limit": limit, "x_min": x_min},
            precision=Precision(kind="float64", backend="numpy"),
            seed=seed,
            duration_s=time.perf_counter() - started,
            label="the largest |M(x)|/sqrt(x) below one million",
        )

    def _jensen_degeneracy(
        self, dps: int, seed: int, context: Mapping[str, Any]
    ) -> Iterator[Candidate]:
        d_max = int(context.get("jensen_d_max", 6))
        n_max = int(context.get("jensen_n_max", 4))
        started = time.perf_counter()
        rows = _jensen_min_gaps(d_max, n_max, dps)
        label = "the most nearly degenerate Jensen polynomial on the grid"
        if len(rows) < 2:
            self._refuse(
                label,
                (f"the grid 2<=d<={d_max}, 0<=n<={n_max} holds {len(rows)} "
                 "polynomial(s); a record needs a search space of at least two",),
            )
            return
        ordered = sorted(rows, key=lambda r: r[2])
        (d, n, best), (_, _, runner_up) = ordered[0], ordered[1]
        if not best < runner_up:
            self._refuse(
                label,
                (f"the smallest gap ties its runner-up at {best!r}: a tie is an "
                 "extremal set, not a record",),
            )
            return
        yield from self._emit(
            claim={
                "subject": "zeta.li.min_relative_root_gap_of_jensen_polynomial",
                "direction": "min",
                "space": f"Jensen polynomials J^(d,n), 2 <= d <= {d_max}, 0 <= n <= {n_max}",
                "n_searched": len(rows),
                "argopt": f"d={d},n={n}",
                "value": best,
            },
            evidence={
                "runner_up": runner_up,
                "note": (
                    "the relative root separation is what an exact Sturm "
                    "certificate must exceed for its conclusion to transfer to "
                    "the true coefficients"
                ),
            },
            lab_object="zeta.li.jensen_polynomial",
            parameters={"d_max": d_max, "n_max": n_max, "dps": dps},
            precision=Precision(kind="dps", value=dps, backend="mpmath"),
            seed=seed,
            duration_s=time.perf_counter() - started,
            label="the most nearly degenerate Jensen polynomial on the grid",
        )

    def _emit(
        self,
        *,
        claim: Mapping[str, Any],
        evidence: Mapping[str, Any],
        lab_object: str,
        parameters: Mapping[str, Any],
        precision: Precision,
        seed: int,
        duration_s: float,
        label: str,
    ) -> Iterator[Candidate]:
        refusals = kind_reasons(CandidateKind.EXTREMAL, claim, evidence)
        if refusals:
            self._refuse(label, refusals)
            return
        yield Candidate(
            kind=CandidateKind.EXTREMAL,
            claim=dict(claim),
            evidence=dict(evidence),
            provenance=_provenance(
                generator=self.name,
                version=self.version,
                route=None,
                lab_object=lab_object,
                parameters=parameters,
                precision=precision,
                seed=seed,
                duration_s=duration_s,
            ),
            label=label,
        )


# ---------------------------------------------------------------------------
# Generator 5, the universe where RH is a theorem
# ---------------------------------------------------------------------------

FINITE_FIELD_PRIMES: Final[tuple[int, ...]] = (503, 1009, 4001)


class FiniteFieldGenerator(_RecordingGenerator):
    """Quantities from curves over finite fields, where RH is a theorem.

    That is the point of mining here: every candidate this generator emits is
    checkable against a proved statement, so the funnel's own accuracy can be
    audited rather than asserted. Two of the relations are exact integer
    identities (Birch's second-moment formula, and the fact that every integer
    in the Hasse interval occurs as a trace); the extremal records are Hasse
    ratios, which a theorem bounds by 1.
    """

    name = "zeta_finite_field"
    version = "1.1"

    def generate(self, context: Mapping[str, Any]) -> Iterator[Candidate]:
        self.refused = []
        seed = int(context.get("seed", DEFAULT_SEED))
        primes = tuple(context.get("ff_primes", FINITE_FIELD_PRIMES))
        for p in primes:
            hist = _sato_tate(int(p))
            yield from self._hasse_record(int(p), hist, seed)
        p0 = int(primes[0])
        hist0 = _sato_tate(p0)
        yield from self._second_moment(p0, hist0, seed)
        yield from self._trace_surjectivity(p0, hist0, seed)

    def _hasse_record(
        self, p: int, hist: Mapping[str, Any], seed: int
    ) -> Iterator[Candidate]:
        started = time.perf_counter()
        max_abs = _i(hist["max_abs_a_p"])
        bound = 2.0 * math.sqrt(p)
        best = max_abs / bound
        runner_up = (max_abs - 1) / bound
        n_curves = _i(hist["n_curves"])
        claim = {
            "subject": "zeta.finitefield.max_hasse_ratio",
            "direction": "max",
            "space": f"all {n_curves} nonsingular curves y^2=x^3+ax+b over F_{p}",
            "n_searched": n_curves,
            "argopt": f"p={p},a_p={max_abs}",
            "value": _f(best),
        }
        evidence = {
            "runner_up": _f(runner_up),
            "max_abs_a_p": max_abs,
            "hasse_bound": _f(bound),
            "hasse_violations": _i(hist["hasse_violations"]),
            "note": (
                "Hasse's theorem bounds this ratio by 1; a value above 1 would be "
                "a defect in the laboratory, not a discovery"
            ),
        }
        label = f"largest Hasse ratio over all curves mod {p}"
        refusals = kind_reasons(CandidateKind.EXTREMAL, claim, evidence)
        if refusals:
            self._refuse(label, refusals)
            return
        yield Candidate(
            kind=CandidateKind.EXTREMAL,
            claim=claim,
            evidence=evidence,
            provenance=_provenance(
                generator=self.name,
                version=self.version,
                route=None,
                lab_object="zeta.finitefield.sato_tate_histogram",
                parameters={"p": p},
                # The point counts are exact integers, but the number claimed
                # is ``max|a_p| / (2 sqrt p)``, a float64 division. Recording
                # this as ``exact`` would assert that the claim carries infinite
                # effort, which is both false and unpromotable.
                precision=Precision(kind="float64", backend="python-float"),
                seed=seed,
                duration_s=time.perf_counter() - started,
            ),
            label=label,
        )

    def _second_moment(
        self, p: int, hist: Mapping[str, Any], seed: int
    ) -> Iterator[Candidate]:
        started = time.perf_counter()
        defect = _f(
            abs(_i(hist["second_moment_exact"]) - _i(hist["second_moment_closed_form"]))
        )
        yield from _emit_relation(
            generator=self,
            claim={
                "lhs": f"sum of a_p^2 over all nonsingular curves mod {p}, counted",
                "rhs": "Birch's closed form for the same sum",
                "relation": "eq",
            },
            evidence={
                "defect": defect,
                "tolerance": 1e-30,
                "defect_definition": "abs(counted - closed form), both exact integers",
                "counted": _i(hist["second_moment_exact"]),
                "closed_form": _i(hist["second_moment_closed_form"]),
            },
            route="defect_ff_second_moment",
            lab_object=ROUTES["defect_ff_second_moment"].lab_object,
            parameters={"p": p},
            precision=Precision(kind="exact", backend="python-int"),
            seed=seed,
            duration_s=time.perf_counter() - started,
            label=f"the second moment of a_p over all curves mod {p}",
        )

    def _trace_surjectivity(
        self, p: int, hist: Mapping[str, Any], seed: int
    ) -> Iterator[Candidate]:
        started = time.perf_counter()
        defect = _f(
            abs(_i(hist["distinct_traces"]) - _i(hist["hasse_interval_size"]))
        )
        yield from _emit_relation(
            generator=self,
            claim={
                "lhs": f"number of distinct traces a_p over all curves mod {p}",
                "rhs": f"number of integers in the Hasse interval for p={p}",
                "relation": "eq",
            },
            evidence={
                "defect": defect,
                "tolerance": 1e-30,
                "defect_definition": "abs(distinct traces - width of the Hasse interval)",
                "distinct_traces": _i(hist["distinct_traces"]),
                "hasse_interval_size": _i(hist["hasse_interval_size"]),
            },
            route="defect_ff_trace_surjectivity",
            lab_object=ROUTES["defect_ff_trace_surjectivity"].lab_object,
            parameters={"p": p},
            precision=Precision(kind="exact", backend="python-int"),
            seed=seed,
            duration_s=time.perf_counter() - started,
            label=f"every integer in the Hasse interval occurs as a trace mod {p}",
        )


def _emit_relation(
    *,
    generator: _RecordingGenerator,
    claim: Mapping[str, Any],
    evidence: Mapping[str, Any],
    route: str | None,
    lab_object: str,
    parameters: Mapping[str, Any],
    precision: Precision,
    seed: int,
    duration_s: float,
    label: str,
) -> Iterator[Candidate]:
    refusals = kind_reasons(CandidateKind.RELATION, claim, evidence)
    if refusals:
        generator._refuse(label, refusals)
        return
    yield Candidate(
        kind=CandidateKind.RELATION,
        claim=dict(claim),
        evidence=dict(evidence),
        provenance=_provenance(
            generator=generator.name,
            version=generator.version,
            route=route,
            lab_object=lab_object,
            parameters=parameters,
            precision=precision,
            seed=seed,
            duration_s=duration_s,
        ),
        label=label,
    )


# ---------------------------------------------------------------------------
# Generator 6, structural claims (the ones the battery must adjudicate)
# ---------------------------------------------------------------------------

#: Predicate strings that :class:`CounterexampleBatteryScreen` knows how to
#: re-express at the level of the zeta-like interface. Any other structural
#: predicate is recorded ``inconclusive`` rather than waved through.
PREDICATE_TURAN: Final[str] = (
    "the Jensen polynomial J^(2,0) of the completed function is hyperbolic "
    "(the Turan inequality gamma(1)^2 >= gamma(0)*gamma(2))"
)
PREDICATE_FUNCTIONAL_EQUATION: Final[str] = (
    "the completed function satisfies F(s) = F(1-s) to within 1e-20"
)
PREDICATE_HASSE: Final[str] = "the trace satisfies |a_p| <= 2*sqrt(p)"


class StructuralGenerator(_RecordingGenerator):
    """Universal claims over enumerated families, each with a failing control.

    The schema refuses a structural claim with no control on which the predicate
    returned ``False``, a property everything satisfies distinguishes nothing.
    That refusal is this repository's counterexample battery, generalised, and
    the controls here are computed rather than asserted.
    """

    name = "zeta_structural"
    version = "1.0"

    def generate(self, context: Mapping[str, Any]) -> Iterator[Candidate]:
        self.refused = []
        dps = int(context.get("dps", DEFAULT_DPS))
        seed = int(context.get("seed", DEFAULT_SEED))
        yield from self._jensen_hyperbolicity(dps, seed, context)
        yield from self._functional_equation(dps, seed)
        yield from self._hasse_family(seed, context)

    def _jensen_hyperbolicity(
        self, dps: int, seed: int, context: Mapping[str, Any]
    ) -> Iterator[Candidate]:
        from zeta.li import hyperbolicity_scan, is_hyperbolic

        d_max = int(context.get("jensen_d_max", 6))
        n_max = int(context.get("jensen_n_max", 4))
        started = time.perf_counter()
        rows = [
            row
            for row in hyperbolicity_scan(d_max, n_max, dps=dps, method="roots")
            if row["d"] >= 2
        ]
        witnesses = [f"J^({row['d']},{row['n']})" for row in rows]
        satisfied = sum(1 for row in rows if bool(row["hyperbolic"]))
        controls = []
        for label, coeffs in (
            ("X^2 + 1 (a complex conjugate root pair)", [1, 0, 1]),
            ("X^3 + X (roots 0, +i, -i)", [0, 1, 0, 1]),
        ):
            report = is_hyperbolic(
                [mp.mpf(c) for c in coeffs], dps=dps, method="roots"
            )
            controls.append({"id": label, "satisfied": bool(report["hyperbolic"])})
        yield from self._emit(
            claim={
                "family": "Jensen polynomials J^(d,n) of 8*xi(1/2+z)",
                "predicate": PREDICATE_TURAN,
                "scope": f"2 <= d <= {d_max}, 0 <= n <= {n_max}",
            },
            evidence={
                "witnesses": witnesses,
                "n_checked": len(witnesses),
                "n_satisfied": satisfied,
                "controls": controls,
                "method": "Durand-Kerner root finding at the recorded precision",
                "note": (
                    "hyperbolicity on a finite grid is not evidence for RH; "
                    "Griffin-Ono-Rolen-Zagier proved it for each d and all large n"
                ),
            },
            lab_object="zeta.li.hyperbolicity_scan",
            parameters={"d_max": d_max, "n_max": n_max, "dps": dps},
            precision=Precision(kind="dps", value=dps, backend="mpmath"),
            seed=seed,
            duration_s=time.perf_counter() - started,
            label="every Jensen polynomial on the grid is hyperbolic",
        )

    def _functional_equation(self, dps: int, seed: int) -> Iterator[Candidate]:
        from zeta.core import functional_equation_defect, zeta as zeta_fn

        started = time.perf_counter()
        points = ("3+4j", "-0.25+10.5j", "1.4-3j", "0.3+2j")
        witnesses: list[str] = []
        satisfied = 0
        tol = mp.mpf("1e-20")
        for point in points:
            with mp.workdps(dps + 10):
                s = mp.mpmathify(point)
                defect = abs(functional_equation_defect(s, dps=dps + 10))
            witnesses.append(f"s={point}")
            satisfied += int(defect < tol)
        with mp.workdps(dps + 10):
            s = mp.mpmathify("3+4j")
            control_defect = abs(zeta_fn(s, dps=dps) - zeta_fn(1 - s, dps=dps))
        controls = [
            {
                "id": "the uncompleted zeta(s) at s=3+4i",
                "satisfied": bool(control_defect < tol),
                "defect": _num(control_defect, 6),
            }
        ]
        yield from self._emit(
            claim={
                "family": "asymmetric sample points of the completed function",
                "predicate": PREDICATE_FUNCTIONAL_EQUATION,
                "scope": "the four points recorded in the witnesses",
            },
            evidence={
                "witnesses": witnesses,
                "n_checked": len(witnesses),
                "n_satisfied": satisfied,
                "controls": controls,
                "tolerance": "1e-20",
                "note": (
                    "this predicate is expected to hold for the "
                    "Davenport-Heilbronn function too, which is exactly what the "
                    "counterexample battery is for"
                ),
            },
            lab_object="zeta.core.functional_equation_defect",
            parameters={"dps": dps, "n_points": len(points)},
            precision=Precision(kind="dps", value=dps, backend="mpmath"),
            seed=seed,
            duration_s=time.perf_counter() - started,
            label="the completed function is symmetric about the critical line",
        )

    def _hasse_family(
        self, seed: int, context: Mapping[str, Any]
    ) -> Iterator[Candidate]:
        from zeta.finitefield import (
            frobenius_power_traces,
            random_curve,
            trace_of_frobenius,
        )

        p = int(context.get("ff_structural_prime", 503))
        n_curves = int(context.get("ff_structural_curves", 12))
        started = time.perf_counter()
        rng = random.Random(seed)
        bound = 2.0 * math.sqrt(p)
        witnesses: list[str] = []
        satisfied = 0
        for _ in range(n_curves):
            a, b = random_curve(p, rng=rng)
            trace = trace_of_frobenius(a, b, p)
            witnesses.append(f"(a,b)=({a},{b}) a_p={trace}")
            satisfied += int(abs(trace) <= bound)
        a, b = random_curve(p, rng=rng)
        t2 = frobenius_power_traces(a, b, p, 2)[1]
        controls = [
            {
                "id": (
                    f"the trace of Frobenius^2 on the same curve (a,b)=({a},{b}), "
                    f"t_2={t2}: bounded by 2p, not by 2 sqrt(p)"
                ),
                "satisfied": bool(abs(t2) <= bound),
                "t_2": _i(t2),
            }
        ]
        yield from self._emit(
            claim={
                "family": f"nonsingular curves y^2=x^3+ax+b over F_{p}",
                "predicate": PREDICATE_HASSE,
                "scope": f"{n_curves} curves drawn with seed {seed}",
            },
            evidence={
                "witnesses": witnesses,
                "n_checked": len(witnesses),
                "n_satisfied": satisfied,
                "controls": controls,
                "bound": _f(bound),
                "note": "Hasse's theorem: this is checked against a proved statement",
            },
            lab_object="zeta.finitefield.trace_of_frobenius",
            parameters={"p": p, "n_curves": n_curves},
            precision=Precision(kind="exact", backend="python-int"),
            seed=seed,
            stochastic=True,
            duration_s=time.perf_counter() - started,
            label=f"Hasse's bound holds for {n_curves} sampled curves mod {p}",
        )

    def _emit(
        self,
        *,
        claim: Mapping[str, Any],
        evidence: Mapping[str, Any],
        lab_object: str,
        parameters: Mapping[str, Any],
        precision: Precision,
        seed: int,
        duration_s: float,
        label: str,
        stochastic: bool = False,
    ) -> Iterator[Candidate]:
        refusals = kind_reasons(CandidateKind.STRUCTURAL, claim, evidence)
        if refusals:
            self._refuse(label, refusals)
            return
        yield Candidate(
            kind=CandidateKind.STRUCTURAL,
            claim=dict(claim),
            evidence=dict(evidence),
            provenance=_provenance(
                generator=self.name,
                version=self.version,
                route=None,
                lab_object=lab_object,
                parameters=parameters,
                precision=precision,
                seed=seed,
                stochastic=stochastic,
                duration_s=duration_s,
            ),
            label=label,
        )


# ---------------------------------------------------------------------------
# Generator 7, the Weil explicit formula on Legendre intervals
# ---------------------------------------------------------------------------


class LegendreWeilGenerator(_RecordingGenerator):
    """Mine the Riemann–Weil explicit formula localised to Legendre intervals.

    ``zeta.weil.legendre_pair(n)`` puts a unit triangle bump on
    ``[log n², log (n+1)²]``, so the prime term of the explicit formula sees
    exactly the interval of Legendre's conjecture and nothing else. One
    evaluation of ``explicit_formula_sides`` per interval feeds up to three
    observations:

    * the two sides agree within the truncation budget, an *instance of a
      theorem*, which the catalogue is expected to recognise as ``known``;
    * the Λ-mass the zeros-plus-pole side assigns to the interval is strictly
      positive, primes detected; for every n this generator can reach that
      is finitely verified, so again ``known``;
    * only under ``context["legendre_mass_constant"]``: the Λ-mass of the
      widest interval as a measured constant no catalogue tabulates, a
      designed survivor, opt-in for the same reason ``xi_points`` is.

    Nothing here is progress on Legendre's conjecture: the truncated zero
    side detects primes the sieve already lists, at a cost the sieve does not
    charge. The ancestor script (``scripts/40_legendre_weil.py``) printed
    "mathematically proves primes exist in this interval" over the same
    computation; the honest content is the measurement, and the funnel's
    verdicts are expected to say so.
    """

    name = "zeta_legendre_weil"
    version = "1.0"

    #: Intervals harvested by default. Small on purpose: the point is the
    #: instrument, not coverage, and every screen escalation re-runs the
    #: archimedean quadrature at roughly double precision.
    DEFAULT_N: Final[tuple[int, ...]] = (3, 6, 10)
    DEFAULT_GAMMA_MAX: Final[float] = 500.0

    def generate(self, context: Mapping[str, Any]) -> Iterator[Candidate]:
        self.refused = []
        dps = int(context.get("dps", DEFAULT_DPS))
        seed = int(context.get("seed", DEFAULT_SEED))
        gamma_max = float(context.get("legendre_gamma_max", self.DEFAULT_GAMMA_MAX))
        ns = tuple(int(n) for n in context.get("legendre_n", self.DEFAULT_N))
        precision = Precision(kind="dps", value=dps, backend="mpmath")

        emitted_any = False
        for n in ns:
            if n < 2:
                self._refuse(
                    f"legendre interval n={n}",
                    ("legendre_pair needs n >= 2: the n = 1 bump touches the "
                     "origin and stops being the Legendre localisation",),
                )
                continue
            started = time.perf_counter()
            sides = _legendre_sides(n, gamma_max, dps)
            with mp.workdps(dps + GUARD_DIGITS):
                resolution = mp.mpf(10) ** -(dps - UNCERTAINTY_GUARD)
                budget = (
                    mp.mpf(sides["zero_side_tail_bound"])
                    + mp.mpf(sides["prime_tail_bound"])
                    + resolution
                )
                mass = -mp.mpf(sides["prime_term"]) / 2
                detection_defect = max(mp.mpf(0), -mass)
            duration = time.perf_counter() - started
            parameters = {"n": n, "gamma_max": gamma_max, "dps": dps}

            # 1. the identity instance: both sides, computed independently
            yield from self._relation(
                claim={
                    "lhs": f"zeta.weil.explicit_formula.zero_side[legendre n={n}]",
                    "rhs": f"zeta.weil.explicit_formula.arithmetic_side[legendre n={n}]",
                    "relation": "eq",
                },
                evidence={
                    "defect": _num(sides["abs_diff"], 6),
                    "tolerance": _num(budget, 6),
                    "defect_definition": "abs(zero_side - arithmetic_side)",
                    "zero_side": _num(sides["zero_side"], 12),
                    "arithmetic_side": _num(sides["arithmetic_side"], 12),
                    "zero_side_tail_bound": _num(sides["zero_side_tail_bound"], 6),
                    "n_zeros_used": _i(sides["n_zeros_used"]),
                },
                route="legendre_weil_defect",
                parameters=parameters,
                precision=precision,
                seed=seed,
                duration_s=duration,
                label=f"explicit formula on the Legendre interval [{n * n}, {(n + 1) ** 2}]",
            )

            # 2. the detection: the interval's Λ-mass is strictly positive
            yield from self._relation(
                claim={
                    "lhs": f"zeta.weil.legendre_interval_lambda_mass[n={n}]",
                    "rhs": "0",
                    "relation": "gt",
                },
                evidence={
                    "defect": _num(detection_defect, 6),
                    "tolerance": _num(resolution, 3),
                    "defect_definition": "max(0, 0 - lambda_mass)",
                    "lambda_mass": _num(mass, dps),
                    "note": (
                        "every term Lambda(k) k^(-1/2) g(log k) is non-negative, "
                        "so positivity says exactly that a prime power lies in "
                        f"({n * n}, {(n + 1) ** 2}), finitely verifiable, and verified"
                    ),
                },
                route="legendre_detection_defect",
                parameters=parameters,
                precision=precision,
                seed=seed,
                duration_s=0.0,
                label=f"primes detected in [{n * n}, {(n + 1) ** 2}] from the zero side",
            )
            emitted_any = True

        # 3. the Λ-mass of the widest harvested interval, as a plain measured
        #    constant: escalates, cross-checks, and is in no catalogue, so it
        #    reaches ``survives`` by construction. Emitted only when the
        #    operator asks (the ``xi_points`` precedent): the default pass is
        #    designed to yield no survivor, and a flag that manufactures one
        #    on every fresh ledger would turn the headline into noise. The one
        #    recorded exercise of the full survivor path, literature check
        #    included, is in ROADMAP.md (2026-08-06).
        if emitted_any and bool(context.get("legendre_mass_constant", False)):
            n = max(x for x in ns if x >= 2)
            started = time.perf_counter()
            value = _route_legendre_lambda_mass({"n": n, "gamma_max": gamma_max}, dps)
            unc_text = _num(mp.mpf(10) ** -(dps - UNCERTAINTY_GUARD), 3)
            claim = {
                "subject": f"zeta.weil.legendre_lambda_mass_n_{n}",
                "value": _num(value, dps),
            }
            evidence = {
                "uncertainty": unc_text,
                "working_precision": f"dps={dps}",
            }
            refusals = kind_reasons(CandidateKind.CONSTANT, claim, evidence)
            if refusals:
                self._refuse(f"legendre lambda mass n={n}", refusals)
            else:
                yield Candidate(
                    kind=CandidateKind.CONSTANT,
                    claim=claim,
                    evidence=evidence,
                    provenance=_provenance(
                        generator=self.name,
                        version=self.version,
                        route="legendre_lambda_mass",
                        lab_object=ROUTES["legendre_lambda_mass"].lab_object,
                        parameters={"n": n, "gamma_max": gamma_max, "dps": dps},
                        precision=precision,
                        seed=seed,
                        duration_s=time.perf_counter() - started,
                    ),
                    dedup_digits=_dedup_digits(claim["value"], unc_text),
                    label=f"the Weil-weighted Lambda-mass of [{n * n}, {(n + 1) ** 2}]",
                )

    def _relation(
        self,
        *,
        claim: Mapping[str, Any],
        evidence: Mapping[str, Any],
        route: str,
        parameters: Mapping[str, Any],
        precision: Precision,
        seed: int,
        duration_s: float,
        label: str,
    ) -> Iterator[Candidate]:
        refusals = kind_reasons(CandidateKind.RELATION, claim, evidence)
        if refusals:
            self._refuse(label, refusals)
            return
        yield Candidate(
            kind=CandidateKind.RELATION,
            claim=dict(claim),
            evidence=dict(evidence),
            provenance=_provenance(
                generator=self.name,
                version=self.version,
                route=route,
                lab_object=ROUTES[route].lab_object,
                parameters=parameters,
                precision=precision,
                seed=seed,
                duration_s=duration_s,
            ),
            label=label,
        )


# ---------------------------------------------------------------------------
# Screens
# ---------------------------------------------------------------------------


def _passed(screen: str, detail: str, effort: float | None = None) -> ScreenResult:
    return ScreenResult(screen=screen, passed=True, detail=detail, effort=effort)


def _stopped(
    screen: str, verdict: Verdict, detail: str, effort: float | None = None
) -> ScreenResult:
    return ScreenResult(
        screen=screen, passed=False, verdict=verdict, detail=detail, effort=effort
    )


def _inconclusive(
    screen: str, version: str, reason: InconclusiveReason, detail: str, ceiling: Mapping[str, Any]
) -> Verdict:
    return Verdict(
        status=VerdictStatus.INCONCLUSIVE,
        decided_by=screen,
        decided_by_version=version,
        decided_at=_utc_now(),
        evidence={
            "reason": reason.value,
            "detail": detail,
            "ceiling": dict(ceiling),
        },
    )


def _refuted(
    screen: str,
    version: str,
    *,
    witness: Mapping[str, Any],
    defect: Any,
    tolerance: Any,
    effort: float,
    escalated_effort: float,
    escalated_defect: Any,
    notes: str = "",
) -> Verdict:
    return Verdict(
        status=VerdictStatus.REFUTED,
        decided_by=screen,
        decided_by_version=version,
        decided_at=_utc_now(),
        evidence={
            "witness": dict(witness),
            "defect": _num(defect, 8),
            "tolerance": _num(tolerance, 8),
            "effort": _f(effort),
            "escalated_effort": _f(escalated_effort),
            "escalated_defect": _num(escalated_defect, 8),
        },
        notes=notes,
    )


#: Absolute size below which an overshoot of a recorded range is not a
#: refutation but a rounding question. Crossing a bound by less than this is
#: what the ``inconclusive`` branch of :class:`NumericSanityScreen` is for.
RANGE_TOLERANCE: Final[str] = "1e-12"

#: Ranges a *theorem or an exact construction* pins, keyed by the candidate's
#: identity string. A value outside one of these is a defect in the laboratory,
#: and the honest reading of "a computation appears to settle something open"
#: is a bug.
#:
#: **Only proved bounds belong here**, because crossing one is recorded as a
#: ``refuted`` verdict whose notes say a theorem was contradicted. ``math.inf``
#: is how an entry says "nothing is proved on that side": a heuristic bound
#: dressed as a theorem would manufacture refutations, which is the opposite of
#: what this screen is for. Two entries used to carry an upper bound of 4.0 on
#: spacing statistics; no theorem pins either, so both now say ``inf``.
RANGE_RULES: Final[Mapping[str, tuple[float, float, str]]] = {
    "zeta.finitefield.max_hasse_ratio": (
        0.0,
        1.0,
        "Hasse's theorem: |a_p| <= 2 sqrt(p) for every curve over F_p",
    ),
    "zeta.statistics.min_unfolded_spacing": (
        0.0,
        math.inf,
        "a spacing between distinct ordinates is non-negative by construction",
    ),
    "zeta.statistics.unfolded_spacing_variance": (
        0.0,
        math.inf,
        "a variance is non-negative; nothing proved bounds this one above, so "
        "only the non-negativity is checked",
    ),
    "zeta.statistics.mean_unfolded_spacing": (
        0.0,
        math.inf,
        "a mean of non-negative spacings is non-negative; that the unfolded "
        "mean sits at 1 is a property of the construction, not a proved bound, "
        "and it is the triviality screen that says so",
    ),
    "zeta.li.min_relative_root_gap_of_jensen_polynomial": (
        0.0,
        math.inf,
        "a relative root separation is non-negative",
    ),
}


def _finite_effort(candidate: Candidate) -> float:
    """The candidate's own effort, as a finite number a verdict can record.

    ``Precision(kind='exact').effort_digits()`` is ``inf``, which is not JSON
    and which the schema refuses. Where a verdict needs a number, the working
    precision the candidate was generated at is the honest finite stand-in.
    """
    effort = candidate.provenance.precision.effort_digits()
    return float(effort) if math.isfinite(effort) else float(_base_dps(candidate))


class NumericSanityScreen(BaseScreen):
    """Cheap arithmetic sanity: finiteness, and the ranges a theorem pins.

    It cannot see whether a quantity is *interesting*. It can see whether a
    recorded number is outside a range that is already proved, which is the one
    numerical failure that is unambiguous.
    """

    name = "numeric_sanity"
    cost = "cheap"
    checks = ("refutation",)
    version = "1.0"

    def apply(self, candidate: Candidate) -> ScreenResult:
        numbers = _all_numbers(candidate)
        for where, value in numbers:
            if not math.isfinite(value):
                return _stopped(
                    self.name,
                    _inconclusive(
                        self.name,
                        self.version,
                        InconclusiveReason.NONDETERMINISTIC,
                        f"{where} is not finite ({value!r}), so nothing about this "
                        "observation can be decided",
                        {"field": where},
                    ),
                    f"{where} is not finite",
                )
        key = _identity_key(candidate)
        rule = RANGE_RULES.get(key)
        if rule is None:
            return _passed(self.name, f"no proved range is recorded for {key!r}")
        lo, hi, reference = rule
        value = _principal_value(candidate)
        if value is None:
            return _passed(self.name, "no principal value to range-check")
        if lo <= value <= hi:
            return _passed(
                self.name, f"{value:.6g} lies in [{lo:g}, {hi:g}] ({reference})"
            )
        overshoot = max(lo - value, value - hi)
        tolerance = mp.mpf(RANGE_TOLERANCE)
        if not overshoot > tolerance:
            # A hair outside a proved bound is a question about the arithmetic,
            # not a refutation, and the schema is right to refuse a refutation
            # whose defect is inside its own tolerance. Building one anyway
            # produced a malformed ScreenResult, which the funnel turns into a
            # FunnelError that kills the whole run, so the near-boundary case,
            # the only interesting one, used to abort the pipeline.
            return _stopped(
                self.name,
                _inconclusive(
                    self.name,
                    self.version,
                    InconclusiveReason.PRECISION_INSUFFICIENT,
                    f"{value!r} lies outside [{lo:g}, {hi:g}] by "
                    f"{mp.nstr(overshoot, 3)}, which is not more than the "
                    f"arithmetic tolerance {RANGE_TOLERANCE}: at this precision "
                    "the value cannot be distinguished from the bound",
                    {"range": [lo, hi], "tolerance": RANGE_TOLERANCE, "subject": key},
                ),
                f"{value:.6g} sits on the boundary of [{lo:g}, {hi:g}] to within "
                f"{RANGE_TOLERANCE}",
            )
        effort = _finite_effort(candidate)
        return _stopped(
            self.name,
            _refuted(
                self.name,
                self.version,
                witness={"subject": key, "value": _num(value, 12)},
                defect=overshoot,
                tolerance=tolerance,
                # Nominal, and said so in the notes: a value outside a *proved*
                # range is outside it at every precision, so there is no second
                # computation to run. The schema's escalation fields exist to
                # stop arithmetic noise being logged as a refutation; here the
                # overshoot exceeding RANGE_TOLERANCE is what rules noise out.
                effort=effort,
                escalated_effort=effort + 1.0,
                escalated_defect=overshoot,
                notes=(
                    f"outside the range {reference} pins, by "
                    f"{mp.nstr(overshoot, 3)} against an arithmetic tolerance of "
                    f"{RANGE_TOLERANCE}; a computation that appears to contradict "
                    "a theorem is a bug, not a discovery. The escalation fields "
                    "are nominal: a proved range does not move with precision, "
                    "and it is the overshoot exceeding the tolerance, not a "
                    "second computation, that rules out arithmetic noise."
                ),
            ),
            f"{value:.6g} is outside [{lo:g}, {hi:g}]: {reference}",
        )


def _all_numbers(candidate: Candidate) -> list[tuple[str, float]]:
    out: list[tuple[str, float]] = []

    def walk(value: Any, where: str) -> None:
        if isinstance(value, bool) or value is None:
            return
        if isinstance(value, (int, float)):
            out.append((where, float(value)))
            return
        if isinstance(value, str):
            if _NUMERIC_RE.match(value.strip()):
                try:
                    out.append((where, float(value)))
                except (ValueError, OverflowError):
                    pass
            return
        if isinstance(value, Mapping):
            for key, item in value.items():
                walk(item, f"{where}.{key}")
            return
        if isinstance(value, Sequence):
            for i, item in enumerate(value):
                walk(item, f"{where}[{i}]")

    walk(dict(candidate.claim), "claim")
    walk(dict(candidate.evidence), "evidence")
    return out


def _identity_key(candidate: Candidate) -> str:
    claim = candidate.claim
    for field_name in ("subject", "lhs", "family"):
        value = claim.get(field_name)
        if isinstance(value, str):
            return value
    return ""


def _principal_value(candidate: Candidate) -> float | None:
    if candidate.kind in (CandidateKind.CONSTANT, CandidateKind.EXTREMAL):
        try:
            return float(candidate.claim["value"])
        except (KeyError, TypeError, ValueError):
            return None
    return None


class PrecisionStabilityScreen(BaseScreen):
    """The single most valuable cheap screen: does the number survive a bump?

    A candidate is re-derived from its own provenance at strictly higher working
    precision. If it moves by more than the error bar it claimed, the error bar
    was fiction and the observation is numerical noise. The refutation is only
    recorded if it *persists* at a second, higher escalation, a failure that
    vanishes when precision rises is arithmetic, not mathematics, and the schema
    refuses it as a refutation.

    Two honest limits, both recorded rather than hidden: a route that cannot buy
    digits (a float64 statistic) is reported as such and decides nothing, and a
    candidate with no re-derivation route at all is recorded ``inconclusive``
    with reason ``dependency_unavailable``.
    """

    name = "precision_stability"
    cost = "cheap"
    checks = ("refutation",)
    version = "1.0"

    def apply(self, candidate: Candidate) -> ScreenResult:
        if candidate.kind not in (CandidateKind.CONSTANT, CandidateKind.RELATION):
            return _passed(self.name, f"not applicable to {candidate.kind.value}")
        route = _route_of(candidate)
        if route is None:
            return _stopped(
                self.name,
                _inconclusive(
                    self.name,
                    self.version,
                    InconclusiveReason.DEPENDENCY_UNAVAILABLE,
                    "the provenance names no re-derivation route, so the value "
                    "cannot be recomputed at higher precision",
                    {"route": str(candidate.provenance.parameters.get("route"))},
                ),
                "no re-derivation route",
            )
        if not route.escalates:
            return _passed(
                self.name,
                f"route {route.name!r} is float64: raising dps buys no digits, so "
                "this screen cannot speak",
            )
        base_dps = _base_dps(candidate)
        params = _route_params(candidate)
        first_dps = base_dps + max(10, base_dps // 2)
        second_dps = base_dps + 2 * max(10, base_dps // 2)

        with mp.workdps(second_dps + GUARD_DIGITS):
            claimed = _claimed_number(candidate)
            tolerance = _claim_tolerance(candidate)
            assert claimed is not None and tolerance is not None
            moved = abs(mp.mpf(route.compute(params, first_dps)) - claimed)
            if moved > tolerance:
                moved_again = abs(mp.mpf(route.compute(params, second_dps)) - claimed)
            else:
                moved_again = moved
        if moved <= tolerance:
            return _passed(
                self.name,
                f"re-derived at dps={first_dps}: moved by {mp.nstr(moved, 3)} "
                f"<= the claimed {mp.nstr(tolerance, 3)}",
                effort=float(first_dps),
            )
        if moved_again <= tolerance:
            return _stopped(
                self.name,
                _inconclusive(
                    self.name,
                    self.version,
                    InconclusiveReason.PRECISION_INSUFFICIENT,
                    f"the value moved by {mp.nstr(moved, 3)} at dps={first_dps} but "
                    f"only {mp.nstr(moved_again, 3)} at dps={second_dps}: the "
                    "disagreement is an artefact of the first escalation",
                    {"dps": second_dps},
                ),
                "movement did not persist under a second escalation",
            )
        return _stopped(
            self.name,
            _refuted(
                self.name,
                self.version,
                witness={
                    "route": route.name,
                    "parameters": {k: str(v) for k, v in params.items()},
                    "base_dps": base_dps,
                },
                defect=moved,
                tolerance=tolerance,
                effort=float(base_dps),
                escalated_effort=float(second_dps),
                escalated_defect=moved_again,
                notes=(
                    "the recorded value does not survive a precision increase, so "
                    "the error bar it claimed was not earned"
                ),
            ),
            f"moved by {mp.nstr(moved_again, 3)} at dps={second_dps}, "
            f"claimed error {mp.nstr(tolerance, 3)}",
            effort=float(second_dps),
        )


def _base_dps(candidate: Candidate) -> int:
    precision = candidate.provenance.precision
    if precision.kind == "dps" and precision.value:
        return int(precision.value)
    parameter = candidate.provenance.parameters.get("dps")
    if isinstance(parameter, int) and not isinstance(parameter, bool):
        return int(parameter)
    return DEFAULT_DPS


@dataclass(frozen=True, slots=True)
class TrivialityRule:
    """One way a claim follows, in a line, from something already recorded.

    ``check`` takes the *candidate's own* parameters as well as its working
    precision. Running the reduction on a fixed sample instead would let the
    screen declare a candidate trivial on the strength of a computation about a
    different object.
    """

    identity: tuple[str, ...]
    derived_from: tuple[str, ...]
    argument: str
    check: Callable[[Mapping[str, Any], int], Any]
    tolerance: str


def _check_gamma0_reduction(params: Mapping[str, Any], dps: int) -> Any:
    return _route_defect_gamma0_vs_Xi0(params, dps)


def _check_mean_spacing_reduction(params: Mapping[str, Any], dps: int) -> Any:
    """|mean spacing - 1|, which unfolding forces to be small by construction.

    The sample is the candidate's own: a mean over 2000 ordinates says nothing
    about a candidate harvested from 200.
    """
    n_zeros = int(params.get("n_zeros", 2000))
    return abs(_route_mean_spacing({"n_zeros": n_zeros}, dps) - 1)


TRIVIALITY_RULES: Final[tuple[TrivialityRule, ...]] = (
    TrivialityRule(
        identity=("zeta.li.xi_taylor_gamma_0", "8 * zeta.core.Xi_at_0"),
        derived_from=(
            "zeta.li.xi_taylor_coefficients: 8*xi(1/2+z) = sum gamma(n) z^(2n)/n!",
            "zeta.core.Xi: Xi(t) = xi(1/2 + it), so Xi(0) = xi(1/2)",
        ),
        argument=(
            "Setting z = 0 in the defining series gives gamma(0) = 8*xi(1/2) = "
            "8*Xi(0). The equality is the normalisation, not a measurement."
        ),
        check=_check_gamma0_reduction,
        tolerance="1e-18",
    ),
    TrivialityRule(
        identity=("zeta.statistics.mean_unfolded_spacing",),
        derived_from=(
            "zeta.statistics.unfold: gamma -> theta(gamma)/pi",
            "zeta.zeros.riemann_von_mangoldt: N(T) ~ theta(T)/pi + 1",
        ),
        argument=(
            "Unfolding divides by the mean density, so consecutive unfolded "
            "ordinates differ by 1 on average by construction. The measured mean "
            "is that construction, not a property of the ordinates."
        ),
        check=_check_mean_spacing_reduction,
        tolerance="0.01",
    ),
)


class TrivialityScreen(BaseScreen):
    """Does the claim follow, in one line, from an identity already in the lab?

    ``trivial`` is expected to be the second largest terminal class after
    ``known``, and the schema will not accept it without three things: the facts
    it follows from, an argument short enough to be one line, and the name of
    the procedure that verified the reduction actually reproduces the claim.
    This screen supplies all three, and it *runs* the reduction rather than
    asserting it.
    """

    name = "triviality"
    cost = "cheap"
    checks = ("trivial",)
    version = "1.0"

    def apply(self, candidate: Candidate) -> ScreenResult:
        if candidate.kind not in (CandidateKind.CONSTANT, CandidateKind.RELATION):
            return _passed(self.name, f"not applicable to {candidate.kind.value}")
        keys = tuple(
            str(candidate.claim.get(k))
            for k in ("subject", "lhs", "rhs")
            if candidate.claim.get(k) is not None
        )
        for rule in TRIVIALITY_RULES:
            if not set(rule.identity) <= set(keys):
                continue
            dps = _base_dps(candidate)
            params = _route_params(candidate)
            with mp.workdps(dps + GUARD_DIGITS):
                defect = abs(mp.mpf(rule.check(params, dps)))
                fails = defect > mp.mpf(rule.tolerance)
            if fails:
                return _passed(
                    self.name,
                    f"the recorded one-line reduction does not reproduce this "
                    f"claim (defect {mp.nstr(defect, 3)}), so it is not trivial "
                    "by that route",
                )
            verdict = Verdict(
                status=VerdictStatus.TRIVIAL,
                decided_by=self.name,
                decided_by_version=self.version,
                decided_at=_utc_now(),
                evidence={
                    "derived_from": list(rule.derived_from),
                    "argument": rule.argument,
                    "checked_by": (
                        "ontology.domains.zeta_domain.TrivialityScreen "
                        f"via {rule.check.__name__}"
                    ),
                    "checked_with": {k: str(v) for k, v in params.items()},
                    "defect": _num(defect, 6),
                    "tolerance": rule.tolerance,
                },
            )
            return _stopped(
                self.name,
                verdict,
                f"follows from {rule.derived_from[0]}",
            )
        return _passed(self.name, "no recorded one-line reduction covers this claim")


class HighPrecisionScreen(BaseScreen):
    """Expensive re-derivation: recompute at roughly twice the working precision.

    This is what buys the right to say ``survives``: the schema refuses that
    status unless verification cost strictly more than generation, and this
    screen is where the extra cost is spent and reported.
    """

    name = "high_precision_recompute"
    cost = "expensive"
    checks = ("refutation",)
    version = "1.0"

    def apply(self, candidate: Candidate) -> ScreenResult:
        if candidate.kind not in (CandidateKind.CONSTANT, CandidateKind.RELATION):
            return _passed(self.name, f"not applicable to {candidate.kind.value}")
        route = _route_of(candidate)
        if route is None or not route.escalates:
            return _passed(
                self.name,
                "no route that buys digits; this screen decides nothing and "
                "reports no verification effort",
            )
        base_dps = _base_dps(candidate)
        target = 2 * base_dps + 10
        params = _route_params(candidate)
        with mp.workdps(target + 20 + GUARD_DIGITS):
            claimed = _claimed_number(candidate)
            tolerance = _claim_tolerance(candidate)
            assert claimed is not None and tolerance is not None
            moved = abs(mp.mpf(route.compute(params, target)) - claimed)
            if moved > tolerance:
                moved_again = abs(
                    mp.mpf(route.compute(params, target + 20)) - claimed
                )
            else:
                moved_again = moved
        if moved <= tolerance:
            return _passed(
                self.name,
                f"re-derived at dps={target}: moved by {mp.nstr(moved, 3)} "
                f"<= claimed {mp.nstr(tolerance, 3)}",
                effort=float(target),
            )
        if moved_again <= tolerance:
            return _stopped(
                self.name,
                _inconclusive(
                    self.name,
                    self.version,
                    InconclusiveReason.PRECISION_INSUFFICIENT,
                    "the disagreement did not survive a further escalation",
                    {"dps": target + 20},
                ),
                "disagreement vanished at higher precision",
            )
        return _stopped(
            self.name,
            _refuted(
                self.name,
                self.version,
                witness={"route": route.name, "dps": target},
                defect=moved,
                tolerance=tolerance,
                effort=float(base_dps),
                escalated_effort=float(target + 20),
                escalated_defect=moved_again,
            ),
            f"disagrees by {mp.nstr(moved_again, 3)} at dps={target + 20}",
            effort=float(target + 20),
        )


class IndependentMethodScreen(BaseScreen):
    """Cross-check by a second route that shares nothing but the object itself.

    Where the laboratory has two implementations, the Cauchy and the literal
    definition of lambda_n, the Mellin and Cauchy routes to the Jensen
    coefficients, two implementations of Xi, this screen runs the other one.
    Where it has only one, it says so and decides nothing: an unavailable
    cross-check is not a passed cross-check.
    """

    name = "independent_method"
    cost = "expensive"
    checks = ("refutation",)
    version = "1.0"

    def apply(self, candidate: Candidate) -> ScreenResult:
        if candidate.kind is not CandidateKind.CONSTANT:
            return _passed(self.name, f"not applicable to {candidate.kind.value}")
        route = _route_of(candidate)
        if route is None or route.cross_check is None:
            return _passed(
                self.name,
                "the laboratory has no second route to this quantity; "
                "cross-check unavailable, nothing decided",
            )
        base_dps = _base_dps(candidate)
        target = base_dps + 10
        params = _route_params(candidate)
        with mp.workdps(target + 20 + GUARD_DIGITS):
            claimed = _claimed_number(candidate)
            tolerance = _claim_tolerance(candidate)
            assert claimed is not None and tolerance is not None
            gap = abs(mp.mpf(route.cross_check(params, target)) - claimed)
            if gap > tolerance:
                gap_again = abs(
                    mp.mpf(route.cross_check(params, target + 20)) - claimed
                )
            else:
                gap_again = gap
        if gap <= tolerance:
            return _passed(
                self.name,
                f"{route.cross_check_note} agrees to {mp.nstr(gap, 3)} at "
                f"dps={target}",
                effort=float(target),
            )
        if gap_again <= tolerance:
            return _stopped(
                self.name,
                _inconclusive(
                    self.name,
                    self.version,
                    InconclusiveReason.PRECISION_INSUFFICIENT,
                    "the two routes reconciled at higher precision",
                    {"dps": target + 20},
                ),
                "routes reconciled under escalation",
            )
        return _stopped(
            self.name,
            _refuted(
                self.name,
                self.version,
                witness={
                    "route": route.name,
                    "cross_check": route.cross_check_note,
                    "dps": target,
                },
                defect=gap,
                tolerance=tolerance,
                effort=float(base_dps),
                escalated_effort=float(target + 20),
                escalated_defect=gap_again,
                notes="two independent implementations disagree; one of them is wrong",
            ),
            f"independent route disagrees by {mp.nstr(gap_again, 3)}",
            effort=float(target + 20),
        )


# -- the battery gate -------------------------------------------------------


def _even_taylor_gammas(completed: Callable[[Any], Any], dps: int, radius: str = "0.4") -> list[Any]:
    """gamma(0), gamma(1), gamma(2) for an even completed function.

    ``G(z) = completed(1/2 + z)`` is even whenever the function satisfies
    ``F(s) = F(1-s)``, so its Taylor coefficients are extracted by one
    equispaced trapezoid pass around a circle. The Turan inequality
    ``gamma(1)^2 >= gamma(0) gamma(2)`` is invariant under both rescalings of
    ``G`` and of ``z``, so no normalisation constant needs to be agreed.
    """
    with mp.workdps(dps + 15):
        r = mp.mpf(radius)
        nodes = 32
        values = [
            completed(mp.mpf(1) / 2 + r * mp.expjpi(mp.mpf(2) * j / nodes))
            for j in range(nodes)
        ]
        out = []
        for n in range(3):
            m = 2 * n
            total = sum(
                v * mp.expjpi(mp.mpf(-2) * j * m / nodes)
                for j, v in enumerate(values)
            )
            coefficient = total / nodes / r**m
            out.append(mp.factorial(n) * mp.re(coefficient))
        return out


def _claim_turan(iface: Mapping[str, Any]) -> bool:
    """Claim: the completed function's J^(2,0) is hyperbolic (Turan inequality)."""
    gammas = _even_taylor_gammas(iface["completed"], 30)
    return bool(gammas[1] ** 2 >= gammas[0] * gammas[2])


def _claim_functional_equation(iface: Mapping[str, Any]) -> bool:
    from zeta.epstein import claim_functional_equation

    return bool(claim_functional_equation(iface))


BATTERY_CLAIMS: Final[Mapping[str, Callable[[Mapping[str, Any]], bool]]] = {
    PREDICATE_TURAN: _claim_turan,
    PREDICATE_FUNCTIONAL_EQUATION: _claim_functional_equation,
}


class CounterexampleBatteryScreen(BaseScreen):
    """The standing test: route every structural claim through the battery.

    ``AGENTS.md``: a claimed structural property that "explains" RH must be run
    against both zeta and the Davenport-Heilbronn function, which satisfies the
    functional equation, has real coefficients and a real Hardy-style Z, and
    violates RH. A property f also satisfies distinguishes nothing.

    Three outcomes, all recorded:

    * the predicate **fails for zeta** under the battery's own independent
      re-expression, the claim is refuted, with the disagreement escalated;
    * the predicate **holds for both**, the claim is not refuted, but it has no
      discriminating power, and this screen says so in the record it passes on;
    * the predicate **has no interface-level analogue**, ``inconclusive`` with
      reason ``dependency_unavailable``. Silence would let an unadjudicated
      structural claim reach ``survives``, which is exactly what the gate exists
      to prevent.
    """

    name = "counterexample_battery"
    cost = "expensive"
    checks = ("refutation",)
    version = "1.0"

    def apply(self, candidate: Candidate) -> ScreenResult:
        if candidate.kind is not CandidateKind.STRUCTURAL:
            return _passed(self.name, f"not applicable to {candidate.kind.value}")
        predicate = str(candidate.claim.get("predicate", ""))
        claim_fn = BATTERY_CLAIMS.get(predicate)
        if claim_fn is None:
            return _stopped(
                self.name,
                _inconclusive(
                    self.name,
                    self.version,
                    InconclusiveReason.DEPENDENCY_UNAVAILABLE,
                    "no zeta-like-interface analogue of this predicate exists, so "
                    "the counterexample battery cannot say whether the property "
                    "distinguishes zeta from a function that violates RH",
                    {"predicate": predicate[:200], "known": sorted(BATTERY_CLAIMS)[:1]},
                ),
                "predicate has no battery analogue",
            )
        from zeta.epstein import battery

        dps = _base_dps(candidate) + 5
        named = _NamedClaim(claim_fn, predicate)
        report = battery(named, dps=dps)
        if not report["riemann_zeta"]:
            return _stopped(
                self.name,
                _refuted(
                    self.name,
                    self.version,
                    witness={
                        "predicate": predicate[:200],
                        "battery_dps": dps,
                        "riemann_zeta": False,
                    },
                    defect=mp.mpf(1),
                    tolerance=mp.mpf("1e-30"),
                    effort=float(_base_dps(candidate)),
                    escalated_effort=float(dps),
                    escalated_defect=mp.mpf(1),
                    notes=(
                        "the battery's independent re-expression of the predicate "
                        "fails for zeta itself"
                    ),
                ),
                "predicate fails for zeta under the battery's own re-expression",
                effort=float(dps),
            )
        if report["distinguishes"]:
            return _passed(
                self.name,
                f"battery at dps={dps}: holds for zeta, fails for "
                "Davenport-Heilbronn, so the property discriminates",
                effort=float(dps),
            )
        return _passed(
            self.name,
            f"battery at dps={dps}: the Davenport-Heilbronn function satisfies "
            "this predicate too, so it distinguishes nothing and cannot be the "
            "load-bearing step of any argument about RH (docs/09 gate #3)",
            effort=float(dps),
        )


@dataclass(frozen=True, slots=True)
class _NamedClaim:
    """A claim function with a readable ``__name__`` for the battery's report."""

    fn: Callable[[Mapping[str, Any]], bool]
    label: str

    @property
    def __name__(self) -> str:  # noqa: A003 - the battery reads this attribute
        return self.label[:80]

    def __call__(self, iface: Mapping[str, Any]) -> bool:
        return self.fn(iface)


# ---------------------------------------------------------------------------
# The already-known catalogue and its detector
# ---------------------------------------------------------------------------

_LI_SUBJECT_RE: Final[re.Pattern[str]] = re.compile(r"^zeta\.li\.lambda_(\d+)$")


def _match_li_coefficient(candidate: Candidate, fact: KnownFact) -> FactMatch | None:
    """Match ``zeta.li.lambda_n`` for n >= 2 as an already-tabulated quantity.

    lambda_1 has its own entry with an explicit closed form and is registered
    first, so this never shadows it. The point of the rule is honesty about
    coverage: a catalogue that stops at n = 1 would report lambda_2 as a lead,
    which would be a defect in the catalogue and not a finding.
    """
    if candidate.kind is not CandidateKind.CONSTANT:
        return None
    hit = _LI_SUBJECT_RE.match(str(candidate.claim.get("subject", "")))
    if hit is None or int(hit.group(1)) < 2:
        return None
    return FactMatch(
        fact_id=fact.id,
        match_kind="statement",
        source=fact.source,
        canonical_form=fact.canonical_form,
        statement=fact.statement,
        detail={
            "matched_subject": str(candidate.claim.get("subject")),
            "n": int(hit.group(1)),
            "literature_status": fact.status,
        },
    )


_LEGENDRE_EF_LHS_RE: Final[re.Pattern[str]] = re.compile(
    r"^zeta\.weil\.explicit_formula\.zero_side\[legendre n=(\d+)\]$"
)
_LEGENDRE_MASS_LHS_RE: Final[re.Pattern[str]] = re.compile(
    r"^zeta\.weil\.legendre_interval_lambda_mass\[n=(\d+)\]$"
)


def _match_explicit_formula_instance(
    candidate: Candidate, fact: KnownFact
) -> FactMatch | None:
    """Match any zero-side = arithmetic-side agreement on a Legendre bump.

    The regex, not a fixed key list, because the interval index n is a free
    parameter of the generator: a catalogue that recognised n = 10 but
    reported n = 11 as a lead would be failing at exactly the coverage this
    matcher exists to provide.
    """
    if candidate.kind is not CandidateKind.RELATION:
        return None
    if str(candidate.claim.get("relation")) != "eq":
        return None
    hit = _LEGENDRE_EF_LHS_RE.match(str(candidate.claim.get("lhs", "")))
    if hit is None:
        return None
    return FactMatch(
        fact_id=fact.id,
        match_kind="statement",
        source=fact.source,
        canonical_form=fact.canonical_form,
        statement=fact.statement,
        detail={
            "matched_lhs": str(candidate.claim.get("lhs")),
            "n": int(hit.group(1)),
            "literature_status": fact.status,
        },
    )


def _match_legendre_interval_detection(
    candidate: Candidate, fact: KnownFact
) -> FactMatch | None:
    """Match a positive-Λ-mass claim for an interval inside the verified range.

    The range guard is the honest part: beyond (n+1)^2 <= 4e18 the statement
    stops being verified, and this matcher must decline rather than stretch a
    finite verification over an open conjecture.
    """
    if candidate.kind is not CandidateKind.RELATION:
        return None
    if str(candidate.claim.get("relation")) != "gt":
        return None
    if str(candidate.claim.get("rhs", "")).strip() != "0":
        return None
    hit = _LEGENDRE_MASS_LHS_RE.match(str(candidate.claim.get("lhs", "")))
    if hit is None:
        return None
    n = int(hit.group(1))
    if (n + 1) ** 2 > 4 * 10**18:
        return None
    return FactMatch(
        fact_id=fact.id,
        match_kind="statement",
        source=fact.source,
        canonical_form=fact.canonical_form,
        statement=fact.statement,
        detail={
            "matched_lhs": str(candidate.claim.get("lhs")),
            "n": n,
            "interval": [n * n, (n + 1) ** 2],
            "literature_status": fact.status,
        },
    )


ZETA_FACTS: Final[tuple[KnownFact, ...]] = (
    KnownFact(
        id="li-lambda-1-closed-form",
        statement="The first Li coefficient is 1 + gamma/2 - log(4 pi)/2.",
        canonical_form="lambda_1 = 1 + gamma/2 - log(4*pi)/2",
        source="Li 1997, J. Number Theory 65; Bombieri-Lagarias 1999; zeta.li.li_closed_form_lambda1",
        domain=DOMAIN_NAME,
        keys=("zeta.li.lambda_1",),
        value="0.023095708966121033814",
        tolerance="1e-18",
        tags=("li-criterion",),
    ),
    KnownFact(
        id="li-lambda-1-two-routes",
        statement=(
            "The Cauchy-integral route to lambda_1 and its closed form agree; the "
            "laboratory exposes the difference as a measured defect."
        ),
        canonical_form="li_coefficients(1, 'cauchy') = li_closed_form_lambda1",
        source="zeta.li docstring and tests/test_li.py",
        domain=DOMAIN_NAME,
        keys=(
            "zeta.li.li_coefficients(1, method='cauchy')",
            "zeta.li.li_closed_form_lambda1",
        ),
        tags=("li-criterion",),
    ),
    KnownFact(
        id="li-coefficients-tabulated",
        statement=(
            "The Li coefficients lambda_n are classical tabulated quantities: "
            "each is a polynomial in the Stieltjes constants and log 2pi, and "
            "numerical tables run far beyond the range this domain generates. "
            "Reporting lambda_2 or lambda_3 as unrecognised would be a "
            "catalogue failure, not a discovery."
        ),
        canonical_form="lambda_n = n-th Li coefficient",
        source=(
            "Li 1997, J. Number Theory 65; Bombieri and Lagarias 1999, "
            "J. Number Theory 77; Coffey 2004, J. Math. Anal. Appl. 288"
        ),
        domain=DOMAIN_NAME,
        matcher=lambda candidate, fact: _match_li_coefficient(candidate, fact),
        tags=("li-criterion",),
    ),
    KnownFact(
        id="xi-at-zero",
        statement="Xi(0) = xi(1/2) = 0.4971207781...",
        canonical_form="Xi(0) = 0.49712077818831410991",
        source="AGENTS.md ground-truth table; zeta.core.Xi",
        domain=DOMAIN_NAME,
        keys=("zeta.core.Xi_at_0",),
        value="0.49712077818831410991",
        tolerance="1e-18",
    ),
    KnownFact(
        id="jensen-gamma-zero",
        statement="The Jensen normalisation gives gamma(0) = 8 xi(1/2).",
        canonical_form="gamma(0) = 8*Xi(0) = 3.9769662255065128793",
        source="Griffin-Ono-Rolen-Zagier, PNAS 116 (2019); zeta.li.xi_taylor_coefficients",
        domain=DOMAIN_NAME,
        keys=("zeta.li.xi_taylor_gamma_0",),
        value="3.9769662255065128793",
        tolerance="1e-16",
    ),
    KnownFact(
        id="li-asymptotic-growth",
        statement=(
            "On RH, lambda_n ~ (n/2)(log n - log 2pi + gamma - 1) + 1; the "
            "remainder oscillates at size O(sqrt(n) log n)."
        ),
        canonical_form="lambda_n ~ li_asymptotic(n)",
        source="Bombieri-Lagarias 1999; Voros 2006; zeta.li.li_asymptotic",
        domain=DOMAIN_NAME,
        keys=("zeta.li.lambda_n", "zeta.li.li_asymptotic"),
        tags=("asymptotic",),
    ),
    KnownFact(
        id="riemann-von-mangoldt",
        statement="N(T) = (T/2pi) log(T/2pi) - T/2pi + 7/8 + S(T) + O(1/T).",
        canonical_form="N(T) ~ riemann_von_mangoldt(T)",
        source="Riemann 1859; von Mangoldt 1905; zeta.zeros.riemann_von_mangoldt",
        domain=DOMAIN_NAME,
        keys=("zeta.zeros.N_of_T", "zeta.zeros.riemann_von_mangoldt"),
        tags=("asymptotic",),
    ),
    KnownFact(
        id="mertens-conjecture-false",
        statement=(
            "M(x)/sqrt(x) is unbounded: the Mertens conjecture is false, by a "
            "non-constructive argument."
        ),
        canonical_form="limsup |M(x)|/sqrt(x) = infinity",
        source="Odlyzko and te Riele 1985, J. reine angew. Math. 357",
        domain=DOMAIN_NAME,
        keys=("zeta.criteria.max_abs_mertens_ratio",),
        tags=("mertens",),
    ),
    KnownFact(
        id="mertens-growth-exponent",
        statement=(
            "The running maximum of |M(x)| grows roughly like sqrt(x) over "
            "computed ranges; on RH the true bound is x^(1/2+epsilon)."
        ),
        canonical_form="max_{y<=x} |M(y)| ~ x^(1/2)",
        source="Odlyzko and te Riele 1985; zeta.criteria.mertens_facts",
        domain=DOMAIN_NAME,
        keys=("zeta.criteria.running_max_abs_mertens", "x"),
        tags=("asymptotic", "mertens"),
    ),
    KnownFact(
        id="montgomery-odlyzko-gue",
        statement=(
            "The unfolded zero spacings follow GUE statistics far better than "
            "Poisson statistics."
        ),
        canonical_form="KS(spacings, GUE) << KS(spacings, Poisson)",
        source="Montgomery 1973; Odlyzko 1987; zeta.statistics.level_repulsion_report",
        domain=DOMAIN_NAME,
        keys=(
            "KS(unfolded spacings, GUE Gaudin law)",
            "KS(unfolded spacings, Poisson law)",
        ),
        tags=("random-matrix",),
    ),
    KnownFact(
        id="gue-spacing-variance",
        statement="The exact GUE nearest-neighbour spacing variance is 0.17999...",
        canonical_form="Var_GUE(s) = 0.17999387769184483",
        source="Gaudin 1961; Mehta, Random Matrices; zeta.statistics.gue_spacing_exact",
        domain=DOMAIN_NAME,
        keys=("zeta.statistics.gue_spacing_variance",),
        value="0.17999387769184483",
        tolerance="1e-12",
        tags=("random-matrix",),
    ),
    KnownFact(
        id="hasse-bound",
        statement="For an elliptic curve over F_p, |a_p| <= 2 sqrt(p).",
        canonical_form="|a_p| <= 2 sqrt(p)",
        source="Hasse 1936; zeta.finitefield.hasse_check",
        domain=DOMAIN_NAME,
        keys=("zeta.finitefield.max_hasse_ratio",),
        tags=("finite-field",),
    ),
    KnownFact(
        id="birch-second-moment",
        statement=(
            "The sum of a_p^2 over all curves y^2=x^3+ax+b mod p has an exact "
            "closed form."
        ),
        canonical_form="sum a_p^2 = p^2 (p-1)",
        source="Birch 1968, J. London Math. Soc. 43; zeta.finitefield.sato_tate_histogram",
        domain=DOMAIN_NAME,
        keys=("Birch's closed form for the same sum",),
        tags=("finite-field",),
    ),
    KnownFact(
        id="deuring-waterhouse-traces",
        statement=(
            "Every integer in the Hasse interval occurs as the trace of some "
            "elliptic curve over F_p."
        ),
        canonical_form="{a_p} = [-2 sqrt p, 2 sqrt p] cap Z",
        source="Deuring 1941; Waterhouse 1969, Ann. Sci. ENS 2",
        domain=DOMAIN_NAME,
        keys=("number of integers in the Hasse interval for p=503",),
        tags=("finite-field",),
    ),
    KnownFact(
        id="gorz-jensen-hyperbolicity",
        statement=(
            "For each degree d, the Jensen polynomials J^(d,n) of Xi are "
            "hyperbolic for all sufficiently large n."
        ),
        canonical_form="J^(d,n) hyperbolic for n >= N(d)",
        source="Griffin, Ono, Rolen and Zagier, PNAS 116 (2019) 11103-11110",
        domain=DOMAIN_NAME,
        keys=("Jensen polynomials J^(d,n) of 8*xi(1/2+z)", PREDICATE_TURAN),
        tags=("jensen",),
    ),
    KnownFact(
        id="riemann-functional-equation",
        statement="The completed zeta function satisfies xi(s) = xi(1-s).",
        canonical_form="xi(s) = xi(1-s)",
        source="Riemann 1859; zeta.core.functional_equation_defect",
        domain=DOMAIN_NAME,
        keys=(
            "asymmetric sample points of the completed function",
            PREDICATE_FUNCTIONAL_EQUATION,
        ),
        tags=("functional-equation",),
        status="theorem",
    ),
    # -- entries the historical-validation suite is measured against --------
    # ``discovery/historical_cases.py`` replays four settled claims and one
    # constructed negative control through this domain. A catalogue that did
    # not carry these would report the prime number theorem as a lead, which
    # would be a gap in the catalogue and not a finding. Their ``status``
    # values are what let a record distinguish "already known and proved" from
    # "already known and still open" from "already known to be false".
    KnownFact(
        # ``knownness.GENERAL_FACTS`` already carries a ``prime-number-theorem``
        # entry keyed on the English name; this one is keyed on the laboratory
        # symbols and states the Li(x) form the block counts actually support,
        # so the two ids must differ.
        id="prime-number-theorem-li-form",
        statement=(
            "pi(x) is asymptotic to Li(x). Conjectured from tables of prime "
            "counts by Gauss (1792/3, stated in his 1849 letter to Encke) and "
            "independently by Legendre; proved in 1896 by Hadamard and by de la "
            "Vallee Poussin. Li(x) is the better approximation of the two "
            "classical ones, which is exactly what the block counts show."
        ),
        canonical_form="pi(x) / Li(x) -> 1 as x -> infinity",
        source=(
            "Gauss, letter to Encke, 24 December 1849; Hadamard 1896, Bull. Soc. "
            "Math. France 24, 199-220; de la Vallee Poussin 1896, Ann. Soc. Sci. "
            "Bruxelles 20; zeta.explicit.pi_true and zeta.explicit.Li"
        ),
        domain=DOMAIN_NAME,
        keys=("zeta.explicit.pi_true", "zeta.explicit.Li", "+inf"),
        tags=("prime-counting", "historical"),
        status="theorem",
    ),
    KnownFact(
        id="montgomery-pair-correlation-conjecture",
        statement=(
            "Montgomery's pair-correlation conjecture: the pair correlation of "
            "the unfolded ordinates approaches 1 - (sin(pi r)/(pi r))^2, the GUE "
            "two-point form. Montgomery (1973) settled it only for test "
            "functions whose Fourier transform is supported in (-1, 1); Odlyzko's "
            "computations near the 10^20-th ordinate match it to high accuracy. "
            "In general it remains a conjecture, and no computation can close it."
        ),
        canonical_form="R_2(r) = 1 - (sin(pi r)/(pi r))^2",
        source=(
            "Montgomery 1973, Proc. Sympos. Pure Math. 24, 181-193; Odlyzko 1987, "
            "Math. Comp. 48, 273-308; zeta.statistics.montgomery_prediction"
        ),
        domain=DOMAIN_NAME,
        keys=(
            "zeta.statistics.pair_correlation",
            "zeta.statistics.montgomery_prediction",
            "dist_match",
        ),
        tags=("random-matrix", "historical"),
        status="conjecture",
    ),
    KnownFact(
        id="mertens-conjecture-disproved",
        statement=(
            "Mertens' conjecture that |M(x)| < sqrt(x) for all x > 1 is false. "
            "Odlyzko and te Riele (1985) showed limsup M(x)/sqrt(x) > 1.06 and "
            "liminf M(x)/sqrt(x) < -1.009 by a non-constructive argument. No "
            "counterexample is exhibited, and none is expected below 10^14, so "
            "no finite scan supports the conjecture: the scan and the disproof "
            "are consistent."
        ),
        canonical_form="limsup |M(x)|/sqrt(x) > 1, so |M(x)| < sqrt(x) fails",
        source=(
            "Mertens 1897, Sitzungsber. Akad. Wiss. Wien 106; Odlyzko and te "
            "Riele 1985, J. reine angew. Math. 357, 138-160; Kotnik and te Riele "
            "2006, Lecture Notes in Comput. Sci. 4076"
        ),
        domain=DOMAIN_NAME,
        aliases=("|M(x)| < sqrt(x)",),
        tags=("mertens", "historical"),
        status="disproved",
    ),
    KnownFact(
        id="li-criterion-equivalence",
        statement=(
            "Li's criterion: lambda_n >= 0 for every n >= 1 exactly when every "
            "non-trivial zero of zeta lies on the line Re(s) = 1/2. The "
            "positivity is therefore equivalent to a question nobody has "
            "settled, and computing lambda_n for finitely many n decides nothing "
            "in either direction."
        ),
        canonical_form="lambda_n >= 0 for all n >= 1 <=> the zeros lie on Re(s)=1/2",
        source=(
            "Li 1997, J. Number Theory 65, 325-333; Bombieri and Lagarias 1999, "
            "J. Number Theory 77, 274-287; docs/12; zeta.li.li_coefficients"
        ),
        domain=DOMAIN_NAME,
        aliases=("lambda_n >= 0",),
        tags=("li-criterion", "historical"),
        status="equivalent_to_open_problem",
    ),
    KnownFact(
        id="riemann-weil-explicit-formula",
        statement=(
            "The Riemann-Weil explicit formula: for an admissible test pair "
            "(h, g), the sum of h over the non-trivial zeros equals the pole, "
            "archimedean and prime terms. Numerical agreement of the two sides "
            "for any particular test function is an instance of a theorem, not "
            "an observation."
        ),
        canonical_form=(
            "sum_rho h(gamma_rho) = h(i/2) + h(-i/2) + arch(h) "
            "- 2 sum_n Lambda(n) n^(-1/2) g(log n)"
        ),
        source=(
            "Weil 1952, Comm. Sem. Math. Lund; Iwaniec and Kowalski, Analytic "
            "Number Theory, Thm 5.12; zeta.weil.explicit_formula_sides and "
            "tests/test_weil.py"
        ),
        domain=DOMAIN_NAME,
        matcher=lambda candidate, fact: _match_explicit_formula_instance(
            candidate, fact
        ),
        tags=("explicit-formula", "theorem"),
        status="theorem",
    ),
    KnownFact(
        id="legendre-interval-primes-finite-range",
        statement=(
            "Legendre's conjecture, a prime between n^2 and (n+1)^2 for every "
            "n, is open in general, but for every n with (n+1)^2 <= 4e18 the "
            "interval provably contains a prime: direct enumeration for small "
            "n, and for 2n+1 > 1476 the tabulated maximal prime gaps below "
            "4e18. Detecting primes in such an interval, by any instrument, "
            "reproduces a verified fact."
        ),
        canonical_form="pi((n+1)^2) - pi(n^2) >= 1 for all n with (n+1)^2 <= 4e18",
        source=(
            "Oliveira e Silva, Herzog and Pardi 2014, Math. Comp. 83, 2033-2060 "
            "(maximal prime gaps to 4e18); OEIS A014085"
        ),
        domain=DOMAIN_NAME,
        matcher=lambda candidate, fact: _match_legendre_interval_detection(
            candidate, fact
        ),
        tags=("primes", "legendre"),
        status="established",
    ),
)


def build_fact_registry() -> KnownFactRegistry:
    """This laboratory's catalogue, then general mathematics.

    Order matters: entries are tried in registration order, so the domain's own
    precise statement is consulted before a general one that might match the
    same number for a vaguer reason.
    """
    registry = KnownFactRegistry(ZETA_FACTS)
    registry.register_all(GENERAL_FACTS)
    return registry


FACT_REGISTRY: Final[KnownFactRegistry] = build_fact_registry()


class CatalogueDetector(BaseKnownnessDetector):
    """The already-known gate for this laboratory.

    Consults the domain catalogue first (cheap and citable), then hands
    ``constant`` candidates to the integer-relation identifier in
    :mod:`ontology.knownness`, supplying the candidate's own re-derivation
    route as the value provider so the escalation that makes an identification
    trustworthy is a real one.

    Offline, "not recognised" is never rendered as "new". There is no code path
    here that concludes novelty.
    """

    name = "zeta_catalogue"
    version = "1.0"

    def check(self, candidate: Candidate) -> Verdict | None:
        route = _route_of(candidate)
        provider = None
        if (
            route is not None
            and route.escalates
            and candidate.kind is CandidateKind.CONSTANT
        ):
            params = _route_params(candidate)

            def provider(dps: int, _route: Route = route, _p: Mapping[str, Any] = params) -> Any:
                return mp.mpf(_route.compute(_p, int(dps)))

        report = screen_known(
            candidate,
            facts=FACT_REGISTRY,
            value_provider=provider,
            identify=candidate.kind is CandidateKind.CONSTANT,
            decided_by=f"ontology.domains.zeta_domain.{self.name}",
        )
        return report.verdict


# ---------------------------------------------------------------------------
# The domain
# ---------------------------------------------------------------------------


def build_domain() -> Domain:
    """Assemble the domain. Called once at import; re-callable in tests."""
    return Domain(
        name=DOMAIN_NAME,
        version=DOMAIN_VERSION,
        description=(
            "The Riemann zeta laboratory: seven generators mining computed objects "
            "for candidate observations, six screens trying to kill them, and a "
            "catalogue of what is already established. Nothing this domain "
            "produces is evidence for the Riemann Hypothesis."
        ),
        generators=(
            ConstantsGenerator(),
            AsymptoticsGenerator(),
            RelationsGenerator(),
            ExtremalGenerator(),
            FiniteFieldGenerator(),
            StructuralGenerator(),
            LegendreWeilGenerator(),
        ),
        screens=(
            NumericSanityScreen(),
            PrecisionStabilityScreen(),
            TrivialityScreen(),
            HighPrecisionScreen(),
            IndependentMethodScreen(),
            CounterexampleBatteryScreen(),
        ),
        detectors=(CatalogueDetector(),),
    )


DOMAIN: Final[Domain] = register_domain(build_domain(), replace=True)
