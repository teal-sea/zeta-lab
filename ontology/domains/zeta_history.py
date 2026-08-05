"""discovery.domains.zeta_history — settled claims, replayed against the funnel.

The harness lives in :mod:`discovery.historical_cases` and knows nothing about
the subject. This file is the subject-matter half: it turns four famous claims,
plus one constructed negative control, into candidates the pipeline in
:mod:`discovery.domains.zeta_domain` can actually process, and states the answer
history has already given for each.

Why the file is separate from ``zeta_domain``
---------------------------------------------
The seam test in ``tests/test_discovery_zeta_domain.py`` globs ``discovery/*.py``
and refuses subject-matter vocabulary in every module outside ``domains/``. So
the *harness* is domain-agnostic by construction (it has to be, or the existing
suite goes red), and everything that names the laboratory lives here, inside
``domains/``, where naming it is the whole job. ``zeta_domain`` stays the module
that defines the pipeline; this one only feeds it questions whose answers are
already in the literature.

The five cases
--------------
======================  ==========  ====================================
``gauss_prime_counts``  1792, true  pi(x) ~ Li(x); proved 1896
``montgomery_pair``     1973, true  the 1 - (sin(pi r)/(pi r))^2 form; open
``mertens``             1897, FALSE |M(x)| < sqrt(x); disproved 1985
``li_criterion``        1997, open  lambda_n >= 0 <=> an unsettled question
``pslq_coincidence``    ---, false  a constructed low-precision coincidence
======================  ==========  ====================================

Honest scope. Nothing here is evidence for the Riemann Hypothesis, and the
Mertens case is in the suite precisely because a century of finite computation
was not evidence for *its* conjecture either. The two structural cases are
recorded as "no violation was found in the range examined"; that is the
strongest sentence any of them supports.

What each candidate is made of
------------------------------
Every observation is computed from the laboratory, not typed in:

* ``gauss_prime_counts`` — ``zeta.explicit.pi_true`` against
  ``zeta.explicit.Li``, fitted in two windows over 10^3..10^6, which is the
  range of the tables Gauss actually worked from;
* ``montgomery_pair`` — ``zeta.statistics.pair_correlation`` of 2000 unfolded
  ordinates against ``zeta.statistics.montgomery_prediction``;
* ``mertens`` — ``zeta.criteria.mertens_array`` up to 10^6, with a seeded
  random +-1 walk as the control the predicate fails on;
* ``li_criterion`` — ``zeta.li.li_coefficients`` for n <= 40, with a symmetric
  quadruple of zeros placed *off* the line as the control;
* ``pslq_coincidence`` — ``mpmath.pslq`` run at ten digits against
  ``zeta.core.Xi(1)``, which finds a six-term integer relation that reproduces
  the value to twelve digits and is wrong at the thirteenth.
"""

from __future__ import annotations

import datetime as _dt
import math
import re
from collections.abc import Mapping, Sequence
from typing import Any, Final

import numpy as np
from mpmath import mp

from discovery.historical_cases import (
    HistoricalCase,
    HistoricalOutcome,
    register_case,
)
from discovery.schema import (
    Candidate,
    CandidateKind,
    Precision,
    capture_provenance,
    kind_reasons,
)

__all__ = [
    "GENERATOR",
    "GENERATOR_VERSION",
    "SEED",
    "GAUSS_WINDOWS",
    "MERTENS_LIMIT",
    "MERTENS_CHECKPOINTS",
    "LI_N_MAX",
    "LI_CONTROL_ZERO",
    "COINCIDENCE_DIGITS",
    "COINCIDENCE_BASIS",
    "gauss_prime_count_windows",
    "pslq_coincidence",
    "build_gauss_prime_counting",
    "build_montgomery_pair_correlation",
    "build_mertens_conjecture",
    "build_li_criterion",
    "build_low_precision_coincidence",
    "build_honest_twin",
    "HISTORICAL_CASES",
    "register_all",
    "REGISTERED",
]

#: The provenance name every replayed observation carries. It is deliberately
#: not one of the six production generators: a validation replay must never be
#: mixed into a real generator's conversion rate.
GENERATOR: Final[str] = "zeta_history"
GENERATOR_VERSION: Final[str] = "1.0"

#: Everything here is deterministic given this seed.
SEED: Final[int] = 20260803

#: Extra digits every comparison is carried out at, for the same reason as in
#: ``zeta_domain``: at the ambient precision two values agreeing to 25 digits
#: differ by exactly zero, and a comparison that cannot fail is not a test.
GUARD_DIGITS: Final[int] = 25

_NUMERIC_RE: Final[re.Pattern[str]] = re.compile(
    r"^[+-]?(?:\d+\.?\d*|\.\d+)(?:[eE][+-]?\d+)?$"
)


def _utc_now() -> str:
    return _dt.datetime.now(_dt.UTC).replace(microsecond=0).isoformat()


def _num(value: Any, digits: int = 17) -> str:
    """A measured number as decimal text the schema accepts."""
    with mp.workdps(max(int(digits) + 10, 20)):
        text = mp.nstr(mp.mpf(value), int(digits), strip_zeros=True)
    text = text.strip()
    if not _NUMERIC_RE.match(text):
        raise ValueError(f"{value!r} did not render as a decimal literal: {text!r}")
    return text


def _f(value: Any) -> float:
    """A plain Python float; ``numpy`` scalars must not reach the schema."""
    out = float(value)
    if not math.isfinite(out):
        raise ValueError(f"non-finite number cannot be recorded: {value!r}")
    return out


def _i(value: Any) -> int:
    return int(value)


def _provenance(
    *,
    lab_object: str,
    parameters: Mapping[str, Any],
    precision: Precision,
    stochastic: bool = False,
):
    import mpmath
    import numpy

    return capture_provenance(
        generator=GENERATOR,
        generator_version=GENERATOR_VERSION,
        lab_object=lab_object,
        parameters=dict(parameters),
        precision=precision,
        seed=SEED,
        stochastic=stochastic,
        runtime={"mpmath": mpmath.__version__, "numpy": numpy.__version__},
    )


def _candidate(kind: CandidateKind, claim, evidence, provenance, label: str) -> Candidate:
    """Build and check. A malformed historical case is a defect in this file.

    The pipeline would record it as ``invalid`` and the suite would report a
    misclassification, which would be the wrong diagnosis: the ontology would
    not have failed, the case author would have.
    """
    reasons = kind_reasons(kind, claim, evidence)
    if reasons:
        raise ValueError(f"{label}: the schema refuses this payload: {reasons}")
    return Candidate(
        kind=kind,
        claim=claim,
        evidence=evidence,
        provenance=provenance,
        label=label,
    )


# ---------------------------------------------------------------------------
# 1. Gauss, 1792: pi(x) ~ Li(x)
# ---------------------------------------------------------------------------

#: The two fitting windows, in the range of the tables Gauss worked from. The
#: total span is 10^3, far above the schema's minimum of 4 — which is the point:
#: the schema refuses a rate fitted over a range that never doubles, and Gauss's
#: evidence comfortably clears that bar. Each window is a set of block
#: boundaries, so the fit is over counts he could have written down.
GAUSS_WINDOWS: Final[tuple[tuple[int, ...], ...]] = (
    (1_000, 2_000, 3_000, 4_000, 5_000, 7_000, 10_000),
    (10_000, 20_000, 30_000, 50_000, 70_000, 100_000, 200_000, 500_000, 1_000_000),
)


def _loglog_exponent(xs: Sequence[float], ys: Sequence[float]) -> float:
    lx = np.log(np.asarray(xs, dtype=float))
    ly = np.log(np.asarray(ys, dtype=float))
    design = np.vstack([lx, np.ones_like(lx)]).T
    solution, *_ = np.linalg.lstsq(design, ly, rcond=None)
    return _f(solution[0])


def gauss_prime_count_windows() -> tuple[dict[str, Any], ...]:
    """The fitted windows, with the raw block counts kept in the record.

    The fitted quantity is the slope of ``log pi(x)`` against ``log Li(x)``. It
    is 1 exactly when the two are asymptotically proportional, which is the
    claim; fitting against ``log x`` instead gives 0.92 over the same range, so
    the statistic discriminates between the two classical approximations rather
    than accepting either.
    """
    from zeta.explicit import Li, pi_true

    out: list[dict[str, Any]] = []
    for block in GAUSS_WINDOWS:
        counts = [_i(pi_true(x)) for x in block]
        approx = [_f(Li(x)) for x in block]
        out.append(
            {
                "index_min": _f(block[0]),
                "index_max": _f(block[-1]),
                "n_points": len(block),
                "exponent": _loglog_exponent(approx, counts),
                "x": [_i(x) for x in block],
                "pi_x": counts,
                "Li_x": [_f(round(a, 3)) for a in approx],
                "ratio": [_f(round(c / a, 6)) for c, a in zip(counts, approx)],
            }
        )
    return tuple(out)


def build_gauss_prime_counting() -> Candidate:
    """pi(x) ~ Li(x), as an asymptotic candidate built from block counts."""
    windows = gauss_prime_count_windows()
    claim = {
        "subject": "zeta.explicit.pi_true",
        "index": "x",
        "limit": "+inf",
        "scale": "zeta.explicit.Li",
        "exponent": 1.0,
    }
    evidence = {
        "windows": [dict(w) for w in windows],
        # 0.03 admits the measured drift of 0.019 in the lower window and
        # refuses the 0.92 that fitting against x alone produces. A tolerance
        # that could not fail would be worse than no tolerance at all.
        "tolerance": 0.03,
        "fit": "least-squares slope of log(pi(x)) against log(Li(x))",
        "range": "10^3 <= x <= 10^6, the range of the tables available in 1792",
        "note": (
            "A finite fit. It measures that the two functions track each other "
            "over six orders of magnitude; it does not establish a limit."
        ),
    }
    provenance = _provenance(
        lab_object="zeta.explicit.pi_true",
        parameters={"x_min": GAUSS_WINDOWS[0][0], "x_max": GAUSS_WINDOWS[-1][-1]},
        # Exact integer prime counts and a float64 logarithmic integral.
        precision=Precision(kind="float64"),
    )
    return _candidate(
        CandidateKind.ASYMPTOTIC,
        claim,
        evidence,
        provenance,
        label="historical: prime counts against the offset logarithmic integral",
    )


# ---------------------------------------------------------------------------
# 2. Montgomery, 1973: the pair-correlation form
# ---------------------------------------------------------------------------

#: How many ordinates the empirical pair correlation is built from, and the
#: histogram used. Both are recorded because both change the statistic.
MONTGOMERY_N_ZEROS: Final[int] = 2000
MONTGOMERY_R_MAX: Final[float] = 3.0
MONTGOMERY_BINS: Final[int] = 30


def _pair_correlation_fit() -> dict[str, Any]:
    """RMS deviation from the predicted form, and from the uncorrelated null.

    The defect is the *ratio* of the two, which is dimensionless and does not
    have to be calibrated against a sample size. The comparison is what makes
    the number falsifiable: a flat empirical curve would score 1.0.
    """
    from zeta.statistics import (
        montgomery_prediction,
        pair_correlation,
        zero_ordinates,
    )

    gammas = zero_ordinates(n=MONTGOMERY_N_ZEROS)
    r, empirical = pair_correlation(
        gammas, r_max=MONTGOMERY_R_MAX, bins=MONTGOMERY_BINS
    )
    predicted = montgomery_prediction(r)
    rms_model = _f(np.sqrt(np.mean((empirical - predicted) ** 2)))
    rms_null = _f(np.sqrt(np.mean((empirical - 1.0) ** 2)))
    return {
        "rms_vs_predicted": rms_model,
        "rms_vs_uncorrelated": rms_null,
        "ratio": _f(rms_model / rms_null),
        "r": [_f(round(v, 4)) for v in r],
        "empirical": [_f(round(v, 5)) for v in empirical],
        "predicted": [_f(round(v, 5)) for v in predicted],
        "max_abs_deviation": _f(np.max(np.abs(empirical - predicted))),
    }


def build_montgomery_pair_correlation() -> Candidate:
    """The empirical pair correlation against 1 - (sin(pi r)/(pi r))^2."""
    fit = _pair_correlation_fit()
    claim = {
        "lhs": "zeta.statistics.pair_correlation",
        "rhs": "zeta.statistics.montgomery_prediction",
        "relation": "dist_match",
    }
    evidence = {
        "defect": fit["ratio"],
        # Half. Stated in advance and genuinely refutable: an empirical curve
        # no closer to the predicted form than to "no correlation at all"
        # scores 1.0 and is refused outright by the schema.
        "tolerance": 0.5,
        "defect_definition": (
            "RMS deviation from the predicted form divided by the RMS deviation "
            "from the uncorrelated null R_2 = 1; below 1 means the predicted "
            "form is the better description, and the tolerance demands twice as "
            "good"
        ),
        "n_zeros": MONTGOMERY_N_ZEROS,
        "r_max": MONTGOMERY_R_MAX,
        "bins": MONTGOMERY_BINS,
        "rms_vs_predicted": fit["rms_vs_predicted"],
        "rms_vs_uncorrelated": fit["rms_vs_uncorrelated"],
        "max_abs_deviation": fit["max_abs_deviation"],
        "r": fit["r"],
        "empirical": fit["empirical"],
        "predicted": fit["predicted"],
        "note": (
            "A finite sample of low-lying ordinates. The agreement is a "
            "measurement of 2000 ordinates, not a statement about the limit."
        ),
    }
    provenance = _provenance(
        lab_object="zeta.statistics.pair_correlation",
        parameters={
            "n_zeros": MONTGOMERY_N_ZEROS,
            "r_max": MONTGOMERY_R_MAX,
            "bins": MONTGOMERY_BINS,
        },
        precision=Precision(kind="float64"),
    )
    return _candidate(
        CandidateKind.RELATION,
        claim,
        evidence,
        provenance,
        label="historical: pair correlation of the unfolded ordinates",
    )


# ---------------------------------------------------------------------------
# 3. Mertens, 1897: |M(x)| < sqrt(x)
# ---------------------------------------------------------------------------

MERTENS_LIMIT: Final[int] = 1_000_000

#: The recorded witnesses. The scan is exhaustive over ``2 <= x <= 10^6``; these
#: are the members written into the record, because the schema requires
#: ``n_checked == len(witnesses)`` and a million witnesses is not a record, it
#: is a data set. The exhaustive counts sit beside them in the evidence.
MERTENS_CHECKPOINTS: Final[tuple[int, ...]] = (
    2, 5, 10, 100, 1_000, 10_000, 50_000, 100_000, 200_000, 500_000, 750_000,
    1_000_000,
)

#: How many independent random +-1 walks are run as controls. Each one is a
#: sequence with the same square-root scale and no multiplicative structure, and
#: every one of them violates the predicate inside the same range.
MERTENS_CONTROLS: Final[int] = 3


def _mertens_scan() -> dict[str, Any]:
    from zeta.criteria import mertens_array

    values = mertens_array(MERTENS_LIMIT)
    x = np.arange(MERTENS_LIMIT + 1, dtype=float)
    x[0] = 1.0
    ratio = np.abs(values) / np.sqrt(x)
    tail = ratio[2:]
    argmax = int(np.argmax(tail)) + 2
    violations = np.nonzero(tail >= 1.0)[0]
    return {
        "M": values,
        "ratio": ratio,
        "max_ratio": _f(tail.max()),
        "argmax": argmax,
        "n_violations": _i(violations.size),
        "first_violation": (_i(violations[0]) + 2 if violations.size else None),
    }


def _random_walk_control(seed: int) -> dict[str, Any]:
    """A +-1 walk of the same length: same scale, no multiplicative structure.

    This is the control the schema demands — a family member the predicate
    *fails* on. It is also the reason nobody should have believed the
    conjecture: a square-root-scale sum with independent signs exceeds sqrt(x)
    somewhere in a million steps essentially always, and the law of the iterated
    logarithm says the excursions grow without bound.
    """
    rng = np.random.default_rng(seed)
    walk = np.cumsum(rng.choice([-1.0, 1.0], size=MERTENS_LIMIT))
    x = np.arange(1, MERTENS_LIMIT + 1, dtype=float)
    ratio = np.abs(walk) / np.sqrt(x)
    tail = ratio[1:]  # x >= 2, matching the predicate's range
    exceed = np.nonzero(tail >= 1.0)[0]
    return {
        "id": f"random +-1 walk of length 10^6, seed {seed}",
        "satisfied": bool(exceed.size == 0),
        "max_ratio": _f(tail.max()),
        "n_exceeding": _i(exceed.size),
        "first_x_exceeding": (_i(exceed[0]) + 2 if exceed.size else None),
    }


def build_mertens_conjecture() -> Candidate:
    """|M(x)| < sqrt(x) over the range a computation can reach.

    The claim recorded is exactly what the computation supports: no violation
    was found for 2 <= x <= 10^6. That is not the Mertens conjecture, which is a
    statement about every x, and the record must not be read as one.
    """
    scan = _mertens_scan()
    witnesses = [
        {
            "x": _i(x),
            "M": _i(scan["M"][x]),
            "ratio": _f(round(float(scan["ratio"][x]), 6)),
            "satisfied": bool(abs(float(scan["M"][x])) < math.sqrt(x)),
        }
        for x in MERTENS_CHECKPOINTS
    ]
    controls = [_random_walk_control(SEED + k) for k in range(MERTENS_CONTROLS)]
    claim = {
        "family": f"the integers 2 <= x <= {MERTENS_LIMIT}",
        "predicate": "|M(x)| < sqrt(x)",
        "scope": (
            f"2 <= x <= {MERTENS_LIMIT}, M(x) = sum_{{n<=x}} mu(n) from "
            "zeta.criteria.mertens_array (exact integer arithmetic)"
        ),
    }
    evidence = {
        "witnesses": witnesses,
        "n_checked": len(witnesses),
        "n_satisfied": sum(1 for w in witnesses if w["satisfied"]),
        "controls": controls,
        # The exhaustive scan, recorded beside the witnesses because the schema
        # ties ``n_checked`` to the number of witnesses written down.
        "n_scanned": MERTENS_LIMIT - 1,
        "n_violations_in_range": scan["n_violations"],
        "max_ratio": scan["max_ratio"],
        "argmax_x": scan["argmax"],
        "first_violation": scan["first_violation"],
        "note": (
            "No violation was found for 2 <= x <= 10^6. That is a statement "
            "about the range examined and about nothing else: the smallest "
            "counterexample is not expected below 10^14, so a scan of this size "
            "cannot distinguish a true universal claim from a false one."
        ),
    }
    provenance = _provenance(
        lab_object="zeta.criteria.mertens_array",
        parameters={"limit": MERTENS_LIMIT, "controls": MERTENS_CONTROLS},
        precision=Precision(kind="exact"),
        stochastic=True,
    )
    return _candidate(
        CandidateKind.STRUCTURAL,
        claim,
        evidence,
        provenance,
        label="historical: no violation of |M(x)| < sqrt(x) below 10^6",
    )


# ---------------------------------------------------------------------------
# 4. Li, 1997: lambda_n >= 0
# ---------------------------------------------------------------------------

LI_N_MAX: Final[int] = 40
LI_DPS: Final[int] = 25

#: The control: a functional-equation-symmetric quadruple with a zero off the
#: line. ``lambda_n`` for a function with these zeros alone goes negative inside
#: the same range of n, so the predicate is not one that everything satisfies.
LI_CONTROL_ZERO: Final[tuple[str, str]] = ("0.6", "2.0")


def _li_from_zeros(zeros: Sequence[Any], n: int) -> Any:
    """lambda_n = sum_rho [1 - (1 - 1/rho)^n], the Li-coefficient formula."""
    return mp.re(sum(1 - (1 - 1 / z) ** n for z in zeros))


def _li_controls() -> tuple[dict[str, Any], ...]:
    with mp.workdps(LI_DPS + GUARD_DIGITS):
        beta, gamma = mp.mpf(LI_CONTROL_ZERO[0]), mp.mpf(LI_CONTROL_ZERO[1])
        off = [
            beta + 1j * gamma,
            beta - 1j * gamma,
            1 - beta + 1j * gamma,
            1 - beta - 1j * gamma,
        ]
        on = [mp.mpf("0.5") + 1j * gamma, mp.mpf("0.5") - 1j * gamma]
        off_values = [_li_from_zeros(off, n) for n in range(1, LI_N_MAX + 1)]
        on_values = [_li_from_zeros(on, n) for n in range(1, LI_N_MAX + 1)]
        first_negative = next(
            (n for n, v in enumerate(off_values, 1) if v < 0), None
        )
    return (
        {
            "id": (
                f"a symmetric quadruple with a zero off the line at "
                f"{LI_CONTROL_ZERO[0]} +- {LI_CONTROL_ZERO[1]}i"
            ),
            "satisfied": bool(first_negative is None),
            "first_negative_n": (None if first_negative is None else _i(first_negative)),
            "min_value": _num(min(off_values), 8),
            "why": (
                "the predicate fails as soon as a zero leaves the line, which is "
                "what makes it a discriminating predicate rather than an "
                "identity everything satisfies"
            ),
        },
        {
            "id": f"a single pair on the line at 0.5 +- {LI_CONTROL_ZERO[1]}i",
            "satisfied": bool(min(on_values) >= 0),
            "min_value": _num(min(on_values), 8),
            "why": "a positive control: the predicate is not trivially false",
        },
    )


def build_li_criterion() -> Candidate:
    """lambda_n >= 0 over the range a computation can reach.

    The claim recorded is the finite one: the first forty coefficients are
    non-negative. Li's criterion says the infinite version is *equivalent* to a
    question nobody has settled, so no value of ``LI_N_MAX`` would turn this
    into evidence either way, and the catalogue entry says so.
    """
    from zeta.li import li_coefficients

    lam = li_coefficients(LI_N_MAX, method="cauchy", dps=LI_DPS, radius="0.5")
    witnesses = [
        {"n": _i(n), "lambda_n": _num(v, 12), "satisfied": bool(v >= 0)}
        for n, v in enumerate(lam, 1)
    ]
    controls = _li_controls()
    claim = {
        "family": "the Li coefficients lambda_n of 8*xi(1/2+z)",
        "predicate": "lambda_n >= 0",
        "scope": (
            f"1 <= n <= {LI_N_MAX}, by the Cauchy-integral route at dps={LI_DPS}"
        ),
    }
    evidence = {
        "witnesses": witnesses,
        "n_checked": len(witnesses),
        "n_satisfied": sum(1 for w in witnesses if w["satisfied"]),
        "controls": [dict(c) for c in controls],
        "min_lambda": _num(min(lam), 12),
        "note": (
            "A finite check. Li's criterion makes the unrestricted statement "
            "equivalent to an open question, so this computation is not "
            "evidence for or against it, at any n."
        ),
    }
    provenance = _provenance(
        lab_object="zeta.li.li_coefficients",
        parameters={"n_max": LI_N_MAX, "method": "cauchy", "radius": "0.5"},
        precision=Precision(kind="dps", value=LI_DPS),
    )
    return _candidate(
        CandidateKind.STRUCTURAL,
        claim,
        evidence,
        provenance,
        label="historical: the first forty Li coefficients are non-negative",
    )


# ---------------------------------------------------------------------------
# 5. The negative control: a coincidence found at ten digits
# ---------------------------------------------------------------------------

#: The precision the integer-relation hunt is run at. Ten digits is enough for
#: ``mpmath.pslq`` to find a six-term relation among a basis of five constants
#: essentially always, and nowhere near enough for the relation to mean
#: anything: the search space has far more members than ten digits can select
#: between.
COINCIDENCE_DIGITS: Final[int] = 10

#: The basis the hunt runs over, named so the record can print the expression.
COINCIDENCE_BASIS: Final[tuple[str, ...]] = ("1", "gamma", "log(2)", "log(pi)", "sqrt(2)")


def _coincidence_basis_values() -> list[Any]:
    return [mp.mpf(1), mp.euler, mp.log(2), mp.log(mp.pi), mp.sqrt(2)]


def pslq_coincidence(digits: int = COINCIDENCE_DIGITS) -> dict[str, Any]:
    """Run the hunt at ``digits`` digits and return the coincidence it finds.

    This is the construction of the negative control, written out so it can be
    audited. ``Xi(1)`` has no known closed form; ``pslq`` is asked for an
    integer relation between it and five standard constants, at a tolerance of
    ``1e-digits``. It finds one, because with six unknowns and a coefficient
    bound of 10^6 the number of candidate relations vastly exceeds the number of
    ten-digit values to be matched. The relation is then *solved for* ``Xi(1)``
    at full precision, giving a number that agrees with the true value to about
    twelve digits and is wrong beyond that.

    Nothing is randomised and nothing is chosen after the fact: the basis, the
    tolerance and the coefficient bound are fixed above, and the first relation
    ``pslq`` returns is the one used.
    """
    from zeta.core import Xi

    with mp.workdps(60):
        true = mp.mpf(Xi(mp.mpf(1), dps=50))
        basis = _coincidence_basis_values()
        relation = mp.pslq(
            [true, *basis],
            tol=mp.mpf(10) ** (-int(digits)),
            maxcoeff=10**6,
            maxsteps=10**6,
        )
        if not relation or relation[0] == 0:  # pragma: no cover - defensive
            raise RuntimeError(
                f"no integer relation was found at {digits} digits; the negative "
                "control cannot be constructed without one"
            )
        rest = sum(mp.mpf(c) * v for c, v in zip(relation[1:], basis))
        spurious = -rest / mp.mpf(relation[0])
        gap = abs(spurious - true)
        terms = " + ".join(
            f"{int(c)}*{name}" for c, name in zip(relation[1:], COINCIDENCE_BASIS)
        )
        expression = f"-({terms}) / {int(relation[0])}"
        return {
            "relation": [int(c) for c in relation],
            "expression": expression,
            "spurious_value": _num(spurious, 25),
            "true_value": _num(true, 25),
            "agreement": _num(gap, 4),
            "digits_of_agreement": _f(round(float(-mp.log10(gap / abs(true))), 2)),
            "search_digits": int(digits),
        }


def build_low_precision_coincidence() -> Candidate:
    """A constant candidate whose value is the coincidence, not the quantity.

    The observation is a genuine one of a very common shape: a laboratory
    quantity, an integer-relation hunt run at whatever precision was to hand, a
    relation that reproduces twelve digits, and an error bar copied from the
    working precision of the *reference* constants rather than earned by the
    quantity itself. It is wrong. The funnel is supposed to say so.
    """
    found = pslq_coincidence()
    claim = {
        "subject": "zeta.core.Xi_at_1",
        "value": found["spurious_value"],
    }
    evidence = {
        # The fiction: twenty digits claimed, twelve actually agreeing.
        "uncertainty": "1e-20",
        "closed_form": found["expression"],
        "integer_relation": found["relation"],
        "basis": list(COINCIDENCE_BASIS),
        "search_digits": found["search_digits"],
        "agreement_with_the_laboratory_value": found["agreement"],
        "digits_of_agreement": found["digits_of_agreement"],
        "construction": (
            "mpmath.pslq over six terms at a tolerance of 1e-10 and a "
            "coefficient bound of 10^6. The search space is far larger than ten "
            "digits can select between, so a relation is found whether or not "
            "one exists, and the closed form is then solved for the quantity."
        ),
    }
    provenance = _provenance(
        lab_object="zeta.core.Xi",
        # ``route`` and ``t`` are what let the domain's screens re-derive the
        # quantity; without them no screen could recompute anything and the
        # negative control would be killed by a missing dependency rather than
        # by arithmetic, which would prove nothing about the screens.
        parameters={"route": "Xi_at", "t": "1"},
        precision=Precision(kind="dps", value=COINCIDENCE_DIGITS),
    )
    return _candidate(
        CandidateKind.CONSTANT,
        claim,
        evidence,
        provenance,
        label="negative control: a six-term relation found at ten digits",
    )


HONEST_TWIN_DPS: Final[int] = 25
HONEST_TWIN_UNCERTAINTY: Final[str] = "1e-20"


def build_honest_twin() -> Candidate:
    """The same quantity, measured honestly. The suite's positive control.

    Identical to :func:`build_low_precision_coincidence` in subject, route and
    error bar; the only difference is that the recorded number is what the
    laboratory computes rather than what an integer-relation hunt guessed. It
    exists to keep the negative control from being vacuous: "the spurious one
    was refuted" says nothing unless a candidate of the same shape can get
    through, and this one does — reaching ``survives``, which is a lead and not
    a result, and whose own ``proof_gap`` says so.

    ``Xi(1)`` is not in the catalogue, so with the catalogue emptied it behaves
    the same way; that is what makes it a usable probe for the ``uncatalogued``
    replay.
    """
    from zeta.core import Xi

    with mp.workdps(HONEST_TWIN_DPS + GUARD_DIGITS):
        value = mp.mpf(Xi(mp.mpf(1), dps=HONEST_TWIN_DPS))
    claim = {"subject": "zeta.core.Xi_at_1", "value": _num(value, 21)}
    evidence = {
        "uncertainty": HONEST_TWIN_UNCERTAINTY,
        "note": (
            f"computed at dps={HONEST_TWIN_DPS}, so an error bar of "
            f"{HONEST_TWIN_UNCERTAINTY} leaves five digits of headroom rather "
            "than claiming the working precision as accuracy"
        ),
    }
    provenance = _provenance(
        lab_object="zeta.core.Xi",
        parameters={"route": "Xi_at", "t": "1"},
        precision=Precision(kind="dps", value=HONEST_TWIN_DPS),
    )
    return _candidate(
        CandidateKind.CONSTANT,
        claim,
        evidence,
        provenance,
        label="positive control: the same quantity, measured rather than guessed",
    )


# ---------------------------------------------------------------------------
# The cases
# ---------------------------------------------------------------------------

HISTORICAL_CASES: Final[tuple[HistoricalCase, ...]] = (
    HistoricalCase(
        key="gauss_prime_counts",
        title="pi(x) ~ Li(x)",
        proposed=1792,
        outcome=HistoricalOutcome.TRUE_AND_PROVEN,
        settled=1896,
        settled_by="Hadamard and de la Vallee Poussin, independently",
        build=build_gauss_prime_counting,
        expect_full=frozenset({"known"}),
        expect_uncatalogued=frozenset({"inconclusive"}),
        must_cite=("Hadamard", "de la Vallee Poussin", "Gauss"),
        note=(
            "The friendly case: conjectured from data, true, and proved. It "
            "exists to check that the pipeline can accept a correct observation "
            "at all, rather than killing everything it is shown."
        ),
        if_it_fails=(
            "A refutation would mean the screens contradict a theorem, which is "
            "a defect in the laboratory. A promotion to 'survives' would mean "
            "the catalogue does not carry the prime number theorem, which is a "
            "gap in the catalogue: the pipeline would have reported one of the "
            "best-known results in the subject as an unexamined lead."
        ),
    ),
    HistoricalCase(
        key="montgomery_pair",
        title="the pair correlation 1 - (sin(pi r)/(pi r))^2",
        proposed=1973,
        outcome=HistoricalOutcome.TRUE_BUT_UNPROVEN,
        settled=None,
        settled_by="",
        build=build_montgomery_pair_correlation,
        expect_full=frozenset({"known"}),
        expect_uncatalogued=frozenset({"inconclusive"}),
        must_cite=("Montgomery 1973", "Odlyzko 1987"),
        # The record must not describe a conjecture as settled. The schema has
        # no field for "known but not proved", so the catalogue's ``status``
        # carries it and this list keeps the prose honest.
        must_not_say=("proved", "proven", "is a theorem"),
        note=(
            "The distinction the schema does not have: this is true so far as "
            "anyone can tell, catalogued, and still open. A single verdict word "
            "cannot say all three, which is why the entry carries a status."
        ),
        if_it_fails=(
            "Recording it as 'survives' would mean the catalogue is missing the "
            "single most-cited connection in the subject. Any record calling it "
            "proved would mean the pipeline promotes a conjecture to a theorem "
            "on the strength of 2000 ordinates."
        ),
    ),
    HistoricalCase(
        key="mertens",
        title="|M(x)| < sqrt(x)",
        proposed=1897,
        outcome=HistoricalOutcome.FALSE,
        settled=1985,
        settled_by="Odlyzko and te Riele, non-constructively",
        build=build_mertens_conjecture,
        expect_full=frozenset({"known"}),
        expect_uncatalogued=frozenset({"inconclusive"}),
        must_cite=("Odlyzko", "te Riele"),
        note=(
            "The case that matters. Every computation feasible for a century "
            "supported this, and it is false. The funnel must record 'no "
            "violation was found in the range examined' and must not, under any "
            "circumstances, record a survivor."
        ),
        if_it_fails=(
            "A 'survives' disposition here would mean the funnel would have "
            "endorsed the Mertens conjecture on exactly the evidence that "
            "convinced its contemporaries, and no output of this pipeline could "
            "then be trusted about anything unsettled."
        ),
    ),
    HistoricalCase(
        key="li_criterion",
        title="lambda_n >= 0 for all n",
        proposed=1997,
        outcome=HistoricalOutcome.EQUIVALENT_TO_AN_OPEN_PROBLEM,
        settled=None,
        settled_by="",
        build=build_li_criterion,
        expect_full=frozenset({"known"}),
        expect_uncatalogued=frozenset({"inconclusive"}),
        must_cite=("Li 1997", "Bombieri"),
        note=(
            "Provably equivalent to an unsettled question, so no computation of "
            "lambda_n is evidence in either direction. The right answer is "
            "'already catalogued, and catalogued as open'."
        ),
        if_it_fails=(
            "Either terminal verdict other than 'known' would be a claim about "
            "an open question. 'survives' would present a finite positivity "
            "check as a lead towards it; 'refuted' would mean the laboratory "
            "believes it has settled it, and the correct inference from that is "
            "a bug."
        ),
    ),
    HistoricalCase(
        key="pslq_coincidence",
        title="a six-term closed form found at ten digits",
        proposed=0,
        outcome=HistoricalOutcome.SPURIOUS,
        settled=None,
        settled_by="",
        build=build_low_precision_coincidence,
        expect_full=frozenset({"refuted"}),
        expect_uncatalogued=frozenset({"refuted"}),
        expect_screens_kill=True,
        note=(
            "Constructed, not historical, and the only case here that the "
            "screens must kill on their own. Its subject is deliberately one "
            "the catalogue does not carry, so nothing but arithmetic can save "
            "it. The honest version of the same candidate reaches 'survives'; "
            "the difference between them is twelve digits."
        ),
        if_it_fails=(
            "If this is not refuted, the precision screens are decorative and "
            "every 'survives' this pipeline has ever written is unsupported: "
            "the system would be unable to tell a measured number from a "
            "coincidence with an error bar copied off the wrong quantity."
        ),
    ),
)


def register_all(*, replace: bool = True) -> tuple[HistoricalCase, ...]:
    """Put every case in the process-wide table. Idempotent by default."""
    return tuple(register_case(case, replace=replace) for case in HISTORICAL_CASES)


#: Registered at import, as ``zeta_domain`` registers its domain. The table is
#: process-wide and a test may legitimately clear it, so callers that depend on
#: it should re-register rather than assume it survived.
REGISTERED: Final[tuple[HistoricalCase, ...]] = register_all()
