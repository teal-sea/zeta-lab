"""``harness.departments.finitefield_department`` — department #2.

Curves over F_p: the universe where RH is a **theorem** (Hasse, 1933). This
department exists for two reasons, and testing the mathematics is neither —
`zeta/finitefield.py` and its tests already do that.

First, it is the harness's second real subject, so it is the first measurement
of the claim in ROADMAP.md's known gaps that the four instrument roles carve
more than exactly one case. It is a *modest* measurement — the subject shares
a repository, an author and half a vocabulary with department #1 — but unlike
department #1 it drives all four runners, and its battery is built from
different material.

Second, and more interesting: here the property at issue is *decidable*, so
every role can be exact where department #1's had to be numerical. The
department is the same architecture under a different epistemic regime.

The payload convention, and why it is strict
--------------------------------------------
Every subject's ``payload()`` is ``{"p": int, "counts": (N_1, ..., N_k)}`` —
the point counts of something over the tower F_p ⊂ F_{p²} ⊂ … — **and nothing
else**. In particular no field says which subject produced it. An earlier
draft of this module handed rivals a ``virtual_a_p`` tell; a claim could
distinguish the target by reading the label, which is a battery that tests
whether claims can read, not whether they are about their subject. Everything
a claim uses must be derived from the counts.

The four roles, and where each came from
----------------------------------------
* **Rivals** — counterfeit Lefschetz profiles: pick an integer trace ``a``
  with ``a² > 4p``, take the roots of ``x² − ax + p``, and generate counts by
  the same fixed-point formula ``N_r = p^r + 1 − α^r − β^r`` a genuine curve
  obeys. Because ``αβ = p``, the counterfeit satisfies the functional
  equation's self-duality exactly; because the recursion has integer
  coefficients, its counts are exact integers; for the traces chosen here they
  are all positive. It shares everything a curve's counting data is *shaped*
  like and violates RH — the Davenport–Heilbronn of finite fields, except that
  here Hasse's theorem says no curve realises it, which is the point: the
  structure alone does not exclude it, only the theorem does.
* **Decoys** — substitutions on the count sequence. ``count_jitter`` moves
  each entry by a nonzero amount on the Hasse–Weil scale ``2·sqrt(N)``, which
  destroys the single eigenvalue pair threading the tower while keeping every
  magnitude plausible; ``tower_permutation`` keeps the very same numbers and
  reorders them. Note the polarity: in department #1 the payload is a *set* of
  places and an honest measurement must ignore the permutation decoy; here the
  payload is a *sequence indexed by r* and an honest measurement must move
  under both. This department's decoy pair is therefore the one for which
  ``AblationVerdict.survives`` (every decoy moves the measurement) is the
  correct aggregate — for department #1's pair it is not, which
  ``tests/test_harness_zeta_department.py`` pins.
* **Surrogates** — Frobenius angles with no curve behind them: draws of
  ``cos θ`` with θ uniform on [0, π], and draws from the Sato–Tate semicircle
  density (2/π)·sin²θ. Both produce normalised traces that satisfy the Hasse
  bound *by construction*, because points on a circle of radius sqrt(p) cannot
  do otherwise. A trace statistic these reproduce is a property of the circle
  model, not of the arithmetic of any curve.
* **Lesions** — a counterfeit profile planted into a survey of genuine ones.
  ``magnitude`` is the relative displacement ``|α|/sqrt(p) − 1`` off the
  circle. The domain quantises this: the smallest integer trace violating
  Hasse at p = 1009 is |a| = 64, giving magnitude 0.129 — **no smaller honest
  lesion exists**, because a fractional trace would break integrality of the
  counts and be detectable for a reason that has nothing to do with the
  circle. Department #1 plants zeros at δ = 0.001; this department provably
  cannot, and detector power below the quantisation floor is unmeasurable
  here. That asymmetry is a fact about the subjects, not a defect of either
  battery.
"""

from __future__ import annotations

import math
from dataclasses import dataclass
from typing import Any

import numpy as np

from harness.protocol import (
    Battery,
    Department,
    NamedDetector,
    ReferenceClaim,
    register_department,
)
from harness.provenance import Provenance
from zeta import finitefield

DEPARTMENT_NAME = "finitefield"
DEPARTMENT_VERSION = "2.0"

#: The reference prime and target curve: y² = x³ + x + 1 over F_1009, chosen
#: non-singular (discriminant −16·31 ≢ 0 mod 1009) and small enough that the
#: O(p) point count on every ``payload()`` call is negligible. Its trace is
#: a_p = −24, comfortably inside the Hasse window |a| ≤ 63.
P: int = 1009
CURVE_A: int = 1
CURVE_B: int = 1

#: Depth of the extension tower F_p ⊂ … ⊂ F_{p^N_MAX} in every payload.
N_MAX: int = 6

#: Integer traces of the counterfeit rivals, both with a² > 4·1009 = 4036.
RIVAL_TRACES: tuple[int, ...] = (70, 200)

#: Integer traces of the planted lesions. 64 is the *smallest* integer
#: violation possible at p = 1009 (63² = 3969 ≤ 4036 < 4096 = 64²) — the
#: quantisation floor discussed in the module docstring.
LESION_TRACES: tuple[int, ...] = (64, 80, 128)

_SEED: int = 20260807

__all__ = [
    "DEPARTMENT_NAME",
    "DEPARTMENT_VERSION",
    "P",
    "CURVE_A",
    "CURVE_B",
    "N_MAX",
    "RIVAL_TRACES",
    "LESION_TRACES",
    "BATTERY",
    "DEPARTMENT",
    "REFERENCE_CLAIMS",
    "CurveSubject",
    "CounterfeitSubject",
    "CountDecoy",
    "AngleSurrogate",
    "OffCircleLesion",
    "counterfeit_counts",
    "claim_functional_equation",
    "claim_hasse_bound",
]


def counterfeit_counts(trace: int, p: int, n_max: int) -> tuple[int, ...]:
    """Counts of nothing: the Lefschetz formula run on an inadmissible trace.

    ``t_r = α^r + β^r`` for the roots of ``x² − trace·x + p`` satisfies the
    integer recursion ``t_r = trace·t_{r−1} − p·t_{r−2}`` with ``t_0 = 2``,
    ``t_1 = trace``, so the counts are exact integers — no floating point
    enters, which matters because a counterfeit detectable by its rounding
    would flatter every detector shown it.
    """
    p = int(p)
    trace = int(trace)
    t_prev, t_cur = 2, trace
    counts = []
    for r in range(1, int(n_max) + 1):
        if r >= 2:
            t_prev, t_cur = t_cur, trace * t_cur - p * t_prev
        counts.append(p**r + 1 - t_cur)
    return tuple(counts)


def _off_circle_magnitude(trace: int, p: int) -> float:
    """``|α|/sqrt(p) − 1`` for the dominant root of ``x² − trace·x + p``."""
    disc = trace * trace - 4 * p
    if disc <= 0:
        raise ValueError(f"trace {trace} is inside the Hasse bound for p={p}; not a violation")
    alpha = (abs(trace) + math.sqrt(disc)) / 2.0
    return alpha / math.sqrt(p) - 1.0


# ---------------------------------------------------------------------------
# Subjects: the genuine article and its rivals
# ---------------------------------------------------------------------------


@dataclass(frozen=True)
class CurveSubject:
    """The genuine article: counts of a real curve, recomputed per call.

    Recomputed rather than cached for the same reason department #1 rebuilds
    its interface dicts: a claim that mutated a cached payload would silently
    contaminate every later run of the battery.
    """

    name: str
    a: int
    b: int
    p: int = P
    n_max: int = N_MAX
    _description: str = ""

    def describe(self) -> str:
        return self._description

    def payload(self) -> dict:
        counts = finitefield.point_counts_over_extensions(self.a, self.b, self.p, self.n_max)
        return {"p": self.p, "counts": tuple(int(c) for c in counts)}


@dataclass(frozen=True)
class CounterfeitSubject:
    """A rival: the same count-shape with the property removed.

    Shares the Lefschetz recursion, the self-duality αβ = p (the functional
    equation of the curve's zeta function), integrality and positivity — and
    has both Frobenius roots off the circle |α| = sqrt(p).
    """

    name: str
    trace: int
    p: int = P
    n_max: int = N_MAX
    _description: str = ""

    def __post_init__(self) -> None:
        # A "rival" inside the Hasse bound would satisfy RH and refute
        # nothing; refuse it here rather than let the battery go soft quietly.
        _off_circle_magnitude(self.trace, self.p)
        if any(c <= 0 for c in counterfeit_counts(self.trace, self.p, self.n_max)):
            raise ValueError(
                f"counterfeit trace {self.trace} produces a non-positive count: "
                "it would be killable for a reason that has nothing to do with RH"
            )

    def describe(self) -> str:
        return self._description

    def payload(self) -> dict:
        return {"p": self.p, "counts": counterfeit_counts(self.trace, self.p, self.n_max)}


TARGET = CurveSubject(
    name="curve_1009_1_1",
    a=CURVE_A,
    b=CURVE_B,
    _description=(
        "y² = x³ + x + 1 over F_1009, non-singular, trace −24: a genuine curve, "
        "so RH holds for it by Hasse's theorem — the property is a theorem here, "
        "not a conjecture"
    ),
)

RIVALS: tuple[CounterfeitSubject, ...] = tuple(
    CounterfeitSubject(
        name=f"counterfeit_trace_{trace}",
        trace=trace,
        _description=(
            f"the Lefschetz formula run on trace {trace} with {trace}² > 4·1009: "
            "integer positive counts, exact functional-equation self-duality, and "
            "both Frobenius roots off the circle — the count-shape without the theorem"
        ),
    )
    for trace in RIVAL_TRACES
)


# ---------------------------------------------------------------------------
# Decoys: same shape, no eigenvalue pair
# ---------------------------------------------------------------------------


@dataclass(frozen=True)
class CountDecoy:
    """A substitution acting on a sequence of counts.

    ``jitter`` moves every entry by a nonzero seeded amount of typical size
    ``2·sqrt(value)`` — the Hasse–Weil scale, so each individual number stays
    plausible while no single (α, β) pair threads the sequence any more.
    ``permute`` keeps the same numbers and changes only their order, which
    destroys the tower structure (the r-th entry *means* F_{p^r}).

    Both are expected to move an honest measurement — see the module
    docstring for why this department's pair, unlike department #1's, has
    uniform polarity.
    """

    name: str
    mode: str
    seed: int = _SEED
    _description: str = ""

    def describe(self) -> str:
        return self._description

    def substitute(self, payload: Any) -> list[int]:
        values = [int(v) for v in payload]
        rng = np.random.default_rng(self.seed)
        if self.mode == "permute":
            order = list(rng.permutation(len(values)))
            if [values[i] for i in order] == values and len(values) > 1:
                order = order[1:] + order[:1]
            return [values[i] for i in order]
        if self.mode == "jitter":
            out = []
            for v in values:
                bound = 1 + math.isqrt(4 * abs(v))
                step = int(rng.integers(1, bound + 1))
                if rng.integers(0, 2) and v - step >= 0:
                    step = -step
                out.append(v + step)
            return out
        raise ValueError(f"unknown decoy mode {self.mode!r}")


DECOYS: tuple[CountDecoy, ...] = (
    CountDecoy(
        name="count_jitter",
        mode="jitter",
        _description=(
            "every count moved by a nonzero amount on the Hasse–Weil scale 2·sqrt(N) — "
            "individually plausible numbers with no shared eigenvalue pair; a statistic "
            "that does not move was never reading the arithmetic"
        ),
    ),
    CountDecoy(
        name="tower_permutation",
        mode="permute",
        _description=(
            "the same counts in a different order — the r-th entry means F_{p^r}, so a "
            "statistic that does not move was never reading the tower"
        ),
    ),
)


# ---------------------------------------------------------------------------
# Surrogates: the Hasse bound from no curve at all
# ---------------------------------------------------------------------------


@dataclass(frozen=True)
class AngleSurrogate:
    """Normalised Frobenius traces drawn from an angle law, no curve anywhere.

    ``sample`` returns ``draws`` values of ``cos θ`` — the normalised trace
    ``a/(2·sqrt(p))`` of a fictitious curve whose Frobenius angle is θ. Every
    draw satisfies the Hasse bound by construction, so any statistic amounting
    to "the traces respect the bound" or "the traces look circle-distributed"
    is reproduced with zero arithmetic input.
    """

    name: str
    kind: str
    draws: int = 64
    seed: int = _SEED
    _description: str = ""

    def describe(self) -> str:
        return self._description

    def sample(self) -> np.ndarray:
        rng = np.random.default_rng(self.seed)
        if self.kind == "uniform":
            return np.cos(rng.uniform(0.0, math.pi, size=self.draws))
        if self.kind == "sato_tate":
            out: list[float] = []
            while len(out) < self.draws:
                theta = rng.uniform(0.0, math.pi)
                if rng.uniform(0.0, 1.0) < math.sin(theta) ** 2:
                    out.append(math.cos(theta))
            return np.array(out)
        raise ValueError(f"unknown surrogate kind {self.kind!r}")


SURROGATES: tuple[AngleSurrogate, ...] = (
    AngleSurrogate(
        name="uniform_angle",
        kind="uniform",
        _description=(
            "cos θ for θ uniform on [0, π] — traces on the circle with the wrong "
            "distribution and no curve behind them"
        ),
    ),
    AngleSurrogate(
        name="sato_tate_angle",
        kind="sato_tate",
        _description=(
            "cos θ for θ drawn from the Sato–Tate density (2/π)·sin²θ — the "
            "conjectured equidistribution law, reproduced from its formula rather "
            "than from any arithmetic"
        ),
    ),
)


# ---------------------------------------------------------------------------
# Lesions: planted off-circle profiles, power measured rather than assumed
# ---------------------------------------------------------------------------


@dataclass(frozen=True)
class OffCircleLesion:
    """Append one counterfeit profile to a survey of genuine ones.

    ``apply`` receives a sequence of ``{"p", "counts"}`` profiles — the shape
    of a curve survey — and returns it with a counterfeit planted at the end.
    ``magnitude`` is ``|α|/sqrt(p) − 1``, the relative displacement of the
    dominant Frobenius root off the circle, the analogue of department #1's
    δ off the critical line. Integer traces quantise it: nothing below 0.129
    can be planted at p = 1009 without breaking integrality, which would make
    the lesion detectable for the wrong reason.
    """

    name: str
    trace: int
    p: int = P
    n_max: int = N_MAX
    _description: str = ""

    @property
    def magnitude(self) -> float:
        return _off_circle_magnitude(self.trace, self.p)

    def describe(self) -> str:
        return self._description or (
            f"a counterfeit profile with trace {self.trace} planted into the survey: "
            f"dominant root {1 + self.magnitude:.3f}·sqrt(p) off the circle"
        )

    def apply(self, payload: Any) -> tuple:
        planted = {"p": self.p, "counts": counterfeit_counts(self.trace, self.p, self.n_max)}
        return (*tuple(payload), planted)


LESIONS: tuple[OffCircleLesion, ...] = tuple(
    OffCircleLesion(name=f"off_circle_trace_{trace}", trace=trace) for trace in LESION_TRACES
)


# ---------------------------------------------------------------------------
# Detectors: the survey scan, exact where department #1's is numerical
# ---------------------------------------------------------------------------


def _survey_probe() -> tuple:
    """A clean survey: three genuine curves over F_1009, recomputed per import."""
    curves = ((CURVE_A, CURVE_B), (2, 3), (5, 7))
    profiles = []
    for a, b in curves:
        counts = finitefield.point_counts_over_extensions(a, b, P, N_MAX)
        profiles.append({"p": P, "counts": tuple(int(c) for c in counts)})
    return tuple(profiles)


_CLEAN_SURVEY = _survey_probe()


def hasse_scan(survey) -> bool:
    """Fires when any profile in the survey has a trace violating a² ≤ 4p.

    Exact integer arithmetic, derived from the counts alone — the decidable
    domain's luxury. Its power is quantised the same way the lesions are:
    below trace 64 at p = 1009 there is no integer violation to detect, so
    "full power" here means full power down to the domain's own floor.
    """
    for profile in survey:
        p = int(profile["p"])
        trace = p + 1 - int(profile["counts"][0])
        if trace * trace > 4 * p:
            return True
    return False


DETECTORS: tuple[NamedDetector, ...] = (
    NamedDetector(
        name="hasse_scan",
        fires=hasse_scan,
        probe=_CLEAN_SURVEY,
        note=(
            "exact integer scan of a survey for any trace with a² > 4p; power is "
            "quantised at the domain's own floor (trace 64 at p = 1009)"
        ),
    ),
)


# ---------------------------------------------------------------------------
# The battery, and the department
# ---------------------------------------------------------------------------

BATTERY = Battery(
    name="finitefield",
    target=TARGET,
    rivals=RIVALS,
    decoys=DECOYS,
    surrogates=SURROGATES,
    lesions=LESIONS,
    notes=(
        "The same architecture as department #1 under a decidable property: the "
        "rivals are counterfeit Lefschetz profiles no curve realises (Hasse's "
        "theorem is exactly the statement that they are counterfeit), and the "
        "lesion magnitudes are quantised at 0.129 by integrality of the trace."
    ),
)


def claim_functional_equation(payload: dict) -> bool:
    """Self-duality: the counts follow a degree-2 Lefschetz recursion with αβ = p.

    Recovers the trace from ``N_1`` and checks every further count against
    ``N_r = p^r + 1 − t_r`` with ``t_r = a·t_{r−1} − p·t_{r−2}`` — which is
    precisely the statement that the counting zeta function is
    ``(1 − aT + pT²) / ((1 − T)(1 − pT))``, self-dual under T ↦ 1/(pT).
    True of the target by the Weil conjectures for curves; true of every
    counterfeit by construction. Exact integer arithmetic throughout.
    """
    p = int(payload["p"])
    counts = [int(c) for c in payload["counts"]]
    trace = p + 1 - counts[0]
    t_prev, t_cur = 2, trace
    for r, observed in enumerate(counts, start=1):
        if r >= 2:
            t_prev, t_cur = t_cur, trace * t_cur - p * t_prev
        if observed != p**r + 1 - t_cur:
            return False
    return True


def claim_hasse_bound(payload: dict) -> bool:
    """RH for the curve: both Frobenius roots on |α| = sqrt(p), i.e. a² ≤ 4p.

    Derived from the counts alone — the trace is ``p + 1 − N_1`` — so nothing
    in the payload can tell this claim which subject it is judging. This is
    the property that is a conjecture in department #1 and a theorem here.
    """
    p = int(payload["p"])
    trace = p + 1 - int(payload["counts"][0])
    return trace * trace <= 4 * p


#: The calibration pair, mirroring department #1's exactly: the functional
#: equation is a real, true property of the target that the battery must kill,
#: because every counterfeit has it too; the Hasse bound is the property the
#: counterfeits lack. The conformance test re-derives both verdicts.
REFERENCE_CLAIMS: tuple[ReferenceClaim, ...] = (
    ReferenceClaim(
        name="functional_equation",
        claim=claim_functional_equation,
        distinguishes=False,
        note=(
            "true of the target and of every counterfeit — self-duality survives the "
            "loss of the property in this department just as it does in department #1, "
            "so it cannot be the load-bearing step of any argument for the property"
        ),
    ),
    ReferenceClaim(
        name="hasse_bound",
        claim=claim_hasse_bound,
        distinguishes=True,
        note=(
            "the property itself, decidable from the counts: true of the target by "
            "Hasse's theorem, false for every counterfeit by choice of trace"
        ),
    ),
)

DEPARTMENT = Department(
    name=DEPARTMENT_NAME,
    summary=(
        "curves over F_p: point counts, Frobenius eigenvalues and the RH that is "
        "a theorem — the same referee architecture under a decidable property"
    ),
    battery=BATTERY,
    door="docs/doors/finitefield.md",
    domain="",
    reference_claims=REFERENCE_CLAIMS,
    detectors=DETECTORS,
    scope=(
        "a surviving claim distinguishes genuine counting data from counterfeit "
        "Lefschetz profiles at p = 1009 up to F_{p^6}; the property itself is "
        "Hasse's theorem, so nothing here is a discovery about curves"
    ),
    provenance=Provenance(
        authored_by=(
            "the laboratory's own process — this battery is the 2026-08-07 rebuild "
            "that replaced the sham caught in review (commit 431cc74)"
        ),
        authored_on="2026-08-07",
        independent_of_subject_author=False,
        results_visible_when_authored=False,
        frozen_before_execution=True,
        oracle_calls_subject=False,
        notes=(
            "rival traces are chosen by the Hasse-bound criterion, not tuned to "
            "any observed detector outcome; the predecessor battery is preserved "
            "as the referee department's held-out rival"
        ),
    ),
    modules=("zeta.finitefield",),
)

register_department(DEPARTMENT, replace=True)
