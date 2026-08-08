"""Department #2, pinned: the finite-field department's wiring and its limits.

``tests/test_department_conformance.py`` audits every department against the
protocol. This file pins what is true of *this* department: the payload that
carries no tell, the counterfeits' exact self-duality, the quantisation floor
on lesion magnitude, and — for the first time with a real department — all
four instrument runners driven with honest measures. Department #1 only ever
drives ``run_battery`` and ``run_power``; the compiler probe (git 2041d86)
recorded that gap, and this department closes it.
"""

from __future__ import annotations

import math
import sys
from pathlib import Path

import numpy as np
import pytest

_REPO_ROOT = Path(__file__).resolve().parents[1]
if str(_REPO_ROOT) not in sys.path:  # pragma: no cover - import bootstrap
    sys.path.insert(0, str(_REPO_ROOT))

from harness import get_department  # noqa: E402
from harness.departments import KNOWN_DEPARTMENTS, load  # noqa: E402
from harness.protocol import run_ablation, run_battery, run_nulls, run_power  # noqa: E402
from zeta import finitefield  # noqa: E402


@pytest.fixture(scope="module")
def department():
    load("finitefield")
    return get_department("finitefield")


# ---------------------------------------------------------------------------
# The wiring, and the payload that cannot be read as a label
# ---------------------------------------------------------------------------


def test_the_department_is_listed_and_therefore_audited() -> None:
    assert KNOWN_DEPARTMENTS["finitefield"] == "harness.departments.finitefield_department"


def test_the_rivals_are_the_two_counterfeits(department) -> None:
    assert tuple(r.name for r in department.battery.rivals) == (
        "counterfeit_trace_70",
        "counterfeit_trace_200",
    )


def test_no_payload_carries_a_tell(department) -> None:
    """An earlier draft handed rivals a ``virtual_a_p`` field; a claim could
    then distinguish the target by reading the label rather than the
    mathematics. Pinned: every subject's payload has exactly the same keys.
    """
    battery = department.battery
    for subject in (battery.target, *battery.rivals):
        assert set(subject.payload().keys()) == {"p", "counts"}, subject.name


def test_the_targets_counts_are_the_librarys(department) -> None:
    """The target's payload is real point-counting, not a copy of a formula:
    ``point_counts_over_extensions`` is itself pinned against brute-force
    enumeration over F_p and F_{p²} in ``tests/test_finitefield.py``."""
    payload = department.battery.target.payload()
    expected = finitefield.point_counts_over_extensions(1, 1, 1009, len(payload["counts"]))
    assert list(payload["counts"]) == [int(c) for c in expected]
    assert 1009 + 1 - payload["counts"][0] == finitefield.trace_of_frobenius(1, 1, 1009)


# ---------------------------------------------------------------------------
# The calibration pair, re-derived (the conformance suite does this too; here
# the *reasons* are pinned, not just the verdicts)
# ---------------------------------------------------------------------------


def test_the_functional_equation_is_shared_with_every_counterfeit(department) -> None:
    """True of the target by the Weil conjectures, true of the counterfeits by
    construction — exactly department #1's situation, made exact."""
    reference = next(r for r in department.reference_claims if r.name == "functional_equation")
    verdict = run_battery(department.battery, reference.claim)
    assert verdict.target is True
    assert verdict.shared_with == ("counterfeit_trace_200", "counterfeit_trace_70")
    assert verdict.errors == {}


def test_the_hasse_bound_is_the_one_that_distinguishes(department) -> None:
    reference = next(r for r in department.reference_claims if r.name == "hasse_bound")
    verdict = run_battery(department.battery, reference.claim)
    assert verdict.distinguishes is True
    assert verdict.errors == {}


# ---------------------------------------------------------------------------
# The quantisation floor: the smallest honest lesion is not a choice
# ---------------------------------------------------------------------------


def test_the_lesion_floor_is_quantised_by_integrality(department) -> None:
    """|a| = 64 is the smallest integer Hasse violation at p = 1009: 63² = 3969
    ≤ 4036 < 4096. Department #1 plants δ = 0.001 off the line; this
    department provably cannot go below magnitude ≈ 0.129 without fractional
    traces, which would break integrality of the counts and make the lesion
    detectable for a reason that has nothing to do with the circle."""
    assert 63 * 63 <= 4 * 1009 < 64 * 64
    smallest = min(lesion.magnitude for lesion in department.battery.lesions)
    assert smallest == pytest.approx(0.12933, abs=1e-4)

    from harness.departments.finitefield_department import _off_circle_magnitude

    with pytest.raises(ValueError, match="inside the Hasse bound"):
        _off_circle_magnitude(63, 1009)


def test_a_counterfeit_inside_the_bound_is_refused(department) -> None:
    """A 'rival' that satisfies RH would refute nothing; the constructor
    refuses it rather than letting the battery go soft quietly."""
    from harness.departments.finitefield_department import CounterfeitSubject

    with pytest.raises(ValueError, match="inside the Hasse bound"):
        CounterfeitSubject(name="soft_rival", trace=24)


# ---------------------------------------------------------------------------
# All four runners, driven with honest measures
# ---------------------------------------------------------------------------


def _normalized_deviation(counts, p: int = 1009) -> float:
    """max_r |N_r − (p^r + 1)| / (2·p^{r/2}) — equals max_r |cos(r·θ)| ≤ 1 for
    genuine counts, which is RH for the curve in normalised form."""
    return max(
        abs(int(n) - (p**r + 1)) / (2.0 * p ** (r / 2.0))
        for r, n in enumerate(counts, start=1)
    )


def test_run_ablation_both_decoys_move_an_honest_measure(department) -> None:
    """This department's decoy pair has uniform polarity — the payload is a
    sequence indexed by r, so jitter *and* permutation both destroy substance
    — which makes ``survives`` the correct aggregate here. Contrast the zeta
    department, whose set-payload pair has opposite polarities; that is
    pinned in ``tests/test_harness_zeta_department.py``."""
    counts = department.battery.target.payload()["counts"]
    baseline = _normalized_deviation(counts)
    assert baseline <= 1.0  # RH for the curve, in the form the decoys attack

    verdict = run_ablation(
        department.battery,
        _normalized_deviation,
        tolerance=0.01,
        payload=list(counts),
    )
    assert verdict.survives is True
    assert verdict.unmoved_by == ()


def test_run_ablation_jitter_breaks_the_self_duality(department) -> None:
    """The ablation removes the substance it claims to: jittered counts no
    longer follow any degree-2 Lefschetz recursion with αβ = p."""
    from harness.departments.finitefield_department import claim_functional_equation

    counts = department.battery.target.payload()["counts"]
    jitter = next(d for d in department.battery.decoys if d.name == "count_jitter")
    assert claim_functional_equation({"p": 1009, "counts": counts}) is True
    assert claim_functional_equation({"p": 1009, "counts": jitter.substitute(counts)}) is False


def test_run_nulls_the_hasse_bound_is_reproduced_from_no_curve(department) -> None:
    """The observation 'normalised traces respect the bound' holds for every
    genuine curve — and for both surrogates, which contain no curve at all,
    because points on a circle cannot do otherwise. Satisfying the bound is a
    property of the model class, not evidence about arithmetic; what *is*
    arithmetic is which angle a curve gets, which this statistic ignores."""

    def share_within_bound(values) -> float:
        return float(np.mean(np.abs(np.asarray(values, dtype=float)) <= 1.0))

    observed = share_within_bound(
        [
            finitefield.trace_of_frobenius(a, b, 1009) / (2.0 * math.sqrt(1009))
            for a, b in ((1, 1), (2, 3), (0, 7))
        ]
    )
    assert observed == 1.0  # Hasse's theorem, measured

    verdict = run_nulls(
        department.battery, share_within_bound, tolerance=1e-12, observed=observed
    )
    assert verdict.survives is False
    assert verdict.reproduced_by == ("sato_tate_angle", "uniform_angle")


def _implied_off_circle_magnitude(profile) -> float:
    p = int(profile["p"])
    trace = p + 1 - int(profile["counts"][0])
    disc = trace * trace - 4 * p
    if disc <= 0:
        return 0.0
    return ((abs(trace) + math.sqrt(disc)) / 2.0) / math.sqrt(p) - 1.0


def test_run_power_and_where_a_coarse_detector_goes_blind(department) -> None:
    """Detector power is measured, not assumed — including the blindness. A
    detector reading the exact bound sees every planted lesion down to the
    quantisation floor; one that only trusts violations past 1.5·sqrt(p)
    misses the floor lesion, and ``blind_to`` says so by name."""
    survey = (department.battery.target.payload(),)

    def exact_detector(profiles) -> bool:
        return any(_implied_off_circle_magnitude(pr) > 0.0 for pr in profiles)

    verdict = run_power(department.battery, exact_detector, payload=survey)
    assert verdict.has_power is True
    assert verdict.smallest_detected == pytest.approx(0.12933, abs=1e-4)

    def coarse_detector(profiles) -> bool:
        return any(_implied_off_circle_magnitude(pr) > 0.5 for pr in profiles)

    verdict = run_power(department.battery, coarse_detector, payload=survey)
    assert verdict.blind_to == ("off_circle_trace_64",)
    assert verdict.has_power is False
