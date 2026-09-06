"""Conformance: every registered department, audited by the same tests.

``tests/test_harness_protocol.py`` checks the protocol against stand-ins. This
file checks the real departments against the protocol, and it is parametrized
over ``harness.departments.KNOWN_DEPARTMENTS`` so that **adding a department
adds its audit automatically**. That is the point of the whole arrangement: a
new department cannot be added quietly, and cannot be added without a referee.

What is pinned here:

1. **It exists as advertised.** Each known department registers under its key,
   validates, declares a door that is really on disk, and names modules that
   really import.
2. **Its battery has teeth.** A claim true of everything must not distinguish.
   This is the check that catches a battery of rivals so weak that nothing
   could ever fail against them.
3. **Its battery is calibrated in both directions.** Every declared reference
   claim is re-run and its verdict re-derived. The declaration in the
   department module is a label; this test is the measurement.
4. **Its instruments do something.** A decoy that returns the payload
   unchanged, or a lesion that plants nothing, would satisfy every structural
   check and measure nothing at all.
"""

from __future__ import annotations

import importlib
import sys
from pathlib import Path

import pytest

_REPO_ROOT = Path(__file__).resolve().parents[1]
if str(_REPO_ROOT) not in sys.path:  # pragma: no cover - import bootstrap
    sys.path.insert(0, str(_REPO_ROOT))

from harness import departments as D  # noqa: E402
from harness.integrity import (  # noqa: E402
    CALIBRATED,
    DETECTOR_INADEQUATE,
    audit_department,
    payloads_same,
)
from harness.protocol import (  # noqa: E402
    department_reasons,
    get_department,
    run_battery,
    run_detector,
)

DEPARTMENT_NAMES = sorted(D.KNOWN_DEPARTMENTS)


@pytest.fixture(scope="module", params=DEPARTMENT_NAMES)
def department(request):
    """Load and return one registered department, once per module."""
    D.load(request.param)
    return get_department(request.param)


# ---------------------------------------------------------------------------
# 1. It exists as advertised
# ---------------------------------------------------------------------------


def test_at_least_one_department_is_known() -> None:
    assert DEPARTMENT_NAMES, "the harness knows no departments"


def test_the_module_registers_under_the_key_it_is_listed_by(department, request) -> None:
    assert department.name == request.node.callspec.params["department"]


def test_the_department_is_admissible(department) -> None:
    assert department_reasons(department) == ()


def test_the_door_is_really_on_disk(department) -> None:
    door = _REPO_ROOT / department.door
    assert door.is_file(), f"{department.name} declares a door at {department.door} that does not exist"
    assert door.read_text(encoding="utf-8").strip(), f"{department.door} is empty"


def test_every_declared_module_imports(department) -> None:
    for name in department.modules:
        importlib.import_module(name)


def test_the_battery_describes_itself_without_raising(department) -> None:
    text = department.describe()
    assert department.name in text
    for rival in department.battery.rivals:
        assert rival.name in text


# ---------------------------------------------------------------------------
# 2. The battery has teeth
# ---------------------------------------------------------------------------


def test_a_claim_true_of_everything_distinguishes_nothing(department) -> None:
    """The single most important test in this file.

    A department whose rivals are too weak to refute anything would pass every
    structural check above and be worthless. If a claim that fires
    unconditionally still "distinguishes", the rivals are not rivals.
    """
    verdict = run_battery(department.battery, lambda payload: True, name="always_true")
    assert verdict.target is True
    assert verdict.distinguishes is False
    assert verdict.shared_with == tuple(sorted(r.name for r in department.battery.rivals))


def test_a_claim_true_of_nothing_does_not_distinguish(department) -> None:
    verdict = run_battery(department.battery, lambda payload: False, name="always_false")
    assert verdict.distinguishes is False


def test_every_rival_actually_answers(department) -> None:
    """A rival that raises refutes nothing, and must not be quietly credited."""
    verdict = run_battery(department.battery, lambda payload: True, name="always_true")
    assert verdict.errors == {}, f"rivals raised: {verdict.errors}"


# ---------------------------------------------------------------------------
# 3. Calibrated in both directions, the labels are re-derived, not trusted
# ---------------------------------------------------------------------------


def test_every_reference_claim_earns_its_declared_verdict(department) -> None:
    for reference in department.reference_claims:
        verdict = run_battery(department.battery, reference.claim, name=reference.name)
        assert verdict.distinguishes == reference.distinguishes, (
            f"{department.name}: reference claim {reference.name!r} was declared "
            f"distinguishes={reference.distinguishes} but measured "
            f"{verdict.distinguishes} (shared with {verdict.shared_with}, "
            f"errors {verdict.errors})"
        )


def test_a_reference_claim_expected_to_be_killed_is_killed_by_a_rival(department) -> None:
    """Not merely 'does not distinguish', it must fail *for the stated reason*.

    A claim can fail to distinguish by not firing for the target at all, which
    says nothing about the rivals. The department's killed reference claims are
    meant to demonstrate the modus tollens, so they must fire for the target
    and be shared with something.
    """
    killed = [r for r in department.reference_claims if not r.distinguishes]
    assert killed, f"{department.name} declares no reference claim its battery kills"
    for reference in killed:
        verdict = run_battery(department.battery, reference.claim, name=reference.name)
        assert verdict.target is True, (
            f"{reference.name} does not fire for the target, so it demonstrates nothing"
        )
        assert verdict.shared_with, f"{reference.name} was not shared with any rival"


# ---------------------------------------------------------------------------
# 4. The instruments do something
# ---------------------------------------------------------------------------


def test_every_decoy_changes_what_it_is_given(department) -> None:
    """An instrument may declare ``probe``, a representative payload of the
    shape it consumes, and is probed with it; without one it gets the
    historical integer-list probe. The ``probe`` convention is
    ``compiler/FINDINGS.md`` §7: this file, not the protocol, was guessing
    departments' payload shapes, and the guess encoded department #1's.
    """
    for decoy in department.battery.decoys:
        probe = getattr(decoy, "probe", None)
        if probe is None:
            probe = list(range(2, 60))
        substituted = decoy.substitute(probe)
        # payloads_same, not list comparison: the list form compared mapping
        # payloads by keys alone and raised on array payloads, department
        # #6's shapes exposed both, the probe-convention lesson one layer down.
        assert not payloads_same(substituted, probe), (
            f"decoy {decoy.name!r} returned its input unchanged and ablates nothing"
        )
        if hasattr(probe, "__len__") and hasattr(substituted, "__len__"):
            assert len(substituted) == len(probe), (
                f"decoy {decoy.name!r} changed the size of the input; it is not a substitution"
            )


def test_every_lesion_changes_what_it_is_given(department) -> None:
    """Strengthened from ``len(apply(())) > 0`` per ``compiler/FINDINGS.md`` §7.

    The rule is now the same one the decoy test uses: ``apply(probe)`` must
    differ from ``probe``. The old rule was satisfied by an identity lesion,
    one that returns its input untouched plants nothing and would report every
    detector shown it as blind to a violation that was never there.
    """
    for lesion in department.battery.lesions:
        probe = getattr(lesion, "probe", ())
        lesioned = lesion.apply(probe)
        assert not payloads_same(lesioned, probe), f"lesion {lesion.name!r} plants nothing"
        assert lesion.magnitude > 0, f"lesion {lesion.name!r} has no magnitude"


def test_the_lesion_magnitudes_span_more_than_one_scale(department) -> None:
    """A battery whose lesions are all the same size measures one threshold.

    Detector power is a function of magnitude, so a department that plants
    violations at a single size cannot report where its detectors go blind.
    """
    magnitudes = {lesion.magnitude for lesion in department.battery.lesions}
    assert len(magnitudes) > 1, f"{department.name} plants lesions at only one magnitude"


def test_every_instrument_describes_itself(department) -> None:
    members = (
        department.battery.target,
        *department.battery.rivals,
        *department.battery.decoys,
        *department.battery.surrogates,
        *department.battery.lesions,
    )
    for member in members:
        assert member.describe().strip(), f"{member.name!r} does not describe itself"


# ---------------------------------------------------------------------------
# 5. The integrity audit agrees, two expressions of the requirements
# ---------------------------------------------------------------------------
#
# ``harness.integrity.audit_department`` re-derives everything this file pins,
# in independent code, plus the measurements this file cannot make (declared
# detector power and specificity, payload symmetry, provenance). Running both
# here is the repository's two-backend habit applied to its own referee:
# where one has a bug, the other is the cross-check.


#: Departments whose declared detector is, by construction, the exact
#: negation of one of their reference claims, a *decision procedure* for the
#: property, not a heuristic whose power had to be estimated. The
#: ``detector-claim-agreement`` check added on 2026-08-09 cannot tell that
#: case from the sham it was built for, and ``docs/23`` §8 records why: the
#: ``detector-is-the-claim`` mode has two conjuncts, the detector is the
#: claim negated, *and* the lesion family was chosen to be exactly what it
#: looks for, and only the first is mechanically visible from this layer.
#:
#: These are recorded as failing rather than exempted. The check is not
#: weakened and the departments are not excused: each has an answer to give
#: (compiler's detector is exhaustive over i8; the referee's detector is the
#: audit itself, which its own module docstring calls "the recursion, and
#: also where it stops"), and until a department records that answer in a
#: form the audit can read, its detector's power really is its claim
#: measuring itself. The same idiom as ``docs/21`` §10.2's S2' xfail:
#: a negative result is pinned, not reframed.
_DETECTOR_IS_A_DECISION_PROCEDURE = {"compiler", "referee"}


def test_the_integrity_audit_grades_the_department_calibrated(department, request) -> None:
    report = audit_department(department)
    if department.name in _DETECTOR_IS_A_DECISION_PROCEDURE:
        assert report.grade == DETECTOR_INADEQUATE, report.render_text()
        assert report.check("detector-claim-agreement").status == "fail"
        request.node.add_report_section(
            "call", "open question", f"{department.name}: {report.grade}"
        )
        pytest.xfail(
            f"{department.name}'s declared detector is a reference claim negated. "
            "Open: docs/23 §8. The department must either declare why its detector "
            "is a decision procedure, or stake its power on an independent one."
        )
    assert report.grade == CALIBRATED, report.render_text()


def test_at_least_one_declared_detector_has_real_power(department) -> None:
    """Closes FINDINGS §8 for every registered department: some declared
    detector must notice at least one planted violation while staying quiet
    on the clean probe. Per-detector blindness remains legal and measured,
    the zeta criterion detector and the compiler concrete backend are blind
    to specific lesions on purpose, and that is the measurement."""
    informative = []
    for detector in department.detectors:
        verdict = run_detector(department.battery, detector)
        if not verdict.false_alarm and any(verdict.fired.values()):
            informative.append(detector.name)
    assert informative, (
        f"{department.name}: no declared detector notices any planted violation "
        "while staying quiet when clean, its silence is not a result"
    )


def test_the_department_states_the_scope_of_a_pass(department) -> None:
    assert department.scope.strip(), f"{department.name} declares no scope"
    verdict_words = ("distinguish", "agree", "verdict", "hold", "claim", "surviv")
    assert any(word in department.scope.lower() for word in verdict_words), (
        f"{department.name}'s scope does not say what a pass means: {department.scope!r}"
    )


@pytest.mark.slow
def test_every_surrogate_draws_a_sample(department) -> None:
    """A sample need not be sized, a program pair is a legitimate draw, but
    when it is sized it must be non-empty, and it must never be ``None``.
    (``compiler/FINDINGS.md`` §7: ``len(sample)`` was a zeta shape.)
    """
    for surrogate in department.battery.surrogates:
        sample = surrogate.sample()
        assert sample is not None, f"surrogate {surrogate.name!r} produced nothing"
        if hasattr(sample, "__len__"):
            assert len(sample) > 0, f"surrogate {surrogate.name!r} produced an empty sample"
