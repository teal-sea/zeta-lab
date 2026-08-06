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
from harness.protocol import (  # noqa: E402
    department_reasons,
    get_department,
    run_battery,
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
# 3. Calibrated in both directions — the labels are re-derived, not trusted
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
    """Not merely 'does not distinguish' — it must fail *for the stated reason*.

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
    probe = list(range(2, 60))
    for decoy in department.battery.decoys:
        substituted = decoy.substitute(probe)
        assert list(substituted) != probe, (
            f"decoy {decoy.name!r} returned its input unchanged and ablates nothing"
        )
        assert len(list(substituted)) == len(probe), (
            f"decoy {decoy.name!r} changed the size of the input; it is not a substitution"
        )


def test_every_lesion_plants_something(department) -> None:
    for lesion in department.battery.lesions:
        lesioned = lesion.apply(())
        assert len(tuple(lesioned)) > 0, f"lesion {lesion.name!r} plants nothing"
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


@pytest.mark.slow
def test_every_surrogate_draws_a_sample(department) -> None:
    for surrogate in department.battery.surrogates:
        sample = surrogate.sample()
        assert len(sample) > 0, f"surrogate {surrogate.name!r} produced nothing"
