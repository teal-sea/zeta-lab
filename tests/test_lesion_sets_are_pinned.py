"""The catcher for ``dropped-hardest-lesion``, which was never built.

``harness.integrity.SHAM_MODES`` lists fifteen ways a battery can be hollow and
marks six of them ``caught_by=None``: modes the audit declares it cannot detect.
One of those six is ``dropped-hardest-lesion``, silently removing the lesion the
detectors struggle with so an easier battery ships under the same name.

Its own ``countermeasure`` field reads:

    "no mechanical check can know what was meant to be there; **pin the lesion
    set in tests**, declare frozen_before_execution in provenance"

The first clause is true and the second clause is a build instruction, and the
build instruction was never followed.  The mode was carried as mechanically
uncatchable for as long as the fix sat unwritten in the same string.

This file writes it.  A mechanical check cannot know what a lesion set *should*
contain, but a pinned set makes any later removal or weakening a failing test,
which is all the mode requires.  ``docs/28`` is the measurement that removed the
excuse for not doing this: two of the three blind spots were caught by no
checker at all, human or model, so "an independent party would notice" is not
load-bearing and the repository has to catch this itself.

Scope, stated so it is not overread: this catches *removal and alteration* of a
lesion in a department whose set is pinned below.  It does not know whether the
original set was adequate, and it cannot.  Adequacy is a judgment; regression is
a test.
"""

from __future__ import annotations

import importlib

import pytest

# name -> the exact lesion set, (lesion name, magnitude) in order.
# Regenerate deliberately, never to make a red test green: a diff here is either
# a lesion you meant to change or exactly the sham this file exists to catch.
PINNED_LESIONS: dict[str, tuple[tuple[str, float], ...]] = {
    "zeta_department": (
        ("off_line_delta_0_1", 0.1),
        ("off_line_delta_0_01", 0.01),
        ("off_line_delta_0_001", 0.001),
    ),
    "finitefield_department": (
        ("off_circle_trace_64", 0.1293327244592113),
        ("off_circle_trace_80", 1.0245860776735891),
        ("off_circle_trace_128", 2.7639439498514076),
    ),
    "compiler_department": (
        ("signed_to_unsigned_predicate", 0.5),
        ("strict_to_nonstrict_predicate", 0.00390625),
        ("single_point_special_case", 1.52587890625e-05),
        ("nsw_flag_on_a_wrapping_shift", 0.5),
    ),
    "croniter_department": (
        ("default-compat-regression", 0.05),
        ("nth-overlap-reemission", 0.35),
        ("range-ignores-flag", 0.05),
    ),
    "referee_department": (
        ("plant-constant-true-detector", 0.1053),
        ("plant-target-as-rival", 0.0526),
        ("plant-inert-lesions", 0.1053),
        ("plant-leaked-label", 0.0526),
    ),
    "stateval_department": (
        ("leak-0_03125", 0.03125),
        ("leak-0_25", 0.25),
        ("leak-0_75", 0.75),
    ),
}


def _department(name: str):
    module = importlib.import_module(f"harness.departments.{name}")
    return module.DEPARTMENT


def _lesion_set(department) -> tuple[tuple[str, float], ...]:
    return tuple(
        (lesion.name, float(lesion.magnitude)) for lesion in department.battery.lesions
    )


@pytest.mark.parametrize("name", sorted(PINNED_LESIONS))
def test_lesion_set_is_unchanged(name: str):
    """Any removal, addition or reweighting of a lesion fails here."""
    observed = _lesion_set(_department(name))
    expected = PINNED_LESIONS[name]
    assert observed == expected, (
        f"{name}'s lesion set changed.\n"
        f"  pinned:   {expected}\n"
        f"  observed: {observed}\n"
        "If this change is intentional, update PINNED_LESIONS deliberately and "
        "say why in the commit. If it is not, this is the dropped-hardest-lesion "
        "sham, and catching it is the whole reason this file exists."
    )


@pytest.mark.parametrize("name", sorted(PINNED_LESIONS))
def test_the_hardest_lesion_is_still_present(name: str):
    """Name the weakest-magnitude lesion explicitly, since it is the target.

    ``harness.shams.without_hardest_lesion`` removes the *minimum* magnitude
    lesion, that being the one detectors struggle with most. Asserting the
    minimum separately means the mode fails a test whose message says what
    happened, rather than a generic set comparison.
    """
    observed = _lesion_set(_department(name))
    expected = PINNED_LESIONS[name]
    hardest = min(expected, key=lambda pair: pair[1])
    assert hardest in observed, (
        f"{name} lost its hardest lesion {hardest[0]!r} (magnitude {hardest[1]}). "
        "That is the dropped-hardest-lesion sham exactly: an easier battery "
        "shipping under the same name."
    )


@pytest.mark.parametrize("name", sorted(PINNED_LESIONS))
def test_the_pin_actually_catches_the_sham(name: str):
    """The negative control: plant the sham and confirm this file goes red.

    A guard that has never been shown to fire is a guard on paper. This runs
    ``without_hardest_lesion`` against each department and asserts the pinned
    set no longer matches, so the catcher is demonstrated rather than asserted.
    """
    from harness.shams import without_hardest_lesion

    department = _department(name)
    corrupted = without_hardest_lesion(department)
    assert _lesion_set(corrupted) != PINNED_LESIONS[name], (
        f"planting dropped-hardest-lesion in {name} did not change the lesion "
        "set, so this file would not catch it"
    )
    hardest = min(PINNED_LESIONS[name], key=lambda pair: pair[1])
    assert hardest not in _lesion_set(corrupted)


def test_every_department_with_lesions_is_pinned():
    """A new department must not silently escape the pin.

    Without this, the mode returns for any battery added later: the catcher
    would cover exactly the departments that existed when it was written.
    """
    from harness.departments import __all__ as exported  # noqa: F401

    candidates = [
        "zeta_department",
        "finitefield_department",
        "compiler_department",
        "croniter_department",
        "referee_department",
        "stateval_department",
    ]
    for name in candidates:
        department = _department(name)
        if department.battery.lesions:
            assert name in PINNED_LESIONS, (
                f"{name} has lesions but no entry in PINNED_LESIONS; "
                "dropped-hardest-lesion is uncaught for it"
            )
