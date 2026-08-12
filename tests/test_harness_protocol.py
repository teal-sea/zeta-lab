"""Tests for ``harness.protocol`` — the falsification protocol, with no subject in it.

What is pinned here, in the order the design's claims are made:

1. **The admission rule bites.** A battery with no rival, no way to show
   emptiness, or no lesion is refused, and every reason is reported at once
   rather than one per run.
2. **A verdict cannot be flattered.** A subject that raises is recorded as an
   error and never counted as a pass or a refutation; a claim shared with any
   rival does not distinguish, however many rivals it excludes.
3. **The instruments read the right direction.** Ablation survives only when
   *every* decoy moves the measurement; a null control survives only when *no*
   surrogate reproduces the observation; a detector has power only when it
   notices *every* planted lesion.
4. **Departments are calibrated in both directions.** A department must name a
   claim its battery is expected to kill and one it is expected to pass; a
   battery that has only ever said "no" has not been shown to work.
5. **The seam holds.** The module imports nothing from any laboratory package
   (AST scan), pulls nothing into ``sys.modules`` when imported in a clean
   interpreter, and contains no subject-matter vocabulary (lexical scan).
"""

from __future__ import annotations

import ast
import re
import subprocess
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import Any

import pytest

_REPO_ROOT = Path(__file__).resolve().parents[1]
if str(_REPO_ROOT) not in sys.path:  # pragma: no cover - import bootstrap
    sys.path.insert(0, str(_REPO_ROOT))

from harness import protocol as P  # noqa: E402
from harness.protocol import (  # noqa: E402
    Battery,
    BatteryError,
    Department,
    DepartmentError,
    NamedDetector,
    ReferenceClaim,
    battery_reasons,
    clear_departments,
    department_reasons,
    get_department,
    list_departments,
    register_department,
    run_ablation,
    run_battery,
    run_detector,
    run_nulls,
    run_power,
    unregister_department,
    validate_battery,
    validate_department,
)


# ---------------------------------------------------------------------------
# Minimal stand-ins. Deliberately arithmetic-free: if these tests needed the
# laboratory to run, the seam they exist to check would already be broken.
# ---------------------------------------------------------------------------


@dataclass(frozen=True)
class FakeSubject:
    name: str
    value: Any = 1.0

    def describe(self) -> str:
        return f"fake subject {self.name}"

    def payload(self) -> Any:
        return self.value


@dataclass(frozen=True)
class FakeDecoy:
    name: str
    delta: float = 10.0

    def describe(self) -> str:
        return f"adds {self.delta}"

    def substitute(self, payload: Any) -> Any:
        return payload + self.delta


@dataclass(frozen=True)
class FakeSurrogate:
    name: str
    value: float = 99.0

    def describe(self) -> str:
        return f"always {self.value}"

    def sample(self) -> Any:
        return self.value


@dataclass(frozen=True)
class FakeLesion:
    name: str
    magnitude: float

    def describe(self) -> str:
        return f"adds {self.magnitude}"

    def apply(self, payload: Any) -> Any:
        return payload + self.magnitude


def _battery(**overrides) -> Battery:
    kwargs = dict(
        name="fake",
        target=FakeSubject("target", 1.0),
        rivals=(FakeSubject("rival_a", 2.0), FakeSubject("rival_b", 3.0)),
        decoys=(FakeDecoy("decoy"),),
        surrogates=(FakeSurrogate("null"),),
        lesions=(FakeLesion("big", 1.0), FakeLesion("small", 0.001)),
    )
    kwargs.update(overrides)
    return Battery(**kwargs)


# ---------------------------------------------------------------------------
# 1. The admission rule
# ---------------------------------------------------------------------------


def test_a_complete_battery_validates() -> None:
    assert battery_reasons(_battery()) == ()
    validate_battery(_battery())


@pytest.mark.parametrize(
    "missing, fragment",
    [
        ("rivals", "no rival"),
        ("lesions", "no lesion"),
    ],
)
def test_a_battery_that_cannot_fail_is_refused(missing, fragment) -> None:
    reasons = battery_reasons(_battery(**{missing: ()}))
    assert any(fragment in reason for reason in reasons), reasons


def test_a_battery_with_no_way_to_show_emptiness_is_refused() -> None:
    reasons = battery_reasons(_battery(decoys=(), surrogates=()))
    assert any("neither decoy nor surrogate" in reason for reason in reasons), reasons


def test_a_decoy_alone_satisfies_the_emptiness_requirement() -> None:
    assert battery_reasons(_battery(surrogates=())) == ()


def test_a_surrogate_alone_satisfies_the_emptiness_requirement() -> None:
    assert battery_reasons(_battery(decoys=())) == ()


def test_every_violation_is_reported_at_once() -> None:
    reasons = battery_reasons(_battery(rivals=(), decoys=(), surrogates=(), lesions=()))
    assert len(reasons) >= 3, reasons


def test_validate_battery_raises_with_every_reason_in_the_message() -> None:
    with pytest.raises(BatteryError) as excinfo:
        validate_battery(_battery(rivals=(), lesions=()))
    message = str(excinfo.value)
    assert "no rival" in message and "no lesion" in message


def test_the_target_may_not_also_be_a_rival() -> None:
    target = FakeSubject("same", 1.0)
    reasons = battery_reasons(_battery(target=target, rivals=(FakeSubject("same", 2.0),)))
    assert any("also listed as a rival" in reason for reason in reasons), reasons


def test_duplicate_member_names_are_refused() -> None:
    reasons = battery_reasons(_battery(rivals=(FakeSubject("dup", 2.0), FakeSubject("dup", 3.0))))
    assert any("more than one member named" in reason for reason in reasons), reasons


def test_a_role_missing_its_methods_is_named_in_the_reasons() -> None:
    class Broken:
        name = "broken"

    reasons = battery_reasons(_battery(rivals=(Broken(),)))
    assert any("broken" in reason and "payload" in reason for reason in reasons), reasons


# ---------------------------------------------------------------------------
# 2. A verdict cannot be flattered
# ---------------------------------------------------------------------------


def test_a_claim_true_of_everything_distinguishes_nothing() -> None:
    verdict = run_battery(_battery(), lambda payload: True, name="always")
    assert verdict.target is True
    assert verdict.distinguishes is False
    assert verdict.shared_with == ("rival_a", "rival_b")
    assert "distinguishes nothing" in verdict.summary()


def test_a_claim_true_only_of_the_target_distinguishes() -> None:
    verdict = run_battery(_battery(), lambda payload: payload == 1.0, name="only_target")
    assert verdict.distinguishes is True
    assert verdict.shared_with == ()


def test_a_claim_shared_with_one_rival_out_of_two_still_fails() -> None:
    verdict = run_battery(_battery(), lambda payload: payload in (1.0, 2.0), name="two")
    assert verdict.distinguishes is False
    assert verdict.shared_with == ("rival_a",)


def test_a_claim_that_does_not_fire_for_the_target_does_not_distinguish() -> None:
    verdict = run_battery(_battery(), lambda payload: False, name="never")
    assert verdict.target is False
    assert verdict.distinguishes is False


def test_a_subject_that_raises_is_recorded_and_never_counted_as_a_refutation() -> None:
    def explode(payload):
        if payload == 2.0:
            raise ValueError("boom")
        return True

    verdict = run_battery(_battery(), explode, name="explodes")
    assert "rival_a" in verdict.errors
    assert "ValueError" in verdict.errors["rival_a"]
    # The rival did not answer, so the claim has NOT been shown to exclude it.
    assert verdict.distinguishes is False
    assert "inconclusive" in verdict.summary()


def test_run_battery_refuses_an_inadmissible_battery() -> None:
    with pytest.raises(BatteryError):
        run_battery(_battery(rivals=()), lambda payload: True)


# ---------------------------------------------------------------------------
# 3. The instruments read the right direction
# ---------------------------------------------------------------------------


def test_ablation_survives_only_when_every_decoy_moves_the_measurement() -> None:
    battery = _battery(decoys=(FakeDecoy("moves", 10.0), FakeDecoy("barely", 0.0)))
    verdict = run_ablation(battery, lambda payload: float(payload), tolerance=1.0)
    assert verdict.baseline == 1.0
    assert verdict.survives is False
    assert verdict.unmoved_by == ("barely",)


def test_ablation_survives_when_all_decoys_move_it() -> None:
    verdict = run_ablation(_battery(), lambda payload: float(payload), tolerance=1.0)
    assert verdict.survives is True
    assert verdict.unmoved_by == ()


def test_a_null_control_dies_when_a_surrogate_reproduces_the_observation() -> None:
    battery = _battery(surrogates=(FakeSurrogate("matches", 1.0), FakeSurrogate("differs", 99.0)))
    verdict = run_nulls(battery, lambda payload: float(payload), tolerance=0.1)
    assert verdict.observed == 1.0
    assert verdict.survives is False
    assert verdict.reproduced_by == ("matches",)


def test_a_null_control_survives_when_no_surrogate_comes_close() -> None:
    verdict = run_nulls(_battery(), lambda payload: float(payload), tolerance=0.1)
    assert verdict.survives is True
    assert verdict.reproduced_by == ()


def test_an_observed_value_may_be_supplied_instead_of_recomputed() -> None:
    verdict = run_nulls(
        _battery(), lambda payload: float(payload), tolerance=0.1, observed=42.0
    )
    assert verdict.observed == 42.0


def test_a_null_band_counts_exceedances_over_many_draws() -> None:
    class CountingSurrogate:
        name = "counting"

        def __init__(self) -> None:
            self.calls = 0

        def describe(self) -> str:
            return "yields 0.0, 1.0, 2.0, ..."

        def sample(self) -> float:
            value = float(self.calls)
            self.calls += 1
            return value

    battery = _battery(surrogates=(CountingSurrogate(),))
    verdict = P.run_null_band(
        battery, lambda payload: float(payload), draws=5, observed=3.5, name="stat"
    )
    assert verdict.total_draws == 5
    assert verdict.draws["counting"] == (0.0, 1.0, 2.0, 3.0, 4.0)
    assert verdict.exceedances == {"counting": 1}  # the 4.0 draw reached it
    assert verdict.survives is False
    assert "5 draws" in verdict.summary()


def test_a_null_band_with_no_reaching_draw_survives_and_states_its_size() -> None:
    verdict = P.run_null_band(
        _battery(), lambda payload: float(payload), draws=3, observed=1000.0
    )
    assert verdict.survives is True
    assert verdict.total_draws == 3
    assert "3 draws" in verdict.summary()


def test_a_deterministic_surrogate_gives_a_visibly_degenerate_band() -> None:
    verdict = P.run_null_band(_battery(), lambda payload: float(payload), draws=4)
    assert verdict.draws["null"] == (99.0, 99.0, 99.0, 99.0)
    assert verdict.band == (99.0, 99.0)


def test_run_null_band_refuses_zero_draws() -> None:
    with pytest.raises(BatteryError, match="at least one draw"):
        P.run_null_band(_battery(), lambda payload: float(payload), draws=0)


def test_a_detector_blind_to_a_lesion_has_no_power() -> None:
    # Fires only when the planted violation is larger than 0.5.
    verdict = run_power(_battery(), lambda payload: float(payload) > 1.5)
    assert verdict.fired == {"big": True, "small": False}
    assert verdict.blind_to == ("small",)
    assert verdict.has_power is False
    assert verdict.smallest_detected == 1.0


def test_a_detector_that_notices_every_lesion_has_power() -> None:
    verdict = run_power(_battery(), lambda payload: float(payload) > 1.0)
    assert verdict.has_power is True
    assert verdict.blind_to == ()


def test_an_explicit_payload_may_be_given_to_ablation_and_power() -> None:
    # The four instruments legitimately consume different objects.
    ablation = run_ablation(
        _battery(), lambda payload: float(payload), tolerance=1.0, payload=100.0
    )
    assert ablation.baseline == 100.0
    power = run_power(_battery(), lambda payload: float(payload) > 100.5, payload=100.0)
    assert power.fired["big"] is True


# ---------------------------------------------------------------------------
# 4. Departments are calibrated in both directions
# ---------------------------------------------------------------------------


def _department(**overrides) -> Department:
    kwargs = dict(
        name="fake",
        summary="a department for testing",
        battery=_battery(),
        door="docs/doors/fake.md",
        reference_claims=(
            ReferenceClaim("kills", lambda payload: True, distinguishes=False),
            ReferenceClaim("passes", lambda payload: payload == 1.0, distinguishes=True),
        ),
        detectors=(
            NamedDetector("threshold", lambda payload: float(payload) > 1.005, probe=1.0),
        ),
        scope="a fake scope for testing",
    )
    kwargs.update(overrides)
    return Department(**kwargs)


def test_a_complete_department_validates() -> None:
    assert department_reasons(_department()) == ()


def test_a_department_with_no_door_is_refused() -> None:
    reasons = department_reasons(_department(door=""))
    assert any("no door" in reason for reason in reasons), reasons


def test_a_department_whose_door_is_not_a_document_is_refused() -> None:
    reasons = department_reasons(_department(door="zeta/core.py"))
    assert any("not a document" in reason for reason in reasons), reasons


def test_a_department_that_never_shows_its_battery_saying_no_is_refused() -> None:
    reasons = department_reasons(
        _department(
            reference_claims=(ReferenceClaim("passes", lambda p: p == 1.0, distinguishes=True),)
        )
    )
    assert any("expected to kill" in reason for reason in reasons), reasons


def test_a_department_that_never_shows_its_battery_saying_yes_is_refused() -> None:
    reasons = department_reasons(
        _department(reference_claims=(ReferenceClaim("kills", lambda p: True, distinguishes=False),))
    )
    assert any("expected to pass" in reason for reason in reasons), reasons


def test_a_department_with_a_broken_battery_reports_it_as_a_battery_problem() -> None:
    reasons = department_reasons(_department(battery=_battery(rivals=())))
    assert any(reason.startswith("battery: ") for reason in reasons), reasons


def test_validate_department_raises_for_an_inadmissible_department() -> None:
    with pytest.raises(DepartmentError):
        validate_department(_department(reference_claims=()))


def test_a_department_with_no_detector_is_refused() -> None:
    """FINDINGS §8 closed: lesions without a declared detector are power theater."""
    reasons = department_reasons(_department(detectors=()))
    assert any("no detector" in reason for reason in reasons), reasons


def test_a_department_with_no_scope_is_refused() -> None:
    reasons = department_reasons(_department(scope=""))
    assert any("no scope" in reason for reason in reasons), reasons


# ---------------------------------------------------------------------------
# 4b. Declared detectors: power and specificity measured together
# ---------------------------------------------------------------------------


def test_run_detector_measures_power_and_stays_quiet_when_clean() -> None:
    detector = NamedDetector("threshold", lambda payload: float(payload) > 1.005, probe=1.0)
    verdict = run_detector(_battery(), detector)
    assert verdict.false_alarm is False
    assert verdict.fired == {"big": True, "small": False}
    assert verdict.blind_to == ("small",)
    assert verdict.has_power is False  # blind to one planted violation


def test_a_constant_true_detector_has_no_power_despite_perfect_sensitivity() -> None:
    """The hole PowerVerdict could not see: an alarm that is always on
    notices every lesion and carries no information."""
    always = NamedDetector("always", lambda payload: True, probe=1.0)
    verdict = run_detector(_battery(), always)
    assert verdict.fired == {"big": True, "small": True}  # perfect lesion record
    assert verdict.false_alarm is True
    assert verdict.has_power is False
    assert "no information" in verdict.summary()


def test_a_full_power_detector_reports_it() -> None:
    detector = NamedDetector("sharp", lambda payload: float(payload) > 1.0005, probe=1.0)
    verdict = run_detector(_battery(), detector)
    assert verdict.false_alarm is False
    assert verdict.has_power is True
    assert verdict.smallest_detected == 0.001


# ---------------------------------------------------------------------------
# The registry
# ---------------------------------------------------------------------------


@pytest.fixture
def clean_registry():
    saved = {name: get_department(name) for name in list_departments()}
    clear_departments()
    yield
    clear_departments()
    for department in saved.values():
        register_department(department, replace=True)


def test_a_department_round_trips_through_the_registry(clean_registry) -> None:
    department = _department()
    register_department(department)
    assert list_departments() == ("fake",)
    assert get_department("fake") is department


def test_registering_the_same_name_twice_is_refused(clean_registry) -> None:
    register_department(_department())
    with pytest.raises(DepartmentError, match="already registered"):
        register_department(_department())


def test_replace_permits_re_registration(clean_registry) -> None:
    register_department(_department())
    register_department(_department(summary="a different summary"), replace=True)
    assert get_department("fake").summary == "a different summary"


def test_an_unknown_department_names_the_ones_that_exist(clean_registry) -> None:
    register_department(_department())
    with pytest.raises(DepartmentError, match="fake"):
        get_department("nonexistent")


def test_an_inadmissible_department_never_enters_the_registry(clean_registry) -> None:
    with pytest.raises(DepartmentError):
        register_department(_department(reference_claims=()))
    assert list_departments() == ()


def test_unregister_is_idempotent(clean_registry) -> None:
    unregister_department("never-existed")
    register_department(_department())
    unregister_department("fake")
    unregister_department("fake")
    assert list_departments() == ()


# ---------------------------------------------------------------------------
# 5. The seam
# ---------------------------------------------------------------------------

_FORBIDDEN_ROOTS = ("zeta", "ontology", "numpy", "scipy", "mpmath", "sympy", "matplotlib", "flint")

_DOMAIN_AGNOSTIC_FILES = (
    "__init__.py",
    "protocol.py",
    "provenance.py",
    "independence.py",
    "guards.py",
    "review.py",
    "graveyard.py",
    "integrity.py",
    "shams.py",
    "preregistration.py",
    "promotion.py",
)


def _harness_dir() -> Path:
    return Path(P.__file__).resolve().parent


@pytest.mark.parametrize("filename", _DOMAIN_AGNOSTIC_FILES)
def test_the_protocol_imports_nothing_from_any_laboratory(filename) -> None:
    tree = ast.parse((_harness_dir() / filename).read_text(encoding="utf-8"))
    imported: list[str] = []
    for node in ast.walk(tree):
        if isinstance(node, ast.Import):
            imported.extend(alias.name for alias in node.names)
        elif isinstance(node, ast.ImportFrom) and node.level == 0 and node.module:
            imported.append(node.module)
    for name in imported:
        root = name.split(".")[0]
        assert root not in _FORBIDDEN_ROOTS, f"{filename} imports {name}"


def test_importing_the_protocol_pulls_in_no_laboratory_module() -> None:
    code = (
        "import sys; sys.path.insert(0, %r);"
        "import harness.protocol, harness.provenance, harness.independence,"
        " harness.guards, harness.review, harness.integrity, harness.shams;"
        "bad=[m for m in sys.modules if m.split('.')[0] in %r];"
        "print(','.join(sorted(bad)))" % (str(_REPO_ROOT), _FORBIDDEN_ROOTS)
    )
    result = subprocess.run(
        [sys.executable, "-c", code], capture_output=True, text=True, timeout=120
    )
    assert result.returncode == 0, result.stderr
    assert result.stdout.strip() == "", f"laboratory modules imported: {result.stdout.strip()}"


#: Words that would mean the protocol had learned its subject. ``prime`` is
#: absent from this list on purpose: it appears in ordinary English ("primary",
#: "prime example") and the AST and ``sys.modules`` checks already forbid the
#: import that would make it load-bearing.
_SUBJECT_VOCABULARY = (
    "zeta",
    "riemann",
    "hypothesis",
    "euler",
    "dirichlet",
    "critical line",
    "eigenvalue",
    "modular",
    "davenport",
    "epstein",
)


@pytest.mark.parametrize("filename", _DOMAIN_AGNOSTIC_FILES)
def test_the_protocol_contains_no_subject_matter_vocabulary(filename) -> None:
    source = (_harness_dir() / filename).read_text(encoding="utf-8").lower()
    for word in _SUBJECT_VOCABULARY:
        assert not re.search(rf"\b{re.escape(word)}\b", source), (
            f"{filename} names {word!r}: the protocol has learned its subject"
        )
