"""Department #4 (croniter), the audits beyond structural conformance.

``tests/test_department_conformance.py`` already checks this department the
same way it checks the other three. This file pins what conformance cannot
see (the sham-battery lesson: structure catches *missing* instruments, not
*empty* ones):

1. the vendored subject is byte-pinned, a silent edit to the frozen source
   changes every verdict's meaning and must fail loudly;
2. every instrument does real work: rivals genuinely disagree with the
   oracle, lesions change measured behavior, decoys collapse a real
   measurement, surrogates fail to reproduce the observation;
3. payloads expose behavior only, no field a claim could read as a label
   (the ``virtual_a_p`` counter-lesson, pinned here as in the finite-field
   department);
4. the lesion fingerprint is bounded: the re-emission lesion makes iteration
   non-monotonic, and the measurement must *record* that rather than hang.
"""

from __future__ import annotations

import hashlib
import sys
import time
from pathlib import Path

_REPO_ROOT = Path(__file__).resolve().parents[1]
if str(_REPO_ROOT) not in sys.path:  # pragma: no cover - import bootstrap
    sys.path.insert(0, str(_REPO_ROOT))

from harness.departments.croniter_department import (  # noqa: E402
    BATTERY,
    DEPARTMENT,
    LESIONS,
    PROBES,
    RIVALS,
    TARGET,
    _FROZEN,
    matches_independent_oracle,
    oracle_agreement,
    oracle_mismatch_detector,
    probe_distinguishing_power,
)
from harness.protocol import run_ablation, run_nulls, run_power  # noqa: E402

FROZEN_SHA256 = "d647e3429e3c43d5b6559f30e990a7f7d827b62e1e664ec7814d133aea13bef6"


def test_the_vendored_subject_is_byte_pinned() -> None:
    path = _REPO_ROOT / "harness/departments/croniter_fixtures/frozen_croniter.py"
    assert hashlib.sha256(path.read_bytes()).hexdigest() == FROZEN_SHA256, (
        "frozen_croniter.py changed: the department's verdicts are about a "
        "different implementation now, re-pin deliberately or revert"
    )


def test_the_oracle_is_satisfied_by_the_target_only() -> None:
    assert matches_independent_oracle(TARGET.payload())
    for rival in RIVALS:
        assert not matches_independent_oracle(rival.payload()), rival.name


def test_each_rival_disagrees_on_at_least_one_probe() -> None:
    target = TARGET.payload()
    for rival in RIVALS:
        r = rival.payload()
        diffs = 0
        for expr, start, n, _ in PROBES:
            try:
                if target(expr, start, n) != r(expr, start, n):
                    diffs += 1
            except Exception:
                diffs += 1
        assert diffs >= 1, f"{rival.name} never disagrees, it is not a rival"


def test_detector_has_power_over_all_three_lesions() -> None:
    verdict = run_power(BATTERY, oracle_mismatch_detector, payload=_FROZEN)
    assert verdict.has_power, f"blind to {verdict.blind_to}"
    assert verdict.smallest_detected is not None and verdict.smallest_detected > 0


def test_lesion_magnitudes_are_measured_not_asserted() -> None:
    for lesion in LESIONS:
        assert 0.0 < lesion.magnitude <= 1.0, lesion.name
    assert len({lesion.magnitude for lesion in LESIONS}) > 1


def test_the_reemission_lesion_is_measured_boundedly() -> None:
    """The nth-overlap lesion makes iteration jump backward; a naive
    iterate-until-stop measurement would hang on it (it did, twice, before
    this bound existed, once in calibration, once in this department's own
    first draft). Measuring its magnitude must terminate fast."""
    lesion = next(l for l in LESIONS if l.name == "nth-overlap-reemission")
    t0 = time.time()
    patched = lesion.apply(_FROZEN)
    assert oracle_mismatch_detector(patched)
    assert time.time() - t0 < 30.0


def test_decoys_collapse_the_probes_distinguishing_power() -> None:
    verdict = run_ablation(
        BATTERY,
        probe_distinguishing_power,
        tolerance=0.5,
        payload=[p[0] for p in PROBES],
    )
    assert verdict.baseline >= 1.0
    assert verdict.survives, f"unmoved by {verdict.unmoved_by}"
    assert all(v == 0.0 for v in verdict.decoys.values()), verdict.decoys


def test_no_surrogate_reproduces_oracle_agreement() -> None:
    verdict = run_nulls(BATTERY, oracle_agreement, tolerance=0.2, observed=1.0)
    assert verdict.survives, f"reproduced by {verdict.reproduced_by}"


def test_payloads_expose_behavior_only() -> None:
    """A claim receives a bare callable. There is no mapping, no label, no
    attribute that names which implementation it is, a claim that wants to
    tell the target from a rival has to measure dates."""
    for subject in (TARGET, *RIVALS):
        payload = subject.payload()
        assert callable(payload)
        assert not isinstance(payload, dict)
        assert not hasattr(payload, "name")
        assert subject.name not in repr(payload)


def test_the_department_is_listed_and_the_protocol_untouched() -> None:
    from harness.departments import KNOWN_DEPARTMENTS

    assert KNOWN_DEPARTMENTS["croniter"] == "harness.departments.croniter_department"
    # the admission claim is "the *unchanged* protocol carved a fourth
    # subject": croniter vocabulary must not have leaked into the seam
    protocol = (_REPO_ROOT / "harness/protocol.py").read_text(encoding="utf-8").lower()
    for word in ("croniter", "cron", "weekday", "schedule"):
        assert word not in protocol, f"protocol.py mentions {word!r}"


def test_honest_scope_is_stated_on_the_door() -> None:
    door = (_REPO_ROOT / DEPARTMENT.door).read_text(encoding="utf-8")
    assert "does not measure" in door and "outside team" in door, (
        "the door must state the open half of known gap #1, ingestion is "
        "measured, outside adoption is not"
    )
