"""The guard ledger's conformance, and the three opening demonstrations.

A guard ledger whose mutants nothing executes would be a self-validating log,
so each ``fired=True`` record in ``harness/departments/guard_ledger.py``
points back at a test *in this file* that constructs the smallest mutant and
watches the guard's own logic fire on it. The conformance half checks the
ledger keeps its bookkeeping honest: outcomes cost artifacts, artifacts name
tests that exist, and the undemonstrated entries surface as worklist.
"""

from __future__ import annotations

import importlib.util
import sys
from fractions import Fraction
from pathlib import Path

import pytest

_REPO_ROOT = Path(__file__).resolve().parent.parent
if str(_REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(_REPO_ROOT))

from harness.departments.guard_ledger import GUARDS  # noqa: E402
from harness.guards import (  # noqa: E402
    GuardRecord,
    GuardRecordError,
    dead_guards,
    offensive_worklist,
    undemonstrated,
)


def _load_test_module(name: str):
    """Import a sibling test module by file path (tests/ is not a package)."""
    path = Path(__file__).parent / f"{name}.py"
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


# ---------------------------------------------------------------------------
# 1. record validation: outcomes cost artifacts
# ---------------------------------------------------------------------------


def test_an_outcome_without_a_demonstration_is_refused() -> None:
    with pytest.raises(GuardRecordError, match="claim, not a measurement"):
        GuardRecord(
            name="g", guards_against="x", smallest_mutant="m", fired=True
        )


def test_a_demonstration_without_an_outcome_is_refused() -> None:
    with pytest.raises(GuardRecordError, match="record what the demonstration"):
        GuardRecord(
            name="g",
            guards_against="x",
            smallest_mutant="m",
            fired=None,
            demonstrated_by="somewhere",
        )


def test_a_guard_without_a_stated_lesion_is_refused() -> None:
    with pytest.raises(GuardRecordError, match="cannot be stated"):
        GuardRecord(name="g", guards_against="  ", smallest_mutant="m", fired=None)


# ---------------------------------------------------------------------------
# 2. ledger conformance
# ---------------------------------------------------------------------------


def test_the_ledger_is_non_empty_and_every_record_validates() -> None:
    assert GUARDS, "the guard ledger is empty"
    # Construction already validated each record; pin the shape too.
    assert all(isinstance(r, GuardRecord) for r in GUARDS)


def test_every_demonstration_artifact_in_this_file_exists() -> None:
    own_source = Path(__file__).read_text(encoding="utf-8")
    for record in GUARDS:
        if record.fired is None:
            continue
        artifact = record.demonstrated_by
        if artifact.startswith("tests/test_guard_ledger.py::"):
            test_name = artifact.split("::", 1)[1]
            assert f"def {test_name}(" in own_source, (
                f"guard {record.name!r} cites demonstration {test_name!r}, "
                "which this file does not define"
            )
        else:
            # Demonstrations may live outside tests/ (a standalone mutation
            # run, say). The file still has to be on disk, or the record
            # cites something nobody can rerun.
            path = _REPO_ROOT / artifact.split("::", 1)[0].split(" ", 1)[0]
            assert path.exists(), (
                f"guard {record.name!r} cites demonstration artifact "
                f"{str(path)!r}, which is not in the tree"
            )


def test_the_worklist_surfaces_the_undemonstrated_entries() -> None:
    open_names = undemonstrated(GUARDS)
    assert "tests/test_doors.py" in open_names
    # 'scripts/make_context.py --check' left this list on 2026-08-13, when
    # hunts/r_414eed/probe.py ran 24 mutants past it. The entry moving off
    # the worklist is the ledger working: an outcome cost a demonstration.
    assert "scripts/make_context.py --check" not in open_names
    reasons = offensive_worklist(GUARDS)
    assert any("never had its power demonstrated" in r for r in reasons)
    # Known misses surface too: the ledger implies work even where guards fire.
    assert any("does not detect" in r for r in reasons)


def test_no_guard_is_currently_recorded_dead() -> None:
    # If this ever fails, the correct response is to read the record, not to
    # delete it: a dead guard is a finding (docs/25 found three).
    assert dead_guards(GUARDS) == ()


# ---------------------------------------------------------------------------
# 3. the demonstrations: smallest mutant in, guard fires
# ---------------------------------------------------------------------------


def test_the_exact_guard_rejects_the_repr_parse() -> None:
    """The docs/25 lesion, reconstructed: repr-parsing an np.float32."""
    np = pytest.importorskip("numpy")
    import zeta.rigor as rigor

    value = np.float32(21.02203941345215)
    lesioned = Fraction(str(value))  # the old fall-through: printed decimal
    true_exact = Fraction(float(value))
    # The mutant produces a different rational than the binary value — the
    # abscissa moves — and the guard's pinned equality is what refuses it.
    assert lesioned != true_exact
    assert rigor._exact(value) == true_exact != lesioned


def test_the_numbering_guard_fires_on_a_duplicate(tmp_path, monkeypatch) -> None:
    """A docs tree with 05-a.md and 05-b.md must trip the uniqueness check."""
    numbering = _load_test_module("test_docs_numbering")
    (tmp_path / "05-a.md").write_text("a\n", encoding="utf-8")
    (tmp_path / "05-b.md").write_text("b\n", encoding="utf-8")
    monkeypatch.setattr(numbering, "DOCS", str(tmp_path))
    with pytest.raises(AssertionError, match="share a leading number"):
        numbering.test_no_two_docs_share_a_number()
    # Control: with the duplicate removed, the same guard is silent.
    (tmp_path / "05-b.md").unlink()
    numbering.test_no_two_docs_share_a_number()


def test_the_pub1_status_guard_fires_on_a_flipped_grade(tmp_path, monkeypatch) -> None:
    """A docs/27 row claiming the grade OBLIGATIONS.md does not must trip the check.

    The mutant is the defect as it actually occurred on 2026-08-17, in the
    direction that matters: the row bolds a grade the obligations file
    contradicts. Both directions are exercised, because a guard that only
    fires when the doc underclaims would be silent on the expensive case — a
    row saying *unconditional* after an obligation reopened.
    """
    status_guard = _load_test_module("test_pub1_status")

    obligations = tmp_path / "OBLIGATIONS.md"
    doc = tmp_path / "27.md"
    row = (
        "| 3 | The Pub 1 source-admissible strong closure: **{grade}** "
        "since 2026-08-16. | `lean/ZetaLean/Pub1.lean` |\n"
    )
    monkeypatch.setattr(status_guard, "OBLIGATIONS", obligations)
    monkeypatch.setattr(status_guard, "DOC27", doc)

    # Mutant A — obligations CLOSED, row still says Conditional (the real defect).
    obligations.write_text("# Pub 1 strong closure — status: CLOSED\n", encoding="utf-8")
    doc.write_text(row.format(grade="Conditional"), encoding="utf-8")
    with pytest.raises(AssertionError, match="must claim"):
        status_guard.test_docs_27_states_the_grade_the_obligations_file_declares()

    # Control: the corrected row is silent against the same obligations file.
    doc.write_text(row.format(grade="Unconditional"), encoding="utf-8")
    status_guard.test_docs_27_states_the_grade_the_obligations_file_declares()

    # Mutant B — the expensive direction: an obligation reopens, the row does not.
    obligations.write_text("# Pub 1 strong closure — status: OPEN\n", encoding="utf-8")
    with pytest.raises(AssertionError, match="must claim"):
        status_guard.test_docs_27_states_the_grade_the_obligations_file_declares()

    # Mutant C — a status nobody has taught the guard is undecided, not benign.
    obligations.write_text("# Pub 1 strong closure — status: PARTIAL\n", encoding="utf-8")
    with pytest.raises(AssertionError, match="does not know how to check"):
        status_guard.test_the_declared_status_is_one_this_guard_understands()


def test_the_reserved_word_guard_fires_on_a_probe_file(tmp_path, monkeypatch) -> None:
    """One overclaiming probe file must trip the lexical scan."""
    discipline = _load_test_module("test_hunt_probe_discipline")
    hunt = tmp_path / "mutant_hunt"
    hunt.mkdir()
    (hunt / "MISSION.md").write_text(
        "this bound is " + "certi" + "fied by the probe\n", encoding="utf-8"
    )
    monkeypatch.setattr(discipline, "_HUNTS", tmp_path)
    monkeypatch.setattr(discipline, "_REPO_ROOT", tmp_path)
    with pytest.raises(AssertionError, match="reserved word"):
        discipline.test_no_hunt_claims_the_reserved_word()
    # Control: the same tree without the word passes.
    (hunt / "MISSION.md").write_text("this bound is measured\n", encoding="utf-8")
    discipline.test_no_hunt_claims_the_reserved_word()
