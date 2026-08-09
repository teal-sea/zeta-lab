"""The demo and the scaffold — the two entry points, pinned to keep working.

A door whose first command errors is worse than no door, so both commands
named in the documentation are exercised here: the demo on one fast
department (with its machine-readable output checked for the pairing that
is the whole point), and the scaffold's three refusals — to overwrite, to
accept a bad name, and above all to produce something importable.
"""

from __future__ import annotations

import importlib
import json
import sys
from pathlib import Path

import pytest

_REPO_ROOT = Path(__file__).resolve().parents[1]
if str(_REPO_ROOT) not in sys.path:  # pragma: no cover - import bootstrap
    sys.path.insert(0, str(_REPO_ROOT))

from harness import demo, new_department  # noqa: E402


def test_the_demo_runs_one_department_and_writes_paired_reports(tmp_path, capsys) -> None:
    out = tmp_path / "reports.json"
    code = demo.main(["--department", "stateval", "--json", str(out)])
    assert code == 0
    printed = capsys.readouterr().out
    assert "DEPARTMENT: stateval" in printed
    assert "battery integrity: CALIBRATED" in printed
    reports = json.loads(out.read_text(encoding="utf-8"))
    assert reports, "the demo produced no machine-readable reports"
    for report in reports:
        # The pairing is the deliverable: no claim outcome without integrity.
        assert "claim_status" in report
        assert report["integrity"]["grade"]
        assert report["integrity"]["checks"]
        assert "audit_blind_spots" in report["integrity"]


def test_the_scaffold_writes_three_files_that_refuse_to_pretend(tmp_path) -> None:
    (tmp_path / "harness" / "departments").mkdir(parents=True)
    (tmp_path / "tests").mkdir()
    (tmp_path / "docs" / "doors").mkdir(parents=True)
    written = new_department.scaffold("probe_domain", root=tmp_path)
    assert len(written) == 3
    module = tmp_path / "harness" / "departments" / "probe_domain_department.py"
    assert "raise NotImplementedError" in module.read_text(encoding="utf-8")
    door = tmp_path / "docs" / "doors" / "probe_domain.md"
    assert "NOT YET ADMITTED" in door.read_text(encoding="utf-8")
    compiled = compile(module.read_text(encoding="utf-8"), str(module), "exec")
    with pytest.raises(NotImplementedError, match="scaffold"):
        exec(compiled, {"__name__": "probe_domain_department"})


def test_the_scaffold_refuses_to_overwrite(tmp_path) -> None:
    (tmp_path / "harness" / "departments").mkdir(parents=True)
    (tmp_path / "tests").mkdir()
    (tmp_path / "docs" / "doors").mkdir(parents=True)
    new_department.scaffold("probe_domain", root=tmp_path)
    with pytest.raises(SystemExit, match="refusing to overwrite"):
        new_department.scaffold("probe_domain", root=tmp_path)


def test_the_scaffold_refuses_a_bad_name() -> None:
    with pytest.raises(SystemExit, match="must match"):
        new_department.scaffold("Bad-Name")


def test_the_demo_module_is_not_part_of_the_agnostic_seam() -> None:
    """demo.py and new_department.py are applications: they may name
    departments, and must therefore never be added to the seam's
    domain-agnostic file list by accident."""
    protocol_tests = (_REPO_ROOT / "tests" / "test_harness_protocol.py").read_text(
        encoding="utf-8"
    )
    assert '"demo.py"' not in protocol_tests
    assert '"new_department.py"' not in protocol_tests
    importlib.import_module("harness.demo")
    importlib.import_module("harness.new_department")
