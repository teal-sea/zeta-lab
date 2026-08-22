from __future__ import annotations

import importlib.util
from pathlib import Path


_ROOT = Path(__file__).resolve().parents[1]
_SCRIPT = _ROOT / "scripts" / "71_contribution_check.py"
_SPEC = importlib.util.spec_from_file_location("contribution_check", _SCRIPT)
assert _SPEC and _SPEC.loader
_MODULE = importlib.util.module_from_spec(_SPEC)
_SPEC.loader.exec_module(_MODULE)
structural_problems = _MODULE.structural_problems


def _fixture(tmp_path: Path) -> Path:
    hunts = tmp_path / "hunts"
    hunt = hunts / "outside_probe"
    hunt.mkdir(parents=True)
    (hunts / "README.md").write_text("outside_probe\n", encoding="utf-8")
    (hunt / "MISSION.md").write_text("```huntspec\nquestion: Q\n```\n", encoding="utf-8")
    (hunt / "RUNS.md").write_text("```runmanifest\nid: R\n```\n", encoding="utf-8")
    (hunt / "RESULTS.md").write_text("The bounded run found nothing.\n", encoding="utf-8")
    return hunt


def test_complete_external_hunt_has_no_structural_problems(tmp_path: Path) -> None:
    hunt = _fixture(tmp_path)
    assert structural_problems(tmp_path, hunt) == []


def test_missing_run_record_and_case_log_are_reported(tmp_path: Path) -> None:
    hunt = _fixture(tmp_path)
    (hunt / "RUNS.md").unlink()
    (tmp_path / "hunts" / "README.md").write_text("other_hunt\n", encoding="utf-8")
    problems = structural_problems(tmp_path, hunt)
    assert "missing hunts/outside_probe/RUNS.md" in problems
    assert "hunts/README.md does not name outside_probe" in problems


def test_nested_or_foreign_directories_are_rejected(tmp_path: Path) -> None:
    hunt = _fixture(tmp_path)
    nested = hunt / "nested"
    nested.mkdir()
    assert "directly under hunts/" in structural_problems(tmp_path, nested)[0]
    assert "must be inside" in structural_problems(tmp_path, tmp_path / "elsewhere")[0]
