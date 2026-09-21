"""The ball atom budget uses the measured tower rate, not an unmeasured proxy."""
from __future__ import annotations

import importlib.util
import io
from contextlib import redirect_stdout
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
SPEC = importlib.util.spec_from_file_location(
    "rung3_ball_atom_budget", ROOT / "scripts" / "67_rung3_ball_atom_budget.py")
assert SPEC is not None and SPEC.loader is not None
budget = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(budget)


def test_tower_rate_is_mean_net_cpu_over_thirty_atoms():
    samples = budget.net_cpu_samples()
    assert [round(s, 3) for s in samples] == [37.009, 37.664, 37.863]
    assert budget.mean_net_cpu_s() == 37.512
    assert budget.MEAN_NET_CPU_S == 37.512
    assert budget.tower_sec_per_atom() == 1.2504
    assert budget.TOWER_SEC_PER_ATOM == 1.2504
    assert budget.OTHER_SEC_PER_ATOM == 0.55
    assert budget.TOWER_MULS == 30


def test_plan_totals_split_tower_and_other_atoms():
    counts = budget.plan_atom_counts()
    assert counts["tower_atoms"] == 468_240
    assert counts["other_atoms"] == 80_909
    assert counts["atoms"] == 468_240 + 80_909
    hours = budget.serial_core_hours(
        counts["tower_atoms"], counts["other_atoms"])
    assert round(hours, 1) == 175.0


def test_budget_cli_uses_mixed_measured_rates():
    buf = io.StringIO()
    with redirect_stdout(buf):
        budget.main([])
    text = buf.getvalue()
    assert "UNMEASURED" not in text
    assert "unmeasured" not in text.lower()
    assert "468,240" in text
    assert "80,909" in text
    assert "1.2504" in text
    assert "175.0 core-hours" in text
    assert "serial CPU" in text
    assert "atom-only" in text
    assert "not total production cost" in text
    assert "import and assembly" in text
    assert "WALL=305.410" in text
    assert "USER=1369.406" in text
    assert "WALL=2580.664" in text
    assert "USER=6628.916" in text
    assert "nonlinear" in text
    assert "138 MB" in text
    assert "32GB" in text
    assert "GitHub" not in text
    assert "Actions" not in text
    assert "wall-hours" not in text
    assert "4-way" not in text
    assert "20-way" not in text


def test_whole_file_evidence_is_recorded_separately():
    assert budget.WHOLE_FILE_B_K17 == {
        "label": "B K17", "K": 17,
        "wall": 305.410, "user": 1369.406, "sys": 16.260,
    }
    assert budget.WHOLE_FILE_GRID_K85 == {
        "label": "grid K85", "K": 85,
        "wall": 2580.664, "user": 6628.916, "sys": 60.079,
    }
