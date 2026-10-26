"""Reproduce the height-100 generated sources without rewriting them."""
import subprocess
import sys
from pathlib import Path

import pytest

HERE = Path(__file__).parent


@pytest.mark.parametrize("generator", ["gen_boxes100.py", "gen_legs100.py"])
def test_generator_check_mode_matches_all_saved_files(generator):
    result = subprocess.run([sys.executable, str(HERE / generator), "--check"],
                            capture_output=True, text=True, timeout=1200)
    assert result.returncode == 0, result.stdout + result.stderr
    assert "differs from" not in result.stdout
    assert result.stdout.count(" matches the generator") == (19 if "boxes" in generator else 3)


def test_box_check_refuses_a_missing_file(monkeypatch, tmp_path):
    from hunts.rh_height_lean import gen_boxes100 as G
    monkeypatch.setattr(G, "LEAN_DIR", tmp_path)
    assert G.main(["--check", "--only", "5297"]) == 1


def test_leg_check_refuses_missing_files(monkeypatch, tmp_path):
    from hunts.rh_height_lean import gen_legs100 as G
    monkeypatch.setattr(G, "LEAN_DIR", tmp_path)
    assert G.main(["--check"]) == 1
