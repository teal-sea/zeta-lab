"""The research-state view: renders from artifacts, runs clean, stays honest."""

from __future__ import annotations

import subprocess
import sys
from pathlib import Path

_REPO_ROOT = Path(__file__).resolve().parent.parent


def test_the_view_renders_every_section(tmp_path: Path) -> None:
    out = tmp_path / "state.html"
    result = subprocess.run(
        [sys.executable, str(_REPO_ROOT / "scripts" / "70_lab_state.py"), "--out", str(out)],
        capture_output=True,
        text=True,
        timeout=120,
    )
    assert result.returncode == 0, result.stderr
    text = out.read_text(encoding="utf-8")
    for fragment in (
        "Attention queue",
        "Graveyard",
        "Guard ledger",
        "Verification independence",
        "Standing reviews",
        "Hunts",
        "what do we know now",
    ):
        assert fragment in text, f"missing section: {fragment}"
    # The page is static: no scripts, no network.
    assert "<script" not in text
    assert "http" not in text.split("</head>")[1], "the body reaches for the network"
    # The known state renders: the exemplar grave, the open worklist.
    assert "0.672529" in text
    assert "never demonstrated" in text
