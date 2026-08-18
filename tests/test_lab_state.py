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
    # The property is "the body fetches nothing", not "the body never says
    # http". Rendered content legitimately quotes URLs -- a branch's commit
    # message naming the repo used to fail this check, which made the guard
    # fire on a page that reaches for nothing at all. Test the constructs
    # that actually cause a fetch instead of the substring.
    body = text.split("</head>")[1]
    for attr in ("src=", "href=", "action=", "srcset=", "data-src="):
        for quote in ('"', "'"):
            assert f"{attr}{quote}http" not in body, (
                f"the body reaches for the network via {attr}")
            assert f"{attr}{quote}//" not in body, (
                f"the body reaches for the network via {attr} (scheme-relative)")
    for construct in ("url(http", "url('http", 'url("http', "@import",
                      "<iframe", "<img", "<link", "fetch(", "XMLHttpRequest"):
        assert construct not in body, (
            f"the body reaches for the network via {construct}")
    # The known state renders: the exemplar grave, the open worklist.
    assert "0.672529" in text
    assert "never demonstrated" in text
