from __future__ import annotations

import json
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
HUNT = ROOT / "hunts" / "r_662b12"


def test_aimo_public_record_carries_the_independent_correction() -> None:
    results = json.loads((HUNT / "results.json").read_text(encoding="utf-8"))
    recommendation = results["recommendation"]
    assert recommendation["verdict"] == "NO-GO after independent audit"
    assert recommendation["audit"] == "AUDIT.md"

    prose = (HUNT / "RESULTS.md").read_text(encoding="utf-8")
    assert "Correction, 2026-08-22" in prose
    assert "did not fit or select the rule inside each training fold" in prose


def test_aimo_case_log_does_not_repeat_the_withdrawn_go_claim() -> None:
    log = (ROOT / "hunts" / "README.md").read_text(encoding="utf-8")
    entry = log.split("### Hunt #72:", 1)[1].split("### Hunt #", 1)[0]
    assert "NO-GO on this hunt's evidence" in entry
    assert "GO for technical report prize track" not in entry
