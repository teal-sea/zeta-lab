"""The DH v6 replay receipts re-aggregate to 400/400 and 1,268/1,268, and lesions fail.

``docs/46-davenport-heilbronn-v6-arb-replay.md`` quotes counts. This test does
not trust them: it re-derives them from ``data/dh_v6_replay/receipts.tar.gz``
through ``scripts/dh_v6_replay_audit.py`` and checks that each planted lesion
makes the audit fail. A cross-check that cannot fail is not a cross-check.
"""

from __future__ import annotations

import importlib.util
import os

import pytest

REPO_ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
SCRIPT = os.path.join(REPO_ROOT, "scripts", "dh_v6_replay_audit.py")


def _load():
    spec = importlib.util.spec_from_file_location("dh_v6_replay_audit", SCRIPT)
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


@pytest.fixture(scope="module")
def audit_mod():
    return _load()


@pytest.fixture(scope="module")
def receipts(audit_mod):
    return audit_mod.load_receipts()


def test_clean_audit_reproduces_the_census_counts(audit_mod, receipts) -> None:
    windows, rows, closure, _ = receipts
    summary = audit_mod.audit(windows, rows, closure)
    assert summary["windows"] == 400
    assert summary["rows"] == 1268
    assert summary["sum_N_R"] == 1268
    assert summary["sum_N_S"] == 25078
    assert summary["total_multiplicity"] == 27614
    assert [b["row"] for b in summary["border_crossing_boxes"]] == [615, 655]


@pytest.mark.parametrize("lesion", ["drop-row", "shift-count", "dup-window"])
def test_each_planted_lesion_is_caught(audit_mod, lesion) -> None:
    windows, rows, closure, _ = audit_mod.load_receipts()
    audit_mod.plant_lesion(lesion, windows, rows)
    with pytest.raises(audit_mod.AuditFailure):
        audit_mod.audit(windows, rows, closure)


def test_cli_exit_codes(audit_mod) -> None:
    assert audit_mod.main([]) == 0
    assert audit_mod.main(["--lesion", "shift-count"]) == 0  # lesion caught -> 0
