"""The preservation guard restores exact precision even when a checker fails."""

import importlib.util
from pathlib import Path

import mpmath as mp
import pytest

from conftest import preserved_checker_precision


@pytest.mark.parametrize("test_name,checker,digits", [
    ("test_combined_weight_baseline_review.py", "certificate_route_test/review/baseline_check.py", 60),
    ("test_joint_correction_candidate.py", "joint_correction_candidate/review/joint_check.py", 80),
])
@pytest.mark.parametrize("interrupt", [False, True])
def test_original_checker_import_is_scoped(test_name, checker, digits, interrupt):
    saved = mp.mp.prec, mp.iv.prec
    root = Path(__file__).resolve().parents[1]
    try:
        mp.mp.prec, mp.iv.prec = 139, 137
        try:
            with preserved_checker_precision(test_name):
                path = root / "hunts/prime_pair_error/frontier/2026-09-06" / checker
                spec = importlib.util.spec_from_file_location("preserved_checker_probe", path)
                module = importlib.util.module_from_spec(spec)
                spec.loader.exec_module(module)
                assert (mp.mp.dps, mp.iv.dps) == (digits, digits)
                if interrupt:
                    raise RuntimeError("planted interruption")
        except RuntimeError as exc:
            if not interrupt:
                raise
            assert str(exc) == "planted interruption"
        assert (mp.mp.prec, mp.iv.prec) == (139, 137)
    finally:
        mp.mp.prec, mp.iv.prec = saved


def test_unrelated_test_is_not_given_a_precision_policy():
    saved = mp.mp.prec, mp.iv.prec
    try:
        with preserved_checker_precision("test_unrelated.py"):
            mp.mp.prec, mp.iv.prec = 139, 137
        assert (mp.mp.prec, mp.iv.prec) == (139, 137)
    finally:
        mp.mp.prec, mp.iv.prec = saved
