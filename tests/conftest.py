"""Keep archived checker tests byte-identical while isolating their precision."""

from contextlib import contextmanager
from pathlib import Path

import pytest


_PRESERVED_CHECKER_TESTS = {
    "test_combined_weight_baseline_review.py",
    "test_joint_correction_candidate.py",
}


@contextmanager
def preserved_checker_precision(path):
    if Path(path).name not in _PRESERVED_CHECKER_TESTS:
        yield
        return
    import mpmath as mp
    saved = mp.mp.prec, mp.iv.prec
    try:
        yield
    finally:
        mp.mp.prec, mp.iv.prec = saved


@pytest.fixture(autouse=True)
def _isolate_preserved_checker_precision(request):
    with preserved_checker_precision(request.node.path):
        yield
