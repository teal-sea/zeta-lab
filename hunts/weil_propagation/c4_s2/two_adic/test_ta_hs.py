"""P F_S P is not Hilbert-Schmidt: partial sums of its HS norm, pinned.

Measured at dps 30 (ta_hs.hs2_partial): the increments per Euler level tend
to 1/2 (0.5000000005 averaged over levels 32..40) and the partial sums sit on
K/2 + 1.07078679... (K = 24, 32, 40 agree with that line to 2e-5, 1e-7, 4e-9).
"""

from __future__ import annotations

import os
import sys

import pytest
from mpmath import mp

HERE = os.path.dirname(os.path.abspath(__file__))
if HERE not in sys.path:
    sys.path.insert(0, HERE)

import ta_hs as H  # noqa: E402


def test_archimedean_trace_of_P_Phat_P():
    with mp.workdps(30):
        v = H.hs2_archimedean()
        # 2 + 2 Si(4 pi)/(4 pi), even sector, lambda = 1
        assert abs(v - (2 + 2 * mp.si(4 * mp.pi) / (4 * mp.pi))) < mp.mpf("1e-28")
        assert abs(v - mp.mpf("2.23748483494183")) < mp.mpf("1e-13")


def test_place_2_off_gives_the_archimedean_value():
    with mp.workdps(30):
        assert abs(H.hs2_partial(10, alpha=0) - H.hs2_archimedean()) < mp.mpf("1e-25")


@pytest.mark.parametrize("K,tol", [(24, "2e-5"), (32, "1e-7"), (40, "4e-9")])
def test_partial_sums_grow_by_one_half_per_level(K, tol):
    with mp.workdps(30):
        v = H.hs2_partial(K)
        assert abs(v - (mp.mpf(K) / 2 + mp.mpf("1.0707867954"))) < mp.mpf(tol)


def test_increment_tends_to_one_half():
    with mp.workdps(30):
        inc = (H.hs2_partial(40) - H.hs2_partial(32)) / 8
        assert abs(inc - mp.mpf("0.5")) < mp.mpf("1e-9")


@pytest.mark.parametrize("K,value", [(0, "0.405037"), (8, "5.052145"), (16, "9.070653"), (24, "13.070786"), (32, "17.070787"), (40, "21.070787")])
def test_results_table_values(K, value):
    with mp.workdps(30):
        assert abs(H.hs2_partial(K) - mp.mpf(value)) < mp.mpf("1e-6")
