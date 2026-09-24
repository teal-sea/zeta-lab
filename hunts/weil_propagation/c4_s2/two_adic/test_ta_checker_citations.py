"""Numbers RESULTS.md and INTERFACE.md cite from checker/: pinned against checker/'s JSON.

They are checker/'s measurements (checker/RESULTS.md line 2, line 3, s7.2,
s7.3a), read here from `../checker/checker_ts_cells.json` and not recomputed.
Tolerances are the printed digits.
"""

from __future__ import annotations

import json
import os

import pytest

HERE = os.path.dirname(os.path.abspath(__file__))
CELLS = ("2.2", "2.5", "2.9")


@pytest.fixture(scope="module")
def ck():
    with open(os.path.join(HERE, "..", "checker", "checker_ts_cells.json")) as fh:
        return json.load(fh)["cells"]


def test_n_minus_of_R_S_below_band(ck):
    """4, 4, 3 (c = 2.2); 4, 9, 20 (2.5); 4, 10, 20 (2.9) at N = 8, 16, 32."""
    want = {"2.2": [4, 4, 3], "2.5": [4, 9, 20], "2.9": [4, 10, 20]}
    for c in CELLS:
        assert [ck[c][N]["full"]["n_minus"] for N in ("8", "16", "32")] == want[c], c


def test_N16_count_under_more_modes(ck):
    """N = 16: 5, 4, 3 (2.2) and 10, 9, 8 (2.5) fall with 80, 120, 160 modes; 12, 10, 10 at 2.9."""
    want = {"2.2": [5, 4, 3], "2.5": [10, 9, 8], "2.9": [12, 10, 10]}
    for c in CELLS:
        m = ck[c]["modes_N16_S1600"]
        assert [m[k]["N16_n_minus"] for k in ("80_S1200", "120", "160")] == want[c], c
    # c = 2.9 at 160 modes: last pair counted -8.9e-3, -8.3e-3, 1.4 to 1.5 times band(2.9, 16)
    last = ck["2.9"]["modes_N16_S1600"]["160"]["N16_last_two_counted"]
    band = ck["2.9"]["16"]["band"]
    assert abs(last[0] + 8.9e-3) < 5e-5 and abs(last[1] + 8.3e-3) < 5e-5
    assert 1.4 <= abs(last[1]) / band and abs(last[0]) / band < 1.55


def test_mode_responses_of_T_S(ck):
    """Spectral norm: 80 -> 120 at N = 16 is 7.8e-2, 4.5e-2, 2.4e-2; 120 -> 160 is 1.6e-2, 5.2e-3, 3.7e-3."""
    a = [ck[c]["mode_response_80_to_120_N16"] for c in CELLS]
    b = [ck[c]["mode_response_120_to_160_N16"] for c in CELLS]
    for x, w in zip(a, (7.8e-2, 4.5e-2, 2.4e-2)):
        assert abs(x - w) <= 0.05 * w
    for x, w in zip(b, (1.6e-2, 5.2e-3, 3.7e-3)):
        assert abs(x - w) <= 0.05 * w
    # (120, 1600) is within its probe at 2.5 and 2.9, not at 2.2
    probes = [ck[c]["16"]["probe"] for c in CELLS]
    assert b[0] > probes[0] and b[1] < probes[1] and b[2] < probes[2]


def test_N8_refinement(ck):
    """(80, 1200) at N = 8 against (160, 1600, 16): 5.6e-3, 5.5e-3, 5.3e-3, above its probe."""
    r = [ck[c]["refinement_response"]["8"] for c in CELLS]
    for x, w in zip(r, (5.6e-3, 5.5e-3, 5.3e-3)):
        assert abs(x - w) < 5e-5
    assert all(ck[c]["refinement_response"]["8"] > ck[c]["8"]["probe"] for c in CELLS)
    assert all(ck[c]["refinement_response"]["32"] is None for c in CELLS)
