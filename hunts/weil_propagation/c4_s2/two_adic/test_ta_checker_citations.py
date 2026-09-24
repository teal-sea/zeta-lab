"""Numbers RESULTS.md and INTERFACE.md cite from checker/: pinned against checker/'s JSON.

They are checker/'s measurements (checker/RESULTS.md lines 1 to 3, s7.2,
s7.3a, s7.7), read here from `../checker/checker_ts_cells.json` and not
recomputed. Tolerances are the printed digits.
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
    """4, 4 (c = 2.2); 4, 9 (2.5); 4, 10 (2.9) at N = 8, 16. N = 32 is undecided (s7.7).

    At band(c, 32) the 200 and 240-mode rows count 0, 2, 2 and 0, 5, 4; the
    240-mode row still counts 19 and 23 at the proxy band (2.5, 2.9), and the
    200-mode row 3, 20, 20 (the counts this folder quoted before the re-grade).
    The 240-mode row falls on every cell; at 2.9 the 280-mode row survives
    with 22, on a Gram matrix of condition 1.1e17, above 1/eps.
    """
    want = {"2.2": [4, 4, 0], "2.5": [4, 9, 2], "2.9": [4, 10, 2]}
    for c in CELLS:
        assert [ck[c][N]["full"]["n_minus"] for N in ("8", "16", "32")] == want[c], c
    b = {c: ck[c]["modes_N32"]["builds"] for c in CELLS}
    assert [b[c]["200"]["n_minus"] for c in CELLS] == [0, 2, 2]
    assert [b[c]["240"]["n_minus"] for c in CELLS] == [0, 5, 4]
    assert [b[c]["200"]["n_minus_at_band_before_merge"] for c in CELLS] == [3, 20, 20]
    assert [b[c]["240"]["n_minus_at_band_before_merge"] for c in ("2.5", "2.9")] == [19, 23]
    verdict = {c: ck[c]["modes_N32"]["s7_6_verdict"] for c in CELLS}
    assert all(verdict[c]["240"]["label"] == "falls" for c in CELLS)
    assert verdict["2.9"]["280"]["label"] == "survives"
    assert b["2.9"]["280"]["n_minus"] == 22
    assert abs(b["2.9"]["280"]["cond_Gb"] - 1.1e17) < 5e15
    assert b["2.9"]["280"]["cond_Gb"] > 1 / 2.220446049250313e-16


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
    """(80, 1200) at N = 8 against (160, 1600, 16): 5.6e-3, 5.5e-3, 5.3e-3, above its probe.

    N = 32 (s7.7): (240, 2400) against (200, 2400) moves T_S by 3.9e-2, 2.4e-2,
    3.2e-2, which sets band(c, 32); T_S's lowest eigenvalue on the 240-mode
    row is -7.3e-3, -8.5e-3, -8.9e-3.
    """
    r = [ck[c]["refinement_response"]["8"] for c in CELLS]
    for x, w in zip(r, (5.6e-3, 5.5e-3, 5.3e-3)):
        assert abs(x - w) < 5e-5
    assert all(ck[c]["refinement_response"]["8"] > ck[c]["8"]["probe"] for c in CELLS)
    r32 = [ck[c]["refinement_response"]["32"] for c in CELLS]
    for x, w in zip(r32, (3.9e-2, 2.4e-2, 3.2e-2)):
        assert abs(x - w) < 5e-4
    assert all(ck[c]["32"]["band"] == ck[c]["refinement_response"]["32"] for c in CELLS)
    assert all(ck[c]["modes_N32"]["builds"]["240"]["dT_vs_200"] == ck[c]["refinement_response"]["32"] for c in CELLS)
    low = [ck[c]["modes_N32"]["builds"]["240"]["T_S_low"] for c in CELLS]
    for x, w in zip(low, (-7.3e-3, -8.5e-3, -8.9e-3)):
        assert abs(x - w) < 5e-5
