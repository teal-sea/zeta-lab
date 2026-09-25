"""Numbers RESULTS.md and INTERFACE.md cite from checker/: pinned against checker/'s JSON.

They are checker/'s measurements (checker/RESULTS.md lines 1 to 3, s7.2,
s7.3a, s7.8), read here from `../checker/checker_ts_cells.json` and not
recomputed. Tolerances are the printed digits. The N = 32 rows are the ones
rebuilt under this folder's QR rho (checker/ s7.8, 3e36fa4). The old-route
N = 32 reading (checker/ s7.7) is quoted in the docstrings as history; its
keys left the JSON, which is citable at 3dc0a74.
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
    """4, 4, 0 (c = 2.2); 4, 9, 8 (2.5); 4, 10, 20 (2.9) at N = 8, 16, 32 (s7.8).

    Under the QR rho, at band(c, 32): the 200, 240, 280, 319 and 364-mode rows
    count 20, 20, 20, 20, 21 at 2.9 (10 at N = 16: survives), 8, 6, 6, 5, 6 at
    2.5 (9 at N = 16: falls on the refined rows 240 and 319) and 0 on every
    build at 2.2 (falls). At 2.5 the verdict rests on the band rule: at the
    240-mode row's band the refined rows would count 14 and 12. At the proxy
    band the 200-mode row counts 3, 20, 20, as before the re-grade.

    History (old route, checker/ s7.7, 3dc0a74): N = 32 was undecided in
    float64; the 200 and 240-mode rows counted 0, 2, 2 and 0, 5, 4 at the band
    the 240-mode row set, the 240-mode row 19 and 23 at the proxy band (2.5,
    2.9), and at 2.9 the 280-mode row 22, on a Gram matrix of condition 1.1e17.
    """
    want = {"2.2": [4, 4, 0], "2.5": [4, 9, 8], "2.9": [4, 10, 20]}
    for c in CELLS:
        assert [ck[c][N]["full"]["n_minus"] for N in ("8", "16", "32")] == want[c], c
    m = {c: ck[c]["modes_N32"] for c in CELLS}
    b = {c: m[c]["builds"] for c in CELLS}
    counts = {"200": [0, 8, 20], "240": [0, 6, 20], "280": [0, 6, 20],
              "319": [0, 5, 20], "364": [0, 6, 21]}
    for X, w in counts.items():
        assert [b[c][X]["n_minus"] for c in CELLS] == w, X
    assert [b[c]["200"]["n_minus_at_proxy_band"] for c in CELLS] == [3, 20, 20]
    assert [b[c]["240"]["n_minus_at_proxy_band"] for c in CELLS] == [1, 14, 20]
    assert [m[c]["n_minus_N16"] for c in CELLS] == [4, 9, 10]
    assert [m[c]["admitted"] for c in CELLS] == [["240", "364"], ["240", "319"], ["240", "280"]]
    assert [m[c]["cell_verdict"] for c in CELLS] == ["falls", "falls", "survives"]
    for c, label in zip(CELLS, ("falls", "falls", "survives")):
        assert all(v["label"] == label for v in m[c]["s7_6_verdict"].values()), c
    sens = b["2.5"]
    assert [sens[X]["sensitivity_n_minus_at_band_240_only"] for X in ("240", "319")] == [14, 12]
    # the rows past A2's last clean case (cond(F) 6.7e11) are admitted: cond_F 1.9e13 to 2.1e13, below 1e14
    for X in ("280", "319", "364"):
        r = b["2.9"][X]
        assert r["beyond_A2_last_clean"] and not r["past_gate"]
        assert 1.8e13 < r["cond_F"] < 2.2e13
    assert all(not b[c][X]["past_gate"] for c in CELLS for X in counts)
    assert b["2.9"]["280"]["cond_Gb"] > 1 / 2.220446049250313e-16
    assert abs(b["2.9"]["280"]["cond_Gb"] - 2.9e17) < 5e15


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

    N = 32 under the QR rho (s7.8): the largest response of an admitted refined
    row, 2.97e-2, 1.41e-2, 4.95e-3 (240, 319, 280 modes), and band(c, 32) =
    max(band_0, that response) = 2.97e-2, 1.41e-2, 8.18e-3 (at 2.9 the probe
    sets it), against the old band(c, 32) 3.92e-2, 2.37e-2, 3.16e-2. The
    240-mode row moves T_S by 2.97e-2, 1.08e-2, 2.3e-3, and T_S's lowest
    eigenvalue there is +2.03e-3, +1.34e-3, +1.09e-3. The falsifier passes on
    every N = 32 build: T_S's lowest eigenvalue lies between +1.09e-3 and
    +4.41e-3.

    History (old route, checker/ s7.7, 3dc0a74): the 240-mode row moved T_S by
    3.9e-2, 2.4e-2, 3.2e-2, which set band(c, 32), and T_S's lowest eigenvalue
    on it was -7.3e-3, -8.5e-3, -8.9e-3.
    """
    r = [ck[c]["refinement_response"]["8"] for c in CELLS]
    for x, w in zip(r, (5.6e-3, 5.5e-3, 5.3e-3)):
        assert abs(x - w) < 5e-5
    assert all(ck[c]["refinement_response"]["8"] > ck[c]["8"]["probe"] for c in CELLS)
    m = {c: ck[c]["modes_N32"] for c in CELLS}
    r32 = [ck[c]["refinement_response"]["32"] for c in CELLS]
    for x, w in zip(r32, (2.97e-2, 1.41e-2, 4.95e-3)):
        assert abs(x - w) < 5e-5
    for c in CELLS:
        b = m[c]["builds"]
        assert ck[c]["refinement_response"]["32"] == max(b[X]["dT_vs_200"] for X in m[c]["admitted"])
        assert ck[c]["32"]["band"] == max(m[c]["band_0"], ck[c]["refinement_response"]["32"])
        assert m[c]["band_0"] == ck[c]["32"]["probe"]
    for x, w in zip([ck[c]["32"]["band"] for c in CELLS], (2.97e-2, 1.41e-2, 8.18e-3)):
        assert abs(x - w) < 5e-5
    for x, w in zip([m[c]["old_band_32"] for c in CELLS], (3.92e-2, 2.37e-2, 3.16e-2)):
        assert abs(x - w) < 5e-5
    # at 2.9 no N = 32 build, admitted or not, moves T_S by more than 4.95e-3
    assert max(r["dT_vs_200"] for r in m["2.9"]["builds"].values()) == ck["2.9"]["refinement_response"]["32"]
    d240 = [m[c]["builds"]["240"]["dT_vs_200"] for c in CELLS]
    for x, w in zip(d240, (2.97e-2, 1.08e-2, 2.3e-3)):
        assert abs(x - w) < 5e-5
    low = [m[c]["builds"]["240"]["T_S_low"] for c in CELLS]
    for x, w in zip(low, (2.03e-3, 1.34e-3, 1.09e-3)):
        assert abs(x - w) < 5e-6
    lows = [r["T_S_low"] for c in CELLS for r in m[c]["builds"].values()]
    assert len(lows) == 15 and abs(min(lows) - 1.09e-3) < 5e-6 and abs(max(lows) - 4.41e-3) < 5e-6
    assert all(r["P2_bin"] == "pass" == r["P2_bin_at_old_band"] for c in CELLS for r in m[c]["builds"].values())


def test_s10_6_outcomes(ck):
    """RESULTS s10.6: the N = 32 numbers it quotes beside s10's predictions.

    T_S's lowest eigenvalue is +1.42e-3 to +2.40e-3 at 280 modes, +1.98e-3 to
    +2.87e-3 at 319, +3.42e-3 to +4.41e-3 at 364; cond(F_z) is 1.9e13, 2.1e13,
    2.1e13 there (squares 3.6e26 to 4.4e26), below 1e14; cond(F_b)^2 is 1.7e17,
    1.9e19, 5.9e21, above the old formed cond(G_b) 1.1e17, 2.8e18, 5.1e17
    (checker/ s7.7, 3dc0a74), and the rebuilt formed cond(G_b) is 2.9e17,
    2.6e17, 1.2e18, above cond(F_b)^2 at 280. This folder's laptop build of
    (200, 2400, 32) (ta_rho_check.json, A4) and checker/'s Modal row differ in
    T_S's lowest eigenvalue by at most 2.3e-12.
    """
    b = {c: ck[c]["modes_N32"]["builds"] for c in CELLS}
    for X, lo, hi in (("280", 1.42e-3, 2.40e-3), ("319", 1.98e-3, 2.87e-3), ("364", 3.42e-3, 4.41e-3)):
        lows = [b[c][X]["T_S_low"] for c in CELLS]
        assert abs(min(lows) - lo) < 5e-6 and abs(max(lows) - hi) < 5e-6, X
    r = b["2.9"]  # the unit diagnostics are per build, shared by the three cells
    assert all(b[c][X]["cond_Fz"] == r[X]["cond_Fz"] for c in CELLS for X in r)
    fz = [r[X]["cond_Fz"] for X in ("280", "319", "364")]
    for x, w in zip(fz, (1.9e13, 2.1e13, 2.1e13)):
        assert abs(x - w) < 0.05e13 and x < 1e14 and x > 6.7e11
    assert abs(min(fz) ** 2 - 3.6e26) < 0.05e26 and abs(max(fz) ** 2 - 4.4e26) < 0.05e26
    fb2 = [r[X]["cond_Fb"] ** 2 for X in ("280", "319", "364")]
    for x, w in zip(fb2, (1.7e17, 1.9e19, 5.9e21)):
        assert abs(x - w) < 0.05 * w
    assert all(x > old for x, old in zip(fb2, (1.1e17, 2.8e18, 5.1e17)))
    gb = [r[X]["cond_Gb"] for X in ("280", "319", "364")]
    for x, w in zip(gb, (2.9e17, 2.6e17, 1.2e18)):
        assert abs(x - w) < 0.05 * w
    assert gb[0] > fb2[0] and gb[1] < fb2[1] and gb[2] < fb2[2]
    with open(os.path.join(HERE, "ta_rho_check.json")) as fh:
        a4 = json.load(fh)["A4"]["cells"]
    drift = [abs(a4[c]["new_2400_low3"][0] - b[c]["200"]["T_S_low"]) for c in CELLS]
    assert 1e-13 < max(drift) < 2.3e-12
