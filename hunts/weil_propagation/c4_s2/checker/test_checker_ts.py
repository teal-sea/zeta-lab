"""Phase 3 tests (checker/), WRITTEN AFTER ROUTING (two_adic/ ad97abf, 88d9dd1,
8dc8525: T_S for zeta). Two groups.

1. The snapshot fails closed (checker_glue.ts_key). It is keyed to the HEAD
   blobs of every T_S input, while the import reads the working tree; so a
   dirty input, a moved digest or a missing unit yields no snapshot rows,
   and T_S() raises instead of building live. A git error raises and is
   never read as clean.
2. Pins of checker_ts_cells.json (run_checker_ts.py) and checker_lesion.json
   (run_checker_lesion.py). They skip, with the reason, while those files
   are absent.

Precision, as routed by the coordinator: Delta_T is float64 with an error
band of a few 1e-3, far above Q's lowest eigenvalues (1.9e-7 to 2.6e-4).
R_S negatives are counted only below -band; eigenvalues within the band are
undecided and listed. The phase 1 dps 40 / 60 response cannot bite on a
float64 Delta_T; the mode-count and quadrature responses replace it as the
tolerance source (phase 1 original: ebf0eae).
"""

from __future__ import annotations

import json
import os
import subprocess
import sys

import pytest

HERE = os.path.dirname(os.path.abspath(__file__))
if HERE not in sys.path:
    sys.path.insert(0, HERE)

import checker_glue as GLUE  # noqa: E402

CELLS = ["2.2", "2.5", "2.9"]
CELLS_JSON = os.path.join(HERE, "checker_ts_cells.json")
LESION_JSON = os.path.join(HERE, "checker_lesion.json")
P = GLUE.C4S2


# ------------------------------------------------------------ fail closed


@pytest.mark.parametrize("line", [
    f" M {P}/two_adic/ta_prolate.py",
    f"M  {P}/two_adic/ta_ts.py",
    f"MM {P}/kernel/sonin.py",
    f" D {P}/kernel/sonin.py",
    f" M {P}/kernel/cells_dps40.json",
    f"R  {P}/two_adic/ta_old.py -> {P}/two_adic/ta_mellin.py",
])
def test_dirty_input_is_seen(line):
    assert GLUE.dirty_inputs(line) == [line]


@pytest.mark.parametrize("line", [
    f" M {P}/two_adic/ta_ts_prolate.json",
    f" M {P}/two_adic/RESULTS.md",
    f" M {P}/two_adic/INTERFACE.md",
    f"?? {P}/two_adic/test_ta_kmax.py",
    f"?? {P}/two_adic/ta_gram_probe.py",
    f" M {P}/two_adic/test_ta_ts.py",
    f" M {P}/cutoff/anything.py",
])
def test_non_input_is_not_dirty(line):
    assert GLUE.dirty_inputs(line) == []


def test_untracked_module_actually_loaded_is_caught():
    """An untracked file is not a key input, but if T_S imports one the
    build refuses: loaded_inputs_outside_key sees it in sys.modules."""
    import types

    fake = types.ModuleType("ta_untracked_helper")
    fake.__file__ = os.path.join(GLUE.TWO_ADIC, "ta_untracked_helper.py")
    real = types.ModuleType("ta_ts_probe")
    real.__file__ = os.path.join(GLUE.TWO_ADIC, "ta_ts.py")
    out = GLUE.loaded_inputs_outside_key({"a": fake, "b": real})
    assert out == [f"{P}/two_adic/ta_untracked_helper.py"]


def test_git_error_raises_not_clean():
    with pytest.raises(subprocess.CalledProcessError):
        GLUE._git("rev-parse", "--verify", "no-such-revision-for-checker")


def test_key_covers_the_modules_T_S_imports():
    lines = GLUE._git("ls-tree", "-r", "--name-only", "HEAD", "--", f"{P}/two_adic", f"{P}/kernel").split()
    ins = {os.path.basename(p) for p in lines if GLUE.ts_input(p)}
    assert {"ta_ts.py", "ta_data.py", "ta_prolate.py", "ta_mellin.py", "sonin.py",
            "cells_dps40.json", "cells_dps60.json"} <= ins
    assert not any(n.startswith("test_") for n in ins)


def _fake_snapshot(tmp_path, monkeypatch, digest="d0"):
    path = tmp_path / "snap.json"
    rows = [[1.0]]
    path.write_text(json.dumps({"meta": {"ts_inputs_digest": digest},
                                "T_S": {"2.2|8|40|80|1200": rows}}))
    monkeypatch.setattr(GLUE, "TS_SNAPSHOT", str(path))
    return rows


def test_clean_matching_tree_serves_rows(tmp_path, monkeypatch):
    rows = _fake_snapshot(tmp_path, monkeypatch)
    assert GLUE._snapshot_rows("2.2", 8, 40, key=("d0", [])) == rows


def test_dirty_tree_yields_no_rows(tmp_path, monkeypatch):
    _fake_snapshot(tmp_path, monkeypatch)
    assert GLUE._snapshot_rows("2.2", 8, 40, key=("d0", [f" M {P}/two_adic/ta_prolate.py"])) is None


def test_mismatched_digest_yields_no_rows(tmp_path, monkeypatch):
    _fake_snapshot(tmp_path, monkeypatch)
    assert GLUE._snapshot_rows("2.2", 8, 40, key=("d1", [])) is None


def test_no_dps_fallback(tmp_path, monkeypatch):
    _fake_snapshot(tmp_path, monkeypatch)
    assert GLUE._snapshot_rows("2.2", 8, 60, key=("d0", [])) is None


def test_T_S_refuses_rather_than_build_live(tmp_path, monkeypatch):
    _fake_snapshot(tmp_path, monkeypatch)
    monkeypatch.setattr(GLUE, "ts_key", lambda: ("d0", [f" M {P}/two_adic/ta_prolate.py"]))
    monkeypatch.setattr(GLUE, "T_S_live", lambda *a, **k: pytest.fail("live build attempted"))
    with pytest.raises(GLUE.SnapshotUnavailable, match="dirty"):
        GLUE.T_S("2.2", 8, 40)
    monkeypatch.setattr(GLUE, "ts_key", lambda: ("d1", []))
    with pytest.raises(GLUE.SnapshotUnavailable, match="no snapshot unit"):
        GLUE.T_S("2.2", 8, 40)


def test_snapshot_unavailable_skips_phase_1_tests():
    """Phase 1's _T_S turns NotRouted into a skip; the refusal must be one."""
    assert issubclass(GLUE.SnapshotUnavailable, GLUE.NotRouted)


# ------------------------------------------------------ pins (data files)


def _load(path, what):
    if not os.path.exists(path):
        pytest.skip(f"{os.path.basename(path)} absent: {what} not run yet")
    with open(path) as fh:
        return json.load(fh)


def test_lesion_refused_at_the_gate_and_at_the_provider():
    """Kill-control 4, layers 1 and 2: the construction as delivered refuses
    W_a's data twice, first at ta_data.validate, then (gate bypassed) in
    KernelProvider.delta_T."""
    J = _load(LESION_JSON, "kill-control 4")["layers"]
    L1 = J["1_builder_with_gate"]
    assert L1["outcome"] == "raised" and L1["exception"].endswith("NonUnitaryLocalData")
    for k in ("2_provider_gate_bypassed", "2_provider_gate_bypassed_alpha_minus"):
        assert J[k] == {"outcome": "raised", "exception": "builtins.NotImplementedError",
                        "message": "Delta_T is wired for real unitary alpha only (all mission data)"}


def test_lesion_below_both_guards():
    """Kill-control 4, layer 3 (LESION ONLY, ta_prolate.delta_T_cells called
    with alpha = 2^{+-1/4}, a formula two_adic/ never validated off
    |alpha| = 1). N = 8, (80, 1200), band 6e-3 (two_adic/'s band at
    alpha = 1; none exists for the lesion). Built from committed inputs."""
    D = _load(LESION_JSON, "kill-control 4")
    assert D["meta"]["dirty_inputs"] == [] and D["meta"]["kmax"] == 10
    J, band = D["cells"], D["meta"]["band"]
    counts = {"2.2": (4, 5, 4), "2.5": (4, 6, 5), "2.9": (4, 6, 5)}
    for c, (nz, nl, n2) in counts.items():
        r = J[c]
        # no eigenvalue of the lesioned T_S below -band; its lowest is positive,
        # above the band at 2.2 and 2.5, inside it (5.7e-3) at 2.9
        assert r["T_les"]["n_below_band"] == 0 and r["T_les"]["low3"][0] > 0, c
        assert (r["T_les"]["low3"][0] > band) == (c != "2.9"), c
        assert r["T_zeta"]["n_below_band"] == 0, c
        # n_-(R) below -band: zeta, the lesion against its own Q, against 2 Q_zeta
        assert r["R_zeta"]["n_below_band"] == nz, c
        assert r["R_les"]["n_below_band"] == nl, c
        assert r["R_les_against_2Q_zeta"]["n_below_band"] == n2, c
        # the lesion moves Delta_T by more than the band
        assert min(r["dT_plus_minus_dT_1_maxabs"], r["dT_minus_minus_dT_1_maxabs"]) > 2 * band, c


# ---------------------------------------------- phase 3: T_S and R_S pins


def _cells():
    return _load(CELLS_JSON, "run_checker_ts.py analysis")


def test_snapshot_matches_live_provider():
    """One snapshot unit equals a live two_adic/ T_S_matrix call, bitwise
    (c = 2.2, N = 8, (80, 1200)): the snapshot route composes exactly as the
    builder does. About 20 s."""
    if GLUE._snapshot_rows("2.2", 8, 40) is None:
        pytest.skip("snapshot stale, dirty or absent (checker_glue.ts_key)")
    import numpy as np

    snap = np.array(GLUE._snapshot_rows("2.2", 8, 40))
    live = np.asarray(GLUE.T_S_live("2.2", 8, 40))
    assert np.array_equal(snap, live)


def test_cells_json_keyed_to_routed_inputs():
    m = _cells()["meta"]
    assert m["routed_two_adic"] == "8dc8525" and m["probe_commit"] == "015895f"
    assert m["python"].endswith("/.venv/bin/python")  # the repo venv, on whichever machine ran it
    assert set(m["units"]) == {"80|1200|8", "120|1600|16", "200|2400|32", "80|1600|16",
                               "120|1200|16", "80|1200|16", "160|1600|16"}


def test_band_per_row_is_the_largest_measured_response():
    """P1 exactly; band(c, N) = max(two_adic/'s probe for the row, the row's
    refinement response, the quadrature response at N = 16). At N = 32 the
    refinement (240 modes) was not run locally; the N = 16 response of the
    same cell is the stated proxy."""
    J = _cells()["cells"]
    for c in CELLS:
        r = J[c]
        for N in ("8", "16", "32"):
            x = r[N]
            assert x["T_S_herm_defect"] == 0, (c, N)
            ref = x["refinement_response"] if N != "32" else x["refinement_proxy"]
            assert x["band"] == max(x["probe"], ref, r["quadrature_response_N16"]), (c, N)
        assert r["32"]["refinement_response"] is None
        assert r["32"]["refinement_proxy"] == r["16"]["refinement_response"]
        assert r["band_cell"] == max(r[N]["band"] for N in ("8", "16", "32"))


def test_80_modes_not_converged_at_N16():
    """two_adic/ INTERFACE.md lists (80, 1200) as converged at N = 16. The
    checker measures 80 -> 120 modes moving T_S by far more than 120 -> 160,
    and more than the band, while the N = 8 central block barely moves: the
    80-mode row under-resolves the top frequencies of N = 16."""
    J = _cells()["cells"]
    for c in CELLS:
        r = J[c]
        assert r["mode_response_80_to_120_N16"] > 4 * r["mode_response_120_to_160_N16"], c
        assert r["mode_response_80_to_120_N16"] > 3 * r["16"]["band"], c
        assert r["mode_response_80_to_120_N16_central_N8"] < r["8"]["band"], c


def test_P3_holds_at_equal_settings_only():
    """P3 (N = 8 is the central block of N = 16): exactly 0 when both use
    (80, 1200); at the delivered rows (80, 1200) against (120, 1600) the
    defect is the settings change, within the band of the cell."""
    J = _cells()["cells"]
    for c in CELLS:
        assert J[c]["P3_same_settings_defect"] == 0, c
        assert 0 < J[c]["P3_converged_rows_defect_norm"] <= J[c]["band_cell"], c


def test_dps_60_is_the_float64_floor():
    """T_S at dps 60 and dps 40 differ only through T_inf before rounding to
    float64; measured drift exactly 0 at N = 8 on every cell. The phase 1
    dps 40 / 60 response is vacuous for this provider."""
    J = _cells()["cells"]
    for c in CELLS:
        assert J[c]["dps60_float64_floor_N8"] == 0, c


def test_banded_P4_counts():
    """P4 at one threshold per cell (band_cell). The delivered rows use
    different settings per N and are not nested, so interlacing does not
    apply to them. Observed: nondecreasing at 2.5 and 2.9; at 2.2 the full
    count goes 1, 4, 3 (one eigenvalue, -1.63e-2 at N = 16, against the
    threshold -1.59e-2). Asserted before the data as monotone; pinned here
    as measured, and reported as a failure of banded P4 at 2.2."""
    J = _cells()["cells"]
    want = {"2.2": [1, 4, 3], "2.5": [4, 8, 20], "2.9": [4, 9, 20]}
    for c in CELLS:
        assert [J[c][N]["full"]["n_minus_at_band_cell"] for N in ("8", "16", "32")] == want[c], c


def test_T_S_removes_the_deep_product_side_negatives():
    """Q - T_inf (product side): lambda_min -0.30 to -0.49, negative count
    below -band growing in N. R_S = Q - T_S: lambda_min above -0.13 on every
    row. The count below -band is NOT smaller in general (c = 2.5, N = 32:
    20 for R_S against 18 for Q - T_inf); T_S removes depth, not count."""
    J = _cells()["cells"]
    for c in CELLS:
        ninf = [J[c][N]["R_inf_full"]["n_minus"] for N in ("8", "16", "32")]
        assert ninf[0] < ninf[1] < ninf[2], (c, ninf)
        for N in ("8", "16", "32"):
            assert J[c][N]["R_inf_full"]["low3"][0] < -0.29, (c, N)
            assert J[c][N]["full"]["low3"][0] > -0.13, (c, N)
    assert J["2.5"]["32"]["full"]["n_minus"] == 20 and J["2.5"]["32"]["R_inf_full"]["n_minus"] == 18


def test_R_S_negative_count_below_band():
    """n_-(R_S) below -band(c, N), full space: 4, 4, 3 at 2.2; 4, 9, 20 at
    2.5; 4, 10, 20 at 2.9 (N = 8, 16, 32). The growth at 2.5 and 2.9 is what
    C4's bounded-rank prediction (P5) forbids; it is measured, and at N = 32
    most of it lives on |n| > N/2, where Delta_T is least resolved."""
    J = _cells()["cells"]
    want = {"2.2": [4, 4, 3], "2.5": [4, 9, 20], "2.9": [4, 10, 20]}
    for c in CELLS:
        assert [J[c][N]["full"]["n_minus"] for N in ("8", "16", "32")] == want[c], c


def test_two_deep_negatives_at_2_9_on_every_class():
    """c = 2.9: the two lowest eigenvalues of R_S are below -3.7e-2 on every
    class and every N, 4.5 times the largest band of the cell."""
    J = _cells()["cells"]["2.9"]
    for N in ("8", "16", "32"):
        for cls in ("full", "minus", "minus_zero"):
            assert J[N][cls]["low3"][1] < -0.037 < -4.5 * J["band_cell"], (N, cls)


def test_top_half_split_of_the_negatives():
    """RESULTS s7.3: negatives of R_S (full) with more than half their weight
    on |n| > N/2, and the rest."""
    J = _cells()["cells"]
    top = {"2.5": [2, 4, 14], "2.9": [2, 5, 12]}
    rest = {"2.5": [2, 5, 6], "2.9": [2, 5, 8]}
    for c in top:
        t = [J[c][N]["full_n_minus_top_half"] for N in ("8", "16", "32")]
        n = [J[c][N]["full"]["n_minus"] for N in ("8", "16", "32")]
        assert t == top[c] and [a - b for a, b in zip(n, t)] == rest[c], c


def test_mode_response_lives_at_the_top_frequencies():
    """RESULTS s7.2: 90 to 96 percent of the 80 -> 120 response at N = 16 is
    on |n| >= 12 (weight of its top eigenvector), read from the snapshot file
    itself, which is the recorded evidence whatever the tree now holds."""
    import numpy as np

    if not os.path.exists(GLUE.TS_SNAPSHOT):
        pytest.skip("checker_ts_snapshot.json absent")
    with open(GLUE.TS_SNAPSHOT) as fh:
        T = json.load(fh)["T_S"]
    n = np.arange(-16, 17)
    for c, lo, hi in (("2.2", 0.895, 0.905), ("2.5", 0.955, 0.965), ("2.9", 0.945, 0.955)):
        D = np.array(T[f"{c}|16|40|120|1600"]) - np.array(T[f"{c}|16|40|80|1600"])
        w, V = np.linalg.eigh(D)
        v = V[:, np.argmax(abs(w))]
        assert lo < float((v[abs(n) >= 12] ** 2).sum()) < hi, c


def test_default_mode_rule_counts():
    """RESULTS s7.2: two_adic/'s default nvec = max(80, int(8N/L) + 40)."""
    import math

    got = [max(80, int(8 * N / math.log(float(c))) + 40) for N in (16, 32) for c in CELLS]
    assert got == [202, 179, 160, 364, 319, 280]


def _table(text, head, stop):
    import re

    sec = text[text.index(head):text.index(stop)]
    return [[x.strip() for x in r.strip().strip("|").split("|")]
            for r in sec.splitlines() if re.match(r"\| 2\.[259] \|", r)]


def test_results_phase3_tables_match_json():
    """Every number in the RESULTS s7.2, s7.3 and s7.4 tables is the JSON value
    at the printed precision."""
    J = _cells()["cells"]
    L = _load(LESION_JSON, "kill-control 4")["cells"]
    with open(os.path.join(HERE, "RESULTS.md")) as fh:
        text = fh.read()
    g = lambda x: "%.2e" % x  # noqa: E731
    f = lambda x: "%.4g" % x  # noqa: E731
    t1 = _table(text, "### 7.2", "### 7.3")
    assert len(t1) == 3
    for row in t1:
        r = J[row[0]]
        assert row[1:6] == [g(r["quadrature_response_N16"]), g(r["mode_response_80_to_120_N16"]),
                            g(r["mode_response_80_to_120_N16_central_N8"]),
                            g(r["mode_response_120_to_160_N16"]), g(r["P3_converged_rows_defect_norm"])]
    rows = _table(text, "### 7.3", "### 7.4")
    t2 = [r for r in rows if len(r) == 8]
    t3 = [r for r in rows if len(r) == 7]
    und = [r for r in rows if len(r) == 4]
    assert len(t2) == len(t3) == len(und) == 9
    for row in t2:
        x = J[row[0]][row[1]]
        ref = x["refinement_response"] if row[1] != "32" else x["refinement_proxy"]
        assert row[3] == g(x["probe"]) and row[4].strip("()") == g(ref) and row[5] == g(x["band"])
        assert row[6] == g(x["T_S_low3"][0])
        assert row[7] == f"{x['R_inf_full']['n_minus']}, {f(x['R_inf_full']['low3'][0])}"
    for row in t3:
        x = J[row[0]][row[1]]
        fu = x["full"]
        assert row[2] == f"{fu['n_minus']} / {fu['n_undecided']} / {fu['n_plus']}"
        assert row[3] == ", ".join(f(v) for v in fu["low3"])
        assert row[4] == f"{x['minus']['n_minus']} / {x['minus']['n_undecided']}"
        assert row[5] == f"{x['minus_zero']['n_minus']} / {x['minus_zero']['n_undecided']}"
        assert row[6] == str(x["full_n_minus_top_half"])
    for row in und:
        x = J[row[0]][row[1]]
        u = x["full"]["undecided"]
        assert row[2] == g(x["band"])
        if row[1] == "8":
            assert row[3] == ", ".join(f(v) for v in u)
        else:
            assert row[3] == f"{sum(1 for v in u if v < 0)} negative of {len(u)}, from {f(min(u))} to {f(max(u))}"
    t4 = _table(text, "### 7.4", "### 7.5")
    t4 = [r for r in t4 if len(r) == 7]
    assert len(t4) == 3
    for row in t4:
        r = L[row[0]]
        assert row[1] == g(r["T_zeta"]["low3"][0])
        assert row[2] == f"{g(r['T_les']['low3'][0])}, {r['T_les']['n_below_band']}"
        assert row[3] == f"{r['R_zeta']['n_below_band']} / {r['R_zeta']['n_in_band']}"
        assert row[4] == f"{r['R_les']['n_below_band']} / {r['R_les']['n_in_band']}"
        assert row[5] == str(r["R_les_against_2Q_zeta"]["n_below_band"])


def test_P3_defect_ranges_quoted():
    """RESULTS s7.2 and the phase 1 xfail reason: across the delivered rows the
    P3 defect is 3.1e-3 to 5.3e-3 (largest entry) and 3.7e-3 to 5.4e-3
    (spectral norm)."""
    J = _cells()["cells"]
    ent = [J[c]["P3_converged_rows_defect"] for c in CELLS]
    nrm = [J[c]["P3_converged_rows_defect_norm"] for c in CELLS]
    assert ("%.1e" % min(ent), "%.1e" % max(ent)) == ("3.1e-03", "5.3e-03")
    assert ("%.1e" % min(nrm), "%.1e" % max(nrm)) == ("3.7e-03", "5.4e-03")


def test_discriminator_more_modes_at_N16():
    """RESULTS s7.3a (1): at N = 16, S = 1600, one threshold band(c, 16), the
    count below -band falls as modes rise (80, 120, 160); the N = 8 block's
    count at 2.5 and 2.9 does not move."""
    J = _cells()["cells"]
    want = {"2.2": [5, 4, 3], "2.5": [10, 9, 8], "2.9": [12, 10, 10]}
    for c in CELLS:
        m = J[c]["modes_N16_S1600"]
        assert [m[k]["N16_n_minus"] for k in ("80", "120", "160")] == want[c], c
    for c in ("2.5", "2.9"):
        m = J[c]["modes_N16_S1600"]
        assert [m[k]["N8_block_n_minus"] for k in ("80", "120", "160")] == [4, 4, 4], c
    assert [J["2.2"]["modes_N16_S1600"][k]["N8_block_n_minus"] for k in ("80", "120", "160")] == [4, 2, 2]


def test_discriminator_resolved_coordinates():
    """RESULTS s7.3a (2): R_S on |n| <= N/2 at the row's band; and |n| <= 16
    at band(c, 16) for the 200-mode N = 32 build."""
    J = _cells()["cells"]
    want = {"2.2": [2, 1, 1], "2.5": [2, 4, 6], "2.9": [2, 4, 8]}
    for c in CELLS:
        assert [J[c][N]["resolved_half"]["n_minus"] for N in ("8", "16", "32")] == want[c], c
    fixed = {"2.2": 1, "2.5": 8, "2.9": 10}
    for c in CELLS:
        assert J[c]["modes_N16_S1600"]["200_N32_on_n_le_16"]["n_minus_at_band16"] == fixed[c], c


def test_results_discriminator_tables_match_json():
    J = _cells()["cells"]
    with open(os.path.join(HERE, "RESULTS.md")) as fh:
        text = fh.read()
    f = lambda x: "%.4g" % x  # noqa: E731
    rows = _table(text, "### 7.3a", "### 7.4")
    d1 = [r for r in rows if len(r) == 6 and r[1].startswith(("1.", "5.", "6.", "7.", "8."))]
    d2 = [r for r in rows if len(r) == 6 and r[1] in ("8", "16", "32")]
    assert len(d1) == 3 and len(d2) == 9
    for row in d1:
        m = J[row[0]]["modes_N16_S1600"]
        for i, k in zip((2, 3, 4), ("80", "120", "160")):
            assert row[i] == f"{m[k]['N16_n_minus']}, {', '.join(f(v) for v in m[k]['N16_low3'])}"
    for row in d2:
        h = J[row[0]][row[1]]["resolved_half"]
        assert row[2] == str(h["dim"]) and row[3] == f"{h['n_minus']} / {h['n_undecided']}"
        assert row[4] == ", ".join(f(v) for v in h["low3"])


def test_last_pair_counted_is_marginal():
    """RESULTS s7.3a: at 2.5 and 2.9 the last pair counted on |n| <= 16 (160
    modes at N = 16, and the 200-mode N = 32 build) sits at -6.7e-3 to
    -8.9e-3, 1.2 to 1.6 times band(c, 16)."""
    J = _cells()["cells"]
    vals, ratios = [], []
    for c in ("2.5", "2.9"):
        m = J[c]["modes_N16_S1600"]
        b = J[c]["16"]["band"]
        for pair in (m["160"]["N16_last_two_counted"], m["200_N32_on_n_le_16"]["last_two_counted"]):
            vals += pair
            ratios += [abs(x) / b for x in pair]
    assert ("%.1e" % max(vals), "%.1e" % min(vals)) == ("-6.7e-03", "-8.9e-03")
    assert ("%.1f" % min(ratios), "%.1f" % max(ratios)) == ("1.2", "1.6")


def test_rerun_matches_laptop_snapshot():
    """RESULTS s7.1: the 2026-09-24 rebuild at key 323b8a07 agrees with the
    laptop snapshot at 11e4afb (key 02f12c86) to 2.3e-7 in every entry, and
    the quoted per-unit seconds are the ones the rebuild recorded."""
    import numpy as np

    rel = "hunts/weil_propagation/c4_s2/checker/checker_ts_snapshot.json"
    old = json.loads(GLUE._git("show", f"11e4afb:{rel}"))
    with open(GLUE.TS_SNAPSHOT) as fh:
        new = json.load(fh)
    assert old["meta"]["ts_inputs_digest"].startswith("02f12c86")
    assert new["meta"]["ts_inputs_digest"].startswith("323b8a07")
    assert sorted(old["T_S"]) == sorted(new["T_S"])
    d = max(float(np.abs(np.array(old["T_S"][k]) - np.array(new["T_S"][k])).max()) for k in old["T_S"])
    assert "%.1e" % d == "2.3e-07"
    secs = {k: v["seconds"] for k, v in new["units"].items()}
    assert secs == {"80|1200|8": 33.5, "120|1600|16": 112.4, "200|2400|32": 427.3, "80|1600|16": 47.5,
                    "120|1200|16": 86.5, "80|1200|16": 32.0, "160|1600|16": 136.7}
