"""Accuracy item on c = 2.2, N = 8 (ta_gram_probe.py, ta_gram_probe.json): pinned.

Float64, measured grade. The band is a spectral norm (see ta_gram_probe's
docstring, where it was fixed before the S = 4800 runs were read). Tolerances:
stored values to 1e-12 where they are recomputed, and to the printed digits
of RESULTS.md s7 where they are quoted. From 2026-09-24 the JSON also carries
modal/'s gram runs (merge_modal); the merge is pinned against modal/out/.
"""

from __future__ import annotations

import json
import os
import sys

import numpy as np
import pytest

HERE = os.path.dirname(os.path.abspath(__file__))
if HERE not in sys.path:
    sys.path.insert(0, HERE)

import ta_gram_probe as G  # noqa: E402


@pytest.fixture(scope="module")
def js():
    with open(os.path.join(HERE, "ta_gram_probe.json")) as fh:
        return json.load(fh)


def _dT(js, key):
    return np.array(js["runs"][key]["dT"])


def band(js):
    s_resp = np.linalg.norm(_dT(js, "80,4800") - _dT(js, "80,2400"), 2)
    n_resp = np.linalg.norm(_dT(js, "100,4800") - _dT(js, "80,4800"), 2)
    probe = js["runs"]["80,4800"]["dT_probe_norm2"]
    return s_resp, n_resp, probe


def test_target_is_checkers_Q_low():
    assert abs(G.q_low() - 2.5738e-4) < 5e-9
    # the 2.33e-4 quoted for c = 2.2 is N = 32
    with open(os.path.join(HERE, "..", "checker", "checker_q_cells.json")) as fh:
        q = json.load(fh)["cells"]["2.2"]
    assert abs(float(q["full_N32_dps40"][0]) - 2.33e-4) < 5e-7


def test_converged_run_matches_the_prolate_table(js):
    """(80, 1200) here is the (80, 1200, 8, 2.2) row of ta_ts_prolate.json."""
    with open(os.path.join(HERE, "ta_ts_prolate.json")) as fh:
        row = next(r for r in json.load(fh)["rows"] if (r["nvec"], r["S"], r["N"], r["c"]) == (80, 1200.0, 8, "2.2"))
    assert np.allclose(js["runs"]["80,1200"]["TS_low3"], row["T_S_eig_low3"], atol=1e-9)
    assert abs(js["runs"]["80,1200"]["dT_probe_maxentry"] - row["gram_sensitivity"]) < 1e-9


def test_s_side_gram_error_falls_with_S_at_fixed_nvec(js):
    """80 modes: probe 3.8e-3, 4.9e-4, 2.5e-5 and max |G_z^s - I| 8.9e-2, 3.5e-2, 8.4e-3 at S = 1200, 2400, 4800."""
    r = js["runs"]
    probe = [r[f"80,{S}"]["dT_probe_norm2"] for S in (1200, 2400, 4800)]
    gz = [r[f"80,{S}"]["gz_dev"] for S in (1200, 2400, 4800)]
    assert np.allclose(probe, [3.81e-3, 4.90e-4, 2.50e-5], rtol=5e-3)
    assert np.allclose(gz, [8.92e-2, 3.53e-2, 8.42e-3], rtol=5e-3)
    s1 = np.linalg.norm(_dT(js, "80,2400") - _dT(js, "80,1200"), 2)
    assert abs(s1 - 6.53e-4) < 5e-6


def test_band_is_nvec_bound_and_above_target(js):
    """band(80, 4800) = 4.48e-3 (the nvec response) > Q_low = 2.574e-4: the accuracy target is not met."""
    s_resp, n_resp, probe = band(js)
    assert abs(s_resp - 1.07e-4) < 5e-6
    assert abs(n_resp - 4.48e-3) < 5e-6
    assert abs(probe - 2.50e-5) < 5e-7
    b = max(s_resp, n_resp, probe)
    assert b == n_resp and b > js["Q_low"]


def test_nvec_response_and_lowest_eigenvalue_drift(js):
    """S = 4800: ||dT(120) - dT(100)||_2 = 1.60e-3; T_S lowest 3.486e-3, 3.001e-3, 2.671e-3 at 80, 100, 120 modes."""
    d = np.linalg.norm(_dT(js, "120,4800") - _dT(js, "100,4800"), 2)
    assert abs(d - 1.60e-3) < 5e-6
    low = [js["runs"][f"{n},4800"]["TS_low3"][0] for n in (80, 100, 120)]
    assert np.allclose(low, [3.486e-3, 3.001e-3, 2.671e-3], atol=5e-7)
    assert low[0] > low[1] > low[2] > 0
    # adding modes lowers Delta_T: the difference 80 -> 120 is negative definite
    assert np.linalg.eigvalsh(_dT(js, "120,4800") - _dT(js, "80,4800")).max() < 0


def test_section_7b_table(js):
    """RESULTS.md s7b table: probe (2-norm), max |G_z^s - I| and T_S lowest per run, to the printed digits."""
    table = {
        "80,1200": (3.8e-3, 8.9e-2, 3.523e-3),
        "80,2400": (4.9e-4, 3.5e-2, 3.500e-3),
        "80,4800": (2.5e-5, 8.4e-3, 3.486e-3),
        "100,4800": (1.2e-4, 1.8e-2, 3.001e-3),
        "120,4800": (3.3e-4, 2.8e-2, 2.671e-3),
        "140,4800": (6.1e-4, 3.7e-2, 2.480e-3),
        "160,4800": (9.6e-4, 4.5e-2, 2.298e-3),
        "180,4800": (1.4e-3, 5.2e-2, 2.156e-3),
        "200,4800": (1.8e-3, 5.9e-2, 2.074e-3),
        "160,9600": (1.2e-4, 1.8e-2, 2.299e-3),
    }
    for key, (probe, gz, low) in table.items():
        r = js["runs"][key]
        assert abs(r["dT_probe_norm2"] - probe) <= 0.05 * probe, key
        assert abs(r["gz_dev"] - gz) <= 0.05 * gz, key
        assert abs(r["TS_low3"][0] - low) < 5e-7, key
        assert r["Kmax"] == {80: 10, 100: 11, 120: 12, 140: 12, 160: 12, 180: 13, 200: 13}[r["nvec"]]
    # the Modal rows' seconds (run() wall), CPU seconds and BLAS kernel family
    modal = {
        "140,4800": (274, 644, "SkylakeX"),
        "160,4800": (298, 637, "Haswell"),
        "180,4800": (471, 980, "Haswell"),
        "200,4800": (623, 1254, "SkylakeX"),
        "160,9600": (793, 1858, "SkylakeX"),
    }
    for key, (sec, cpu, core) in modal.items():
        r = js["runs"][key]
        assert abs(r["seconds"] - sec) <= 0.5, key
        assert abs(r["source"]["cpu_seconds"] - cpu) <= 0.5, key
        assert r["source"]["blas_core"] == core, key
        assert r["source"]["avx512"] == (core == "SkylakeX"), key


# ---------------------------------------------------------------------------
# 2026-09-24: modal/'s gram runs (BRIEF.md follow-up, 7ee4121)
# ---------------------------------------------------------------------------

NVECS = (80, 100, 120, 140, 160, 180, 200)
TREE = "284eff64b32cbcbd8b99f0198b129e90cc940623"


def _modal_file(key):
    nvec, S = key.split(",")
    with open(os.path.join(G.MODAL_OUT, f"gram_{nvec}_{S}.json")) as fh:
        return json.load(fh)


def _nvec_responses(js):
    return [np.linalg.norm(_dT(js, f"{b},4800") - _dT(js, f"{a},4800"), 2) for a, b in zip(NVECS, NVECS[1:])]


def test_merge_is_the_modal_files_unchanged(js):
    """Every merged run equals its modal/out/ run field for field; its source
    names the file, tree 284eff6 and the platform; the local runs are marked."""
    for key in G.MODAL_RUNS:
        d = _modal_file(key)
        r = js["runs"][key]
        assert {k: v for k, v in r.items() if k != "source"} == d["runs"][key], key
        src = r["source"]
        nvec, S = key.split(",")
        assert src["file"] == f"modal/out/gram_{nvec}_{S}.json"
        assert src["tree_commit"] == TREE == d["meta"]["tree_commit"]
        assert src["platform"] == "Linux-4.19.0-gvisor-x86_64-with-glibc2.36"
        assert src["python"] == "3.12.10"
        assert d["meta"]["guard_before"]["ok"] and d["meta"]["guard_after"]["ok"]
    for key in ("80,1200", "80,2400", "80,4800", "100,4800", "120,4800"):
        assert js["runs"][key]["source"] == G.LOCAL_SOURCE, key
    # idempotent: merging again changes nothing
    again = G.merge_modal(json.loads(json.dumps(js)))
    assert again == js


def test_modal_calibration_matches_the_local_80_mode_run(js):
    """The 80-mode Modal unit is not merged; it matches the local run to 8.2e-15 (dT) and 7.6e-15 (scalars)."""
    cal = js["modal_calibration"]
    d = _modal_file("80,4800")
    diff = float(np.abs(_dT(js, "80,4800") - np.array(d["runs"]["80,4800"]["dT"])).max())
    assert diff == cal["max_abs_diff_dT"]
    assert abs(cal["max_abs_diff_dT"] - 8.2e-15) < 5e-16
    assert abs(cal["max_abs_diff_scalars"] - 7.6e-15) < 5e-16
    assert cal["tree_commit"] == TREE


def test_nvec_responses_through_200_modes(js):
    """S = 4800, spectral norm per 20 modes: 4.48e-3, 1.60e-3, 1.22e-3, 6.49e-4,
    5.21e-4, 3.46e-4 (80 -> 200), every one above Q_low; ratios 0.36, 0.76,
    0.53, 0.80, 0.67. Each step from 120 -> 140 on is negative definite
    (max eigenvalue -1.9e-4, -1.8e-4, -1.4e-4, -8.2e-5); 80 -> 100 and 100 -> 120 are not."""
    d = _nvec_responses(js)
    assert np.allclose(d, [4.48e-3, 1.60e-3, 1.22e-3, 6.49e-4, 5.21e-4, 3.46e-4], rtol=5e-3)
    assert min(d) > js["Q_low"]
    assert abs(d[-1] / js["Q_low"] - 1.35) < 5e-3
    ratios = [b / a for a, b in zip(d, d[1:])]
    assert np.allclose(ratios, [0.36, 0.76, 0.53, 0.80, 0.67], atol=5e-3)
    tops = [np.linalg.eigvalsh(_dT(js, f"{b},4800") - _dT(js, f"{a},4800")).max() for a, b in zip(NVECS, NVECS[1:])]
    assert tops[0] > 0 and tops[1] > 0
    assert np.allclose(tops[0:2], [4.6e-5, 3.1e-4], rtol=2e-2)
    assert np.allclose(tops[2:], [-1.9e-4, -1.8e-4, -1.4e-4, -8.2e-5], rtol=2e-2)
    assert abs(np.linalg.eigvalsh(_dT(js, "200,4800") - _dT(js, "80,4800")).max() - (-1.41e-3)) < 5e-6


def test_the_0p36_prediction_is_refuted(js):
    """s7b's prediction, from the two local differences only: ratio 0.36 per 20
    modes, so 5.7e-4 at 120 -> 140 and 2.0e-4 (below Q_low) at 140 -> 160, with
    a tail near 1e-4 from 160. Measured: 1.22e-3 and 6.49e-4, and the single
    step 160 -> 180 is 5.21e-4."""
    d = _nvec_responses(js)
    r = d[1] / d[0]
    pred = [d[1] * r, d[1] * r * r]
    assert abs(r - 0.36) < 5e-3
    assert np.allclose(pred, [5.7e-4, 2.0e-4], rtol=2e-2)
    assert pred[1] < js["Q_low"] < d[3]
    assert d[2] > 2 * pred[0] and d[3] > 3 * pred[1]
    tail = d[1] * r**3 / (1 - r)  # the predicted sum from 160 on
    assert abs(tail - 1.1e-4) < 5e-6
    assert d[4] > 4 * tail


def test_S_response_at_160_modes(js):
    """160 modes, S = 4800 against 9600: ||dT difference||_2 = 1.82e-4, below
    Q_low; probe 9.59e-4 at 4800 and 1.23e-4 at 9600 (7.8 times smaller); T_S's
    lowest eigenvalue moves by 8.7e-7."""
    s = np.linalg.norm(_dT(js, "160,9600") - _dT(js, "160,4800"), 2)
    assert abs(s - 1.82e-4) < 5e-7
    assert s < js["Q_low"]
    p48, p96 = (js["runs"][k]["dT_probe_norm2"] for k in ("160,4800", "160,9600"))
    assert abs(p48 - 9.59e-4) < 5e-7 and abs(p96 - 1.23e-4) < 5e-7
    assert abs(p48 / p96 - 7.8) < 0.05
    assert abs(p48 / s - 5.3) < 0.05
    dl = js["runs"]["160,9600"]["TS_low3"][0] - js["runs"]["160,4800"]["TS_low3"][0]
    assert abs(dl - 8.7e-7) < 5e-9


def test_band_at_each_nvec_is_above_the_target(js):
    """The docstring's band at each nvec, S = 4800. Complete at 80 (4.48e-3,
    nvec response) and 160 (9.59e-4, the probe); elsewhere a lower bound:
    1.60e-3, 1.22e-3, 6.49e-4 (100, 120, 140: nvec response), 1.36e-3, 1.80e-3
    (180, 200: probe). Not met at any nvec; the smallest is 6.49e-4 at 140,
    2.5 times the target."""
    runs = js["runs"]
    b = {n: G.band_terms(runs, n) for n in NVECS}
    assert G.band_terms(runs, 80)["band"] == max(band(js))
    assert [n for n in NVECS if b[n]["complete"]] == [80, 160]
    expect = {80: (4.48e-3, "nvec"), 100: (1.60e-3, "nvec"), 120: (1.22e-3, "nvec"), 140: (6.49e-4, "nvec"),
              160: (9.59e-4, "probe"), 180: (1.36e-3, "probe"), 200: (1.80e-3, "probe")}
    for n, (val, binding) in expect.items():
        assert abs(b[n]["band"] - val) <= 5e-3 * val, n
        assert b[n]["binding"] == binding, n
        assert b[n]["band"] > js["Q_low"], n
    assert min(NVECS, key=lambda n: b[n]["band"]) == 140
    assert abs(b[140]["band"] / js["Q_low"] - 2.5) < 0.05  # 2.5 times the target
    assert abs(b[140]["probe"] - 6.13e-4) < 5e-7  # just under the nvec term there
    assert b[200]["nvec"] is None  # needs a 220-mode run
    # 160: of the two measured responses only the nvec one is above the target
    assert b[160]["S"] < js["Q_low"] < b[160]["nvec"] < b[160]["probe"]
    # the probe at S = 4800 is above the target from 120 modes on
    assert [n for n in NVECS if runs[f"{n},4800"]["dT_probe_norm2"] > js["Q_low"]] == [120, 140, 160, 180, 200]


def test_lowest_eigenvalue_of_T_S_through_200_modes(js):
    """T_S lowest 3.486e-3 ... 2.074e-3 from 80 to 200 modes, falling by 4.85e-4,
    3.30e-4, 1.91e-4, 1.82e-4, 1.42e-4, 8.2e-5 per 20 modes (1.41e-3 in all),
    positive throughout; at 160 it exceeds the complete band by 1.34e-3, at 80
    it lies inside it (by 1.0e-3); from (80, 1200) to (200, 4800) it moves by 1.45e-3."""
    low = [js["runs"][f"{n},4800"]["TS_low3"][0] for n in NVECS]
    assert all(x > 0 for x in low)
    drops = [a - b for a, b in zip(low, low[1:])]
    assert np.allclose(drops, [4.85e-4, 3.30e-4, 1.91e-4, 1.82e-4, 1.42e-4, 8.2e-5], atol=5e-7)
    assert abs(low[0] - low[-1] - 1.41e-3) < 5e-6
    b80, b160 = (G.band_terms(js["runs"], n)["band"] for n in (80, 160))
    assert abs(low[4] - b160 - 1.34e-3) < 5e-6
    assert abs(b80 - low[0] - 1.0e-3) < 5e-5
    assert abs(js["runs"]["80,1200"]["TS_low3"][0] - low[-1] - 1.45e-3) < 5e-6


def test_modal_cost_against_the_s7b_estimate(js):
    """s7b estimated 3 to 10 CPU minutes and 2 to 5 GB per run, about 40 CPU
    minutes (laptop scale). Modal, 4 vCPU per unit: 637 to 1858 CPU s per run,
    5373 in all (89.5 min), peak 1281 to 2064 MiB; its 80-mode calibration took
    426 CPU s against 107 s of laptop wall."""
    cpu = [js["runs"][k]["source"]["cpu_seconds"] for k in G.MODAL_RUNS]
    peak = [js["runs"][k]["source"]["peak_rss_mib"] for k in G.MODAL_RUNS]
    assert (round(min(cpu)), round(max(cpu))) == (637, 1858)
    assert abs(sum(cpu) - 5373) < 1 and abs(sum(cpu) / 60 - 89.5) < 0.05
    assert (round(min(peak)), round(max(peak))) == (1281, 2064)
    cal = _modal_file("80,4800")["meta"]
    assert round(cal["cpu_seconds"]) == 426 and js["runs"]["80,4800"]["seconds"] == 107.0


def test_next_run_estimate(js):
    """Proposal, not run: band(200, 9600) in the docstring's shape needs (200, 9600)
    and (220, 9600) (Kmax 13 both). Scaled from Modal run() times: S = 9600 took
    2.66 times S = 4800 at 160 modes, and 180 -> 200 modes took 1.32 times at
    Kmax 13, so about 1660 s and 2190 s, 3850 s in all, 0.34 USD at modal/RUNS.md's
    computed rate (4 cores x 1.31e-5 + 16 GiB x 2.22e-6 USD/s)."""
    import ta_prolate as TP

    sec = {k: js["runs"][k]["seconds"] for k in js["runs"]}
    s_ratio = sec["160,9600"] / sec["160,4800"]
    n_ratio = sec["200,4800"] / sec["180,4800"]
    assert abs(s_ratio - 2.66) < 5e-3 and abs(n_ratio - 1.32) < 5e-3
    e200 = sec["200,4800"] * s_ratio
    e220 = e200 * n_ratio
    assert abs(e200 - 1660) < 10 and abs(e220 - 2190) < 10 and abs(e200 + e220 - 3850) < 10
    assert TP.kmax_for(200) == TP.kmax_for(220) == 13
    rate = 4 * 1.31e-5 + 16 * 2.22e-6
    assert abs((e200 + e220) * rate - 0.34) < 5e-3


def test_mixed_blas_kernels_are_small_against_the_differences(js):
    """The nvec differences from 140 on mix SkylakeX and Haswell runs. Their own
    kernel sensitivity was not measured; checker/'s 200-mode unit moves by at
    most 3.3e-7 under a kernel change (modal/out, Sandybridge against the
    calibration unit, max abs over the three cells), 9.5e-4 of the smallest
    difference used here (3.46e-4)."""
    def ts(name):
        with open(os.path.join(G.MODAL_OUT, f"{name}.json")) as fh:
            return {k: np.array(v, dtype=float) for k, v in json.load(fh)["T_S"].items()}

    a, b = ts("checker_200_2400_32"), ts("checker_200_2400_32_sandybridge")
    moved = max(float(np.abs(a[k] - b[k]).max()) for k in a)
    assert abs(moved - 3.3e-7) < 5e-9
    smallest = min(_nvec_responses(js))
    assert abs(moved / smallest - 9.5e-4) < 5e-6
    cores = {js["runs"][f"{n},4800"]["source"]["blas_core"] for n in (140, 160, 180, 200)}
    assert cores == {"SkylakeX", "Haswell"}
