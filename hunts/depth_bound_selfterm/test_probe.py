import numpy as np
import pytest

from probe import (
    ARTIFACT,
    SCAN_STEP,
    Y_MAX,
    S_mpmath,
    S_numpy,
    load_kernel,
    run_measurements,
    scan_control,
)


@pytest.fixture(scope="module")
def res():
    return run_measurements()


def test_artifact_roles_and_h():
    import json

    records = json.loads(ARTIFACT.read_text())
    assert records[0]["label"] == "control, in-band only"
    assert records[1]["label"] == "out-of-band positivity to 1.5"
    assert records[0]["z"] == []
    ctrl = load_kernel(records[0])
    dual = load_kernel(records[1])
    assert ctrl["z"] is None
    assert dual["z"] is not None
    assert abs(dual["h"] - 1.0 / 16.0) < 1e-15
    assert abs(ctrl["h"] - 1.0 / 16.0) < 1e-15


def test_dual_crossings_are_the_preserved_roots(res):
    d = res["dual"]
    assert abs(d["r0_numpy"] - 0.125) < 1e-14
    assert d["y_r0"] is not None
    assert d["y_0"] is not None
    assert abs(d["y_r0"]["y_numpy"] - 0.919892507) < 1e-7
    assert abs(d["y_0"]["y_numpy"] - 0.952877351) < 1e-7


def test_two_routes_agree_at_the_crossing_depths(res):
    d = res["dual"]
    assert d["r0_agreement"] < 1e-14
    assert d["y_r0"]["agreement"] < 1e-12
    assert d["y_0"]["agreement"] < 1e-12
    assert abs(d["y_r0"]["y_mpmath"] - 0.919892507) < 1e-7
    assert abs(d["y_0"]["y_mpmath"] - 0.952877351) < 1e-7


def test_scan_finds_the_first_drop_not_a_later_root(res):
    import json

    dual = load_kernel(json.loads(ARTIFACT.read_text())[1])
    r0 = S_numpy(0.0, dual)
    y_r0 = res["dual"]["y_r0"]["y_numpy"]
    y_0 = res["dual"]["y_0"]["y_numpy"]
    n = int(round(Y_MAX / SCAN_STEP))
    ys = np.linspace(0.0, Y_MAX, n + 1)
    before_r0 = [float(y) for y in ys if 0.0 < y < y_r0]
    before_0 = [float(y) for y in ys if 0.0 < y < y_0]
    assert before_r0 and before_0
    assert all(S_numpy(y, dual) >= r0 for y in before_r0)
    assert all(S_numpy(y, dual) >= 0.0 for y in before_0)
    assert S_numpy(min(ys[ys > y_r0]), dual) < r0
    assert S_numpy(min(ys[ys > y_0]), dual) < 0.0


def test_inband_control_has_no_crossing_and_rises(res):
    c = res["control"]
    assert abs(c["r0_numpy"] - 0.125) < 1e-14
    assert c["y_r0"] is None
    assert c["y_0"] is None
    sc = c["scan"]
    assert sc["monotonic_increase"] is True
    assert abs(sc["S_at_0.9"] - 1.011758641909) < 1e-9
    assert abs(sc["S_at_1.0"] - 1.525986086627) < 1e-9
    assert sc["S_at_1.0"] > sc["S_at_0.9"] > c["r0_numpy"]


def test_control_scan_covers_the_interval():
    import json

    ctrl = load_kernel(json.loads(ARTIFACT.read_text())[0])
    sc = scan_control(ctrl)
    assert sc["ys"][0] == 0.0
    assert abs(sc["ys"][-1] - Y_MAX) < 1e-15
    assert np.max(np.diff(sc["ys"])) <= SCAN_STEP + 1e-15
    assert sc["monotonic_increase"]
    assert sc["S_min"] == pytest.approx(S_numpy(0.0, ctrl), rel=0, abs=1e-15)


def test_mpmath_route_uses_workdps_not_global_dps():
    import inspect

    import mpmath as mp

    import probe as probe_mod

    src = inspect.getsource(probe_mod)
    assert "mp.workdps" in src
    assert "mp.dps =" not in src
    before = int(mp.mp.dps)
    import json

    dual = load_kernel(json.loads(ARTIFACT.read_text())[1])
    S_mpmath(0.5, dual)
    assert int(mp.mp.dps) == before
