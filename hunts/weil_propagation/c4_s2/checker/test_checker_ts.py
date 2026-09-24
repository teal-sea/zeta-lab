"""Phase 3 tests (checker/), WRITTEN AFTER ROUTING (two_adic/ ad97abf, 88d9dd1,
8dc8525: T_S for zeta). Two groups.

1. The snapshot fails closed (checker_glue.ts_key). It is keyed to the HEAD
   blobs of every T_S input, while the import reads the working tree; so a
   dirty input, a moved digest or a missing unit yields no snapshot rows,
   and T_S() raises instead of building live. A git error raises and is
   never read as clean. The inputs are the import closure of
   two_adic/ta_ts.py plus kernel/'s two moments JSON (ts_closure,
   2026-09-24); a committed change to them turns
   test_snapshot_key_is_the_built_commits_and_heads red, not skipped.
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

import functools
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
    # untracked, but shadows a name the closure imports (kernel/ precedes
    # two_adic/ on sys.path once KernelProvider has run)
    f"?? {P}/kernel/ta_mellin.py",
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
    # tracked, but outside the import closure of ta_ts.py
    f" M {P}/two_adic/ta_gram_probe.py",
    f" M {P}/two_adic/ta_hs.py",
    f" M {P}/kernel/calibrate.py",
    f"?? {P}/two_adic/ta_new_helper.py",
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


def test_loaded_module_outside_the_closure_is_caught():
    """A tracked module the static scan did not reach, loaded during a build,
    is refused too: the runtime check of the scan."""
    import types

    probe = types.ModuleType("ta_gram_probe")
    probe.__file__ = os.path.join(GLUE.TWO_ADIC, "ta_gram_probe.py")
    sonin = types.ModuleType("sonin")
    sonin.__file__ = os.path.join(GLUE.KERNEL, "sonin.py")
    assert GLUE.loaded_inputs_outside_key({"a": probe, "b": sonin}) == [f"{P}/two_adic/ta_gram_probe.py"]


def test_git_error_raises_not_clean():
    with pytest.raises(subprocess.CalledProcessError):
        GLUE._git("rev-parse", "--verify", "no-such-revision-for-checker")


CLOSURE = ["kernel/cells_dps40.json", "kernel/cells_dps60.json", "kernel/sonin.py",
           "two_adic/ta_data.py", "two_adic/ta_mellin.py", "two_adic/ta_prolate.py",
           "two_adic/ta_ts.py"]


def test_closure_at_head_is_exactly():
    """ta_ts imports ta_data, and lazily (inside KernelProvider) sonin and
    ta_prolate; ta_prolate imports sonin and ta_mellin. Equality, not a
    subset: a module entering the closure fails this test."""
    _, paths, _ = GLUE.ts_closure("HEAD")
    assert [p.split(P + "/", 1)[1] for p in paths] == CLOSURE
    assert f"{P}/two_adic/ta_gram_probe.py" not in paths


def test_snapshot_key_is_the_built_commits_and_heads():
    """The committed snapshot was rebuilt on 2026-09-24 (follow-up 2, s7.8)
    from modal/out_rho, every unit built on Modal from the tree e2b46a5. Its
    key is the closure digest there and at c3dca00 (where two_adic/ changed
    rho), and HEAD's closure digest equals it. A two_adic/ or kernel/ commit
    that changes a closure file turns this red rather than letting the
    snapshot's tests skip: rebuild with run_checker_ts.py. (Until then the
    snapshot was built at 8dc8525 under digest 1dcab230; it is at 3dc0a74.)"""
    with open(GLUE.TS_SNAPSHOT) as fh:
        meta = json.load(fh)["meta"]
    assert meta["source"] == "modal/out_rho" and meta["routed_two_adic"] == "c3dca00"
    assert meta["built_tree"].startswith("e2b46a5")
    built = GLUE.ts_closure(meta["built_tree"])
    routed = GLUE.ts_closure("c3dca00")
    head = GLUE.ts_closure("HEAD")
    assert built[0] == routed[0] == head[0] == meta["ts_inputs_digest"]
    assert meta["ts_inputs_digest"].startswith("b2e7787bce7a")
    assert built[1] == head[1]
    assert GLUE.ts_closure("8dc8525")[0].startswith("1dcab230")  # the old key, for the record


# The same scan over a directory copy of HEAD's two_adic/ and kernel/ (tmp_path,
# never the tree itself), with git's blob ids, so a planted edit is measured
# by the function ts_key uses.


@pytest.fixture(scope="module")
def head_blobs():
    import subprocess

    top = GLUE._git("rev-parse", "--show-toplevel").strip()
    out = {}
    for ln in GLUE._git("ls-tree", "-r", "HEAD", "--", f"{P}/two_adic", f"{P}/kernel").splitlines():
        meta, path = ln.split("\t", 1)
        out[path] = subprocess.run(["git", "cat-file", "blob", meta.split()[2]], cwd=top,
                                   capture_output=True, check=True).stdout
    return out


class _Copy:
    def __init__(self, root, blobs):
        self.root = root
        for p, b in blobs.items():
            f = root / p
            f.parent.mkdir(parents=True, exist_ok=True)
            f.write_bytes(b)

    def file(self, rel):
        return self.root / P / rel

    def key(self):
        import hashlib

        blobs = {}
        for f in (self.root / P).rglob("*"):
            if f.is_file():
                b = f.read_bytes()
                blobs[f.relative_to(self.root).as_posix()] = hashlib.sha1(b"blob %d\0" % len(b) + b).hexdigest()
        return GLUE.closure(blobs, lambda p: (self.root / p).read_bytes())


@pytest.fixture
def copy(tmp_path, head_blobs):
    return _Copy(tmp_path, head_blobs)


def _plant(path, text):
    path.write_text(path.read_text() + text)


def test_directory_route_reproduces_the_git_key(copy):
    assert copy.key()[:2] == GLUE.ts_closure("HEAD")[:2]


def test_file_outside_the_closure_does_not_move_the_key(copy):
    k0 = copy.key()[0]
    _plant(copy.file("two_adic/ta_gram_probe.py"), "\nX_PLANTED = 1\n")
    copy.file("two_adic/ta_new_helper.py").write_text("Y = 2\n")
    _plant(copy.file("two_adic/RESULTS.md"), "\nplanted\n")
    assert copy.key()[0] == k0


def test_changed_blob_in_the_closure_moves_the_key(copy):
    k0 = copy.key()[0]
    _plant(copy.file("kernel/sonin.py"), "\n# planted\n")
    assert copy.key()[0] != k0


def test_planted_lazy_import_brings_its_module_into_the_key(copy):
    """A new module imported inside a function (as KernelProvider imports
    sonin) enters the closure, and from then on its own blob is keyed."""
    copy.file("two_adic/ta_planted.py").write_text("Z = 3\n")
    k0, paths0, _ = copy.key()
    assert f"{P}/two_adic/ta_planted.py" not in paths0
    _plant(copy.file("two_adic/ta_prolate.py"), "\n\ndef _planted():\n    import ta_planted\n    return ta_planted.Z\n")
    k1, paths1, _ = copy.key()
    assert k1 != k0 and set(paths1) - set(paths0) == {f"{P}/two_adic/ta_planted.py"}
    copy.file("two_adic/ta_planted.py").write_text("Z = 4\n")
    assert copy.key()[0] != k1


def test_planted_import_is_followed_transitively(copy):
    """ta_run_ts imports ta_hs: importing ta_run_ts from ta_prolate brings
    both in."""
    _plant(copy.file("two_adic/ta_prolate.py"), "\n\ndef _planted():\n    import ta_run_ts\n    return ta_run_ts\n")
    _, paths, _ = copy.key()
    assert {f"{P}/two_adic/ta_run_ts.py", f"{P}/two_adic/ta_hs.py"} <= set(paths)


def test_loader_reached_transitively_raises(copy):
    """ta_gram_probe -> ta_run_prolate -> ta_es, which loads a file by path
    (spec_from_file_location). Importing the probe from ta_ts would put a
    load the scan cannot name into T_S: the key raises instead of omitting it."""
    _plant(copy.file("two_adic/ta_ts.py"), "\n\ndef _planted():\n    from ta_gram_probe import main\n    return main\n")
    with pytest.raises(GLUE.UnresolvedImport, match=r"ta_es\.py:\d+: spec_from_file_location"):
        copy.key()


def test_unresolvable_dynamic_import_raises(copy):
    _plant(copy.file("two_adic/ta_mellin.py"), "\n\ndef _planted(n):\n    return __import__(n)\n")
    with pytest.raises(GLUE.UnresolvedImport, match="non-literal"):
        copy.key()


def test_re_compile_is_not_a_loader():
    """compile() as a method (re.compile) loads nothing; exec() does."""
    assert GLUE.imported_names("import re\nP = re.compile('x')\n") == {"re"}
    with pytest.raises(GLUE.UnresolvedImport, match="exec"):
        GLUE.imported_names("exec(open('f').read())\n")


def test_missing_moments_json_raises(copy):
    copy.file("kernel/cells_dps60.json").unlink()
    with pytest.raises(RuntimeError, match="absent"):
        copy.key()


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
    """One snapshot unit against a live two_adic/ T_S_matrix call
    (c = 2.2, N = 8, (80, 1200)): the snapshot route composes exactly as the
    builder does. Bitwise until s7.8 (laptop rows); since then through the
    laptop half of modal/'s calibration. About 20 s."""
    if GLUE._snapshot_rows("2.2", 8, 40) is None:
        pytest.skip("snapshot stale, dirty or absent (checker_glue.ts_key)")
    import numpy as np

    import run_checker_ts as RT

    snap = np.array(GLUE._snapshot_rows("2.2", 8, 40))
    live = np.asarray(GLUE.T_S_live("2.2", 8, 40))
    # since s7.8 every snapshot row is a Modal build: the laptop build of the
    # same unit (modal/out_rho, local calibration half) equals the live call
    # bitwise, and the Modal row differs from it by the measured calibration
    # (5.8e-15 at c = 2.2; 7.1e-15 over the unit, threshold 1e-10)
    with open(os.path.join(RT.MODAL_OUT_RHO, RT.RHO_LOCAL_CALIBRATION)) as fh:
        local = np.array(json.load(fh)["T_S"]["2.2|8|40|80|1200"])
    assert np.array_equal(local, live)
    assert "%.1e" % np.abs(snap - live).max() == "5.8e-15"


def test_cells_json_keyed_to_routed_inputs():
    """Since s7.8: rho by QR (two_adic/ c3dca00, also the probe's commit),
    every unit from modal/out_rho, the reading committed at 49db49f. (Until
    then: routed 8dc8525, probe 015895f; at 3dc0a74.)"""
    m = _cells()["meta"]
    assert m["routed_two_adic"] == "c3dca00" and m["probe_commit"] == "c3dca00"
    assert m["reading_commit"] == "49db49f" and m["source"] == "modal/out_rho"
    assert m["python"].startswith("/Users/thomas/zeta-lab/.venv/")
    assert m["pending"] == [] and m["n32_pending"] == []
    assert set(m["units"]) == {"80|1200|8", "120|1600|16", "200|2400|32", "80|1600|16",
                               "120|1200|16", "80|1200|16", "160|1600|16",
                               "240|2400|32", "280|2266|32", "319|2633|32", "364|3060|32"}
    assert {u["source"]["file"].split("/")[-2] for u in m["units"].values()} == {"out_rho"}


def test_band_per_row_is_the_largest_measured_response():
    """P1 exactly; band(c, N) = max(two_adic/'s probe for the row, the row's
    refinement response, the quadrature response at N = 16). At N = 32 the
    refinement response is the largest over the cell's admitted refined rows
    (s7.8; until then the 240-mode row alone, s7.7, and before that the
    N = 16 proxy of 535882e, which is kept as band_32_proxy)."""
    J = _cells()["cells"]
    for c in CELLS:
        r = J[c]
        for N in ("8", "16", "32"):
            x = r[N]
            assert x["T_S_herm_defect"] == 0, (c, N)
            assert x["band"] == max(x["probe"], x["refinement_response"], r["quadrature_response_N16"]), (c, N)
            assert x["refinement_response"] == r["refinement_response"][N], (c, N)
        assert r["band_32_proxy"] == max(r["32"]["probe"], r["16"]["refinement_response"],
                                         r["quadrature_response_N16"])
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
        # 0 exactly on the old route's laptop rows; since s7.8 the two units ran on
        # different OpenBLAS kernel families (SkylakeX, Haswell): 4.4e-15 to 6.2e-15
        assert 0 <= J[c]["P3_same_settings_defect"] < 1e-14, c
        assert 0 < J[c]["P3_converged_rows_defect_norm"] <= J[c]["band_cell"], c
    d = [J[c]["P3_same_settings_defect"] for c in CELLS]
    assert ("%.1e" % min(d), "%.1e" % max(d)) == ("4.4e-15", "6.2e-15")
    S = _snap()["units"]
    assert S["80|1200|8"]["source"]["blas_core"] == "SkylakeX" and S["80|1200|16"]["source"]["blas_core"] == "Haswell"


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
    apply to them. Until 535882e (band_cell from the N = 16 proxy) the counts
    were 1, 4, 3 / 4, 8, 20 / 4, 9, 20: a failure of banded P4 at 2.2. At the
    old route's N = 32 band (s7.7) they were 0, 0, 0 / 1, 2, 2 / 2, 2, 2.
    Under the QR rho (s7.8) band_cell is 3.0e-2 / 1.4e-2 / 8.2e-3 and the
    counts are 0, 0, 0 / 2, 6, 8 / 4, 9, 20: nondecreasing on every cell,
    growing at 2.5 and 2.9."""
    J = _cells()["cells"]
    assert ["%.1e" % J[c]["band_cell"] for c in CELLS] == ["3.0e-02", "1.4e-02", "8.2e-03"]
    want = {"2.2": [0, 0, 0], "2.5": [2, 6, 8], "2.9": [4, 9, 20]}
    for c in CELLS:
        assert [J[c][N]["full"]["n_minus_at_band_cell"] for N in ("8", "16", "32")] == want[c], c


def test_T_S_removes_the_deep_product_side_negatives():
    """Q - T_inf (product side): lambda_min -0.30 to -0.49, negative count
    below -band growing in N. R_S = Q - T_S: lambda_min above -0.13 on every
    row. Until 535882e the count was not smaller in general (c = 2.5,
    N = 32: 20 for R_S against 18 for Q - T_inf at the proxy band); at the
    old route's N = 32 band it was 2 against 17 (s7.7); under the QR rho,
    8 against 18 (s7.8)."""
    J = _cells()["cells"]
    for c in CELLS:
        ninf = [J[c][N]["R_inf_full"]["n_minus"] for N in ("8", "16", "32")]
        assert ninf[0] < ninf[1] < ninf[2], (c, ninf)
        for N in ("8", "16", "32"):
            assert J[c][N]["R_inf_full"]["low3"][0] < -0.29, (c, N)
            assert J[c][N]["full"]["low3"][0] > -0.13, (c, N)
    assert J["2.5"]["32"]["full"]["n_minus"] == 8 and J["2.5"]["32"]["R_inf_full"]["n_minus"] == 18


def test_R_S_negative_count_below_band():
    """n_-(R_S) below -band(c, N), full space: 4, 4, 0 at 2.2; 4, 9, 8 at
    2.5; 4, 10, 20 at 2.9 (N = 8, 16, 32), under the QR rho with the N = 32
    band of s7.8. On the old route (s7.7) the N = 32 counts were 0, 2, 2,
    and at the N = 16 proxy band of 535882e 3, 20, 20."""
    J = _cells()["cells"]
    want = {"2.2": [4, 4, 0], "2.5": [4, 9, 8], "2.9": [4, 10, 20]}
    for c in CELLS:
        assert [J[c][N]["full"]["n_minus"] for N in ("8", "16", "32")] == want[c], c


def test_two_deep_negatives_at_2_9_on_every_class():
    """c = 2.9: the two lowest eigenvalues of R_S are below -3.7e-2 on every
    class and every N. Against the largest band of the cell, under the QR rho
    the probe 8.18e-3 at N = 32 (s7.8; 3.16e-2 on the old route, s7.7): the
    second sits 4.6 to 5.6 times below it, the first 8.3 to 14.7 times."""
    J = _cells()["cells"]["2.9"]
    bc = J["band_cell"]
    r1, r2 = [], []
    for N in ("8", "16", "32"):
        for cls in ("full", "minus", "minus_zero"):
            lo = J[N][cls]["low3"]
            assert lo[1] < -0.037 and lo[1] < -bc, (N, cls)
            r1.append(-lo[0] / bc)
            r2.append(-lo[1] / bc)
    assert ("%.1f" % min(r2), "%.1f" % max(r2)) == ("4.6", "5.6")
    assert ("%.1f" % min(r1), "%.1f" % max(r1)) == ("8.3", "14.7")


def test_top_half_split_of_the_negatives():
    """RESULTS s7.3: negatives of R_S (full) with more than half their weight
    on |n| > N/2, and the rest."""
    J = _cells()["cells"]
    top = {"2.5": [2, 4, 2], "2.9": [2, 5, 12]}  # N = 32 on the old route (s7.7): 0 and 0
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
        assert row[6] == "%.1e" % r["P3_same_settings_defect"] and row[7] == "%g" % r["dps60_float64_floor_N8"]
    rows = _table(text, "### 7.3 R_S", "### 7.3a")
    t2 = [r for r in rows if len(r) == 8]
    t3 = [r for r in rows if len(r) == 7]
    und = [r for r in rows if len(r) == 4]
    assert len(t2) == len(t3) == len(und) == 9
    for row in t2:
        x = J[row[0]][row[1]]
        assert row[3] == g(x["probe"]) and row[4] == g(x["refinement_response"]) and row[5] == g(x["band"])
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
    want = {"2.2": [2, 1, 0], "2.5": [2, 4, 6], "2.9": [2, 4, 8]}  # N = 32 on the old route: 0, 2, 2
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
    key = {"(80, 1200)": "80_S1200", "(120, 1600)": "120", "(160, 1600)": "160", "(80, 1600)": "80"}
    d1 = [r for r in rows if len(r) == 6 and r[1] in key]
    d2 = [r for r in rows if len(r) == 7]
    assert len(d1) == 12 and len(d2) == 9
    for row in d1:
        d = J[row[0]]["modes_N16_S1600"][key[row[1]]]
        assert row[2] == str(d["N16_n_minus"]) and row[3] == str(d["N16_n_minus_top_half"])
        assert row[4] == ", ".join(f(v) for v in d["N16_low3"])
        assert row[5] == ", ".join(f(v) for v in d["N16_last_two_counted"])
    for row in d2:
        x = J[row[0]][row[1]]
        h = x["resolved_half"]
        assert row[2] == str(h["dim"]) and row[3] == f"{h['n_minus']} / {h['n_undecided']}"
        assert row[4] == ", ".join(f(v) for v in h["low3"])
        assert row[5] == str(x["full"]["n_minus"])
        assert row[6] == str(x["full"]["n_minus"] - x["full_n_minus_top_half"])


def test_growth_at_2_9_survives_120_to_160_modes():
    """RESULTS line 2 and s7.3a: at c = 2.9, N = 16 holds 10 negatives below
    -band(c, 16) at 120 and at 160 modes (5 on |n| > 8 both times), against 4
    at N = 8 in every build; the last pair counted at 160 modes is -8.9e-3,
    -8.3e-3, 1.4 to 1.5 times the band. At 2.5 the count falls 9 -> 8, at
    2.2 5 -> 4 -> 3 (the (80, 1200) build first)."""
    J = _cells()["cells"]
    m = J["2.9"]["modes_N16_S1600"]
    assert [m[k]["N16_n_minus"] for k in ("80_S1200", "120", "160")] == [12, 10, 10]
    assert [m[k]["N16_n_minus_top_half"] for k in ("80_S1200", "120", "160")] == [8, 5, 5]
    assert [m[k]["N8_block_n_minus"] for k in ("80", "120", "160")] == [4, 4, 4]
    assert J["2.9"]["8"]["full"]["n_minus"] == 4
    pair, b = m["160"]["N16_last_two_counted"], J["2.9"]["16"]["band"]
    assert ["%.1e" % x for x in pair] == ["-8.9e-03", "-8.3e-03"]
    assert ["%.1f" % (abs(x) / b) for x in pair] == ["1.5", "1.4"]
    assert [J["2.5"]["modes_N16_S1600"][k]["N16_n_minus"] for k in ("80_S1200", "120", "160")] == [10, 9, 8]
    assert [J["2.2"]["modes_N16_S1600"][k]["N16_n_minus"] for k in ("80_S1200", "120", "160")] == [5, 4, 3]
    wb = {"2.2": [2, 2, 0], "2.5": [2, 5, 6], "2.9": [2, 5, 8]}  # N = 32 under the QR rho (s7.8)
    for c in CELLS:
        assert [J[c][N]["full"]["n_minus"] - J[c][N]["full_n_minus_top_half"] for N in ("8", "16", "32")] == wb[c]


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


def test_what_sets_the_band():
    """RESULTS s7.3: the refinement response sets the band on every N = 8
    row, at 2.2 for N = 16 and at 2.2 and 2.5 for N = 32 (the 240-mode row
    at 2.2, the 319-mode row at 2.5); the Gram probe sets it at 2.5 and 2.9
    for N = 16 and at 2.9 for N = 32 (s7.8). On the old route the 240-mode
    response set it on every N = 32 row (s7.7)."""
    J = _cells()["cells"]
    for c in CELLS:
        for N in ("8", "16", "32"):
            x = J[c][N]
            by_ref = N == "8" or c == "2.2" or (N == "32" and c == "2.5")
            assert x["band"] == (x["refinement_response"] if by_ref else x["probe"]), (c, N)
    m = {c: J[c]["modes_N32"] for c in CELLS}
    assert J["2.2"]["32"]["band"] == m["2.2"]["builds"]["240"]["dT_vs_200"]
    assert J["2.5"]["32"]["band"] == m["2.5"]["builds"]["319"]["dT_vs_200"]


# ------------------------------------ s7.7: the Modal N = 32 rows (2026-09-24)
#
# Written after the s7.6 criterion's reading was committed (ee4a1ff) and after
# the rows were analysed: these pin measured values, they do not test a
# prediction. The merge tests read modal/out (read only) and the snapshot.
# Since follow-up 2 (s7.8) they pin the OLD ROUTE's record (rho by
# np.linalg.inv): the snapshot and cells JSON at 3dc0a74 (both last written
# 8d66d09), read from git history, not the working tree.

OLD = "3dc0a74"


@functools.lru_cache(maxsize=None)
def _old_json(name):
    return json.loads(GLUE._git("show", f"{OLD}:{P}/checker/{name}"))


def _old_cells():
    return _old_json("checker_ts_cells.json")


def _old_snap():
    return _old_json("checker_ts_snapshot.json")

MODAL_FILES = {"240|2400|32": "checker_240_2400_32.json", "280|2266|32": "checker_280_2266_32.json",
               "319|2633|32": "checker_319_2633_32.json", "364|3060|32": "checker_364_3060_32.json"}


def _modal(fname):
    import run_checker_ts as RT

    path = os.path.join(RT.MODAL_OUT, fname)
    if not os.path.exists(path):
        pytest.skip(f"modal/out/{fname} absent")
    with open(path, "rb") as fh:
        raw = fh.read()
    return raw, json.loads(raw)


@pytest.mark.parametrize("ukey", sorted(MODAL_FILES))
def test_merged_rows_are_the_modal_files_bitwise(ukey):
    """Each merged unit: its three rows equal the modal/out file's rows
    exactly, the file carries the snapshot's T_S input digest with the
    in-container guard clean before and after, and the unit records its
    source file and platform."""
    import hashlib

    S = _old_snap()
    raw, d = _modal(MODAL_FILES[ukey])
    u = S["units"][ukey]
    assert u["source"]["file"] == f"{P}/modal/out/{MODAL_FILES[ukey]}"
    assert u["source"]["sha256"] == hashlib.sha256(raw).hexdigest()
    assert u["source"]["platform"].startswith("Linux") and u["source"]["python"].startswith("3.12")
    assert d["meta"]["ts_inputs_digest"] == S["meta"]["ts_inputs_digest"] == u["source"]["ts_inputs_digest"]
    assert d["meta"]["guard_before"]["ok"] and d["meta"]["guard_after"]["ok"] and d["meta"]["status"] == "ok"
    assert u["kmax"] == d["units"][ukey]["kmax"] and u["diag"] == d["units"][ukey]["diag"]
    assert set(d["T_S"]) and all(S["T_S"][k] == v for k, v in d["T_S"].items())


def test_merge_keeps_the_laptop_row_and_the_key():
    """The laptop (200, 2400, 32) rows are those of 535882e, bitwise; the meta
    keeps its build commit and re-key (so the fail-closed test still bites);
    the merge is recorded under the same digest."""
    S = _old_snap()
    old = json.loads(GLUE._git("show", f"535882e:{P}/checker/checker_ts_snapshot.json"))
    for k, v in old["T_S"].items():
        assert S["T_S"][k] == v, k
    assert set(S["units"]) - set(old["units"]) == set(MODAL_FILES)
    assert S["meta"]["head_at_start"] == old["meta"]["head_at_start"]
    assert S["meta"]["rekey"] == old["meta"]["rekey"]
    m = S["meta"]["merge_modal"]
    assert m["digest_equal"] and m["ts_inputs_digest"] == S["meta"]["ts_inputs_digest"]
    assert sorted(m["files"]) == sorted(f"{P}/modal/out/{f}" for f in MODAL_FILES.values())
    assert GLUE.TS_SETTINGS[32] == (200, 2400)  # T_S() still serves the laptop row


@pytest.mark.parametrize("plant", ["digest", "status", "guard", "unit"])
def test_merge_refuses_a_bad_modal_file(tmp_path, monkeypatch, plant):
    """modal_unit refuses a file whose digest, status, guard or unit key is
    not what build_unit on the same inputs would have written."""
    import run_checker_ts as RT

    raw, d = _modal("checker_240_2400_32.json")
    digest = d["meta"]["ts_inputs_digest"]
    if plant == "digest":
        d["meta"]["ts_inputs_digest"] = "0" * 64
    elif plant == "status":
        d["meta"]["status"] = "timeout"
    elif plant == "guard":
        d["meta"]["guard_after"]["ok"] = False
    else:
        d["units"] = {"240|2400|16": d["units"]["240|2400|32"]}
    (tmp_path / "x.json").write_text(json.dumps(d))
    monkeypatch.setattr(RT, "MODAL_OUT", str(tmp_path))
    with pytest.raises(SystemExit, match="refused"):
        RT.modal_unit("x.json", 240, 2400, digest)
    (tmp_path / "y.json").write_bytes(raw)
    assert RT.modal_unit("y.json", 240, 2400, digest)[0] == "240|2400|32"


def _n32(c):
    return _old_cells()["cells"][c]["modes_N32"]


def test_N32_band_replaces_the_proxy():
    """band(c, 32) is now the (240, 2400) refinement response: 3.92e-2 /
    2.37e-2 / 3.16e-2, against the proxy band 1.59e-2 / 7.55e-3 / 8.18e-3
    (2.5 to 3.9 times it). The refinement response is 2.5 to 8.6 times the
    N = 16 response it replaces."""
    J = _old_cells()["cells"]
    got = [("%.2e" % J[c]["32"]["band"], "%.2e" % J[c]["band_32_before_merge"]) for c in CELLS]
    assert got == [("3.92e-02", "1.59e-02"), ("2.37e-02", "7.55e-03"), ("3.16e-02", "8.18e-03")]
    r = [J[c]["32"]["band"] / J[c]["band_32_before_merge"] for c in CELLS]
    assert ("%.1f" % min(r), "%.1f" % max(r)) == ("2.5", "3.9")
    q = [J[c]["refinement_response"]["32"] / J[c]["refinement_response"]["16"] for c in CELLS]
    assert ("%.1f" % min(q), "%.1f" % max(q)) == ("2.5", "8.6")


def test_N32_counts_per_build():
    """RESULTS s7.7 table: n_- below -band(c, 32) and the top-half count on
    every N = 32 build, and at the pre-merge (proxy) band."""
    want = {  # build: (n_-, top half, n_- at the proxy band, top half there)
        "2.2": {"200": (0, 0, 3, 2), "240": (0, 0, 9, 6), "280": (20, 8, 25, 9),
                "319": (19, 13, 22, 14), "364": (25, 12, 27, 14)},
        "2.5": {"200": (2, 0, 20, 14), "240": (5, 1, 19, 8), "280": (22, 12, 27, 13),
                "319": (22, 12, 27, 15), "364": (28, 16, 29, 17)},
        "2.9": {"200": (2, 0, 20, 12), "240": (4, 2, 23, 13), "280": (22, 13, 28, 16),
                "319": (20, 12, 26, 16), "364": (28, 17, 30, 18)},
    }
    for c in CELLS:
        B = _n32(c)["builds"]
        for name, w in want[c].items():
            b = B[name]
            assert (b["n_minus"], b["n_minus_top_half"], b["n_minus_at_band_before_merge"],
                    b["n_minus_top_half_at_band_before_merge"]) == w, (c, name)


def test_s7_6_verdict_as_read_before_the_numbers():
    """s7.7 items 4 and 5, committed in ee4a1ff: 240 falls on every cell
    (0, 5, 4 against the N = 16 counts 4, 9, 10); the default rows at 2.2
    and 2.5 are not admitted (P2 fails at the band); the 280-mode row at 2.9
    is admitted and survives (22). The reading does not combine two admitted
    rows that disagree: c = 2.9 is split."""
    want = {"2.2": {"240": (True, "falls"), "364": (False, "not admitted")},
            "2.5": {"240": (True, "falls"), "319": (False, "not admitted")},
            "2.9": {"240": (True, "falls"), "280": (True, "survives")}}
    for c in CELLS:
        m = _n32(c)
        assert m["n_minus_N16"] == {"2.2": 4, "2.5": 9, "2.9": 10}[c]
        assert {k: (v["admitted"], v["label"]) for k, v in m["s7_6_verdict"].items()} == want[c], c


def test_weyl_clause_response_exceeds_every_top_half_depth():
    """s7.7 item 2: the 200-mode row's top-half negatives (14 at 2.5 from
    -1.83e-2 to -8.0e-3, 12 at 2.9 from -1.45e-2 to -1.21e-2) are all
    shallower than ||T_S(240) - T_S(200)||_2, so none is held below -band
    by Weyl; at 2.9 one eigenvalue (the deepest) is."""
    for c, n, lo, hi, kept in (("2.5", 14, "-1.83e-02", "-8.01e-03", 0), ("2.9", 12, "-1.45e-02", "-1.21e-02", 1)):
        m = _n32(c)
        d = m["top_half_depths_200_before_merge"]
        assert len(d) == n and ("%.2e" % min(d), "%.2e" % max(d)) == (lo, hi), c
        b = m["builds"]["240"]
        assert b["top_half_depths_exceeded_by_dT"] == n and b["n_kept_by_weyl"] == kept, c


def test_platform_flag_decides_nothing():
    """No eigenvalue of R_S on any N = 32 build lies within 2.93e-7 + 3.39e-7
    of -band(c, 32). The three builds of the 200-mode unit (laptop, Modal,
    Modal with the Sandybridge kernels) give the same counts at both bands;
    their eigenvalues differ by at most 2.8e-7. The closest eigenvalue to
    -band is 5.0e-4 away (319 modes, c = 2.5); on the 240-mode row, 5.9e-4
    (c = 2.5)."""
    gaps = []
    for c in CELLS:
        m = _n32(c)
        assert "%.2e" % m["platform_flag"] == "6.32e-07"
        for name, b in m["builds"].items():
            assert b["n_flagged"] == 0 and b["n_minus_range"] == [b["n_minus"]] * 2, (c, name)
            gaps.append(b["min_gap_to_band"])
        p = m["platform_200"]
        assert p["counts_equal"] and p["counts_equal_before_merge"] and p["max_eig_diff"] < 2.9e-7, c
    assert "%.1e" % min(gaps) == "5.0e-04"
    assert "%.1e" % min(_n32(c)["builds"]["240"]["min_gap_to_band"] for c in CELLS) == "5.9e-04"


def test_the_240_row_violates_P2_and_moves_the_low_block():
    """T_S(240, 2400) has lowest eigenvalue -7.3e-3 / -8.5e-3 / -8.9e-3, so by
    P2 (T_S >= 0, elementary) its own error is at least that large. It moves
    the N = 8 block by 1.6e-2 to 1.8e-2, 10 to 15 times what 120 -> 160 moved
    it at N = 16 (1.1e-3 to 1.7e-3); the direction it moves most has weight
    0.99 / 0.06 / 0.29 on |n| > 16. At the eps * cond(Gb) estimate (1.1e-3,
    not measured) its counts range 0 / 4 to 6 / 4, all at most the N = 16
    counts."""
    J = _old_cells()["cells"]
    low = [_n32(c)["builds"]["240"]["T_S_low"] for c in CELLS]
    assert ["%.1e" % x for x in low] == ["-7.3e-03", "-8.5e-03", "-8.9e-03"]
    blk = [_n32(c)["builds"]["240"]["dT_vs_200_N8_block"] for c in CELLS]
    ref = [J[c]["mode_response_120_to_160_N16_central_N8"] for c in CELLS]
    assert ("%.1e" % min(blk), "%.1e" % max(blk)) == ("1.6e-02", "1.8e-02")
    assert ("%.1e" % min(ref), "%.1e" % max(ref)) == ("1.1e-03", "1.7e-03")
    rat = [a / b for a, b in zip(blk, ref)]
    assert ("%.1f" % min(rat), "%.0f" % max(rat)) == ("10.5", "15")
    top = [_n32(c)["builds"]["240"]["dT_top_eigvec_weight_on_n_gt_16"] for c in CELLS]
    assert ["%.2f" % x for x in top] == ["0.99", "0.06", "0.29"]
    rng = [_n32(c)["builds"]["240"]["n_minus_range_at_eps_cond"] for c in CELLS]
    assert rng == [[0, 0], [4, 6], [4, 4]]
    for c, r in zip(CELLS, rng):
        assert r[1] <= _n32(c)["n_minus_N16"], c


def test_default_rule_rows_are_past_float64_breakdown():
    """The default-rule rows invert Gb with cond(Gb) 1.1e17 / 2.8e18 / 5.1e17,
    above 1/eps = 4.5e15 (240 modes: 4.9e12; 200: 3.9e9). T_S at 319 and 364
    modes fails P2 by 13.6 to 36.6; at 280 it passes P2 but moves T_S by 1.09
    to 1.32 from the 200-mode row, 32 to 46 times the 240-mode step."""
    cond = {n: _n32("2.5")["builds"][n]["cond_Gb"] for n in ("200", "240", "280", "319", "364")}
    assert ["%.1e" % cond[n] for n in ("200", "240", "280", "319", "364")] == \
        ["3.9e+09", "4.9e+12", "1.1e+17", "2.8e+18", "5.1e+17"]
    eps_inv = 1 / 2.220446049250313e-16
    assert all(cond[n] > eps_inv for n in ("280", "319", "364")) and cond["240"] < eps_inv
    fails = [-_n32(c)["builds"][n]["T_S_low"] for c in CELLS for n in ("319", "364")]
    assert ("%.1f" % min(fails), "%.1f" % max(fails)) == ("13.6", "36.6")
    d280 = [_n32(c)["builds"]["280"]["dT_vs_200"] for c in CELLS]
    assert ("%.2f" % min(d280), "%.2f" % max(d280)) == ("1.09", "1.32")
    assert all(_n32(c)["builds"]["280"]["P2_at_band"] for c in CELLS)
    step = [_n32(c)["builds"]["280"]["dT_vs_200"] / _n32(c)["builds"]["240"]["dT_vs_200"] for c in CELLS]
    assert ("%.0f" % min(step), "%.0f" % max(step)) == ("32", "46")


def test_results_s7_7_table_matches_json():
    """Every row of the RESULTS s7.7 table is the JSON value at the printed
    precision."""
    with open(os.path.join(HERE, "RESULTS.md")) as fh:
        text = fh.read()
    sec = text[text.index("**Every N = 32 build at one threshold"):text.index("**Outcome, by the reading above.**")]
    rows = [[x.strip() for x in r.strip().strip("|").split("|")] for r in sec.splitlines() if r.startswith("| 2.")]
    assert len(rows) == 15
    name = {"(200, 2400) laptop": "200", "(240, 2400)": "240", "(280, 2266)": "280",
            "(319, 2633)": "319", "(364, 3060)": "364"}
    f = lambda x: "%.4g" % x  # noqa: E731
    for r in rows:
        b = _n32(r[0])["builds"][name[r[1]]]
        assert r[2] == "%.1e" % b["cond_Gb"] and r[3] == "%.2e" % b["T_S_low"] and r[4] == "%.2e" % b["dT_vs_200"]
        assert r[5] == f"{b['n_minus']} / {b['n_minus_top_half']}"
        assert r[6] == f"{b['n_minus_at_band_before_merge']} / {b['n_minus_top_half_at_band_before_merge']}"
        assert r[7] == (", ".join(f(v) for v in b["last_two_counted"]) or "none")


def test_s7_7_quoted_numbers():
    """Numbers quoted in s7.6, s7.7 and the first five lines that the other
    s7.7 tests do not already pin."""
    import run_checker_ts as RT

    B = {c: _n32(c)["builds"] for c in CELLS}
    # laptop against Modal, the same 200-mode unit
    d = [B[c]["200_modal"]["dT_vs_200"] for c in CELLS]
    assert ["%.1e" % x for x in d] == ["2.3e-07", "2.6e-07", "2.9e-07"]
    assert "%.1e" % max(_n32(c)["platform_200"]["max_eig_diff"] for c in CELLS) == "2.8e-07"
    # the eps * cond(Gb) estimates and the calibration's ratio to it
    assert "%.1e" % B["2.5"]["240"]["eps_cond_estimate"] == "1.1e-03"
    assert "%.0f" % B["2.5"]["280"]["eps_cond_estimate"] == "24"
    assert "%.2f" % (2.933789496755222e-07 / B["2.5"]["200"]["eps_cond_estimate"]) == "0.34"
    # the 280-mode row: T_S lowest at 2.9, N = 8 block moved
    assert "%.1e" % B["2.9"]["280"]["T_S_low"] == "2.0e-02"
    blk = [B[c]["280"]["dT_vs_200_N8_block"] for c in CELLS]
    assert ("%.1e" % min(blk), "%.2f" % max(blk)) == ("9.1e-02", "0.13")
    assert "%.1f" % B["2.5"]["319"]["T_S_low"] == "-13.6"
    # the 200-mode row's T_S is positive at N = 32
    low = [B[c]["200"]["T_S_low"] for c in CELLS]
    assert ("%.1e" % min(low), "%.1e" % max(low)) == ("1.5e-03", "2.4e-03")
    # Modal child seconds of the four merged units, and the optional unit's cost
    S = _old_snap()
    sec = [S["units"][k]["seconds"] for k in MODAL_FILES]
    assert ("%.0f" % min(sec), "%.0f" % max(sec)) == ("844", "1784")
    _, d240 = _modal(RT.MODAL_UNITS[0][2])
    wall = d240["meta"]["wall_seconds"]
    assert "%.0f" % wall == "890"
    assert "%.3f" % (wall * (4 * 0.0000131 + 16 * 0.00000222)) == "0.078"


def _snap():
    if not os.path.exists(GLUE.TS_SNAPSHOT):
        pytest.skip("checker_ts_snapshot.json absent")
    with open(GLUE.TS_SNAPSHOT) as fh:
        return json.load(fh)


# ------------------------------- s7.8: the rows under the QR rho (follow-up 2)
#
# The reading (band at N = 32, falsifier bins, determinacy gate, verdict rule,
# platform flag) was committed at 49db49f before any eigenvalue of a rebuilt
# row was computed. The rule tests below recompute each clause from the JSON's
# own fields; the pins after them are measured values, not predictions.

RHO_UNITS = ["80|1200|8", "120|1600|16", "200|2400|32", "80|1600|16", "120|1200|16", "80|1200|16",
             "160|1600|16", "240|2400|32", "280|2266|32", "319|2633|32", "364|3060|32"]


def _rho(ukey):
    import run_checker_ts as RT

    nv, S, N = next((nv, S, N) for nv, S, N, _ in RT.RHO_UNITS if f"{nv}|{int(S)}|{N}" == ukey)
    path = os.path.join(RT.MODAL_OUT_RHO, RT.rho_file(nv, S, N))
    if not os.path.exists(path):
        pytest.skip(f"modal/out_rho/{os.path.basename(path)} absent")
    with open(path, "rb") as fh:
        raw = fh.read()
    return (nv, S, N), raw, json.loads(raw)


@pytest.mark.parametrize("ukey", RHO_UNITS)
def test_rho_rows_are_the_out_rho_files_bitwise(ukey):
    """Each unit of the rebuilt snapshot: its rows equal the out_rho file's
    rows exactly, the file carries the snapshot's digest with the in-container
    guard clean and the calibration passed, and the unit records its source
    file, sha256, platform and tree."""
    import hashlib

    S = _snap()
    _, raw, d = _rho(ukey)
    u = S["units"][ukey]
    assert u["source"]["file"] == f"{P}/modal/out_rho/{os.path.basename(u['source']['file'])}"
    assert u["source"]["sha256"] == hashlib.sha256(raw).hexdigest()
    assert u["source"]["platform"].startswith("Linux") and u["source"]["python"].startswith("3.12")
    assert u["source"]["tree_commit"].startswith("e2b46a5") and u["source"]["calibration"]["passed"]
    assert d["meta"]["ts_inputs_digest"] == S["meta"]["ts_inputs_digest"] == u["source"]["ts_inputs_digest"]
    assert d["meta"]["guard_before"]["ok"] and d["meta"]["guard_after"]["ok"] and d["meta"]["status"] == "ok"
    assert u["kmax"] == d["units"][ukey]["kmax"] and u["diag"] == d["units"][ukey]["diag"]
    assert set(d["T_S"]) and all(S["T_S"][k] == v for k, v in d["T_S"].items())


def test_rebuilt_snapshot_holds_only_out_rho_rows():
    """No row of the old route survives in the rebuilt snapshot: every T_S key
    belongs to a unit read from out_rho (six rows at N = 8, three otherwise)."""
    S = _snap()
    assert set(S["units"]) == set(RHO_UNITS)
    want = sum(6 if u.endswith("|8") else 3 for u in RHO_UNITS)
    assert len(S["T_S"]) == want
    for k in S["T_S"]:
        c, N, dps, nv, SS = k.split("|")
        assert f"{nv}|{SS}|{N}" in S["units"], k


@pytest.mark.parametrize("plant", ["digest", "status", "guard", "unit", "calibration", "S"])
def test_rho_unit_refuses_a_bad_file(tmp_path, monkeypatch, plant):
    """rho_unit refuses a file whose digest, status, guard, unit key,
    calibration or S is not what build_unit on the same inputs would have
    written; the untouched file passes."""
    import run_checker_ts as RT

    (nv, S, N), raw, d = _rho("280|2266|32")
    digest = d["meta"]["ts_inputs_digest"]
    if plant == "digest":
        d["meta"]["ts_inputs_digest"] = "0" * 64
    elif plant == "status":
        d["meta"]["status"] = "timeout"
    elif plant == "guard":
        d["meta"]["guard_before"]["ok"] = False
    elif plant == "unit":
        d["units"] = {"280|2266|16": d["units"]["280|2266|32"]}
    elif plant == "calibration":
        d["meta"]["calibration"]["passed"] = False
    else:
        d["units"]["280|2266|32"]["S_exact"] = 2266.0
    (tmp_path / "x.json").write_text(json.dumps(d))
    monkeypatch.setattr(RT, "MODAL_OUT_RHO", str(tmp_path))
    with pytest.raises(SystemExit, match="refused"):
        RT.rho_unit("x.json", nv, S, N, digest)
    (tmp_path / "y.json").write_bytes(raw)
    assert RT.rho_unit("y.json", nv, S, N, digest)[0] == "280|2266|32"


def _m32(c):
    J = _cells()["cells"][c]
    if "modes_N32" not in J:
        pytest.skip("N = 32 pending in checker_ts_cells.json")
    return J["modes_N32"]


def test_s7_8_band_and_admission_as_read():
    """Clauses 2 to 6 recomputed from the JSON: band_0 = max(probe, quadrature);
    a refined row (240, the cell's default row) is admitted iff cond_F < 1e14
    and T_S has no eigenvalue below -band_0; band(c, 32) = max(band_0, the
    admitted rows' ||T_S(X) - T_S(200)||_2); the N = 32 row carries it."""
    import run_checker_ts as RT

    J = _cells()["cells"]
    for c in CELLS:
        r, m = J[c], _m32(c)
        b0 = max(r["32"]["probe"], r["quadrature_response_N16"])
        assert m["band_0"] == r["band_0_32"] == b0, c
        assert r["band_32_proxy"] == max(r["32"]["probe"], r["16"]["refinement_response"],
                                         r["quadrature_response_N16"]), c
        adm = []
        for nv in RT.REFINED[c]:
            b = m["builds"].get(str(nv))
            ok = b is not None and b["cond_F"] < 1e14 and b["T_S_low"] >= -b0
            assert m["s7_6_verdict"][str(nv)]["admitted"] == ok, (c, nv)
            if ok:
                adm.append(str(nv))
        assert m["admitted"] == adm, c
        resp = [m["builds"][n]["dT_vs_200"] for n in adm]
        assert m["band"] == max([b0] + resp) == r["32"]["band"], c
        assert m["refinement_response"] == (max(resp) if resp else None) == r["refinement_response"]["32"], c
        for name, b in m["builds"].items():
            assert b["cond_F"] == max(b["cond_Fz"], b["cond_Fb"]), (c, name)
            assert b["past_gate"] == (b["cond_F"] >= 1e14), (c, name)


def test_s7_8_falsifier_bins_as_read():
    """Clause 7: the bins, fixed before the run, recomputed from T_S's lowest
    eigenvalue on every N = 32 build, at band_0 and at the old band(c, 32)."""
    import run_checker_ts as RT

    def bin_(low, band):
        return ("pass" if low >= -band else "fails at order 1e-2" if low >= -0.1
                else "fails at order 1e-1" if low >= -1 else "fails at order 1 or more")

    old = _old_cells()["cells"]
    for c in CELLS:
        m = _m32(c)
        assert m["old_band_32"] == old[c]["32"]["band"], c
        for name, b in m["builds"].items():
            assert b["P2_bin"] == bin_(b["T_S_low"], m["band_0"]) == RT.p2_bin(b["T_S_low"], m["band_0"]), (c, name)
            assert b["P2_bin_at_old_band"] == bin_(b["T_S_low"], m["old_band_32"]), (c, name)


def test_s7_8_verdict_rule_as_read():
    """Clause 9: per admitted refined row, survives / falls / undecided against
    the rebuilt N = 16 count outside the platform-undecided eigenvalues; the
    cell survives or falls only if every admitted row does, else split."""
    J = _cells()["cells"]
    for c in CELLS:
        m = _m32(c)
        n16 = J[c]["16"]["full"]["n_minus"]
        assert m["n_minus_N16"] == n16, c
        labels = []
        for name, v in m["s7_6_verdict"].items():
            if not v["admitted"]:
                assert v["label"] == "not admitted", (c, name)
                continue
            lo, hi = m["builds"][name]["n_minus_range"]
            want = "survives" if lo > n16 else "falls" if hi <= n16 else "undecided"
            assert v["label"] == want, (c, name)
            labels.append(want)
        cell = ("undecided, no admitted refinement" if not labels else "survives" if set(labels) == {"survives"}
                else "falls" if set(labels) == {"falls"} else "split")
        assert m["cell_verdict"] == cell, c


def test_s7_8_platform_flag_as_read():
    """Clause 10: flag = 3.2e-12 x max(1, cond_F / cond_F(200, 2400)); the
    range of n_- is the count at -band -+ flag."""
    for c in CELLS:
        m = _m32(c)
        for name, b in m["builds"].items():
            assert b["platform_flag"] == 3.2e-12 * max(1.0, b["cond_F"] / m["cond_F_200"]), (c, name)
            lo, hi = b["n_minus_range"]
            assert lo <= b["n_minus"] <= hi, (c, name)


def test_N8_N16_unmoved_by_the_QR_rho():
    """Clause 11: every count at N = 8 and 16 (the delivered rows on all three
    classes, the top-half and resolved-half splits, Q - T_inf, and the
    discriminator builds at N = 16) equals the old route's (3dc0a74). The
    delivered rows' listed eigenvalues move by at most 2.8e-14 (N = 8) and
    2.1e-13 (N = 16); the bands by at most 3.5e-8, through the 160-mode build
    (its eigenvalues move by 3.7e-8 to 4.7e-8), whose old Gram inverse had the
    largest condition of the N = 16 builds. two_adic/ expected 1e-7 at most."""
    J = _cells()["cells"]
    for c in CELLS:
        v = J[c]["vs_old_route"]
        assert v["8"]["counts_equal"] and v["16"]["counts_equal"] and v["modes_N16_S1600"]["counts_equal"], c
        assert v["8"]["undecided_lengths_equal"] and v["16"]["undecided_lengths_equal"], c
    mx = lambda N, k: max(J[c]["vs_old_route"][N][k] for c in CELLS)  # noqa: E731
    assert ("%.1e" % mx("8", "max_eig_change"), "%.1e" % mx("16", "max_eig_change")) == ("2.8e-14", "2.1e-13")
    assert "%.1e" % max(mx("8", "band_change"), mx("16", "band_change")) == "3.5e-08"
    m16 = [J[c]["vs_old_route"]["modes_N16_S1600"]["max_eig_change"] for c in CELLS]
    assert ("%.1e" % min(m16), "%.1e" % max(m16)) == ("3.7e-08", "4.7e-08")
    assert "%.1e" % max(J[c]["vs_old_route"]["mode_response_120_to_160_N16_change"] for c in CELLS) == "3.7e-08"
    assert max(mx("8", "band_change"), mx("16", "band_change")) < 1e-7
    cf = {k: max(u["diag"]["cond_Fz"], u["diag"]["cond_Fb"]) for k, u in _snap()["units"].items() if k.endswith("|16")}
    assert max(cf, key=cf.get) == "160|1600|16" and "%.1e" % cf["160|1600|16"] == "4.4e+05"


def test_N8_platform_calibration():
    """Clause 10: the one cross-platform measurement on the QR route, the
    (80, 1200, 8) unit, laptop against Modal: 7.1e-15 over its six rows."""
    assert "%.1e" % _cells()["meta"]["platform_N8_local_vs_modal"] == "7.1e-15"


# s7.8 outcome: measured values, pinned after the numbers (the rules they are read
# by are the *_as_read tests above).

BUILDS = ("200", "240", "280", "319", "364")


def test_s7_8_falsifier_passes_everywhere():
    """Clause 7: T_S has no eigenvalue below -band_0 on any of the fifteen
    N = 32 builds, nor below the old band(c, 32); its lowest lies between
    +1.09e-3 and +4.41e-3 (the old route: -13.6 to -36.6 at 319 and 364
    modes). So no order-1e-2 failure, and batch 2 is not asked for."""
    lows = []
    for c in CELLS:
        B = _m32(c)["builds"]
        assert set(B) == set(BUILDS), c
        for name, b in B.items():
            assert b["P2_bin"] == b["P2_bin_at_old_band"] == "pass", (c, name)
            lows.append(b["T_S_low"])
    assert ("%.2e" % min(lows), "%.2e" % max(lows)) == ("1.09e-03", "4.41e-03")
    old = [-_n32(c)["builds"][n]["T_S_low"] for c in CELLS for n in ("319", "364")]
    assert ("%.1f" % min(old), "%.1f" % max(old)) == ("13.6", "36.6")


def test_s7_8_determinacy_gate():
    """Clause 4: cond_F is 8.7e5 / 1.1e9 / 1.9e13 / 2.1e13 / 2.1e13 for 200,
    240, 280, 319 and 364 modes (the same on every cell: one unit serves the
    three). None reaches 1e14; 280, 319 and 364 lie beyond A2's last clean
    case, 6.7e11."""
    want = ["8.7e+05", "1.1e+09", "1.9e+13", "2.1e+13", "2.1e+13"]
    for c in CELLS:
        B = _m32(c)["builds"]
        assert ["%.1e" % B[n]["cond_F"] for n in BUILDS] == want, c
        assert not any(B[n]["past_gate"] for n in BUILDS), c
        assert [B[n]["beyond_A2_last_clean"] for n in BUILDS] == [False, False, True, True, True], c
        assert all(v["admitted"] for v in _m32(c)["s7_6_verdict"].values()), c


def test_s7_8_band_history_and_what_sets_it():
    """band(c, 32): 2.97e-2 / 1.41e-2 / 8.18e-3 (the 240-mode response at 2.2,
    the 319-mode response at 2.5, band_0 = the probe at 2.9, where 240 and
    280 move T_S by 2.3e-3 and 4.95e-3). On the old route 3.92e-2 / 2.37e-2 /
    3.16e-2; at the N = 16 proxy 1.59e-2 / 7.55e-3 / 8.18e-3. The probe moved
    by at most 6.4e-8 at c3dca00."""
    J, O = _cells()["cells"], _old_cells()["cells"]
    assert ["%.2e" % J[c]["32"]["band"] for c in CELLS] == ["2.97e-02", "1.41e-02", "8.18e-03"]
    assert ["%.2e" % O[c]["32"]["band"] for c in CELLS] == ["3.92e-02", "2.37e-02", "3.16e-02"]
    assert ["%.2e" % J[c]["band_32_proxy"] for c in CELLS] == ["1.59e-02", "7.55e-03", "8.18e-03"]
    m = _m32("2.9")
    assert m["band"] == m["band_0"] == J["2.9"]["32"]["probe"]
    assert ["%.2e" % m["builds"][n]["dT_vs_200"] for n in ("240", "280")] == ["2.26e-03", "4.95e-03"]
    assert "%.1e" % max(abs(J[c]["32"]["probe"] - O[c]["32"]["probe"]) for c in CELLS) == "6.4e-08"
    # two_adic/'s prediction "the 240-mode row comes within about 1e-2": 2.3e-3, 1.08e-2, 2.97e-2
    r240 = [_m32(c)["builds"]["240"]["dT_vs_200"] for c in CELLS]
    assert ["%.2e" % x for x in r240] == ["2.97e-02", "1.08e-02", "2.26e-03"]


def test_s7_8_referent_and_weyl():
    """Clauses 8 and 9: the delivered row's top-half negatives at the proxy
    band are the old set (2 at 2.2, 14 at 2.5 from -1.83e-2 to -8.0e-3, 12 at
    2.9 from -1.45e-2 to -1.21e-2), within 1e-6 of the old route's. At 2.9 no
    response exceeds any depth; Weyl keeps 20 of the delivered row's
    negatives under the 240-mode response and 10 under the 280-mode one. At
    2.5 the 319-mode response exceeds 12 of the 14 depths, 240's exceeds 2."""
    for c, n, lo, hi in (("2.5", 14, "-1.83e-02", "-8.01e-03"), ("2.9", 12, "-1.45e-02", "-1.21e-02")):
        d = _m32(c)["top_half_depths_200_at_proxy_band"]
        old = _n32(c)["top_half_depths_200_before_merge"]
        assert len(d) == len(old) == n and max(abs(a - b) for a, b in zip(d, old)) < 1e-6, c
        assert ("%.2e" % min(d), "%.2e" % max(d)) == (lo, hi), c
    assert len(_m32("2.2")["top_half_depths_200_at_proxy_band"]) == 2
    B = _m32("2.9")["builds"]
    assert all(B[n]["top_half_depths_exceeded_by_dT"] == 0 for n in BUILDS)
    assert (B["240"]["n_kept_by_weyl"], B["280"]["n_kept_by_weyl"]) == (20, 10)
    B = _m32("2.5")["builds"]
    assert (B["319"]["top_half_depths_exceeded_by_dT"], B["240"]["top_half_depths_exceeded_by_dT"]) == (12, 2)


def test_s7_8_verdicts():
    """Clause 9: 2.9 survives (240: 20, 280: 20, against 10); 2.5 falls (240:
    6, 319: 5, against 9); 2.2 falls (0, 0, against 4). None is
    platform-undecided."""
    want = {"2.2": ("falls", {"240": 0, "364": 0}), "2.5": ("falls", {"240": 6, "319": 5}),
            "2.9": ("survives", {"240": 20, "280": 20})}
    for c, (cell, counts) in want.items():
        m = _m32(c)
        assert m["cell_verdict"] == cell, c
        assert {n: m["builds"][n]["n_minus"] for n in counts} == counts, c
        assert all(v["label"] == cell for v in m["s7_6_verdict"].values()), c
        assert all(b["n_flagged"] == 0 and b["n_minus_range"] == [b["n_minus"]] * 2 for b in m["builds"].values()), c
    assert [_m32(c)["n_minus_N16"] for c in CELLS] == [4, 9, 10]


def test_s7_8_what_2_9_rests_on():
    """At 2.9 the 240-mode row alone (below A2's last clean case) gives the
    same band and the same 20; the last pair counted on the delivered, 240
    and 280-mode builds sits at -1.03e-2 to -1.24e-2 (1.26 to 1.51 times the
    band), the first not counted at -7.7e-3. The 280-mode row's response is
    on the low modes (weight 0.0 on |n| > 16; its N = 8 block carries all of
    it): an S change, as two_adic/'s A4 measured S = 1200 -> 2400 at 200
    modes moving T_S by 5.6e-3 / 6.2e-3 / 8.0e-3."""
    m = _m32("2.9")
    B = m["builds"]
    assert B["240"]["dT_vs_200"] < m["band_0"] and not B["240"]["beyond_A2_last_clean"]
    assert B["240"]["sensitivity_n_minus_at_band_240_only"] == B["240"]["n_minus"] == 20
    last = [x for n in ("200", "240", "280") for x in B[n]["last_two_counted"]]
    assert ("%.2e" % max(last), "%.2e" % min(last)) == ("-1.03e-02", "-1.24e-02")
    assert ("%.2f" % (-max(last) / m["band"]), "%.2f" % (-min(last) / m["band"])) == ("1.26", "1.51")
    assert {"%.1e" % B[n]["first_not_counted"] for n in ("200", "240", "280")} == {"-7.7e-03"}
    assert "%.1f" % B["280"]["dT_top_eigvec_weight_on_n_gt_16"] == "0.0"
    assert abs(B["280"]["dT_vs_200_N8_block"] - B["280"]["dT_vs_200"]) < 1e-5
    assert "%.2e" % B["280"]["dT_vs_200"] == "4.95e-03"
    A4 = json.loads(GLUE._git("show", f"HEAD:{P}/two_adic/ta_rho_check.json"))["A4"]
    assert ["%.1e" % A4["cells"][c]["new_S_response_norm2"] for c in CELLS] == ["5.6e-03", "6.2e-03", "8.0e-03"]
    assert (A4["nvec"], A4["S"], A4["N"]) == (200, 1200.0, 32)


def test_s7_8_what_2_5_rests_on():
    """Sensitivity, not part of the reading: at the 240-mode band (1.08e-2)
    the refined rows count 14 and 12, above 9; 8 and 7 of their eigenvalues
    lie between -1.41e-2 and -1.08e-2. At the proxy band (7.55e-3) the count
    drops from 20 on the delivered row to 14 on each refined build, top half
    from 14 to 6 to 8. The band is set by the 319-mode row (cond_F 2.1e13,
    S/nvec^2 = 0.026); the delivered row counts 8, one eigenvalue 1.8e-5
    from -band. At 2.2 the proxy band counts 1 to 3."""
    import run_checker_ts as RT

    m = _m32("2.5")
    B = m["builds"]
    assert "%.2e" % m["sensitivity_band_240_only"] == "1.08e-02"
    s240 = {n: B[n]["sensitivity_n_minus_at_band_240_only"] for n in ("240", "319")}
    assert s240 == {"240": 14, "319": 12} and all(v > m["n_minus_N16"] for v in s240.values())
    assert [s240[n] - B[n]["n_minus"] for n in ("240", "319")] == [8, 7]
    assert B["200"]["n_minus_at_proxy_band"] == 20 and B["200"]["n_minus_top_half_at_proxy_band"] == 14
    assert all(B[n]["n_minus_at_proxy_band"] == 14 for n in BUILDS[1:])
    assert sorted({B[n]["n_minus_top_half_at_proxy_band"] for n in BUILDS[1:]}) == [6, 7, 8]
    assert "%.2g" % (RT.MODAL_UNITS[2][1] / 319 ** 2) == "0.026"
    assert B["200"]["n_minus"] == 8 and "%.1e" % B["200"]["min_gap_to_band"] == "1.8e-05"
    p22 = [_m32("2.2")["builds"][n]["n_minus_at_proxy_band"] for n in BUILDS]
    assert (min(p22), max(p22)) == (1, 3)


def test_s7_8_platform():
    """Clause 10: flags from 3.2e-12 (200 modes) to 7.7e-5 (319, the scaled
    estimate); the smallest gap to -band is 1.8e-5 (the delivered row at 2.5).
    two_adic/'s laptop build of (200, 2400, 32) on the QR route (A4) against
    the Modal row: the three lowest T_S eigenvalues differ by at most 2.5e-12
    (A3's proxy: 3.2e-12)."""
    flags = [b["platform_flag"] for c in CELLS for b in _m32(c)["builds"].values()]
    gaps = [b["min_gap_to_band"] for c in CELLS for b in _m32(c)["builds"].values()]
    assert ("%.1e" % min(flags), "%.1e" % max(flags)) == ("3.2e-12", "7.7e-05")
    assert "%.1e" % min(gaps) == "1.8e-05"
    A4 = json.loads(GLUE._git("show", f"HEAD:{P}/two_adic/ta_rho_check.json"))["A4"]["cells"]
    J = _cells()["cells"]
    d = max(abs(a - b) for c in CELLS for a, b in zip(A4[c]["new_2400_low3"], J[c]["32"]["T_S_low3"]))
    assert "%.1e" % d == "2.5e-12"


def test_results_s7_8_table_matches_json():
    """Every row of the RESULTS s7.8 table is the JSON value at the printed
    precision."""
    with open(os.path.join(HERE, "RESULTS.md")) as fh:
        text = fh.read()
    sec = text[text.index("Every N = 32 build at band(c, 32), and at the proxy band."):
               text.index("**Outcome, by the reading.**")]
    rows = [[x.strip() for x in r.strip().strip("|").split("|")] for r in sec.splitlines() if r.startswith("| 2.")]
    assert len(rows) == 15
    f = lambda x: "%.4g" % x  # noqa: E731
    for r in rows:
        b = _m32(r[0])["builds"][r[1]]
        assert r[2] == "%.1e" % b["cond_F"] and r[3] == "%.2e" % b["T_S_low"] and r[4] == b["P2_bin"]
        assert r[5] == "%.2e" % b["dT_vs_200"]
        assert r[6] == f"{b['n_minus']} / {b['n_minus_top_half']}"
        assert r[7] == f"{b['n_minus_at_proxy_band']} / {b['n_minus_top_half_at_proxy_band']}"
        assert r[8] == (", ".join(f(v) for v in b["last_two_counted"]) or "none")


def test_first_five_lines_quoted_numbers():
    """RESULTS lines 1 to 5 as rewritten after s7.8."""
    J = _cells()["cells"]
    b816 = [J[c][N]["band"] for c in CELLS for N in ("8", "16")]
    assert ("%.1e" % min(b816), "%.1e" % max(b816)) == ("5.3e-03", "1.6e-02")
    assert ["%.1e" % J[c]["32"]["band"] for c in CELLS] == ["3.0e-02", "1.4e-02", "8.2e-03"]
    ts = [J[c][N]["T_S_low3"][0] for c in CELLS for N in ("8", "16", "32")]
    assert ("%.1e" % min(ts), "%.1e" % max(ts)) == ("1.5e-03", "3.5e-03")
    B = _m32("2.9")["builds"]
    assert [B[n]["n_minus"] for n in BUILDS] == [20, 20, 20, 20, 21]
    assert "%.2e" % max(B[n]["dT_vs_200"] for n in BUILDS) == "4.95e-03"
    assert "%.1e" % _m32("2.5")["sensitivity_band_240_only"] == "1.1e-02"
    assert [J["2.9"][N]["full"]["n_minus"] for N in ("8", "16", "32")] == [4, 10, 20]
