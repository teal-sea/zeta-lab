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
    """The committed snapshot was built at 8dc8525. Its key is the closure
    digest there, and HEAD's closure digest equals it (re-keyed 2026-09-24
    from the folder rule after proving this). A two_adic/ or kernel/ commit
    that changes a closure file turns this red rather than letting the
    snapshot's tests skip: rebuild with run_checker_ts.py."""
    with open(GLUE.TS_SNAPSHOT) as fh:
        meta = json.load(fh)["meta"]
    assert meta["head_at_start"].startswith("8dc8525")
    assert meta["rekey"]["built_commit"] == meta["head_at_start"]
    built = GLUE.ts_closure("8dc8525")
    head = GLUE.ts_closure("HEAD")
    assert built[0] == head[0] == meta["ts_inputs_digest"]
    assert built[1] == head[1] == meta["rekey"]["inputs"]


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
    assert m["python"].startswith("/Users/thomas/zeta-lab/.venv/")
    assert set(m["units"]) == {"80|1200|8", "120|1600|16", "200|2400|32", "80|1600|16",
                               "120|1200|16", "80|1200|16", "160|1600|16",
                               # merged from modal/out on 2026-09-24 (s7.7)
                               "240|2400|32", "280|2266|32", "319|2633|32", "364|3060|32"}


def test_band_per_row_is_the_largest_measured_response():
    """P1 exactly; band(c, N) = max(two_adic/'s probe for the row, the row's
    refinement response, the quadrature response at N = 16). At N = 32 the
    refinement is (240, 2400), run on Modal and merged 2026-09-24 (s7.7); it
    replaces the N = 16 proxy of 535882e, whose band is kept as a record."""
    J = _cells()["cells"]
    for c in CELLS:
        r = J[c]
        for N in ("8", "16", "32"):
            x = r[N]
            assert x["T_S_herm_defect"] == 0, (c, N)
            assert x["band"] == max(x["probe"], x["refinement_response"], r["quadrature_response_N16"]), (c, N)
        assert r["32"]["refinement_proxy"] is None
        assert r["32"]["refinement_response"] == r["refinement_response"]["32"]
        assert r["band_32_before_merge"] == max(r["32"]["probe"], r["16"]["refinement_response"],
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
    apply to them. Until 535882e (band_cell from the N = 16 proxy) the counts
    were 1, 4, 3 / 4, 8, 20 / 4, 9, 20: a failure of banded P4 at 2.2. With
    the N = 32 band measured (s7.7), band_cell is 3.9e-2 / 2.4e-2 / 3.2e-2
    and the counts are 0, 0, 0 / 1, 2, 2 / 2, 2, 2: nondecreasing, and
    bounded, at that threshold."""
    J = _cells()["cells"]
    want = {"2.2": [0, 0, 0], "2.5": [1, 2, 2], "2.9": [2, 2, 2]}
    for c in CELLS:
        assert [J[c][N]["full"]["n_minus_at_band_cell"] for N in ("8", "16", "32")] == want[c], c


def test_T_S_removes_the_deep_product_side_negatives():
    """Q - T_inf (product side): lambda_min -0.30 to -0.49, negative count
    below -band growing in N. R_S = Q - T_S: lambda_min above -0.13 on every
    row. Until 535882e the count was not smaller in general (c = 2.5,
    N = 32: 20 for R_S against 18 for Q - T_inf at the proxy band); at the
    measured N = 32 band it is 2 against 17 (s7.7)."""
    J = _cells()["cells"]
    for c in CELLS:
        ninf = [J[c][N]["R_inf_full"]["n_minus"] for N in ("8", "16", "32")]
        assert ninf[0] < ninf[1] < ninf[2], (c, ninf)
        for N in ("8", "16", "32"):
            assert J[c][N]["R_inf_full"]["low3"][0] < -0.29, (c, N)
            assert J[c][N]["full"]["low3"][0] > -0.13, (c, N)
    assert J["2.5"]["32"]["full"]["n_minus"] == 2 and J["2.5"]["32"]["R_inf_full"]["n_minus"] == 17


def test_R_S_negative_count_below_band():
    """n_-(R_S) below -band(c, N), full space: 4, 4, 0 at 2.2; 4, 9, 2 at
    2.5; 4, 10, 2 at 2.9 (N = 8, 16, 32). At N = 32 the band is now the
    measured (240, 2400) refinement response (s7.7); at the N = 16 proxy
    band of 535882e the N = 32 counts were 3, 20, 20."""
    J = _cells()["cells"]
    want = {"2.2": [4, 4, 0], "2.5": [4, 9, 2], "2.9": [4, 10, 2]}
    for c in CELLS:
        assert [J[c][N]["full"]["n_minus"] for N in ("8", "16", "32")] == want[c], c


def test_two_deep_negatives_at_2_9_on_every_class():
    """c = 2.9: the two lowest eigenvalues of R_S are below -3.7e-2 on every
    class and every N. Against the largest band of the cell, now the
    measured N = 32 band 3.16e-2 (it was 8.2e-3, and 4.5 times, at the proxy
    band): the second sits 1.2 to 1.4 times below it, the first 2.1 to 3.8
    times."""
    J = _cells()["cells"]["2.9"]
    bc = J["band_cell"]
    r1, r2 = [], []
    for N in ("8", "16", "32"):
        for cls in ("full", "minus", "minus_zero"):
            lo = J[N][cls]["low3"]
            assert lo[1] < -0.037 and lo[1] < -bc, (N, cls)
            r1.append(-lo[0] / bc)
            r2.append(-lo[1] / bc)
    assert ("%.1f" % min(r2), "%.1f" % max(r2)) == ("1.2", "1.4")
    assert ("%.1f" % min(r1), "%.1f" % max(r1)) == ("2.1", "3.8")


def test_top_half_split_of_the_negatives():
    """RESULTS s7.3: negatives of R_S (full) with more than half their weight
    on |n| > N/2, and the rest."""
    J = _cells()["cells"]
    top = {"2.5": [2, 4, 0], "2.9": [2, 5, 0]}  # N = 32: 14 and 12 at the proxy band (535882e)
    rest = {"2.5": [2, 5, 2], "2.9": [2, 5, 2]}
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
    want = {"2.2": [2, 1, 0], "2.5": [2, 4, 2], "2.9": [2, 4, 2]}  # N = 32: 1, 6, 8 at the proxy band
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
    wb = {"2.2": [2, 2, 0], "2.5": [2, 5, 2], "2.9": [2, 5, 2]}  # N = 32 at the measured band (s7.7)
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
    and N = 32 row and at 2.2 for N = 16; the Gram probe sets it at 2.5 and
    2.9 for N = 16. (At N = 32 the probe set it at 2.5 and 2.9 while the
    N = 16 proxy stood in for the refinement, 535882e.)"""
    J = _cells()["cells"]
    for c in CELLS:
        for N in ("8", "16", "32"):
            x = J[c][N]
            by_ref = N in ("8", "32") or c == "2.2"
            assert x["band"] == (x["refinement_response"] if by_ref else x["probe"]), (c, N)


# ------------------------------------ s7.7: the Modal N = 32 rows (2026-09-24)
#
# Written after the s7.6 criterion's reading was committed (ee4a1ff) and after
# the rows were analysed: these pin measured values, they do not test a
# prediction. The merge tests read modal/out (read only) and the snapshot.

MODAL_FILES = {"240|2400|32": "checker_240_2400_32.json", "280|2266|32": "checker_280_2266_32.json",
               "319|2633|32": "checker_319_2633_32.json", "364|3060|32": "checker_364_3060_32.json"}


def _snap():
    if not os.path.exists(GLUE.TS_SNAPSHOT):
        pytest.skip("checker_ts_snapshot.json absent")
    with open(GLUE.TS_SNAPSHOT) as fh:
        return json.load(fh)


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

    S = _snap()
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
    S = _snap()
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
    J = _cells()["cells"][c]
    if "modes_N32" not in J:
        pytest.skip("checker_ts_cells.json predates the Modal merge")
    return J["modes_N32"]


def test_N32_band_replaces_the_proxy():
    """band(c, 32) is now the (240, 2400) refinement response: 3.92e-2 /
    2.37e-2 / 3.16e-2, against the proxy band 1.59e-2 / 7.55e-3 / 8.18e-3
    (2.5 to 3.9 times it). The refinement response is 2.5 to 8.6 times the
    N = 16 response it replaces."""
    J = _cells()["cells"]
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
    J = _cells()["cells"]
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
    S = _snap()
    sec = [S["units"][k]["seconds"] for k in MODAL_FILES]
    assert ("%.0f" % min(sec), "%.0f" % max(sec)) == ("844", "1784")
    _, d240 = _modal(RT.MODAL_UNITS[0][2])
    wall = d240["meta"]["wall_seconds"]
    assert "%.0f" % wall == "890"
    assert "%.3f" % (wall * (4 * 0.0000131 + 16 * 0.00000222)) == "0.078"
