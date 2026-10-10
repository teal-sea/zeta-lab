"""modal/ follow-up 2: pins the provenance of every out_rho/ output and the calibration.

Pins no mathematical conclusion: grading belongs to checker/, which commits
its criterion reading before any eigenvalue of these rows is seen. What is
pinned:

- each of the eleven checker/ units has an out_rho/<unit>.json computed from
  the tree at e2b46a5, whose T_S input digest is b2e7787b (the QR rho), with
  the guard passing in the container before and, for a finished unit, after
  the build; a unit that did not finish says so in its status;
- the rows are in checker_ts_snapshot.json's shape, with dps (40, 60) at
  N = 8 as run_checker_ts.snapshot builds them, and diag carries cond_Fz and
  cond_Fb;
- the calibration unit (80, 1200, 8) matches the local build of the same
  unit (out_rho/local_checker_80_1200_8.json) to 1e-10 max abs, the
  threshold the brief fixed before the run, and every output carries those
  measured differences (meta.calibration);
- no output carries an eigenvalue of T_S or R_S.

modal/out/ and test_modal_outputs.py (the old route, digest 1dcab230) are not
read here. run_modal_rho.py is not imported (it needs the Modal client and the
tree tarball); its constants are read from its source text.
"""

from __future__ import annotations

import json
import math
import os
import re
import subprocess
import sys

import pytest

HERE = os.path.dirname(os.path.abspath(__file__))
C4 = os.path.normpath(os.path.join(HERE, ".."))
OUT = os.path.join(HERE, "out_rho")
SRC = open(os.path.join(HERE, "run_modal_rho.py"), encoding="utf-8").read()

TREE_COMMIT = "e2b46a5a82f365469a814f80c94b5232cf8bee46"
LOCAL_DIGEST = "b2e7787bce7a77db4a1a81b9311fc75a2b9326649b88a49883bd4d737ca70eaa"
OLD_DIGEST = "1dcab23022a36c1b75c1f23379c1549bf7be9d4be7f526a5257bb3004577fb9a"
CAL_TOL = 1e-10  # BRIEF.md follow-up 2, fixed before the run
CELLS = ("2.2", "2.5", "2.9")

# (nvec, S as passed, N): the seven of run_checker_ts.UNITS and the four N = 32
# units of the first follow-up (S of the default rule as the same floats)
SEVEN = [(80, 1200, 8), (120, 1600, 16), (200, 2400, 32), (80, 1600, 16), (120, 1200, 16), (80, 1200, 16),
         (160, 1600, 16)]
FOUR = [(240, 2400, 32), (280, 2266.1020257693895, 32), (319, 2633.163333456407, 32),
        (364, 3060.0807085398565, 32)]
ELEVEN = SEVEN + FOUR
NAMES = [f"checker_{nv}_{int(S)}_{N}" for nv, S, N in ELEVEN]
CAL = "checker_80_1200_8"
FINISHED = ("ok",)
NOT_FINISHED = ("timed_out", "restarted", "failed", "modal_error")
DIAG = {"gram_z_offI", "cond_Gb", "cond_Fz", "cond_Fb"}


def _git(*args):
    top = subprocess.run(["git", "rev-parse", "--show-toplevel"], cwd=HERE, capture_output=True,
                         text=True, check=True).stdout.strip()
    return subprocess.run(["git", *args], cwd=top, capture_output=True, text=True, check=True).stdout


def _load(name):
    with open(os.path.join(OUT, f"{name}.json")) as fh:
        return json.load(fh)


def _max_abs(a, b):
    return max(abs(float(x) - float(y)) for ra, rb in zip(a, b) for x, y in zip(ra, rb))


def test_constants_match_run_modal_rho():
    assert f'TREE_COMMIT = "{TREE_COMMIT}"' in SRC
    assert f'LOCAL_DIGEST = "{LOCAL_DIGEST}"' in SRC
    assert 'VOL_NAME = "c4s2-modal-rho-out"' in SRC  # not the old Volume: its markers share five names
    assert 'OUT = os.path.join(HERE, "out_rho")' in SRC


def test_local_digest_is_the_tree_at_e2b46a5():
    """The digest of the tree the units ran on, not of today's HEAD, and it is
    not the old route's."""
    sys.path.insert(0, os.path.join(C4, "checker"))
    import checker_glue as G

    assert G.ts_closure(TREE_COMMIT)[0] == LOCAL_DIGEST != OLD_DIGEST


def test_the_eleven_are_checker_s_units():
    """The seven are run_checker_ts.UNITS at the tree; the default-rule S are
    two_adic/ta_ts.py lines 146 and 147 at the tree."""
    src = _git("show", f"{TREE_COMMIT}:hunts/weil_propagation/c4_s2/checker/run_checker_ts.py")
    block = src.split("UNITS = [", 1)[1].split("\n]", 1)[0]
    listed = [tuple(int(x) for x in m) for m in re.findall(r"\((\d+), (\d+), (\d+), \"", block)]
    assert listed == SEVEN
    lines = _git("show", f"{TREE_COMMIT}:hunts/weil_propagation/c4_s2/two_adic/ta_ts.py").splitlines()
    assert lines[145].strip() == "nvec = self.nvec or max(80, int(8 * N / L) + 40)"
    assert lines[146].strip() == "S = self.S or max(1200.0, 12.0 * 2 * math.pi * N / L)"
    for c, (nv, S, N) in zip((None, 2.9, 2.5, 2.2), FOUR):
        if c is None:
            continue
        L = math.log(c)
        assert (nv, S) == (max(80, int(8 * 32 / L) + 40), max(1200.0, 12.0 * 2 * math.pi * 32 / L))


@pytest.mark.parametrize("unit", ELEVEN, ids=NAMES)
def test_every_unit_is_recorded_with_its_provenance(unit):
    nv, S, N = unit
    name = f"checker_{nv}_{int(S)}_{N}"
    m = _load(name)["meta"]
    assert m["unit"] == name
    assert (m["args"]["nvec"], m["args"]["S"], m["args"]["N"]) == (nv, S, N)
    assert m["tree_commit"] == TREE_COMMIT
    assert m["ts_inputs_digest_local"] == LOCAL_DIGEST
    assert m["status"] in FINISHED + NOT_FINISHED
    if m["status"] in ("restarted", "modal_error"):
        return  # no guard ran in this attempt; the status says so
    g = m["guard_before"]
    assert g["ok"] and g["head"] == TREE_COMMIT and g["ts_inputs_digest"] == LOCAL_DIGEST
    assert g["dirty"] == [] and g["porcelain"] == []
    assert m["ts_inputs_digest"] == LOCAL_DIGEST
    if m["status"] == "ok":
        ga = m["guard_after"]
        assert ga["ok"] and ga["ts_inputs_digest"] == LOCAL_DIGEST and ga["porcelain"] == []
        for k in ("wall_seconds", "cpu_seconds", "peak_rss_mib"):
            assert m[k] > 0
        assert m["versions"] == {"numpy": "2.5.1", "scipy": "1.18.0", "mpmath": "1.3.0",
                                 "python-flint": "0.9.0", "sympy": "1.14.0"}
        assert m["blas_core"] in {"Sandybridge", "Haswell", "SkylakeX", "Zen", "Cooperlake", "SapphireRapids"}


@pytest.mark.parametrize("unit", ELEVEN, ids=NAMES)
def test_finished_units_have_the_snapshot_shape(unit):
    nv, S, N = unit
    d = _load(f"checker_{nv}_{int(S)}_{N}")
    if d["meta"]["status"] != "ok":
        pytest.skip(d["meta"]["status"])
    dps = (40, 60) if N == 8 else (40,)
    assert d["meta"]["dps"] == list(dps)
    assert set(d["T_S"]) == {f"{c}|{N}|{p}|{nv}|{int(S)}" for c in CELLS for p in dps}
    n = 2 * N + 1
    for rows in d["T_S"].values():
        assert len(rows) == n and all(len(r) == n and all(math.isfinite(x) for x in r) for r in rows)
    (key, u), = d["units"].items()
    assert key == f"{nv}|{int(S)}|{N}"
    assert set(u) >= {"role", "seconds", "kmax", "diag", "S_exact"} and u["S_exact"] == S
    assert set(u["diag"]) >= DIAG


def test_calibration_matches_the_local_build():
    loc, mod = _load(f"local_{CAL}"), _load(CAL)
    assert loc["meta"]["ts_inputs_digest"] == LOCAL_DIGEST and loc["meta"]["head"] == TREE_COMMIT
    assert mod["meta"]["status"] == "ok"
    assert set(loc["T_S"]) == set(mod["T_S"]) and len(loc["T_S"]) == 6
    for k in loc["T_S"]:
        assert _max_abs(loc["T_S"][k], mod["T_S"][k]) <= CAL_TOL, k


@pytest.mark.parametrize("name", NAMES)
def test_every_output_carries_the_measured_calibration(name):
    d = _load(name)
    if d["meta"]["status"] != "ok":
        pytest.skip(d["meta"]["status"])
    rec = d["meta"]["calibration"]
    loc, mod = _load(f"local_{CAL}"), _load(CAL)
    assert rec["unit"] == CAL and rec["threshold"] == CAL_TOL and rec["passed"] is True
    for k in loc["T_S"]:
        assert math.isclose(rec["max_abs_diff"][k], _max_abs(loc["T_S"][k], mod["T_S"][k]), rel_tol=1e-9,
                            abs_tol=1e-300)
    assert rec["max"] == max(rec["max_abs_diff"].values()) <= CAL_TOL


def _keys(obj):
    if isinstance(obj, dict):
        for k, v in obj.items():
            yield k
            yield from _keys(v)
    elif isinstance(obj, list):
        for v in obj:
            yield from _keys(v)


@pytest.mark.parametrize("name", NAMES + [f"local_{CAL}"])
def test_no_output_carries_an_eigenvalue(name):
    """checker/ commits its criterion reading before any eigenvalue is seen."""
    bad = [k for k in _keys(_load(name)) if re.search(r"eig|low3|T_S_low|n_minus|spectral", str(k))]
    assert not bad, bad
