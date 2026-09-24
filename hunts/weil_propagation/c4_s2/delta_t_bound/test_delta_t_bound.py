"""delta_t_bound/ tests: the routed recount (assembler/assemble.py --routed on
the bound files as committed at 843544a and 3be0dce) and the numbers of
RESULTS.md that are not pinned in assembler/ (the floor: test_floor_count.py;
the crossover: test_crossover.py; PREREG s6: test_assembler.py).
"""

from __future__ import annotations

import functools
import hashlib
import json
import os
import sys

import numpy as np
import pytest

HERE = os.path.dirname(os.path.abspath(__file__))
ASSEMBLER = os.path.join(os.path.dirname(HERE), "assembler")
if ASSEMBLER not in sys.path:
    sys.path.insert(0, ASSEMBLER)

import assemble as AS  # noqa: E402
import floor_count as FC  # noqa: E402
from flint import fmpq  # noqa: E402

TRUNC_COMMIT, QUAD_COMMIT = "843544a", "3be0dce"  # the routed commits (RESULTS s0)
BOUND_TRUNC_RESULTS = os.path.join(AS.C4S2, "bound_trunc", "RESULTS.md")


@functools.lru_cache(maxsize=None)
def _routed():
    with open(AS.ROUTED_JSON) as fh:
        return json.load(fh)


@functools.lru_cache(maxsize=None)
def _quad_blob():
    return json.loads(AS.git_blob(QUAD_COMMIT, AS.QUAD_JSON))


@functools.lru_cache(maxsize=None)
def _trunc_blob():
    return json.loads(AS.git_blob(TRUNC_COMMIT, AS.TRUNC_JSON))


@functools.lru_cache(maxsize=None)
def _floor():
    with open(FC.OUT) as fh:
        return json.load(fh)


def _results():
    with open(os.path.join(HERE, "RESULTS.md")) as fh:
        return fh.read()


def _q(pair):
    return fmpq(int(pair[0]), int(pair[1]))


def _intkeys(d):
    return {int(k): v for k, v in d.items()}


# ------------------------------------------------------------ structure


def test_routed_covers_every_build_on_the_committed_blobs():
    r = _routed()
    assert sorted(r["builds"]) == sorted(AS.build_key(c, nv, S, N) for c in AS.CELLS for nv, S, N in AS.BUILDS)
    m = r["meta"]
    assert m["ts_inputs_digest"] == AS.DIGEST
    assert (m["trunc_commit"], m["quad_commit"]) == (TRUNC_COMMIT, QUAD_COMMIT)
    assert m["trunc_json_sha256"] == hashlib.sha256(AS.git_blob(TRUNC_COMMIT, AS.TRUNC_JSON)).hexdigest()
    assert m["quad_json_sha256"] == hashlib.sha256(AS.git_blob(QUAD_COMMIT, AS.QUAD_JSON)).hexdigest()


def test_bound_records_are_the_committed_entries():
    r = _routed()
    t, q = AS.load_bound(AS.TRUNC_JSON, TRUNC_COMMIT), AS.load_bound(AS.QUAD_JSON, QUAD_COMMIT)
    assert len(t) == len(q) == 33
    for key, b in r["builds"].items():
        c, nv, S, N = key.split("|")
        for name, table in (("trunc", t), ("quad", q)):
            e = AS.bound_for(table, c, int(nv), int(S), int(N))
            assert "missing" not in e, (name, key)  # every build has its entry, at kmax_for(nvec)
            assert b[name]["eps_upper"] == e["eps_upper"] and b[name]["grade"] == e["grade"]


def test_every_eps_is_null_and_why():
    """RESULTS line 1, s1: null in both folders on all 33 builds, so no eps and
    no count; the reasons name the Sonin overlap and E2."""
    for key, b in _routed()["builds"].items():
        assert b["trunc"]["eps_upper"] is None and b["quad"]["eps_upper"] is None
        assert b["eps"] is None and b["count"] is None
        assert "Sonin overlap" in b["trunc"]["why_null"] and "Sonin overlap" in b["trunc"]["blocking_step"]
        assert "G_S^{-1} G_exact" in b["quad"]["why_null"] and "E2" in b["quad"]["grade"]


def test_outcome_4_everywhere():
    r = _routed()
    again = AS.routed_decisions(r)
    for c in AS.CELLS:
        for sp in ("full", "V4"):
            d = r["decisions"][f"{c}|{sp}"]
            assert d["decision"]["outcome"] == 4 == again[f"{c}|{sp}"]["decision"]["outcome"]
            assert _intkeys(d["agg"]["has_bound"]) == {8: False, 16: False, 32: False}
            assert d["agg"]["consistent"]
    assert r["eps_grow_2.9_full"] is None


@pytest.mark.parametrize("c", AS.CELLS)
def test_fixed_terms_recomputed_on_the_N8_build(c):
    fx = AS.fixed_terms(c, 80, 1200, 8)
    rec = _routed()["builds"][AS.build_key(c, 80, 1200, 8)]["fixed"]
    assert {k: AS.q_pair(v) for k, v in fx.items()} == {k: v["q"] for k, v in rec.items()}


def test_fixed_terms_at_29():
    tot = [b["fixed"]["total"]["float"] for k, b in _routed()["builds"].items() if k.startswith("2.9|")]
    assert ("%.1e" % min(tot), "%.1e" % max(tot)) == ("1.2e-15", "4.2e-15")


# --------------------------------------------- the two folders' figures


def test_quad_blob_figures():
    """bound_quad/ at 3be0dce, c = 2.9: E1 3.7e-3 at N = 8, 9.2e-3 to 1.46e-2 at
    N = 32; the E2 obstruction at least 9.2e9 on every N = 32 build."""
    rows = [e for e in _quad_blob() if e["c"] == "2.9"]
    e1_8 = [float(e["parts_upper"]["E1"]) for e in rows if e["N"] == 8]
    e1_32 = [float(e["parts_upper"]["E1"]) for e in rows if e["N"] == 32]
    x32 = [float(e["e2_obstruction_lower"]) for e in rows if e["N"] == 32]
    assert ["%.1e" % x for x in e1_8] == ["3.7e-03"]
    assert ("%.1e" % min(e1_32), "%.2e" % max(e1_32)) == ("9.2e-03", "1.46e-02")
    assert len(x32) == 5 and "%.1e" % min(x32) == "9.2e+09"
    assert all(e["eps_upper"] is None and e["parts_upper"]["E2"] is None for e in _quad_blob())


def test_trunc_figures_quoted():
    """bound_trunc/'s RESULTS at 843544a, quoted in s5: Proposition 4's sizes and
    the 4.950e-3 floor on a pair of bounds."""
    text = AS.git_blob(TRUNC_COMMIT, BOUND_TRUNC_RESULTS).decode()
    line3 = text.splitlines()[2]
    for s in ("0.2125 / 0.1603 / 0.1313 / 0.1131 / 0.0975", "4.950e−3", "would cost even if it closed"):
        assert s in line3, s
    assert all(e["eps_upper"] is None for e in _trunc_blob())


# ------------------------------------------------------ the floor, measured


@pytest.mark.slow
def test_floor_mechanism():
    """RESULTS s3 (measured, float64, c = 2.9, N = 16): the negative directions of
    Q - kappa T_inf carry Q's Rayleigh quotients 4.2e-5, 4.4e-6 (Q's lowest
    eigenvalues 2.1e-7, 3.9e-5) and weights 0.44, 0.93 in the complement of V_4
    (3/33 for a generic direction)."""
    c, N = "2.9", 16
    n = 2 * N + 1
    Q = AS.CQ.Q_matrix(c, N, 40)
    T = FC.t_inf_direct(c, N)
    Qf = np.array([[float(Q[i, j]) for j in range(n)] for i in range(n)])
    Tf = np.array([[float(T[i, j]) for j in range(n)] for i in range(n)])
    w, V = np.linalg.eigh(Qf - float(FC.KAPPA_LO) * Tf)
    h, nh, e0 = AS.class_constraints_c(AS.C_EXACT[c], N, 64)
    C, _ = np.linalg.qr(np.array([[float(x.mid()) for x in r] for r in (h, nh, e0)]).T)
    k = int((w < 0).sum())
    assert k == 2
    ray = ["%.1e" % float(V[:, i] @ Qf @ V[:, i]) for i in range(k)]
    wt = ["%.2f" % float(np.linalg.norm(C.T @ V[:, i]) ** 2) for i in range(k)]
    assert ray == ["4.2e-05", "4.4e-06"] and wt == ["0.44", "0.93"]
    assert ["%.1e" % x for x in np.linalg.eigvalsh(Qf)[:2]] == ["2.1e-07", "3.9e-05"]
    assert "%.2f" % (3 / n) == "0.09"


def test_floor_numbers_quoted():
    f = _floor()["cells"]
    negs = [(b["lo_float"] + b["hi_float"]) / 2 for b in f["2.9|32"]["negatives_kappa_lo"]]
    assert ["%.1e" % x for x in negs] == ["-1.0e-04", "-1.7e-05"]
    assert "%.1e" % max(r["eta_float"] for r in f.values()) == "2.2e-26"
    assert "%.0f" % f["2.9|32"]["seconds"] == "544"


# -------------------------------------------------------- RESULTS.md


def test_first_five_lines_quote_the_pinned_numbers():
    head = "\n".join(_results().splitlines()[:5])
    for s in ("null on all 33 builds", "‖X‖ ≥ 9.2e9", "3.7e−3", "**9.2e−3 to 1.46e−2**",
              "**1.2e−15 to 4.2e−15**", "4, 10, 20", "≥ 2, 2, 2 at c = 2.9", "≥ 1, 1, 1 at 2.5",
              "≥ 0 on C4's class V_4 at every cell", "−1.0e−4 and −1.7e−5", "91ce087",
              "81f0b47", "e174d19", "**1.50e−2**", "1.52e−2", "**1.18e−2**", "0.0975 to 0.2125",
              "**unresolved, paused by the box and by allocation**", "843544a", "3be0dce"):
        assert s in head, s
    for i, start in enumerate(("1. ", "2. ", "3. ", "4. ", "5. ")):
        assert _results().splitlines()[i].startswith(start)
