"""exact_gram/: pins for MISSION, PREREG, RUNS and the guard.

Fast except the stored-row context of PREREG s2.4 (slow: it forms Q at
dps 40 through assembler/).
"""

from __future__ import annotations

import json
import os
import sys

import pytest

HERE = os.path.dirname(os.path.abspath(__file__))
C4S2 = os.path.normpath(os.path.join(HERE, ".."))
REPO = os.path.normpath(os.path.join(C4S2, "..", "..", ".."))
for p in (HERE, os.path.join(C4S2, "checker"), os.path.join(C4S2, "two_adic"), os.path.join(C4S2, "bound_quad"),
          os.path.join(REPO, "tests")):
    if p not in sys.path:
        sys.path.insert(0, p)

import guard as GD  # noqa: E402

PRICE = os.path.join(HERE, "price_block.json")


def _read(name):
    with open(os.path.join(HERE, name), encoding="utf-8") as fh:
        return fh.read()


# --- MISSION ---------------------------------------------------------------


def test_mission_huntspec_validates():
    import test_huntspec as HS

    blocks = HS._blocks_in(_read("MISSION.md"))
    assert len(blocks) == 1
    assert HS.validate_huntspec(HS.parse_huntspec(blocks[0])) == ()


def test_runs_manifests_validate():
    import test_huntspec as HS

    import re

    blocks = re.findall(r"```runmanifest\n(.*?)```", _read("RUNS.md"), re.DOTALL)
    assert blocks
    for b in blocks:
        assert HS.validate_runmanifest(HS.parse_huntspec(b)) == ()


# --- PREREG s1: E1 at the registered S' and at the stored S ------------------


def test_e1_at_registered_and_stored_S():
    import eps_quad as E

    wide = E.kappa(2.9, 32, 1.0e4) * 280
    stored = E.kappa(2.9, 32, 2266.1020257693895) * 280
    assert float(wide.upper()) < 6.98e-4 and float(wide.lower()) > 6.96e-4  # PREREG s1: 6.97e-4
    assert float(stored.lower()) > 1.18e-2  # the stored S cannot carry the scale on E1 alone
    assert abs(float(stored.mid()) - 1.4546e-2) < 1e-6


def test_prereg_quotes_the_record():
    t = _read("PREREG.md")
    for s in ("1.18e−2", "6.97e−4", "1.455e−2", "b2e7787b", "S' = 10^4", "G ≥ 2"):
        assert s in t, s


@pytest.mark.slow
def test_stored_row_context_s2_4():
    import numpy as np

    sys.path.insert(0, os.path.join(C4S2, "assembler"))
    import assemble as A

    R = A.stored_R("2.9", 280, 2266, 32)
    R = (R + R.T) / 2
    n = R.shape[0]
    ev = np.sort(np.linalg.eigvalsh(R))
    one = np.ones((n, 1)) / np.sqrt(n)
    Qm, _ = np.linalg.qr(np.hstack([one, np.random.default_rng(0).standard_normal((n, n - 1))]))
    evH = np.sort(np.linalg.eigvalsh(Qm[:, 1:].T @ R @ Qm[:, 1:]))
    assert abs(ev[19] + 1.0285e-2) < 1e-6
    assert abs(evH[19] + 9.7248e-3) < 1e-6 and abs(evH[18] + 1.0527e-2) < 1e-6


# --- PREREG s5: the gate, extended to DH --------------------------------------


def _dh_coeffs(n_max):
    import sympy

    r5 = sympy.sqrt(5)
    kappa = (sympy.sqrt(10 - 2 * r5) - 2) / (r5 - 1)
    per = {1: sympy.Integer(1), 2: kappa, 3: -kappa, 4: sympy.Integer(-1), 0: sympy.Integer(0)}
    return {n: per[n % 5] for n in range(1, n_max + 1)}, kappa


def test_gate_refuses_dh_at_the_first_composite():
    import sympy
    import checker_gate as CG

    a, kappa = _dh_coeffs(12)
    lam = CG.lambda_vectors(a, 12)
    x = sympy.Symbol("x")
    # Lambda_DH(6) = (1 + kappa^2)(log 2 + log 3): nonzero, decided by the minimal polynomial
    for p in (2, 3):
        assert sympy.minimal_polynomial(lam[6][p], x) != x
        assert sympy.simplify(lam[6][p] - (1 + kappa**2)) == 0
    for n in (4, 5):  # prime powers: no composite atom before 6
        assert set(lam[n]) <= {2, 5}
    ev = CG.gate_events(lam, 1, 12)
    first = next(e for e in ev if e["kind"] == "composite_atom")
    assert first["n"] == 6


def test_dh_two_adic_data_refused():
    import ta_data as D

    a, kappa = _dh_coeffs(16)
    import checker_gate as CG

    lam = CG.lambda_vectors(a, 16)
    tower = {k: lam[2**k][2] for k in (1, 2, 3, 4)}
    assert tower[1] == kappa
    with pytest.raises(D.NonUnitaryLocalData):
        D.validate(("tower", tower), degree=1)


def test_gate_still_refuses_epstein_and_W_a():
    import checker_gate as CG

    g = CG.run_gate()  # n_max 200 (towers() reads its own default n_max)
    ep = g["epstein_(1,1,6)"]
    assert ep["first_composite_atom"] == 6 and ep["first_tower_violation"] == 8
    assert g["W_a(a=1/4)"]["first_rejection_n"] == 2
    assert g["zeta"]["first_rejection_n"] is None and g["dedekind_Q(sqrt-23)"]["first_rejection_n"] is None


# --- PREREG s6: the guard fails closed ----------------------------------------


def test_the_rebuild_closure_is_what_it_imports():
    """rebuild.py is committed (2026-10-26): its HEAD closure holds the modules it runs, and
    key() either keys a clean tree or refuses a dirty one; it never keys a dirty one."""
    digest, paths, names = GD.head_closure()  # no skip: a skip here once hid a path bug
    for f in ("exact_gram/rebuild.py", "exact_gram/bounds.py", "exact_gram/guard.py", "two_adic/ta_data.py"):
        assert f"{GD.C4S2}/{f}" in paths, f
    try:
        k = GD.key()
        assert k["rebuild_digest"] == digest
    except GD.GuardRefused as e:
        assert "dirty" in str(e)


def test_key_refuses_an_absent_root():
    with pytest.raises(GD.GuardRefused, match="absent"):
        GD.head_closure(root=f"{GD.C4S2}/exact_gram/no_such_module.py")


def _fake_tree():
    root = f"{GD.C4S2}/exact_gram/rebuild.py"
    files = {root: b"import ta_mellin\nimport guard\n", f"{GD.C4S2}/two_adic/ta_mellin.py": b"import numpy\n",
             f"{GD.C4S2}/exact_gram/guard.py": b"import json\n", f"{GD.C4S2}/two_adic/ta_es.py": b"import math\n"}
    return root, files


def test_closure_digest_moves_with_a_closure_blob_only():
    root, files = _fake_tree()
    blobs = {p: f"b{i}" for i, p in enumerate(sorted(files))}
    d0, paths, names = GD.closure(blobs, files.__getitem__, root)
    assert f"{GD.C4S2}/two_adic/ta_es.py" not in paths and f"{GD.C4S2}/two_adic/ta_mellin.py" in paths
    moved = dict(blobs, **{f"{GD.C4S2}/two_adic/ta_mellin.py": "zz"})
    assert GD.closure(moved, files.__getitem__, root)[0] != d0
    outside = dict(blobs, **{f"{GD.C4S2}/two_adic/ta_es.py": "zz"})
    assert GD.closure(outside, files.__getitem__, root)[0] == d0
    assert GD.dirty(f" M {GD.C4S2}/two_adic/ta_mellin.py\n", paths, names)
    assert GD.dirty(f"?? {GD.C4S2}/kernel/ta_mellin.py\n", paths, names)  # a shadowing file
    assert not GD.dirty(f" M {GD.C4S2}/two_adic/ta_es.py\n", paths, names)


def test_checkpoint_round_trip_and_refusals(tmp_path):
    k = {"rebuild_digest": "aa", "ts_inputs_digest": "bb", "head": "cc"}
    pay = {"last_block": 7, "M": {"2.9|32": [["1.0", "1e-40"]]}}
    GD.save_block(str(tmp_path), "shard00", 7, k, pay)
    assert GD.load_block(str(tmp_path), "shard00", 7, k) == pay
    assert GD.load_block(str(tmp_path), "shard00", 8, k) is None
    with pytest.raises(GD.GuardRefused, match="stale"):
        GD.load_block(str(tmp_path), "shard00", 7, dict(k, rebuild_digest="zz"))
    path = GD.block_path(str(tmp_path), "shard00", 7)
    body = json.load(open(path))
    body["payload"]["last_block"] = 8
    json.dump(body, open(path, "w"))
    with pytest.raises(GD.GuardRefused, match="hash"):
        GD.load_block(str(tmp_path), "shard00", 7, k)


# --- RUNS: the block price ----------------------------------------------------


def test_price_json_is_a_full_block_at_both_precisions():
    p = json.load(open(PRICE))
    m = p["meta"]
    assert m["nvec"] == 280 and m["N"] == 32 and m["Kmax"] == 14 and m["flint_threads"] == 1
    assert m["grids"]["stored_S"]["nw"] == 238764
    assert [b["bits"] for b in p["block"]] == [133, 200]
    for b in p["block"]:
        assert b["nw"] == m["grids"]["stored_S"]["nw"] and b["block_s_nodes"] == 128


# --- LEMMA s1, s3: the record's Proposition 4 sizes at 280 modes ---------------


def test_lemma_reads_proposition_4_at_280_modes():
    import math

    rows = json.load(open(os.path.join(C4S2, "bound_trunc", "eps_trunc.json")))
    r = next(x for x in rows if str(x["c"]) == "2.9" and x["nvec"] == 280 and x["N"] == 32)["size_if_closed"]
    assert abs(r["W"] - 0.1313) < 5e-5 and r["W"] / 1.18e-2 > 11  # LEMMA s1 item 3, s2
    assert abs(r["W_continuous"] - 0.0063) < 5e-5
    # Prop 4(c)'s closed-form upper bound at sigma_n, by hand: about 20 times W_continuous (LEMMA s3)
    L, N = math.log(2.9), 32
    K2 = (2 * math.pi / L) ** 2 * N * (N + 1) * (2 * N + 1) / 3
    sig, kap = 2 * 280 / math.sqrt(3), 2 * math.pi * N / L
    up = 4 * K2 / (3 * math.pi * L * (sig - kap) ** 3)
    assert abs(up - r["upper_d"]) < 1e-9 and abs(up - 0.13) < 1e-3 and 20 < up / r["W_continuous"] < 21


def test_runs_quotes_the_price_and_the_estimate():
    import estimate as ES

    p = json.load(open(PRICE))
    lo, hi = p["block"]
    assert round(lo["phase_s"] + lo["matmul_s"] + p["rho_window"][0]["rho_two_families_s"]
                 + p["rho_window"][0]["window_three_cells_s"]) == 258
    assert round(hi["phase_s"] + hi["matmul_s"] + p["rho_window"][1]["rho_two_families_s"]
                 + p["rho_window"][1]["window_three_cells_s"]) == 340
    assert max(b["rss_gib_after"] for b in p["block"]) < 0.8
    est = json.load(open(os.path.join(HERE, "estimate.json")))
    # the JSON is what the module computes from the price
    for name, nvec, Ns in ES.BUILDS:
        assert est["builds"][name]["dps40"] == ES.build_estimate(p, 133, nvec, Ns)
    b = est["builds"]
    r = b["rebuild_280"]
    assert r["dps40"]["blocks"] == 1250 and r["dps40"]["nw"] == 382068 and r["dps40"]["S_prime"] == 1.0e4
    assert round(r["dps40"]["block_core_s"]) == 412 and round(r["production_core_hours"]) == 155
    assert [round(b[k]["production_core_hours"]) for k in ("sweep_364", "sweep_500", "sweep_700", "sweep_700_N64")] \
        == [341, 869, 2398, 3636]
    t = _read("RUNS.md")
    for s in ("258 s", "340 s", "155 core-hours", "341 core-hours", "869 core-hours", "2,398 core-hours",
              "3,636 core-hours", "412 s", "7 jobs"):
        assert s in t, s


# --- the workflow, as ruled (RUNS.md s6, s8) -------------------------------------


def test_workflow_matches_the_ruling():
    import yaml

    path = os.path.join(REPO, ".github", "workflows", "c4-exact-gram.yml")
    text = open(path).read()
    wf = yaml.safe_load(text)
    on = wf.get(True, wf.get("on"))  # YAML 1.1 reads the key `on` as True
    assert set(on) == {"push"}, "push only: no workflow_dispatch, no schedule"
    assert on["push"]["branches"] == ["hunt/c4-exact-gram"]
    assert on["push"]["paths"] == ["hunts/weil_propagation/c4_s2/exact_gram/RUN_REQUEST.json"]
    assert wf["permissions"] == {"contents": "read"}
    assert wf["concurrency"]["group"] == "c4-exact-gram"
    sh = wf["jobs"]["shards"]
    assert sh["timeout-minutes"] <= 350 and sh["strategy"]["max-parallel"] <= 6
    for v in ("OMP_NUM_THREADS", "OPENBLAS_NUM_THREADS", "MKL_NUM_THREADS", "FLINT_NUM_THREADS"):
        assert wf["env"][v] == "1"
    steps = [s.get("name", s.get("uses", "")) for s in sh["steps"]]
    assert steps.index("preflight (ball backend, snapshot guard, request, headroom, memory)") < steps.index("run 4 shards")
    assert "guard.key()" in text and "github.run_attempt" in text and "if: always()" in text
    assert not os.path.exists(os.path.join(HERE, "RUN_REQUEST.json")), "committed only after 'go'"


def test_tail_mass_and_the_aposteriori_reprice():
    tm = json.load(open(os.path.join(HERE, "tailmass.json")))["S"]
    got = [tm[k]["m_z"] for k in ("1200.0", "2266.1020257693895", "6000.0", "10000.0")]
    assert [round(x, 1) for x in got] == [40.1, 21.8, 8.3, 5.0]
    model = [(2 * 280 * 280 - 280) / (3.141592653589793 * S) for S in (1200.0, 2266.1020257693895, 6000.0, 10000.0)]
    assert all(g < m for g, m in zip(got, model))  # LEMMA s5: the model is above the measurement
    assert abs(got[0] / model[0] - 1) < 0.034 and all(abs(g / m - 1) < 0.01 for g, m in zip(got[1:], model[1:]))
    est = json.load(open(os.path.join(HERE, "estimate.json")))["builds_aposteriori"]
    assert est["rebuild_280"]["dps40"]["S_prime"] == 2700.0
    assert [round(est[k]["production_core_hours"]) for k in
            ("rebuild_280", "sweep_364", "sweep_500", "sweep_700", "sweep_700_N64")] == [28, 72, 209, 658, 844]
    for s in ("28 core-hours", "**72**", "**209**", "**658**", "**844**"):
        assert s in _read("RUNS.md"), s
