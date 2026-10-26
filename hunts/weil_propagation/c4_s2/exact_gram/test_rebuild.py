"""exact_gram/: rebuild.py at toy size (2 modes, Kmax 6, S' = 12), with planted faults."""

from __future__ import annotations

import json
import os
import sys

import pytest
from flint import arb, ctx

HERE = os.path.dirname(os.path.abspath(__file__))
if HERE not in sys.path:
    sys.path.insert(0, HERE)

import guard as GD  # noqa: E402
import rebuild as R  # noqa: E402


@pytest.fixture(autouse=True)
def _prec():
    old = ctx.prec
    ctx.prec = 133
    yield
    ctx.prec = old

REQ = {"nvec": 2, "dps": 40, "Kmax": 6, "S_prime": 12, "delta_num": 1, "delta_den": 16, "block": 64,
       "M": 14, "J": 14, "kb": 24, "cells": ["2.9"], "Ns": [2], "gram": "toy-region-a",
       "local_data": ["satake", [1]], "replay_every": 0}
KEY = {"rebuild_digest": "toy", "ts_inputs_digest": "toy", "head": "toy"}


@pytest.fixture(scope="module")
def state():
    old = ctx.prec
    ctx.prec = 133
    st = R.setup(REQ)
    ctx.prec = old
    return st


@pytest.fixture(scope="module")
def full(state, tmp_path_factory):
    d = str(tmp_path_factory.mktemp("full"))
    R.run_shard(REQ, 0, 1, d, lambda: KEY, state=state)
    return R.assemble(REQ, 1, d, lambda: KEY)


# --- the gate -------------------------------------------------------------------


def test_gate_accepts_zeta_and_refuses_the_rivals():
    import sympy
    import ta_data as D

    assert R.gate(("satake", (1,))).alphas == (1,)
    with pytest.raises(D.NonUnitaryLocalData):
        R.gate(D.W_A_QUARTER)
    with pytest.raises(D.NonUnitaryLocalData):
        R.gate(D.EPSTEIN_116_TOWER)
    r5 = sympy.sqrt(5)
    kappa = (sympy.sqrt(10 - 2 * r5) - 2) / (r5 - 1)
    with pytest.raises(D.NonUnitaryLocalData):
        R.gate(("tower", {1: kappa}))  # DH's s_1(2) at degree 1
    with pytest.raises(D.NonUnitaryLocalData):
        R.gate(("satake", (-1,)))  # unitary but not zeta's: the rebuild builds zeta only


def test_the_cli_refuses_toys(state, tmp_path):
    req = tmp_path / "req.json"
    req.write_text(__import__("json").dumps(REQ))
    with pytest.raises(R.NotABound):
        R.main(["run", "--request", str(req), "--out", str(tmp_path)])


# --- the toy run ------------------------------------------------------------------


def test_toy_run_assembles_and_is_marked_D0(full):
    assert full["_reading"].startswith("PREREG row D0")
    D = full["2.9|2"]["delta_T"]
    r = full["2.9|2"]["radius_F"]
    assert r < 1e-2 and r > 0
    for i in range(5):
        for j in range(5):
            assert D[i, j].imag.overlaps(arb(0)) or abs(D[i, j].imag) < r
            assert D[i, j].real.overlaps(D[j, i].real)


def test_key_moved_mid_shard_is_refused_then_resume_matches(state, full, tmp_path):
    calls = {"n": 0}

    def moving():
        calls["n"] += 1
        return KEY if calls["n"] < 3 else dict(KEY, rebuild_digest="moved")

    with pytest.raises(GD.GuardRefused, match="moved"):
        R.run_shard(REQ, 0, 1, str(tmp_path), moving, state=state)
    assert GD.load_block(str(tmp_path), "shard00of01", 0, KEY)["last_block"] == 0
    R.run_shard(REQ, 0, 1, str(tmp_path), lambda: KEY, state=state)
    res = R.assemble(REQ, 1, str(tmp_path), lambda: KEY)
    A, Bm = res["2.9|2"]["delta_T"], full["2.9|2"]["delta_T"]
    assert all(A[i, j].real.overlaps(Bm[i, j].real) for i in range(5) for j in range(5))


def test_stale_checkpoint_and_missing_shard_are_refused(state, tmp_path):
    R.run_shard(REQ, 0, 2, str(tmp_path), lambda: KEY, state=state)
    with pytest.raises(GD.GuardRefused, match="stale"):
        R.run_shard(REQ, 0, 2, str(tmp_path), lambda: dict(KEY, ts_inputs_digest="other"), state=state)
    with pytest.raises(GD.GuardRefused, match="shard 1 missing"):
        R.assemble(REQ, 2, str(tmp_path), lambda: KEY)


def test_planted_hat_fault_is_caught_by_the_replay(state, tmp_path):
    req = dict(REQ, replay_every=1, replay_prec=200)
    with pytest.raises(R.ReplayMismatch, match="zeta"):
        R.run_shard(req, 0, 1, str(tmp_path), lambda: KEY, fault="hat", state=state)


def test_inner_mass_and_eps_q(full):
    r = full["2.9|2"]
    for t in r["tail_mass"]:  # nvec + alias - inner: a negative tail would be a defect
        assert t.upper() > 0 and t.lower() > -1e-20
    assert r["eps_q"].is_finite() and r["eps_q"] > r["radius_F"]


def test_calibration_stops_after_max_blocks(state, tmp_path):
    pay = R.run_shard(REQ, 0, 1, str(tmp_path), lambda: KEY, state=state, max_blocks=1)
    assert pay["last_block"] == 0 and len(pay["block_seconds"]) == 1 and pay["block_seconds"][0][1] > 0


def test_a_shard_with_no_blocks_returns_none(state, tmp_path):
    # 4 toy blocks in 6 shards leave shards 4 and 5 empty, as 338 blocks in 36 leave 34 and 35
    assert len(R.blocks(REQ)) == 4 and len(R.shard_range(4, 5, 6)) == 0

    def never():
        raise AssertionError("an empty shard reads no key and writes nothing")

    assert R.run_shard(REQ, 5, 6, str(tmp_path), never, state=state) is None
    assert os.listdir(tmp_path) == []


def test_a_gram_named_by_sha256_is_fail_closed(tmp_path):
    # the full run reuses the calibration's gram.json by digest (RUNS s11): absent or altered refuses
    req = dict(REQ, prepared=str(tmp_path / "prep"))
    R.prepare(req, req["prepared"])
    g = tmp_path / "prep" / "gram.json"
    R.setup(dict(req, gram_sha256=R._sha256(str(g))))
    with pytest.raises(GD.GuardRefused, match="sha256"):
        R.setup(dict(req, gram_sha256="0" * 64))
    good = R._sha256(str(g))
    g.write_text(g.read_text().replace("]", " ]", 1))  # planted: one byte changed, same JSON
    with pytest.raises(GD.GuardRefused, match="sha256"):
        R.setup(dict(req, gram_sha256=good))
    g.unlink()
    with pytest.raises(GD.GuardRefused, match="absent"):
        R.setup(dict(req, gram_sha256=good))


# --- the disk-backed table (unit 3) ---------------------------------------------------


def test_disk_table_reproduces_the_memory_table(state, tmp_path):
    modes, _, _, table, _ = state
    # chunk 100 < the largest level (408 nodes): a level written in several chunks (a truncation
    # defect of the first version, found by this test at chunk 300)
    disk = R.DiskModeTable.build(str(tmp_path / "t"), modes, REQ["Kmax"], REQ["S_prime"], chunk=100)
    s = [arb(0), arb(5) / 16, arb(12)]
    Z1, B1 = R.hats_block(table, s, 14, 14, 24)
    Z2, B2 = R.hats_block(disk, s, 14, 14, 24)
    assert all(Z1[i, j].overlaps(Z2[i, j]) and B1[i, j].overlaps(B2[i, j]) for i in range(2) for j in range(3))
    assert disk.disk_bytes() == 40 * (modes.nvec + 1) * sum(disk.counts) + os.path.getsize(str(tmp_path / "t" / "meta.json"))
    # a table for other parameters is refused
    with pytest.raises(ValueError, match="does not match"):
        R.DiskModeTable(str(tmp_path / "t"), modes, REQ["Kmax"], 13.0)


def test_disk_table_planted_corruptions_are_caught(state, tmp_path):
    """Two layers: the sha256 refuses any changed byte; the dps-60 replay catches a corruption above
    the hats' radius even with the hash check off. A flip below the radius is the hash's job alone."""
    modes = state[0]
    path = tmp_path / "t"
    R.DiskModeTable.build(str(path), modes, REQ["Kmax"], REQ["S_prime"])
    f = path / "level00.bin"
    raw = bytearray(f.read_bytes())
    raw[40 + 2] ^= 0x01  # a low mantissa bit of the first node's first mode
    f.write_bytes(bytes(raw))
    with pytest.raises(ValueError, match="sha256"):
        R.DiskModeTable(str(path), modes, REQ["Kmax"], REQ["S_prime"])
    raw[40 + 2] ^= 0x01
    raw[40 + 16] ^= 0x01  # a high mantissa bit: a change far above any radius
    f.write_bytes(bytes(raw))
    bad = R.DiskModeTable(str(path), modes, REQ["Kmax"], REQ["S_prime"], verify=False)
    s = [arb(1), arb(2)]
    Zd, Bd = R.hats_block(bad, s, 14, 14, 24)
    with pytest.raises(R.ReplayMismatch):
        R.replay_check(dict(REQ, replay_prec=200), modes, s, Zd, Bd)


@pytest.mark.slow
def test_toy_with_the_exact_provider_is_a_bound(tmp_path):
    req = dict(REQ, gram="exact", gram_target_exp=8, gram_R=40, prepared=str(tmp_path / "prep"))
    old = ctx.prec
    ctx.prec = 133
    try:
        nbytes = R.prepare(req, req["prepared"])
        assert nbytes > 0
        R.run_shard(req, 0, 1, str(tmp_path / "out"), lambda: KEY)
        res = R.assemble(req, 1, str(tmp_path / "out"), lambda: KEY)
    finally:
        ctx.prec = old
    assert "_reading" not in res and res["2.9|2"]["is_bound"]
    assert res["2.9|2"]["eps_q"].is_finite()


@pytest.mark.slow
def test_gram_parts_merge_to_the_prepared_gram(tmp_path):
    req = dict(REQ, gram="exact", gram_target_exp=8, gram_R=40, prepared=str(tmp_path / "prep"))
    for p in range(2):
        R.gram_part(req, req["prepared"], p, 2)
    R.merge_gram(req, req["prepared"], 2)
    whole = tmp_path / "whole"
    R.prepare(req, str(whole), gram=True, table=False)
    a = json.load(open(tmp_path / "prep" / "gram.json"))
    b = json.load(open(whole / "gram.json"))
    for key in ("Gz", "Gb"):
        A, Bm = R._mat_load(a[key]), R._mat_load(b[key])
        assert all(A[i, j].overlaps(Bm[i, j]) for i in range(2) for j in range(2))
    (tmp_path / "prep" / "gram_part01of02.json").unlink()
    with pytest.raises(FileNotFoundError):
        R.merge_gram(req, req["prepared"], 2)
