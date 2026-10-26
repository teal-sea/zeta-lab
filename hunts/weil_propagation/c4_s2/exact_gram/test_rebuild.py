"""exact_gram/: rebuild.py at toy size (2 modes, Kmax 6, S' = 12), with planted faults."""

from __future__ import annotations

import os
import sys

import pytest
from flint import arb, ctx

HERE = os.path.dirname(os.path.abspath(__file__))
if HERE not in sys.path:
    sys.path.insert(0, HERE)

import guard as GD  # noqa: E402
import rebuild as R  # noqa: E402

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


def test_the_exact_provider_stops_at_P4_and_the_cli_refuses_toys(state, tmp_path):
    modes = state[0]
    with pytest.raises(NotImplementedError):
        R.provider("exact", modes, 6)
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
