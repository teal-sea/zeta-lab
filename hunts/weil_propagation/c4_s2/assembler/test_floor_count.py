"""PREREG Addendum A tests: the mode-free floor F and ceiling G.

Planted checks first (written and committed before any floor count ran);
the pins of floor_count.json follow in their own section, added with the
numbers.
"""

from __future__ import annotations

import json
import os
import sys

import pytest

HERE = os.path.dirname(os.path.abspath(__file__))
if HERE not in sys.path:
    sys.path.insert(0, HERE)

import floor_count as FC  # noqa: E402
from flint import arb, fmpq  # noqa: E402
from mpmath import mp  # noqa: E402

AS = FC.AS
RI = FC.RI


def test_kappa_and_K_are_bracketed_exactly():
    with RI.arb_prec(1024):
        kap = 17 - 12 * arb(2).sqrt()
        K = 17 + 12 * arb(2).sqrt()
        assert arb(FC.KAPPA_LO) < kap and arb(FC.K_HI) > K
        assert kap - arb(FC.KAPPA_LO) < arb(2) ** -250 and arb(FC.K_HI) - K < arb(2) ** -250
        assert (kap * K - 1).contains(0)  # K = 1/kappa
        assert ((arb(2).sqrt() - 1) ** 4 - kap).contains(0)
    assert "%.6f" % float(FC.KAPPA_LO) == "0.029437"


def test_eta_covers_the_stated_sizes():
    for N in (8, 16, 32):
        e = FC.eta(N)
        assert e == (2 * N + 1) * (AS.E_Q_ENTRY + FC.K_HI * AS.E_TINF_ENTRY)
        assert e >= (2 * N + 1) * (AS.E_Q_ENTRY + FC.KAPPA_LO * AS.E_TINF_ENTRY)
        assert float(e) < 3e-26


def _mpdiag(xs):
    with mp.workdps(40):
        M = mp.matrix(len(xs))
        for i, x in enumerate(xs):
            M[i, i] = mp.mpf(x)
        return M


def test_both_routes_on_a_planted_pair():
    """Q = diag(1e-3, 2, 3), T = diag(1, 1, 1e-2): Q - kappa T has one negative
    (1e-3 - 0.0294), Q - K T has two (2 - 33.97, 1e-3 - 33.97)."""
    Qq, Tq = FC.exact(_mpdiag(["1e-3", "2", "3"])), FC.exact(_mpdiag(["1", "1", "1e-2"]))
    e = fmpq(1, 10 ** 30)
    assert RI.inertia_both(FC.combo(Qq, Tq, FC.KAPPA_LO, e)) == (1, 0, 2)
    assert RI.inertia_both(FC.combo(Qq, Tq, FC.K_HI, -e)) == (2, 0, 1)
    with RI.arb_prec(256):
        kap, K = 17 - 12 * arb(2).sqrt(), 17 + 12 * arb(2).sqrt()
        assert FC.ball_inertia(FC.balls(Qq, Tq, kap, e, 256)) == (1, 0, 2)
        assert FC.ball_inertia(FC.balls(Qq, Tq, K, -e, 256)) == (2, 0, 1)


def test_combined_rule_on_planted_floors():
    def floor(F, G):
        return {"cells": {f"2.9|{N}": {"F": F[i], "G": G[i],
                                         "V4": {"F": {"n_minus": max(F[i] - 1, 0)}, "G": {"n_minus": G[i] - 1}}}
                          for i, N in enumerate(AS.NS)}}
    flat = floor((2, 2, 2), (17, 33, 65))
    assert FC.combined(None, flat, "2.9", "full")["decision"]["outcome"] == 3
    grows = floor((2, 3, 5), (17, 33, 65))
    assert FC.combined(None, grows, "2.9", "full")["decision"]["outcome"] == 1
    pinned = floor((2, 4, 4), (4, 4, 4))
    assert FC.combined(None, pinned, "2.9", "V4")["decision"]["outcome"] == 2
    # the rule's lower bounds are max(L*, F): a routed bound can lift them
    routed = {"has_bound": {8: True, 16: True, 32: True}, "raw_L": {8: 4, 16: 10, 32: 20},
              "raw_U": {8: 6, 16: 20, 32: 40}}
    d = FC.combined(routed, flat, "2.9", "full")
    assert d["decision"]["outcome"] == 1 and d["agg"]["L"] == {8: 4, 16: 10, 32: 20}


# ----------------------------------------------------------------- pins
# Added with floor_count.json, after the numbers (Addendum A was committed
# at e174d19 before any count at N = 32 or at c = 2.5, 2.2).

import functools  # noqa: E402
import subprocess  # noqa: E402

FLOOR = {"2.9": (2, 2, 2), "2.5": (1, 1, 1), "2.2": (0, 0, 0)}  # F at N = 8, 16, 32, full space
NEGS = {  # the negative eigenvalues of Q - kappa_lo T_inf, midpoints of exact brackets, 4 digits
    "2.9|8": ["-9.8913e-05", "-1.6206e-05"], "2.9|16": ["-9.9510e-05", "-1.6626e-05"],
    "2.9|32": ["-1.0017e-04", "-1.6736e-05"],
    "2.5|8": ["-7.1419e-06"], "2.5|16": ["-9.4713e-06"], "2.5|32": ["-1.0006e-05"]}
BOUND_TRUNC_COMMIT = "91ce087"  # bound_trunc/'s own count of the same floor, committed, later withdrawn


@functools.lru_cache(maxsize=None)
def _floor():
    if not os.path.exists(FC.OUT):
        pytest.skip("floor_count.json absent (run floor_count.py)")
    with open(FC.OUT) as fh:
        return json.load(fh)


def test_floor_pinned():
    f = _floor()["cells"]
    assert sorted(f) == sorted(f"{c}|{N}" for c in AS.CELLS for N in AS.NS)
    for c, Fs in FLOOR.items():
        for N, F in zip(AS.NS, Fs):
            r = f[f"{c}|{N}"]
            assert r["F"] == F and r["route2"]["F"] == F and r["n_minus_kappa_lo_unshifted"] == F
            assert r["F_at_eta_minus_delta"] == F == r["F_at_eta_plus_delta"]
            # on C4's class the floor is empty at every cell, decided by balls at 256 bits
            assert r["V4"]["F"]["n_minus"] == 0 and r["V4"]["F"]["prec"] == 256
            # the ceiling is the whole space: Q - K T_inf is negative definite, full and on V_4
            assert r["G"] == r["route2"]["G"] == 2 * N + 1 and r["V4"]["G"]["n_minus"] == 2 * N + 1 - 3
            mids = ["%.4e" % ((b["lo_float"] + b["hi_float"]) / 2) for b in r["negatives_kappa_lo"]]
            assert mids == NEGS.get(f"{c}|{N}", [])
            assert r["T_inf_direct_vs_moments"] < 1e-39


def test_floor_combined_rule_reads_flat_floor_everywhere():
    """A.3: with no eps, the combined rule is the floor alone: reading 3 (flat
    floor, upper bound open) on every cell and both spaces."""
    f = _floor()
    for c in AS.CELLS:
        for sp in ("full", "V4"):
            d = FC.combined(None, f, c, sp)
            assert d["decision"]["outcome"] == 3 and d["agg"]["consistent"]
            want = FLOOR[c] if sp == "full" else (0, 0, 0)
            assert tuple(d["agg"]["L"][N] for N in AS.NS) == want
            assert d["agg"]["U"][32] == (65 if sp == "full" else 62)


def test_floor_agrees_with_bound_truncs_own_count():
    """bound_trunc/ counted the same floor at 91ce087 (its kappa_floor.json, a
    separate script on the same inputs and the same inertia library; it shifts by
    -2^-40 where this one shifts by +eta). Same counts on all nine cells, same
    V_4 counts, the same negative eigenvalues to 1e-9."""
    try:
        raw = subprocess.run(["git", "show", f"{BOUND_TRUNC_COMMIT}:hunts/weil_propagation/c4_s2/bound_trunc/kappa_floor.json"],
                             capture_output=True, text=True, check=True, cwd=HERE).stdout
    except (subprocess.CalledProcessError, FileNotFoundError):
        pytest.skip(f"git object {BOUND_TRUNC_COMMIT} not available")
    theirs = {f"{r['c']}|{r['N']}": r for r in json.loads(raw)["rows"]}
    mine = _floor()["cells"]
    assert sorted(theirs) == sorted(mine)
    for key, r in theirs.items():
        m = mine[key]
        assert r["count_below_0"] == r["count_below_minus_margin"] == m["F"]
        assert r["class_V4"]["n_minus"] == m["V4"]["F"]["n_minus"]
        assert len(r["brackets"]) == len(m["negatives_kappa_lo"])
        for a, b in zip(r["brackets"], m["negatives_kappa_lo"]):
            assert abs(a["lo_float"] - (b["lo_float"] + b["hi_float"]) / 2) < 1e-9
