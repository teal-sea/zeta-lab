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
