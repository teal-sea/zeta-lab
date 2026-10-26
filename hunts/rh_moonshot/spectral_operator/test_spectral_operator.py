"""Tests for hunt #150 mechanism 5 (spectral_operator): the CCM spectral triple.

Each test can fail.  They pin:

* provenance: the source of every defining function, and of the Weil-form
  assembly it calls, reads no zero, zero list or xi phase; a planted function
  that does read the zeros is flagged by the same scan;
* CCM's Lemma "key" (ii): W D' = D'^T W with W = T - eps_N, for zeta and DH;
* the even-simple hypothesis by Arb LDL^T inertia, for zeta and for DH,
  including a DH window where T itself is not positive (eps_N < 0) and the
  intertwiner W = T - eps_N is positive all the same;
* the spectrum by two routes (eigenvalues of D', real zeros of F_xi);
* the numbers NOTES.md quotes from data/cell_*.json.

Nothing here writes into the tree.
Run: .venv/bin/python -m pytest -q -n0 hunts/rh_moonshot/spectral_operator/test_spectral_operator.py
"""

from __future__ import annotations

import inspect
import json
import os
import re
import sys

import pytest
from mpmath import mp

HERE = os.path.dirname(os.path.abspath(__file__))
if HERE not in sys.path:
    sys.path.insert(0, HERE)

import spo_common as S  # noqa: E402
import ccm_common as C  # noqa: E402
import enclosures as EN  # noqa: E402
from flint import ctx  # noqa: E402

DATA = os.path.join(HERE, "data")

FORBIDDEN = re.compile(
    r"zetazero|zeta_zero|first_n_zeros|zeros_upto|siegelz|rs_theta|riemann_siegel|grampoint"
    r"|dh_zeros|zero_list|zeta_ordinates|radical|xi_kind|xi_real|completed_dh|shifted_completed"
    r"|epstein_completed|loggamma\(|zeta\.core|from zeta"
)


def _flags(src: str) -> list:
    return FORBIDDEN.findall(src)


def test_provenance_of_the_definition():
    srcs = [inspect.getsource(getattr(S, name)) for name in S.DEFINITION]
    srcs.append(inspect.getsource(EN.BallTruncation))
    srcs.append(inspect.getsource(C.lowest_pairs))
    srcs.append(inspect.getsource(C.to_mp))
    for src in srcs:
        assert _flags(src) == [], _flags(src)


def test_provenance_scan_catches_a_planted_import():
    def tainted(N):
        return [mp.im(mp.zetazero(k)) for k in range(1, N)]

    assert _flags(inspect.getsource(tainted)) == ["zetazero"]


def _small(kind, c, N):
    prec = S.prec_for(kind, c, N)
    bt, Te, To = S.sectors(kind, c, N, prec)
    rq, v = S.ground(Te)
    return prec, bt, Te, To, rq, v


@pytest.mark.parametrize("kind", ["zeta", "dh"])
def test_intertwining_lemma_key(kind):
    prec, bt, Te, To, rq, v = _small(kind, 13, 12)
    T = S.full_matrix(bt)
    with mp.workdps(int(prec / 3.32)):
        xi = S.xi_full(v)
        eps = mp.mpf(rq.mid().str(int(prec / 3.32), radius=False))
        assert S.commutator_check(T, xi, eps) < 1e-60
        # planted fault: the wrong shift breaks it
        assert S.commutator_check(T, xi, eps + mp.mpf("1e-3")) > 1e-6


@pytest.mark.parametrize("kind,c,N,sign0", [("zeta", 13, 16, 1), ("dh", 13, 16, 1), ("dh", 60, 64, -1)])
def test_even_simple_by_inertia(kind, c, N, sign0):
    prec, bt, Te, To, rq, v = _small(kind, c, N)
    ctx.prec = prec
    lam2 = C.lowest_pairs(Te, k=2)[1][0].mid()
    lo = S.lowest_odd_mid(To)
    eps = rq.mid()
    rho = (min(lam2, lo) - eps) / 2
    assert tuple(S.inertia(Te, eps - rho)) == (N + 1, 0, True)
    assert tuple(S.inertia(Te, eps + rho)) == (N, 1, True)
    assert tuple(S.inertia(To, eps + rho)) == (N, 0, True)
    # T itself: positive for zeta and DH at c = 13, one negative direction for DH at c = 60
    expect = (N + 1, 0, True) if sign0 > 0 else (N, 1, True)
    assert tuple(S.inertia(Te, 0)) == expect


@pytest.mark.parametrize("kind", ["zeta", "dh"])
def test_spectrum_two_routes(kind):
    c, N = 13, 16
    prec, bt, Te, To, rq, v = _small(kind, c, N)
    with mp.workdps(int(prec / 3.32)):
        L = C.L_mp(c)
        xi = S.xi_full(v)
        sp = S.spectrum_matrix(S.operator(xi), L, 400)
        assert max(abs(mp.im(z)) for z in sp) < mp.mpf("1e-60")
        zs = sorted(mp.re(z) for z in sp if mp.re(z) > mp.mpf("0.1") and mp.re(z) < 30)
        fz = C.real_zeros(lambda t: mp.re(C.F_mp(v, L, mp.mpc(t, 0))), mp.mpf("0.3"), mp.mpf(30), mp.mpf("0.05"))
        assert len(zs) == len(fz) >= 3
        assert max(abs(a - b) for a, b in zip(zs, fz)) < mp.mpf("1e-20")
        if kind == "zeta":
            for z, g in zip(zs, ("14.134725141734694", "21.022039638771555", "25.010857580145689")):
                assert abs(z - mp.mpf(g)) < 1e-10


def _cell(kind, c, N):
    path = os.path.join(DATA, f"cell_{kind}_{c}_{N}.json")
    if not os.path.exists(path):
        pytest.skip(f"no {path}")
    with open(path) as fh:
        return json.load(fh)


@pytest.mark.parametrize("kind,c,N", [("zeta", 13, 50), ("zeta", 13, 100), ("zeta", 60, 100), ("zeta", 13, 200), ("dh", 13, 100), ("dh", 60, 100), ("dh", 13, 200)])
def test_cells_hypotheses_and_routes(kind, c, N):
    r = _cell(kind, c, N)
    assert r["even_simple_hardened"] is True
    assert r["n_eig"] == r["n_transform"]
    assert float(r["eig_vs_transform_max"]) < 1e-15
    assert float(r["max_abs_imag"]) < 1e-50
    if kind == "dh" and c == 60:
        assert r["inertia"]["even_at_0"][1] == 2 and r["inertia"]["odd_at_0"][1] == 2  # T not positive, W = T - eps is
    else:
        assert r["inertia"]["even_at_0"][1] == 0 and r["inertia"]["odd_at_0"][1] == 0


def test_zeta_table_first_hundred_zeros():
    r = _cell("zeta", 13, 200)
    t = r["table"]
    assert len(t) == 100
    res = [float(row[3]) for row in t]
    assert max(res[:10]) < 1e-25
    assert float(r["gram_residual_median"]) > 0.1  # the counting-function control is far off
    assert max(res[:50]) < 1e-2


def test_dh_real_eigenvalue_in_the_gap():
    r = _cell("dh", 13, 100)
    assert len(r["eig_in_gap_83_88"]) >= 1


def test_zeta_window_60_matches_every_zero_below_138():
    r = _cell("zeta", 60, 100)
    assert r["n_eig"] == len(r["table"]) == 46
    assert max(float(row[3]) for row in r["table"]) < 5e-40  # measured 4.6e-40


def test_zeta_13_200_stops_tracking_by_the_sixtieth_zero():
    r = _cell("zeta", 13, 200)
    res = [float(row[3]) for row in r["table"]]
    assert r["n_eig"] == 92 and len(res) == 100
    assert res[49] < 2e-3 and res[59] > 0.1
