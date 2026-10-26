"""Tests for hunt #150 mechanism 2 (de_branges): the Lagarias structure functions.

Each test can fail.  They pin:

* Conrey and Li's two printed numbers (IMRN 2000, section 3.1), reproduced by
  two routes, so the reading of their E(z) = xi(1 - iz) and of their
  normalization of xi is checked;
* the two evaluation routes of every completed function against each other,
  and the functional equation s -> 1 - s (present for zeta, DH, Epstein (1,1,6)
  and W_{1/4}; absent for zeta(s - 1/5), as a planted lack);
* the Hermite-Biehler defect: negative for zeta at every h tried, positive for
  each rival exactly where its off-line zero puts a zero of E_h in the upper
  half-plane, and negative again once h exceeds the zero's offset;
* the derived fact that a single Euler factor is not Hermite-Biehler, with the
  closed-form criterion;
* the numbers NOTES.md quotes from data/grid_*.json.

Nothing here writes into the tree.
Run: .venv/bin/python -m pytest -q -n0 hunts/rh_moonshot/de_branges/test_de_branges.py
"""

from __future__ import annotations

import json
import os
import sys

import pytest
from mpmath import mp

HERE = os.path.dirname(os.path.abspath(__file__))
if HERE not in sys.path:
    sys.path.insert(0, HERE)

import dbr_common as D  # noqa: E402

DATA = os.path.join(HERE, "data")


def test_conrey_li_numbers_two_routes():
    a, b = D.conrey_li_numbers()
    c, d = D.conrey_li_numbers_arb()
    # printed: -5.389100507182945e-69 and -0.000131957
    assert abs(a / mp.mpf("-5.389100507182945e-69") - 1) < 1e-14
    assert abs(b - mp.mpf("-0.000131957")) < 5e-10
    assert abs(float(c.mid()) / float(a) - 1) < 1e-13 and c < 0
    assert abs(float(d.mid()) - float(b)) < 1e-15 and d < 0


@pytest.mark.parametrize("kind", ["zeta", "dh", "wa", "zshift", "epstein"])
def test_routes_agree(kind):
    s = mp.mpc("0.71", "9.3")
    a = D.mp_completed(kind, s, dps=20)
    b = D.arb_completed(kind, s, prec=200)
    bm = mp.mpc(b.real.mid().str(25, radius=False), b.imag.mid().str(25, radius=False))
    assert abs(a - bm) / abs(a) < 1e-12


@pytest.mark.parametrize("kind,symmetric", [("zeta", True), ("dh", True), ("wa", True), ("epstein", True), ("zshift", False)])
def test_functional_equation(kind, symmetric):
    s = mp.mpc("0.83", "7.1")
    a = D.arb_completed(kind, s, prec=200)
    b = D.arb_completed(kind, 1 - s, prec=200)
    za = float(a.real.mid()) + 1j * float(a.imag.mid())
    zb = float(b.real.mid()) + 1j * float(b.imag.mid())
    rel = abs(za - zb) / abs(za)
    assert (rel < 1e-12) if symmetric else (rel > 1e-2)


@pytest.mark.parametrize("h", ["1/2", "3/8", "1/4", "1/10", "1/20"])
def test_zeta_defect_negative(h):
    num, den = (int(t) for t in h.split("/"))
    hh = mp.mpf(num) / den
    for x, y in ((0.5, 0.05), (14.134725141734694, 0.1), (21.02, 0.3), (60.0, 0.05), (99.5, 0.2)):
        assert D.defect_arb("zeta", hh, x, y) < 0


@pytest.mark.parametrize("kind", ["dh", "epstein", "wa"])
def test_rival_fails_exactly_below_its_offset(kind):
    gamma = mp.mpf(D.OFFLINE[kind][1])
    delta = D.offset(kind)
    h_bad = delta - 0.05
    y0 = delta - h_bad  # E_{h_bad} has a zero at gamma + i y0
    prec = 160 + int(3 * float(gamma))
    assert D.defect_arb(kind, h_bad, gamma, y0 * 0.8, prec=prec) > 0
    h_good = delta + 0.03
    for y in (0.02, 0.1, 0.3):
        assert D.defect_arb(kind, h_good, gamma, y, prec=prec) < 0


def test_zshift_lacks_the_symmetry_and_fails_everywhere_below_delta():
    for x in (0.5, 30.0, 70.0):
        assert D.defect_arb("zshift", 0.1, x, 0.05) > 0
        assert D.defect_arb("zshift", 0.3, x, 0.05) < 0


def test_local_euler_factor_is_not_hermite_biehler():
    h, y = mp.mpf(1) / 2, mp.mpf(1) / 10
    for p in (2, 3, 5, 7, 101):
        assert D.local_factor_ratio(p, h, 0, y) > 1  # cos = 1
        with mp.workdps(30):
            rp = mp.power(p, -(mp.mpf(1) / 2 + h + y))
            rm = mp.power(p, -(mp.mpf(1) / 2 + h - y))
            for x in (0.3, 1.7, 2.9, 4.4):
                crit = mp.cos(x * mp.log(p)) > (rp + rm) / 2
                assert (D.local_factor_ratio(p, h, x, y) > 1) == crit


def _grid(kind):
    path = os.path.join(DATA, f"grid_{kind}.json")
    if not os.path.exists(path):
        pytest.skip(f"no {path}")
    with open(path) as fh:
        return json.load(fh)["by_h"]


def test_grid_zeta():
    g = _grid("zeta")
    assert len(g) == 7
    for h, v in g.items():
        s = v["summary"]
        assert s["n_positive"] == 0 and s["max_D_arb"] < 0
        assert s["n_undecided"] <= 1  # the removable point s = 1 on the Arb route
        assert s["max_abs_mp_minus_arb"] < 1e-10


def test_grid_dh():
    g = _grid("dh")
    for h in ("1/2", "3/8"):
        assert g[h]["summary"]["n_positive"] == 0
    for h in ("3/10", "1/4", "1/5", "1/10", "1/20"):
        s = g[h]["summary"]
        assert "85.6993484854" in s["positive_x"]
        assert set(s["positive_x"]) <= {"85.5", "85.6993484854"}
        assert s["column_positive_y"]["85.6993484854"]
    assert all(v["summary"]["max_abs_mp_minus_arb"] < 1e-10 for v in g.values())


def test_grid_wa_and_zshift():
    w = _grid("wa")
    for h in ("1/2", "3/8", "3/10"):
        assert w[h]["summary"]["n_positive"] == 0
    assert w["1/4"]["summary"]["n_positive"] == 0  # h equal to the offset 1/4
    for h in ("1/5", "1/10", "1/20"):
        assert "14.1347251417" in w[h]["summary"]["positive_x"]
    z = _grid("zshift")
    for h in ("1/2", "3/8", "3/10", "1/4"):
        assert z[h]["summary"]["n_positive"] == 0
    for h in ("1/10", "1/20"):
        assert z[h]["summary"]["n_positive"] == z[h]["summary"]["n_points"]


def test_grid_epstein():
    g = _grid("epstein")
    if len(g) < 7:
        pytest.skip("epstein grid incomplete")
    assert g["1/2"]["summary"]["n_positive"] == 0
    for h in ("3/8", "3/10", "1/4", "1/5", "1/10", "1/20"):
        assert "16.2902157204" in g[h]["summary"]["positive_x"]
