"""exact_gram/: tests of P1 to P4 (BOUNDS.md). Each check is paired with a planted fault it must catch."""

from __future__ import annotations

import os
import sys

import pytest
from flint import acb, arb, ctx

HERE = os.path.dirname(os.path.abspath(__file__))
if HERE not in sys.path:
    sys.path.insert(0, HERE)

import bounds as B  # noqa: E402
import rebuild as R  # noqa: E402


@pytest.fixture(autouse=True)
def _prec():
    old = ctx.prec
    ctx.prec = 133
    yield
    ctx.prec = old


@pytest.fixture(scope="module")
def modes4():
    old = ctx.prec
    ctx.prec = 133
    m = B.prolate_modes(4)
    ctx.prec = old
    return m


# --- s0: the cited inequalities, spot-checked (measured) ----------------------


def test_landau_and_kapteyn_on_a_grid():
    worst_l = 0.0
    for nu in (0.5, 1.5, 4.5, 20.5, 100.5, 648.5):
        for i in range(1, 160):
            x = arb(nu) * (arb(i) / 40) + arb(1) / 10
            J = x.bessel_j(arb(nu))
            if J.rad() > 1e-20:
                continue  # arb cannot resolve it here; no claim
            worst_l = max(worst_l, float((abs(J) * x ** (arb(1) / 3)).upper()))
            t = x / arb(nu)
            if t < 1:
                r = (1 - t * t).sqrt()
                kap = t ** arb(nu) * (arb(nu) * r).exp() / (1 + r) ** arb(nu)
                assert abs(J) < kap * (1 + arb(10) ** -30) + arb(10) ** -60, (nu, float(x.mid()))
    assert worst_l < 0.7858


def test_bessel_table_matches_arb_where_arb_resolves():
    for x in (1.0, 6.5, 33.0, 250.0, 4000.0):
        tab = B.bessel_table(lambda x=x: B.two_pi() * arb(x), 120)
        z = B.two_pi() * arb(x)
        for k in (0, 1, 7, 30, 60, 120):
            ref = z.bessel_j(arb(k) + arb(0.5)) * (arb.pi() / (2 * z)).sqrt()
            if ref.rad() < 1e-30:
                assert tab[k].overlaps(ref), (x, k)
        assert max(float(v.rad()) for v in tab) < 1e-38


# --- P1, P2 against the rule itself -------------------------------------------


@pytest.fixture(scope="module")
def tables():
    old = ctx.prec
    ctx.prec = 133
    md = B.prolate_modes(2)
    t12 = R.ModeTable(md, 6, 12.0, per_panel=12)
    t24 = R.ModeTable(md, 6, 12.0, per_panel=24)
    t4 = R.ModeTable(md, 6, 12.0, per_panel=4)
    ctx.prec = old
    return t12, t24, t4


def _hats(table, s):
    return R.hats_block(table, s, 14, 14, 24)


def test_p1_twelve_nodes_contain_the_twentyfour_node_value(tables):
    t12, t24, _ = tables
    s = [arb(0), arb(3) / 2, arb(12)]
    Z12, B12 = _hats(t12, s)
    Z24, B24 = _hats(t24, s)
    for i in range(2):
        for j in range(3):
            assert Z12[i, j].overlaps(Z24[i, j]) and B12[i, j].overlaps(B24[i, j])


def test_p1_planted_a_coarse_rule_under_a_fine_rules_radius_is_caught(tables):
    t12, _, t4 = tables
    t4.per_panel = 12  # the 4-node table now claims the 12-node bound: too small
    t4._radii_key = None
    s = [arb(3) / 2, arb(12)]
    Z4, _ = _hats(t4, s)
    Z12, _ = _hats(t12, s)
    assert any(not Z4[i, j].overlaps(Z12[i, j]) for i in range(2) for j in range(2))
    t4.per_panel = 4
    t4._radii_key = None


def test_p2_tail_expansion_inside_its_bound(modes4):
    s = arb(7)
    lo = R._tail_T(modes4, 64.0, s, 10, 10)
    hi = R._tail_T(modes4, 64.0, s, 40, 40)
    for n in range(4):
        r = B.e4_tail_bound(modes4, n, 64.0, 7.0, 10, 10)
        assert abs(lo[n] - hi[n]) < r + B.e4_tail_bound(modes4, n, 64.0, 7.0, 40, 40)
    # planted: a 3-term expansion claiming the 40-term radius is caught
    lo3 = R._tail_T(modes4, 64.0, s, 3, 3)
    assert any(abs(lo3[n] - hi[n]) > 2 * B.e4_tail_bound(modes4, n, 64.0, 7.0, 40, 40) for n in range(4))


# --- P3: Poisson aliasing ------------------------------------------------------


@pytest.mark.parametrize("den", [2, 4, 16])
def test_poisson_bound_is_sharp_on_the_model(den):
    d = arb(1) / den
    x = arb.pi() / (3 * d)
    exact = arb(1.5) * (x.cosh() / x.sinh() - 1)  # (Delta/2pi) sum |k^|^2 - ||k||^2 for k = e^{-u/3}
    bound = B.p3_alias_rho(arb(1), d)
    assert (bound - exact).overlaps(arb(0)) or bound > exact
    assert abs(bound - exact) < arb(10) ** -30 * (1 + abs(exact))
    # planted: a bound with e^{-U/2} in place of e^{-U/3} is violated
    q2 = (-(arb.pi() / d)).exp()
    assert exact > arb(1.5) * 2 * q2 / (1 - q2)


def test_kappa_matches_bound_quad():
    sys.path.insert(0, os.path.join(HERE, "..", "bound_quad"))
    import eps_quad as E

    a, b = B.kappa((arb(29) / 10).log(), 32, 1.0e4), E.kappa(2.9, 32, 1.0e4)  # bounds.kappa takes L = log c
    assert abs(a - b) < arb(10) ** -12


# --- P4: G_z is the identity; the float-endpoint defect is caught --------------


def test_gram_z_is_the_identity(modes4):
    G = B.gram_z(modes4, 10)
    for i in range(4):
        for j in range(4):
            assert G[i, j].overlaps(arb(1 if i == j else 0)), (i, j, G[i, j])
    assert float(G[0, 0].rad()) < 1e-12 and float(G[3, 3].rad()) < 1e-15


def test_planted_float_endpoints_exclude_the_identity(modes4, monkeypatch):
    """The defect of BOUNDS.md s1.1: float midpoints leave ulp gaps the balls cannot see."""

    def float_point(left, right=None, n=0, j=0):
        if right is None:
            return lambda: arb(left)
        mid, half = left + (right - left) / 2.0, (right - left) / 2.0
        mid = mid * (1 + 2.0**-52)  # a one-ulp shift, the size float rounding produces
        return lambda: arb(mid) + arb(half) * B.gauss_rule(n)[j][0]

    monkeypatch.setattr(B, "point", float_point)
    G = B.gram_z(modes4, 10)
    assert any(not G[i, j].overlaps(arb(1 if i == j else 0)) for i in range(4) for j in range(4))




# --- the production-size numbers BOUNDS.md and RUNS.md quote ------------------


@pytest.mark.slow
def test_production_size_numbers():
    md = B.prolate_modes(280)
    e3 = B.e3_hat_bound(14, 1.0e4)
    assert e3 < arb(10) ** -15
    sc2 = sum((md.C(n) ** 2 for n in range(280)), arb(0))
    assert abs(float(sc2.mid()) - 5.17e4) < 0.01e4
    # the stored route's k >= Kmax tail at 5 derivatives and 8 terms, highest mode (BOUNDS s2)
    stored = B.e4_tail_bound(md, 279, 2.0**14, 2266.1, 5, 8)
    assert stored > arb(10) ** -6
    # the rebuild's choice closes there
    assert B.e4_tail_bound(md, 279, 2.0**14, 1.0e4, B.choose_M(md, 2.0**14), 40) < arb(10) ** -20
