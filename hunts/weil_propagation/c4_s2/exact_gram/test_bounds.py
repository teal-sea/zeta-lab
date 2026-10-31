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


# --- s0: the n-point Gauss bound against true errors (correction of 2026-10-27) --------


def _cheb_T(k, x):
    t0, t1 = arb(1), x
    for _ in range(k - 1):
        t0, t1 = t1, 2 * x * t1 - t0
    return t1 if k else t0


def _old_formula(h, M, rho, n):
    """The pre-correction gauss_panel_error: (h/2)(64/15) M rho^{-2n}/(rho^2 - 1), the (n+1)-point rate."""
    rho = arb(rho)
    return arb(h) / 2 * B.GAUSS_CONST * M * rho ** (-2 * n) / (rho * rho - 1)


def _gauss_cases():
    """(name, n, rho, |I - G_n| on [-1, 1], M = max |f| on E_rho) for entire f: T_2n (the first even
    Chebyshev polynomial the rule misses; max on E_rho is (rho^2n + rho^-2n)/2), exp(3x), exp(10x)
    (max e^{a (rho + 1/rho)/2}) and cos(20x) (|cos(u + iv)| <= cosh v, |v| <= (rho - 1/rho)/2)."""
    out = []
    for n in (2, 4, 12, 13, 16):
        rule = B.gauss_rule(n)
        k = 2 * n
        err = abs(arb(-2) / (k * k - 1) - sum((w * _cheb_T(k, x) for x, w in rule), arb(0)))
        for rho in (1.2, 1.5, 3.0, 8.0, 15.0, 40.0):
            R = arb(rho)
            out.append((f"T_{k}", n, rho, err, (R**k + R ** (-k)) / 2))
        fam = [("exp(3x)", lambda x: (3 * x).exp(), ((arb(3)).exp() - (-arb(3)).exp()) / 3,
                lambda R: (3 * (R + 1 / R) / 2).exp()),
               ("exp(10x)", lambda x: (10 * x).exp(), ((arb(10)).exp() - (-arb(10)).exp()) / 10,
                lambda R: (10 * (R + 1 / R) / 2).exp()),
               ("cos(20x)", lambda x: (20 * x).cos(), 2 * (arb(20)).sin() / 20,
                lambda R: (20 * (R - 1 / R) / 2).cosh())]
        for name, f, I, Mf in fam:
            err = abs(I - sum((w * f(x) for x, w in rule), arb(0)))
            for rho in (1.5, 3.0, 8.0, 15.0):
                out.append((name, n, rho, err, Mf(arb(rho))))
    return out


def test_gauss_bound_holds_on_entire_functions():
    """BOUNDS.md s5: the corrected n-point bound covers the true error in every case (measured: it can
    only refute, and here it does not); the T_2n cases come within a factor 1.6 of it."""
    old = ctx.prec
    ctx.prec = 256
    try:
        cases = _gauss_cases()
        for name, n, rho, err, M in cases:
            assert err < B.gauss_panel_error(2, M, rho, n), (name, n, rho)  # h = 2: the panel [-1, 1]
        t24 = [c for c in cases if c[0] == "T_24"]
        assert all(abs(float(c[3].mid()) - 1.54) < 0.01 for c in t24)
        assert float((B.gauss_panel_error(2, t24[-1][4], 40.0, 12) / t24[-1][3]).mid()) < 1.4
    finally:
        ctx.prec = old


def test_gauss_old_formula_fails_on_entire_functions():
    """Planted: the pre-correction formula (the (n+1)-point rate used for n points) is violated, by T_24
    at n = 12 for rho >= 3 (1.54 against 0.267 at rho = 3 and 0.0095 at rho = 15) and by exp(3x), a
    non-polynomial integrand, at n = 12, rho = 15 (9.1e-20 against 7.4e-21)."""
    old = ctx.prec
    ctx.prec = 256
    try:
        bad = {(c[0], c[1], c[2]) for c in _gauss_cases() if not c[3] < _old_formula(2, c[4], c[2], c[1])}
        assert {("T_24", 12, r) for r in (3.0, 8.0, 15.0, 40.0)} <= bad
        assert ("exp(3x)", 12, 15.0) in bad and ("T_26", 13, 15.0) in bad
        assert len(bad) == 25  # of 90 (BOUNDS.md s5)
    finally:
        ctx.prec = old


def test_corrected_bound_at_n_plus_one_is_the_old_formula_at_n():
    """Why production runs 13 nodes: the corrected 13-node bound equals the old 12-node formula, so every
    radius term of the rerun equals the one run 40371181784 carried (now valid)."""
    for rho in (1.5, 3.0, 15.0):
        for h in (arb(1) / 1000, arb(1) / 2):
            a, b = B.gauss_panel_error(h, arb(7), rho, 13), _old_formula(h, arb(7), rho, 12)
            assert (a - b).overlaps(arb(0)) and abs(a - b) < arb(10) ** -12 * a  # GAUSS_CONST is a 53-bit ball
            assert abs(B.gauss_panel_error(h, arb(7), rho, 12) / b - arb(rho) ** 2) < arb(10) ** -12  # rho^2 wider
    with pytest.raises(ValueError):
        B.gauss_panel_error(arb(1), arb(1), 3.0, 1)


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
    G = B.gram_z(modes4, 10, per_panel=13)  # production nodes since 2026-10-27 (BOUNDS.md s5)
    for i in range(4):
        for j in range(4):
            assert G[i, j].overlaps(arb(1 if i == j else 0)), (i, j, G[i, j])
    assert float(G[0, 0].rad()) < 1e-12 and float(G[3, 3].rad()) < 1e-15
    # at 12 nodes the corrected bound is about rho^2 = 225 times wider: 1.4e-10 at (0, 0)
    G12 = B.gram_z(modes4, 10, per_panel=12)
    assert all(G12[i, j].overlaps(arb(1 if i == j else 0)) for i in range(4) for j in range(4))
    assert 1e-10 < float(G12[0, 0].rad()) < 2e-10


def test_planted_float_endpoints_exclude_the_identity(modes4, monkeypatch):
    """The defect of BOUNDS.md s1.1: float midpoints leave ulp gaps the balls cannot see."""

    def float_point(left, right=None, n=0, j=0):
        if right is None:
            return lambda: arb(left)
        mid, half = left + (right - left) / 2.0, (right - left) / 2.0
        mid = mid * (1 + 2.0**-52)  # a one-ulp shift, the size float rounding produces
        return lambda: arb(mid) + arb(half) * B.gauss_rule(n)[j][0]

    monkeypatch.setattr(B, "point", float_point)
    G = B.gram_z(modes4, 10, per_panel=13)
    assert any(not G[i, j].overlaps(arb(1 if i == j else 0)) for i in range(4) for j in range(4))
    # observed 2026-10-27: under the corrected bound at 12 nodes the one-ulp gap hides inside the radius,
    # one more reason production runs 13 (BOUNDS.md s5)
    G12 = B.gram_z(modes4, 10, per_panel=12)
    assert all(G12[i, j].overlaps(arb(1 if i == j else 0)) for i in range(4) for j in range(4))




# --- the production-size numbers BOUNDS.md and RUNS.md quote ------------------


def test_production_gauss_terms_at_12_and_13_nodes():
    """BOUNDS.md s5: at the production grid (K = 14, S' = 2700) the corrected bound at 12 nodes is about
    rho^2 = 225 times the old values; at 13 nodes it is the old values (E3 here; the Gram terms are
    quoted in BOUNDS.md s5 from the same panel loop)."""
    e12, e13 = B.e3_hat_bound(14, 2700, 12), B.e3_hat_bound(14, 2700, 13)
    assert abs(float(e12.mid()) / 1.0189e-15 - 1) < 1e-3 and abs(float(e13.mid()) / 4.5284e-18 - 1) < 1e-3
    assert 200 < float((e12 / e13).mid()) < 226


@pytest.mark.slow
def test_production_size_numbers():
    md = B.prolate_modes(280)
    e3 = B.e3_hat_bound(14, 1.0e4, 13)  # production nodes since 2026-10-27 (at 12 the corrected E3 is 1.007e-15)
    assert e3 < arb(10) ** -15
    assert B.e3_hat_bound(14, 1.0e4, 12) > arb(10) ** -15
    sc2 = sum((md.C(n) ** 2 for n in range(280)), arb(0))
    assert abs(float(sc2.mid()) - 5.17e4) < 0.01e4
    # the stored route's k >= Kmax tail at 5 derivatives and 8 terms, highest mode (BOUNDS s2)
    stored = B.e4_tail_bound(md, 279, 2.0**14, 2266.1, 5, 8)
    assert stored > arb(10) ** -6
    # the rebuild's choice closes there
    assert B.e4_tail_bound(md, 279, 2.0**14, 1.0e4, B.choose_M(md, 2.0**14), 40) < arb(10) ** -20
