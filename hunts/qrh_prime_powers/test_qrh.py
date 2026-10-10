"""Checks for the prime-between-ninth-powers chain (RESULTS.md).

Independent routes: the explicit formula is tested against 1000 tabulated
zeros and a direct prime-power sum; the closed-form zero-sum integrals are
tested against mpmath quadrature; the Pratt checker is integer-only and is
fed planted faults.  The full chain replays in about a second.
"""

from __future__ import annotations

import json
from fractions import Fraction
from pathlib import Path

import mpmath as mp
import pytest
import sympy
from flint import arb

from hunts.qrh_prime_powers import bound as B
from hunts.qrh_prime_powers import pratt, verify

ROOT = Path(__file__).resolve().parents[2]
HERE = Path(__file__).resolve().parent
B.set_precision()


@pytest.fixture
def no_height():
    old = B.H0
    B.H0 = 0
    yield
    B.H0 = old


# ---------------------------------------------------------------- weight


def test_weight_constants_are_exact():
    u = sympy.symbols("u")
    pieces = [(sympy.Rational(27, 2) * u ** 2, 0, sympy.Rational(1, 3)),
              (-27 * u ** 2 + 27 * u - sympy.Rational(9, 2), sympy.Rational(1, 3), sympy.Rational(2, 3)),
              (sympy.Rational(27, 2) * (1 - u) ** 2, sympy.Rational(2, 3), 1)]
    assert sum(sympy.integrate(f, (u, a, b)) for f, a, b in pieces) == 1
    # C^1 at the knots
    for (f, _, b), (g, _, _) in zip(pieces, pieces[1:]):
        assert f.subs(u, b) == g.subs(u, b)
        assert sympy.diff(f, u).subs(u, b) == sympy.diff(g, u).subs(u, b)
    assert pieces[1][0].subs(u, sympy.Rational(1, 2)) == B.PHI_MAX
    l1 = sum(sympy.integrate(sympy.Abs(sympy.diff(f, u)), (u, a, b)) for f, a, b in pieces)
    assert l1 == B.C_M1
    second = [sympy.diff(f, u, 2) for f, _, _ in pieces]
    assert second == [27, -54, 27]
    jumps = [27, -81, 81, -27]
    assert sum(abs(j) for j in jumps) == B.C_M3
    # the m = 2 bound 36/u^2 is never below min(1, 9/(2u), 216/u^3)
    for k in range(1, 4000):
        x = Fraction(k, 100)
        env = min(Fraction(1), Fraction(9, 2) / x, 216 / x ** 3)
        assert Fraction(36) / x ** 2 >= env


def _W(s, x, h):
    """Closed-form Mellin transform of w(t) = phi((t-x)/h) (RESULTS.md (2.3))."""
    jumps = [27, -81, 81, -27]
    tot = sum(j * mp.power(x + i * mp.mpf(h) / 3, s + 2) for i, j in enumerate(jumps))
    return -tot / (h ** 2 * s * (s + 1) * (s + 2))


def _w(t, x, h):
    u = (mp.mpf(t) - x) / h
    if u <= 0 or u >= 1:
        return mp.mpf(0)
    if u <= mp.mpf(1) / 3:
        return mp.mpf(27) / 2 * u ** 2
    if u <= mp.mpf(2) / 3:
        return -27 * u ** 2 + 27 * u - mp.mpf(9) / 2
    return mp.mpf(27) / 2 * (1 - u) ** 2


def test_explicit_formula_normalization_against_tabulated_zeros():
    zeros = json.loads((ROOT / "data" / "zeros_1000.json").read_text())["zeros"]
    x, h = 1000, 1000
    with mp.workdps(30):
        assert abs(_W(mp.mpf(1), x, h) - h) < mp.mpf("1e-20")
        direct = mp.mpf(0)
        for p in sympy.primerange(2, x + h):
            q = p
            while q < x + h:
                if q > x:
                    direct += _w(q, x, h) * mp.log(p)
                q *= p
        zsum = mp.mpf(0)
        for g in zeros:
            zsum += 2 * mp.re(_W(mp.mpc(0.5, mp.mpf(g)), x, h))
        triv = sum(mp.quad(lambda t: _w(t, x, h) / (t * (t * t - 1)),
                           [x + i * mp.mpf(h) / 3, x + (i + 1) * mp.mpf(h) / 3]) for i in range(3))
        formula = h - zsum - triv
        flipped = h + zsum - triv
    # truncation after 1000 zeros: at most about 0.02 (RESULTS.md section 6)
    assert abs(direct - formula) < mp.mpf("0.05")
    assert abs(direct - flipped) > 5          # planted sign fault is visible


def test_envelope_dominates_the_mellin_transform_on_zeros():
    zeros = json.loads((ROOT / "data" / "zeros_1000.json").read_text())["zeros"]
    x, h = 10 ** 6, 3 * 10 ** 4
    eta = mp.mpf(h) / x
    with mp.workdps(30):
        for g in zeros[::50]:
            g = mp.mpf(g)
            W = abs(_W(mp.mpc(0.5, g), x, h))
            u = g * eta / (1 + eta)
            env = min(1, mp.mpf(9) / 2 / u, 216 / u ** 3)
            assert W <= h * x ** mp.mpf(-0.5) * env * (1 + mp.mpf("1e-20"))


# ------------------------------------------------------------- zero sums


def _quad_int_N_plus(p, A, B_, tangent):
    C1, C2, C3 = (mp.mpf(c.numerator) / c.denominator for c in (B.C1, B.C2, B.C3))
    lA = mp.log(A)

    def f(t):
        ll = (mp.log(lA) + (mp.log(t) - lA) / lA) if tangent else mp.log(mp.log(t))
        Np = t / (2 * mp.pi) * (mp.log(t) - mp.log(2 * mp.pi * mp.e)) + C1 * mp.log(t) + C2 * ll + C3
        return Np * t ** (-p)

    return mp.quad(f, [A, B_] if B_ != mp.inf else [A, 10 * A, 1000 * A, mp.inf])


@pytest.mark.parametrize("p,A,B_", [(2, 45, 4.0e4), (2, 1.0e6, 3.0e9), (4, 70, None), (4, 2.0e13, None)])
def test_closed_form_integrals_against_quadrature(p, A, B_):
    closed = B.int_N_plus(p, arb(A), None if B_ is None else arb(B_))
    with mp.workdps(30):
        q_tan = _quad_int_N_plus(p, mp.mpf(A), mp.inf if B_ is None else mp.mpf(B_), True)
        q_true = _quad_int_N_plus(p, mp.mpf(A), mp.inf if B_ is None else mp.mpf(B_), False)
    c = mp.mpf(closed.mid().str(30, radius=False))
    assert abs(c - q_tan) < mp.mpf("1e-15") * max(1, abs(q_tan))
    assert c >= q_true - mp.mpf("1e-20")       # the tangent line bounds log log t above


def test_low_sum_bounds_the_first_thousand_zeros():
    zeros = [float(z) for z in json.loads((ROOT / "data" / "zeros_1000.json").read_text())["zeros"]]
    for a in [1, 3, 10, 40]:
        actual = sum(min(1.0, 4.5 * a / g, 216 * a ** 3 / g ** 3) for g in zeros)
        assert actual <= float(B.S_low(arb(a)).upper().mid())
        # and the high-zero bound with no verified height dominates the same partial sum
        old = B.H0
        B.H0 = 0
        try:
            assert actual <= float(B.S_high(arb(a)).upper().mid())
        finally:
            B.H0 = old


def test_N_bounds_bracket_known_counts():
    # N(100) = 29 (CLAUDE.md ground truth); N(1000) = 649 from the zero table.
    zeros = [float(z) for z in json.loads((ROOT / "data" / "zeros_1000.json").read_text())["zeros"]]
    assert sum(1 for g in zeros if g <= 100) == 29
    for T in [100, 1000, 1400]:
        n = sum(1 for g in zeros if g <= T)
        assert B.N_minus(arb(T)) < n < B.N_plus(arb(T))


# ------------------------------------------------------------------ Pratt


def test_pratt_checker_accepts_witnesses_and_rejects_plants():
    for k in (9, 17):
        data = json.loads((HERE / f"witnesses_k{k}.json").read_text())
        assert [w["n"] for w in data] == list(range(1, 10))
        assert all(pratt.check_witness(w) for w in data)
    good = pratt.make(1000003)
    assert pratt.check(good)
    bad = json.loads(json.dumps(good))
    bad["p"] = 1000001                         # composite: 101 * 9901
    assert not pratt.check(bad)
    bad = json.loads(json.dumps(good))
    bad["factors"][-1][1] += 1                 # wrong factorisation
    assert not pratt.check(bad)
    w = pratt.witness(4, 9)
    w["prime"] = (5 ** 9) + 2                  # outside the interval
    assert not pratt.check_witness(w)


# -------------------------------------------------------------- the chain


def test_theorem1_chain_closes_with_height():
    res, wit = verify.chain(9, Fraction(7, 8), Fraction(100))
    assert res["closed"] and res["analytic_cover"]["closed"] and res["tail"]["closed"]
    assert float(res["analytic_cover"]["worst_margin_lower"]) > 0.8
    assert all(pratt.check_witness(w) for w in wit)


def test_theorem1_chain_closes_without_any_RH_verification(no_height):
    res, _ = verify.chain(9, Fraction(7, 8), Fraction(100))
    assert res["closed"]
    assert float(res["analytic_cover"]["worst_margin_lower"]) > 0.3


def test_weakened_abscissa_moves_the_threshold_as_predicted():
    res, _ = verify.chain(17, Fraction(15, 16), Fraction(200))
    assert res["closed"]
    for k, th in [(8, Fraction(7, 8)), (16, Fraction(15, 16))]:
        ff = verify.first_failure(B.KthPowers(k), th, 2.3, 60.0)
        assert ff["found"] and 27 < ff["logn_bisected"] < 31
        assert not B.kth_power_tail(k, th, Fraction(100))["closed"]
    # the predicted threshold is floor(1/(1-theta)) + 1
    assert [int(1 / (1 - th)) + 1 for th in (Fraction(7, 8), Fraction(15, 16))] == [9, 17]


def test_eleven_twelfths_gives_thirteenth_powers():
    for h0 in (B.H0, 0):
        old = B.H0
        B.H0 = h0
        try:
            res, _ = verify.chain(13, Fraction(11, 12), Fraction(200))
        finally:
            B.H0 = old
        assert res["closed"]
    ff = verify.first_failure(B.KthPowers(12), Fraction(11, 12), 2.3, 60.0)
    assert ff["found"] and 28 < ff["logn_bisected"] < 30
    data = json.loads((HERE / "witnesses_k13.json").read_text())
    assert [w["n"] for w in data] == list(range(1, 10))
    assert all(pratt.check_witness(w) for w in data)


def test_k8_failure_grows_like_log_n():
    fam = B.KthPowers(8)
    E1 = B.interval_bound(fam, Fraction(7, 8), arb(500), arb(500))["E"]
    E2 = B.interval_bound(fam, Fraction(7, 8), arb(1000), arb(1000))["E"]
    slope = (E2 - E1) / 500
    J1 = B.envelope_moments()["J1"]
    assert abs(slope - J1 / (8 * arb.pi())) < arb("0.001")


def test_theorem2_short_intervals_close():
    fam = B.PowerLog(Fraction(1, 2), Fraction(7, 8))
    grid = verify.cover(fam, Fraction(7, 8), Fraction(8), Fraction(400))
    tail = B.powerlog_tail(Fraction(1, 2), Fraction(7, 8), Fraction(400))
    assert grid["closed"] and tail["closed"]
    # c below J1/(8 pi) = 0.3458 cannot close the tail: the limit exceeds 1
    assert not B.powerlog_tail(Fraction(1, 3), Fraction(7, 8), Fraction(400))["closed"]


def test_no_zero_below_height_14():
    # Arb's zero count (argument principle with enclosures) and the table agree.
    assert arb(B.T_ZERO_FREE).zeta_nzeros() == 0
    assert arb(15).zeta_nzeros() == 1
    first = float(json.loads((ROOT / "data" / "zeros_1000.json").read_text())["zeros"][0])
    assert 14 < first < 14.2


def test_theorem3_psi_bound_closes():
    grid = verify.psi_cover(Fraction(7, 8), Fraction(10), Fraction(200))
    tail = B.psi_tail(Fraction(7, 8), Fraction(200))
    assert grid["closed"] and tail["closed"]
    # the target is genuinely tight: at log x = 6 the bound exceeds it
    assert B.psi_interval(Fraction(7, 8), arb(6), arb(6))["margin"] < 0


def test_psi_bound_is_consistent_with_actual_psi():
    # psi(x) at x = e^10 and e^12 by direct summation versus the bound
    for L in (10, 12):
        x = int(mp.e ** L)
        psi = sum(mp.log(p) * int(mp.floor(mp.log(x) / mp.log(p))) for p in sympy.primerange(2, x + 1))
        ratio = abs(psi - x) / mp.power(x, mp.mpf(7) / 8)
        bound = float(B.psi_interval(Fraction(7, 8), arb(L), arb(L))["ratio"].upper().mid())
        assert ratio < bound


def test_recorded_verification_matches_replay():
    rec = json.loads((HERE / "verification.json").read_text())
    res, _ = verify.chain(9, Fraction(7, 8), Fraction(100))
    assert rec["theorem1_k9"]["analytic_cover"] == res["analytic_cover"]
    assert rec["theorem1_k9"]["closed"] is True
    assert rec["theorem1_k9_without_RH_verification"]["closed"] is True
    assert rec["controls"]["theta15_16_k17"]["closed"] is True
    assert rec["theorem2_short"]["closed"] is True
    assert rec["theorem1prime_k13_eleven_twelfths"]["with_height"]["closed"] is True
    assert rec["theorem3_psi"]["closed"] is True
