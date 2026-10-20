"""Review of hunt #135 phase 2 (`REVIEW_PHASE2.md`): the independent reproduction, the
algebra the chain shares with Holland, and plants this review's own code must catch.

Nothing here imports `effective.py`, `probe.py`, `review/` or `review_h1h3/`.

Run: .venv/bin/python -m pytest -q -n0 hunts/jensen_wedge/review_p2/test_review_p2.py
"""

from __future__ import annotations

import sys
from fractions import Fraction
from pathlib import Path

import mpmath as mp
import pytest

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
for p in (str(ROOT), str(HERE)):
    if p not in sys.path:
        sys.path.insert(0, p)

import reproduce_p2 as R  # noqa: E402
from flint import arb  # noqa: E402
from zeta import rigor  # noqa: E402


def test_backend_is_arb():
    assert rigor.BACKEND == "python-flint"


# ---------------------------------------------------------------------------
# Lemma D(i), from this review's own sympy derivation
# ---------------------------------------------------------------------------


def test_F_k_normalisation_and_first_order_constants():
    harmonic = [Fraction(0), Fraction(1), Fraction(3, 2), Fraction(11, 6), Fraction(25, 12), Fraction(137, 60)]
    with R.prec():
        for k in range(2, 8):
            num, den = R.derive_F()[k]
            n0, d0 = num.get((0, 0), 0), den.get((0, 0), 0)
            assert Fraction(n0) / Fraction(d0) == 1
            # dF/de at (0, 0) = (n1 d0 - n0 d1)/d0^2
            n1, d1 = num.get((1, 0), 0), den.get((1, 0), 0)
            assert (Fraction(n1) * d0 - Fraction(n0) * d1) / Fraction(d0) ** 2 == harmonic[k - 2] - 1
        for e in ("0.01", "0.1", "0.3"):
            x = R.Q(Fraction(e))
            assert (R.F_point(2, x, arb(0)) - 1 / (1 + x)).abs_upper() < arb(10) ** -60


# ---------------------------------------------------------------------------
# Lemmas V, L, R: the review's majorants, and a measured remainder
# ---------------------------------------------------------------------------

CLAIMED_LAPLACE = {  # EFFECTIVE.md section 7: (C_rho, lambda) claimed upper bounds
    789702: ("2.029", "6.978e-3"),
    14237025: ("1.985", "1.790e-3"),
    Fraction("9.91e33"): ("1.888", "1.507e-16"),
    Fraction("5.65e35"): ("1.887", "2.048e-17"),
}


@pytest.mark.parametrize("x0", list(CLAIMED_LAPLACE))
def test_laplace_constants_reproduce_and_conditions_hold(x0):
    with R.prec():
        lb = R.laplace(x0)
        assert all(lb["conds"].values()), lb["conds"]
        c_rho, lam = CLAIMED_LAPLACE[x0]
        assert lb["C_rho"] < R.Q(Fraction(c_rho))
        assert lb["lambda"] < R.Q(Fraction(lam))
        # and within 0.1 percent: the two derivations agree, not just bound each other
        assert lb["C_rho"] > R.Q(Fraction(c_rho) * Fraction(999, 1000))


def _measured_rho(x, ang):
    """|I(s) e^{-phi(v0)} (Psi/2pi)^{1/2} - 1| at s = 2x(1 + e^{i ang}/4), by quadrature
    on a tilted contour through the complex saddle (slope 0.1, not the lemma's contour)."""
    with mp.workdps(40):
        a = mp.mpf(9) / 4
        s = 2 * x * (1 + mp.mpf(1) / 4 * mp.exp(1j * ang))

        def alpha(v):
            return mp.fsum((k**4 - 3 / (2 * mp.pi) * k**2 * mp.exp(-v)) * mp.exp(-mp.pi * (k * k - 1) * mp.exp(v))
                           for k in range(1, 6))

        v = mp.log(abs(s) / mp.log(abs(s)))
        for _ in range(100):
            v -= (v * (mp.pi * mp.exp(v) - a) - s) / (mp.pi * mp.exp(v) * (1 + v) - a)
        Psi = s / v**2 + s / v + a
        phi0 = s * mp.log(v) + a * v - mp.pi * mp.exp(v)

        def f(w):
            return mp.exp(s * mp.log(w) + a * w - mp.pi * mp.exp(w) - phi0) * alpha(w)

        d = mp.mpc(1, 0.1)
        Rv = mp.re(v)
        w1 = v - d * Rv / 2
        seg = mp.quad(lambda u: f(w1 * u) * w1, [0, 0.5, 1])
        sc = 1 / mp.sqrt(abs(Psi))
        pts = sorted({-Rv / 2, *[k * sc for k in range(-40, 41, 4)], 60 * sc, 2, 5})
        line = mp.quad(lambda t: f(v + d * t) * d, pts)
        return float(abs((seg + line) / mp.sqrt(2 * mp.pi / Psi) - 1))


def test_laplace_bound_covers_quadrature_and_a_planted_fault_is_caught():
    x0 = 789702
    with R.prec():
        lam = R.up(R.laplace(x0)["lambda"])
        crho = R.laplace(x0)["C_rho"]
        p = R.laplace(x0)["p"]
    worst = max(_measured_rho(mp.mpf(x0), ang) for ang in (0.0, mp.pi / 2, mp.pi))
    assert worst < lam
    assert lam / worst > 100
    # plant: C_rho/1e4 gives a bound below the measured remainder
    with R.prec():
        planted = R.up(-(1 - crho / 10**4 / p.sqrt()).log())
    assert planted < worst


# ---------------------------------------------------------------------------
# the algebra the chain takes from Holland: (75), (76), (78), (86), (90), V_m
# ---------------------------------------------------------------------------


def test_holland_86_90_and_V_m_in_exact_rationals():
    import sympy as sp

    y = sp.symbols("y")
    A, B, C, D = sp.Rational(1013, 7), sp.Rational(311, 5), sp.Rational(203, 3), sp.Rational(150)
    d = 5
    p = sum(sp.rf(-d, j) * sp.rf(A, j) * sp.rf(C, j) / (sp.rf(B, j) * sp.rf(D, j) * sp.factorial(j))
            * (D * y / (A * C)) ** j for j in range(d + 1))

    def E(f):
        return y * sp.diff(f, y)

    def J(f):
        return y * (1 - y / A) * sp.diff(f, y, 2) + (B - y + (d - 1) * y / A) * sp.diff(f, y) + d * f

    cubic = E(E(E(p) + A * p) - d * (E(p) + A * p))
    assert sp.expand(E(J(p)) + D * J(p) + (C - D) / C / A * cubic) == 0  # (86)
    # a planted sign of eps_p must break it
    assert sp.expand(E(J(p)) + D * J(p) - (C - D) / C / A * cubic) != 0

    def T(k):
        return y**k * sp.diff(p, y, k) / p if k <= d else sp.Integer(0)

    y0 = sp.Rational(7, 3)
    for m in range(d + 1):
        Vm = y**m / (A * p) * sp.diff(cubic, y, m)
        bm = A * (2 * m + 1 - d) - d * (2 * m + 1) + 3 * m**2 + 3 * m + 1
        gm = m * (m - d) * (m + A)
        claim = (T(m + 3) + (A - d + 3 + 3 * m) * T(m + 2) + bm * T(m + 1) + gm * T(m)) / A
        assert sp.simplify((Vm - claim).subs(y, y0)) == 0
        Um = y**m * sp.diff(J(p), y, m) / p
        r90 = (1 - y / A) * T(m + 2) + (B + m - y + (d - 1 - 2 * m) * y / A) * T(m + 1) \
            + (d - m) * (1 + m / A) * y * T(m)
        assert sp.simplify((y * Um - r90).subs(y, y0)) == 0


def test_holland_78_identity():
    import sympy as sp

    H, V, k, d = sp.symbols("H V k d")
    U = H + d + 1
    lhs = U * (H * (V + 2 * k) + 2 * k * (k + 1)) - V * (H + 2 * k) * (H + 2 * k + 2)
    assert sp.expand(lhs - (2 * k * (k + H + 1) * (U - 2 * V) + V * H * (d - 1))) == 0


@pytest.mark.parametrize("U,V,d", [(5405, 400, 10), (900, 400, 12)])
def test_jacobi_matrix_eigenvalues_are_the_roots(U, V, d):
    with mp.workdps(50):
        H, al, be = U - d - 1, V - 1, U - V - d
        M = mp.zeros(d, d)
        for k in range(d):
            M[k, k] = mp.mpf(U) * (H * (V + 2 * k) + 2 * k * (k + 1)) / ((H + 2 * k) * (H + 2 * k + 2))
            if k:
                M[k, k - 1] = M[k - 1, k] = mp.mpf(U) / (2 * k + H) * mp.sqrt(
                    mp.mpf(k * (k + al) * (k + be) * (k + H)) / ((2 * k + H - 1) * (2 * k + H + 1)))
        ev = sorted(mp.re(x) for x in mp.eig(M)[0])
        c = [mp.rf(-d, j) * mp.rf(U, j) / (mp.rf(V, j) * mp.factorial(j) * mp.mpf(U) ** j) for j in range(d + 1)]
        roots = sorted(mp.re(r) for r in mp.polyroots(c[::-1], maxsteps=200, extraprec=200))
        assert max(abs(a - b) / b for a, b in zip(ev, roots)) < mp.mpf(10) ** -30


# ---------------------------------------------------------------------------
# the matching systems are Holland's (52): checked against a direct solve on real data
# ---------------------------------------------------------------------------


def _h_values(n, count, dps):
    with mp.workdps(dps):
        a = mp.mpf(9) / 4

        def alpha(v):
            return mp.fsum((k**4 - 3 / (2 * mp.pi) * k**2 * mp.exp(-v)) * mp.exp(-mp.pi * (k * k - 1) * mp.exp(v))
                           for k in range(1, 6))

        def logI(s):
            v = mp.log(s / mp.log(s))
            for _ in range(100):
                v -= (v * (mp.pi * mp.exp(v) - a) - s) / (mp.pi * mp.exp(v) * (1 + v) - a)
            phi0 = s * mp.log(v) + a * v - mp.pi * mp.exp(v)
            w = 1 / mp.sqrt(s / v**2 + s / v + a)
            f = lambda t: mp.exp(s * mp.log(t) + a * t - mp.pi * mp.exp(t) - phi0) * alpha(t)  # noqa: E731
            pts = [mp.mpf("1e-30"), v / 2] + [v + k * w for k in range(-60, 61, 4)] + [v + 2, v + 6]
            return phi0 + mp.log(mp.quad(f, pts))

        return [mp.log(2 * mp.pi**2) - (2 * (n + j) + 1) * mp.log(4) + logI(2 * mp.mpf(n + j)) for j in range(count)]


@pytest.mark.parametrize("model", [5, 6])
def test_matching_system_is_hollands_52(model):
    n = mp.mpf(1000)
    with mp.workdps(50):
        H = _h_values(n, model + 2, 50)
        lg = [mp.loggamma(n + j + 1) + H[j] - mp.loggamma(2 * n + 2 * j + 1) for j in range(model + 2)]
        q = [mp.exp(2 * lg[k + 1] - lg[k] - lg[k + 2]) for k in range(model - 2)]
        tau = [(-1) ** j * n ** (j + 1) / mp.factorial(j)
               * mp.fsum((-1) ** (j + 2 - i) * mp.binomial(j + 2, i) * H[i] for i in range(j + 3))
               for j in range(model - 2)]
        eps = tau[0]
        t = [tj / eps - 1 for tj in tau]
        wb = n / (n + mp.mpf(1) / 2)

        def U(j, w):
            return mp.quad(lambda x: (j + 1) * x**j / mp.fprod([1 + i * x / n for i in range(1, j + 2)]), [0, w])

        def qq(k, U_, V_):
            return (U_ + k) * (V_ + k + 1) / ((V_ + k) * (U_ + k + 1))

        if model == 5:
            def Phi(g0, gb, gc):
                wA, wB, wC = eps * g0, wb - eps * gb, 2 - eps * gc
                return [(U(j, wA) + U(j, wb) - U(j, wB) + U(j, wC) - U(j, 2)) / eps - (1 + t[j]) for j in range(3)]

            g0, gb, gc = mp.findroot(Phi, (mp.mpf(5) / 12, mp.mpf(2) / 3, mp.mpf(1) / 12))
            A, B, C, D = n / (eps * g0), n / (wb - eps * gb), n / (2 - eps * gc), n / 2
        else:
            def Phi(g0, gx, g1, x):
                wA, wB, wC, wD = eps * g0, x - eps * gx / 2, x + eps * gx / 2, 1 - eps * g1
                return [(U(j, wA) + U(j, wC) - U(j, wB) + U(j, wb) - U(j, wD)) / eps - (1 + t[j]) for j in range(4)]

            g0, gx, g1, x = mp.findroot(Phi, (mp.mpf(1) / 6, mp.mpf(2) / 3, mp.mpf(1) / 6, mp.mpf(1) / 2))
            A, B, C, D = n / (eps * g0), n / (x - eps * gx / 2), n / (x + eps * gx / 2), n / (1 - eps * g1)
        for k in range(model - 2):
            assert abs(qq(k, A, B) * qq(k, C, D) / q[k] - 1) < mp.mpf(10) ** -40


# ---------------------------------------------------------------------------
# the four constants, recomputed over full covers, and plants that must turn red
# ---------------------------------------------------------------------------


@pytest.mark.parametrize("name", ["5a", "6a"])
def test_assisted_constants_reproduce(name):
    r = R.run_variant(name)
    assert r["green"], (r["fails"][:3], r["agg"])
    assert r["agg"]["K_req"] < float(R.VARIANTS[name]["K"])


@pytest.mark.parametrize("name", ["5s", "6s"])
def test_standalone_constants_reproduce(name):
    r = R.run_variant(name, step=Fraction(5, 10**4))
    assert r["green"], (r["fails"][:3], r["agg"])
    assert r["absorption"] <= float(R.VARIANTS[name]["K"])


def test_five_assisted_numbers_match_the_claims():
    r = R.run_variant("5a")
    agg = r["agg"]
    assert agg["C_loc"] <= 2.094 and agg["abt"] <= 0.997 and agg["Theta5"] <= 1.034
    assert agg["C_E"] <= 354.1 and agg["K_req"] <= 17710


def test_plants_turn_this_reproduction_red():
    # K just below the recomputed requirement
    r = R.run_variant("5a")
    bad = R.run_variant("5a", K=Fraction(int(r["agg"]["K_req"] * 0.999)))
    assert not bad["green"]
    # K_6 lowered by 0.01: the closing condition a + b + theta < 1 fails
    assert not R.run_variant("5a", K6=Fraction("2.52"))["green"]
    # K' just below the recomputed requirement
    r6 = R.run_variant("6a")
    assert not R.run_variant("6a", K=Fraction(int(r6["agg"]["K_req"] * 0.999)))["green"]
    # a standalone K below the absorption constant
    assert not R.run_variant("5s", K=Fraction("9.08e19"), step=Fraction(5, 10**4))["green"]
    # a chain start below the Laplace threshold R_min >= 10
    with R.prec():
        assert not all(R.laplace(400000)["conds"].values())


def test_gorttw_hand_off_and_the_c_equals_one_remark():
    assert R.gorttw_threshold_ok(5, 17900, Fraction("9.91e33"))
    assert R.gorttw_threshold_ok(6, Fraction("7.21e9"), Fraction("5.65e35"))
    # a planted threshold far above n_min must fail
    assert not R.gorttw_threshold_ok(5, 17900, Fraction("2e35"))
    with R.prec():
        d = R.Q(R.D_GORTTW)
        # d > 9.36e20 and n >= e^(d/2): n^3 log^2(n+2) >= e^(3d/2) (d/2)^2 >= 17900 d^5
        assert R.certainly(3 * d / 2 > (R.Q(71600) * d**3).log())
