"""Tests for kernel/: every number stated in RESULTS.md is asserted here.

Run from the worktree root:
    PYTHONPATH=$PWD <venv python> -m pytest -q -n 2 hunts/weil_propagation/c4_s2/kernel

Tolerances are set from deviations measured at the stated dps (RESULTS.md s6),
with at least three orders of headroom, never asserted a priori.
Printed values of Connes-Consani arXiv:2006.13771 (CC) are compared at half a
unit of their last printed digit.
"""

from __future__ import annotations

import json
import sys
from pathlib import Path

import pytest
from mpmath import mp

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]
sys.path.insert(0, str(HERE))
sys.path.insert(0, str(ROOT / "hunts" / "rogue_frontier" / "weil_trunc"))

import calibrate as C  # noqa: E402
import sonin as S  # noqa: E402

J40 = HERE / "cells_dps40.json"
J60 = HERE / "cells_dps60.json"


def _load(p):
    return json.loads(p.read_text())


def _half_ulp(printed: str):
    """Half a unit of the last printed digit of a CC value."""
    s = printed.lstrip("-")
    if "e" in s:
        mant, ex = s.split("e")
        dec = len(mant.split(".")[1]) if "." in mant else 0
        return mp.mpf(10) ** (int(ex) - dec) / 2
    dec = len(s.split(".")[1]) if "." in s else 0
    return mp.mpf(10) ** (-dec) / 2


def _phi(d, n, x):
    """phi~_n(x) from its Legendre coefficients (three-term recurrence)."""
    ks, coef = d["ks"], d["coef"][n]
    kmax = ks[-1]
    P = [mp.mpf(1), x]
    for k in range(1, kmax):
        P.append(((2 * k + 1) * x * P[k] - k * P[k - 1]) / (k + 1))
    return mp.fsum(cf * P[k] for k, cf in zip(ks, coef))


def _phi_all(d, x, nn):
    """[phi~_n(x), n < nn] with one Legendre recurrence."""
    ks = d["ks"]
    P = [mp.mpf(1), x]
    for k in range(1, ks[-1]):
        P.append(((2 * k + 1) * x * P[k] - k * P[k - 1]) / (k + 1))
    Pk = [P[k] for k in ks]
    return [mp.fsum(cf * pk for cf, pk in zip(d["coef"][n], Pk)) for n in range(nn)]


# ---------------------------------------------------------------------------
# 1. prolate data against the source (CC s4, Lemma 5.4, Rem 4.6, footnote 7)
# ---------------------------------------------------------------------------

CC_LAM = ["0.999971", "-0.979485", "0.524086", "-0.0589766", "0.00273233", "-0.0000762914"]
CC_T = ["11.9719", "8.77574", "2.20528", "0.0433983", "0.000125459"]


def test_prolate_eigenvalues_match_cc_list():
    d = S.prolate_data(40)
    with mp.workdps(40):
        for got, pr in zip(d["lam"], CC_LAM):
            assert abs(got - mp.mpf(pr)) <= _half_ulp(pr)


def test_sum_lam2_equals_delta_at_1_closed_form():
    """CC Rem 4.6: delta(1) = 2(Si(4 pi)/(4 pi) + 1) = sum lam_n^2 (even)."""
    d = S.prolate_data(40)
    with mp.workdps(40):
        lhs = mp.fsum(x**2 for x in d["lam"])
        rhs = 2 * (mp.si(4 * mp.pi) / (4 * mp.pi) + 1)
        assert abs(lhs - rhs) < mp.mpf(10) ** -35
        assert mp.nstr(lhs, 10) == "2.237484835"


def test_even_plus_odd_sum_is_4():
    """CC footnote 7: including the odd prolates the sum of squares is 4."""
    d0, d1 = S.prolate_data(40, 0), S.prolate_data(40, 1)
    with mp.workdps(40):
        tot = mp.fsum(x**2 for x in d0["lam"]) + mp.fsum(x**2 for x in d1["lam"])
        assert abs(tot - 4) < mp.mpf(10) ** -35


def test_edge_terms_and_eps_derivative_match_cc():
    """CC Lemma 5.4: t(n) = lam^2/(1-lam^2) xi_n(1)^2 and eps'(1+) ~ 22.9965."""
    d = S.prolate_data(40)
    with mp.workdps(40):
        for (vn, en), pr in zip(zip(d["v"], d["edge"]), CC_T):
            assert abs(vn * en**2 - mp.mpf(pr)) <= _half_ulp(pr)
    e_series = S.eps_right_derivative_at_1(40, 0, "series")
    e_split = S.eps_right_derivative_at_1(40, 0, "split")
    assert abs(e_series - mp.mpf("22.9965")) <= _half_ulp("22.9965")
    # two routes: CC's series vs derivative of this module's split
    assert abs(e_series - e_split) < mp.mpf(10) ** -30


def test_eigen_relation_68_by_direct_quadrature():
    """int_{-1}^1 phi~_n(x) cos(2 pi x w) dx = lam_n phi~_n(w), inside and outside [-1,1];
    the Taylor data e_nj reproduce the same eta_n."""
    d = S.prolate_data(40)
    with mp.workdps(45):
        for n in range(4):
            for w in (mp.mpf("0.7"), mp.mpf(2)):
                lhs = mp.quad(lambda x: _phi(d, n, x) * mp.cos(2 * mp.pi * x * w), [-1, 0, 1])
                rhs = d["lam"][n] * _phi(d, n, w)
                tay = mp.fsum(e * w ** (2 * j) for j, e in enumerate(d["e"][n]))
                assert abs(lhs - rhs) < mp.mpf(10) ** -30
                assert abs(lhs - tay) < mp.mpf(10) ** -30


def test_completeness_part_is_delta_closed_form():
    """sum_n int_0^1 eta_n(t) eta_n(y t) dt (prolate Taylor data) = A0(y), and
    rho^{1/2} A0(rho) = delta(rho) of CC eq. (49)."""
    d = S.prolate_data(40)
    with mp.workdps(60):
        for y in (mp.mpf("0.5"), mp.mpf("1.3"), mp.mpf("2.7")):
            ser = mp.fsum(
                d["e"][n][j] * d["e"][n][l] * y ** (2 * l) / (2 * j + 2 * l + 1)
                for n in range(d["n_max"])
                for j in range(d["J"])
                for l in range(d["J"])
            )
            assert abs(ser - S._A0(y)) < mp.mpf(10) ** -30
        for r in ("1.3", "2.2"):
            rho = mp.mpf(r)
            closed = 2 * mp.sqrt(rho) * (
                mp.si(2 * mp.pi * (1 + rho)) / (2 * mp.pi * (1 + rho))
                + mp.si(2 * mp.pi * (rho - 1)) / (2 * mp.pi * (rho - 1))
            )
            assert abs(S.delta(rho, 40) - closed) < mp.mpf(10) ** -35


def test_eps_basic_properties():
    """eps(1) = 0, eps(1/rho) = eps(rho), and eps(rho) = sum_n v_n rho^{1/2}
    int_{1/rho}^1 phi~ phi~(rho .) (CC Lemma 5.4 proof) by direct quadrature."""
    assert abs(S.eps(1, 40)) < mp.mpf(10) ** -35
    assert abs(S.eps(mp.mpf("1.7"), 40) - S.eps(1 / mp.mpf("1.7"), 40)) < mp.mpf(10) ** -35
    d = S.prolate_data(40)
    rho = mp.mpf("1.6")
    from mpmath.calculus.quadrature import GaussLegendre

    with mp.workdps(45):
        nodes = GaussLegendre(mp).calc_nodes(6, mp.prec)
        a, b = 1 / rho, mp.mpf(1)
        xs = [(b - a) / 2 * (1 + t) + a for t, _ in nodes]
        ws = [(b - a) / 2 * w for _, w in nodes]
        n_max = d["n_max"]
        p1 = [_phi_all(d, x, n_max) for x in xs]
        p2 = [_phi_all(d, rho * x, n_max) for x in xs]
        direct = mp.sqrt(rho) * mp.fsum(
            d["v"][n] * mp.fsum(w * f1[n] * f2[n] for w, f1, f2 in zip(ws, p1, p2)) for n in range(n_max)
        )
        assert abs(direct - S.eps(rho, 40)) < mp.mpf(10) ** -30


# ---------------------------------------------------------------------------
# 2. Galerkin blocks: independent routes agree
# ---------------------------------------------------------------------------


@pytest.mark.parametrize("c", ["1.5", "2.5"])
def test_arch_block_matches_ccm_closed_forms(c):
    import galerkin as G

    N, dps = 8, 40
    c = mp.mpf(c)
    win = S.Window(c, N, dps)
    A = S.arch_matrix(c, N, dps, 0, win)
    with mp.workdps(dps):
        tr = G.Truncation(c, N)
        L = mp.log(c)

        def wp(n, m):
            tot = mp.mpf(0)
            for q, p in G.prime_powers_upto(float(c)):
                y = mp.log(q)
                w = mp.log(p) / mp.sqrt(q)
                if n == m:
                    qq = 2 * (1 - y / L) * mp.cos(2 * mp.pi * n * y / L)
                else:
                    qq = (mp.sin(2 * mp.pi * m * y / L) - mp.sin(2 * mp.pi * n * y / L)) / (mp.pi * (n - m))
                tot += w * qq
            return tot

        dev = max(
            abs(tr.entry(i - N, j - N) - tr.w02(i - N, j - N) + wp(i - N, j - N) - A[i, j])
            for i in range(2 * N + 1)
            for j in range(2 * N + 1)
        )
    assert dev < mp.mpf(10) ** -36  # measured 1.6e-40


def test_arch_block_matches_theory_s0_formula_verbatim():
    """A(f) for F = U_0 (g(x) = 1 - |x|/L) from theory RESULTS s0 by mp.quad."""
    c, N, dps = mp.mpf("2.2"), 8, 40
    A = S.arch_matrix(c, N, dps)
    with mp.workdps(50):
        L = mp.log(c)
        const = mp.euler + mp.log(mp.pi) + mp.log(1 - mp.exp(-2 * L))
        g = lambda x: 1 - x / L  # noqa: E731
        integ = mp.quad(
            lambda x: 2 * (mp.exp(-2 * x) * g(0) - mp.exp(-x / 2) * g(x)) / (1 - mp.exp(-2 * x)), [0, L]
        )
        val = -const * g(0) + integ
        assert abs(val - A[N, N]) < mp.mpf(10) ** -35


def test_odd_arch_block_matches_dh_route_and_sech_identity():
    """parity 1 (a = 3/4) equals weil_trunc's DH archimedean block minus log 5,
    and A_odd - A_even = int g(x) / (2 cosh(x/2)) dx (CC tau with sin kernel)."""
    import galerkin as G

    c, N, dps = mp.mpf("1.5"), 8, 40
    win = S.Window(c, N, dps)
    A1 = S.arch_matrix(c, N, dps, 1, win)
    A0 = S.arch_matrix(c, N, dps, 0, win)
    with mp.workdps(dps + S.GUARD):
        s, d = win.moments(lambda x: 1 / (2 * mp.cosh(x / 2)))
        M = S.form_from_moments(s, d, N)
    with mp.workdps(dps):
        tr = G.Truncation(c, N, kind="dh")
        dev = max(
            abs(tr.entry(i - N, j - N) - (mp.log(5) if i == j else 0) - A1[i, j])
            for i in range(2 * N + 1)
            for j in range(2 * N + 1)
        )
        dev2 = max(abs(A1[i, j] - A0[i, j] - M[i, j]) for i in range(2 * N + 1) for j in range(2 * N + 1))
    assert dev < mp.mpf(10) ** -36
    assert dev2 < mp.mpf(10) ** -36


def test_pole_block_matches_w02():
    import galerkin as G

    c, N, dps = mp.mpf("2.9"), 8, 40
    P = S.pole_matrix(c, N, dps)
    with mp.workdps(dps):
        tr = G.Truncation(c, N)
        dev = max(abs(tr.w02(i - N, j - N) - P[i, j]) for i in range(2 * N + 1) for j in range(2 * N + 1))
    assert dev < mp.mpf(10) ** -36


@pytest.mark.parametrize("c", ["1.5", "2.9"])
def test_quadrature_rule_by_doubling(c):
    """Moments of E and A with 192 and 384 Gauss nodes agree (N = 16, dps 40)."""
    c = mp.mpf(c)
    N, dps = 16, 40
    w7, w8 = S.Window(c, N, dps, deg=7), S.Window(c, N, dps, deg=8)
    data = S.prolate_data(dps)
    with mp.workdps(dps + S.GUARD):
        for fn in (lambda w: w.moments(lambda x: S._eps_x(x, data)), lambda w: S._arch_moments(w, 0)):
            s7, d7 = fn(w7)
            s8, d8 = fn(w8)
            dev = max(max(abs(a - b) for a, b in zip(s7, s8)), max(abs(a - b) for a, b in zip(d7, d8)))
            assert dev < mp.mpf(10) ** -40


def test_T_inf_matrix_interface():
    """Shape, symmetry, index convention (reflection n -> -n), Gamma_C = even + odd."""
    c, N, dps = mp.mpf("2.5"), 8, 40
    T = S.T_inf_matrix(c, N, dps)
    TC = S.T_inf_matrix(c, N, dps, arch_type="C")
    To = S.T_inf_matrix(c, N, dps, arch_type="R_odd")
    assert T.rows == T.cols == 2 * N + 1
    with mp.workdps(dps):
        for i in range(2 * N + 1):
            for j in range(2 * N + 1):
                assert abs(T[i, j] - T[j, i]) == 0
                assert abs(T[i, j] - T[2 * N - i, 2 * N - j]) < mp.mpf(10) ** -38
                assert abs(TC[i, j] - T[i, j] - To[i, j]) < mp.mpf(10) ** -38


# ---------------------------------------------------------------------------
# 3. positivity statements of the source, measured at N = 8, 16 (dps 40)
# ---------------------------------------------------------------------------


@pytest.mark.parametrize("c", ["1.5", "1.9", "2.0", "2.2", "2.5", "2.9"])
def test_T_inf_psd_and_D_minus_E_psd(c):
    """CC Thm 4.7 (T = A + E >= 0), Cor 2.3 (A + D >= 0), eq. (90) (D - E >= 0)."""
    c = mp.mpf(c)
    N, dps = 16, 40
    win = S.Window(c, N, dps)
    for p in (0, 1):
        with mp.workdps(dps + S.GUARD):
            A, _, _ = S.arch_matrix(c, N, dps, p, win, raw=True)
            E, _, _ = S.eps_matrix(c, N, dps, p, win, raw=True)
            D, _, _ = S.delta_matrix(c, N, dps, p, win, raw=True)
        with mp.workdps(dps):
            for M in (A + E, A + D, D - E):
                assert min(mp.eigsy(+M, eigvals_only=True)) > mp.mpf(10) ** -6


# ---------------------------------------------------------------------------
# 4. the JSON cells: stated numbers, recomputation, precision response
# ---------------------------------------------------------------------------


def _v(x):
    return mp.mpf(x)


@pytest.fixture(scope="module")
def j40():
    return _load(J40)


@pytest.fixture(scope="module")
def j60():
    return _load(J60)


def test_json_recompute_N8(j40):
    """analyze_cell at N = 8, dps 40 reproduces the stored cells."""
    for grp in ("calibration", "mission"):
        for c, cell in j40[grp].items():
            o = C.analyze_cell(mp.mpf(c), 8, 40)
            st = cell["8"]
            with mp.workdps(40):
                for key in ("T_low", "R_full_low", "R_C1_low", "R_C2_low", "K_top"):
                    for a, b in zip(o[key], st[key]):
                        assert abs(a - _v(b)) < mp.mpf(10) ** -30
                for key in ("T_inertia", "R_full_inertia", "R_C1_inertia", "R_C2_inertia"):
                    assert o[key] == st[key]


def test_precision_response_40_vs_60(j40, j60):
    """Every eigenvalue and constant agrees between dps 40 and 60 (measured, RESULTS s6)."""
    worst = mp.mpf(0)
    for grp in ("calibration", "mission"):
        for c in j40[grp]:
            for N in ("8", "16", "32"):
                a, b = j40[grp][c][N], j60[grp][c][N]
                for key in ("T_low", "R_full_low", "R_C1_low", "R_C2_low", "K_top"):
                    for x, y in zip(a[key], b[key]):
                        worst = max(worst, abs(_v(x) - _v(y)))
                for key in ("cstar", "thm611_low"):
                    if a[key] is not None:
                        worst = max(worst, abs(_v(a[key]) - _v(b[key])))
                for key in ("T_inertia", "R_full_inertia", "R_C1_inertia", "R_C2_inertia"):
                    assert a[key] == b[key]
    assert worst < mp.mpf(10) ** -35


def test_calibration_statements(j40):
    """The calibration claims of RESULTS s3, read from the dps-40 cells."""
    cal = j40["calibration"]
    c0 = C.C0_THM611()
    for c in ("1.5", "1.9", "2.0"):
        for N in ("8", "16", "32"):
            cell = cal[c][N]
            assert cell["T_inertia"][0] == 0  # Thm 4.7
            assert cell["R_C2_inertia"][0] == 0  # Thm 1 / eq. (4)
            assert _v(cell["thm611_low"]) > 0  # Thm 6.11 with c0 = 4 gamma / log 2
            assert _v(cell["cstar"]) < c0
            assert _v(cell["K_top"][0]) < mp.mpf("1.05158") + mp.mpf("0.00122")
    # c = 1.5: R_inf >= 0 already on the full space; lam_max(K) < 1
    for N in ("8", "16", "32"):
        assert cal["1.5"][N]["R_full_inertia"][0] == 0
        assert _v(cal["1.5"][N]["K_top"][0]) < 1
        for c in ("1.9", "2.0"):
            assert cal[c][N]["R_C1_inertia"][0] == 1
            assert cal[c][N]["R_full_inertia"][0] == 2
            assert _v(cal[c][N]["K_top"][0]) > 1
    # c = 2 is the Thm 6.11 window: monotone Galerkin lower bounds
    k = [_v(cal["2.0"][N]["K_top"][0]) for N in ("8", "16", "32")]
    k2 = [_v(cal["2.0"][N]["K_top"][1]) for N in ("8", "16", "32")]
    cs = [_v(cal["2.0"][N]["cstar"]) for N in ("8", "16", "32")]
    assert k[0] < k[1] < k[2] and k2[0] < k2[1] < k2[2] and cs[0] < cs[1] < cs[2]
    assert 13 < cs[1] and 13 < cs[2]
    assert mp.nstr(k[2], 6) == "1.04881"
    assert mp.nstr(k2[2], 6) == "0.679248"
    assert mp.nstr(cs[2], 6) == "14.5566"
    # first-order (1/N) Richardson from N = 16, 32: a measured heuristic
    assert abs((2 * k[2] - k[1]) - mp.mpf("1.05158")) < mp.mpf("0.0002")
    assert mp.nstr(2 * cs[2] - cs[1], 5) == "15.236"


def test_mission_cell_statements(j40):
    mis = j40["mission"]
    expect = {"2.2": (2, 1, 0), "2.5": (2, 1, 0), "2.9": (2, 2, 1)}
    for c, (nf, n1, n2) in expect.items():
        for N in ("8", "16", "32"):
            cell = mis[c][N]
            assert cell["T_inertia"][0] == 0
            assert cell["R_full_inertia"][0] == nf
            assert cell["R_C1_inertia"][0] == n1
            assert cell["R_C2_inertia"][0] == n2
            assert _v(cell["thm611_low"]) < 0  # outside the support of Thm 6.11
            assert (cell["cstar"] is None) == (n2 > 0)


def test_json_moments_rebuild_T_inf(j40):
    """The stored generating sequences rebuild T_inf_matrix (N = 16)."""
    N, dps = 16, 40
    for c in ("2.2", "2.9"):
        m = j40["moments"][c]
        with mp.workdps(dps):
            sA = [_v(x) for x in m["A_even"]["s"][: N + 1]]
            dA = [_v(x) for x in m["A_even"]["d"][: N + 1]]
            sE = [_v(x) for x in m["E_even"]["s"][: N + 1]]
            dE = [_v(x) for x in m["E_even"]["d"][: N + 1]]
            M = S.form_from_moments([a + b for a, b in zip(sA, sE)], [a + b for a, b in zip(dA, dE)], N)
        T = S.T_inf_matrix(mp.mpf(c), N, dps)
        with mp.workdps(dps):
            dev = max(abs(M[i, j] - T[i, j]) for i in range(2 * N + 1) for j in range(2 * N + 1))
        assert dev < mp.mpf(10) ** -36


@pytest.mark.slow
def test_json_recompute_N32_c2(j40):
    o = C.analyze_cell(mp.mpf("2.0"), 32, 40)
    st = j40["calibration"]["2.0"]["32"]
    with mp.workdps(40):
        for key in ("T_low", "R_C1_low", "K_top"):
            for a, b in zip(o[key], st[key]):
                assert abs(a - _v(b)) < mp.mpf(10) ** -30
        assert abs(o["cstar"] - _v(st["cstar"])) < mp.mpf(10) ** -30


# ---------------------------------------------------------------------------
# 5. S_inf as a projection (the representation two_adic/ composes with)
# ---------------------------------------------------------------------------


def test_eta_bessel_route_matches_taylor_route():
    d = S.prolate_data(40)
    with mp.workdps(40):
        for s_ in ("0.7", "1.5", "2.5"):
            s = mp.mpf(s_)
            eb = S.eta_all(s, 40)
            et = [mp.fsum(e * s ** (2 * j) for j, e in enumerate(d["e"][n])) for n in range(d["n_max"])]
            assert max(abs(a - b) for a, b in zip(eb, et)) < mp.mpf(10) ** -34  # measured 2.4e-36


def test_projection_maps_into_sonin_space():
    """For v = 1_[1,1.5]: S v = v - sum_k <zeta_k|v> zeta_k vanishes on [-1,1] by
    construction, and its Fourier transform must vanish on [-1,1]:
    F(Sv)(w) = Fv(w) - sum_k (int_1^1.5 eta_k) phi~_k(w), |w| <= 1."""
    from mpmath.calculus.quadrature import GaussLegendre

    with mp.workdps(40 + S.GUARD):
        nodes = GaussLegendre(mp).calc_nodes(6, mp.prec)
        a, b = mp.mpf(1), mp.mpf("1.5")
        xs = [(b - a) / 2 * (1 + t) + a for t, _ in nodes]
        ws = [(b - a) / 2 * w for _, w in nodes]
        ets = [S.eta_all(x, 40, 0, 40) for x in xs]
        coeff = [mp.fsum(w * e[k] for w, e in zip(ws, ets)) for k in range(40)]
        worst = mp.mpf(0)
        for w_ in ("0", "0.3", "0.7", "1"):
            w = mp.mpf(w_)
            Fv = mp.mpf(1) if w == 0 else (mp.sin(3 * mp.pi * w) - mp.sin(2 * mp.pi * w)) / (mp.pi * w)
            if w == 0:
                Fv = 2 * (b - a)
            rest = mp.fsum(coeff[k] * S.phi_tilde(k, w, 40) for k in range(40))
            worst = max(worst, abs(Fv - rest))
    assert worst < mp.mpf(10) ** -35


def test_window_projection_matrix():
    """<V_m|S_inf|V_n> on [c^-1/2, c^1/2]: Hermitian, spectrum in [0, 1],
    truncation tail below 10^-45; on [1, c] the step part is the identity."""
    Sv, K, tail = S.S_inf_window_matrix(mp.mpf("2.5"), 8, 40)
    with mp.workdps(40):
        ev = mp.eighe(Sv, eigvals_only=True)
        assert min(ev) > -mp.mpf(10) ** -30 and max(ev) < 1 + mp.mpf(10) ** -30
        assert tail < mp.mpf(10) ** -45
        assert K == 20
        dim = Sv.rows
        assert max(abs(Sv[i, j] - mp.conj(Sv[j, i])) for i in range(dim) for j in range(dim)) < mp.mpf(10) ** -38
    S1, K1, _ = S.S_inf_window_matrix(mp.mpf("2.5"), 4, 40, u0=1)
    with mp.workdps(40):
        ev = mp.eighe(S1, eigvals_only=True)
        assert min(ev) > -mp.mpf(10) ** -30 and max(ev) < 1 + mp.mpf(10) ** -30


# ---------------------------------------------------------------------------
# 6. every number quoted in RESULTS.md and INTERFACE.md
# ---------------------------------------------------------------------------


def _get(j, path):
    x = j
    for k in path:
        x = x[k] if not isinstance(x, list) else x[int(k)]
    return x


#: (json path, significant digits, stated string) for the dps-40 cells
QUOTED = [
    (("calibration", "2.0", "8", "K_top", 0), 7, "1.040345"),
    (("calibration", "2.0", "16", "K_top", 0), 7, "1.046028"),
    (("calibration", "2.0", "32", "K_top", 0), 7, "1.048814"),
    (("calibration", "2.0", "8", "K_top", 1), 7, "0.6578403"),
    (("calibration", "2.0", "16", "K_top", 1), 7, "0.6720548"),
    (("calibration", "2.0", "32", "K_top", 1), 7, "0.6792478"),
    (("calibration", "2.0", "8", "cstar"), 7, "12.42835"),
    (("calibration", "2.0", "16", "cstar"), 7, "13.87771"),
    (("calibration", "2.0", "32", "cstar"), 7, "14.55663"),
    (("calibration", "2.0", "8", "R_C1_low", 0), 7, "-0.06921652"),
    (("calibration", "2.0", "16", "R_C1_low", 0), 7, "-0.07804222"),
    (("calibration", "2.0", "32", "R_C1_low", 0), 7, "-0.08222624"),
    (("calibration", "1.5", "32", "T_low", 0), 7, "0.03772234"),
    (("calibration", "1.9", "32", "T_low", 0), 7, "0.003925064"),
    (("calibration", "2.0", "32", "T_low", 0), 7, "0.002550097"),
    (("calibration", "1.5", "8", "cstar"), 4, "-93.13"),
    (("calibration", "1.5", "16", "cstar"), 4, "-81.06"),
    (("calibration", "1.5", "32", "cstar"), 4, "-75.26"),
    (("calibration", "1.5", "8", "K_top", 0), 3, "0.807"),
    (("calibration", "1.5", "16", "K_top", 0), 3, "0.827"),
    (("calibration", "1.5", "32", "K_top", 0), 3, "0.837"),
    (("calibration", "1.5", "32", "R_C1_low", 0), 4, "0.0001871"),
    (("calibration", "1.9", "8", "R_C1_low", 0), 4, "-0.0282"),
    (("calibration", "1.9", "16", "R_C1_low", 0), 4, "-0.03582"),
    (("calibration", "1.9", "32", "R_C1_low", 0), 4, "-0.03931"),
    (("calibration", "1.9", "8", "cstar"), 4, "7.422"),
    (("calibration", "1.9", "16", "cstar"), 4, "9.51"),
    (("calibration", "1.9", "32", "cstar"), 4, "10.49"),
    (("calibration", "1.9", "8", "K_top", 0), 4, "1.023"),
    (("calibration", "1.9", "16", "K_top", 0), 4, "1.03"),
    (("calibration", "1.9", "32", "K_top", 0), 4, "1.033"),
    (("mission", "2.2", "32", "T_low", 0), 7, "0.001198416"),
    (("mission", "2.5", "32", "T_low", 0), 7, "0.0004740128"),
    (("mission", "2.9", "32", "T_low", 0), 7, "0.0001832311"),
    (("mission", "2.2", "32", "R_C1_low", 0), 7, "-0.1716829"),
    (("mission", "2.5", "32", "R_C1_low", 0), 7, "-0.2981016"),
    (("mission", "2.9", "32", "R_C1_low", 0), 7, "-0.4395782"),
    (("mission", "2.9", "32", "R_C1_low", 1), 7, "-0.01635431"),
    (("mission", "2.2", "32", "K_top", 0), 7, "1.068616"),
    (("mission", "2.2", "32", "K_top", 1), 6, "0.811608"),
    (("mission", "2.5", "32", "K_top", 0), 7, "1.082943"),
    (("mission", "2.5", "32", "K_top", 1), 7, "0.9320488"),
    (("mission", "2.9", "32", "K_top", 0), 6, "1.08903"),
    (("mission", "2.9", "32", "K_top", 1), 7, "1.022986"),
    (("prolate", "even", "eps1p_series"), 7, "22.99648"),
    (("prolate", "odd", "lam", 0), 5, "0.99878"),
    (("prolate", "odd", "lam", 1), 5, "-0.84956"),
    (("prolate", "odd", "lam", 2), 5, "0.2074"),
    (("prolate", "odd", "sum_lam2"), 10, "1.762515165"),
    (("prolate", "odd", "eps1p_series"), 7, "16.73365"),
]


def test_quoted_numbers(j40, j60):
    with mp.workdps(40):
        for path, digits, stated in QUOTED:
            assert mp.nstr(_v(_get(j40, path)), digits) == stated, path
        cal = j40["calibration"]["2.0"]
        k16, k32 = _v(cal["16"]["K_top"][0]), _v(cal["32"]["K_top"][0])
        c16, c32 = _v(cal["16"]["cstar"]), _v(cal["32"]["cstar"])
        assert mp.nstr(2 * k32 - k16, 6, strip_zeros=False) == "1.05160"
        assert mp.nstr(2 * c32 - c16, 5) == "15.236"
        assert mp.nstr(_v(j40["prolate"]["even"]["sum_lam2"]), 10) == "2.237484835"
        assert mp.nstr(_v(j40["prolate"]["odd"]["sum_lam2_closed"]), 10) == "1.762515165"
    pe40, pe60 = j40["prolate"]["even"], j60["prolate"]["even"]
    assert (pe40["n_max"], pe40["J"], pe40["K"], pe60["n_max"]) == (20, 74, 76, 23)
    assert j40["seconds_total"] == 215.5 and j60["seconds_total"] == 365.0
    # precision response: the worst deviation over all stored eigenvalues and constants
    worst = mp.mpf(0)
    with mp.workdps(70):
        for grp in ("calibration", "mission"):
            for c in j40[grp]:
                for N in ("8", "16", "32"):
                    a, b = j40[grp][c][N], j60[grp][c][N]
                    for key in ("T_low", "R_full_low", "R_C1_low", "R_C2_low", "K_top"):
                        for x, y in zip(a[key], b[key]):
                            worst = max(worst, abs(_v(x) - _v(y)))
                    for key in ("cstar", "thm611_low"):
                        if a[key] is not None:
                            worst = max(worst, abs(_v(a[key]) - _v(b[key])))
        assert mp.nstr(worst, 2) == "5.1e-39"


def test_interface_eta_table():
    """INTERFACE s3: |eta_n(X)| at dps 40, two significant digits."""
    table = {
        "sqrt3": ["2.6e-5", "1.0e-20", "9.2e-41", "8.9e-64", "5.5e-89"],
        "3": ["0.23", "1.2e-10", "3.9e-25", "1.1e-42", "1.7e-62"],
    }
    with mp.workdps(40):
        for key, row in table.items():
            X = mp.sqrt(3) if key == "sqrt3" else mp.mpf(3)
            et = S.eta_all(X, 40)
            got = [mp.nstr(abs(et[k]), 2, strip_zeros=False) for k in (10, 20, 30, 40, 50)]
            assert got == row, (key, got)


def test_zeta_mellin_closed_form():
    """zeta_mellin_all: (a) the moment recurrence R_k against quadrature,
    (b) the Tate constant on xi = 1_[0,1], (c) the full M_n(s) against a direct
    integral over [1, V] at s = 0.7 - 0.49i (Re z = 0.01, integrand ~ v^-2),
    whose error falls like V^-2 (measured 2e-4 at V = 30, 5e-5 at V = 60)."""
    from mpmath.calculus.quadrature import GaussLegendre

    dps = 30
    for par in (0, 1):
        pv = S.prolate_vectors(dps, par, 10)
        with mp.workdps(dps + 10):
            a = mp.mpc("0.3", "0.7")
            r = 1 / (a + 1) if par == 0 else 1 / (a + 2)
            R = []
            for k in pv["ks"]:
                R.append(r)
                r = r * (a - k) / (a + k + 3)
            for n in (0, 3, 7):
                I = mp.fsum(cf * x for cf, x in zip(pv["coef"][n], R))
                q = mp.quad(lambda x: S.phi_tilde(n, x, dps, par) * x**a, [0, 0.5, 1])
                assert abs(I - q) < mp.mpf(10) ** -38  # measured <= 1.2e-41
    with mp.workdps(40):
        z = mp.mpf("0.5") - 0.7j
        lhs = (1 / mp.pi) * mp.gamma(z - 1) * mp.sin(mp.pi * (z - 1) / 2) * (2 * mp.pi) ** (1 - z)
        rhs = 2 * mp.gamma(z) * mp.cos(mp.pi * z / 2) * (2 * mp.pi) ** (-z) / (1 - z)
        assert abs(lhs - rhs) < mp.mpf(10) ** -38
    dps = 20
    with mp.workdps(25):
        s = mp.mpc("0.7", "-0.49")
        M = S.zeta_mellin_all(s, dps, 0, 2)
        lam = S.prolate_data(dps, 0)["lam"]
        nodes = GaussLegendre(mp).calc_nodes(4, mp.prec)
        errs = {}
        for V in (30, 60):
            tot = [mp.mpc(0), mp.mpc(0)]
            for j in range(1, V):
                a_, b_ = mp.mpf(j), mp.mpf(j + 1)
                for tt, w in nodes:
                    v = (b_ - a_) / 2 * (1 + tt) + a_
                    e = S.eta_all(v, dps, 0, 2)
                    for n in (0, 1):
                        tot[n] += (b_ - a_) / 2 * w * e[n] * v ** (-0.5 - 1j * s)
            errs[V] = [abs(M[n] - tot[n] / mp.sqrt(1 - lam[n] ** 2)) for n in (0, 1)]
        for n in (0, 1):
            assert errs[60][n] < mp.mpf("1e-4")
            assert errs[60][n] < errs[30][n] / 3


def test_many_modes_orthonormal():
    """prolate_vectors(40, 0, 150): Gram matrix of phi~_n on [0, 1] is the
    identity to 10^-40 (spot checks across the range)."""
    pv = S.prolate_vectors(40, 0, 150)
    ks, c = pv["ks"], pv["coef"]
    with mp.workdps(60):

        def ip(a, b):
            return mp.fsum(x * y / (2 * k + 1) for x, y, k in zip(a, b, ks))

        for i, j in ((0, 0), (3, 100), (100, 100), (148, 149), (149, 149), (20, 21)):
            assert abs(ip(c[i], c[j]) - (1 if i == j else 0)) < mp.mpf(10) ** -40
