"""Tests of the checker's own Q (phase 1).

Tolerances are 10x a deviation measured at the stated dps (2026-09-23), not
asserted a priori; the measured value is quoted next to each.
"""

from __future__ import annotations

import json
import os
import sys

import pytest
from mpmath import mp

HERE = os.path.dirname(os.path.abspath(__file__))
WT = os.path.abspath(os.path.join(HERE, "..", "..", "..", "rogue_frontier", "weil_trunc"))
for p in (HERE, WT):
    if p not in sys.path:
        sys.path.insert(0, p)

import checker_props as CP  # noqa: E402
import checker_q as CQ  # noqa: E402

CELLS = ["2.2", "2.5", "2.9"]
CALIB = ["1.5", "1.9"]
JSON = os.path.join(HERE, "checker_q_cells.json")


def _json():
    with open(JSON) as fh:
        return json.load(fh)


# ---------------------------------------------------------------- arithmetic


def test_atoms_in_window():
    for c in CELLS:
        assert CQ.zeta_atoms(float(c)) == [(2, 2)]
    for c in CALIB:
        assert CQ.zeta_atoms(float(c)) == []
    assert CQ.zeta_atoms(2.0) == []  # log n < log c is strict
    assert [n for n, _ in CQ.zeta_atoms(10.5)] == [2, 3, 4, 5, 7, 8, 9]


# ---------------------------------------------------- the x -> 0 limit of A


@pytest.mark.parametrize("a,b", [(0, 0), (3, 3), (-5, -5), (1, 4), (-2, 7)])
def test_a_integrand_analytic_limit(a, b):
    """The rearranged integrand at x = 1e-30 equals the stated analytic limit
    to O(x); there is no 0/0 anywhere (module docstring)."""
    with mp.workdps(50):
        L = mp.log(mp.mpf("2.5"))
        wa, wb = 2 * mp.pi * a / L, 2 * mp.pi * b / L
        x = mp.mpf("1e-30")
        if a == b:
            w = lambda t: 2 * (1 - t / L) * mp.cos(wa * t)
            D = lambda t: 4 * mp.sin(wa * t / 2) ** 2 + (2 * t / L) * mp.cos(wa * t)
            lim = CQ.a_integrand_limit(L, "diag")
        else:
            w = lambda t: (mp.sin(wa * t) - mp.sin(wb * t)) / (mp.pi * (b - a))
            D = lambda t: -w(t)
            lim = CQ.a_integrand_limit(L, "off", a, b)
        # the next term is O(x (1 + w_a^2 + w_b^2)), from sin^2(w x / 2) / x
        assert abs(CQ.a_integrand(w, D, x) - lim) < 10 * x * (1 + wa * wa + wb * wb)


# ------------------------------------------------- oracle 1: CCM galerkin.py


@pytest.mark.parametrize("c", CALIB + CELLS)
def test_matches_ccm_galerkin_entrywise(c):
    """Measured max |Q - galerkin| at N = 6, dps 40: <= 3.8e-40 (all five c)."""
    import galerkin as G

    N = 6
    M = CQ.Q_matrix(c, N, 40)
    with mp.workdps(40):
        T = G.Truncation(mp.mpf(c), N)
        dev = max(abs(M[i, j] - T.entry(i - N, j - N)) for i in range(2 * N + 1) for j in range(2 * N + 1))
    assert dev < mp.mpf("4e-39")


def test_galerkin_dev_at_N32_pinned():
    """N = 32, dps 40, from the JSON (run_checker_q.py): <= 4e-39 at all c."""
    for c, rec in _json()["cells"].items():
        assert mp.mpf(rec["galerkin_maxdev_N32_dps40"]) < mp.mpf("4e-39"), c


def test_two_quadrature_routes_agree():
    """Gauss-Legendre (shared nodes) against tanh-sinh per entry, N = 4."""
    a = CQ.q_parts("2.5", 4, 40, method="gl")["Q"]
    b = CQ.q_parts("2.5", 4, 40, method="ts")["Q"]
    assert CP.entry_drift(a, b) < mp.mpf("1e-38")


def test_quadrature_error_estimate_pinned():
    """Degree 5 against degree 6 Gauss-Legendre, N = 32, dps 40: <= 1.1e-50."""
    for c, rec in _json()["cells"].items():
        assert mp.mpf(rec["quad_err_dps40"]) < mp.mpf("1e-45"), c


# ------------------------------------------- oracle 2: zeta.weil, two families


def _bump(c, p, dps):
    """f(y) = sin^{2p}(pi y / L) on [0, L]: in the span of U_{-p..p}.
    Returns (h, g, v) with h = |f-hat|^2 in closed form, g by quadrature."""
    with mp.workdps(dps + 10):
        L = mp.log(mp.mpf(c))
        om = 2 * mp.pi / L
        a = [mp.binomial(2 * p, p) / mp.mpf(4) ** p]
        a += [2 * (-1) ** j * mp.binomial(2 * p, p - j) / mp.mpf(4) ** p for j in range(1, p + 1)]
        v = mp.matrix(2 * p + 1, 1)
        for n in range(-p, p + 1):
            v[n + p] = mp.sqrt(L) * (a[0] if n == 0 else a[abs(n)] / 2)

    def S(r):
        return a[0] / r + mp.fsum(a[j] * r / (r * r - (j * om) ** 2) for j in range(1, p + 1))

    def h(r):
        if r == 0:
            return (a[0] * L) ** 2
        return 4 * mp.sin(r * L / 2) ** 2 * S(r) ** 2

    def f(y):
        return mp.sin(mp.pi * y / L) ** (2 * p)

    def g(u):
        u = abs(u)
        if u >= L:
            return mp.mpf(0)
        return mp.quad(lambda y: f(y) * f(y - u), [u, L])

    return h, g, v


@pytest.mark.parametrize(
    "c,p,tol",
    [
        ("2.2", 2, "1e-17"),  # measured 9.95e-19
        ("2.5", 2, "1e-17"),  # measured 3.43e-19
        ("2.9", 2, "1e-17"),  # measured 5.34e-19
        ("2.5", 1, "4e-13"),  # measured 4.6e-15 (2.2: 3.67e-14); h ~ r^-6 tail
    ],
)
def test_matrix_vs_weil_functional_smooth_bumps(c, p, tol):
    """v^T Q v against zeta.weil.weil_functional (r-space quadrature, no
    shared code), dps 30. The residual is the oracle's generic archimedean
    quadrature, which is why p = 1 (slower h decay) is looser."""
    from zeta.weil import weil_functional

    h, g, v = _bump(c, p, 30)
    W = weil_functional(h, g, n_max=2, dps=30)
    M = CQ.Q_matrix(c, p, 40)
    with mp.workdps(40):
        q = (v.T * M * v)[0]
    assert abs(W - q) < mp.mpf(tol)


@pytest.mark.parametrize("c", CELLS)
def test_e0_vs_weil_functional_fejer(c):
    """Fejer pair with b = L/2 is f = L^{-1/2} U_0 exactly, so W = Q_00 / L.
    Measured at dps 30: <= 3.52e-16 (the oracle's Fejer tail machinery)."""
    from zeta.weil import fejer_pair, weil_functional

    with mp.workdps(40):
        L = mp.log(mp.mpf(c))
    h, g = fejer_pair(L / 2)
    W = weil_functional(h, g, dps=30)
    M = CQ.Q_matrix(c, 0, 40)
    with mp.workdps(40):
        assert abs(M[0, 0] / L - W) < mp.mpf("4e-15")


def _fejer_w(b):
    bb = mp.mpf(b)
    w = lambda x: 2 * (1 - x / (2 * bb)) / (2 * bb) if x < 2 * bb else mp.mpf(0)
    D = lambda x: x / (2 * bb * bb) if x < 2 * bb else 1 / bb
    return w, D


@pytest.mark.parametrize("c,b", [("2.5", "0.4"), ("2.9", "0.4"), ("2.5", "0.3"), ("2.2", "0.3")])
def test_scalar_functional_vs_weil_functional_fejer(c, b):
    """Theory s0 as a functional of w (triangle support 2b < L, kink as a
    panel break) against weil_functional. Measured <= 8.95e-16 at dps 30."""
    from zeta.weil import fejer_pair, weil_functional

    h, g = fejer_pair(b)
    W = weil_functional(h, g, dps=30)
    with mp.workdps(50):
        w, D = _fejer_w(b)
        r = CQ.q_of_w(w, D, c, 40, k_hint=4, breaks=[2 * mp.mpf(b)])
    assert abs(W - r["Q"]) < mp.mpf("1e-14")


def test_scalar_functional_window_independent():
    """The value for a fixed f cannot depend on the window it is placed in:
    the log(1 - e^{-2L}) term compensates the truncated integral exactly."""
    with mp.workdps(50):
        w, D = _fejer_w("0.3")
        vals = [CQ.q_of_w(w, D, c, 40, k_hint=4, breaks=[mp.mpf("0.6")])["Q"] for c in ("2.2", "2.9")]
    assert abs(vals[0] - vals[1]) < mp.mpf("1e-35")


# ---------------------------------------------------- structural identities


def test_pole_block_rank_two_identity():
    """v^* P v = 2 Re(F_+ conj F_-) on a complex vector, N = 8, dps 40.
    Measured 1.8e-40 at N = 32."""
    N = 8
    P = CQ.q_parts("2.5", N, 40)["pole"]
    with mp.workdps(40):
        v = [mp.mpc(mp.sin(k + 1), mp.cos(3 * k)) / (1 + abs(k - N)) for k in range(2 * N + 1)]
    assert CP.pole_identity_defect(P, "2.5", N, v, 40) < mp.mpf("1e-38")


@pytest.mark.parametrize("cls", ["minus", "minus_zero", "plus_zero"])
def test_pole_block_vanishes_on_constraint_classes(cls):
    """On V_- (g-hat(-i/2) = 0) the pole term is zero for f = g * g^*.
    Measured max entry 3.2e-43 at N = 8, dps 40."""
    N = 8
    P = CQ.q_parts("2.9", N, 40)["pole"]
    B = CP.class_bases("2.9", N, 40)[cls]
    assert CP.max_abs(CQ.compress(P, B, 40)) < mp.mpf("1e-40")


def test_galerkin_consistency_of_Q():
    """P3 for Q: separately computed N = 8 and N = 16 (different panel counts)."""
    a = CQ.Q_matrix("2.9", 8, 40)
    b = CQ.Q_matrix("2.9", 16, 40)
    assert CP.submatrix_defect(a, b) < mp.mpf("1e-38")


# ------------------------------------------------------------ pinned numbers


def test_Q_positive_on_cells_zhu():
    """P8: every Galerkin minimum on the cells is above Zhu's floor 8.9e-18."""
    J = _json()["cells"]
    for c in CELLS:
        for N in (8, 16, 32):
            for dps in (40, 60):
                lo = mp.mpf(J[c][f"full_N{N}_dps{dps}"][0])
                assert lo > mp.mpf(CP.ZHU_FLOOR), (c, N, dps)


def test_Q_lambda_min_nonincreasing_in_N():
    """P4 for Q: nested bases."""
    J = _json()["cells"]
    for c in CALIB + CELLS:
        seq = [mp.mpf(J[c][f"full_N{N}_dps40"][0]) for N in (8, 16, 32)]
        assert seq[0] >= seq[1] >= seq[2], c


def test_Q_precision_response_pinned():
    """dps 40 against 60 at N = 32: entry drift and eigenvalue drift."""
    J = _json()["cells"]
    with mp.workdps(40):
        for c in CALIB + CELLS:
            assert mp.mpf(J[c]["drift_40_60_N32"]) < mp.mpf("1e-38"), c
            for N in (8, 16, 32):
                a = [mp.mpf(x) for x in J[c][f"full_N{N}_dps40"]]
                b = [mp.mpf(x) for x in J[c][f"full_N{N}_dps60"]]
                for x, y in zip(a, b):
                    assert abs(x - y) <= mp.mpf("1e-20") * abs(y), (c, N)


@pytest.mark.parametrize("N", [8, 16, 32])
@pytest.mark.parametrize("c", CELLS)
def test_json_recomputed(c, N):
    """The stored lowest eigenvalues (full, V_-, V_- n {v_0 = 0}) at dps 40,
    recomputed from scratch for every cell and N."""
    J = _json()["cells"][c]
    M = CQ.Q_matrix(c, N, 40)
    ev = CQ.eigvals_hermitian(M, 40)[:3]
    B = CP.class_bases(c, N, 40)
    evc = {cls: CQ.eigvals_hermitian(CQ.compress(M, B[cls], 40), 40)[:3] for cls in ("minus", "minus_zero")}
    with mp.workdps(40):
        for x, y in zip(ev, J[f"full_N{N}_dps40"]):
            assert abs(x - mp.mpf(y)) <= mp.mpf("1e-22") * abs(x)
        for cls in ("minus", "minus_zero"):
            for x, y in zip(evc[cls], J[f"{cls}_N{N}_dps40"]):
                assert abs(x - mp.mpf(y)) <= mp.mpf("1e-22") * abs(x), cls


def test_results_table_matches_json():
    """Every number in RESULTS.md section 2 is the JSON value to 5 digits."""
    import re

    J = _json()["cells"]
    with open(os.path.join(HERE, "RESULTS.md")) as fh:
        text = fh.read()
    sec = text[text.index("## 2."):text.index("## 3.")]
    rows = [r for r in sec.splitlines() if re.match(r"\| 2\.[259] \| \d+ \|", r)]
    assert len(rows) == 9
    for r in rows:
        cells = [x.strip() for x in r.strip("|").split("|")]
        c, N = cells[0], int(cells[1])
        for col, key, k in ((2, "full", 3), (3, "minus", 2), (4, "minus_zero", 2)):
            got = [mp.mpf(x) for x in cells[col].split(",")]
            want = [mp.mpf(x) for x in J[c][f"{key}_N{N}_dps40"][:k]]
            assert len(got) == k
            for g_, w_ in zip(got, want):
                assert abs(g_ - w_) <= mp.mpf("6e-5") * abs(w_), (c, N, key, g_, w_)


def test_results_headline_numbers():
    J = _json()["cells"]
    assert max(mp.mpf(J[c]["galerkin_maxdev_N32_dps40"]) for c in J) <= mp.mpf("5.5e-40")
    assert max(mp.mpf(J[c]["drift_40_60_N32"]) for c in J) <= mp.mpf("3.95e-41")
    assert max(mp.mpf(J[c]["quad_err_dps40"]) for c in J) <= mp.mpf("1.1e-50")


@pytest.mark.parametrize("c,N", [("2.9", 8), ("2.2", 16)])
def test_second_minus_eigenvector_has_v0_zero(c, N):
    """Measured: the second eigenvector of Q on V_- has v_0 = 0 (7.5e-40 and
    5.8e-42 at dps 40), which is why min over V_- n {v_0 = 0} equals the
    second eigenvalue on V_-. Also validates the class_bases/compress path
    that P7 uses."""
    M = CQ.Q_matrix(c, N, 40)
    B = CP.class_bases(c, N, 40)["minus"]
    with mp.workdps(40):
        E, V = mp.eighe(CQ.compress(M, B, 40))
        i = sorted(range(len(E)), key=lambda k: mp.re(E[k]))[1]
        u = B * V[:, i]
        assert abs(u[N]) < mp.mpf("1e-35")
