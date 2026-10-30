"""exact_gram/: P4, the Gram matrix G_b, region by region against direct quadrature (BOUNDS.md s4.3 to s4.5).

Toy: two prolate modes, K = 6. Each region has a planted fault that the comparison must catch.
"""

from __future__ import annotations

import math
import os
import sys

import pytest
from flint import arb, ctx

HERE = os.path.dirname(os.path.abspath(__file__))
if HERE not in sys.path:
    sys.path.insert(0, HERE)

import bounds as B  # noqa: E402

K = 6


@pytest.fixture(autouse=True)
def _prec():
    old = ctx.prec
    ctx.prec = 133
    yield
    ctx.prec = old


@pytest.fixture(scope="module")
def md():
    old = ctx.prec
    ctx.prec = 133
    m = B.prolate_modes(2)
    ctx.prec = old
    return m


@pytest.fixture(scope="module")
def M(md):
    old = ctx.prec
    ctx.prec = 133
    v = B.choose_M(md, 2.0**K)
    ctx.prec = old
    return v


def _all_overlap(P, Q):
    return all(P[i, j].overlaps(Q[i, j]) for i in range(P.nrows()) for j in range(P.ncols()))


def test_derivative_table_by_taylor(md):
    Zd = B.zeta_derivs(md, 3.0, 25)
    h = arb(3.01) - arb(3.0)  # the exact float step, not 1/100
    z = B.zeta_values(md, [B.point(3.01)])
    for n in range(2):
        tay = sum((Zd[a, n] * h**a / math.factorial(a) for a in range(26)), arb(0))
        assert z[0, n].overlaps(tay)
    for a in range(26):  # |zeta^{(a)}| <= 2 norm (2 pi)^a
        assert abs(Zd[a, 0]) < 2 * md.norm[0] * B.two_pi() ** a


# --- region B (t < K <= t + m) ---------------------------------------------------


@pytest.mark.parametrize("mt", [(3, 4), (2, 5), (5, 1)])
def test_region_B_matches_quadrature(md, M, mt):
    m, t = mt
    P = B.ibp_balls(md, M, B.ibp_pieces(md, K, M, max(m, 3), max(t, 4), 60, arb(10) ** -10)[(m, t)])
    Q = B.quad_pair(md, 2.0**t, 2.0 ** (t + 1), m)
    assert _all_overlap(P, Q)


def test_region_B_planted_short_ibp_without_remainder_is_caught(md, M, monkeypatch):
    monkeypatch.setattr(B, "ibp_remainder", lambda *a, **k: arb(0))
    P = B.ibp_balls(md, M, B.ibp_pieces(md, K, M, 3, 4, 2, arb(10) ** -10)[(2, 4)])
    Q = B.quad_pair(md, 16.0, 32.0, 2)
    assert not _all_overlap(P, Q)


# --- region C (t >= K) --------------------------------------------------------------


def test_region_C_m_positive_matches_quadrature(md, M):
    pcs = B.ibp_pieces(md, K, M, 3, 7, 80, arb(10) ** -10)
    for m, t in ((1, 6), (3, 6), (2, 7)):
        assert _all_overlap(B.ibp_balls(md, M, pcs[(m, t)]), B.quad_pair(md, 2.0**t, 2.0 ** (t + 1), m)), (m, t)


def test_region_C_planted_short_expansion_without_remainder_is_caught(md, monkeypatch):
    monkeypatch.setattr(B.Modes, "dl1", lambda self, n, m: arb(0))
    P = B.ibp_balls(md, 2, B.ibp_pieces(md, K, 2, 1, 6, 80, arb(10) ** -10)[(1, 6)])
    assert not _all_overlap(P, B.quad_pair(md, 64.0, 128.0, 1))


def test_region_C_m_zero_from_the_gz_tail(md, M):
    d = B.gram_z_tail(md, 64.0, M) - B.gram_z_tail(md, 128.0, M)
    assert _all_overlap(d, B.quad_pair(md, 64.0, 128.0, 0))


def test_region_C_m_zero_planted_missing_difference_is_caught(md, M):
    assert not _all_overlap(B.gram_z_tail(md, 64.0, M), B.quad_pair(md, 64.0, 128.0, 0))


# --- the whole of G_b ----------------------------------------------------------------


@pytest.fixture(scope="module")
def Gb(md):
    old = ctx.prec
    ctx.prec = 133
    G, info = B.gram_b(md, K, target=arb(10) ** -8, R=40)
    ctx.prec = old
    return G, info


def test_gram_b_closes_on_the_toy(Gb):
    G, info = Gb
    assert info["m_max"] >= 40 and info["t_max"] >= 60
    for i in range(2):
        for j in range(2):
            assert G[i, j].rad() < 1e-6 and G[i, j].overlaps(G[j, i])
    # positive definite in balls: det and the leading entry
    assert G[0, 0] > 0 and G[0, 0] * G[1, 1] - G[0, 1] ** 2 > 0


@pytest.mark.slow
def test_gram_b_against_plancherel(md, Gb):
    """Two routes: G_b in v-space (P4) against (Delta/2pi) sum |b^|^2 on |s| <= S' from the hats
    (w-quadrature, P1, P2). The missing tail is positive semidefinite: G_b - inner >= -alias, and the
    off-diagonal gap is at most sqrt(tail_00 tail_11) (Cauchy-Schwarz)."""
    import rebuild as R

    G, _ = Gb
    S = 200.0
    d = arb(1) / 16
    table = R.ModeTable(md, K, S)
    s = [arb(k) * d for k in range(int(S * 16) + 1)]
    inner = [[arb(0)] * 2 for _ in range(2)]
    for i0 in range(0, len(s), 256):
        _, Bh = R.hats_block(table, s[i0:i0 + 256], 14, 14, 24)
        for c, sk in enumerate(s[i0:i0 + 256]):
            f = (1 if sk == 0 else 2) * d / B.two_pi()
            for i in range(2):
                for j in range(2):
                    inner[i][j] += f * (Bh[i, c].conjugate() * Bh[j, c]).real
    q5 = 1 / (1 - arb(2) ** (-arb(5) / 6))
    Cb = [md.C(n) * q5 for n in range(2)]
    tails = []
    for i in range(2):
        alias = arb(1.5) * Cb[i] * Cb[i] * 2 * B.alias_q(d) / (1 - B.alias_q(d))
        t = G[i, i] - inner[i][i]
        assert t > -alias - arb(10) ** -6
        assert t < 0.1  # the tail beyond S' = 200 is a few percent at these modes
        tails.append(t)
    gap = abs(G[0, 1] - inner[0][1])
    assert gap < (tails[0].upper() * tails[1].upper()).sqrt() + arb(10) ** -6


def test_gram_b_parts_sum_to_the_whole(md, Gb):
    G, info = Gb
    parts = [B.gram_b(md, K, target=arb(10) ** -8, R=40, part=p, nparts=3) for p in range(3)]
    S = B.gram_b_merge(parts)
    assert all(S[i, j].overlaps(G[i, j]) for i in range(2) for j in range(2))
    with pytest.raises(ValueError):
        B.gram_b_merge(parts[:2])  # a part missing is refused
