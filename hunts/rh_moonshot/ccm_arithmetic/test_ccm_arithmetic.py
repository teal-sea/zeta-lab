"""Tests for hunt #150 mechanism 1 (ccm_arithmetic): CCM step 2.

Each test can fail.  They pin, at small cells:

* the new assembly pieces (general digamma parameter, pole vectors) against
  the validated weil_trunc blocks;
* the radical lemma as an assembly check: the radical vector of X (samples of
  Xi_X at the nodes) has a tiny Rayleigh quotient for X's own form, and a
  planted fault in the form (a prime removed, a pole removed) destroys that;
* the measured structure of zeta's CvS ground state: radical times an even
  polynomial, every zero of Xi below the band matched, the Sturm counts
  0, 1, 2 for the three lowest eigenvectors, and the a2 law;
* the rival gate: DH's ground state is captured by its radical subspace below
  its crossing and is not above it; W_{1/4}'s is not captured from c = 3;
  Dedekind Q(sqrt -23) stays captured where Epstein (1,1,6) is negative.

Nothing here writes into the tree (Xi values are cached in memory only).
Run: .venv/bin/python -m pytest -q -n0 hunts/rh_moonshot/ccm_arithmetic/test_ccm_arithmetic.py
"""

from __future__ import annotations

import os
import sys

import pytest

HERE = os.path.dirname(os.path.abspath(__file__))
if HERE not in sys.path:
    sys.path.insert(0, HERE)

import ccm_common as C  # noqa: E402
from flint import acb, arb, arb_mat, ctx  # noqa: E402
from mpmath import mp  # noqa: E402

import enclosures as EN  # noqa: E402
import wp_common as WP  # noqa: E402

_XI: dict = {}


def _radical(kind, c, N, power=0, tcut=None, dps=30):
    """Radical vector with an in-memory Xi cache; nodes above tcut set to 0."""
    L = C.L_mp(c)
    out = []
    for k in range(N + 1):
        om = 2 * mp.pi * k / L
        if tcut is not None and om > tcut:
            xv = mp.mpf(0)
        else:
            key = (kind, WP.cstr(c), k)
            if key not in _XI:
                _XI[key] = C.xi_real(kind, om, dps)
            xv = _XI[key]
        if k == 0:
            out.append(xv / mp.sqrt(L) if power == 0 else mp.mpf(0))
        else:
            out.append(mp.sqrt(2 / L) * (-1) ** k * om ** (2 * power) * xv)
    return out


def _rq_ball(A, vec, prec):
    ctx.prec = prec
    col = arb_mat(len(vec), 1, [arb(mp.nstr(x, int(prec / 3.32) + 10)) for x in vec])
    return C._dot(col, A * col) / C._dot(col, col)


def _ground(kind, c, N, k=3):
    prec = C.prec_for(kind, c, N)
    A = C.matrix(kind, c, N, prec)
    return prec, A, C.lowest_pairs(A, k=k)


# ---------------------------------------------------------------------------
# assembly pieces
# ---------------------------------------------------------------------------


def test_arch_block_general_parameter_matches_weil_trunc():
    prec = 300
    for kind, a, lq in (("zeta", arb(1) / 4, "pi"), ("dh", arb(3) / 4, "pi/5")):
        bt = EN.BallTruncation(WP.cq(13), 12, kind=kind, prec=prec)
        ctx.prec = prec
        q = arb.pi() if lq == "pi" else arb.pi() / 5
        const = -q.log() + acb(a).digamma().real
        S, d = C.arch_seqs(13, 12, a, const, prec)
        for k in range(13):
            assert (S[k] - bt._S[k]).contains(0)
            assert (d[k] - bt._archdiag[k]).contains(0)
            assert abs(float((d[k] - bt._archdiag[k]).mid())) < 1e-80


def test_pole_vector_reproduces_W02():
    prec = 300
    bt = EN.BallTruncation(WP.cq(13), 12, kind="zeta", prec=prec)
    ctx.prec = prec
    full = arb_mat(bt.even_matrix())
    nopole = WP.sector_matrix(bt, "even", S=bt._S, archdiag=bt._archdiag, P=bt._P, R=bt._R)
    W02 = full - nopole
    PB = C.pole_block(bt.L, 12, [arb(1) / 2])
    for i in range(13):
        for j in range(13):
            assert abs(float((W02[i, j] - PB[i, j]).mid())) < 1e-80


def test_chi_minus23_split_and_inert_primes():
    assert [C._chi_m23(p) for p in (2, 3, 13)] == [1, 1, 1]
    assert [C._chi_m23(p) for p in (5, 7, 11)] == [-1, -1, -1]
    assert C._chi_m23(23) == 0


# ---------------------------------------------------------------------------
# the radical lemma as an assembly check, with planted faults
# ---------------------------------------------------------------------------


def test_radical_vector_is_near_null_for_zeta_and_a_planted_fault_breaks_it():
    c, N = 13, 32
    prec = C.prec_for("zeta", c, N)
    A = C.matrix("zeta", c, N, prec)
    with mp.workdps(60):
        r = _radical("zeta", c, N)
        q = _rq_ball(A, r, prec)
    # measured 1.70e-28; the kernel leakage scale Phi(L/2)^2 is ~3e-29
    assert q < arb("1e-25") and q > 0
    # planted fault: remove the prime 2 from the prime block
    bt = EN.BallTruncation(WP.cq(c), N, kind="zeta", prec=prec)
    coeffs = [t for t in WP._coeffs(bt) if t[2] != 2]
    P, R = WP._prime_seqs(bt, coeffs)
    ctx.prec = prec
    A_bad = (
        WP.sector_matrix(bt, "even", S=bt._S, archdiag=bt._archdiag, pole=True)
        + WP.sector_matrix(bt, "even", P=P, R=R)
    )
    with mp.workdps(60):
        q_bad = _rq_ball(A_bad, r, prec)
    assert abs(float(q_bad.mid())) > 1e-4


def test_radical_vector_is_near_null_for_wa_and_a_planted_fault_breaks_it():
    c, N, prec = 13, 32, 400
    A = C.wa_matrix(c, N, prec)
    with mp.workdps(50):
        r = _radical("wa", c, N, tcut=60)
        q = _rq_ball(A, r, prec)
    assert abs(float(q.mid())) < 1e-7  # measured 2.2e-9
    # planted fault: drop the pole at z = +- i(1/2 - a)
    bt = EN.BallTruncation(WP.cq(c), N, kind="zeta", prec=prec)
    ctx.prec = prec
    a = arb(C.WA_SHIFT)
    A_bad = A - C.pole_block(bt.L, N, [arb(1) / 2 - a])
    with mp.workdps(50):
        q_bad = _rq_ball(A_bad, r, prec)
    assert abs(float(q_bad.mid())) > 1e-3


# ---------------------------------------------------------------------------
# zeta: the CvS ground state is radical times an even polynomial
# ---------------------------------------------------------------------------


def test_zeta_ground_state_structure_at_13_32():
    c, N = 13, 32
    prec, A, pairs = _ground("zeta", c, N, k=3)
    with mp.workdps(130):
        L = C.L_mp(c)
        vs = [C.to_mp(p[1]) for p in pairs]
        rs = [_radical("zeta", c, N, power=j) for j in range(5)]
        res2, _ = C.project_residual(vs[0], rs[:3])
        res4, _ = C.project_residual(vs[0], rs[:5])
        assert res2 < mp.mpf("1e-9")  # measured 1.22e-11
        assert res4 < mp.mpf("1e-16")  # measured 2.25e-19
        assert C.overlap_misfit(vs[0], rs[0]) > mp.mpf("1e-5")  # P is not constant
        # every zero of Xi below 0.9 * band edge is matched, no extra zeros
        TZ = mp.mpf("0.9") * 2 * mp.pi * N / L
        fz = C.real_zeros(lambda t: mp.re(C.F_mp(vs[0], L, t)), mp.mpf("0.3"), TZ, mp.mpf("0.05"))
        gam = []
        k = 1
        while True:
            g = mp.im(mp.zetazero(k))
            if g > TZ:
                break
            gam.append(g)
            k += 1
        assert len(fz) == len(gam) == 17
        assert max(abs(a - b) for a, b in zip(fz, gam)) < mp.mpf("1e-12")  # measured 3.2e-14
        # Sturm counts on [0, 40]: extra real zeros of F_vk beyond Xi's = k - 1
        g40 = len([g for g in gam if g <= 40])
        extra = []
        for v in vs:
            zz = C.real_zeros(lambda t, v=v: mp.re(C.F_mp(v, L, t)), mp.mpf("0.3"), mp.mpf(40), mp.mpf("0.05"))
            extra.append(len(zz) - g40)
        assert extra == [0, 1, 2]


@pytest.mark.parametrize("c,N", [(6, 32), (13, 64)])
def test_zeta_a2_law(c, N):
    """a2 = (rho_1 - 1)/om_1^2 against kappa/(4 pi^2 c): measured kappa
    0.83 (c=6) and 0.80 (c=13, N=64); the band must be saturated."""
    prec, A, pairs = _ground("zeta", c, N, k=1)
    with mp.workdps(100):
        L = C.L_mp(c)
        v = C.to_mp(pairs[0][1])
        r = _radical("zeta", c, N)
        om1 = 2 * mp.pi / L
        a2 = ((v[1] / r[1]) / (v[0] / r[0]) - 1) / om1**2
        kappa = a2 * 4 * mp.pi**2 * c
        assert mp.mpf("0.6") < kappa < mp.mpf("1.0")


# ---------------------------------------------------------------------------
# the rival gate
# ---------------------------------------------------------------------------


def test_dh_captured_below_crossing_and_not_above():
    with mp.workdps(80):
        out = {}
        for c in (29, 37):
            prec, A, pairs = _ground("dh", c, 64, k=1)
            v = C.to_mp(pairs[0][1])
            r = _radical("dh", c, 64, tcut=60)
            out[c] = (pairs[0][0], C.overlap_misfit(v, r))
    lam29, mis29 = out[29]
    lam37, mis37 = out[37]
    assert lam29 > 0 and mis29 < mp.mpf("0.01")
    # above the crossing the Rayleigh-quotient ball of the computed vector is
    # negative (an upper bound for lambda_1) and the ground state is a beam
    assert lam37.upper() < 0 and mis37 > mp.mpf("0.9")


def test_wa_not_captured_from_c3():
    with mp.workdps(60):
        res = {}
        for c in (2, 3):
            prec, A, pairs = _ground("wa", c, 32, k=1)
            v = C.to_mp(pairs[0][1])
            r = _radical("wa", c, 32, tcut=60)
            res[c] = (pairs[0][0], C.overlap_misfit(v, r))
    assert res[2][0] > 0 and res[2][1] < mp.mpf("0.3")
    assert res[3][0].upper() < 0 and res[3][1] > mp.mpf("0.9")


def test_dedekind_captured_where_epstein_is_negative():
    c, N = 31, 64
    prec = C.prec_for("epstein", c, N)
    Ae = C.matrix("epstein", c, N, prec)
    lam_e = C.lowest_pairs(Ae, k=1)[0][0]
    assert lam_e.upper() < 0  # Epstein (1,1,6) even sector negative at c = 31
    prec, Ad, pairs = _ground("dedekind", c, N, k=1)
    assert pairs[0][0] > 0
    with mp.workdps(60):
        v = C.to_mp(pairs[0][1])
        r = _radical("dedekind", c, N, tcut=40)
        assert C.overlap_misfit(v, r) < mp.mpf("0.02")
