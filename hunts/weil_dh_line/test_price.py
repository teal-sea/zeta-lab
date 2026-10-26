"""Tests for hunt weil_dh_line (#146): every number PRICE.md states is pinned
here or read back from the JSON artifact it came from, and every instrument
the numbers rest on has a check that can fail (planted faults included).

Run from the repo root: .venv/bin/python -m pytest -q -n0 hunts/weil_dh_line/test_price.py
"""
from __future__ import annotations

import json
import math
import re
import sys
from fractions import Fraction
from pathlib import Path

import numpy as np
import pytest
from flint import arb, arb_mat, ctx

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import price  # noqa: E402
import joint  # noqa: E402
import scout  # noqa: E402

TABLE = HERE / "price_table.json"
JOINT = {tag: HERE / f"joint_{tag}.json" for tag in price.WINDOWS}
K2 = HERE / "k2_dh.json"
SCOUT = HERE / "scout_L140.json"
K2_SCOUTS = HERE / "k2_scouts.json"


def _load(path: Path):
    if not path.exists():
        pytest.skip(f"{path.name} not produced yet")
    return json.loads(path.read_text())


# ------------------------------------------------------------- the windows

def test_the_dh_line_and_the_task_rational():
    """L_DH = 171079/100000 is at or above (log 30.617188)/2 = 1.7107808; the
    task's 1.71078 lies 7.8e-7 below it, so DH is not proved negative there."""
    with ctx.workprec(256):
        ldh = arb(price.DH_CUTOFF.numerator).log() / 2 - arb(price.DH_CUTOFF.denominator).log() / 2
        assert bool(price.to_arb(price.WINDOWS["L_DH"]) >= ldh)
        gap = ldh - price.to_arb(Fraction(171078, 100000))
        assert bool(gap > 0)
        assert 7.7e-7 < float(gap.mid()) < 7.8e-7
        assert abs(float(ldh.mid()) - 1.7107808) < 5e-8
        assert abs(math.exp(2 * 1.71078) - 30.61714) < 1e-5
        l31 = arb(31).log() / 2
        assert bool(price.to_arb(price.WINDOWS["L_31"]) < l31)
        assert abs(float(l31.mid()) - 1.7169936) < 1e-7
        # Epstein (1,1,6): L = 1.6615 lies above the odd-sector line (log 27.741699)/2
        # and below the even-sector line (log 29.304199)/2
        odd = arb(27741699).log() / 2 - arb(10 ** 6).log() / 2
        even = arb(29304199).log() / 2 - arb(10 ** 6).log() / 2
        assert bool(price.to_arb(Fraction(16615, 10000)) > odd)
        assert bool(price.to_arb(Fraction(16615, 10000)) < even)
        assert bool(price.to_arb(price.WINDOWS["L_DH"]) > even)
    assert abs(math.log(27.741699) / 2 - 1.66147) < 1e-5
    assert abs(math.log(29.304199) / 2 - 1.68887) < 1e-5


def test_comb_sets():
    dh_line = [n for n, _, _ in price.prime_powers(price.WINDOWS["L_DH"])]
    assert dh_line == [2, 3, 4, 5, 7, 8, 9, 11, 13, 16, 17, 19, 23, 25, 27, 29]
    assert [n for n, _, _ in price.prime_powers(price.WINDOWS["L_31"])] == dh_line
    assert [n for n, _, _ in price.prime_powers(price.WINDOWS["1.4"])] == [2, 3, 4, 5, 7, 8, 9, 11, 13, 16]
    assert price.m_of(price.WINDOWS["L_DH"]) == {2: 4, 3: 3, 5: 2, 7: 1, 11: 1, 13: 1, 17: 1, 19: 1, 23: 1, 29: 1}
    assert price.m_of(price.WINDOWS["1.4"]) == {2: 4, 3: 2, 5: 1, 7: 1, 11: 1, 13: 1}


def test_A_L():
    assert abs(float(price.A_L(price.WINDOWS["1.4"]).mid()) - 10.29034) < 1e-5
    assert abs(float(price.A_L(price.WINDOWS["L_DH"]).mid()) - 16.64046) < 1e-5


# ------------------------------------------------------------- S*_L

def test_galerkin_eigensolvers_agree_at_two_precisions():
    """The Galerkin matrix's top eigenvalue by scipy eigsh, numpy eigvalsh and
    mpmath eigsy at 40 digits (an independent eigensolver at two precisions)."""
    from mpmath import mp, matrix, eigsy, mpf
    L, M = price.WINDOWS["1.4"], 72
    lam_sparse = price.galerkin_top(L, M)
    d = 2 * float(L) / M
    A = np.zeros((M, M))
    idx = np.arange(M)
    U = (idx[None, :] - idx[:, None]) * d
    for w, s, _, _ in price._shifts(L):
        A += w * (np.maximum(0.0, d - np.abs(U - s)) + np.maximum(0.0, d - np.abs(U + s))) / d
    lam_dense = float(np.linalg.eigvalsh(A)[-1])
    assert abs(lam_dense - lam_sparse) < 1e-10
    with mp.workdps(40):
        dd = 2 * mpf(L.numerator) / L.denominator / M
        Am = matrix(M, M)
        for n, p, m in price.prime_powers(L):
            w, s = mp.log(p) / mpf(p) ** (mpf(m) / 2), mp.log(n)
            for i in range(M):
                for j in range(M):
                    u = (j - i) * dd
                    Am[i, j] += w * (max(mpf(0), dd - abs(u - s)) + max(mpf(0), dd - abs(u + s))) / dd
        E, _ = eigsy(Am)
        lam_mp = float(max(E))
    assert abs(lam_mp - lam_dense) < 1e-11


def test_s_star_enclosure_small_grid_brackets_the_recorded_values():
    """A coarse enclosure (M = 1000) must contain the recorded fine one's
    values: its Schur upper end may not fall below the fine Rayleigh lower end."""
    tab = _load(TABLE)
    L = price.WINDOWS["1.4"]
    enc = price.s_star_enclosure(L, 1000, iters=400)
    lo, hi = float(enc["lower"].mid()), float(enc["upper"].mid())
    assert lo < hi
    fine_lo = float(tab["1.4"]["S_star"]["lower"])
    fine_hi = float(tab["1.4"]["S_star"]["upper"])
    assert lo <= fine_lo <= fine_hi <= hi
    g = tab["1.4"]["S_star_galerkin"]
    assert g["2000"] <= g["8000"] <= g["32000"] <= fine_hi


def test_a_lesioned_comb_is_caught_by_the_cross_check():
    """Planted fault: a Schur bound computed for a comb whose p = 2 terms lost
    10 percent of their weight falls below the independently computed fine
    Rayleigh lower end of the true comb; the true comb's bound does not."""
    tab = _load(TABLE)
    L, M = price.WINDOWS["1.4"], 1000
    fine_lo = float(tab["1.4"]["S_star"]["lower"])
    h, _ = price.schur_vector(L, M, iters=400)
    w, types = price._subinterval_types(L, M)
    full = float((price._max_system(h, w, types) / h).max())
    assert full >= fine_lo
    lesion = {p: (0.9 if p == 2 else 1.0) for p in price.primes_of(L)}
    h2, _ = price.schur_vector(L, M, weights=lesion, iters=400)
    w2, types2 = price._subinterval_types(L, M, weights=lesion)
    bad = float((price._max_system(h2, w2, types2) / h2).max())
    assert bad < fine_lo


@pytest.mark.parametrize("tag", list(price.WINDOWS))
def test_recorded_s_star_and_sep(tag):
    tab = _load(TABLE)[tag]
    lo, hi = float(tab["S_star"]["lower"]), float(tab["S_star"]["upper"])
    assert 0 < hi - lo < 0.007
    first, _, last = tab["S_star"]["schur_iteration"]
    assert last <= hi and first > last
    if tag == "1.4":
        assert abs(first - 4.99) < 0.005 and abs(last - 3.715977) < 1e-6
    assert tab["S_star_galerkin"]["32000"] <= hi
    slo, shi = float(tab["S_sep"]["lower"]), float(tab["S_sep"]["upper"])
    assert 0 <= shi - slo < 1e-8
    tot = 0.0
    for p, m in price.m_of(price.WINDOWS[tag]).items():
        t = [0.0] + [math.log(p) / p ** (k / 2) for k in range(1, m + 1)]
        T = np.array([[t[abs(i - j)] for j in range(m + 1)] for i in range(m + 1)])
        tot += float(np.linalg.eigvalsh(T)[-1])
    assert abs(tot - slo) < 1e-9
    assert float(tab["S_sep"]["lower"]) > lo          # weak duality
    for D, r in tab["S_sep_sine"].items():
        assert r["scan_ok"]
        assert r["S_float"] >= slo
    vals = [tab["partitions"][b]["value"] for b in sorted(tab["partitions"])]
    assert all(a >= b - 1e-9 for a, b in zip(vals, vals[1:]))
    assert vals[-1] >= lo - 2e-3


def test_prime_three_block_at_1_4_is_log_3():
    """Closed form: with m = 2 the Toeplitz block of p = 3 has top eigenvalue log 3."""
    lo, hi = price.toeplitz_top(3, 2)
    assert bool(lo <= arb(3).log() + arb(10) ** -15) and bool(hi >= arb(3).log() - arb(10) ** -15)


def test_hardened_partition_floors():
    """Arb lower ends of the best partitions agree with the float search and
    bound every cluster-separable envelope from below (weak duality per cluster)."""
    d = _load(HERE / "partition_lower.json")
    tab = _load(TABLE)
    for tag in ("1.4", "L_DH"):
        for b, r in d[tag].items():
            fl = tab[tag]["partitions"][b]["value"]
            assert abs(float(r["value_lower"]) - fl) < 2e-6
            assert sorted(map(tuple, r["clusters"])) == sorted(map(tuple, tab[tag]["partitions"][b]["clusters"]))
    assert float(d["L_DH"]["3"]["value_lower"]) > 6.1743
    assert float(d["L_DH"]["3"]["value_lower"]) < price.GO_THRESHOLD


# ------------------------------------------------------------- joint machinery

def test_planted_inband_frequency_is_refused():
    L = price.WINDOWS["1.4"]
    bad = [(1, -1)]                                   # log 7 - log 3 < 2L: in band
    audit = joint.frequency_audit(L, [3, 7], bad)
    assert not audit["ok"]
    om, skipped = joint.omega(L, [3, 7], [3, 3])
    assert (1, -1) not in om and skipped > 0
    # the shell keeps only near-band points, all of them still out of band
    sh, _ = joint.omega(L, [3, 7], [6, 6], shell=6.0)
    assert sh and all(2 * 1.4 <= abs(k[0] * math.log(3) + k[1] * math.log(7)) <= 6.0 for k in sh)


def test_weights_must_carry_every_comb_term_once():
    """P_L = sum_c P_c needs every comb term carried with total weight 1."""
    L = price.WINDOWS["L_DH"]
    price.check_weight_cover(L, "dh", [([2, 3, 7], None), ([2, 13], {13: 1, 26: 1}), ([11], None), ([17], None),
                                       ([19], None), ([23], None), ([29], None)])
    with pytest.raises(ValueError):          # the pure powers of 2 carried twice
        price.check_weight_cover(L, "dh", [([2, 3, 7], None), ([2, 13], None), ([11], None), ([17], None),
                                           ([19], None), ([23], None), ([29], None)])
    with pytest.raises(ValueError):          # a prime left out
        price.check_weight_cover(price.WINDOWS["1.4"], "zeta", [([2, 5, 11], None), ([3, 7], None)])


@pytest.fixture(scope="module")
def small_cluster():
    """A small joint envelope built from scratch: {3, 7} at L = 7/5, degree box (4, 3)."""
    return joint.build_cluster(price.WINDOWS["1.4"], [3, 7], [4, 3], tau=2e-4)


def test_whole_torus_bound_on_a_small_cluster(small_cluster):
    """U bounds a fine float grid and the optimizer's polished maximum, and its
    proven lower end LB sits within tau of it."""
    L = price.WINDOWS["1.4"]
    r = small_cluster
    sb = r["sup_bound"]
    assert sb["U"] >= sb["LB"] >= sb["U"] - 2.1e-4
    assert sb["U"] >= r["t_opt"] - 1e-9
    hq = [Fraction(x) for x in r["h"]]
    comb = joint.cluster_comb(L, [3, 7])
    keys = [k for k, _ in comb] + [tuple(k) for k in r["omega"]]
    vals = np.array([float(c.mid()) for _, c in comb] + [-float(x) for x in hq])
    F = joint._eval_grid([512, 512], keys, vals)
    assert F.max() <= sb["U"]
    spot = joint.arb_spot_check(L, [3, 7], [tuple(k) for k in r["omega"]], hq, n=40)
    assert spot["ok"]
    box = joint.arb_box_check(L, [3, 7], [tuple(k) for k in r["omega"]], hq, n=10)
    assert box["ok"]
    # weak duality, cluster by cluster
    assert sb["U"] >= price.galerkin_top(L, 2000, {3, 7})


def test_planted_coefficient_change_breaks_the_old_bound(small_cluster):
    """Lesion: lower one H coefficient by 1/4; the old U must no longer bound
    the lesioned function somewhere on the torus (proven by the new LB)."""
    L = price.WINDOWS["1.4"]
    r = small_cluster
    hq = [Fraction(x) for x in r["h"]]
    hq[0] -= Fraction(1, 4)
    sb = joint.sup_bound(L, [3, 7], [tuple(k) for k in r["omega"]], hq, tau=2e-4)
    assert sb["LB"] > r["U"]


def test_quadratic_box_bound_dominates_dense_samples(small_cluster):
    """The global quadratic bound used on boxes where -H is verified positive
    definite never falls below the function on a dense sample of the box, and
    the same holds for the separable bound; a planted fault (a Hessian error
    budget of zero with a wrong sign on the gradient) is caught."""
    L = price.WINDOWS["1.4"]
    r = small_cluster
    om = [tuple(k) for k in r["omega"]]
    hq = [Fraction(x) for x in r["h"]]
    K, a, a_abs, a_err = joint._terms(L, [3, 7], om, hq)
    P, d = K.shape
    Ev, Eg, EH = joint._errors(K, a_abs, a_err, P)
    t1, t0 = joint._tables()
    rng = np.random.default_rng(5)
    level = 7
    J = rng.integers(0, 2 ** level, size=(4000, d), dtype=np.int64)
    Bv = np.full((4000, d), level, dtype=np.int64)
    f, g, Hs = joint._box_values(J, Bv, K, a, t1, t0)
    Q2 = joint._quadratic_bound(f, g, Hs, Eg, EH, d)
    use = np.where(np.isfinite(Q2))[0][:150]
    assert use.size > 20
    r_u = 2.0 ** -(level + 1)
    absK = np.abs(K).astype(float)
    Kf = K.astype(float)
    worst = np.inf
    for b in use:
        c_u = (2 * J[b] + 1) / 2.0 ** (level + 1)
        grid = np.stack(np.meshgrid(*[np.linspace(-r_u, r_u, 9)] * d, indexing="ij"), -1).reshape(-1, d)
        vals = np.cos(2 * np.pi * ((c_u + grid) @ Kf.T)) @ a
        rr = 2 * np.pi * r_u
        R3 = ((rr * absK.sum(axis=1)) ** 3 @ a_abs) / 6
        worst = min(worst, f[b] + Q2[b] + R3 - vals.max())
    assert worst > 0
    # planted fault: flip the gradient sign in the model; the bound then misses
    # the true maxima of boxes whose model peak lies off centre
    Q2bad = joint._quadratic_bound(f, -g * 0, Hs, Eg * 0, EH * 0, d)
    missed = 0
    for b in use:
        c_u = (2 * J[b] + 1) / 2.0 ** (level + 1)
        grid = np.stack(np.meshgrid(*[np.linspace(-r_u, r_u, 9)] * d, indexing="ij"), -1).reshape(-1, d)
        vals = np.cos(2 * np.pi * ((c_u + grid) @ Kf.T)) @ a
        if f[b] + Q2bad[b] < vals.max() - 1e-12:
            missed += 1
    assert missed > 0


def test_fast_bessel_column_matches_the_enclosed_one():
    """The scout's midpoint recurrence against the re-seeded Arb column of
    oob_envelope/numerics/assemble.py, at an argument in the oscillatory range."""
    with ctx.workprec(320):
        x = arb(857) / 4                 # exact dyadic, in the oscillatory range n < x
        a = scout.sph_j_all(260, x)
        b = scout.sph_j_fast(260, x)
        dev = max(float(abs((b[n] - a[n].mid()) / a[n].mid()).mid()) for n in range(261))
    assert dev < 1e-80


@pytest.mark.parametrize("parity", ["even", "odd"])
def test_scout_basis_is_orthonormal_up_to_its_tail(parity):
    """G(T) -> I (Parseval for the orthonormal Legendre basis) with the 1/T
    tail of a window cut off sharply: on [0, 60] with N = 6 modes at L = 7/5,
    0 <= 1 - G_nn <= 4 nu_n / (pi L T) and |G_nm| <= 4 sqrt(nu_n nu_m) / (pi L T)
    (from |j_n(x)| <= 1/x), in both parity sectors; the diagonal gap sits near
    half its bound, the average of sin^2."""
    L = Fraction(7, 5)
    env = HERE / f"_test_env_{parity}.json"
    env.write_text(json.dumps({"S_exact": "1", "kind": "zeta",
                               "clusters": [{"primes": [3], "omega": [[2]], "h": ["0"]}]}))
    try:
        C, G, _ = scout.unit(L, env, 6, 24, Fraction(1, 2), 0, 120, 128, parity=parity, bessel="fast")
    finally:
        env.unlink()
    ns = scout.orders(6, parity)
    for i, n in enumerate(ns[:4]):
        gap = 1 - float(G[i, i].mid())
        bound = 4 * (n + 0.5) / (math.pi * 1.4 * 60)
        assert 0.3 * bound <= gap <= bound, (n, gap)
        for j in range(4):
            if j != i:
                assert abs(float(G[i, j].mid())) <= 4 * math.sqrt((n + 0.5) * (ns[j] + 0.5)) / (math.pi * 1.4 * 60)
    assert scout.orders(6, parity)[0] == (0 if parity == "even" else 1)


@pytest.mark.parametrize("parity", ["even", "odd"])
def test_scout_transform_signs_and_pole_vector(parity):
    """Against direct quadrature (mpmath): for f = T_a + T_b the scout's
    |F(t)|^2 = (sigma_a j_a(tL) + sigma_b j_b(tL))^2 at one t, which pins the
    relative signs sigma_n (a wrong sign on one mode changes the cross term),
    and p_n = int T_n cosh(u/2) du (even) or int T_n sinh(u/2) du (odd), so the
    pole term is +2 (c.p)^2 or -2 (c.p)^2. Here t = 205/56, so tL = 41/8."""
    from mpmath import mp, quad, legendre, sqrt as msqrt, cos as mcos, sin as msin, cosh, sinh, mpf
    L = Fraction(7, 5)
    with mp.workdps(30):
        Lm = mpf(7) / 5

        def Tn(n, u):
            return legendre(n, u / Lm) * msqrt((2 * n + 1) / mpf(2)) / msqrt(Lm)
        ns = scout.orders(3, parity)
        a, b = ns[1], ns[2]
        t = mpf(205) / 56                  # tL = 41/8, an exact dyadic
        if parity == "even":
            Fre = quad(lambda u: (Tn(a, u) + Tn(b, u)) * mcos(t * u), [-Lm, 0, Lm])
            F2 = Fre ** 2
        else:
            Fim = quad(lambda u: (Tn(a, u) + Tn(b, u)) * msin(t * u), [-Lm, 0, Lm])
            F2 = Fim ** 2
        with ctx.workprec(128):
            La, scale, pvec = scout.basis(L, 3, parity)
            x = price.to_arb(Fraction(41, 8))
            j = scout.sph_j_all(ns[-1] + 1, x)
            val = (scale[1] * j[a] + scale[2] * j[b]) ** 2
            wrong = (scale[1] * j[a] - scale[2] * j[b]) ** 2
            assert abs(float(val.mid()) - float(F2)) < 1e-12
            assert abs(float(wrong.mid()) - float(F2)) > 1e-6
            for i, n in enumerate(ns):
                kern = cosh if parity == "even" else sinh
                ref = quad(lambda u: Tn(n, u) * kern(u / 2), [-Lm, 0, Lm])
                assert abs(float(pvec[i].mid()) - float(ref)) < 1e-15


@pytest.mark.parametrize("parity,kind", [("even", "zeta"), ("odd", "zeta"), ("even", "dh"), ("odd", "epstein")])
def test_scout_assembly_against_an_independent_float_route(parity, kind):
    """The scout's Arb assembly of C and G against a float64 route that shares
    no code with it (scipy spherical_jn and complex digamma, numpy
    Gauss-Legendre, numpy cosines for the comb and H) at L = 7/5 on [0, 20]
    with N = 6: entries agree to 1e-9 for every kind and parity."""
    from scipy.special import spherical_jn, psi
    L = Fraction(7, 5)
    Lf = 1.4
    om = [(0, 2, -1), (1, 1, -1), (2, 0, 1)]
    hs = ["3/8", "-5/16", "1/4"]
    env = HERE / f"_test_env_{parity}_{kind}.json"
    env.write_text(json.dumps({"S_exact": "4", "kind": kind,
                               "clusters": [{"primes": [3, 7, 13], "omega": [list(k) for k in om], "h": hs}]}))
    try:
        C, G, _ = scout.unit(L, env, 6, 32, Fraction(1, 2), 0, 40, 128, parity=parity, bessel="fast")
    finally:
        env.unlink()
    ns = scout.orders(6, parity)
    xg, wg = np.polynomial.legendre.leggauss(32)
    Cf = np.zeros((6, 6))
    Gf = np.zeros((6, 6))
    if kind == "zeta":
        comb = [(2 * math.log(p) / p ** (m / 2), math.log(n)) for n, p, m in price.prime_powers(L)]
    elif kind == "dh":
        comb = [(float(c.mid()), math.log(n)) for n, c in price.dh_comb(L)]
    else:
        comb = [(float(c.mid()), math.log(n)) for n, c in price.epstein_comb(L)]
    logs = np.log([3.0, 7.0, 13.0])
    for k in range(40):
        t = 0.5 * k + 0.25 * (1 + xg)
        w = wg * 0.25 / math.pi
        if kind == "zeta":
            sym = np.real(psi(0.25 + 0.5j * t)) - math.log(math.pi)
        elif kind == "dh":
            sym = np.real(psi(0.75 + 0.5j * t)) + math.log(5 / math.pi)
        else:
            sym = (math.log(23) + np.real(psi(0.25 + 0.5j * t)) + np.real(psi(0.75 + 0.5j * t))
                   - 2 * math.log(math.pi))
        for c, ln in comb:
            sym = sym - c * np.cos(t * ln)
        for kk, hh in zip(om, hs):
            sym = sym + float(Fraction(hh)) * np.cos(t * float(np.dot(kk, logs)))
        V = np.array([(-1) ** (n // 2) * 2 * math.sqrt(Lf * (n + 0.5)) * spherical_jn(n, t * Lf) for n in ns])
        Gf += (V * w) @ V.T
        Cf += (V * (w * sym)) @ V.T
    dC = max(abs(float(C[i, j].mid()) - Cf[i, j]) for i in range(6) for j in range(6))
    dG = max(abs(float(G[i, j].mid()) - Gf[i, j]) for i in range(6) for j in range(6))
    assert dC < 1e-9 and dG < 1e-9, (dC, dG)


@pytest.mark.parametrize("tag", list(price.WINDOWS))
def test_joint_envelope_frequencies_and_bounds(tag):
    d = _load(JOINT[tag])
    L = price.WINDOWS[tag]
    tab = _load(TABLE)[tag]
    total = Fraction(0)
    for c in d["clusters"]:
        audit = joint.frequency_audit(L, c["primes"], [tuple(k) for k in c["omega"]])
        assert audit["ok"] and audit["least_margin"] > 0
        sb = c["sup_bound"]
        assert sb["U"] >= sb["LB"]
        assert not sb["unresolved"]
        assert c["sup_bound_recheck"]["U"] <= c["U"]
        floor = price.galerkin_top(L, 2000, set(c["primes"]))
        assert c["U"] >= floor                     # weak duality, cluster by cluster
        assert c["arb_spot_check"]["ok"]
        assert c["arb_box_check"]["ok"]
        total += Fraction(c["U"])
    assert d["weights_cover_comb"]
    assert Fraction(d["S_exact"]) == total
    assert d["S"] >= float(tab["S_star"]["lower"])  # weak duality, whole comb
    # the joint envelope must beat the per-prime limit to be worth its cost
    assert d["S"] < float(tab["S_sep"]["lower"])


# ------------------------------------------------------------- K2 and DH data

def test_dh_comb_reproduces_the_oob_envelope_k2_constant():
    """S_DH = sum 2|Lambda_f(n)|/sqrt(n) over n <= 46 is 25.5916527 in
    oob_envelope/numerics/k2_dh.json; this module's recursion must agree."""
    L = Fraction(192, 100)
    comb = price.dh_comb(L)
    assert max(n for n, _ in comb) == 46
    S = sum(abs(float(c.mid())) for _, c in comb)
    assert abs(S - 25.591652703258486) < 1e-9


def test_digamma_bounds_used_by_the_dh_gate_and_the_dh_scout():
    """log(t/2) - 1/t <= Re digamma(3/4 + it/2) <= log(t/2) + 1/t on a grid of
    t in [1, 1e6] (measured): the upper side closes the H = 0 DH gate, the
    lower side is the DH and Epstein scouts' beta rule."""
    from mpmath import mp, digamma, mpc, log, re
    with mp.workdps(30):
        for k in range(0, 601, 7):
            t = 10 ** (k / 100)
            v = re(digamma(mpc(0.75, t / 2)))
            assert log(t / 2) - 1 / mp.mpf(t) <= v <= log(t / 2) + 1 / mp.mpf(t)


def test_k2_gate_data_on_dh():
    d = _load(K2)
    assert d["L_DH"]["gate_closed_to_T_feasible"]
    assert d["L_DH"]["T_min_for_beta_positive"] > 3.4e6
    assert d["L_DH"]["coupling_components"][0] == [2, 3, 7, 13]
    assert d["1.4"]["coupling_components"][0] == [2, 3, 7]
    assert 1.2e4 < d["1.4"]["T_min_for_beta_positive"] < 1.25e4
    assert 22 not in [n for n, _ in d["L_DH"]["comb"]]
    tab = _load(TABLE)
    assert d["L_DH"]["dh_comb_floor_galerkin"] < float(tab["L_DH"]["S_star"]["lower"])


def test_epstein_gate():
    d = _load(HERE / "k2_epstein.json")
    for tag in ("1.6615", "L_DH"):
        r = d[tag]
        assert r["coupling_components"] == [[2, 3, 13], [5], [23]]
        assert all(c > 0 for _, c in r["comb"])
    assert [n for n, _ in d["L_DH"]["comb"]] == [4, 6, 8, 9, 12, 16, 18, 23, 25, 26, 27]


def test_k2_scouts_refuse_where_the_form_is_known_negative():
    """Measured stage-A blocks: wherever the rival's form is known negative on
    the window (DH at L_DH even; Epstein at L_DH even and at 1.6615 odd) every
    checkpoint with beta* > 0 has a negative pivot, so no bound."""
    d = _load(K2_SCOUTS)
    must = [k for k, v in d.items() if v["form_known_negative"]]
    assert must
    for key in must:
        rows = [r for r in d[key]["rows"] if "n_neg" in r]
        assert rows, key
        assert all(r["n_neg"] >= 1 for r in rows), key


# ------------------------------------------------------------- prices

def test_price_rules():
    p = price.price(6.2, float(price.WINDOWS["L_DH"]))
    assert abs(p["T_sharp"] - 2 * math.pi * math.exp(6.7)) < 1e-9
    assert p["N_rule"] == math.ceil(math.e * float(price.WINDOWS["L_DH"]) * p["T_sharp"] / 2)
    assert p["bits"] == 1280
    assert abs(price.assembly_core_hours(500, 500, 384) * 3600 - 4849.0) < 1e-6
    sa = price.assembly_core_hours(360, 525, 384, q=64, n_mat=3) * 3600
    assert 0.5 < sa / 2776.0 < 2.0


def test_bits_rule_proxy_points():
    assert price.bits_rule(1.4) == 640
    assert price.bits_rule(float(price.WINDOWS["L_DH"])) == 1280


# ------------------------------------------------------------- the scout

def test_scout_rows():
    d = _load(SCOUT)
    assert d["kind"] == "zeta" and d["parity"] == "even"
    rows = [r for r in d["rows"] if "n_neg" in r]
    assert rows
    for r in d["rows"]:
        T = r["T"]
        beta = math.log(T / (2 * math.pi)) - 1 / T - d["S"]
        assert abs(beta - r["beta"]) < 1e-9
    pos = [r for r in rows if r["n_neg"] == 0]
    lams = [float(r["lam_min"]) for r in pos]
    assert all(a <= b * (1 + 1e-6) for a, b in zip(lams, lams[1:]))   # R_{T#} increases with T#
    joint_env = _load(JOINT["1.4"])
    assert abs(d["S"] - joint_env["S"]) < 1e-12


# ------------------------------------------------------------- the streaming driver
#
# A small DH case at 7/5 (k2env_dh_1.4.json, N = 10 even modes, 256 bits, q = 16,
# 8 units of 20 panels to T# = 80; beta* > 0 from T# = 60), so units, reducer and
# streaming driver all run in seconds.

_SM = dict(L=Fraction(7, 5), env=HERE / "k2env_dh_1.4.json", N=10, q=16, h=Fraction(1, 2), prec=256)
_SM_UNITS = scout.plan(80, 20, Fraction(1, 2))
_SM_CPS = {float(Fraction(1, 2) * k1) for _, k1 in _SM_UNITS}
_SM_RESP = {60.0, 80.0}


def _strip(rows):
    return [{k: v for k, v in r.items() if k != "seconds"} for r in rows]


def _sm_stream(state_dir, **kw):
    return scout.stream(_SM["L"], _SM["env"], _SM["N"], _SM["q"], _SM["h"], _SM_UNITS, _SM["prec"],
                        state_dir, _SM_CPS, responses=_SM_RESP, **kw)


@pytest.fixture(scope="module")
def small_units(tmp_path_factory):
    d = tmp_path_factory.mktemp("units")
    files = [scout.run_unit((_SM["L"], str(_SM["env"]), _SM["N"], _SM["q"], _SM["h"], k0, k1, _SM["prec"],
                             str(d), "sm", "even", "fast"))[0] for k0, k1 in _SM_UNITS]
    keep = {}
    rows = scout.reduce(_SM["L"], _SM["env"], _SM["N"], _SM["h"], files, _SM_CPS, _SM["prec"],
                        responses=_SM_RESP, keep=keep)
    return {"files": files, "rows": rows, "C": keep["C"], "G": keep["G"]}


def _sources(files):
    return {(int(Path(f).stem.split("_")[-2]), int(Path(f).stem.split("_")[-1])): f for f in files}


def test_streaming_rows_equal_the_reducer_rows(small_units, tmp_path):
    """Same unit files through the ordered pool: identical rows (every midpoint
    string, pivot count, residual) and running sums whose midpoints equal the
    reducer's and whose balls overlap them."""
    ref = small_units["rows"]
    assert [r["T"] for r in ref] == sorted(_SM_CPS)
    assert sum("n_neg" in r for r in ref) == 3 and all("response" in r for r in ref if r["T"] in _SM_RESP)
    keep = {}
    rows, status = _sm_stream(tmp_path / "s", procs=2, sources=_sources(small_units["files"]), keep=keep)
    assert status == "done"
    assert _strip(rows) == _strip(ref)
    on_disk = [json.loads(x) for x in (tmp_path / "s" / "rows.jsonl").read_text().splitlines()]
    assert _strip(on_disk) == _strip(ref)
    N = _SM["N"]
    for name in ("C", "G"):
        A, B = keep[name], small_units[name]
        for i in range(N):
            for j in range(N):
                assert A[i, j].mid() == B[i, j].mid()
                assert A[i, j].overlaps(B[i, j])
    # computing the units inside the driver (no unit files) gives the same rows
    rows2, _ = _sm_stream(tmp_path / "c", procs=1)
    assert _strip(rows2) == _strip(ref)


def test_a_perturbed_unit_changes_the_streaming_rows(small_units, tmp_path):
    """Planted fault: one unit's C diagonal scaled by 1 + 2^-12 before the
    checkpoints with beta* > 0; every live row after it changes."""
    import pickle
    files = list(small_units["files"])
    bad = tmp_path / Path(files[1]).name
    with open(files[1], "rb") as fh:
        u = pickle.load(fh)
    N, k = _SM["N"], 0
    enc = []
    for i in range(N):
        for j in range(i + 1):
            m, e, r = u["C"][k]
            enc.append((m + (m >> 12) if i == j else m, e, r))
            k += 1
    u["C"] = enc
    with open(bad, "wb") as fh:
        pickle.dump(u, fh)
    files[1] = str(bad)
    rows, _ = _sm_stream(tmp_path / "s", sources=_sources(files))
    ref = small_units["rows"]
    live = [(a, b) for a, b in zip(rows, ref) if "n_neg" in b]
    assert live and all(a["lam_min"] != b["lam_min"] for a, b in live)


@pytest.mark.parametrize("k", [1, 6])
def test_streaming_resume_after_a_stop_gives_identical_rows(small_units, tmp_path, k):
    """Stopped after unit k (state saved, a stale row appended to rows.jsonl as
    if the kill came between the two writes), then resumed: identical rows, and
    at most two generations of state files on disk."""
    src = _sources(small_units["files"])
    rows, status = _sm_stream(tmp_path / "s", sources=src, stop_after=k)
    assert status == "stopped: stop_after"
    meta = json.loads((tmp_path / "s" / "state.json").read_text())
    assert meta["k1"] == _SM_UNITS[k - 1][1]
    with open(tmp_path / "s" / "rows.jsonl", "a") as fh:
        fh.write(json.dumps({"T": -1.0}) + "\n")
    rows, status = _sm_stream(tmp_path / "s", sources=src)
    assert status == "done"
    assert _strip(rows) == _strip(small_units["rows"])
    on_disk = [json.loads(x) for x in (tmp_path / "s" / "rows.jsonl").read_text().splitlines()]
    assert _strip(on_disk) == _strip(small_units["rows"])
    assert len(list((tmp_path / "s").glob("state_*.pkl"))) <= 4


def test_streaming_refuses_a_state_from_other_parameters(small_units, tmp_path):
    src = _sources(small_units["files"])
    _sm_stream(tmp_path / "s", sources=src, stop_after=1)
    with pytest.raises(SystemExit):
        scout.stream(_SM["L"], _SM["env"], _SM["N"], _SM["q"], _SM["h"], _SM_UNITS, _SM["prec"] + 64,
                     tmp_path / "s", _SM_CPS, sources=src)


def test_streaming_stops_at_the_core_hour_cap(small_units, tmp_path):
    rows, status = _sm_stream(tmp_path / "s", sources=_sources(small_units["files"]), cap_core_seconds=1e-9)
    assert status.startswith("stopped: projected")
    assert json.loads((tmp_path / "s" / "state.json").read_text())["k1"] == _SM_UNITS[0][1]


# ------------------------------------------------------------- explorations

def test_overlapping_clusters_value():
    d = _load(HERE / "overlap_L_DH.json")
    tab = _load(TABLE)["L_DH"]
    assert d["V_overlap"] <= d["partition_value"]
    assert d["V_overlap"] >= float(tab["S_star"]["lower"]) - 5e-3


def test_envelope_transfer_witness():
    """K2, transfer: zeta's joint envelope is not an envelope for the DH comb:
    at an explicit dyadic t the Arb value of P_DH - H_zeta exceeds S_zeta,
    while the control P_zeta - H_zeta stays below it."""
    found = False
    for tag in ("1.4", "L_DH"):
        p = HERE / f"transfer_{tag}.json"
        if not p.exists():
            continue
        found = True
        d = json.loads(p.read_text())
        assert d["dh"]["exceeds_S"]
        assert d["zeta"]["below_S"]
    if not found:
        pytest.skip("no transfer file")


# ------------------------------------------------------------- PRICE.md pins

def _md():
    return (HERE / "PRICE.md").read_text(encoding="utf-8")


def _down(x: float, k: int = 6) -> str:
    return f"{math.floor(x * 10 ** k) / 10 ** k:.{k}f}"


def _up(x: float, k: int = 6) -> str:
    return f"{math.ceil(x * 10 ** k) / 10 ** k:.{k}f}"


@pytest.mark.parametrize("tag", list(price.WINDOWS))
def test_price_md_quotes_the_table(tag):
    md = _md()
    t = _load(TABLE)[tag]
    ball = f"[{_down(float(t['S_star']['lower']))}, {_up(float(t['S_star']['upper']))}]"
    assert ball in md, ball
    assert f"{float(t['S_sep']['lower']):.6f}" in md
    for D in ("16", "64"):
        assert f"{t['S_sep_sine'][D]['S_float']:.6f}" in md
    for b, part in t["partitions"].items():
        assert f"{part['value']:.4f}" in md


@pytest.mark.parametrize("tag", list(price.WINDOWS))
def test_price_md_quotes_the_joint_envelopes(tag):
    md = _md()
    d = _load(JOINT[tag])
    assert _up(d["S"]) in md, _up(d["S"])


def test_hunt_prose_has_no_em_dash():
    dash = chr(0x2014)
    for name in ("PRICE.md", "MISSION.md", "RUNS.md"):
        assert dash not in (HERE / name).read_text(encoding="utf-8")
