"""
Tests for zeta.weil, the Riemann–Weil explicit formula and Weil positivity.

The load-bearing tests here are the explicit-formula agreement tests: the
convention implemented in ``zeta/weil.py`` (factor placement of the pole,
archimedean and prime terms) was *calibrated* by requiring the zero side
(computed from cached, independently verified zeros) to match the arithmetic
side (Γ-factors, primes, quadrature, no zeros) across three unrelated
test-function families.  These tests re-run that calibration.

Measured on this machine (tolerances below are set to roughly 2–10x the
measured error, so a real regression fails):

  Gaussian a = 0.01, dps 30:  |Δ| = 8.25e-32   (agreement 2.76e-31)
  Gaussian a = 0.002, dps 30: |Δ| = 2.81e-31   (agreement 7.88e-32)
  autocorr [1,1] σ=0.25:      agreement 6.3e-28
  autocorr [1,-1] σ=0.25:     agreement 1.4e-30
  autocorr [1,2,1] σ=0.3:     |Δ| = 2.49e-40 on a zero side of 1.99e-17
  Fejér b=1.5 / b=2, T=1e4:   |Δ| = 5.92e-5 / 3.33e-5, inside the tail
                              bound 1.19e-4 / 6.67e-5; the density tail
                              *estimate* matches Δ to 1.7e-5 / 2.0e-4 rel.
  Gaussian a=0.2 (probe):     W = 8.8603644e-18 from pieces of size ~2,
                              matching the direct zero sum (18 orders of
                              cancellation survive).
  log-margin slope (a-scan):  -199.79051 vs -γ₁² = -199.79045 (2.8e-7 rel)
  Backlund envelope:          max |N - RvM| = 0.984 over T ≤ 1e4, Q ≥ 5.49
  ψ(x)/x for x ≤ 1e5:         max 1.03883 < 1.04 (Rosser–Schoenfeld)
  Fejér prime-sum support:    n_max = 54 (b=2), 20 (b=1.5), finite, exact
"""

from __future__ import annotations

import math

import numpy as np
import pytest
from mpmath import mp

from zeta.weil import (
    GAMMA1,
    autocorrelation_pair,
    explicit_formula_sides,
    fejer_pair,
    gaussian_pair,
    legendre_pair,
    near_tightness_report,
    positivity_probe,
    weil_functional,
    _arch_term,
    _N_MAX_CAP,
    _pole_term,
    _prime_powers,
    _resolve_n_max,
    _w,
    _zeros_upto,
)

# ---------------------------------------------------------------------------
# Shared expensive results (computed once per module)
# ---------------------------------------------------------------------------


@pytest.fixture(scope="module")
def res_g001():
    h, g = gaussian_pair("0.01")
    return explicit_formula_sides(h, g, dps=30)


@pytest.fixture(scope="module")
def res_g0002():
    h, g = gaussian_pair("0.002")
    return explicit_formula_sides(h, g, dps=30)


@pytest.fixture(scope="module")
def res_fejer2():
    h, g = fejer_pair(2)
    return explicit_formula_sides(h, g, gamma_max=10000.0, dps=25)


@pytest.fixture(scope="module")
def res_fejer15():
    h, g = fejer_pair("1.5")
    return explicit_formula_sides(h, g, gamma_max=10000.0, dps=25)


@pytest.fixture(scope="module")
def res_fejer2_small():
    h, g = fejer_pair(2)
    return explicit_formula_sides(h, g, gamma_max=3000.0, dps=25)


# ---------------------------------------------------------------------------
# The pairs: Fourier partnership, positivity, closed forms
# ---------------------------------------------------------------------------


def _ft_defect(h, g, r, quad_pts):
    """h(r) - ∫ g(u) e^{iru} du, the measured defect of the pairing."""
    r = mp.mpf(r)
    rhs = mp.quad(lambda u: g(u) * mp.cos(r * u), quad_pts)
    return abs(h(r) - rhs)


def test_gaussian_pair_is_fourier_pair():
    with mp.workdps(30):
        h, g = gaussian_pair("0.01")
        pts = [-mp.inf, 0, mp.inf]
        assert _ft_defect(h, g, "0.7", pts) < mp.mpf("1e-28")
        assert _ft_defect(h, g, "2.3", pts) < mp.mpf("1e-28")


def test_fejer_pair_is_fourier_pair():
    with mp.workdps(30):
        b = mp.mpf(2)
        h, g = fejer_pair(b)
        pts = [-2 * b, 0, 2 * b]  # compact support, kinks at 0 and ±2b
        assert _ft_defect(h, g, "0.7", pts) < mp.mpf("1e-28")
        assert _ft_defect(h, g, "2.3", pts) < mp.mpf("1e-28")


def test_autocorrelation_pair_is_fourier_pair():
    with mp.workdps(30):
        h, g = autocorrelation_pair([1, -1, 2], spacing="1.5", sigma="0.4")
        pts = [-mp.inf, -3, 0, 3, mp.inf]
        assert _ft_defect(h, g, "0.7", pts) < mp.mpf("1e-27")
        assert _ft_defect(h, g, "2.3", pts) < mp.mpf("1e-27")


def test_pairs_nonnegative_on_real_axis():
    # h must be of positive type: h = |f̂|² >= 0 on the real line.
    with mp.workdps(25):
        pairs = [
            gaussian_pair("0.05")[0],
            fejer_pair("1.7")[0],
            autocorrelation_pair([1, -1], spacing=2.0, sigma="0.3")[0],
            autocorrelation_pair([1, 2, 1], spacing=1.0, sigma="0.5")[0],
        ]
        for h in pairs:
            vals = [h(mp.mpf(r) / 8) for r in range(-320, 321)]
            floor = -mp.mpf("1e-24") * max(abs(v) for v in vals)
            assert min(vals) >= floor


def test_gaussian_pole_term_closed_form(res_g001):
    # h(i/2) + h(-i/2) = 2 e^{a/4} exactly for h = e^{-a r²}
    with mp.workdps(30):
        expected = 2 * mp.e ** (mp.mpf("0.01") / 4)
        assert abs(res_g001["pole_term"] - expected) < mp.mpf("1e-28")


def test_fejer_pole_term_closed_form(res_fejer2):
    # (sin(ib/2)/(ib/2))² = (sinh(b/2)/(b/2))²
    with mp.workdps(25):
        expected = 2 * (mp.sinh(1) / 1) ** 2  # b = 2
        assert abs(res_fejer2["pole_term"] - expected) < mp.mpf("1e-23")


def test_pair_constructors_reject_bad_input():
    with pytest.raises(ValueError):
        gaussian_pair(-1)
    with pytest.raises(ValueError):
        fejer_pair(0)
    with pytest.raises(ValueError):
        autocorrelation_pair([0, 0])
    with pytest.raises(ValueError):
        autocorrelation_pair([1], sigma=0)


# ---------------------------------------------------------------------------
# LOAD-BEARING: explicit-formula agreement, three independent families
# ---------------------------------------------------------------------------


def test_explicit_formula_gaussian_a001(res_g001):
    # measured agreement 2.76e-31; anything near 1e-30 still means the
    # convention (pole + arch - 2·prime, g = (1/2π)∫h e^{-iru}) is exact.
    assert float(res_g001["agreement"]) < 1e-30
    assert float(res_g001["zero_side"]) == pytest.approx(0.29939602250755914, rel=1e-14)


def test_explicit_formula_gaussian_a0002(res_g0002):
    # wide h: 88 zeros contribute, prime term is ~5e-26, a genuinely
    # different balance of terms from a = 0.01.  Measured 7.9e-32.
    assert float(res_g0002["agreement"]) < 1e-30
    assert float(res_g0002["zero_side"]) == pytest.approx(3.5667624107582642, rel=1e-14)


def test_docs10_table_numbers_pinned(res_g001):
    # docs/10 §2 prints this exact decomposition for the Gaussian a = 0.01
    # pair and says the tests pin every quoted number, this test is that pin
    # (audit addition; every literal below re-measured independently first).
    with mp.workdps(30):
        assert abs(
            res_g001["zero_side"] - mp.mpf("0.299396022507559155789163943544")
        ) < mp.mpf("2e-29")
        assert abs(res_g001["pole_term"] - mp.mpf("2.005006255211590")) < mp.mpf("5e-16")
        assert abs(res_g001["arch_term"] - mp.mpf("-1.705593433712344")) < mp.mpf("5e-16")
        assert abs(res_g001["prime_term"] - mp.mpf("-1.6798991687e-5")) < mp.mpf("5e-16")
    assert res_g001["n_zeros_used"] == 28  # "the first 28 pairs ±γ suffice"
    assert res_g001["n_max"] == 7  # prime powers n = 2, 3, 4, 5, 7 only
    with mp.workdps(30):
        # "90.6% of the spectral side is the first zero pair"
        share = 2 * mp.e ** (-mp.mpf("0.01") * mp.mpf(GAMMA1) ** 2) / res_g001["zero_side"]
        assert abs(share - mp.mpf("0.906")) < mp.mpf("0.002")
        # "99.99998% of the prime side is the single shortest orbit n = 2"
        a = mp.mpf("0.01")
        g = lambda u: mp.e ** (-u * u / (4 * a)) / (2 * mp.sqrt(mp.pi * a))
        n2_term = mp.log(2) / mp.sqrt(2) * g(mp.log(2))
        assert abs(n2_term / (-res_g001["prime_term"] / 2) - 1) < mp.mpf("3e-8")


def test_explicit_formula_autocorrelation_members():
    with mp.workdps(30):
        h, g = autocorrelation_pair([1, 1], spacing=2.0, sigma="0.25")
        res = explicit_formula_sides(h, g, dps=30)
        assert float(res["agreement"]) < 1e-26  # measured 6.3e-28

        h, g = autocorrelation_pair([1, -1], spacing=2.0, sigma="0.25")
        res = explicit_formula_sides(h, g, dps=30)
        assert float(res["agreement"]) < 1e-28  # measured 1.4e-30
        # this member has h(0) = 0: pole term is negative, prime term
        # positive, positivity is carried entirely by the zeros.
        assert res["pole_term"] < 0 < res["prime_term"]
        assert res["zero_side"] > 0


def test_explicit_formula_gamma1_annihilating_member():
    # [1,2,1] at spacing 2: |f̂(r)|² ∝ |1+e^{2ir}|⁴ and 2γ₁ ≈ 9π, so h
    # nearly annihilates γ₁, the zero side is a *1e-17-sized* sum led by
    # γ₂, yet the arithmetic side matches to 2.5e-40 absolute (measured).
    with mp.workdps(30):
        h, g = autocorrelation_pair([1, 2, 1], spacing=2.0, sigma="0.3")
        res = explicit_formula_sides(h, g, dps=30)
        assert float(res["abs_diff"]) < 1e-38
        zs = float(res["zero_side"])
        assert 0 < zs < 1e-16
        # the cancelled mass is ~30: >17 digits of cancellation survive
        assert float(res["pole_term"]) > 25


def test_explicit_formula_fejer_within_tail_bound(res_fejer15, res_fejer2):
    # Fejér decays like 1/(bγ)², so the truncated zero tail dominates the
    # residual; the residual must sit inside the *bound* and match the
    # density *estimate*.
    for res in (res_fejer15, res_fejer2):
        assert float(res["abs_diff"]) < float(res["zero_side_tail_bound"])
        # missing tail is positive: arithmetic side exceeds truncated sum
        assert res["arithmetic_side"] > res["zero_side"]
        assert res["prime_tail_bound"] == 0  # compact support: exact sum


def test_fejer_tail_estimate_accounts_for_residual(res_fejer15, res_fejer2):
    # measured |Δ - est|/est: 1.7e-5 (b=1.5), 2.0e-4 (b=2).  After adding
    # the estimate back, the two sides agree to ~1.5e-6 relative, the
    # "6 significant digits after accounting for the tail" claim.
    for res in (res_fejer15, res_fejer2):
        diff = float(res["abs_diff"])
        est = float(res["zero_side_tail_estimate"])
        assert abs(diff - est) / est < 1e-3
        assert abs(diff - est) / float(res["zero_side"]) < 5e-6


# ---------------------------------------------------------------------------
# Tail bounds are honored (recompute-and-move test), and their ingredients
# ---------------------------------------------------------------------------


def test_zero_tail_bound_honored_by_recomputation(res_fejer2, res_fejer2_small):
    # enlarge gamma_max 3000 -> 10000: the zero side must move by less than
    # the tail bound claimed at 3000.  Measured move 6.17e-5, bound 1.91e-4.
    move = abs(float(res_fejer2["zero_side"]) - float(res_fejer2_small["zero_side"]))
    bound = float(res_fejer2_small["zero_side_tail_bound"])
    assert move < bound
    assert bound < 1e-3  # ... and the bound is not vacuous


def test_gaussian_tail_bound_negligible(res_g001):
    # e^{-0.01γ²} envelope: everything above the early-exit height is
    # certified below ~1e-36.
    assert float(res_g001["zero_side_tail_bound"]) < 1e-30


def test_backlund_envelope_empirical():
    # The tail bound leans on |N(T) - RvM(T)| <= 0.137 log T +
    # 0.443 log log T + 4.35.  Verify empirically over the cached zeros:
    # measured max gap 0.984, min Q 5.49, enormous slack.
    from zeta.statistics import zero_ordinates
    from zeta.zeros import riemann_von_mangoldt

    gammas = zero_ordinates(t_max=10000.0)
    Ts = np.linspace(50.0, 9950.0, 199)
    Ns = np.searchsorted(gammas, Ts)
    for T, n in zip(Ts, Ns):
        gap = abs(int(n) - riemann_von_mangoldt(T))
        Q = 0.137 * math.log(T) + 0.443 * math.log(math.log(T)) + 4.35
        assert gap < Q
        assert gap < 1.2  # observed slack, pinned so drift is noticed


def test_prime_tail_bound_honored_by_recomputation():
    # truncate the prime sum brutally (n_max = 50) and compare with the
    # full sum: the move must sit inside the claimed Rosser–Schoenfeld
    # bound.  Measured: move 2.76e-6, bound 2.54e-5.
    h, g = gaussian_pair("0.3")
    r50 = explicit_formula_sides(h, g, gamma_max=1400.0, n_max=50, dps=25)
    rbig = explicit_formula_sides(h, g, gamma_max=1400.0, n_max=200000, dps=25)
    move = abs(float(r50["prime_term"]) - float(rbig["prime_term"]))
    assert move < float(r50["prime_tail_bound"])
    assert float(rbig["prime_tail_bound"]) < 1e-40


def test_psi_rosser_schoenfeld_envelope_empirical():
    # ψ(x) < 1.04 x, used in the prime tail bound; the true sup of ψ(x)/x
    # is 1.03883... at x = 113 (re-measured here, not trusted).
    table = _prime_powers(100_000)
    ns = np.array([n for n, _ in table], dtype=np.int64)
    lps = np.array([math.log(p) for _, p in table])
    psi = np.cumsum(lps)
    ratios = psi / ns
    assert ratios.max() < 1.04
    n_at_max = int(ns[int(ratios.argmax())])
    assert n_at_max == 113
    assert ratios.max() == pytest.approx(1.03883, abs=5e-5)


# ---------------------------------------------------------------------------
# Prime-side machinery
# ---------------------------------------------------------------------------


def test_prime_powers_match_mangoldt_oracle():
    from zeta.explicit import mangoldt

    table = dict(_prime_powers(300))
    for n in range(2, 301):
        lam = math.log(table[n]) if n in table else 0.0
        assert lam == pytest.approx(mangoldt(n), abs=1e-12)


def test_wide_fejer_support_hits_n_max_cap():
    # e^{2b} for b = 9 would be ~6.6e7 prime powers; the support branch of
    # _resolve_n_max must cap at _N_MAX_CAP (the truncated tail is then
    # reported through the Rosser-Schoenfeld bound, not silently exact).
    _, g = fejer_pair(9)
    assert _resolve_n_max(g, None, 25) == _N_MAX_CAP


def test_explicit_formula_sech_fresh_family():
    # Adversarial re-derivation of the convention with a pair from OUTSIDE
    # the module's families: h(r) = sech(pi r/2), g(u) = sech(u)/pi (exact
    # Fourier partners; poles at r = ±i, exponential but non-Gaussian decay,
    # no compact support).  Every arithmetic piece has an independent closed
    # form: pole = 2*sqrt(2); prime = (4/pi) sum_k (-1)^k (zeta'/zeta)(3/2+2k)
    # via sech(log n) = 2n/(n^2+1) expanded geometrically.  Measured:
    # standalone two-sides diff 5.3e-32 at dps 30 on a zero side of 9.1e-10
    # (9 orders of cancellation); module-vs-closed-form 3.5e-26 at dps 25.
    with mp.workdps(30):
        h = lambda r: mp.sech(mp.pi * r / 2)
        g = lambda u: mp.sech(u) / mp.pi
        from zeta.zeros import first_n_zeros

        zero_side = mp.fsum(2 * h(z) for z in first_n_zeros(60))
        pole = 2 * mp.sqrt(2)  # h(i/2) + h(-i/2) = 2/cos(pi/4)
        arch = mp.quad(lambda r: h(r) * _w(r), [0, 2, 5, 15, 40, mp.inf]) / mp.pi
        terms, k = [], 0
        while True:
            s = mp.mpf(3) / 2 + 2 * k
            t = (-1) ** k * mp.zeta(s, derivative=1) / mp.zeta(s)
            terms.append(t)
            if abs(t) < mp.mpf("1e-38"):
                break
            k += 1
        prime_closed = 4 / mp.pi * mp.fsum(terms)
        assert abs(zero_side - (pole + arch + prime_closed)) < mp.mpf("1e-29")

    # the module's evaluator on the same hint-less pair must reproduce the
    # closed-form pieces, and its truncated prime term must sit inside the
    # reported tail bound (which must not be vacuous either).
    res = explicit_formula_sides(h, g, gamma_max=1000.0, n_max=30000, dps=25)
    with mp.workdps(30):
        sharp = res["pole_term"] + res["arch_term"] + prime_closed
        assert abs(res["zero_side"] - sharp) < mp.mpf("1e-23")
        trunc = abs(res["prime_term"] - prime_closed)
        assert trunc < res["prime_tail_bound"]  # honored...
        assert res["prime_tail_bound"] < 5 * trunc  # ...and not vacuous


def test_fejer_prime_sum_is_finite_and_exact():
    # b = 2: support of g is [-4, 4], so only n < e⁴ = 54.598... contribute:
    # n_max = 54 < 100, prime tail bound exactly 0, and enlarging n_max
    # changes NOTHING (g vanishes identically beyond its support).
    h, g = fejer_pair(2)
    assert _resolve_n_max(g, None, 25) == 54
    W_auto = weil_functional(h, g, dps=20)
    W_500 = weil_functional(h, g, n_max=500, dps=20)
    assert W_auto == W_500
    h, g = fejer_pair("1.5")
    assert _resolve_n_max(g, None, 25) == 20  # e³ = 20.08...


# ---------------------------------------------------------------------------
# The Weil functional and positivity probes
# ---------------------------------------------------------------------------


def test_weil_functional_equals_arithmetic_side(res_g001):
    h, g = gaussian_pair("0.01")
    W = weil_functional(h, g, dps=30)
    assert W == res_g001["arithmetic_side"]


def test_positivity_gaussian_family():
    probe = positivity_probe("gaussian", n_points=4, dps=20)
    assert all(d["positive"] for d in probe)
    # margin collapses monotonically as h concentrates in (-γ₁, γ₁)
    margins = [float(d["margin"]) for d in probe]
    assert margins == sorted(margins, reverse=True)
    assert probe[-1]["is_tightest"]
    # the a = 0.2 member: W ~ 8.86e-18 out of pieces of size ~2, sign
    # certified by automatic dps escalation (measured 8.8603644e-18,
    # matching the dps-45 reference 8.860364360447e-18)
    assert probe[-1]["dps_used"] > 20
    assert float(probe[-1]["W"]) == pytest.approx(8.860364360447e-18, rel=1e-6)


def test_positivity_fejer_family():
    probe = positivity_probe("fejer", n_points=3, param_range=(1.0, 2.0), dps=15)
    assert all(d["positive"] for d in probe)
    assert all(float(d["W"]) > 1e-3 for d in probe)


def test_positivity_autocorrelation_family():
    probe = positivity_probe(
        "autocorrelation", n_points=3, param_range=(0.15, 0.35), dps=15
    )
    assert all(d["positive"] for d in probe)
    # σ = 0.35 member is ~1e-10: needs escalation to certify
    assert probe[-1]["dps_used"] > 15


def test_positivity_probe_input_validation():
    with pytest.raises(ValueError):
        positivity_probe("no-such-family")
    with pytest.raises(ValueError):
        positivity_probe(lambda p: gaussian_pair(p))  # callable needs range


def test_gamma1_constant_matches_zeros_module():
    from zeta.zeros import first_n_zeros

    assert abs(float(first_n_zeros(1)[0]) - GAMMA1) < 1e-15


# ---------------------------------------------------------------------------
# Near-tightness reconnaissance
# ---------------------------------------------------------------------------


def test_near_tightness_gamma1_controls_margin():
    # measured (a-scan 0.05/0.10/0.15, dps 30): fitted slope of log W(a)
    # is -199.79051 vs -γ₁² = -199.79045 (rel err 2.8e-7); γ₁ carries
    # >99.9999% of the zero side at the tightest member; the arithmetic
    # side agrees with the direct zero sum to ~1e-27 through >13 digits
    # of cancellation.
    rep = near_tightness_report(
        gaussian_a=(0.05, 0.10, 0.15), dps=30, include_fejer=False
    )
    assert rep["slope_rel_error"] < 1e-5
    assert rep["gamma1_share_at_tightest"] > 0.999999
    assert rep["max_cancellation_digits"] > 12
    for d in rep["gaussian_scan"]:
        assert d["W"] > 0
        assert d["rel_agreement"] < 1e-20
    assert rep["tightest_member"]["a"] == 0.15
    assert "gamma1" in rep["narrative"]


# ---------------------------------------------------------------------------
# Internals: zero data plumbing and the archimedean integral
# ---------------------------------------------------------------------------


def test_zeros_upto_hybrid_is_complete_and_ordered():
    from zeta.statistics import zero_ordinates

    with mp.workdps(30):
        zs = list(_zeros_upto(2000.0))
    gammas = zero_ordinates(t_max=10000.0)
    assert len(zs) == int(np.searchsorted(gammas, 2000.0))  # == N(2000) = 1517
    assert len(zs) == 1517
    assert all(zs[i] < zs[i + 1] for i in range(len(zs) - 1))
    assert abs(float(zs[0]) - GAMMA1) < 1e-12


def test_archimedean_density_value():
    # w(0) = ψ(1/4) - log π = -γ - 3 log 2 - π/2 - log π (closed form)
    with mp.workdps(30):
        expected = -mp.euler - 3 * mp.log(2) - mp.pi / 2 - mp.log(mp.pi)
        assert abs(_w(0) - expected) < mp.mpf("1e-28")


def test_pole_term_of_even_analytic_h_is_real():
    with mp.workdps(25):
        h, _ = autocorrelation_pair([1, -1, 1], spacing="1.3", sigma="0.6")
        v = _pole_term(h)
        assert mp.im(v) == 0  # returned as a real mpf, not an mpc
        assert v > 0  # closed form: 2πσ²e^{σ²/4}·(3 - 4cosh(.65) + 2cosh(1.3))


def test_pole_term_rejects_non_even_h():
    # Schwarz reflection makes h(i/2) + h(-i/2) real for ANY h that is
    # real-valued on the reals, so a wrong (non-even) h can only be caught
    # by comparing h(r) with h(-r) directly, which _pole_term now does.
    with mp.workdps(25):
        with pytest.raises(ValueError):
            _pole_term(lambda r: mp.e ** (-((r - 1) ** 2)))


def test_explicit_formula_sides_key_contract(res_g001):
    for key in (
        "zero_side",
        "zero_side_tail_bound",
        "zero_side_tail_estimate",
        "pole_term",
        "arch_term",
        "prime_term",
        "prime_tail_bound",
        "arithmetic_side",
        "agreement",
        "abs_diff",
        "n_zeros_used",
        "n_max",
        "gamma_max",
    ):
        assert key in res_g001
    with mp.workdps(30):  # the dict holds dps-30 values; sum at that dps
        resum = (
            res_g001["pole_term"] + res_g001["arch_term"] + res_g001["prime_term"]
        )
        assert abs(res_g001["arithmetic_side"] - resum) < mp.mpf("1e-28")


# ---------------------------------------------------------------------------
# Slow tier: independent-oracle cross-checks
# ---------------------------------------------------------------------------


@pytest.mark.slow
def test_fejer_arch_integral_vs_quadosc_oracle():
    # the fast path integrates the oscillatory tail by parts analytically
    # (polygamma derivatives); mp.quadosc is the independent oracle.
    # Measured difference 4.6e-25 at dps 35.
    h, _ = fejer_pair(2)
    with mp.workdps(35):
        fast = _arch_term(h, 25)
        b = mp.mpf(2)
        P = mp.pi / b
        K = int(mp.ceil(45 / float(P)))
        A = K * P
        I_main = mp.quad(lambda r: h(r) * _w(r), [k * P for k in range(K + 1)])
        I_smooth = mp.quad(
            lambda r: _w(r) / (r * r), [A, 2 * A, 8 * A, 32 * A, mp.inf]
        )
        I_osc = mp.quadosc(
            lambda r: mp.cos(2 * b * r) * _w(r) / (r * r), [A, mp.inf], period=P
        )
        ref = (I_main + (I_smooth - I_osc) / (2 * b * b)) / mp.pi
        assert abs(fast - ref) < mp.mpf("1e-22")


@pytest.mark.slow
def test_near_tightness_full_report():
    rep = near_tightness_report()
    # slope contaminated only by the γ₂ term at small a: measured 1.48e-4
    assert rep["slope_rel_error"] < 5e-4
    assert rep["max_cancellation_digits"] > 17  # a = 0.2: W ~ 9e-18
    assert all(d["W"] > 0 for d in rep["gaussian_scan"])
    assert all(d["W"] > 0 for d in rep["fejer_scan"])
    # Σ 1/γ² partial to T=1e4: measured 0.0229717; the full sum is
    # 0.0231050 and the difference is exactly the predicted 1.33e-4 tail
    assert rep["sum_inv_gamma_sq_partial"] == pytest.approx(0.0229717, abs=2e-6)
    # γ₁ alone carries ~22% of Σ 1/γ² (measured 0.2179)
    assert 0.20 < rep["gamma1_share_of_sum"] < 0.24
    # W·b² hovers around Σ 1/γ² with sin²(bγ) oscillation
    for d in rep["fejer_scan"]:
        assert 0.01 < d["W_times_b2"] < 0.04


# ---------------------------------------------------------------------------
# The Legendre pair: the explicit formula localised to [n², (n+1)²]
# ---------------------------------------------------------------------------


@pytest.fixture(scope="module")
def res_legendre10():
    h, g = legendre_pair(10)
    return explicit_formula_sides(h, g, gamma_max=500.0, n_max=122, dps=25)


def test_legendre_pair_is_fourier_pair():
    # Same convention check as the other pairs: h(r) = ∫ g(u) e^{iru} du,
    # integrated over the compact support with the triangle kinks as nodes.
    with mp.workdps(30):
        h, g = legendre_pair(4)
        A, B = 2 * mp.log(4), 2 * mp.log(5)
        C = (A + B) / 2
        pts = [-B, -C, -A, 0, A, C, B]
        assert _ft_defect(h, g, "0.7", pts) < mp.mpf("1e-28")
        assert _ft_defect(h, g, "2.3", pts) < mp.mpf("1e-28")


def test_legendre_pair_support_is_exactly_the_interval():
    with mp.workdps(25):
        h, g = legendre_pair(10)
        A, B = 2 * mp.log(10), 2 * mp.log(11)
        # The pair freezes its endpoints at 60 digits; the ambient-25 A and B
        # here sit within 1e-24 of them, so the edge values are that small,
        # not exactly zero.
        assert g(A) < mp.mpf("1e-20") and g(B) < mp.mpf("1e-20")
        assert g(-A) < mp.mpf("1e-20") and g(-B) < mp.mpf("1e-20")
        assert g(h.weil_hints["support"]) == 0   # the exact endpoint is exact
        assert abs(g((A + B) / 2) - 1) < mp.mpf("1e-20")  # unit height at centre
        assert g(A - mp.mpf("0.01")) == 0        # nothing outside
        assert g(B + mp.mpf("0.01")) == 0
        assert g(A + mp.mpf("1e-6")) > 0         # everything inside
        assert h.weil_hints["n"] == 10


def test_legendre_pole_term_closed_form():
    # h(i/2) = 2W cosh(C/2) (sinh(W/4)/(W/4))², and h is even.
    with mp.workdps(30):
        h, _ = legendre_pair(10)
        W = mp.log(11) - mp.log(10)
        C = mp.log(110)
        expected = 2 * W * mp.cosh(C / 2) * (mp.sinh(W / 4) / (W / 4)) ** 2
        measured = h(mp.mpc(0, "0.5"))
        assert abs(measured - expected) < mp.mpf("1e-27")
        assert abs(h(mp.mpc(0, "-0.5")) - expected) < mp.mpf("1e-27")


def test_legendre_pair_rejects_small_n():
    with pytest.raises(ValueError):
        legendre_pair(1)
    with pytest.raises(ValueError):
        legendre_pair(0)


def test_legendre_envelope_majorises_h():
    with mp.workdps(25):
        h, _ = legendre_pair(6)
        env = h.weil_hints["envelope"]
        for r in ("0.1", "1", "7.3", "40", "333"):
            r = mp.mpf(r)
            assert abs(h(r)) <= env(r) * (1 + mp.mpf("1e-20"))


def test_legendre_explicit_formula_within_tail_bound(res_legendre10):
    # h decays like 1/r² (g is only C⁰), so the truncated zero tail dominates;
    # the residual must sit inside the bound and the prime sum is exact.
    assert float(res_legendre10["abs_diff"]) < float(
        res_legendre10["zero_side_tail_bound"]
    )
    assert res_legendre10["prime_tail_bound"] == 0


def test_legendre_prime_term_matches_sieve_oracle(res_legendre10):
    # The engine's prime term against a hand-rolled sieve of the open interval
    # (100, 121): the primes 101, 103, 107, 109, 113 and no other prime power
    # (121 = 11² sits on the boundary, where g vanishes).
    from sympy import isprime

    with mp.workdps(35):
        _, g = legendre_pair(10)
        ks = [k for k in range(101, 121) if isprime(k)]
        assert ks == [101, 103, 107, 109, 113]
        oracle = -2 * mp.fsum(
            mp.log(k) * g(mp.log(k)) / mp.sqrt(k) for k in ks
        )
        assert abs(res_legendre10["prime_term"] - oracle) < mp.mpf("1e-20")
