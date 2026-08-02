"""
Tests for zeta.explicit — the explicit formula (primes ⟷ zeros).

Ground truth used here:
  ψ(10)   = log(2³·3²·5·7) = log 2520 = 7.8320141805…
  θ(10)   = log(2·3·5·7)   = log 210
  π(100)  = 25,  π(1000) = 168
  γ₁      = 14.134725141734693790, …
  R(100)  = 25.6616332669…
  li(2)   = 1.0451637801174927848…
  J(10)   = 4 + 2/2 + 1/3 = 16/3,   J(100) = 25 + 4/2 + 2/3 + 2/4 + 1/5 + 1/6

Tolerances policy: every numerical tolerance below is set to roughly twice the
error actually measured on this machine, so a real regression fails the test.
Where a formula genuinely does not converge fast (the Möbius series for R, the
peak heights of the prime spectrum) the test asserts the *true* behaviour —
oscillation bounds, monotone improvement in T — instead of a fake tight bound.
"""

from __future__ import annotations

import math

import numpy as np
import pytest
from mpmath import mp

from zeta.explicit import (
    LI2,
    J_from_zeros,
    Li,
    R,
    as_gammas,
    convergence_table,
    first_zeros,
    li,
    mangoldt,
    pi_from_zeros,
    pi_true,
    prime_spectrum,
    psi_curve,
    psi_from_zeros,
    psi_staircase,
    psi_true,
    spectrum_peaks,
    theta_cheb,
)

# first ten zero ordinates, verified independently
GAMMA_10 = [
    14.134725141734693790,
    21.022039638771554993,
    25.010857580145688763,
    30.424876125859513210,
    32.935061587739189691,
    37.586178158825671257,
    40.918719012147495187,
    43.327073280914999519,
    48.005150881167159727,
    49.773832477672302182,
]


@pytest.fixture(scope="session")
def zeros500() -> np.ndarray:
    """First 500 zero ordinates (cached to data/explicit_zeros.npz after the first run)."""
    return first_zeros(500)


# ---------------------------------------------------------------------------
# the exact prime side
# ---------------------------------------------------------------------------


def test_mangoldt():
    assert mangoldt(1) == 0.0
    assert mangoldt(2) == pytest.approx(math.log(2))
    assert mangoldt(8) == pytest.approx(math.log(2))
    assert mangoldt(9) == pytest.approx(math.log(3))
    assert mangoldt(121) == pytest.approx(math.log(11))
    for n in (1, 6, 10, 12, 15, 100):
        assert mangoldt(n) == 0.0


def test_mangoldt_against_sympy_oracle():
    """Λ(n) exhaustively vs sympy.factorint for every n ≤ 500 — a real oracle."""
    import sympy

    for n in range(1, 501):
        f = sympy.factorint(n)
        want = float(math.log(next(iter(f)))) if len(f) == 1 else 0.0
        assert mangoldt(n) == pytest.approx(want, abs=1e-13), n


def test_psi_true_small():
    # ψ(10) = log(2^3 · 3^2 · 5 · 7) = log 2520
    assert psi_true(10) == pytest.approx(math.log(2**3 * 3**2 * 5 * 7), abs=1e-12)
    assert psi_true(10) == pytest.approx(math.log(2520), abs=1e-12)
    assert psi_true(10) == pytest.approx(7.832014180505469, abs=1e-12)
    assert psi_true(1) == 0.0
    assert psi_true(1.5) == 0.0
    assert psi_true(2) == pytest.approx(math.log(2))
    # ψ(x) = log lcm(1..⌊x⌋)
    import math as _m

    lcm = 1
    for k in range(1, 31):
        lcm = lcm * k // _m.gcd(lcm, k)
    assert psi_true(30) == pytest.approx(math.log(lcm), rel=1e-13)


def test_psi_jumps_at_prime_powers():
    # ψ is a step function that jumps by Λ(n) exactly at n = p^k
    for n, lam in [(2, math.log(2)), (3, math.log(3)), (4, math.log(2)), (8, math.log(2)), (9, math.log(3))]:
        assert psi_true(n) - psi_true(n - 0.5) == pytest.approx(lam, abs=1e-12)
    for n in (6, 10, 12, 15):  # no jump at non-prime-powers
        assert psi_true(n) - psi_true(n - 0.5) == pytest.approx(0.0, abs=1e-12)


def test_theta_cheb():
    assert theta_cheb(10) == pytest.approx(math.log(2 * 3 * 5 * 7), abs=1e-12)
    assert theta_cheb(1) == 0.0
    # ψ(x) = Σ_k θ(x^{1/k})
    for x in (10.0, 100.0, 1000.0):
        s = 0.0
        k = 1
        while x ** (1.0 / k) >= 2.0:
            s += theta_cheb(x ** (1.0 / k))
            k += 1
        assert s == pytest.approx(psi_true(x), rel=1e-12)


def test_pi_true():
    assert pi_true(1) == 0
    assert pi_true(2) == 1
    assert pi_true(10) == 4
    assert pi_true(100) == 25
    assert pi_true(1000) == 168
    assert pi_true(10**5) == 9592


def test_psi_staircase_matches_psi_true():
    xs = np.linspace(2.0, 200.0, 400)
    ref = np.array([psi_true(x) for x in xs])
    assert np.allclose(psi_staircase(xs), ref, atol=1e-12)


def test_psi_staircase_is_exact_at_the_jumps():
    """Right-continuity: the jump at n = p^k must be taken at exactly x = n."""
    xs = []
    for n in (2, 3, 4, 5, 7, 8, 9, 16, 25, 27, 31, 32, 49, 64, 81, 121, 125, 127, 128):
        xs += [n - 1e-9, float(n), n + 1e-9]
    xs = np.array(xs)
    ref = np.array([psi_true(x) for x in xs])
    assert np.max(np.abs(psi_staircase(xs) - ref)) < 1e-13
    # and the jump height at x = n is Λ(n)
    for n in (2, 4, 8, 9, 25, 27, 49, 121, 127):
        lo = float(psi_staircase(np.array([n - 1e-9]))[0])
        hi = float(psi_staircase(np.array([float(n)]))[0])
        assert hi - lo == pytest.approx(mangoldt(n), abs=1e-12), n
    assert psi_staircase(np.float64(10.0)).shape == ()  # 0-d passes through


# ---------------------------------------------------------------------------
# li, Li, R
# ---------------------------------------------------------------------------


def test_li_against_mpmath_oracle():
    assert li(2) == pytest.approx(LI2, abs=1e-15)
    assert Li(2) == pytest.approx(0.0, abs=1e-15)
    with mp.workdps(30):
        for x in (0.5, 2.0, 10.0, 100.0, 1e6):
            assert li(x) == pytest.approx(float(mp.li(x)), rel=1e-15)
    assert li(100, offset=True) == pytest.approx(li(100) - LI2, abs=1e-12)
    # exact double-precision values (mpmath, 30 dps, rounded)
    assert li(100) == pytest.approx(30.126141584079630, rel=1e-14)
    assert li(1e6) == pytest.approx(78627.549159462182, rel=1e-14)
    assert li(1.0) == float("-inf")
    with pytest.raises(ValueError):
        li(0.0)


def test_R_gram_series():
    assert R(100) == pytest.approx(25.661633266924184, rel=1e-13)
    assert R(1e6) == pytest.approx(78527.399429127700, rel=1e-13)
    # R is a much better approximation to π than li
    for x in (1e4, 1e5, 1e6):
        assert abs(R(x) - pi_true(x)) < abs(li(x) - pi_true(x))


def test_R_against_mpmath_riemannr_oracle():
    """Our Gram series vs mpmath.riemannr — an entirely independent implementation."""
    with mp.workdps(30):
        for x in (0.5, 1.0, 2.0, 10.0, 100.0, 1000.0, 1e6, 1e12):
            assert R(x) == pytest.approx(float(mp.riemannr(x)), rel=1e-14)
    with pytest.raises(ValueError):
        R(-1.0)


def test_R_terms_cap_is_honoured():
    """`terms` really truncates Gram's series: fewer terms ⇒ a worse value."""
    exact = R(100.0)
    partials = [R(100.0, terms=k) for k in (1, 2, 5, 10, 20, 60)]
    errs = [abs(p - exact) for p in partials]
    assert errs == sorted(errs, reverse=True), errs  # monotone improvement
    assert errs[0] > 1.0  # one term is genuinely bad
    assert errs[-1] < 1e-12  # 60 terms is converged
    assert R(100.0, terms=10_000) == pytest.approx(exact, rel=1e-15)


def test_R_matches_its_mobius_definition_loosely():
    """
    R(x) = Σ_n μ(n)/n li(x^{1/n}).  That series converges only conditionally (its
    tail is Σ_{n>N} μ(n)/n·(γ + log log x − log n), which is PNT-hard), so the
    partial sums merely *oscillate* around the Gram value with amplitude ~0.1
    even at N = 400.  Assert exactly that, and nothing stronger.
    """
    from zeta.explicit import _R_mobius

    target = R(100.0)
    partials = [_R_mobius(100.0, N) for N in (100, 200, 400)]
    # measured deviations: -0.0753, +0.0969, -0.0300 — they do NOT shrink
    for v in partials:
        assert abs(v - target) < 0.15, (v, target)
    assert max(abs(v - target) for v in partials) > 0.02  # really is not converged
    assert abs(sum(partials) / len(partials) - target) < 0.05


def test_mobius_against_sympy_oracle():
    from zeta.explicit import _mobius

    import sympy

    for n in range(1, 301):
        assert _mobius(n) == int(sympy.mobius(n)), n


# ---------------------------------------------------------------------------
# zeros plumbing
# ---------------------------------------------------------------------------


def test_first_zeros_ground_truth():
    g = first_zeros(10)
    assert np.allclose(g, GAMMA_10, atol=1e-12)
    assert first_zeros(0).size == 0
    assert first_zeros(-3).size == 0


def test_first_zeros_high_index_against_mpmath_oracle(zeros500):
    """Guard against an off-by-one in the cache-extension loop."""
    with mp.workdps(25):
        for k in (1, 2, 10, 100, 500):
            assert zeros500[k - 1] == pytest.approx(float(mp.im(mp.zetazero(k))), abs=1e-12), k
    # Riemann–von Mangoldt sanity: 29 ordinates below 100
    assert int(np.sum(zeros500 < 100.0)) == 29
    assert np.all(np.diff(zeros500) > 0.0)  # strictly increasing, no duplicates


def test_first_zeros_cache_is_extended_not_restarted(tmp_path, monkeypatch):
    """
    The cache-extension branch (``range(len(out)+1, n+1)``) is never touched
    when data/explicit_zeros.npz is already big enough, so exercise it against a
    deliberately short cache — this is where an off-by-one would hide.
    """
    import zeta.explicit as _E

    cache = tmp_path / "z.npz"
    np.savez_compressed(cache, gammas=np.array(GAMMA_10[:3]), dps=np.int64(25))
    monkeypatch.setattr(_E, "_ZEROS_CACHE", str(cache))
    monkeypatch.setattr(_E, "_DATA_DIR", str(tmp_path))
    g = _E.first_zeros(6)
    assert g.size == 6
    assert np.allclose(g, GAMMA_10[:6], atol=1e-12), g
    assert np.load(cache)["gammas"].size == 6  # extended in place
    assert np.allclose(_E.first_zeros(6), GAMMA_10[:6], atol=1e-12)  # served from cache
    assert np.allclose(_E.first_zeros(2), GAMMA_10[:2], atol=1e-12)  # truncated view


def test_as_gammas_accepts_every_form():
    g = first_zeros(5)
    assert np.allclose(as_gammas(5), g)
    assert np.allclose(as_gammas(list(g)), g)
    assert np.allclose(as_gammas(np.array([0.5 + 1j * t for t in g])), g)
    assert np.allclose(as_gammas(np.array([-t for t in g])), g)  # conjugates fold in
    assert np.allclose(as_gammas(tuple(reversed(list(g)))), g)  # sorted on the way out
    assert as_gammas([]).size == 0


def test_as_gammas_does_not_double_count_a_conjugate_pair():
    """
    Handing over the *full* conjugate-symmetric zero set {½±iγ} must give the
    same answer as handing over the ordinates γ — every consumer already adds
    the ρ̄ term itself, so a naive |Im ρ| fold would silently double the
    oscillatory part.
    """
    g = first_zeros(20)
    both = np.array([0.5 + 1j * t for t in g] + [0.5 - 1j * t for t in g])
    assert as_gammas(both).size == g.size
    assert np.allclose(as_gammas(both), g)
    assert psi_from_zeros(63.7, both) == pytest.approx(psi_from_zeros(63.7, g), rel=1e-14)
    # genuinely distinct ordinates are never merged
    assert as_gammas(np.array([14.0, 14.0 + 1e-3])).size == 2


# ---------------------------------------------------------------------------
# the von Mangoldt explicit formula
# ---------------------------------------------------------------------------


def test_psi_from_zeros_zero_zeros_is_the_main_term():
    x = 100.0
    expected = x - math.log(2 * math.pi) - 0.5 * math.log1p(-(x**-2.0))
    assert psi_from_zeros(x, []) == pytest.approx(expected, abs=1e-12)


def test_psi_real_form_equals_the_complex_sum(zeros500):
    """
    The module evaluates 2√x·cos(γ log x − arg ρ)/|ρ| instead of x^ρ/ρ + x^ρ̄/ρ̄.
    Check that reduction against honest complex arithmetic in mpmath — this is
    what would catch a wrong sign or the wrong branch of arg ρ.
    """
    g = zeros500[:50]
    for x in (2.5, 10.5, 63.7, 99.5, 1000.3):
        with mp.workdps(40):
            xv = mp.mpf(x)
            s = mp.mpf(0)
            for gam in g:
                rho = mp.mpc(mp.mpf(1) / 2, mp.mpf(float(gam)))
                s += 2 * mp.re(mp.power(xv, rho) / rho)
            ref = float(xv - s - mp.log(2 * mp.pi) - mp.mpf(1) / 2 * mp.log(1 - xv**-2))
        assert psi_from_zeros(x, g) == pytest.approx(ref, abs=1e-12), x


def test_trivial_zero_term_is_the_trivial_zeros(zeros500):
    """−½log(1−x⁻²) must equal −Σ_{n≥1} x^{−2n}/(−2n), the ρ = −2n contribution."""
    for x in (2.0, 10.0, 100.0):
        with mp.workdps(40):
            series = float(sum(-mp.mpf(x) ** (-2 * n) / (-2 * n) for n in range(1, 400)))
        d = psi_from_zeros(x, 10, include_trivial=True) - psi_from_zeros(x, 10, include_trivial=False)
        assert d == pytest.approx(series, rel=1e-12), x
        assert d == pytest.approx(-0.5 * math.log1p(-(x**-2.0)), abs=1e-14)
    d10 = psi_from_zeros(10.0, 10, True) - psi_from_zeros(10.0, 10, False)
    d100 = psi_from_zeros(100.0, 10, True) - psi_from_zeros(100.0, 10, False)
    assert d10 == pytest.approx(5.0251679e-3, rel=1e-6)
    assert d100 == pytest.approx(5.00025e-5, rel=1e-5)


@pytest.mark.parametrize(
    "x,err500",
    [
        (10.5, +0.01526),
        (20.5, -0.01038),
        (33.3, -0.01064),
        (47.5, +0.09851),
        (63.7, -0.05760),
        (88.2, +0.10398),
        (99.5, +0.05369),
    ],
)
def test_explicit_formula_reproduces_psi(x, err500, zeros500):
    """
    500 zeros pin ψ(x) to ~0.01–0.10 at these x — the errors are deterministic,
    so assert them individually (abs=0.01) as well as by a global bound.
    """
    est = psi_from_zeros(x, zeros500)
    assert est - psi_true(x) == pytest.approx(err500, abs=0.01), (x, est - psi_true(x))
    assert abs(est - psi_true(x)) < 0.15, (x, est, psi_true(x))


def test_explicit_formula_improves_with_more_zeros(zeros500):
    """RMS error over a grid must fall monotonically as zeros are added."""
    xs = np.linspace(10.25, 99.75, 179)  # step 0.5028
    # exactly one grid point is an integer (55 = 5·11) and it is not a prime
    # power, so psi_staircase is unambiguous everywhere on this grid
    ints = xs[np.abs(xs - np.round(xs)) < 1e-9]
    assert [int(round(v)) for v in ints] == [55]
    assert all(mangoldt(int(round(v))) == 0.0 for v in ints)
    truth = psi_staircase(xs)
    rms = [float(np.sqrt(np.mean((psi_curve(xs, zeros500[:n]) - truth) ** 2))) for n in (0, 10, 50, 100, 500)]
    assert rms == sorted(rms, reverse=True), rms
    # measured: 1.6263 → 1.0362 → 0.6725 → 0.5462 → 0.2767
    assert rms == pytest.approx([1.6263, 1.0362, 0.6725, 0.5462, 0.2767], abs=5e-4)
    # the *max* error barely moves: it is Gibbs overshoot at the jumps, 1.78 at N=500
    mx = float(np.max(np.abs(psi_curve(xs, zeros500) - truth)))
    assert 1.7 < mx < 1.9, mx


def test_explicit_formula_hits_psi0_at_a_prime_power(zeros500):
    """At x = p^k the formula converges to ψ(x) − Λ(x)/2, not ψ(x)."""
    x = 97.0
    psi0 = psi_true(x) - 0.5 * mangoldt(97)
    est = psi_from_zeros(x, zeros500)
    assert abs(est - psi0) < abs(est - psi_true(x))
    assert est == pytest.approx(psi0, abs=0.05)  # measured error −0.0102
    assert abs(est - psi_true(x)) > 2.0  # ψ itself is 2.29 away — the half-jump is real


def test_psi_curve_matches_scalar_and_rejects_x_le_1(zeros500):
    xs = np.array([12.3, 45.6, 78.9])
    got = psi_curve(xs, zeros500[:50])
    for x, v in zip(xs, got):
        assert v == pytest.approx(psi_from_zeros(x, zeros500[:50]), rel=1e-14)
    with pytest.raises(ValueError):
        psi_from_zeros(1.0, zeros500[:10])
    with pytest.raises(ValueError):
        psi_curve(np.array([5.0, 0.5]), zeros500[:10])


def test_psi_curve_chunking_is_transparent(zeros500):
    """The memory-bounding chunk loop must not change a single bit."""
    xs = np.linspace(10.0, 99.0, 10_000)  # > default chunk of 4096
    ref = psi_curve(xs, zeros500[:100])
    assert np.array_equal(psi_curve(xs, zeros500[:100], chunk=7), ref)
    assert np.array_equal(psi_curve(xs, zeros500[:100], chunk=10**6), ref)
    assert psi_curve(np.array([[10.0, 20.0], [30.0, 40.0]]), zeros500[:5]).shape == (2, 2)


def test_convergence_table(zeros500):
    rows = convergence_table(63.7, zeros500, counts=(0, 1, 10, 50, 100, 500))
    assert [r["n_zeros"] for r in rows] == [0, 1, 10, 50, 100, 500]
    assert rows[0]["gamma_max"] == 0.0
    assert rows[1]["gamma_max"] == pytest.approx(GAMMA_10[0], abs=1e-10)
    for r in rows:
        assert r["psi_true"] == pytest.approx(psi_true(63.7))
        assert r["abs_error"] == pytest.approx(abs(r["error"]))
        assert r["error"] == pytest.approx(r["psi_est"] - r["psi0_true"])
    # 63.7 is not a prime power, so ψ₀ = ψ there
    assert rows[0]["psi0_true"] == pytest.approx(psi_true(63.7))
    # measured |error|: 0.2182, 0.6910, 1.0277, 0.0576, 0.3342, 0.0576 — NOT monotone
    assert [round(r["abs_error"], 4) for r in rows] == pytest.approx(
        [0.2182, 0.6910, 1.0277, 0.0576, 0.3342, 0.0576], abs=1e-3
    )
    assert rows[-1]["abs_error"] < 0.1


def test_convergence_table_at_a_prime_power_uses_psi0(zeros500):
    rows = convergence_table(97.0, zeros500, counts=(500,), include_trivial=True)
    assert rows[0]["psi0_true"] == pytest.approx(psi_true(97.0) - 0.5 * mangoldt(97))
    assert rows[0]["abs_error"] < 0.05
    # include_trivial=False shifts every estimate by exactly the trivial-zero term
    off = convergence_table(97.0, zeros500, counts=(500,), include_trivial=False)
    assert rows[0]["psi_est"] - off[0]["psi_est"] == pytest.approx(
        -0.5 * math.log1p(-(97.0**-2.0)), abs=1e-14
    )


# ---------------------------------------------------------------------------
# Riemann's π(x)
# ---------------------------------------------------------------------------


def J_exact(y: float) -> float:
    """J(y) = Σ_{k≥1} π(y^{1/k})/k, computed from the exact π."""
    s, k = 0.0, 1
    while y ** (1.0 / k) >= 2.0:
        s += pi_true(y ** (1.0 / k)) / k
        k += 1
    return s


def test_J_exact_ground_truth():
    assert J_exact(10.0) == pytest.approx(4 + 2 / 2 + 1 / 3)  # = 16/3 = 5.33333…
    assert J_exact(100.0) == pytest.approx(25 + 4 / 2 + 2 / 3 + 2 / 4 + 1 / 5 + 1 / 6)  # 28.53333…


def test_J_from_zeros_reproduces_J(zeros500):
    """J(y) from the zeros; measured errors at 500 zeros are 0.0015 / 0.0046 / 0.0119."""
    for y, err in ((10.0, -0.0015), (50.0, -0.0046), (100.0, -0.0119)):
        got = J_from_zeros(y, zeros500)
        assert got - J_exact(y) == pytest.approx(err, abs=0.002), (y, got - J_exact(y))
        assert abs(got - J_exact(y)) < 0.05
    with pytest.raises(ValueError):
        J_from_zeros(1.0, zeros500[:5])


def test_J_from_zeros_improves_with_more_zeros(zeros500):
    e50 = abs(J_from_zeros(100.0, zeros500[:50]) - J_exact(100.0))
    e500 = abs(J_from_zeros(100.0, zeros500) - J_exact(100.0))
    assert e500 < e50 / 4.0, (e50, e500)


def test_J_tail_integral_term(zeros500):
    from zeta.explicit import _tail_integral

    # ∫_y^∞ dt/(t(t²−1)log t): 0.1400 at y=2, 9.876e-6 at y=100
    assert _tail_integral(2.0) == pytest.approx(0.1400101, rel=1e-5)
    assert _tail_integral(100.0) == pytest.approx(9.87567e-6, rel=1e-5)
    d = J_from_zeros(10.0, zeros500[:20], include_tail=True) - J_from_zeros(
        10.0, zeros500[:20], include_tail=False
    )
    assert d == pytest.approx(_tail_integral(10.0), rel=1e-12)


def test_mobius_inversion_of_J_is_exact():
    """
    π(x) = Σ_{n≤⌊log₂x⌋} μ(n)/n·J(x^{1/n}) is an identity, not an approximation.
    Feeding it the *exact* J must return π(x) to machine precision — this is what
    validates the cut-off N = ⌊log₂ x⌋ used inside pi_from_zeros.
    """
    from zeta.explicit import _mobius

    for x in (10.0, 50.0, 64.0, 100.0, 500.0, 1000.0, 1024.0, 10000.0):
        N = max(1, int(math.floor(math.log(x) / math.log(2.0))))
        s = sum(_mobius(n) / n * J_exact(x ** (1.0 / n)) for n in range(1, N + 1))
        assert s == pytest.approx(float(pi_true(x)), abs=1e-11), x
        assert x ** (1.0 / N) >= 2.0 and x ** (1.0 / (N + 1)) < 2.0  # N is the right cut-off


@pytest.mark.parametrize(
    "x,err500", [(50.0, -0.0103), (100.0, -0.0101), (500.0, -0.0381), (1000.0, +0.0103)]
)
def test_pi_from_zeros(x, err500, zeros500):
    est = pi_from_zeros(x, zeros500)
    assert est - pi_true(x) == pytest.approx(err500, abs=0.005), (x, est - pi_true(x))
    assert abs(est - pi_true(x)) < 0.1, (x, est, pi_true(x))
    # and it must beat the zero-free approximation R(x) at x = 100 and 1000
    if x in (100.0, 1000.0):
        assert abs(est - pi_true(x)) < abs(R(x) - pi_true(x))
    with pytest.raises(ValueError):
        pi_from_zeros(1.5, zeros500)


def test_pi_from_zeros_terms_override(zeros500):
    """`terms` truncates the Möbius inversion and is clamped at ⌊log₂ x⌋ = 6."""
    full = pi_from_zeros(100.0, zeros500)
    assert pi_from_zeros(100.0, zeros500, terms=1) == pytest.approx(
        J_from_zeros(100.0, zeros500), rel=1e-12
    )
    assert abs(pi_from_zeros(100.0, zeros500, terms=1) - 25) > 3.0  # J(100) ≈ 28.5, not π
    assert abs(pi_from_zeros(100.0, zeros500, terms=3) - 25) < 0.1
    for t in (6, 20, 10_000):  # clamped — identical results beyond N = 6
        assert pi_from_zeros(100.0, zeros500, terms=t) == pytest.approx(full, rel=1e-14)


def test_pi_from_zeros_R_form_bookkeeping(zeros500):
    """
    The two forms differ by exactly three terms; verify the decomposition rather
    than hand-waving a tolerance.  Measured at x = 100:
        (Σ_{n≤6} μ(n)/n li(100^{1/n}) − R(100)) = +0.11956
        − log2 · Σ_{n≤6} μ(n)/n               = −0.09242
        + Σ_{n≤6} μ(n)/n · tail(100^{1/n})    = −0.00026   →  net +0.02688
    """
    from zeta.explicit import _R_mobius, _mobius, _tail_integral

    a = pi_from_zeros(100.0, zeros500, form="mobius")
    b = pi_from_zeros(100.0, zeros500, form="R")
    N = 6
    mu_sum = sum(_mobius(n) / n for n in range(1, N + 1))
    tails = sum(_mobius(n) / n * _tail_integral(100.0 ** (1.0 / n)) for n in range(1, N + 1))
    predicted = (_R_mobius(100.0, N) - R(100.0)) - math.log(2) * mu_sum + tails
    assert a - b == pytest.approx(predicted, abs=1e-10)
    assert a - b == pytest.approx(0.026877, abs=1e-4)
    assert mu_sum == pytest.approx(2.0 / 15.0)  # 1 − 1/2 − 1/3 − 1/5 + 1/6
    assert abs(b - 25) < 0.1


# ---------------------------------------------------------------------------
# the dual view: the music of the primes
# ---------------------------------------------------------------------------


def test_prime_spectrum_peaks_land_on_log_p(zeros500):
    u = np.linspace(0.4, 4.7, 40001)
    sp = prime_spectrum(zeros500, u)
    peaks = spectrum_peaks(u, sp, n_peaks=14)
    assert len(peaks) >= 12
    for d in peaks:
        assert d["is_prime_power"], d
        # the peak sits on log(n) for a prime power n — measured max 4.4e-5
        assert abs(d["u"] - math.log(d["nearest_n"])) < 1e-4, d
        assert d["x"] == pytest.approx(math.exp(d["u"]), rel=1e-14)
    found = {d["nearest_n"] for d in peaks}
    assert {3, 5, 7, 11, 13, 17, 19, 23}.issubset(found)
    assert [d["height"] for d in peaks] == sorted((d["height"] for d in peaks), reverse=True)
    assert spectrum_peaks(u[:10], np.zeros(10)) == []


def test_spectrum_peaks_parabolic_refinement():
    """
    The sub-sample peak position is a 3-point parabola vertex,
    u* = u_j + ½(y₋−y₊)/(y₋−2y₀+y₊)·Δu.  On a synthetic bump whose centre is
    known this must beat the nearest sample by an order of magnitude (and a
    flipped sign would land twice as far away on the wrong side).
    """
    u = np.linspace(0.0, 1.0, 101)  # Δu = 0.01
    centre = 0.3337
    sp = np.exp(-(((u - centre) / 0.03) ** 2))
    pk = spectrum_peaks(u, sp, n_peaks=1)
    assert len(pk) == 1
    j = int(np.argmax(sp))
    assert abs(u[j] - centre) == pytest.approx(3.7e-3, abs=1e-4)  # nearest sample
    assert abs(pk[0]["u"] - centre) < 4e-4  # refined: measured 9.4e-5
    assert pk[0]["u"] > u[j]  # refinement moves toward the true centre
    assert pk[0]["height"] == pytest.approx(float(sp.max()))


def test_prime_spectrum_heights_are_lambda_over_sqrt_n(zeros500):
    """
    Heights → Λ(n)/√n, but from *below*: at finite T the truncation costs a
    systematic few percent (−1.3 % at n=2 … −6.3 % at n=8 with 500 zeros).
    """
    ns = [2, 3, 4, 5, 7, 8, 9]
    u = np.array([math.log(n) for n in ns])
    h = prime_spectrum(zeros500, u)
    for n, v in zip(ns, h):
        want = mangoldt(n) / math.sqrt(n)
        assert v == pytest.approx(want, rel=0.10), (n, v, want)
        assert v < want, (n, v, want)  # the deficit is systematic, never an excess


def test_prime_spectrum_deficit_shrinks_like_one_over_T(zeros500):
    """Doubling γ_max must roughly halve the height deficit — proof it converges."""
    ns = [2, 3, 4, 5, 7, 8, 9]
    u = np.array([math.log(n) for n in ns])
    h200 = prime_spectrum(zeros500[:200], u)
    h500 = prime_spectrum(zeros500, u)
    want = np.array([mangoldt(n) / math.sqrt(n) for n in ns])
    d200, d500 = want - h200, want - h500
    assert np.all(d500 > 0) and np.all(d200 > 0)
    assert np.all(d500 < 0.75 * d200), (d200, d500)


def test_prime_spectrum_background_at_non_prime_powers(zeros500):
    """
    At a non-prime-power the spectrum is not 0 but ≈ −√x/W(0): the comb sits on
    a smooth −e^{u/2} background.  Check the law, not just smallness.
    """
    from zeta.explicit import _window_weights

    T = float(zeros500.max())
    rr = np.linspace(0.0, T, 4001)
    w0 = float(np.trapezoid(_window_weights(rr, "gauss", T), rr)) / math.pi
    assert w0 == pytest.approx(154.4456, rel=1e-4)

    ns = [6, 10, 12, 14, 15, 18, 20, 50, 100]
    h = prime_spectrum(zeros500, np.array([math.log(n) for n in ns]))
    for n, v in zip(ns, h):
        assert v < 0.0, (n, v)
        assert v == pytest.approx(-math.sqrt(n) / w0, rel=0.25), (n, v, -math.sqrt(n) / w0)
    assert np.all(np.abs(h) < 0.07), dict(zip(ns, h))
    # and the prime-power peaks tower over the background
    peak2 = float(prime_spectrum(zeros500, np.array([math.log(2)]))[0])
    assert peak2 > 10 * float(np.abs(h[:7]).max())


def test_prime_spectrum_windows_and_shapes(zeros500):
    u = np.linspace(0.5, 3.0, 501)
    for win in ("gauss", "fejer", "none", None, lambda r: np.exp(-r / float(zeros500.max()))):
        sp = prime_spectrum(zeros500[:100], u, window=win)
        assert sp.shape == u.shape
        assert np.isfinite(sp).all()
    assert prime_spectrum([], u).shape == u.shape
    assert np.allclose(prime_spectrum([], u), 0.0)
    with pytest.raises(ValueError):
        prime_spectrum(zeros500[:10], u, window="bogus")
    assert prime_spectrum(zeros500[:5], np.log(np.array([[2.0, 3.0], [5.0, 7.0]]))).shape == (2, 2)


def test_prime_spectrum_normalisation_constant(zeros500):
    """
    normalize=True divides by W(0) = (1/π)∫₀^T w.  For the rectangular window
    that is exactly T/π, and the un-normalised peak of a Dirichlet kernel is
    (Λ(n)/√n)·T/π — an independent, closed-form check of the constant.
    """
    from zeta.explicit import _window_weights

    T = float(zeros500.max())
    u = np.array([math.log(n) for n in (2, 3, 5, 7)])
    raw = prime_spectrum(zeros500, u, window="none", normalize=False)
    nrm = prime_spectrum(zeros500, u, window="none", normalize=True)
    assert np.allclose(raw / nrm, T / math.pi, rtol=1e-9)
    for n, v in zip((2, 3, 5, 7), raw):
        want = mangoldt(n) / math.sqrt(n) * T / math.pi
        assert v == pytest.approx(want, rel=0.02), (n, v, want)
    # and for the tapered windows the divisor is the trapezoid of w, not T/π
    for win in ("gauss", "fejer"):
        rr = np.linspace(0.0, T, 4001)
        w0 = float(np.trapezoid(_window_weights(rr, win, T), rr)) / math.pi
        r = prime_spectrum(zeros500, u, window=win, normalize=False)
        m = prime_spectrum(zeros500, u, window=win, normalize=True)
        assert np.allclose(r / m, w0, rtol=1e-9), win
        assert w0 < T / math.pi  # tapering always removes mass


def test_prime_spectrum_chunking_is_transparent(zeros500):
    u = np.linspace(0.5, 4.5, 5000)  # > default chunk of 2048
    ref = prime_spectrum(zeros500[:100], u)
    assert np.array_equal(prime_spectrum(zeros500[:100], u, chunk=13), ref)
