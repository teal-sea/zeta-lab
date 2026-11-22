"""Regression for the false converse about the local rational kernel.

The rational closed form can be positive where the Satake bound fails, so it
cannot carry the converse. These tests pin that, pin that the gate itself is
not fooled by the same input, and pin the measured least-PSD-diagonal numbers
quoted in ``CORRECTIONS.md`` ("Later correction").

The second half pins the regime reading of ``gate()`` on oscillating
weights. Until the repair for issue 335 it misread conjugate pairs in both
directions (``CORRECTIONS.md``, "Found while landing this correction", and
``DIAGNOSIS-335.md``); those pins were changed on purpose in that repair.
What remains pinned as a limitation is narrower: in the summable regime an
excess the truncation estimate cannot resolve still reads as PASS.
"""

import cmath
import math

import numpy as np

from hunts.local_positivity import localpos
from hunts.local_positivity.localpos import (
    gate,
    lesion_sweep,
    local_lambdas,
    null_distribution,
    ramanujan_violator,
    reference_table,
    satake_kernel,
    satake_local,
    threshold,
)

COUNTEREXAMPLE = (3 * math.sqrt(2), 0, 0, 0)


def least_psd_diagonal(s: np.ndarray, n: int) -> float:
    """Least ``c`` making the ``n x n`` Toeplitz section with diagonal ``c`` and
    off-diagonals ``s[1:n]`` positive semidefinite (real symmetric ``s``)."""
    idx = np.abs(np.subtract.outer(np.arange(n), np.arange(n)))
    t = np.where(idx == 0, 0.0, s[idx])
    return float(-np.linalg.eigvalsh(t).min())


def weights(aloc, p: int, top: int) -> np.ndarray:
    """``s_0..s_top`` with ``s_m = λ_m p^{−m/2}``, through the module's own recursion."""
    return local_lambdas(aloc, p, top) * float(p) ** (-np.arange(top + 1) / 2.0)


def conjugate_pair(radius: float, p: int, phi: float):
    """Satake parameters ``radius·√p·e^{±iφ}``: real coefficients, oscillating weights."""
    alpha = radius * math.sqrt(p) * cmath.exp(1j * phi)
    return satake_local([alpha, alpha.conjugate()])


def shifted(delta: float):
    """``ζ(s − δ)``: ``a_{p^k} = p^{kδ}``, one real parameter ``α_p = p^δ``."""
    return lambda p, k: float(p) ** (k * delta)


def test_positive_rational_kernel_does_not_force_satake_bound() -> None:
    p = 2
    theta = np.linspace(0, 2 * math.pi, 1001)
    kernel = satake_kernel(COUNTEREXAMPLE, p, theta)

    assert max(abs(alpha) for alpha in COUNTEREXAMPLE) > math.sqrt(p)
    # The nonzero parameter contributes -8/(10 - 6*cos(theta)); three
    # zero parameters contribute 3. Its exact range is [1, 5/2].
    np.testing.assert_allclose(kernel, 3 - 8 / (10 - 6 * np.cos(theta)))
    assert abs(float(kernel.min()) - 1) < 1e-12
    assert abs(float(kernel.max()) - 2.5) < 1e-12
    # Its Fourier coefficients have magnitude 3**m, so the defining series
    # does not converge. Positivity of the rational expression proves nothing
    # about the divergent series.
    np.testing.assert_allclose(weights(satake_local(COUNTEREXAMPLE), p, 8)[1:],
                               3.0 ** np.arange(1, 9))


def test_gate_is_not_fooled_by_the_counterexample() -> None:
    aloc = satake_local(COUNTEREXAMPLE)
    _, tail, regime = threshold(aloc, 2)
    assert regime == "divergent"
    assert tail == float("inf")
    out = gate(aloc, 4, primes=[2])
    assert out["verdict"] == "FAIL"
    assert out["divergent_places"] == [2]
    # and no finite diagonal works: the 2x2 minors alone need c >= 3**(n-1)
    s = weights(aloc, 2, 7)
    for n in range(2, 9):
        assert least_psd_diagonal(s, n) >= 3.0 ** (n - 1) * (1 - 1e-12)


def test_least_psd_diagonal_grows_outside_the_bound() -> None:
    # One parameter with |alpha|/sqrt(p) = 1.05: s_m = 1.05**m is unbounded,
    # so the least PSD diagonal grows without limit (CORRECTIONS.md step 2).
    s = 1.05 ** np.arange(0, 201)
    vals = [least_psd_diagonal(s, n) for n in (5, 50, 200)]
    assert abs(vals[0] - 1.2806) < 1e-3
    assert abs(vals[1] - 77.31) < 1e-1
    assert abs(vals[2] / 1.770e5 - 1) < 1e-3
    assert vals[0] < vals[1] < vals[2]
    # the same numbers through the module's coefficient pipeline
    via_module = weights(satake_local((1.05 * math.sqrt(2),)), 2, 199)
    assert abs(least_psd_diagonal(via_module, 200) / vals[2] - 1) < 1e-9


def test_least_psd_diagonal_at_the_boundary_is_the_degree() -> None:
    # zeta(s - 1/2): alpha_p = sqrt(p), s_m = 1. The cosine series diverges,
    # but every Toeplitz section is PSD with diagonal exactly d = 1.
    s = np.ones(401)
    for n in (5, 50, 200, 400):
        assert abs(least_psd_diagonal(s, n) - 1.0) < 1e-9
    # and the gate declines to decide there rather than reporting a number
    out = gate(lambda p, k: float(p) ** (0.5 * k), 1, primes=[2, 3, 5])
    assert out["verdict"] == "INDETERMINATE"
    # a conjugate pair on the bound is a sum of two rank-one sections: d = 2
    pair = weights(conjugate_pair(1.0, 7, 0.9), 7, 149)
    for n in (3, 50, 150):
        assert abs(least_psd_diagonal(pair, n) - 2.0) < 1e-9


def test_inside_the_bound_the_sections_rise_to_the_series_minimum() -> None:
    # zeta at p = 2: c_p = 2/(sqrt 2 + 1), approached from below
    target = 2 / (math.sqrt(2) + 1)
    c, _, regime = threshold(shifted(0.0), 2)
    assert regime == "summable" and abs(c - target) < 1e-12
    s = weights(shifted(0.0), 2, 399)
    vals = [least_psd_diagonal(s, n) for n in (5, 50, 400)]
    assert vals[0] < vals[1] < vals[2] < target
    assert target - vals[2] < 1e-5


def test_the_shift_threshold_sits_at_one_half() -> None:
    # c_p(zeta(s - delta)) = 2x/(1 + x), x = p^(delta - 1/2), below delta = 1/2
    for delta in (0.1, 0.3):
        x = 2 ** (delta - 0.5)
        c, tail, regime = threshold(shifted(delta), 2)
        assert regime == "summable"
        assert abs(c - 2 * x / (1 + x)) <= tail
    assert gate(shifted(0.1), 1)["verdict"] == "PASS"
    half = gate(shifted(0.5), 1)
    assert half["verdict"] == "INDETERMINATE" and 2 in half["boundary_places"]
    above = gate(shifted(0.6), 1)
    assert above["verdict"] == "FAIL" and 2 in above["divergent_places"]


def test_the_violator_value_is_a_truncation() -> None:
    # alpha = 2.3, 1/alpha at p = 5: alpha/sqrt 5 = 1.0286 > 1, so c_p = +inf;
    # the recorded 65.24 is the series cut at depth 41 and moves with the depth
    aloc = satake_local([2.3, 1 / 2.3])
    assert abs(2.3 / math.sqrt(5) - 1.0286) < 1e-4
    readings = {}
    for tol, depth, value in ((1e-8, 23, 22.46), (1e-14, 41, 65.24), (1e-18, 52, 110.80)):
        assert localpos._depth(5, tol) == depth
        c, tail, regime = threshold(aloc, 5, tol=tol)
        assert regime == "divergent" and tail == float("inf")
        assert abs(c - value) < 0.01
        readings[depth] = c
    violator = ramanujan_violator()
    assert violator["verdict"] == "FAIL"
    assert abs(violator["c_p"] - readings[41]) < 1e-12
    assert least_psd_diagonal(weights(aloc, 5, 199), 200) > 1e3


def test_the_gate_reads_oscillating_weights_by_their_envelope() -> None:
    # Issue 335: until the envelope repair the two-term regime test got all
    # three of these wrong (FAIL, PASS and FAIL respectively).
    # inside the bound, c_p ~ 1.894 < d = 2: summable and PASS
    inside = conjugate_pair(0.9, 2, 0.2)
    assert abs(least_psd_diagonal(weights(inside, 2, 119), 120) - 1.894) < 1e-3
    c, tail, regime = threshold(inside, 2)
    assert regime == "summable" and abs(c - 1.893747) < 1e-6
    assert math.isfinite(tail) and tail < 0.01
    assert gate(inside, 2, primes=[2])["verdict"] == "PASS"
    # outside the bound, c_p = +inf: divergent and FAIL
    outside = conjugate_pair(1.2, 7, 0.4)
    assert least_psd_diagonal(weights(outside, 7, 119), 120) > 1e9
    assert threshold(outside, 7)[2] == "divergent"
    out = gate(outside, 2, primes=[7])
    assert out["verdict"] == "FAIL" and out["divergent_places"] == [7]
    # on the bound, c_p = d = 2 exactly: boundary and INDETERMINATE, the
    # same convention steady weights on the bound have always received
    on = conjugate_pair(1.0, 2, 0.9)
    assert abs(least_psd_diagonal(weights(on, 2, 49), 50) - 2.0) < 1e-9
    assert threshold(on, 2)[2] == "boundary"
    assert gate(on, 2, primes=[2])["verdict"] == "INDETERMINATE"


def test_on_the_bound_the_gate_declines_for_steady_and_oscillating_weights() -> None:
    # steady-modulus weights on the bound: the gate declines to decide
    for alphas, p in (((math.sqrt(2),), 2), ((-math.sqrt(3),), 3),
                      ((math.sqrt(97),), 97), ((math.sqrt(5), -math.sqrt(5)), 5)):
        aloc = satake_local(alphas)
        assert threshold(aloc, p)[2] == "boundary"
        assert gate(aloc, len(alphas), primes=[p])["verdict"] == "INDETERMINATE"
    # one real parameter: the verdict changes within a relative 1e-6 of sqrt p;
    # the envelope interval collapses to its floor when weights are steady
    for p in (2, 97):
        verdicts = [gate(satake_local((f * math.sqrt(p),)), 1, primes=[p])["verdict"]
                    for f in (1 - 2e-6, 1 - 5e-7, 1 + 5e-7, 1 + 2e-6)]
        assert verdicts == ["PASS", "INDETERMINATE", "INDETERMINATE", "FAIL"]
    # conjugate pairs on the bound (c_p = d = 2 exactly) decline as well.
    # Before the issue 335 repair phi = 0.9 read FAIL and phi = 2.0 read PASS.
    for phi in (0.9, 2.0):
        pair = conjugate_pair(1.0, 2, phi)
        assert threshold(pair, 2)[2] == "boundary"
        assert gate(pair, 2, primes=[2])["verdict"] == "INDETERMINATE"


def test_the_sixty_angle_control_keeps_its_margins_and_its_verdicts() -> None:
    # the unit-modulus degree-2 family behind "margin >= 0.343 over 60 angles";
    # the 2026-08-10 gate passed all 60, the two-term regime test failed 22,
    # and the envelope repair passes all 60 again at the same margins
    verdicts, margins = [], []
    for phi in np.linspace(0.05, math.pi - 0.05, 60):
        alpha = cmath.exp(1j * phi)
        res = gate(satake_local([alpha, alpha.conjugate()]), 2)
        verdicts.append(res["verdict"])
        margins.append(2 - res["max_c"])
    assert abs(min(margins) - 0.3434) < 1e-4
    assert verdicts == ["PASS"] * 60


def test_conjugate_pair_sweep_has_no_wrong_decisive_regime() -> None:
    # Envelope methods cannot be decisive at every angle near the bound
    # (slow amplitudes at phi near 0, pi/2 and pi: DIAGNOSIS-335.md), so
    # the pin is the honesty property: a wrong decisive regime never
    # occurs, undecided angles read boundary, and rate exactly 1 is
    # boundary at every angle on this grid.
    for radius, forbidden in ((0.9, "divergent"), (1.1, "summable")):
        for phi in np.linspace(0.05, math.pi - 0.05, 60):
            regime = threshold(conjugate_pair(radius, 2, float(phi)), 2)[2]
            assert regime != forbidden, (radius, float(phi), regime)
    for phi in np.linspace(0.05, math.pi - 0.05, 60):
        assert threshold(conjugate_pair(1.0, 2, float(phi)), 2)[2] == "boundary"


def test_the_recorded_numbers_reproduce_under_the_repair() -> None:
    # The hunt's recorded outputs (results.json) under the envelope repair:
    # every verdict stands, every printed max_c stands, and the
    # Davenport-Heilbronn witnesses are finite again at p = 3 (see
    # CORRECTIONS.md, the issue 335 update).
    rows = reference_table()
    expected = {
        "zeta": (0.8284271247461844, "PASS"),
        "L(chi quad mod 5)": (0.8284271247461844, "PASS"),
        "degree-2 Euler factor (phi=0.9)": (1.5796710859022287, "PASS"),
        "Davenport-Heilbronn": (1.8360682541448021, "FAIL"),
        "DH-family t=0": (1.3333333333333428, "FAIL"),
        "Epstein (1,1,6) principal": (5.9950743518758625, "FAIL"),
        "Epstein (2,1,3) non-principal": (6.461868411582862, "FAIL"),
    }
    assert {row["subject"] for row in rows} == set(expected)
    for row in rows:
        want_c, want_verdict = expected[row["subject"]]
        assert row["agrees"] and row["verdict"] == want_verdict
        assert abs(row["max_c"] - want_c) < 1e-12
        assert all(math.isfinite(c) for _, c in row["witnesses"])
    dh = next(row for row in rows if row["subject"] == "Davenport-Heilbronn")
    assert dh["witnesses"] == [(2, 1.8360682541448021), (3, 1.3923820214683353)]
    assert abs(lesion_sweep()["eps_star"] - 0.1841018918280497) < 1e-12
    null = null_distribution(n_samples=300)
    assert abs(null["median"] - 5.881092757081788) < 1e-9
    assert abs(null["p05"] - 0.7444949199285268) < 1e-9
    assert null["fraction_failing"] == 1.0
    assert abs(null["dh_percentile"] - 6.333333333333334) < 1e-9


def test_an_unresolved_excess_reads_as_pass() -> None:
    # zeta(s - 0.49) at p = 2: the truncated c exceeds d = 1 fifteenfold, the
    # tail estimate is larger still, and the verdict is PASS, not INDETERMINATE
    c, tail, regime = threshold(shifted(0.49), 2)
    x = 2 ** (0.49 - 0.5)
    assert regime == "summable"
    assert abs(c - 15.99) < 0.01 and abs(tail - 149.9) < 0.1
    assert abs(2 * x / (1 + x) - 0.9965) < 1e-4
    res = gate(shifted(0.49), 1)
    assert res["verdict"] == "PASS" and res["witnesses"] == []
