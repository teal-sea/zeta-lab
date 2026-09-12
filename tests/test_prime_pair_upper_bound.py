"""Finite identity checks for the upper-bound attempt, not asymptotic evidence.

Fourier grid averages below are exact quadrature for the relevant finite
trigonometric polynomials, up to arithmetic rounding. Arc indicators are
tested pointwise; no quadrature claim is made for a discontinuous cutoff.
"""
from __future__ import annotations

from math import gcd, isqrt

from mpmath import mp
import pytest
from sympy import mobius, totient

from hunts.prime_pair_error import probe


def _fourier(weights, alpha):
    return mp.fsum(w * mp.exp(2j * mp.pi * n * alpha)
                   for n, w in enumerate(weights, 1))


def _series(z, k):
    # Divisor formula, independent of the reduced-fraction exponential sum.
    return mp.fsum(
        mp.mpf(int(mobius(q)) ** 2)
        / int(totient(q)) ** 2
        * sum(d * int(mobius(q // d))
              for d in range(1, q + 1) if q % d == 0 and k % d == 0)
        for q in range(1, z + 1)
    )


def _model(N, z, alpha):
    return mp.fsum(
        mp.mpf(int(mobius(q)) ** 2) / int(totient(q)) ** 2
        * abs(_fourier([1] * N, alpha - mp.mpf(a) / q)) ** 2
        for q in range(1, z + 1)
        for a in range(1, q + 1) if gcd(a, q) == 1
    )


@pytest.mark.parametrize("N", [2, 9, 25])
def test_centered_fourier_norm_diagonal_signs_and_truncation(N):
    with mp.workdps(45):
        lam, _ = probe.von_mangoldt(N)
        weights = [mp.mpf(float(v)) for v in lam[1:]]
        y = isqrt(N)
        d_N = mp.fsum(w * w for w in weights)
        sy = [_series(y, k) for k in range(N + 1)]
        a0 = d_N - N * sy[0]
        pairs = [mp.fsum(weights[n] * weights[n + k]
                         for n in range(N - k))
                 for k in range(1, N + 1)]
        j_direct = 2 * mp.fsum(
            (pairs[k - 1] - (N - k) * sy[k]) ** 2
            for k in range(1, N + 1)
        )
        assert pairs[-1] == 0
        if N >= 9:
            assert any(pairs[k - 1] > 0 for k in range(1, N + 1, 2))
            assert abs(weights[3] - mp.log(2)) < mp.mpf("1e-15")
            assert abs(weights[7] - mp.log(2)) < mp.mpf("1e-15")

        # The infinite singular series is used only as a coefficient vector
        # for the norm comparison, with the existing probe's numeric values.
        singular = [mp.mpf(float(s)) for s in probe.singular_series(N)]
        e_direct = 2 * mp.fsum(
            (pairs[k - 1] - (N - k) * singular[k]) ** 2
            for k in range(1, N + 1)
        )
        tail = 2 * mp.fsum(
            ((N - k) * (singular[k] - sy[k])) ** 2
            for k in range(1, N + 1)
        )
        g_values, squares, expansions, e_squares = [], [], [], []
        for j in range(4 * N + 1):
            alpha = mp.mpf(j) / (4 * N + 1)
            f2 = abs(_fourier(weights, alpha)) ** 2
            v = _model(N, y, alpha)
            v_coeff = N * sy[0] + 2 * mp.fsum(
                (N - k) * sy[k] * mp.cos(2 * mp.pi * k * alpha)
                for k in range(1, N + 1)
            )
            assert abs(v - v_coeff) < mp.mpf("1e-35")
            g = f2 - v - a0
            g_values.append(g)
            squares.append(g * g)
            expansions.append(f2 * f2 - 2 * f2 * v + v * v - a0 * a0)
            full_model = d_N + 2 * mp.fsum(
                (N - k) * singular[k] * mp.cos(2 * mp.pi * k * alpha)
                for k in range(1, N + 1)
            )
            e_squares.append((f2 - full_model) ** 2)
        length = len(squares)
        assert abs(mp.fsum(g_values) / length) < mp.mpf("1e-35")
        assert abs(mp.fsum(squares) / length - j_direct) < mp.mpf("1e-33")
        assert abs(mp.fsum(expansions) / length - j_direct) < mp.mpf("1e-33")
        assert abs(mp.fsum(e_squares) / length - e_direct) < mp.mpf("1e-33")
        assert abs(mp.sqrt(e_direct) - mp.sqrt(j_direct)) <= mp.sqrt(tail)
        assert e_direct <= 2 * j_direct + 2 * tail


def test_full_arc_decomposition_keeps_centering_on_both_sets():
    N, Q = 36, 2
    y = isqrt(N)
    with mp.workdps(45):
        lam, _ = probe.von_mangoldt(N)
        weights = [mp.mpf(float(v)) for v in lam[1:]]
        d_N = mp.fsum(w * w for w in weights)
        a0_Q, a0_y = (d_N - N * _series(z, 0) for z in (Q, y))
        sets_seen = set()
        for j in range(4 * N + 1):
            alpha = mp.mpf(j) / (4 * N + 1)
            f2 = abs(_fourier(weights, alpha)) ** 2
            active = []
            for q in range(1, Q + 1):
                for a in range(1, q + 1):
                    if gcd(a, q) != 1:
                        continue
                    beta = alpha - mp.mpf(a) / q
                    beta -= mp.floor(beta + mp.mpf("0.5"))
                    if abs(beta) <= mp.mpf(Q) / (q * N):
                        active.append((q, beta))
            assert len(active) <= 1
            sets_seen.add(bool(active))
            arc_model = mp.fsum(
                mp.mpf(int(mobius(q)) ** 2) / int(totient(q)) ** 2
                * abs(_fourier([1] * N, beta)) ** 2
                for q, beta in active
            )
            vQ, vy = (_model(N, z, alpha) for z in (Q, y))
            leakage = vQ - arc_model
            assert leakage >= -mp.mpf("1e-35")
            centered_change = vy - vQ - N * (_series(y, 0) - _series(Q, 0))
            b = f2 - arc_model
            full_g = f2 - vy - a0_y
            reconstructed = b - leakage - a0_Q - centered_change
            assert abs(full_g - reconstructed) < mp.mpf("1e-35")
            assert full_g ** 2 <= (
                4 * (b ** 2 + leakage ** 2 + a0_Q ** 2 + centered_change ** 2)
                + mp.mpf("1e-30")
            )
        assert sets_seen == {False, True}


@pytest.mark.parametrize("kind", ["arbitrary", "mangoldt"])
def test_q1_weighted_convolution_and_endpoint_square(kind):
    N, Q = 16, 1
    with mp.workdps(45):
        if kind == "arbitrary":
            weights = [mp.mpf((7 * n) % 11 - 5) / 3 for n in range(1, N + 1)]
        else:
            lam, _ = probe.von_mangoldt(N)
            weights = [mp.mpf(float(v)) for v in lam[1:]]
        delta = [mp.mpf(0)]
        for w in weights:
            delta.append(delta[-1] + w - 1)
        convolution = [
            mp.fsum(weights[n - 1] - 1
                    for n in range(max(1, m - N), min(N, m - 1) + 1))
            for m in range(2, 2 * N + 1)
        ]
        expected = delta[1:] + [delta[N] - delta[t] for t in range(1, N)]
        assert max(abs(a - b) for a, b in zip(convolution, expected)) < mp.mpf("1e-38")
        total = mp.fsum(c * c for c in convolution)
        completed = (mp.mpf(N + 1) / 2 * delta[N] ** 2
                     + 2 * mp.fsum((delta[t] - delta[N] / 2) ** 2
                                   for t in range(1, N)))
        assert abs(total - completed) < mp.mpf("1e-35")
        samples = []
        for j in range(4 * N + 1):
            alpha = mp.mpf(j) / (4 * N + 1)
            k2 = abs(_fourier([1] * N, alpha)) ** 2
            r2 = abs(_fourier([w - 1 for w in weights], alpha)) ** 2
            samples.append(k2 * r2)
            distance = min(alpha, 1 - alpha)
            if distance > mp.mpf(Q) / N:
                assert k2 * r2 <= mp.mpf(N * N) / (4 * Q * Q) * r2 + mp.mpf("1e-35")
        assert abs(mp.fsum(samples) / len(samples) - total) < mp.mpf("1e-33")
