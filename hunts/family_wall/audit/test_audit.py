#!/usr/bin/env python3
"""Cross-checks for the independent implementation in audit.py."""

import math
import unittest

import mpmath as mp
import numpy as np

import audit


class KernelTests(unittest.TestCase):
    def test_closed_form_against_quadrature(self):
        mp.mp.dps = 60
        for x in (0, 1e-7, 0.2250790790392765, 0.5, 1.0, 3.75, 19.0):
            direct = mp.quad(
                lambda t: mp.cos(mp.sqrt(2) * t) * mp.cos(2 * mp.pi * x * t),
                [-mp.mpf("0.5"), mp.mpf("0.5")],
            )
            closed = float(audit.kernel_all(x)[0])
            self.assertLess(abs(mp.mpf(closed) - direct), mp.mpf("2e-15"))

    def test_even_kernel_and_weight(self):
        x = np.linspace(0, 50, 1001)
        self.assertTrue(np.allclose(audit.kernel_all(x)[0], audit.kernel_all(-x)[0], atol=2e-15))
        self.assertTrue(np.all(audit.weight_all(x)[0] >= 0))

    def test_derivatives(self):
        for x in (0.01, 0.2250790790392765, 0.8, 3.0, 20.0):
            h = 2e-6
            k, kp, kpp = audit.kernel_all(x)
            km = audit.kernel_all(x - h)[0]
            kplus = audit.kernel_all(x + h)[0]
            self.assertAlmostEqual(float(kp), float((kplus - km) / (2 * h)), places=8)
            self.assertAlmostEqual(float(kpp), float((kplus - 2 * k + km) / h**2), places=4)


class ObjectiveTests(unittest.TestCase):
    def test_gradient_against_central_differences(self):
        rng = np.random.default_rng(1203)
        for n in (3, 7, 12):
            gaps = rng.uniform(0.2, 2.5, n - 1)
            _, analytic = audit.objective_and_gradient(gaps)
            numeric = np.empty(n - 1)
            h = 1e-6
            for i in range(n - 1):
                plus = gaps.copy()
                minus = gaps.copy()
                plus[i] += h
                minus[i] -= h
                numeric[i] = (audit.objective(plus) - audit.objective(minus)) / (2 * h)
            self.assertLess(np.max(np.abs(analytic - numeric)), 2e-9)

    def test_reversal_invariance(self):
        rng = np.random.default_rng(42)
        gaps = rng.uniform(0, 3, 15)
        self.assertAlmostEqual(audit.objective(gaps), audit.objective(gaps[::-1]), places=15)

    def test_direct_definition(self):
        gaps = np.array([0.7, 1.2, 2.1])
        n = len(gaps) + 1
        expected = 0.0
        for s in range(1, n):
            expected += 2 / (n - s) * sum(
                float(audit.weight_all(sum(gaps[i : i + s]))[0]) for i in range(n - s)
            )
        self.assertAlmostEqual(audit.objective(gaps), expected, places=15)


if __name__ == "__main__":
    unittest.main()
