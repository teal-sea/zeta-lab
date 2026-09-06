#!/usr/bin/env python3
"""Finite checks for SHARP_TRANSFER.md, not numerical proof of its asymptotics.

Run: python check_sharp_transfer.py
Requires Python >=3.10, numpy, scipy. All computation is local and deterministic.
The output checks.json records tests and numerical diagnostics separately.
"""
from __future__ import annotations

import json
import math
import platform
from fractions import Fraction
from pathlib import Path

import numpy as np
import scipy
from scipy.integrate import quad

HERE = Path(__file__).resolve().parent
RNG = np.random.default_rng(20260906)


def next_power_two(x: int) -> int:
    if x < 1:
        raise ValueError("x must be positive")
    return 1 << (x - 1).bit_length()


def h_closed(n: int, t: np.ndarray | float) -> np.ndarray:
    if n < 1:
        raise ValueError("N must be positive")
    w = 1.0 / n + 2j * np.pi * np.asarray(t)
    return np.exp(w) * np.expm1(n * w) / np.expm1(w)


def circular_convolve(a: np.ndarray, b: np.ndarray) -> np.ndarray:
    if a.shape != b.shape or a.ndim != 1:
        raise ValueError("Inputs must be equally sized one-dimensional arrays")
    return np.fft.ifft(np.fft.fft(a) * np.fft.fft(b)) / len(a)


def values_from_coefficients(c: np.ndarray, length: int) -> np.ndarray:
    if length <= len(c):
        raise ValueError("Use enough grid points to avoid aliasing")
    return np.fft.ifft(c, n=length) * length


def von_mangoldt(n: int) -> np.ndarray:
    out = np.zeros(n + 1)
    for p in range(2, n + 1):
        if all(p % d for d in range(2, math.isqrt(p) + 1)):
            power = p
            while power <= n:
                out[power] = math.log(p)
                power *= p
    return out


def convolution_checks() -> dict:
    max_rel = 0.0
    cases = 0
    for n in range(1, 65):
        m = 3 * n + 5
        length = next_power_two(m + n + 8)
        t = np.arange(length) / length
        index = np.arange(1, m + 1)
        for trial in range(4):
            a = RNG.integers(-7, 8, m) + 1j * RNG.integers(-7, 8, m)
            alpha = float(RNG.uniform(-0.5, 0.5))
            b_shifted = np.exp(2j * np.pi * np.outer(alpha - t, index)) @ (
                a * np.exp(-index / n)
            )
            h = np.exp(2j * np.pi * np.outer(t, np.arange(1, n + 1))) @ (
                np.exp(np.arange(1, n + 1) / n)
            )
            integrated = np.mean(b_shifted * h)
            direct = np.dot(a[:n], np.exp(2j * np.pi * alpha * np.arange(1, n + 1)))
            relative = abs(integrated - direct) / max(1.0, float(np.sum(np.abs(a[:n]))))
            max_rel = max(max_rel, float(relative))
            assert relative < 5e-12, (n, trial, relative)
            cases += 1
    return {"cases": cases, "max_scaled_error": max_rel,
            "tolerance": 5e-12,
            "interpretation": "Floating evaluation of a finite Fourier identity; not interval arithmetic"}


def kernel_checks() -> dict:
    rows = []
    for n in (2, 3, 8, 16, 64, 257, 1024):
        t = np.r_[np.geomspace(1e-13, 0.49, 1000), np.linspace(0, 0.5, 8001)]
        absolute = np.abs(h_closed(n, t))
        cap = np.full_like(t, math.e * n)
        np.minimum(cap, np.divide(2.0, t, out=np.full_like(t, np.inf), where=t > 0), out=cap)
        ratio = float(np.max(absolute / cap))
        assert ratio <= 1 + 1e-10
        grid = np.arange(131072) / 131072
        l1 = float(np.mean(np.abs(h_closed(n, grid))))
        bound = 2 * math.e + 4 * math.log(n)
        assert l1 <= bound
        rows.append({"N": n, "max_pointwise_bound_ratio": ratio,
                     "L1_numerical": l1, "L1_proved_upper_bound": bound})
    return {"rows": rows, "status": "Pointwise samples and numerical L1 diagnostics; proof is in note"}


def local_split_checks() -> dict:
    rows = []
    length = 32768
    t = np.arange(length) / length
    for n in (64, 144, 400):
        m = 4 * n
        index = np.arange(1, m + 1)
        delta = (1 / 3) / math.sqrt(n)
        inside = (t >= delta) & (t <= 2 * delta)
        enlarged = (t >= delta / 2) & (t <= 4 * delta)
        h_coeff = np.zeros(n + 1, dtype=complex)
        h_coeff[1:] = np.exp(np.arange(1, n + 1) / n)
        h = values_from_coefficients(h_coeff, length)
        l1 = float(np.mean(np.abs(h)))
        far_kernel_energy = circular_convolve((~enlarged).astype(float), np.abs(h)**2).real
        assert np.max(far_kernel_energy[inside]) <= 16 / delta
        for family in ("random_complex", "central_coherent", "band_coherent"):
            if family == "random_complex":
                a = RNG.standard_normal(m) + 1j * RNG.standard_normal(m)
            elif family == "central_coherent":
                a = np.ones(m, dtype=complex)
            else:
                a = np.exp(-2j * np.pi * 1.5 * delta * index)
            b_coeff = np.zeros(m + 1, dtype=complex)
            b_coeff[1:] = a * np.exp(-index / n)
            b = values_from_coefficients(b_coeff, length)
            sharp_coeff = np.zeros(n + 1, dtype=complex)
            sharp_coeff[1:] = a[:n]
            sharp = values_from_coefficients(sharp_coeff, length)
            near = circular_convolve(b * enlarged, h)
            far = circular_convolve(b * (~enlarged), h)
            error = float(np.max(np.abs(near + far - sharp)))
            assert error <= 1e-9 * max(1, n)
            norm2 = float(np.mean(np.abs(b)**2))
            near4 = float(np.mean(np.abs(near[inside])**4)) * float(np.mean(inside))
            local_b4 = float(np.mean(np.abs(b)**4 * enlarged))
            near_budget = l1**4 * local_b4
            assert near4 <= near_budget * (1 + 1e-9) + 1e-10
            far2 = np.abs(far[inside])**2
            cs_budget = norm2 * far_kernel_energy[inside]
            assert np.all(far2 <= cs_budget * (1 + 1e-9) + 1e-10)
            far4 = float(np.mean(np.abs(far)**4 * inside))
            discrete_far_budget = float(np.mean(inside)) * (16 / delta)**2 * norm2**2
            assert far4 <= discrete_far_budget
            sharp4 = float(np.mean(np.abs(sharp)**4 * inside))
            final_discrete_budget = 8 * near_budget + 8 * discrete_far_budget
            assert sharp4 <= final_discrete_budget
            rows.append({"N": n, "family": family, "delta": delta,
                         "convolution_max_error": error,
                         "near_L4_fourth": near4, "near_Young_budget": near_budget,
                         "far_L4_fourth": far4, "far_CS_budget": discrete_far_budget,
                         "sharp_L4_fourth": sharp4,
                         "final_discrete_budget": final_discrete_budget})
    return {"rows": rows, "status": "Discrete analogues on a periodic grid; analytic constants proved separately"}


def arc_and_exponent_checks() -> dict:
    for n in range(36, 50001):
        q = math.isqrt(n) // 3
        assert q >= 1
        assert 2 * q*q + q < n
        assert Fraction(2*q, n) < Fraction(1, q) - Fraction(1, n)
    for numerator in range(500, 1000):
        sigma = Fraction(numerator, 1000)
        a_bound = min(3/(2-sigma), 3/(3*sigma-1))
        assert a_bound <= Fraction(12, 5)
        exponent = 4*sigma - Fraction(3, 2) + Fraction(18, 5)*(1-sigma)
        assert exponent == Fraction(21, 10) + Fraction(2, 5)*sigma
        assert exponent <= Fraction(5, 2)
    return {"arc_integer_cases": 50000-36+1,
            "density_and_energy_fraction_cases": 500,
            "same_band_exponent_gain": str(Fraction(13, 5)-Fraction(5, 2)),
            "status": "Exact rational/integer arithmetic; general algebraic proofs are in note"}


def prime_band_diagnostics() -> dict:
    rows = []
    for n in (144, 400, 900, 1600):
        lam = von_mangoldt(n)
        idx = np.arange(1, n + 1)
        q = math.isqrt(n) // 3
        def fk(alpha: float) -> tuple[complex, complex]:
            phases = np.exp(2j * np.pi * idx * alpha)
            return complex(np.dot(lam[1:], phases)), complex(np.sum(phases))
        def integrand(alpha: float, kind: str) -> float:
            f, k = fk(alpha)
            if kind == "residual": return float(abs(f-k)**4)
            if kind == "intensity": return float((abs(f)**2-abs(k)**2)**2)
            return float(abs(f)**4)
        result = {"N": n, "Q": q}
        for band, lo, hi in (("major_outer", q/(2*n), q/n),
                             ("minor_adjacent", q/n, 2*q/n)):
            for kind in ("residual", "intensity", "F_fourth"):
                value, estimated_error = quad(lambda alpha: integrand(alpha, kind), lo, hi,
                                              epsabs=1e-7, epsrel=2e-10, limit=400)
                value *= 2; estimated_error *= 2
                result[f"{band}_{kind}"] = value
                result[f"{band}_{kind}_over_N2p5"] = value / n**2.5
                result[f"{band}_{kind}_estimated_quad_error"] = estimated_error
        rows.append(result)
    return {"rows": rows,
            "status": "Finite diagnostics, not fitted exponents, asymptotic verification, or rigorous enclosures"}


def main() -> None:
    results = {
        "date": "2026-09-06",
        "environment": {"python": platform.python_version(), "numpy": np.__version__, "scipy": scipy.__version__},
        "claim_boundary": "Finite tests do not prove the asymptotic estimates and are not an independent proof review.",
        "finite_convolution": convolution_checks(),
        "geometric_kernel": kernel_checks(),
        "localized_transfer": local_split_checks(),
        "exact_parameters": arc_and_exponent_checks(),
        "von_mangoldt_bands": prime_band_diagnostics(),
        "all_checks_passed": True,
    }
    output = HERE / "checks.json"
    output.write_text(json.dumps(results, indent=2) + "\n")
    print(json.dumps({"all_checks_passed": True,
                      "convolution_cases": results["finite_convolution"]["cases"],
                      "max_convolution_scaled_error": results["finite_convolution"]["max_scaled_error"],
                      "localized_split_cases": len(results["localized_transfer"]["rows"]),
                      "arc_cases": results["exact_parameters"]["arc_integer_cases"],
                      "output": str(output)}, indent=2))


if __name__ == "__main__":
    main()
