"""Completed-CUE oracle for angular derivatives of characteristic polynomials.

For even ``N`` and Haar ``U``, the completed characteristic polynomial is a
real trigonometric polynomial

    Z_U(theta) = phase * exp(-i N theta/2) det(exp(i theta) I - U).

Its real zeros are the eigenangles of ``U``.  Cyclic Rolle interlacing gives
exactly one zero of each next angular derivative between neighboring zeros of
the previous derivative.  This module uses that interlacing instead of taking
ordinary complex roots of the raw characteristic-polynomial derivative.

The experiment estimates

    K[k,N](m/N) = E |sum_j exp(i m theta_j[k])|^2 / N.

Level zero has the exact CUE expectation ``m/N`` for ``m <= N``.  Level one
has the Farmer-Gonek-Lee limiting curve.  Those are the two controls before
level two is compared with the independently regenerated finite series.
"""

from __future__ import annotations

import argparse
import json
from dataclasses import dataclass
from pathlib import Path

import numpy as np
from scipy.optimize import brentq

from exact_c2 import derive_c2, derive_level_one


TWO_PI = 2.0 * np.pi


def f1_closed(alpha: np.ndarray, terms: int = 60) -> np.ndarray:
    """Farmer-Gonek-Lee's continuous level-one form factor on ``[0,1]``."""

    a = np.abs(np.asarray(alpha, dtype=float))
    result = a - 4.0 * a**2
    term = 0.5 * (2.0 * a) ** 3
    result = result + term
    for k in range(2, terms + 1):
        term = term * (k - 1) * (2.0 * a) ** 2 / ((2 * k) * (2 * k - 1))
        result = result + term
    return result


def derived_truncation(derivative_level: int, alpha: np.ndarray) -> np.ndarray:
    if derivative_level == 1:
        coefficients = derive_level_one(11).values()
    elif derivative_level == 2:
        coefficients = derive_c2(11)["coefficients"].values()
    else:
        raise ValueError("only derivative levels one and two are available")
    a = np.asarray(alpha, dtype=float)
    return sum(float(value) * a**index for index, value in enumerate(coefficients, 1))


def haar_eigenangles(size: int, rng: np.random.Generator) -> np.ndarray:
    """Sample Haar ``U(size)`` by complex Gaussian QR decomposition."""

    z = (rng.normal(size=(size, size)) + 1j * rng.normal(size=(size, size))) / np.sqrt(2.0)
    q, r = np.linalg.qr(z)
    diagonal = np.diag(r)
    q = q * (diagonal / np.abs(diagonal))
    return np.sort(np.mod(np.angle(np.linalg.eigvals(q)), TWO_PI))


def angular_derivative_levels(eigenangles: np.ndarray, max_level: int = 2) -> list[np.ndarray]:
    """Return cyclically ordered zeros through ``Z_U^(max_level)``.

    The Fourier representation is formed once.  At each level, Brent's method
    locates the unique next zero in every cyclic interval.  A small scan is a
    fallback for floating endpoint noise, not a way to choose among roots.
    """

    angles = np.asarray(eigenangles, dtype=float)
    size = len(angles)
    if size % 2:
        raise ValueError("the current completed-periodic implementation requires even size")
    if np.any(np.diff(angles) <= 0):
        raise ValueError("eigenangles must be strictly increasing")

    coefficients = np.poly(np.exp(1j * angles))
    frequencies = np.arange(size, -1, -1, dtype=float) - size / 2.0
    midpoint = 0.5 * (angles[0] + angles[1])
    raw_midpoint = np.sum(coefficients * np.exp(1j * frequencies * midpoint))
    phase = np.exp(-1j * np.angle(raw_midpoint))

    def value(theta: float, level: int) -> float:
        raw = np.sum(
            coefficients
            * (1j * frequencies) ** level
            * np.exp(1j * frequencies * theta)
        )
        return float(np.real(phase * raw))

    levels = [angles.copy()]
    previous = angles.copy()
    for level in range(1, max_level + 1):
        roots: list[float] = []
        for index, left in enumerate(previous):
            right = previous[(index + 1) % size]
            if index == size - 1:
                right += TWO_PI
            f_left = value(left, level)
            f_right = value(right, level)
            if f_left * f_right > 0:
                grid = np.linspace(left, right, 129)
                values = np.array([value(point, level) for point in grid])
                crossings = np.flatnonzero(values[:-1] * values[1:] <= 0)
                if len(crossings) != 1:
                    raise ArithmeticError(
                        f"interlacing lost at N={size}, level={level}, interval={index}"
                    )
                crossing = int(crossings[0])
                left, right = float(grid[crossing]), float(grid[crossing + 1])
            root = brentq(
                lambda theta: value(theta, level),
                left,
                right,
                xtol=5e-14,
                rtol=1e-14,
            )
            roots.append(root)
        previous = np.sort(np.mod(np.asarray(roots), TWO_PI))
        levels.append(previous)
    return levels


def point_form_factor(angles: np.ndarray, modes: np.ndarray) -> np.ndarray:
    return np.array(
        [abs(np.exp(1j * int(mode) * angles).sum()) ** 2 / len(angles) for mode in modes],
        dtype=float,
    )


@dataclass(frozen=True)
class SizeResult:
    size: int
    samples: int
    modes: np.ndarray
    means: np.ndarray
    standard_errors: np.ndarray
    cumulative_means: np.ndarray
    cumulative_standard_errors: np.ndarray

    def as_dict(self) -> dict[str, object]:
        alpha = self.modes / self.size
        return {
            "size": self.size,
            "samples": self.samples,
            "modes": self.modes.tolist(),
            "alpha": alpha.tolist(),
            "levels": {
                str(level): {
                    "mean": self.means[level].tolist(),
                    "standard_error": self.standard_errors[level].tolist(),
                    "cumulative_integral": self.cumulative_means[level].tolist(),
                    "cumulative_standard_error": self.cumulative_standard_errors[
                        level
                    ].tolist(),
                }
                for level in range(self.means.shape[0])
            },
            "controls": {
                "cue_level0": alpha.tolist(),
                "fgl_level1": f1_closed(alpha).tolist(),
                "derived_level2_11_terms": derived_truncation(2, alpha).tolist(),
            },
        }


def run_size(size: int, samples: int, seed: int) -> SizeResult:
    if size % 8:
        raise ValueError("size must be divisible by eight for the fixed comparison modes")
    modes = np.array([size // 8, size // 4, 3 * size // 8, size // 2], dtype=int)
    all_modes = np.arange(1, size // 2 + 1, dtype=int)
    rng = np.random.default_rng(seed)
    observations = np.empty((samples, 3, len(all_modes)), dtype=float)
    for sample in range(samples):
        levels = angular_derivative_levels(haar_eigenangles(size, rng), max_level=2)
        for level, angles in enumerate(levels):
            observations[sample, level] = point_form_factor(angles, all_modes)
    selected = observations[:, :, modes - 1]
    means = selected.mean(axis=0)
    standard_errors = selected.std(axis=0, ddof=1) / np.sqrt(samples)
    cumulative = np.cumsum(observations, axis=2)[:, :, modes - 1] / size
    cumulative_means = cumulative.mean(axis=0)
    cumulative_standard_errors = cumulative.std(axis=0, ddof=1) / np.sqrt(samples)
    return SizeResult(
        size,
        samples,
        modes,
        means,
        standard_errors,
        cumulative_means,
        cumulative_standard_errors,
    )


def run_ladder(specifications: list[tuple[int, int]], seed: int = 20260811) -> dict[str, object]:
    results = [
        run_size(size=size, samples=samples, seed=seed + size)
        for size, samples in specifications
    ]
    return {
        "seed_rule": "seed + matrix_size",
        "base_seed": seed,
        "results": [result.as_dict() for result in results],
    }


def _parse_sizes(text: str) -> list[tuple[int, int]]:
    result = []
    for item in text.split(","):
        size, samples = item.split(":", maxsplit=1)
        result.append((int(size), int(samples)))
    return result


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--sizes", default="24:200,32:200")
    parser.add_argument("--seed", type=int, default=20260811)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    payload = run_ladder(_parse_sizes(args.sizes), seed=args.seed)
    rendered = json.dumps(payload, indent=2, sort_keys=True)
    if args.output is not None:
        args.output.write_text(rendered + "\n")
    print(rendered)


if __name__ == "__main__":
    main()
