"""Window optimization against the direct Dirichlet coefficient measures.

This is a discovery-stage weighted-tail experiment.  It does not reconstruct a
pointwise ``F_2``.  Instead it inserts the positive finite measure

    |r_k(n)|^2 / (n ell^2)  at  alpha = log(n)/ell

directly into the autocorrelation quadratic form.  Level one is compared with
the known sharp ``xi'`` window value before level two is exposed.
"""

from __future__ import annotations

import argparse
import json

import numpy as np
from numpy.polynomial.legendre import leggauss, legval

from dirichlet_recurrence import coefficient_measures


KNOWN_XIPRIME_H = 0.8686415005297671


def _basis_values(points: np.ndarray, count: int) -> np.ndarray:
    scaled = 2.0 * points
    rows = []
    for index in range(count):
        coefficients = np.zeros(2 * index + 1)
        coefficients[-1] = 1.0
        rows.append(legval(scaled, coefficients))
    return np.asarray(rows)


def bin_measure(
    locations: np.ndarray, weights: np.ndarray, bins: int
) -> tuple[np.ndarray, np.ndarray]:
    edges = np.linspace(0.0, 1.0, bins + 1)
    mass, _ = np.histogram(locations, bins=edges, weights=weights)
    centers = 0.5 * (edges[:-1] + edges[1:])
    return centers, mass


def optimize_measure(
    locations: np.ndarray,
    weights: np.ndarray,
    basis_count: int = 10,
    bins: int = 1200,
    quadrature: int = 100,
) -> dict[str, object]:
    centers, mass = bin_measure(locations, weights, bins)
    nodes, node_weights = leggauss(quadrature)

    points = 0.5 * nodes
    weights_on_interval = 0.5 * node_weights
    basis = _basis_values(points, basis_count)
    linear = basis @ weights_on_interval
    diagonal = (basis * weights_on_interval) @ basis.T

    pair = np.zeros((basis_count, basis_count))
    for separation, measure_mass in zip(centers, mass):
        if measure_mass == 0.0:
            continue
        left, right = -0.5 + separation, 0.5
        midpoint, half = 0.5 * (left + right), 0.5 * (right - left)
        sample = midpoint + half * nodes
        first = _basis_values(sample, basis_count)
        second = _basis_values(sample - separation, basis_count)
        overlap = (first * (half * node_weights)) @ second.T
        pair += measure_mass * (overlap + overlap.T)

    matrix = diagonal + pair
    coefficients = np.linalg.solve(matrix, linear)
    c_value = float(linear @ coefficients)
    h_value = 2.0 - 1.0 / c_value
    dense = np.linspace(-0.5, 0.5, 2001)
    window = coefficients @ _basis_values(dense, basis_count)
    return {
        "c": c_value,
        "H": h_value,
        "coefficients": coefficients.tolist(),
        "minimum_window": float(window.min()),
        "measure_mass": float(weights.sum()),
    }


def run(
    ells: tuple[int, ...], basis_count: int, bins: int, quadrature: int
) -> dict[str, object]:
    rows = []
    for ell in ells:
        measures = coefficient_measures(ell, max_level=2)
        levels = {
            str(level): optimize_measure(
                locations,
                weights,
                basis_count=basis_count,
                bins=bins,
                quadrature=quadrature,
            )
            for level, (locations, weights) in enumerate(measures, start=1)
        }
        rows.append({"ell": ell, "limit": int(np.exp(ell)), "levels": levels})
    return {
        "known_xiprime_H": KNOWN_XIPRIME_H,
        "basis_count": basis_count,
        "bins": bins,
        "quadrature": quadrature,
        "results": rows,
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--ells", default="8,10,12")
    parser.add_argument("--basis", type=int, default=10)
    parser.add_argument("--bins", type=int, default=1200)
    parser.add_argument("--quadrature", type=int, default=100)
    args = parser.parse_args()
    payload = run(
        tuple(int(value) for value in args.ells.split(",")),
        args.basis,
        args.bins,
        args.quadrature,
    )
    print(json.dumps(payload, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
