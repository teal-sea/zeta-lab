"""Measure where nested window estimates inflate a pressure penalty.

Exact gap-incidence arithmetic is separate from the measured Gram examples.
The proposed zeta constants below are arithmetic projections of a derived
replacement assembly, not new kernel-checked statements about zeta.
"""

from __future__ import annotations

import json
from fractions import Fraction as Q
from pathlib import Path

import numpy as np
from mpmath import mp

HERE = Path(__file__).resolve().parent


def pressure_coefficients(points: int, block: int, local: int):
    """Coefficients of each gap, before and after the early span estimate.

    Pressure denominator is omitted. This enumerates both nested window
    levels directly, without using the proposed multiplicity formula.
    """
    if not 2 <= local <= block <= points:
        raise ValueError("Expected 2 <= local <= block <= points")
    exact = [0] * (points - 1)
    coarse = [0] * (points - 1)
    for outer in range(points - block + 1):
        for inner in range(outer, outer + block - local + 1):
            for gap in range(inner, inner + local - 1):
                exact[gap] += 1
        for gap in range(outer, outer + block - 1):
            coarse[gap] += local - 1
    return exact, coarse


def pair_coefficients(block: int, local: int):
    """Regroup all local pair occurrences by their actual global pair."""
    if not 2 <= local <= block:
        raise ValueError("Expected 2 <= local <= block")
    weights = {(i, j): Q(0) for i in range(block) for j in range(i + 1, block)}
    for start in range(block - local + 1):
        for i in range(local):
            for j in range(i + 1, local):
                weights[start + i, start + j] += Q(2, local - (j - i))
    return weights


def projection(local: int, floor: Q, block: int, pressure: int):
    """Exact affine coefficients in H for old and candidate new proportions."""
    q = local - 1
    windows = block - q
    amount = floor * windows
    if not 2 <= local <= block or pressure <= 0 or not 0 < amount <= 1:
        raise ValueError("Invalid parameters or block cap")
    den = block - amount
    hcoef = Q(block) / den
    old_cost = Q(q * (block - 1), pressure) / den
    new_cost = Q(q * windows, pressure) / den
    saving = old_cost - new_cost
    with mp.workdps(60):
        real = lambda r: mp.mpf(r.numerator) / r.denominator
        h = mp.mpf(3) / 2 - mp.cot(1 / mp.sqrt(2)) / mp.sqrt(2)
        old = real(hcoef) * h - real(old_cost)
        new = real(hcoef) * h - real(new_cost)
        return {
            "local_points": local, "block_points": block,
            "floor": str(floor), "pressure_denominator": pressure,
            "block_cap": str(amount), "H_coefficient": str(hcoef),
            "old_subtracted_constant": str(old_cost),
            "new_subtracted_constant": str(new_cost),
            "exact_gain": str(saving),
            "old_proportion_measured": mp.nstr(old, 40),
            "new_proportion_candidate_measured": mp.nstr(new, 40),
            "gain_percentage_points_measured": mp.nstr(100 * real(saving), 25),
        }


def mt_gram(gaps):
    """Measured normalized Montgomery-Taylor Gram matrix, direct sinc formula."""
    gaps = np.asarray(gaps, dtype=float)
    if gaps.ndim != 1 or np.any(gaps < 0):
        raise ValueError("Expected nonnegative gaps")
    y = np.r_[0.0, np.cumsum(gaps)]
    distances = y[:, None] - y[None, :]
    half = np.sqrt(2.0) / 2
    transform = (np.sinc((half - np.pi * distances) / np.pi)
                 + np.sinc((half + np.pi * distances) / np.pi)) / 2
    return transform / np.sinc(half / np.pi)


def defect(matrix):
    eig = np.linalg.eigvalsh(matrix)
    return float(np.where(eig <= 2, (eig - 1)**2, 2 * eig - 3).sum())


def kernel_example(gaps, block: int, local: int, floor: Q, pressure: int):
    """Check the finite inequality and isolate pinching on an actual kernel.

    Every offset is a whole partition, including its short endpoint blocks.
    Also report the full-block-only sum used by the bridge.
    """
    gram = mt_gram(gaps)
    points = len(gaps) + 1
    exact, coarse = pressure_coefficients(points, block, local)
    full = defect(gram)
    full_block_sum = sum(defect(gram[s:s+block, s:s+block])
                         for s in range(points - block + 1))
    partitions = []
    for offset in range(block):
        cuts = sorted({0, points, *range(offset, points + 1, block)})
        partitions.append(sum(defect(gram[a:b, a:b])
                              for a, b in zip(cuts, cuts[1:])))
    amount = float(floor) * (block - local + 1)
    exact_pressure = float(np.dot(exact, gaps)) / pressure
    coarse_pressure = float(np.dot(coarse, gaps)) / pressure
    span_cap = (local - 1) * (block - local + 1) * sum(gaps) / pressure
    finite_left = amount * (points - block + 1) - span_cap
    return {
        "gaps": list(map(float, gaps)), "block_points": block, "local_points": local,
        "minimum_gram_eigenvalue": float(np.linalg.eigvalsh(gram)[0]),
        "full_defect": full, "average_partition_defect": float(np.mean(partitions)),
        "pinching_loss": full - float(np.mean(partitions)),
        "averaged_full_blocks": full_block_sum / block,
        "exact_nested_pressure": exact_pressure,
        "early_coarse_pressure": coarse_pressure,
        "improved_global_pressure_cap": float(span_cap),
        "finite_inequality_margin": block * full - finite_left,
        "local_to_block_margin": full_block_sum + exact_pressure
                                 - amount * (points - block + 1),
    }


def report():
    exact, coarse = pressure_coefficients(7, 4, 3)
    cases = [
        ([1.04, 1.97] * 5, 4, 3, Q(1345, 10**6), 3000),
        ([0.25] * 10, 4, 3, Q(1345, 10**6), 3000),
        ([1.04, 1.97] * 6, 6, 4, Q(2310, 10**6), 2500),
    ]
    return {
        "status": "derived counting refinement; zeta projections await replacement assembly check",
        "small_exact_witness": {"points": 7, "block": 4, "local": 3,
                                "exact_gap_coefficients": exact,
                                "early_coarse_gap_coefficients": coarse},
        "projections": [projection(3, Q(1345, 10**6), 745, 3000),
                        projection(4, Q(2310, 10**6), 435, 2500)],
        "actual_kernel_examples_measured": [kernel_example(*case) for case in cases],
    }


if __name__ == "__main__":
    result = report()
    (HERE / "counting_audit.json").write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps(result, indent=2))
