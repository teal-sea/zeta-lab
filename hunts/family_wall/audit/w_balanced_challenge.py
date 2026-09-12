#!/usr/bin/env python3
"""Challenge higher-dimensional W minima with balanced and defect seeds."""

from __future__ import annotations

import argparse
import json
from pathlib import Path

import numpy as np
from scipy.optimize import brentq

from audit import H, kernel_all, polish_simplex


def kernel_zero(index: int) -> float:
    return brentq(
        lambda x: float(kernel_all(x)[0]),
        index - 0.45,
        index + 0.45,
        xtol=5e-15,
    )


def rotations(bits: np.ndarray):
    seen = set()
    for shift in range(bits.size):
        candidate = tuple(np.roll(bits, shift).tolist())
        if candidate not in seen:
            seen.add(candidate)
            yield np.asarray(candidate, dtype=int)


def balanced_bits(length: int, high_count: int) -> np.ndarray:
    indices = np.arange(length + 1)
    prefix = np.floor(high_count * indices / length).astype(int)
    return np.diff(prefix)


def period37_bits(length: int, phase: int) -> np.ndarray:
    indices = np.arange(phase, phase + length + 1)
    prefix = np.floor(18 * indices / 37).astype(int)
    return np.diff(prefix)


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--n", type=int, nargs="+", default=[14, 16, 20, 30, 56, 100])
    parser.add_argument("--output", type=Path, default=Path("results/w-balanced-challenge.json"))
    parser.add_argument("--max-rotations", type=int, default=37)
    args = parser.parse_args()
    root1, root2 = kernel_zero(1), kernel_zero(2)
    value_pairs = ((1.0, 2.0), (root1, root2), (1.036075, 1.963925))
    records = []

    for n in args.n:
        k = n - 1
        cap = k / H
        bit_patterns: dict[tuple[int, ...], np.ndarray] = {}
        integer_high_limit = int(np.floor(cap - k + 1e-12))
        for high_count in range(max(0, integer_high_limit - 3), min(k, integer_high_limit + 3) + 1):
            all_rotations = list(rotations(balanced_bits(k, high_count)))
            if len(all_rotations) > args.max_rotations:
                chosen = np.linspace(0, len(all_rotations) - 1, args.max_rotations, dtype=int)
                all_rotations = [all_rotations[index] for index in chosen]
            for bits in all_rotations:
                bit_patterns[tuple(bits)] = bits
        for phase in range(37):
            bits = period37_bits(k, phase)
            bit_patterns[tuple(bits)] = bits
        alternating = np.arange(k) % 2
        for bits in rotations(alternating):
            bit_patterns[tuple(bits)] = bits

        best = None
        starts = 0
        for bits in bit_patterns.values():
            for low, high in value_pairs:
                x0 = low + (high - low) * bits
                if x0.sum() > cap:
                    x0 *= cap / x0.sum()
                result = polish_simplex(x0, cap, ftol=1e-14, maxiter=10000)
                starts += 1
                if best is None or result.fun < best.fun:
                    best = result
        assert best is not None
        record = {
            "n": n,
            "objective": float(best.fun),
            "gaps": [float(x) for x in best.x],
            "gaps_decimal": [format(float(x), ".17g") for x in best.x],
            "sum": float(best.x.sum()),
            "cap": cap,
            "distinct_patterns": len(bit_patterns),
            "polished_starts": starts,
        }
        records.append(record)
        print(json.dumps(record, indent=2))

    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps({"results": records}, indent=2) + "\n")


if __name__ == "__main__":
    main()
