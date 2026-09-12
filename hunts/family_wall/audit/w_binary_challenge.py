#!/usr/bin/env python3
"""Challenge low-dimensional W searches from every promising 1/2 skeleton."""

from __future__ import annotations

import argparse
import heapq
import itertools
import json
from pathlib import Path

import numpy as np
from scipy.optimize import brentq

from audit import H, kernel_all, objective, polish_simplex


def kernel_zero(index: int) -> float:
    return brentq(
        lambda x: float(kernel_all(x)[0]),
        max(0.0, index - 0.45),
        index + 0.45,
        xtol=5e-15,
    )


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--n", type=int, nargs="+", default=[7, 8, 9, 10, 12])
    parser.add_argument("--top", type=int, default=300)
    parser.add_argument("--output", type=Path, default=Path("results/w-binary-challenge.json"))
    args = parser.parse_args()
    roots = np.array([kernel_zero(1), kernel_zero(2)])
    records = []

    for n in args.n:
        k = n - 1
        cap = k / H
        ranked: list[tuple[float, tuple[int, ...]]] = []
        feasible_skeletons = 0
        for bits in itertools.product((0, 1), repeat=k):
            skeleton = np.array(bits, dtype=int) + 1
            if skeleton.sum() > cap + 1e-12:
                continue
            feasible_skeletons += 1
            value = objective(skeleton)
            item = (-value, tuple(bits))
            if len(ranked) < args.top:
                heapq.heappush(ranked, item)
            elif value < -ranked[0][0]:
                heapq.heapreplace(ranked, item)

        candidates = sorted([(-negative, bits) for negative, bits in ranked])
        best = None
        polished_count = 0
        for _, bits in candidates:
            for x0 in (np.array(bits, dtype=float) + 1.0, roots[np.array(bits, dtype=int)]):
                if x0.sum() > cap:
                    x0 *= cap / x0.sum()
                result = polish_simplex(x0, cap, ftol=1e-14, maxiter=10000)
                polished_count += 1
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
            "feasible_binary_skeletons": feasible_skeletons,
            "ranked_skeletons": len(candidates),
            "polished_starts": polished_count,
        }
        records.append(record)
        print(json.dumps(record, indent=2))

    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps({"results": records}, indent=2) + "\n")


if __name__ == "__main__":
    main()
