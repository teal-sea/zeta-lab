#!/usr/bin/env python3
"""Independent basin enumeration and deterministic challenge for F_{7,3000}."""

from __future__ import annotations

import argparse
import itertools
import json
from pathlib import Path

import numpy as np
from scipy.optimize import brentq, direct, minimize

from audit import kernel_all, objective, objective_and_gradient, weight_all


def kernel_zero(index: int) -> float:
    if index < 1:
        raise ValueError(index)
    return brentq(
        lambda x: float(kernel_all(x)[0]),
        max(0.0, index - 0.45),
        index + 0.45,
        xtol=5e-15,
    )


def canonical(gaps: np.ndarray) -> tuple[float, ...]:
    direct_key = tuple(np.round(gaps, 10))
    reverse_key = tuple(np.round(gaps[::-1], 10))
    return min(direct_key, reverse_key)


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--pressure", type=float, default=3000.0)
    parser.add_argument("--incumbent", type=float, default=0.0038262312113046)
    parser.add_argument("--max-lobe-sum", type=int, default=13)
    parser.add_argument("--direct-maxfun", type=int, default=0)
    parser.add_argument("--output", type=Path, default=Path("results/f7-landscape.json"))
    args = parser.parse_args()

    pressure = args.pressure
    incumbent = args.incumbent
    singleton_threshold = 3.0 * incumbent
    first_zero = kernel_zero(1)
    gap_lower = brentq(
        lambda x: float(weight_all(x)[0]) - singleton_threshold,
        0.0,
        first_zero,
        xtol=5e-15,
    )
    sum_upper = pressure * incumbent
    gap_upper = sum_upper - 5.0 * gap_lower
    roots = [kernel_zero(i) for i in range(1, int(np.ceil(gap_upper)) + 1)]

    minima: dict[tuple[float, ...], dict] = {}
    starts = 0
    for labels in itertools.product(range(1, len(roots) + 1), repeat=6):
        if sum(labels) > args.max_lobe_sum:
            continue
        x0 = np.array([roots[label - 1] for label in labels])
        if x0.sum() > sum_upper + 2.0:
            continue
        starts += 1
        result = minimize(
            fun=lambda x: objective_and_gradient(x, pressure),
            x0=x0,
            jac=True,
            method="L-BFGS-B",
            bounds=[(gap_lower, gap_upper)] * 6,
            options={"ftol": 1e-15, "gtol": 1e-13, "maxiter": 20000, "maxls": 60},
        )
        key = canonical(result.x)
        old = minima.get(key)
        record = {
            "objective": float(result.fun),
            "gaps": [float(x) for x in result.x],
            "sum": float(result.x.sum()),
            "labels": labels,
            "gradient_inf": float(np.max(np.abs(objective_and_gradient(result.x, pressure)[1]))),
        }
        if old is None or record["objective"] < old["objective"]:
            minima[key] = record

    ranked = sorted(minima.values(), key=lambda item: item["objective"])
    direct_record = None
    if args.direct_maxfun:
        result = direct(
            lambda x: objective(x, pressure),
            [(gap_lower, gap_upper)] * 6,
            locally_biased=False,
            eps=1e-8,
            maxfun=args.direct_maxfun,
            maxiter=args.direct_maxfun,
        )
        polished = minimize(
            fun=lambda x: objective_and_gradient(x, pressure),
            x0=result.x,
            jac=True,
            method="L-BFGS-B",
            bounds=[(gap_lower, gap_upper)] * 6,
            options={"ftol": 1e-15, "gtol": 1e-13, "maxiter": 20000},
        )
        direct_record = {
            "raw_objective": float(result.fun),
            "raw_gaps": [float(x) for x in result.x],
            "evaluations": int(result.nfev),
            "message": str(result.message),
            "polished_objective": float(polished.fun),
            "polished_gaps": [float(x) for x in polished.x],
        }

    payload = {
        "pressure": pressure,
        "incumbent_used_for_domain": incumbent,
        "singleton_threshold": singleton_threshold,
        "gap_lower": gap_lower,
        "sum_upper": sum_upper,
        "gap_upper": gap_upper,
        "kernel_zeros": roots,
        "enumerated_starts": starts,
        "distinct_minima": len(ranked),
        "best_minima": ranked[:50],
        "direct": direct_record,
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(payload, indent=2) + "\n")
    print(json.dumps({**payload, "best_minima": ranked[:5]}, indent=2))


if __name__ == "__main__":
    main()
