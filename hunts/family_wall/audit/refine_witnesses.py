#!/usr/bin/env python3
"""Solve the local KKT equations at the best discovered W basins."""

from __future__ import annotations

import argparse
import json
from pathlib import Path

import numpy as np
from scipy.optimize import root

from audit import H, hessian, objective_and_gradient


REQUESTED = [7, 8, 9, 10, 12, 14, 16, 20, 30, 56, 100]


def load_best(paths: list[Path]) -> dict[int, dict]:
    best = {}
    for path in paths:
        payload = json.loads(path.read_text())
        for record in payload.get("results", []):
            n = int(record["n"])
            if n in REQUESTED and (n not in best or record["objective"] < best[n]["objective"]):
                best[n] = record
    return best


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("inputs", nargs="+", type=Path)
    parser.add_argument("--output", type=Path, default=Path("results/w-refined.json"))
    args = parser.parse_args()
    starts = load_best(args.inputs)
    records = []
    for n in REQUESTED:
        record = starts[n]
        g0 = np.array(record["gaps"], dtype=float)
        cap = (n - 1) / H
        active = bool(cap - g0.sum() < 1e-6)
        if active:
            # The binary64 value of cap can lie a few ulps above the true
            # transcendental cap.  Reserve explicit slack before solving the
            # equality KKT system so the emitted decimal witness is safe.
            constraint_cap = cap - 1e-10
            initial_lambda = -float(np.mean(objective_and_gradient(g0)[1]))
            z0 = np.concatenate((g0, [initial_lambda]))

            def equations(z):
                grad = objective_and_gradient(z[:-1])[1]
                return np.concatenate((grad + z[-1], [z[:-1].sum() - constraint_cap]))

            def jacobian(z):
                k = n - 1
                matrix = np.empty((k + 1, k + 1))
                matrix[:k, :k] = hessian(z[:-1])
                matrix[:k, k] = 1.0
                matrix[k, :k] = 1.0
                matrix[k, k] = 0.0
                return matrix

            solved = root(equations, z0, jac=jacobian, method="lm", options={"ftol": 1e-14, "xtol": 1e-14, "gtol": 1e-14, "maxiter": 5000})
            gaps = solved.x[:-1]
            multiplier = float(solved.x[-1])
            residual = float(np.max(np.abs(equations(solved.x))))
        else:
            solved = root(
                lambda x: objective_and_gradient(x)[1],
                g0,
                jac=hessian,
                method="lm",
                options={"ftol": 1e-14, "xtol": 1e-14, "gtol": 1e-14, "maxiter": 5000},
            )
            gaps = solved.x
            multiplier = 0.0
            residual = float(np.max(np.abs(objective_and_gradient(gaps)[1])))
        value = objective_and_gradient(gaps)[0]
        if np.min(gaps) <= 0 or gaps.sum() > cap + 2e-10:
            raise RuntimeError(f"refinement left feasible set for n={n}")
        refined = {
            "n": n,
            "objective": float(value),
            "gaps": [float(x) for x in gaps],
            "gaps_decimal": [format(float(x), ".17g") for x in gaps],
            "sum": float(gaps.sum()),
            "cap": cap,
            "active_cap": active,
            "cap_safety_backoff": 1e-10 if active else 0.0,
            "multiplier": multiplier,
            "equation_residual_inf": residual,
            "solver_success": bool(solved.success),
            "solver_message": str(solved.message),
        }
        records.append(refined)
        print(json.dumps({k: refined[k] for k in ("n", "objective", "sum", "cap", "active_cap", "multiplier", "equation_residual_inf", "solver_success")}, indent=2))

    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps({"results": records}, indent=2) + "\n")


if __name__ == "__main__":
    main()
