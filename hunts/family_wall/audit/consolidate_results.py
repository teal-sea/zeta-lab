#!/usr/bin/env python3
"""Select and re-diagnose the best W witness found for every requested n."""

from __future__ import annotations

import argparse
import json
from pathlib import Path

import mpmath as mp
import numpy as np

from audit import H, hessian, mp_objective, objective_and_gradient


REQUESTED = [7, 8, 9, 10, 12, 14, 16, 20, 30, 56, 100]


def records_from(path: Path):
    payload = json.loads(path.read_text())
    for record in payload.get("results", []):
        yield record


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("inputs", nargs="+", type=Path)
    parser.add_argument("--output", type=Path, default=Path("results/search-results.json"))
    args = parser.parse_args()

    best: dict[int, tuple[dict, str]] = {}
    comparisons: dict[int, list[dict]] = {n: [] for n in REQUESTED}
    for path in args.inputs:
        if not path.exists():
            continue
        for record in records_from(path):
            n = int(record["n"])
            if n not in comparisons:
                continue
            candidate = {
                "source": str(path),
                "objective": float(record["objective"]),
            }
            comparisons[n].append(candidate)
            if n not in best or record["objective"] < best[n][0]["objective"]:
                best[n] = (record, str(path))

    missing = [n for n in REQUESTED if n not in best]
    if missing:
        raise RuntimeError(f"missing n: {missing}")

    results = []
    for n in REQUESTED:
        raw, source = best[n]
        gaps_decimal = raw.get("gaps_decimal") or [repr(x) for x in raw["gaps"]]
        gaps = np.array([float(x) for x in gaps_decimal])
        value, gradient = objective_and_gradient(gaps)
        cap = (n - 1) / H
        slack = cap - float(gaps.sum())
        active = slack < 1e-7
        if active:
            multiplier = -float(np.mean(gradient))
            kkt_residual = float(np.max(np.abs(gradient + multiplier)))
        else:
            multiplier = 0.0
            kkt_residual = float(np.max(np.abs(gradient)))

        matrix = hessian(gaps)
        if active:
            # Orthonormal basis for the tangent space sum(v)=0.
            raw_basis = np.vstack((np.eye(n - 2), -np.ones(n - 2)))
            basis, _ = np.linalg.qr(raw_basis)
            min_eigenvalue = float(np.linalg.eigvalsh(basis.T @ matrix @ basis)[0])
        else:
            min_eigenvalue = float(np.linalg.eigvalsh(matrix)[0])

        with mp.workdps(90):
            high_value = mp_objective(gaps_decimal, dps=90)
            high_string = mp.nstr(high_value, 70)
        results.append(
            {
                "n": n,
                "W_double": value,
                "W_high_precision": high_string,
                "bound_double": H * (1 + value),
                "gaps_decimal": gaps_decimal,
                "sum_decimal": format(float(gaps.sum()), ".17g"),
                "cap_double": cap,
                "cap_slack_double": slack,
                "active_cap": active,
                "kkt_multiplier": multiplier,
                "kkt_residual_inf": kkt_residual,
                "projected_hessian_min_eigenvalue": min_eigenvalue,
                "selected_from": source,
                "candidate_objectives": sorted(comparisons[n], key=lambda x: x["objective"]),
            }
        )

    output = {
        "H_double": H,
        "claimed_bound": 0.6751676068,
        "target": 0.6818286874638,
        "claimed_W_threshold_double": 0.6751676068 / H - 1,
        "target_W_threshold_double": 0.6818286874638 / H - 1,
        "results": results,
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(output, indent=2) + "\n")
    print(json.dumps({"results": [{k: r[k] for k in ("n", "W_double", "bound_double", "sum_decimal", "active_cap", "kkt_residual_inf", "projected_hessian_min_eigenvalue", "selected_from")} for r in results]}, indent=2))


if __name__ == "__main__":
    main()
