"""Replay finite weighted moments without solving or changing saved vectors.

Floor heights, feasibility, drift and common-period variance use rational
arithmetic. Prime-weighted moments use mpmath at two explicit precisions.
The exact counterexample and general inequalities are in FINITE_TRANSFER.md.
"""
from __future__ import annotations

import argparse
from collections import Counter
from datetime import datetime, timezone
from fractions import Fraction
import hashlib
import json
from pathlib import Path
import sys
import time

from mpmath import mp

ROOT = Path(__file__).resolve().parents[2]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))
from hunts.quotient_certificate.probe import prime_powers, quotient_cells


def mass_factors(N: int) -> dict[int, Counter]:
    """Exact m_q = sum_p count[q,p] log(p), retaining zero-weight cells."""
    result = {q: Counter() for q in quotient_cells(N)}
    for d, p in prime_powers(N):
        result[N // d][p] += 1
    return result


def floor_rows(cells: list[int], y: int) -> list[list[int]]:
    """Integer evaluation matrix; its row differences determine the kernel."""
    if not cells or y < 1 or any(q < 1 for q in cells):
        raise ValueError("positive cells and nonempty support required")
    return [[q // j for j in range(1, y + 1)] for q in cells]


def period_variance(c: list[Fraction]) -> Fraction:
    """Full-period quadratic form, evaluated through the Jordan divisor sum."""
    if not c:
        raise ValueError("nonempty coefficient vector required")
    y = len(c)
    jordan = [d * d for d in range(y + 1)]
    for d in range(1, y + 1):
        for multiple in range(2 * d, y + 1, d):
            jordan[multiple] -= jordan[d]
    return sum((jordan[d] * sum((c[j - 1] / j
                for j in range(d, y + 1, d)), Fraction()) ** 2
                for d in range(2, y + 1)), Fraction()) / 12


def finite_moments(N: int, c: list[Fraction], dps: int) -> dict:
    """Evaluate centered drift and fluctuation terms on the actual measure."""
    if not c or any(not isinstance(v, Fraction) for v in c):
        raise ValueError("nonempty exact Fraction coefficients required")
    if dps < 30:
        raise ValueError("at least 30 decimal digits required")
    factors = mass_factors(N)
    cells = list(factors)
    heights = {q: sum((v * (q // j) for j, v in enumerate(c, 1)), Fraction())
               for q in cells}
    if min(heights.values()) < 1:
        raise ValueError("coefficient vector fails attainable-cell coverage")
    active = [q for q in cells if factors[q]]
    A = sum((v / j for j, v in enumerate(c, 1)), Fraction())
    offset = sum((v * Fraction(j - 1, 2 * j)
                  for j, v in enumerate(c, 1)), Fraction())
    # Direct fractional-part evaluation, independent of the floor-height sum.
    saw = {q: sum((v * (Fraction(q % j, j) - Fraction(j - 1, 2 * j))
                   for j, v in enumerate(c, 1)), Fraction()) for q in active}
    if any(heights[q] != q * A - saw[q] - offset for q in active):
        raise ArithmeticError("exact drift identity failed")
    full = period_variance(c)
    with mp.workdps(dps):
        def number(x):
            return mp.mpf(x.numerator) / x.denominator

        logs = {p: mp.log(p) for counts in factors.values() for p in counts}
        mass = {q: mp.fsum(k * logs[p] for p, k in factors[q].items())
                for q in active}
        psi = mp.fsum(mass.values())
        probs = {q: mass[q] / psi for q in active}

        def mean(values):
            return mp.fsum(probs[q] * values[q] for q in active)

        def cov(left, right):
            ml, mr = mean(left), mean(right)
            return mp.fsum(probs[q] * (left[q] - ml) * (right[q] - mr)
                           for q in active)

        X = {q: number(heights[q] - 1) for q in active}
        S = {q: number(saw[q]) for q in active}
        Q = {q: mp.mpf(q) for q in active}
        mu, v, vs, vq, h = mean(X), cov(X, X), cov(S, S), cov(Q, Q), cov(Q, S)
        drift, cross = number(A) ** 2 * vq, -2 * number(A) * h
        # Evaluate residuals directly to avoid subtracting close variances.
        beta = h / vq if vq else mp.mpf(0)
        residual = {q: S[q] - beta * Q[q] for q in active}
        residual_var = cov(residual, residual)
        mismatch = (number(A) - beta) ** 2 * vq
        alpha = min(probs.values())
        atom_bound = (psi * mp.sqrt(alpha * v / (1 - alpha))
                      if len(active) > 1 else mp.mpf(0))
        mean_max_bound = psi * (v + mu ** 2) / max(X.values()) if max(X.values()) else mp.mpf(0)
        scalars = {
            "psi": psi, "excess": psi * mu, "mean_slack": mu,
            "variance_W": v, "variance_S": vs, "variance_q": vq,
            "covariance_q_S": h, "drift_variance": drift,
            "cross_term": cross, "regression_slope": beta,
            "residual_variance": residual_var, "drift_mismatch": mismatch,
            "period_variance": number(full), "minimum_probability": alpha,
            "atom_excess_lower_bound": atom_bound,
            "max_slack_excess_lower_bound": mean_max_bound,
            "maximum_slack": max(X.values()),
            "drift_identity_defect": abs(v - vs - drift - cross),
            "residual_identity_defect": abs(v - residual_var - mismatch),
        }
        if full:
            scalars["height_to_period_variance_ratio"] = v / number(full)
            scalars["saw_to_period_variance_ratio"] = vs / number(full)
        else:
            # Explicitly undefined, rather than silently converting 0/0 to zero.
            scalars["height_to_period_variance_ratio"] = None
            scalars["saw_to_period_variance_ratio"] = None
        tolerance = mp.power(10, -dps + 12) * max(1, vs, drift, v)
        if max(scalars["drift_identity_defect"], scalars["residual_identity_defect"]) > tolerance:
            raise ArithmeticError("finite centered identity failed")
        if atom_bound > psi * mu + tolerance or mean_max_bound > psi * mu + tolerance:
            raise ArithmeticError("linear excess inequality failed")
        return {"N": N, "y": len(c), "dps": dps,
                "cells_checked": len(cells), "positive_mass_cells": len(active),
                "zero_mass_cells": len(cells) - len(active),
                "minimum_height_exact": str(min(heights.values())),
                "A_exact": str(A), "period_variance_exact": str(full),
                **{key: None if value is None else mp.nstr(value, dps - 8)
                   for key, value in scalars.items()}}


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    source = Path(__file__).with_name("results.json")
    if args.output.resolve() == source.resolve():
        parser.error("the original results.json archive must remain unchanged")
    payload = source.read_bytes()
    saved = json.loads(payload)
    if saved["status"] != "complete" or saved["completed"] != len(saved["results"]):
        raise ValueError("source archive is incomplete")
    cases = [("flat_N9", 9, [Fraction(1), Fraction(-1), Fraction(-1)]),
             ("e1_N9", 9, [Fraction(1), Fraction(0), Fraction(0)])]
    for t in (Fraction(0), Fraction(1, 2), Fraction(1), Fraction(2)):
        cases.append((f"atom_N4_t{t}", 4, [Fraction(1), t - 1]))
    cases.extend((f"saved_N{row['N']}", row["N"],
                  [Fraction(a, row["denominator"]) for a in row["coefficient_numerators"]])
                 for row in saved["results"])
    report = {"status": "running", "input_commit": "880ec07ae605d93f4c49e4464d8b4526457cfb65",
              "source_sha256": hashlib.sha256(payload).hexdigest(),
              "started": datetime.now(timezone.utc).isoformat(),
              "requested": len(cases), "completed": 0, "results": []}
    started = time.perf_counter()

    def write():
        args.output.write_text(json.dumps(report, indent=2) + "\n")

    write()
    print(f"started: {len(cases)} moment checks, zero optimizations", flush=True)
    try:
        for name, N, c in cases:
            tick = time.perf_counter()
            evaluations = [finite_moments(N, c, dps) for dps in (50, 80)]
            with mp.workdps(80):
                keys = ("variance_W", "variance_S", "residual_variance", "excess")
                defect = max(abs(mp.mpf(evaluations[0][k]) - mp.mpf(evaluations[1][k]))
                             / max(1, abs(mp.mpf(evaluations[1][k]))) for k in keys)
                if defect > mp.mpf("1e-39"):
                    raise ArithmeticError(f"{name}: precision response failed")
            seconds = time.perf_counter() - tick
            report["results"].append({"name": name, "evaluations": evaluations,
                                       "seconds": seconds})
            report["completed"] += 1
            write()
            print(f"completed {report['completed']}/{len(cases)}: {name}, {seconds:.3f}s", flush=True)
        report["status"] = "complete"
    except Exception as exc:
        report["status"] = "failed"
        report["error"] = f"{type(exc).__name__}: {exc}"
        print(f"FAILED after {report['completed']}/{len(cases)}: {report['error']}",
              file=sys.stderr, flush=True)
        raise
    finally:
        report["seconds"] = time.perf_counter() - started
        report["finished"] = datetime.now(timezone.utc).isoformat()
        write()
    print(f"complete: {report['completed']}/{len(cases)}, {report['seconds']:.3f}s", flush=True)


if __name__ == "__main__":
    main()
