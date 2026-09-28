"""Exact finite paid-surplus witness at N=144; no uniform-rate conclusion."""

from __future__ import annotations

import argparse
from fractions import Fraction as F
import importlib.util
import json
from math import isqrt
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
SPEC = importlib.util.spec_from_file_location(
    "paid_surplus_log_arithmetic", ROOT / "hunts/paid_shortfall/construction.py"
)
LOG = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(LOG)
N = 144
SUPPORT = 12
COVERAGE = 5
MASS_BOUND = F(23)
WITNESS = tuple(map(F, ("1", "-1", "-1", "0", "-1", "-13/20",
                         "7/20", "3/10", "0", "0", "0", "13/20")))


def prime_powers():
    """Enumerate pairs (prime power, prime) through the fixed cutoff."""
    sieve = [True] * (N + 1)
    sieve[0] = sieve[1] = False
    for p in range(2, isqrt(N) + 1):
        if sieve[p]:
            for d in range(p * p, N + 1, p):
                sieve[d] = False
    out = []
    for p in range(2, N + 1):
        if sieve[p]:
            power = p
            while power <= N:
                out.append((power, p))
                power *= p
    return tuple(sorted(out))


def weight(c, q):
    return sum((a * (q // j) for j, a in enumerate(c, 1)), F(0))


def class_failures(c):
    """Explicitly check each defining constraint, with no float conversion."""
    if len(c) != SUPPORT or any(not isinstance(a, (int, F)) for a in c):
        return ["coefficient domain or support"]
    failures = []
    if sum((F(a) / j for j, a in enumerate(c, 1)), F(0)) != 0:
        failures.append("harmonic balance")
    failures.extend(f"coverage q={q}" for q in range(1, COVERAGE + 1)
                    if weight(c, q) != 1)
    if sum(map(abs, c), F(0)) > MASS_BOUND:
        failures.append("coefficient mass")
    return failures


def surplus_violations(c):
    return [(d, weight(c, N // d)) for d, _ in prime_powers()
            if weight(c, N // d) > 1]


def add(vector, prime, amount):
    vector[prime] = vector.get(prime, F(0)) + amount
    if vector[prime] == 0:
        del vector[prime]


def combine(*vectors):
    out = {}
    for vector in vectors:
        for p, a in vector.items():
            add(out, p, a)
    return out


def cost_vectors(c):
    """Price every prime-power row, checked against factorial valuations."""
    B, repair, surplus, psi = {}, {}, {}, {}
    for d, p in prime_powers():
        w = weight(c, N // d)
        add(B, p, w)
        add(repair, p, max(F(0), 1 - w))
        add(surplus, p, max(F(0), w - 1))
        add(psi, p, F(1))
    factorial = {}
    for j, a in enumerate(c, 1):
        for p in sorted({p for _, p in prime_powers()}):
            power, valuation = p, 0
            while power <= N // j:
                valuation += (N // j) // power
                power *= p
            add(factorial, p, a * valuation)
    assert factorial == B, "factorial and prime-power cost disagree"
    total = combine(B, repair)
    assert total == combine(psi, surplus), "complete cost identity failed"
    return {"B": B, "P_Lambda": repair, "S": surplus, "psi": psi, "C": total}


def exact_checks(c):
    assert not class_failures(c), class_failures(c)
    assert not surplus_violations(c), surplus_violations(c)
    # Orthogonal route: count multiples by accumulating divisor coefficients.
    divisor_sum = F(0)
    for q in range(N + 1):
        if q:
            divisor_sum += sum((a for j, a in enumerate(c, 1) if q % j == 0), F(0))
        assert divisor_sum == weight(c, q)
    costs = cost_vectors(c)
    assert costs["S"] == {}
    assert costs["C"] == costs["psi"]
    return {"class_constraints_checked": 7, "prime_power_rows_checked": len(prime_powers()),
            "surplus_violations": 0, "floor_divisor_comparisons": N + 1,
            "identity_failures": 0, "mass": str(sum(map(abs, c), F(0)))}


def discover():
    """Optional floating LP discovery; its reconstructed witness is checked exactly."""
    from scipy import __version__
    from scipy.optimize import linprog

    rows = [[float(N // (d * j)) for j in range(1, SUPPORT + 1)] + [0.] * SUPPORT
            for d, _ in prime_powers()]
    rhs = [1.] * len(rows)
    for j in range(SUPPORT):
        for sign in (-1, 1):
            row = [0.] * (2 * SUPPORT)
            row[j], row[SUPPORT + j] = sign, -1
            rows.append(row)
            rhs.append(0.)
    rows.append([0.] * SUPPORT + [1.] * SUPPORT)
    rhs.append(float(MASS_BOUND))
    equalities = [[float(q // j) for j in range(1, SUPPORT + 1)] + [0.] * SUPPORT
                  for q in range(1, COVERAGE + 1)]
    equalities.append([1. / j for j in range(1, SUPPORT + 1)] + [0.] * SUPPORT)
    result = linprog([0.] * SUPPORT + [1.] * SUPPORT, A_ub=rows, b_ub=rhs,
                     A_eq=equalities, b_eq=[1.] * COVERAGE + [0.],
                     bounds=[(None, None)] * SUPPORT + [(0, None)] * SUPPORT,
                     method="highs")
    if not result.success:
        raise RuntimeError(f"discovery unresolved, not a refutation: {result.message}")
    c = tuple(F(float(v)).limit_denominator(1000000) for v in result.x[:SUPPORT])
    checks = exact_checks(c)
    return {"scipy_version": __version__, "optimizer_status": int(result.status),
            "optimizer_message": result.message, "coefficients": list(map(str, c)),
            "exact_checks": checks, "optimality_claimed": False}


def price(c):
    vectors = cost_vectors(c)
    expressions = {"B_minus_N": (-N, vectors["B"]),
                   "P_Lambda": (0, vectors["P_Lambda"]), "S": (0, vectors["S"]),
                   "C_minus_N": (-N, vectors["C"]), "psi_minus_N": (-N, vectors["psi"])}
    intervals = {}
    for backend in ("python-flint", "mpmath.iv"):
        for dps in (35, 70):
            with LOG.log_intervals(backend, dps) as log:
                intervals[backend, dps] = {
                    name: LOG.enclose_expression(constant, vector, log)
                    for name, (constant, vector) in expressions.items()}
    comparisons = 0
    for name in expressions:
        pairs = [row[name] for row in intervals.values()]
        assert max(x[0] for x in pairs) <= min(x[1] for x in pairs)
        comparisons += 1
    for backend in ("python-flint", "mpmath.iv"):
        for name in expressions:
            coarse, fine = intervals[backend, 35][name], intervals[backend, 70][name]
            if expressions[name][1]:
                assert fine[1] - fine[0] < coarse[1] - coarse[0]
            else:
                assert coarse == fine
    return {"vectors": {name: {str(p): str(a) for p, a in sorted(v.items())}
                        for name, v in vectors.items()},
            "expressions": {name: {"constant": str(constant),
                                    "prime_log_vector": {str(p): str(a) for p, a in sorted(v.items())}}
                            for name, (constant, v) in expressions.items()},
            "enclosures": {f"{backend}:{dps}": {name: list(map(str, pair)) for name, pair in row.items()}
                           for (backend, dps), row in intervals.items()},
            "expression_overlap_checks": comparisons, "evaluations": len(intervals) * len(expressions)}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--discover", action="store_true")
    args = parser.parse_args()
    checks = exact_checks(WITNESS)
    old = tuple(map(F, ("1", "-1", "-1", "0", "-1", "1", "-1", "0", "0", "1", "-1", "2/385")))
    assert not class_failures(old)
    assert len(surplus_violations(old)) == 5
    lesion = list(WITNESS)
    lesion[5] += F(6, 10)
    lesion[11] -= F(12, 10)
    assert not class_failures(lesion)
    assert surplus_violations(lesion), "balanced lesion was not detected"
    zero = (F(0),) * SUPPORT
    assert class_failures(zero), "zero decoy must fail prefix coverage"
    assert not surplus_violations(zero)
    output = {"status": "EXACT_FINITE_CONSTRUCTION", "N": N, "support": SUPPORT,
              "coverage_through": COVERAGE, "mass_bound": str(MASS_BOUND),
              "coefficients": list(map(str, WITNESS)), "checks": checks,
              "prime_power_rows": [{"d": d, "p": p, "q": N // d,
                                     "W": str(weight(WITNESS, N // d)),
                                     "slack": str(1 - weight(WITNESS, N // d))}
                                    for d, p in prime_powers()],
              "cost": price(WITNESS), "old_endpoint_cost": price(old),
              "controls": {"old_endpoint_surplus_violations": len(surplus_violations(old)),
                           "balanced_lesion_surplus_violations": len(surplus_violations(lesion)),
                           "zero_decoy_coverage_failures": len(class_failures(zero)),
                           "zero_decoy_surplus_violations": len(surplus_violations(zero))},
              "discovery": discover() if args.discover else {"status": "not requested"},
              "scope": "N=144 only; no coefficient family, uniform rate, or optimality claim"}
    args.output.write_text(json.dumps(output, indent=2, sort_keys=True) + "\n")
    print(json.dumps({"status": output["status"], "checks": checks, "controls": output["controls"],
                      "enclosed_expressions": 10, "log_evaluations": 40}))


if __name__ == "__main__":
    main()
