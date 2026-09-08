"""Exact height-kernel exclusion at N=10000, with enclosed finite bounds.

Consume one saved basis and primal from PR #208. Reconstruct its logarithmic
dual by exact rational matrix arithmetic, without an optimization call.
All logarithms use a fresh interval context; reported decimal endpoints are
rounded outwards from exact binary interval endpoints.
"""
from __future__ import annotations

import argparse
from fractions import Fraction
import hashlib
import json
from pathlib import Path
import sys
import time

from flint import fmpq, fmpq_mat
from mpmath.ctx_iv import MPIntervalContext

ROOT = Path(__file__).resolve().parents[2]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))
from hunts.quotient_certificate.finite_transfer import mass_factors

HUNT = Path(__file__).resolve().parent
RELATION = {1: 1, 2: -1, 3: 2, 4: -2, 5: 2, 6: -1, 7: -1, 8: 2,
            10: -1, 11: -1, 12: 1, 14: 1, 17: -2, 20: 2, 24: -1,
            34: 1, 41: -1, 51: 1, 61: -1, 103: -1, 123: 1}


def rational(value) -> Fraction:
    return Fraction(int(value.numerator), int(value.denominator))


def endpoint(value, index: int) -> Fraction:
    """Read one finite binary interval endpoint exactly, with no float cast."""
    sign, mantissa, exponent, bits = value._mpi_[index]
    if bits < 0:
        raise ArithmeticError("nonfinite interval endpoint")
    return Fraction((-1 if sign else 1) * mantissa) * (
        Fraction(2 ** exponent) if exponent >= 0 else Fraction(1, 2 ** (-exponent)))


def outward_bounds(lower: Fraction, upper: Fraction, digits: int = 30) -> list[str]:
    """Decimal endpoints enclosing the supplied rational interval."""
    if lower > upper or digits < 0:
        raise ValueError("ordered interval and nonnegative digit count required")
    scale = 10 ** digits
    lo = (lower.numerator * scale) // lower.denominator
    hi = -((-upper.numerator * scale) // upper.denominator)

    def decimal(integer):
        whole, remainder = divmod(abs(integer), scale)
        return f"{'-' if integer < 0 else ''}{whole}.{remainder:0{digits}d}"

    return [decimal(lo), decimal(hi)]


def enclosure(value) -> list[str]:
    return outward_bounds(endpoint(value, 0), endpoint(value, 1))


def check_consumed_basis(source: dict) -> dict:
    """Exact consumed ingredients: basis inverse, primal and every log moment."""
    N, y = source["N"], source["y"]
    if (N, y) != (10000, 100):
        raise ValueError("this deliverable tests only N=10000, y=100")
    factors = mass_factors(N)
    Q, S = list(factors), source["basis_cells"]
    if len(S) != y or len(set(S)) != y or not set(S) <= set(Q):
        raise ValueError("basis must have 100 distinct attainable cells")
    A = fmpq_mat([[s // j for j in range(1, y + 1)] for s in S])
    inverse = A.inv()
    identity = fmpq_mat([[int(i == j) for j in range(y)] for i in range(y)])
    if A * inverse != identity or inverse * A != identity:
        raise ArithmeticError("basis inverse identity failed")
    c = [Fraction(source["primal_c"].get(str(j), "0")) for j in range(1, y + 1)]
    cmat = fmpq_mat([[fmpq(v.numerator, v.denominator)] for v in c])
    ones = fmpq_mat([[1] for _ in S])
    if A * cmat != ones:
        raise ArithmeticError("consumed primal is not tight on the basis")
    heights = {q: sum((v * (q // j) for j, v in enumerate(c, 1)), Fraction()) for q in Q}
    if min(heights.values()) < 1:
        raise ArithmeticError("consumed primal violates attainable coverage")
    # Independent factorial prime exponents via Legendre's formula.
    primes = sorted({p for counts in factors.values() for p in counts})
    ell = []
    for j in range(1, y + 1):
        row = []
        for p in primes:
            n, exponent = N // j, 0
            while n:
                n //= p
                exponent += n
            row.append(exponent)
        ell.append(row)
    E = fmpq_mat(ell)
    # These are exact coefficients of log p, not rationalized logarithms.
    dual_coefficients = inverse.transpose() * E
    if A.transpose() * dual_coefficients != E:
        raise ArithmeticError("exact logarithmic moment identities failed")
    cost_coefficients = cmat.transpose() * E
    if ones.transpose() * dual_coefficients != cost_coefficients:
        raise ArithmeticError("primal/dual objective identity failed")
    archive = json.loads((HUNT / "results.json").read_text())
    archived = next(row for row in archive["results"] if row["N"] == N)
    old_c = [Fraction(a, archived["denominator"]) for a in archived["coefficient_numerators"]]
    return dict(N=N, y=y, factors=factors, S=S, primes=primes, c=c,
                heights=heights, inverse=inverse, determinant=str(A.det()),
                dual_coefficients=dual_coefficients, cost_coefficients=cost_coefficients,
                archive_equal=(old_c == c))


def analyze(source: dict, dps: int = 80) -> dict:
    """One cutoff, one exact relation, positive dual signs and interval bounds."""
    if dps < 50:
        raise ValueError("at least 50 interval digits required")
    data = check_consumed_basis(source)
    factors, primes, N, y = data["factors"], data["primes"], data["N"], data["y"]
    if not all(factors.get(q) for q in RELATION):
        raise ArithmeticError("relation uses a cell without positive prime mass")
    if sum(RELATION.values()) != 1 or any(
        sum(w * (q // j) for q, w in RELATION.items()) != 0 for j in range(1, y + 1)
    ):
        raise ArithmeticError("height-kernel exclusion relation failed")
    iv = MPIntervalContext()
    iv.dps = dps

    def fr(value):
        v = rational(value)
        return iv.mpf(v.numerator) / v.denominator

    logs = {p: iv.log(iv.mpf(p)) for p in primes}
    mass = {q: sum((k * logs[p] for p, k in counts.items()), iv.mpf(0))
            for q, counts in factors.items() if counts}
    psi = sum(mass.values(), iv.mpf(0))
    C, cost = data["dual_coefficients"], data["cost_coefficients"]
    nu = [sum((fr(C[i, k]) * logs[p] for k, p in enumerate(primes) if C[i, k]), iv.mpf(0))
          for i in range(y)]
    if any(endpoint(v, 0) <= 0 for v in nu):
        raise ArithmeticError("strict dual positivity was not established")
    T = sum((fr(cost[0, k]) * logs[p] for k, p in enumerate(primes)), iv.mpf(0))
    counts = {p: sum(row.get(p, 0) for row in factors.values()) for p in primes}
    gap = sum((fr(cost[0, k] - counts[p]) * logs[p] for k, p in enumerate(primes)), iv.mpf(0))
    delta = 2 * N - T
    if endpoint(delta, 0) <= 0:
        raise ArithmeticError("the exact optimizer does not establish a nonempty broad class")
    H = sum((w * w / mass[q] for q, w in RELATION.items()), iv.mpf(0))
    D = psi * H - 1
    if endpoint(D, 0) <= 0:
        raise ArithmeticError("variance denominator is not positive")
    alpha = logs[2] / psi
    v_basic = 1 / D
    v_optimum = (T / psi) ** 2 / D
    atom_factor = logs[2] / (psi - logs[2])
    atom_basic = psi * iv.sqrt(atom_factor / D)
    atom_optimum = T * iv.sqrt(atom_factor / D)
    self_denominator = iv.sqrt(D * (psi / logs[2] - 1)) - 1
    if endpoint(self_denominator, 0) <= 0:
        raise ArithmeticError("self-consistent atom denominator is not positive")
    atom_self = psi / self_denominator
    actual_variance = sum((mass[q] / psi * (fr(data["heights"][q]) - T / psi) ** 2
                           for q in mass), iv.mpf(0))
    # z=e_1 in basis order satisfies nonnegativity and the broad cost budget,
    # but one retained non-basis row is essential to reject this point.
    control_height = data["heights"][20] + sum(
        rational(data["inverse"][j - 1, 0]) * (20 // j) for j in range(1, y + 1))
    control_cost = T + nu[0]
    if data["S"][0] != 1 or control_height != Fraction(-13, 83) or endpoint(control_cost, 1) >= 2 * N:
        raise ArithmeticError("retained-constraint control failed")
    values = {"psi": psi, "T_star": T, "optimal_excess": gap, "Delta_broad": delta,
              "minimum_probability": alpha, "H": H, "D": D,
              "variance_floor_from_coverage": v_basic,
              "variance_floor_from_optimality": v_optimum,
              "atom_excess_from_coverage": atom_basic,
              "atom_excess_self_consistent": atom_self,
              "atom_excess_from_optimality": atom_optimum,
              "optimizer_variance": actual_variance}
    return {"status": "complete", "N": N, "y": y, "budget": 2 * N, "interval_dps": dps,
            "source": source["source"], "basis_determinant": data["determinant"],
            "basis_cells": data["S"], "primes_checked": len(primes),
            "log_moment_equalities_checked": y * len(primes),
            "all_primal_cells_checked": len(factors), "positive_mass_cells": len(mass),
            "archived_primal_equals_exact_optimizer": data["archive_equal"],
            "strictly_positive_dual_masses": len(nu),
            "minimum_dual_mass": outward_bounds(min(endpoint(v, 0) for v in nu),
                                                 min(endpoint(v, 1) for v in nu)),
            "dual_mass_enclosures": {str(s): enclosure(v) for s, v in zip(data["S"], nu)},
            "relation": RELATION, "relation_column_equalities_checked": y,
            "relation_coefficient_sum": sum(RELATION.values()),
            "height_kernel_intersection": "empty for all feasible coefficients at this N,y",
            "retained_constraint_control": {"z_basis_cell": 1, "z_value": 1,
                "violated_cell": 20, "height_exact": str(control_height),
                "cost_enclosure": enclosure(control_cost)},
            "enclosures": {key: enclosure(value) for key, value in values.items()}}


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    source_path = HUNT / "height_kernel_input.json"
    if args.output.resolve() in {source_path, HUNT / "results.json"}:
        parser.error("input and original archive must remain unchanged")
    started = time.perf_counter()
    report = {"status": "running", "completed": 0, "requested": 1}
    args.output.write_text(json.dumps(report) + "\n")
    print("started: one fixed height-kernel check, zero optimizations", flush=True)
    try:
        payload = source_path.read_bytes()
        report = analyze(json.loads(payload))
        report["input_sha256"] = hashlib.sha256(payload).hexdigest()
        report.update(completed=1, requested=1)
    except Exception as exc:
        report.update(status="failed", error=f"{type(exc).__name__}: {exc}")
        print(f"FAILED: {report['error']}", file=sys.stderr, flush=True)
        raise
    finally:
        report["seconds"] = time.perf_counter() - started
        args.output.write_text(json.dumps(report, indent=2) + "\n")
    print(f"complete: 1/1, {report['seconds']:.3f}s; kernel intersection empty", flush=True)


if __name__ == "__main__":
    main()
