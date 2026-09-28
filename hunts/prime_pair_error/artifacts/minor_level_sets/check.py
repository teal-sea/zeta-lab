"""One bounded diagnostic for MINOR_LEVEL_SETS.md, with exact integer algebra.

Run from the repository root with .venv/bin/python. No prime data are sampled.
The fixed cases stop at N=1024; an alarm stops execution after 20 seconds.
Every invocation writes and prints a result, including failures and zero cases.
"""

from __future__ import annotations

import hashlib
import itertools
import json
from pathlib import Path
import signal
import subprocess
import sys
import time


def correlations(a):
    return [sum(a[j] * a[j + h] for j in range(len(a) - h))
            for h in range(len(a))]


def fourth_by_differences(a):
    c = correlations(a)
    return c[0] ** 2 + 2 * sum(x * x for x in c[1:])


def fourth_by_sums(a):
    c = [0] * (2 * len(a) - 1)
    for i, x in enumerate(a):
        for j, y in enumerate(a):
            c[i + j] += x * y
    return sum(x * x for x in c)


def polynomial_case(r):
    d, m, n = 2 ** (2 * r), 2 ** (3 * r), 2 ** (5 * r)
    assert n <= 1024
    a, b = [1], [1]
    for _ in range(2 * r):
        a, b = a + b, a + [-x for x in b]
    ca, cb = correlations(a), correlations(b)
    assert ca[0] + cb[0] == 2 * d
    assert all(x + y == 0 for x, y in zip(ca[1:], cb[1:]))
    fourths = []
    for coefficients in (a * m, b * m):
        assert len(coefficients) == n
        assert set(coefficients) <= {-1, 1}
        assert sum(x * x for x in coefficients) == n
        differences = fourth_by_differences(coefficients)
        sums = fourth_by_sums(coefficients)
        assert differences == sums
        fourths.append(differences)
    kernel_fourth = fourth_by_differences([1] * m)
    assert 3 * kernel_fourth == 2 * m ** 3 + m
    assert sum(fourths) >= 2 * d ** 2 * kernel_fourth
    assert max(fourths) >= d ** 2 * kernel_fourth
    assert 3 * max(fourths) >= 2 * d ** 2 * m ** 3
    return {
        "r": r, "N": n, "d": d, "m": m,
        "fourth_A": fourths[0], "fourth_B": fourths[1],
        "lower_bound_for_max": d ** 2 * kernel_fourth,
        "kernel_fourth": kernel_fourth,
        "coefficient_count_per_polynomial": n,
        "l2_squared_per_polynomial": n,
        "integer_routes_agree": True,
        "recursion_complement_identity": True,
        "status": "passed",
    }


def gaussian_add(x, y):
    return (x[0] + y[0], x[1] + y[1])


def gaussian_neg(x):
    return (-x[0], -x[1])


def gaussian_i(x):
    return (-x[1], x[0])


def gaussian_fourth(x):
    return (x[0] ** 2 + x[1] ** 2) ** 2


def nonnegative_conversion_cases():
    """Check equation (20) after multiplying away all denominators."""
    values = list(itertools.product(range(-2, 3), repeat=2))
    count = 0
    min_slack = None
    for u, g, h in itertools.product(values, repeat=3):
        two_u = (2 * u[0], 2 * u[1])
        v = gaussian_add(g, h)
        w = gaussian_i(gaussian_add(g, gaussian_neg(h)))
        twice_f = [gaussian_add(two_u, x)
                   for x in (v, gaussian_neg(v), w, gaussian_neg(w))]
        slack = (sum(gaussian_fourth(x) for x in twice_f)
                 - 4 * (gaussian_fourth(g) + gaussian_fourth(h)))
        assert slack >= 0
        min_slack = slack if min_slack is None else min(min_slack, slack)
        count += 1
    assert count == 15625
    return {"cases_checked": count, "minimum_integer_slack": min_slack,
            "status": "passed"}


def timeout_handler(signum, frame):
    raise TimeoutError("20-second diagnostic limit reached")


def main():
    started = time.monotonic()
    here = Path(__file__).resolve()
    root = here.parents[4]
    result = {
        "status": "running", "polynomial_cases": [],
        "polynomial_cases_requested": 2,
        "polynomial_cases_completed": 0,
        "maximum_N": 1024, "wall_limit_seconds": 20,
        "processes": 1, "worker_threads": 0,
        "scope": "finite integer identities, no arc quadrature or prime estimate",
    }
    signal.signal(signal.SIGALRM, timeout_handler)
    signal.alarm(20)
    exit_code = 0
    try:
        result["base_revision"] = subprocess.check_output(
            ["git", "merge-base", "HEAD", "2da62eb9842db72d4f6bad09c6f13efe384d6ab7"],
            cwd=root, text=True, timeout=3).strip()
        result["script_sha256"] = hashlib.sha256(here.read_bytes()).hexdigest()
        result["proof_sha256"] = hashlib.sha256(
            (root / "hunts/prime_pair_error/MINOR_LEVEL_SETS.md").read_bytes()
        ).hexdigest()
        for r in (1, 2):
            result["polynomial_cases"].append(polynomial_case(r))
            result["polynomial_cases_completed"] += 1
        result["nonnegative_conversion"] = nonnegative_conversion_cases()
        assert result["polynomial_cases_completed"] == 2
        result["status"] = "passed"
    except Exception as exc:
        result["status"] = "failed"
        result["error"] = {"type": type(exc).__name__, "message": str(exc)}
        exit_code = 1
    finally:
        signal.alarm(0)
        result["elapsed_seconds"] = round(time.monotonic() - started, 6)
        output = json.dumps(result, indent=2, sort_keys=True) + "\n"
        here.with_name("result.json").write_text(output)
        print(output, end="")
    return exit_code


if __name__ == "__main__":
    sys.exit(main())
