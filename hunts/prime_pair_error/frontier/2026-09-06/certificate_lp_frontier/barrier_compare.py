"""Compare measured LP floors with the candidate barrier laws.

Reads any number of result JSON files written by lp_allcells_cg.py /
lp_frontier.py and prints, per (N, y): the excess ratio E/N against

    0.32 / sqrt(y)              the fluctuation law fitted at y = sqrt(N),
    |M1(y)|,  M1(y) = sum_{j<=y} mu(j)/j     the Mobius drift,
    I(y) = sum_{j<=y} mu(j) log(y/j)/j - 1   the smoothed Mobius tail.

Pure bookkeeping; no LP is solved here.
"""
from __future__ import annotations

import json
import math
import sys


def mobius_table(n: int) -> list[int]:
    mu = [1] * (n + 1)
    mu[0] = 0
    is_prime = [True] * (n + 1)
    for p in range(2, n + 1):
        if not is_prime[p]:
            continue
        for q in range(p, n + 1, p):
            if q > p:
                is_prime[q] = False
            mu[q] = -mu[q]
        for q in range(p * p, n + 1, p * p):
            mu[q] = 0
    return mu


def main(paths: list[str]) -> None:
    rows = []
    for p in paths:
        with open(p) as fh:
            data = json.load(fh)
        for r in data:
            ex = r.get("excess", r.get("gap_V_minus_psi"))
            if ex is None:
                continue
            rows.append((int(r["N"]), int(r["y"]), float(ex)))
    rows.sort()
    ymax = max(y for _, y, _ in rows) if rows else 1
    mu = mobius_table(ymax)
    print(f"{'N':>9} {'y':>6} {'y=N^a':>6} {'E':>12} {'E/N':>9} {'0.32/sqrt(y)':>12} {'|M1(y)|':>9} {'I(y)':>9} {'E/(N 0.32/sqrt y)':>17} {'E/(N|M1|)':>10}")
    for N, y, ex in rows:
        M1 = sum(mu[j] / j for j in range(1, y + 1))
        I = sum(mu[j] * math.log(y / j) / j for j in range(1, y + 1)) - 1.0
        fl = 0.32 / math.sqrt(y)
        a = math.log(y) / math.log(N)
        print(
            f"{N:>9} {y:>6} {a:>6.3f} {ex:>12.2f} {ex / N:>9.5f} {fl:>12.5f} {abs(M1):>9.5f} {I:>+9.5f} "
            f"{ex / (N * fl):>17.2f} {ex / (N * abs(M1)) if M1 else float('inf'):>10.2f}"
        )


if __name__ == "__main__":
    main(sys.argv[1:])
