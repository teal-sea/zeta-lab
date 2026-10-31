"""Gabcke's coefficient recursion, Satz 2.1.1.

The numbers ``lambda_n`` are defined by ``lambda_0 = 1`` and

    (n + 1) lambda_{n+1} = sum_{k=0}^{n} 2^{4k+1} |E_{2k+2}| lambda_{n-k}

where ``E_{2k}`` are the Euler numbers. The seven values printed on pages
19-20 of the 2015 PDF are the check. Matching them does not prove the
remainder bound.
"""
from __future__ import annotations

from math import comb

# Printed in Satz 2.1.1, and stated there to be prime factorizations.
PRINTED = (
    1,
    2,
    2 * 41,
    4 * 3 * 881,
    2 * 3 * 7 * 68111,
    4 * 3 * 47 * 499 * 4729,
    4 * 3 * 409 * 193077047,
)


def euler_even(m: int) -> dict[int, int]:
    """Even Euler numbers ``E_0, E_2, ..., E_{2m}`` from the secant recurrence."""
    out = {0: 1}
    for n in range(1, m + 1):
        out[2 * n] = -sum(comb(2 * n, 2 * k) * out[2 * k] for k in range(n))
    return out


def lambdas(n_max: int) -> list[int]:
    """``lambda_0`` through ``lambda_{n_max}``."""
    euler = euler_even(n_max + 1)
    out = [1]
    for n in range(n_max):
        acc = sum(
            (2 ** (4 * k + 1)) * abs(euler[2 * k + 2]) * out[n - k]
            for k in range(n + 1)
        )
        if acc % (n + 1) != 0:
            raise ValueError(f"lambda_{n + 1} is not an integer")
        out.append(acc // (n + 1))
    return out


def matches_printed() -> bool:
    got = lambdas(len(PRINTED) - 1)
    return got == list(PRINTED)
