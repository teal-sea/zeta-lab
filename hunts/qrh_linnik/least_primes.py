"""Descriptive sanity table: least primes in every reduced class, q <= Q.

For each modulus 3 <= q <= Q this computes p(q, a), the least prime congruent
to a mod q, for every a with gcd(a, q) = 1, and records

* M(q) = max_a p(q, a) and the class attaining it,
* log M(q) / log q, the quantity the Linnik exponent bounds from above,
* the 50% and 90% quantiles of log p(q, a) / log q over the reduced classes.

This is descriptive only.  The theorem in RESULTS.md bounds p(q, a) by
C(eps) q^(7/3 + eps) with an effective but uncomputed constant, so no finite
table can confirm or refute it; the table shows where the actual values sit
relative to the exponents in play (2, 7/3, 12/5, 5).

The sieve route here is cross-checked in the tests against an independent
brute-force route (`brute_least_primes`, trial division with sympy.isprime).
"""

from __future__ import annotations

import argparse
import json
import math
import time
from pathlib import Path

import numpy as np

HERE = Path(__file__).resolve().parent


def primes_upto(n: int) -> np.ndarray:
    """All primes <= n by an odd-only Eratosthenes sieve (int64 array)."""
    if n < 2:
        return np.zeros(0, dtype=np.int64)
    sieve = np.ones(n // 2 + 1, dtype=bool)  # index i <-> 2i+1
    sieve[0] = False
    for i in range(1, (math.isqrt(n) - 1) // 2 + 1):
        if sieve[i]:
            p = 2 * i + 1
            sieve[p * p // 2 :: p] = False
    odd = 2 * np.nonzero(sieve)[0] + 1
    odd = odd[odd <= n]
    return np.concatenate([np.array([2], dtype=np.int64), odd.astype(np.int64)])


def least_primes(q: int, primes: np.ndarray) -> dict[int, int]:
    """p(q, a) for every reduced a mod q, from a prime table.

    Raises ValueError if the table is too short to reach every class."""
    units = [a for a in range(q) if math.gcd(a, q) == 1]
    r = primes % q
    first = np.full(q, -1, dtype=np.int64)
    idx = np.arange(len(primes), dtype=np.int64)
    first[r[::-1]] = idx[::-1]  # last write wins, so reversed order keeps the first hit
    out = {}
    for a in units:
        i = int(first[a])
        if i < 0:
            raise ValueError(f"prime table too short for q={q}, a={a}")
        out[a] = int(primes[i])
    return out


def brute_least_primes(q: int) -> dict[int, int]:
    """Independent route: walk n = a, a+q, ... with sympy.isprime."""
    from sympy import isprime

    out = {}
    for a in range(q):
        if math.gcd(a, q) != 1:
            continue
        n = a if a > 1 else a + q
        while not isprime(n):
            n += q
        out[a] = n
    return out


def summarize(q: int, table: dict[int, int]) -> dict:
    vals = np.array(sorted(table.values()), dtype=float)
    a_max = max(table, key=table.get)
    lq = math.log(q)
    ratios = np.log(vals) / lq
    return {
        "q": q,
        "M": int(table[a_max]),
        "a_max": int(a_max),
        "exp_max": float(math.log(table[a_max]) / lq),
        "exp_q50": float(np.quantile(ratios, 0.5)),
        "exp_q90": float(np.quantile(ratios, 0.9)),
    }


def run(Q: int, limit: int) -> dict:
    t0 = time.perf_counter()
    primes = primes_upto(limit)
    t_sieve = time.perf_counter() - t0
    rows = []
    for q in range(3, Q + 1):
        # scan a prefix first; fall back to the whole table if a class is missing
        cut = int(np.searchsorted(primes, 64 * q * max(1.0, math.log(q)) ** 2))
        try:
            table = least_primes(q, primes[: max(cut, 64)])
        except ValueError:
            table = least_primes(q, primes)
        rows.append(summarize(q, table))
    t_total = time.perf_counter() - t0
    big = [r for r in rows if r["q"] >= 100]
    worst = max(big, key=lambda r: r["exp_max"])
    return {
        "Q": Q,
        "prime_table_limit": limit,
        "n_primes": int(len(primes)),
        "seconds_sieve": round(t_sieve, 3),
        "seconds_total": round(t_total, 3),
        "max_exp_max_all_q": max(r["exp_max"] for r in rows),
        "argmax_all_q": max(rows, key=lambda r: r["exp_max"])["q"],
        "max_exp_max_q_ge_100": worst["exp_max"],
        "argmax_q_ge_100": worst["q"],
        "count_exp_max_ge_2": sum(r["exp_max"] >= 2 for r in rows),
        "max_exp_q90_q_ge_100": max(r["exp_q90"] for r in big),
        "rows": rows,
    }


def plot(result: dict, path: Path) -> None:
    import matplotlib

    matplotlib.use("Agg")
    import matplotlib.pyplot as plt

    rows = result["rows"]
    q = np.array([r["q"] for r in rows])
    emax = np.array([r["exp_max"] for r in rows])
    e90 = np.array([r["exp_q90"] for r in rows])
    ink, muted, grid = "#0b0b0b", "#52514e", "#e4e3df"
    blue, orange = "#2a78d6", "#eb6834"

    fig, ax = plt.subplots(figsize=(7.6, 4.2), dpi=130)
    fig.patch.set_facecolor("#fcfcfb")
    ax.set_facecolor("#fcfcfb")
    ax.scatter(q, emax, s=3, color=blue, linewidths=0, label="max over a of log p(q,a) / log q")
    ax.scatter(q, e90, s=3, color=orange, linewidths=0, label="90% quantile over a")
    refs = [
        (7 / 3, "7/3: this hunt (given 7/8 + CGL)"),
        (12 / 5, "12/5: classical density"),
        (2, "2: GRH"),
        (7 / 6, "7/6: almost all a (this hunt)"),
    ]
    for y, text in refs:
        ax.axhline(y, color=muted, lw=0.8, ls=(0, (4, 3)), zorder=0)
        ax.text(q.max() * 1.02, y, text, va="center", ha="left", fontsize=7.5, color=muted)
    ax.set_xscale("log")
    ax.set_xlim(3, q.max())
    ax.set_ylim(0.9, 2.8)
    ax.set_xlabel("modulus q", color=ink)
    ax.set_ylabel("log p / log q", color=ink)
    ax.set_title(
        f"Least primes in reduced classes, 3 <= q <= {result['Q']} (descriptive)",
        fontsize=10,
        color=ink,
    )
    ax.grid(True, axis="x", color=grid, lw=0.6)
    for side in ("top", "right"):
        ax.spines[side].set_visible(False)
    ax.tick_params(colors=muted, labelsize=8)
    ax.legend(loc="upper left", fontsize=7.5, frameon=False, markerscale=3)
    fig.tight_layout(rect=(0, 0, 0.74, 1))
    fig.savefig(path)
    plt.close(fig)


def main(argv=None) -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--Q", type=int, default=5000)
    ap.add_argument("--limit", type=int, default=20_000_000)
    ap.add_argument("--out", type=Path, default=HERE / "least_primes.json")
    ap.add_argument("--figure", type=Path, default=HERE / "least_primes.png")
    args = ap.parse_args(argv)
    result = run(args.Q, args.limit)
    summary = {k: v for k, v in result.items() if k != "rows"}
    print(json.dumps(summary, indent=2))
    plot(result, args.figure)
    compact = dict(summary)
    compact["row_fields"] = ["q", "M", "a_max", "exp_q50", "exp_q90"]
    compact["rows"] = [
        [r["q"], r["M"], r["a_max"], round(r["exp_q50"], 4), round(r["exp_q90"], 4)]
        for r in result["rows"]
    ]
    args.out.write_text(json.dumps(compact, separators=(",", ":")) + "\n", encoding="utf-8")
    return 0


if __name__ == "__main__":  # pragma: no cover
    raise SystemExit(main())
