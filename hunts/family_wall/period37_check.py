"""Independent check of the audit's period-37 all-n witness word.

The word (audit, `audit/results/REPORT.md`, "An explicit all-n construction") is

    g_i = 1 + floor(18 i / 37) - floor(18 (i-1) / 37),      i = 1, 2, 3, ...

a period-37 word of 19 ones and 18 twos.  Its prefix of length k = n-1 has
S_k = k + floor(18 k / 37) <= (55/37) k, and 55/37 < 1/H, so the length cap
S <= k/H holds for every k with a closed-form margin.

Two independent evaluations of W are printed for each n:

  * `famlib.Wsum`, this repository's own float evaluator, used unchanged;
  * an mpmath evaluation at 60 decimal digits.  Every window sum of this word
    is a positive integer, and at integer j the kernel collapses to
    k(j) = (-1)^(j+1) / (2 pi^2 j^2 - 1), so W is a finite sum of exactly
    representable terms and needs no quadrature.

Run:  .venv/bin/python hunts/family_wall/period37_check.py
"""
import json
import os
import sys

import mpmath as mp

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import famlib  # noqa: E402

mp.mp.dps = 60

H_MP = mp.mpf(3) / 2 - mp.cot(1 / mp.sqrt(2)) / mp.sqrt(2)


def word(k):
    """First k letters of the period-37 word."""
    return [1 + (18 * i) // 37 - (18 * (i - 1)) // 37 for i in range(1, k + 1)]


def w_int(j):
    """w(j) = k(j)^2 at a positive integer j, in 60-digit arithmetic."""
    return 1 / (2 * mp.pi**2 * j**2 - 1) ** 2


def W_exact(g):
    """W(g) at 60 digits, using the integer-window closed form."""
    k = len(g)
    n = k + 1
    cs = [0] * (k + 1)
    for i, gi in enumerate(g):
        cs[i + 1] = cs[i] + gi
    total = mp.mpf(0)
    for s in range(1, n):
        acc = mp.mpf(0)
        for i in range(0, k - s + 1):
            acc += w_int(cs[i + s] - cs[i])
        total += (mp.mpf(2) / (n - s)) * acc
    return total


def check(n):
    k = n - 1
    g = word(k)
    S = sum(g)
    assert S == k + (18 * k) // 37
    cap = k / H_MP
    W_float = famlib.Wsum(g)
    W_mp = W_exact(g)
    return {
        "n": n,
        "k": k,
        "S": S,
        "cap_(n-1)/H": mp.nstr(cap, 16),
        "S_le_cap": bool(S <= cap),
        "cap_margin": mp.nstr(cap - S, 10),
        "W_famlib_float": W_float,
        "W_mpmath_60dp": mp.nstr(W_mp, 20),
        "W_agreement": mp.nstr(abs(W_mp - W_float), 3),
        "H(1+W)_float": famlib.H * (1.0 + W_float),
        "H(1+W)_mpmath": mp.nstr(H_MP * (1 + W_mp), 20),
    }


def twos_fraction_floor(kmax=20000, kmin=11):
    """min over k in [kmin, kmax] of (number of twos in the prefix)/k."""
    best_k, best = None, mp.mpf(2)
    for k in range(kmin, kmax + 1):
        f = mp.mpf((18 * k) // 37) / k
        if f < best:
            best_k, best = k, f
    return best_k, best


def tail_bound():
    """The audit's closed-form tail bound on W for the period-37 word, n >= 12.

        W <= 2 [ (7/12) w(1) + (5/12) w(2) ]  +  2 w(1) (pi^4/90 - 1).

    Scale 1: coefficient 2/(n-1) times a sum over n-1 gaps, each 1 or 2, with at
    most 7/12 of them ones.  Scale s >= 2: coefficient 2/(n-s) times n-s windows,
    each an integer of size at least s, and w is decreasing at the integers, so
    the whole scale contributes at most 2 w(s); and w(s) <= w(1)/s^4 because
    2 pi^2 s^2 - 1 >= s^2 (2 pi^2 - 1) for s >= 1.  Summing s >= 2 gives
    2 w(1) (zeta(4) - 1) = 2 w(1) (pi^4/90 - 1).
    """
    w1, w2 = w_int(1), w_int(2)
    W = 2 * (mp.mpf(7) / 12 * w1 + mp.mpf(5) / 12 * w2) + 2 * w1 * (mp.pi**4 / 90 - 1)
    return W, H_MP * (1 + W)


def main():
    ns = [8, 38, 56, 100, 401]
    rows = [check(n) for n in ns]
    for r in rows:
        print(json.dumps(r, indent=2, default=str))

    # worst H(1+W) over the whole tiled range, float evaluator only
    worst_n, worst = None, -1.0
    for n in range(8, 402):
        g = word(n - 1)
        assert sum(g) <= (n - 1) / famlib.H
        v = famlib.H * (1.0 + famlib.Wsum(g))
        if v > worst:
            worst_n, worst = n, v
    print(f"\nworst H(1+W) over 8 <= n <= 401 (famlib float): {worst!r} at n = {worst_n}")

    kmin, frac = twos_fraction_floor()
    print(f"\nmin twos-fraction over 11 <= k <= 20000: {mp.nstr(frac, 12)} at k = {kmin}"
          f"   (>= 5/12 = {mp.nstr(mp.mpf(5)/12, 12)}: {frac >= mp.mpf(5)/12})")

    Wt, Bt = tail_bound()
    print(f"closed-form tail bound, n >= 12:  W <= {mp.nstr(Wt, 20)}")
    print(f"                              H(1+W) <= {mp.nstr(Bt, 21)}")
    print("audit's stated tail figure:                  0.675142509660253902")
    print("PR 2.4 figure:                               0.6751676068")

    out = os.path.join(os.path.dirname(os.path.abspath(__file__)), "artifacts", "period37-check.json")
    with open(out, "w") as fh:
        json.dump(
            {
                "rows": rows,
                "worst_over_8_401": {"n": worst_n, "H(1+W)": worst},
                "min_twos_fraction_11_20000": {"k": kmin, "fraction": mp.nstr(frac, 20)},
                "tail_bound_n_ge_12": {"W": mp.nstr(Wt, 20), "H(1+W)": mp.nstr(Bt, 21)},
            },
            fh,
            indent=2,
            default=str,
        )
    print("\nwrote hunts/family_wall/artifacts/period37-check.json")


if __name__ == "__main__":
    main()
