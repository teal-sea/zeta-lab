"""Finite checks for ENDPOINT_SHARP.md sections 2 and 4.

(1) Mertens against the elementary bound ENDPOINT_BOUND.md section 2 uses.
    H_Z = sum_{p<Z} 1/p is loglog Z + M + O(1/log Z), not O(log Z). At
    Z = exp(l^kappa) that is kappa*log l + M, not l^kappa.

(2) The retuned Bonferroni cutoff. For Z = exp(l^kappa), find the least even
    m with N*(e*H_Z/m)^m <= N*exp(-c*l^kappa) (decay rate c), and report
    A = log D_0 / log N = m*l^kappa/l. Asymptotically A -> 0 for kappa <= 1/2.
    Also reports the crossover l where the least viable m first gives A < 1/2.

(3) Complete-period cancellation for the nondividing-conductor case: for a
    primitive real character chi mod q and g = gcd(q,r) < q, the coset sum
    sum over c mod q, (c,q)=1, c = a mod g, of chi(c) vanishes.
"""
from __future__ import annotations

import json
import math
from pathlib import Path

HERE = Path(__file__).resolve().parent
MEISSEL_MERTENS = 0.26149721284764278375


def primes_below(z):
    if z < 3:
        return []
    n = int(z)
    sieve = bytearray([1]) * n
    sieve[0:2] = b"\x00\x00"
    for p in range(2, int(n ** 0.5) + 1):
        if sieve[p]:
            sieve[p * p::p] = bytearray(len(sieve[p * p::p]))
    return [i for i in range(2, n) if sieve[i]]


def H_of_Z_exact(z):
    return sum(1.0 / p for p in primes_below(z))


def H_of_Z_mertens(logz):
    return math.log(logz) + MEISSEL_MERTENS


def bonferroni_log_error(H, m):
    """log of H^(m+1)/(m+1)! , exactly via lgamma."""
    return (m + 1) * math.log(H) - math.lgamma(m + 2)


def least_m(H, target):
    """least even m with H^(m+1)/(m+1)! <= exp(-target), by bisection.

    log(H^(m+1)/(m+1)!) is eventually strictly decreasing in m (its increment
    is log H - log(m+2) < 0 once m+2 > H), so bisection above that point is
    valid; the search starts there.
    """
    lo = max(2, 2 * math.ceil(H))
    if bonferroni_log_error(H, lo) <= -target:
        m = lo
        while m > 2 and bonferroni_log_error(H, m - 2) <= -target:
            m -= 2
        return m
    hi = lo
    while bonferroni_log_error(H, hi) > -target:
        hi *= 2
        if hi > 10 ** 13:
            return None
    while hi - lo > 2:
        mid = 2 * (((lo + hi) // 2) // 2)
        if bonferroni_log_error(H, mid) <= -target:
            hi = mid
        else:
            lo = mid
    return hi


def jacobi(a, n):
    a %= n
    result = 1
    while a:
        while a % 2 == 0:
            a //= 2
            if n % 8 in (3, 5):
                result = -result
        a, n = n, a
        if a % 4 == 3 and n % 4 == 3:
            result = -result
        a %= n
    return result if n == 1 else 0


def main():
    out = {}

    # (1) Mertens vs the elementary bound, at Z = exp(sqrt(l))
    rows = []
    for z_exp in (5.0, 7.0, 9.0, 11.0, 13.0):
        Z = math.exp(z_exp)
        if Z < 2e6:
            exact = H_of_Z_exact(Z)
        else:
            exact = None
        rows.append({"log_Z": z_exp, "Z": Z,
                     "H_Z_exact": exact,
                     "H_Z_mertens": H_of_Z_mertens(z_exp),
                     "elementary_bound_1_plus_logZ": 1 + z_exp})
    out["mertens"] = rows
    print("=== (1) H_Z: Mertens vs the elementary bound 1 + log Z ===")
    for r in rows:
        e = f"{r['H_Z_exact']:.4f}" if r["H_Z_exact"] else "  (too big)"
        print(f"  log Z={r['log_Z']:5.1f}  H_Z exact={e}  Mertens={r['H_Z_mertens']:.4f}"
              f"  1+log Z={r['elementary_bound_1_plus_logZ']:5.1f}"
              f"  bound/truth={r['elementary_bound_1_plus_logZ']/r['H_Z_mertens']:.1f}x")

    # (2) retuned cutoff at kappa = 1/2, decay rate c = 1
    print()
    print("=== (2) retuned Bonferroni cutoff at Z = exp(sqrt(log N)), decay exp(-sqrt(log N)) ===")
    print("   old fixed cutoff m = 2*ceil(sqrt l);  A = log D_0 / log N")
    rows = []
    for l in (100, 230.26, 400, 1000, 10 ** 4, 10 ** 6, 10 ** 10, 10 ** 20):
        logZ = math.sqrt(l)
        H = H_of_Z_mertens(logZ)
        m_fixed = 2 * math.ceil(math.sqrt(l))
        A_fixed = m_fixed * logZ / l
        m_min = least_m(H, logZ)          # decay rate c = 1
        A_min = m_min * logZ / l if m_min else None
        rows.append({"log_N": l, "log_Z": logZ, "H_Z": H, "e_H_Z": math.e * H,
                     "m_fixed": m_fixed, "A_fixed": A_fixed,
                     "m_retuned": m_min, "A_retuned": A_min,
                     "retuned_below_sqrt_N": bool(A_min is not None and A_min < 0.5)})
        print(f"  log N={l:<10.0f} log Z={logZ:8.2f} H_Z={H:6.3f} eH_Z={math.e*H:6.2f} | "
              f"fixed m={m_fixed:<6d} A={A_fixed:8.3f} | retuned m={m_min:<5d} A={A_min:7.4f} "
              f"{'D_0 < N^(1/2)' if A_min < 0.5 else 'D_0 >= N^(1/2)'}")
    out["retuned_cutoff"] = rows

    # crossover
    lo, hi = 100.0, 2.0e6
    for _ in range(200):
        mid = (lo + hi) / 2
        logZ = math.sqrt(mid)
        m = least_m(H_of_Z_mertens(logZ), logZ)
        if m * logZ / mid < 0.5:
            hi = mid
        else:
            lo = mid
    out["crossover_log_N_for_A_below_half"] = hi
    print(f"  crossover: A < 1/2 from log N ~ {hi:.0f}, i.e. N ~ e^{hi:.0f} ~ 10^{hi/math.log(10):.0f}")

    # (3) coset character sums
    print()
    print("=== (3) complete-period cancellation, primitive real chi mod q, g = gcd(q,r) < q ===")
    rows = []
    for q in (3, 5, 7, 11, 13, 15, 21, 33, 105):
        if q % 2 == 0:
            continue
        chi = lambda c, q=q: jacobi(c, q)
        # primitive iff q squarefree (for the Jacobi symbol mod q)
        sq = all((q // p) % p for p in range(2, q + 1) if q % p == 0 and
                 all(p % r for r in range(2, int(p ** 0.5) + 1)))
        if not sq:
            continue
        full = sum(chi(c) for c in range(q) if math.gcd(c, q) == 1)
        worst = 0.0
        checked = 0
        for g in [d for d in range(1, q) if q % d == 0]:
            for a in range(g):
                if math.gcd(a, g) != 1:
                    continue
                s = sum(chi(c) for c in range(q)
                        if math.gcd(c, q) == 1 and c % g == a % g)
                worst = max(worst, abs(s))
                checked += 1
        rows.append({"q": q, "squarefree": sq, "full_period_sum": full,
                     "proper_divisors_checked": checked, "max_abs_coset_sum": worst,
                     "all_vanish": worst == 0})
        print(f"  q={q:4d}  full period sum={full:3d}  cosets checked={checked:4d}  "
              f"max |coset sum|={worst:.0f}  {'all vanish' if worst == 0 else 'NONZERO'}")
    # even conductors 4 and 8
    for q, tab in ((4, (0, 1, 0, -1)), (8, (0, 1, 0, -1, 0, -1, 0, 1))):
        chi = lambda c, tab=tab, q=q: tab[c % q]
        worst = 0.0
        checked = 0
        for g in [d for d in range(1, q) if q % d == 0]:
            for a in range(g):
                if math.gcd(a, g) != 1:
                    continue
                s = sum(chi(c) for c in range(q) if math.gcd(c, q) == 1 and c % g == a % g)
                worst = max(worst, abs(s))
                checked += 1
        rows.append({"q": q, "squarefree": False, "full_period_sum": sum(tab),
                     "proper_divisors_checked": checked, "max_abs_coset_sum": worst,
                     "all_vanish": worst == 0})
        print(f"  q={q:4d}  (2-part)         cosets checked={checked:4d}  "
              f"max |coset sum|={worst:.0f}  {'all vanish' if worst == 0 else 'NONZERO'}")
    out["coset_sums"] = rows

    (HERE / "results_endpoint_sharp_mertens_probe.json").write_text(json.dumps(out, indent=2) + "\n")


if __name__ == "__main__":
    main()
