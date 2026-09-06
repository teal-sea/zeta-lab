#!/usr/bin/env python3
"""Independent exact recheck of the combined-weight baseline in certificate_route_test.

Review code, not the package. It imports nothing from the package (no refine.py, no
numpy), rebuilds the construction with its own arithmetic (integer divisor tables,
Fractions, mpmath interval logarithms) and compares against the recorded
aggregate_results.json. It reads the package files read-only and writes only
baseline_check.json beside itself.

Everything asserted here is a finite exact check or an interval enclosure. The
all-cutoff conclusions rest on the written arguments in BASELINE_REVIEW.md; the checks
here establish their finite hypotheses and reproduce the recorded numbers.

    OPENBLAS_NUM_THREADS=1 ../../../../../../.venv/bin/python baseline_check.py
"""
from __future__ import annotations

import json
import math
import random
import sys
import time
from fractions import Fraction as F
from pathlib import Path

import mpmath as mp
from mpmath import iv

HERE = Path(__file__).resolve().parent
PKG = HERE.parent
M, R, MASK, PRIMES = 15, 100_000, (2, 3, 5, 7), (17, 19, 23, 29, 31)
mp.mp.dps = 60
iv.dps = 60

REPORT: dict = {"scope": "finite exact checks and interval enclosures of the recorded baseline; "
                         "no asymptotic, novelty or RH claim", "checks": {}}


def note(key, **fields):
    REPORT["checks"][key] = fields
    flag = "ok" if fields.get("ok", True) else "FAIL"
    print(f"[{flag}] {key}: " + ", ".join(f"{k}={v}" for k, v in fields.items() if k != "ok"))


# ---------------------------------------------------------------- basic algebra

def coeffs(d):
    return {int(j): F(a) for j, a in d.items()}


def balanced(c):
    return sum((a / j for j, a in c.items()), F(0)) == 0


def mass(c):
    return sum((abs(a) for a in c.values()), F(0))


def common_den(c):
    return math.lcm(*(a.denominator for a in c.values()))


def add(c, other, factor=F(1)):
    out = dict(c)
    for j, a in other.items():
        out[j] = out.get(j, F(0)) + factor * a
    return {j: a for j, a in out.items() if a}


def carry_coeff(n):
    return {n: F(1), n + 1: F(-1), n * (n + 1): F(-1)}


def carry(n, t):
    return t // n - t // (n + 1) - t // (n * (n + 1))


def mobius_divisors(primes):
    out = {1: 1}
    for p in primes:
        out.update({d * p: -mu for d, mu in list(out.items())})
    return out


def stencil_coeff(p):
    c = {}
    for d, mu in mobius_divisors(MASK).items():
        for j, a in carry_coeff(p).items():
            c[d * j] = c.get(d * j, F(0)) + mu * a
    return {j: a for j, a in c.items() if a}


def floor_sum_table(c, size, den):
    """g(t) = sum_j a_j floor(t/j) for 0 <= t < size, scaled by den.

    Uses floor(t/j) = #{m <= t : j | m}: add a_j at every multiple of j, then prefix-sum.
    This is a different evaluation route from the package's numpy floor arrays.
    """
    d = [0] * size
    for j, a in c.items():
        aj = a * den
        assert aj.denominator == 1
        aj = int(aj)
        if aj == 0 or j >= size:
            continue
        for m in range(j, size, j):
            d[m] += aj
    out = [0] * size
    s = 0
    for t in range(size):
        s += d[t]
        out[t] = s
    return out


def lifted_increments(c, size, den):
    """Divisor increments of W(t) = sum_k g(t/M^k) on [0, size), scaled by den."""
    d = [0] * size
    for j, a in c.items():
        aj = int(a * den)
        if aj == 0:
            continue
        q = j
        while q < size:
            for m in range(q, size, q):
                d[m] += aj
            q *= M
    return d


def prefix(d):
    out = [0] * len(d)
    s = 0
    for t, x in enumerate(d):
        s += x
        out[t] = s
    return out


# ------------------------------------------------------------- interval logs

def q_iv(a: F):
    return iv.mpf(a.numerator) / iv.mpf(a.denominator)


def kappa_iv(c):
    s = iv.mpf(0)
    for j, a in c.items():
        s += q_iv(a) * iv.log(iv.mpf(j)) / iv.mpf(j)
    return -s


def kappa_mp(c):
    return -mp.fsum(mp.mpf(a.numerator) / a.denominator * mp.log(j) / j for j, a in c.items())


def C_iv(c, H, star):
    """C = (kappa(D) + H * kappa(g_*) / (R (1-1/M))) / (1-1/M)."""
    q = q_iv(F(14, 15))
    return (kappa_iv(c) + iv.mpf(H) * kappa_iv(star) / (iv.mpf(R) * q)) / q


def C_mp(c, H, star):
    q = mp.mpf(14) / 15
    return (kappa_mp(c) + H * kappa_mp(star) / (R * q)) / q


def lo(x):
    """Lower endpoint of an mpmath interval as a plain mpf (iv's .a is itself an interval)."""
    return mp.make_mpf(x._mpi_[0])


def hi(x):
    return mp.make_mpf(x._mpi_[1])


def ivstr(x):
    return {"lower": mp.nstr(lo(x), 40), "upper": mp.nstr(hi(x), 40)}


# --------------------------------------------------------- certificate pieces

def lifted_coeff(c, H, star, N):
    out = {}
    s = 1
    while s <= N:
        for j, a in c.items():
            if s * j <= N:
                out[s * j] = out.get(s * j, F(0)) + a
        s *= M
    s, m = R, 0
    while s <= N:
        for j, a in star.items():
            if s * j <= N:
                out[s * j] = out.get(s * j, F(0)) + H * (m + 1) * a
        s *= M
        m += 1
    return {q: a for q, a in out.items() if a}


def W_final(c, H, star, t):
    """Exact lifted weight of the final seed at integer t >= 0."""
    return sum((a * (t // q) for q, a in lifted_coeff(c, H, star, t).items()), F(0))


def logfact(n):
    return mp.loggamma(n + 1) if n > 1 else mp.mpf(0)


def B_of(c, H, star, N):
    lc = lifted_coeff(c, H, star, N)
    return mp.fsum(mp.mpf(a.numerator) / a.denominator * logfact(N // q) for q, a in lc.items())


def levels(N):
    k = 0
    while N >= M:
        N //= M
        k += 1
    return k


def S1(N):
    K = levels(N)
    return (K + 1) * (1 + mp.log(N)) - mp.log(M) * K * (K + 1) / 2


def S2(N):
    if N < R:
        return mp.mpf(0)
    K = levels(N // R)
    return mp.fsum((m + 1) * (1 + mp.log(mp.mpf(N) / R) - m * mp.log(M)) for m in range(K + 1))


def legendre(n, p):
    s = 0
    while n:
        n //= p
        s += n
    return s


def primes_upto(N):
    flags = bytearray([1]) * (N + 1)
    flags[0:2] = b"\x00\x00"
    for p in range(2, math.isqrt(N) + 1):
        if flags[p]:
            flags[p * p::p] = bytearray(len(range(p * p, N + 1, p)))
    return [i for i in range(N + 1) if flags[i]]


_LOGP: dict = {}


def psi(N, primes):
    """Chebyshev psi(N) = sum over prime powers p^k <= N of log p, at 60 digits."""
    total = mp.mpf(0)
    for p in primes:
        if p > N:
            break
        k, q = 0, p
        while q <= N:
            k += 1
            q *= p
        if p not in _LOGP:
            _LOGP[p] = mp.log(p)
        total += k * _LOGP[p]
    return total


# ----------------------------------------------------------------------- main

def main():
    t0 = time.perf_counter()
    inp = json.loads((PKG / "inputs.json").read_text())
    rec = json.loads((PKG / "aggregate_results.json").read_text())
    orig = json.loads((PKG / "original_results.json").read_text())
    initial = coeffs(inp["starting_coefficients"])
    star = coeffs(inp["repair_coefficients"])
    assert inp["M"] == M and rec["parameters"] == {"M": M, "R": R, "mask": list(MASK), "primes": list(PRIMES)}

    # 1. Input seeds: balanced, nonnegative on a full period, cover [1, M). Exact, pure Python.
    for name, c, L in (("g0_period_30030", initial, inp["starting_L"]), ("gstar_period_2310", star, inp["repair_L"])):
        assert all(L % j == 0 for j in c), name
        den = common_den(c)
        g = floor_sum_table(c, L, den)
        ok = balanced(c) and min(g) >= 0 and min(g[1:M]) >= den and g[0] == 0
        note(name, ok=ok, balanced=balanced(c), min_scaled=min(g), min_cover_scaled=min(g[1:M]),
             den=den, mass=str(mass(c)), period_cells=L)
        assert ok

    # 2. Carry functions take only the values 0 and 1, vanish before n, equal 1 at n.
    bad = 0
    for n in range(2, 121):
        P = n * (n + 1)
        vals = {carry(n, t) for t in range(0, 2 * P)}
        if not vals <= {0, 1} or any(carry(n, t) for t in range(n)) or carry(n, n) != 1:
            bad += 1
    rng = random.Random(20260906)
    for _ in range(2000):
        n = rng.randrange(2, 10**6)
        t = rng.randrange(0, 10**12)
        if carry(n, t) not in (0, 1):
            bad += 1
    note("carry_values_in_0_1", ok=bad == 0, exhaustive_n="2..120 over two periods", random_samples=2000)
    assert bad == 0

    # 3. Perturbations h_p: balanced, zero before p, exact sup over the full period.
    hp = {}
    period_cells = 0
    for p in PRIMES:
        h = stencil_coeff(p)
        period = math.prod(MASK) * p * (p + 1)
        vals = floor_sum_table(h, period, 1)
        H = max(vals)
        hp[p] = (h, H)
        period_cells += period
        ok = balanced(h) and H == 3 and min(h) == p and all(v == 0 for v in vals[:p])
        # kappa(h_p) = (8/35) k_p, with k_p = log(p+1)/p - log(p)/(p+1)
        kp = iv.log(iv.mpf(p + 1)) / iv.mpf(p) - iv.log(iv.mpf(p)) / iv.mpf(p + 1)
        lhs, rhs = kappa_iv(h), q_iv(F(8, 35)) * kp
        overlap = not (hi(lhs) < lo(rhs) or hi(rhs) < lo(lhs))
        note(f"h_{p}", ok=ok and overlap, H_exact=H, min_over_period=min(vals), period=period,
             balanced=balanced(h), kappa_matches_8_35_k_p=overlap, mass=str(mass(h)))
        assert ok and overlap
    assert sum((F(mu, d) for d, mu in mobius_divisors(MASK).items()), F(0)) == F(8, 35)
    note("perturbation_period_cells_total", ok=period_cells == 651000, cells=period_cells)

    # 4. Independent reconstruction of the five greedy stages on the LIFTED prefix.
    c = dict(initial)
    den = 3
    totalH = 0
    prev = C_iv(c, 0, star)
    stage_rows = []
    all_repairs = 0
    for p in PRIMES:
        h, H = hp[p]
        c = add(c, h, F(-1))
        assert common_den(c) in (1, 3)
        d = lifted_increments(c, R, den)
        repairs = []
        W = 0
        for n in range(1, R):
            W += d[n]
            if W < den:
                deficit = den - W
                repairs.append((n, F(deficit, den)))
                W += deficit
                for q0, sign in ((n, 1), (n + 1, -1), (n * (n + 1), -1)):
                    q = q0
                    while q < R:
                        for m in range(q, R, q):
                            if m != n:
                                d[m] += sign * deficit
                        q *= M
        for n, lam in repairs:
            c = add(c, carry_coeff(n), lam)
        totalH += H
        # Fresh rebuild from the combined coefficients, independent of the scan above.
        Wr = prefix(lifted_increments(c, R, den))
        g = floor_sum_table(c, R, den)
        recorded = rec["stages"][PRIMES.index(p)]
        rec_repairs = [(int(n), F(a)) for n, a in recorded["repairs"]]
        Cv = C_iv(c, totalH, star)
        strict = hi(Cv) < lo(prev)
        row = {"p": p, "H": H, "repairs": len(repairs), "repairs_match_recorded": repairs == rec_repairs,
               "lifted_prefix_min_scaled": min(Wr[1:]), "negative_seed_cells": sum(1 for x in g[1:] if x < 0),
               "mass": str(mass(c)), "recorded_mass": recorded["coefficient_mass"],
               "C_interval": ivstr(Cv), "recorded_C": recorded["C"][:32],
               "strict_decrease_by_interval": strict, "balanced": balanced(c)}
        ok = (row["repairs_match_recorded"] and min(Wr[1:]) >= den and strict and balanced(c)
              and mass(c) == F(recorded["coefficient_mass"])
              and lo(Cv) <= mp.mpf(recorded["C"]) <= hi(Cv)
              and row["negative_seed_cells"] == recorded["negative_seed_cells"]
              and len(repairs) == recorded["number_of_repairs"])
        note(f"stage_p{p}", ok=ok, **{k: v for k, v in row.items() if k not in ("p", "C_interval")})
        assert ok
        stage_rows.append(row)
        all_repairs += len(repairs)
        prev = Cv

    final = c
    recorded_final = coeffs(rec["new_coefficients"])
    ok = final == recorded_final and totalH == rec["tail_multiplier"] == 15 and all_repairs == 537
    note("final_seed_matches_recorded", ok=ok, coefficients=len(final), total_repairs=all_repairs,
         tail_multiplier=totalH, mass=str(mass(final)), recorded_mass=rec["new_final_mass"])
    assert ok
    assert mass(final) == F(2641, 3) == F(rec["new_final_mass"])

    # 5. Prefix coverage and negativity, from the RECORDED coefficients (not the reconstruction).
    Wrec = prefix(lifted_increments(recorded_final, R, den))
    grec = floor_sum_table(recorded_final, R, den)
    neg = sum(1 for x in grec[1:] if x < 0)
    note("recorded_final_prefix_coverage", ok=min(Wrec[1:]) >= den and neg == 705,
         lifted_min_scaled=min(Wrec[1:]), cells=R - 1, negative_seed_cells_below_R=neg,
         first_negative_cell=next((t for t in range(1, R) if grec[t] < 0), None))
    assert min(Wrec[1:]) >= den and neg == 705

    # 6. Tail: exact samples of g_final(t) >= 0 and W_final(t) >= 1 for t >= R (diagnostic; the
    #    proof is in the review and needs only items 1, 2, 3).
    rng = random.Random(1729)
    pts = [R, R + 1, R * M, R * M * M, 10**8, 10**12] + [rng.randrange(R, 10**12) for _ in range(60)]
    seed_ok = w_ok = True
    for t in pts:
        seed = sum((a * (t // j) for j, a in final.items()), F(0)) + totalH * sum(
            (a * ((t // R) // (j * M**k)) for k in range(0, 40) for j, a in star.items()), F(0))
        seed_ok &= seed >= 0
        w_ok &= W_final(final, totalH, star, t) >= 1
    note("tail_samples", ok=seed_ok and w_ok, points=len(pts), seed_nonnegative=seed_ok, lifted_at_least_one=w_ok)
    assert seed_ok and w_ok

    # 7. Leading constant: interval enclosure by mpmath.iv logs, versus the recorded decimal.
    Cfin = C_iv(final, totalH, star)
    Crec = mp.mpf(rec["new_final_C"])
    kD = kappa_iv(final)
    width = hi(Cfin) - lo(Cfin)
    ok = lo(Cfin) <= Crec <= hi(Cfin) and width < mp.mpf(10) ** -45 and lo(kD) > 0
    note("final_C_enclosure", ok=ok, **ivstr(Cfin), recorded=mp.nstr(Crec, 40), width=mp.nstr(width, 5),
         kappa_D_lower=mp.nstr(lo(kD), 20), sixty_digit=mp.nstr(C_mp(final, totalH, star), 50))
    assert ok
    REPORT["reproduced"] = {"C": mp.nstr(C_mp(final, totalH, star), 50), "C_interval": ivstr(Cfin),
                            "finite_coefficient_mass": str(mass(final)), "tail_coefficient": totalH,
                            "repairs": all_repairs, "negative_seed_cells_below_R": neg}

    # 8. Factorial exponent identity at every prime, and B_N >= psi(N) directly.
    idents = 0
    for N in (2000, 10000):
        lc = lifted_coeff(final, totalH, star, N)
        for p in primes_upto(N):
            left = sum((a * legendre(N // q, p) for q, a in lc.items()), F(0))
            right, power = F(0), p
            while power <= N:
                w = W_final(final, totalH, star, N // power)
                assert w >= 1
                right += w
                power *= p
            assert left == right, (N, p)
            idents += 1
    note("prime_exponent_identities", ok=True, count=idents, cutoffs="2000 and 10000, every prime")

    primes = primes_upto(10**6)
    rng = random.Random(2026)
    Ns = [10**4, 10**6] + sorted(rng.randrange(1000, 10**6) for _ in range(12))
    direct = []
    for N in Ns:
        B = B_of(final, totalH, star, N)
        ps = psi(N, primes)
        direct.append({"N": N, "B_minus_psi": mp.nstr(B - ps, 12), "ratio_B_over_N": mp.nstr(B / N, 12)})
        assert B >= ps, N
    note("B_N_majorizes_psi_N_directly", ok=True, cutoffs=len(Ns), sample=direct[:2])
    REPORT["direct_majorant_samples"] = direct

    # 9. Recorded comparison rows: recompute new_B and new_U, check B <= U and agreement.
    rows = []
    for row in rec["comparisons"]:
        N = row["N"]
        B = B_of(final, totalH, star, N)
        U = C_mp(final, totalH, star) * N + mp.mpf(mass(final).numerator) / mass(final).denominator * S1(N) \
            + totalH * mp.mpf(mass(star).numerator) / mass(star).denominator * S2(N)
        agreeB = abs(B - mp.mpf(row["new_B"])) < mp.mpf(10) ** -40 * N
        agreeU = abs(U - mp.mpf(row["new_U"])) < mp.mpf(10) ** -40 * N
        rows.append({"N": N, "B": mp.nstr(B, 25), "U": mp.nstr(U, 25), "B_le_U": B <= U,
                     "agrees_with_recorded": agreeB and agreeU})
        assert B <= U and agreeB and agreeU, N
    note("recorded_comparisons_reproduced", ok=True, rows=len(rows))
    REPORT["comparisons"] = rows

    # 10. Early-excess view below 37, for the combined-weight seed and the old five-stage seed.
    old = coeffs(orig["final_direct_coefficients"])
    views = {}
    for name, cc in (("combined_weight_final", final), ("old_five_stage_final", old)):
        Wt = {t: W_final(cc, totalH, star, t) for t in range(1, 37)}
        excess = sum(((Wt[t] - 1) / (t * (t + 1)) for t in range(1, 37)), F(0))
        views[name] = {"cells_above_one": {t: str(Wt[t]) for t in range(1, 37) if Wt[t] > 1},
                       "weighted_excess": str(excess), "equals_23977_over_1441440": excess == F(23977, 1441440)}
    note("early_excess_below_37", ok=True, **{k: v["weighted_excess"] for k, v in views.items()})
    REPORT["early_excess_views"] = views

    # 11. Fixed-recipe ceiling arithmetic (its hypotheses are the restriction; see the review).
    assert F(12, 49) * F(11, 124) == F(33, 1519)
    assert F(21, 20) - F(33, 1519) == F(31239, 30380)
    assert F(8, 35) * F(15, 14) == F(12, 49)
    log31 = iv.log(iv.mpf(31))
    assert hi(log31) < mp.mpf(7) / 2
    assert hi(iv.mpf(2) + log31) / 62 < mp.mpf(11) / 124
    Cold = C_iv(old, 15, star)
    assert lo(Cold) > mp.mpf(21) / 20 and lo(Cfin) > mp.mpf(131) / 125
    kn_ok = True
    for n in range(33, 3001):
        kn = iv.log(iv.mpf(n + 1)) / iv.mpf(n) - iv.log(iv.mpf(n)) / iv.mpf(n + 1)
        fn = (iv.mpf(1) + iv.log(iv.mpf(n))) / iv.mpf(n * n)
        kn_ok &= hi(kn) <= lo(fn)
    note("fixed_recipe_arithmetic", ok=kn_ok, gross_cap="33/1519", old_floor="31239/30380",
         new_floor_gt_1_026=(F(131, 125) - F(33, 1519)) > F(1026, 1000),
         old_C_lower=mp.nstr(lo(Cold), 20), k_n_le_f_n_checked="n=33..3000")
    assert kn_ok

    REPORT["seconds"] = time.perf_counter() - t0
    REPORT["all_ok"] = all(v.get("ok", True) for v in REPORT["checks"].values())
    (HERE / "baseline_check.json").write_text(json.dumps(REPORT, indent=2, default=str) + "\n")
    print(json.dumps({"all_ok": REPORT["all_ok"], "reproduced": REPORT["reproduced"], "seconds": REPORT["seconds"]},
                     indent=2, default=str))
    return 0 if REPORT["all_ok"] else 1


if __name__ == "__main__":
    sys.exit(main())
