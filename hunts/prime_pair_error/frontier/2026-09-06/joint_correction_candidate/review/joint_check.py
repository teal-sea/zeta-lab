#!/usr/bin/env python3
"""Independent exact recheck of the first coordinated signed-correction candidate.

Review code, not the candidate. It imports nothing from the candidate package and nothing
from the baseline package (no joint_correction.py, no refine.py, no numpy), rebuilds the
candidate seed from its recorded amplitudes with its own arithmetic (integer divisor
tables, Fractions, an exact rational logarithm series, and mpmath interval logarithms as a
second route), and compares against the recorded joint_results.json. It reads the
candidate and baseline files read-only and writes only joint_check.json beside itself.

Everything asserted here is a finite exact check or an enclosure. The all-cutoff
conclusions rest on the written arguments in JOINT_REVIEW.md; the checks here establish
their finite hypotheses and reproduce the recorded numbers.

    OPENBLAS_NUM_THREADS=1 ../../../../../../.venv/bin/python joint_check.py
"""
from __future__ import annotations

import json
import math
import random
import sys
import time
from fractions import Fraction as F
from functools import lru_cache
from pathlib import Path

import mpmath as mp
from mpmath import iv

HERE = Path(__file__).resolve().parent
PKG = HERE.parent
BASE = PKG.parent / "certificate_route_test"
M, R, MASK = 15, 100_000, (2, 3, 5, 7)
CANDIDATES = list(range(13, 37))
mp.mp.dps = 80
iv.dps = 80

REPORT: dict = {"scope": "finite exact checks and enclosures of the recorded joint candidate against the "
                         "reviewed baseline; no optimality, asymptotic, novelty or RH claim", "checks": {}}


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


def stencil_coeff(q):
    c = {}
    for d, mu in mobius_divisors(MASK).items():
        for j, a in carry_coeff(q).items():
            c[d * j] = c.get(d * j, F(0)) + mu * a
    return {j: a for j, a in c.items() if a}


def floor_sum_table(c, size, den):
    """g(t) = sum_j a_j floor(t/j) on [0, size), scaled by den, via divisor increments."""
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


def lifted_table(c, size, den):
    """W(t) = sum_k g(t/M^k) on [0, size), scaled by den, from the lifted indices j M^k."""
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
    out = [0] * size
    s = 0
    for t in range(size):
        s += d[t]
        out[t] = s
    return out


# ------------------------------------------------------ exact rational logs

@lru_cache(None)
def _atanh_series(u: F, terms: int = 40):
    """[lower, upper] for 2 atanh(u) = log((1+u)/(1-u)), 0 <= u <= 1/3, exact Fractions."""
    assert F(0) <= u <= F(1, 3)
    s = F(0)
    v = u
    for k in range(terms):
        s += 2 * v / (2 * k + 1)
        v *= u * u
    tail = 2 * v / ((2 * terms + 1) * (1 - u * u))  # geometric bound on the positive remainder
    return s, s + tail


@lru_cache(None)
def log_bounds_exact(n: int):
    """Exact rational [lower, upper] enclosing log n, from n = 2^e r with 1 <= r < 2."""
    assert n >= 1
    e = n.bit_length() - 1
    r = F(n, 1 << e)
    lo, hi = _atanh_series((r - 1) / (r + 1))
    l2, h2 = _atanh_series(F(1, 3))  # log 2 = 2 atanh(1/3)
    return lo + e * l2, hi + e * h2


def kappa_bounds_exact(c):
    """Exact rational [lower, upper] for kappa(c) = -sum a_j log j / j."""
    lo = hi = F(0)
    for j, a in c.items():
        lj, hj = log_bounds_exact(j)
        w = -a / j
        lo += w * (lj if w >= 0 else hj)
        hi += w * (hj if w >= 0 else lj)
    return lo, hi


def C_bounds_exact(c, H: F, star):
    """C = (kappa(D) + H kappa(g_*) / (R (1-1/M))) / (1-1/M), exact rational endpoints."""
    q = F(14, 15)
    kd = kappa_bounds_exact(c)
    ks = kappa_bounds_exact(star)
    return tuple((kd[i] + H * ks[i] / (R * q)) / q for i in (0, 1))


def q_iv(a: F):
    return iv.mpf(a.numerator) / iv.mpf(a.denominator)


def kappa_iv(c):
    s = iv.mpf(0)
    for j, a in c.items():
        s += q_iv(a) * iv.log(iv.mpf(j)) / iv.mpf(j)
    return -s


def C_iv(c, H: F, star):
    q = q_iv(F(14, 15))
    return (kappa_iv(c) + q_iv(H) * kappa_iv(star) / (iv.mpf(R) * q)) / q


def kappa_mp(c):
    return -mp.fsum(mp.mpf(a.numerator) / a.denominator * mp.log(j) / j for j, a in c.items())


def C_mp(c, H: F, star):
    q = mp.mpf(14) / 15
    return (kappa_mp(c) + mp.mpf(H.numerator) / H.denominator * kappa_mp(star) / (R * q)) / q


def lo(x):
    return mp.make_mpf(x._mpi_[0])


def hi(x):
    return mp.make_mpf(x._mpi_[1])


def mpf_to_frac(x) -> F:
    """Exact rational value of an mpf (sign, mantissa, exponent), for exact comparisons."""
    sign, man, exp, _ = x._mpf_
    val = F(man) * (F(2) ** exp)
    return -val if sign else val


def fstr(x: F, digits=40):
    return mp.nstr(mp.mpf(x.numerator) / x.denominator, digits)


# --------------------------------------------------------- certificate pieces

def lifted_coeff(c, H: F, star, N):
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


def W_at(c, H: F, star, t):
    return sum((a * (t // q) for q, a in lifted_coeff(c, H, star, t).items()), F(0))


def seed_at(c, H: F, star, t):
    """The seed itself at integer t: D(t) + H W_*(t/R), exact."""
    val = sum((a * (t // j) for j, a in c.items()), F(0))
    x = t // R
    while x >= 1:
        val += H * sum((a * (x // j) for j, a in star.items()), F(0))
        x //= M
    return val


def logfact(n):
    return mp.loggamma(n + 1) if n > 1 else mp.mpf(0)


def B_of(c, H: F, star, N):
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


def U_of(c, H: F, star, N, C):
    A = mass(c)
    return C * N + mp.mpf(A.numerator) / A.denominator * S1(N) \
        + mp.mpf(H.numerator) / H.denominator * mp.mpf(mass(star).numerator) / mass(star).denominator * S2(N)


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
    inp = json.loads((BASE / "inputs.json").read_text())
    agg = json.loads((BASE / "aggregate_results.json").read_text())
    cand = json.loads((PKG / "joint_results.json").read_text())
    g0 = coeffs(inp["starting_coefficients"])
    star = coeffs(inp["repair_coefficients"])
    baseline = coeffs(agg["new_coefficients"])
    H_old = F(agg["tail_multiplier"])
    assert inp["M"] == M and agg["parameters"]["R"] == R

    # 0. The exact rational log series is sound: its bounds contain mpmath's interval log.
    bad = [n for n in list(range(1, 3001)) + [30030, 2310, 100000, 10**6]
           if not (log_bounds_exact(n)[0] <= mpf_to_frac(lo(iv.log(iv.mpf(n))))
                   and mpf_to_frac(hi(iv.log(iv.mpf(n)))) <= log_bounds_exact(n)[1])]
    note("exact_log_series_contains_interval_log", ok=not bad, checked="n=1..3000 and four larger", violations=bad)
    assert not bad

    # 1. Input seeds and the baseline, as reviewed: exact full-period facts they must keep.
    for name, c, L in (("g0_period_30030", g0, inp["starting_L"]), ("gstar_period_2310", star, inp["repair_L"])):
        den = common_den(c)
        g = floor_sum_table(c, L, den)
        ok = balanced(c) and all(L % j == 0 for j in c) and min(g) >= 0 and min(g[1:M]) >= den and g[0] == 0
        note(name, ok=ok, min_scaled=min(g), min_cover_scaled=min(g[1:M]), den=den, mass=str(mass(c)))
        assert ok

    # 2. The selected amplitudes: on the 1/108 grid, nonnegative, starts inside 13..36,
    #    repairs on baseline cells only, and the recorded sums.
    y = {int(q): F(a) for q, a in cand["selected_masked_corrections"].items()}
    lam = {int(n): F(a) for n, a in cand["repair_coefficients"].items()}
    base_cells = set()
    stage_repairs = 0
    for st in agg["stages"]:
        for n, _ in st["repairs"]:
            base_cells.add(int(n))
            stage_repairs += 1
    H_new = 3 * sum(y.values(), F(0))
    ok = (all(a > 0 and a.denominator in (1, 2, 3, 4, 6, 9, 12, 18, 27, 36, 54, 108) and 108 % a.denominator == 0
              for a in list(y.values()) + list(lam.values()))
          and set(y) <= set(CANDIDATES) and set(lam) <= base_cells
          and H_new == F(701, 36) == F(cand["new_tail_H"])
          and sum(y.values(), F(0)) == F(701, 108)
          and len(lam) == 172 == cand["selected_repair_count"]
          and sum(lam.values(), F(0)) == F(19471, 108) == F(cand["repair_coefficient_sum"])
          and len(base_cells) == 411 and stage_repairs == 537
          and sorted(y) == [17, 18, 19, 23, 24, 25, 29, 31, 32])
    note("amplitudes_reconstruct", ok=ok, selected_starts=sorted(y), composite_starts=[q for q in y if any(q % d == 0 for d in range(2, q))],
         sum_y=str(sum(y.values(), F(0))), H=str(H_new), repair_cells=len(lam), baseline_distinct_cells=len(base_cells),
         repair_sum=str(sum(lam.values(), F(0))), max_denominator=max(a.denominator for a in list(y.values()) + list(lam.values())))
    assert ok

    # 3. Rebuild the finite seed D = g0 - sum y_q h_q + sum lambda_n b_n; compare with the record.
    D = dict(g0)
    for q, a in y.items():
        D = add(D, stencil_coeff(q), -a)
    for n, a in lam.items():
        D = add(D, carry_coeff(n), a)
    recorded_D = coeffs(cand["new_coefficients"])
    ok = (D == recorded_D and balanced(D) and mass(D) == F(56345, 108) == F(cand["new_finite_mass"])
          and len(D) == 662 == cand["new_coefficient_count"] and 108 % common_den(D) == 0)
    note("finite_seed_rebuilds_exactly", ok=ok, coefficients=len(D), balanced=balanced(D), mass=str(mass(D)),
         common_denominator=common_den(D), baseline_mass=str(mass(baseline)))
    assert ok

    # 4. Every candidate masked carry q = 13..36 has exact supremum 3 over its complete period,
    #    is balanced, and vanishes before q. Composite q included; nothing here uses primality.
    total_cells = 0
    sups = {}
    for q in CANDIDATES:
        h = stencil_coeff(q)
        period = 210 * q * (q + 1)
        vals = floor_sum_table(h, period, 1)
        total_cells += period
        sups[q] = (max(vals), min(vals))
        assert max(vals) == 3 and balanced(h) and min(h) == q and all(v == 0 for v in vals[:q]), q
        # the carry identity itself for this q: values in {0, 1} over a full period
        assert {carry(q, t) for t in range(2 * q * (q + 1))} <= {0, 1}, q
    note("masked_carry_suprema", ok=total_cells == 3_390_240, period_cells=total_cells,
         sup_all_equal_3=all(s[0] == 3 for s in sups.values()), min_range=[min(s[1] for s in sups.values()), max(s[1] for s in sups.values())])
    assert total_cells == 3_390_240

    # 5. Prefix coverage from the RECORDED coefficients: W >= 1 on every cell of [1, R).
    den = 108
    Wt = lifted_table(recorded_D, R, den)
    seed = floor_sum_table(recorded_D, R, den)
    neg = sum(1 for x in seed[1:] if x < 0)
    minW = min(Wt[1:])
    early = {int(e["t"]): F(e["joint"]) for e in cand["early_weights"]}
    early_ok = all(F(Wt[t], den) == v for t, v in early.items())
    early_base = {t: F(v["baseline"]) for t, v in ((int(e["t"]), e) for e in cand["early_weights"])}
    Wb = lifted_table(baseline, R, 3)
    early_base_ok = all(F(Wb[t], 3) == v for t, v in early_base.items())
    ok = minW >= den and F(minW, den) == F(cand["lifted_prefix_min"]) and neg == 640 == cand["negative_seed_cells_below_R"] and early_ok and early_base_ok
    note("recorded_prefix_coverage", ok=ok, lifted_min=str(F(minW, den)), cells=R - 1, negative_seed_cells=neg,
         first_negative_cell=next((t for t in range(1, R) if seed[t] < 0), None),
         early_weights_match=early_ok, baseline_early_weights_match=early_base_ok,
         cells_at_exactly_one=sum(1 for x in Wt[1:] if x == den))
    assert ok

    # 6. Tail: exact samples of the seed and lifted weight at t >= R (diagnostic; the proof needs 1, 4 and
    #    H = 3 sum y_q only).
    rng = random.Random(1729)
    pts = [R, R + 1, R * M, R * M * M, 10**8, 10**12] + [rng.randrange(R, 10**12) for _ in range(60)]
    seed_ok = all(seed_at(recorded_D, H_new, star, t) >= 0 for t in pts)
    w_ok = all(W_at(recorded_D, H_new, star, t) >= 1 for t in pts)
    note("tail_samples", ok=seed_ok and w_ok, points=len(pts), seed_nonnegative=seed_ok, lifted_at_least_one=w_ok)
    assert seed_ok and w_ok

    # 7. Leading constants: exact rational enclosures (own series) and interval enclosures (mpmath.iv),
    #    strict separation C_new < C_old, and kappa(D) > 0 (needed to drop the geometric tails).
    new_ex = C_bounds_exact(recorded_D, H_new, star)
    old_ex = C_bounds_exact(baseline, H_old, star)
    new_iv = C_iv(recorded_D, H_new, star)
    old_iv = C_iv(baseline, H_old, star)
    Cnew_rec = mp.mpf(cand["new_C"])
    Cold_rec = mp.mpf(agg["new_final_C"])
    kD_ex = kappa_bounds_exact(recorded_D)
    sep_exact = new_ex[1] < old_ex[0]
    sep_iv = hi(new_iv) < lo(old_iv)
    inside = (mp.mpf(new_ex[0].numerator) / new_ex[0].denominator <= Cnew_rec <= mp.mpf(new_ex[1].numerator) / new_ex[1].denominator
              and lo(new_iv) <= Cnew_rec <= hi(new_iv)
              and mp.mpf(old_ex[0].numerator) / old_ex[0].denominator <= Cold_rec <= mp.mpf(old_ex[1].numerator) / old_ex[1].denominator)
    rec_int = cand["new_C_interval"]
    rec_int_ok = F(rec_int["lower"]) <= new_ex[1] and F(rec_int["upper"]) >= new_ex[0]
    ok = sep_exact and sep_iv and inside and kD_ex[0] > 0 and rec_int_ok
    note("leading_constants", ok=ok, C_new_exact_lower=fstr(new_ex[0]), C_new_exact_upper=fstr(new_ex[1]),
         C_old_exact_lower=fstr(old_ex[0]), C_old_exact_upper=fstr(old_ex[1]),
         exact_width_new=fstr(new_ex[1] - new_ex[0], 5), separation_exact=sep_exact, separation_interval=sep_iv,
         decrease_at_least=fstr(old_ex[0] - new_ex[1], 25), recorded_inside=inside, kappa_D_lower=fstr(kD_ex[0], 25),
         recorded_interval_consistent=rec_int_ok, eighty_digit=mp.nstr(C_mp(recorded_D, H_new, star), 60))
    assert ok
    REPORT["reproduced"] = {"C_new": mp.nstr(C_mp(recorded_D, H_new, star), 60),
                            "C_new_enclosure_decimal": [fstr(new_ex[0], 45), fstr(new_ex[1], 45)],
                            "C_new_exact_enclosure_width": fstr(new_ex[1] - new_ex[0], 6),
                            "C_old_enclosure_decimal": [fstr(old_ex[0], 45), fstr(old_ex[1], 45)],
                            "decrease_at_least": fstr(old_ex[0] - new_ex[1], 25),
                            "finite_coefficient_mass": str(mass(recorded_D)), "tail_coefficient": str(H_new),
                            "tail_allowance_coefficient": str(H_new * mass(star)),
                            "repairs": len(lam), "negative_seed_cells_below_R": neg}

    # 8. Factorial identity at every prime up to 2000 and 10000, and B_N >= psi(N) directly.
    idents = 0
    for N in (2000, 10000):
        lc = lifted_coeff(recorded_D, H_new, star, N)
        for p in primes_upto(N):
            left = sum((a * legendre(N // q, p) for q, a in lc.items()), F(0))
            right, power = F(0), p
            while power <= N:
                w = W_at(recorded_D, H_new, star, N // power)
                assert w >= 1
                right += w
                power *= p
            assert left == right, (N, p)
            idents += 1
    note("prime_exponent_identities", ok=True, count=idents)
    primes = primes_upto(10**6)
    rng = random.Random(2026)
    Ns = [10**4, 10**6] + sorted(rng.randrange(1000, 10**6) for _ in range(12))
    direct = []
    for N in Ns:
        B = B_of(recorded_D, H_new, star, N)
        ps = psi(N, primes)
        assert B >= ps, N
        direct.append({"N": N, "B_minus_psi": mp.nstr(B - ps, 12)})
    note("B_N_majorizes_psi_N_directly", ok=True, cutoffs=len(Ns))
    REPORT["direct_majorant_samples"] = direct

    # 9. The four comparison rows, recomputed from lifted coefficient dictionaries.
    Cnew = C_mp(recorded_D, H_new, star)
    Cold = C_mp(baseline, H_old, star)
    rows = []
    for row in cand["comparisons"]:
        N = row["N"]
        nB, oB = B_of(recorded_D, H_new, star, N), B_of(baseline, H_old, star, N)
        nU, oU = U_of(recorded_D, H_new, star, N, Cnew), U_of(baseline, H_old, star, N, Cold)
        tol = mp.mpf(10) ** -40 * N
        agree = all(abs(x - mp.mpf(row[k])) < tol for x, k in ((nB, "new_B"), (oB, "old_B"), (nU, "new_U"), (oU, "old_U")))
        ok = agree and nB <= nU and oB <= oU and nB < oB and nU < oU
        rows.append({"N": N, "new_B": mp.nstr(nB, 25), "old_B": mp.nstr(oB, 25), "new_U": mp.nstr(nU, 25), "old_U": mp.nstr(oU, 25),
                     "B_gain": mp.nstr(oB - nB, 15), "U_gain": mp.nstr(oU - nU, 15), "agrees_with_recorded": agree})
        assert ok, N
    note("comparisons_reproduced", ok=True, rows=len(rows))
    REPORT["comparisons"] = rows

    # 10. Composite starts: the only places primality entered the earlier notes are the omitted-prime
    #     jump identity and the ceiling's enumeration of future primes; neither is an obligation of the
    #     certificate. Record the jump structure at the composite starts for the record.
    comp = {}
    for q in (18, 24, 25, 32):
        h = stencil_coeff(q)
        comp[q] = {"indices": sorted(h), "nonzero_terms": len(h), "mass": str(mass(h)), "sup": sups[q][0]}
    note("composite_starts_use_only_finite_facts", ok=True, starts=list(comp))
    REPORT["composite_starts"] = comp

    REPORT["seconds"] = time.perf_counter() - t0
    REPORT["all_ok"] = all(v.get("ok", True) for v in REPORT["checks"].values())
    (HERE / "joint_check.json").write_text(json.dumps(REPORT, indent=2, default=str) + "\n")
    print(json.dumps({"all_ok": REPORT["all_ok"], "reproduced": REPORT["reproduced"], "seconds": REPORT["seconds"]}, indent=2, default=str))
    return 0 if REPORT["all_ok"] else 1


if __name__ == "__main__":
    sys.exit(main())
