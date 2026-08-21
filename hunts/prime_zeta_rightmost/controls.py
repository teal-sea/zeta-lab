"""WP5 controls for the prime_zeta_rightmost hunt: calibration, lesions, precision response.

Run from the repo root:

    .venv/bin/python hunts/prime_zeta_rightmost/controls.py

The verdict machinery of decide.py is only trustworthy if the same code path
(a) reproduces a known constant when pointed at a solved problem, (b) responds
to its input, and (c) responds to its working precision. Four controls:

1. CALIBRATION (known answer, same code path). The zeta-partial-sums balance:
   leading term a_1 = 1 against the tail sum_{n>=2} n^(-sigma), whose root is
   the root of zeta(sigma) = 2, the OEIS A107311 constant x*. The balance
   function (zeta(sigma) - 1) - 1 is run through decide.bisect_decreasing,
   the very function object decide.main() calls for sigma_c (asserted
   identical to instrument.bisect_decreasing), with sigma_c's bracket
   [1.7, 1.9] and target widths. Pass: the OEIS value interval lies inside
   the resulting enclosure on both backends, and the flint leg reproduces
   the entry's digits to the enclosure's width (>= 30 digits). The balance
   function is strictly decreasing exactly: its derivative is
   zeta'(sigma) = -sum_{n>=2} log n * n^(-sigma) < 0 termwise for sigma > 1,
   so no numeric monotonicity guard is needed.

2. LESION 1 (input sensitivity). Drop the p = 3 term from the tail of the
   sigma_c balance: solve sum_{p>=5} p^(-s) = 2^(-s), i.e.
   les1(s) = P(s) - 2^(1-s) - 3^(-s) = 0. The root must move away from
   sigma_c by a decided amount; a solver reading a cache instead of its
   input would return sigma_c again. Monotonicity guard on the bracket:

       les1'(s) = 2 log2 * 2^(-s) + log3 * 3^(-s) - sum_p log p * p^(-s)
               <= 2 log2 * 2^(-s) + log3 * 3^(-s)
                  - sum_{p<=1000} log p * p^(-s),

   since dropping the positive tail of the subtracted sum only raises the
   value; evaluated over 16 subintervals of the bracket, every upper
   endpoint negative decides strict decrease, hence root uniqueness there.

3. LESION 2 (the mis-port made mechanical). The conjecture's error is
   carrying x*, the threshold of the zeta-partial-sum family whose leading
   term is a_1 = 1, over to P(s), whose leading term is 2^(-s). Make that
   error a computation: keep the zeta series but balance the leading term
   2^(-sigma) against the tail AFTER it, sum_{n>=3} n^(-sigma). That is
   les2(s) = (zeta(s) - 1 - 2^(-s)) - 2^(-s) = zeta(s) - 1 - 2^(1-s) = 0.
   Its root reproduces neither x* nor sigma_c (decided disjointness), which
   is the point: the balance template and the series fed to it both matter,
   and the wrong pairing lands nowhere. (The other mechanical pairing,
   leading 2^(-sigma) against the full tail sum_{n>=2}, has no root at all:
   zeta(s) - 1 - 2^(-s) = 3^(-s) + 4^(-s) + ... > 0 for every s.)
   Monotonicity guard, same shape as lesion 1:

       les2'(s) = zeta'(s) + 2 log2 * 2^(-s)
               <= 2 log2 * 2^(-s) - sum_{2<=n<=200} log n * n^(-s).

4. PRECISION RESPONSE. The sigma_c solve (identical balance function and
   bracket as decide.py's flint leg) at three working precisions with an
   unreachably small target width: the achieved enclosure width must shrink
   strictly as precision grows, because the honest stopping rule is a sign
   stall, not a fixed iteration count.

5. DECIDE.PY REPRODUCIBILITY. decide.py is rerun in a subprocess and the
   fresh decided.json is compared to the recorded one line for line with
   the time_s lines masked (wall-clock times are the one thing a rerun may
   change); the recorded bytes are then restored, so this control never
   edits the record it checks. decide.py itself is untouched by WP5: the
   calibration imports its solver rather than refactoring it.

Vocabulary contract as in MISSION.md: decided means an interval or ball
enclosure whose exact rational endpoints settle a sign, stated with backend
and precision; measured means one float route. All bracket bookkeeping is
exact Fractions; backend arithmetic only answers sign questions.

Results are written to controls_results.json next to this file.
"""

from __future__ import annotations

import json
import os
import subprocess
import sys
from fractions import Fraction
from math import floor

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

import flint
import mpmath

import decide
import instrument
from decide import (
    FLINT_PREC_BITS,
    IV_DPS,
    K_FLINT,
    K_IV,
    N_IV_XSTAR,
    OEIS_DIGITS,
    OEIS_HI,
    OEIS_LO,
    interval_record,
)
from instrument import (
    Timer,
    arb_endpoints,
    arb_from_fraction,
    arb_interval,
    h_arb,
    h_iv,
    iv_endpoints,
    iv_from_fraction,
    mobius_sieve,
    outward_decimal,
    primes_upto,
    zeta_iv,
)

arb = flint.arb
fctx = flint.ctx
iv = mpmath.iv

HERE = os.path.dirname(os.path.abspath(__file__))

# The solver under test: the same function object decide.main() uses for
# sigma_c. The assert pins that identity so a later refactor cannot silently
# hand this control a different solver.
solve = decide.bisect_decreasing
assert solve is instrument.bisect_decreasing

SIGMA_C_BRACKET = (Fraction(17, 10), Fraction(19, 10))
SIGMA_C_TARGET_FLINT = Fraction(1, 10 ** 31)
SIGMA_C_TARGET_IV = Fraction(1, 10 ** 13)

LES1_BRACKET = (Fraction(5, 4), Fraction(8, 5))
LES2_BRACKET = (Fraction(2, 1), Fraction(29, 10))
LES_TARGET_FLINT = Fraction(1, 10 ** 31)
LES1_TARGET_IV = Fraction(1, 10 ** 9)
LES2_TARGET_IV = Fraction(1, 10 ** 10)

PREC_RESPONSE_BITS = (60, 120, 200)
PREC_RESPONSE_TARGET = Fraction(1, 10 ** 60)

GUARD_PIECES = 16
GUARD_PRIME_CUTOFF = 1000
GUARD_N_CUTOFF = 200


def oeis_digits_agreed(lo: Fraction, hi: Fraction) -> int:
    """Largest d such that the first d significant digits of every point of
    [lo, hi] equal the first d digits of the OEIS A107311 expansion. Exact
    integer arithmetic on Fractions."""
    agreed = 0
    for k in range(1, len(OEIS_DIGITS) + 1):
        scale = 10 ** (k - 1)
        target = int(OEIS_DIGITS[:k])
        if floor(lo * scale) == target and floor(hi * scale) == target:
            agreed = k
        else:
            break
    return agreed


def decided_negative(upper_fn, a: Fraction, b: Fraction, pieces: int):
    """Decide upper_fn < 0 on [a, b] by subdividing into `pieces` closed
    subintervals; upper_fn(p, q) returns exact endpoints of an enclosure of
    an upper bound valid on all of [p, q]. Returns (decided, worst upper
    endpoint as a Fraction)."""
    worst = None
    all_negative = True
    for i in range(pieces):
        p = a + (b - a) * Fraction(i, pieces)
        q = a + (b - a) * Fraction(i + 1, pieces)
        _, hi_ = upper_fn(p, q)
        if worst is None or hi_ > worst:
            worst = hi_
        if not hi_ < 0:
            all_negative = False
    return all_negative, worst


def main() -> None:
    fctx.prec = FLINT_PREC_BITS
    iv.dps = IV_DPS
    mu = mobius_sieve(K_FLINT + 1)

    with open(os.path.join(HERE, "decided.json")) as f:
        decided = json.load(f)
    xs_rec = decided["constants"]["x_star"]["flint"]["interval"]
    xs_rec_lo, xs_rec_hi = Fraction(xs_rec[0]), Fraction(xs_rec[1])
    sc_rec = decided["constants"]["sigma_c"]["flint"]["interval"]

    out: dict = {
        "hunt": "prime_zeta_rightmost",
        "task": "WP5 calibration control, lesions, precision response",
        "date": "2026-08-16",
        "versions": {
            "python-flint": getattr(flint, "__version__", "unknown"),
            "mpmath": mpmath.__version__,
        },
        "vocabulary": "decided = interval/ball enclosure with exact endpoint sign logic; measured = one float route",
        "solver": {
            "name": "decide.bisect_decreasing",
            "identity": "same function object decide.main() calls for sigma_c; asserted identical to instrument.bisect_decreasing at import",
        },
    }

    # ------------------------------------------------------------------
    # Baseline: re-solve sigma_c in this process, exactly as decide.py does,
    # and require the outward decimal interval to match decided.json byte for
    # byte. Ties every comparison below to the recorded constant.
    # ------------------------------------------------------------------
    def f_h_arb(q: Fraction):
        return arb_endpoints(h_arb(arb_from_fraction(q), K_FLINT, mu))

    with Timer() as t:
        r_sc = solve(f_h_arb, *SIGMA_C_BRACKET, SIGMA_C_TARGET_FLINT)
    sc_lo, sc_hi = r_sc["lo"], r_sc["hi"]
    sc_here = interval_record(
        sc_lo, sc_hi, "python-flint (arb)", f"{FLINT_PREC_BITS} bits",
        "sigma_c re-solved in-process, decide.py's exact flint code path",
        t.seconds, {"iterations": r_sc["iterations"], "sign_stalled": r_sc["sign_stalled"]})
    baseline_match = sc_here["interval"] == sc_rec
    out["baseline_sigma_c"] = {
        "resolved": sc_here,
        "decided_json_interval": sc_rec,
        "interval_strings_match_decided_json": baseline_match,
    }

    # ------------------------------------------------------------------
    # 1. CALIBRATION: zeta partial-sum balance, root of zeta(sigma) = 2 = x*
    # ------------------------------------------------------------------
    def cal_flint(q: Fraction):
        s = arb_from_fraction(q)
        tail = arb.zeta(s) - 1        # sum_{n>=2} n^(-s)
        return arb_endpoints(tail - 1)  # minus the leading term a_1 = 1

    with Timer() as t:
        r = solve(cal_flint, *SIGMA_C_BRACKET, SIGMA_C_TARGET_FLINT)
    cal_f_lo, cal_f_hi = r["lo"], r["hi"]
    cal_f = interval_record(
        cal_f_lo, cal_f_hi, "python-flint (arb)", f"{FLINT_PREC_BITS} bits",
        "balance (zeta(s)-1) - 1 through decide.bisect_decreasing, sigma_c's "
        "bracket [1.7, 1.9] and target width; arb zeta",
        t.seconds, {"iterations": r["iterations"], "sign_stalled": r["sign_stalled"]})

    def cal_iv(q: Fraction):
        s = iv_from_fraction(q)
        tail = zeta_iv(s, N_IV_XSTAR) - 1
        return iv_endpoints(tail - 1)

    with Timer() as t:
        r = solve(cal_iv, *SIGMA_C_BRACKET, SIGMA_C_TARGET_IV)
    cal_i_lo, cal_i_hi = r["lo"], r["hi"]
    cal_i = interval_record(
        cal_i_lo, cal_i_hi, "mpmath.iv", f"dps {IV_DPS}",
        f"same balance and solver; zeta by Dirichlet sum N={N_IV_XSTAR} plus "
        "Euler-Maclaurin tail (instrument.py docstring 2)",
        t.seconds, {"iterations": r["iterations"], "sign_stalled": r["sign_stalled"],
                    "dirichlet_N": N_IV_XSTAR})

    digits_f = oeis_digits_agreed(cal_f_lo, cal_f_hi)
    digits_i = oeis_digits_agreed(cal_i_lo, cal_i_hi)
    oeis_in_f = cal_f_lo <= OEIS_LO and OEIS_HI <= cal_f_hi
    oeis_in_i = cal_i_lo <= OEIS_LO and OEIS_HI <= cal_i_hi
    consistent_with_xstar = max(cal_f_lo, xs_rec_lo) <= min(cal_f_hi, xs_rec_hi)
    cal_pass = bool(oeis_in_f and oeis_in_i and digits_f >= 30 and consistent_with_xstar)
    out["calibration_zeta_partial_sums"] = {
        "balance": "leading a_1 = 1 vs tail sum_{n>=2} n^(-sigma); root of zeta(sigma) = 2, OEIS A107311's x*",
        "monotonicity": "exact, termwise: zeta'(sigma) < 0 for sigma > 1, no numeric guard needed",
        "flint": cal_f,
        "mpmath_iv": cal_i,
        "oeis_value_interval_inside_flint_enclosure": bool(oeis_in_f),
        "oeis_value_interval_inside_iv_enclosure": bool(oeis_in_i),
        "oeis_digits_reproduced_flint": digits_f,
        "oeis_digits_reproduced_iv": digits_i,
        "enclosure_intersects_decided_json_x_star": bool(consistent_with_xstar),
        "pass": cal_pass,
    }

    # ------------------------------------------------------------------
    # 2. LESION 1: drop the p = 3 term from the tail
    # ------------------------------------------------------------------
    def les1_flint(q: Fraction):
        s = arb_from_fraction(q)
        return arb_endpoints(h_arb(s, K_FLINT, mu) - arb(3) ** (-s))

    with Timer() as t:
        r = solve(les1_flint, *LES1_BRACKET, LES_TARGET_FLINT)
    l1f_lo, l1f_hi = r["lo"], r["hi"]
    l1f = interval_record(
        l1f_lo, l1f_hi, "python-flint (arb)", f"{FLINT_PREC_BITS} bits",
        f"balance sum_{{p>=5}} p^(-s) = 2^(-s) as P(s) - 2^(1-s) - 3^(-s); "
        f"Moebius series K={K_FLINT}, same tail bound as sigma_c; bracket [1.25, 1.6]",
        t.seconds, {"iterations": r["iterations"], "sign_stalled": r["sign_stalled"],
                    "moebius_K": K_FLINT})

    def les1_iv(q: Fraction):
        s = iv_from_fraction(q)
        return iv_endpoints(h_iv(s, K_IV, mu) - iv.mpf(3) ** (-s))

    with Timer() as t:
        r = solve(les1_iv, *LES1_BRACKET, LES1_TARGET_IV)
    l1i_lo, l1i_hi = r["lo"], r["hi"]
    l1i = interval_record(
        l1i_lo, l1i_hi, "mpmath.iv", f"dps {IV_DPS}",
        f"same lesioned balance, iv machinery, Moebius K={K_IV}",
        t.seconds, {"iterations": r["iterations"], "sign_stalled": r["sign_stalled"],
                    "moebius_K": K_IV})

    def les1_prime_upper(a: Fraction, b: Fraction):
        I = arb_interval(a, b)
        val = 2 * arb(2).log() * arb(2) ** (-I) + arb(3).log() * arb(3) ** (-I)
        for p in primes_upto(GUARD_PRIME_CUTOFF):
            val -= arb(p).log() * arb(p) ** (-I)
        return arb_endpoints(val)

    with Timer() as t:
        g1_ok, g1_worst = decided_negative(les1_prime_upper, *LES1_BRACKET, GUARD_PIECES)

    shift_lo = sc_lo - l1f_hi
    shift_hi = sc_hi - l1f_lo
    shift_dec = outward_decimal(shift_lo, shift_hi, 31)
    moved = shift_lo > 0
    below_x_star = l1f_hi < xs_rec_lo
    backends_meet = max(l1f_lo, l1i_lo) <= min(l1f_hi, l1i_hi)
    les1_pass = bool(moved and g1_ok and backends_meet)
    out["lesion_1_drop_p3_from_tail"] = {
        "balance": "sum_{p>=5} p^(-s) = 2^(-s), the sigma_c balance with the p = 3 tail term removed",
        "flint": l1f,
        "mpmath_iv": l1i,
        "cross_checks": {"backends_intersect": bool(backends_meet)},
        "uniqueness_guard": {
            "statement": "les1'(s) < 0 on [1.25, 1.6] via the truncated upper bound (module docstring 2), 16 subintervals",
            "decided": bool(g1_ok),
            "worst_upper_endpoint": str(float(g1_worst)),
            "backend": "python-flint (arb)",
            "precision": f"{FLINT_PREC_BITS} bits",
            "prime_cutoff": GUARD_PRIME_CUTOFF,
            "time_s": round(t.seconds, 3),
        },
        "shift_from_sigma_c": {
            "statement": "sigma_c - root(lesion 1), exact rational endpoint arithmetic on the two flint enclosures",
            "interval": list(shift_dec),
            "decided_nonzero": bool(moved),
            "backend": "python-flint (arb)",
            "precision": f"{FLINT_PREC_BITS} bits",
        },
        "decidedly_below_x_star_too": bool(below_x_star),
        "reading": "the solver moved by ~0.35 when one tail term was removed, so it reads its input rather than a cache",
        "pass": les1_pass,
    }

    # ------------------------------------------------------------------
    # 3. LESION 2: zeta partial-sum series with the wrong leading term 2^(-s)
    # ------------------------------------------------------------------
    def les2_flint(q: Fraction):
        s = arb_from_fraction(q)
        tail = arb.zeta(s) - 1 - arb(2) ** (-s)   # sum_{n>=3} n^(-s)
        return arb_endpoints(tail - arb(2) ** (-s))

    with Timer() as t:
        r = solve(les2_flint, *LES2_BRACKET, LES_TARGET_FLINT)
    l2f_lo, l2f_hi = r["lo"], r["hi"]
    l2f = interval_record(
        l2f_lo, l2f_hi, "python-flint (arb)", f"{FLINT_PREC_BITS} bits",
        "balance 2^(-s) = sum_{n>=3} n^(-s), i.e. zeta(s) - 1 - 2^(1-s) = 0; "
        "arb zeta; bracket [2, 2.9]",
        t.seconds, {"iterations": r["iterations"], "sign_stalled": r["sign_stalled"]})

    def les2_iv(q: Fraction):
        s = iv_from_fraction(q)
        tail = zeta_iv(s, N_IV_XSTAR) - 1 - iv.mpf(2) ** (-s)
        return iv_endpoints(tail - iv.mpf(2) ** (-s))

    with Timer() as t:
        r = solve(les2_iv, *LES2_BRACKET, LES2_TARGET_IV)
    l2i_lo, l2i_hi = r["lo"], r["hi"]
    l2i = interval_record(
        l2i_lo, l2i_hi, "mpmath.iv", f"dps {IV_DPS}",
        f"same balance and solver; zeta by Dirichlet sum N={N_IV_XSTAR} plus Euler-Maclaurin tail",
        t.seconds, {"iterations": r["iterations"], "sign_stalled": r["sign_stalled"],
                    "dirichlet_N": N_IV_XSTAR})

    def les2_prime_upper(a: Fraction, b: Fraction):
        I = arb_interval(a, b)
        val = 2 * arb(2).log() * arb(2) ** (-I)
        for n in range(2, GUARD_N_CUTOFF + 1):
            val -= arb(n).log() * arb(n) ** (-I)
        return arb_endpoints(val)

    with Timer() as t:
        g2_ok, g2_worst = decided_negative(les2_prime_upper, *LES2_BRACKET, GUARD_PIECES)

    not_sigma_c = l2f_lo > sc_hi
    not_x_star = l2f_lo > xs_rec_hi
    backends_meet2 = max(l2f_lo, l2i_lo) <= min(l2f_hi, l2i_hi)
    les2_pass = bool(not_sigma_c and not_x_star and g2_ok and backends_meet2)
    out["lesion_2_wrong_leading_term"] = {
        "balance": "the zeta partial-sum series with P's leading term 2^(-sigma) balanced against the tail after it, sum_{n>=3} n^(-sigma): the conjecture's mis-port made mechanical",
        "flint": l2f,
        "mpmath_iv": l2i,
        "cross_checks": {"backends_intersect": bool(backends_meet2)},
        "uniqueness_guard": {
            "statement": "les2'(s) < 0 on [2, 2.9] via zeta'(s) <= -sum_{2<=n<=200} log n * n^(-s) (module docstring 3), 16 subintervals",
            "decided": bool(g2_ok),
            "worst_upper_endpoint": str(float(g2_worst)),
            "backend": "python-flint (arb)",
            "precision": f"{FLINT_PREC_BITS} bits",
            "n_cutoff": GUARD_N_CUTOFF,
            "time_s": round(t.seconds, 3),
        },
        "reproduces_x_star": {"decided_false": bool(not_x_star),
                              "compare": "exact rational: lo(lesion 2) > hi(x_star record)"},
        "reproduces_sigma_c": {"decided_false": bool(not_sigma_c),
                               "compare": "exact rational: lo(lesion 2) > hi(sigma_c re-solve)"},
        "no_root_variant": "balancing 2^(-sigma) against the full tail sum_{n>=2} instead has no root: zeta(s) - 1 - 2^(-s) = 3^(-s) + 4^(-s) + ... > 0 for all s, exactly",
        "reading": "the mechanical mis-port lands at ~2.424, near neither constant: the balance template and the series fed to it both matter",
        "pass": les2_pass,
    }

    # ------------------------------------------------------------------
    # 4. PRECISION RESPONSE: sigma_c width vs working precision
    # ------------------------------------------------------------------
    runs = []
    widths = []
    for bits in PREC_RESPONSE_BITS:
        fctx.prec = bits
        with Timer() as t:
            r = solve(f_h_arb, *SIGMA_C_BRACKET, PREC_RESPONSE_TARGET)
        w = r["hi"] - r["lo"]
        widths.append(w)
        lo_s, hi_s = outward_decimal(r["lo"], r["hi"], 40)
        runs.append({
            "precision": f"{bits} bits",
            "backend": "python-flint (arb)",
            "achieved_width": f"{float(w):.3e}",
            "interval": [lo_s, hi_s],
            "iterations": r["iterations"],
            "sign_stalled": r["sign_stalled"],
            "time_s": round(t.seconds, 3),
        })
    fctx.prec = FLINT_PREC_BITS
    strictly_shrinking = all(widths[i] > widths[i + 1] for i in range(len(widths) - 1))
    out["precision_response_sigma_c"] = {
        "setup": "decide.py's exact sigma_c flint code path, target width 1e-60 (unreachable at the lower precisions), so the achieved width is set by where the sign stalls",
        "runs": runs,
        "strictly_shrinking": bool(strictly_shrinking),
        "pass": bool(strictly_shrinking),
    }

    # ------------------------------------------------------------------
    # 5. decide.py reproducibility: rerun, compare outside time_s, restore
    # ------------------------------------------------------------------
    dec_path = os.path.join(HERE, "decided.json")
    with open(dec_path, "rb") as f:
        before = f.read()
    with Timer() as t:
        proc = subprocess.run([sys.executable, os.path.join(HERE, "decide.py")],
                              capture_output=True)
    with open(dec_path, "rb") as f:
        after = f.read()
    with open(dec_path, "wb") as f:
        f.write(before)  # restore the recorded artifact unconditionally
    before_lines = [l for l in before.decode().splitlines() if '"time_s"' not in l]
    after_lines = [l for l in after.decode().splitlines() if '"time_s"' not in l]
    masked = sum('"time_s"' in l for l in before.decode().splitlines())
    rerun_pass = bool(proc.returncode == 0 and before_lines == after_lines)
    out["decide_rerun_reproducibility"] = {
        "statement": "decide.py rerun in a subprocess; fresh decided.json compared to the recorded one line for line with time_s lines masked; recorded bytes restored afterwards",
        "returncode": proc.returncode,
        "identical_outside_time_s": rerun_pass,
        "differing_lines_outside_time_s": sum(x != y for x, y in zip(before_lines, after_lines)) + abs(len(before_lines) - len(after_lines)),
        "time_s_lines_masked": masked,
        "decide_py_modified_by_wp5": False,
        "time_s": round(t.seconds, 3),
        "pass": rerun_pass,
    }

    # ------------------------------------------------------------------
    # Verdict
    # ------------------------------------------------------------------
    out["summary"] = {
        "baseline_sigma_c_matches_decided_json": bool(baseline_match),
        "calibration": "PASS" if cal_pass else "FAIL",
        "lesion_1": "PASS" if les1_pass else "FAIL",
        "lesion_2": "PASS" if les2_pass else "FAIL",
        "precision_response": "PASS" if strictly_shrinking else "FAIL",
        "decide_rerun_reproducibility": "PASS" if rerun_pass else "FAIL",
        "overall": "PASS" if (baseline_match and cal_pass and les1_pass and les2_pass
                              and strictly_shrinking and rerun_pass) else "FAIL",
    }

    path = os.path.join(HERE, "controls_results.json")
    with open(path, "w") as f:
        json.dump(out, f, indent=2)
        f.write("\n")

    print(json.dumps(out, indent=2))


if __name__ == "__main__":
    main()
