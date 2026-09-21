"""Lightweight sanity checks for THEOREM_B_FORMULA_REPAIR.md.

NOT proof. Every number here is a floating-point or ball-free mpmath
evaluation at finite precision on a finite range. The checks exist to catch
sign slips, factor-of-two slips and misidentified constants in the derivation
recorded in THEOREM_B_FORMULA_REPAIR.md, not to establish any claim.

chi is the primitive real character mod 3, written through Hurwitz zeta as

    L(s, chi) = 3^{-s} ( zeta(s, 1/3) - zeta(s, 2/3) ),

which is the analytic continuation for all s != 1.

Run from the repository root:

    <venv>/bin/python hunts/prime_pair_error/formula_repair_checks.py

Writes hunts/prime_pair_error/results_formula_repair_checks.json.
"""

from __future__ import annotations

import json
from pathlib import Path

from mpmath import mp

mp.dps = 60

HERE = Path(__file__).resolve().parent
ZEROS_JSON = HERE / "results_landau_zero_probe.json"
OUT_JSON = HERE / "results_formula_repair_checks.json"


# ---------------------------------------------------------------------------
# character, L-function, von Mangoldt
# ---------------------------------------------------------------------------


def chi3(n: int) -> int:
    """Primitive real character mod 3. chi3(-1) = chi3(2) = -1, so chi3 is odd."""
    r = n % 3
    return 0 if r == 0 else (1 if r == 1 else -1)


def L(s):
    """L(s, chi3) by Hurwitz zeta; valid for all s != 1."""
    s = mp.mpf(s) if not isinstance(s, mp.mpf) else s
    return mp.power(3, -s) * (mp.zeta(s, mp.mpf(1) / 3) - mp.zeta(s, mp.mpf(2) / 3))


def Lprime(s):
    return mp.diff(L, s)


def dlogL(s):
    """L'/L (s, chi3)."""
    return Lprime(s) / L(s)


def von_mangoldt_upto(N: int):
    """Lambda(n) for n <= N by sieve, as mpf."""
    lam = [mp.mpf(0)] * (N + 1)
    for p in range(2, N + 1):
        if lam[p] != 0:
            continue
        # p is prime iff untouched (every composite gets set by a smaller prime)
        is_prime = all(p % q for q in range(2, int(p**0.5) + 1))
        if not is_prime:
            continue
        logp = mp.log(p)
        q = p
        while q <= N:
            lam[q] = logp
            q *= p
    return lam


# ---------------------------------------------------------------------------
# C1. the algebraic decomposition I = psi_1 - (x/2) psi
# ---------------------------------------------------------------------------


def check_decomposition(N: int = 200):
    """I(x) = psi_1(x, chi) - (x/2) psi(x, chi) at integer x, exactly.

    This is the load-bearing algebraic step of the truncated formula: the
    sharp-cutoff object I is the first Riesz mean minus x/2 times the sharp
    prime-counting sum. It is an identity, so the residual should be at
    round-off level.
    """
    lam = von_mangoldt_upto(N)
    worst = mp.mpf(0)
    for x in range(2, N + 1):
        I = mp.fsum(lam[m] * chi3(m) * (mp.mpf(x) / 2 - m) for m in range(2, x + 1))
        psi = mp.fsum(lam[m] * chi3(m) for m in range(2, x + 1))
        psi1 = mp.fsum(lam[m] * chi3(m) * (x - m) for m in range(2, x + 1))
        worst = max(worst, abs(I - (psi1 - mp.mpf(x) / 2 * psi)))
    return {
        "x_max": N,
        "max_abs_residual": mp.nstr(worst, 8),
        "passes": bool(worst < mp.mpf(10) ** (-40)),
    }


# ---------------------------------------------------------------------------
# C2. where the trivial zeros are, and where they are not
# ---------------------------------------------------------------------------


def check_trivial_zeros():
    """chi3 is odd, so L(s, chi3) vanishes at s = -1, -3, -5, ... and not at
    s = 0, -2, -4, ....  The s = -1 vanishing is what collides with the
    1/(s+1) of the Mellin kernel; L(0, chi3) != 0 is why s = 0 stays simple.
    """
    vals = {str(s): mp.nstr(L(s), 12) for s in (0, -1, -2, -3, -4, -5)}
    return {
        "L_at": vals,
        "L(0)_minus_one_third": mp.nstr(abs(L(0) - mp.mpf(1) / 3), 8),
        "abs_L(-1)": mp.nstr(abs(L(-1)), 8),
        "abs_L(-3)": mp.nstr(abs(L(-3)), 8),
        "abs_L(-2)": mp.nstr(abs(L(-2)), 8),
        "passes": bool(
            abs(L(0) - mp.mpf(1) / 3) < mp.mpf(10) ** (-30)
            and abs(L(-1)) < mp.mpf(10) ** (-30)
            and abs(L(-3)) < mp.mpf(10) ** (-30)
            and abs(L(-2)) > mp.mpf(10) ** (-3)
        ),
    }


# ---------------------------------------------------------------------------
# C3. the Laurent expansion of G at s = -1 (the double pole and the log x)
# ---------------------------------------------------------------------------


def G(s):
    """G(s) = -(L'/L)(s, chi) (1 - s) / (2 s (s + 1)).

    This is the Mellin transform of I: for Re s > 1,
    int_1^infty I(x) x^{-s-2} dx = G(s).
    """
    return -dlogL(s) * (1 - s) / (2 * s * (s + 1))


def check_double_pole_at_minus_one():
    """Res_{s=-1} G(s) x^{s+1} = A log x + B with A = 1 and B = nu.

    G has a DOUBLE pole at s = -1: the kernel contributes 1/(s+1) and
    -(L'/L) contributes another 1/(s+1) from the simple trivial zero of L
    there.  Writing u = s + 1 and f(u) = u^2 G(u-1), the Laurent data is
    A = f(0), B = f'(0), and the residue of G(s) x^{s+1} is A log x + B.

    Closed form derived from the functional equation:
        nu = gamma + log(2 pi / 3) - 1/2 - (L'/L)(2, chi3).
    """
    h = mp.mpf(10) ** (-15)

    def f(u):
        return u**2 * G(u - 1)

    fp, fm = f(h), f(-h)
    A = (fp + fm) / 2
    B = (fp - fm) / (2 * h)

    nu_closed = mp.euler + mp.log(2 * mp.pi / 3) - mp.mpf(1) / 2 - dlogL(2)
    # h(-1) = lim_{s -> -1} [ (L'/L)(s) - 1/(s+1) ] ; B = 1/2 + h(-1)
    h_minus_one_numeric = dlogL(-1 + h) - 1 / h
    h_minus_one_closed = mp.euler + mp.log(2 * mp.pi / 3) - 1 - dlogL(2)

    return {
        "A_numeric": mp.nstr(A, 12),
        "A_minus_1": mp.nstr(abs(A - 1), 6),
        "B_numeric": mp.nstr(B, 12),
        "nu_closed_form": mp.nstr(nu_closed, 12),
        "B_minus_nu": mp.nstr(abs(B - nu_closed), 6),
        "h(-1)_numeric": mp.nstr(h_minus_one_numeric, 10),
        "h(-1)_closed": mp.nstr(h_minus_one_closed, 10),
        "h(-1)_gap": mp.nstr(abs(h_minus_one_numeric - h_minus_one_closed), 6),
        "passes": bool(
            abs(A - 1) < mp.mpf(10) ** (-8) and abs(B - nu_closed) < mp.mpf(10) ** (-8)
        ),
    }


def check_mu1():
    """mu_1 = Res_{s=0} G(s) x^{s+1} / x = -(1/2) (L'/L)(0, chi3).

    s = 0 is a simple pole of G because L(0, chi3) != 0.
    """
    mu1 = -dlogL(0) / 2
    h = mp.mpf(10) ** (-15)
    residue_numeric = (h * G(h) + (-h) * G(-h)) / 2  # even-average of s G(s) at 0
    return {
        "mu1_closed": mp.nstr(mu1, 12),
        "residue_of_sG_at_0": mp.nstr(residue_numeric, 12),
        "gap": mp.nstr(abs(mu1 - residue_numeric), 6),
        "passes": bool(abs(mu1 - residue_numeric) < mp.mpf(10) ** (-8)),
    }


# ---------------------------------------------------------------------------
# C4. the defect: the coefficient decays like 1/|gamma|, not 1/|gamma|^2
# ---------------------------------------------------------------------------


def load_zero_ordinates():
    data = json.loads(ZEROS_JSON.read_text(encoding="utf-8"))
    located = data.get("located_zeros", [])
    out = []
    for z in located:
        if isinstance(z, (int, float, str)):
            out.append(mp.mpf(z))
        elif isinstance(z, dict):
            for key in ("im", "t", "gamma", "ordinate", "imag"):
                if key in z:
                    out.append(mp.mpf(z[key]))
                    break
    return out


def check_coefficient_decay():
    """Partial sums of |c(rho)| against partial sums of 1/|rho(rho+1)|.

    c(rho) = (rho - 1) / (2 rho (rho + 1)).  Because |rho - 1| grows like
    |gamma|, |c(rho)| ~ 1/(2|gamma|), while 1/|rho(rho+1)| ~ 1/|gamma|^2.
    Over the 21 ordinates the probe located below height 60 this is an
    illustration of the ratio, nothing more: divergence of sum 1/|gamma| is a
    statement about infinitely many zeros and is argued in the report from
    Riemann-von Mangoldt, not from this table.
    """
    gammas = load_zero_ordinates()
    rows = []
    s_abs_c = mp.mpf(0)
    s_sq = mp.mpf(0)
    for g in gammas:
        rho = mp.mpc(mp.mpf(1) / 2, g)
        c = (rho - 1) / (2 * rho * (rho + 1))
        # conjugate pair contributes twice
        s_abs_c += 2 * abs(c)
        s_sq += 2 / abs(rho * (rho + 1))
        rows.append(
            {
                "gamma": mp.nstr(g, 10),
                "abs_c": mp.nstr(abs(c), 6),
                "abs_c_times_gamma": mp.nstr(abs(c) * g, 6),
                "one_over_abs_rho_rho_plus_1": mp.nstr(1 / abs(rho * (rho + 1)), 6),
                "running_sum_abs_c_pairs": mp.nstr(s_abs_c, 8),
                "running_sum_sq_pairs": mp.nstr(s_sq, 8),
            }
        )
    # coefficient identity: (rho-1)/(2 rho (rho+1)) = 1/(2 rho) - 1/(rho(rho+1))
    worst = mp.mpf(0)
    for g in gammas:
        rho = mp.mpc(mp.mpf(1) / 2, g)
        lhs = (rho - 1) / (2 * rho * (rho + 1))
        rhs = 1 / (2 * rho) - 1 / (rho * (rho + 1))
        worst = max(worst, abs(lhs - rhs))
    return {
        "n_ordinates": len(gammas),
        "identity_max_residual": mp.nstr(worst, 6),
        "rows": rows,
        "passes": bool(len(gammas) > 0 and worst < mp.mpf(10) ** (-40)),
    }


# ---------------------------------------------------------------------------
# C5. the truncation height the original document proposed is too small
# ---------------------------------------------------------------------------


def check_truncation_height(beta0: float = 0.6):
    """The remainder of the truncated formula carries x^2 log^2(xT) / T.

    For that to be o(x^{1+beta0}) one needs T >> x^{1-beta0}.  The original
    document's "T = x^delta for small fixed delta" therefore fails whenever
    delta < 1 - beta0.  Tabulated here at beta0 = 0.6, delta = 0.1.
    """
    b0 = mp.mpf(beta0)
    rows = []
    for e in (4, 8, 16, 32, 64, 128):
        x = mp.mpf(10) ** e
        T_small = x ** mp.mpf("0.1")
        T_ok = x ** (1 - b0 + mp.mpf("0.05"))
        main = x ** (1 + b0)
        err_small = x**2 * mp.log(x * T_small) ** 2 / T_small
        err_ok = x**2 * mp.log(x * T_ok) ** 2 / T_ok
        rows.append(
            {
                "x": f"1e{e}",
                "main_term_scale_x^(1+beta0)": mp.nstr(main, 6),
                "err_T=x^0.1": mp.nstr(err_small, 6),
                "err_over_main_T=x^0.1": mp.nstr(err_small / main, 6),
                "err_T=x^(1-beta0+0.05)": mp.nstr(err_ok, 6),
                "err_over_main_T=x^(1-beta0+0.05)": mp.nstr(err_ok / main, 6),
            }
        )
    return {
        "beta0": float(beta0),
        "rows": rows,
        "passes": True,
    }


# ---------------------------------------------------------------------------
# C7. Lemma 1: no real zeros of L(s, chi3) in (0, 1)
# ---------------------------------------------------------------------------


def check_no_real_zeros(n_terms: int = 20000):
    """Lemma 1 says L(s, chi3) = sum_k [(3k+1)^-s - (3k+2)^-s] >= 1 - 2^-s > 0 for s > 0.

    Two things are checked, neither of which is the proof:
      (i) the grouped series agrees with the continuation used elsewhere in
          this file, which is what makes the rearrangement in Lemma 1 the
          same function;
      (ii) every bracket is positive and L(s) >= 1 - 2^-s on a grid of s.
    The proof is in section 1 and does not depend on these numbers.
    """
    rows = []
    all_brackets_positive = True
    bound_holds = True
    tail_respected = True
    for s_float in ("0.05", "0.25", "0.5", "0.75", "0.95", "1.5"):
        s = mp.mpf(s_float)
        total = mp.mpf(0)
        neg_brackets = 0
        for k in range(n_terms):
            term = mp.power(3 * k + 1, -s) - mp.power(3 * k + 2, -s)
            if term <= 0:
                neg_brackets += 1
            total += term
        direct = L(s)
        gap = abs(total - direct)
        lower = 1 - mp.power(2, -s)
        # Each omitted bracket is int_{3k+1}^{3k+2} s t^{-s-1} dt <= s (3k+1)^{-s-1},
        # so the omitted tail is at most (3 n_terms - 2)^{-s} / 3.  For small s
        # this is large: the grouped series converges very slowly there, which
        # is a property of the series and not a discrepancy.
        tail_bound = mp.power(3 * n_terms - 2, -s) / 3
        all_brackets_positive = all_brackets_positive and neg_brackets == 0
        bound_holds = bound_holds and (direct >= lower)
        tail_respected = tail_respected and (gap <= tail_bound)
        rows.append(
            {
                "s": s_float,
                "grouped_series_partial": mp.nstr(total, 12),
                "L_via_hurwitz": mp.nstr(direct, 12),
                "gap": mp.nstr(gap, 6),
                "tail_bound": mp.nstr(tail_bound, 6),
                "gap_within_tail_bound": bool(gap <= tail_bound),
                "negative_brackets": neg_brackets,
                "lower_bound_1_minus_2^-s": mp.nstr(lower, 12),
                "L_exceeds_lower_bound": bool(direct >= lower),
            }
        )
    return {
        "n_terms": n_terms,
        "rows": rows,
        "all_brackets_positive": all_brackets_positive,
        "lower_bound_holds_on_grid": bound_holds,
        "all_gaps_within_tail_bound": tail_respected,
        "passes": bool(all_brackets_positive and bound_holds and tail_respected),
    }


# ---------------------------------------------------------------------------
# C8. provenance audit of the inherited zero ordinates
# ---------------------------------------------------------------------------


def check_zero_ordinate_provenance():
    """Audit results_landau_zero_probe.json, which the reviewer flagged as unaudited.

    (i) re-evaluate |L(1/2 + i gamma)| at each listed ordinate;
    (ii) compare the count to the Riemann-von Mangoldt prediction (F2-low),
         N(T, chi) ~ (T/2pi) log(qT/2pi) - T/2pi - chi(-1)/8, at the scan's
         stated height.

    This is NOT a completeness proof.  A step-0.25 sign-change scan can miss a
    close pair of ordinates and this check cannot see that.  It establishes
    only that the listed ordinates sit on genuine zeros and that the count is
    not obviously short.
    """
    data = json.loads(ZEROS_JSON.read_text(encoding="utf-8"))
    gammas = [mp.mpf(str(z["im"])) for z in data["located_zeros"]]
    t_max = mp.mpf(str(data["t_max_scanned"]))
    worst = mp.mpf(0)
    rows = []
    def L_complex(s):
        return mp.power(3, -s) * (mp.zeta(s, mp.mpf(1) / 3) - mp.zeta(s, mp.mpf(2) / 3))

    for g in gammas:
        val = abs(L_complex(mp.mpc(mp.mpf(1) / 2, g)))
        worst = max(worst, val)
        rows.append({"gamma": mp.nstr(g, 12), "abs_L_at_half_plus_i_gamma": mp.nstr(val, 6)})
    q = mp.mpf(3)
    two_pi = 2 * mp.pi
    predicted = (t_max / two_pi) * mp.log(q * t_max / two_pi) - t_max / two_pi + mp.mpf(1) / 8
    return {
        "source": ZEROS_JSON.name,
        "t_max_scanned": mp.nstr(t_max, 6),
        "scan_step": float(data["scan_step"]),
        "n_listed": len(gammas),
        "max_abs_L_at_listed_ordinates": mp.nstr(worst, 6),
        "rvm_predicted_count_to_t_max": mp.nstr(predicted, 6),
        "count_minus_prediction": mp.nstr(len(gammas) - predicted, 6),
        "completeness_proved": False,
        "passes": bool(worst < mp.mpf(10) ** (-10) and abs(len(gammas) - predicted) < 3),
    }


# ---------------------------------------------------------------------------


def main() -> None:
    results = {
        "note": (
            "NOT proof. Finite-precision, finite-range sanity checks on the "
            "derivation in THEOREM_B_FORMULA_REPAIR.md."
        ),
        "mp_dps": mp.dps,
        "C1_decomposition_identity": check_decomposition(),
        "C2_trivial_zeros": check_trivial_zeros(),
        "C3_double_pole_at_s_minus_1": check_double_pole_at_minus_one(),
        "C4_mu1_residue_at_s_0": check_mu1(),
        "C5_coefficient_decay": check_coefficient_decay(),
        "C6_truncation_height": check_truncation_height(),
        "C7_no_real_zeros": check_no_real_zeros(),
        "C8_zero_ordinate_provenance": check_zero_ordinate_provenance(),
    }
    OUT_JSON.write_text(json.dumps(results, indent=2) + "\n", encoding="utf-8")
    for key, val in results.items():
        if isinstance(val, dict) and "passes" in val:
            print(f"{key}: passes={val['passes']}")
    print(f"wrote {OUT_JSON}")


if __name__ == "__main__":
    main()
