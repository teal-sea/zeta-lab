"""Independent challenge + verification of the arithmetic cancellation candidate.

Target: hunts/prime_pair_error/ARITHMETIC_CANCELLATION_CANDIDATE.md
        at commit b0f8daed26bfd310b173a18514dcd5b6a50d70bb.

Independence: written from the memo's definitions only. Imports nothing from
the author's checker (arithmetic_cancellation_candidate_check.py), nothing
from zeta/, ontology/, harness/, or any other hunts/ module. Only stdlib
(math, cmath, json, fractions) plus mpmath as an external transcendental
engine, run at dps=80 (author used dps=40) with independently coded paths.
Lambda comes from a fresh sieve, not the author's trial-division factorer.

What is tested (the NEW intermediate claims, not just the original identity):
  E3  - memo eq (3), second equality: T_bilinear == -sum(R(N/k)-R(Y))?
        Tested in EXACT rational arithmetic (Fraction). Any nonzero value is
        a rigorous refutation of the equality as written.
  BD  - memo section 4, lines 170-175: the arithmetic sum
        A(N) = sum_{d<=Y} Lam(d) floor(N/d) + B_main(N,K) approximates
        log(N!) = sum_{dk<=N} Lam(d) with O(sqrt N) discrepancy.
        Tests the exact identity  A - log(N!) = T_bilinear - (psi(N)-psi(Y))
        and the scale of the discrepancy (ratio to N).
  RB  - memo section 4 table: R_boundary = O(sqrt N) "established".
        Tests the exact identity  R_b + T_bil - R(N) = E_det(N),
        E_det(N) = S_smooth - log(N!) + N - psi(Y)/2 (elementary + psi(Y)),
        which shows what the R_boundary bound really assumes.
  SP  - memo section 5: the spectral remainder after K^{1-rho} cancellation
        is O(N^beta K^{-beta}) = O(N^{beta/2}), and the k=1 mode accounting.
        Tests the exact finite bracket on pure power modes with stdlib cmath.
  A34 - memo table + section 5.1: sum|R(N/k)| "grows as N^{3/4}" (upper bound
        only was derived). Reports the measured envelope and its oscillation.
  ID  - the candidate identity (2) itself, re-evaluated at dps=80 on squares,
        nonsquares and prime-power cutoffs, plus the integral formula (9)-(10)
        with real (non-integer) upper limit Y re-derived by direct interval
        summation with exact Fraction endpoints.

Author files are not modified by this script.
"""

import cmath
import json
import math
from fractions import Fraction
from pathlib import Path

import mpmath as mp

mp.mp.dps = 80
ROOT = Path(__file__).parent
N_MAX = 100000  # task cap; sieve to here, loops are O(K) per N via prefix sums


# ----------------------------------------------------------------------------
# Fresh von Mangoldt sieve (pure stdlib trial-division-free sieve)
# ----------------------------------------------------------------------------
def build_lambda_psi_py(n_max):
    """Pure-stdlib sieve. lam[n] = log p if n = p^m else 0.0 (float)."""
    is_comp = bytearray(b"\x00") * (n_max + 1)
    primes = []
    lam = [0.0] * (n_max + 1)
    for n in range(2, n_max + 1):
        if not is_comp[n]:
            primes.append(n)
            # prime powers n = p^m
            pp = n
            while pp <= n_max:
                lam[pp] = math.log(n)
                if pp > n_max // n:
                    break
                pp *= n
            if n * n <= n_max:
                step = n
                start = n * n
                for m in range(start, n_max + 1, step):
                    is_comp[m] = 1
    psi = [0.0] * (n_max + 1)
    s = 0.0
    for n in range(1, n_max + 1):
        s += lam[n]
        psi[n] = s
    return lam, psi


def main():
    lam, psi = build_lambda_psi_py(N_MAX)

    out = {
        "description": "Independent challenge of ARITHMETIC_CANCELLATION_CANDIDATE.md",
        "base_commit": "b0f8daed26bfd310b173a18514dcd5b6a50d70bb",
        "engine": "stdlib math/cmath/fractions + mpmath at dps=80; pure-stdlib sieve",
        "cases": {},
        "spectral": {},
        "max_identity_defect": 0.0,
        "max_integral_defect": 0.0,
        "max_E3_exact_nonzero_denominator": None,
        "max_RB_identity_defect": 0.0,
        "max_BD_identity_defect": 0.0,
    }

    test_N = [16, 25, 27, 32, 36, 49, 64, 81, 100, 121, 144, 200, 400,
              1000, 10000, 100000]

    for N in test_N:
        K = math.isqrt(N)
        Yf = Fraction(N, K)          # exact rational endpoint (need not be integer)
        Y = float(Yf)
        fY = int(math.floor(Y))

        # ---- E3: exact rational test of memo eq (3), second equality ----
        # E_frac = sum_{k=2}^K [(N/k - Y) - (floor(N/k) - floor(Y))], exact.
        # T_bilinear + sum(R(N/k)-R(Y)) = -E_frac  (real parts; psi parts cancel
        # in the difference, floors do not). Nonzero E_frac refutes the equality.
        e_frac = Fraction(0)
        for k in range(2, K + 1):
            e_frac += (Fraction(N, k) - Yf) - (Fraction(N // k) - Fraction(fY))
        e3_nonzero = e_frac != 0

        # ---- High-precision independent evaluation of the decomposition ----
        Nf, Kf = mp.mpf(N), mp.mpf(K)
        Ym = Nf / Kf
        psiY = mp.mpf(psi[fY])
        psiN = mp.mpf(psi[N])

        def R_of(xf, xint):
            return mp.mpf(psi[xint]) - xf

        # D_N by definition (1), tail via inherited integral value -(1+gamma)
        # Recompute log(p) in mpmath at dps=80 from integer p
        # (independent transcendental evaluation).
        s_lam_over_d = mp.mpf(0)
        for d in range(1, fY + 1):
            if lam[d]:
                # recover base prime of prime power d
                tmp, p = d, None
                f = 2
                td = d
                while f * f <= td:
                    if td % f == 0:
                        p = f
                        break
                    f += 1 if f == 2 else 2
                p = p or d
                s_lam_over_d += mp.log(mp.mpf(p)) / mp.mpf(d)
        int_1_Y = s_lam_over_d - psiY / Ym - mp.log(Ym)
        tail = Nf * (-(1 + mp.euler) - int_1_Y)
        sum_RNk = mp.mpf(0)
        for k in range(2, K + 1):
            khi = int(N // k)
            sum_RNk += mp.mpf(psi[khi]) - Nf / mp.mpf(k)
        D_N = tail - sum_RNk

        # T_bilinear via prefix sums (exact same set as the double sum)
        T_bil = mp.mpf(0)
        for k in range(2, K + 1):
            khi = int(N // k)
            if khi > fY:
                lam_seg = mp.mpf(psi[khi] - psi[fY])
                T_bil -= lam_seg - mp.mpf(khi - fY)
        # T_sawtooth
        T_saw = mp.mpf(0)
        for d in range(1, fY + 1):
            if lam[d]:
                tmp = d
                f = 2
                td = d
                p = None
                while f * f <= td:
                    if td % f == 0:
                        p = f
                        break
                    f += 1 if f == 2 else 2
                p = p or d
                frac = Nf / mp.mpf(d) - mp.mpf(N // d)
                T_saw -= mp.log(mp.mpf(p)) * (frac - mp.mpf("0.5"))
        # R_boundary
        B_main = sum((N // k) - fY for k in range(2, K + 1))
        sum_lam_floor = mp.mpf(0)
        for d in range(1, fY + 1):
            if lam[d]:
                tmp = d
                f = 2
                td = d
                p = None
                while f * f <= td:
                    if td % f == 0:
                        p = f
                        break
                    f += 1 if f == 2 else 2
                p = p or d
                sum_lam_floor += mp.log(mp.mpf(p)) * mp.mpf(N // d)
        H_K = sum(mp.mpf(1) / mp.mpf(k) for k in range(1, K + 1))
        S_smooth = Nf * (mp.log(Ym) + H_K - 2 - mp.euler)
        R_b = mp.mpf("0.5") * psiY - mp.mpf(B_main) - sum_lam_floor + S_smooth

        defect_id = abs(float(D_N - (T_bil + T_saw + R_b)))
        out["max_identity_defect"] = max(out["max_identity_defect"], defect_id)

        # ---- BD: exact discrepancy identity + scale ----
        # A(N) - log(N!) = T_bil - (psi(N) - psi(Y)); discrepancy scale via lgamma.
        A_minus_logfact = float(T_bil) - (psi[N] - psi[fY])
        logfact = math.lgamma(N + 1)
        A_val = float(sum_lam_floor) + B_main
        bd_defect = abs((A_val - logfact) - A_minus_logfact)
        out["max_BD_identity_defect"] = max(out["max_BD_identity_defect"], bd_defect)

        # ---- RB: R_b + T_bil - R(N) = E_det(N) ----
        R_N = psi[N] - N
        E_det = float(S_smooth) - logfact + N - 0.5 * psi[fY]
        rb_lhs = float(R_b + T_bil) - R_N
        rb_defect = abs(rb_lhs - E_det)
        out["max_RB_identity_defect"] = max(out["max_RB_identity_defect"], rb_defect)

        # ---- A34: absolute-value envelope ----
        s_abs = 0.0
        for k in range(2, K + 1):
            khi = int(N // k)
            xk = N / k
            s_abs += abs(psi[khi] - xk)

        # ---- Integral formula (9)-(10) by direct interval summation ----
        # int_1^Y psi(u)/u^2 du over unit intervals + [floorY, Y], exact endpoints.
        if N <= 400:
            acc = mp.mpf(0)
            n = 1
            while n < fY:
                c = mp.mpf(psi[n])
                acc += c * (mp.mpf(1) / n - mp.mpf(1) / (n + 1))
                n += 1
            if fY >= 1 and Ym > fY:
                c = mp.mpf(psi[fY])
                acc += c * (mp.mpf(1) / fY - mp.mpf(1) / Ym)
            # int psi/u^2 = acc; int_1^Y R/u^2 = acc - log(Y)
            int_direct = acc - mp.log(Ym)
            int_defect = abs(float(int_direct - int_1_Y))
            out["max_integral_defect"] = max(out["max_integral_defect"], int_defect)
        else:
            int_defect = None

        sq = math.sqrt(N)
        out["cases"][str(N)] = {
            "K": K,
            "Y_exact": str(Yf),
            "Y_is_integer": (Yf.denominator == 1),
            "N_is_prime_power": lam[N] > 0,
            "E3_Efrac_exact": str(e_frac),
            "E3_Efrac_float": float(e_frac),
            "E3_refutes_eq3": bool(e3_nonzero),
            "D_N": float(D_N),
            "T_bilinear": float(T_bil),
            "T_sawtooth": float(T_saw),
            "R_boundary": float(R_b),
            "identity_defect": defect_id,
            "integral_defect": int_defect,
            "R_N": R_N,
            "R_boundary_over_sqrtN": float(R_b) / sq,
            "T_bilinear_over_sqrtN": float(T_bil) / sq,
            "D_N_over_sqrtN": float(D_N) / sq,
            "A_minus_logfact": A_minus_logfact,
            "A_minus_logfact_over_N": A_minus_logfact / N,
            "BD_identity_defect": bd_defect,
            "RB_lhs": rb_lhs,
            "E_det": E_det,
            "RB_identity_defect": rb_defect,
            "sum_abs_R_over_N34": s_abs / (N ** 0.75),
            "E_det_over_sqrtN": E_det / sq,
        }

    # ---- SP: exact finite spectral bracket on pure power modes (stdlib cmath) ----
    # D[g](N) = N*int_{N/K}^inf g(u) u^-2 du - sum_{k=2}^K g(N/k), g(u)=u^rho.
    # Closed form: D_mode = N^rho * B, B = K^{1-rho}/(1-rho) - S2,
    # S2 = sum_{k=2}^K k^{-rho}. Memo sec.5 claims |B| ~ K^{-beta} (decaying);
    # the k=1-exact algebra gives B = (1 - zeta(rho)) - tail_K, i.e. |B| -> O(1).
    for tag, rho in [("hypothetical_0.75+2i", complex(0.75, 2.0)),
                     ("critical_line_first_zero", complex(0.5, 14.134725141734693))]:
        out["spectral"][tag] = {"rho": str(rho), "rows": {}}
        z_rho = complex(mp.zeta(mp.mpc(rho.real, rho.imag)))
        for N in [400, 10000, 100000]:
            K = math.isqrt(N)
            S1 = sum(complex(k) ** (-rho) for k in range(1, K + 1))
            S2 = S1 - 1.0
            pole = complex(K) ** (1 - rho) / (1 - rho)
            B = pole - S2                      # exact finite bracket
            tail_S1 = S1 - pole                # -> zeta(rho); memo drops the "-1"
            memo_scale = K ** (-rho.real)      # memo's claimed remainder scale
            out["spectral"][tag]["rows"][str(N)] = {
                "K": K,
                "bracket_abs": abs(B),
                "one_minus_zeta_abs": abs(1 - z_rho),
                "tail_S1_abs": abs(tail_S1),
                "memo_claimed_scale_K_minus_beta": memo_scale,
                "ratio_bracket_over_claimed": abs(B) / memo_scale,
                "D_mode_over_N_beta": abs(B),
            }
        out["spectral"][tag]["zeta_rho_mpmath_dps80"] = str(z_rho)

    out["max_identity_defect"] = float(out["max_identity_defect"])
    out["max_integral_defect"] = float(out["max_integral_defect"])

    path = ROOT / "independent_arithmetic_cancellation_evidence.json"
    path.write_text(json.dumps(out, indent=2) + "\n")

    # Console summary (short, human-readable)
    print(f"identity(2) max defect : {out['max_identity_defect']:.2e}")
    print(f"integral(9-10) max def : {out['max_integral_defect']:.2e}")
    print(f"BD identity max defect : {out['max_BD_identity_defect']:.2e}")
    print(f"RB identity max defect : {out['max_RB_identity_defect']:.2e}")
    for ns in ["27", "49", "121", "200"]:
        c = out["cases"][ns]
        print(f"N={ns}: E3={c['E3_Efrac_float']:.6f} refutes_eq3={c['E3_refutes_eq3']} "
              f"Y={c['Y_exact']} sq={c['N_is_prime_power']}")
    for ns in ["400", "1000", "10000", "100000"]:
        c = out["cases"][ns]
        print(f"N={ns}: (A-log!)/N={c['A_minus_logfact_over_N']:.4f} "
              f"Rb/sqrtN={c['R_boundary_over_sqrtN']:.3f} "
              f"Tbl/sqrtN={c['T_bilinear_over_sqrtN']:.3f} "
              f"|R|sum/N34={c['sum_abs_R_over_N34']:.3f}")
    for tag, blk in out["spectral"].items():
        for ns, r in blk["rows"].items():
            print(f"SP {tag} N={ns}: |B|={r['bracket_abs']:.4f} "
                  f"K^-b={r['memo_claimed_scale_K_minus_beta']:.4f} "
                  f"ratio={r['ratio_bracket_over_claimed']:.2f}")
    return out


if __name__ == "__main__":
    main()
