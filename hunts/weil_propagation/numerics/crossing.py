"""Where between c = 30 and c = 31 the DH form first goes negative, per band N.

For each N, bisection over dyadic c in [30, 31] (10 halvings, resolution
2^-10) on the sign of lambda_min(c, N), even sector. The two ends of the
final bracket are then hardened:
  c_neg: the ball Rayleigh quotient of an exact vector has upper endpoint < 0
         (a rigorous upper bound on lambda_min);
  c_pos: ball LDL^T of the even matrix at shift 0 is conclusive with no
         negative pivot (Sylvester: positive definite).
Zeta control at c_neg, same N: ball LDL^T conclusive positive.

Why it matters (the implication is elementary, the inputs hardened): the
band-N space at window c is a subspace of L^2 on an interval of length
log c, and the continuum form is the restriction of one window-free Weil
functional, so lambda_inf(c') <= lambda(c, N) for every c' >= c and every N.
A hardened negative cell at c_neg < 31 therefore makes the continuum DH form
negative on every window c' >= c_neg, and windows in [30, 31) carry exactly
the coefficient set n <= 30.

Writes crossing.json (checkpoint per N).
"""

from __future__ import annotations

import os
import sys
import time
from fractions import Fraction

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import wp_common as W  # noqa: E402

OUT = os.path.join(W.HERE, "crossing.json")
NS = [int(x) for x in sys.argv[1:]] or [64, 96, 128, 192, 256]


def lam(c: Fraction, N: int, kind: str = "dh"):
    _, A = W.build(W.cq(c), N, kind)
    (r1, v1), (r2, _) = W.lowest_pairs(A, 2)
    return A, r1, v1, r2


def key(c: Fraction) -> str:
    return str(c.numerator) if c.denominator == 1 else f"{c.numerator}/{c.denominator}"


def ldl_positive(c: Fraction, N: int, kind: str):
    pb = W.ldl_prec(kind, N)
    for _ in range(3):
        _, A = W.build(W.cq(c), N, kind, prec=pb)
        npos, nneg, concl = W.ldl_signs(A)
        if concl:
            return {"inertia_at_0": [npos, nneg, True], "prec": pb}
        pb *= 2
    return {"inertia_at_0": [npos, nneg, False], "prec": pb // 2}


def main():
    d = W.load(OUT, {"meta": {"note": __doc__.split("\n\n")[0], "sector": "even"}, "by_N": {}})
    for N in NS:
        if str(N) in d["by_N"]:
            continue
        t0 = time.time()
        lo, hi = Fraction(30), Fraction(31)
        _, rl, _, _ = lam(lo, N)
        _, rh, _, _ = lam(hi, N)
        path = [(key(lo), W.fnum(rl)), (key(hi), W.fnum(rh))]
        if not (rl > 0 and rh < 0):
            d["by_N"][str(N)] = {"no_bracket": path}
            W.save(OUT, d)
            print(f"N={N}: no sign change on [30, 31]: {path}", flush=True)
            continue
        for _ in range(10):
            mid = (lo + hi) / 2
            _, rm, _, _ = lam(mid, N)
            path.append((key(mid), W.fnum(rm)))
            if rm.mid() < 0:
                hi = mid
            else:
                lo = mid
        # harden both ends
        A, rneg, vneg, _ = lam(hi, N)
        neg_upper = rneg.upper()
        pos = ldl_positive(lo, N, "dh")
        zeta = ldl_positive(hi, N, "zeta")
        _, rz, _, _ = lam(hi, N, "zeta")
        _, rpos, _, _ = lam(lo, N)
        rec = {
            "c_pos": key(lo), "c_pos_float": float(lo), "lam_at_c_pos": W.as_str(rpos, 12),
            "c_pos_ldl": pos,
            "c_neg": key(hi), "c_neg_float": float(hi), "lam_at_c_neg": W.as_str(rneg, 12),
            "c_neg_rq_upper": neg_upper.str(12, radius=False),
            "hardened_negative": bool(neg_upper < 0),
            "hardened_positive": bool(pos["inertia_at_0"][2] and pos["inertia_at_0"][1] == 0),
            "linear_interp_c_star": float(lo + (hi - lo) * Fraction(W.fnum(rpos)) / Fraction(W.fnum(rpos) - W.fnum(rneg))),
            "zeta_control_at_c_neg": {"ldl": zeta, "lam_min_rq": W.as_str(rz, 12)},
            "bisection_path": path,
            "elapsed_s": round(time.time() - t0, 1),
        }
        d["by_N"][str(N)] = rec
        W.save(OUT, d)
        print(f"N={N}: c* in ({rec['c_pos_float']:.6f}, {rec['c_neg_float']:.6f}] "
              f"neg_hard={rec['hardened_negative']} pos_hard={rec['hardened_positive']} "
              f"zeta={zeta['inertia_at_0']} [{rec['elapsed_s']}s]", flush=True)


if __name__ == "__main__":
    main()
