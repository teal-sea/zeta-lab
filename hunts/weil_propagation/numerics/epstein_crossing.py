"""First window where the Epstein (1,1,6) form goes negative, per (N, sector).

Bracket from the scan (epstein_N<N>.json: last hardened-positive and first
hardened-negative half-integer c), then bisection over dyadic c to 2^-10 on
the sign from ball LDL^T inertia at 0 (conclusive, so every step is itself a
hardened sign), and at the negative end a ball Rayleigh quotient upper bound
< 0 as a second, independent rigorous route. Dedekind control at the negative
end, same N and sector: ball LDL^T inertia (positive definite expected).

By Fact B (RESULTS s0) a hardened negative cell (c, N) makes the continuum
Epstein form negative on every window c' >= c. Writes epstein_crossing.json.
"""

from __future__ import annotations

import json
import os
import sys
import time
from fractions import Fraction

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import wp_common as W  # noqa: E402

OUT = os.path.join(W.HERE, "epstein_crossing.json")
PREC = 400


def nneg(c: Fraction, N: int, sector: str, form=W.EPSTEIN_FORM):
    M = W.epstein_matrices(W.cq(c), N, PREC, form=form)[sector]
    npos, n, concl = W.ldl_signs(M)
    if not concl:
        raise ArithmeticError(f"inconclusive LDL at c={c}, N={N}, {sector}")
    return n, M


def key(c: Fraction) -> str:
    return str(c.numerator) if c.denominator == 1 else f"{c.numerator}/{c.denominator}"


def main():
    d = W.load(OUT, {"meta": {"note": __doc__.split("\n\n")[0], "prec": PREC}, "runs": {}})
    for N in (64, 128):
        scan = json.load(open(os.path.join(W.HERE, f"epstein_N{N}.json")))["cells"]
        cs = sorted(scan, key=Fraction)
        for sector in ("odd", "even"):
            rk = f"{N}|{sector}"
            if rk in d["runs"]:
                continue
            t0 = time.time()
            first = next(k for k in cs if scan[k][sector]["inertia_at_0"][1] > 0)
            later_pos = [k for k in cs if Fraction(k) > Fraction(first) and scan[k][sector]["inertia_at_0"][1] == 0]
            lo, hi = Fraction(first) - Fraction(1, 2), Fraction(first)
            assert scan[key(lo)][sector]["inertia_at_0"][1] == 0
            path = []
            for _ in range(10):
                mid = (lo + hi) / 2
                n, _ = nneg(mid, N, sector)
                path.append([key(mid), n])
                if n > 0:
                    hi = mid
                else:
                    lo = mid
            n_hi, M = nneg(hi, N, sector)
            l1 = W.approx_spectrum(M, 1)[0]
            r1, _ = W.eig_near(M, l1)
            n_lo, _ = nneg(lo, N, sector)
            n_ded, _ = nneg(hi, N, sector, form="dedekind-23")
            rec = {
                "c_pos": key(lo), "c_pos_float": float(lo), "n_neg_at_c_pos": n_lo,
                "c_neg": key(hi), "c_neg_float": float(hi), "n_neg_at_c_neg": n_hi,
                "lam1_at_c_neg": W.as_str(r1, 10), "rq_upper_at_c_neg": r1.upper().str(10, radius=False),
                "hardened_negative_two_routes": bool(n_hi > 0 and r1.upper() < 0),
                "dedekind_n_neg_at_c_neg": n_ded,
                "positive_grid_cells_after_first_negative": later_pos,
                "path": path, "elapsed_s": round(time.time() - t0, 1),
            }
            d["runs"][rk] = rec
            W.save(OUT, d)
            print(rk, {k: rec[k] for k in ("c_pos_float", "c_neg_float", "lam1_at_c_neg", "hardened_negative_two_routes",
                                           "dedekind_n_neg_at_c_neg", "positive_grid_cells_after_first_negative")},
                  rec["elapsed_s"], "s", flush=True)


if __name__ == "__main__":
    main()
