"""Basis-size check of Fact A (zero extension preserves the form exactly).

Fact A says the zero-extended ground state f_c has the same continuum energy
at any larger window c'. At N' = N the band-N projection of the zero-extended
vector showed RQ_{c'}(G^T v) - lambda(c) as large as the lambda changes being
measured (grid_*.json, "rq_minus_lam_c"). If that deviation is the projection
(truncating a function with jumps at the inner-window edges), it must shrink
as N' grows, roughly like (jump^2) log N' / N'. If it plateaus, the assembly
carries a window-dependent term and Fact A fails for it.

For each (kind, c, N, c'): v = ground state at (c, N); for N' in a ladder,
w = G(c,N; c',N')^T v, record ||w||^2 and RQ_{c'}(w) - lambda(c) (balls).
Writes factA_check.json.
"""

from __future__ import annotations

import os
import sys
import time
from fractions import Fraction

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import wp_common as W  # noqa: E402

OUT = os.path.join(W.HERE, "factA_check.json")
CASES = [("dh", "30", 64, "31"), ("dh", "30", 128, "31"), ("dh", "61/2", 128, "63/2"), ("zeta", "30", 64, "31")]
LADDER = [64, 128, 256, 384]
EXTRA = {"dh|30|64|31": [512, 768, 1024]}


def main():
    d = W.load(OUT, {"meta": {"note": __doc__.split("\n\n")[0]}, "cases": {}})
    for kind, cs, N, c2s in CASES:
        key = f"{kind}|{cs}|{N}|{c2s}"
        rec = d["cases"].setdefault(key, {"rows": {}})
        c, c2 = W.cq(Fraction(cs)), W.cq(Fraction(c2s))
        _, A = W.build(c, N, kind)
        (r1, v1), _ = W.lowest_pairs(A, 2)
        rec["lam_c"] = W.as_str(r1, 14)
        for N2 in LADDER + EXTRA.get(key, []):
            if str(N2) in rec["rows"] or N2 < N:
                continue
            t0 = time.time()
            _, A2 = W.build(c2, N2, kind, prec=W.prec_for(kind, max(N2, N)))
            G = W.gram_zero_ext(c, N, c2, N2)
            w = G.transpose() * v1
            nw = W.dot(w, w)
            dev = W.rq(A2, w) - r1
            rec["rows"][str(N2)] = {
                "one_minus_proj_norm2": (1 - nw).str(6),
                "rq_minus_lam_c": dev.str(8),
                "rel_to_lam_c": float((dev / r1).mid()),
                "elapsed_s": round(time.time() - t0, 1),
            }
            W.save(OUT, d)
            print(f"{key} N'={N2}: 1-|w|^2 {(1 - nw).str(4)} RQ-lam {dev.str(6)} rel {float((dev / r1).mid()):.4g} "
                  f"[{time.time() - t0:.1f}s]", flush=True)


if __name__ == "__main__":
    main()
