"""Precision response of the two quantities the conclusions lean on.

The mission's kill condition: a transport relation that fails an independent
precision or basis-size check is a measurement artifact. Basis size is the
N-ladder in edge.py. This script moves the precision: each quantity is
recomputed with (a) the working precision doubled and (b) the HF stencil
half-width changed by a factor 2^-24 (the only error not carried in a ball is
the O(eps^2) stencil truncation), and the relative change is recorded.

Quantities: lambda_1, mu_0, and the HF derivative d lambda/dL with its
pieces, at DH (61/2, 128), DH (125/4, 128) (past the crossing), zeta
(61/2, 64) and zeta (61/2, 128). Writes precision_check.json.
"""

from __future__ import annotations

import os
import sys
import time
from fractions import Fraction

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import wp_common as W  # noqa: E402
from flint import arb, ctx, fmpq  # noqa: E402

OUT = os.path.join(W.HERE, "precision_check.json")
CELLS = [("dh", "61/2", 128), ("dh", "125/4", 128), ("zeta", "61/2", 64), ("zeta", "61/2", 128)]


def hf_at(c, N, kind, v, k, prec):
    eps = fmpq(1, 2**k)
    parts, Ls = {}, []
    for sgn in (1, -1):
        bt = W.EN.BallTruncation(c + sgn * eps, N, kind=kind, prec=prec)
        comp = W.components(bt, check=False)
        Ls.append(bt.L)
        for name in ("pole", "arch", "prime"):
            if comp[name] is not None:
                ctx.prec = prec
                parts.setdefault(name, []).append(W.quad(comp[name], v))
    ctx.prec = prec
    dL = Ls[0] - Ls[1]
    out = {n: (a - b) / dL for n, (a, b) in parts.items()}
    out["total"] = sum(out.values(), arb(0))
    return out


def main():
    d = W.load(OUT, {"meta": {"note": __doc__.split("\n\n")[0]}, "cells": {}})
    for kind, cs, N in CELLS:
        key = f"{kind}|{cs}|{N}"
        if key in d["cells"]:
            continue
        t0 = time.time()
        c = W.cq(Fraction(cs))
        p0 = W.prec_for(kind, N)
        k0, hp0 = W.hf_eps_prec(kind, N)
        runs = {}
        for tag, p, k, hp in [("base", p0, k0, hp0), ("prec_x2", 2 * p0, k0, 2 * hp0), ("eps_x2^-24", p0, k0 + 24, hp0 + 200)]:
            _, A = W.build(c, N, kind, prec=p)
            (r1, v1), _ = W.lowest_pairs(A, 2)
            h = hf_at(c, N, kind, v1, k, hp)
            runs[tag] = {"lam1": r1, "mu0": W.mu0(v1), "hf": h["total"]}
        base = runs["base"]
        rec = {"kind": kind, "c": cs, "N": N}
        for tag in ("prec_x2", "eps_x2^-24"):
            rec[tag] = {q: float(abs((runs[tag][q] - base[q]) / base[q]).mid()) for q in ("lam1", "mu0", "hf")}
        rec["base"] = {q: base[q].str(12) for q in ("lam1", "mu0", "hf")}
        rec["elapsed_s"] = round(time.time() - t0, 1)
        d["cells"][key] = rec
        W.save(OUT, d)
        print(key, rec["prec_x2"], rec["eps_x2^-24"], rec["elapsed_s"], flush=True)


if __name__ == "__main__":
    main()
