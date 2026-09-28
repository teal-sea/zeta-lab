"""Re-run the ball LDL^T inertia at doubled precision for zeta_pole cells
whose first factorization was inconclusive (large c at N = 128, where 1600
bits ran out), so every reported inertia is conclusive or marked otherwise.

Usage: zeta_pole_fixup.py N   (edits zeta_pole_N<N>.json in place)
"""

from __future__ import annotations

import os
import sys
from fractions import Fraction

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import wp_common as W  # noqa: E402
from flint import ctx  # noqa: E402

N = int(sys.argv[1])
PATH = os.path.join(W.HERE, f"zeta_pole_N{N}.json")


def main():
    from flint import arb_mat

    d = W.load(PATH, None)
    for k, rec in sorted(d["cells"].items(), key=lambda kv: Fraction(kv[0])):
        todo = [f for f in ("inertia_full_at_0", "inertia_polefree_at_0") if not rec[f][2]]
        if not todo:
            continue
        prec = 2 * d["meta"]["ldl_prec"]
        for _ in range(2):
            bt = W.EN.BallTruncation(W.cq(Fraction(k)), N, kind="zeta", prec=prec)
            ctx.prec = prec
            E = arb_mat(bt.even_matrix())
            mats = {"inertia_full_at_0": E, "inertia_polefree_at_0": E - W.components(bt, check=False)["pole"]}
            res = {f: W.ldl_signs(mats[f]) for f in todo}
            if all(r[2] for r in res.values()):
                break
            prec *= 2
        for f, r in res.items():
            rec[f] = list(r)
            rec[f + "_prec"] = prec
        W.save(PATH, d)
        print(k, {f: r for f, r in res.items()}, prec, flush=True)


if __name__ == "__main__":
    main()
