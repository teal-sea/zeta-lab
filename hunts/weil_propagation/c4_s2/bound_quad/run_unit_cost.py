"""bound_quad/: the measured unit of route (ii) (DERIVATION s1, s2.8), written to bound_quad_unit.json.

One unit is one (s, w) pair of the b-hat quadrature in arb: the weighted phase
w^{-1/2-is} wt at 106 bits, and the ball product of a row of such phases
against the mode columns (acb_mat, 2000 w-nodes by 80 modes). Also recorded:
the node counts of the stored grids (two_adic/ta_mellin.w_nodes and s_grid,
read-only import), the laptop's load average (a timing under load is an
upper estimate), and the per-build extrapolation
pairs x (phase + nvec x product), in core-seconds. Estimate only.
"""

from __future__ import annotations

import json
import math
import os
import sys
import time

HERE = os.path.dirname(os.path.abspath(__file__))
TWO_ADIC = os.path.normpath(os.path.join(HERE, "..", "two_adic"))
if TWO_ADIC not in sys.path:
    sys.path.insert(0, TWO_ADIC)

import ta_mellin as TM  # noqa: E402  (two_adic/, read-only)
from flint import acb, acb_mat, arb, ctx  # noqa: E402

OUT = os.path.join(HERE, "bound_quad_unit.json")
GRIDS = [(80, 1200.0, 10), (280, 2266.1020257693895, 14), (364, 3060.0807085398565, 15)]


def main() -> None:
    old = ctx.prec
    ctx.prec = 106
    w, wt, _ = TM.w_nodes(10, 1200.0, 12)
    w, wt = w[:2000], wt[:2000]
    s = acb(0.5, -777.0)
    t = time.perf_counter()
    ph = [(acb(float(x)).log() * (-s)).exp() * arb(float(y)) for x, y in zip(w, wt)]
    t_phase = (time.perf_counter() - t) / len(ph)
    cols = acb_mat(2000, 80)
    t = time.perf_counter()
    acb_mat([ph]) * cols
    t_prod = (time.perf_counter() - t) / (2000 * 80)
    ctx.prec = old
    grids = []
    for nvec, S, K in GRIDS:
        s_nodes = TM.s_grid(S, width=1.0, per_panel=8)[0]
        nw = int(TM.w_nodes(K, float(abs(s_nodes).max()), 12)[0].size)  # as hats_modes calls it
        ns = int(s_nodes.size)
        pairs = nw * ns
        grids.append({"nvec": nvec, "S": S, "Kmax": K, "w_nodes": nw, "s_nodes": ns, "pairs": pairs,
                      "core_seconds_estimate": pairs * (t_phase + nvec * t_prod)})
    out = {"prec_bits": 106, "seconds_per_phase": t_phase, "seconds_per_pair_mode_product": t_prod,
           "load_average": os.getloadavg(), "grids": grids,
           "usd_per_core_hour": 0.0473, "usd_rate_source": "modal/run_modal_rho.py RATE_CORE_S (modal billing rates, 2026-09-24)"}
    with open(OUT, "w") as fh:
        json.dump(out, fh, indent=1)
    print(json.dumps(out, indent=1))


if __name__ == "__main__":
    main()
