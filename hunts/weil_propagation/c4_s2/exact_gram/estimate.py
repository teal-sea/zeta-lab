"""exact_gram/: the rebuild and sweep estimates from the measured block (RUNS.md s2, s3).

Reads price_block.json, writes estimate.json. Scaling rules (stated, not
measured): the phase cost of a block is proportional to its w-node count nw
and independent of nvec; the hat products to nw * nvec; rho to nvec^2 (an
upper estimate from a 280 x 280 LU per block); the window sums to (2N + 1)^2
summed over the N of the build. Grids: two_adic's own rules, Kmax =
kmax_for(nvec) and w_nodes(Kmax, S', 12), s-panels as PREREG s1; S' is the
smallest S' (to 100) at which bound_quad/'s crude E1 is at most E1_TARGET
for that (nvec, N) at c = 2.9. One-time terms: the mode table (one Bessel
table per w-node, plus 14 per v-node of the G_b quadrature, an upper
count), the eigensolve (scaled as nvec^3 from the measured 120), the Gram
products. Estimate grade; nothing here is a number about Delta_T.

    <venv python> hunts/weil_propagation/c4_s2/exact_gram/estimate.py   # seconds
"""

from __future__ import annotations

import json
import math
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
for sub in ("two_adic", "bound_quad"):
    p = os.path.normpath(os.path.join(HERE, "..", sub))
    if p not in sys.path:
        sys.path.insert(0, p)

import eps_quad as E  # noqa: E402  (bound_quad/, read-only)
import ta_mellin as TM  # noqa: E402  (two_adic/, read-only)
import ta_prolate as TP  # noqa: E402  (two_adic/, read-only)

PRICE = os.path.join(HERE, "price_block.json")
OUT = os.path.join(HERE, "estimate.json")
E1_TARGET = 7.0e-4  # PREREG s1: the registered S' = 1e4 gives 6.97e-4 at (280, 32)
REPLAY_EVERY = 16  # PREREG s4
GB_V_LEVELS = 14  # dyadic terms per v-node in the G_b quadrature (upper count)
BUILDS = [  # (name, nvec, N values carried by the window sums)
    ("rebuild_280", 280, (8, 16, 32)),
    ("sweep_364", 364, (8, 16, 32)),
    ("sweep_500", 500, (8, 16, 32)),
    ("sweep_700", 700, (8, 16, 32)),
    ("sweep_700_N64", 700, (8, 16, 32, 64)),
]


def s_prime(nvec: int, N: int) -> float:
    S = 100.0
    while float((E.kappa(2.9, N, S) * nvec).upper()) > E1_TARGET:
        S += 100.0
    return S


def build_estimate(price: dict, bits: int, nvec: int, Ns) -> dict:
    blk = next(b for b in price["block"] if b["bits"] == bits)
    rw = next(r for r in price["rho_window"] if r["bits"] == bits)
    bes = next(b for b in price["bessel"] if b["bits"] == bits)
    m = price["meta"]
    S = s_prime(nvec, max(Ns))
    K = TP.kmax_for(nvec)
    nw = int(TM.w_nodes(K, S, 12)[0].size)
    blocks = math.ceil(int(round(S / m["s_width"])) * m["s_per_panel"] / m["block"])
    f_nw = nw / blk["nw"]
    t_block = (blk["phase_s"] * f_nw + blk["matmul_s"] * f_nw * nvec / m["nvec"]
               + rw["rho_two_families_s"] * (nvec / m["nvec"]) ** 2
               + rw["window_three_cells_s"] * sum((2 * n + 1) ** 2 for n in Ns) / (2 * m["N"] + 1) ** 2)
    t_node = max(x["seconds"] for x in bes["per_node"] if x["x"] > 2 * (m["nvec"] + 45))
    nv_nodes = int(TM.w_nodes(K, 0.0, 12)[0].size)
    eig = next(e for e in price["eigensolve"] if e["nvec"] == 120)["seconds"] * (nvec / 120) ** 3
    one_time = (nw + GB_V_LEVELS * nv_nodes) * t_node * (nvec + 45) / (m["nvec"] + 45) + eig
    total = blocks * t_block + one_time
    return {"bits": bits, "nvec": nvec, "N": list(Ns), "S_prime": S, "Kmax": K, "nw": nw, "blocks": blocks,
            "block_core_s": t_block, "one_time_core_s": one_time, "core_hours": total / 3600.0}


def main() -> None:
    price = json.load(open(PRICE))
    out = {"e1_target": E1_TARGET, "replay_every": REPLAY_EVERY, "builds": {}}
    for name, nvec, Ns in BUILDS:
        lo = build_estimate(price, 133, nvec, Ns)
        hi = build_estimate(price, 200, nvec, Ns)
        replay_h = math.ceil(lo["blocks"] / REPLAY_EVERY) * hi["block_core_s"] / 3600.0
        out["builds"][name] = {"dps40": lo, "dps60": hi, "replay_core_hours": replay_h,
                               "production_core_hours": lo["core_hours"] + replay_h}
    with open(OUT, "w") as fh:
        json.dump(out, fh, indent=1)
    print(json.dumps(out, indent=1))


if __name__ == "__main__":
    main()
