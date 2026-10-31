"""exact_gram/: the measured price of one block of the exact-Gram rebuild (RUNS.md s1, s2).

The rebuild (PREREG.md s1) recomputes Delta_T at (nvec, N) = (280, 32) with
the exact projections (Gram matrices in v-space, never from s-samples) as
python-flint ball matrices. Its unit of work and of checkpoint is an
s-block: BLOCK s-nodes of the Gauss grid on s >= 0 (the modes are real, so
rho(-s) = rho(s)), every w-node of the hat quadrature, and the 280 modes.
Per block the work is

  (P) the phase matrices cos(s log w), sin(s log w): BLOCK x nw elementwise
      arb calls (Python level, the dominant cost);
  (H) the per-level hat partials: two real ball products (BLOCK x nw) by
      (nw x 280), cut at the dyadic levels, from which both zeta^ and b^
      follow (ta_prolate.hats_modes, the same algebra in balls);
  (R) rho for both families against the Cholesky factors of the exact Grams;
  (M) the window sums for the three cells.

This script runs (P) and (H) for one real block of the 280-mode grid (the
block at the top of s >= 0, the stored S of the (280, 2266) build) over the
full w-range in chunks, at 133 and 200 bits (dps 40 and 60), with synthetic
mode values: timing does not depend on the values, and the real values are a
one-time cost priced separately here ((B) Bessel table, (E) prolate
eigensolve). (R) and (M) are timed on one block's shapes. Measured grade:
timings on a shared box, load average recorded; nothing here is a number
about Delta_T.

    nice -n 10 <venv python> hunts/weil_propagation/c4_s2/exact_gram/price_block.py   # about 10 min
"""

from __future__ import annotations

import json
import math
import os
import random
import sys
import time

HERE = os.path.dirname(os.path.abspath(__file__))
TWO_ADIC = os.path.normpath(os.path.join(HERE, "..", "two_adic"))
KERNEL = os.path.normpath(os.path.join(HERE, "..", "kernel"))
for p in (TWO_ADIC, KERNEL):
    if p not in sys.path:
        sys.path.insert(0, p)

import ta_mellin as TM  # noqa: E402  (two_adic/, read-only)
import ta_prolate as TP  # noqa: E402  (two_adic/, read-only)
from flint import arb, arb_mat, acb, acb_mat, ctx  # noqa: E402

OUT = os.path.join(HERE, "price_block.json")
NVEC, N = 280, 32
KMAX = TP.kmax_for(NVEC)  # 14
S_STORED = 2266.1020257693895  # the (280, 2266) build, bound_quad/ BUILDS
S_WIDE = 10000.0  # PREREG s1 option (b): crude E1 below 7e-4 without a tail-mass lemma
S_WIDTH, S_PER_PANEL = 0.5, 8  # PREREG s1: panels half the stored width
BLOCK = 128
WCHUNK = 8192
LEGENDRE_DIM = NVEC + 45  # kernel/sonin.prolate_vectors: Kdim = nvec + 45 even orders
BITS = (133, 200)  # dps 40 and 60


def rss_gib() -> float:
    with open("/proc/self/status") as fh:
        for ln in fh:
            if ln.startswith("VmRSS:"):
                return int(ln.split()[1]) / 2**20
    return float("nan")


def s_nodes_nonneg(S: float) -> int:
    return int(round(S / S_WIDTH)) * S_PER_PANEL


def w_grid(S: float):
    w, wt, level = TM.w_nodes(KMAX, S, 12)
    return w, wt, level


def time_block(bits: int, w, level) -> dict:
    """(P) and (H) for the top block of s >= 0 on the stored grid, all w."""
    ctx.prec = bits
    xg = [0.5 * (1 + x) for x in __import__("numpy").polynomial.legendre.leggauss(S_PER_PANEL)[0]]
    top = S_STORED - BLOCK // S_PER_PANEL * S_WIDTH
    s = [arb(top + S_WIDTH * (j // S_PER_PANEL) + S_WIDTH * xg[j % S_PER_PANEL]) for j in range(BLOCK)]
    rnd = random.Random(1)
    Fc = arb_mat(WCHUNK, NVEC, [arb(rnd.uniform(-1, 1)) for _ in range(WCHUNK * NVEC)])  # reused
    nw = len(w)
    t_phase = t_mm = 0.0
    parts = {}
    for i0 in range(0, nw, WCHUNK):
        i1 = min(i0 + WCHUNK, nw)
        # cut the chunk at dyadic level boundaries (per-level partials, as hats_modes)
        cuts = [i0] + [i for i in range(i0 + 1, i1) if level[i] != level[i - 1]] + [i1]
        for a, b in zip(cuts[:-1], cuts[1:]):
            lw = [arb(float(x)).log() for x in w[a:b]]
            t = time.perf_counter()
            cs = [(sj * l).sin_cos() for sj in s for l in lw]
            C = arb_mat(BLOCK, b - a, [x[1] for x in cs])
            Sn = arb_mat(BLOCK, b - a, [x[0] for x in cs])
            t_phase += time.perf_counter() - t
            Fp = Fc if b - a == WCHUNK else arb_mat(b - a, NVEC, [Fc[i, j] for i in range(b - a) for j in range(NVEC)])
            t = time.perf_counter()
            pc, ps = C * Fp, Sn * Fp
            t_mm += time.perf_counter() - t
            k = int(level[a])
            if k in parts:
                parts[k] = (parts[k][0] + pc, parts[k][1] + ps)
            else:
                parts[k] = (pc, ps)
    return {"bits": bits, "nw": nw, "block_s_nodes": BLOCK, "phase_s": t_phase, "matmul_s": t_mm,
            "seconds_per_phase": t_phase / (BLOCK * nw), "seconds_per_real_madd": t_mm / (2 * BLOCK * nw * NVEC),
            "levels": len(parts), "rss_gib_after": rss_gib()}


def time_rho_and_window(bits: int) -> dict:
    """(R) one block's rho for two families, (M) one block's window sums for three cells."""
    ctx.prec = bits
    rnd = random.Random(2)
    A = arb_mat(NVEC, NVEC, [arb(rnd.uniform(-1, 1)) for _ in range(NVEC * NVEC)])
    G = A.transpose() * A + arb_mat(NVEC, NVEC, [arb(NVEC) if i == j else arb(0) for i in range(NVEC) for j in range(NVEC)])
    H = arb_mat(NVEC, BLOCK, [arb(rnd.uniform(-1, 1)) for _ in range(NVEC * BLOCK)])
    t = time.perf_counter()
    X = G.solve(H)  # LU per call: an upper estimate of a reused Cholesky
    t_solve = time.perf_counter() - t
    t = time.perf_counter()
    rho = [sum((H[i, j] * X[i, j] for i in range(NVEC)), arb(0)) for j in range(BLOCK)]
    t_rho = time.perf_counter() - t
    t = time.perf_counter()
    for c in (2.2, 2.5, 2.9):
        L = arb(c).log()
        V = acb_mat(2 * N + 1, BLOCK, [((acb(0, 1) * (2 * arb.pi() * n / L - arb(1000.25)) * L).exp() - 1)
                                       / (acb(0, 1) * (2 * arb.pi() * n / L - arb(1000.25)))
                                       for n in range(-N, N + 1) for _ in range(BLOCK)])
        W = acb_mat(BLOCK, 2 * N + 1, [V[j, i].conjugate() * rho[i] for i in range(BLOCK) for j in range(2 * N + 1)])
        _ = V * W
    t_win = time.perf_counter() - t
    # per family: one solve and one rho; two families
    return {"bits": bits, "rho_two_families_s": 2 * (t_solve + t_rho), "window_three_cells_s": t_win}


def time_bessel(bits: int, xs=(2 * math.pi * 1.5, 2 * math.pi * 900.0, 2 * math.pi * 16000.0)) -> dict:
    """(B) one node's spherical Bessel table j_0 .. j_{2 Kdim} by upward recurrence (stable for x > order)
    or arb's j at x below the order range; recorded per node."""
    ctx.prec = bits
    kmax = 2 * LEGENDRE_DIM
    out = []
    for x in xs:
        z = arb(x)
        t = time.perf_counter()
        if x > kmax:
            j0, j1 = z.sin() / z, z.sin() / z**2 - z.cos() / z
            vals = [j0, j1]
            for k in range(1, kmax):
                vals.append((2 * k + 1) / z * vals[k] - vals[k - 1])
        else:
            vals = [(arb.pi() / (2 * z)).sqrt() * z.bessel_j(arb(k) + arb(0.5)) for k in range(0, kmax + 1, 2)]
        out.append({"x": x, "seconds": time.perf_counter() - t, "orders": len(vals)})
    return {"bits": bits, "per_node": out}


def time_eigensolve(dps: int, nvec: int) -> dict:
    import sonin  # kernel/, read-only

    t = time.perf_counter()
    sonin.prolate_vectors(dps, 0, nvec)
    return {"dps": dps, "nvec": nvec, "seconds": time.perf_counter() - t}


def main() -> None:
    old = ctx.prec
    w, wt, level = w_grid(S_STORED)
    w_wide = TM.w_nodes(KMAX, S_WIDE, 12)[0]
    out = {"meta": {"load_average_start": os.getloadavg(), "flint_threads": ctx.threads, "nvec": NVEC, "N": N,
                    "Kmax": KMAX, "s_width": S_WIDTH, "s_per_panel": S_PER_PANEL, "block": BLOCK, "wchunk": WCHUNK,
                    "grids": {"stored_S": {"S": S_STORED, "nw": int(w.size), "s_nodes_nonneg": s_nodes_nonneg(S_STORED)},
                              "wide_S": {"S": S_WIDE, "nw": int(w_wide.size), "s_nodes_nonneg": s_nodes_nonneg(S_WIDE)}}}}
    out["block"] = [time_block(b, w, level) for b in BITS]
    out["rho_window"] = [time_rho_and_window(b) for b in BITS]
    out["bessel"] = [time_bessel(b) for b in BITS]
    out["eigensolve"] = [time_eigensolve(40, n) for n in (60, 120)]
    out["meta"]["load_average_end"] = os.getloadavg()
    ctx.prec = old
    with open(OUT, "w") as fh:
        json.dump(out, fh, indent=1)
    print(json.dumps(out, indent=1))


if __name__ == "__main__":
    main()
