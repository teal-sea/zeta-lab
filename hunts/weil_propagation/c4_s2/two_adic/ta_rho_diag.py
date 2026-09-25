"""Follow-up 3, step 1: where the condition of the rho Gram matrices comes from.

Written and run before any change to ta_mellin.rho. Writes ta_rho_diag.json.

T_S's Gram matrices are not gram_v's: ta_prolate.delta_T_cells takes both on
the s side (gram_s), G = (1/2pi) H^* W_s H + (J J^T + dil A A^T) / (pi S),
from the hats H on s_grid(S, width 1, per_panel 8) (ta_mellin.gram_v serves
only the synthetic route delta_T_mellin). Such a G is F^* F for the factor

    F = [ sqrt(w_s / 2pi) H^T ; sqrt(1/(pi S)) J ; sqrt(dil/(pi S)) A ],

so cond(G) = cond(F)^2. This file measures, per part (one process each):

  scan80 / scan200   cond(G_z), cond(G_b) against the cutoff S at fixed nvec,
                     S restricted from one s-grid (its panels are unit
                     intervals, so |s| <= S' is exactly s_grid(S')): both as
                     the float64 eigenvalue ratio of the formed G and as
                     cond(F)^2 from the singular values of F (reliable while
                     cond(F) is well below 1/eps);
  refine             cond at nvec 80, S 300 under a finer s-grid, a finer
                     w-grid (hats' per_panel), Kmax + 1, and S doubled;
  lowdir             where the lowest direction of G_b lives in s (80, 1200);
  hats               float64 hats against kernel/'s closed form
                     (zeta_mellin_all, dps 30), the sample error delta;
  nodes              node counts for the N = 32 rows (s-grid, hats' w-grid,
                     gram_v's w-grid) against nvec.

The exact Gram matrices, for comparison (derivation, unreviewed): the zeta_n
are orthonormal on v >= 1 (zeta_n = (1 - P) F xi_n / sqrt(1 - lam_n^2),
xi_n prolate), so G_z = I. b_n = K zeta_n with K the compression of
Theta^{*-1} = sum_k a^k D^{-k} (|a| = 2^{-1/2}) to x >= 0; D^{-1} maps
x < 0 into x < 0, so compression is multiplicative on power series in D^{-1},
K = (1 - a T)^{-1} with T the compressed D^{-1}, ||T|| <= 1, and
sigma(K) lies in [1/(1 + 2^{-1/2}), 1/(1 - 2^{-1/2})]. Hence
cond(G_b exact) <= ((1 + 2^{-1/2}) / (1 - 2^{-1/2}))^2 cond(G_z exact) = 33.97.
Float64 throughout (the closed form at dps 30): measured grade.
"""

from __future__ import annotations

import json
import math
import os
import sys
import time

import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
if HERE not in sys.path:
    sys.path.insert(0, HERE)

import ta_mellin as TM  # noqa: E402
import ta_prolate as TP  # noqa: E402

OUT = os.path.join(HERE, "ta_rho_diag.json")
TOEPLITZ = ((1 + 2**-0.5) / (1 - 2**-0.5)) ** 2
N32_ROWS = ((200, 2400.0), (240, 2400.0), (280, 2266.0), (319, 2633.0), (364, 3060.0))


def factor(H, sw, J, A, S, dil):
    """F with F^* F = ta_prolate.gram_s(H, sw, J, S, A, dil)."""
    return np.vstack([(H * np.sqrt(sw / TM.TWO_PI)).T, math.sqrt(1 / (math.pi * S)) * J[None, :],
                      math.sqrt(dil / (math.pi * S)) * A[None, :]])


def conds(H, sw, J, A, S, dil) -> dict:
    e = np.linalg.eigvalsh(TP.gram_s(H, sw, J, S, A, dil))
    sv = np.linalg.svd(factor(H, sw, J, A, S, dil), compute_uv=False)
    return {"eig_min": float(e[0]), "eig_max": float(e[-1]), "cond_formed": float(e[-1] / abs(e[0])),
            "cond_F": float(sv[0] / sv[-1]), "cond_F_sq": float((sv[0] / sv[-1]) ** 2)}


def hats(nvec, S, spp=8, wpp=12, Kmax=None):
    pm = TP.ProlateModes(nvec=nvec, dps=20)
    s, sw = TM.s_grid(S, width=1.0, per_panel=spp)
    Z, B = TP.hats_modes(pm, s, 1.0, Kmax=Kmax, per_panel=wpp)
    jz, jb = TP.jumps(pm, 1.0)
    return pm, s, sw, Z, B, jz, jb, pm.derivs[:, 0] * pm.norm


def scan(nvec, Smax, subs, npz=None) -> dict:
    """cond against S' <= Smax from one s-grid. npz: hats saved from the identical
    call TP.hats_modes(ProlateModes(nvec, 20), s_grid(Smax, 1, 8), 1.0)."""
    t0 = time.time()
    if npz:
        d = np.load(npz)
        s, sw, Z, B, jz, jb, A = (d[k] for k in ("s", "sw", "Z", "B", "jz", "jb", "A"))
        src = "hats loaded from a saved run of the identical call"
    else:
        _, s, sw, Z, B, jz, jb, A = hats(nvec, Smax)
        src = "computed here"
    rows = []
    for S in subs:
        m = np.abs(s) <= S + 1e-9
        rows.append({"S": S, "S_over_nvec2": S / nvec**2,
                     "z": conds(Z[:, m], sw[m], jz, A, S, 1.0), "b": conds(B[:, m], sw[m], jb, A, S, 2.0)})
    return {"nvec": nvec, "Smax": Smax, "Kmax": TP.kmax_for(nvec), "hats": src,
            "seconds": round(time.time() - t0, 1), "rows": rows}


def refine(nvec=80, S=300.0) -> dict:
    kb = TP.kmax_for(nvec)
    out = []
    for label, spp, wpp, K, SS in (("base", 8, 12, kb, S), ("s_per_panel_12", 12, 12, kb, S),
                                   ("w_per_panel_16", 8, 16, kb, S), ("Kmax_plus_1", 8, 12, kb + 1, S),
                                   ("S_doubled", 8, 12, kb, 2 * S)):
        _, s, sw, Z, B, jz, jb, A = hats(nvec, SS, spp, wpp, K)
        out.append({"label": label, "s_per_panel": spp, "w_per_panel": wpp, "Kmax": K, "S": SS,
                    "z": conds(Z, sw, jz, A, SS, 1.0), "b": conds(B, sw, jb, A, SS, 2.0)})
    return {"nvec": nvec, "S": S, "rows": out}


def lowdir(nvec=80, S=1200.0) -> dict:
    _, s, sw, Z, B, jz, jb, A = hats(nvec, S)
    w, U = np.linalg.eigh(TP.gram_s(B, sw, jb, S, A, 2.0))
    u = U[:, 0]
    e = np.abs(u @ B) ** 2 * sw / TM.TWO_PI
    bands = {}
    for lo, hi in ((0, 100), (100, 500), (500, 1000), (1000, S)):
        m = (np.abs(s) >= lo) & (np.abs(s) < hi + (1e-9 if hi == S else 0))
        bands[f"{lo}-{int(hi)}"] = float(e[m].sum())
    return {"nvec": nvec, "S": S, "eig_min": float(w[0]), "energy_by_abs_s": bands,
            "abs_A_dot_u": float(abs(A @ u)), "abs_J_dot_u": float(abs(jb @ u)),
            "weight_top_decile_modes": float(np.sum(np.abs(u[int(0.9 * nvec):]) ** 2))}


def hats_accuracy(nvec=80, nodes=(0.0, 3.7, 41.0, -149.8125, 600.4, -2399.9)) -> dict:
    pm = TP.ProlateModes(nvec=nvec, dps=20)
    ss = np.array(nodes)
    Z, _ = TP.hats_modes(pm, ss, 1.0)
    rel, ab = 0.0, 0.0
    per = []
    for j, s0 in enumerate(ss):
        ref = np.array([complex(x) for x in TP.sonin.zeta_mellin_all(float(s0), 30, 0, nvec)])
        d = np.abs(Z[:, j] - ref)
        per.append({"s": float(s0), "max_abs": float(d.max()), "max_rel": float(d.max() / np.abs(ref).max())})
        rel, ab = max(rel, per[-1]["max_rel"]), max(ab, per[-1]["max_abs"])
    return {"nvec": nvec, "dps": 30, "Kmax": TP.kmax_for(nvec), "nodes": per, "max_rel": rel, "max_abs": ab}


def node_counts() -> list:
    out = []
    for nvec, S in N32_ROWS:
        K = TP.kmax_for(nvec)
        s, _ = TM.s_grid(S, width=1.0, per_panel=8)
        w, _, _ = TM.w_nodes(K, S, 12)
        wv, _, _ = TM.w_nodes(14, 0.0, 12)
        out.append({"nvec": nvec, "S": S, "Kmax": K, "S_over_nvec2": S / nvec**2, "s_nodes": int(s.size),
                    "hats_w_nodes": int(w.size), "gram_v_w_nodes": int(wv.size)})
    return out


def main(argv=None):
    argv = sys.argv[1:] if argv is None else argv
    try:
        with open(OUT) as fh:
            out = json.load(fh)
    except (OSError, ValueError):
        out = {}
    out["toeplitz_cond_ratio"] = TOEPLITZ
    part = argv[0]
    if part == "scan80":
        out["scan80"] = scan(80, 2400.0, (150.0, 200.0, 300.0, 600.0, 1200.0, 2400.0))
    elif part == "scan200":
        out["scan200"] = scan(200, 2400.0, (300.0, 600.0, 1200.0, 2400.0), argv[1] if len(argv) > 1 else None)
    elif part == "refine":
        out["refine"] = refine()
    elif part == "lowdir":
        out["lowdir"] = lowdir()
    elif part == "hats":
        out["hats_accuracy"] = hats_accuracy()
    elif part == "nodes":
        out["node_counts"] = node_counts()
    with open(OUT, "w") as fh:
        json.dump(out, fh, indent=1)
    return out


if __name__ == "__main__":
    main()
