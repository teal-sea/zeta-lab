"""hunts/weil_gram/gram.py

The Gram matrix of the Weil form on a Gaussian basis, its bottom eigenvalue, and
the entrywise check that the arithmetic side equals the zero side.

    f_j = N(x_j, sigma_j^2)   (normalised)
    h_jk(r) = exp(-a2 r^2 / 2) cos(r (x_j + x_k)),  a2 = sigma_j^2 + sigma_k^2
    g_jk(u) = N(x_j + x_k, a2)(u)          (the Fourier partner of h_jk)
    M_jk = W(h_jk)          Z_jk = 2 sum_{gamma>0} h_jk(gamma)
    G_jk = <f_j, f_k>

M_jk must equal Z_jk for every entry; if it does not, the instrument is wrong.

Two bases are run:

    broad  = sigma in {0.10, 0.15, 0.20}      h has mass on many zeros
    plus1  = broad + {0.45}                   adds the degenerate direction

lambda_min on `broad` should be bounded away from zero; on `plus1` it should
collapse to the floor, which is the control: the extra element is the direction
hunts/arch_cover showed to carry no gap.

Run:  python hunts/weil_gram/gram.py     -> results.json
"""

from __future__ import annotations

import json
import os
import sys
import time

import mpmath as mp

from zeta.weil import explicit_formula_sides

DPS = 50
BASES = {
    "broad": [0.10, 0.15, 0.20],
    "plus1": [0.10, 0.15, 0.20, 0.45],
    "plus2": [0.10, 0.15, 0.20, 0.45, 0.60],
}
NOISE_FLOOR = mp.mpf("1e-25")     # eigenvalues below this are labelled noise


def pair(sj: float, sk: float, xj: float = 0.0, xk: float = 0.0):
    a2 = mp.mpf(sj) ** 2 + mp.mpf(sk) ** 2
    c = mp.mpf(xj + xk)

    def h(r):
        return mp.e ** (-a2 * r * r / 2) * mp.cos(r * c)

    def g(u):
        return mp.e ** (-((u - c) ** 2) / (2 * a2)) / mp.sqrt(2 * mp.pi * a2)

    return h, g


def gram_entry(sj: float, sk: float, dps: int = DPS) -> dict:
    t0 = time.time()
    h, g = pair(sj, sk)
    d = explicit_formula_sides(h, g, dps=dps)
    arith = mp.mpf(d["arithmetic_side"])
    zero = mp.mpf(d["zero_side"])
    scale = max(abs(arith), abs(zero), mp.mpf("1e-300"))
    return {
        "arith": arith,
        "zero": zero,
        "abs_diff": abs(arith - zero),
        "rel_diff": abs(arith - zero) / scale,
        "zero_tail_bound": mp.mpf(d["zero_side_tail_bound"]),
        "prime_tail_bound": mp.mpf(d["prime_tail_bound"]),
        # NOTE: this compares the residual against the *truncation* tails only.
        # For Gaussian h those tails are e^{-a R^2} with R = 1e4, i.e. absurdly
        # small, so the flag fires on the zero table's ~30-digit floor and is
        # uninformative except near that floor. See RESULTS.md section 1.
        "covered": abs(arith - zero)
        <= mp.mpf(d["zero_side_tail_bound"]) + mp.mpf(d["prime_tail_bound"]),
        "n_zeros": d["n_zeros_used"],
        "z_half": zero / 2,          # sum over gamma > 0 only
        "seconds": round(time.time() - t0, 1),
    }


def g_entry(sj: float, sk: float, xj: float = 0.0, xk: float = 0.0):
    a2 = mp.mpf(sj) ** 2 + mp.mpf(sk) ** 2
    return (
        mp.e ** (-((xj - xk) ** 2) / (2 * a2))
        * mp.sqrt(2 * mp.mpf(sj) * mp.mpf(sk) / a2)
    )


def _chol_solve(L, A):
    """L^{-1} A for lower-triangular L and matrix A, column by column."""
    n = A.rows
    out = mp.matrix(n, A.cols)
    for c in range(A.cols):
        col = mp.matrix([A[i, c] for i in range(n)])
        sol = mp.lu_solve(L, col)
        for i in range(n):
            out[i, c] = sol[i]
    return out


def gen_eig(M, G, dps: int = DPS):
    """Smallest and largest eigenvalue of (M, G), G SPD, in mpmath."""
    with mp.workdps(dps + 20):
        L = mp.cholesky(mp.matrix(G))
        Y = _chol_solve(L, mp.matrix(M))          # L^{-1} M
        C = _chol_solve(L, Y.T).T                 # L^{-1} M L^{-T}
        E, V = mp.eigsy((C + C.T) / 2)
        order = sorted(range(len(E)), key=lambda i: E[i])
        lams = [E[i] for i in order]
        vecs = [mp.lu_solve(L.T, mp.matrix([V[i, j] for i in range(len(E))]))
                for j in order]                   # back to a-coords
        return lams, vecs


def run_base(name: str, sigmas, cache: dict, dps: int = DPS) -> dict:
    J = len(sigmas)
    M, Z, G, checks = [], [], [], []
    for j in range(J):
        Mrow, Zrow, Grow = [], [], []
        for k in range(J):
            key = (min(sigmas[j], sigmas[k]), max(sigmas[j], sigmas[k]))
            if key not in cache:
                cache[key] = gram_entry(sigmas[j], sigmas[k], dps)
                print(f"  entry sigma=({sigmas[j]},{sigmas[k]}) done "
                      f"{cache[key]['seconds']}s", flush=True)
            e = cache[key]
            Mrow.append(e["arith"])
            Zrow.append(e["zero"])
            Grow.append(g_entry(sigmas[j], sigmas[k]))
            checks.append(e)
        M.append(Mrow)
        Z.append(Zrow)
        G.append(Grow)
    lam, vecs = gen_eig(M, G, dps)
    lam_z, _ = gen_eig(Z, G, dps)
    worst = max(checks, key=lambda c: c["rel_diff"])
    uncovered = [c for c in checks if not c["covered"]]
    return {
        "name": name,
        "dps": dps,
        "sigmas": list(sigmas),
        "M": [[float(x) for x in row] for row in M],
        "G": [[float(x) for x in row] for row in G],
        "lambda": [float(x) for x in lam],
        "lambda_from_zeros": [float(x) for x in lam_z],
        "lambda_min": float(lam[0]),
        "lambda_min_from_zeros": float(lam_z[0]),
        "at_floor": bool(abs(lam[0]) < NOISE_FLOOR),
        "eigvec_min": [float(x) for x in vecs[0]],
        "worst_entry_rel_diff": float(worst["rel_diff"]),
        "worst_entry_abs_diff": float(worst["abs_diff"]),
        "worst_entry_scale": float(max(abs(worst["arith"]), abs(worst["zero"]))),
        "smallest_entry": float(min(max(abs(c["arith"]), abs(c["zero"])) for c in checks)),
        "n_entries": len(checks),
        "n_uncovered": len(uncovered),
        "largest_uncovered_scale": float(
            max((max(abs(c["arith"]), abs(c["zero"])) for c in uncovered), default=0.0)
        ),
        "max_prime_tail": float(max(c["prime_tail_bound"] for c in checks)),
        "max_zero_tail": float(max(c["zero_tail_bound"] for c in checks)),
    }


def main() -> dict:
    global DPS
    if len(sys.argv) > 1:
        DPS = int(sys.argv[1])
    mp.mp.dps = DPS
    cache: dict = {}
    out = {}
    for name, sig in BASES.items():
        print(f"[{name}] sigmas={sig} dps={DPS}", flush=True)
        out[name] = run_base(name, sig, cache)
        r = out[name]
        print(
            f"  lambda_min={r['lambda_min']:+.6e} "
            f"(zeros side {r['lambda_min_from_zeros']:+.6e}) "
            f"floor={r['at_floor']} worst_rel={r['worst_entry_rel_diff']:.1e} "
            f"uncovered={r['n_uncovered']}/{r['n_entries']} "
            f"(largest uncovered {r['largest_uncovered_scale']:.1e})",
            flush=True,
        )
    here = os.path.dirname(os.path.abspath(__file__))
    with open(os.path.join(here, f"results_dps{DPS}.json"), "w") as f:
        json.dump(out, f, indent=1)
    return out


if __name__ == "__main__":
    main()
