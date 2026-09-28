"""assembler/, post-hoc (not in PREREG, labelled so in delta_t_bound/RESULTS.md):
how small a uniform eps would have to be for the rule of PREREG (c) to say
outcome 1 at c = 2.9.

With one eps for every build of the cell, L*_N(eps) is the max over builds of
n_-(RL + eps I), interlaced. The float64 scan (measured) gives the profile
(L*_8, L*_16, L*_32) on every interval between breakpoints. eps_first is the
first eps, going up from 0, at which L*_32 > L*_16 fails: outcome 1 holds for
every uniform eps below it. It is confirmed by exact counts (full space:
both rational routes; V_4: balls) at eps_first (1 - 1e-6) and
eps_first (1 + 1e-6). The profile also shows where growth reappears at large
eps, from the single deepest eigenvalue deepening with N (interlacing), which
the pre-registered test cannot tell from growth of the count.

    PYTHONPATH=<worktree root> <venv python> .../crossover.py
"""

from __future__ import annotations

import json
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
if HERE not in sys.path:
    sys.path.insert(0, HERE)

import numpy as np  # noqa: E402
from flint import fmpq  # noqa: E402

import assemble as AS  # noqa: E402

RI = AS.RI
OUT = os.path.join(HERE, "crossover.json")
REL = fmpq(1, 10 ** 6)


def v4_eigs(RL, c, N):
    """Float eigenvalues of RL on V_4 (orthonormalised midpoints of Z(c))."""
    Z, _ = AS.class_basis_c(AS.C_EXACT[c], N, 64)
    Zf = np.array([[float(Z[i, j].mid()) for j in range(Z.ncols())] for i in range(Z.nrows())])
    B, _ = np.linalg.qr(Zf)
    return np.linalg.eigvalsh(B.T @ RL @ B)


def L_of(eigs_by_build, eps):
    L = {}
    for N in AS.NS:
        L[N] = max(int((w < -eps).sum()) for (n, _), w in eigs_by_build.items() if n == N)
    L[16] = max(L[16], L[8])
    L[32] = max(L[32], L[16])
    return L


def profile(eigs_by_build):
    """[(a, b, (L8, L16, L32))]: the float profile on [a, b) between breakpoints."""
    pts = sorted({float(-x) for w in eigs_by_build.values() for x in w if x < 0})
    grid = [0.0] + pts
    out = []
    for a, b in zip(grid, grid[1:]):
        L = L_of(eigs_by_build, (a + b) / 2)
        t = (L[8], L[16], L[32])
        if out and out[-1][2] == t:
            out[-1] = (out[-1][0], b, t)
        else:
            out.append((a, b, t))
    return out


def locate(eigs_by_build):
    """eps_first from floats: the first breakpoint at which L_32 > L_16 fails."""
    for a, b, t in profile(eigs_by_build):
        if not t[2] > t[1]:
            return a
    return None


def exact_L(c, space, eps):
    L = {N: 0 for N in AS.NS}
    per = {}
    for nv, S, N in AS.BUILDS:
        RL = RI.lower_mirrored(AS.stored_R(c, nv, S, N))
        if space == "full":
            k = RI.inertia_both(RI.shifted(RI.exact_matrix(RL), eps))[0]
        else:
            k = AS.class_inertia_c(RL, eps, N, AS.C_EXACT[c])["n_minus"]
        per[AS.build_key(c, nv, S, N)] = k
        L[N] = max(L[N], -1 if k is None else k)
    L[16] = max(L[16], L[8])
    L[32] = max(L[32], L[16])
    return L, per


def run(c="2.9"):
    out = {"c": c, "rel": AS.q_pair(REL), "spaces": {}}
    for space in ("full", "V4"):
        eigs = {}
        for nv, S, N in AS.BUILDS:
            RL = RI.lower_mirrored(AS.stored_R(c, nv, S, N))
            eigs[(N, AS.build_key(c, nv, S, N))] = np.linalg.eigvalsh(RL) if space == "full" else v4_eigs(RL, c, N)
        star = locate(eigs)
        prof = profile(eigs)
        rec = {"eps_first_float": star,
               "profile": [[a, b, list(t)] for a, b, t in prof if a < 0.2],
               "regrowth_float": [[a, b, list(t)] for a, b, t in prof if star is not None and a >= star and t[2] > t[1]]}
        if star is not None:
            s = RI.to_q(star)
            lo, hi = s * (1 - REL), s * (1 + REL)
            Llo, plo = exact_L(c, space, lo)
            Lhi, phi = exact_L(c, space, hi)
            rec.update({"eps_lo": AS.q_pair(lo), "eps_hi": AS.q_pair(hi),
                        "L_at_lo": Llo, "L_at_hi": Lhi, "per_build_lo": plo, "per_build_hi": phi,
                        "float_L_at_lo": L_of(eigs, float(lo)), "float_L_at_hi": L_of(eigs, float(hi))})
        out["spaces"][space] = rec
        AS._dump(out, OUT)
        print(space, rec.get("eps_first_float"), rec.get("L_at_lo"), rec.get("L_at_hi"), rec["regrowth_float"], flush=True)
    return out


if __name__ == "__main__":
    run()
