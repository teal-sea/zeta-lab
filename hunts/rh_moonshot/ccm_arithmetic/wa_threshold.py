"""Where W_{1/4} = zeta(s+1/4) zeta(s-1/4) loses window positivity and capture.

Bisection in c on (2, 3) of the even-sector ball LDL^T inertia at shift 0
(conclusive pivots or the step is reported inconclusive), at N = 32 and 64.
Then, at a few windows, which radical captures W_a's ground state: its own
(samples of Xi_a(t) = |xi(3/4 + it)|^2) or zeta's (samples of Xi(t)).

Usage: .venv/bin/python hunts/rh_moonshot/ccm_arithmetic/wa_threshold.py
writes data/wa_threshold.json.
"""

from __future__ import annotations

import os
import sys
import time

HERE = os.path.dirname(os.path.abspath(__file__))
if HERE not in sys.path:
    sys.path.insert(0, HERE)

import ccm_common as C  # noqa: E402
from flint import arb, ctx, fmpq  # noqa: E402
from mpmath import mp  # noqa: E402

import enclosures as EN  # noqa: E402
import wp_common as WP  # noqa: E402

DATA = os.path.join(HERE, "data")


def inertia(c, N, prec=400):
    A = C.wa_matrix(c, N, prec)
    ctx.prec = prec
    M = [[A[i, j] for j in range(N + 1)] for i in range(N + 1)]
    return EN.ldlt_inertia(M, arb(0))


def radical(kind, c, N, tcut=60):
    L = C.L_mp(c)
    out = []
    for k in range(N + 1):
        om = 2 * mp.pi * k / L
        xv = mp.mpf(0) if om > tcut else C.xi_real(kind, om, 30)
        out.append(xv / mp.sqrt(L) if k == 0 else mp.sqrt(2 / L) * (-1) ** k * xv)
    return out


def main():
    t0 = time.time()
    out = {"bisection": {}, "capture": {}}
    for N in (32, 64):
        lo, hi = fmpq(2), fmpq(3)
        ilo, ihi = inertia(lo, N), inertia(hi, N)
        steps = []
        if not (ilo[1] == 0 and ihi[1] >= 1 and ilo[2] and ihi[2]):
            out["bisection"][N] = {"error": "endpoints not bracketing", "lo": ilo, "hi": ihi}
            continue
        for _ in range(14):
            mid = (lo + hi) / 2
            im = inertia(mid, N)
            steps.append([WP.cstr(mid), list(im[:2]), bool(im[2])])
            if not im[2]:
                break
            if im[1] == 0:
                lo = mid
            else:
                hi = mid
        out["bisection"][N] = {"positive_at": WP.cstr(lo), "negative_at": WP.cstr(hi), "steps": steps}
        print(N, out["bisection"][N]["positive_at"], out["bisection"][N]["negative_at"], flush=True)
    with mp.workdps(60):
        for c in (2, 3, 5, 13, 31):
            N = 32
            A = C.wa_matrix(c, N, 400)
            pairs = C.lowest_pairs(A, k=2)
            v = C.to_mp(pairs[0][1])
            rec = {"lambda1": pairs[0][0].str(8, radius=True)}
            for kind in ("wa", "zeta"):
                r = radical(kind, c, N)
                rec[f"misfit_vs_{kind}_radical"] = mp.nstr(C.overlap_misfit(v, r), 6)
            out["capture"][str(c)] = rec
            print(c, rec, flush=True)
    out["elapsed_s"] = round(time.time() - t0, 1)
    os.makedirs(DATA, exist_ok=True)
    WP.save(os.path.join(DATA, "wa_threshold.json"), out)


if __name__ == "__main__":
    main()
