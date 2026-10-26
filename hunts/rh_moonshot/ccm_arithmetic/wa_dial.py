"""The unitarity dial: W_a = zeta(s+a) zeta(s-a) for a -> 0.

W_a has local roots p^{+-a} (unitary only at a = 0, where W_0 = zeta^2 and the
window form is exactly 2 Q_zeta) and zeros rho +- a.  For each a, find the
smallest window c_a (on the doubling-then-bisection grid, N = 32) where the
even-sector form acquires a negative eigenvalue, by ball LDL^T inertia at
shift 0 (conclusive pivots required; inconclusive steps are reported).
At a = 0 the form is checked to equal 2 Q_zeta entry by entry.

Usage: .venv/bin/python hunts/rh_moonshot/ccm_arithmetic/wa_dial.py
writes data/wa_dial.json.
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

import enclosures as EN  # noqa: E402
import wp_common as WP  # noqa: E402

DATA = os.path.join(HERE, "data")
N = 32
PREC = 600


def nneg(c, a):
    A = C.wa_matrix(c, N, PREC, shift=a)
    ctx.prec = PREC
    M = [[A[i, j] for j in range(N + 1)] for i in range(N + 1)]
    npos, nn, concl = EN.ldlt_inertia(M, arb(0))
    return nn, bool(concl)


def main():
    t0 = time.time()
    out = {"N": N, "prec": PREC, "dial": {}}
    # a = 0: W_0 = zeta^2, form must be 2 Q_zeta
    A0 = C.wa_matrix(13, N, PREC, shift=fmpq(0))
    Az = C.matrix("zeta", 13, N, PREC)
    ctx.prec = PREC
    dev = max(abs(float((A0[i, j] - 2 * Az[i, j]).mid())) for i in range(N + 1) for j in range(N + 1))
    out["a0_equals_2Qzeta_maxdev"] = dev
    print("a=0 max |W_0 - 2 Q_zeta| =", dev, flush=True)
    for a in (fmpq(1, 4), fmpq(1, 8), fmpq(1, 16), fmpq(1, 32), fmpq(1, 64)):
        c = fmpq(2)
        hist = []
        n0, ok = nneg(c, a)
        hist.append([WP.cstr(c), n0, ok])
        if n0 != 0:
            out["dial"][WP.cstr(a)] = {"error": "negative already at c = 2", "hist": hist}
            continue
        hi = None
        while float(c) < 2000:
            c2 = c * 2
            nn, ok = nneg(c2, a)
            hist.append([WP.cstr(c2), nn, ok])
            if not ok:
                break
            if nn > 0:
                hi = c2
                break
            c = c2
        if hi is None:
            out["dial"][WP.cstr(a)] = {"no_negativity_up_to": WP.cstr(c), "hist": hist}
            print(WP.cstr(a), "no negativity up to", WP.cstr(c), flush=True)
            continue
        lo = c
        for _ in range(10):
            mid = (lo + hi) / 2
            nn, ok = nneg(mid, a)
            hist.append([WP.cstr(mid), nn, ok])
            if not ok:
                break
            if nn > 0:
                hi = mid
            else:
                lo = mid
        out["dial"][WP.cstr(a)] = {
            "positive_at": WP.cstr(lo),
            "negative_at": WP.cstr(hi),
            "c_float": [float(lo), float(hi)],
            "hist": hist,
        }
        print(WP.cstr(a), float(lo), float(hi), flush=True)
        WP.save(os.path.join(DATA, "wa_dial.json"), out)
    out["elapsed_s"] = round(time.time() - t0, 1)
    os.makedirs(DATA, exist_ok=True)
    WP.save(os.path.join(DATA, "wa_dial.json"), out)


if __name__ == "__main__":
    main()
