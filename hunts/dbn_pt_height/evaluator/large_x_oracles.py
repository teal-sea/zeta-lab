"""Milestone 1b: H_t at large x, where E_C is much smaller than |C_t|.

On the milestone-1 grid (x <= 2000) the correction C_t/B_t is about as large as
its own error term e_C, so containment there cannot tell a right C_t from
several wrong ones.  At x >= 1e5 it can: |C_t/B_t| is tens to hundreds of times
e_C.  This script writes reference values of H_t at such points.

* t = 0: H_0(x + iy) = (1/8) xi((1 - y + ix)/2), xi(s) = s(s-1)/2 pi^{-s/2} Gamma(s/2) zeta(s),
  by two routes that share no code: mpmath (zeta, loggamma) and PARI/GP through
  cypari2 (zeta, lngamma).
* t > 0: the heat-kernel representation (htz) of the paper,
  H_t(z) = int (1/8) xi((1 + iz)/2 + sqrt(t) v) e^{-v^2} / sqrt(pi) dv, by
  Gauss-Hermite quadrature with mpmath's xi at 80 and at 120 nodes; the two
  node counts are recorded so that their agreement can be checked.

Both are floating-point routes at a requested precision: agreement with the
evaluator is a measurement, not an enclosure.  One JSON line per point is
appended as soon as it is done (checkpoint per unit); a rerun skips finished
points.

Usage:  .venv/bin/python hunts/dbn_pt_height/evaluator/large_x_oracles.py OUT.jsonl
"""

from __future__ import annotations

import json
import sys
import time
from pathlib import Path

from mpmath import mp

T0_POINTS = [
    ("100000.3", "0.4"), ("1000000", "0.5"), ("1000000.37", "1"), ("3162277.7", "0.3"),
    ("10000000.81", "0.9"), ("31622776.6", "0"), ("100000000.5", "0.6"), ("100000000.73", "1"),
]
TPOS_POINTS = [
    ("100000.5", "0.5", "0.2"), ("300000.25", "0.7", "0.5"), ("1000000", "1", "0.4"), ("1000000.5", "0.2", "0.05"),
]


def xi_mpmath(s):
    return s * (s - 1) / 2 * mp.exp(-(s / 2) * mp.log(mp.pi) + mp.loggamma(s / 2)) * mp.zeta(s)


def H0_mpmath(x: str, y: str, dps: int = 30):
    with mp.workdps(dps):
        s = mp.mpc(1 - mp.mpf(y), mp.mpf(x)) / 2
        return +(xi_mpmath(s) / 8)


def H0_pari(x: str, y: str, digits: int = 38) -> tuple[str, str]:
    import cypari2

    pari = cypari2.Pari()
    pari.set_real_precision(digits)
    v = pari(f"my(s = (1 - ({y}) + I*({x}))/2); s*(s-1)/2*exp(-(s/2)*log(Pi) + lngamma(s/2))*zeta(s)/8")
    re = str(pari.real(v)).replace(" E", "e").replace("E", "e")
    im = str(pari.imag(v)).replace(" E", "e").replace("E", "e")
    return re, im


def Ht_gauss_hermite(x: str, y: str, t: str, n: int, dps: int = 25):
    with mp.workdps(dps):
        nodes, weights = mp.gauss_quadrature(n, "hermite")
        s0 = mp.mpc(1 - mp.mpf(y), mp.mpf(x)) / 2
        rt = mp.sqrt(mp.mpf(t))
        tot = mp.fsum(w * xi_mpmath(s0 + rt * v) for v, w in zip(nodes, weights))
        return +(tot / (8 * mp.sqrt(mp.pi)))


def main() -> None:
    out = Path(sys.argv[1])
    done = set()
    if out.exists():
        for line in out.read_text().splitlines():
            if line.strip():
                r = json.loads(line)
                done.add((r["x"], r["y"], r["t"]))
    for (x, y) in T0_POINTS:
        if (x, y, "0") in done:
            continue
        t1 = time.perf_counter()
        v = H0_mpmath(x, y)
        pre, pim = H0_pari(x, y)
        with mp.workdps(40):
            pv = mp.mpc(mp.mpf(pre), mp.mpf(pim))
            rec = {
                "x": x, "y": y, "t": "0", "route": "xi: mpmath and PARI",
                "re": mp.nstr(mp.re(v), 25), "im": mp.nstr(mp.im(v), 25),
                "pari_re": mp.nstr(pv.real, 25), "pari_im": mp.nstr(pv.imag, 25),
                "rel_diff_routes": mp.nstr(abs(v - pv) / abs(pv), 3),
                "seconds": round(time.perf_counter() - t1, 2),
            }
        with out.open("a") as fh:
            fh.write(json.dumps(rec) + "\n")
        print(json.dumps(rec), flush=True)
    for (x, y, t) in TPOS_POINTS:
        if (x, y, t) in done:
            continue
        t1 = time.perf_counter()
        a = Ht_gauss_hermite(x, y, t, 80)
        b = Ht_gauss_hermite(x, y, t, 120)
        with mp.workdps(40):
            rec = {
                "x": x, "y": y, "t": t, "route": "heat kernel: Gauss-Hermite 80 and 120 nodes, mpmath xi",
                "re": mp.nstr(mp.re(b), 22), "im": mp.nstr(mp.im(b), 22),
                "re_80": mp.nstr(mp.re(a), 22), "im_80": mp.nstr(mp.im(a), 22),
                "rel_diff_routes": mp.nstr(abs(a - b) / abs(b), 3),
                "seconds": round(time.perf_counter() - t1, 2),
            }
        with out.open("a") as fh:
            fh.write(json.dumps(rec) + "\n")
        print(json.dumps(rec), flush=True)


if __name__ == "__main__":
    main()
