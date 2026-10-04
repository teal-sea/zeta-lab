"""Measure one unit of the L = 1.19 assembly locally (phase 3 estimate input)."""
import sys
import time
from fractions import Fraction
from pathlib import Path

from flint import arb, arb_mat, ctx

sys.path.insert(0, str(Path(__file__).resolve().parent))
from assemble import Symbol, load_envelope, sph_j_all  # noqa: E402

for prec in (384,):
    ctx.prec = prec
    L = Fraction(119, 100)
    sym = Symbol(L, {"sine:16": load_envelope(L, "sine", 16)})
    for K, x in ((629, 500), (1259, 540)):
        xs = arb(x) + arb(1) / 3
        xs = arb(xs.mid())
        t0 = time.time()
        reps = 5
        for _ in range(reps):
            j = sph_j_all(K, xs)
        dt = (time.time() - t0) / reps
        print(f"prec={prec} bessel K={K} x={x}: {dt * 1e3:.1f} ms/node, max rad {max(float(v.rad()) for v in j):.1e}")
    t = arb(400) + arb(1) / 7
    t0 = time.time()
    for _ in range(20):
        sym.psi(t) + sym.H("sine:16", t)
    print(f"symbol: {(time.time() - t0) / 20 * 1e3:.2f} ms/node")
    for N, q in ((315, 96), (630, 96)):
        A = arb_mat(N, q, [arb(i % 13) / 7 for i in range(N * q)])
        t0 = time.time()
        A * A.transpose()
        print(f"panel product N={N} q={q}: {time.time() - t0:.2f} s")
    N = 630
    A = arb_mat(N, N, [arb(i % 13) / 7 for i in range(N * N)])
    t0 = time.time()
    A * A
    print(f"full product N={N}: {time.time() - t0:.1f} s")
