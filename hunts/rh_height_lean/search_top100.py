"""Scratch search for the top-leg partition at height 100 (not part of the proof)."""
import importlib.util, sys, time
from fractions import Fraction as F
from pathlib import Path
HERE = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location("gen_legs", HERE / "gen_legs.py")
G = importlib.util.module_from_spec(spec); spec.loader.exec_module(G)
G.KE = 10
M = G.load_mirror()
Y = F(100)
grid = [F(32 + k, 64) for k in range(0, 97)]  # 1/2 .. 2 step 1/64
a, segs, t0 = F(1, 2), [], time.time()
while a < 2:
    best = None
    for N in range(8, 31, 2):
        # largest b on the grid with slack > MARGIN
        cand = [b for b in grid if b > a]
        lo, hi, ok = 0, len(cand) - 1, None
        while lo <= hi:
            mid = (lo + hi) // 2
            d = G.segment(M, a, cand[mid], Y, N)
            if d["slack"] > G.MARGIN:
                ok, lo = (cand[mid], d), mid + 1
            else:
                hi = mid - 1
        if ok:
            reach = ok[0] - a
            score = reach / G.towers(N)
            if best is None or score > best[0]:
                best = (score, N, ok[0], ok[1]["slack"])
    if best is None:
        print("no segment from", a); sys.exit(1)
    _, N, b, sl = best
    segs.append((a, b, N)); print(f"[{a}, {b}] N={N} slack={float(sl):.4f}  ({time.time()-t0:.0f}s)", flush=True)
    a = b
print("TOP =", segs)
for N in range(16, 61, 4):
    d = G.point(M, F(1, 2), Y, N, F(-1, 5))
    print("point N", N, "ok", d["ok"], "im_hi", float(d["im"][1]), "margin", float(d["margin"]))
    if d["ok"] and d["margin"] > G.MARGIN:
        break
