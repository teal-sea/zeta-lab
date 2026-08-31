"""The control lane A never got to run: the in-band LP at the SAME (X, J, eps)
rungs as the out-of-band pass, so the two truncation excesses are comparable.

A constant ratio of excesses over 0.6725007 across the ladder is the signature
of one limit with a rescaled truncation error (out-of-band buys nothing).
A ratio declining toward 1 is the signature of two different limits.
"""
import json, sys, time, pathlib
sys.path.insert(0, "/Users/thomas/zeta-lab/hunts/frontier_math")
from configuration_lp import solve

MT_LIMIT = 0.6725007036794116
RUNGS = [(40.0, 200), (80.0, 320), (120.0, 480), (160.0, 640)]
OUT = {40.0: 0.6918386643557259, 80.0: 0.6862544470607155,
       120.0: 0.6847195241510968, 160.0: 0.6838667734772812}
dst = pathlib.Path("/Users/thomas/.claude/jobs/c4f0ce42/tmp/inband_control.json")

rows = []
print(f"{'X':>6} {'J':>5} {'in-band':>12} {'e_in':>10} {'e_out':>10} {'ratio':>7} {'s':>7}",
      flush=True)
for X, J in RUNGS:
    t0 = time.time()
    r = solve(J=J, X=X, eps=0.4 / X, A_out=None)
    dt = time.time() - t0
    v = r["value"]
    e_in = v - MT_LIMIT
    e_out = OUT[X] - MT_LIMIT
    rows.append({"X": X, "J": J, "in_band": v, "D": r["D"], "e_in": e_in,
                 "e_out": e_out, "ratio": e_out / e_in, "wall_seconds": round(dt, 1)})
    dst.write_text(json.dumps(rows, indent=1))
    print(f"{X:6.0f} {J:5d} {v:12.7f} {e_in:10.6f} {e_out:10.6f} "
          f"{e_out/e_in:7.3f} {dt:7.1f}", flush=True)
