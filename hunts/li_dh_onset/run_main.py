"""The main extraction: lambda_n(DH) for n = 1 .. n_max, one circle, one DFT.

Two phases with a checkpoint between them, because they fail differently.  The
sampling phase is thousands of independent high-precision evaluations of the
completed Davenport-Heilbronn function and is the expensive half; it writes
every block of 64 nodes to disk as it lands, so a killed run resumes rather than
restarts.  The extraction phase is one pass of arithmetic over samples that are
already paid for, and it can be re-run at a different n_max off the same circle
for free.

The winding check inside ``dhli.coefficients_from_samples`` is not a formality.
It is an argument-principle count of the zeros of F inside the exact contour
being integrated, so it is the last line of defence behind :mod:`radius_scan`,
run on the real thing rather than on a rectangle that contains it.

Nothing here is evidence about the Riemann Hypothesis.
"""

from __future__ import annotations

import argparse
import json
import os
import sys
import time

import mpmath
from mpmath import mp

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from dhli import (
    coefficients_from_samples,
    node_count,
    sample_circle_iter,
    work_digits,
)

HERE = os.path.dirname(os.path.abspath(__file__))
ART = os.path.join(HERE, "artifacts")


def sample_path(target: str, radius, n_points: int, work: int) -> str:
    return os.path.join(
        ART, f"samples_{target}_r{radius}_N{n_points}_w{work}.json"
    )


def gather_samples(target, work, radius, n_points, processes, block=64) -> list:
    """Sample the circle, resuming from whatever the checkpoint already holds."""
    path = sample_path(target, radius, n_points, work)
    done: list = []
    if os.path.exists(path):
        with open(path) as fh:
            blob = json.load(fh)
        if blob.get("n_points") == n_points and blob.get("work") == work:
            done = blob["rows"]
            print(f"resuming from {len(done)}/{n_points} nodes", flush=True)
    if len(done) < n_points:
        t0 = time.time()
        remaining = n_points - len(done)
        for lo, hi, rows in sample_circle_iter(
            target, work, radius, n_points, processes, block=block
        ):
            if hi <= len(done):
                continue
            done.extend(rows[len(done) - lo:])
            if (hi // block) % 8 == 0 or hi == n_points:
                with open(path + ".tmp", "w") as fh:
                    json.dump(
                        {"target": target, "radius": str(radius),
                         "n_points": n_points, "work": work, "rows": done}, fh
                    )
                os.replace(path + ".tmp", path)
                el = time.time() - t0
                pace = el / max(hi - (n_points - remaining), 1)
                print(
                    f"  nodes {hi}/{n_points}  {el:.0f}s elapsed  "
                    f"eta {pace * (n_points - hi):.0f}s", flush=True
                )
    with mp.workdps(work):
        return [
            mp.mpc(mpmath.make_mpf(tuple(re)), mpmath.make_mpf(tuple(im)))
            for re, im in done
        ]


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--target", default="dh")
    ap.add_argument("--n-max", type=int, default=2000)
    ap.add_argument("--dps", type=int, default=30)
    ap.add_argument("--radius", default="0.9")
    ap.add_argument("--processes", type=int, default=3)
    ap.add_argument("--block", type=int, default=64)
    args = ap.parse_args()

    work = work_digits(args.n_max, args.dps, args.radius)
    npts = node_count(args.n_max, work, args.radius)
    print(
        f"target={args.target} n_max={args.n_max} r={args.radius} "
        f"work={work} nodes={npts}", flush=True
    )
    os.makedirs(ART, exist_ok=True)

    t0 = time.time()
    samples = gather_samples(
        args.target, work, args.radius, npts, args.processes, block=args.block
    )
    t_sample = time.time() - t0

    t1 = time.time()
    lam = coefficients_from_samples(
        samples, args.n_max, work, args.radius, processes=args.processes
    )
    t_dft = time.time() - t1

    with mp.workdps(args.dps):
        vals = [+v for v in lam]
        worst = min(range(len(vals)), key=lambda i: vals[i])
        digits = mpmath.libmp.repr_dps(mp.prec)
        out = {
            "generated": time.strftime("%Y-%m-%dT%H:%M:%S"),
            "target": args.target,
            "n_max": args.n_max,
            "dps": args.dps,
            "radius": str(args.radius),
            "work_digits": work,
            "n_points": npts,
            "processes": args.processes,
            "seconds_sampling": round(t_sample, 1),
            "seconds_extraction": round(t_dft, 1),
            "all_positive": bool(all(v > 0 for v in vals)),
            "min_index": worst + 1,
            "min_value": mp.nstr(vals[worst], 25),
            "lambda": [mp.nstr(v, digits) for v in vals],
        }
    path = os.path.join(ART, f"lambda_{args.target}_n{args.n_max}_r{args.radius}.json")
    with open(path, "w") as fh:
        json.dump(out, fh, indent=1)
    print("all positive:", out["all_positive"], "min at n =", out["min_index"],
          "=", out["min_value"])
    print("sampling %.0f s, extraction %.0f s" % (t_sample, t_dft))
    print("wrote", path)


if __name__ == "__main__":
    main()
