"""Zero layer: Arb isolation of zeta zeros (route 1) and an mpmath bracket check (route 2).

Route 1 is python-flint's ``acb.zeta_zeros`` (Arb's ``acb_dirichlet_zeta_zeros``,
Platt's algorithm as implemented in Arb, with Turing's method for the count),
and ``arb.zeta_nzeros`` for N(T). It returns zeros by index with real part
exactly 1/2, so the index is the completeness statement and it rests on Arb.

Route 2 shares no code with Arb: mpmath's ``siegelz`` (Riemann-Siegel) at the
two ends of each Arb bracket widened to +/- delta must have opposite signs.
That confirms one zero of odd order in each bracket, at float grade (mpmath
``siegelz`` carries no error bound). It does not check completeness: the count
is the layer both routes share, through Arb's Turing count, unless an
independent count is added.

Shard driver::

    nice -n 10 .venv/bin/python -u hunts/skewes_enclosure/zero_layer.py \
        --n0 1 --num 100000 --batch 5000 --prec 64 --out <scratch>/shard.json

The JSON holds timings, the shard's partial sums at the parameter sets in
``skewes_terms``, the route-2 sample outcome and the SHA-256 of the zeros as
written (one ``mid +/- rad`` line per zero, not committed).
"""

from __future__ import annotations

import argparse
import hashlib
import json
import random
import sys
import time
from pathlib import Path

import flint
from flint import acb, arb

sys.path.insert(0, str(Path(__file__).resolve().parent))
import skewes_terms as st  # noqa: E402


def arb_zeros(n0: int, num: int, batch: int = 5000, prec: int = 128):
    """Ordinates gamma_{n0} .. gamma_{n0+num-1} as arb balls, plus seconds per batch."""
    old = flint.ctx.prec
    flint.ctx.prec = prec
    try:
        out, times = [], []
        n = n0
        while n < n0 + num:
            k = min(batch, n0 + num - n)
            t = time.perf_counter()
            zs = acb.zeta_zeros(n, k)
            times.append(time.perf_counter() - t)
            for z in zs:
                if not (z.real == arb(1) / 2):
                    raise ValueError(f"zero {n} has real part {z.real}, not exactly 1/2")
                out.append(z.imag)
            n += k
        return out, times
    finally:
        flint.ctx.prec = old


def check_ordered(gammas) -> bool:
    """Consecutive balls are disjoint and increasing (decided on balls)."""
    return all(bool(a < b) for a, b in zip(gammas, gammas[1:]))


def count_below(T: str, prec: int = 128) -> int:
    """N(T) from Arb's Turing count; raises if the ball does not pin an integer."""
    old = flint.ctx.prec
    flint.ctx.prec = prec
    try:
        return int(arb(T).zeta_nzeros().unique_fmpz())
    finally:
        flint.ctx.prec = old


def mpmath_bracket_signs(gamma: arb, delta: str = "1e-8", dps: int = 30) -> bool:
    """Route 2: siegelz(gamma - delta) and siegelz(gamma + delta) differ in sign."""
    import mpmath

    with mpmath.workdps(dps):
        mid = mpmath.mpf(gamma.mid().str(40, radius=False))
        d = mpmath.mpf(delta)
        if not (gamma.rad() < arb(delta)):
            raise ValueError("Arb radius exceeds delta; widen delta")
        a = mpmath.siegelz(mid - d)
        b = mpmath.siegelz(mid + d)
        return bool(a * b < 0)


def zeros_digest(gammas) -> str:
    h = hashlib.sha256()
    for g in gammas:
        h.update((g.str(45) + "\n").encode())
    return h.hexdigest()


def run_shard(n0: int, num: int, batch: int, sample: int, seed: int, prec: int = 128) -> dict:
    t0 = time.perf_counter()
    gammas, times = arb_zeros(n0, num, batch, prec)
    t_zeros = time.perf_counter() - t0

    t1 = time.perf_counter()
    sums = {
        "chao_plymen": st.lehman_sum(gammas, st.CHAO_PLYMEN.omega, st.CHAO_PLYMEN.alpha),
        "saouter_demichel": st.lehman_sum(gammas, st.SAOUTER_DEMICHEL.omega,
                                          st.SAOUTER_DEMICHEL.alpha),
    }
    t_sums = time.perf_counter() - t1

    rng = random.Random(seed)
    picks = sorted(rng.sample(range(num), min(sample, num)))
    t2 = time.perf_counter()
    route2 = {n0 + i: mpmath_bracket_signs(gammas[i]) for i in picks}
    t_route2 = time.perf_counter() - t2

    max_rad = max(g.rad() for g in gammas)
    return {
        "n0": n0,
        "num": num,
        "batch": batch,
        "isolation_prec_bits": prec,
        "first": gammas[0].str(30),
        "last": gammas[-1].str(30),
        "ordered_disjoint": check_ordered(gammas),
        "max_radius": max_rad.str(5),
        "seconds_zeros": t_zeros,
        "seconds_per_batch": times,
        "ms_per_zero": 1e3 * t_zeros / num,
        "seconds_sums": t_sums,
        "partial_sums": {k: v.str(40) for k, v in sums.items()},
        "route2_sample": {"seed": seed, "size": len(picks),
                          "all_sign_changes": all(route2.values()),
                          "failures": [k for k, v in route2.items() if not v],
                          "seconds": t_route2},
        "zeros_sha256": zeros_digest(gammas),
        "python_flint": flint.__version__,
    }


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--n0", type=int, required=True)
    ap.add_argument("--num", type=int, required=True)
    ap.add_argument("--batch", type=int, default=5000)
    ap.add_argument("--sample", type=int, default=200)
    ap.add_argument("--seed", type=int, default=152)
    ap.add_argument("--prec", type=int, default=128)
    ap.add_argument("--out", type=Path, required=True)
    a = ap.parse_args()
    res = run_shard(a.n0, a.num, a.batch, a.sample, a.seed, a.prec)
    a.out.write_text(json.dumps(res, indent=1))
    print(json.dumps({k: v for k, v in res.items() if k != "seconds_per_batch"}, indent=1))


if __name__ == "__main__":
    main()
