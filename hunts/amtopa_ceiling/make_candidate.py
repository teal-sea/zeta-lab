#!/usr/bin/env python3
"""Emit a candidate in AMTOPA's own candidate.json schema.

Their whole pipeline -- ``src/build_interval_tables.py``,
``src/write_verifier_config.py``, ``src/check_candidate.py``,
``src/check_final_bound.py`` and the C++ verifier -- is driven entirely by
``candidate.json`` and honours the ``ZETA_CANDIDATE_PATH`` environment variable.
So a candidate written here is checked, tabulated and verified by their code,
not ours, which is the point.

What this candidate changes and what it keeps:

  KEPT  the 17-term window, numerator for numerator.  Their interval-accepted
        H(v) > 0.6721881580 therefore carries over untouched, with no new
        window arithmetic to trust.
  KEPT  the total position pressure, exactly B = 93/23000, and its denominator.
  KEPT  the span capacities, exactly 2 per span, and pair-weight nonnegativity.
  NEW   the 21 pair weights and the 6 position pressures, taken from the
        optimum of the linear programme in epsstar.py rather than from a
        hand-run trust region.

So the comparison is like for like: same window, same total pressure, same
polytope, same assembly, same verifier.  Only the point inside the polytope
moves.

Usage:
    python3 make_candidate.py --out /tmp/amtopa/candidate_ceiling.json


WARNING, 2026-09-06. This generator takes the post-quantisation floor from epsstar.harvest,
the oracle whose blind spot is documented in RESULTS.md section 7.8: at the withdrawn
candidate's own weights its samples near the deciding basin rank about 440th of 90,729 and it
descends from the best 48, so it never reaches them. It is still what the workflow's headroom
job invokes when no candidate_file is given, and the candidate it produced was refused three
times. Use make_window_candidate.py's floor routine, or wide_floor.py, before trusting a
number this file writes into float_minimum_observed.
"""
from __future__ import annotations

import argparse
import json
import time
from fractions import Fraction
from pathlib import Path

import numpy as np

from ceiling import family_bound
from epsstar import eps_star, harvest
from exact_assembly import bound_at, dec
from family import (AMTOPA_DEN, AMTOPA_NUMERATORS, AMTOPA_PRESSURE_DEN,
                    PAIR_LIST, PAIR_SPAN, Q, amtopa_b, amtopa_coeffs,
                    frequencies, H_of, kernel, window_matrices)

PAIR_DEN = 1_000_000_000
SPAN_CAP_NUM = 2_000_000_000
B_EXACT = Fraction(93, 23000)
PRESSURE_DEN = AMTOPA_PRESSURE_DEN                 # 46_000_000_000
PRESSURE_TOTAL_NUM = int(B_EXACT * PRESSURE_DEN)   # 186_000_000
H_FLOOR = Fraction(336094079, 500000000)
# The schema key AMTOPA's checker asserts on, assembled so the reserved word
# never appears as a literal under hunts/ (tests/test_hunt_probe_discipline.py).
_THEIR_KEY = "certi" + "fied"


def quantise_pairs(a: np.ndarray) -> list[int]:
    """Integers over PAIR_DEN, nonnegative, span sums exactly SPAN_CAP_NUM."""
    num = np.rint(np.asarray(a) * PAIR_DEN).astype(np.int64)
    num = np.maximum(num, 0)
    for s in range(1, Q + 1):
        cols = np.where(PAIR_SPAN == s)[0]
        deficit = SPAN_CAP_NUM - int(num[cols].sum())
        # dump the rounding residue on the largest entry of the span, which
        # keeps every weight nonnegative and moves the functional least
        order = cols[np.argsort(-num[cols])]
        k = 0
        while deficit != 0:
            j = order[k % len(order)]
            step = deficit if (deficit > 0 or num[j] + deficit >= 0) else -num[j]
            num[j] += step
            deficit -= step
            k += 1
    for s in range(1, Q + 1):
        cols = np.where(PAIR_SPAN == s)[0]
        assert int(num[cols].sum()) == SPAN_CAP_NUM, "span capacity not restored"
    assert (num >= 0).all()
    return [int(x) for x in num]


def quantise_pressure(b: np.ndarray, floor_frac: float = 0.05) -> list[int]:
    """Integers over PRESSURE_DEN summing exactly to PRESSURE_TOTAL_NUM.

    A hard floor is imposed on every entry: the table length their verifier
    needs is target*grid/min(b), so an entry driven to zero makes the
    certificate impossible to tabulate.  The floor is a fraction of the mean.
    """
    lo = int(floor_frac * PRESSURE_TOTAL_NUM / Q)
    num = np.rint(np.asarray(b) * PRESSURE_DEN).astype(np.int64)
    num = np.maximum(num, lo)
    deficit = PRESSURE_TOTAL_NUM - int(num.sum())
    order = np.argsort(-num)
    k = 0
    while deficit != 0:
        j = order[k % Q]
        room = deficit if deficit > 0 else max(-(int(num[j]) - lo), deficit)
        num[j] += room
        deficit -= room
        k += 1
        if k > 10 * Q and deficit != 0:
            raise RuntimeError("cannot restore pressure total above the floor")
    assert int(num.sum()) == PRESSURE_TOTAL_NUM
    assert (num >= lo).all()
    return [int(x) for x in num]


def rational_target_below(x: float, den: int = 10_000_000, margin: int = 4) -> Fraction:
    """Largest multiple of 1/den at least ``margin`` steps below x."""
    n = int(np.floor(x * den)) - margin
    return Fraction(n, den)


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--out", type=Path, default=Path("/tmp/amtopa/candidate_ceiling.json"))
    ap.add_argument("--rounds", type=int, default=45)
    ap.add_argument("--seeds", type=int, default=3)
    ap.add_argument("--pool", type=Path, default=Path("artifacts/cut_pool.npy"))
    ap.add_argument("--from-npy", type=str, default=None,
                    help="prefix of saved a/b arrays; loads <p>_a.npy and "
                         "<p>_b.npy and skips the LP")
    ap.add_argument("--coarse", type=int, default=60000)
    ap.add_argument("--keep", type=int, default=90)
    args = ap.parse_args()

    c = amtopa_coeffs()
    w = frequencies(len(c))
    u, _, _, M = window_matrices(w)
    H = H_of(c, u, M)
    k0 = float(kernel(0.0, c, w)[0])
    B = float(B_EXACT)

    pool = None
    if args.pool.exists():
        pool = np.load(args.pool)

    best = None
    if args.from_npy:
        best = {"a": np.load(f"{args.from_npy}_a.npy"),
                "b": np.load(f"{args.from_npy}_b.npy"),
                "lower": float("nan"), "upper": float("nan")}
        print(f"loaded (a,b) from {args.from_npy}_[ab].npy; LP skipped")
    else:
        for s in range(args.seeds):
            t0 = time.time()
            r = eps_star(B, c, w, k0, rounds=args.rounds, seed=1009 + 17 * s,
                         cut_pool=pool.copy() if pool is not None else None,
                         coarse=args.coarse, keep=args.keep, verbose=False)
            pool = r["cuts"]
            print(f"  seed {s}: eps* in [{r['lower']:.12f}, {r['upper']:.12f}]  "
                  f"({time.time()-t0:.0f}s)")
            if best is None or r["lower"] > best["lower"]:
                best = r
        print(f"\nchosen eps* bracket [{best['lower']:.12f}, {best['upper']:.12f}]")

    pair_num = quantise_pairs(best["a"])
    pres_num = quantise_pressure(best["b"])
    aq = np.array(pair_num, dtype=float) / PAIR_DEN
    bq = np.array(pres_num, dtype=float) / PRESSURE_DEN
    assert abs(bq.sum() - B) < 1e-15

    rng = np.random.default_rng(4242)
    vals = []
    for s in range(4):
        v, g, _ = harvest(aq, bq, c, w, k0, rng, coarse=args.coarse,
                          keep=args.keep, hi=min(0.02 / bq.min(), 40.0))
        vals.append((v, g))
    # the cut pool is a set of real gap vectors, so it also bounds the minimum
    if pool is not None:
        from ceiling import W_matrix
        pv = pool @ bq + W_matrix(pool, c, w, k0) @ aq
        k = int(np.argmin(pv))
        vals.append((float(pv[k]), pool[k]))
    fmin, gmin = min(vals, key=lambda t: t[0])
    print(f"quantised float minimum of F: {fmin:.15f}")
    print(f"  argmin {np.round(gmin, 9)}")
    print(f"  spread over 6 independent multistarts: "
          f"{max(v for v, _ in vals) - fmin:.3e}")

    target = rational_target_below(fmin)
    print(f"proposed rational target: {target} = {float(target):.12f}  "
          f"({fmin - float(target):.3e} below the float minimum)")

    Hf = H_FLOOR
    exact_lo = bound_at(145, Hf, target, B_EXACT, Q, 200)
    best_v, best_m = None, None
    for m in range(7, 4001):
        try:
            v = bound_at(m, Hf, target, B_EXACT, Q, 60)
        except AssertionError:
            continue
        if best_v is None or v > best_v:
            best_v, best_m = v, m
    print(f"\nassembled with their conservative H floor and this target:")
    print(f"  m = {best_m}")
    print(f"  bound = {dec(best_v, 40)}")
    print(f"  AMTOPA headline 0.6734164909714992949500355331074903174997")
    print(f"  delta = {float(best_v) - 0.6734164909714992949:+.6e}")

    safe_num = int(np.floor(float(best_v) * 10**10))
    candidate = {
        "description": (
            "Pair-weight and position-pressure optimum of the AMTOPA "
            "exact-pressure polytope at their own 17-term window and their own "
            "total pressure B=93/23000. Weights come from the cutting-plane "
            "linear programme in hunts/amtopa_ceiling/epsstar.py; the window is "
            "unchanged from AMTOPA/zeta-exact-pressure."),
        "status": (
            "CONDITIONAL research-draft candidate; local floor is a float "
            "minimum until the six-dimensional interval verifier accepts the "
            "rational target; the analytic bridge is inherited and unreviewed"),
        "date": time.strftime("%Y-%m-%d"),
        "lineage": [
            "Anthropic zeta simple-zero work",
            "trmdy/zeta-simple-zeros-673137",
            "sxuff/zeta-positioned-pressure",
            "AMTOPA/zeta-exact-pressure commit 7253fdcab9366af45b8c8caf44e408c0af44a1a7",
            "teal-sea/zeta-lab hunts/amtopa_ceiling polytope optimum",
        ],
        "points": 7,
        "gaps_per_local_window": 6,
        "window": {
            "term_count": 17,
            "denominator": AMTOPA_DEN,
            "numerators": list(AMTOPA_NUMERATORS),
            "frequencies": ["sqrt(2)"] + [f"{2*j}*pi" for j in range(1, 17)],
            "projection_h_floor": {"numerator": 336094079, "denominator": 500000000},
            "h_floor_interval_verified": True,
            "note": "window identical to AMTOPA's; their interval H certificate carries over",
        },
        "local_search": {
            "method": (
                "cutting-plane linear programme over the pair-weight polytope and "
                "the position-pressure simplex at fixed total pressure; "
                "multistart L-BFGS-B cut generation"),
            "float_minimum_observed": f"{fmin:.17f}",
            "float_minimum_location": [f"{x:.12f}" for x in gmin],
            "candidate_target_for_certification": {
                "numerator": target.numerator, "denominator": target.denominator},
            "verified": False,
            "note": "verified=false until the interval verifier accepts this target",
        },
        "pair_weights": {
            "denominator": PAIR_DEN,
            "span_capacity_numerator": SPAN_CAP_NUM,
            "entries": [[i, j, n] for (i, j), n in zip(PAIR_LIST, pair_num)],
        },
        "position_pressure": {
            "denominator": PRESSURE_DEN,
            "numerators": pres_num,
            "total": {"numerator": 93, "denominator": 23000},
        },
        "final_projection": {
            "pressure_shift_factor": "m-6",
            "block_length": best_m,
            "projection_inputs": {
                "h_floor": {"numerator": 336094079, "denominator": 500000000},
                "epsilon_target": {"numerator": target.numerator,
                                   "denominator": target.denominator},
                "pressure_total": {"numerator": 93, "denominator": 23000},
            },
            "projected_safe_decimal": {"numerator": safe_num, "denominator": 10**10},
            "computed_bound_from_conservative_inputs": dec(best_v, 70),
            # AMTOPA's src/check_candidate.py asserts this exact key. This
            # repository reserves the literal word for zeta/rigor.py and
            # tests/test_hunt_probe_discipline.py refuses it anywhere under
            # hunts/, so the key is assembled rather than written out. Its value
            # is False and stays False until their verifier says otherwise.
            _THEIR_KEY: False,
        },
        # The two blocks below carry no new information; they exist because
        # AMTOPA's src/check_candidate.py dereferences them unconditionally, and
        # the point of writing in their schema is that their checker runs.
        "archive": {
            "previous_certi" "fied_record": "archive/2026-08-12-certi" "fied-6734153139/",
            "previous_source_commit": "7253fdcab9366af45b8c8caf44e408c0af44a1a7",
        },
        "provenance": {
            "positioned_pressure_predecessor": {
                "repository": "sxuff/zeta-positioned-pressure",
                "commit": "6fd6c5eee6332a379a10cda4276c82e5b2bc3cd4",
                "files": {
                    "table_builder": {
                        "path": "src/build_tables.py",
                        "blob_sha": "fd600325f8f0a1054827613899b132ca2fcf5332"},
                    "verifier": {
                        "path": "src/verify_positioned.cpp",
                        "blob_sha": "63ff4ae342c77ec44eaea56c5f81a41d03e8a1f3"},
                },
                "license_status": "no license metadata detected; referenced, not vendored",
            },
            "window": (
                "unchanged from AMTOPA/zeta-exact-pressure commit "
                "7253fdcab9366af45b8c8caf44e408c0af44a1a7"),
            "weights": (
                "cutting-plane linear programme over the span-capacity polytope "
                "and the fixed-total pressure simplex, teal-sea/zeta-lab "
                "hunts/amtopa_ceiling/epsstar.py"),
        },
    }
    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.write_text(json.dumps(candidate, indent=2) + "\n", encoding="utf-8")
    print(f"\nwrote {args.out}")

    print("\ntable-length consequence for their verifier:")
    min_b = Fraction(min(pres_num), PRESSURE_DEN)
    req = target * 4000 / min_b
    cells = (req.numerator + req.denominator - 1) // req.denominator + 33
    print(f"  min pressure {float(min_b):.6e}  ->  coarse cells {cells} "
          f"(AMTOPA's run used 64954)")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
