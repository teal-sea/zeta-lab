"""Modal job: the n-point pressure inequality, sharded across containers.

Runs ``zeta_simple_zeros.verify_n`` (a generalisation of the published
``verify_seven.py`` to n points, pinned source 040c5e8 plus verify_n.py) with the
initial (n-1)-dimensional box list partitioned round-robin over ``shard_count``
containers, cpu=2 each, 2 h container timeout, a per-shard node cap and a
per-shard time cap below the container timeout so a shard that runs out returns
UNDECIDED instead of dying.

Overall verdict, written to artifacts/verify-n<n>-<num>-<den>-p<p>.json:
  ACCEPTED  iff every shard ACCEPTED
  REFUSED   if any shard REFUSED (the refuting cell is recorded)
  UNDECIDED otherwise, with the list of undecided shards

Run (defaults are the 7-point control; the 8-point stage passes its own values):
  source <(hunts/ainta_seven_point/fetch_upstream.sh) \
  ~/Zeta/.venv/bin/modal run hunts/ainta_seven_point/modal_verify_n.py \
      --n 8 --num <num> --den <den> --p 3000 --grid 4000 --shard-count 64 --presplit-depth 6

``--presplit-depth d`` bisects every initial box d times (the search's own rule)
before the round-robin, so a run with few initial boxes (n=8 near its floor has
128) still spreads evenly; the halves partition the box, so nothing is skipped.

A shard's ACCEPTED means its boxes were exhausted; it is the finite inequality
at one grid and nothing about zeta zeros.
"""
from __future__ import annotations

import json
import os
import sys
import time

import modal

ZSZ_SRC = os.environ.get(
    "ZSZ_SRC", os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "..", ".upstream", "zeta-simple-zeros", "src", "zeta_simple_zeros")
)
HERE = os.path.dirname(os.path.abspath(__file__))

CONTAINER_TIMEOUT = 2 * 3600
DEFAULT_NODE_CAP = 50_000_000
DEFAULT_TIME_CAP = CONTAINER_TIMEOUT - 300  # return UNDECIDED before Modal kills the container

image = (
    modal.Image.debian_slim(python_version="3.12")
    .pip_install("python-flint==0.9.0")
    .add_local_dir(ZSZ_SRC, remote_path="/root/zsz/zeta_simple_zeros")
)
app = modal.App("zeta-hunt-verify-n", image=image)


@app.function(cpu=2, timeout=CONTAINER_TIMEOUT)
def verify_n_shard(args: dict) -> dict:
    """One shard of the initial box list; returns verify_n's result dict."""

    sys.path.insert(0, "/root/zsz")
    from zeta_simple_zeros.verify_n import verify_n

    t0 = time.perf_counter()
    try:
        result = verify_n(
            args["n"],
            args["num"],
            args["den"],
            grid=args["grid"],
            pressure=args["p"],
            precision_bits=args.get("precision", 128),
            shard_index=args["shard_index"],
            shard_count=args["shard_count"],
            node_cap=args.get("node_cap", DEFAULT_NODE_CAP),
            time_cap_seconds=args.get("time_cap", DEFAULT_TIME_CAP),
            use_tangent_prune=args.get("tangent", True),
            presplit_depth=args.get("presplit_depth", 0),
        )
    except Exception as exc:  # a crashed shard decides nothing
        result = {
            "outcome": "UNDECIDED",
            "stop_reason": "exception",
            "error": f"{type(exc).__name__}: {exc}"[:500],
            "shard_index": args["shard_index"],
            "shard_count": args["shard_count"],
            "nodes": 0,
        }
    result["container_seconds"] = round(time.perf_counter() - t0, 1)
    return result


def _verdict(shards: list[dict], shard_count: int) -> dict:
    by_index = {s["shard_index"]: s for s in shards}
    missing = [i for i in range(shard_count) if i not in by_index]
    refused = [s for s in shards if s["outcome"] == "REFUSED"]
    undecided = [s["shard_index"] for s in shards if s["outcome"] == "UNDECIDED"] + missing
    if refused:
        overall = "REFUSED"
    elif not undecided and len(by_index) == shard_count and all(
        s["outcome"] == "ACCEPTED" for s in shards
    ):
        overall = "ACCEPTED"
    else:
        overall = "UNDECIDED"
    return {
        "overall": overall,
        "shards_returned": len(by_index),
        "shards_accepted": sum(1 for s in shards if s["outcome"] == "ACCEPTED"),
        "shards_refused": [s["shard_index"] for s in refused],
        "shards_undecided": sorted(undecided),
        "refuting_cells": [
            {"shard_index": s["shard_index"], "cell": s.get("refuting_cell"),
             "gaps": s.get("refuting_cell_gaps"), "lower_hex": s.get("refuting_lower_hex")}
            for s in refused
        ],
        "nodes_total": sum(s.get("nodes", 0) for s in shards),
        "max_depth": max((s.get("maximum_depth", 0) for s in shards), default=0),
        "pressure_pruned_total": sum(s.get("pressure_pruned", 0) for s in shards),
        "interval_pruned_total": sum(s.get("interval_pruned", 0) for s in shards),
        "tangent_pruned_total": sum(s.get("tangent_pruned", 0) for s in shards),
        "container_seconds_max": max((s.get("container_seconds", 0) for s in shards), default=0),
        "container_seconds_sum": round(sum(s.get("container_seconds", 0) for s in shards), 1),
    }


@app.local_entrypoint()
def main(
    n: int = 7,
    num: int = 19,
    den: int = 5000,
    p: int = 3000,
    grid: int = 4000,
    shard_count: int = 8,
    node_cap: int = DEFAULT_NODE_CAP,
    time_cap: int = DEFAULT_TIME_CAP,
    precision: int = 128,
    presplit_depth: int = 0,
    out: str = "",
):
    t0 = time.perf_counter()
    out = out or os.path.join(HERE, "artifacts", f"verify-n{n}-{num}-{den}-p{p}.json")
    os.makedirs(os.path.dirname(out), exist_ok=True)
    jobs = [
        {"n": n, "num": num, "den": den, "p": p, "grid": grid, "precision": precision,
         "shard_index": i, "shard_count": shard_count, "node_cap": node_cap, "time_cap": time_cap,
         "presplit_depth": presplit_depth}
        for i in range(shard_count)
    ]
    header = {
        "n_points": n, "target": f"{num}/{den}", "target_float": num / den, "pressure": p,
        "grid": grid, "precision_bits": precision, "shard_count": shard_count,
        "node_cap_per_shard": node_cap, "time_cap_per_shard": time_cap, "presplit_depth": presplit_depth,
        "container_timeout": CONTAINER_TIMEOUT, "cpu_per_container": 2,
        "verifier": "zeta_simple_zeros.verify_n (generalised verify_seven.py, cutoff derived from target)",
        "zsz_src": ZSZ_SRC,
    }
    shards: list[dict] = []

    def write() -> dict:
        verdict = _verdict(shards, shard_count)
        payload = {**header, **verdict, "wall_seconds": round(time.perf_counter() - t0),
                   "shards": sorted(shards, key=lambda s: s["shard_index"])}
        with open(out, "w", encoding="utf-8") as f:
            json.dump(payload, f, indent=1)
        return verdict

    for result in verify_n_shard.map(jobs, order_outputs=False, return_exceptions=True):
        if not isinstance(result, dict):
            # the map machinery itself failed for one shard; recorded as undecided
            # under an unknown index, counted via the missing-shard rule in _verdict
            shards.append({"outcome": "UNDECIDED", "stop_reason": "map_exception",
                           "error": str(result)[:500], "shard_index": -1,
                           "shard_count": shard_count, "nodes": 0})
        else:
            shards.append(result)
        verdict = write()
        s = shards[-1]
        print(f"shard {s.get('shard_index')}: {s['outcome']} nodes={s.get('nodes')} "
              f"depth={s.get('maximum_depth')} cell={s.get('refuting_cell')} "
              f"{s.get('container_seconds')}s  [{verdict['shards_returned']}/{shard_count} in, "
              f"overall so far {verdict['overall']}]", flush=True)

    verdict = write()
    print(json.dumps({k: verdict[k] for k in ("overall", "shards_accepted", "shards_refused",
                                              "shards_undecided", "refuting_cells", "nodes_total",
                                              "max_depth", "container_seconds_max")}, indent=1))
    print(f"wrote {out} after {time.perf_counter() - t0:.0f}s")
