"""Modal job: retry one UNDECIDED shard of modal_verify_n.py, re-split into sub-shards.

Takes the parent run's parameters (n, target, p, grid, shard_count, presplit_depth)
and one parent shard index, rebuilds exactly that shard's initial box list with
``verify_n.prepare`` + ``shard_boxes`` (deterministic, so it is the same list the
parent container searched), bisects every one of those boxes ``extra_depth`` more
times with the search's own rule (``verify_n.presplit``; the halves partition the
box, so nothing is skipped), shuffles the result with a fixed seed so that the
hard neighbourhood of the minimiser is spread across sub-shards instead of landing
in one of them (which is what round-robin over a deterministic bisection order
does: index mod 2^j is the last j bisection choices), and round-robins the
shuffled list over ``sub_count`` containers.

Exhaustiveness: the parent shard's boxes are partitioned by the presplit, the
shuffle is a permutation, and the round-robin covers every index, so the union
of the sub-shards' boxes is exactly the parent shard's box list. The parent run
is ACCEPTED iff its other shards are ACCEPTED and every sub-shard here is
ACCEPTED; that combination is stated in the output JSON, not asserted by code.

Run:
  source <(hunts/ainta_seven_point/fetch_upstream.sh) \
  ~/Zeta/.venv/bin/modal run hunts/ainta_seven_point/modal_verify_n_resplit.py \
      --n 8 --num 41763 --den 10000000 --p 3200 --grid 4000 \
      --parent-shard-count 64 --parent-presplit-depth 7 --parent-shard 0 \
      --sub-count 4 --extra-depth 12 --seed 1
"""
from __future__ import annotations

import json
import os
import random
import sys
import time

import modal

ZSZ_SRC = os.environ.get(
    "ZSZ_SRC", os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "..", ".upstream", "zeta-simple-zeros", "src", "zeta_simple_zeros")
)
HERE = os.path.dirname(os.path.abspath(__file__))

CONTAINER_TIMEOUT = 2 * 3600
DEFAULT_NODE_CAP = 50_000_000
DEFAULT_TIME_CAP = CONTAINER_TIMEOUT - 300

image = (
    modal.Image.debian_slim(python_version="3.12")
    .pip_install("python-flint==0.9.0")
    .add_local_dir(ZSZ_SRC, remote_path="/root/zsz/zeta_simple_zeros")
)
app = modal.App("zeta-hunt-verify-n-resplit", image=image)


def _subshard_boxes(prepared, args: dict):
    """Parent shard's boxes -> extra presplit -> seeded shuffle; returns the full list."""

    from zeta_simple_zeros.verify_n import presplit, shard_boxes

    parent = shard_boxes(prepared.boxes, args["parent_shard"], args["parent_shard_count"])
    boxes = presplit(parent, args["extra_depth"])
    rng = random.Random(args["seed"])
    rng.shuffle(boxes)
    return parent, boxes


@app.function(cpu=2, timeout=CONTAINER_TIMEOUT)
def verify_n_subshard(args: dict) -> dict:
    sys.path.insert(0, "/root/zsz")
    from zeta_simple_zeros.verify_n import prepare, search

    t0 = time.perf_counter()
    try:
        prepared = prepare(
            args["n"], args["num"], args["den"], args["grid"], args["p"],
            args.get("precision", 128), presplit_depth=args["parent_presplit_depth"],
        )
        parent, boxes = _subshard_boxes(prepared, args)
        prepared.boxes = boxes
        prepared.presplit_depth = args["parent_presplit_depth"] + args["extra_depth"]
        remaining = max(1e-9, args["time_cap"] - (time.perf_counter() - t0))
        result = search(
            prepared,
            shard_index=args["sub_index"],
            shard_count=args["sub_count"],
            node_cap=args["node_cap"],
            time_cap_seconds=remaining,
            use_tangent_prune=args.get("tangent", True),
        )
        result.update({
            "parent_shard": args["parent_shard"],
            "parent_shard_count": args["parent_shard_count"],
            "parent_presplit_depth": args["parent_presplit_depth"],
            "parent_shard_boxes": len(parent),
            "extra_depth": args["extra_depth"],
            "shuffle_seed": args["seed"],
            "sub_index": args["sub_index"],
            "sub_count": args["sub_count"],
            "time_cap_seconds": args["time_cap"],
            "elapsed_seconds": time.perf_counter() - t0,
        })
    except Exception as exc:
        result = {
            "outcome": "UNDECIDED", "stop_reason": "exception",
            "error": f"{type(exc).__name__}: {exc}"[:500],
            "sub_index": args["sub_index"], "sub_count": args["sub_count"],
            "shard_index": args["sub_index"], "shard_count": args["sub_count"], "nodes": 0,
        }
    result["container_seconds"] = round(time.perf_counter() - t0, 1)
    return result


def _verdict(shards: list[dict], sub_count: int) -> dict:
    by_index = {s["sub_index"]: s for s in shards}
    missing = [i for i in range(sub_count) if i not in by_index]
    refused = [s for s in shards if s["outcome"] == "REFUSED"]
    undecided = [s["sub_index"] for s in shards if s["outcome"] == "UNDECIDED"] + missing
    if refused:
        overall = "REFUSED"
    elif not undecided and len(by_index) == sub_count and all(
        s["outcome"] == "ACCEPTED" for s in shards
    ):
        overall = "ACCEPTED"
    else:
        overall = "UNDECIDED"
    return {
        "overall_for_parent_shard": overall,
        "subshards_returned": len(by_index),
        "subshards_accepted": sum(1 for s in shards if s["outcome"] == "ACCEPTED"),
        "subshards_refused": [s["sub_index"] for s in refused],
        "subshards_undecided": sorted(undecided),
        "refuting_cells": [
            {"sub_index": s["sub_index"], "cell": s.get("refuting_cell"),
             "gaps": s.get("refuting_cell_gaps"), "lower_hex": s.get("refuting_lower_hex")}
            for s in refused
        ],
        "nodes_total": sum(s.get("nodes", 0) for s in shards),
        "max_depth": max((s.get("maximum_depth", 0) for s in shards), default=0),
        "pressure_pruned_total": sum(s.get("pressure_pruned", 0) for s in shards),
        "interval_pruned_total": sum(s.get("interval_pruned", 0) for s in shards),
        "tangent_pruned_total": sum(s.get("tangent_pruned", 0) for s in shards),
        "initial_boxes_shard_sum": sum(s.get("initial_boxes_shard", 0) for s in shards),
        "initial_boxes_total_reported": sorted({s.get("initial_boxes_total") for s in shards}),
        "container_seconds_max": max((s.get("container_seconds", 0) for s in shards), default=0),
        "container_seconds_sum": round(sum(s.get("container_seconds", 0) for s in shards), 1),
    }


@app.local_entrypoint()
def main(
    n: int = 8,
    num: int = 41763,
    den: int = 10000000,
    p: int = 3200,
    grid: int = 4000,
    parent_shard_count: int = 64,
    parent_presplit_depth: int = 7,
    parent_shard: int = 0,
    sub_count: int = 4,
    extra_depth: int = 12,
    seed: int = 1,
    node_cap: int = DEFAULT_NODE_CAP,
    time_cap: int = DEFAULT_TIME_CAP,
    precision: int = 128,
    out: str = "",
):
    t0 = time.perf_counter()
    out = out or os.path.join(
        HERE, "artifacts", f"verify-n{n}-{num}-{den}-p{p}-resplit-shard{parent_shard}.json"
    )
    os.makedirs(os.path.dirname(out), exist_ok=True)
    jobs = [
        {"n": n, "num": num, "den": den, "p": p, "grid": grid, "precision": precision,
         "parent_shard_count": parent_shard_count, "parent_presplit_depth": parent_presplit_depth,
         "parent_shard": parent_shard, "sub_index": i, "sub_count": sub_count,
         "extra_depth": extra_depth, "seed": seed, "node_cap": node_cap, "time_cap": time_cap}
        for i in range(sub_count)
    ]
    header = {
        "n_points": n, "target": f"{num}/{den}", "target_float": num / den, "pressure": p,
        "grid": grid, "precision_bits": precision,
        "parent_run": f"verify-n{n}-{num}-{den}-p{p}.json",
        "parent_shard": parent_shard, "parent_shard_count": parent_shard_count,
        "parent_presplit_depth": parent_presplit_depth,
        "sub_count": sub_count, "extra_depth": extra_depth, "shuffle_seed": seed,
        "node_cap_per_subshard": node_cap, "time_cap_per_subshard": time_cap,
        "container_timeout": CONTAINER_TIMEOUT, "cpu_per_container": 2,
        "combination_rule": "parent run ACCEPTED iff every other parent shard ACCEPTED and every sub-shard here ACCEPTED",
        "zsz_src": ZSZ_SRC,
    }
    shards: list[dict] = []

    def write() -> dict:
        verdict = _verdict(shards, sub_count)
        payload = {**header, **verdict, "wall_seconds": round(time.perf_counter() - t0),
                   "subshards": sorted(shards, key=lambda s: s["sub_index"])}
        with open(out, "w", encoding="utf-8") as f:
            json.dump(payload, f, indent=1)
        return verdict

    for result in verify_n_subshard.map(jobs, order_outputs=False, return_exceptions=True):
        if not isinstance(result, dict):
            shards.append({"outcome": "UNDECIDED", "stop_reason": "map_exception",
                           "error": str(result)[:500], "sub_index": -1,
                           "sub_count": sub_count, "nodes": 0})
        else:
            shards.append(result)
        verdict = write()
        s = shards[-1]
        print(f"sub-shard {s.get('sub_index')}: {s['outcome']} nodes={s.get('nodes')} "
              f"depth={s.get('maximum_depth')} cell={s.get('refuting_cell')} "
              f"stop={s.get('stop_reason')} {s.get('container_seconds')}s  "
              f"[{verdict['subshards_returned']}/{sub_count} in, so far {verdict['overall_for_parent_shard']}]",
              flush=True)

    verdict = write()
    print(json.dumps({k: verdict[k] for k in ("overall_for_parent_shard", "subshards_accepted",
                                              "subshards_refused", "subshards_undecided",
                                              "refuting_cells", "nodes_total", "max_depth",
                                              "initial_boxes_shard_sum", "container_seconds_max")},
                     indent=1))
    print(f"wrote {out} after {time.perf_counter() - t0:.0f}s")
