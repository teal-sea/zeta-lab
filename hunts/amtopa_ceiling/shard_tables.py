#!/usr/bin/env python3
"""Drive AMTOPA's own table builder in shards, so it fits a 20-minute CI job.

Their ``src/build_interval_tables.py`` builds all 84k coarse cells and 168k
midpoints in one process. Measured at 0.0225 CPU-seconds per cell on the
authoring host, that is about 25 CPU-minutes, and a slower shared runner can push
the wall clock past a job timeout.

This wrapper imports **their** module and calls **their** ``coarse_chunk`` and
``midpoint_chunk`` over an index range, so the arithmetic is theirs unchanged. It
writes partial little-endian f64 streams; ``--join`` concatenates them in index
order into exactly the files their C++ verifier reads, and re-derives the
big-endian SHA-256 stream digests their manifest records.

    python3 shard_tables.py --upstream <dir> --out parts --shard 0 --shards 6
    python3 shard_tables.py --upstream <dir> --out parts --join --tables tables

Concatenating in index order reproduces the single-process file byte for byte,
because every cell is computed independently from the candidate alone.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import math
import multiprocessing as mp
import os
import struct
import sys
from fractions import Fraction
from pathlib import Path


def load_upstream(upstream: Path):
    sys.path.insert(0, str(upstream / "src"))
    import build_interval_tables as bit          # noqa: E402
    from candidate_data import load_candidate, rational  # noqa: E402
    return bit, load_candidate, rational


def cell_counts(candidate, rational, grid):
    target = rational(candidate["local_search"]["candidate_target_for_certification"])
    pressure = candidate["position_pressure"]
    den = int(pressure["denominator"])
    min_pressure = min(Fraction(int(x), den) for x in pressure["numerators"])
    required = target * grid / min_pressure
    cells = (required.numerator + required.denominator - 1) // required.denominator + 33
    return cells, 2 * cells + 1


def write_f64(path: Path, values) -> None:
    with path.open("wb") as fh:
        for x in values:
            fh.write(struct.pack("<d", x))


def read_f64(path: Path):
    raw = path.read_bytes()
    return list(struct.unpack("<%dd" % (len(raw) // 8), raw))


def stream_sha256(values) -> str:
    d = hashlib.sha256()
    for x in values:
        d.update(struct.pack(">d", x))
    return d.hexdigest()


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--upstream", type=Path, required=True)
    ap.add_argument("--out", type=Path, default=Path("parts"))
    ap.add_argument("--grid", type=int, default=4000)
    ap.add_argument("--precision", type=int, default=50)
    ap.add_argument("--shard", type=int, default=0)
    ap.add_argument("--shards", type=int, default=1)
    ap.add_argument("--workers", type=int, default=max(1, os.cpu_count() or 1))
    ap.add_argument("--join", action="store_true")
    ap.add_argument("--tables", type=Path, default=Path("tables"))
    args = ap.parse_args()

    bit, load_candidate, rational = load_upstream(args.upstream)
    candidate = load_candidate()
    n_coarse, n_mid = cell_counts(candidate, rational, args.grid)
    args.out.mkdir(parents=True, exist_ok=True)

    names_coarse = ("w_lower.bin", "w_second_lower.bin")
    names_mid = ("w_mid_lower.bin", "w_mid_upper.bin",
                 "w_prime_mid_lower.bin", "w_prime_mid_upper.bin")

    if args.join:
        args.tables.mkdir(parents=True, exist_ok=True)
        manifest = {"grid": args.grid, "precision_decimal_digits": args.precision,
                    "coarse_cells": n_coarse, "midpoint_values": n_mid,
                    "joined_from_shards": args.shards, "files": {}}
        for name, total in [(n, n_coarse) for n in names_coarse] + \
                           [(n, n_mid) for n in names_mid]:
            vals = []
            for s in range(args.shards):
                p = args.out / f"{name}.{s}"
                if not p.exists():
                    raise SystemExit(f"missing shard part {p}")
                vals.extend(read_f64(p))
            if len(vals) != total:
                raise SystemExit(f"{name}: joined {len(vals)} values, expected {total}")
            write_f64(args.tables / name, vals)
            manifest["files"][name] = {
                "length": len(vals),
                "sha256_big_endian_float_stream": stream_sha256(vals)}
        (args.tables / "manifest.json").write_text(
            json.dumps(manifest, indent=2) + "\n", encoding="utf-8")
        print(json.dumps(manifest, indent=2))
        return 0

    def slice_of(total):
        per = math.ceil(total / args.shards)
        lo = args.shard * per
        return lo, min(total, lo + per)

    ctx = mp.get_context("spawn")

    c_lo, c_hi = slice_of(n_coarse)
    tasks = bit.coarse_tasks(c_hi - c_lo, args.workers, args.grid,
                             args.precision, candidate, False)
    tasks = [(s + c_lo, e + c_lo, g, p, cand, lo)
             for (s, e, g, p, cand, lo) in tasks]
    with ctx.Pool(max(1, min(args.workers, max(1, c_hi - c_lo)))) as pool:
        parts = pool.map(bit.coarse_chunk, tasks)
    lower = [0.0] * (c_hi - c_lo)
    second = [0.0] * (c_hi - c_lo)
    for start, lo_vals, sec_vals in parts:
        off = start - c_lo
        lower[off:off + len(lo_vals)] = lo_vals
        second[off:off + len(sec_vals)] = sec_vals
    write_f64(args.out / f"w_lower.bin.{args.shard}", lower)
    write_f64(args.out / f"w_second_lower.bin.{args.shard}", second)

    m_lo, m_hi = slice_of(n_mid)
    tasks = bit.midpoint_tasks(m_hi - m_lo, args.workers, args.grid,
                               args.precision, candidate)
    tasks = [(s + m_lo, e + m_lo, g, p, cand) for (s, e, g, p, cand) in tasks]
    with ctx.Pool(max(1, min(args.workers, max(1, m_hi - m_lo)))) as pool:
        parts = pool.map(bit.midpoint_chunk, tasks)
    cols = [[0.0] * (m_hi - m_lo) for _ in range(4)]
    for start, wl, wh, dl, dh in parts:
        off = start - m_lo
        for k, v in enumerate((wl, wh, dl, dh)):
            cols[k][off:off + len(v)] = v
    for name, v in zip(names_mid, cols):
        write_f64(args.out / f"{name}.{args.shard}", v)

    print(json.dumps({"shard": args.shard, "shards": args.shards,
                      "coarse_range": [c_lo, c_hi],
                      "midpoint_range": [m_lo, m_hi],
                      "coarse_cells_total": n_coarse,
                      "midpoint_values_total": n_mid}, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
