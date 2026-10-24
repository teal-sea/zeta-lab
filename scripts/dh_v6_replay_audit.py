#!/usr/bin/env python
"""Recompute the Davenport-Heilbronn v6 replay counts from the raw receipts.

Companion to ``docs/46-davenport-heilbronn-v6-arb-replay.md``. The receipts in
``data/dh_v6_replay/receipts.tar.gz`` are the raw per-window and per-row JSON
emitted by the 2026-10-24 same-verifier Arb replay (400 windows, 1,268 rows).
This script trusts none of the summary numbers in that note: it re-derives
every count, the de-duplication, and the window/row closure from the receipts
and from the v6 closure table, and exits non-zero on the first disagreement.

What it checks (stdlib only, no ball arithmetic: this is bookkeeping, not a
re-run of the verifier):

* manifest hashes of the tarball and of every member;
* 400 distinct window receipts ``w = 0..399`` with contiguous ``[t_lo, t_hi)``
  covering ``[0, 20000)``, every one ``status == computed`` with runner exit 0,
  ``N_S == S_sign_changes``, no undecided separator sign, ``imag_not_zero == 0``;
* 1,268 distinct row receipts, each ``winding == 1``, ``verdict == confirmed``,
  with a Rouche radius present;
* closure: per window, the number of listed rows with ``t`` in the window equals
  that window's ``N_R``, equals the v6 closure table's ``offline_pairs_v6``, and
  ``N_S`` equals ``online_zeros_certified`` with ``total = N_S + 2 N_R``;
* sums ``N_R = 1268``, ``N_S = 25078``, total multiplicity ``27614``;
* every row's minimum Rouche disc lies strictly inside its window, and the
  rows whose larger winding box crosses a window border are listed (two are
  expected: rows 615 and 655).

``--lesion NAME`` plants a fault in memory after loading and expects the audit
to FAIL; the process then exits 0 only if the fault was caught. Available
lesions: ``drop-row`` (delete one row receipt), ``shift-count`` (decrement one
window's ``N_R``), ``dup-window`` (replace window 7 by a copy of window 8).

Usage:
    .venv/bin/python scripts/dh_v6_replay_audit.py            # audit, exit 0 on pass
    .venv/bin/python scripts/dh_v6_replay_audit.py --lesion drop-row
    .venv/bin/python scripts/dh_v6_replay_audit.py --json      # machine-readable summary
"""

from __future__ import annotations

import argparse
import csv
import hashlib
import io
import json
import math
import os
import sys
import tarfile

REPO_ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
DATA_DIR = os.path.join(REPO_ROOT, "data", "dh_v6_replay")
TARBALL = os.path.join(DATA_DIR, "receipts.tar.gz")
MANIFEST = os.path.join(DATA_DIR, "manifest.json")

N_WINDOWS = 400
WINDOW_HEIGHT = 50.0
EXPECTED_ROWS = 1268
EXPECTED_ONLINE = 25078
LESIONS = ("drop-row", "shift-count", "dup-window")


class AuditFailure(AssertionError):
    """Raised on the first disagreement between receipts and expectations."""


def _check(cond: bool, msg: str) -> None:
    if not cond:
        raise AuditFailure(msg)


def _sha256_bytes(b: bytes) -> str:
    return hashlib.sha256(b).hexdigest()


def load_receipts(tarball: str = TARBALL, manifest_path: str = MANIFEST):
    """Return (windows, rows, closure, member_hashes) read straight from the tarball."""
    with open(manifest_path) as fh:
        manifest = json.load(fh)
    with open(tarball, "rb") as fh:
        blob = fh.read()
    _check(
        _sha256_bytes(blob) == manifest["receipts_tar_gz_sha256"],
        "receipts.tar.gz hash differs from manifest",
    )
    windows: dict[int, dict] = {}
    rows: list[dict] = []
    closure: list[dict] = []
    member_hashes: dict[str, str] = {}
    with tarfile.open(fileobj=io.BytesIO(blob), mode="r:gz") as tf:
        for m in tf.getmembers():
            if not m.isfile():
                continue
            data = tf.extractfile(m).read()
            member_hashes[m.name] = _sha256_bytes(data)
            if m.name.startswith("receipts/") and m.name.endswith(".json"):
                rec = json.loads(data)
                _check(rec["w"] not in windows, f"duplicate window receipt w={rec['w']}")
                windows[rec["w"]] = rec
            elif m.name == "rows_cert.jsonl":
                rows = [json.loads(line) for line in data.decode().splitlines() if line.strip()]
            elif m.name == "closure_table.csv":
                closure = list(csv.DictReader(io.StringIO(data.decode())))
    for name, want in manifest["members_sha256"].items():
        _check(member_hashes.get(name) == want, f"member hash mismatch: {name}")
    return windows, rows, closure, member_hashes


def plant_lesion(name: str, windows: dict[int, dict], rows: list[dict]) -> None:
    if name == "drop-row":
        rows.pop(len(rows) // 2)
    elif name == "shift-count":
        # pick a window that has at least one off-line pair
        w = next(k for k in sorted(windows) if windows[k]["N_R"] > 0)
        # keep the ball consistent so only the row/closure bookkeeping can catch it
        windows[w]["N_R"] -= 1
        windows[w]["N_R_ball_mid"] = float(windows[w]["N_R"])
    elif name == "dup-window":
        windows[7] = dict(windows[8])
        windows[7]["w"] = 7
    else:  # pragma: no cover
        raise ValueError(f"unknown lesion {name!r}; choose from {LESIONS}")


def audit(windows: dict[int, dict], rows: list[dict], closure: list[dict]) -> dict:
    # --- windows -----------------------------------------------------------
    _check(sorted(windows) == list(range(N_WINDOWS)), "window indices are not exactly 0..399")
    sum_nr = sum_ns = 0
    for w in range(N_WINDOWS):
        rec = windows[w]
        _check(rec["status"] == "computed", f"window {w}: status {rec['status']!r}")
        _check(rec["runner"]["exit"] == 0, f"window {w}: runner exit {rec['runner']['exit']}")
        _check(rec["t_lo"] == w * WINDOW_HEIGHT and rec["t_hi"] == (w + 1) * WINDOW_HEIGHT,
               f"window {w}: bounds {rec['t_lo']},{rec['t_hi']} not contiguous")
        _check(rec["N_S"] == rec["S_sign_changes"], f"window {w}: N_S != S")
        _check(rec["undecided_signs"] == 0, f"window {w}: undecided separator sign")
        _check(rec["imag_not_zero"] == 0, f"window {w}: imag_not_zero flag")
        _check(isinstance(rec["N_R"], int) and rec["N_R"] >= 0, f"window {w}: bad N_R")
        _check(abs(rec["N_R_ball_mid"] - rec["N_R"]) + rec["N_R_ball_rad"] < 0.5,
               f"window {w}: N_R ball does not isolate the integer")
        _check(abs(rec["N_S_ball_mid"] - rec["N_S"]) + rec["N_S_ball_rad"] < 0.5,
               f"window {w}: N_S ball does not isolate the integer")
        sum_nr += rec["N_R"]
        sum_ns += rec["N_S"]

    # --- rows --------------------------------------------------------------
    idx = [r["row"] for r in rows]
    _check(len(idx) == len(set(idx)), "duplicate row receipts")
    _check(sorted(idx) == list(range(EXPECTED_ROWS)), f"row indices are not 0..{EXPECTED_ROWS - 1}")
    rows_per_window = [0] * N_WINDOWS
    border_boxes: list[dict] = []
    for r in rows:
        _check(r["winding"] == 1, f"row {r['row']}: winding {r['winding']}")
        _check(r["verdict"] == "confirmed", f"row {r['row']}: verdict {r['verdict']!r}")
        _check(abs(r["winding_ball_mid"] - 1) + r["winding_ball_rad"] < 0.5,
               f"row {r['row']}: winding ball does not isolate 1")
        rho = r.get("rouche_rho_min")
        _check(rho is not None and rho > 0, f"row {r['row']}: no Rouche radius")
        t = float(r["t"])
        w = int(math.floor(t / WINDOW_HEIGHT))
        _check(0 <= w < N_WINDOWS, f"row {r['row']}: t={t} outside 0..20000")
        rows_per_window[w] += 1
        lo, hi = w * WINDOW_HEIGHT, (w + 1) * WINDOW_HEIGHT
        _check(t - rho > lo and t + rho < hi,
               f"row {r['row']}: Rouche disc crosses a window border")
        h = r["box_half_side"]
        if t - h < lo or t + h > hi:
            border_boxes.append({"row": r["row"], "t": t, "box_half_side": h, "rouche_rho_min": rho})

    # --- closure -----------------------------------------------------------
    _check(len(closure) == N_WINDOWS, f"closure table has {len(closure)} rows, want {N_WINDOWS}")
    for w, c in enumerate(closure):
        rec = windows[w]
        _check(float(c["t_lo"]) == rec["t_lo"] and float(c["t_hi"]) == rec["t_hi"],
               f"closure row {w}: window bounds differ")
        _check(rows_per_window[w] == rec["N_R"],
               f"window {w}: {rows_per_window[w]} listed rows but N_R={rec['N_R']}")
        _check(int(c["offline_pairs_v6"]) == rec["N_R"],
               f"window {w}: closure table offline_pairs_v6 != N_R")
        _check(int(c["online_zeros_certified"]) == rec["N_S"],
               f"window {w}: closure table on-line count != N_S")
        _check(int(c["total_zeros_exact"]) == rec["N_S"] + 2 * rec["N_R"],
               f"window {w}: total != N_S + 2 N_R")
        _check(c["status"] == "CLOSED", f"window {w}: closure status {c['status']!r}")

    _check(sum_nr == EXPECTED_ROWS, f"sum N_R = {sum_nr}, want {EXPECTED_ROWS}")
    _check(sum_ns == EXPECTED_ONLINE, f"sum N_S = {sum_ns}, want {EXPECTED_ONLINE}")
    _check(len(rows) == sum_nr, "row receipt count != sum N_R")
    _check([b["row"] for b in border_boxes] == [615, 655],
           f"rows with boxes crossing a window border: {[b['row'] for b in border_boxes]}, want [615, 655]")

    return {
        "windows": len(windows),
        "rows": len(rows),
        "sum_N_R": sum_nr,
        "sum_N_S": sum_ns,
        "total_multiplicity": sum_ns + 2 * sum_nr,
        "border_crossing_boxes": border_boxes,
        "max_window_seconds": max(w["seconds"] for w in windows.values()),
    }


def main(argv: list[str] | None = None) -> int:
    ap = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    ap.add_argument("--lesion", choices=LESIONS, help="plant a fault and require the audit to fail")
    ap.add_argument("--json", action="store_true", help="print the summary as JSON")
    args = ap.parse_args(argv)

    windows, rows, closure, _ = load_receipts()
    if args.lesion:
        plant_lesion(args.lesion, windows, rows)
        try:
            audit(windows, rows, closure)
        except AuditFailure as e:
            print(f"lesion {args.lesion!r} caught: {e}")
            return 0
        print(f"lesion {args.lesion!r} NOT caught: audit passed on faulted data", file=sys.stderr)
        return 1
    try:
        summary = audit(windows, rows, closure)
    except AuditFailure as e:
        print(f"AUDIT FAILED: {e}", file=sys.stderr)
        return 1
    if args.json:
        print(json.dumps(summary, indent=2))
    else:
        print(f"windows {summary['windows']}/400, rows {summary['rows']}/1268, "
              f"sum N_R {summary['sum_N_R']}, sum N_S {summary['sum_N_S']}, "
              f"total {summary['total_multiplicity']}; border-crossing boxes: "
              f"{[b['row'] for b in summary['border_crossing_boxes']]}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
