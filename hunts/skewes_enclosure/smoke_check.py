"""Fail-closed smoke check: does this machine reproduce the lab box's zeros and sums?

Recomputes gamma_1999901 .. gamma_2000000 (the top 100 zeros of target A's range)
with the production settings, then compares the SHA-256 of the printed balls and
both partial sums with ``smoke_reference.json``. The reference was written on
the lab box with the versions that ran target A (python-flint 0.9.0, mpmath
1.3.0). A's shards digest 1e5 zeros at a time, so the only direct tie to run A
is the last zero: it must equal ``shards/shard_020.json``'s ``last`` string.

    python3 hunts/skewes_enclosure/smoke_check.py            # exit 1 on mismatch
    python3 hunts/skewes_enclosure/smoke_check.py --write    # regenerate (box only)
"""

from __future__ import annotations

import argparse
import json
import sys
import time
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import skewes_terms as st  # noqa: E402
import zero_layer as zl  # noqa: E402

REF = HERE / "smoke_reference.json"
N0, NUM, BATCH, PREC = 1_999_901, 100, 100, 64


def compute() -> dict:
    t = time.perf_counter()
    g, _ = zl.arb_zeros(N0, NUM, BATCH, PREC)
    return {
        "n0": N0, "num": NUM, "batch": BATCH, "prec": PREC,
        "zeros_sha256": zl.zeros_digest(g),
        "partial_sums": {
            "chao_plymen": st.lehman_sum(g, st.CHAO_PLYMEN.omega, st.CHAO_PLYMEN.alpha).str(40),
            "saouter_demichel": st.lehman_sum(g, st.SAOUTER_DEMICHEL.omega,
                                              st.SAOUTER_DEMICHEL.alpha).str(40),
        },
        "last": g[-1].str(30),
        "seconds": time.perf_counter() - t,
    }


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--write", action="store_true")
    a = ap.parse_args()
    got = compute()
    if a.write:
        REF.write_text(json.dumps(got, indent=1) + "\n")
        print(json.dumps(got, indent=1))
        return 0
    ref = json.loads(REF.read_text())
    keys = ("n0", "num", "batch", "prec", "zeros_sha256", "partial_sums", "last")
    bad = [k for k in keys if got[k] != ref[k]]
    run_a_last = json.loads((HERE / "shards" / "shard_020.json").read_text())["last"]
    if got["last"] != run_a_last:
        bad.append("last != run A shard_020 last")
    print(json.dumps({"seconds": got["seconds"], "mismatched": bad}, indent=1))
    if bad:
        print("SMOKE CHECK FAILED: this machine does not reproduce the reference", file=sys.stderr)
        return 1
    print("smoke check passed")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
