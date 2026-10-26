"""Fail-closed check of one workflow block: every requested shard produced a sound JSON.

    python3 hunts/skewes_enclosure/check_block.py out 217 218 219 220

Exit 1 unless each shard k has out/shard_kkk.json that parses, carries
n0 = (k-1)*1e5 + 1 and num = 1e5, has its balls ordered and disjoint, and shows a
sign change at every route-2 sampled bracket.
"""

from __future__ import annotations

import json
import sys
from pathlib import Path

SHARD = 100_000


def problems(out: Path, ks: list[int]) -> list[str]:
    bad = []
    for k in ks:
        f = out / f"shard_{k:03d}.json"
        try:
            d = json.loads(f.read_text())
        except (OSError, ValueError) as exc:
            bad.append(f"shard {k}: {exc}")
            continue
        if d.get("n0") != (k - 1) * SHARD + 1 or d.get("num") != SHARD:
            bad.append(f"shard {k}: n0/num {d.get('n0')}/{d.get('num')}")
        if d.get("ordered_disjoint") is not True:
            bad.append(f"shard {k}: balls not ordered and disjoint")
        if d.get("route2_sample", {}).get("all_sign_changes") is not True:
            bad.append(f"shard {k}: route-2 failures {d.get('route2_sample', {}).get('failures')}")
    return bad


if __name__ == "__main__":
    out = Path(sys.argv[1])
    ks = [int(x) for x in sys.argv[2:]]
    bad = problems(out, ks)
    for b in bad:
        print(b)
    print(f"{len(ks) - len({b.split(':')[0] for b in bad})}/{len(ks)} shards sound")
    raise SystemExit(1 if bad or not ks else 0)
