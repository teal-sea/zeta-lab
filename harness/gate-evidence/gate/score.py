"""Mechanical scorer for the harness gate. No judgment, no tallying by hand.

Reads results.json — one record per run:
    {"claim": "C01", "arm": "A"|"B", "verdict": "SOUND"|"DEFECTIVE"|"UNPARSEABLE",
     "wall_seconds": float|null, "chars": int|null}

Applies the criterion frozen in HARNESS-GATE-2026-08-13.md §7:
    b = claims where B correct and A wrong
    c = claims where A correct and B wrong
    GATE PASSES iff b - c >= 3.  Anything else is a FAIL.
"""

from __future__ import annotations

import json
import math
from pathlib import Path

HERE = Path(__file__).resolve().parent
THRESHOLD = 3


def exact_binomial_two_sided(b: int, c: int) -> float | None:
    """Exact McNemar p over discordant pairs. Reported, never part of the gate."""
    n = b + c
    if n == 0:
        return None
    k = min(b, c)
    tail = sum(math.comb(n, i) for i in range(0, k + 1)) / (2 ** n)
    return min(1.0, 2 * tail)


def main() -> int:
    key = json.loads((HERE / "key.json").read_text())
    results = json.loads((HERE / "results.json").read_text())

    by_claim: dict[str, dict[str, dict]] = {}
    for row in results:
        by_claim.setdefault(row["claim"], {})[row["arm"]] = row

    voided = [cid for cid in key if set(by_claim.get(cid, {})) != {"A", "B"}]
    paired = [cid for cid in sorted(key) if cid not in voided]

    b = c = both = neither = 0
    rows = []
    for cid in paired:
        truth = key[cid]
        a_ok = by_claim[cid]["A"]["verdict"] == truth
        b_ok = by_claim[cid]["B"]["verdict"] == truth
        if b_ok and not a_ok:
            b += 1
        elif a_ok and not b_ok:
            c += 1
        elif a_ok and b_ok:
            both += 1
        else:
            neither += 1
        rows.append((cid, truth, by_claim[cid]["A"]["verdict"], a_ok,
                     by_claim[cid]["B"]["verdict"], b_ok))

    print(f"{'claim':<6} {'truth':<10} {'ArmA':<11} {'':<3} {'ArmB':<11}")
    for cid, truth, av, a_ok, bv, b_ok in rows:
        print(f"{cid:<6} {truth:<10} {av:<11} {'ok ' if a_ok else 'MISS':<3} "
              f"{bv:<11} {'ok' if b_ok else 'MISS'}")

    a_correct = sum(1 for r in rows if r[3])
    b_correct = sum(1 for r in rows if r[5])
    n = len(paired)

    print()
    print(f"paired claims           : {n}" + (f"  (voided: {voided})" if voided else ""))
    print(f"Arm A correct (control) : {a_correct}/{n}")
    print(f"Arm B correct (harness) : {b_correct}/{n}")
    print(f"both correct            : {both}")
    print(f"neither correct         : {neither}")
    print(f"b (B right, A wrong)    : {b}")
    print(f"c (A right, B wrong)    : {c}")
    print(f"b - c                   : {b - c}")
    p = exact_binomial_two_sided(b, c)
    print(f"exact McNemar p         : "
          + ("n/a (no discordant pairs)" if p is None else f"{p:.4f}")
          + "   [reported, NOT part of the gate]")

    for arm in ("A", "B"):
        walls = [r["wall_seconds"] for r in results
                 if r["arm"] == arm and r.get("wall_seconds")]
        chars = [r["chars"] for r in results if r["arm"] == arm and r.get("chars")]
        print(f"Arm {arm} effort proxies    : "
              f"median wall {sorted(walls)[len(walls)//2]:.0f}s, "
              f"median response {sorted(chars)[len(chars)//2]} chars"
              if walls and chars else f"Arm {arm} effort proxies    : not captured")

    passed = (b - c) >= THRESHOLD
    print()
    print("=" * 62)
    print(f"CRITERION (frozen): b - c >= {THRESHOLD}")
    print(f"OBSERVED         : b - c = {b - c}")
    print(f"GATE             : {'PASS' if passed else 'FAIL'}")
    print("=" * 62)
    if not passed and both == n:
        print("note: ceiling — both arms answered every paired claim correctly.")
    if not passed and neither == n:
        print("note: floor — neither arm answered any paired claim correctly.")
    return 0 if passed else 1


if __name__ == "__main__":
    raise SystemExit(main())
