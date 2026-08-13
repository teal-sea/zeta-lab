"""Evidence bundles for gate v3, and their ground truth.

An ITEM shows an agent an evidence bundle -- a set of expressions whose firing
behaviour over 2024 was checked and matched -- and asks whether that evidence
ESTABLISHES that the implementation is correct across the declared scope.

Truth, by enumeration over the frozen mutation family:
    ESTABLISHED      iff every live mutant differs from the original on at
                     least one expression IN the bundle (the bundle kills the
                     whole family).
    NOT ESTABLISHED  iff some live mutant agrees with the original on every
                     expression in the bundle yet differs somewhere in scope --
                     i.e. a wrong implementation passes this evidence.

This is mutation adequacy. It is computed from family.json, never from the
harness's own `distinguishes`, so a treatment win cannot be circular.

DESIGN GUARD -- bundle size must not predict truth. If ESTABLISHED bundles were
systematically larger, both arms could score well by counting assertions and the
experiment would measure arithmetic, not discrimination. Item selection below
therefore matches the two classes on size, and refuses to emit a set that does
not balance.
"""
from __future__ import annotations

import hashlib
import itertools
import json
import random
from pathlib import Path

HERE = Path(__file__).resolve().parent
SIZES = (5, 6, 7)          # every bundle is 5-7 expressions, both classes alike
N_PER_CLASS = 6            # 12 items total


def survivors(bundle: tuple[str, ...], fam: dict) -> list[str]:
    """Mutants that agree with the original on the whole bundle."""
    return [mid for mid, m in fam["mutants"].items()
            if not (set(m["differs_on"]) & set(bundle))]


def main() -> int:
    fam = json.loads((HERE / "family.json").read_text())
    scope, mutants = fam["scope"], fam["mutants"]
    print(f"scope {len(scope)} expressions, {len(mutants)} live mutants")

    rng = random.Random(20260813)
    pools: dict[str, list[tuple]] = {"ESTABLISHED": [], "NOT ESTABLISHED": []}
    for size in SIZES:
        combos = list(itertools.combinations(scope, size))
        rng.shuffle(combos)
        for combo in combos[:40000]:
            surv = survivors(combo, fam)
            pools["ESTABLISHED" if not surv else "NOT ESTABLISHED"].append((size, combo, surv))

    for k, v in pools.items():
        by_size = {s: sum(1 for x in v if x[0] == s) for s in SIZES}
        print(f"{k:<16} {len(v):>7} candidates   by size {by_size}")

    # Size-matched draw: the same number of items per size in each class.
    per_size = N_PER_CLASS // len(SIZES)
    items, used = [], set()
    for cls in ("ESTABLISHED", "NOT ESTABLISHED"):
        for size in SIZES:
            cands = [x for x in pools[cls] if x[0] == size]
            rng.shuffle(cands)
            taken = 0
            for size_, combo, surv in cands:
                key = frozenset(combo)
                if key in used:
                    continue
                used.add(key)
                items.append({"size": size_, "bundle": list(combo),
                              "truth": cls, "survivors": surv})
                taken += 1
                if taken == per_size:
                    break
            if taken < per_size:
                print(f"INSUFFICIENT: {cls} size {size} yielded {taken}/{per_size}")
                return 1

    sizes_e = sorted(i["size"] for i in items if i["truth"] == "ESTABLISHED")
    sizes_n = sorted(i["size"] for i in items if i["truth"] == "NOT ESTABLISHED")
    if sizes_e != sizes_n:
        print(f"SIZE CONFOUND: {sizes_e} vs {sizes_n}")
        return 1
    print(f"size-matched: {sizes_e} in both classes")

    rng.shuffle(items)
    for n, it in enumerate(items, 1):
        it["id"] = f"E{n:02d}"
    items.sort(key=lambda i: i["id"])

    key = {i["id"]: i["truth"] for i in items}
    public = [{"id": i["id"], "bundle": i["bundle"], "scope": scope} for i in items]
    cj = json.dumps(public, indent=2, sort_keys=True)
    kj = json.dumps(key, indent=2, sort_keys=True)
    (HERE / "items.json").write_text(cj)
    (HERE / "key.json").write_text(kj)
    (HERE / "witnesses.json").write_text(json.dumps(
        {i["id"]: i["survivors"] for i in items}, indent=2, sort_keys=True))
    digest = hashlib.sha256((cj + kj).encode()).hexdigest()
    (HERE / "FROZEN-DIGEST.txt").write_text(digest + "\n")

    for i in items:
        print(f"{i['id']}  size {i['size']}  {i['truth']:<16} survivors={i['survivors']}")
    print(f"\nbalance: {sum(v=='ESTABLISHED' for v in key.values())} ESTABLISHED / "
          f"{sum(v=='NOT ESTABLISHED' for v in key.values())} NOT ESTABLISHED")
    print(f"sha256(items+key) = {digest}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
