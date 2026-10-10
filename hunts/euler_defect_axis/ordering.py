"""Does the defect ordering actually hold across cutoffs?

`RESULTS.md` asserted, from 2026-09-10 until this file was written the same day,
that the nine loud discriminants "rank in exactly the same order at n < 61 and
at n < 401".  They do not.  This recomputes the orderings from
`artifacts/cutoff.json`, which is the artifact that sentence was read off, and
reports what is actually stable: the head of the list is not, the tail is, and
the ordering settles by cutoff 201.

The sentence was written during a rewrite prompted by an adversarial audit, and
no audit attacked it because it entered the file after the audit ran.  That is
the interesting part and it is recorded in RUNS.md.

    .venv/bin/python hunts/euler_defect_axis/ordering.py
"""
from __future__ import annotations

import itertools
import json
from pathlib import Path

from scipy.stats import spearmanr

ART = Path(__file__).resolve().parent / "artifacts"


def orderings(data: dict) -> dict:
    """Discriminants sorted by defect, largest first, per cutoff."""
    return {c: [d for d, _ in sorted(rows, key=lambda r: -r[1])]
            for c, rows in data.items()}


def inversions(base: list, other: list) -> list:
    """Pairs whose relative order differs between two rankings."""
    return [(x, y) for i, x in enumerate(base) for y in base[i + 1:]
            if other.index(x) > other.index(y)]


def fixed_positions(order: dict) -> list:
    """Positions holding the same discriminant at every cutoff."""
    cuts = list(order)
    n = len(order[cuts[0]])
    return [i for i in range(n)
            if len({order[c][i] for c in cuts}) == 1]


def main() -> None:
    data = json.load(open(ART / "cutoff.json"))
    cuts = sorted(data, key=int)
    order = orderings(data)

    for c in cuts:
        print(f"n<{c:>3}: " + " ".join(f"{x:>4}" for x in order[c]))

    base = order[cuts[0]]
    print()
    print("inversions against the smallest cutoff:")
    inv = {}
    for c in cuts[1:]:
        v = inversions(base, order[c])
        inv[c] = v
        print(f"  n<{c:>3}: {v if v else 'none'}")

    print()
    print("pairwise Spearman on the defect values:")
    rho = {}
    for a, b in itertools.combinations(cuts, 2):
        va, vb = dict(data[a]), dict(data[b])
        ks = sorted(va)
        r = float(spearmanr([va[k] for k in ks], [vb[k] for k in ks]).statistic)
        rho[f"{a}:{b}"] = r
        print(f"  n<{a:>3} vs n<{b:>3}:  rho = {r:.4f}")

    fixed = fixed_positions(order)
    print()
    print(f"positions identical at every cutoff: {len(fixed)} of {len(base)}  {fixed}")
    churn = sorted({x for c in cuts[1:] for pair in inv[c] for x in pair})
    print(f"discriminants that ever move: {churn}")
    print(f"identical to n<{cuts[0]} anywhere: "
          f"{[c for c in cuts[1:] if order[c] == base] or 'nowhere'}")

    out = {
        "orderings": order,
        "inversions_against_smallest_cutoff": {c: inv[c] for c in cuts[1:]},
        "spearman": rho,
        "positions_fixed_at_every_cutoff": fixed,
        "discriminants_that_move": churn,
        "cutoffs_matching_smallest": [c for c in cuts[1:] if order[c] == base],
        "note": ("RESULTS.md claimed the orderings at n<61 and n<401 are "
                 "identical. They are not: -23 and -24 transpose. The tail is "
                 "rigid and the ordering settles by n<201."),
    }
    (ART / "ordering.json").write_text(json.dumps(out, indent=1) + "\n")
    print(f"-> {ART / 'ordering.json'}")


if __name__ == "__main__":
    main()
