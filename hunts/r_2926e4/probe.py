"""Rebuild `o9_leaf.py`'s 1-D O9 table on kernel leaves, and price the caveat.

## The question

`hunts/frontier_math/o9_leaf.py` states a **LEAF CAVEAT**: its transcendental
leaves come from Arb at 300 bits rounded outward with a 4-ulp pad, whereas
`BandCert/Leaves.lean` builds them from truncated Taylor series with `hornerI`,
`EIv.widen`, an argument reduction against a `2^-64` enclosure of `2π`, and two
`dbl` steps.  The caveat says the two "agree to well under `2^-60`" and that a
cell passing with margin is therefore safely predicted.  Issue #23 says that is
false for wide cells, because the two objects differ in *kind*, not precision:
Arb encloses `sin` by its range, `sinCosIv` propagates a widening series.

The 344-cell count in `o9_leaf.py` rests on the caveat.  This probe asks what
the count actually is once the leaves are computed the way the kernel computes
them, and how far off 344 was.

## What it does

Four measurements, all in the fixed-point arithmetic at scale `2^64` that
`decide +kernel` runs (`o9_leaf.Iv` / `civ_mul` / `phiC`, imported unchanged):

1. **baseline**: `o9_leaf.build()` verbatim, to reproduce 344.
2. **leaf widths**: Arb leaves vs `o9_leaves_kernel` leaves, per leaf, over a
   sample of the cells the baseline table actually contains.  This is the
   caveat's own claim ("well under `2^-60`") put to a number.
3. **rebuild**: the same adaptive walk, the same seed cuts, the same caps and
   targets, with `o9_leaf.leaves` replaced by
   `o9_leaves_kernel.kernel_leaves`.  Everything downstream is byte-identical
   code.  Reports cells, undecided, max depth, min margin.
4. **cell-level agreement**: for each baseline cell, does the kernel-leaf
   verdict agree?  This turns "the table is refutable" into a count of exactly
   which cells the model got wrong.

`o9_leaves_kernel` is not this hunt's work: it exists in `hunts/frontier_math`
and is pinned against Lean's own `#eval` output integer for integer by
`tests/test_o9_leaves_kernel.py`.  This probe consumes it and writes nothing
there.

Nothing here is kernel-checked (no Lean toolchain is invoked) and nothing here
is evidence about RH.
"""

from __future__ import annotations

import json
import sys
import time
from fractions import Fraction as F
from pathlib import Path

_ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(_ROOT / "hunts" / "frontier_math"))

import o9_leaf as L                                    # noqa: E402
from o9_leaves_kernel import kernel_leaves              # noqa: E402

Y = F(1, 2)
LEAF_KEYS = ("sinX2", "cosX2", "sinh", "cosh", "SQ2", "SINC", "COSC")


# ---------------------------------------------------------------------------
# the walk, with the leaf layer swapped
# ---------------------------------------------------------------------------

def damage_iv_kernel(lo: F, hi: F, y: F = Y):
    """`o9_leaf.damage_iv`, on `Leaves.lean`'s leaves instead of Arb's."""
    p = L.phiC(kernel_leaves(lo, hi, y))
    if p is None:
        return None
    return L.civ_mul(p, p)[0].neg()


def cell_verdict_kernel(lo: F, hi: F, y: F = Y):
    """`o9_leaf.cell_verdict`, verbatim but for the leaf source."""
    d = damage_iv_kernel(lo, hi, y)
    if d is None:
        return False, 0, None
    cap = L._cap_for(lo, hi)
    if cap is None:
        if L._straddles(lo, hi):
            return False, 0, None
        target = 0
    else:
        target = -((-(cap * y * y * L.SO)).__floor__())
    return d.hi <= target, target - d.hi, target


def build_kernel(y: F = Y, max_depth: int = 40, cell_budget: int = 400_000):
    """`o9_leaf.build`, verbatim but for the verdict source, plus a budget.

    The budget exists because the kernel's leaves are wider and the complement
    test (`D <= 0` outside every window) is not guaranteed to close at all: a
    walk that cannot decide simply doubles at every depth.  Hitting the budget
    is itself a result and is reported rather than raised.
    """
    cells, undecided, seen = [], 0, 0
    stack = [(a, b, 0) for a, b in L._seed_segments()]
    while stack:
        if seen >= cell_budget:
            return {"cells": cells, "undecided": undecided, "budget_hit": True,
                    "max_depth": max((c["depth"] for c in cells), default=0),
                    "stack_left": len(stack)}
        lo, hi, d = stack.pop()
        seen += 1
        ok, margin, target = cell_verdict_kernel(lo, hi, y)
        if ok:
            cells.append({"lo": lo, "hi": hi, "target": target,
                          "margin_ulp": margin, "depth": d})
            continue
        if d >= max_depth:
            cells.append({"lo": lo, "hi": hi, "target": target,
                          "margin_ulp": -1, "depth": d})
            undecided += 1
            continue
        mid = (lo + hi) / 2
        stack.append((lo, mid, d + 1))
        stack.append((mid, hi, d + 1))
    cells.sort(key=lambda c: c["lo"])
    return {"cells": cells, "undecided": undecided, "budget_hit": False,
            "max_depth": max(c["depth"] for c in cells),
            "stack_left": 0}


def summarise(t: dict) -> dict:
    ms = [c["margin_ulp"] for c in t["cells"]]
    return {"cells": len(t["cells"]), "undecided": t["undecided"],
            "budget_hit": t.get("budget_hit", False),
            "max_depth": t["max_depth"],
            "min_margin_ulp": min(ms) if ms else None,
            "min_margin_abs": (min(ms) / L.SO) if ms else None,
            "all_decided": t["undecided"] == 0 and not t.get("budget_hit")}


# ---------------------------------------------------------------------------
# measurements
# ---------------------------------------------------------------------------

def leaf_width_gap(cells, sample: int = 24) -> dict:
    """Per-leaf Arb width vs kernel width, over cells of the baseline table.

    The caveat's claim is about *agreement*, so the honest statistic is the
    ratio of widths on cells the table really contains, not on one hand-picked
    interval.  `step` samples across the whole `[28/5, 60]` range rather than
    the first few, which are the widest.
    """
    step = max(1, len(cells) // sample)
    picked = cells[::step][:sample]
    per_leaf = {k: [] for k in LEAF_KEYS}
    widest = None
    for c in picked:
        a = L.leaves(c["lo"], c["hi"], Y)
        k = kernel_leaves(c["lo"], c["hi"], Y)
        for key in LEAF_KEYS:
            wa, wk = a[key].width(), k[key].width()
            r = (wk / wa) if wa > 0 else float("inf")
            per_leaf[key].append(r)
            if key in ("sinX2", "cosX2") and (widest is None or r > widest[2]):
                widest = (float(c["lo"]), key, r)
    return {
        "sampled_cells": len(picked),
        "ratio_kernel_over_arb": {
            k: {"min": min(v), "max": max(v), "mean": sum(v) / len(v)}
            for k, v in per_leaf.items()
        },
        "widest_trig_ratio": {"cell_lo": widest[0], "leaf": widest[1],
                              "ratio": widest[2]} if widest else None,
        "note": ("the caveat says the two agree to well under 2^-60; a ratio "
                 "above 1 on a leaf whose width is ~1e-1 means the difference "
                 "is a fraction of the leaf, not 2^-60"),
    }


def baseline_cells_under_kernel_leaves(cells) -> dict:
    """How many of the 344 baseline cells still pass on the kernel's leaves."""
    fail, worst = [], None
    for c in cells:
        ok, margin, _ = cell_verdict_kernel(c["lo"], c["hi"], Y)
        if not ok:
            fail.append({"lo": float(c["lo"]), "hi": float(c["hi"]),
                         "arb_margin_ulp": c["margin_ulp"],
                         "kernel_margin_ulp": margin})
        if worst is None or margin < worst[1]:
            worst = (float(c["lo"]), margin)
    # The caveat's own safety criterion is "passes with margin". The number
    # that tests it is the LARGEST Arb margin among the cells that fail: if a
    # cell with an enormous recorded margin still fails, the recorded margin is
    # not a bound on the leaf-model error, and no threshold on it would help.
    biggest = max((f["arb_margin_ulp"] for f in fail), default=None)
    return {"checked": len(cells), "failed": len(fail),
            "pass_rate": (len(cells) - len(fail)) / len(cells),
            "worst_kernel_margin_ulp": worst[1] if worst else None,
            "largest_arb_margin_among_failures_ulp": biggest,
            "module_min_margin_ulp": min(c["margin_ulp"] for c in cells),
            "first_failures": fail[:8]}


#: `decide +kernel`'s verdict on the 344-cell table, chunk by chunk, as
#: recorded in `hunts/frontier_math/O9-2D-STATUS.md` §0 for the 2026-08-13
#: build. This is the only figure in this probe that comes from a real Lean
#: run rather than from a model of one, which is why it is the control.
LEAN_CHUNK_VERDICT_2026_08_13 = {0: False, 40: False, 80: False, 120: False,
                                 160: False, 200: True, 240: False,
                                 280: True, 320: False}


def chunk_agreement(cells, chunk: int = 40) -> dict:
    """Do the kernel-leaf failures land in the chunks Lean actually rejected?

    `emit_lean` writes the cells sorted by `lo` and slices them into chunks of
    40, one `decide +kernel` each. A chunk is `true` only if every cell in it
    passes, so "this chunk contains at least one failure" is the model's
    prediction of `false`. Comparing that against the recorded build is a check
    the model cannot pass by being uniformly pessimistic: it has to put the
    failures in the right places and, harder, keep both surviving chunks clean.
    """
    per_chunk: dict[int, int] = {}
    for i, c in enumerate(cells):
        off = (i // chunk) * chunk
        per_chunk.setdefault(off, 0)
        if not cell_verdict_kernel(c["lo"], c["hi"], Y)[0]:
            per_chunk[off] += 1
    rows, agree = [], 0
    for off in sorted(per_chunk):
        predicted = per_chunk[off] == 0        # model says the chunk passes
        recorded = LEAN_CHUNK_VERDICT_2026_08_13.get(off)
        ok = recorded is not None and predicted == recorded
        agree += ok
        rows.append({"offset": off, "failures": per_chunk[off],
                     "model_says_chunk_passes": predicted,
                     "lean_2026_08_13": recorded, "agree": ok})
    return {"chunks": len(rows), "agreeing": agree,
            "all_agree": agree == len(rows), "per_chunk": rows,
            "source": "hunts/frontier_math/O9-2D-STATUS.md §0"}


# ---------------------------------------------------------------------------

def main() -> dict:
    out: dict = {"run_id": "5849dba6-1f35-48cf-98ac-a1a002febf21",
                 "y": "1/2", "scale": "2^64"}

    t0 = time.time()
    base = L.build()
    out["baseline_arb_leaves"] = L.validate(base)
    out["baseline_arb_leaves"]["seconds"] = round(time.time() - t0, 2)
    print(f"baseline (Arb leaves): {out['baseline_arb_leaves']}")

    out["leaf_widths"] = leaf_width_gap(base["cells"])
    print("leaf width ratios (kernel/Arb): "
          + json.dumps({k: round(v["mean"], 3) for k, v in
                        out["leaf_widths"]["ratio_kernel_over_arb"].items()}))

    t0 = time.time()
    out["baseline_cells_rechecked"] = baseline_cells_under_kernel_leaves(
        base["cells"])
    out["baseline_cells_rechecked"]["seconds"] = round(time.time() - t0, 2)
    print(f"baseline cells rechecked: {out['baseline_cells_rechecked']['failed']}"
          f" of {out['baseline_cells_rechecked']['checked']} fail")

    out["chunk_agreement_vs_lean"] = chunk_agreement(base["cells"])
    print(f"chunk agreement vs the 2026-08-13 Lean build: "
          f"{out['chunk_agreement_vs_lean']['agreeing']}"
          f"/{out['chunk_agreement_vs_lean']['chunks']}")

    for md in (20, 30, 40):
        t0 = time.time()
        t = build_kernel(max_depth=md)
        s = summarise(t)
        s["seconds"] = round(time.time() - t0, 2)
        s["max_depth_cap"] = md
        out[f"rebuild_kernel_leaves_depth{md}"] = s
        print(f"rebuild @maxdepth {md}: {s}")
        if s["all_decided"]:
            out["rebuild_settled_at_depth"] = md
            break

    return out


if __name__ == "__main__":
    res = main()
    (Path(__file__).resolve().parent / "results.json").write_text(
        json.dumps(res, indent=2) + "\n")
    print("wrote results.json")
