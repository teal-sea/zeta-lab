"""What the ball-emission certificate actually costs, in atoms rather than terms.

Every rung-3 cost estimate so far has been quoted in *terms*: "~78k certified
terms, ~25 core-hours". That undercounts, because a term and a kernel obligation
are not the same thing, and the gap is not small.

Under ball emission a composite `m` costs one product (its factors are already
in the cache, `cpow` is multiplicative). A **prime** `m` costs a whole tower:
`nExp` products for the Taylor sum of `expSmallB` plus `kE` products for the
squarings, so about 30 at the plan's `nExp = 20, kE = 10`. Counting obligations
instead of terms over all 215 sites of `lean/cert/rung3_plan2.json`:

    kind      sites        atoms    primes   composites
    big         110      197,198     5,684       15,854
    grid        104      341,718     9,646       31,642
    centre        1       10,233       278        1,169
    TOTAL       215      549,149

**549k atoms, 7.1x the 77,675 terms the old figure counted.** At the measured
0.55 s per atom that is ~84 core-hours serial, against the ~25 core-hours that
has been quoted since 2026-08-10. Roughly 3.4x, and the difference is entirely
that primes were priced as if they were composites.

That is affordable but it is not free, and where it runs matters. On GitHub
Actions, which `CLAUDE.md` names as the default compute for this repository,
20 parallel jobs put it near 4 wall-hours; it must not run on a laptop.

**The load-bearing caveat.** 0.55 s/atom was measured on *composite* atoms: one
coarsened product of two 64-bit-coarsened literal balls
(`scripts/66_rung3_ball_atom_cost.py`). Tower atoms have not been measured, and
they are not obviously the same: early Taylor terms carry smaller literals,
which should be cheaper, while `expSumCB`'s accumulator carries the widest ones
in the tower, which may not be. Since primes contribute
`30 x 15,608 = 468,240` of the 549,149 atoms, **85% of this estimate rests on a
rate that has never been measured**, and the staged prime tower is precisely the
shape that produced the rectangle layer's negative result #2. Treat the number
as a planning figure with one pilot outstanding, not as a cost model.

Run: python3 scripts/67_rung3_ball_atom_budget.py [--sec-per-atom S]
"""
from __future__ import annotations

import argparse
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
PLAN = json.loads((ROOT / "lean" / "cert" / "rung3_plan2.json").read_text())

NEXP, KE = 20, 10
TOWER_MULS = NEXP + KE
OLD_TERM_COUNT = 77675
OLD_CORE_HOURS = 25.0


def _sieve(n: int) -> bytearray:
    s = bytearray([1]) * (n + 1)
    s[0:2] = b"\0\0"
    for i in range(2, int(n ** 0.5) + 1):
        if s[i]:
            s[i * i::i] = bytearray(len(s[i * i::i]))
    return s


def site_atoms(K: int, prime: bytearray) -> tuple[int, int, int]:
    """Atoms for one site: a tower per prime, one product per composite.

    The range runs to `5K + 4` because the order-2 correction needs boxes for
    `5K+1 .. 5K+4`, and `m` divisible by 5 is skipped because its coefficient is
    zero, so no box is ever built for it.
    """
    ms = [m for m in range(2, 5 * K + 5) if m % 5]
    primes = sum(1 for m in ms if prime[m])
    composites = len(ms) - primes
    kappa_muls = sum(1 for m in ms if m % 5 in (2, 3))
    return primes * TOWER_MULS + composites + kappa_muls, primes, composites


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--sec-per-atom", type=float, default=0.55)
    args = ap.parse_args()

    sites = ([("big", b) for b in PLAN["big"]["boxes"]]
             + [("grid", g) for g in PLAN["grid"]]
             + [("centre", PLAN["centre"])])
    prime = _sieve(5 * max(s["K"] for _, s in sites) + 5)

    by: dict[str, list[int]] = {}
    total = 0
    for kind, s in sites:
        atoms, pr, co = site_atoms(s["K"], prime)
        total += atoms
        d = by.setdefault(kind, [0, 0, 0, 0])
        d[0] += 1
        d[1] += atoms
        d[2] += pr
        d[3] += co

    print(f"{'kind':8s} {'sites':>6s} {'atoms':>12s} {'primes':>9s} {'composites':>11s}")
    for kind, (n, a, pr, co) in by.items():
        print(f"{kind:8s} {n:6d} {a:12,d} {pr:9,d} {co:11,d}")
    print(f"{'TOTAL':8s} {sum(v[0] for v in by.values()):6d} {total:12,d}")

    tower_share = sum(v[2] for v in by.values()) * TOWER_MULS / total
    hours = total * args.sec_per_atom / 3600
    print()
    print(f"atoms per old 'term': {total / OLD_TERM_COUNT:.1f}x "
          f"({total:,} against {OLD_TERM_COUNT:,})")
    print(f"serial at {args.sec_per_atom}s/atom: {hours:.1f} core-hours "
          f"(old figure {OLD_CORE_HOURS:.0f}, ratio {hours / OLD_CORE_HOURS:.1f}x)")
    for c in (4, 16, 20, 64):
        print(f"  {c:2d}-way: {hours / c:6.1f} wall-hours")
    print()
    print(f"UNMEASURED: {tower_share:.0%} of these atoms are tower atoms, and the "
          f"{args.sec_per_atom}s rate was measured on composite atoms only.")


if __name__ == "__main__":
    main()
