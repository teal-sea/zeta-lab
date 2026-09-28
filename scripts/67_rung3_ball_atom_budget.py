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

**549k atoms, 7.1x the 77,675 terms the old figure counted.** Primes contribute
`30 x 15,608 = 468,240` tower atoms; the remaining 80,909 are composite products
plus kappa multiplies.

Tower atoms were measured on the staged prime-tower pilot (script 68), minus
the import baseline, as CPU seconds (`user + sys`):

    WALL 29.599/30.225/30.344
    USER 39.352/40.123/40.225
    SYS  2.230/2.119/2.216
    import WALL 4.561/4.567/4.567
    import USER 3.075/3.097/3.120
    import SYS  1.498/1.481/1.458

Mean net CPU is 37.512 s / 30 atoms = 1.2504 CPU-s per tower atom. Composite
atoms stay at the previously measured 0.55 s. Mixed serial CPU cost:

    468,240 * 1.2504 + 80,909 * 0.55 = 175.0 core-hours.

That 175.0 core-hours is the measured atom-only serial CPU estimate, before
per-module import and assembly overhead. It is not total production cost.
Core-hours also do not establish wall clock without a measured placement.

Whole-file evidence is recorded separately and is **not** this cost model.
An unsharded B site at K=17 took WALL 305.410, USER 1369.406, SYS 16.260.
A grid site at K=85 took WALL 2580.664, USER 6628.916, SYS 60.079. Unsharded
centre (~138 MB) caused sustained memory pressure on a 32 GB machine and was
aborted. Full-file scaling is nonlinear; do not price the 215-site run from
those whole-file walls.

Run: python3 scripts/67_rung3_ball_atom_budget.py
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

# Staged tower pilot, three runs, then the matching import baseline.
TOWER_PILOT_WALL = (29.599, 30.225, 30.344)
TOWER_PILOT_USER = (39.352, 40.123, 40.225)
TOWER_PILOT_SYS = (2.230, 2.119, 2.216)
IMPORT_WALL = (4.561, 4.567, 4.567)
IMPORT_USER = (3.075, 3.097, 3.120)
IMPORT_SYS = (1.498, 1.481, 1.458)
MEAN_NET_CPU_S = 37.512
TOWER_SEC_PER_ATOM = MEAN_NET_CPU_S / TOWER_MULS  # 1.2504
OTHER_SEC_PER_ATOM = 0.55

WHOLE_FILE_B_K17 = {"label": "B K17", "K": 17,
                    "wall": 305.410, "user": 1369.406, "sys": 16.260}
WHOLE_FILE_GRID_K85 = {"label": "grid K85", "K": 85,
                       "wall": 2580.664, "user": 6628.916, "sys": 60.079}


def net_cpu_samples() -> list[float]:
    return [
        (user + sys) - (iu + isu)
        for user, sys, iu, isu in zip(
            TOWER_PILOT_USER, TOWER_PILOT_SYS, IMPORT_USER, IMPORT_SYS)
    ]


def mean_net_cpu_s() -> float:
    samples = net_cpu_samples()
    return round(sum(samples) / len(samples), 3)


def tower_sec_per_atom() -> float:
    return mean_net_cpu_s() / TOWER_MULS


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


def plan_sites() -> list[tuple[str, dict]]:
    return ([("big", b) for b in PLAN["big"]["boxes"]]
            + [("grid", g) for g in PLAN["grid"]]
            + [("centre", PLAN["centre"])])


def plan_atom_counts() -> dict:
    sites = plan_sites()
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
    tower_atoms = sum(v[2] for v in by.values()) * TOWER_MULS
    other_atoms = total - tower_atoms
    return {
        "by_kind": {
            kind: {"sites": n, "atoms": a, "primes": pr, "composites": co}
            for kind, (n, a, pr, co) in by.items()
        },
        "sites": sum(v[0] for v in by.values()),
        "atoms": total,
        "tower_atoms": tower_atoms,
        "other_atoms": other_atoms,
        "primes": sum(v[2] for v in by.values()),
        "composites": sum(v[3] for v in by.values()),
    }


def serial_core_hours(
    tower_atoms: int,
    other_atoms: int,
    *,
    tower_rate: float = TOWER_SEC_PER_ATOM,
    other_rate: float = OTHER_SEC_PER_ATOM,
) -> float:
    return (tower_atoms * tower_rate + other_atoms * other_rate) / 3600


def main(argv: list[str] | None = None) -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--sec-per-tower-atom", type=float, default=TOWER_SEC_PER_ATOM)
    ap.add_argument("--sec-per-atom", type=float, default=OTHER_SEC_PER_ATOM,
                    help="seconds per non-tower atom (composites + kappa)")
    args = ap.parse_args(argv)

    counts = plan_atom_counts()
    print(f"{'kind':8s} {'sites':>6s} {'atoms':>12s} {'primes':>9s} {'composites':>11s}")
    for kind, row in counts["by_kind"].items():
        print(f"{kind:8s} {row['sites']:6d} {row['atoms']:12,d} "
              f"{row['primes']:9,d} {row['composites']:11,d}")
    print(f"{'TOTAL':8s} {counts['sites']:6d} {counts['atoms']:12,d}")

    hours = serial_core_hours(
        counts["tower_atoms"], counts["other_atoms"],
        tower_rate=args.sec_per_tower_atom, other_rate=args.sec_per_atom)
    print()
    print(f"atoms per old 'term': {counts['atoms'] / OLD_TERM_COUNT:.1f}x "
          f"({counts['atoms']:,} against {OLD_TERM_COUNT:,})")
    print(f"tower atoms: {counts['tower_atoms']:,} at "
          f"{args.sec_per_tower_atom} CPU-s/atom "
          f"(mean net CPU {MEAN_NET_CPU_S}s / {TOWER_MULS})")
    print(f"other atoms: {counts['other_atoms']:,} at "
          f"{args.sec_per_atom} s/atom")
    print(f"serial CPU: {hours:.1f} core-hours "
          f"(atom-only estimate before per-module import and assembly "
          f"overhead; not total production cost; "
          f"old figure {OLD_CORE_HOURS:.0f}, ratio {hours / OLD_CORE_HOURS:.1f}x)")
    print()
    print("WHOLE-FILE evidence (not the sharded cost model; "
          "full-file scaling is nonlinear):")
    for row in (WHOLE_FILE_B_K17, WHOLE_FILE_GRID_K85):
        print(f"  {row['label']} WALL={row['wall']:.3f} "
              f"USER={row['user']:.3f} SYS={row['sys']:.3f}")
    print("  unsharded centre (~138 MB) caused sustained memory pressure "
          "on 32GB and was aborted.")


if __name__ == "__main__":
    main()
