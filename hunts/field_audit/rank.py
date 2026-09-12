#!/usr/bin/env python3
"""Rank the public claims for liminf N0s(T,2T)/N(T,2T), exactly.

Constants as published by each repository, transcribed on 2026-08-24 and
compared as exact decimals.  Sources and labels are in RESULTS.md section 2;
this script only does the ordering and the deficits, so that the ranking in
that table is a computation and not a transcription of a sorted list.

Run:  python3 hunts/field_audit/rank.py
"""

from __future__ import annotations

from decimal import Decimal, getcontext

getcontext().prec = 40

OURS_EIGHT = "0.6730529829896288869"
OURS_SEVEN = "0.6730295534796927114"

CLAIMS = [
    ("AMTOPA/zeta-exact-pressure", "0.6734164909714992949"),
    ("yuhangshi888/zeta-simple-zeros-673316977", "0.6733169771424713135"),
    ("trmdy/zeta-simple-zeros-673137", "0.6733127422722459981"),
    ("AMTOPA/zeta-exact-pressure-673262", "0.6732623755849780503"),
    ("sxuff/zeta-positioned-pressure", "0.6732059784228011963"),
    ("npip99/zeta-zeros", "0.6731951989010000000"),
    ("tawanerguo-cn/zeta-simple-zeros", "0.6731929114731422535"),
    ("hrx114514x/riemann-simple-zero-certificate", "0.6731304969056384320"),
    ("MichaelMobius/simple_zeros_of_the_riemann_zeta_function",
     "0.6730732086087052768"),
    ("teal-sea/zeta-lab  EIGHT-POINT (ours)", OURS_EIGHT),
    ("teal-sea/zeta-lab  seven-point (ours)", OURS_SEVEN),
    ("uwe-schwarz/zeta-simple-zeros-673026", "0.6730266625438475497"),
    ("learademacher/ai-refines-ai-zeta-bound", "0.6730213619501665335"),
    ("ainta/zeta-simple-zeros", "0.6730085279270000000"),
    ("anthropics/zeta-23-lean  Theorem D", "0.6725007036794116457"),
]

FAMILY_CEILING = Decimal("0.675142509660254")        # Hunt #82
CONFIG_CEILING = Decimal("0.6818286874638")


def main() -> int:
    ordered = sorted(CLAIMS, key=lambda row: Decimal(row[1]), reverse=True)
    leader = Decimal(ordered[0][1])
    ours = Decimal(OURS_EIGHT)

    for rank, (name, value) in enumerate(ordered, 1):
        flag = "  <-- OURS" if "ours" in name else ""
        print(f"{rank:2d}. {value}  {name}{flag}")

    our_rank = 1 + next(
        i for i, (n, _) in enumerate(ordered) if n.startswith("teal-sea")
    )
    print()
    print(f"our best claim ranks       : {our_rank} of {len(ordered)}")
    print(f"deficit to the leader      : {leader - ours}")
    print(f"deficit to trmdy           : {Decimal('0.6733127422722459981') - ours}")
    print(f"our margin over ainta      : {ours - Decimal('0.6730085279270000000')}")
    print(f"family ceiling (Hunt #82)  : {FAMILY_CEILING}")
    print(f"leader sits below it by    : {FAMILY_CEILING - leader}")
    print(f"configuration ceiling      : {CONFIG_CEILING}")
    assert leader < FAMILY_CEILING, "a public claim would contradict Hunt #82"
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
