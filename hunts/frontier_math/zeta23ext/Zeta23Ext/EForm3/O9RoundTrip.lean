import Zeta23Ext.BandCert.Leaves

/-!
# O9 round-trip control

These `#eval`s exist to be compared, integer for integer, against
`hunts/frontier_math/o9_leaves_kernel.py`.

`O9-2D-STATUS.md` §0 records what happens without such a control: the leaf
model in `o9_leaf.py` computed its transcendentals with Arb and a 4-ulp pad
rather than the way `Leaves.lean` computes them, nobody ever compared the two,
and the resulting table was refuted by `decide +kernel` on 7 of 9 chunks. A
generator that only checks itself can only confirm itself.

This file is a control, not mathematics. It asserts nothing and proves nothing;
it prints the kernel's own integers so a test outside Lean can insist they
match.
-/

open BandDual

-- small-argument series, |v| ≤ 1
#eval sinCosSmall (EIv.ofQ 1 4)
#eval sinCosSmall (EIv.ofQ 1 2)
#eval sinCosSmall (EIv.ofQ 1 1)
#eval sinCosSmall (EIv.ofQ (-3) 4)
#eval sinhCoshSmall (EIv.ofQ 1 4)
#eval sinhCoshSmall (EIv.ofQ 1 2)
#eval sinhCoshSmall (EIv.ofQ 1 1)
#eval sinhCoshSmall (EIv.ofQ (-3) 4)

-- the reduction path, for the arguments the O9 box actually reaches
#eval sinCosIv (EIv.ofQ 28 10)
#eval sinCosIv (EIv.ofQ 97 8)
#eval sinCosIv (EIv.ofQ 30 1)
#eval sinCosIv (EIv.ofQ 60 1)

-- the pinned constants
#eval SQ2
#eval PI2iv
