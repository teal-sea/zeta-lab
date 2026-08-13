import Zeta23Ext.EForm3.O9Comp

/-!
# O9 composition round-trip control

The leaf round-trip (`O9RoundTrip.lean`) pins the transcendental leaves against
`o9_leaves_kernel.py`. It does **not** pin the compositions built on top of
them, and `rIv`/`qreIv` stack roughly twenty further interval operations. The
defect that refuted the first O9 table — a Python model narrower than the
kernel — can recur at this level, and nothing would catch it.

So these `#eval`s exist to be compared, integer for integer, against
`o9_leaf2d.qre_iv` and `o9_leaf2d.r_iv` on the same boxes. Same discipline as
the leaf control: equal, not close.

Boxes are given in raw grid integers (scale `2^-64`) so the comparison has no
conversion step of its own to get wrong.
-/

open Retention

-- s in [5.6, 5.83], y in [0, 0.25]
#eval qreIv 103275952565021900800 107517428211175260160 0 4611686018427387904
#eval rIv   103275952565021900800 107517428211175260160 0 4611686018427387904

-- s in [6.1, 6.2], y in [0, 0.25]
#eval qreIv 112533895920948609024 114378506817583136768 0 4611686018427387904
#eval rIv   112533895920948609024 114378506817583136768 0 4611686018427387904

-- s in [6.1, 6.2], y in [0.375, 0.5]
#eval qreIv 112533895920948609024 114378506817583136768 6917529027641081856 9223372036854775808
#eval rIv   112533895920948609024 114378506817583136768 6917529027641081856 9223372036854775808

-- s in [30, 30.1], y in [0, 0.125]
#eval qreIv 553402322211286548480 555246933107921076224 0 2305843009213693952
#eval rIv   553402322211286548480 555246933107921076224 0 2305843009213693952

-- s in [56.1, 56.2], y in [0.25, 0.5]
#eval qreIv 1034911735529500114944 1036756346426134642688 4611686018427387904 9223372036854775808
#eval rIv   1034911735529500114944 1036756346426134642688 4611686018427387904 9223372036854775808
