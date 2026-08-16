# ZetaLean

Kernel-checked analytic number theory in Lean 4, from the
[zeta-lab](https://github.com/teal-sea/zeta-lab) research laboratory.
Zero `sorry`s; every public theorem depends only on `propext`,
`Classical.choice`, `Quot.sound`.

## Highlights

| theorem | statement | notes |
|---|---|---|
| `Mertens.mertens_first_theorem` | pipe Σ_{p≤N} (log p)/p − log N pipe ≤ log 4 + 16 | explicit constants, elementary route |
| `Mertens.mertens_second_theorem` | pipe Σ_{p≤N} 1/p − log log N pipe ≤ 76 | every natural N; constant deliberately coarse, tightening route recorded |
| `HardyRamanujan.hardy_ramanujan` | the normal-order density bound, Turán's proof | variance constant 5855, explicit |

Mathlib (v4.33.0-rc2 pin) carries none of these at time of writing
(Wikidata Q1196729, Q5656674 both listed wanted/unbuilt).

## Use

    [[require]]
    name = "ZetaLean"
    scope = "teal-sea"

## Provenance, stated plainly

The mathematics is classical (Mertens 1874; Hardy–Ramanujan 1917, Turán
1934). The formalizations are new, produced by AI workers operated by the
zeta-lab under machine verification: every result here compiled by the
Lean kernel before any human read it, and each module's docstring names
the lab run that produced it. The laboratory publishes its full working
record — including failed routes and retracted candidates — at the lab
repository; the method is documented there. Constants are deliberately
coarse where the elementary argument gives them; sharpening routes are
recorded as loose threads in the corresponding hunt records.

MIT license.
