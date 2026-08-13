# O9: the leaf layer repaired, and what the corrected table costs

**2026-08-13.** Follows `O9-2D-STATUS.md` §0, which recorded that `decide +kernel`
refuted the generated O9 table on 7 of 9 chunks. Nothing here is kernel-checked
yet and nothing here is evidence about RH.

## 1. The generator now computes leaves the way the kernel does

`o9_leaf.py` built its transcendental leaves with Arb at 300 bits, rounded
outward onto the `2^-64` grid with a 4-ulp pad. `BandCert/Leaves.lean` builds
them from truncated Taylor series through `hornerI`, widens by one ulp, and for
arguments outside `[-1,1]` reduces modulo a `2^-64` enclosure of `2π` and
doubles twice.

`o9_leaves_kernel.py` replaces that layer with no Arb anywhere in the path: the
same coefficient lists, the same `hornerI`, the same `widen(·,1)`, the same
`SQ2` and `PI2iv` integers **copied rather than recomputed**, and the same
`sinCosIv` reduction including Lean's truncating integer division for the
reduction index.

## 2. The control that was missing

`tests/test_o9_leaves_kernel.py` emits `#eval` for fourteen leaves through
`Zeta23Ext/EForm3/O9RoundTrip.lean`, runs Lean, and requires the integers to be
**equal, not close**. Fixed-point interval arithmetic has no rounding slack to
hide in, which is what makes the check decisive.

**All fourteen match**, including the reduction path at `s = 30` and `s = 60`
where the old model diverged worst.

The general lesson, which is the reason this file exists: *a generator with no
round-trip against the thing it claims to mirror can only ever confirm itself.*
The leaf caveat was written down honestly before any build existed, and stayed
un-measured for exactly as long as nothing forced the comparison.

## 3. What the correction costs — measured, both models, same generator

| inflation | Arb-model cells | kernel-grade cells | ratio |
|---|---|---|---|
| `1.20x` | 339 | **699** | 2.06 |
| `1.25x` | 325 | **618** | 1.90 |
| `1.30x` | 309 | **568** | 1.84 |

The Arb model reproduces its recorded 339 exactly, so the harness is faithful
and the difference is entirely the leaves. **The old figures were optimistic by
roughly a factor of two in cell count.**

Where the width goes, on one box (`s ∈ [6.1, 6.2]`, `y ∈ [0, 1/4]`):

| leaf | kernel / Arb width |
|---|---|
| `cosX2` | **39.9x** |
| `sinX2` | 1.6x |
| `sinh`, `cosh` | 1.0x |
| `shc` | 0.7x |

So the entire defect lives in the **trig leaves through the argument
reduction**. The hyperbolic leaves were never the problem — `y ≤ 1/2` keeps
`y/2` inside the small-argument range where no reduction happens. `shc` is
*narrower* in the kernel, because the Arb version padded by `2^-160` on top of
its series tail while `hornerI` is tight.

## 4. The route survives

At `1.20x` inflation: **699 cells, 0 undecided, max depth 18**, worst margin
`2.76e11` ulp at scale `2^-64`. Every inflation tried from `1.20x` to `1.39x`
closes with 0 undecided.

`o9_scoping.max_inflation` is `1.3945x` and that is a wall on **inflation**, not
on cell count. The corrected table needs **no extra inflation at all** — `1.20x`
still closes — so §7's budget is untouched and the surplus recorded there
stands. The route is not dead. It is twice as large as advertised.

Kernel reduction cost remains a non-issue: `O9-2D-STATUS.md` §0 measured ~22 s
for a 344-cell target, so 699 cells is minutes, not hours.

## 5. The corrected table kernel-checks

With `rIv`, `qreIv` and `EIv.sqrScaled` written (`EForm3/O9Comp.lean`), the
699-cell table passes **all 18 chunks** of `decide +kernel`. The table that was
refuted on 7 of 9 chunks now decides completely, with no `sorry`, no
`native_decide`, and no `axiom`.

**Before trusting that, the round-trip was extended one level up.** The leaf
control pins the transcendentals; it says nothing about the ~20 further
interval operations `rIv` and `qreIv` stack on top of them, and the defect that
refuted the first table could recur at exactly that level. So
`EForm3/O9CompEval.lean` `#eval`s both compositions on five boxes — including
two that reach `y = 0` and one at `s ≈ 56` — and they agree with
`o9_leaf2d.qre_iv` / `r_iv` **10 of 10, integer for integer**. Only then was
the table believed.

`EForm3/Main.lean` now imports the checker, so a plain build of that chain
re-decides the table. §5 below is what that green build does *not* say.

## 6. What is still missing, precisely

**The table is consistent; it is not yet sound.** `decide +kernel` establishes
that each recorded box passes the test `o9Box` states, in the kernel's own
arithmetic. It does **not** establish that passing that test implies
`Dam y s ≤ c·y²`, because the `_mem` seam lemmas — `rIv_mem`, `qreIv_mem`,
`sqrScaled_mem`, and the truncation lemma for `shcSmall` — are unwritten. Those
are what connect an enclosure to the quantity it encloses.

Two are mechanical, following `phiC_mem`. Two are not:

- **The `y = 0` split.** `phiC_mem` carries the hypothesis `y ≠ 0` and the 2-D
  boxes reach `y = 0` by construction. It should be written first, as a case
  split — at `y = 0`, `Qim = 0` so `Dam = -Qre² ≤ 0` with no arithmetic at all
  — so the side condition never comes under pressure to be weakened.
- **The `shcSmall` truncation lemma.** The genuinely new one:
  `sinh_taylor`'s bound divided by `|v|` blows up exactly where this branch is
  used, so it cannot be borrowed.

**Status: O9 open.** Its table now decides at kernel grade, on leaves and
compositions pinned to the kernel's own arithmetic, and a plain build of the
`EForm3` chain re-decides it. What remains is soundness, and until it lands, a
green build means the table is self-consistent — not that O9 holds.
