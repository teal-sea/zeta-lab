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

## 5. What is still missing, precisely

The emitted `O9Check2.lean` does not build, and the reason is the one §7 of
`O9-2D-STATUS.md` already named: it calls three Lean definitions that **do not
exist**.

```
error: Unknown identifier `rIv`
error: Unknown identifier `qreIv`
error: Unknown constant `BandDual.EIv.sqrScaled`
```

`rIv` and `qreIv` are the two compositions over the box — the removable branch
`R = Qim/y` and the real part — with their `_mem` seam lemmas; `sqrScaled` is
the scaled square the `mode = 2` test uses. Writing them is the same shape as
`phiC` in `Phi.lean` plus the `y = 0` case split (`phiC_mem` requires `y ≠ 0`,
and at `y = 0` the damage is `-Qre² ≤ 0` with no arithmetic needed).

Until those exist, the checker is not wired into `EForm3/Main.lean`, and
deliberately so: importing a module that does not compile would break the
package build for everyone, and an unimported checker that *does* compile is
the failure this whole exercise is about. Neither is worth doing early.

**Status: O9 open.** The table is regenerated at kernel grade and the generator
is now pinned to the kernel's own arithmetic, which is what makes any future
cell count mean something. No cell has been kernel-checked.
