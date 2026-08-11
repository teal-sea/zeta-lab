# Marked two-gap consistency: the coexistence question, answered

## The immediate question, first

> Can one actual off-line pair simultaneously realise the worst signed
> incidence allowed by level 1 across two consecutive on-line gaps?

**No — and for a sharper reason than incompatible offsets: the level-1
envelope is not attained in even one cell.**

On the full grid the signed cell value of an on-line zero at offset `g` from
a pair of depth `y` is `W(g,y) = 2 Re(Phi2(g+iy)^2)/(aL)^2`. Writing
`Phi2(g+iy) = C - iS` and using the parity of `phi^2`, the two mixed-parity
integrands vanish and

```text
C(g,y) = int phi^2(u) cos(gu) cosh(yu) du      (even in g, even in y)
S(g,y) = int phi^2(u) sin(gu) sinh(yu) du      (odd  in g, odd  in y)
W(g,y) = 2 (C^2 - S^2) / (aL)^2                (even in g, even in y)
```

Level 1's floor came from `|S| <= aL sigma(y)` by Cauchy–Schwarz on
`int (phi sin gu)(phi sinh yu)`. Saturating `W = -2 sigma^2` needs `C = 0`
**and** Cauchy–Schwarz equality, i.e. `sin(gu) = lambda sinh(yu)` for all `u`
in the support. Matching Taylor coefficients at `u = 0`: first order forces
`lambda = g/y`, third order forces `-g^3/6 = lambda y^3/6 = g y^2/6`, hence

```text
g (g^2 + y^2) = 0.
```

With `y > 0` that gives `g = 0` — and at `g = 0` we have `S = 0`, so
`W(0,y) = 2C^2/(aL)^2 >= 0`, which misses the negative floor outright
(measured `W(0, 0.3) = +2.8046` against a floor of `-0.8623`). So **no cell
ever sits at the level-1 floor**, and the two-cell question is moot before it
is asked. The measured proportionality defect stays bounded away from zero at
every offset, including in the `g -> 0` limit, where it tends to the defect
between `u` and `sinh(yu)` rather than to zero.

## Phase 1: the exact identities

All four hold exactly, from the decomposition above:

1. **Translation covariance.** `W` depends on the difference `g = x - t`
   alone, never on absolute position.
2. **`rho <-> 1 - conj(rho)` symmetry.** `W` is even in `y` (C is even, S is
   odd, and only their squares appear).
3. **Shared kernel column.** Both adjacent gaps read the *same* function
   `W(., y)` at arguments differing by exactly the gap — this is what
   "projective consistency" amounts to, and it is an identity, not a
   constraint to be imposed.
4. **Cell parity.** `W` is even in `g`, so a cell depends only on `|offset|`.
   This single fact is what makes the coexistence question collapse (below).

## LAW I — the one-cell tightening (proved, uniform)

Sharpening the same Cauchy–Schwarz against `sin^2` rather than `1`:

```text
S^2 <= (int phi^2 sin^2(gu) du)(int phi^2 sinh^2(yu) du)
     = [(aL - Phi2(2g))/2] * aL sigma^2(y),
```

so with the single window constant `m0 := - min_r omega(r) >= 0`, where
`omega(r) = Phi2(r)/Phi2(0)`:

```text
W(g,y)  >=  -sigma^2(y) (1 - omega(2g))  >=  -(1 + m0) sigma^2(y).
```

Level 1 had `-2 sigma^2(y)`. For this window `m0 = 0.2137172540` (attained at
`r = 1.31762587`), so **every cell carries a uniform factor
`2/(1+m0) = 1.6478` of slack against the level-1 envelope**, at every offset
and every depth. Measured against the proved cap `(1+m0)/2 = 0.6069`:

| y | min_g W | proved floor | r(y) = \|min W\|/(2σ²) | g* |
|---|---|---|---|---|
| 0.01 | −0.00023144 | −0.00047140 | 0.297942 | 0.922373 |
| 0.10 | −0.02560843 | −0.04824639 | 0.322111 | 0.892714 |
| 0.30 | −0.36951190 | −0.52328645 | 0.428525 | 0.767463 |
| 0.49 | −1.55156340 | −1.97083720 | 0.477756 | 0.687281 |

`r(y)` rises monotonically from `0.2979` toward `0.4786` at the strip edge —
always inside the proved cap, and always far from level 1's implicit `1`.
The pointwise form `-sigma^2 (1 - omega(2g))` is retained separately because
it is sharper than the constant cap wherever `omega(2g) > -m0`.

## LAW J — the periodic word (exact, and it answers a Phase-4 lesion)

If the on-line zeros sit at the critical grid `tau_k = t + k h`, `h = 2pi/L`,
Poisson summation applies to `F(r) = Phi2(r+iy)^2`, whose density
`(phi^2 e^{-y.}) * (phi^2 e^{-y.})` is supported in `[-L, L]` **and vanishes
at both endpoints**, so only the `m = 0` dual term survives:

```text
sum_{k in Z} W(t + k h, y)  =  2 b / a^2,
```

with `a = (1/L) int phi^2` and `b = (1/L) int phi^4` — the paper's own (2.14)
constants. The value is **positive and independent of both the depth and the
ordinate**: measured `2.2959062623` against every tested `(y, offset)` to
better than `6e-8`. A periodic near-obstruction word at critical spacing —
the lesion the hierarchy names — yields an off-line pair *exactly no
negativity*, at any depth. Breaking the spacing by 65/64 moves the total to
`2.2605846`, a defect of `3.5e-2`, so the identity is genuinely a property of
critical spacing.

## Phases 2–3: coexistence by itself is empty — OUTCOME B

The directive's `Delta` is identically zero on a nonempty set, by two exact
constructions:

**The mirror pair.** `W` is even in `g`, so its minimum is attained at *both*
`+g*` and `-g*`. Two on-line zeros separated by exactly `s = 2 g*(y)`
therefore both sit at the single-cell minimum, and the two-cell penalty is
exactly zero:

| y | g* | mirror gap | Δ |
|---|---|---|---|
| 0.10 | 0.89271437 | 1.78542875 | +3.2e-14 |
| 0.30 | 0.76746328 | 1.53492657 | −3.4e-13 |
| 0.49 | 0.68728064 | 1.37456129 | −2.5e-13 |

**The cluster.** On-line offsets need only be *distinct*, so `n` zeros packed
at spacing `delta` near `g*` drive the penalty per cell to zero: measured
`5.4e-2` at `delta = 0.1`, `5.6e-6` at `delta = 1e-3` (n = 3), and
`7.0e-5` at `delta = 1e-3` (n = 10).

So **marked two-gap projective consistency, on its own, yields no positive
penalty**. `Delta` is positive for generic gaps (e.g. `+0.507` at `s = 0.4`,
`+0.360` at `s = 3.0`, depth 0.3) but has exact zeros, so no uniform bound
follows. Per the directive this is a clean result, not a failure — and it is
the reason no LP was built: a projective-consistency program whose value is
known to be zero on an explicit family would be an expensive way to
rediscover these two constructions.

## OUTCOME C — the escaping family, pinned exactly

The family that survives every level-1 law *and* all two-gap consistency is

```text
on-line zeros clustered at offsets  +-g*(y) + O(delta),   delta -> 0,
```

i.e. a **near-multiple zero sitting at the kernel's optimal offset**. It is
excluded by neither gap geometry nor the signed envelopes; it is controlled
only by *density and multiplicity* — the paper charges a multiple on-line
point to the index side at the flat cost 4, and `gap_consistency.py`'s LAW H
caps the cluster's size by `nu <= A_0 log T`. Imposing a separation `delta`
does restore a positive penalty (`separation_penalty`: `>0.1` per cell at
`delta = 0.5`, `<1e-4` at `delta = 1e-3`), which is the honest statement of
what the coupling is worth: **consistency plus density has force;
consistency alone does not.**

This family is the natural level-3 kill control.

## Phase 5 — epsilon robustness

LAW I gives it directly, uniformly, and without any coexistence input: no
cell is ever within `(1 - m0) sigma^2(y)` of the level-1 floor. Hence a
configuration declaring `n` cells within `epsilon` of that floor is excluded
outright for `epsilon < (1 - m0) sigma^2(y)`, and otherwise pays at least

```text
n [ (1 - m0) sigma^2(y) - epsilon ]     -- linear in n, uniform in placement.
```

Measured bands: `0.031255` at `y = 0.1` (floor `-0.079502`), `0.339001` at
`y = 0.3` (floor `-0.862287`), `1.276768` at `y = 0.49` (floor `-3.247605`).

## Phase 6 gate — NOT passed, deliberately

No new proportion is computed and no decimal search is opened. LAW I tightens
the *envelope*, not a proportion; converting an envelope into a proportion
needs the additive floor that level 3's telescoping potential would supply,
and the coexistence route that could have produced one is the route that
collapsed. Both gate conditions fail, so the gate holds.

## Controls ledger

| control | instrument | measured |
|---|---|---|
| cell value vs the level-1 mpmath kernel | `test_cell_value_matches_the_mpmath_kernel` | agreement `< 1e-9` |
| parity identities (Phase 1.1, 1.2) | `test_cell_is_even_in_offset_and_in_depth` | `< 1e-12` both |
| no negativity at zero depth | `test_no_negativity_without_depth` | holds at every probe |
| LAW I pointwise, dense grid | `test_law_i_holds_pointwise_over_a_dense_grid` | 60 offsets x 4 depths, no violation |
| LAW J at every depth and offset | `test_periodic_word_gives_...` | defect `< 1e-6` against `2b/a^2` |
| lesion: independent cells (the named cheat) | `lesion_independent_cells` | the cheat buys `0.3827` at depth 0.3 |
| lesion: independent depths | `lesion_independent_depths` | **negative result, recorded**: mixing never beats using the deeper depth twice, so shared *depth* is not the binding half of pairing — shared *ordinate* is |
| lesion: conjugate-transpose geometry | `lesion_hermitian_geometry` | worst true `-0.3610`, worst Hermitian `+4.9e-11` — all sign structure destroyed, as `CLEAN-KILL-REPORT.md` requires |
| lesion: broken Gabor spacing | `lesion_broken_spacing` | identity defect `3.5e-2` |
| lesion: periodic near-obstruction word | `periodic_total` | total `+2.2959`, no negativity available |
| escaping family (cluster) | `cluster_collapse` | penalty per cell `-> 0` monotonically |

## Reproduction

```bash
.venv/bin/python hunts/frontier_math/two_gap_marked.py
.venv/bin/python -m pytest -q -o addopts='' \
    hunts/frontier_math/test_two_gap_marked.py
```

About 25 s and 28 s. Optimisations are deterministic (grid scan, then golden
section); no random search enters any reported number.

## What level 3 needs, restated after this

The coexistence route is closed as a source of penalties *by itself*, so
level 3 should not re-derive it. The two live objects this session leaves:

1. **The telescoping potential**, now with a sharper input: LAW I's
   pointwise form `-sigma^2(1 - omega(2g))` is a function of the gap, which
   is exactly the shape a telescoping argument consumes.
2. **The `+-g*` cluster as kill control.** Any level-3 mechanism must
   either exclude it or explain why the density/multiplicity charge already
   does — and must be run against it before anything else.
