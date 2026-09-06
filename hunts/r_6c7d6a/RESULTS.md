# R-6C7D6A: results

Run `4df2ee65-1c9a-4e3b-8f7d-2a6b9c4e0f11`, 2026-08-17. Target: the
numerator-side `boxParts` fields of the O9 two-dimensional checker, in
`hunts/frontier_math/zeta23ext/Zeta23Ext/EForm3/`.

**Outcome: settled, and the brief's premise was stale in a way that mattered.**
Every one of the seven `boxParts` fields now carries a zero-sorry enclosure
lemma, and both composition lemmas are instantiated at a box with every
hypothesis discharged. Getting there turned up a defect in the seam layer, and
that is the part of this run worth a second reader.

## 1. What was already there, and what the brief got wrong

The brief warned that `START-HERE.md` was stale about O9 soundness. It is, but
so is the brief, and in the same direction. The brief was written from
`O9Parts.lean`'s header sentence:

> "The numerator side needs the trig and hyperbolic leaves and is the remaining
> step; it is not in this file and no `sorry` stands in for it."

That sentence was true when written and was superseded seven minutes later, by
commit `6f81078` (2026-08-13 17:51:32 -0500), *"O9: the numerator half, and
every `boxParts` field is now sound"*. `O9Num.lean` was already on `main` with
`leaves_mem`, `reNum_mem` and `imNumOverY_mem`, all zero-sorry. A run that took
the brief at its word would have rewritten work that already existed.

Commit `6f81078`'s own message is the second thing that is wrong, and it is the
one that mattered. `Retention.Parts` has **seven** fields:

| field | lemma before this run | after |
| --- | --- | --- |
| `reNum` | `O9Num.reNum_mem` | unchanged |
| `imNumOverY` | `O9Num.imNumOverY_mem` | unchanged |
| `imNum` | **none** | `O9Num.imNum_mem` (new) |
| `reDen` | `O9Parts.reDen_mem` | unchanged |
| `imDen` | `O9Parts.imDen_mem` | unchanged |
| `imDenOverY` | `O9Parts.imDenOverY_mem` | unchanged |
| `denAbs2` | `O9Parts.denAbs2_mem` | unchanged |

Six of seven. Not "every field". The missing one, `imNum`, is a hypothesis of
`O9Assemble.qreIv_mem` (`hB`), so the `Qre` composition could not be
instantiated at a box at all. That is the field the brief was actually asking
for, and it is the field this run supplies.

## 2. `imNum_mem`: the missing field

`boxParts.imNum` is `EIv.mul imNumOverY Y` by construction, so its enclosure is
a product and needs no new leaf and no new truncation bound:

```lean
theorem imNum_mem {v : ℝ} (hy : EIv.mem (some ⟨yLo, yHi⟩) y)
    (hv : EIv.mem (boxParts sLo sHi yLo yHi).imNumOverY v) :
    EIv.mem (boxParts sLo sHi yLo yHi).imNum (v * y) := by
  unfold boxParts at hv ⊢
  exact EIv.mul_mem hv hy
```

The component `v` is left abstract rather than written out. That follows the
idiom the addendum names and that `O9Seam` and `O9Assemble` both chose: the
layer does not couple to the leaves, so moving them forces no reproof here.
`imNumOverY_mem` is what fixes which real `v` is.

The abstraction also keeps the `y = 0` story straight. `imNumOverY` carries
`sinh(y/2)/y` through `shcSmall`, whose branch value at `y = 0` is the limit
`1/2` rather than a quotient; multiplying by `y` afterwards gives `0`, which is
`Im num` there. Nothing on either side divides by `y`.

## 3. The defect: `O9Seam.r_comp_mem` cannot be instantiated at a box

This is the finding, and it is not what the run was sent for.

`O9Seam.r_comp_mem` (`O9Real.lean`) writes `c*c + dOverY*dOverY` into **both**
its `E` hypothesis and its conclusion:

```lean
    (hE : E.mem (c * c + dOverY * dOverY)) :
    (EIv.neg (EIv.div (EIv.sub (EIv.mul B C) (EIv.mul A D)) E)).mem
      (-((bOverY * c - a * dOverY) / (c * c + dOverY * dOverY)))
```

Self-consistent, so it is provable, and it is. But `rIv` divides by `denAbs2`,
and `denAbs2` is `sqr reDen + sqr imDen`, which encloses `c*c + d*d` with
`d = dOverY * y` (`O9Comp.boxParts`). `O9Real.im_div_over_y`: the identity that
says the composition *is* `Im(num/den)/y`, puts `c ^ 2 + (dOverY * y) ^ 2`
under the quotient as well. So the real `r_comp_mem` asks `denAbs2` to enclose
is not the real `denAbs2` encloses.

Concretely, at `s = 1`, `y = 0`: `c = s² − y² − 2 = −1`, `dOverY = 2s = 2`,
`d = 2sy = 0`. The hypothesis wants `denAbs2` to contain `c*c + dOverY*dOverY
= 5`; `denAbs2` contains `c*c + d*d = 1`. The two agree only when `y² = 1` or
`s = 0`, and the O9 box family is `[28/5, 60] × [0, 1/2]`, so `y² = 1` never
happens and `s = 0` never happens.

`O9Assemble.rIv_mem` inherits the hypothesis verbatim, so it inherits the
problem. Both lemmas are true, both are zero-sorry, and both go through
vacuously at every box in the table. `O9Assemble.lean`'s own "What remains"
note half-saw this, it said the two denominators "are different reals, the
second is the first divided by `y²`", but that diagnosis is also wrong:
`c² + dOverY²` is not `(c² + d²)/y²`, and reading it as a mode-2 bookkeeping
detail is what let it sit.

This is the shape `O9-2D-STATUS.md` §6 already records once for this file: a
quantity that enters only squared has no self-check, so it needs an external
one. `R` was caught there by an independent evaluation. This one was caught by
trying to discharge the hypothesis instead of restating it.

**The fix, which weakens nothing.** Leave the denominator's real as a variable:

```lean
theorem r_comp_mem' {A B C D E : EIv} {a bOverY c dOverY e : ℝ}
    (hA : A.mem a) (hB : B.mem bOverY) (hC : C.mem c) (hD : D.mem dOverY)
    (hE : E.mem e) :
    (EIv.neg (EIv.div (EIv.sub (EIv.mul B C) (EIv.mul A D)) E)).mem
      (-((bOverY * c - a * dOverY) / e))
```

The original is the case `e = c*c + dOverY*dOverY`; the box needs
`e = c*c + d*d`, which `O9Seam.denAbs2_mem` discharges. Same proof term, one
fewer coincidence. `qre_comp_mem'` is the matching statement for the `Qre`
side, added for symmetry rather than as a fix, `qre_comp_mem`'s own `E`
hypothesis was already the right real.

The existing `r_comp_mem` and `rIv_mem` are left in place and unedited. They
are not wrong, they are unusable, and deleting them is a judgment for whoever
owns this package, not for a hunt.

## 4. Both compositions, instantiated at a box

With all seven fields supplied, `O9Assemble` can state the two compositions
against the box's own reals with every field hypothesis discharged. Only the
two numerator components stay abstract, because those are what the trig and
hyperbolic leaves fix:

* `qreIv_mem_box`: via `qreIv_mem`, discharging `imNum` by `imNum_mem`,
  `reDen`/`imDen` by `O9Parts`, and `denAbs2` by `O9Parts.denAbs2_mem`.
* `rIv_mem_box`: via `r_comp_mem'`, not `r_comp_mem`, for the reason in §3.

The denominator is written out in both (`c = s² − y² − 2`, `d = 2sy`,
`dOverY = 2s`) because it is small and because it is exactly what the
discharged hypothesis is about.

## 5. What compiles

Everything. Toolchain `leanprover/lean4:v4.33.0-rc2`, elan installed cold in
this container, Mathlib cache fetched with `lake exe cache get` (8681 files
decompressed), dependency `Zeta23` at `3635e74`.

```
lake build Zeta23Ext.EForm3.O9Audit    exit 0, 8716 jobs
lake build                             exit 1, and not because of this run
```

`lake build Zeta23Ext.EForm3.O9Audit` is the complete dependent closure of
every file this run edited: only `O9Parts` imports `O9Real`, only `O9Num`
imports `O9Parts`, only `O9Assemble` imports `O9Num`, and `O9Audit` imports all
of them.

The **full** package build fails, at `Zeta23Ext/RetentionWired.lean:44`,
`` `ring_nf` made no progress on the goal``, then a type mismatch on
`Finset.sum_congr`. That file is untouched by this run, but it transitively
imports `EForm3.Main` and so imports this run's files, which is why the failure
was checked rather than assumed: with this run's changes stashed
(`git stash push -- hunts/frontier_math/zeta23ext/`), `lake build
Zeta23Ext.RetentionWired` produces the identical two errors. Pre-existing,
consistent with commit `178d534`'s landing note about pre-existing failures at
land time, and out of this run's lane.

Five new declarations, **zero sorrys**, all reported by `#print axioms` as
depending on `[propext, Classical.choice, Quot.sound]` and nothing else:

| declaration | file |
| --- | --- |
| `Retention.imNum_mem` | `O9Num.lean` |
| `O9Seam.r_comp_mem'` | `O9Real.lean` |
| `O9Seam.qre_comp_mem'` | `O9Real.lean` |
| `Retention.qreIv_mem_box` | `O9Assemble.lean` |
| `Retention.rIv_mem_box` | `O9Assemble.lean` |

`O9Audit.lean` gains all five, plus `Retention.denAbs2_mem`, which existed
since 2026-08-13 and had never been in the audit list. An audit aggregator that
omits a lemma is the defect `O9Audit.lean`'s own header was written to prevent,
so it is fixed here rather than noted.

One duplicate was written during this run and then removed before landing: a
`denAbs2_box_mem` restating `O9Parts.denAbs2_mem` verbatim. It compiled, and it
would have padded the count with nothing. The brief's line about not
manufacturing a compiling triviality applies to one's own drafts too.

## 6. What this does *not* establish

The chain from the kernel-checked table to O9 is **not** closed, and this run
does not claim it is. What is closed is the field-and-composition layer:
`O9Assemble.lean`'s sentence that "the only thing between the kernel-checked
table and O9 is the arithmetic of the two modes" is now true, where before it
was one field and one unusable seam short of true.

What is left, precisely:

1. **Mode 2.** Both `O9Sound.dam_le_of_mode1` and `dam_le_of_mode2` are proved,
   as real-number implications, but nothing connects either to the enclosures.
   (`O9Assemble.lean`'s old note said "mode 2 is not" proved. That was a third
   stale sentence: `dam_le_of_mode2` has compiled since 2026-08-13. This run
   rewrote the note.) Reading `qreIv`/`rIv` back against `Qre` and `Qim` goes through
   `BandDual.phiC_mem`, whose `y ≠ 0` hypothesis `dam_zero_le` routes around
   for the boxes that touch the axis.
2. **The leaf-shape identity.** `reNum_mem` and `imNumOverY_mem` enclose the
   expressions the interval arithmetic computes, not `Re num` and `Im num / y`
   as such. `O9Real.re_div_eq` and `im_div_over_y` are the identities that
   relate the two shapes; nothing yet applies them at a box.
3. **The `sinCosSmall`/`SQ2` constants.** `reNum_mem` and `imNumOverY_mem` take
   `ss`, `cc`, `sc` as hypotheses. Something has to supply them.

None of that is numerator-field work, and none of it is blocked by anything
this run found.

## 7. Environment notes

No `.venv` and no `pytest` in this container, so none of the repository's
Python tests were run, including `tests/test_zeta23ext_imports.py`, which is
the guard against exactly the orphaned-module defect `O9Audit.lean` exists to
prevent. The import graph is unchanged by this run (five declarations added to
three existing modules, no new module, no new import edge), so the guard has
nothing new to catch, but that is an argument and not a test result.

## Loose threads

1. **`r_comp_mem` and `rIv_mem` are dead weight now.** They are true,
   zero-sorry, and unusable at any box in the table. Left in place. Whoever
   owns the package should decide whether to delete them or keep them as the
   record of the mismatch; `harness/graveyard.py` exists for the second option.
   The `#print axioms` lines for both are still in `O9Audit.lean`, so an audit
   reader currently sees two green lemmas that do no work.
2. **`O9Parts.lean`'s header is now false** and `O9Assemble.lean`'s "What
   remains" note was rewritten by this run. `START-HERE.md` and
   `O9-2D-STATUS.md` were not touched and are presumably stale in the same
   direction. This is the second time in five days that a stale in-file header
   set a run's premise; the headers are load-bearing documentation with no test
   behind them.
3. **`O9Parts.reDen_mem` and `imDenOverY_mem` take an unused `hy`/`hs`.** The
   build emits a linter warning for `imDenOverY_mem`'s `hy`. Harmless, but it
   means the lemma is stated over a box coordinate it does not constrain.
4. **The `y = 0` claim in `imNum_mem`'s docstring is prose, not a lemma.** That
   `v * y` is `Im num` at `y = 0` follows from `imNumOverY_mem`'s branch value
   and is stated in the docstring; nothing checks it. It becomes checkable the
   moment thread (2) of §6 is done.
