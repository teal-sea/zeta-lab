# Results — hunt r_88dc5e (run 40c2efbc)

**Both halves landed, zero sorrys, standard axioms only.** The two dead-weight
seam lemmas are retired at no reproof cost, and the two-mode arithmetic is
proved and instantiated at a recorded box from the kernel's own verdict. What
this does *not* do is close O9 soundness end to end; §5 says exactly what is
left and why it is not in this run.

Environment note: this was a fresh clone with neither `.venv` nor `elan`. The
Lean toolchain was installed and `lake exe cache get` run first, as the brief
directed. Wall clock overran the 80-minute budget (see §7).

## 1. The dead weight is retired, and the grep was re-run

The brief said not to take run bbe76b9a's use-site survey on faith. It was
re-run, over `*.lean`, `*.py`, `*.md` and `*.sh` in the whole repository,
excluding the primed names `r_comp_mem'` and `rIv_mem_box`:

* `O9Seam.r_comp_mem` — **one** use site in code: `Retention.rIv_mem`
  (`O9Assemble.lean:55`). Everything else is prose or `#print axioms`.
* `Retention.rIv_mem` — **no** use site in code at all. Prose and
  `#print axioms` only.

Both are now removed:

* `O9Real.lean` — `O9Seam.r_comp_mem` deleted; its docstring content moved onto
  `r_comp_mem'`, which is the live statement, and now records what the retired
  version got wrong and why the correction weakens nothing.
* `O9Assemble.lean` — `Retention.rIv_mem` deleted, replaced by a note saying
  what it was and that it had no use site.
* `O9Audit.lean` — the two `#print axioms` lines removed.
* `O9NumShape.lean` — the prose that said the two were "left in place" now says
  they were retired, with the date.

`Zeta23Ext.EForm3.O9Audit` and `Zeta23Ext.EForm3.Main` both build green after
the removal. **Nothing was reproved**, which is the claim the previous run
made and this run checked.

## 2. The gap nobody had named: `Phi2` is not `Qre`

The chain as it stood ended at `BandDual.Phi2`. `O9NumShape.qreIv_mem_phi2`
says `qreIv` encloses `Re Phi2 (s + iy)`; `rIv_mem_phi2` says `rIv` encloses
`-Im Phi2 (s + iy) / y`. But `O9Sound` states the damage obligation in terms of
`Retention.Qre` and `Retention.Qim`, which are *integrals against the window
`g`* (`EForm3/Defs.lean`), and `BandDual.Phi2` is *`s(z+√2) + s(z−√2)` with
`s(u) = sin(u/2)/u`* (`BandCert/Phi.lean`). Those are two different definitions.
A search over the package found no lemma connecting them: `EForm2/Bridge.lean`
relates `EForm2`'s own integral `Phi2` to `EForm2`'s `Pre`/`Qim`, which is a
different pair of definitions in a different module that the O9 chain does not
import.

So the "arithmetic of the two modes" had a prerequisite that was not on
anyone's list. It is now `EForm3/O9Bridge.lean`:

* `phi2_re_eq_Qre (s y) (hy : y ≠ 0) : (Phi2 (s + iy)).re = Qre y s`
* `phi2_im_eq_neg_Qim (s y) (hy : y ≠ 0) : (Phi2 (s + iy)).im = -Qim y s`

The route is closed forms on both sides and no new analysis: `Qre_closed` and
`Qim_closed` (`ClosedForm.lean`) already give the two-term shape from explicit
antiderivatives, and splitting `sin(u/2)/u` into components is
`O9Real.re_div_eq` / `im_div_eq`, already proved. The sign on the imaginary
side is the one `O9Comp.rIv` carries and the one the 1-D route once got wrong.

Two derived statements follow, and they are what the mode lemmas consume:

* `qreIv_mem_Qre` : `qreIv` encloses `Qre y s`
* `rIv_mem_R` : `rIv` encloses the removable branch `R = Qim y s / y`

## 3. The two-mode arithmetic

`EForm3/O9Modes.lean`. Three lemmas and one instantiation.

**`dam_le_mode1_of_iv`** — given `rIv … = some r` and the recorded test
`(Iv.sub (Iv.sqr r) ⟨cap,cap⟩).hi ≤ 0`, plus the box memberships, concludes
`Dam y s ≤ (cap/2⁶⁴) · y²`. The content is one division by `2⁶⁴ > 0`:
`Iv.mem` is `lo ≤ 2⁶⁴·x ≤ hi`, so the recorded `hi ≤ 0` says exactly
`R² − c ≤ 0`, which is `dam_le_of_mode1`'s hypothesis.

**`dam_le_mode2_of_iv`** — same, for
`(y_hi² · sup(R² − c)).hi ≤ (inf Qre²).lo`. `dam_le_of_mode2` is stated with
`Rsq` and `yhi` abstract; here they are `e.hi/2⁶⁴ + c` and `yHi/2⁶⁴`, and
`y ≤ yhi` is the box membership itself. Nothing else is needed.

**`dam_le_of_box`** — `o9Box b = true` and `0 ≤ b.cap` imply the bound at every
point of the box. The `y = 0` case is discharged inside by `dam_zero_le`, so
the lemma carries no `y ≠ 0` hypothesis, which is the whole point of the
removable branch.

**`o9Box_of_mem` / `dam_le_of_mem_walk`** — a decided walk decides each of its
boxes, so a box in a chunk `O9Check2` accepted carries the real bound.

### Instantiability, checked at a real box

The brief's rule, and the reason it exists. `dam_le_box0` is

    Dam (1/8) (23/4) ≤ (0 : ℤ)/2⁶⁴ · (1/8)²

for the first recorded row `⟨103301766812773489049, 107547284961337742355, 0,
4611686018427387904, 0, 2⟩` (a `mode = 2` box with cap `0`), at the interior
point `(s, y) = (23/4, 1/8)`. Its verdict comes from `o9_box_chunk0` — the
kernel's own `decide +kernel` over the first forty rows — via
`box0_in_chunk0`, not from a fresh decision of that one box. Every remaining
hypothesis is discharged by `norm_num` through `s_in_box0`, `y_in_box0`,
`y_small_box0`. So the statement is not vacuous: it is about a point of a box
in the table.

## 4. Declarations relied on, and two that were looked for and not found

Relied on, all pre-existing and unchanged:

| declaration | file | what it gave |
| --- | --- | --- |
| `qreIv_mem_phi2`, `rIv_mem_phi2` | `O9NumShape.lean` | the enclosures against `Phi2` |
| `Qre_closed`, `Qim_closed` | `ClosedForm.lean` | the closed forms the bridge matches |
| `O9Real.re_div_eq`, `im_div_eq` | `O9Real.lean` | componentwise complex quotient |
| `dam_zero_le`, `dam_le_of_mode1`, `dam_le_of_mode2` | `O9Sound.lean` | the real-side soundness |
| `Iv.sqr_mem`, `sub_mem`, `mul_mem`, `ofQ_mem`, `EIv.pt_mem` | `BandCert/Iv.lean` | the interval layer |
| `o9_box_chunk0` | `O9Check2.lean` | the kernel's verdict on rows 0–39 |

Looked for and **not found**, hence written here:

* any lemma relating `BandDual.Phi2` to `Retention.Qre`/`Retention.Qim`
  (§2). `EForm2/Bridge.lean` is the near miss and is about different objects.
* any lemma turning `o9Box`'s `Bool` into a real inequality. There was none;
  `O9Check2`'s own docstring says so ("it does **not** yet say anything about
  `Dam`, because the `_mem` seam lemmas are not written").

## 5. What is still between this and the retention obligation

Stated precisely, because the brief asked and because it is the honest part.
`dam_le_of_mem_walk` bounds `Dam` **at points of boxes the table records**.
The retention obligation needs the bound **on the whole window**. Two things
are missing and neither is in this run:

1. **A covering argument.** Nothing in Lean says the recorded boxes cover
   `[28/5, 60] × [0, 1/2]`. The generator (`hunts/frontier_math/o9_leaf2d.py`)
   produced a cover; the Lean side carries the boxes but not the fact that
   their union contains the window. Until that exists, the per-box bound does
   not compose into a per-window bound. This is a finite check over the
   recorded list (adjacency of the scaled endpoints) and looks decidable, but
   it is a real piece of work, not a rewrite.
2. **The assembly into `Gap`/`FarField`.** The consumers want the damage bound
   in the aggregated form those files state, not box by box.

There is also a **hypothesis** on `dam_le_of_box` worth naming rather than
burying: `0 ≤ b.cap`. Every row of `o9boxes` this run inspected has `cap = 0`,
so it is discharged by `norm_num` at instantiation, but the general lemma
carries it because `dam_le_of_mode1` needs `0 ≤ c` and nothing in `O9Box`
constrains the field.

**O9 soundness is not closed.** What is closed is the step the brief named.

## 6. Build and axioms

```
lake build Zeta23Ext.EForm3.O9Bridge   → exit 0
lake build Zeta23Ext.EForm3.O9Modes    → exit 0
lake build Zeta23Ext.EForm3.O9Audit    → exit 0
lake build Zeta23Ext.EForm3.Main       → exit 0
```

Every new declaration reports
`[propext, Classical.choice, Quot.sound]` (`o9Box_of_mem` and `box0_in_chunk0`
report `[propext]` alone). Zero `sorry`s: the only occurrence of the word in
either new file is in prose saying there are none.

`lake build` over the **whole** package fails, and it failed before this run
touched anything: `Zeta23Ext/TruncEst/Kernel.lean` and
`Zeta23Ext/EForm2/Bridge.lean` do not compile against the current Mathlib
(`sin_gt_sub_cube` arity, `HasDerivAt` instance mismatch, two `simp made no
progress`). Neither file was modified here and neither is in the O9 chain. It
is recorded as a thread rather than fixed, because it is outside this hunt's
scope and because a Mathlib-drift repair in `TruncEst` is its own piece of work.

## 7. Budget

The 80-minute budget was exceeded; the run finished at roughly 95 minutes. The
overrun is attributable to a fresh clone with no toolchain (elan install plus
`lake exe cache get` for a ~8 GB Mathlib cache before any mathematics), and to
one dead end: `simp only [o9Box]` and `rw [o9Box]` both fail with a `whnf`
heartbeat timeout, because unfolding the checker asks the elaborator to reduce
`rIv b.sLo …` symbolically through the whole leaf layer. `unfold o9Box at hb`
followed by `split at hb` and one definitional `have` does the same job in
milliseconds. That is recorded as a Core candidate below, since it will bite
anyone who touches a `decide`-backed checker in this package.

## Loose threads

1. **The covering argument (§5.1).** Without it the per-box bound is not a
   per-window bound. First step: state
   `∀ s y, s ∈ [28/5, 60] → y ∈ [0, 1/2] → ∃ b ∈ o9boxes, s ∈ box ∧ y ∈ box`
   and see whether it is `decide`-able over the scaled endpoints in chunks the
   way the table itself is.
2. **`TruncEst/Kernel.lean` and `EForm2/Bridge.lean` do not compile** against
   the current Mathlib (§6). Pre-existing, unrelated to O9, and it means a bare
   `lake build` on this package is red for reasons that have nothing to do with
   whatever a session is working on. Worth fixing so the package's own build is
   a signal again.
3. **`0 ≤ b.cap` is a free hypothesis on `dam_le_of_box`** (§5). If every row
   of the table has `cap ≥ 0` — they appear to — a one-line `decide` over
   `o9boxes` would discharge it once and for all and remove the hypothesis from
   every downstream statement.
4. **`O9PhiCmp.lean` is `#eval`s only.** It answered "should O9 use `phiC`'s
   real part or its own composition?" and the answer is recorded in prose. Now
   that `qreIv_mem_Qre` exists, the comparison could be made a pinned test
   rather than an experiment nobody re-runs.
