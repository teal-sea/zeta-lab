# R-938AB4 — what `reNum_mem` and `imNumOverY_mem` actually enclose

Run `bbe76b9a-ccf3-4d53-bfe9-6480334f4648`, 2026-08-17. Hunt #44.

**Status: settled.** Both identifications are proved in Lean, zero sorrys,
standard axioms only, and both are instantiated at a recorded box of
`Retention.o9boxes`. The two sides answer differently, and the difference is
the result.

Nothing here is evidence for or against RH (`docs/08`).

## The question, restated exactly

`Retention.reNum_mem` and `Retention.imNumOverY_mem`
(`hunts/frontier_math/zeta23ext/Zeta23Ext/EForm3/O9Num.lean`) conclude that
two of the seven `boxParts` fields enclose long trigonometric expressions.
Those expressions are read off `boxParts` operation for operation, and they
leave the three constant leaves as free variables `ss`, `cc`, `sc` — any
reals the constant enclosures happen to contain. They are not stated as
`Re num` and `Im num / y` for

    num z = 2 · (z · sin(z/2) · cos(√2/2) − √2 · cos(z/2) · sin(√2/2)),

the numerator of `BandDual.Phi2_closed`. Whether the shapes and the named
quantities agree was unproved in either direction.

## What was found

New file: `hunts/frontier_math/zeta23ext/Zeta23Ext/EForm3/O9NumShape.lean`
(409 lines, 27 declarations, imported by `EForm3/Main.lean`).

### 1. `reNum` encloses `Re num`, unconditionally

`Retention.reNum_mem_numC` says

    EIv.mem (boxParts sLo sHi yLo yHi).reNum ((numC (s + i y)).re)

under exactly the hypotheses `reNum_mem` already carried: the two box
memberships and the small-range bound `|y/2| ≤ 1`. There is no `y ≠ 0`. The
identification needs the three constants instantiated at their true values,
which `BandDual.SQ2_mem`, `SINC_mem` and `COSC_mem` supply; the arithmetic
identity is `Retention.numC_re_eq`, obtained from `Complex.sin_add_mul_I` and
`Complex.cos_add_mul_I` and closed by `ring`.

So on the real side there is no gap at all between the computed shape and the
mathematics: the shape *is* `Re num`, at every point of every box including
`y = 0`.

### 2. `imNumOverY` encloses `Im num / y` only for `y ≠ 0`

The field's value is named `Retention.imOverYShape s y` — the shape,
`if`-branch and all, with the constants instantiated.
`Retention.imNumOverY_mem_shape` proves the enclosure unconditionally, and
`Retention.imOverYShape_eq_im_div` proves

    imOverYShape s y = (numC (s + i y)).im / y      for y ≠ 0.

The single step that consumes the hypothesis is `shcSmall`'s `if`: away from
zero the removable branch is `sinh(y/2)/(y/2)`, and halving it is
`sinh(y/2)/y`, which is what dividing `Im num` by `y` produces.

**The hypothesis is not an artefact of the proof — the statement is false
without it, and the witness is in the file.** `Retention.numC_im_zero` shows
`Im num = 0` on the real axis, so `Im num / y` at `y = 0` is `0` by Lean's
division convention. What `imNumOverY` encloses there is instead the removable
limit, and `Retention.imOverYShape_pi_zero_pos` shows that limit is
`2·cos(√2/2) + √2·sin(√2/2) > 0` at `s = π`.
`Retention.imOverYShape_ne_im_div_at_zero` is the resulting disequality,
stated as a disequality rather than hedged into a hypothesis.

This asymmetry is the design working, not a defect. The removable branch
exists so that `y = 0` is an ordinary point for the 2-D route, and it can only
be an ordinary point by enclosing something other than a quotient by `y`
there. What the file adds is that the "something other" is now named and
pinned rather than left as whatever the arithmetic happened to produce.

The witness point `s = π` is outside the table's own `s`-range `[28/5, 60]`.
That is deliberate and it costs nothing: `π` is where the trig values are
exact, so the disequality is provable without bounding `cos(2.8)`. The
mismatch inside the table is the same algebra with the same `if` branch — the
enclosed real is a limit and `Im num / 0` is `0` — but exhibiting it at a
table point would need numeric bounds on the leaves that this run did not
build. **Recorded as a loose thread, not claimed.**

### 3. Both compositions, read back against `Phi2`

Having both numerator components identified, the two compositions can be
stated against the field itself rather than against abstract components:

* `Retention.qreIv_mem_phi2` — `qreIv` encloses `Re Phi2 (s + i y)`;
* `Retention.rIv_mem_phi2` — `rIv` encloses `−Im Phi2 (s + i y) / y`, which is
  the removable branch `R` the O9 table is built on.

Both carry `y ≠ 0`, which they inherit from item 2 and from
`BandDual.sq_ne_two_of_im_ne_zero`. `Retention.denAbs2_pos` supplies the
positivity `O9Real.re_div_eq` and `im_div_over_y` require.

This is a strictly stronger statement than anything the seam previously
reached, and it is **not** a claim that O9 soundness is closed. The two-mode
arithmetic (`dam_le_of_mode1`, `dam_le_of_mode2` against the recorded table)
and the link from `Phi2` to `EForm3.Qre` / `Qim` are separate and untouched.

### 4. What follows for the dead-weight lemmas

`O9Seam.r_comp_mem` and `Retention.rIv_mem` are true, zero-sorry, and vacuous
at every box in the table (run 4df2ee65: they ask `denAbs2` to enclose
`c*c + dOverY*dOverY` where it encloses `c*c + d*d`, `d = dOverY·y`).

**They can be retired, and retiring them costs no reproof.** Nothing in the
route built here passes through either: `rIv_mem_phi2` goes through
`O9Seam.r_comp_mem'` and `Retention.rIv_mem_box`, and `qreIv_mem_phi2` goes
through `O9Seam.qre_comp_mem` and `Retention.qreIv_mem_box`. Grep confirms
`r_comp_mem` has exactly one use site (`rIv_mem`) and `rIv_mem` has none.

They were left in place. Showing a declaration unnecessary and deleting it are
two different decisions and only the first was this run's; the second is a
one-line edit whenever the operator wants it.

### 5. Instantiability, checked

A statement that compiles is not thereby a statement with content — that is
exactly what `r_comp_mem` demonstrated. So every identification above is also
instantiated at a **recorded** box:

* `Retention.box0_in_table` — the box
  `⟨103301766812773489049, 107547284961337742355, 0, 4611686018427387904, 0, 2⟩`
  is the first row of `Retention.o9boxes`, proved by membership rather than
  asserted (this declaration depends on no axioms at all);
* the point `(23/4, 1/8)` is interior to it, with `s_in_box0`, `y_in_box0`,
  `y_small_box0` discharged by `norm_num` against `Iv.mem` and `SO`;
* `reNum_mem_numC_box0`, `imNumOverY_mem_numC_box0`, `rIv_mem_phi2_box0`,
  `qreIv_mem_phi2_box0` are the four statements with every hypothesis
  discharged.

The `y = 0` face of the box is exactly where item 2's hypothesis bites, which
is why the box was chosen: it is a `mode = 2` box whose `y`-range starts at
`0`.

## Build status

    cd hunts/frontier_math/zeta23ext
    PATH="$HOME/.elan/bin:$PATH" lake exe cache get
    PATH="$HOME/.elan/bin:$PATH" lake build Zeta23Ext.EForm3.O9NumShape
    # → Build completed successfully (8708 jobs), exit 0
    PATH="$HOME/.elan/bin:$PATH" lake build Zeta23Ext.EForm3.Main
    # → Build completed successfully (8726 jobs), exit 0
    #   (the target that now imports the new file, and that re-decides the
    #    699-cell O9 table on the way)

Every `#print axioms` in the new file reports
`[propext, Classical.choice, Quot.sound]`, except `box0_in_table`, which
reports "does not depend on any axioms". Zero `sorry`s were added; the string
appears in the file only inside prose describing the retired lemmas.

**Two pre-existing build failures, neither in scope and neither introduced
here.** A package-wide `lake build` in this container was already red before
any edit:

* `Zeta23Ext/RetentionWired.lean:44` — ``ring_nf` made no progress` followed
  by a type mismatch. A genuine elaboration error, outside `EForm3/`.
* `Zeta23Ext.BandCert.Verify` — Lean exited with code 137 after 704 s, i.e.
  killed. A container resource limit, not a proof failure.

Both were observed on the baseline build performed before the new file
existed, and both are recorded here rather than absorbed into a claim of a
green tree. `Zeta23Ext.EForm3.Main`, which is where the new file is imported,
did build in that same baseline run, and the new module builds green on its
own full import closure.

## Repository checks

    python3 -m pytest -q -n0 tests/test_hunt_probe_discipline.py \
        tests/test_huntspec.py tests/test_docs_numbering.py
    # → 27 passed
    python3 scripts/make_context.py --check
    # → CONTEXT.md is up to date.

`tests/test_doors.py` is 9 passed, 2 failed, and both failures are the same
container gap: the learn and refute door commands shell out to
`scripts/23_gate_3_battery.py`, which imports `zeta`, and this container has
no `.venv` and no editable install. Neither failure touches anything this run
wrote. `pytest`, `numpy`, `mpmath` and `scipy` had to be installed with the
system `python3` before any of the above could run at all.

## Toolchain note

The container had **no Lean toolchain at all** at session start: `lake` was
not on the `PATH` and `~/.elan` did not exist, so the addendum's "run
`lake exe cache get` FIRST" silently no-op'd with `lake: command not found`.
`elan` was installed from `elan.lean-lang.org` and the pinned toolchain
(`leanprover/lean4:v4.33.0-rc2`) and Mathlib cache fetched from there. Total
cold-start cost was on the order of ten minutes of the run's budget. A future
run against this package should check `which lake` before trusting a cache
command's exit status.

## Loose threads

1. **A `y = 0` mismatch witness inside the table's own `s`-range.** The
   disequality is proved at `s = π`, which is outside `[28/5, 60]`. Making the
   same statement at a table point needs numeric enclosures for `cos(s/2)` and
   `sin(s/2)` on `[2.8, 2.92]` — available from the package's own leaves, but
   it was not built here. First step: instantiate `sinCosIv` at box 0's
   `s`-interval and read off the sign of `imOverYShape s 0` by `decide`.
2. **`r_comp_mem` and `rIv_mem` are still present.** Shown unnecessary, not
   deleted. First step: delete both plus their `#print axioms` lines and
   rebuild; nothing should break.
3. **`Phi2` to `Qre`/`Qim`.** `qreIv_mem_phi2` and `rIv_mem_phi2` stop at
   `Phi2`. `O9Sound`'s mode lemmas are stated about `Retention.Qre` and
   `Qim` from `EForm3/Defs.lean`, which are integrals. The identity joining
   them is in `ClosedForm.lean` and was not traced. Until it is, the O9 chain
   has a named gap rather than an unnamed one.
4. **`Zeta23Ext/RetentionWired.lean:44` does not elaborate.** Pre-existing,
   unrelated to O9, and someone should look at it. First step: open the file
   at line 44 and see what `ring_nf` was expected to do.
