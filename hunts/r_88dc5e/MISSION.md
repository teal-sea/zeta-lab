# Hunt r_88dc5e: the two-mode arithmetic, and retiring the dead-weight seam lemmas

**Run:** 40c2efbc-2ed1-4de3-a762-fc57524791f6 · **Case log:** Hunt #47

## The question

`O9Assemble.lean` named the last step: once the seven `boxParts` fields and the
two compositions are joined, "the only thing between the kernel-checked table
and O9 is the arithmetic of the two modes." Two things were asked of this run.

1. **Retire the dead weight.** `O9Seam.r_comp_mem` and `Retention.rIv_mem` were
   shown by runs 4df2ee65 and bbe76b9a to be true, zero-sorry and vacuous at
   every box in the table. Remove them, having re-verified the use-site claim
   rather than taking it on faith.
2. **Land the two-mode arithmetic.** Turn `O9Check2.o9Box`'s `Bool` verdict into
   the real hypotheses `O9Sound.dam_le_of_mode1` and `dam_le_of_mode2` want, so
   a box the kernel accepted actually bounds `Dam` on that box.

## Scope

`hunts/frontier_math/zeta23ext/Zeta23Ext/EForm3/*` plus this directory and one
case-log entry. Not `hunts/frontier_math/*.py` (two other runs live there), not
`meta/`, `harness/`, or any root markdown file.

## What was done

Two new modules, both zero-sorry, standard axioms only:

* `EForm3/O9Bridge.lean`: `Re Phi2 (s + iy) = Qre y s` and
  `Im Phi2 (s + iy) = -Qim y s` for `y ≠ 0`, and the two enclosures read back
  against `Qre` and `Qim` rather than against `BandDual.Phi2`.
* `EForm3/O9Modes.lean`: the two-mode arithmetic itself, plus
  `dam_le_box0`, the bound instantiated at the first recorded row from the
  kernel's own chunk verdict.

Both retirements landed. See `RESULTS.md`.

```huntspec
id: r_88dc5e
question: Does the O9 checker's Bool verdict imply the real damage bound on the box it decided, and can the two dead-weight seam lemmas be retired without reproof?
frontier: before this run the chain reached BandDual.Phi2 (O9NumShape) and stopped; O9Sound's two mode lemmas were proved but nothing connected them to o9Box; two lemmas were known vacuous and still present
proposed_attack: bridge BandDual.Phi2 to the retention integrals Qre and Qim through the closed forms on both sides, then read Iv.mem's fixed-point comparisons back as real inequalities
dead_routes:
  - O9Seam.r_comp_mem, true and zero-sorry but asking denAbs2 for a real it does not enclose at any box in the table
  - Retention.rIv_mem, which inherited that hypothesis verbatim
  - borrowing the soundness seam from BandDual.phiC_mem, whose CIv.div real part is a different and wider composition than qreIv
required_oracles:
  - Lean 4 kernel with Mathlib, zero sorrys
  - print axioms restricted to propext, Classical.choice, Quot.sound
  - instantiation at a recorded box of o9boxes with every hypothesis discharged
kill_conditions:
  - a new lemma compiles but cannot be instantiated at any box in the table
  - retiring either lemma forces a reproof anywhere
  - a statement has to be weakened to make it close
agents_may:
  - search
  - derive
  - code
  - attack
  - formalize
agents_may_not:
  - declare novelty
  - declare theorem status beyond what the kernel checked
  - promote their own claim
  - claim O9 soundness closed end to end
```
