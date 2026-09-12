# Hunt R-938AB4: what `reNum_mem` and `imNumOverY_mem` actually enclose

Run `bbe76b9a-ccf3-4d53-bfe9-6480334f4648`, opened 2026-08-17.

## The question

`Retention.reNum_mem` and `Retention.imNumOverY_mem`
(`hunts/frontier_math/zeta23ext/Zeta23Ext/EForm3/O9Num.lean`) each conclude
that a `boxParts` field encloses a long trigonometric expression. Those
expressions are the shapes the interval arithmetic **computes**. They are not
written as `Re num` and `Im num / y`, where

    num z = 2 · ( z · sin(z/2) · cos(√2/2) − √2 · cos(z/2) · sin(√2/2) )

is the numerator of `BandDual.Phi2_closed`. Whether the two agree, and under
what hypotheses, was unsettled. It matters because it decides whether the
seam lemmas that run 4df2ee65 found to be dead weight
(`O9Seam.r_comp_mem`, `Retention.rIv_mem`) can be retired or must be reproved.

## Scope

Writes confined to `hunts/frontier_math/zeta23ext/Zeta23Ext/EForm3/`, this
directory, and the case-log entry in `hunts/README.md`. Nothing in `meta/`,
`harness/`, `zeta/`, `lean/`, or any root markdown file. Two other runs are
live in `hunts/frontier_math/*.py` and `lean/ZetaLean/` and were not touched.

The bar is the repository's: the Lean arm counts nothing with a `sorry`, and
axioms must stay `propext` / `Classical.choice` / `Quot.sound`. A statement
that compiles is not thereby a statement with content, the cautionary
example is the run-4df2ee65 finding that `r_comp_mem` was true, zero-sorry
and vacuous at every box in the table. Instantiability at a real box from
`o9boxes` is therefore part of the deliverable, not a nicety.

Nothing here is evidence for or against RH (`docs/08`).

```huntspec
id: r_938ab4
question: Do the reals enclosed by reNum_mem and imNumOverY_mem equal Re num and Im num / y, and under what hypotheses?
frontier: six of seven boxParts fields have _mem lemmas whose targets are computed shapes, not named mathematical quantities; the identification is unproved in either direction
proposed_attack: define the closed-form numerator as a complex function, compute its real and imaginary parts at z = s + iy through Mathlib's sin/cos decomposition, and match term for term against the two enclosed shapes with the constant leaves instantiated at their true values
dead_routes:
  - borrowing the seam from BandDual.phiC_mem, which carries y != 0 and cannot reach the boxes touching y = 0
  - O9Seam.r_comp_mem, true and zero-sorry but asking denAbs2 for a real it does not enclose at any box in the table
required_oracles:
  - Lean 4 kernel with Mathlib, zero sorrys, axioms limited to propext / Classical.choice / Quot.sound
  - instantiation at a recorded box of Retention.o9boxes with concrete rational witnesses
kill_conditions:
  - the identification needs a hypothesis the box family cannot supply
  - a lemma would have to be stated in weakened form to compile
  - the toolchain or Mathlib cache cannot be obtained inside budget
agents_may:
  - search
  - derive
  - code
  - attack
  - formalize
agents_may_not:
  - declare novelty
  - declare theorem status
  - promote their own claim
```
