# Hunt R-233ABE: the omega bridge, and the pointwise Hardy–Ramanujan

## The question

`lean/ZetaLean/HardyRamanujantheorem.lean` landed the Hardy–Ramanujan theorem
in its density form, with zero `sorry`s, on top of
`ZetaLean.Mertens.mertens_second_theorem`. It carries its own `omega n :=
n.primeFactors.card` so that no `ArithmeticFunction` coercion sits between the
combinatorics and the sums. The discovering run (`43d363c1`) left two threads
in that file, and this hunt is both of them:

**(a) The bridge.** State `omega n = ArithmeticFunction.cardDistinctFactors n`
and prove it. The point is not the one-line equality: it is that a consumer
built on Mathlib's own vocabulary can cite the landed theorem without
unfolding anything this namespace defines. The discovering run priced it at
"rfl or simp".

**(b) The pointwise form.** The theorem as landed normalises every `n ∈ (0, N]`
by the same `log log N`. The form usually quoted normalises each `n` by its own
`log log n`. Route as recorded by the discovering run: split `(0, N]` at
`N^delta`, compare `log log n` with `log log N` on the upper range, count the
lower range trivially. The run states all ingredients are in the file.

## Scope

Writes allowed, per the operator addendum:
`lean/ZetaLean/HardyRamanujantheorem.lean` and its import line in
`lean/ZetaLean.lean`, this directory, and the Hunt #45 case-log entry in
`hunts/README.md`. Nothing else. Two other runs are live in
`hunts/frontier_math/*.py` and `hunts/frontier_math/zeta23ext/`; this hunt
stays out of both.

The bar: zero `sorry`s, axioms unchanged, no statement weakened. If (b) will
not close in budget, land (a) plus an exact account of where (b) stopped.

Nothing here is evidence for or against RH (`docs/08`).

```huntspec
id: r_233abe
question: Can omega be bridged to ArithmeticFunction.cardDistinctFactors, and can the density-form Hardy-Ramanujan theorem be upgraded to the pointwise log log n form, both kernel-checked with zero sorrys against pinned Mathlib v4.33.0-rc2?
frontier: ZetaLean.HardyRamanujan.hardy_ramanujan is landed with zero sorrys in the density form, variance constant 275, standing on ZetaLean.Mertens.mertens_second_theorem with band 16; no bridge to Mathlib's own omega exists, and the pointwise form is not stated
proposed_attack: prove the bridge by rfl and restate the theorem in Mathlib's vocabulary; then transfer to the pointwise form by splitting (0, N] at the square root of N, bounding the low range by Nat.sqrt N and the loglog gap on the high range by log 2
dead_routes:
  - weakening either the variance constant 275 or the Mertens band 16 to make a step go through
  - rebuilding mertens_second_theorem, which is landed and out of scope
required_oracles:
  - the Lean 4 kernel via lake build, exit status plus a zero sorry count
  - grep over the edited file for sorry as an independent count
  - "#print axioms" on every new public statement, read for anything beyond propext, Classical.choice, Quot.sound
kill_conditions:
  - the toolchain will not install or Mathlib will not fetch
  - the budget is exceeded
  - a target would need a weakened statement, in which case it is reported as not landed rather than restated
agents_may:
  - search the pinned Mathlib source
  - edit the one permitted Lean file and its import line
  - build with lake and read the kernel's answer
  - report an obstruction as the result when the build does not close
agents_may_not:
  - add a sorry and present the file as a result
  - weaken an existing statement or constant
  - restate a definition and present it as the theorem
  - declare novelty
  - promote their own claim
```
