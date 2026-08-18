# Hunt R-4218D4 — Tighten the variance constant 5855

## The question

`ZetaLean.HardyRamanujan.sum_sq_dev_le` carries Turan's variance bound with
the explicit constant `5855`. That constant is not a fact about the
mathematics; it is `76^2 + 76 + 3`, where `76` is the band of
`ZetaLean.Mertens.mertens_second_theorem`, which is in turn a rounding of a
chain that starts at `mertens_first_theorem`'s `log 4 + 16`. The dependence
is quadratic in the Mertens band, so one local tightening upstream moves
every downstream constant with no new mathematics.

Can the chain be tightened, keeping every statement's shape, with a green
`lake build` and no sorrys?

## Scope

Writes allowed, per the operator addendum to the brief:

- `lean/ZetaLean/Mertensstheorems.lean`
- `lean/ZetaLean/MertensSecond.lean`
- `lean/ZetaLean/HardyRamanujantheorem.lean`
- this directory
- the Hunt #39 case-log entry in `hunts/README.md`

Nothing else. In particular: no `zeta/`, no `ontology/`, no `harness/`, no
root markdown, no other hunt directory.

The addendum overrides the usual prohibition on editing landed proofs, and
only for constant-tightening that preserves every statement's shape. No
statement may be weakened, no hypothesis added, no sorry introduced. Every
theorem name and signature stays; only constants move, and only downward.

## What was actually done

Three edits upstream of the variance constant, then propagation:

1. **The Chebyshev remainder.** Mathlib's `Chebyshev.psi_le` gives
   `psi x <= x log 4 + 2 sqrt(x) log x`; its packaged corollary
   `psi_le_const_mul_self` bounds the remainder by `4x`. The supremum of
   `log t / sqrt t` is `2/e`, so the remainder is at most `(4/e) x`. A new
   local lemma `log_le_div_exp_one` (`log t <= t/e`) supplies it, and
   `psi_le_const_mul_self'` states `psi x <= (log 4 + 3/2) x` for `x >= 1`.
2. **`sum_log_div_sq_le`.** The same `log t <= t/e` majorant replaces
   `log n <= 2 sqrt n`, and the vanishing `n = 1` term is dropped before the
   telescope, so `sum n^{-3/2}` runs from `2` and is bounded by `2` rather
   than `3`. Together `6` becomes `3/2`.
3. **The asymmetry of Mertens I.** Its lower half loses `1` and its upper
   half loses the Chebyshev constant; routing the prime form through the
   symmetric von Mangoldt band paid both. A new one-sided
   `log_sub_one_le_sum_vonMangoldt_div` keeps them apart.

Then `mertens_second_theorem` was re-derived from the new band (also
replacing the crude `1/log 2 < 2` by `< 1.443`), and the variance constant
recomputed as `16^2 + 16 + 3`.

## Result

`log 4 + 16` -> `log 4 + 3`; `76` -> `16`; `5855` -> `275`.

```huntspec
id: r_4218d4
question: Can the Turan variance constant 5855 be lowered by tightening the Mertens band it inherits quadratically, without weakening any statement?
frontier: mertens_first_theorem band log 4 + 16 = 17.3863; mertens_second_theorem band 76; variance constant 5855 = 76^2 + 76 + 3; classical values 2, 4 and (for the variance) a small absolute constant
proposed_attack: replace the crude majorant log n <= 2 sqrt n by the sharp log t <= t/e everywhere it is used, keep the two halves of Mertens I apart since their losses differ, and propagate
dead_routes:
  - chasing the classical Mertens I constant 2 at the cost of a green build, which the brief names as a kill condition
  - weakening log_sub_log_le_mul_add's hypothesis 1/2 < x to 0.69 < x to shrink its factor 4; that strengthens a hypothesis, which is a weakening, and the addendum forbids it
required_oracles:
  - Lean 4 kernel with Mathlib v4.33.0-rc2, zero sorrys
  - the axiom audit, which must show only propext, Classical.choice and Quot.sound
  - direct floating-point evaluation of every majorant against the quantity it majorises
kill_conditions:
  - a constant can only be moved by weakening a statement, adding a hypothesis, or introducing a sorry
  - lake build stops being green
  - the axiom audit changes
  - the run exceeds its 75 minute budget
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
