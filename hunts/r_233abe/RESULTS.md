# Hunt R-233ABE: results

**Status: settled. Both threads closed, zero `sorry`s, axioms unchanged, no
statement weakened.**

`lean/ZetaLean/HardyRamanujantheorem.lean` grows from 384 to 588 lines. Nothing
that stood before was touched: `hardy_ramanujan`, `turan_variance` with its
constant `275`, and `ZetaLean.Mertens.mertens_second_theorem` with band `16`
are used exactly as they stand, and no existing proof was edited.

## (a) The bridge

```lean
@[simp]
theorem omega_eq_cardDistinctFactors (n : ℕ) :
    omega n = ArithmeticFunction.cardDistinctFactors n := rfl
```

The discovering run priced this at "rfl or simp" and `rfl` is what it is, but
the reason is not the one the file's own docstring assumed. This file counts
`n.primeFactors.card`; Mathlib (`Mathlib/NumberTheory/ArithmeticFunction/Misc.lean`,
line 323) counts `n.primeFactorsList.dedup.length`. They are not the same
spelling. `Nat.primeFactors` is `primeFactorsList.toFinset`, `List.toFinset`
is `⟨l.dedup, _⟩`, and `Finset.card` of that is the dedup'd list's length, so
the two unfold to the same term and the kernel accepts `rfl`. The docstring in
the file now says which two definitions are being identified rather than
asserting they are the same one.

A one-line `rfl` is a restated definition, and the brief is explicit that a
restated definition is not a result. So the bridge is carried through to the
thing that actually makes the landed theorem consumable:

```lean
theorem hardy_ramanujan_cardDistinctFactors (ε : ℝ) (hε : 0 < ε) :
    Tendsto (fun N : ℕ =>
        (((Finset.Ioc 0 N).filter fun n =>
            ε * Real.log (Real.log N)
              < |((ArithmeticFunction.cardDistinctFactors n : ℕ) : ℝ)
                  - Real.log (Real.log N)|).card : ℝ) / (N : ℝ))
      atTop (𝓝 0)
```

Every name in that statement is Mathlib's. `omega`, `loglog`, `exceptional`
and `HardyRamanujanTheorem` have all been unfolded away, so an
`ArithmeticFunction`-facing development can cite the theorem without importing
a single definition from `ZetaLean.HardyRamanujan`. `exceptional_eq_filter_cardDistinctFactors`
records the set-level identity separately, also by `rfl`.

## (b) The pointwise form

Landed, and it is the substantive half of the run.

```lean
noncomputable def exceptionalPointwise (N : ℕ) (ε : ℝ) : Finset ℕ :=
  (Finset.Ioc 0 N).filter fun n => ε * loglog n < |(omega n : ℝ) - loglog n|

theorem hardy_ramanujan_pointwise : HardyRamanujanPointwise
```

that is: for every `ε > 0`, the density in `(0, N]` of the `n` with
`|ω n − log log n| > ε · log log n` tends to `0`. The deviation is measured
against each `n`'s own `log log n`, which is the form the theorem is usually
quoted in; `hardy_ramanujan` measures every `n` against the common `log log N`.

The route is the one the discovering run recorded, with `delta` fixed at
`1/2` so that no parameter has to be carried:

1. **The split.** `(0, N]` is cut by `n * n ≤ N` versus `N < n * n`.
2. **The low range** has at most `Nat.sqrt N` elements (`card_low_range_le`,
   by `Nat.le_sqrt` into `Finset.Icc 1 (Nat.sqrt N)`), and
   `Nat.sqrt N / N → 0` (`tendsto_natSqrt_div`, from `Nat.sqrt N * Nat.sqrt N ≤ N`
   and `Nat.sqrt (b*b) = b` for the `atTop` half).
3. **The high range** is the estimate that does the work (`loglog_band`):
   `N < n * n` gives `log N < 2 log n`, hence
   `log log N − log 2 < log log n ≤ log log N`. The gap between the two
   normalisations is bounded by the constant `log 2`, uniformly in `N`.
4. **The transfer** (`exceptionalPointwise_subset`): on the high range,
   `|ω n − log log N| ≥ |ω n − log log n| − (log log N − log log n)
   > ε log log n − log 2 ≥ ε log log N − (ε+1) log 2`, and once
   `(ε+1) log 2 ≤ (ε/2) log log N`: which happens eventually, since
   `log log N → ∞`: that is at least `(ε/2) log log N`. So the pointwise
   exceptional set sits inside the low range together with
   `exceptional N (ε/2)`, and `hardy_ramanujan` at `ε/2` finishes it.

No new arithmetic enters. The variance bound, its constant `275`, and Mertens'
band `16` are consumed unchanged; the whole upgrade is the `√N` split plus the
`log 2` slack it costs. That is worth saying plainly, because it means the
pointwise form inherits every sharpening of the density form for free: if the
Mertens band moves, both statements move together and this proof does not
change.

## What the kernel said

```
$ cd lean && PATH="$HOME/.elan/bin:$PATH" lake build ZetaLean.HardyRamanujantheorem
✔ [8699/8699] Built ZetaLean.HardyRamanujantheorem (10s)
Build completed successfully (8699 jobs).
```

`grep -c sorry` over the edited file: **0**. `#print axioms` on all five new
public statements plus `hardy_ramanujan` itself:
`[propext, Classical.choice, Quot.sound]`: the standard three, unchanged from
what the file carried before.

The repository's hunt-discipline tests are green:
`tests/test_docs_numbering.py`, `tests/test_hunt_probe_discipline.py`,
`tests/test_huntspec.py` and `tests/test_doors.py`, 31 passed;
`scripts/make_context.py --check` reports `CONTEXT.md is up to date`.

**One thing a green targeted build does not say.** `lake build` over the whole
package does *not* succeed in this container: `ZetaLean.Pub1.CertL2` and
`ZetaLean.Pub1.CertAtoms` log failures. Neither imports anything from
`ZetaLean.HardyRamanujan`: checked by `grep` over their import closure, which
runs `Mathlib`, `Pub1.CertDefs`, `Pub1.CertBounds` and `Pub1.Aristotle.O`,
so neither can be a consequence of this run's edit. What this run did *not*
establish is why they fail: both modules are expensive, one carries
`maxHeartbeats 4000000`, and re-running them to capture the error was not a
good use of the remaining budget, so a container resource limit is as
consistent with the evidence as a source defect. Recorded rather than resolved,
and flagged to the operator.

## Environment note, since it cost most of the wall clock

The container arrived with **no Lean toolchain at all**, `lake` was not on
`PATH` and `~/.elan` did not exist, so the addendum's
`cd lean && lake exe cache get` failed silently with "command not found" and
exit status 0 through the pipe. `elan` installed cleanly from
`elan.lean-lang.org` at the pinned `leanprover/lean4:v4.33.0-rc2`, and
`lake exe cache get` then fetched all 8681 Mathlib oleans. This is not a
finding about the mathematics, but a run that reads a piped exit status
instead of checking for `lake` itself will conclude the cache is warm when
nothing has happened at all.

## What resisted

Nothing mathematical. Five compile errors on the first build, all of them
library-name drift against Mathlib v4.33.0-rc2 and all fixed in one pass:
`le_or_lt` is gone (used `by_cases` instead), `div_add_div_same` is gone (used
`← add_div`), `rw [..., loglog]` cannot rewrite with the equation lemmas of a
`noncomputable def` (restated the step as a `have` closed by `rfl`), and
`Filter.Tendsto.inv_tendsto_atTop` produces `f⁻¹` in `Pi` form, which `simpa`
would not reconcile with the beta-reduced lambda the squeeze wanted (`exact`
accepts it by defeq, and a `show` pins the shape). Worth recording only as a
list for the next run in this file: the mathematics compiled as designed.

## Scope

This says nothing about ζ and nothing about RH (`docs/08`). It says nothing
about novelty either: no literature search was run, and the Hardy–Ramanujan
theorem is a 1917 result. What is original here is provenance, this
laboratory's Lean development of it, now stated in Mathlib's vocabulary and in
the pointwise form. External verification remains pending, as it does for
every claim this laboratory publishes.

## Loose threads

- **`ArithmeticFunction.cardFactors` (`Ω`, with multiplicity).** The same
  normal order `log log n` holds for `Ω`, and the standard route is
  `Ω n − ω n = O(1)` on average, `∑_{n ≤ N} (Ω n − ω n) = O(N)` by summing
  over prime powers `p^k ≤ N` with `k ≥ 2`. That is a self-contained
  double-count in the style of `sum_omega_eq_sum_div` already in the file, and
  it would put a second Mathlib-named arithmetic function under the theorem.
  First step: `∑_{n ≤ N} (Ω n − ω n) = ∑_{p, k ≥ 2, p^k ≤ N} ⌊N/p^k⌋ ≤ 2N`.
- **The Erdős–Kac strengthening is out of reach and should be said so.** It
  needs the method of moments and a central limit theorem for the
  prime-indicator sums; nothing in the current file's second-moment machinery
  extends to the higher moments without a genuine new development.
- **The constant `275` is still hostage to the Mertens band `16`,** which
  `hunts/r_4218d4/RESULTS.md` prices: the largest remaining term is the
  `log 4` in Chebyshev's bound, 39 % slack, whose removal is the prime number
  theorem. Not a thread this hunt opened, restated only because the pointwise
  form now depends on it too.
