# LOG: counting perfect matchings in Lean 4 + Mathlib

Running log. Appended as things happen, because a session can be killed at
any moment and a result held only in a chat window is a result that is lost.

Pin: toolchain `leanprover/lean4:v4.33.0-rc2`, mathlib rev `51e6992e`
(from `lean/lake-manifest.json`). Compiles are run as
`cd /home/user/zeta-lab/lean && lake env lean <abs path>`.

## 2026-08-18, entry 1: the oracle, run first

`hunts/rogue_frontier/matchings/oracle.py` already existed in the tree. Run
before writing any Lean, so that the target numbers are fixed before the
formal statement is:

```
 n   brute force   recursion    (n/2-1)!!
 0            1           1            1   OK
 1            0           0            0   OK
 2            1           1            1   OK
 3            0           0            0   OK
 4            3           3            3   OK
 5            0           0            0   OK
 6           15          15           15   OK
 7            0           0            0   OK
 8          105         105          105   OK
 9            0           0            0   OK
10          945         945          945   OK

all three routes agree: True
```

So the target row is `1, 0, 1, 0, 3, 0, 15, 0, 105, 0, 945`, matching the
brief. Any Lean statement disagreeing with this table on a small case is
wrong; the oracle is not.

## 2026-08-18, entry 2: gap evidence probe written

`Probe.lean` written. It does three things rather than the one asked for,
because a `#check` that succeeds is evidence of presence and there is no
`#check` that succeeds for an absent name. So absence is probed with
`run_cmd` over `getEnv`, which asks the environment directly, and then the
whole environment is swept for any declaration mentioning `PerfectMatching`,
`Isserlis`/`Wick`, or `doubleFactorial`. That converts "I grepped and found
nothing" into "the elaborated environment contains exactly these".

Compile launched (first Mathlib import, expected slow).

## 2026-08-18, entry 3: gap evidence COMPILED, exit 0

`cd lean && lake env lean .../Probe.lean` -> exit 0. Full output kept below.
This is the compiled answer to the brief's "confirm these by compiling
`#check`s, not by grep".

**Present, and load-bearing:**

```
Nat.doubleFactorial : ℕ → ℕ
Nat.doubleFactorial_two_mul     : (2 * n)‼ = 2 ^ n * n !
Nat.factorial_eq_mul_doubleFactorial : (n + 1)! = (n + 1)‼ * n‼
Nat.doubleFactorial_add_two     : (n + 2)‼ = (n + 2) * n‼
Nat.doubleFactorial_add_one     : (n + 1)‼ = (n + 1) * (n - 1)‼
SimpleGraph.Subgraph.IsPerfectMatching : G.Subgraph → Prop
SimpleGraph.Subgraph.IsPerfectMatching.even_card :
    M.IsPerfectMatching → Even (Fintype.card V)
Finset.card_eq_sum_card_fiberwise : Set.MapsTo f ↑s ↑t →
    s.card = ∑ b ∈ t, {a ∈ s | f a = b}.card
Finset.card_nbij' (i : α → β) (j : β → α) : Set.MapsTo i ↑s ↑t →
    Set.MapsTo j ↑t ↑s → Set.LeftInvOn j i ↑s → Set.RightInvOn j i ↑t →
    s.card = t.card
```

`doubleFactorial_add_one` is a small windfall the brief did not mention: it is
the recursion `(n+1)‼ = (n+1)·(n-1)‼` already in natural subtraction, which is
exactly the arithmetic shape the induction step produces. One helper lemma
saved.

**Absent, by asking the environment rather than by grep.** `run_cmd` over
`getEnv` reports ABSENT for all of: `IsPerfectMatching.card_eq`,
`IsPerfectMatching.card`, `SimpleGraph.card_perfectMatchings`,
`Subgraph.card_isPerfectMatching`, `Isserlis`, `isserlis`, `Wick`, `wick`,
`Nat.card_involutive`, `Equiv.Perm.card_fixedPointFree_involutions`,
`Finset.card_pairings`, `Finset.card_perfectMatchings`,
`Nat.card_perfectMatchings`.

**Exhaustive sweeps of the elaborated environment** (stronger than a name
list, because it does not depend on guessing the right name):

- every declaration whose name contains `PerfectMatching`, all 14 of them:
  `ConnectedComponent.even_card_of_isPerfectMatching`, `IsPerfectMatching`,
  `IsPerfectMatching.even_card`, `.exists_of_isClique_supp`,
  `.induce_connectedComponent_isMatching`, `.isAlternating_symmDiff_left`,
  `.isAlternating_symmDiff_right`, `.symmDiff_isCycles`,
  `.symmDiff_of_isAlternating`, `.toSubgraph_iff`, `isPerfectMatching_iff`,
  `isPerfectMatching_iff_forall_degree`,
  `exists_isPerfectMatching_of_forall_ncard_le`,
  `not_isTutteViolator_of_isPerfectMatching`. Exactly one of those is a
  cardinality statement and it is a parity statement, not a count. The
  brief's claim holds.
- every declaration whose lowercased name contains `isserlis` or `wick`:
  **the empty list**. Nothing in Mathlib at this pin.
- every declaration whose lowercased name contains `doublefactorial`: 15,
  all in `Nat`, all arithmetic. Nothing connects the double factorial to any
  combinatorial count.

So the gap is real: Mathlib has the number and it has the objects, and
nothing anywhere joins them.

## 2026-08-18, entry 4: formulation adopted, with two changes

Adopting the brief's `Finset`-based formulation essentially verbatim. Two
deliberate deviations, justified here as required:

1. **`dropPair` / `addPair` are named top-level definitions**, not lambdas
   inlined into `Finset.card_nbij'`. Same mathematics. The reason is
   mechanical: the four `card_nbij'` obligations each need the two maps
   evaluated at three kinds of point (`= x`, `= y`, neither), so the
   three-way case analysis is done once in three `@[simp]` lemmas per map
   rather than six times inside nested `if` goals.
2. **The induction is `Nat.twoStepInduction`, not strong induction.** The
   step consumes exactly `motive n` to build `motive (n+2)`, so the two-step
   principle is the exact shape of the recursion and strong induction would
   carry an unused hypothesis. `Nat.twoStepInduction` is in
   `Mathlib/Data/Nat/Init.lean` with cases `zero`, `one`, `more`.

Neither changes the statement. The statement is the brief's.

## 2026-08-18, entry 5: Matchings.lean written, compile 1 launched

367 lines. Narrow imports rather than `import Mathlib`, so the edit-compile
loop is loading four module trees instead of the whole library:

```
Mathlib.Data.Nat.Factorial.DoubleFactorial
Mathlib.Algebra.BigOperators.Group.Finset.Basic
Mathlib.Data.Fintype.Pi
Mathlib.Algebra.Ring.Parity
```

Structure of the file:
1. `PairsUp` / `pairings` and four accessor lemmas.
2. `pairings_empty` and `pairings_of_card_eq_one`, the two base cases.
3. `dropPair` / `addPair` with six evaluation lemmas.
4. `card_fiber_pairings`, the bijection, via `Finset.card_nbij'`.
5. `card_pairings_aux` by `Nat.twoStepInduction`, then the four public results.
6. An oracle section, and four `#print axioms`.

Compile launched.

## 2026-08-18, entry 6: compile 1, EXIT=1, nine errors, 6.4 s

Nine errors, all mechanical, none mathematical. Recorded because the
distribution is the useful datum:

1. `PairsUp.invol` returned `h.1` where `h.1 x` was wanted (the first
   conjunct is itself a `∀`).
2. Six `rewrite` failures, all one bug repeated: in the two inverse-law
   obligations the goal is `addPair x y (dropPair x y f) z = f z`, and I had
   listed `dropPair_of_ne` before `addPair_of_ne`. The inner `dropPair x y f z`
   is not a syntactic subterm until the outer `addPair` has been rewritten,
   so the inner rewrite has to come second. Composition order, not mathematics.
3. `smul_eq_mul` is not in the four narrow imports.

The mathematics compiled on the first attempt. Every error was Lean plumbing.

The 6.4 s is the payoff from narrow imports: `import Mathlib` cost several
minutes for `Probe.lean`. The edit-compile loop here is interactive.

## 2026-08-18, entry 7: compile 2, EXIT=0. It closed.

Fixes: `h.1 x`; swapped the two rewrite orders; replaced the
`sum_congr`/`sum_const`/`smul_eq_mul` chain with a single
`Finset.sum_const_nat`, which is in an import already present and is the
better lemma anyway. Also split the `variable` block into three tiers
(nothing / `[DecidableEq α]` / `[DecidableEq α] [Fintype α]`) to clear nine
unused-section-variable warnings, and dropped an unused `and_assoc` simp arg.

Result: **zero errors, zero warnings, zero sorrys**, 6.1 s.

```
'ZetaLab.Matchings.card_pairings' depends on axioms: [propext, Classical.choice, Quot.sound]
'ZetaLab.Matchings.card_pairings_two_mul' depends on axioms: [propext, Classical.choice, Quot.sound]
'ZetaLab.Matchings.card_pairings_eq_zero_of_odd' depends on axioms: [propext, Classical.choice, Quot.sound]
'ZetaLab.Matchings.pairings_eq_empty_of_odd' depends on axioms: [propext, Classical.choice, Quot.sound]
'ZetaLab.Matchings.two_pow_mul_factorial_mul_card_pairings' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Standard axioms only. No `native_decide` anywhere in the file except the word
inside a comment saying it is not used.

## 2026-08-18, entry 8: the oracle check that actually bites

The `decide` block over `Fin 0 … Fin 4` is a weak test, because with
`s = univ` the third clause of `PairsUp` ("fixes everything outside `s`") is
vacuous, so a bug in that clause would not show. The check that exercises it
is a **proper subset of a strictly larger ambient type**: if the clause were
wrong, the spare points of `Fin 5` would contribute extra pairings.

Measured, kernel `decide`, no `native_decide`:

```
(pairings ({0,1,2,3} : Finset (Fin 5))).card = 3     -- proved, ~17 s
(pairings ({0,1,2}   : Finset (Fin 5))).card = 0     -- evaluated
(pairings ({0,1}     : Finset (Fin 5))).card = 1     -- evaluated
```

The first is in the file as a `decide` proof. The other two, plus `Fin 5` and
`Fin 6` on `univ`, are `#eval` checks: compiled evaluation rather than kernel
reduction, so they are checks and not proofs, and they are labelled that way
in the file. `Fin 6` by `decide` would be roughly 15x the `Fin 5` cost and is
not worth 4 minutes on every build.

Full `#eval` row printed by the final compile, against the oracle:

| n or s | oracle | Lean |
| --- | --- | --- |
| univ, Fin 0 | 1 | 1 |
| univ, Fin 1 | 0 | 0 |
| univ, Fin 2 | 1 | 1 |
| univ, Fin 3 | 0 | 0 |
| univ, Fin 4 | 3 | 3 |
| univ, Fin 5 | 0 | 0 |
| univ, Fin 6 | 15 | 15 |
| {0,1,2,3} in Fin 5 | 3 | 3 |
| {0,1,2} in Fin 5 | 0 | 0 |
| {0,1} in Fin 5 | 1 | 1 |

Agreement on every row. The `n = 8` and `n = 10` entries (105, 945) are
covered through `card_pairings_two_mul` plus `(2*4-1)‼ = 105` and
`(2*5-1)‼ = 945` by `decide`, which is the theorem plus kernel arithmetic
rather than enumeration; enumerating `Fin 8` is 16^8 functions and is not
reachable by any evaluator here.

## 2026-08-18, entry 9: two lesion tests, both fail as they should

A file that compiles proves nothing about whether the proof is load-bearing.
Two deliberate breakages, each compiled:

- **Lesion A**, `(n-1)‼` replaced by `n‼` throughout the statement:
  **EXIT=1, 8 errors.** The count is pinned to the right double factorial,
  not to any double factorial.
- **Lesion B**, the clause `∀ x ∉ s, f x = x` deleted from `PairsUp`:
  **EXIT=1, 9 errors.** The extension-by-identity convention is load-bearing,
  which is the same thing the `Fin 5` proper-subset check tests from the
  other side.

Neither lesion is in the tree; they were built in the scratch directory and
are recorded here as measurements.

## 2026-08-18, entry 10: what is NOT proved, stated plainly

The count is proved for pairings represented as **fixed-point-free
involutions extended by the identity**. Two bridges a reader might expect are
not in this file:

1. **To `SimpleGraph.Subgraph.IsPerfectMatching`.** Mathlib's predicate lives
   on subgraphs of a `SimpleGraph`. Connecting it needs a bijection between
   `{f // PairsUp s f}` and the perfect matchings of the complete graph on
   `s`, in both directions. Nothing here is hard, and it is not free:
   estimate **80 to 150 lines**, most of it `Subgraph` bookkeeping
   (`verts`, `Adj`, symmetry, `IsMatching` as a `∀ v ∈ verts, ∃! w`).
2. **To set-partitions / `Finpartition`.** This is the form Erdos-Kac step
   A2c actually consumes, since A2b is indexed by partitions of `Fin k`. It
   needs the map from a pairing to its orbit partition and back. Estimate
   **150 to 250 lines**, and it is the one worth building next, because A2b
   already has to construct partition-indexed sums.

Neither is required by the brief, which asked for the count. Both are named
here so that nobody reads this file as having removed more of the A2c blocker
than it did. What A2c needs numerically, the number `(k-1)‼` and the fact
that it counts the maximising partitions, is now a theorem; what A2c needs
structurally, that number attached to Mathlib's partition vocabulary, is
bridge 2 and is not written.

## 2026-08-18, entry 11: a process observation, not a result

While this session was working, **something else in this checkout committed**
to branch `claude/riemann-hypothesis-research-ofds8s`: `69f9f0e` and
`e43a079` landed `oracle.py`, `NOTE.md` and the first two entries of this log
at 21:56, and `hunts/rogue_frontier/erdos_scan/` appeared untracked. This
session ran no git write command and `Matchings.lean` is untracked, as
instructed. Recorded because a reader comparing timestamps would otherwise
conclude this session committed its own work, and because the repo's own
guidance warns that parallel agents share this tree.

## Reproducing

```bash
export PATH="$HOME/.elan/bin:$PATH"
cd /home/user/zeta-lab/lean
lake env lean /home/user/zeta-lab/hunts/rogue_frontier/matchings/Matchings.lean   # ~24 s, EXIT=0
lake env lean /home/user/zeta-lab/hunts/rogue_frontier/matchings/Probe.lean       # gap evidence, slow (full Mathlib)
/home/user/zeta-lab/.venv/bin/python /home/user/zeta-lab/hunts/rogue_frontier/matchings/oracle.py
```

## Final accounting

- `Matchings.lean`: 430 lines total. 31 header doc, 62 oracle section, 7
  `#print axioms`. The mathematics proper is 330 lines, of which 51 blank and
  18 comment, so **261 substantive lines of Lean**.
- Seven public results, zero sorrys, axioms `[propext, Classical.choice,
  Quot.sound]` on every one.
- Two compiles to close it. Wall clock for the Lean work, excluding the
  full-Mathlib probe, was under an hour.
- Difficulty, honestly: **low**, and the brief is the reason. Representing a
  pairing as `α → α` over a `Finset` rather than as a matching on `Fin n`
  removed the entire reindexing problem, which is the part that makes this
  lemma expensive when people attempt it. Every error in compile 1 was
  plumbing. The one genuine design decision, extension by the identity
  outside `s`, is exactly the decision the two lesion tests and the
  proper-subset check are there to defend.
