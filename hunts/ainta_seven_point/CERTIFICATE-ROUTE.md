# What it would take to prove the certificate itself

> Feasibility study, plus the first proved slice, for the one thing the Lean bridge does not
> prove: the finite inequality `hCert`. `BRIDGE.md` proves everything between that inequality
> and the zero count, at every point count. This document is about the inequality.
>
> Labels, as elsewhere in this hunt: **VERIFIED** means run or read here this session;
> **MEASURED** means timed here on this machine; **REPORTED** means a record says so and it was
> not re-established; **INFERRED** means arithmetic or extrapolation on top of the above, with
> no independent check.

---

## 0. Answer first

**Ranked first: route (b), the verified-checker route.** Route (a) is dead on arrival because
the verifier's inner loop is a range-minimum query over a 45 608-entry table, and a
tactic-generated proof would have to re-establish each such minimum from scratch at every one of
707 901 nodes. (b) is the only one of the three with a design.

**But (b) is not executable today, and the obstruction is the search, not the table.** Measured
here: Lean's kernel reduces a balanced traversal of 131 071 nodes doing five `Nat` operations
each in 11.1 s, and does not finish 524 287 such nodes in 11 minutes of CPU while holding 2.1 GB
resident. The real search is 707 901 nodes at `p = 3000` and 1 112 733 at `p = 3400`, each node
far heavier than five `Nat` operations, and `native_decide` is refused by this laboratory's own
proof adapter. The table half, by contrast, projects to a large but finite bill: about
**90 592 cell lemmas** at the advertised parameters, at a **measured 1.6 s each** for the one
cell proved here, so roughly **40 CPU-hours** before the corrections of §5.

**The executable target is `n = 3`, not `n = 7`.** The same parametric theorem
`Zeta23Ext.Bridge.n_point_bound` at `n = 3`, `c = 1353/10⁶`, `p = 3000`, `m = 741` gives
`0.67274270083558308787` (VERIFIED, computed here at 50 digits from the closed form `Phi_n`),
which is `2.4199715617 × 10⁻⁴` **above** the upstream unconditional constant
`H = 0.67250070367941164573`. Its search is **342 nodes** (VERIFIED, this hunt's own
artifact), which is inside the measured kernel envelope by three orders of magnitude, and its
table is 29 488 cell lemmas rather than 90 592. That instance would be an unconditional
improvement on the dependency's Theorem D, kernel-checked end to end, and it is the only member
of the family that is reachable with today's Lean.

---

## 1. The goal, in Lean

### 1.1 What `hCert` says

`Zeta23Ext.Bridge.n_point_bound` (VERIFIED, read this session at
`lean/bridge/Zeta23Ext/Bridge/Main.lean:281`) takes `2 ≤ n`, `n ≤ m`, `0 < p`, `0 < c`,
`hA0 : c(m − (n−1)) ≤ 1`, and the hypothesis

```lean
hCert : ∀ g : Fin (n - 1) → ℝ, (∀ i, 0 ≤ g i) → c ≤ F n p g
```

and `seven_point_bound_lab` is its instance at `(n, c, m, p) = (7, 34697/10⁷, 294, 3400)`.
Written out at those numbers, a proof of the certificate must establish exactly this (VERIFIED,
it is `Zeta23Ext.Bridge.CertRoute.certGoal` in this hunt's Lean package, and
`certGoal_eq_hypothesis` proves by `Iff.rfl` that it is the hypothesis the theorem consumes):

```lean
∀ g : Fin (7 - 1) → ℝ, (∀ i, 0 ≤ g i) → (34697/10000000 : ℝ) ≤ F 7 3400 g
```

Unfolding the four definitions of `lean/bridge/Zeta23Ext/Bridge/Defs.lean` (VERIFIED, read this
session):

```lean
F n p g   = (1 / (p:ℝ)) * ∑ i, g i
              + ∑ i : Fin n, ∑ j : Fin n,
                  if (i:ℕ) < (j:ℕ) then
                    (2 / ((n:ℝ) - ((j:ℕ) - (i:ℕ) : ℕ))) * wfun (ptsN n g j - ptsN n g i)
                  else 0
ptsN n g i = ∑ j : Fin (n-1), if (j:ℕ) < (i:ℕ) then g j else 0
wfun x     = kfun x ^ 2
kfun x     = Kfun x / Kfun 0
Kfun x     = ∫ t in (-1/2)..(1/2), Real.cos (Real.sqrt 2 * t) * Real.cos (2 * Real.pi * x * t)
```

So the obligation is a statement about a Lebesgue interval integral of a product of two cosines,
quantified over an unbounded six-dimensional region, with 21 pairwise terms.

### 1.2 The three things that have to happen

**(i) Replace the integral by a formula.** No interval arithmetic can be run on `Kfun` as
written. `Defs.lean` says in prose that "the closed sinc form printed there is a consequence and
is what the Arb verifier evaluates", and until this session that sentence was a docstring and not
a theorem anywhere in the tree (VERIFIED: the string `sinc` occurs exactly once in
`lean/bridge/Zeta23Ext/`, in that docstring). What the bridge does prove about the kernel is
structural and not numerical: `Kfun_neg`, `kfun_neg`, `wfun_neg`, `wfun_sub_comm`,
`wfun_nonneg`, `abs_Kfun_le_Kfun_zero`, `abs_kfun_le_one`, `wfun_le_one`, all in
`Helpers_finite.lean`. None of them evaluates `Kfun` anywhere. It is now a theorem, see §4.

**(ii) Compactify.** The quantifier runs over all nonnegative `g`. The verifier's compactifying
step is the pressure term: `F n p g ≥ (1/p) ∑ gᵢ`, because every `wfun` term is a square, so
`∑ gᵢ ≥ c p` already gives `F ≥ c`. At `(c, p) = (19/5000, 3000)` that threshold is `11.4`, and
`PRESSURE_CUTOFF_CELLS / GRID = 45600 / 4000 = 11.4` exactly (VERIFIED, both constants read from
`verify_seven.py` at the pinned upstream commit). At `(34697/10⁷, 3400)` it is `11.79698`, so
`47 188` cells. This step is a three-line Lean argument and is not a difficulty.

**(iii) Discharge the compact part.** This is the whole problem, and it splits into a *table*
(rigorous lower bounds for `w` and `w''` on each grid cell) and a *search* (branch and bound over
six-dimensional boxes of cells). The rest of this document is about those two.

---

## 2. What the certificate actually is

Read off `verify_seven.py` and `kernel.py` at the pinned upstream commit
`040c5e899e658aed7b56a2a87f501798fe10761d` (VERIFIED, both files read this session), and
cross-checked against this hunt's own run record `artifacts/seven-point.local.txt` (VERIFIED).

| quantity | value | label |
|---|---|---|
| grid | `1/4000` | VERIFIED |
| Arb working precision | 128 bits | VERIFIED |
| kernel table length (`p = 3000`) | 45 608 cells | VERIFIED |
| second-derivative table, first finite cell | index 3 800 | VERIFIED |
| second-derivative table length (`p = 3000`) | 41 808 finite entries | INFERRED (45 608 − 3 800) |
| kernel table length (`p = 3400`) | 47 196 cells | INFERRED (`⌈c·p·grid⌉ + 8`) |
| second-derivative entries (`p = 3400`) | 43 396 | INFERRED |
| initial boxes | 729 = 3⁶ | VERIFIED |
| surviving one-gap components | `[3809,4778];[7221,9363];[10572,44827]` | VERIFIED |
| nodes, `p = 3000` | 707 901 | VERIFIED |
| splits / pruned | 353 586 / 354 315 | VERIFIED |
| pruning breakdown | interval 257 493, tangent 93 735, pressure 3 087 | VERIFIED |
| maximum depth | 37 | VERIFIED |
| nodes, `p = 3400`, grid 4000 | 1 112 733, depth 57 | VERIFIED (RESULTS.md §3) |
| wall time of the Arb run | 155.1 s | VERIFIED |

Three structural facts matter for the Lean question, and none of them is obvious from the
outside.

**The range-minimum structure is the inner loop.** `box_lower` makes 21 calls to
`RangeMinimum.query(left, right)` per node, where the query interval can be tens of thousands of
cells wide (the third surviving component alone spans 34 256 cells). The Python builds a sparse
table of 16 levels, about **664 209 precomputed minima** (INFERRED, from
`RangeMinimum.__init__` at length 45 608). A Lean proof must either carry that structure as data
with a soundness theorem, or re-prove each minimum from the cells beneath it. That single fact is
what decides between routes (a) and (b).

**There are two tables, not one.** The tangent prune needs lower bounds on `w''`, computed from
a formula that divides by `z³` and is therefore only used for `x ≥ 0.95`. It fires on 93 735 of
707 901 nodes (13.2%, VERIFIED). Whether the search terminates at grid 4000 without it was **not
tested here** (§6). A `w''` cell lemma is strictly harder than a `w` cell lemma: same
transcendental inputs, three more derivative levels of algebra.

**The prune that was unsound is fixed, and it changes the table size.** RESULTS.md records that
`PRESSURE_CUTOFF_CELLS = 45 600` hardcodes the original target; a Lean redo derives the cutoff
from `c` and `p`, which is what `verify_n.py` already does (VERIFIED, RESULTS.md §3).

---

## 3. The three routes

### (a) Interval arithmetic by tactic, inside Lean

The shape: subdivide the compact region, and for each box emit a `norm_num` or `nlinarith` proof
that the box's lower bound clears the target.

**Not viable, and the reason is not the node count.** It is the range minima. Each node needs 21
statements of the form "on every cell in `[left, right]`, `w ≥ q`". Produced by tactic, each such
statement costs one comparison per cell in the range, and the ranges are up to 34 256 cells wide.
Even at an optimistic 10 µs per rational comparison that is 0.34 s per query, 7.2 s per node, and
`7.2 s × 707 901 = 5.1 × 10⁶ s`, about **59 CPU-days for the queries alone** (INFERRED), before
any proof term is written. The proof term is worse: 21 queries × 34 000 comparisons × 707 901
nodes is `5 × 10¹¹` proof steps.

Sharing the minima across nodes is exactly what the sparse table does, and a shared, proved data
structure is route (b). So (a) is not a separate route so much as (b) done without the data
structure.

**Ranked third.**

### (b) A verified checker, run with `decide`

The shape: define the tables and the search tree as data; prove once that "if the checker accepts
this data then `∀ g ≥ 0, c ≤ F n p g`"; run the checker in the kernel.

This is the right design, and it is the standard one (it is what
`hunts/frontier_math/zeta23ext/Zeta23Ext/BandCert/Check.lean` does in this repository, and what the house rule in
`hunts/frontier_math/O9-BRIEF.md` prescribes: "Use `decide`, not `native_decide`"). It decomposes
cleanly:

| obligation | shape | measured or projected |
|---|---|---|
| B1. Kernel closed form | one theorem | **proved**, §4 |
| B2. Numerical primitive for `sin`/`cos` | one theorem | **proved**, §4 |
| B3. Table soundness, `w` | 47 196 cell lemmas | 1.6 s each, MEASURED |
| B4. Table soundness, `w''` | 43 396 cell lemmas | not attempted, strictly harder |
| B5. Range-minimum soundness | one theorem + 664 209 data entries | not attempted |
| B6. Box lower bound | one theorem | not attempted, routine |
| B7. Cover and pressure cutoff | one theorem | not attempted, routine |
| B8. Run the checker | 1 112 733 nodes in the kernel | **measured to be out of reach**, §5 |

**Ranked first, and blocked at B8.**

### (c) Not viable at present

This is the honest verdict for `n = 7`, and §5 gives the number that makes it a verdict rather
than an opinion. It is *not* the verdict for the family: §5.4 names an instance that is reachable
now.

---

## 4. The proved slice

Package: `hunts/ainta_seven_point/lean/`, one module `CertRoute.lean`, library `CertRoute`.
It requires `lean/bridge` **by path**, so every theorem below is about the same
`Zeta23Ext.Bridge.Kfun`, `kfun`, `wfun`, `F`, `F6` that the advertised theorem uses. Nothing is
transcribed and there is no restatement to audit. It is not part of the Palomar submission
surface and nothing in `lean/bridge` imports it.

Build (MEASURED, this machine, this session):

```
cd hunts/ainta_seven_point/lean && lake build CertRoute
```

`8842 jobs`, of which two are new (`Zeta23Ext.StableRankTrace`, `Zeta23Ext.Bridge.Defs`) and one
is this file; **55 s** cold against the shared prebuilt Mathlib store, **10.3 s** to re-elaborate
`CertRoute.lean` alone (of which most is the `#print axioms` block, see §5.1). Zero `sorry`, zero `axiom`, zero `native_decide`. All eleven audited
declarations report `[propext, Classical.choice, Quot.sound]`.

### 4.1 `Kfun_eq_sinc`, the entry point every route needs

```lean
theorem Kfun_eq_sinc (x : ℝ) :
    Kfun x = (Real.sinc ((Real.sqrt 2 - 2 * Real.pi * x) / 2)
              + Real.sinc ((Real.sqrt 2 + 2 * Real.pi * x) / 2)) / 2
```

The integral that defines the kernel equals the entire sinc form the Arb verifier evaluates, at
every real `x`, including the two points where the naive quotient form has a removable
singularity. Proved from `intervalIntegral.integral_comp_mul_left`, `integral_cos` and the
product-to-sum identity, through the lemma
`integral_cos_mul_eq_sinc : (∫ t in (-1/2)..(1/2), Real.cos (c * t)) = Real.sinc (c/2)`,
which needs no case split at `c = 0` because Mathlib's `Real.sinc` is total.

This is the first brick of any route and it did not exist. It is also the only step of the whole
project that is pure analysis rather than arithmetic.

### 4.2 `cos_sin_taylor12`, the numerical primitive Mathlib does not have

```lean
theorem cos_sin_taylor12 (θ : ℝ) (hθ : |θ| ≤ 1) :
    |Real.cos θ - (1 - θ^2/2 + θ^4/24 - θ^6/720 + θ^8/40320 - θ^10/3628800)|
        ≤ |θ|^12 * (13/5748019200) ∧
    |Real.sin θ - (θ - θ^3/6 + θ^5/120 - θ^7/5040 + θ^9/362880 - θ^11/39916800)|
        ≤ |θ|^12 * (13/5748019200)
```

VERIFIED, about the pinned Mathlib: there is no numerical evaluator for `Real.sin` or `Real.cos`
and no interval-arithmetic tactic. `Mathlib/Tactic/NormNum/` has 25 extension files and none of
them is trigonometric; `Mathlib/Tactic/` has `Bound` (a positivity-style bound prover) and
`IntervalCases` (case splitting on integer ranges), neither of which encloses a transcendental.
The sharpest thing available is `Real.cos_bound`, whose error is `5/96 · |x|⁴`, about
`2 × 10⁻²` at `θ = 0.79`. The kernel table needs about `10⁻⁹`.

The theorem above closes that by taking `Complex.exp_bound` at `n = 12`, applying it at
`x = θ i`, and reading off real and imaginary parts. Error `13/(12! · 12) = 2.26 × 10⁻⁹` at
`|θ| = 1` and `8 × 10⁻¹¹` at `θ = 0.79`. Wrapped as four one-sided enclosures
(`cos_lower`, `cos_upper`, `sin_lower`, `sin_upper`) using Mathlib's monotonicity of `cos` on
`[0, π]` and of `sin` on `[-π/2, π/2]`, so an interval argument is reduced to two rational
evaluations.

### 4.3 `kfun_closed`, and the one constant

```lean
theorem kfun_closed (x : ℝ) (h : 1 - 2*(Real.pi*x)^2 ≠ 0) :
    kfun x = (Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x))
             / (1 - 2*(Real.pi*x)^2)
```

with `gam = (√2/2) · cos(√2/2) / sin(√2/2)`, which is `(1/√2) cot(1/√2) = 3/2 − H`, the same
constant the upstream Theorem D is written in. Collecting the two sinc terms this way leaves
**one** transcendental constant to enclose once, and then `cos(πx)` and `sin(πx)` per cell, whose
argument reduction is exact in `x` because the period is exactly `2` in `x`. That is a real
simplification over enclosing two sinc values per cell, which is what the Arb code does.

`gam_bounds : 827499/10⁶ ≤ gam ∧ gam ≤ 827500/10⁶` (a `10⁻⁶`-wide enclosure) is proved from
`sqrt2_half_bounds` and §4.2.

### 4.4 The pivotal artifact: one cell of the real table

```lean
theorem wfun_cell_4160_lower (x : ℝ) (hx : 104/100 ≤ x) (hx' : x ≤ 104025/100000) :
    (23/100000 : ℝ) ≤ wfun x
```

Cell index 4160 of the verifier's `1/4000` grid, that is `x ∈ [1.04, 1.04025]`, one of the
45 608. It sits in the first surviving gap component `[3809, 4778]`, so it is a cell the search
actually queries, not a decorative one. The proof chain, all rational after the first two steps:

1. `Real.pi_gt_d20` / `pi_lt_d20` give `π` to 20 digits, hence `b = πx ∈ [3.267256, 3.268042]`.
2. `cos(πx) = −cos(π(x−1))`, `sin(πx) = −sin(π(x−1))`, so `θ = π(x−1) ∈ [0.1256637, 0.1264492]`.
3. §4.2 gives `cos θ ∈ [0.992015, 0.992115]`, `sin θ ∈ [0.125333, 0.126113]`.
4. §4.3 gives `k(x) ≥ 1522/10⁵`, hence `w(x) ≥ 23/10⁵`.

An interval evaluation of the same closed form at 20-digit precision, in exact rationals, gives
`2.3164 × 10⁻⁴` for this cell (INFERRED, computed here, not read out of the Arb table). The Lean
bound is `2.3 × 10⁻⁴`, that is **99.3% of what the arithmetic allows**, which is the relevant
tightness question: a looser table entry is still a valid one, and the only cost of looseness is
more nodes. The true minimum of `w` on the cell is `2.3171 × 10⁻⁴` in float, so the interval
evaluation itself loses `3 × 10⁻⁸` and the Lean rounding loses the remaining `1.6 × 10⁻⁶`.

**MEASURED marginal cost of one such cell: 1.6 s** of Lean elaboration plus kernel type-check
(§5.1).

---

## 5. The wall, measured

### 5.1 One cell

Measured by deletion, which is the only figure that matters for a table: build the module with
the cell theorem present once, then with six copies of it under different names, and difference.
Two runs of each, `touch` before every run so the module is re-elaborated, everything else warm
(MEASURED, this machine):

| module | run 1 | run 2 |
|---|---|---|
| one cell theorem | 6.37 s | 5.68 s |
| six cell theorems | 14.51 s | 13.39 s |

Marginal cost of five extra cells: 8.14 s and 7.71 s, that is **1.63 s and 1.54 s per cell**.
Take **1.6 s**. Everything else in the module, the one-time lemmas of §4.1 to §4.3 and Lean's
own module overhead, is the 5.7 s baseline and is paid once.

The `#print axioms` block is excluded from these numbers: auditing `certGoal_eq_hypothesis`
alone takes 11.2 s, because it walks the whole `F` and `Kfun` dependency graph down through the
pinned dependency. That is an audit cost, not a proof cost.

### 5.2 The table bill

At the advertised parameters `(n, c, p) = (7, 34697/10⁷, 3400)`, grid 4000:

```
w  cells   47 196
w'' cells  43 396
total      90 592 cell lemmas
```

(INFERRED from the verifier's own cutoff rule; the `p = 3000` figures are 45 608 and 41 808,
VERIFIED from the source constants.)

Projected: `90 592 × 1.6 s = 144 947 s = 40.3 CPU-hours`. Denominator stated plainly: **that is
90 592 lemmas at one measured lemma, extrapolated flat.** Three corrections, all upward, none
measured:

- The cell proved here has `θ = π·frac(x) ≤ 1`, so §4.2 applies directly. A general cell has
  `θ` up to `π`, needing a reflection to `[0, π/2]` and one half-angle step to get inside
  `[-1, 1]`. Estimate `× 2` (INFERRED).
- `w''` cells are harder than `w` cells by an unmeasured factor. The Arb code needs a different
  formula for them and restricts them to `x ≥ 0.95`. Estimate `× 2` (INFERRED).
- 90 592 hand-shaped lemmas need a generator and a general reduction lemma. Neither exists.

So call it **160 CPU-hours** for the tables (INFERRED), embarrassingly parallel across
files. Large, but this is not the thing that stops the project.

### 5.3 The search bill, and why it is the wall

Kernel reduction throughput, measured here with `decide` on a balanced binary traversal (`2^d`
leaves, depth `d`, five `Nat` operations per node, all on machine-sized numerals so the kernel's
GMP acceleration applies and only the recursion is unfolded). The balanced shape is the fair
model: the real branch-and-bound tree has maximum depth 37, not 10⁶.

| nodes | wall | per node |
|---|---|---|
| 2 047 | 122 ms | 60 µs |
| 32 767 | 2 545 ms | 78 µs |
| 131 071 | 11 063 ms | 84 µs |
| 524 287 | did not finish in 11 min of CPU, 2.1 GB resident | (MEASURED, negative) |

All MEASURED, this machine, `leanprover/lean4:v4.33.0-rc2`, `maxHeartbeats 0`.

Linear at about **84 µs per five-operation node up to 1.3 × 10⁵ nodes**, and then a cliff. A
linear fuel loop is worse still: 3 `Nat` operations per iteration ran 1 000 in 54 ms, 5 000 in
276 ms, 10 000 in 574 ms, and did not finish 20 000 in 15 minutes at `maxRecDepth 4 × 10⁶`
(MEASURED).

The real search is **707 901 nodes** at `p = 3000` and **1 112 733** at `p = 3400`, and a real
node is not five `Nat` operations: `box_lower` alone does 12 prefix additions, 21 range-minimum
queries and 21 rounded multiply-adds, so **at least 30 times** the arithmetic of the benchmark
node (INFERRED), plus whatever the range-minimum lookups cost in whatever encoding is chosen
(not measured, and the main remaining uncertainty).

Even taking the *linear* rate and ignoring the cliff, `1 112 733 × 30 × 84 µs = 2 804 s`, about
**47 minutes**, which would be fine. The cliff is what kills it: the measurement says the kernel
stops being linear somewhere between `1.3 × 10⁵` and `5.2 × 10⁵` nodes of *five* operations, and
the real problem is 1.1 × 10⁶ nodes of at least 150. `native_decide` would remove this entirely
and is refused by `lean/proof_adapter.py` on this repository's own rule (VERIFIED: regex
`\bnative_decide\b`, reason "trusts the compiler instead of the kernel").

### 5.4 The instance that fits

The same parametric theorem at `n = 3`. This hunt already ran the generalised verifier there
(`artifacts/verify-n3-1353-1000000-p3000.json`, VERIFIED, read this session):

| | `n = 3`, `c = 1353/10⁶`, `p = 3000`, grid 4000 |
|---|---|
| outcome | accepted |
| nodes | **342** |
| maximum depth | 17 |
| cutoff cells | 16 636 |
| surviving components | 4 |
| `w` cell lemmas | 16 644 (INFERRED) |
| `w''` cell lemmas | 12 844 (INFERRED) |
| block size cap `m` | 741, from `c(m−2) ≤ 1` |
| `Φ₃(1353/10⁶, 741, 3000)` | **0.67274270083558308787** (VERIFIED, 50 digits) |
| gain over `H = 0.67250070367941164573` | `+2.4199715617 × 10⁻⁴` |

342 nodes is **six thousand times** inside the measured envelope. The table is 29 488 lemmas
rather than 90 592, so about `29 488 × 1.6 s × 4 = 52 CPU-hours` on the same corrected
extrapolation (INFERRED). And the payoff is not conditional: `n_point_bound` is already proved
for every `n ≥ 2`, so discharging `hCert` at `n = 3` would turn
`liminf N₀ˢ(T,2T)/N(T,2T) ≥ 0.672742700` into a Lean theorem with no hypothesis left, above the
constant the dependency proves.

That is the recommendation. It is a smaller number than 0.673029553, and it is a different kind
of number.

### 5.5 Reproducing the measurements

```
cd hunts/ainta_seven_point/lean
lake build CertRoute                      # 8842 jobs, 55 s cold, zero sorry
```

The profiler figures of §5.1 and the kernel-reduction figures of §5.3 come from throwaway modules
outside the repository; the commands are recorded in `RUNS.md`.

---

## 6. What I did not do

- **I did not prove `hCert`, or any part of the search.** B5 to B8 of §3 are untouched. There is
  no checker in this repository, not even a toy one, and no soundness lemma for one.
- **I did not prove a `w''` cell bound.** The second-derivative table is 43 396 of the 90 592
  lemmas and is the harder half. Its cost is extrapolated from the `w` measurement with a
  guessed factor of 2, which is the weakest number in this document.
- **I did not handle the general cell.** `wfun_cell_4160_lower` uses a cell whose reduced
  argument already lies in `[-1, 1]`. The reflection and half-angle steps that a general cell
  needs are stated in §5.2 and are not written.
- **I did not test whether the search terminates without the tangent prune.** It fires on 13.2%
  of nodes. If it is load-bearing rather than merely fast, B4 is mandatory; if it is not, the
  table bill halves. This is one Python run and it was not made.
- **I did not measure the cost of a range-minimum lookup in the kernel** under any encoding, and
  said so in §5.3. That is the largest unmeasured quantity in the search projection.
- **I did not attempt route (a) empirically.** Its rejection in §3 is an arithmetic argument on
  the verifier's own query widths, not a timed experiment.
- **I did not touch `lean/bridge`.** The new package requires it by path and adds nothing to it.
  The Palomar submission surface, its comparator files and its `formalization.yaml` are
  unchanged, and `formalization.yaml`'s `status.scope` line that the certificate is
  "a separate project of a different size" stands: this document is the size estimate.
- **I did not change any claim of `RESULTS.md`, `TRUST-MAP.md` or `BRIDGE.md`.** Nothing here
  contradicts them. The certificate remains an interval-arithmetic verifier's acceptance and not
  a Lean fact, at every `n`.
- **I did not contact anyone, and nothing was submitted anywhere.**

---

## 7. Kill conditions for the follow-on

If someone takes the `n = 3` target of §5.4, these end it:

1. A `w` cell lemma at a general cell costs more than 10 s after the reduction lemmas exist. Then
   even 16 644 cells is 46 CPU-hours for half a table, and the generator is not worth writing.
2. The 342-node checker does not reduce in the kernel inside 10 minutes once the range-minimum
   data is real rather than a benchmark. Then no member of the family is reachable and the answer
   to this whole question is (c), flatly.
3. The `n = 3` bridge turns out to need something `n_point_bound` does not supply. The theorem
   is stated for every `n ≥ 2` and `n = 3` is inside that range, but no instance at `n = 3` has
   ever been elaborated in this tree, and `seven_point_bound` and `eight_point_bound` are the
   only instances that exist. Writing `three_point_bound` is the first thing to do, before any
   table work, and it is an afternoon or it is a surprise.
