# Pricing Erdős–Kac: the moment method against a characteristic-function route

**Status: settled.** Both routes are mapped, both are priced, and they are not
close. The moment method is roughly 2,400 to 3,700 lines of Lean and every one
of its obligations is a thing somebody knows how to write down. The
characteristic-function / Berry–Esseen route is blocked on the fundamental
lemma of sieve theory, which Mathlib does not have, this tree does not have,
and which nobody has formalized in Lean at all. That is not a larger number.
It is a different kind of answer.

Every Mathlib claim below is resolved by compiling `Probe.lean` against the
pin in `lean/lake-manifest.json`: mathlib4 rev `51e6992e`, toolchain
`leanprover/lean4:v4.33.0-rc2`. Forty-three Mathlib declarations resolve, plus
the nine from this tree that the base rests on; the misses
are named in `results.json` and were searched for by name over the pinned
source tree, not remembered.

Nothing here is evidence for or against RH (`docs/08`). Erdős–Kac is a
theorem of 1940. Nothing here is novel mathematics, and nothing here is a step
toward the theorem: this run priced two routes and walked neither.

---

## 1. The target, and the base it starts from

Erdős–Kac: for every real `x`,

    (1/N) · #{ n ≤ N : ω(n) − log log N ≤ x·√(log log N) }  →  Φ(x).

On `main`, zero sorrys, verified by `#check` in `Probe.lean`:

| declaration | what it gives |
| --- | --- |
| `ZetaLean.HardyRamanujan.hardy_ramanujan` | Hardy–Ramanujan, density form |
| `…hardy_ramanujan_pointwise` | the same against `log log n` |
| `…hardy_ramanujan_cardDistinctFactors` | restated in Mathlib's vocabulary |
| `…omega_eq_cardDistinctFactors` | `omega = ArithmeticFunction.cardDistinctFactors`, by `rfl` |
| `…sum_sq_dev_le` | Turán's variance bound, constant `275` |
| `…second_moment_upper` | the k = 2 moment, `N·S² + N·S` |
| `…card_dvd_pair` | the k = 2 pair count |
| `ZetaLean.Mertens.mertens_second_theorem` | `|∑_{p≤N} 1/p − log log N| ≤ 16` |
| `ZetaLean.Mertens.mertens_first_theorem` | band `log 4 + 3` |

Measured sizes, which are the calibration for everything in §5:

    Mertensstheorems.lean         530 lines   (Mertens 1st)
    MertensSecond.lean            354 lines   (Mertens 2nd from 1st)
    HardyRamanujantheorem.lean    588 lines   (of which lines 90-348,
                                               259 lines, are the k=2
                                               moment computation proper)

Run `43d363c1` produced the 588-line file in 34 minutes of wall clock and
246,656 output tokens, reusing the statement and the Chebyshev reduction from
an earlier run. That is the one honest per-line datum this tree has for work
of this kind, and it is an *optimistic* datum: the mathematics there was
classical, local, and had no step whose Lean shape was in doubt.

### 1.1 A correction to the tree's own prose, which changes the price

`hunts/r_0339c1/RESULTS.md` records the Mertens band `16` as soft and its
tightening as the lever on the constant `275`. True for Hardy–Ramanujan.
**Irrelevant to Erdős–Kac**, and it is worth saying so before anyone funds the
tightening as a prerequisite.

The moment route needs the k-th central moment of `ω_y` about
`λ = ∑_{p≤y} 1/p`, and then a shift from `λ` to `log log N`. That shift enters
as `(ω − log log N) = (ω − λ) + (λ − log log N)` with `|λ − log log N| = O(1)`,
divided by `√(log log N)`. An `O(1)` **band** is exactly what is needed and it
is exactly what `mertens_second_theorem` already supplies. Mertens with its
constant, `∑_{p≤y} 1/p = log log y + M + o(1)`, is **not** needed, and this
tree does not have it. One prerequisite that looked live is dead: good news,
recorded because the opposite belief would have bought a file nobody needs.

---

## 2. What Mathlib carries, at this pin

Everything in this section resolved by compilation. The full table, hits and
misses, is `results.json`.

### 2.1 Present, and load-bearing

- **`ProbabilityTheory.tendstoInDistribution_inv_sqrt_mul_sum_sub`** and
  `…_inv_sqrt_mul_sum`. Mathlib has a one-dimensional central limit theorem
  (`Mathlib/Probability/CentralLimitTheorem.lean`, wikidata `Q190391`). Its
  hypotheses are `iIndepFun X P` and `∀ i, IdentDistrib (X i) (X 0) P P`.
- **`MeasureTheory.ProbabilityMeasure.tendsto_iff_tendsto_charFun`**: Lévy's
  continuity theorem, both directions. This is the hinge either route's last
  step turns on, and it being present is the single biggest thing in Mathlib's
  favour.
- **`MeasureTheory.charFun`**, `charFun_gaussianReal`, `taylor_charFun_two`,
  and the independence-to-product lemma
  `charFun_map_fun_finsetSum_eq_prod`. The complete characteristic-function
  toolkit, which is why Mathlib's whole CLT file is 156 lines.
- **`MeasureTheory.TendstoInDistribution`** is indexed by a *family* of
  measure spaces `(i : ι) → Ω i → E`. The arithmetic setting, where the
  probability space is uniform measure on `(0, N]` and therefore changes with
  `N`, fits the existing definition with no new one needed. Worth stating,
  because the obvious worry is that it would not.
- **`Chebyshev.pi_le_log4_mul_div`**, `Chebyshev.pi_ge`,
  `Chebyshev.theta_le_log4_mul_x`, `Chebyshev.psi_le_const_mul_self`. Explicit
  two-sided bounds on `π`. These are what bound the moment route's error
  term, and they are newer than this tree's own `ChebyshevBounds.lean`.
- **`ProbabilityTheory.iteratedDeriv_mgf_zero`** and `analyticAt_mgf`: the
  moment-generating function is analytic on the interior of its integrability
  set and its derivatives at zero are the moments. This is the scaffolding for
  the moments-to-characteristic-function shortcut A4′ of §3.
- `ProbabilityTheory.uniformOn` with `uniformOn_apply_finset`;
  `MeasureTheory.IsTightMeasureSet` and the Prokhorov direction
  `isCompact_closure_of_isTightMeasureSet` (root namespace, not
  `MeasureTheory`); `ProbabilityTheory.moment`, `centralMoment`,
  `centralMoment_two_eq_variance`.
- `Nat.doubleFactorial`, `Real.Gamma_nat_add_half` and
  `Real.Gamma_nat_add_one_add_half` (which is `Γ(k+1+1/2) = (2k+1)‼√π/2^(k+1)`,
  stated in terms of the double factorial), `integral_gaussian`, `Finpartition`,
  `Nat.smoothNumbers`, `Nat.stirlingSecond`.

### 2.2 Absent

Searched for by name across the pinned tree, and not there:

- **Berry–Esseen**, in any spelling. Zero occurrences.
- **Lindeberg**, in any spelling. Zero occurrences. There is no CLT for
  triangular arrays and none for independent non-identically-distributed
  summands.
- **Method of moments**: no Carleman condition, no Hamburger or Stieltjes
  moment problem, no theorem taking moment convergence to convergence in
  distribution. `moment` and `centralMoment` are definitions with a handful of
  small lemmas.
- **The k-th moment of a Gaussian.** `gaussianReal` has `integral_id_…` and
  `variance_id_…` and nothing higher. `∫ x^{2m} dgaussianReal 0 1 = (2m−1)‼`
  is not stated, although `Real.Gamma_nat_add_half` puts it one change of
  variables away.
- **Mertens' theorems.** Mathlib has `Nat.Primes.not_summable_one_div`, the
  divergence of `∑ 1/p`, with no rate at all. This tree's
  `ZetaLean.Mertens.mertens_second_theorem` has no Mathlib counterpart.
- **The fundamental lemma of sieve theory**, and Brun's sieve. Mathlib's
  `Mathlib/NumberTheory/SelbergSieve.lean` carries the Selberg *setup*:
  `BoundingSieve`, `IsUpperMoebius`, `siftedSum_le_mainSum_errSum_of_upperMoebius`,
  `upperMoebius_lambdaSquared`, and the diagonalisation of the Λ² main term.
  It is an **upper bound sieve only**. The phrase "fundamental lemma" occurs
  once in the file, in a docstring, describing what the sifted set is for. No
  lower bound, no two-sided asymptotic.
- **The Kubilius model.** Zero occurrences.
- **Set-partition content for `Nat.stirlingSecond`.** The file
  (`Mathlib/Combinatorics/Enumerative/Stirling.lean`, added 2025) has the
  recurrences and small values. There is no bijection to partitions of a
  `Finset`, no falling-factorial identity `x^n = ∑_k S(n,k)·x^(k)`, and
  nothing connecting it to `Finpartition`. For the k-th moment expansion it is
  a name, not a tool.
- **Perfect matchings counted by the double factorial.**
  `Mathlib/Data/Nat/Factorial/DoubleFactorial.lean` has the recurrence and
  `factorial_eq_mul_doubleFactorial`, nothing combinatorial.
- **Erdős–Kac**, and the normal order of `ArithmeticFunction.cardFactors`.

Two spelling misses worth recording so the next reader does not repeat them:
`MeasureTheory.isCompact_closure_of_isTightMeasureSet` does not resolve (the
lemma is in the root namespace), and `SelbergSieve.BoundingSieve` does not
resolve (`BoundingSieve` is a root-namespace structure; `SelbergSieve` is a
different structure extending it).

---

## 3. Route A: the moment method

Fix `k`. Truncate at `y = y(N) = N^{1/(2k)}`, set
`ω_y(n) = #{p ≤ y : p ∣ n}` and `λ = ∑_{p≤y} 1/p`.

### A1. Truncation

`∑_{n≤N} (ω(n) − ω_y(n)) ≤ C_k·N`, so the tail is `O_k(1)` in mean, hence
`o(√(log log N))` off a set of density `o(1)` by Markov.

Input: `mertens_second_theorem` applied at `N` and at `y`, giving
`∑_{y<p≤N} 1/p = O(1)` with the `O(1)` explicitly `log(2k) + 32`. The Markov
step is the shape of the existing `card_exceptional_mul_le`.

Bookkeeping, not mathematics. **~200 lines**, of which perhaps 30 novel.

### A2. The k-th moment of `ω_y`

    (1/N)·∑_{n≤N} (ω_y(n) − λ)^k  =  μ_k·λ^{k/2} + O_k(λ^{(k−1)/2}),
    μ_k = (k−1)‼ for k even, 0 for k odd.

This is the route. Sub-obligations:

- **A2a. The k-fold double count.** `(1/N)∑_n ∏_{i<r} 1_{p_i ∣ n} = ⌊N/(p_1⋯p_r)⌋/N`
  for distinct primes, which is `1/(p_1⋯p_r) + O(1/N)`. The k = 2 case is
  `card_dvd_pair` and it is 18 lines because there are exactly two cases. The
  general case needs `Nat.Coprime` over a `Finset.prod` of the image, and the
  `Nat.Ioc_filter_dvd_card_eq_div` step generalises cleanly. **~200 lines.**
- **A2b. The reindexing.** Expand `(ω_y − λ)^k = (∑_p (1_{p∣n} − 1/p))^k` and
  group the `k`-tuples `p : Fin k → primes` by the set-partition of `[k]` that
  records which coordinates carry the same prime. **This is the hardest step
  of the route.** Mathlib gives no help: `stirlingSecond` counts these
  partitions but is not connected to them, and `Finpartition` exists but has
  no `Finset.sum` reindexing lemma of the shape wanted. It has to be built,
  most likely through `Finset.sum_fiberwise` over the kernel of
  `p : Fin k → ℕ` rather than through `Finpartition` at all.
  **~400 to 700 lines**, essentially all novel.
- **A2c. The per-partition estimate.** Using `1_{p∣n}² = 1_{p∣n}`, a block of
  size `m ≥ 2` contributes `∑_p (1/p)(1 − 1/p)^m + …`, which is `λ + O(1)` for
  every `m ≥ 2`, while a block of size 1 contributes `O(1/N)` per prime. So a
  partition into `r` blocks all of size `≥ 2` contributes `~λ^r`, maximised at
  `r = k/2` by the perfect matchings, of which there are `(k−1)‼`.
  Includes proving that count, which Mathlib does not have.
  **~400 to 600 lines**, mostly novel.
- **A2d. The error term.** The accumulated `O(1/N)` over `k`-tuples is
  `O(π(y)^k/N)`, and `Chebyshev.pi_le_log4_mul_div` with `y = N^{1/(2k)}` puts
  it at `O(N^{1/2}/N)`. **~200 lines**, mostly bookkeeping now that Mathlib
  carries the `π` bound.

Subtotal A2: **~1,200 to 1,700 lines**, of which ~1,000 to 1,400 novel.

### A3. The Gaussian moments

`∫ x^k dgaussianReal 0 1 = (k−1)‼` for `k` even, `0` for `k` odd. Absent from
Mathlib; derivable from `Real.Gamma_nat_add_half` plus `integral_gaussian` and
a change of variables. Standard, but nobody has written it.
**~200 to 300 lines.**

### A4. Moments to distribution

Two ways, and the choice matters.

**A4 proper.** A general method-of-moments theorem: bounded second moments
give tightness, Prokhorov gives subsequential limits, moment determinacy of
the Gaussian (Carleman) pins the limit. Mathlib has `IsTightMeasureSet` and
`isCompact_closure_of_isTightMeasureSet`; it has nothing on determinacy.
**~800 to 1,500 lines**, and it is a Mathlib-grade contribution in its own
right, worth having independently of Erdős–Kac.

**A4′, the shortcut.** Skip determinacy. If A2 is proved with constants
uniform enough to give `E|X_N|^k ≤ C^k·k^{k/2}`, then the exponential series
for `E[e^{itX_N}]` can be summed against those moments with a uniform
remainder, and `ProbabilityMeasure.tendsto_iff_tendsto_charFun` closes it.
This trades ~600 lines of determinacy theory for ~300 to 500 lines of extra
explicit-constant work inside A2. Roughly a wash on total lines, and it
should be preferred anyway: it removes the tightness and subsequence
plumbing entirely and leans on a Mathlib theorem that is already there.

### Route A total

**~2,400 to 3,700 lines**, of which roughly 1,800 to 2,600 are novel
mathematics rather than bookkeeping.

**Hardest step: A2b, the reindexing of k-tuples of primes by set-partition of
the index set.** It is the step where the k = 2 file's two-case split
(`p = q` or `p ≠ q`) has to become something uniform in `k`, and it is the
step with the fattest tail: Lean combinatorics over `Finset` partitions is
where an estimate like this goes wrong by a factor of three rather than
twenty per cent.

---

## 4. Route B: Berry–Esseen and characteristic functions

### B1. Mathlib's CLT does not apply

`tendstoInDistribution_inv_sqrt_mul_sum_sub` requires `iIndepFun X P` and
`∀ i, IdentDistrib (X i) (X 0) P P`. The prime indicators
`X_p(n) = 1_{p ∣ n}` satisfy neither, under any measure in play:

- Under the arithmetic measure (uniform on `(0, N]`) they are not independent.
  `⌊N/pq⌋/N ≠ (⌊N/p⌋/N)(⌊N/q⌋/N)` in general, and the discrepancy is exactly
  what the whole subject is about.
- Even under the *independent model* they are not identically distributed:
  `X_p ~ Bernoulli(1/p)` and the `1/p` differ.
- The index set grows with `N`, so this is a triangular array, not a sequence.

Applying the existing CLT is not a matter of finding the right coercion.

### B2. Berry–Esseen is absent

Zero occurrences at this pin. A Berry–Esseen theorem would in any case be
*more* than the route needs (it supplies a rate; Erdős–Kac needs only the
limit), and it is harder than the Lindeberg statement that would suffice.
Pricing it is therefore pricing the wrong object, which is itself a finding:
the run 43d363c1 phrase "a formalised Berry–Esseen route" names a heavier tool
than the route actually requires.

### B3. What the route really needs first: a triangular-array CLT

For independent, non-identically-distributed, uniformly bounded summands.
Absent from Mathlib, but well supported by what is there: `charFun`,
`taylor_charFun_two`, `charFun_map_fun_finsetSum_eq_prod`,
`charFun_gaussianReal`, and Lévy continuity. The standard proof needs one
lemma Mathlib may not have in the right form
(`|∏ a_i − ∏ b_i| ≤ ∑ |a_i − b_i|` for unit-disc factors) and otherwise
follows the shape of the existing 120-line i.i.d. proof with the Taylor step
done by hand per summand.

**~600 to 900 lines**, all novel to Mathlib, and **reusable**: this is a
genuine upstream contribution that has nothing to do with ζ. Recorded as a
Core candidate.

### B4. The step that blocks the route

B3 gives a CLT for the *independent Bernoulli model*. Getting from the
arithmetic measure to that model is the whole content of Erdős–Kac, and it has
no support anywhere.

- **Via Kubilius**: bound the total variation between `(X_p)_{p≤y}` under the
  arithmetic measure and under the independent model, for `y = N^{1/u}` with
  `u → ∞`. This needs the **fundamental lemma of sieve theory**, a two-sided
  estimate. Mathlib's sieve is one-sided (`siftedSum_le_…`). There is no
  formalization of the fundamental lemma in Lean known to this run.
- **Via direct inclusion-exclusion**: compute
  `E_n[e^{it·ω_y(n)}] = ∏_{p≤y}(1 + (e^{it}−1)/p) + error` by Möbius over
  squarefree `y`-smooth divisors. The error is
  `∑_{d ∣ P(y)} |⌊N/d⌋ − N/d| ≤ 2^{π(y)}`, so the route needs
  `π(y) ≲ log₂ N`, hence `y` about `log N`. But then
  `log log y ≈ log log log N`, which is **not** asymptotic to `log log N`, and
  the normalisation the theorem is stated in dies. **The route closes on
  itself.** This is why Erdős and Kac needed Brun's sieve in 1940, and the
  same wall is there in Lean.

**Hardest step: B4, and it is hard in a different way from A2b.** A2b is a
large amount of known Lean work. B4 is a piece of mathematics that has never
been formalized, whose formalization is a multi-thousand-line project on its
own, and which is not on anybody's critical path but this one.

### The structural asymmetry, which is the finding

The moment route survives the same error-term arithmetic that kills the direct
characteristic-function route, and the reason is quantitative and simple.
**Route A needs only `k`-fold products, so its accumulated error is
`π(y)^k`, polynomial. Route B's characteristic function needs all orders at
once, so its error is `2^{π(y)}`, exponential.** Polynomial error tolerates
`y = N^{1/2k}`, which keeps `log log y ~ log log N`. Exponential error does
not. Everything else in the comparison follows from that one line.

### Route B total

B3 (~600 to 900) + B4 (~3,000 to 6,000, dominated by the sieve) =
**~3,600 to 6,900 lines**, and the wide band is not modesty. It is the honest
width for a project whose largest component has no precedent to calibrate
against.

---

## 5. How the estimates were made

They are anchored, not felt.

The k = 2 moment computation in this tree is **259 lines**
(`HardyRamanujantheorem.lean` lines 90 to 348) and it delivers a one-sided
bound with an explicit constant, not an asymptotic. Erdős–Kac needs an
asymptotic at every `k`. So the scaling question is not "259 × something": it
is how much the two-case split (`p = q`, `p ≠ q`) costs once it must be
uniform in `k`.

- A2a is the honest analogue of `card_dvd_pair` (18 lines) and
  `sum_omega_sq_eq` (21 lines), 39 lines together at k = 2, generalised to
  `Finset.prod` over an image: call it 5× for the extra `Nat.Coprime`,
  `Finset.image` and cast work. **~200.**
- A2b has no k = 2 analogue at all, because at k = 2 there are two partitions
  and both are handled by `rcases eq_or_ne p q`. The nearest comparable object
  in this tree is `MatchingCount.lean` at **655 lines**, which is one
  combinatorial counting argument over matchings and nothing else. The 400 to
  700 band is that file, taken as the unit of "one Lean combinatorial
  reindexing". It is the weakest anchor in this section and it is the reason
  §6 asks for a k = 4 probe before anyone believes the total.
- A3 is calibrated against `ChebyshevBounds.lean` (207 lines) as a comparable
  "one classical computation from Mathlib primitives" file.
- A4/A4′ is calibrated against `MertensSecond.lean` (354 lines) as the unit
  of "one self-contained analytic argument", times two to four for a general
  limit theorem.
- B3 is calibrated against Mathlib's own `CentralLimitTheorem.lean`, **156
  lines** including its header *given* the charFun toolkit, times four to six
  for losing both the i.i.d. shortcut and the sequence (rather than array)
  structure.
- B4 is calibrated against nothing, which is why its band is a factor of two
  wide and why it should be read as "unbounded" rather than as "5,000".

**What the estimates do not include**, and it is a real omission: the failed
attempts. Run `43d363c1`'s 588 lines are the surviving lines. The tree does
not record how many were written and discarded. Every number above is a
count of the file that would exist at the end, and the work is larger.

---

## 6. The comparison, and what to fund

**Fund Route A, or fund nothing. Do not fund Route B.**

Route B is not more expensive by a factor. It is blocked on the fundamental
lemma of sieve theory, an unformalized piece of mathematics whose cost is not
knowable from here, and its cheaper variant closes on itself for the reason in
§4. A run sent at Route B would spend its budget discovering §4.

Route A is expensive and every step is a step somebody knows how to write.

### The first obligation, if funded

**Not** the general `k`. Fund the **k = 4 central moment of `ω_y` with
truncation**, as a single file, as a bounded probe:

    ∑_{n≤N} (ω_y(n) − λ)^4 / N  =  3λ² + O(λ^{3/2})

k = 4 is the smallest case where A2b is real: it has partitions with a
3-block and a singleton, and it has two distinct perfect matchings, so the
`(k−1)‼` count is exercised rather than trivial. k = 3 would not do it (the
leading term vanishes and the partition structure is degenerate).

**It is diagnostic in both directions.** If the k = 4 file lands and its
partition handling is visibly uniform in `k`, then A2b is a scale-up and the
2,400-line figure is the right one. If k = 4 alone costs more than the whole
588-line k = 2 file did, then A2b is not a scale-up, the estimate is wrong by
the factor that matters, and general `k` is out of reach at this tree's
current state. Either way the operator learns it for one file's price instead
of one project's.

### Do not fund this yet, if

- The lab wants a **Mathlib contribution** sooner than a hard theorem. Then
  fund **B3 (the triangular-array CLT), or A3 (the Gaussian moments), or A4
  (method of moments) on their own.** All three are wanted upstream, none
  depends on Erdős–Kac succeeding, and each is a bounded file. B3 in
  particular is the most reusable object either route touches, and it is
  worth building whether or not Erdős–Kac is ever attempted.
- The k = 4 probe overruns. Say ~600 lines, more than twice the k = 2 moment
  computation, is the point at which the general-`k` estimate has failed and
  the honest move is to stop.
- Nobody has decided what the deliverable is. Erdős–Kac in Lean is a
  formalization of a 1940 theorem. Under this tree's own rules it would be an
  **original kernel-checked result** for this laboratory and it would not be
  novel, and it should be positioned that way from the start rather than
  discovered to be that at the end.

### The one thing that is cheap and should be done regardless

`ArithmeticFunction.cardFactors` (`Ω`, with multiplicity) has the same normal
order, by `∑_{n≤N}(Ω n − ω n) ≤ 2N` summed over prime powers. That is a
self-contained double count in the exact style of `sum_omega_eq_sum_div`,
already flagged in `hunts/r_233abe/RESULTS.md`, and it is perhaps 150 lines
for a second Mathlib-named arithmetic function under an existing theorem. It
is not on either route, and it is the best lines-to-result ratio in sight.

---

## Loose threads

- **Mathlib has no Mertens theorem, and this tree has two.**
  `mertens_first_theorem` (band `log 4 + 3`) and `mertens_second_theorem`
  (band `16`) have no counterpart at this pin; the only related declaration is
  `Nat.Primes.not_summable_one_div`, which is divergence with no rate. Run
  `43d363c1` already flagged upstreaming as operator-priced work. This run
  adds only that the gap is still open at rev `51e6992e`, so nobody filled it
  in the interim.
- **`Nat.stirlingSecond` is a stub with no combinatorial content.** Added in
  2025, it carries the recurrences and nothing tying it to partitions of a
  `Finset`. Whoever writes A2b will build that content; it belongs upstream
  and is a smaller, cleaner contribution than anything else on either route.
- **Mathlib's `TendstoInDistribution` already admits a varying probability
  space**, which is unusual and lucky. Nobody appears to have used it for a
  number-theoretic limit law. Worth knowing if the lab ever wants a second
  arithmetic distribution result.
- **The failed-attempt overhead is unmeasured**, here and everywhere in this
  tree. Every Lean estimate the lab makes counts surviving lines, because
  surviving lines are what the repository holds. A cheap instrument would be
  to have proving runs record lines-written against lines-landed; without it
  every formalization estimate this lab makes is biased low by an unknown
  factor. Recorded as a Core candidate, not built.
- **Route B's obstruction was derived, not looked up.** The `2^{π(y)}` versus
  `π(y)^k` comparison in §4 is elementary and this run is confident in it, but
  it was reasoned out here rather than taken from a source. If the operator
  wants to lean hard on "do not fund Route B", one hour against
  Granville–Soundararajan or Tenenbaum would either confirm it or find the
  sieve-free variant this run did not.
