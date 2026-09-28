# The two `hprime` derivation chains, in full

**Status: probe record. Two independent derivation chains for the retargeted
gate of `LEAN-FRONTIER.md` item 19, each with every link checked numerically at
`X = 250` and `X = 5000`, plus two independent obstruction arguments against
the literal gate. Nothing here is a result and nothing here is evidence about
RH. The Lean arm counts only what compiles; none of the chains below is in the
kernel yet.**

Captured 2026-08-12 because these chains existed only in a transient agent
transcript and are the content a later session needs in order to formalise
anything. The one-paragraph summary lives in `LEAN-FRONTIER.md` item 20; this
is the full working.

---

## 0. What both chains agree on

Both routes were run independently, told to differ deliberately, and reached
the same three conclusions:

1. **The literal gate cannot close by a Chebyshev route.** The stated
   inequality `(2j)(2j+1)D_j(X) ≤ B(X)A_j(X)` puts the *true* mass on the
   right, which needs an order-uniform **lower** bound on `A_j`.
2. **The gate should be retargeted to a majorant.** `A_j ≤ M_j` plus the
   recurrence *on `M`* gives everything downstream consumes.
3. **The majorant satisfies the recurrence with equality.** The factorial
   denominator is built so `(j+1)(2j)(2j+1)` is exactly the step ratio, so the
   tightness that defeats the literal gate is the equality the majorant enjoys.

Item 3 is now kernel-checked (`ZetaLean/MajorantBypass.lean`). Items 1 and 2
are the reason it was worth doing.

**Constants.** Route A reaches `D = log 16 ≈ 2.7726`. Route B reaches
`D = 60 log 4 ≈ 83.178`, a factor 30 worse. **Route A is the one to
formalise**; route B is kept because its obstruction argument (§3.2) is
independent and sharper, and because its analysis is strictly one-dimensional,
which is a real formalisation advantage.

---

## 1. Route A: one-shot Stieltjes domination

`C₀ = log 16 = 4 log 2`, `L = log X`, `E_j(V) = (1/(2j-1)!)∫₀^V s^(2j-1)e^s ds`,
`W_j(V)` the ordered-tuple mass (repetition allowed) with budget `V`,
`V_j(X)` the distinct-support mass without the `L_S²` head factor,
`N(y) = Σ_{p≤y}(log p)²`. Majorant `M_j(X) = C₀^j X L^(2j+1)/(j!(2j-1)!)`.

| # | statement | formalisation cost |
|---|---|---|
| L1 | `θ(y) ≤ (log 4)y` | **done**, Mathlib `Chebyshev.theta_le_log4_mul_x`, re-expressed as `ChebyshevBounds.theta_le_mul_log_four` |
| L2 | `N(y) ≤ (log y)θ(y) ≤ (log 4)y log y` | routine, termwise `log p ≤ log y`, `Finset.sum_le_sum`. **Done** as `theta_sq_le` |
| L3 | `N(e^u) ≤ C₀∫₀^u te^t dt = C₀(e^u(u-1)+1)` for all `u ≥ 0` | routine but tedious, split at `u = 2`; `u ≤ 2(u-1)` for `u ≥ 2`, then four pointwise checks at `p = 2,3,5,7` (worst needed fact: `4 ≤ 7 log 2`) |
| L4 | Abel comparison: `g ≥ 0` nonincreasing on `[0,V]` ⟹ `Σ_{log p ≤ V}(log p)²g(log p) ≤ C₀∫₀^V te^t g(t)dt` | **medium, the fiddliest link**, discrete Abel (`Mathlib.NumberTheory.AbelSummation`) plus `intervalIntegral` monotonicity against a piecewise-constant comparison |
| L5 | `W_{j+1}(V) = Σ_{log p ≤ V}(log p)²W_j(V - log p)` | routine finite combinatorics, partition ordered tuples by last coordinate |
| L6 | `∫₀^V te^t E_j(V-t)dt = E_{j+1}(V)` | routine-to-medium, Fubini on the triangle, then the Beta step `∫₀^σ t(σ-t)^(2j-1)dt = σ^(2j+1)/((2j)(2j+1))` |
| L7 | `W_j(V) ≤ C₀^j E_j(V)`, all `j ≥ 1`, `V ≥ 0` | routine given L3–L6, `Nat.le_induction` carrying a `∀V` statement |
| L8 | `E_j(V) ≤ e^V V^(2j-1)/(2j-1)!`; at `V = L`, `≤ X L^(2j-1)/(2j-1)!` | routine, monotone integrand |
| L9 | `V_j(X) ≤ W_j(L)/j!` | medium combinatorics, `j`-subsets vs ordered tuples, `j!` orderings, plus `Real.log_prod` |
| L10 | `A_j(X) ≤ L² V_j(X)` | routine, `L_S ≤ L` on every admissible support. **Done** as `logSum_le_log_of_mem_distinctPrimeSupports` |
| **M** | `A_j(X) ≤ M_j(X)`, all `j ≥ 1`, `X ≥ 2` | the chain L10 → L9 → L7 → L8 |
| **R** | `(j+1)(2j)(2j+1)M_{j+1} = C₀L²·M_j`, an equality | **done**, `MajorantBypass.powerMajorant_step` |

The transfer at the end is immediate:
`WeightedSimplex.mass_le_base_mul_pow_div_simplexFactorialDenominator` is
abstract over any mass sequence, so instantiating it at `M` and composing with
Theorem M gives the display for the true mass,
`A_r(X) ≤ (log 16)^r X (log X)^(2r+1)/(r!(2r-1)!)`, which is exactly what
`RAMS2-CLUSTER.md` line ~427 consumes.

**Numerics** (`mpmath` dps 30 for integrals, exact SPF-sieve sums; every link
at `X = 250` and `X = 5000`, global Chebyshev facts at every prime to `10^6`):

- L1 max `θ(p)/(log4·p) = 0.7209`; L2 max `0.6685`; L3 max `0.4697` (worst at
  `p = 3`).
- L3's four small-prime checks: `0.4805 ≤ 1.0710`, `1.6874 ≤ 3.5928`,
  `4.2777 ≤ 11.2212`, `8.0643 ≤ 21.1309`.
- L5 recursion identities against an independent Ω-sieve: relative error
  `≤ 1.9e-15`. L6 convolution identity: `≤ 6.6e-17`. Theorem R: `≤ 3.5e-16`.
- L4 instances: margins 3.49×/3.89× at 250, 3.22×/3.52× at 5000.
- L7 pointwise at every integer cutoff `m ≤ X` for `j = 1,2` (max ratios 0.470,
  0.099) and at the endpoint for every feasible `j` (margins 3.0× to 5.9e5× at
  250; 2.8× to 1.7e11× at 5000).
- Theorem M margins 3.9× to 3582×. `B(250) = 84.53 ≤ 117.92`;
  `B(5000) = 201.13 ≤ 251.13`.

---

## 2. Route B: marked deletion, one-dimensional Abel, induction on `j`

Deliberately different: **route B never forms a `j`-fold integral.** Every
analytic input is one-dimensional, used once per induction step. That is its
formalisation advantage over route A, and the reason it is kept despite the
worse constant.

Notation adds `m_T = ∏T`, `l_T = log m_T`, `P_T = ∏(log p)²`, and the kernel
`φ(s) = (L-s)e^(L-s)/s²` on `(0,L]`, with
`-φ'(s) = e^(L-s)s^(-2)[1+(L-s)+2(L-s)/s] ≥ 0` and `φ(L) = 0`.
Majorant `M_j(Y) = K_j Y(1+log Y)^(2j+1)`, `K_1 = log 4`,
`K_{j+1} = 60 log4·K_j/((j+1)(2j)(2j+1))`.

The claim is proved by induction on `j` with the statement quantified over
**all** cutoffs, which is what makes the one-dimensional step work:

| # | step | note |
|---|---|---|
| E1 | `(j+1)A_{j+1}(X) = Σ_{(T,q)} P_T u_q²(l_T+u_q)²` | **done**, `distinctPrimeDeletionMass_eq`, kernel-checked |
| E2 | drop `q ∉ T`; all summands `≥ 0`; every surviving `T` has `m_T ≤ X/2` | routine |
| E3 | the only prime input: `Σ_{q≤Y}(l+u_q)²u_q² ≤ log4·Y(l+log Y)²log Y` via `h(u) = (l+u)²u` increasing and `Σu_q = θ(Y)`. With `Y = X/m_T`, `l = l_T`: `l_T + log Y = L` **exactly** | routine |
| E4 | extend the `T`-range to `m_T ≤ X`; added terms have `L - l_T ≥ 0` | routine |
| E5 | exact partial summation: `(L-l)X/m = l²φ(l)`, `φ(l) = ∫_l^L(-φ')`, so the `T`-sum `= ∫_{s_j}^L(-φ'(s))A_j(e^s)ds` | **the priciest lemma**, finite-sum/integral interchange plus the cumulative-set identification `{l_T ≤ s} = {m_T ≤ e^s}`; needs a real-cutoff wrapper |
| E6 | inductive display pointwise against the nonnegative kernel | routine |
| E7 | `e^(L-s)e^s = X` exactly, giving `K_j X J_j(L)` | routine |
| E8 | `J_j ≤ 60(1+L)^(2j+1)/((2j)(2j+1))` via `(1+s)/s ≤ 1+1/(j log2)` and two Beta-type integrals; the three scalar bounds total **59.83 ≤ 60** | laborious but routine; **12× measured headroom** |
| E9 | assembly, `L² ≤ (1+L)²`; induction closes | routine |

**Numerics** (SPF sieve, exact enumeration of every squarefree support, scipy
quadrature for `J_j`; all `j` from 1 to the maximal support order at both
cutoffs, including the vacuous frontier cases): all links hold. E1 reproduces
the independent ratio table exactly (`16.4357, 10.5895, 4.6972` at 250;
`46.6417, 36.6293, 24.5703, 8.8505` at 5000). E5's identity agrees to `1e-10`
by two independent evaluations. E6 pointwise at **every** jump cutoff: minimum
`M_j/A_j` = 3.787, 803, 2.63e5, 1.42e8 at 250 and 2.718, 433.6, 9.0e4, 2.7e7,
2.2e10 at 5000. E8 measured `J_j/unit` = 4.86…4.14 at 250 and 3.62…3.18 at
5000 against the uniform proof constant 60.

---

## 3. Why the literal gate does not close: two independent arguments

### 3.1 Route A's argument: the inequality is irreducibly aggregate

The deletion identity writes
`(j+1)A_{j+1}(X) = Σ_T P_T·F(T)` with
`F(T) = Σ_{q ∉ T, q ≤ X/m_T}(L_T + log q)²(log q)²`, while
`A_j(X) = Σ_T P_T L_T²` over the **same** supports. The ratio `F(T)/L_T²` is
unbounded on supports with small product, at `T = {2}`,
`F ~ (X/2)(log X)³` against `L_T² = (log 2)²`: so the inequality is not
termwise. It asserts that the `∏(log p)²`-measure as a function of `s = L_T`
carries enough mass near `s = L`. Upper-Chebyshev information alone is
consistent with that measure concentrated at small `s`, where the inequality
fails.

And elementary two-sided Chebyshev does not repair it: Mathlib's `theta_ge`
gives lower constant `log 2` against upper `log 4`, so a two-sided route loses
`(log4/log2)^j = 2^j` across the `j`-fold structure. Since `j` ranges to
about `log X/log log X`, `2^j` exceeds every fixed power of `(1+log X)`.
Closing the literal gate uniformly in `j` therefore needs
`θ(x) = x(1+O(1/log x))`-quality input, PNT with an error term, which the
pinned Mathlib does not have.

### 3.2 Route B's argument: subset-local charging is impossible, with a
### measured crossing point

Sharper, and independent. In **any** scheme that charges each
`(j+1)`-support's weight onto its own `j`-subsets, any deletion rule
whatsoever, the pairs with both primes `≤ √X` must be absorbed by singletons
`{r}`, `r ≤ √X`. That requires

`12·A₂^small(X)/A₁(√X) ≤ B(X)`.

Since `A₂^small ~ X L⁴` and `A₁(√X) ~ √X L³`, the left side grows like
`√X/log X`. Measured against `B(X) = 60log4(1+L)²`:

| X | ratio |
|---|---|
| 250 | 0.097 |
| 5000 | 0.56 |
| 10⁵ | **2.54** |
| 10⁶ | **7.36** |

It crosses 1 near `X ≈ 2×10⁴` and diverges. **So no termwise or deletion-local
derivation of the literal gate with `B = O((1+log X)²)` exists at all.**

### 3.3 What is and is not established here

The literal statement is *numerically* true with margin at every cutoff tested,
max `LHS/RHS` = 0.194 at `X = 250` and 0.232 at `X = 5000` under route A's
`B`, i.e. 5.1× and 4.3× margin, and the measured asymptotic
`B*/(1+log X)² → ~1.1 < 2.77` makes it a plausible conjecture for all `X ≥ 2`.
It is a conjecture, not a theorem, and on the pinned toolkit it is PNT-hard.

The impossibility in §3.2 is established for the **local-transport class**
only. A fundamentally non-local elementary argument is not excluded, though
nothing in this repository or in either derivation points to one. Recorded at
that scope deliberately.

---

## 4. Disposition

- **Formalise route A**, in link order. L1, L2, L10 and Theorem R are already
  in the kernel; L3, L5, L8 are routine; **L4 and L6 are the real work** and
  are where a weaker model should not start (see the token-constraint record in
  `HANDOFF.md`).
- Keep route B for its obstruction argument and as the fallback if L4/L6 prove
  worse in Lean than estimated, its analysis is one-dimensional throughout,
  at the cost of a 30× worse constant.
- Do **not** re-derive either chain. Do not re-attempt the literal gate by a
  Chebyshev or deletion route; both are closed above, with mechanisms.
- Nothing here is promoted. A hunt may not judge itself, and this hunt has
  measured its own routes rather than had them checked by anyone else.
