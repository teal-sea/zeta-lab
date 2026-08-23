# TRUST-MAP: what proves the seven-point simple-zero bound, step by step

Written 2026-08-23. Companion to this hunt's `MISSION.md`, which reproduces the
finite certificates and which was still uncommitted in a sibling worktree when
this landed, so this file may arrive on `main` first. Two bookkeeping notes for
whoever lands the other half: the case-log entry in `hunts/README.md` numbers
this hunt **#78**, because `#77` is already taken on `main` by AIMO-2, and
`MISSION.md` should be renumbered to match.

This document does the other half of the hunt: it takes the implication

```
(for all g_1..g_6 >= 0:  F6(g) >= c)  and  [analytic hypotheses]
    ==>  liminf_{T->oo} N_0^s(T,2T) / N(T,2T)  >=  Phi(c, m)
```

apart into steps and grades each one. It is a map, not a proof. It re-derives
and re-checks the arithmetic of the deduction, and it does not attempt to
re-prove the analysis.

## 0. Sources, and how to read the labels

Everything below was read at these exact revisions.

| tag | what | revision |
|---|---|---|
| `[A]` | `ainta/zeta-simple-zeros`, `paper/riemann.tex` (499 lines), `docs/proof.md`, `docs/verifier.md`, `src/zeta_simple_zeros/{verify_seven,kernel,constants}.py` | `040c5e899e658aed7b56a2a87f501798fe10761d` |
| `[G]` | Gohms, issue #1 on that repository | posted 2026-08-19T03:25:43Z, no comments |
| `[C26]` | Anthropic preprint, 36 pages | `www-cdn.anthropic.com/564f962e60643842f5fcb4a17c9dbc8f608f1c37.pdf` |
| `[L23]` | `anthropics/zeta-23-lean` | HEAD `cec57f9`, tag `v1.0`, 326 `.lean` files, toolchain `v4.33.0-rc2`, Mathlib `51e6992efd06126df61a496bebf8f49482a4e129` |
| `[LZ]` | this laboratory's `lean/`, including `ZetaLean/Pub1/` | main at `f8f881b`; same toolchain and Mathlib pin as `[L23]` |

Four grades, applied to each step of the implication:

- **LEAN-BACKED**: a named declaration in a Lean 4 development that builds with
  zero `sorry`, cited by file. Which development is stated each time, because
  three different ones are in play.
- **ARB-ENCLOSED**: every step of the number carries an interval enclosure. The
  brief for this document used the laboratory's reserved word for this grade;
  that word is banned in every file under `hunts/` by
  `tests/test_hunt_probe_discipline.py`, lexically and without an exemption for
  disclaiming sentences, so the grade is spelled this way here. It is the same
  grade.
- **HANDWRITTEN**: a proof written out in prose and symbols, checked by nothing
  mechanical. Most of the chain is this, which is normal for a two-week-old
  preprint and is not by itself a criticism.
- **MISSING**: required by the chain and not proved anywhere I looked, or
  asserted without a proof I could find.

Facts carry a provenance tag: **VERIFIED** (I ran it or checked it here),
**REPORTED** (a record says so and I did not re-establish it), **INFERRED**
(reconstruction or float search), **OPEN**.

One thing this document does not do: it does not call Ainta's theorem verified.
The finite inequality has a machine-checkable artifact. The implication from it
to a statement about the zeros of zeta does not, and that asymmetry is the
subject here.

## 1. The map from the finite constant to the bound

### 1.1 The formula, now derived rather than fitted

The brief arrived with `Phi` reconstructed from two published data points and a
warning that the reconstruction could not be the whole story. The paper settles
it. Every ingredient is explicit in `paper/riemann.tex` at commit
`040c5e899e658aed7b56a2a87f501798fe10761d`, and the general shape is:

```
                H  -  6(m-1) / (p*m)
Phi(c, m, p) = ----------------------- ,      H = 3/2 - (1/sqrt2) cot(1/sqrt2)
                1  -  c(m-6) / m                = 0.6725007036794116457...
```

where `p` is the denominator of the linear pressure term in `F6` (`p = 3000` in
both published runs, `PRESSURE_DENOMINATOR` in `src/zeta_simple_zeros/verify_seven.py:28`),
`c` is the certificate target, and `m` is the sliding block size.

Derivation, by line number in `paper/riemann.tex`:

1. Line 424 (eq. `defect-global`), the output of the shifted-block averaging:
   `D(M-circ) >= (A_0/m) N_0^s - ((m-1)/(500 m)) N - o(N)`, with
   `A_0 = c(m-6)` from line 375.
2. The `1/500` there is not independent: it is `6/p` with `p = 3000`. Line 348
   derives it as "each single gap occurs at most six times", so summing the
   pressure term over the `m-6` windows charges each gap at most `6/p`. Replace
   `1/500` by `6/p` and the penalty term becomes `6(m-1)/(p*m)`.
3. Line 186 (eq. `global-defect`), the input from the stability lemma:
   `N_0^s >= H N + D(M-circ) - o(N)`.
4. Substitute 1 into 3, collect `N_0^s` on the left (lines 437 to 450), divide
   by `N` and let `T -> oo`.

VERIFIED, against both published constants at 40 decimal digits:

| source | c | m | p | Phi | published |
|---|---|---|---|---|---|
| Ainta, Theorem 1.1 (line 111) | 19/5000 | 269 | 3000 | 0.6730085279277797613234752598542 | 0.6730085279277797613 |
| Gohms, issue #1 | 191/50000 | 267 | 3000 | 0.6730213619501665335143215468657 | 0.6730213619501665 |

The paper's own closed form `(1345000 H - 2680)/1340003` (line 455) agrees with
`Phi(19/5000, 269, 3000)` to the last digit computed, which is the arithmetic
check the reconstruction needed.

A second, independent check of the same final algebra: the three-point route in
`docs/proof.md` §3 reaches the bound through a completely different defect
conversion and lands on `(H - eps/4)/(1 - eps/2)`, which at `eps = 221/10^6`
gives 0.6725197671136777, matching the 0.672519767 that document prints.
Different mechanism, same "solve the linear inequality for `S`" endgame.

### 1.2 Why m is not a free parameter

The brief's puzzle was that `Phi` is monotone increasing in `m`, so nobody would
ever "optimise" `m` down to 267. The resolution is that `m` is capped, and both
published values sit exactly at their cap.

`paper/riemann.tex:375` sets `A_0 := c(m-6)` and requires `A_0 < 1`. That
constraint is not cosmetic. It is what makes the block bound at line 387 follow
from the two lemmas above it. Lemma 4.3 (line 354) gives only

```
tr Psi(G)  >=  min { 1,  2 sum_{i<j} |G_ij|^2 }
```

and the `min` with 1 is a hard ceiling on what one block can contribute. The
block-energy lemma at line 330 supplies `2 sum |G_ij|^2 >= A_0 - span/500`, so
`min{1, A_0 - span/500} = A_0 - span/500` holds only when `A_0 <= 1`. Push
`A_0` past 1 and the block bound silently becomes `1 - o(1)`, not `A_0 - o(1)`,
and the whole `m`-linear gain disappears.

Therefore

```
m_max(c) = 6 + floor(1/c)
```

VERIFIED, both cases:

| c | 1/c | m_max | A_0 = c(m_max - 6) | published m |
|---|---|---|---|---|
| 19/5000 | 263.157894... | 269 | 4997/5000 = 0.99940 | 269 |
| 191/50000 | 261.780104... | 267 | 49851/50000 = 0.99702 | 267 |

So the reconstruction was complete after all, and there is only one free
variable. `Phi` increases in `m` and increases in `c`; "optimising the sliding
window block size", in the Gohms issue's phrase, means evaluating `m_max(c)`.
Gohms's 267 is smaller than Ainta's 269 precisely *because* their `c` is larger.

### 1.3 The consequence: the bound is not monotone in the certificate target

Because `m_max(c)` steps down as `c` rises, `c -> Phi(c, m_max(c), 3000)` is
sawtoothed: smooth and increasing on each interval `1/(n+1) < c <= 1/n`, with a
drop at every `c = 1/n`. Pushing the certificate target up can therefore *lower*
the published constant, and a decimal-race run that reports only `c` is not
reporting the bound.

The branches that matter, at `p = 3000`, with `c*` the apparent float floor
0.0038262312114228695 inherited from the sibling hunt (INFERRED, not rigorous):

| branch | largest admissible c | m | Phi |
|---|---|---|---|
| m = 269 | 1/263 = 0.00380228... | 269 | 0.673010034663 |
| m = 268 | 1/262 = 0.00381679... | 268 | 0.673019432907 |
| **m = 267** | **c\* = 0.00382623...** | **267** | **0.673025476838** |
| m = 266 | c\* | 266 | 0.673025286736 |

The `m = 269` branch that Ainta used is dominated: even saturated at `c = 1/263`
it yields 0.673010035, below what Gohms already published on the `m = 267`
branch. The family's optimum at `p = 3000` is `m = 267` with `c` as close to the
floor as a certificate can reach.

### 1.4 The ceiling of this certificate family, at the published pressure

INFERRED (the floor `c*` is a float minimum, so this is an apparent ceiling, not
a proved one):

```
Phi(c*, 267, 3000) = 0.673025476838
```

Room left on the table, from where the published work stands:

- above Ainta (0.6730085279): 1.72e-5
- above Gohms (0.6730213620): 4.11e-6
- above the window ceiling H (0.6725007037): 5.25e-4
- as a fraction of the distance from H to the configuration ceiling: **5.61
  percent** against Remark 1.1's decimal 0.68185, or 5.63 percent against the
  constant the Lean development actually proves (see below)

That last number is the one worth carrying. Everything this certificate family
can ever extract, run to exhaustion at the published pressure, is about one
eighteenth of the room the method's own optimality remark leaves open. Retuning
the pressure moves it to 0.673027719 and 5.64 percent, and no further: see
§1.5.

A correction to the number this laboratory has been quoting. `FRONTIER_MAP.md`
and `MISSION.md` both cite the configuration ceiling as 0.68185, from Remark 1.1.
That decimal appears exactly once in the Anthropic PDF, in that remark,
attributed to "an explicit extremal law on configurations" with no
cross-reference and no numbered result proving it. What `[L23]` formalizes is a
different and slightly smaller number: `Zeta23/PairCeiling/LawN256.lean:13`
carries the exact rational

```
p_0 = 10909258999421303588095230195816054408197 / 16000000000000000000000000000000000000000
    = 0.6818286874638314742559519...
```

and `Zeta23/PairCeiling/Signed.lean:94` (`ceiling_law256_signed`) proves the
ceiling as `p_0` plus a stability correction
`2.5431316e-6 * (|r'(1)| + integral |r''|)`. The string "68185" does not occur
anywhere in the Lean repository. The difference is 2.1e-5 and changes no
conclusion here, but a laboratory that quotes a ceiling to five decimals should
quote the one that has a proof attached.

Two caveats on that proof, both stated by the repository itself and worth
carrying whenever the ceiling is cited. Every ceiling theorem carries the
displayed hypothesis `EnclOK`, that the true form factor lies inside the 256
recorded enclosures, and `LawN256.lean:8-15` says those were "verified outside
Lean by interval arithmetic"; only what is downstream of them is kernel-checked,
by `decide +kernel`. And the certificate they come from,
`cert_N256_blk_b128m.json`, sha256
`cc3de9917db4d14d844630a4e97dda8387fd6e257e52b6967f430b8914584eb8`, is recorded
in that comment as "available from the authors" rather than committed. So the
ceiling is a kernel-checked implication whose antecedent is discharged by a file
that is not distributed. That is a perfectly ordinary arrangement and it is not
the same thing as an unconditional theorem, which is the distinction this
document exists to keep.

### 1.5 The third leg: the pressure denominator, which turns out to be nearly optimal

`p = 3000` is a tuning constant, not a derived one. It enters the bound twice
and in opposite directions:

- it *helps*: the penalty `6(m-1)/(p*m)` shrinks as `p` grows;
- it *hurts*: the floor `c_p = min F6` shrinks as `p` grows, because the linear
  term is what stops the gaps from spreading out to where `w` vanishes. As
  `p -> oo` the floor goes to 0 and `Phi -> H`.

That an interior optimum exists can be settled exactly, without any search.
Split the functional into its two p-independent halves,

```
F6^(p)(g) = (1/p) S(g) + W(g),   S(g) = sum g_i,   W(g) = the 21-term w-sum,
c(p) := inf_{g >= 0} F6^(p)(g).
```

VERIFIED, all four by inspection of that decomposition:

1. As a function of `u = 1/p`, `c` is an infimum of a family of affine
   functions of `u`, hence **concave and nondecreasing in `1/p`**, so
   nonincreasing in `p`. The floor can only fall as the pressure is relaxed.
2. `c(p) -> W(0) = 12` as `p -> 0+`. All 21 separations vanish, `w(0) = 1`, and
   `sum_{s=1..6} (2/(7-s)) * (7-s) = 12`.
3. `c(p) -> inf W = 0` as `p -> oo`, since `w` decays and the points may spread.
4. Therefore `m_max(c(p)) = 6 + floor(1/c(p))` runs from **6** at tiny `p` to
   unbounded at large `p`.

Feed those into `Phi`. At large `p` the gain `c(m-6)/m -> c(1 - 6c) -> 0` and
the penalty `6(m-1)/(pm) -> 0`, so `Phi -> H` and the whole refinement
evaporates. At small `p`, `m_max = 6` kills the gain outright (`A_0 = 0`) while
the penalty `6(m-1)/(pm) = 5/p` diverges, so `Phi < H`. **`Phi` therefore has an
interior maximum in `p`, and nothing in `[A]` derives 3000 or claims it is at
that maximum.** A useful approximation, accurate to about 1e-5 near the
published point because `m_max` is close to `1/c`:

```
Phi*(p)  ~  ( H - 6/p ) / ( 1 - c(p) )
```

which displays the trade-off in one line: raising `p` buys `6/p` in the
numerator and pays `c(p)` in the denominator.

Where the optimum sits is a numerical question, and it needed a gate to answer
honestly. Three global-search strategies (uniform multistart Nelder-Mead,
differential evolution, sample-then-polish) all failed at `p = 3000`, returning
floors between 0.003868 and 0.004140 against the known 0.0038262312114228695.
The reason is the shape of the minimiser: the true argmin
`(1.046, 1.989, 1.986, 1.042, 1.977, 1.045)` sums to 9.085 and is not
palindromic, while every basin those searches fell into was symmetric and summed
near 10.08. What does work is exhaustive seeding: polish all `4^6 = 4096`
combinations of the first four positive zeros of `k`
(1.057278, 2.030068, 3.020243, 4.015236), then refine the best thirty basins. At
`p = 3000` that recovers 0.0038262312113044703 and the inherited argmin to
1.2e-13, so it is used as the gate and the same method is applied at every `p`.

INFERRED (float; every `c_p` is an upper bound on the true floor, so every
`Phi*` is optimistic by an unknown amount, and the grid is coarse):

| p | c_p | sum of gaps | m\* | Phi\* |
|---|---|---|---|---|
| 2000 | 0.00534036715012 | 9.0844 | 193 | 0.672998574783 |
| 2400 | 0.00458331753466 | 9.0848 | 224 | 0.673013876508 |
| 2800 | 0.00404254533650 | 9.0851 | 253 | 0.673022517266 |
| **3000** | **0.00382623121130** | **9.0853** | **267** | **0.673025476838** |
| **3200** | **0.00363695389206** | **9.0854** | **280** | **0.673027718658** |
| 3600 | 0.00330800880647 | 10.0836 | 308 | 0.673022441702 |
| 4200 | 0.00290786192489 | 10.0838 | 349 | 0.672999570882 |
| 5000 | 0.00252371153573 | 10.0841 | 402 | 0.672976738672 |

The curve is unimodal with its peak near `p = 3200`, and **the published 3000 is
very nearly at it**. Whatever process picked 3000 picked well, whether or not it
was searched. Retuning to the peak is worth 2.24e-6 on top of the `p = 3000`
ceiling, so the family's reach becomes

- 0.673027719 at `p ~ 3200`, against 0.673025477 at `p = 3000`
- 6.36e-6 above the Gohms claim, and 1.92e-5 above Ainta's
- 5.64 percent of the room under the configuration ceiling, against 5.61

So the answer to the coupling question is a mild negative result, which is the
useful kind here: **the third leg is nearly exhausted already**. The remaining
purse in this family is about 6.4e-6 in the bound, not the 4.1e-6 a pure decimal
race would suggest and not the order of magnitude a badly tuned pressure would
have left. And it is not free: each candidate `p` changes the target, the
one-body pruning and the compactification cutoff (see §5.1, which needs
`cutoff >= p * c`), so it costs a fresh interval run per point.

## 2. The step table

`[C26]` is the Anthropic preprint, `[A]` is `paper/riemann.tex` at the pinned
commit, `[L23]` is `github.com/anthropics/zeta-23-lean` at tag v1.0, `[LZ]` is
this laboratory's `lean/`.

The single most useful thing found while building this table: **`[C26]` is not a
prose preprint with a Lean appendix bolted on. Theorem D is a kernel-checked
theorem**, and most of the machinery Ainta reaches into is already named,
reusable Lean. `comparator/Solution.lean:82` states

```lean
theorem montgomery_taylor_simple_on_critical_line_mult :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (2 - 1 / cMT - ε) * (Ncount T (2 * T) : ℝ) ≤ N0simple T (2 * T)
```

with no hypotheses on the theorem type, backed by `Zeta23/ThmD/Mult.lean:435`,
and `Zeta23/` contains zero `sorry` (the only ones are the deliberate challenge
side of `comparator/`). So the base constant `H` is not a step to grade: it is a
theorem.

| # | step | source | status | difficulty to close |
|---|---|---|---|---|
| S0 | analytic inputs: explicit formula, Riemann-von Mangoldt, Chebyshev-Mertens, Montgomery-Vaughan, Stirling | `[L23] Zeta23/Hypotheses.lean:147` (`PaperInputs`), discharged | LEAN-BACKED | done |
| S1 | `H = 3/2 - (1/sqrt2)cot(1/sqrt2)`, the base bound | `[L23] Zeta23/ThmD/Mult.lean:435`, `comparator/Solution.lean:82` | LEAN-BACKED | done |
| S2 | stability rank-trace: `‖P+Q‖_F² >= 4tr(P+Q) - 3r - 4b + tr Psi(M)` | `[A]:131` | HANDWRITTEN | **SMALL** |
| S3 | von Neumann trace inequality (inside S2) | `[L23] Zeta23/LinAlg/VonNeumann.lean:171` | LEAN-BACKED | done |
| S4 | `Q = Q+ - Q-`, `Q+Q- = 0`, `rank Q+ = n+(Q)` (inside S2) | `[L23] Zeta23/LinAlg/HermitianPosPart.lean:148-180` | LEAN-BACKED | done |
| S5 | `tr Psi(M)` is well defined for Hermitian `M` | `[L23] Zeta23/LinAlg/HermitianPosPart.lean:42` (`specMap`) | LEAN-BACKED | done |
| S6 | regrouping `Â = P₁ + Q'` with `n+(Q') <= s₂ + p` | `[C26]` Prop 4.4 proof body, `[A]:92` | HANDWRITTEN; not a named declaration in `[L23]` | SMALL-MEDIUM |
| S7 | `s₁ >= 4 tr Â - ‖Â‖_F² - 2N(I') + D(M)` | `[A]:182` | HANDWRITTEN | SMALL |
| S8 | tail passage to `N_0^s >= H·N + D(M°) - o(N)` | `[A]:186`, using `[C26]` Prop 4.2, 4.4, §§5-7 | HANDWRITTEN | **LARGE** |
| S9 | uniform kernel limit `⟨v_ρ,v_ρ'⟩ = k(x_ρ - x_ρ') + o(1)` | `[A]:227` | HANDWRITTEN | **LARGE** |
| S10 | `F6(g) >= 19/5000` for all `g >= 0` | Arb verifier, reproduced locally | ARB-ENCLOSED | LARGE (as Lean) |
| S10' | `F6(g) >= 191/50000` | Gohms run | **not established as run**, see §5.1 | one line plus a re-run |
| S11 | block energy `E_m + span/500 >= c(m-6)` | `[A]:330` | HANDWRITTEN | SMALL |
| S12 | block defect `tr Psi(G) >= min{1, 2 Σ_{i<j}|G_ij|²}` | `[A]:354` | HANDWRITTEN | SMALL |
| S13 | block bound `D(G_B) + span(B)/500 >= A_0 - o(1)`, needs `A_0 <= 1` | `[A]:387` | HANDWRITTEN | MEDIUM |
| S14 | block pinching `D(M°) >= Σ_B D(G_B)` (convex, unitarily invariant `tr Psi`) | `[A]:406` | HANDWRITTEN; general pinching MISSING from Mathlib and both Lean trees | MEDIUM |
| S15 | average over `m` offsets, `x_{S°} - x_1 <= N + o(N)` | `[A]:411` | HANDWRITTEN (RvM itself is S0) | SMALL-MEDIUM |
| S16 | solve the linear inequality for `N_0^s`, get `Phi(c,m,p)` | `[A]:437` | HANDWRITTEN | TRIVIAL, and checked here to 40 digits |

Notes on the rows that carry the weight.

**S2 is small and unusually well positioned.** Ainta's Lemma 2.1 is a strict
strengthening of `[C26]`'s Lemma 3.2 at `c = 2`, and that lemma is already Lean:
`Zeta23/LinAlg/RankTrace.lean:163`,

```lean
theorem rank_trace_ineq {P Q : Matrix n n 𝕜}
    (hP : P.PosSemidef) (hQ : Q.IsHermitian)
    {r b : ℕ} (hr : P.rank ≤ r) (hb : posIndex hQ ≤ b)
    {c : ℝ} (hc : 0 < c) :
    c * rtrace P - c ^ 2 / 4 * r + 2 * c * rtrace Q - c ^ 2 * b
      ≤ frobSq (P + Q)
```

Its Lean proof follows the same four moves Ainta's does: split `Q`, expand the
Frobenius norm, discard `tr(PQ+) >= 0`, apply von Neumann. Every one of those is
a named lemma (S3, S4). The only new content is replacing the scalar estimate
`min_{n>=0}((p-n)² + 4n) >= 2p - 1` by the exact value `2p - 1 + Psi(p)`, and
`Psi` is expressible today as `specMap`. That is why S2 is the obligation named
in §4.

**`[L23]` already keeps a defect term, just a different one.**
`Zeta23/ZeroSide/RankTraceMult.lean:281` proves a multiplicity-aware rank-trace
inequality carrying a per-zero term `gc c x = x² - c·x - (max (x-c) 0)²`, and
`Zeta23/ZeroSide/TightMult.lean:93` (`lemmaR_tight`) proves that inequality is
tight. So the repository has already mapped where the slack at the block level
is and is not. Ainta's `tr Psi(M)` is a *spectral* defect on the Gram matrix
rather than a per-zero one, and the tightness result does not forbid it, but
anyone formalizing S2 should read `lemmaR_tight` first to know what they are
not allowed to gain.

**S6 is the seam that does not exist upstream.** `[L23]`'s block layer
(`Zeta23/ZeroSide.lean`) collects *all* on-line zeros into one positive block
(`blockP`, `rank_blockP_le : ≤ s₁ + s₂`) and bounds `posIndex blockQ ≤ p`. It
never forms Ainta's `P₁` of simple zeros only with `n+(Q') <= s₂ + p`. The
ingredients are all named (`posIndex_add_le` at `Inertia.lean:90`,
`rank_hermPosPart` at `HermitianPosPart.lean:180`, `onLine_eq_S₁_union_S₂` at
`ZeroSide.lean:266`), so this is bookkeeping rather than mathematics, but it is
bookkeeping nobody has written.

**S8 and S9 are the bridge.** Both have the same shape: reach inside `[C26]`'s
analysis and carry a new nonnegative term through it uniformly. S8 needs the
tail estimate (`[L23] Zeta23/Tail.lean:450`, `prop_tail`, LEAN-BACKED) and the
trace asymptotics (`[L23] Zeta23/FinalMult.lean:76`, `moments_of_traces`,
LEAN-BACKED) to compose with a defect term that `[L23]`'s seam files do not
carry.

S9 is the harder of the two, and its status wants stating precisely rather than
as "missing". `[L23]` has more of the surrounding material than one expects: the
exact full-grid Poisson identity (`Zeta23/Poisson.lean:347`, `hasSum_phiHatR_mul`,
which is the `‖v_ρ‖ <= 1` input), the finite-`L` transform `PhiR` of the squared
window (`Zeta23/Defs.lean:241`, `Taper/Basic.lean:90`), the Montgomery-Taylor
profile itself as `vStar lam s = cos(sqrt 2 * lam * s)`
(`Zeta23/ThmD/Functional.lean:32`), and a closed-form evaluation of the cosine
window's autocorrelation (`Zeta23/ThmD/Window.lean:1211,1217`, `Cfun` and
`integral_cos_overlap`). What it does not have is Ainta's `k(x) = K(x)/K(0)`,
the `L -> oo` limit of `PhiR(hx)/(aL)`, nor any statement that a single Gram
entry converges to it. And the limit alone would not be enough: the content of
S9 is that the convergence is **uniform in `T`** over all retained pairs at
bounded normalised separation, after deleting strips of normalised width `L^2`
at both grid ends. That uniformity is what licenses replacing `2 sum |G_ij|^2`
by `E_m + o(1)` inside a block of fixed size, which is the only place the
seven-point functional touches the actual zeros. Without S9 the whole
seven-point apparatus is a true statement about a kernel that nobody has
connected to zeta.

**S10 as Lean is a scale problem, not a novelty problem.** `[L23]` already
ingests an externally computed grid of rational enclosures and re-checks it in
the kernel: `Zeta23/PairCeiling/NumericCert.lean` defines `EnclOK`, a verified
fold, and a soundness theorem `cert_of_check`, and
`Zeta23/PairCeiling/LawN256.lean:288` closes `checkRows LawN256 = true` by
`decide +kernel` over 256 rows produced outside Lean. The seven-point search
visits 707,901 nodes over a 45,600-cell table, three orders of magnitude larger,
and the transcendental (a sinc at 128 bits) would have to be re-enclosed inside
Lean rather than trusted from Arb. The pattern exists; the budget is the
question.

**S14 has a proved template for the wrong function.** General pinching, and
general convexity of `X -> tr f(X)`, are absent from Mathlib at the pinned
revision `51e6992efd06126df61a496bebf8f49482a4e129` and from both Lean trees.
But `RankTraceMult.lean:119` proves
`sum_gc_diag_le_sum_gc_eigenvalues`, Schur-Jensen for the specific function
`gc`, through the doubly-stochastic matrix of the eigenvector unitary and
Mathlib's Birkhoff theorem. That is the same proof, one function over. Note the
difference that matters: the proved statement is *diagonal* pinching, Ainta
needs *block* pinching.

### What this laboratory's own Lean arm contributes, and what it does not

Checked so that nothing above is graded MISSING when `[LZ]` already has it.

It has nothing for S2, S6, S12 or S14. There is no matrix analysis anywhere in
`lean/ZetaLean/`: no positive-semidefinite theory, no Frobenius norm, no
eigenvalues, no positive index, no von Neumann, no pinching, no Gram matrices.
The `Frobenius` hits are Frobenius traces of elliptic curves in
`FiniteFieldTrace.lean`, and the `Schur` hits are the Schur test for integral
operators in `Pub1/Aristotle/B.lean`. `Pub1/` is a self-contained variational
statement about the kernel `F1` and the source-admissible class; its two
headline theorems `pub1_strong_closure` and `pub1_strong_closure_reciprocal`
(`Pub1/Unconditional.lean`) are about `IsLUB`/`IsGLB` of a quotient, and
`Pub1/OBLIGATIONS.md` is explicit that it says nothing about zeta itself. The
tag `xi-prime-ceiling-support-v1` is an ancestor of main and everything under
`Pub1/` is byte-identical between them, so there is no separate state to check.

What it does have is directly relevant to S10, and is the one place this
laboratory is ahead rather than behind. `ZetaLean/Rigor.lean` is a rational
`Interval` type with soundness proved over the reals; `IntervalExp.lean` and
`IntervalCExp.lean` build enclosures for `exp`, `log` and `m^{-s}` from Taylor
remainders rather than trusting a library; `Ball.lean` is a rotation-invariant
second primitive; and `Pub1/CertAtoms.lean` plus `DHCertSupport.lean` are two
worked instances of the same pattern `[L23]`'s `PairCeiling` uses, namely an
external computation choosing the grid and the kernel re-proving every bound.
`Pub1/CertAtoms.lean` closes 132 externally computed atomic integrals by
`norm_num`. `DHDemo.lean`'s own header prices the scaling honestly: weeks of
`norm_num` compute for the oracle point. Anyone attempting S10 in Lean should
read those two trees together, because between them they contain both halves of
the mechanism and both measurements of what it costs.

## 3. World verdict

**B. One substantial analytic bridge**, with a large but well-templated
certificate-consumption job hanging off it.

The reasoning. The world is not A, because what is missing is not a handful of
Lean lemmas: S8 and S9 are genuine analysis, not bookkeeping, and S9 in
particular has no counterpart anywhere in `[L23]`. The world is not C either,
even though S10 really is certificate-consumption infrastructure and really is
the largest single line item by compute, because closing only S10 would leave
the interesting implication unproved. And it is not D: the marginal value is
high precisely because the surrounding material is in unusually good shape. Six
of the sixteen steps are already kernel-checked theorems in a repository that
builds sorry-free, including the two hardest classical inputs (von Neumann, the
positive-part splitting) and the two analytic inputs S8 would need to compose
with (`prop_tail`, `moments_of_traces`). Four more steps are small finite
matrix or counting statements. What separates a formalized Ainta from a
handwritten one is one bridge, taken twice: **carrying a new nonnegative
spectral defect term uniformly through the tail passage (S8), and establishing
the limiting overlap kernel with uniformity in `T` (S9)**. Both are reaching
into `[C26]`'s proof rather than citing its theorem, and `[C26]`'s Lean
development is organized to expose its *hypotheses* (`PaperInputs`) and its
*analytic estimates*, not its counting seam: the counting inequality is baked
into `ZeroSide/Mult.lean` and `FinalMult.lean` rather than abstracted behind a
parameter. A refiner writes a new seam file parallel to those, which is real
work and is not a rewrite.

One caveat on the verdict's own scope. B describes the distance from here to a
kernel-checked Ainta. It says nothing about whether a human reviewer would
accept the handwritten version, which is a different and probably faster route,
and it says nothing about whether the result is worth either: §1.4 puts the
whole family's remaining reach at 5.6 percent of the room under the
configuration ceiling.

## 4. The smallest obligation

**S2, the stability rank-trace lemma.** It is the smallest step that is both new
to Ainta and load-bearing for everything downstream, and it is the only one
whose every ingredient is already a named declaration in the same Lean
development, in the same namespace, over the same types.

Stated in a form Lean could take, in `[L23]`'s own vocabulary (`rtrace`,
`frobSq`, `posIndex`, `specMap` from `Zeta23/LinAlg/`), so that a probe would be
adding a theorem to an existing file rather than building a context:

```lean
noncomputable def Psi (t : ℝ) : ℝ := if t ≤ 2 then (t - 1) ^ 2 else 2 * t - 3

/-- Stability-enhanced rank-trace inequality.  Strengthens
`RHLinalg.rank_trace_ineq_two` by the spectral defect `tr Psi(VᴴV)`. -/
theorem stable_rank_trace
    {𝕜 : Type*} [RCLike 𝕜] {n r : Type*} [Fintype n] [DecidableEq n]
    [Fintype r] [DecidableEq r]
    (V : Matrix n r 𝕜) (hV : ∀ j, ∑ i, ‖V i j‖ ^ 2 ≤ 1)
    {Q : Matrix n n 𝕜} (hQ : Q.IsHermitian) {b : ℕ} (hb : posIndex hQ ≤ b) :
    4 * rtrace (V * Vᴴ + Q) - 3 * (Fintype.card r : ℝ) - 4 * b
        + rtrace (specMap (isHermitian_conjTranspose_mul_self V) Psi)
      ≤ frobSq (V * Vᴴ + Q)
```

Why this is the right probe target rather than a bigger one:

- It is finite-dimensional, hypothesis-free beyond the two stated bounds, and
  needs no analysis, no limits and no zeta.
- Its proof is `rank_trace_ineq`'s proof with one scalar estimate sharpened.
  `RankTrace.lean:52-56` currently supplies `sq_ge_linear`, `x² >= cx - c²/4`;
  the sharpened form is the exact minimum
  `min_{n>=0} ((p-n)² + 4n) = 2p - 1 + Psi(p)`, a one-variable calculus fact.
- The three structural inputs are done: von Neumann (`VonNeumann.lean:171`),
  the positive-part splitting with `rank Q+ = posIndex Q`
  (`HermitianPosPart.lean:148-180`), and `specMap` with its calculus
  (`specMap_isHermitian`, `rtrace_specMap`, `specMap_posSemidef`).
- Non-vacuity is easy to check: specialising `Psi` to the constant `0` must
  recover `rank_trace_ineq_two` exactly, which is a test a probe can be scored
  against.

The second-smallest, if the first lands, is S12 (`tr Psi(G) >= min{1, 2Σ|G_ij|²}`),
same file, same tools, two cases.

What a probe should **not** be pointed at: S8 or S9. Those import `[C26]`'s
machinery and are expected to stay handwritten for now. Saying so plainly is
part of the map: a probe that lands S2 has not moved the theorem, it has moved
one lemma, and the bridge is still the bridge.

## 5. Two defects found on the way

### 5.1 The Gohms variant's compactification prune is unsound at its own target

VERIFIED by reading the code and the sibling hunt's run artifact.

The verifier reduces the unbounded region to a compact box with one argument,
stated at `docs/verifier.md` under "7-point search": *if `sum g_i >= 11.4`, the
linear pressure alone proves the target*. In code this is two places:

- `verify_seven.py:105`, which only ever builds surviving cells over
  `range(PRESSURE_CUTOFF_CELLS)`, so no coordinate above 11.4 is ever enumerated;
- `verify_seven.py:276`, which prunes any box whose lower corner sums to at
  least `PRESSURE_CUTOFF_CELLS`, unconditionally and without consulting the
  target.

`PRESSURE_CUTOFF_CELLS = 45600` at `GRID = 4000` is `sum g_i >= 11.4`, and
`11.4 / 3000 = 0.0038 = 19/5000` **exactly**. The prune is therefore sound at
Ainta's target, at equality, with nothing to spare.

Gohms's run changes only `TARGET_NUMERATOR = 191`, `TARGET_DENOMINATOR = 50000`
(their issue says so explicitly, and the sibling hunt's `gohms.py` reproduces
exactly that). The target becomes 0.00382 while the outer-region argument still
delivers only 0.0038. The shortfall of 2.0e-5 per pruned box is supplied by
nothing: the pruned boxes are never evaluated.

It is exercised, not vacuous. The sibling hunt's artifact
`artifacts/seven-point.gohms-191-50000.local.txt` records
`pressure_pruned = 3087`, and its node, prune and depth counts (786421 / 393575
/ 43) match the issue's numbers exactly, so the published run pruned the same
3087 boxes on the same unproved grounds.

What this does and does not mean:

- It does **not** show `F6 >= 191/50000` is false. The apparent floor is
  0.0038262, comfortably above 0.00382, and the minimiser sits at
  `sum g = 9.085`, well inside the cutoff. The claim is likely true.
- It does mean the Gohms artifact does not establish it. As run, the program
  proves `F6 >= 191/50000` on the region it searched and `F6 >= 19/5000` on the
  region it pruned.
- The repair is one line, `PRESSURE_CUTOFF_CELLS = ceil(GRID * p * target)`,
  which is 45840 cells for 191/50000, plus a re-run. Whether the enlarged region
  still closes at grid 4000 is OPEN and needs the run, not an argument.

This belongs to the sibling hunt's reproducibility report to upstream. It is
recorded here because §2 has to grade the finite step, and the honest grade for
the Gohms target is different from the grade for Ainta's.

### 5.2 A candidate cause for the second-derivative table hash mismatch

The sibling hunt reproduced every field of the seven-point certificate except
`second_derivative_table_sha256`, and left the cause unconfirmed. Two candidates,
neither established, offered as leads rather than findings:

1. `kernel.py:145` calls `arb_lower_to_float(second.lower())`, and that helper
   itself calls `.lower()` on its argument. The double application is harmless
   if `arb.lower()` is idempotent, and is exactly where an Arb-version-dependent
   endpoint conversion would show up. Contrast `build_kernel_table`, which goes
   through `abs_lower()` once and whose hash *does* match.
2. `squared_kernel_derivatives` evaluates `z.sin()` and `z.cos()` on balls; the
   radius Arb returns for those is an implementation detail that has changed
   between FLINT releases, and only the lower endpoint is retained.

Both predict the same signature: a looser lower bound, every downstream count
identical. That is what was observed.

## 6. What I did not read

Stated plainly, because a map's blind spots are part of the map.

- **Ainta's PDF.** I read `paper/riemann.tex` (499 lines) and `docs/proof.md`
  (256 lines), not `paper/riemann.pdf`. If the two disagree, I would not know.
- **The Anthropic PDF, myself.** A subagent read all 36 pages and returned
  quoted statements; I did not independently open it. Every `[C26]` citation in
  §2 is at that one remove.
- **The Lean sources of either Lean development.** Both inventories are
  declaration-level: names, signatures, `sorry` greps. Neither was built. I did
  not run `lake build` on `lean/` or on `zeta-23-lean`, so "zero sorry" below is
  textual plus each repository's own audit artifact.
- **`tests/` in the Ainta repository**, and `verify_three.py`. The three-point
  route is quoted from `docs/proof.md`, not audited.
- **The publication workspace.** `release-candidates/pub1-arxiv/arxiv_note.tex`
  is cited by `MISSION.md` and lives in another repository I did not open.
- **PRs #91 and #81**, out of scope by instruction.
- **The proof behind the configuration ceiling.** I did not read
  `Zeta23/PairCeiling/*` myself beyond the declaration inventory in §1.4, and I
  did not check the 256 enclosures against anything. The PDF's Remark 1.1 has no
  proof in the PDF to read.
- **The `[C26]` Lean development's proofs**, as opposed to its statements. I
  know `Zeta23/` has no `sorry` by grep and by its own `#print axioms` audit
  files, not by building it.
