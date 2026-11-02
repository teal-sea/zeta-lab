# Zero visibility: results

Branch `mad/zero-visibility` (local only, never pushed), worktree
`.claude/worktrees/mad-zero-visibility`, base `origin/main` at `b278389f3`. Session of
2026-11-02. Scope and rules: `lab/MISSION.md`. Labels: **PROVEN** (proof written here and
checked exhaustively on small cases, or a cited theorem), **OBSERVED** (measured, float
grade), **GUESS**. Novelty was not searched (the brief forbids external sends), so
"original" below means produced in this session, not new to the world.

## Headline

1. **The zeros zigzag more than random matrices.** Among unfolded gaps between consecutive
   zeta zeros up to T = 10^5 (138,068 gaps), the fraction that are strict local minima is
   **pV = 0.35514 ± 0.00036**, against **0.35148 ± 0.00017** for GUE (1,200,000 bulk gaps
   of 600 tridiagonal matrices) and 1/3 for independent data. Excess over GUE: 0.00366, about
   **9.2 standard errors**. Equivalently (Lemma 3), three consecutive gaps are monotone with
   probability 0.28972 ± 0.00072 for the zeros and 0.29704 ± 0.00034 for GUE. **OBSERVED.**
2. **No finite random matrix does it.** CUE(N) never exceeds the GUE value: it sits below
   at N = 4 and 6 (0.34818, 0.35053) and is flat within errors from N = 7 to 128. So no
   CUE(N) reproduces the zeros' pV, and the effective-matrix-size picture of the zeros'
   finite-height corrections accounts for at most about half of the excess. **OBSERVED**
   (the effective-size formula is quoted from memory; sections 5 and 7).
3. **Mostly, it is known physics in a new costume.** Surrogates keeping the gaps' marginal
   law and spectrum reproduce about 85% of the excess (*reported* by a verification
   agent), so it largely re-expresses the zeros' narrower gaps and stronger neighbour
   anticorrelation at these heights. **OBSERVED, reported.**
4. **No arrow of time.** The directed visibility graph of the zero gaps is as reversible as
   GUE, shuffled data and a reversible control, while the same detector finds a planted
   irreversible process at 86 standard errors. **OBSERVED.**
5. Three small exact facts about horizontal visibility graphs, one of which I first stated
   wrongly. **PROVEN** (section 2).

## 1. Reproduce

All commands from the worktree root. `lab/.venv` holds numpy 2.5.4, scipy 1.18.1,
mpmath 1.3.0, python-flint 0.9.0, hypothesis, pytest (Python 3.13.5). Prefix numerical runs
with `OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1` on a shared machine (see failure 4).

```bash
python3 -m venv lab/.venv && lab/.venv/bin/pip install numpy scipy mpmath matplotlib sympy pytest pyyaml python-flint hypothesis
lab/.venv/bin/python -m pytest -q -p no:cacheprovider -o addopts="" lab/test_hvg.py   # 10 passed
lab/.venv/bin/python lab/scan_zeros.py 100000      # 138,069 zeros, block test passes
lab/.venv/bin/python lab/scan_zeros.py 1000000     # about 75 min on this machine
lab/.venv/bin/python lab/exp_a_degree_law.py        # about 3 min, writes lab/results/exp_a.json
lab/.venv/bin/python lab/exp_b_arrow_of_time.py     # under 1 min, exp_b.json
lab/.venv/bin/python lab/exp_c_effective_n.py       # about 8 min, exp_c.json
lab/.venv/bin/python lab/exp_d_height.py            # needs the 10^6 scan, exp_d.json
lab/.venv/bin/python lab/make_viz.py                # lab/viz.html, self-contained
```

Seeds are fixed in each script (20261102 to 20261105, 7 for the sign flips), so reruns give
the same numbers.

Zeros: `zeta.statistics.zero_ordinates(t_max=..., use_cache=False)`, the repo's vectorised
Riemann-Siegel scan, saved under `lab/data/`. Completeness, float grade: with
D_n = n - 1 - theta(gamma_n)/pi, a missed or spurious zero shifts every later D_n by 1; the
mean of D over 552 blocks of 250 zeros stays in [0.4933, 0.5069] for T = 10^5 (1/2 is
correct), and max |D_n - 1/2| = 1.129. The count, 138,069, equals the repo's documented count
for T = 10^5. This is not Turing's method and not ball arithmetic.

## 2. PROVEN: three exact facts

HVG: for x_1, ..., x_n, join i < j iff x_k < min(x_i, x_j) for every i < k < j.

**Lemma 1 (edges and records).** If the x_i are distinct, the HVG has exactly 2n - L - R
edges, L and R being the numbers of strict left-to-right and right-to-left maxima.

*Proof.* Let m index the minimum. It is joined only to its immediate neighbours (a farther
node would need the neighbour in between to be below x_m). Deleting m changes no other
visibility: m never blocks (blocking needs x_m >= min(x_i, x_j)), and its two neighbours, if
both exist, were already joined. So E(x) = E(x minus m) + deg(m), with deg(m) = 2 inside and
1 at an end. Deleting down to one value gives E = 2(n - 1) - b, b the number of deletions at
an end. A value deleted at the left end is then the leftmost survivor and the minimum of the
survivors, so everything to its left is smaller: it is a left-to-right maximum; conversely
every left-to-right maximum other than the global one is deleted at the left end. Same on
the right. The global maximum is never deleted and is the only value that is both kinds of
record. So b = (L - 1) + (R - 1). QED.

Consequences: mean degree 4 - 2(L + R)/n; for i.i.d. continuous data E[L] = E[R] = H_n, so
E|E| = 2n - 2H_n. Checked: all 46,233 orderings with n <= 8; 3,000 random real sequences
(hypothesis); the exact rational identity E|E| = 2n - 2H_9 over all 362,880 orderings of 9.

**Lemma 2 (degree 2).** For distinct values, with a sentinel larger than every value at
each end, an original node has degree 2 iff it is a strict local minimum. For arbitrary
reals the weak form holds: degree 2 iff x_{i-1} >= x_i <= x_{i+1} (referee, section 7). *Proof.* On the right, i always sees
i+1. If x_{i+1} > x_i nothing beyond is visible. If x_{i+1} < x_i, the first later value
above x_{i+1} exists (sentinel) and is visible, so the right view has at least 2 nodes.
Same on the left. QED. **Without sentinels the claim is false**: in (2, 1, 0) the 1 has
degree 2 and is not a minimum. I stated the bare version first; `lab/test_hvg.py` refuted
it at n = 3 and now pins the counterexample (failure 2).

**Lemma 3 (three-gap patterns).** For a stationary sequence with a continuous law,
P(local max) = P(local min) = pV and P(a < b < c) = P(a > b > c) = 1/2 - pV for consecutive
(a, b, c). *Proof.* Stationarity gives P(a > b) = P(b < c) = 1/2. Of the six orderings,
a > b holds for (b < a < c), (b < c < a), (c < b < a), so 1/2 = pV + P(down); likewise
1/2 = pV + P(up). The four classes sum to 1, so P(local max) = 1 - pV - 2(1/2 - pV) = pV.
QED. So pV is the only three-gap ordinal statistic: "more local minima" and "fewer monotone
triples" are the same fact.

These are elementary and probably known in the HVG literature (Luque, Lacasa et al.); I did
not search.

## 3. OBSERVED: experiment A, the degree law (Conjecture A, FALSIFIED)

Conjecture A: the HVG degree law of the zero gaps breaks the i.i.d. theorem and agrees with
GUE at every k = 2..12 within 3 sigma, up to T = 10^5.

Protocol: segments of 2000 gaps, HVG per segment, 25 nodes trimmed per segment end, degrees
>= 13 pooled; error bars from the spread over segments (69 zeta segments, 300 GUE
segments). Command: `lab/exp_a_degree_law.py`; numbers in `lab/results/exp_a.json`.

| k | i.i.d. theorem | zeta (138,068 gaps) | GUE (600,000 gaps) | z(zeta - iid) | z(zeta - GUE) |
|---|---|---|---|---|---|
| 2 | 0.33333 | 0.35515 | 0.35110 | 59.0 | **8.9** |
| 3 | 0.22222 | 0.21446 | 0.21730 | -10.6 | **-3.3** |
| 4 | 0.14815 | 0.13975 | 0.14196 | -10.7 | -2.5 |
| 5 | 0.09877 | 0.09358 | 0.09283 | -8.3 | 1.1 |
| 6 | 0.06584 | 0.06326 | 0.06189 | -4.7 | 2.2 |
| 8 | 0.02926 | 0.02922 | 0.02888 | -0.1 | 0.8 |
| 12 | 0.00578 | 0.00611 | 0.00672 | 1.7 | -2.8 |
| >= 13 | 0.01156 | 0.01477 | 0.01378 | 16.5 | **4.5** |

First half of the claim holds overwhelmingly. The second fails at k = 2 (8.9 sigma), k = 3
(3.3) and the pooled tail (4.5). Checks:
- Two independent GUE samplers agree (tridiagonal beta = 2 Hermite, n = 4002, against the
  repo's dense `gue_eigenvalues`, n = 1000, at segment length 400): |z| <= 1.7 for k = 2..8.
- Planted control (zeta gaps shuffled, i.e. i.i.d. with the same marginal): matches the
  theorem within |z| <= 1.7 for k = 2..12, **but not in the pooled k >= 13 bin (z = -5.1)**:
  2000-gap segments cut long views, so the theorem's tail cannot be compared in that bin.
  Zeta against GUE uses the same protocol on both sides, so that comparison stands.
- Height: first half against second half of the zeros up to 10^5, z(high - low) = 0.3 at
  k = 2; no drift visible inside this range.

## 4. OBSERVED: experiment B, arrow of time (Conjecture B, survives)

Signed statistic d2 = mean(k_out^2) - mean(k_in^2) per 2000-gap segment, sign-flip test
over 20,000 random reversal patterns. Command: `lab/exp_b_arrow_of_time.py`.

| sequence | gaps | d2 mean ± s.e. | z | sign-flip p | KL(out ‖ in) |
|---|---|---|---|---|---|
| zeta, T <= 10^5 | 138,068 | 0.0088 ± 0.0115 | 0.8 | 0.44 | 8.1e-5 |
| zeta gaps shuffled | 138,068 | 0.0090 ± 0.0110 | 0.8 | 0.42 | 3.4e-5 |
| GUE tridiagonal | 140,000 | 0.0068 ± 0.0119 | 0.6 | 0.57 | 7.4e-5 |
| planted irreversible AR(1), Exp noise | 138,068 | -1.3927 ± 0.0161 | -86.5 | < 5e-5 | 1.4e-1 |
| planted reversible AR(1), Gaussian | 138,068 | -0.0062 ± 0.0138 | -0.4 | 0.65 | 2.5e-5 |

The zeros show no arrow on this statistic: |d2| is below 0.032 at 2 s.e., under 2.3% of the
planted arrow. A limit of the test, not a theorem: an asymmetry this statistic does not
see is not excluded.

## 5. OBSERVED: experiment C, one effective matrix size? (Conjecture C, FALSIFIED)

Conjecture C: one N makes CUE(N) match the zeros on three local statistics at once: pV, the
gap variance, and the lag-1 gap autocorrelation rho1. No segments here, so no truncation.
CUE by Haar QR with the Mezzadri phase fix, 1.2 million circular gaps per N; error bars over
matrices (CUE) or blocks of 2000 gaps (zeta, GUE). Command: `lab/exp_c_effective_n.py`.

| sequence | pV | variance | rho1 |
|---|---|---|---|
| zeta, T <= 10^5, unfolded | **0.35514 ± 0.00036** | 0.16137 ± 0.00033 | -0.35583 ± 0.00077 |
| zeta, raw gaps (control) | 0.35513 ± 0.00036 | (not comparable) | (not comparable) |
| GUE tridiagonal | 0.35148 ± 0.00017 | 0.18028 ± 0.00025 | -0.30840 ± 0.00072 |
| CUE N = 4 | 0.34818 ± 0.00022 | 0.16758 ± 0.00023 | -0.37656 ± 0.00057 |
| CUE N = 6 | 0.35053 ± 0.00018 | 0.17382 ± 0.00024 | -0.30997 ± 0.00068 |
| CUE N = 8 | 0.35096 ± 0.00018 | 0.17679 ± 0.00024 | -0.29855 ± 0.00071 |
| CUE N = 16 | 0.35142 ± 0.00018 | 0.17962 ± 0.00024 | -0.29697 ± 0.00073 |
| CUE N = 64 | 0.35101 ± 0.00018 | 0.17967 ± 0.00024 | -0.30249 ± 0.00073 |

(N = 12, 24, 32, 48 in `lab/results/exp_c.json`.) The raw-gap control reproduces the
unfolded pV to five decimals, so unfolding is not the cause. Inverting each statistic
through the CUE curve: the variance needs N below 4 (about 3.1 by extrapolating
var(N) ≈ 0.180 - 0.18/N^2), rho1 crosses at N ≈ 4.4 (but CUE's rho1 is not monotone in N,
since the gaps of one matrix sum exactly to N), and **pV crosses nowhere**: every CUE(N) lies
at or below GUE, the zeros lie above. Conjecture C fails.

Against the published picture. Bogomolny, Bohigas, Leboeuf and Monastra (J. Phys. A 39,
10743, 2006) argue that, to leading order, the zeros near height E deviate from the
asymptotic law as CUE of dimension N_eff = log(E/2pi)/sqrt(12 Lambda), Lambda = 1.57314.
**That formula and constant are quoted from memory and were not checked here.** It gives
N_eff ≈ 2.1 for the bulk of these zeros, far from the regime where a 1/N^2 expansion is
safe. My first reading, from N = 6 and 8, was a 1/N^2 coefficient of -0.033 ± 0.009,
i.e. a predicted deficit. The verification (section 7) showed that rests on N <= 6; for
N >= 8 the coefficient is -0.012 ± 0.010, so the sign is not established, only that the
leading correction is too small to give +0.004. Experiment D measures the trend with
height.

## 6. Experiment D: height dependence

PENDING (written when the 10^6 scan lands).

## 7. Independent verification (three agents, own code, nothing imported from lab/)

Workflow `zero-visibility-verify`, run `wf_9ac0e077-4cc`; scripts and outputs under the
session scratchpad `verify/`. These are agent reports: I read their numbers but did not
re-run their scripts, so anything below that I did not reproduce is marked *reported*.

**Independent recompute: confirmed.** Blind to my numbers. Zeta pV = 0.355142 ± 0.000361
(49,033 strict minima in 138,066 interior positions), identical for theta/pi unfolding,
the smooth counting function and raw gaps (49,032). Own GUE (N = 2000, central 40%, 320
matrices): 0.351537 ± 0.000397, z = 6.7. Own CUE (N = 400, 1600 matrices):
0.350870 ± 0.000250, z = 9.7. Its two references agree (1.4 sigma).

**Artifact hunter: confirmed, no artifact.** *Reported:* every one of the 138,069 zeros lies
within 1e-7 of the true zero of the same index (Arb zero counter, 0 failures, 0 undecided;
a planted 1e-9 shift is caught); the smallest gap-comparison margin is 6.8e-6, so the
count 49,033 holds for the true zeros. Noise of 1e-8 and 1e-6 on every zero moves 0
minima. Sine-process reference from 9.66 million CUE and tridiagonal gaps:
**pV_GUE = 0.35118 ± 0.00006**; excess 0.00396 (546 extra minima), **7.4 to 10.9 sigma**
depending on the error model. Its CUE values are flat for N = 7 to 128 (intercept
0.35123 ± 0.00007, 1/N^2 slope consistent with 0).

**Proof referee: confirmed, one required fix.** Lemma 1 holds on all 409,114 permutations
with n <= 9 and every proof step holds at 3,219,686 deletions. Lemma 2 needs distinct values:
with ties, (0, 0) plus sentinels has a degree-2 node with an equal neighbour. The weak
form, deg = 2 iff x_{i-1} >= x_i <= x_{i+1}, holds for all reals (4,728,880 of 4,728,880
node checks over every weak order of length <= 8). With ties, Lemma 1 becomes
**E = 2n - L - R - T**, T = number of edges joining equal values (598,445 of 598,445 weak
orders, n <= 8); no formula in record counts alone works.

**What the verification changed.**
1. *The mechanism is mostly second order.* Surrogates that keep the gaps' marginal law and
   power spectrum (IAAFT) give zeta 0.35379 against GUE 0.35035, so about 0.0034 of the
   0.0040 excess (*reported*) is carried by the zeros' narrower gap law and stronger
   neighbour anticorrelation at these heights, which are known finite-height effects. The
   excess is mainly a re-expression of them, not an independent signature.
2. *The CUE claim is weaker than I first wrote.* CUE drops below GUE only at N <= 6; from
   N = 7 up it is flat within errors. A fit over my N >= 8 values against the hunter's
   intercept gives a 1/N^2 coefficient of -0.012 ± 0.010. So the sign of the leading
   effective-CUE correction is not established. What is established: no CUE(N) for
   N = 3..128 reaches 0.355, and at 2 sigma the leading correction is at most about
   +0.008/N_eff^2, under half the excess even at N_eff = 2.1.
3. *A tension.* Inside T <= 10^5 the gap variance (0.1553 to 0.1633) and rho1 move toward
   GUE with height, but the pV excess does not shrink. By index thirds it is 0.00349,
   0.00390 and 0.00451 above GUE, about +/- 0.0006 each. Section 6 tests this to T = 10^6.
4. *Fluctuations.* The zeros' local-minimum count is unusually regular: variance per index
   0.018, against 0.040 for GUE and CUE and 2/45 = 0.044 for i.i.d. data (*reported*). That
   is consistent with the zeros' known long-range rigidity, but I did not test the link.

## 8. Failures and corrections, in order

1. **Bash and Workflow were blocked** at session start: `.claude/settings.local.json` runs
   `~/.claude/hooks/zeta-budget-guard.py`, which did not exist; python exits 2 on a missing
   script and Claude Code reads exit 2 as a block. With the operator's approval I wrote a
   minimal guard (logs and counts every Bash and Workflow call, blocks `git push` and
   `lake build`). It passed 8 of 8 self-test cases. It false-positived once on a path
   containing `pre-push`, which only blocks, so it fails safe.
2. **My Lemma 2 was wrong as first stated** (bare finite sequences). Fixed and pinned.
3. **My first exact-enumeration test claimed a 9-window decides degree 3.** It does not: a
   long decreasing run postpones the deciding value. Replaced by checks that are decided.
4. **Experiment A's first run hung for about 13 minutes**: 60 tridiagonal eigensolves of size
   20,002 (8.5 s each single-threaded) plus OpenBLAS starting 31 threads on a box at load 18.
   Killed, rerun with n = 4002 and one BLAS thread: 3 minutes.
5. **The shuffled planted control fails in the pooled k >= 13 bin** (z = -5.1): segment
   truncation. Reported in section 3; that bin is not compared against the theorem.
6. **I misquoted the levels in the artifact hunter's brief** ("about 0.353" against GUE
   "0.349 to 0.350"; the measured values were 0.3551 and 0.3511 to 0.3515). The hunter
   caught it. The numbers came from a mental Gaussian estimate, not the data.
7. **Lemma 2 was stated without "distinct values"** in the first draft of this file; the
   referee's counterexample (0, 0) forced the fix (section 2).
8. **The session process exited mid-run** while waiting on the 10^6 scan; the scan
   survived (nohup), the waiter that was to launch experiment D did not. Re-armed as a
   detached chain. Nothing was lost.
9. Side observation, not investigated: `zeta/statistics.py`'s docstring gives the block-mean
   range [0.4966, 0.5028] for T = 10^5; my blocks of 250 starting at n = 1 give
   [0.4933, 0.5069]. Both pass the completeness test by a wide margin; the docstring's
   blocking may differ.

## 9. What this is not

- Not evidence about RH. Every zero here is on the line by construction of the scan; the
  statistics are about spacing, not location.
- Float grade throughout. No ball arithmetic, no Lean.
- One family of zeros (zeta), one height range per experiment. No other L-function was
  tested, so "arithmetic" versus "finite-height universal" is not separated.
