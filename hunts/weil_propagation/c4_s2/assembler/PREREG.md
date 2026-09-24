# PREREG: assembler/, the composition of ε, the recount, the decision rule

Written 2026-09-24 on branch `teal-sea/weil-c4-s2` by the assembler/ worker,
under `assembler/BRIEF.md` (870d1bd). **Committed before any ε exists.** At
this commit `bound_trunc/` and `bound_quad/` hold only their `BRIEF.md`; I
listed both directories and read neither brief nor anything else in them.
Everything below is fixed from here on; anything added after the numbers
goes in a section headed as such in `delta_t_bound/RESULTS.md`, never here.
Nothing here is a claim about RH.

The code that carries this out is `assemble.py`; its tests are
`test_assembler.py`. The harness run on synthetic ε is `synthetic.json`
(s6).

## 0. The objects

- **Build** b = (c, N, nvec, S), Kmax = `two_adic.ta_prolate.kmax_for(nvec)`:
  the eleven (nvec, S, N) of the brief at each c ∈ {2.2, 2.5, 2.9}, 33 in all,
  each a row `c|N|40|nvec|S` of `checker/checker_ts_snapshot.json`
  (digest b2e7787bce7a).
- **R_ex(c, N)**: the Galerkin compression of R_S = Q − T_∞ − ΔT, with Q,
  T_∞ and ΔT **as this construction defines them** (checker/ s1, kernel/
  s1 to s2, two_adic/ s5 item 2), to span{U_n : |n| ≤ N}. It does not depend
  on nvec or S: every build at (c, N) approximates the same R_ex(c, N).
- **RL(b)**: the stored float64 matrix, formed exactly as
  `checker/run_checker_inertia.stored_R` forms it (Q = checker's Q at dps 40
  rounded by `to_np`, its central block for N < 32; T_S = the snapshot row;
  R = Q − T_S in numpy; lower triangle mirrored), every entry the exact
  dyadic rational it is. `run_checker_inertia` hardcodes c = 2.9;
  `assemble.stored_R` is the same lines with c a parameter, bitwise equal at
  2.9 (tested).

## (a) The composition

With Q_mp, T∞_mp the mpmath dps 40 matrices, Q_f, T∞_f their float64
roundings, dT the float64 ΔT that entered the stored sum
(`((dT + dT^*)/2).real` in `run_checker_ts.build_unit`), T_S,f = fl(T∞_f + dT)
the stored row and R_f = fl(Q_f − T_S,f):

    R_ex − RL = (Q_ex − Q_mp) + (Q_mp − Q_f)
              − (T∞_ex − T∞_mp) − (T∞_mp − T∞_f)
              − (ΔT_ex − dT)
              + (T_S,f − T∞_f − dT) − (R_f − (Q_f − T_S,f)) + (R_f − RL).

By the triangle inequality and ‖·‖₂ ≤ ‖·‖_F, ε(b) is the sum of:

| term | bounds | size, source | grade |
|---|---|---|---|
| eps_trunc | ‖ΔT_ex − ΔT_nvec‖ | `bound_trunc/eps_trunc.json` eps_upper | the folder's |
| eps_quad | ‖ΔT_nvec − dT‖ | `bound_quad/eps_quad.json` eps_upper | the folder's |
| e_Q | ‖Q_ex − Q_mp‖ | (2N+1) · 4e−39: checker/ s1, entrywise agreement with the independent CCM `galerkin.py` ≤ 5.5e−40 (pinned at 4e−39), dps 40/60 drift ≤ 3.9e−41 | hardened |
| e_T∞ | ‖T∞_ex − T∞_mp‖ | (2N+1) · 1e−29: kernel/ s2, weakest stated route agreement 1e−30 on the kernel ε(ρ), times ∫_{−L}^{L} \|K_ab\| ≤ 2L · 2 < 4.4 < 10; A to 1e−36, dps 40/60 5.1e−39 | hardened, derivation unreviewed (kernel/ s7) |
| r_Q | ‖Q_mp − Q_f‖ | Frobenius norm of the exact rational difference (mpf read from its raw tuple) | exact |
| r_T∞ | ‖T∞_mp − T∞_f‖ | the same; T∞_mp recomputed as `ta_ts.KernelProvider.T_inf_matrix` composes it (float64 bitwise equal, tested) | exact |
| r_add | ‖T_S,f − T∞_f − dT‖ | 2^−53 ‖T_S,f‖_F (binary64 round to nearest of numpy's elementwise add: \|fl(x) − x\| ≤ 2^−53 \|fl(x)\|) | exact, given IEEE 754 |
| r_sub | ‖R_f − (Q_f − T_S,f)‖ | Frobenius norm of the exact rational difference | exact |
| r_mirror | ‖R_f − RL‖ | the same (0 where R_f is symmetric) | exact |

Every term is an exact rational; eps_upper is read with `fractions.Fraction`
from its decimal string; each square root is rounded up to a rational. So
ε(b) is an exact rational, and the shift is exact.

**Interface assumptions** (for referee/ to check against the two
derivations; the assembler records what each folder states):

- **A1 (no gap between the two bounds).** ΔT_nvec is the ΔT that the first
  nvec prolate modes give with every integral exact. eps_trunc bounds
  ‖ΔT_ex − ΔT_nvec‖ and eps_quad bounds ‖ΔT_nvec − dT‖, dT being the float64
  array above. If the two folders name a different intermediate, their pair
  must still bound ‖ΔT_ex − dT‖; if it does not, that is a gap and the
  outcome is 4 until it closes.
- **A2 (the discarded imaginary part).** dT keeps the real part of
  (dT + dT^*)/2. Either ΔT_ex is real symmetric in the U_n basis or
  eps_quad covers the discarded part.
- **A3 (overlap is harmless).** If bound_quad's rounding row already
  covers the addition into T_S, r_add is counted twice; it is below 3e−15.
- Q_mp has no imaginary part (checked on every build; a nonzero one stops
  the run).

**Matching.** A build takes the entry with key (c, N, nvec, S, Kmax) with
Kmax = `kmax_for(nvec)`, c and S normalised. A missing entry, an entry at
another Kmax, or `"eps_upper": null` means **no bound for that build**
(ε(b) = none, its reason recorded). The JSON is the interface; a test calls
each folder's Python function on at least one build and checks
eps_upper ≥ the upper end of the returned arb ball, and that grade and
assumptions are present.

## (b) The count

For each build with ε = ε(b), exact rational inertia by
`run_checker_inertia`'s two routes (imported read-only; `inertia_both`,
which refuses if LDL^T and charpoly with Descartes disagree):

    L(b) = n_−(RL + εI)   (eigenvalues of RL strictly below −ε)
    U(b) = n_−(RL − εI)   (eigenvalues of RL strictly below +ε)

**Weyl** (‖R_ex − RL‖ ≤ ε): λ_k(RL) − ε ≤ λ_k(R_ex) ≤ λ_k(RL) + ε, hence
**L(b) ≤ n_−(R_ex(c, N)) ≤ U(b)**. An eigenvalue of RL at exactly +ε
gives λ_k(R_ex) ≥ 0, so U counts strictly below +ε.

**On C4's class V_4** (ĝ(+i/2) = ĝ(−i/2) = ĝ(0) = 0; v_0 = 0,
Σ h_n v_n = 0, Σ n h_n v_n = 0, h_n = 1/(L² + 16π²n²), L = log c), the same
two shifts of Z^T(RL ± εI)Z by `run_checker_inertia.inertia_balls` (every
pivot ball excluding 0, at 256 then 512 bits). `run_checker_inertia`'s class
basis hardcodes 29/10; `assemble.class_basis_c` is the same formula with c
exact (11/5, 5/2, 29/10), identical balls at 29/10 (tested), and checker/'s
derivation check against `checker_q.transform_rows` is repeated at each
cell. Weyl holds on V_4 for the compressions (‖P(R_ex − RL)P‖ ≤ ε). Where
the balls do not decide, the min-max fallback is used and labelled:
L_V4 ≥ L − 3, U_V4 ≤ U.

**Aggregation over builds.** Every build at (c, N) bounds the same
n_−(R_ex(c, N)), so

    L*_N = max over builds with a bound of L(b),   U*_N = min of U(b).

**Interlacing.** span_8 ⊂ span_16 ⊂ span_32, and V_4 at N is V_4 at N' ∩
span_N (its three constraints are functionals on L²[0, L]); by Cauchy
interlacing n_−(R_ex) is nondecreasing in N on both spaces. So
L*_16 ← max(L*_16, L*_8), L*_32 ← max(L*_32, L*_16), U*_16 ← min(U*_16, U*_32),
U*_8 ← min(U*_8, U*_16). Where no build of an N has a bound, L = 0 and
U = dim (trivial), flagged.

**Falsification check, fixed now.** L*_N ≤ U*_N at every N after
interlacing, and L(b) ≤ U(b) on every build. A failure means a bound or a
stored matrix is wrong. It stops the rule: no outcome is assigned, the
failing builds are reported to referee/ and the coordinator.

**Reported, not part of the rule:**

- **Robustness:** n_−(RL + (ε ± δ)I) with δ = 1e−9, so a reader can see
  that no counted eigenvalue sits within δ of −ε (the hardened terms e_Q,
  e_T∞ would have to be wrong by 18 orders of magnitude to move a count).
- **ε_grow(b)** for each N = 32 build at c = 2.9: the exact bracket of
  −λ_{m+1}(RL(b)) with m = L*_16 (by `run_checker_inertia.bracket`), the
  ε below which that build alone would show growth at the last step.
- The count at every c, every build, both spaces; n_0 at both shifts.

## (c) The decision rule, fixed before any ε

Applied at each cell c and on each space. **The outcome of this follow-up is
the one at c = 2.9 on V_4**, C4's own class; the full-space outcome at 2.9 is
reported beside it (s7.9 reported V_4 without judging it; here it is the
count that answers C4, so it is judged). If the two differ, line 2 states
both and names V_4's as the outcome. 2.5 and 2.2 are reported by the same
rule.

In order:

0. **Stop** if the falsification check fails (above).
1. **Outcome 4 (no usable bound)** if no build at N = 32, or no build at
   N = 16, has a finite ε at that cell. The step that did not close is
   named from the folders' null reasons (and A1, if the referee finds a gap).
   A cell with bounds on some builds only is decided on those builds; the
   builds without one are listed.
2. **Outcome 1 (growth below −ε)** if L*_32 > L*_16: the proven lower bound
   rises at the last step. Line 2 states L*_8, L*_16, L*_32 and whether the
   first step (8 to 16) also rises.
3. **Outcome 2 (growth absent, resolved)** if L*_32 = L*_16 and
   U*_32 ≤ L*_16. Then n_−(R_ex(c, 32)) = n_−(R_ex(c, 16)) = L*_16 by
   interlacing: growth from 16 to 32 is excluded, not just unobserved.
4. **Outcome 3 (ε swamps the spectrum)** otherwise: L*_32 = L*_16 < U*_32.
   Growth is neither shown nor excluded at ε; the counts fell because ε is
   large, not because the negatives are gone. U*_32 − L*_32 is reported as
   the undecided count, and ε_grow as the bound that would have been needed.

Why outcome 2 needs U: a count below −ε can only show negatives present.
Their absence needs an upper bound, and the only one available from these
matrices is U. **What the stored matrices already imply** is in s6: outcome
2 is reachable at a cell only if min over N = 32 builds of n_−(RL) is at
most max over N ≤ 16 builds of n_−(RL), since U*_32 ≥ the former and
L*_16 ≤ the latter for every ε ≥ 0.

**Sanity, from checker/ s7.9, without any ε:** if ε ≤ band on the eight s7.9
builds, L ≥ 4, 10, 20 and the rule gives outcome 1; if ε ≥ 2 band on every
build, the N = 32 counts fall to at most 8 (PIN_EXACT x2) while U stays
near the stored n_−, which is outcome 3 unless some other build lifts
L*_32 above L*_16.

**Grade does not decide the outcome.** The numbers decide the outcome; the
grade is stated beside it (s(e)). If a build used in the decision carries
an ε that its folder grades below a proven bound (an assumption the folder
itself marks as measured or open), line 2 says the outcome holds
conditional on that numbered assumption and names it.

## (d) The wording of line 2 (proposed to the coordinator, who writes it)

Braces are filled from `delta_t_bound/delta_t_bound.json`; V_4 counts first,
full space in parentheses.

**Outcome 1.** "**ΔT now carries a proven error bound, and at c = 2.9 the
count below it still grows: n_−(R_S) ≥ {L8}, {L16}, {L32} at N = 8, 16, 32 on
this construction (lower bounds, on C4's class V_4; {F8}, {F16}, {F32} on the
full space).** ε ≥ ‖R_S,exact − R_S,stored‖ is {eps range} at c = 2.9
(delta_t_bound/: bound_trunc/ plus bound_quad/ plus Q, T_∞ and float64
rounding), and the count is exact inertia of the stored matrices shifted
by ε, so by Weyl each counted eigenvalue is a negative eigenvalue of the
Galerkin compression of R_S. C4 fixes no rank bound, so no finite N refutes
bounded rank: this rules out any remainder of rank below {L32} here and is
evidence against bounded rank, not a refutation. At 2.5 and 2.2: {outcome
and counts}. Grade: {grade}."

**Outcome 2.** "**With ΔT's proven error bound (ε = {eps range} at
c = 2.9), the negative index of R_S on C4's class is pinned at {L16} at both
N = 16 and N = 32 (lower and upper bounds agree), so it does not grow from
N = 16 to 32 on this construction. C4 survives this test.** The growth
4, 10, 20 below −band (checker/ s7.9) was band grade and does not survive a
bound. This is consistency with bounded rank at three values of N, not a
proof of C4. At 2.5 and 2.2: {…}. Grade: {grade}."

**Outcome 3.** "**ΔT's error bound closes but does not resolve the count:
at c = 2.9, ε = {eps32} at N = 32 is larger than the depth of the negatives
that carried the growth, so below −ε the count is {L8}, {L16}, {L32} on C4's
class ({F8}, {F16}, {F32} full) and {U32 − L32} eigenvalues at N = 32 are
undecided in [−ε, ε). Not resolved at ε: the counts fall because ε is large,
not because the negatives are gone.** Growth would be shown with ε below
{eps_grow}. The measured count 4, 10, 20 below −band (checker/ s7.9) stands
at its measured grade. At 2.5 and 2.2: {…}. Grade: {grade}."

**Outcome 4.** "**No usable bound on ΔT: {step} does not close
({folder}: {reason}).** The c = 2.9 count stays as checker/ s7.9 states it:
exact on the stored matrices, measured as a statement about R_S, weakest
step ΔT."

## (e) The grade, named now

| step | grade |
|---|---|
| inertia of RL ± εI | exact (two rational routes that must agree) |
| V_4 inertia | ball arithmetic, every pivot excluding 0 (enclosure-carrying) |
| Weyl, Cauchy interlacing, min-max, ‖·‖₂ ≤ ‖·‖_F | standard theorems; applied here by ordinary argument, reviewed by referee/ or unreviewed |
| r_Q, r_T∞, r_sub, r_mirror | exact; r_add given IEEE 754 round to nearest |
| e_Q, e_T∞ | hardened (independent routes), not enclosure-carrying; below 7e−28, and the δ check shows no count moves unless they are wrong by 18 orders |
| eps_trunc, eps_quad | as their folders grade them; the ceiling is enclosure-carrying numerics on a derivation reviewed internally by referee/ (unreviewed externally) |
| the formulas ε bounds against | T_∞ = A + E (kernel/, derivation unreviewed), ΔT (two_adic/ s5, ordinary arguments, unreviewed; CCM Thm 4.6 as published) |

**What ε bounds, and what it does not.** ε bounds the distance from the
stored matrix to the Galerkin compression of the construction's formulas.
Whether those formulas are T_S is a different step, and it is unreviewed
(kernel/ s7, two_adic/ s5). So the statement "n_−(R_S) ≥ k" is about R_S as
this construction defines it. The weakest step of line 2 is the lowest of:
the review status of the two bound derivations and of this composition (A1
to A3), and kernel/'s unreviewed T_∞ derivation. Line 2 names it; if
referee/ has not reviewed a bound derivation when line 2 is proposed, its
grade is "unreviewed derivation", said so.

## (f) Phase 2, in order

1. Read `bound_trunc/` and `bound_quad/` (RESULTS, JSON, assumptions).
2. `assemble.py --routed` writes `delta_t_bound/delta_t_bound.json`.
3. Tests in `delta_t_bound/` pin every number of `delta_t_bound/RESULTS.md`,
   whose first five lines are the brief's five.
4. The outcome by (c); the wording by (d); the grade by (e). Then the
   proposed line 2 to the coordinator.

## s6. The harness on synthetic ε (`synthetic.json`, before any bound)

(Filled in the same commit as this file, from `assemble.py --synthetic`;
pinned by `test_assembler.py`.)

## Addendum A (post-hoc: added after 81f0b47, at the coordinator's request): the mode-free floor

Written 2026-09-24 after the PREREG commit, when the coordinator relayed that
bound_trunc/ (4a0818f) finds no bound on the truncation error and bound_quad/
(ab0f8fa) finds one source that does not close a priori, so every eps_upper
is expected null (outcome 4 by (c), which already handles it). Fixed
**before** any count below is run at N = 32 or at c = 2.5, 2.2. The only
numbers of this kind seen: bound_trunc/'s float64 probe as its DERIVATION
s1.4 prints it (2, 2 negatives at c = 2.9, N = 8, 16; 1 at 2.5; 0 at 2.2).
Nothing in (a) to (f) above changes.

**A.1 Source.** bound_trunc/ DERIVATION s1.4, Lemma 3 (ordinary argument,
unreviewed until referee/ reviews it): with κ = (√2 − 1)⁴ = 17 − 12√2 and
K = κ^{−1} = 17 + 12√2, κT_∞ ≤ T_S ≤ K T_∞ as forms on window functions.
Galerkin compression keeps form inequalities, and A ≤ B gives
λ_k(A) ≤ λ_k(B), so

    n_−(Q − K T_∞) ≥ n_−(R_ex(c, N)) ≥ n_−(Q − κ T_∞)   (compressed to span_N).

No ΔT, no prolate mode count, no stored float64 matrix enters.

**A.2 The count, enclosure-carrying end to end** (`floor_count.py`, written
after this section, in the same commit):

- Inputs: Q_mp = `checker_q.Q_matrix(c, N, 40)` and T∞_mp =
  `kernel/sonin.T_inf_matrix(c, N, 40)`, read-only imports, both mpmath at
  dps 40, every entry an exact binary rational. Their accuracy is the stated
  sizes of (a): Q hardened (checker/ s1, ≤ 5.5e−40 against CCM, pinned at
  4e−39), T_∞ hardened (kernel/ s6, dps 40 against 60 ≤ 5.1e−39;
  derivation unreviewed, kernel/ s7). η_N := (2N+1)(4e−39 + K_hi · 1e−29)
  bounds the input error of Q − cT_∞ for every c ≤ K_hi.
- Route 1, exact. κ_lo := 17 − 12 s and K_hi := 17 + 12 s with
  s = (isqrt(2 · 4^256) + 1)/2^256 ≥ √2, so κ_lo ≤ κ and K_hi ≥ K, rationals.
  T_∞,ex ≥ 0 (a trace of ϑ S_∞ ϑ* with S_∞ a projection, so its compression
  is positive semidefinite), hence Q − κT_∞ ≤ Q − κ_lo T_∞ and
  Q − K T_∞ ≥ Q − K_hi T_∞. With Weyl for η:

      F_N(c) := n_−(Q_mp − κ_lo T∞_mp + η_N I)  ≤ n_−(R_ex(c, N)),
      G_N(c) := n_−(Q_mp − K_hi T∞_mp − η_N I)  ≥ n_−(R_ex(c, N)),

  each by `run_checker_inertia.inertia_both` (both rational routes).
- Route 2, balls, a cross-check with κ and K as arb balls (no rational
  rounding): `inertia_balls` of Q_mp − κT∞_mp ± η at 256 bits; it must agree
  with route 1 wherever it decides.
- V_4: the same two shifts on Z(c)^T(·)Z(c) by ball elimination (256, then
  512 bits), the min-max fallback (F − 3, G) where undecided, labelled.
- Reported, not judged: the exact brackets of every negative eigenvalue of
  Q_mp − κ_lo T∞_mp (`run_checker_inertia.bracket`), and F at η ± δ,
  δ = 1e−9.
- Nine cells: c ∈ {2.2, 2.5, 2.9}, N ∈ {8, 16, 32}. Cost measured first:
  `sonin.T_inf_matrix(2.9, 8, 40)` took 6.3 s on the shared laptop and
  matches the moments route of `KernelProvider` to 4.6e−40; N = 32 is timed
  before the batch. Checkpoint per cell.

**A.3 What the numbers will mean.** F and G are further lower and upper
bounds on the same n_−(R_ex(c, N)) that (b) bounds, valid **conditional on
Lemma 3** (the lower half for F, the upper half for G). They enter the rule
of (c) as

    L_N ← max(L*_N, F_N),   U_N ← min(U*_N, G_N),

then interlacing and the falsification check as in (b), and `decide()` runs
on the result with every N counted as bounded (F and G exist at every N).
The outcome so obtained is reported **separately** from the ΔT-bound
outcome of (c) and labelled "conditional on Lemma 3"; it does not replace
it. Readings, fixed now:

1. **Floor grows** (F_32 > F_16 after interlacing, or L as combined): the
   mode-free lower bound rises with N. Wording: "n_−(R_S) ≥ F_8, F_16, F_32
   at N = 8, 16, 32 on this construction, conditional on Lemma 3 (bound_trunc/,
   {review status}); this rules out any remainder of rank below F_32 and is
   evidence against bounded rank that does not depend on ΔT; not a
   refutation."
2. **Growth excluded** (combined L_32 = L_16 and combined U_32 ≤ L_16):
   growth from 16 to 32 excluded conditional on both halves of Lemma 3.
   Expected unreachable, since K ≈ 34 makes Q − K T_∞ far from
   semidefinite; stated so that the rule has no unassigned branch.
3. **Floor flat, upper bound open** (the rest): "by Lemma 3, n_−(R_S) ≥
   F_32 at c = 2.9 at every N here (a remainder of rank below F_32 is ruled
   out), and the floor does not grow with N. It is one-sided: it cannot
   exclude negatives, so it is not evidence for C4, and it does not resolve
   the 4, 10, 20 count."

Where the ΔT-bound outcome is 4, line 2 carries this reading after the
outcome 4 sentence of (d), in one sentence, with F_8, F_16, F_32 at c = 2.9
on V_4 (full space in parentheses), and the counts at 2.5 and 2.2.

**A.4 Grade.** The count: exact inertia (route 1), ball arithmetic
(route 2, V_4). The inputs: hardened accuracy, with η covering their
stated sizes; the δ check shows no count moves unless they are wrong by
far more than stated. The implication: Lemma 3, an ordinary argument whose
grade is referee/'s review status, and T_∞ ≥ 0 by construction. Composite:
weakest step Lemma 3's review status (and kernel/'s unreviewed T_∞
derivation, which every statement about "T_S" here shares). Named in line 2.
