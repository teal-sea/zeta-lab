# Review of the first coordinated signed-correction candidate

Date: 2026-09-06. Reviewer: a Claude Code session working from the repository, not the
session that produced the candidate. Status: **an independent written and computational
review of an archived candidate.** It re-derives every all-cutoff argument the candidate
relies on, establishes every finite hypothesis by its own exact computation with no code
shared with the candidate or the baseline package, reproduces the candidate's own script
from the repository baseline, and compares the result with the reviewed baseline. It is not
a Lean check, not an external human review, and not a claim of novelty or optimality.
Nothing here is a prime-counting record and nothing here bears on RH: the leading constant
stays above one.

The object under review is `joint_results.json`, produced by `joint_correction.py` against
the baseline in `../certificate_route_test/` (main at `9ec3b6b3`, reviewed in PR #199).
The candidate replaces the baseline's five unit-amplitude greedy stages by one block of
nine rational amplitudes on masked-carry starts q = 17, 18, 19, 23, 24, 25, 29, 31, 32, with
fresh nonnegative repairs on 172 of the baseline's 411 repair cells and tail shield
H = 3 sum_q y_q = 701/36.

## 1. Verdict

**SURVIVES.** Every claimed quantity reproduces, every finite hypothesis holds under
independent exact arithmetic, every written all-cutoff argument carries over from the
reviewed baseline unchanged, and the composite starts are legitimate. No repair is needed.
Section 6 lists what this verdict does not cover.

| Quantity | Recorded | Reproduced here | How |
|---|---|---|---|
| leading constant C_new | 1.04762393137926786058... | exact rational enclosure of width 6.3e-40, both endpoints begin 1.047623931379267860580006972148025253682 | own rational log series; mpmath interval logs agree; 80-digit float agrees |
| strict decrease C_new < C_old | claimed by `refine.py` enclosures | C_old − C_new >= 0.001039732413952767653671588, exact | upper endpoint of C_new below lower endpoint of C_old, both from the own series and from interval logs |
| finite coefficient mass | 56345/108 | 56345/108 over 662 coefficients | exact, from the recorded coefficients and from the rebuild |
| tail coefficient H | 701/36 | 701/36 = 3 · 701/108 | exact sum of the nine amplitudes |
| tail allowance in the budget | H · 15 | 10515/36 = 3505/12 | exact |
| repairs | 172 cells, sum 19471/108 | 172, all inside the baseline's 411 distinct cells, sum 19471/108 | exact |
| lifted prefix minimum on [1, R) | 1 | 1 (scaled 108/108); 292 cells sit exactly at 1 | divisor-increment table of the recorded coefficients |
| negative seed cells below R | 640 | 640, first at t = 275 | same table |
| masked carries q = 13..36 | sup 3 each, 3,390,240 cells | sup 3 each, min −3 each, 3,390,240 cells | full-period enumeration |
| early weights at 18, 19, 20, 21, 24, 25, 32 | 79/54, 245/108, 3, 2, 53/36, 191/108, 137/108 | same; baseline values 2, 2, 3, 2, 2, 2, 2 also re-derived | exact |
| B_N and U_N at 10^4, 10^6, 10^8, 10^12 | both below the baseline | same values to better than 1e-40 relative; B_N <= U_N; both strictly below the baseline | lifted coefficient dictionaries, 80 digits |

Reproduction of the candidate's own script: `joint_correction.py` run unchanged from the
repository root (its baseline import resolves to `../certificate_route_test/refine.py`)
wrote a file **byte-identical** to the archived `joint_results.json`; the copy is
`review/rerun_joint_results.json`. The LP (scipy 1.18.0, HiGHS) returned the same vertex on
this machine. That is a reproduction, not an optimality statement.

## 2. Preservation and hashes

`archive/joint_correction_candidate.zip` is the download, unchanged: 13,746 bytes, SHA-256
`828a4d85d471b51331b5f0a32c30818ccff4de95e9e4c91dbb836536376e8260`, pinned by
`archive/SHA256SUMS` and by `tests/test_joint_correction_candidate.py`. The three members,
extracted beside this file unchanged, hash as follows:

| File | Bytes | SHA-256 |
|---|---:|---|
| `JOINT_CORRECTION.md` | 7,334 | `e573762c46d817f2e6e7693c79cf5f0b7eb459c05b1f3102167b657231d45247` |
| `joint_correction.py` | 9,640 | `92dd9b882f7edba1f8f99e46e3469fc1791e3cc7c2eb5c7b6931809f27ff1eaf` |
| `joint_results.json` | 22,880 | `e951a89fdd8fe4311cc5e0e5a8ad303945f10982844e37669fde3ae48f933e89` |

The package ships no hash manifest of its own; these are the hashes measured at extraction.
None of the three files carries the word this repository reserves for `zeta/rigor.py`.

## 3. What was run

- **Reproduction.** The candidate's script, from the repository root, output redirected to
  scratch, then compared leaf by leaf and byte by byte with the archived record: identical.
- **Independent checker.** `review/joint_check.py`, output `review/joint_check.json`. It
  imports nothing from the candidate and nothing from `refine.py`, and uses no numpy. Seeds
  and lifted weights are evaluated by divisor increments (floor(t/j) counted as the multiples
  of j up to t, then a prefix sum). Logarithms are enclosed two ways: an exact rational
  series of this reviewer's own (2 atanh with a geometric tail bound, n = 2^e r) whose
  soundness is itself checked against mpmath's interval log for every n up to 3000 and four
  larger n, and mpmath's interval context directly. Runs in about 40 s on a laptop.
- Environment: Python 3.14.0, mpmath 1.3.0, numpy 2.5.2, scipy 1.18.0.

## 4. The obligations, one at a time

Notation as in `JOINT_CORRECTION.md` and the baseline notes: g_0 the period-30030 seed,
g_* the period-2310 repair seed (both from the baseline's `inputs.json`), b_n the carry
function, h_q the mask-210 signed carry at start q, y_q >= 0 the amplitudes, lambda_n >= 0
the repairs, D = g_0 − sum_q y_q h_q + sum_n lambda_n b_n the finite seed, and
g = D + H W_*(t/R) with H = 3 sum_q y_q.

**Amplitudes reconstruct exactly.** All nine y_q and all 172 lambda_n are positive
rationals with denominators dividing 108. sum_q y_q = 701/108, so H = 701/36 exactly. The
repair cells are a subset of the baseline's 411 distinct cells (537 stage repairs collapse
to 411 cells; verified) and sum to 19471/108. Rebuilding D from these amplitudes with the
reviewer's own stencil and carry coefficients gives the recorded 662 coefficients exactly.
The floating LP is only the proposer: the reconstructed rationals are what every check
below is run on.

**D is balanced.** sum_j d_j / j = 0 exactly. (g_0 is balanced, each h_q is balanced because
each b_q(t/d) is, and each b_n is; the rebuild confirms the total.) Its mass is 56345/108
against the baseline's 2641/3, and its common denominator is 108.

**Prefix coverage.** From the recorded coefficients, W(t) = sum_k D(t/M^k) >= 1 on every
integer cell 1 <= t < R, with 292 cells exactly at 1. All breakpoints are integers, so the
integer cells decide all real t (baseline review, 3.1). The seed D is negative at 640 of
those cells, first at t = 275; that is the combined-weight relaxation the baseline review
accepted, and the lifted weight covers anyway.

**Tail argument with H = 701/36.** For t >= R: g_0(t) >= 0 (period 30030, every cell
checked), each h_q(t) <= 3 (below), every lambda_n b_n(t) >= 0, and W_*(t/R) >= 1 because
g_* >= 0 with g_* >= 1 on [1, 15) (period 2310, every cell checked). Hence
g(t) >= 0 − 3 sum_q y_q + 0 + H = 0. The argument is linear in the amplitudes, so fractional
y_q change nothing. With R = 100000 >= M = 15 and D = 0 on [0, 1), the baseline review's
argument 3.2 then gives W_g(t) >= 1 for every t >= 1. Sixty-six exact samples of the seed
and of the lifted weight at t between R and 10^12 agree; the proof does not use them.

**Each masked carry really has sup 3.** For every q = 13..36, not only the nine selected,
h_q was enumerated over the full period 210 q (q + 1) (a period because every index
d q, d (q + 1), d q (q + 1) divides it and the sum is balanced): supremum exactly 3 and
infimum exactly −3 in each case, 3,390,240 cells in total. The generic bound 8 (drop the
eight negative terms) is never needed.

**Integrability.** D is bounded by its mass, W_*(t/R) = O(1 + log t), so the integral of
|g| t^−2 is finite and the sum over dilations exchanges with the integral (baseline review,
3.4). The formula C = (kappa(D) + H kappa(g_*)/(R (1 − 1/M)))/(1 − 1/M) follows and is
what both enclosures compute. Dropping the geometric tails in the budget needs
kappa(D) > 0: the exact enclosure gives kappa(D) > 0.97757. The candidate's script does not
assert this; it holds.

**Factorial identity and full budget.** The identity B_N = sum_{d <= N} Lambda(d) W_g(N/d)
is unchanged; the lifted coefficient of index R j M^m is now H (m + 1) a*_j with H
rational, which is the same counting. Checked at every prime up to 2000 and up to 10000
(1532 exact identities, each demanding W_g >= 1 at the arguments it touches) and directly:
B_N at 80 digits against an exact Chebyshev psi(N) at fourteen cutoffs between 10^3 and
10^6, B_N >= psi(N) at all of them. The per-level inequality
|sum_j a_j log(floor(x/j)!) − kappa x| <= A (1 + log^+ x) holds for any balanced seed with
no sign condition (baseline review, 3.5), so

    psi(N) <= B_N <= C_new N + (56345/108) S1(N) + (10515/36) S2(N),

with S1 and S2 as in `REFINEMENT.md`. The tail allowance rises from 225 to 10515/36
(about 292.1) because H rose from 15 to 701/36; the finite allowance falls from 2641/3 to
56345/108. The four recorded comparison rows were recomputed from lifted coefficient
dictionaries: they agree with the record to better than 1e-40 relative, B_N <= U_N holds,
and both B_N and U_N are strictly below the baseline's at all four N.

**The rational log enclosures really prove C_new < C_old.** Three routes agree. The
reviewer's exact rational series gives C_new in an interval of width 6.3e-40 and C_old in
one of width 7.5e-43, with the upper endpoint of the first below the lower endpoint of the
second by at least 0.001039732413952767653671588. mpmath's interval logs give the same
separation (and, as in PR #199, enclose C_old to width 1.1e-58). The candidate's own `refine.py` enclosure is a
fourth route with the same conclusion; its published outward-rounded interval for C_new is
consistent with the exact one. The decrease is a rigorous rational inequality, not a
floating comparison.

**B_N and U_N recomputed.** Table in section 1; values in `review/joint_check.json`.

## 5. Composite starts q = 18, 24, 25, 32

The certificate's validity uses only these facts about a start q: h_q is a balanced floor
sum, it vanishes before q, and it is bounded above by an enumerated supremum over a full
period. Each holds for any integer q >= 2: b_q is floor(u + v) − floor(u) − floor(v) with
1/q = 1/(q + 1) + 1/(q (q + 1)), so it takes only the values 0 and 1 (checked over a full
period for every q = 13..36); the Moebius sum over d | 210 preserves balance and the
starting index; and the period 210 q (q + 1) is a period regardless of whether q shares a
factor with 210. Nothing in the coverage, tail, integrability, identity or budget argument
mentions primality.

Where primality did enter the earlier notes: the omitted-prime lemma in
`STRUCTURAL_STEP.md` (the jump W(p) − W(p − 1) = a_1 needs p to have no divisor among the
coefficient indices other than 1), and the fixed-recipe ceiling in `ROUTE_ASSESSMENT.md`
(its enumeration of future gross gains sums over primes above 31). Both are statements
about the *size* of the excess in a restricted family, not obligations of the certificate.
The word "prime" in the baseline's description of h_p as discounting "copies at multiples
of the four already-present small primes" is motivation, not a hypothesis. So the
composite-q corrections are legitimate: they are ordinary balanced signed corrections whose
finite hypotheses were checked exactly like the prime ones.

## 6. Stated limitations, checked

- **Repairs restricted to the baseline's 411 cells.** True of the record: the 172 repair
  cells are a subset of the 411 distinct cells of the baseline's 537 stage repairs, and the
  script builds its repair columns from exactly those cells.
- **Starts restricted to q = 13..36.** True of the record: `candidate_range` is 13..36 and
  every selected start lies in it; 15 of the 24 candidates received amplitude zero.
- **The LP proposes the vertex; no exact optimality.** Correct as stated. The reviewer
  reproduced the same vertex but did not certify dual feasibility or optimality in exact
  arithmetic, and the candidate claims none. Any other feasible point of the same prefix
  problem would be admissible on the same terms.
- **No asymptotic rate.** Correct. One block of nine amplitudes on one window lowers C by
  about 0.00104 and the finite mass by about 40.7 percent while raising the tail coefficient
  from 15 to about 19.47. No rule for growing the window is proved or claimed.

## 7. Observations that are not failures

- The candidate's script does not check kappa(D) > 0, which the budget's tail-dropping
  needs; it holds with margin (kappa(D) > 0.97757), and the checker asserts it.
- The recorded `new_C_interval` is outward-rounded to a 1e-16 grid for display; the
  separation was asserted on the unrounded rational endpoints inside the script, and the
  reviewer's exact endpoints lie inside the displayed interval.
- 292 prefix cells sit exactly at lifted weight 1 (the baseline review did not count these).
  That is the LP pressing the constraint, as expected of a vertex.
- The early overcount is reduced at 18, 24, 25, 32 and unchanged at 20, 21; it is not
  removed. The note says so.

## 8. What this review does not establish

No optimality, no rate, no novelty search, no Lean check, nothing about the total CHHL
error E(N) or about RH. The finite checks are exact integer and rational arithmetic and
interval enclosures by two independent routes (hardened, in the laboratory's vocabulary);
the all-cutoff arguments are elementary and were walked by one reviewer.
External verification is pending.

## 9. Reproduce

From the repository root, with the laboratory's virtual environment:

    cd hunts/prime_pair_error/frontier/2026-09-06/joint_correction_candidate/review
    OPENBLAS_NUM_THREADS=1 ../../../../../../.venv/bin/python joint_check.py

writes `joint_check.json` beside itself and exits non-zero on any failed check. To rerun
the candidate's own script:

    OPENBLAS_NUM_THREADS=1 .venv/bin/python hunts/prime_pair_error/frontier/2026-09-06/joint_correction_candidate/joint_correction.py --output /tmp/rerun.json

from the repository root (it resolves the baseline from the working directory); pass an
output path so the archived `joint_results.json` is not overwritten.
`tests/test_joint_correction_candidate.py` pins the archive hash, the unchanged members,
and the numbers in section 1 on every run.

## 10. Boundary

This review checks the candidate as recorded. It does not extend the q-window, add
corrections, run another objective, switch criteria, or reopen the A/B record.
