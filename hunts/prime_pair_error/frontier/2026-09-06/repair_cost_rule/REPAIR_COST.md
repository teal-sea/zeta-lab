# A repair-potential bound and direct final-weight corrections

Date: 2026-09-06, local conversation date. A continuation of the saved joint-support analysis.

**Status.** This note gives elementary arguments, an executed construction, and a separate-code self-check by the originating session. It is not independently refereed, not an optimality or novelty claim, not a modern prime-counting improvement, not an asymptotic refinement-rate theorem, and not an upper bound improving the completed total CHHL error. No repository file, branch, or PR was changed in this pass.

## 1. What the pass actually accomplishes

The preceding `joint_support_analysis.zip` found that a frozen repair dictionary prohibited the correction at 20. Allowing new repair sites made that correction feasible, but gave no general estimate for the repairs' cost.

This pass does two things.

1. It bounds the entire greedy repair bill by a quantity computed from the **initial deficits**, before the greedy repairs are constructed. The inequality holds for any correction satisfying the stated hypotheses, not only the two numerical examples.
2. It applies the correction directly to the final majorant, instead of inserting it into a seed and repeating it at all powers of 15. The revised final-majorant argument has its own tail proof and factorial error accounting. This is a deliberate enlargement of the old representation, not an omitted rescaling.

Two steps, at 20 and 21, pass the sufficient test and lower the leading coefficient from 1.04762393137926786... to 1.04590351044777010.... A further step at 20 fails the sufficient test. It was evaluated as a negative-control diagnostic and the particular greedy construction actually increases the coefficient; it is not retained.

The result is **a general one-step sufficient improvement test**, not a guarantee that sufficiently good steps continue to exist. Proving a useful uniform relationship between the residual excess, initial deficits, and coefficient growth remains open in this calculation.

## 2. Inputs and provenance

The unchanged joint candidate in PR #200 was reviewed against its baseline and reported to survive. Its review is at commit `85a42e7c0c7dad8163dcab8d239bac5bb6fe1b38` in `teal-sea/zeta-lab`, under

`hunts/prime_pair_error/frontier/2026-09-06/joint_correction_candidate/JOINT_REVIEW.md`.

That review is an input, not a review of this new construction. The current pass does not reopen or merge PR #200.

The working inputs here are copied from the attached `joint_support_analysis.zip`:

- `inputs/joint_results.json`: the joint candidate's original rational coefficients and measurements;
- `inputs/seeds.json`: the original period-30030 seed and period-2310 repair seed;
- `inputs/joint_support_analysis.zip`: the entire preceding source package, unchanged, including its source archives and code.

The last ZIP is 129,164 bytes and has SHA-256

`50692a8fce2d29b3f81cb2d7c06fa1d9ae9b1402f10e45aff331d0155144864e`.

All inputs are hashed by the producer and checked again by the separate checker. No original input is rewritten. Exact per-file hashes of this pass are in `SHA256SUMS.json`.

Write M=15, R=100000, a=1-1/M=14/15. Let D be the joint candidate's finite balanced floor sum, and let g_* be the fixed repair seed. Define

    V(t) = sum_{k>=0} g_*(t/M^k),
    W_0(t) = sum_{k>=0} D(t/M^k)
             + H_0 sum_{m>=0} (m+1) g_*(t/(R M^m)),
    H_0 = 701/36.

All sums are locally finite. The reviewed input establishes W_0(t)>=1 and V(t)>=1 for t>=1, and both vanish before 1. It has

    A_D = sum |d_j| = 56345/108,
    A_* = sum |a*_j| = 15,
    C_* = integral_1^infinity V(t) dt/t^2,
    C_0 = integral_1^infinity W_0(t) dt/t^2
        = 1.047623931379267860580006972148025253682... .

The factor (m+1) is the earlier *double* rescaling of the tail seed. It remains in the baseline and is never silently removed.

## 3. General direct-weight repair lemma

### Hypotheses

Let W be any majorant with W(t)>=1 for t>=1. Assume W is constant on integer cells, vanishes for 0<=t<1, and is absolutely integrable against dt/t^2. Let V have the same properties. Let h be a finite balanced floor sum with positive integer denominator indices, zero before 1, and bounded above by H>=0 on the whole half-line. Let R>=2 be an integer.

For each integer 1<=n<R define the raw deficit

    d_n = max(0, 1 - W(n) + h(n)).

These are the deficits of W-h **before adding any new repair**.

Define the carry

    b_n(t) = floor(t/n) - floor(t/(n+1)) - floor(t/[n(n+1)]).

Because 1/n = 1/(n+1) + 1/[n(n+1)], this is floor(u+v)-floor(u)-floor(v). It is 0 or 1, zero for t<n, and exactly 1 at t=n. In particular, a positive carry repair cannot create a new deficit anywhere.

Process n=1,...,R-1 in increasing order and put

    lambda_n = max(0, 1-W(n)+h(n)-sum_{m<n} lambda_m b_m(n)).

Let

    P(t) = sum_{n<R} lambda_n b_n(t),
    W_new(t) = W(t) - h(t) + P(t) + H V(t/R).

### Coverage conclusion

For each processed cell, its repair lifts that cell to at least 1. Later repairs cannot damage it, because every b_n is nonnegative and zero before its start. All breakpoints are integers, so the integer-cell check covers every real t<R. The tail term vanishes on that prefix.

For t>=R,

    W_new(t) >= 1 - H + 0 + H = 1.

Thus W_new is a global majorant. This proof uses the **old final weight W>=1**, not a requirement that a newly defined seed be nonnegative above R. It is valid with composite carry indices and rational amplitudes. It is not the old seed-tail argument with a missing factor.

### Repair-cost conclusion

Since all earlier repairs in the recursion are nonnegative,

    0 <= lambda_n <= d_n.                                      (R1)

Define

    k_n = integral_1^infinity b_n(t) dt/t^2
        = log(n+1)/n - log(n)/(n+1) > 0,
    Phi_R(W,h) = sum_{n=1}^{R-1} d_n k_n.

The integral formula follows from the balanced floor-sum identity, or by integrating the three floors to a finite endpoint and cancelling their linear divergences. Equation (R1) now gives the a priori bound

    integral P(t) dt/t^2 = sum_n lambda_n k_n <= Phi_R(W,h).    (R2)

The word 'a priori' here means before constructing the repairs. Evaluating Phi still requires knowing W and h on the finite prefix; it is not a closed-form estimate independent of the input construction.

Changing variables in the shield integral gives

    integral H V(t/R) dt/t^2 = H C_*/R.

Absolute integrability of the old functions, bounded finite h and P, and the scaled V justifies every integral and addition. Consequently

    C_new = C_old - kappa(h) + sum lambda_n k_n + H C_*/R,
    C_old - C_new >= G_R(W,h),
    G_R(W,h) := kappa(h) - Phi_R(W,h) - H C_*/R.                (R3)

**If G_R(W,h)>0, this algorithm necessarily lowers the leading constant.** This is a sufficient condition, not a necessary one. Failure of the test is not a proof that no alternative repair could improve the constant.

The combined coefficient mass of the finite update F=-h+P also satisfies

    ||F||_1 <= ||h||_1 + 3 sum_n d_n,                         (R4)

because each carry has coefficient mass 3 (merging coincident denominator indices can only reduce it). This is a bound on construction cost, separate from the weighted-integral saving.

### A coarser geometric version

An exact identity is

    n(n+1) k_n = (n+1) log(n+1) - n log n
              = integral_n^{n+1} (1+log x) dx.

Therefore, for n<R,

    k_n <= (1+log R)/[n(n+1)],
    Phi_R(W,h) <= (1+log R) sum_{n<R} d_n/[n(n+1)].             (R5)

This quantifies an at-most-logarithmic amplification of raw deficit area in this simple repair rule. The location-dependent sum Phi is substantially tighter. In fact the coarser right side in (R5) is too large to prove either of the positive examples below; the exact weighted potential does prove them. No favorable deficit-distribution estimate is silently assumed.

## 4. Why the correction is applied at the final weight

The old local update inserted -h into a seed g, so its effect on the final weight was

    -h(t)-h(t/15)-h(t/15^2)-... .

That was a valid construction, but it imposed additional scale copies of every correction and repair. The new update acts as -h(t) on the final weight, with direct carries P(t). The periodicity within h itself remains; only the additional radix-15 repetitions are removed.

Equivalently, a finite final-weight update F can be inserted into a seed as

    delta g(t) = F(t)-F(t/15),

since its locally finite lifted sum telescopes to F(t). This identity explains the relation to the earlier representation. We do not demand seed nonnegativity for this update; the direct final-weight proof in Section 3 is the replacement invariant.

There is no RH assumption or change to the factorial-majorant criterion. The construction remains a pointwise upper certificate for the actual von Mangoldt weighted count.

## 5. Executed two-step construction and a rejected control

Use the existing masked carries

    h_q(t) = sum_{d|210} mu(d) b_q(t/d).

They are balanced finite floor sums with period 210q(q+1). For q=20,21 the exact full-period supremum is 3 and infimum is -3. This is verified, not inferred from sampling.

Starting from W_0, the first correction is h_20. Its raw deficits have 279 nonzero cells. The second is h_21, evaluated against the **updated** weight; its raw deficits have 303 nonzero cells. Each step adds 3V(t/R) for its tail protection.

| Step | Gross kappa(h) | Raw repair potential Phi | Tail cost | Guaranteed saving G | Actual saving |
|---|---:|---:|---:|---:|---:|
| 20 | .002187932365231 | .001277463464077 | .000032095633577 | .000878373267577 | .000974459299804 |
| 21, after 20 | .002012597541962 | .001321626866464 | .000032095633577 | .000658875041921 | .000745961631694 |
| another 20, after both | .002187932365231 | .002513391362117 | .000032095633577 | -.000357554630463 | -.000116078916486 |

All signs in the last two columns were checked with exact rational logarithm enclosures and independently with interval logarithms. The third candidate is rejected by the sufficient policy. It was nevertheless constructed once as a diagnostic; this particular greedy completion increases C, so it was not retained. This is not an impossibility assertion about every repair for that third candidate.

| State | C | New repairs at that step | W(20) | W(21) |
|---|---:|---:|---:|---:|
| Reviewed joint input | 1.04762393137926786058... | -- | 3 | 2 |
| After direct h_20 | 1.04664947207946403908... | 127 | 2 | 2 |
| After direct h_21 | 1.04590351044777009790... | 187 | 2 | 1 |

Every initial deficit, every resulting repair, and the complete rational coefficient vector is recorded in `results.json`. All repairs are allowed to appear where required; no inherited support restriction is used.

The resulting representation is

    W_new(t) = W_0(t) + F(t) + 6 V(t/R),

where F is a finite balanced floor sum. It has

    ||F||_1 = 19237/54,
    ||D+F||_1 = 91127/108,
    ||D||_1 = 56345/108.

The new repair shield 6V is a **single** lift. It is separate from the old H_0 double-lift shield. Adding 6 to H_0 inside the old (m+1)-weighted expression would describe the wrong certificate.

### Selection history

This is exploratory, not preregistered. Before fixing the recorded sequence 20,21,20, this pass compared the seed-level and final-weight q=20 constructions; tried direct amplitudes 1 and 2 at 20; tried standalone 21 and amplitude 1/3 at 18; and tested a dyadic-block upper cover of raw deficits. The dyadic covers did not beat the greedy repair cost in those checks and were not used. The chosen positive steps address the previously identified early cells 20 and 21. These finite explorations do not establish optimality or explain a uniform best sequence.

## 6. Full factorial budget, including all new costs

For a finite balanced floor sum f(t)=sum c_j floor(t/j), write

    L_f(x) = sum_j c_j log(floor(x/j)!),
    kappa(f) = -sum_j c_j log(j)/j,
    A_f = sum_j |c_j|.

The classical divisor identity gives

    L_f(N) = sum_{d<=N} Lambda(d) f(N/d).

This identity applies to signed rational coefficients. As in the reviewed pilot,

    |L_f(x)-kappa(f)x| <= A_f(1+log^+ x),

with no sign assumption on f. It follows by applying the elementary factorial/integral error to each term and using balance. These are the existing inputs, not new prime-distribution assumptions.

For the new weight,

    B_new(N) = B_0(N) + L_F(N) + 6 B_*(N/R) >= psi(N),

where B_* is the factorial certificate of V. The statement is at the original sharp integer cutoff; no smoothing or restriction of prime pairs is involved.

Let

    S1(N) = sum_{k:15^k<=N} [1+log(N/15^k)],
    S1_R(N) = sum_{k:R*15^k<=N} [1+log(N/(R*15^k))],
    S2(N) = sum_{m:R*15^m<=N} (m+1)[1+log(N/(R*15^m))].

An empty sum is zero. By merging F with the baseline's level-zero coefficients D, the complete sufficient bound is

    psi(N) <= B_new(N) <= U_new(N),

    U_new(N) = C_new N
        + (91127/108)(1+log N)
        + (56345/108)[S1(N)-(1+log N)]
        + (3505/12) S2(N)
        + 90 S1_R(N).                                      (B1)

The higher baseline levels retain their original mass, not the larger new level-zero mass. The coefficient 3505/12 is the old shield allowance H_0 A_*. The last term is the additional single-lift shield allowance 6 A_*.

To derive (B1), keep the first-level main term kappa(D+F)N exactly and sum kappa(D)N/15^k for k>=1. The unused geometric tail of kappa(D)>0 is dropped in the favorable direction. The double-lift and single-lift shield tails have positive coefficients and kappa(g_*)>0, so their omitted geometric tails also have the correct sign. The checker explicitly verifies both positivity facts. No sign of kappa(F) is assumed.

The corresponding reviewed envelope is

    U_0(N)=C_0 N+(56345/108)S1(N)+(3505/12)S2(N).

Thus its comparison with (B1) is particularly transparent:

    U_0(N)-U_new(N) = (C_0-C_new)N
                      - (5797/18)(1+log N) - 90 S1_R(N).    (B2)

A finite direct correction incurs an additional first-level logarithmic error, not a copy of that error at every radix level. The shield still has its explicit higher-scale cost.

### Proved eventual improvement of the displayed envelope

This is stronger than checking four sample N, but still a statement about this fixed certificate, not an RH-level bound.

Let gamma=C_0-C_new. The rational enclosures prove gamma>1/600. For N>=10^7, set ell=log(N/R), a0=log15, and

    Q(N)=(5797/18)(1+log N)+90(1+ell/a0)(1+ell).

The number of terms in S1_R is at most 1+ell/a0 and each is at most 1+ell, so the subtracted cost in (B2) is at most Q(N). Direct differentiation gives

    Q(N)-N Q'(N)=(5797/18)log N
                    +90[ell+(ell^2-ell-1)/a0] > 0

for ell>=2. Hence Q(N)/N decreases for all N>=10^7. At N0=10^7, using log10<7/3, log15>2, and ell=log100>2, all checked by enclosures,

    Q(N0) < (5797/18)(52/3)+90(10/3)(17/3)
          =196622/27 < N0/600.

The last rational gap is 253378/27>0. Therefore

    U_new(N) < U_0(N) for every integer N>=10^7.              (B3)

For smaller N, both remain valid; min(U_0,U_new) is a safe envelope that cannot worsen the old one. Taking a minimum of valid upper bounds needs no prime computation.

### Finite values, with the unfavorable comparisons retained

The separate checker enclosed factorial values via interval log-gamma on a combined coefficient dictionary. It confirms each displayed comparison's sign.

| N | B_0-B_new | U_0-U_new |
|---|---:|---:|
| 10^4 | 32.7370213 | -3271.0926316 |
| 10^6 | 1803.5519304 | -3348.2292105 |
| 10^8 | 172324.5738792 | 164383.6346525 |
| 10^12 | 1720421425.4526672 | 1720406122.8144710 |

The actual factorial values improve in these four cases. The conservative error envelope worsens in the first two; this is not hidden by quoting only C. The minimum-envelope option retains the better old bound there.

## 7. What remains to reach the original ambition

For a sequence of admissible corrections h_i against successive majorants W_i, (R3) gives

    C_r <= C_0 - sum_{i<r} G_R(W_i,h_i),

whenever the chosen G values are positive, and (R4) bounds cumulative finite coefficient growth by

    ||F_total||_1 <= sum_i ||h_i||_1 + 3 sum_i sum_n d_{i,n}.

These inequalities are uniform in the number of steps, but their right-hand sides still depend on the actual correction and deficit sequence. A positive G for two examples does not prove that G stays positive, that the available savings exhaust C_0-1, or that the coefficient cost stays manageable. In particular, a monotonically decreasing C bounded below by 1 need not converge to 1.

The next missing arithmetic estimate is now explicit: construct admissible corrections whose **initial deficit potential and unweighted deficit mass** are controlled relative to the remaining excess, with all tail allowances included, and prove that useful steps persist as the construction grows. The crude logarithmic estimate (R5) alone does not supply it.

The final leading constant here is still greater than 1. The completed total CHHL E(N) bound is unchanged. The new proof is a repair-cost lemma and a finite application inside the certificate branch, not a result about E(N). No Nyman-Beurling switch, larger prime survey, or external-agent task was launched.

## 8. Checks and reproducibility

`repair_cost.py` uses exact integer prefix arrays, rational coefficient arithmetic, and rational logarithm enclosures. It has no dependency on the old proposer or its helper module and uses no LP.

`check_independent.py` imports neither that script nor the upstream helpers. It uses Python divisor-increment tables, an event-based greedy reconstruction, mpmath interval logarithms, and a combined factorial coefficient dictionary as separate code paths. It is still a self-check from this originating session, not a fresh agent's mathematical review.

The executed separate checker reports:

- 299,997 full-prefix cells across the two positive cases and the rejected diagnostic;
- 273,420 correction-period cells, plus the initial and repair seed periods;
- 120 unrelated finite-array tests of the raw-deficit repair lemma;
- 1,422 exact prime-exponent checks of the factorial identity;
- 66 additional large-weight samples, supplementary to the tail proof;
- interval signs for four complete B/U comparisons;
- exact rational witnesses for the all-N>=10^7 envelope comparison;
- byte hashes of every supplied input.

Run in a scratch copy, not by overwriting this record:

    python -m pip install -r requirements.txt
    OPENBLAS_NUM_THREADS=1 python repair_cost.py --output rerun_results.json
    OPENBLAS_NUM_THREADS=1 python check_independent.py \
        --results rerun_results.json --output rerun_checks.json

Only timing fields should vary. The file paths resolve relative to the script, so the current working directory need not be the Zeta Lab root. These are all local computations. No whole-repository suite, Lean build, independent proof review, or optimality computation was run.

## 9. Sources and priority boundary

The divisor identity and the floor/factorial framework are established mathematics:

- NIST DLMF, 27.5.5: https://dlmf.nist.gov/27.5
- Jonathan Bober, *Factorial Ratios, Hypergeometric Series, and a Family of Step Functions*, introduction and Section 3: https://arxiv.org/html/0709.1977
- Reviewed baseline, fixed commit: https://github.com/teal-sea/zeta-lab/blob/85a42e7c0c7dad8163dcab8d239bac5bb6fe1b38/hunts/prime_pair_error/frontier/2026-09-06/joint_correction_candidate/JOINT_REVIEW.md

The present repair inequality is an elementary deduction from positivity. No literature sweep establishing its novelty was performed. Its value here is to replace an unquantified repair bill by an explicit sufficient bound, and to expose which estimate is still missing.
