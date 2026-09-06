# Fixed-recipe ceiling and aggregate-only repair

Date: 2026-09-06. Prepared in this conversation.

**Status:** self-contained mathematical deductions and one executed comparison, not independently refereed, not a literature-priority claim, not a prime-counting record, and not an improved bound on the full CHHL error. This continues the factorial-certificate experiment; it does not assume that its success implies an RH proof. Nothing was pushed to GitHub or launched on a desktop.

## 1. Provenance and the scope of this test

The input is the uploaded `certificate_refinement_rule.zip`. Its `refine.py`, `inputs.json`, and original `results.json` are copied here, with the original results renamed `original_results.json`. The archived rule fixes M=15, mask P=210, and R=100000. It starts from the period-30030 seed, then subtracts h_p for p=17,19,23,29,31, repairs any seed-level negative values with nonnegative carry functions, and adds a positive tail shield. The original final constant is enclosed between 1.0500311981418248 and 1.0500311981418250; its finite coefficient mass is 4676/3 and its tail coefficient is 15.

This test derives a limitation of continuing that **particular** new-prime rule. It then changes which positivity condition is imposed, not the perturbation list or numerical objective.

## 2. The remaining gross-saving budget of the fixed rule is finite

Write

    b_n(t) = floor(t/n)-floor(t/(n+1))-floor(t/[n(n+1)]),
    k_n = int_1^infinity b_n(t) dt/t^2
        = log(n+1)/n-log(n)/(n+1).

The previous note's fixed perturbation is

    h_p(t) = sum_{d|210} mu(d) b_p(t/d).

Dilation in the integral and the finite Euler product give

    kappa(h_p) = (8/35) k_p.

After dividing by 1-1/15, the greatest possible reduction in the leading constant from one use of h_p is therefore

    gross_gain(p) = (12/49) k_p.

Every repair and every tail shield in the recorded rule is nonnegative and has a nonnegative weighted integral. Consequently repairs can only reduce the actual gain relative to this gross gain.

Suppose every future prime p>31 is used at most once, M and the mask remain fixed, and all repair charges remain nonnegative. Then for every finite continuation S,

    C_S >= C_current - (12/49) sum_{p in S} k_p.       (CAP)

To bound all possible future gross gains without a prime number theorem, observe

    k_n = log(1+1/n)/n + log(n)/(n(n+1))
        <= (1+log n)/n^2 = f(n).

The function f decreases for n>=1. Every p>31 is odd and at least 33. Hence

    sum_{p>31} k_p <= sum_{j>=0} f(33+2j)
                    <= (1/2) int_31^infinity f(x) dx
                    = (log 31+2)/62
                    < 11/124.

The last strict inequality uses log31 < log32 = 5log2 < 7/2. For example log2<7/10 follows directly from the positive series

    log2 = 2 sum_{k>=0} (1/3)^(2k+1)/(2k+1),

bounding the part after the first term by a geometric series: log2 <= 2/3+1/36=25/36<7/10.

Therefore

    sum of ALL future gross gains < (12/49)(11/124) = 33/1519.

The original five-stage C is greater than 21/20. Thus any continuation of that fixed recipe satisfies

    C_S > 21/20 - 33/1519 = 31239/30380 > 1.028.    (OLD-FLOOR)

This is an optimistic bound that pretends future repairs are free and even allows every odd integer instead of just primes. It rules out C tending to 1 under this restricted continuation. It does not rule out new perturbations, changed amplitudes, revisiting earlier indices, changing the mask/rescaling, signed net repair charges, or alternative factorial certificates.

It also does not rule out an alternative analysis of a varying family that retains cancellations in its factorial remainder. The blocked sufficient budget is the recorded one, C*N plus nonnegative complexity allowances.

### Another exact view: early excess is frozen

For the recorded final seed, the lifted weight W(t) on 1<=t<37 exceeds 1 at these integer cells:

    t :       18 19 20 21 24 25 32
    W(t) :     2  2  3  2  2  2  2

Its weighted excess in this prefix is exactly

    sum_{t=1}^{36}(W(t)-1)/(t(t+1)) = 23977/1441440.

Later h_p with p>=37 vanish before 37. The greedy repairs they trigger and the tail shields do not subtract there. Thus marching only to larger prime indices cannot erase this already-present prefix excess. This provides an independent, weaker floor C>=1+23977/1441440 for that continuation. It suggests revisiting overcovered cells rather than only adding higher prime indices.

## 3. A sufficient condition weaker than seed nonnegativity

For a step function g with integer breakpoints and g=0 on [0,1), let

    W_g(t) = sum_{k>=0} g(t/M^k).

The sum is locally finite. Choose an integer R>=M. It suffices to establish

    W_g(t)>=1 for 1<=t<R,
    g(t)>=0 for t>=R.                                  (WEAK)

Unlike the earlier rule, (WEAK) permits g to be negative on [M,R).

**Proof.** For t>=R, repeatedly use W_g(t)=g(t)+W_g(t/M) until the argument enters [R/M,R). All seed terms removed in the process have arguments at least R and are nonnegative. The terminal argument is at least 1 and its lifted weight is at least one by the first condition. Therefore W_g(t)>=1 for every t>=1.

All real prefix values are checked by their integer cells. This is not a weaker requirement on the final factorial certificate: its final weight still majorizes one everywhere.

## 4. Modified repair algorithm

Start from the same period-30030 seed and subtract exactly the same five h_p in the same order, with the same M, R, mask, and H_p=3.

At each stage, form the lifted prefix W_(g-h_p), rather than only the seed prefix. At the first n<R with W(n)<1, add

    lambda_n b_n(t) to g(t), where lambda_n=1-W(n)>0.

On the lifted weight the addition is

    lambda_n sum_{k>=0} b_n(t/M^k).

It is nonnegative everywhere, vanishes before n, and equals lambda_n at n. Thus this greedy procedure corrects the current cell without damaging any earlier one.

Finally add H_p W_*(t/R) to the seed, where the fixed W_*>=1 for arguments >=1 and is zero before 1. The added term vanishes for t<R. For t>=R the previous seed is nonnegative, -h_p>=-H_p, the finite patches are nonnegative, and the tail shield is at least H_p. Hence the second condition in (WEAK) holds. Induction establishes global validity after every stage.

### Integrability and leading constant

Seeds now need not be globally nonnegative, so do not use Tonelli on a signed seed without justification. Each resulting seed is a bounded balanced floor sum plus a fixed multiple of W_*(t/R)=O(1+log t). Therefore int_1^infinity |g(t)|t^-2 dt is finite. Absolute integrability justifies exchanging the sum of dilations with the integral, giving

    int_1^infinity W_g(t)t^-2 dt = kappa(g)/(1-1/M)=C.

The final W_g is nonnegative and at least one. The same factorial identity gives B_N=sum_{d<=N} Lambda(d)W_g(N/d)>=psi(N).

## 5. Executed comparison

`aggregate_repair.py` executed in about 4.6 seconds; see aggregate_results.json for actual elapsed time and complete coefficients.

| stage | repairs at this stage | new C | finite coefficient mass |
|---|---:|---:|---:|
| p=17 | 78 | 1.0541074689353 | 524/3 |
| p=19 | 172 | 1.0521483374280 | 1301/3 |
| p=23 | 156 | 1.0508625152088 | 1945/3 |
| p=29 | 33 | 1.0496802434288 | 2176/3 |
| p=31 | 98 | 1.0486636637932 | 2641/3 |

The earlier procedure made 1182 finite repairs; this one makes 537. Its finite mass is 880 1/3 instead of 1558 2/3, a reduction of about 43.5%. The accumulated tail coefficient remains 15, and its repair seed has mass 15.

There are 705 integer cells below R where the final seed g is negative. Every lifted prefix value W_g(n), 1<=n<R, is nonetheless at least one. This is the exact relaxation being tested, not a positivity tolerance.

Every stage's constant decrease passed the existing rational logarithm enclosure check. Full prefix weights were independently rebuilt from combined rational floor coefficients with integer arithmetic. All 651000 perturbation-period cells were checked to establish H_p=3, all 500000 lifted prefix cells were checked, and 1411 prime-exponent factorial identities plus 69 large-argument checks passed.

### Full sufficient error budget

Write g_final(t)=D(t)+15 W_*(t/R), with D balanced and finite. The rational enclosure check gives kappa(D)>0. Consequently the same favorable geometric-tail truncations used in the previous note apply. The bound is

    psi(N) <= B_new(N)
            <= C_new*N + (2641/3) S1(N) + 225 S2(N),

with exactly the S1 and S2 defined in REFINEMENT.md. In particular, the error allowances remain O(log^2 N) and O(log^3 N) for this fixed construction.

The script also evaluated the actual factorial certificates and these envelopes at N=10^4,10^6,10^8,10^12 at 60 digits. Both were lower than their previous counterparts in all four comparisons. These factorial evaluations are diagnostics, not directed-rounding interval claims.

This is an improvement to this experimental certificate family, not to the known state of prime-counting bounds. No claim about optimality or a uniform refinement rate follows.

## 6. The mutation is useful, but the fixed perturbation menu still has a ceiling

The new C is greater than 131/125=1.048. Applying the same gross-gain cap gives

    C_future > 131/125 - 33/1519 > 1.026

for once-per-new-prime continuation with the same mask and nonnegative charges. Thus changing the positivity invariant removes an artificial expense, but does not turn the old perturbation menu into a route to C->1.

The next certificate experiment should allow **coupled signed corrections revisiting earlier overcovered cells**, preserve only the final covering inequality plus a provable tail invariant, and derive an improvement-versus-complexity estimate for a family. Repeating this computation at the next five primes is not that experiment.

## 7. A genuinely different but mathematically adjacent criterion

Bober Section 1.1 describes the Nyman--Beurling / Baez-Duarte formulation using the same balanced floor sums. With

    q_n(t)=floor(t)/n-floor(t/n), n>=2,

one may ask for finite real combinations f_K=sum_{n=2}^K c_n q_n such that

    int_1^infinity |1-f_K(t)|^2 dt/t^2 -> 0.

RH is equivalent to existence of such an approximating sequence. These approximants are NOT required to be pointwise upper bounds, so all-point positive repair is not required. This is a known criterion, not a new insight or a theorem saying an arbitrary coefficient family converges. Its proof-level missing requirement is convergence with controlled infinite tails. Switching to it would be an explicitly different route to RH, not an improved CHHL bound or an improved factorial majorant.

Primary sources checked:
- Jonathan Bober, arXiv:0709.1977, Section 1.1, Theorem 1.3 and following equivalent step-function formulation: https://arxiv.org/html/0709.1977
- Luis Baez-Duarte, A strengthening of the Nyman-Beurling criterion for the Riemann Hypothesis, arXiv:math/0202141: https://arxiv.org/abs/math/0202141

The known mathematical framework is separate from the new deductions and the finite rule comparison in this note.

## 8. Reproduce and limits

    OPENBLAS_NUM_THREADS=1 python aggregate_repair.py

Dependencies: numpy, mpmath. The copied baseline helper code is an input, not an independent verifier. Rebuilt combined-coefficient checks are independent of the greedy update arrays; their agreement is not a formal proof assistant result.

No GitHub write, merge, external agent job, or desktop operation was performed. Results are preserved as conversation files; no claim of repo-native preservation is made.
