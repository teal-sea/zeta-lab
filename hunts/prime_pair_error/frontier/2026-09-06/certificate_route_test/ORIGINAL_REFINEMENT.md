# An explicit positive-repair rule for factorial upper certificates

Date: 2026-09-06. Status: written derivation with executed exact arithmetic
checks. This is not an independently reviewed theorem, a novelty claim, an
improvement over established prime-counting estimates, or an RH proof.

This pass answers the requested construction problem with a reusable update,
rather than a new linear-programming optimum at each period. It generalizes
the old *periodic seed* class: the seed may now include a controlled sum of
dilates of one fixed valid seed. The factorial-majorant argument still applies.
The change of admissible class is intentional and is accounted for below.

## 1. Inputs and objective

The starting seed g_0 has period 30030, rescaling M=15, coefficient mass 39,
and leading constant

    C_0 = 1.0558051175401548984946997960984321129...

The fixed repair seed g_* is the previous period-2310 seed, also at M=15.
It has coefficient mass 15 and

    C_* = 1.0698544525734642379888416758839241028...

Their exact rational coefficients are in inputs.json. They come from the
attached certificate_structural_step/checked_results.json, not an assumed
new computation of the LP. refine.py independently checks all residues of
both seed periods, their balance, and their cover of [1,15).

For a nonnegative seed g, zero on [0,1), at least one on [1,M), define

    W_g(t) = sum_{k>=0} g(t/M^k).
    kappa(g) = integral_1^infinity g(t)/t^2 dt.
    C(g) = kappa(g)/(1-1/M).

The sums are locally finite for our constructions. Choosing k with
1 <= t/M^k < M proves W_g(t)>=1 for all t>=1. Nonnegativity and Tonelli
give C(g)=integral_1^infinity W_g(t)/t^2 dt.

Use W_*=W_(g_*) throughout. The repair function is FIXED, rather than
recursively nesting a new rescaling layer at every iteration.

## 2. A small nonnegative arithmetic patch

For integer n>=2, define

    b_n(t)=floor(t/n)-floor(t/(n+1))-floor(t/[n(n+1)]).

Since 1/n=1/(n+1)+1/[n(n+1)], this is
floor(u+v)-floor(u)-floor(v), so it always equals 0 or 1.
Moreover b_n(t)=0 for t<n and b_n(n)=1.
All breakpoints are integers; its period is n(n+1).

Its balanced floor coefficients have total absolute mass 3. Its integral is

    k_n = integral_1^infinity b_n(t)/t^2 dt
        = log(n+1)/n - log(n)/(n+1) > 0.

This follows from the same balanced-floor integral identity used in the
reviewed pilot. These carry functions and the floor/factorial framework are
classical ingredients; no claim of inventing them is made.

## 3. The correction to subtract

Fix P=210=2*3*5*7. For each tested p, define

    h_p(t)=sum_{d|210} mu(d) b_p(t/d).

This discounts the copies at multiples of the four already-present small
primes. It is a signed function, not required to be a majorant itself.
Its coefficients are obtained by a fixed rule; there is no LP.

It vanishes for t<p, its coefficients are balanced, and

    kappa(h_p) = (phi(210)/210) k_p = (8/35) k_p.

Every b_p(t/d) has period dividing 210*p*(p+1). The analytic bound h_p<=8
follows by discarding the eight negative terms. For the five particular
p in this pass, an exact enumeration of that complete period proves the
sharper bound h_p<=3. The period check is part of the finite certificate,
not an extrapolation of sampled values.

The mask was selected after the exploratory p=17 comparisons preserved in
exploration.json; this is not a preregistered or blindly selected parameter.
It was then held fixed in the sequence p=17,19,23,29,31. There was no new LP
in any of these stages.

## 4. The general positive-repair lemma

Let g be any currently valid seed, h a balanced-floor perturbation zero
on [0,M), and suppose h(t)<=H for all t>=0. Fix an integer R>M.

Set the current prefix f=g-h. For n=1,...,R-1 in increasing order, let

    q_n = 1 if 1<=n<M, and 0 otherwise;
    a_n = max(0, q_n - f(n));
    f(t) <- f(t) + a_n b_n(t).

Here no patch at n=1 is needed, since h=0 on [0,M) and g already covers
that interval. Earlier repairs have no negative values and b_n(t)=0
for t<n, so nothing already checked is damaged.

After the finite loop, define

    g_new(t)=g(t)-h(t)+sum_{n<R} a_n b_n(t)+H W_*(t/R).       (R1)

This is an explicit construction, including its tail, not merely a
definition of the desired inequality.

**Proof of global validity.**

* For 0<=t<R, the final tail is zero. The finite integer checks cover all
  real t in this interval, since every function involved is constant on
  [n,n+1). The loop ensures nonnegativity and the required cover.
* For t>=R, the previous g and every added patch are nonnegative, h<=H,
  and W_*(t/R)>=1. Therefore g_new(t)>=-H+H=0.
* The initial interval [1,M) retains its cover. g_new is zero on [0,1).

Thus the ordinary rescaling argument proves W_(g_new)>=1 at EVERY cutoff.
The proof is not dependent on testing prime counts up to R.

The exact leading-constant change is

    C(g_new)-C(g)
      =[-kappa(h)+sum a_n k_n + H C_*/R]/(1-1/M).            (R2)

Every cost, including coverage of the infinite tail, is in this formula.
A correction is an improvement only when the bracket is negative.
No theorem that it is always negative is asserted.

This rule need not stay inside denominators dividing pL: a repair b_n
introduces n, n+1 and n(n+1). It is a deliberate extension of the old
denominator class, not merely one new prime index in the old LP.

## 5. Five executed applications

Use R=100000, M=15, the same repair seed, and the same small-prime mask
at all five steps. Start with the period-30030 seed.

| p targeted | H | nonzero repair patches | resulting C (approx.) |
|---|---:|---:|---:|
| starting seed | — | — | 1.05580511754015490 |
|17|3|161|1.05464046024778005|
|19|3|298|1.05277233461141158|
|23|3|251|1.052079534139605|
|29|3|207|1.05101155666215312|
|31|3|265|1.05003119814182489|

The full 60-digit values in results.json, rather than the rounded intermediate
values in this table, are the numerical record. Each strict decrease is also
checked by rational upper/lower enclosures for logarithms.

The enclosure for the final constant is contained in

    1.0500311981418248 < C_final < 1.0500311981418250.

The method for those enclosures is the positive atanh series for log(r),
1<=r<=2, with an explicit positive tail bound. Integer n is reduced as
n=2^e r. Endpoints are rounded OUTWARD to a dyadic grid using integers.

There are 1182 repair patches across all steps. After combining repeated
denominators, the finite part has 1609 nonzero floor coefficients, total
absolute mass 4676/3. The final seed has the form

    g_final(t)=D(t)+15 W_*(t/100000),

where D is a finite balanced floor sum. Its kappa is positive, checked by
the same rational log enclosures. The tail is not hidden in the finite mass.

## 6. Explicit factorial certificate and full error budget

Let D(t)=sum_j d_j floor(t/j), and let a*_j be the coefficients of g_*.
For the final seed, with H_total=15, the exact factorial expression is

 B_final(N)
  = sum_{k>=0,j} d_j log(floor(N/[j M^k])!)
    + H_total sum_{m>=0,j}(m+1) a*_j
        log(floor(N/[R j M^m])!).                           (F1)

These sums are finite for each integer N. The factor (m+1) counts the
ways the outer rescaling and the fixed repair rescaling can sum to m.

The standard identity sum_{d|n} Lambda(d)=log n gives, exactly,

    B_final(N)=sum_{d<=N} Lambda(d) W_(g_final)(N/d)>=psi(N). (F2)

The proof uses full prime-power weights, not a fitted approximation.

Put K=floor(log_M N), and define

 S1(N)=(K+1)(1+log N)-log(M)K(K+1)/2.

For N<R set S2(N)=0. Otherwise set K_R=floor(log_M(N/R)) and

 S2(N)=sum_{m=0}^{K_R}(m+1)[1+log(N/R)-m log M].

The pilot's factorial-error inequality, applied to D and g_* separately,
proves, since their kappas are positive,

 B_final(N)
 <= C_final N + (4676/3) S1(N) + 15*15 S2(N).               (F3)

No uncertain sign of a discarded error is used. The omitted geometric
main-term tails have the favorable sign because kappa(D), kappa(g_*)>0.

For this fixed construction the remainder is O(log^3 N).
A more complicated finite seed was purchased with a much larger explicit
error allowance, not obtained for free.

60-digit diagnostic evaluations (not outward-rounded factorial evaluations):

| N | old B_N | new B_N | old proved envelope U_N | new proved envelope U_N |
|---|---:|---:|---:|---:|
|10^4|10533.543704|10466.910031|11517.180526|48832.695273|
|10^6|1055759.569096|1049637.735149|1057687.737643|1126014.720824|
|10^8|105580426.553620|105001137.606200|105583595.706744|105132173.468302|
|10^12|1055805117379.805|1050031192298.811|1055805124014.095|1050031495109.320|

The old envelope in this table uses the simpler valid C*N+A*S1 bound,
dropping the negative geometric-tail adjustment. That is why it differs
slightly from the tighter old U_N numbers in STRUCTURAL_STEP.md.

The new ACTUAL certificate is lower in these four examples. The new proved
envelope is worse at the two smaller cutoffs and better at the two larger
ones. This retains the distinction learned in PR #196.

## 7. Checks actually executed

Run:

    OPENBLAS_NUM_THREADS=1 python refine.py --output rerun.json

The run does not use scipy, an LP solver, a remote agent, or prime data to
choose coefficients. Numpy and mpmath are the only nonstandard libraries.

Checked:
- 32340 input-seed period positions and exact balance.
- 651000 positions covering the entire five perturbation periods;
  the upper cap H=3 is consequently valid globally.
- 500000 prefix positions independently rebuilt from combined rational
  floor coefficients, not just trusted from the greedy update array.
- Each leading-constant decrease via exact rational logarithm enclosures.
- 70 exact large-argument tail samples in addition to the general tail proof.
- 1411 exact prime-exponent factorial identities, using independent
  Legendre exponent calculations at N=1000,10000,1000000.
- The four actual-certificate and proved-envelope evaluations above.

The exponent tests use primes only to check the identity after construction,
not to fit or choose the certificates. Finite tests do not independently
referee the entire analytic proof or certify a growth rate in refinement count.

## 8. What this establishes, and what it does not

Established by the written construction and finite certificates:
- a deterministic, reusable correction-and-repair rule;
- preservation of the upper-certificate inequality for every N;
- five strict decreases of the leading coefficient;
- an explicit full cost, including the infinite tail and rescaling.

Not established:
- a uniform rate making C_r-1 tend to zero;
- a bound on coefficient complexity as r and the prefix length grow;
- a half-gap/double-mass recurrence;
- an RH-scale bound, improvement of total CHHL E(N), or new prime-counting record;
- novelty or independent proof review.

The five steps reduce the leading excess by about ten percent while
increasing the finite coefficient mass from 39 to 4676/3 and adding the
explicit tail cost. This does NOT meet the illustrative RH-sufficient
tradeoff proposed in the preceding message.

It is mathematical construction work, not a fourth optimizer scoring rule.
Its remaining question is a quantitative theorem about this rule's benefits
and costs, not whether an unspecified future agent can invent the rule.

The work in this package has not been pushed to GitHub. No existing archive,
pilot, PR, or referee result was changed.

## 9. Sources and provenance

- Attached STRUCTURAL_STEP.md and its checked_results.json provide the two
  seed inputs; inputs.json records their exact coefficients and ZIP hash.
- The pilot's balanced-floor integral identity and factorial-error bound
  are reproduced at the points they are used.
- Bober, Factorial ratios, hypergeometric series, and a family of step
  functions, arXiv:0709.1977, especially the Chebyshev discussion and
  Section 3: https://arxiv.org/html/0709.1977
  This is context for the classical floor/factorial framework, not a claim
  that Bober proves this particular update or its numerical constants.
- NIST DLMF 27.5, the von Mangoldt divisor identity:
  https://dlmf.nist.gov/27.5

No literature search sufficient to claim this refinement rule is new has
been completed. The elementary carry identity is standard.
