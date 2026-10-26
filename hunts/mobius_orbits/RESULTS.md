# Multi-prime Mobius orbits: exact cancellation, still an open RH target

**Status: ordinary argument with independent model challenge completed.**
See [the review and its limitations](REVIEW.md). This is not human peer
review or a kernel-checked statement.
The finite tests check the identities, not an unbounded estimate.
There is no RH proof or disproof here, and no claim of novelty.
Base: `8941a80`. The earlier p=2 note is not edited or regraded.

## 1. Target and attempted construction

The parent target, from
[the factorization note](../prime_pair_error/FACTORIZATION_NEXT_STEP.md), is

    D_N = S_smooth(N) + Sigma1(N) + Sigma2(N),
    |D_N| = O_epsilon(N^(1/2+epsilon)) for every epsilon > 0.

Its relation to RH depends on that note's full reduction. Nothing here
re-establishes the reduction or supplies the joint bound. In particular,
controlling Sigma2 alone does not control cancellation with the other terms.

For integer N >= 4, set H=floor(N/2), U=floor(sqrt(H)), and
V_b=floor(H/b). Write

    T_b = sum_{U<a<=V_b} mu(a) [1-floor(N/(ab))],
    Sigma2 = sum_{b=2..U} log(b) T_b.

This is the integer-kernel branch inherited from the parent note. Empty
sums are zero. The extension attempted here keeps the sign relations for
several primes simultaneously instead of one p=2 pair. It is compared to a
separate exact level-set expansion, not assumed better because it is newer.

## 2. An exact orbit identity with all boundaries

Let P>1 be squarefree. Every term not killed by a squared prime dividing P
has a unique representation a=dm with d|P and gcd(m,P)=1. Then
mu(a)=mu(d)mu(m), including zero when m is not squarefree. Thus, with

    J_m = {d|P : U<dm<=V_b},
    K_m = sum_{d in J_m} mu(d) [1-floor(N/(dmb))],

one has exactly

    T_b = sum_{m<=V_b, gcd(m,P)=1} mu(m) K_m.                 (1)

No cutoff term has been discarded. The sums are finite. Terms divisible by
a squared prime from P contribute zero to the original sum and are absent
on the right for that reason only.

An orbit is complete precisely when U<m and Pm<=V_b. For those m, all d|P
are active, and elementary inclusion-exclusion gives

    K_m = -Phi_P(floor(N/(mb))),                            (2)
    Phi_P(x) = #{j in Z : 1<=j<=x, gcd(j,P)=1}.

Indeed sum_{d|P}mu(d)=0, and
sum_{d|P}mu(d)floor(x/d)=Phi_P(x). This is an ordinary finite combinatorial
proof, not an inference from numerical agreement.

The complete-orbit kernel has a fixed negative sign. The surviving
oscillation is mu(m), not cancellation inside Phi_P. Setting m=1 in a
complete orbit is impossible because U>=1; the formula itself still holds
as an inclusion-exclusion identity for any positive x.

## 3. A specified majorant and its fixed-P asymptotic

Define A_P(N), explicitly discarding |mu(m)|<=1, by

    sum_{b=2..U} log b [
      sum_{U<m<=V_b/P, gcd(m,P)=1} Phi_P(floor(N/(mb)))
      + sum_{incomplete m, gcd(m,P)=1}
          sum_{d in J_m} N/(dmb)
    ].                                                     (3)

Then |Sigma2|<=A_P(N). Complete orbits use (2); incomplete ones use
|1-floor(N/(ab))|<=N/(ab), valid on this range since ab<=H<=N/2.

**Candidate ordinary asymptotic, with P fixed:** if c_P=phi(P)/P, then

    A_P(N) = (c_P^2/48) N(log N)^3 + O_P(N(log N)^2).        (4)

This is not asserted uniformly for P growing with N.

Proof details to be challenged:

1. Periodicity gives Phi_P(x)=c_P x+O_P(1). Partial summation of the
   periodic coprimality indicator gives, uniformly for B>=U>=1,
   sum_{U<m<=B,gcd(m,P)=1}1/m = c_P log(B/U)+O_P(1/U).
2. An incomplete orbit satisfies m<=U or Pm>V_b. Every active a=dm then
   lies in (U,PU] or (V_b/P,V_b], intersected with (U,V_b]. The
   representation is unique, so its total majorant is bounded by the sum
   of N/(ab) over these two intervals. Their harmonic mass is O_P(1).
   Consequently all incomplete orbits together cost
   O_P(N sum_{b<=U}(log b)/b)=O_P(N(log N)^2).
3. The exact geometric cutoff for a potentially nonempty complete
   interval is B=floor(H/[P(U+1)]). Coprimality may still leave no m.
   Set L=H/(PU); then B=L+O_P(1) for fixed P. For the complete part,
   the upper m cutoff is floor(H/(Pb)). Its harmonic evaluation gives
   the main term

       c_P^2 N sum_{2<=b<=L} (log b)/b log(L/b).

   Extending the exact integer endpoint to L adds only the endpoint
   errors covered by the same estimate. Floor and harmonic errors cost
   O_P(N(log N)^2); the O_P(1) error per coprime-count term also sums to
   O_P(N sum_{b<=U}(log b)/b).
4. Integral comparison yields
   sum_{2<=b<=L}(log b)/b log(L/b)=(log L)^3/6+O((log L)^2).
   For fixed P, log L=(log N)/2-log(P sqrt(2))+O(N^(-1/2)).
   This yields (4). Finitely many small N are absorbed in the fixed-P
   remainder constant; none is omitted from the exact identities.

At P=2, the proposed coefficient is 1/192, matching the previously
recorded leading coefficient. P=6 gives 1/432, P=30 gives 1/675, and
P=210 gives 4/3675. The script computes these fractions rather than
estimating them from a short scan.

Thus this SPECIFIED fixed-P absolute-value estimate changes the leading
constant, not the exponent or logarithmic power. It supplies no RH-strength
bound. It does not obstruct a signed estimate, a growing-P construction
with uniformly controlled boundaries, or a different argument entirely.

## 4. An independent exact floor-level representation

Let M(t)=sum_{a<=t}mu(a) be the Mertens function and
Q_b=floor(N/[b(U+1)]). Since

    floor(N/(ab))-1 = sum_{k=2..floor(N/(ab))}1,

interchanging finite sums yields

    T_b = -sum_{k=2..Q_b} [M(floor(N/(bk)))-M(U)].           (5)

For k>=2 the upper a cutoff is at most floor(N/(2b))=V_b,
so there is no missing V endpoint. For k<=Q_b it is at least U+1;
if Q_b<2 both sides are empty.

A useful uniform transfer, with its input visible: suppose

    |M(t)| <= t E_U  for every integer t>=U.

Then, for each nonempty b-row,

    |T_b| <= (2N/b) E_U sum_{k=2..Q_b}1/k.                 (6)

Both Mertens arguments are at least U, and
U<=floor(N/(bk))<=N/(bk), which proves (6) without assumptions on where
floor jumps occur. For U>=2, summing gives the coarse bound

    |Sigma2| <= 2N E_U (log U)(1+log U) log N.              (7)

For U=1 the sum is empty. The finite test uses the exact rational envelope
max_{U<=t<=floor(H/2)} |M(t)|/t, which covers all arguments in (5),
not an infinite-range estimate. It checks (6) row by row with Fractions.

Inserting an independently supplied classical envelope
E_U=C exp(-c sqrt(log U)) into (7) gives a subexponential saving over
N log^3 N, with constants retained. This corollary is explicitly conditional
on that input as stated here; the underlying analytic-number-theory bound
is not re-proved in this hunt. The exact identity (5) and transfer (6)
address the endpoints and uniformity that were left unpriced in the earlier
factorization note. They do not give the N^(1/2+epsilon) joint estimate.

## 5. What arithmetic has and has not been removed

For fixed P and Re(s)>1, absolute convergence of the Euler product gives

    sum_{gcd(n,P)=1} mu(n)n^(-s)
      = (1/zeta(s)) product_{p|P}(1-p^(-s))^(-1).          (8)

The finite product is analytic and nonzero on Re(s)>0, because
|p^(-s)|<1 there. Its meromorphic continuation cannot cancel a pole of
1/zeta at an off-critical zero. This is a conditional statement about
such a zero, not a claim that one exists. Removing finitely many Euler
factors alone has not removed the remaining zero-exclusion problem.

Equation (8) is not a theorem that every multi-prime approach fails. An
estimate exploiting the remaining mu(m) signs could still supply the
missing information; (3) discards precisely those signs.

## 6. Evidence and controls

`probe.py` independently computes a Mobius sieve and a trial-division
Mobius function, compares (1) and (5) to the direct integer sum in every
b-row, checks the rational bound (6), and compares the inclusion-exclusion
count to direct gcd enumeration. `pilot.json` and `results.json` retain
the finite rows. The full run covered 1196 (N,P) cases and 8412 b-rows:
N=4..300, plus 1000 and 10000, at P=2,6,30,210. Every direct/orbit/level
comparison had exact zero defect. The Mobius sieve matched independent
trial division at all 5000 inputs and coprime counts matched direct gcd
counts in 4004 checks. At P=210, N=10000 there are no complete orbits:
all of Sigma2 is boundary. A favorable local density must not erase it.
Log-weighted totals are ordinary floating-point diagnostics,
not sign enclosures or proofs of (4).

Dropping incomplete orbits and reversing the complete-orbit sign are
intentional lesions. Both must have an exact nonzero witness or the script
fails. No floating-point precision setting is needed for these integer
and rational checks; the float totals are outside their truth claims.

Davenport-Heilbronn is not run as a rival here: no structural implication
from shared analytic axioms to RH is claimed. The construction explicitly
uses the genuine Mobius function and does not establish its required
uniform cancellation. Nor does a surrogate passing inclusion-exclusion
refute the elementary identity. No zeta zero census is being inferred.

## 7. Disposition

RH remains unresolved in this attempt. The exact construction survives the
finite checks only at their stated scope. The handwritten asymptotic is
subject to the separate review record; it is not a formal proof.
Nothing is published, and no prior manuscript or accepted result is changed.

## The doors

- **Active loss:** taking absolute values of the remaining rough-index
  mu(m) terms. Equation (2) exposes those signs instead of controlling them.
- **Frozen choices:** P is fixed; the split U=floor(sqrt(floor(N/2))) and
  the kernel are inherited. Letting P grow changes both the density and
  the error constants. Treating O_P as uniform would be invalid.
- **Information class:** (3) uses only local sign relations at primes
  dividing P, coprimality, and |mu(m)|<=1. A signed rough-index estimate
  or a joint cancellation argument with S_smooth+Sigma1 retains information
  discarded by (3). No further run is launched or presumed justified here.

**Completed on landing, 2026-10-21.** The three bullets above are the hunt's
text of 2026-09-26. They name no active constraint and predate the energy
continuation and its pause, so the parts below complete the section from the
hunt's own record. No claim, run or grade changes.

- **Active constraint at the optimum, fixed-prime route:** the step
  |mu(m)|<=1 on the rough-index terms of (3). With those signs discarded, the
  specified majorant gains only a constant from the complete-orbit kernel
  (2): by (4) the leading constant falls from 1/192 at P=2 through 1/432 and
  1/675 to 4/3675 at P=210, and the order N(log N)^3 stays. Set against that constant is
  boundary mass, which grows with P. The review's boundary estimate carries
  the factor sigma_{-1}(P)(1+log P), and at N=10000 the exact counts of
  complete (b,m) orbits in `results.json` fall from 2745 at P=2 to 331, 5
  and 0 at P=6, 30 and 210, so at P=210 all of Sigma2 is boundary. No shadow
  price is computed. Raising P moves the constant and the boundary and
  leaves the discarded signs discarded.
- **Active constraint, energy route:** the unproved correlation bound
  `ENERGY.md` (7), or its weaker form (12), which suffices through the
  divergence condition (11). The block identity and the trace cap (10) are
  exact, and the cap has room: tr S measured 0.148 to 0.180 against the cap
  0.874 (`energy_reviewed.json`). What binds is a lower bound on the
  correlation, or on the residual moment, relative to E_N^2 and the Schur
  cost. The normalized trace values M_N/(T_N E_N^2) fall from 4.28 through
  0.955, 0.546 and 0.327 to 0.243 over the shells N=4 to 64, while the
  shell's own gain_N/E_N^2 stays between 7.80 and 10.98. Neither finite
  range supplies a constant.
- **Frozen constants, energy route:** the dyadic schedule N=4*2^j, the
  predeclared shell weight log(2N/n) of `ENERGY.md` (3), the five shells and
  the precisions of 128 and 192 bits. Fitting the shell to the block optimum
  would buy gain and give up what makes (7) a target: it is specified by the
  Gram matrix and the shell alone, not a new name for the optimized distance
  (`ENERGY.md` section 4). Larger shells were not run; the route is paused
  by allocation, not closed.
- **Information class, energy route:** the construction reads only the
  Baez-Duarte Gram matrix and target vector, through the existing Vasyunin
  implementation, and mu on (N,2N]. Another predeclared shell, weight or
  block schedule stays inside that class. A proof of (7) or (12) needs an
  unconditional lower bound on the correlation q or on the residual moment
  M_N, which neither Gram positivity nor the construction supplies. The
  Bettin-Conrey-Farmer result for the smoothed Mobius shape assumes RH, so
  it cannot be that input.
