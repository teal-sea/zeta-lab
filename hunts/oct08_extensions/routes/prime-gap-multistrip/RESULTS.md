# Layered density gives seventh powers

Written conditional result, independently audited (../../audits/prime-gap-multistrip/AUDIT.md): assuming
every nontrivial zeta zero has real part <=7/8, every integer n>=1 has a prime
strictly between n^7 and (n+1)^7. Neither a novelty claim nor kernel formalization.
All inherited explicit-formula and verified-height assumptions are unchanged
from routes/prime-gap/RESULTS.md; this is a refinement of its density bound.

## Exact additional source rows

Kadiri-Lumley-Ng, arXiv:2101.12263v1, Lemma4.14 (4.71) and section5 Table1:
https://arxiv.org/pdf/2101.12263v1 . For T>=3.0610046e10,
N(s,T)<=A_s T^[8(1-s)/3](log T)^[5-2s]+C_s(log T)^2.
The rows (s,A_s,C_s) actually printed are
(.75,5.277,4.403),(.8,6.918,3.997),(.85,8.975,3.588),
(.86,9.441,3.514),(.87,9.926,3.430).
The implementation rounds upward to (5.28,4.41),(6.92,4),(8.98,3.59),
(9.45,3.52),(9.93,3.44). Counts have beta>s, positive ordinate, multiplicity.
The Lemma4.14 versus Theorem1.1 delta-condition issue was already resolved in
the previous route. Source constant calculations are cited, not reproduced.

## Layer-cake reduction

Let s0=.75,s1=.8,s2=.85,s3=.86,s4=.87,s5=.875 and x>1.
For every beta<=s5,

 x^(beta-1) <= x^(s0-1)
     + sum[j=0..4] (x^(s[j+1]-1)-x^(s[j]-1))*1[beta>s[j]].

The right side telescopes to the right endpoint of beta's strip, or to
x^(s0-1) below the first strip. It is therefore a pointwise upper bound.
All coefficients are positive, so substituting upper bounds for the strip
counts is valid. No subtraction of independently bounded counts occurs.
After multiplying by G(gamma)=g(gamma/a) and summing positive ordinates >H,
the new high-zero error is

 2x^(-.25) S_high(a) + 2 sum[j] Delta_j(x) R_j(a),

where R_j integrates the jth density bound against -G', from
max(H,4.5a) to infinity, exactly as in the audited eighth-power route.
That route's endpoint repair is inherited: the integration endpoint remains
an Arb ball, never rounded upward to discard a positive interval.
The low-zero, trivial-zero, and prime-power terms are unchanged.

For logx>=8 each Delta decreases in x. Indeed, writing y=logx,
Delta=y*integral[sj,sj+1] exp[-(1-t)y]dt, every integrand times y decreases
when y>=1/(1-t); t<=7/8 makes y>=8 sufficient. Thus on a logn interval
[La,Lb], evaluate every Delta at x=exp(7La), and the nonnegative zero-sum
majorants at a(Lb). This produces a valid interval bound.

## Complete cover

764 closed intervals of width1/16 cover logn in [2.25,50]. Arb at256bits
proves every margin>.13045; the weakest cell begins at29.125.
Since2.25<log10, this handles n>=10 to exp50. Trial division through isqrt
verifies explicit prime witnesses and strict membership for n=1,...,9.

For L=logn>=50, the inherited tail routine at k7,theta=.75 bounds the
baseline, low zeros, trivial zeros and prime-power subtraction. It is only
a bound on these quantities, not an assumption of QRH(.75).
Use a<=1+n/7<=n, replacing a by n in each positive zero sum. Then B=4.5n>H.
For row j put r=8(1-sj)/3,q=5-2sj,t=sj+1,d=7(1-t)-r.
We have r+q/logB<.8, q<4, 4.5^r<3. The power moment at exponent.8 is<3.
Therefore, discarding the negative part of Delta for an upper bound,

 2 Delta_j R_j <=18 A_j n^(-d)(L+2)^4
                    +6 C_j n^[-7(1-t)](L+2)^2.

Both monomials decrease on L>=50, verified from4/(L+2)<d and
2/(L+2)<7(1-t). Adding their values at50 to the baseline tail gives
total error<.012961<1. All stated decimal inequalities are Arb assertions.
This completes the candidate conditional implication for all integer n.

## Boundaries and falsification

The previous single-.85-split bound failed at k7 nearL30; replacing it with
single-.8 fails much worse. The success comes from resolving beta strips,
not from ignoring those negative tests. Same layered implementation for k6
fails at L29 with negative margin approximately -56.04, while eventual
positivity returns. This is a failure of the bound, not of sixth-power primes.
The external density estimate remains a cited theorem, and the inherited
explicit-formula source check is complete in ../../audits/prime-gap/SOURCE-CHECK.md.
The critical-line source addendum is in ../../audits/kln-restoration/SOURCE-CHECK.md.

The independent audit reconstructed the pointwise layer identity and the
monotonicity of Delta, checked moment and tail constants, and replayed the
cover at higher precision. Its scope and shared inherited code are disclosed
in ../../audits/prime-gap-multistrip/AUDIT.md.

Prior-art scope: the earlier route checked KLN and Cully-Hugill-Johnston
arXiv:2402.04272v3 section5. Density arguments and asymptotic prime-in-power
results are classical. Worldwide priority for the explicit all-n conclusion
under precisely QRH(7/8) remains unresolved; no first-result claim is made.

## The doors

Active k6 loss: finite-width beta bins and the absolute zero-sum majorant
near the verified-height transition. Frozen choices: these five source rows,
quadratic spline, verified H, and simple log-power majorants. Finer bins or
continuous density integration retain the new density information class.
The measured k6 failure is not an optimality certificate. No additional
weight optimization or brute-force prime search was needed for k7.
