# Density closes the eighth-power obstruction

Status: written conditional derivation, numerical inequalities enclosed
by Arb; independent audit completed in ../../audits/prime-gap/AUDIT.md. No kernel formalization or novelty claim.

Claim: If every nontrivial zero of zeta has real part at most 7/8,
then for every integer n >= 1 a prime lies strictly between n^8 and (n+1)^8.
The zero-free input remains an assumption. We additionally use the classical
explicit formula, zero-count and verified-RH-height inputs already specified in
PR276 RESULTS sections 1 to 5. We do not reauthenticate those inherited leaves.

## New source input

Kadiri, Lumley and Ng, *Explicit zero density for the Riemann zeta function*,
JMAA 465 (2018) 22-46, arXiv:2101.12263v1, submitted 2021-01-28.
https://arxiv.org/pdf/2101.12263v1
Lemma 4.14 equation (4.71) and section 5 Table 1, sigma=.85 row, give
N(.85,T) <= 8.975 T^.4 (log T)^3.3 + 3.588 (log T)^2
for T >= 3.0610046e10. We round coefficients upward to 9 and 4.
Here N counts zeros with beta>sigma and positive ordinate, with multiplicity.
The modern verified height H=3000175332800 is larger than this threshold.
This is source extraction, not a rerun of the source's constant calculations.
Source-audit trap: Theorem 1.1 imposes delta>=1 whereas the table uses
delta=.303. The lemma actually used for the table, Lemma 4.14, explicitly
assumes delta>0. Section 5 explicitly identifies equation (4.71) as the
table's input and says the U-monotonicity conditions are checked for each
parameter set. We therefore cite that lemma and table, not the more narrowly
stated introductory theorem. No silent correction to a theorem is needed.

## Reduction and proof

Use PR276's same weight, g(u)=min(1,4.5/u,216/u^3), a=1+x/h,
x=n^8, h=(n+1)^8-n^8. Set G(t)=g(t/a) and
D(t)=9t^.4(log t)^3.3+4(log t)^2.
Let S_low,S_high be PR276's positive-ordinate zero sums below/above H.
Splitting the high zeros at beta=.85 gives

 E_new = 2x^(-1/2) S_low + 2x^(-.15) S_high
         + 2x^(-1/8) R(a) + 1/[x(x^2-1)],
 R(a) = integral from max(H,4.5a) to infinity D(t)(-G'(t))dt.

Indeed, zeros with beta<=.85 cost at most x^(-.15), and those above
cost at most x^(-1/8). Counting the latter twice only enlarges the bound.
Their count is zero up to H. Stieltjes integration, followed by N(.85,t)<=D(t),
gives the expression for R. No subtraction of an upper density estimate at H
is permissible or used. Endpoint conventions in N do not affect the integral.
The prime-power subtraction P and sufficient condition E_new+(9/4)P/h<1
are unchanged from PR276 Proposition 4.1.

For B=max(H,4.5a), t>=B, log t <= log B*(t/B)^(1/log B).
Thus each t^r(log t)^q integrand is bounded by
B^r(log B)^q*(t/B)^(r+q/log B). The power moments against -G' are elementary
and evaluated by density.moment. This supplies a bound, not an approximate
numerical integration. Powers are computed as Arb real powers at 256 bits.

For an interval L=log n in [La,Lb], take a at Lb, x negative powers at La,
and the inherited interval bounds for P/h. The majorants are monotone in a
because G(t) is monotone in a and Stieltjes measures are positive. The bound
on R is computed after this replacement, so it need not itself be proved
monotone. All 604 intervals of length 1/16 covering [2.25,40] close.
The least enclosed margin is greater than .95468. Since 2.25<log10, this
covers integer n>=10 through e^40.

For n>=e^40, first use PR276 kth_power_tail with k=8, theta=.85 to bound
the low and full high-count terms, trivial zeros and prime powers. This use
does not assume QRH(.85): it is a numerical majorant of those terms only.
Its bound is less than .037126 and each monomial decreases.
For the additional rare-zero term replace a by n, since a<=1+n/8<=n.
Now B=4.5n>H, log B<=L+2, and .4+3.3/log B<.5.
The moment at exponent .5 is <2; also 4.5^.4<2.
Consequently the additional contribution is at most

 72 n^(-.6)(L+2)^4 + 16 n^(-1)(L+2)^2.

We enlarged (L+2)^3.3 to (L+2)^4. Both monomials decrease for L>=40,
since 4/(L+2)<.6 and 2/(L+2)<1. At L=40 their sum is less than .008458.
The complete tail bound is <.045583<1. Every cited decimal comparison is
checked by density.py with certain Arb inequalities.

For n=1,...,9, density.py searches for and verifies a prime witness by
exhaustive integer trial division through isqrt(p), then checks strict interval
membership. This closes the remaining cases without a probabilistic test.

## Falsification and audit path

crosscheck.py independently integrates D(t)(-G') in log coordinates with
mpmath at four transition regimes. It is nonrigorous corroboration only.
It confirms that the analytic majorant dominates quadrature. The original
full-N bound fails at k8,L30, the new density bound succeeds, and the same
single split fails at k7,L30. Composite 341 and 561 are rejected by the
small witness checker. A failed k7 bound is neither a theorem nor a prime
counterexample. Initial analytic testing from n=2 failed; those small values
are handled with exact witnesses, not silently dropped.
The independent audit caught an endpoint-rounding error in the first rare()
implementation: rounding B upward shortened the positive integration domain.
The repair preserves B as an Arb ball enclosing the exact endpoint throughout
the elementary integral. Both scripts were rerun after this change. The
previous cover's positive margins did not license that discarded sliver.

The original audit request was to derive the Stieltjes bound, check the source row,
verify monotone interval replacements and tail, and replay both scripts.
The copied base_bound.py is byte-for-byte from the pinned input branch.
No mathematical independence is claimed for the reused PR276 implementation.

## Prior-art scope

Checked primary Cully-Hugill and Johnston arXiv:2402.04272v3 section 5,
which uses zero density for an all-n 90th-power theorem, and KLN above.
The mechanism is classical; using density is not new. Searches for eighth
powers plus 7/8, and consecutive primes plus quasi-Riemann, did not return an
authenticated identical theorem, but broad search results were noisy.
Classification: new written extension of this lab's previous mechanism;
worldwide novelty unresolved. Unconditional eventual eighth-power existence
already follows from classical short-interval results, so the shareable delta
would be the explicit all-n statement under the stated half-plane assumption.

## The doors

Active constraint for k7: this split assigns all beta<=.85 the endpoint .85;
that full-count term remains too large near H. Fixed constants: split .85,
weight, H, and rounded density coefficients. Multistrip density could reduce
this loss, but was not required for k8. Weight changes stay in the old
information class; density reads a genuinely additional input. None of the
observed failures is a universal lower bound on what the half-plane implies.
