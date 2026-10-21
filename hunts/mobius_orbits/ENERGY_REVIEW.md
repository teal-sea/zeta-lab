# Controlled-energy mathematical review

**The block descent identity survived independent model challenge.**
The review did not prove RH or the all-scale quantitative decrease.
This is not human peer review, formal checking, or a novelty search.
The reviewer analyzed the mathematical brief rather than auditing the
parent's source. The parent verified the returned derivation and then
executed the added finite checks in `energy_reviewed.json`.

## Accepted algebra

With S=D-C^T G^(-1)C and u=d-C^T G^(-1)b, the exact optimum obeys
E_(2N)=E_N-u^T S^(-1)u. A one-direction update uses the old coefficient
correction -alpha G^(-1)Cv as well as the appended shell alpha v.
Its decrease is (v^T u)^2/(v^T S v). Neither a bounded norm nor a
strictly positive finite sequence of decreases establishes a zero limit.

## Constructive addition

Take v=u when u is nonzero. With M=u^T u and T=tr S, the decrease is
M^2/(u^T S u), at least M/T since S<=T I. The denominator can be
priced without an inverse or a smallest-eigenvalue estimate:

    T <= tr D = (log(2pi)-gamma) sum_{n=N+1..2N}1/n
      < (log(2pi)-gamma) log 2.

This avoids directional orthogonality: a fixed Mobius vector can satisfy
v^T u=0 even for u nonzero. It does not prove u nonzero at every scale,
and it is not guaranteed to outperform the Mobius direction numerically.
The parent therefore retains the larger of the two exact gains, rather
than discarding the predeclared direction.

## Missing lower bound

A sufficient condition is divergence of
sum_j M_(N_j)/(T_(N_j) E_(N_j)^2), where N_j=4*2^j.
For example a lower bound c/(j+1) for its summand would suffice.
This condition was not proved. The review did not derive it from RH either.
Unnormalized gains cannot have divergent total, because their sum is
bounded by the starting energy. The divergence target is explicitly the
normalized reciprocal-energy budget.

## Checks subsequently run by the parent

At N=4,8,16,32,64 and both 128 and 192 bits:
- the adaptive update's directly computed error overlaps E_N-gain;
- its gain exceeds the trace lower bound;
- the trace stays below the explicit uniform cap;
- precision responses and the existing block identities pass;
- the better-direction selector chooses the Mobius shell at every tested N.

A synthetic exact rational control has S=I_2, u=(1/2,0), v=(0,1):
the fixed direction has zero gain, the adaptive one has gain 1/4.
This tests the inference, not any zeta arithmetic claim.
Independent mpmath comparison at N=4 was extended to both new quantities.
The final focused suite returned 49 passed and 5 explicit slow exclusions.

The measured trace lower bound weakens across the five cases. No positive
constant or divergent infinite budget is inferred from those observations.
No files from the prior Nyman-Beurling hunt were modified.
