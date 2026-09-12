# Blind Attack on blockpos-0.672529

## The Question
What modification of the world would preserve the appearance of this result while making its interpretation false?

## Findings
The claim asserts that block-positivity transplants to the pinned upstream zero side. The stated assumptions reveal that the upstream zero side analytically requires the un-conjugated transpose `u u^T`.

If an implementation or numerical control mistakenly computes the conjugate transpose `u u^*` (as the stated assumption hints), it constructs a Gram matrix that is positive semi-definite by definition. This modification of the world perfectly preserves the *appearance* of the result, any block-positivity scan will pass unconditionally. 

However, this makes the *interpretation* strictly false. The actual upstream zero side requires `u u^T`. For an off-line root $\gamma = \alpha + i\beta$, the vector $u = \hat{\phi}(\gamma - \tau)$ is complex ($u = x + iy$). The pairing of such a root with its conjugate yields:

$u u^T + \bar{u} \bar{u}^T = (x+iy)(x^T+iy^T) + (x-iy)(x^T-iy^T) = 2(xx^T - yy^T)$

This is a hyperbolic block. A matrix of the form $xx^T - yy^T$ has a negative eigenvalue (unless $y=0$, which is only true for on-line roots). Therefore, the true block is not positive semi-definite, and its interaction with other blocks (like the on-line part) can be strictly negative.

## Evidence Generated
We ran a dedicated scan (`hunts/frontier_math/blind_attack.py`) calculating the exact interaction between an on-line pair and an off-line pair using the correct `u u^T` construction. 

Configuration:
- On-line part: weight 2 at center
- Off-line pair: weight 3 at center + 18.58, depth 0.452

Result:
The cross-block interaction evaluates to approximately `-0.000435`, strictly falsifying the assumption that "off-line pair blocks interact non-negatively with on-line part."

## Conclusion
The claim `blockpos-0.672529` fails. The numerical evidence supporting it was likely gathered on the modified $u u^*$ world, which does not transplant to the required analytic structure.
