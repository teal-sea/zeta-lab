# Independent mathematical challenge

**Disposition: the challenged identities and fixed-P asymptotic survived
this review. RH was not established.**

A separate-context reviewer was given the definitions and proposed proof
mechanism, not the parent's code or finite output, and returned an ordinary
mathematical analysis. This is a model review, not human peer review, a
formal proof, a literature search, or an audit of the upstream RH reduction.
The reviewer did not read or modify repository files. The parent checked
the reasoning below against the written argument before incorporating it.

## Accepted within the stated hypotheses

- Unique factorization a=dm with d|P and gcd(m,P)=1 after excluding
  terms divisible by a squared prime from P. All such excluded terms
  have mu(a)=0; non-squarefree m remain harmless zeros.
- Complete-orbit identity K_m=-Phi_P(floor(N/(mb))) for U<m and Pm<=V_b.
- The defined positive majorant has leading coefficient
  (phi(P)/P)^2/48 at fixed P. Its incomplete part is O_P(N log^2 N).
- Exact level-set identity for T_b, including odd N and empty ranges.
- The bound with a uniform Mertens envelope, without unpriced floor jumps.

## Endpoint clarification incorporated

The exact geometric cutoff for a potentially nonempty complete interval is

    B = floor(H/[P(U+1)]),

not floor(H/[PU]). Coprimality can still make that interval empty.
For L=H/(PU), B=L+O_P(1), so changing the endpoint to L is permitted
only in the asymptotic evaluation, not in the exact identity. The parent's
code uses the exact condition U<m and Pm<=V_b.

The reviewer supplied the alternate boundary estimate

    A_inc,b <= (2N/b) sigma_{-1}(P)(1+log P),

by enclosing incomplete m in (U/P,U] union (V_b/P,V_b]. This agrees
with the parent's bound using the unique active a rather than m.

## Wording clarification

The initial condensed brief used the ambiguous expression 'zeta poles'.
The correct objects preserved by the nonzero finite Euler factor are poles
of 1/zeta arising from zeros of zeta. The pole of zeta at s=1 instead
gives a zero. RESULTS.md uses the correct wording.

## What the review does not establish

- No lower bound for the true signed Sigma2.
- No constants uniform in growing P.
- No theorem excluding other multi-prime or signed constructions.
- No joint bound with S_smooth+Sigma1, hence no RH implication discharged.
- No fresh proof of the classical Mertens estimate or claim of novelty.

The reviewer also reported independent in-memory finite checks. Their
numerical totals are not adopted into the parent's evidence count; the
reproducible finite evidence of record remains probe.py and results.json.
