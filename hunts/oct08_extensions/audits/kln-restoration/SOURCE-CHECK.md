# KLN critical-line input: correction and restoration

Date: 2026-10-08. Independent reviewer: independent_audit.

**Verdict: the reported source defect is real, but the original KLN input constants are recoverable without changing the density rows or prime-gap arithmetic.** This addendum supplies the missing replacement source and repairs a separate small rounding gap in KLN's printed low-height argument. Earlier source acceptance omitted this correction history and should be read with this addendum. This is a written source implication with Acb interval verification, not Lean formalization.

## Authenticated sources

1. Johnston and Yang, *Some explicit estimates for the error term in the prime number theorem*, [arXiv:2204.01980v2](https://arxiv.org/pdf/2204.01980v2), Section 1.4 and Section 2 preceding Lemma 2.6. They identify the unreliable critical-line input inherited from Hiary, give the corrected coefficient 0.77 for t>=3, and explain that their recalculation uses a1=0.77 and a2=3.161 in KLN. Thus the historical objection is substantive, not merely a different optimization choice.

2. Hiary, Patel and Yang, *An improved explicit estimate for zeta(1/2+it)*, [arXiv:2207.02366v1](https://arxiv.org/pdf/2207.02366v1), dated 6 July 2022; published J. Number Theory 256 (2024), 195–217. Theorem 1.1 proves |zeta(1/2+it)|<=0.618 t^(1/6) log t for **every real t>=3**. Section 7 explicitly explains restoration of the older 0.63 bound. The primary theorem, not that commentary, supplies the replacement input. Full theorem statement and range were inspected.

3. Kadiri, Lumley and Ng, *Explicit zero density for the Riemann zeta function*, [arXiv:2101.12263v1](https://arxiv.org/pdf/2101.12263v1), Lemma 3.2, equations (3.2)–(3.4), printed pp.5–6. The required inputs are the 0.63 bound for t>=3 and the global maximum bound M(T)<=0.63 T^(1/6)log T+2.851 for every T>0, where M(T)=max_{|t|<=T}|zeta(1/2+it)|. These are the same constants used downstream to compute the original Table 1. The separate Lemma 4.14 versus introductory theorem parameter issue remains handled by the previous audit.

4. Hiary, *An explicit van der Corput estimate for zeta(1/2+it)*, [arXiv:1507.01261v4](https://arxiv.org/html/1507.01261v4), Theorem 1.1 and Lemma 2.2. The low-height bound 1.461 on [0,3] comes from Euler–Maclaurin interval arithmetic, not the faulty Kusmin–Landau step. We inspected that derivation's description. Its stated precision, however, is insufficient for the particular rounded KLN value a2=2.851, so the independent computation below replaces that low-height input.

These versioned primary full texts were read through the web tool. No new source PDF cache was retained. Author publication metadata is also available on [Hiary's university page](https://people.math.osu.edu/hiary.1/).

## Exact implication and rounding issue

For t>=3, log t>0 and 0.618<0.63, so the new theorem immediately restores KLN (3.2), on its full original range. Negative t follow by complex conjugation.

KLN's explanation of (3.3) uses min_{T>0} T^(1/6)log T=-6/e and the low-height bound 1.461. Taken literally, this does not establish their rounded value: 2.851-0.63*(6/e) is about 1.460415712, less than 1.461. This is an insufficient printed estimate, not a counterexample to (3.3).

The independent calculation in `check_low.py` proves

    max_{0<=t<=3}|zeta(1/2+it)| < 1.4604.

It also encloses the slack

    2.851 - 0.63*(6/e) - 1.4604 > 0.000015712371948.

For 0<T<=3 these facts prove (3.3). For T>=3, the function t^(1/6)log t is increasing; HPY bounds every t in [3,T], and the constant 2.851 already dominates the low-height maximum. This proves (3.3) for all T>0. We retain a1=0.63 rather than substituting 0.618 into a formula with log T<0.

Consequently the exact old critical-line inputs are established, not merely numerically close alternatives. The downstream KLN proof may retain its old constants and parameters. No monotonicity claim about a reoptimized table or approximate margin is needed. This resolves the specific correction threat; it does not claim a new line-by-line audit of every other external input in KLN.

## Reproducible low-height verification

Run from the repository root:

    .venv/bin/python hunts/oct08_extensions/audits/kln-restoration/check_low.py

The script uses python-flint's Acb zeta and Arb absolute-value enclosures, at 192-bit precision. There are 196608 cells, exactly

    [j/65536, (j+1)/65536],  j=0,...,196607.

Their midpoint (2j+1)/131072 and radius 1/131072 are dyadic and exactly represented. Cells include shared endpoints and cover [0,3] with no gaps. Each entire complex input ball is evaluated, not just its midpoint. Every resulting modulus enclosure is strictly below the exact rational 1.4604. This is a finite computation over a compact continuum using interval enclosures, and conjugation extends it to [-3,3]. It does not evaluate zeta at unbounded height; that part uses HPY's theorem.

The output in `check_low.txt` records the largest upper endpoint, 1.460357107222080230712890625, and positive slack above. An initial coarser exploratory mesh also bounded the function but did not give sufficient margin; an initial assertion using 1.461 failed, exposing the printed rounding gap. The final dyadic script contains the stronger bound and passes.

Residual scope: trust in Acb's enclosure implementation and in the cited HPY theorem is explicit. This bounded review has not independently re-proved HPY's full analytic proof or rebuilt its original computations. Previous seventh-power audit conclusions remain conditional on the stated 7/8 zero-free assumption; this correction adds no new hypothesis about zeta.
