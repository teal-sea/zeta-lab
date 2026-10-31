# DH_LITERATURE: is there an effective approximation for the Davenport-Heilbronn heat flow?

Searched 2026-10-26, before any DH correction term was written (DH.md, step 3).
The question: is there a published Riemann-Siegel-type or other effective
approximation, **with explicit error terms**, for H_t^DH, or for DH itself as
c L(s, chi) + conj(c) L(s, conj chi) with chi mod 5?

## Queries and what they returned

Web search (standard mode), 2026-10-26. Hits are listed as the search returned
them; "read" means more than the abstract or snippet was read, and almost
nothing was.

| query | relevant hits | what they settle |
|---|---|---|
| Riemann-Siegel formula Dirichlet L-functions explicit error term | Hiary, *An alternative to Riemann-Siegel type formulas*, arXiv:1403.0317 (Math. Comp. 85 (2016), no. 298); Arb's `acb_dirichlet` documentation; a Proc. Japan Acad. note correcting an earlier L-function RS formula | Hiary (snippet, introduction): for the Riemann-Siegel type formulas for L(1/2+it, chi) of Davies, Deuring, Lavrik and others, "it does not seem that we have an analogue of Gabcke's explicit estimate for the remainder terms", nor an easy a posteriori estimate. Arb's explicit RS bound (Arias de Reyna, Theorem 4.2) covers zeta only. |
| Davenport-Heilbronn function zeros computation Riemann-Siegel type formula | Gonek-Ivic and Balanzario-type DH papers; Gritsenko, *On the zeros of the Davenport-Heilbronn function* (Trudy MIAN 296, 2017); Zetafast, arXiv:1703.01414 | no RS formula for DH specifically. Balanzario and Sanchez-Ortiz compute DH's off-line zeros by deforming a series with known zeros, not with an RS formula. |
| de Bruijn-Newman constant Davenport-Heilbronn heat flow effective approximation | Polymath 15 (arXiv:1904.12438), Rodgers-Tao, the Wikipedia entry | every effective heat-flow approximation found is zeta's (Polymath 15). |
| Rubinstein smoothed approximate functional equation incomplete gamma | Booker et al., *Computing L-functions: a survey* (JTNB, doi 10.5802/jtnb.920); Johansson, arXiv:2110.10583; Rubinstein's method restated in arXiv:1211.4181 | the smoothed approximate functional equation: L-values as rapidly converging sums of incomplete gamma functions, exact up to truncation, with a free complex parameter that controls cancellation. **This is what step 3 uses.** |
| Siegel 1943, *Contributions to the theory of the Dirichlet L-series and the Epstein zeta-functions* | the citation only (Ann. of Math. 44 (1943), 143-172, doi 10.2307/1968761) | not read; its role in L-function RS formulas is not confirmed by the hits. |
| Davies 1965, approximate functional equation for Dirichlet L-functions | D. Davies, Proc. Roy. Soc. A 284 (1965), 224-236, doi 10.1098/rspa.1965.0060, through Hiary's description | an RS-type formula for L(s, chi), with no explicit remainder bound (Hiary). |
| Balanzario Sanchez-Ortiz 2007 | Math. Comp. 76 (2007), no. 260, 2045-2049 | off-line zeros by deformation, as above. |
| Dobner arXiv:2005.05142 | Acta Arith. 201 (2021), 29-62 | Lambda_F >= 0 for the extended Selberg class, so DH has a de Bruijn-Newman constant (hunt #61 uses this). No approximation. |

Hunt #61's own search record (`hunts/lambda_dh_bounds/NOVELTY.md`, "Searches
run", 2026-08-15 to 2026-08-18) covers the de Bruijn-Newman side in depth:
ANTEDB chapter 18 and a three-index forward-citation sweep of Dobner. It
found no heat-flow computation attached to DH, and its note is not repeated
here.

## Conclusion, at the level of the search

- **No published effective approximation of H_t^DH was found**, and no
  Riemann-Siegel formula for DH or for L(s, chi) mod 5 with an explicit
  remainder. One such source would have been the analogue of Polymath's
  Theorem 1.3. Hiary (2016) states the gap for L-functions in general.
- **What can be used:** Rubinstein's smoothed approximate functional equation.
  It is exact up to a truncation that can be bounded, and its two sums play the
  roles of Polymath's A and B. The correction C is then the difference between
  the sharp sums and the smoothed ones (DH.md, step 3). Hunt #61's ball
  instruments (`instrument.H_ball`, `winding.second_derivative_bound`,
  `winding.winding_rectangle`) enclose H_t^DH directly and are reused for t > 0
  and as ground truth.
- **Not searched:** MathSciNet and zbMATH (no access from this session), and
  the full texts of Davies, Deuring and Lavrik. A remainder bound may be
  hidden in one of them. Hiary's statement is the evidence against it, not a
  proof of absence.

Spira's DH zeros used by the gate (0.650830 + 114.163343i,
0.574356 + 166.479306i, 0.724258 + 176.702461i, besides the pinned
0.808517 + 85.699348i) were recalled from Spira (Math. Comp. 63 (1994),
747-748; the citation is `zeta.epstein`'s). Each was then located here with
mpmath's findroot on F. It moved by at most 6e-7 from the recalled digits
(measured, 2026-10-26).
