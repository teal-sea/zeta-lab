# PRIOR_ART: what was searched before calling the rung-3 result original or novel

Hunt #145, searched 2026-10-26 with web search (four queries, one of them in the
thorough mode). The question: has anyone kernel-checked, formally verified, or
rigorously enclosed an off-line zero of the Davenport-Heilbronn function? The lab may
call its own work *original*, since this lab produced it. *Novel* is a claim about the
world, and it rests only on what this search found; an unsearched source can always
overturn it.

## Queries

1. "formal verification Lean Davenport-Heilbronn function zero off critical line" (thorough)
2. "arXiv Davenport-Heilbronn zeros off the critical line computed 85.699"
3. "Mathlib formalized Dirichlet series functional equation without Riemann hypothesis
   counterexample proof assistant"
4. "Davenport Heilbronn zero off critical line rigorous interval arithmetic ... verified
   computation" (one word of the query is elided here: it is the reserved word, which no
   file under `hunts/` may carry, even in quotation)

Not searched: zbMATH Open's own query interface, OEIS (no sequence is involved), the
Lean Zulip archive and the Isabelle and Coq/Rocq archives. These are the next sources
to check before any novelty claim goes beyond "searched-and-absent in the sources above".

## Found

- **The zero's location (numerical, not a proof).** Davenport and Heilbronn (1936)
  showed the function has zeros off the critical line. Potter and Titchmarsh (1934) gave
  early candidates by calculations they called inconclusive. Spira (1994) computed
  specific off-line zeros, and the lowest is near 0.808517 + 85.699348 i. Later papers
  repeat or refine that value:
  [arXiv:1703.02844](https://arxiv.org/pdf/1703.02844),
  [arXiv:2010.03521](https://arxiv.org/pdf/2010.03521) (Spira's four off-line zeros),
  [arXiv:2307.01254](https://arxiv.org/pdf/2307.01254) (0.8085171825 + 85.6993484854 i, by
  a counting argument). A 2015 note and a 2016 paper raise an ambiguity about the points
  symmetric to Spira's across the critical line
  ([arXiv:1503.05129](https://arxiv.org/pdf/1503.05129),
  [arXiv:1602.06328](https://arxiv.org/abs/1602.06328)). Balanzario and Sanchez-Ortiz,
  "Zeros of the Davenport-Heilbronn counterexample", Math. Comp. 76 (2007) 2045-2049
  ([AMS](https://www.ams.org/journals/mcom/2007-76-260/S0025-5718-07-01999-0/S0025-5718-07-01999-0.pdf)),
  also cited by `docs/29`, computed off-line zeros. This search did not read it closely
  enough to say whether its computation encloses a zero rigorously, so the claim below
  leaves room for it. None of the others is a rigorous enclosure or a formal proof.
- **Analytic results** on the function's zeros, all on the critical line and not about
  the off-line zero: Gritsenko, "On the zeros of the Davenport-Heilbronn function"
  ([Proc. Steklov Inst. 2017](https://link.springer.com/article/10.1134/S0081543817010060));
  related work in Chebyshevskii Sbornik ([mathnet](https://www.mathnet.ru/eng/cheb850)).
- **Lean and Mathlib.** Loeffler and Stoll formalized zeta and Dirichlet L-functions in
  Mathlib, including the functional equations, a statement of RH and Dirichlet's
  theorem ([arXiv:2503.00959](https://arxiv.org/pdf/2503.00959)); nothing about
  Davenport-Heilbronn. A 2026 paper formally verified in Lean 4 that at least two thirds of
  the zeta zeros are simple and on the line, and it names Davenport-Heilbronn only as a
  contrast case ([arXiv:2608.13637](https://arxiv.org/html/2608.13637v1)). A Lean project
  on critical-line zero proportions
  ([GitHub](https://github.com/lixiang90/RH-Zero-Proportion-Formalization)) is about zeta.
  A PhilPapers preprint works with Davenport-Heilbronn "frames" in core Lean but carries
  every analytic fact as a hypothesis
  ([PhilPapers](https://philpapers.org/archive/ISLAFC-2.pdf)).

## Absent

No source found states a kernel-checked or formally verified proof that the
Davenport-Heilbronn function (or any function with its Dirichlet series and functional
equation) has a non-trivial zero off the critical line, that is, one in the critical
strip. The qualifier matters: a zero off the line with no such restriction is already
formal, since Mathlib proves that the L-function of an odd Dirichlet character vanishes
at s = -1, and this tree's `lean/ZetaLean/DHTrivialZero.lean` applies that to `DH`
(added 2026-10-26, after the PR #353 review). Whether Balanzario and Sanchez-Ortiz (2007)
enclose one rigorously by hand-checked numerics is not assessed here. **Status: searched-and-absent in
the sources above. That is not a novelty claim.** The lab's own claim, if the full run
and the assembly succeed, is *original*: a kernel-checked theorem produced here. It is
stated as a delta against Spira (1994): the same zero, now enclosed in the closed square
of half-width 3/64 around 0.808517 + 85.699348 i and proved by the Lean kernel, rather
than located numerically.
