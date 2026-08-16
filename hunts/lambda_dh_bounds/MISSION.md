# MISSION: Two-sided bounds for the de Bruijn-Newman constant of the Davenport-Heilbronn function

**Opened 2026-08-16.** Nothing in this directory is a result until the case log
in `hunts/README.md` says how it ended. Everything here obeys the probe
discipline: the strongest words used are *measured*, *observed* and *decided*
(an enclosure with an exact sign or an exact integer count); the reserved
enclosure word belongs to `zeta/rigor.py` and appears nowhere in this
directory.

> **Frame note added 2026-08-16** (`GATE.md` closure item (a)). Nothing in
> the preregistration below is altered; this note only says which
> normalization its numbers are in, because the mission did not say and a
> `Lambda` number means nothing without it. The deformation defined below
> sits at `s = 1/2 + iz`, which is Stopple's published frame
> (arXiv:1301.3158). de Bruijn as usually quoted, Newman, Rodgers-Tao,
> Polymath 15 and Dobner all sit at `s = (1+iz)/2`, where the same constant
> is **four times larger**. So the pre-registered prediction P5,
> "0.0575 < Lambda_DH <= 0.400634", reads "0.2300 < Lambda_DH <= 1.602537"
> there. Conversion table, derivation and per-row numerical checks:
> `FRAME.md`.

## The question

`hunts/flow_repair/` (closed, 2026-08-07) measured the backward-heat repair
times of nine off-line quadruples of the Davenport-Heilbronn function and
closed with the sentence *"Nothing here bounds Lambda_DH from above"*. Its
floor, Lambda_DH >= 0.0576518, is float grade: one route, no enclosures.

This hunt upgrades that loose end to theorem grade on both sides. In the
normalisation flow_repair measured to be exact, with a_n the period-5
coefficients (1, kappa, -kappa, -1, 0),

    Phi_DH(u) = 4 e^{3u/2} sum_{n>=1} n a_n exp(-pi n^2 e^{2u} / 5),
    H_t(z)    = int_0^inf e^{t u^2} Phi_DH(u) cos(zu) du,   H_0 = Xi_DH,

and Lambda_DH := inf{t : H_t has only real zeros}, which is a well-defined
finite real number >= 0 by Dobner's theorem for the extended Selberg class
(arXiv:2005.05142, Theorems 1 and 2; the half-line structure {t : all zeros
real} = [Lambda_F, inf) is his Theorem 1).

> **What are the first quantitative two-sided bounds for Lambda_DH?**

Positioning, so the claim is neither over- nor under-stated: existence,
finiteness and Lambda_DH >= 0 are published (Dobner 2020, for all of S#).
Strict positivity is an immediate corollary of Dobner's half-line structure
plus any off-line zero (Davenport-Heilbronn 1936; computed by Spira 1994).
What is absent from the literature, per the novelty sweep recorded in
`NOVELTY.md`, is any *number*: no quantitative bound, upper or lower, for the
de Bruijn-Newman constant of any RH-violating L-function. The deliverable is
that number, from both sides.

## Work packages

> **Independence note added 2026-08-16** (`GATE.md` closure item (e)). The
> preregistration below is not altered; this note says what WP1's phrase
> "two independent winding routes" turned out to be worth, because the word
> *independent* was never measured when it was written. Measured with
> `harness/independence.py`, the two routes share the whole evaluator:
> independence radius 9 of 12 declared layers at the granularity of
> `independence_decl.py`, 8 of 11 at the gate's slightly coarser one, the
> same declaration either way. Their agreement is evidence about the two
> schemes that turn H-balls into an integer and about nothing else, and
> route 2 ran at one t and one box. The independence the claim rests on
> comes from two other legs, both landed here as runnable scripts:
> `crosscheck_dhflow_winding.py` (radius 0, N = 1 at **both** t) and
> `crosscheck_quadfree.py` (radius 0, one reconvergent layer, a different
> kappa equation). Layer lists, the two repaired validation gaps and what
> is still not covered: `INDEPENDENCE.md`.

- **WP1 (lower bound, decided).** At the pre-registered t1 = 0.0575 (stretch
  0.0576), an argument-principle count with every evaluation an Arb ball
  proves H_{t1} has a zero strictly off the real axis near the pair-5 site
  (centre Re z about 240.4165, the deepest measured quadruple). With Dobner's
  half-line structure this decides Lambda_DH > t1. Two independent winding
  routes: segment-argument tracking, and direct ball quadrature of H'/H.
- **WP2 (upper bound, cited theorem + decided strip).** de Bruijn 1950
  (Duke Math. J. 17, Theorem 13): if all zeros of H_0 lie in |Im z| <= Delta
  then H_t has only real zeros for t >= Delta^2 / 2. The exact statement and
  hypotheses are to be pinned from the original text and its restatements
  (Csordas-Norfolk-Varga 1988; Ki-Kim 2003) before use, and the
  strip-to-time factor Delta^2/2 is to be re-derived numerically in-tree
  (polynomial flow calibration), never recalled. The strip itself,
  |Im z| <= Delta = sigma_0 - 1/2 with sum_{n>=2} |a_n| n^{-sigma_0} = 1,
  is decided by directed-rounding interval arithmetic on both backends;
  scouted value sigma_0 = 1.39513615823511, giving Delta^2/2 = 0.400634.
- **WP3 (census, optional).** Screen heights above flow_repair's list for
  deeper quadruples; any pair landing later than 0.0576518 raises the floor.
- **WP4 (controls).** Lesion: a deliberately mis-centred or on-axis box must
  fail loudly or return undecided, never a wrong integer. Precision response:
  every enclosure must shrink when precision rises. Rival framing: the same
  pipeline pointed at zeta produces no positive floor (no off-line zero is
  known for zeta), so the number separates DH from zeta only through the
  already-known off-line zeros; this echoes flow_repair's P5 moral and claims
  nothing about RH.

## Pre-registered predictions

- P1: the winding count at t1 = 0.0575 over the pair-5 box decides N = 1 in
  the open upper half-plane box, on the first budget, with >= 30 digits of
  sign margin on every boundary segment.
- P2: the two winding routes agree exactly (both decide N = 1).
- P3: sigma_0 lands in [1.3949, 1.3954] on both backends and the two-backend
  intervals overlap.
- P4: no surveyed pair beats 0.0576518 below height 600 (flow_repair's data
  says depth, not height, drives landing times, and the strip caps depth).
- P5: the headline lands as 0.0575 < Lambda_DH <= 0.400634, a ratio of
  about 7 between the two sides.

## Scope

**This hunt may write**: `hunts/lambda_dh_bounds/`, `figures/`, one new
`docs/NN-*.md` if the run earns it, a case-log entry in `hunts/README.md`,
and a pinning test under `tests/` (precedent:
`tests/test_frontier_math_clean_kill.py`).

**This hunt may not write**: `zeta/`, `ontology/`, `harness/`, `lean/`, and
may not promote its own claim into `README.md`, `ROADMAP.md` or `HANDOFF.md`
as an established finding.

```huntspec
id: lambda_dh_bounds
question: What are the first quantitative two-sided bounds for the de Bruijn-Newman constant Lambda_DH of the Davenport-Heilbronn function?
frontier: lower 0.0576518 measured float-grade by flow_repair (nine quadruples, no enclosures), upper absent everywhere; Dobner 2020 gives existence, finiteness and Lambda_DH >= 0 with no numbers
proposed_attack: Arb ball argument-principle winding count at t1 = 0.0575 for the lower side; de Bruijn 1950 Theorem 13 with a directed-rounding zero-strip constant sigma_0 for the upper side
dead_routes:
  - reading an O(1) residue as an off-line zero without a completeness check (Hunt 2, withdrawn)
  - float-grade landing times as bounds (flow_repair already measured them; they decide nothing)
  - mp.diff on internally rounded functions (returns exactly 0, pinned by regression tests)
required_oracles:
  - Arb ball arithmetic winding counts that must enclose an exact integer
  - directed-rounding interval arithmetic on both in-tree backends for the strip constant
  - cross-route agreement between H_0 quadrature and zeta.epstein.completed_dh
  - published theorems cited with hypotheses checked (de Bruijn 1950, Dobner 2020)
kill_conditions:
  - the all-zeros-in-strip form of de Bruijn Theorem 13 cannot be confirmed from the original text or a reliable restatement, in which case the upper bound is withdrawn and the hunt reports the lower side alone
  - a winding enclosure fails to bracket an integer after the subdivision budget, in which case no lower-bound claim is made at that t
  - any enclosure that fails to shrink when working precision rises, which marks the instrument as the artifact
  - any source found to already bound Lambda_DH quantitatively, in which case the novelty claim is withdrawn and the delta restated against that source
agents_may:
  - build instruments inside this directory
  - run ball-arithmetic computations and record enclosures with their precisions
  - fetch and read the cited papers
  - write measured and decided values into RESULTS.md and results.json
agents_may_not:
  - modify zeta or ontology or harness or lean
  - use the reserved enclosure vocabulary of zeta/rigor.py anywhere in this directory
  - promote this hunt's claim into repo-level status files
  - treat a float measurement as a decided fact
```

## Vocabulary contract

Measured: one float route. Observed: a pattern in measured data. Decided: an
Arb or interval enclosure whose exact endpoints settle a sign or an integer
count, stated with backend and precision. The composite headline takes the
weakest grade of its steps and says so: the lower bound is decided modulo
Dobner's Theorem 1; the upper bound is a cited theorem applied to a decided
strip constant.
