# Research target: a compounding simple-zero bound

Recorded 2026-09-05. Continuation from `fd71337`.
Status: research proposal. No new correlation estimate, bootstrap theorem,
or route to 80% has been established.

## The target

Find a mechanism whose guaranteed gain grows as additional joint information
about zeros is retained, with the ambition of moving the unconditional
simple-on-critical-line proportion substantially toward 80%.

Another small improvement to a pressure constant does not meet this target.
The proposed direction is new arithmetic constraints on three-way and higher
correlations, or a global spectral estimate that consumes such information.
This is a research hypothesis, not a demonstrated advantage of higher moments.
Larger blocks containing the same pairwise inputs do not by themselves supply
new correlation information.

## Where the previous work stopped

- `575669f`: preserved the reversal minimax witness. This bounds an intermediate
  optimization problem; it does not improve the zeta proportion.
- `fd71337`: saved `counting_audit.py`, its tests and `counting_audit.json`.
  Retaining actual window incidences reduces a pressure overcharge.
- The existing four-point Lean instance gives approximately
  `0.6728470197666888`; the counting correction projects
  `0.6728525496941030`. These values are reproduced by the counting audit.
  The corrected analytic assembly has not been checked end to end in Lean.
- Finite Gram examples show that splitting into blocks can discard positive
  spectral defect. They do not establish a uniform positive gain, or a gain
  that grows with scale. The suggestion that this alone might compound toward
  80% was unsupported and is withdrawn.

The inherited base is
`H = 3/2 - cot(1/sqrt(2))/sqrt(2)`, approximately `0.6725007036794116`.
The target counts simple zeros on the critical line, with all nontrivial
zeros counted with multiplicity in the denominator. A distinct-zero bound
or a bound for zeros of xi-prime is a different quantity.

## Why repeating the current argument does not compound

Algebraic deductions from the displayed assembly follow. These have been
checked arithmetically in this session, but are not new Lean theorems.

Write `x` for the limiting simple-on-line fraction, `n` for local points,
`m` for block points, `c` for a valid local floor, and `p > 0` for the
pressure denominator. At the level of leading constants, the bridge gives

    x >= H - b + a*x,
    a = c*(m-n+1)/m,    0 < c*(m-n+1) <= 1,    b >= 0.

Its output `(H-b)/(1-a)` already sums that feedback. Iterating the same
inequality does not improve it. In particular,

    (H-b)/(1-a) <= H*m/(m-1).

At the current `m = 435`, even discarding the entire pressure penalty and
allowing the largest permitted `a` gives only
`435*H/434 = 0.674050244471299691`, or about `67.4050%`.
Since `m >= n`, the upper bound is at most `H*n/(n-1)`, tending back to
`H` as `n` grows. This obstruction applies to the capped assembly, including
the proposed counting correction. It does not cover arbitrary replacements.

There is also a proposed extension of the existing witness argument. Set
`k = n-1`, `t = m-k`. For the corrected formula,

    Phi_new - H = t/(m-c*t) * (H*c - k/p).

A witness with pair energy `W >= 0`, length `S <= k/H`, and
`c <= W + S/p` gives `H*c-k/p <= H*W`. The cap `c*t <= 1 <= k`
gives `0 < t/(m-c*t) <= 1`, hence `Phi_new <= H*(1+W)`.
This suggests that the old all-n witness envelope, about `0.67514251`,
also bounds the corrected capped family for `n >= 3`. It remains subject
to the original witness bounds and independent checking of this extension.
Do not describe it as a new kernel-checked ceiling.

## First research test on resumption

The first deliverable should be one explicit candidate inequality and a
test of whether it contains information absent from the existing pairwise
argument. A literature search and derivation are still required.

1. Identify a specific three-zero statistic, or higher spectral moment, that
   could strengthen the global defect bound. State its multiplicity weights,
   treatment of off-line conjugate pairs, and exact Fourier support.
2. Identify the prime-side estimate needed to control it unconditionally.
   Check primary literature before treating that estimate as available.
   If only a conditional estimate is known, name the extra hypothesis.
3. Test whether the resulting joint constraint excludes the periodic and
   mixed low-energy configurations already defeating the pressure family.
   A reformulation that accepts all the old adversaries has not yet earned
   an expectation of a substantial improvement.
4. Derive how the surviving gain depends on the amount of joint information
   retained. A proposed bootstrap must show why the next application adds
   information and why its hypotheses remain valid. Removing selected zeros
   does not automatically preserve the zeta explicit formula or correlations.

One possible interface is a new estimate `D/N >= f(x)`, where `D` is the
global spectral defect retained by the bridge, leading to `x >= H+f(x)`.
This is a proposed form, not an available theorem. To force `x >= 0.8`
through such an inequality, it must exclude every smaller feasible `x`;
evaluating a favorable example at `x = 0.8` is insufficient.

Before treating a measured effect as structural, use the relevant matched
surrogates and the Davenport-Heilbronn battery. Finite zeta data, random-matrix
agreement, and extra decimal precision cannot replace the missing uniform
estimate. Any claim about RH remains outside the scope of this target.

## Known traps and source trail

- The joint constraints obtained by taking many separate scalar window bounds
  collapse to their best member. See
  `hunts/wide_search/RESULTS-pair-ceiling.md`, section 1.
- The uncapped Gram-energy envelope already appears in AMTOPA's work.
  Do not reopen it as an original invention. See this hunt's `MAP.md` and
  `RESULTS.md`.
- `hunts/family_wall/RESULTS.md` and `FAMILY-LIMIT.md` contain the capped-family
  witnesses and their limitations. Read the correction and audit, not just
  the headline number.
- Do not call `0.68185` a verified universal ceiling on all possible methods.
  `hunts/wide_search/RESULTS-pair-ceiling.md` records the finite-law derivative
  error terms and the gap in the broader quantification.
- `hunts/outband_intake/RESULTS.md`, especially section 4, records an unresolved
  translation from a weighted form factor on complex differences to the
  proposed real pair-density constraints. Do not assume that bridge is valid.
- The primary paper [A new proof that more than 2/3 of the zeros of the Riemann
  zeta function are simple and on the critical line](https://arxiv.org/html/2609.02882v1),
  introduction and Remark 3.4, identifies the second-moment reduction and
  Montgomery-Taylor optimum for its method. It does not establish an upper
  bound on every higher-correlation approach.
- Exact current interfaces: `lean/bridge/Zeta23Ext/Bridge/S6.lean`, `S7.lean`,
  `S11.lean`, `S15.lean`, `Main.lean`, and `lean/bridge/FourPoint/Main.lean`.

No higher-correlation experiment has been run for this target. This note
preserves the proposed question and its first test; it does not launch a new
hunt or authorize publication, proof replacement, or a large compute run.
