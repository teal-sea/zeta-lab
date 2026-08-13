# What the theorem prover actually changed about this result

Evidence for the `meta/` arm, written from the job history rather than
from impressions. This hunt ran **nine** submissions to Harmonic's
Aristotle service on 2026-08-12/13 (a tenth is still running), all on a
free tier with no payment method attached. The question this file
answers is narrow and it is not "was it useful": it is **which specific
properties of the result would be different if the prover had not been
in the loop.**

Written by the coordinator, who is a party to the comparison. The
`meta/` arm's own rule applies — a system may not resolve a disagreement
it is party to — so the accounting below is deliberately weighted toward
what the prover changed *against* the coordinator's intent, which is the
half a self-interested account would omit.

## 1. The submissions

| # | Target | Wall | Outcome |
|---|---|---|---|
| 1 | composition skeleton | 18 min | proved |
| 2 | grid-incidence law (LAW D) | 36 min | proved, **plus a counterexample to the brief** |
| 3 | census-LP floor certificate | 2 h 27 | proved |
| 4 | band-dual certificate | ~2 h | proved in part, **hypothesis carried explicitly** |
| 5 | pair-energy positivity | 1 h 44 | proved sharply, **two hypotheses dropped** |
| 6 | single-pair retention | 1 h 44 | partial, **obstruction named exactly** |
| 7 | truncation bridge | 1 h 26 | proved, **plus an unrequested fidelity check** |
| 8 | retention, retry | 1 h 43 | first all-n result, **better method than supplied** |
| 9 | retention, second retry | running | **refuted the brief's prescribed route** |

## 2. What changed *because* of the prover, itemised

**(a) It caught two errors in the coordinator's mathematics.**

- Submission 2: the brief's statement of the grid-incidence law was
  **false as written**. The prover did not silently repair it; it proved
  the corrected version and shipped `grid_incidence_needs_even`, an
  explicit counterexample (the indicator of `(0, 1/2]`, grid sum 0
  against `2π∫φ² = π`) establishing that the missing hypothesis is
  necessary. Every window this hunt uses is even, so nothing downstream
  moved — but the brief was wrong and would have stayed wrong.
- Submission 9: the brief prescribed a `C·y/s²` far-field bound,
  reasoning by analogy from a companion result. The prover's analysis
  said this **cannot hold**, because the underlying function jumps at
  the support edge. Checked numerically afterwards: `|Qim|·s` stays in
  0.13–0.30 over `s = 20…1600` while `|Qim|·s²` grows 5 → 220. The
  prover was right, the coordinator was wrong, and the coordinator's
  error was a repeat of an earlier one in this same hunt (conflating a
  function with its autocorrelation). **It refused the instruction and
  proposed a better route instead of proving what it was asked.**

**(b) It found better methods than the ones specified, three times.**

- Submission 2 replaced the brief's Poisson-summation route with a
  polarised Parseval identity on `ℝ/2πℤ` — which is why the theorem
  needs only *bounded and measurable*, with no smoothness, and therefore
  covers the jump-discontinuous windows this hunt actually uses. The
  brief's route would have needed regularity the windows do not have.
- Submission 8 replaced the brief's absolute far-field bound `C/s²` with
  a bound **measured against the slack**, `Qim² ≤ (3136/25)·Shq(y)/s²`.
  Its own summary states this is what makes the summation close.
- Submission 9's proposed route uses a near-field cancellation that
  submission 6 had discarded.

**(c) It minimised hypotheses the coordinator had assumed necessary.**
Submission 5 was asked for `k ≥ 1` and `y ∈ [0,1/2]`; it proved the
result for **all** `k` and **all real** depths and positions, and
recorded that the requested hypotheses were unnecessary. Submission 8
likewise dropped a depth restriction from the `n ≤ 3` case.

**(d) It named an obstruction precisely enough to be attacked.**
Submission 6's partial result stated the barrier as arithmetic: any
uniform damage bound `κ·Shq` caps at `n ≤ 2A/κ`, giving `n ≤ 3` at its
constants and `n ≤ 7` at the numerically optimal one. That single
sentence is what made submission 8 possible — and submission 8 produced
the first all-`n` theorem in the chain. **The diagnosis was worth more
than the theorem it came with.**

**(e) It checked our definitions against themselves, unasked.**
Submission 7 proved `c2_eq_autocorrelation` — that the closed form this
hunt had hand-derived for its kernel really is the autocorrelation it
was supposed to be — plus `integral_g` pinning the constant. Nobody
asked for this. It closes a defect class that had already bitten this
hunt twice by other routes.

**(f) It scoped honestly when it could not finish.** Submission 4 could
have hidden the unproved modelling step inside its arithmetic; instead
`band_dual_verdict` carries it as a named hypothesis `H3`. Submission 6
declined to reach past what it could prove and said so. Submission 9
committed in advance to falling back to the smallest separation its
constants support.

## 3. What it did *not* do, and what that cost

- **It did not notice prior art.** Submission 5's result is a corollary
  of two lemmas in the source paper, with the numerical specialisation
  printed in that paper's §7.5(a). The prover proved it cleanly and said
  nothing about novelty — correctly, since it was not asked. The
  coordinator then described it as research-grade in three places and
  had to retract. **The prover's silence was not a claim; the
  overclaim was entirely the coordinator's.**
- **It did not choose targets, notice irrelevance, or judge
  significance.** Every submission's subject was chosen by the
  coordinator, including one (submission 9) whose prescribed method was
  impossible.
- **It cost two full rebuilds to coordinator packaging errors** —
  submissions 4 and 9 were shipped without artifacts their briefs told
  them to reuse, so the service rebuilt them. In submission 4 that
  produced an accidental independent regeneration that closed with
  different-but-positive margins, which was luck, not design.

## 4. The counterfactual, stated plainly

Without the prover, this hunt would still have the numerical chain, the
rational certificates, the depth-uniform cover and the adversarial
searches — those were built here. What it would **not** have:

1. any kernel-checked step at all (there are now eight artifacts,
   ~7,000 lines, every declaration on `propext / Classical.choice /
   Quot.sound` and no `native_decide`);
2. a corrected grid-incidence law, with the necessity of its missing
   hypothesis exhibited;
3. an all-`n` retention theorem;
4. the knowledge that its own prescribed far-field route was impossible;
5. the exact arithmetic of the barrier that route was meant to cross.

Items 2, 4 and 5 are corrections and diagnoses, not proofs. On the
evidence of this hunt, **the prover's most valuable output was not the
theorems it proved but the three times it told the coordinator he was
wrong** — twice about mathematics, once about what a hypothesis was
doing. That is a claim about this hunt only, at n = 9 submissions, by a
party to the comparison, and it should be read as such.
