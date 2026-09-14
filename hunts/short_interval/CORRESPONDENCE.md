# The outside contribution that opened this hunt

**Recorded 2026-09-14.** A record of unsolicited correspondence from a member
of the public, and of what came of it. It lives in this hunt's directory
because this hunt exists because of it. Nothing here is a mathematical result.

## Who

**Luke Kenneth Casson Leighton**, working with an instance of ChatGPT he calls
C.A.T., writing from `gitlab.com/d12rg`. He reached the laboratory through the
contact form on `zeta.teal-sea.com` on 2026-09-08, having read the published
account of the withdrawn zero-proportion candidates. He had no prior
connection to this laboratory and was not asked to write.

## What he contributed, in two parts

### 1. The generalization of the `blockpos` failure, 2026-09-08

The laboratory had already killed the `0.672529` candidate and published the
mechanism: the construction used `u u*` where the pinned upstream zero side
uses `u u^T`, an off-line pair is the hyperbolic block `2m(xx^T - yy^T)`, and
an exact Gaussian-integer witness gives `tr(P1 Q') = -2`
(`hunts/frontier_math/CLEAN-KILL-REPORT.md`).

Leighton wrote to say he had hit the same structural failure repeatedly in
independent work, and to state the rule he had adopted for it:

> Do not square, Hermitianize, or pass to a positive quadratic object until
> the signed/oriented carrier has been fully accounted for.

with the observation that `x -> x^2`, `T -> T T*` and `u u^T -> u u*` can each
quotient out exactly the sign, orientation, conjugation or phase datum on
which the intended theorem still depends, and that `Re(B^2)` and `|B|^2` are
materially different invariants because the second has positivity built in.

C.A.T. then broadened it, in a second message the same week, to what it named
**premature non-faithful reduction**: a proof carries a signed or oriented
object `T` and replaces it too early by some `F(T)` for which
`F(T_1) = F(T_2)` although `T_1 != T_2` on the datum needed downstream. The
repair rule is the same one: retain a faithful polarized or operator-valued
carrier until every sign-, phase-, conjugation- or orientation-sensitive
statement has been discharged, and scalarize only afterward.

The message also reported that the two of them had caught themselves making
the same mistake again, in their own work, days after writing. That is the
part that makes the rule worth recording rather than merely agreeing with.

**Status in this tree.** The specific kill was already recorded and
kernel-checked. What was missing, and what this record adds, is the general
form of the hazard and the credit for stating it. It is entered in
`harness/departments/review_ledger.py` as an outside attack outcome on
`blockpos-0.672529`, and the graveyard's recurrence guard for that entry now
names the general rule rather than only the transpose-for-adjoint swap.

The laboratory's own experience since is consistent with it. `MISSION.md` §5
measures that the window-shape optimization is worth `lambda^3/180`, which is
a statement about a quotient being nearly faithful; and hunt #118's closure
of the out-of-band route turns on an orientation fact, that a real even
spectral profile's autocorrelation is strictly positive just inside its
support edge and the lemma is false for odd factors. Neither was derived from
Leighton's rule, and neither is evidence for it. They are recorded here
because a rule that never touches the work is not a rule.

### 2. Wang's short-interval paper, 2026-09-12

On 2026-09-12 Leighton forwarded a note from C.A.T. observing that the
constant in Biao Wang's arXiv:2609.07918 looked familiar, because `c(1)` is
the Montgomery-Taylor constant.

That observation is the paper's own first sentence and is not a finding. **The
paper was.** It had posted on 2026-09-07 and nothing in this tree had seen it.
It is the short-interval form of the theorem every Palomar entry this
laboratory holds is built on, and it reached the laboratory five days late
through an unsolicited email rather than through any mechanism here.

Everything in this hunt follows from that: the reading that the laboratory's
own bandwidth landscape and Wang's interval exponent are the same parameter
(§3), the three routes and their closures, the gate on the `xi'` arm and the
proof draft, and, in `meta/literature-monitor.md`, the standing literature
watch the laboratory did not have. The incident is recorded in
`meta/interventions.jsonl` as an intervention caught by an outsider, with the
missing capability named.

## What was not adopted, stated plainly

Leighton's larger programme, a ten-by-ten Verlinde or generalized-Chebyshev
hypergroup operator basis, presented as the setting in which sin and cos
retain information that is lost in the usual basis, was not evaluated here and
nothing in this tree rests on it. He also asserted a connection between the
`3/2` in Wang's formula and Lucas-Chebyshev criteria, Dixon trace polynomials,
an RCFT modular torus and a golden-spiral holonomy condition. No such
connection was checked, and this record neither endorses nor refutes it. His
repositories are `gitlab.com/d12rg/d12rg_riemann`,
`gitlab.com/d12rg/d12rg_hypergroup` and `gitlab.com/d12rg/d12rg-hypergroup-lean`.

Recording what was not used is part of the credit, not a qualification of it.
The two things above are real, and this laboratory is better off for both.

## The correspondence itself

Held in the operator's mail, thread "Zeta Lab: a hello for Thomas", beginning
2026-09-08. It is not reproduced here: it is a private exchange with a member
of the public, and the technical content that mattered is stated above in the
laboratory's own words.
