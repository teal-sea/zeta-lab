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

### 3. His reply of 2026-09-14

The laboratory's account of what came of his mail went out on 2026-09-14
and he answered the same afternoon. Three things in the answer bear on this
tree; the rest is recorded in the operator's vault.

- **A second literature watch exists.** He found Wang's paper because C.A.T.
  searches arXiv hourly and notifies him, and he offered to have it email
  the operator as well. That is an outside feed with a measured hit that
  this tree's own monitor (`meta/literature-monitor.md`, weekday mornings)
  did not have. Whether to accept it is the operator's decision and is not
  taken here; it is noted as a door the monitor's brief did not list.
- **A guard of the same shape as ours.** He reports that assistant-written
  Lean repeatedly drops or reintroduces the imaginary part of a real
  quantity, and that he now runs a Lean AST walker that bans specific
  patterns and keywords before anything executes. This tree's lexical tests
  under `hunts/` are the same idea applied to prose. Neither is evidence
  for the other; the convergence is worth a line.
- **Palomar.** He has no GitHub account and asked whether the registry
  accepts submissions from other people with attribution, and for
  procedural help. Not answered here and not this hunt's to answer.

### 4. The repository walkthrough, 2026-09-14

Later the same day he sent C.A.T.'s walkthrough of this public repository.
Its account of `hunts/higher_xi` was checked against the tree and is
accurate: the `xi'''/xi''` identity and the rational `Q(z)` are where it
says, and its "N=3 jet" typing, `U + d/ds log(U^2 + U')`, is that hunt's
identity restated, already checked symbolically by `resummed_bridge.py`.
The message attaches a 920-line audit note and a solver script, both read
in full. The note is more careful than the covering email: its own ledger
marks the proposed link between this tree's jet and the correspondent's
"DVJ" object as open, and says a match on dimension or Jordan form alone
should be rejected. The overlap it establishes is that a second-order
Taylor jet has three coefficients, which is true of every smooth function.
The headline claim, that this tree contains the basis of de Vries'
formula for the fine-structure constant, has no counterpart here: nothing
in this repository concerns a physical constant. The solver was run once
in this tree's venv; its root gives 1/alpha = 137.035999096, inside the
CODATA 2018 uncertainty and about four standard deviations from CODATA
2022. The operator's reply says the laboratory will not assess it.
Recorded so that a later reader who finds the claim quoted elsewhere
knows it was seen, read, and where the line was drawn.

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

His 2026-09-14 reply adds three more claims, recorded as his and unchecked:
that Erkki Brandas has peer-reviewed work carrying the same information loss
under squaring; that he has derived c, mu_0 and Z_0 from first principles by
a method that turns out to use eigenvalues of underlying matrices; and that
the ten operators arise as a C2 over a conjugate pair giving C4, rotated by
45 degrees to C4 x C4, with four further rotations. He puts the number of
people who understand the loss at between one and about ten.

Recording what was not used is part of the credit, not a qualification of it.
The two things above are real, and this laboratory is better off for both.

## The correspondence itself

Held in the operator's mail, thread "Zeta Lab: a hello for Thomas", beginning
2026-09-08. It is not reproduced here: it is a private exchange with a member
of the public, and the technical content that mattered is stated above in the
laboratory's own words.
