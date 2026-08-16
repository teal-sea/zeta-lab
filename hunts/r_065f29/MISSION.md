# R-065F29 — the white-box attack on `urms2-0.51`

## The question

`harness.review.standing_reasons` returns, for the claim `urms2-0.51` in
`harness/departments/review_ledger.py`:

> claim 'urms2-0.51' has no recorded white-box attack: the review is not
> standing until one runs

The blind attack landed on 2026-08-15 (hunt R-FB9C81, recorded in commit
d09bdba). The white-box attack is the other half of the standing-review
specification: it sees everything the author saw, including
`author_reasoning`, and hunts the eight named failure modes in
`harness.review.WHITEBOX_CHECKLIST`.

This hunt runs that attack and records its outcome where the question came
from. It does not judge the claim: `meta/operator-functions.md`'s load-bearing
guard applies, so an `AttackOutcome` records what the attacker found and the
resolution stays with the operator.

## What this hunt may touch

`hunts/r_065f29/` only, plus the two exceptions the brief grants: one case-log
line in `hunts/README.md`, and one appended `AttackOutcome` in
`harness/departments/review_ledger.py`. It reads `hunts/higher_xi/` and does
not write there.

```huntspec
id: r-065f29
question: does a white-box attack on the URMS2-051 claim, seeing the author's reasoning and hunting the recorded checklist, find a fault that survives checking
frontier: the blind attack of 2026-08-15 found no structural failure in the RC2 off-diagonal error bounds; no white-box attack had run, so standing_reasons still listed the claim
dead_routes:
  - re-running the blind attack's angle on the Montgomery-Vaughan arithmetic conditions, already covered by R-FB9C81
  - attacking delta_n inverse bounded by 2n, which is elementary and holds for every n at least 1
  - attacking the n equals 1 spacing term, absorbed in the same absolute constant
  - hunting an empty upper range in the finite control, ruled out: the array runs to exp(ell) while x is exp(0.51 ell)
required_oracles:
  - exact rational arithmetic in the fractions module over the recorded margin system
  - direct evaluation of the block second moment as a double sum against the closed-form sharp-block kernel
  - a mutation applied to the layer two allegedly independent routes share, checked for identical response
  - the second-moment law measured directly on the coefficient family the record's own control runs on
kill_conditions:
  - the attack reports a fault it cannot exhibit as a rerunnable number
  - a claimed non-independence is contradicted by the two routes diverging under mutation
  - the block second moment fails to saturate as W passes U, which would make the finding an instrument defect rather than a result
agents_may:
  - read every file in hunts/higher_xi and the harness review machinery
  - compute exactly and numerically, and report what the numbers say
  - record an AttackOutcome naming what was found, including nothing
agents_may_not:
  - edit hunts/higher_xi, meta, lean, or any root markdown file
  - withdraw the claim on its own authority
  - describe a re-derivation of the same numbers as an independent check
proposed_attack: sweep the recorded rational witness for bindingness at 51/100; mutate the shared tail majorant and test whether the audit's independent route diverges; evaluate the block second moment where the old proof forbade it; measure whether the record's own control family satisfies the hypothesis of the step it is offered as evidence for
```
