# START HERE — the honest state of the frontier_math hunt

Written 2026-08-13 as a handoff, because the working record grew to **29
markdown files and 8131 lines** and buried the one thing that matters.
Read this file. Ignore the rest unless it is cited from here.

**Corrected 2026-08-14**, because a page that exists to carry the one
number that matters carried the wrong one. See the correction box in §2.

---

## 1. The objective

Improve the constant in *"More than two thirds of the zeros of the Riemann
zeta function lie on the critical line"* (10 Aug 2026).

    paper:  0.6725007037

## 2. Have we improved it?  **Not proved. A candidate.**

    reading of record:  0.6725106958    (+9.99e-6), a CANDIDATE

It is a candidate, not a result: one step of the chain is open, so the
composite takes that grade. An earlier, larger candidate from this same
programme (`0.672529`, later `0.6725124`) was **killed by this project's
own controls**, see `PROOF-LEDGER.md` line 24, "CLEAN KILL". That is the
base rate to keep in mind.

> **Correction, 2026-08-14.** The first version of this page named
> `0.6725087070` (+8.00e-6) as the reading of record, and said the higher
> figure "waits on a burden that has not landed". That was the ledger
> state at `PROOF-LEDGER.md` line 438, and it had already been superseded
> when this page was written. Burden (a), the chain re-run at the paper
> field, is delivered in the section beginning line 449, and line 462
> records **"Reading of record | MOVES to 0.6725106958"**; lines 529,
> 574, 593, 609 and 660 hold it there. `README.md`, `docs/27` and the
> public site carried the right number and this page did not. It is the
> same shape as coordinator defect #23, logged two screens further down
> in the same ledger: a superseded figure carried past its own
> retraction, by a session reading one row instead of the last row.

Four pieces of the chain **are** kernel-checked and none of them is in
§3 below: the census floor (`FloorCert.lean`), the retention
certificate's arithmetic (`BandCert`), the composition inequality
(`t3_composition_skeleton.lean`) and the grid-incidence law
(`law_d_incidence.lean`). Statements and obligations in `docs/27` §2.

**Distance to a clear win, honestly:** one open research question (§4).
The Lean gap this page listed beside it has closed since: the arm was
built for the first time on 2026-08-13, it refuted the O9 leaf table on
7 of 9 chunks, and the repaired 699-cell table now decides at kernel
grade on all 18. The research question still has no schedule.

## 3. What is actually solid

Grade **hardened** = measured many ways with controls that have power;
**not** kernel-checked. Nothing below is kernel-checked.

1. **The `k = 1` retention inequality**, for every `n`, every shift, every
   depth in `[0,1/2]`, **with no separation hypothesis**. Four independent
   instruments agree, plus an exact-rational certificate and a
   from-definitions reproduction (`salvage_audit.py`, 7/7).
   This is the real result of the session.
2. **`ghat(z) = Phi2(-i z)`** — the `BandCert` and `EForm3` arms compute
   one function. Residual exactly `0.0`. Puts 7 of 12 Road A obligations
   on machinery that already compiles.
3. **The `k`-pair identity** (residual `4.21e-17`) and its three-term Gram
   form, two of whose three terms are free.
4. **`int D(y,s) ds = -2 pi c2(0)`**, exact and depth-free.

## 4. What is open

* **`k >= 2` (blocker 2 proper).** THE research question. All four of its
  named sub-worries were measured and none binds — unbounded crowding,
  decaying budget, the counting question, shared-`R`. What is missing is
  a *proof*, and there is no route with a schedule.
* **O9 soundness, the last step.** No longer "nothing compiled": the
  table decides at kernel grade across all 18 chunks, and the seam
  lemmas landed through `O9Sound`/`O9Assemble`, both modes included.
  What is left is bridging the two denominator forms, `qreIv_mem` at
  `c*c + d*d` against `rIv_mem` at `c*c + dOverY*dOverY`, which differ
  by `y^2`. No `sorry` stands in for it. Read `O9-LEAF-REPAIR.md` §5-§6,
  not the cell counts in `O9-2D-STATUS.md` §1, which are the Arb-model
  figures the kernel refuted.

## 5. What to ignore

Most of the 29 markdown files are working record, not input. If you read
five, read: this file, `RETENTION-PROBLEM.md` (the prover-facing
statement), `O9-SCOPING.md` (the O9 route), `O9-LEAF-REPAIR.md` (what the
kernel did to it, and the current cell counts), `ACTIVE-CLAIMS.md`
(who else is editing this directory).

`PROOF-LEDGER.md` is ~2000 lines and is a *defect record*, not a plan.
Five coordinator defects (#19-#23) were logged in one session, all the
same shape: a quantity carried across contexts without being re-derived
in the context it was used. That record is worth keeping and is not worth
reading end to end.

## 6. The one next action

**Superseded, and worth reading for why.** This page originally said:
get a container with elan + Lean 4 `v4.33.0-rc2`, build the 2-D O9 table
and run `lake build`, because "one build converts a pile of staged work
into a list of what actually fails". That happened on 2026-08-13 and the
list was short and expensive: `decide +kernel` refuted the table on 7 of
9 chunks. The generator computed its transcendental leaves with Arb at
300 bits and a 4-ulp pad while `Leaves.lean` builds them from truncated
series, so the model was narrower than the kernel and the correction cost
roughly a factor of two in cells, 339 to 699. The prediction to keep is
the general one in `O9-LEAF-REPAIR.md` §2: *a generator with no
round-trip against the thing it claims to mirror can only ever confirm
itself.*

The next action now is the denominator bridge in §4, and after it the
`Dam y s <= c*y^2` statement O9 exists to support.

`k >= 2` is a separate, open-ended research effort and should not be
sequenced behind that.

## 7. What went wrong in the session that produced this

Stated plainly so it is not repeated: the bottom line — *we have not moved
the constant* — was never surfaced in one place. It was true throughout
and buried under working record. A large share of the session went into
correcting my own errors and re-sizing the same table three times. The
markdown sprawl is self-inflicted. This file exists to replace it.
