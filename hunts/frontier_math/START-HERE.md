# START HERE — the honest state of the frontier_math hunt

Written 2026-08-13 as a handoff, because the working record grew to **29
markdown files and 8131 lines** and buried the one thing that matters.
Read this file. Ignore the rest unless it is cited from here.

---

## 1. The objective

Improve the constant in *"More than two thirds of the zeros of the Riemann
zeta function lie on the critical line"* (10 Aug 2026).

    paper:  0.6725007037

## 2. Have we improved it?  **No.**

    reading of record:  0.6725087070    (+8.00e-6)   — a CANDIDATE

It is a candidate, not a result. It is contingent on a chain with at
least one **open quantifier** and **nothing kernel-checked**. An earlier,
larger candidate from this same programme (`0.672529`, later `0.6725124`)
was **killed by this project's own controls** — see `PROOF-LEDGER.md`
line 24, "CLEAN KILL". That is the base rate to keep in mind.

A second figure, `0.6725106958` (+9.99e-6), appears in the ledger. It is
**not** the reading of record: it waits on a burden that has not landed,
and the record was deliberately revised *downward* to `0.6725087070`.

**Distance to a clear win, honestly:** one open research question (below),
plus a Lean build that has never been run because no container in this
session had a toolchain. The research question has no schedule.

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
* **Everything in Lean.** O9 is sized twice (344 cells 1-D here; **389
  leaves 2-D** by `lab-rejection-philosophy`, whose route is better
  because it needs no unproved depth-reduction lemma). Nothing compiled.

## 5. What to ignore

Most of the 29 markdown files are working record, not input. If you read
four, read: this file, `RETENTION-PROBLEM.md` (the prover-facing
statement), `O9-SCOPING.md` (the better O9 route), `ACTIVE-CLAIMS.md`
(who else is editing this directory).

`PROOF-LEDGER.md` is ~2000 lines and is a *defect record*, not a plan.
Five coordinator defects (#19-#23) were logged in one session, all the
same shape: a quantity carried across contexts without being re-derived
in the context it was used. That record is worth keeping and is not worth
reading end to end.

## 6. The one next action

Get a container with **elan + Lean 4 `v4.33.0-rc2`** and network access to
`github.com/anthropics/zeta-23-lean` @ `3635e74`. Then build the 2-D O9
table by `o9_scoping`'s route and run `lake build`. Every Road A
obligation is staged and none has ever been compiled; one build converts
a pile of staged work into a list of what actually fails.

`k >= 2` is a separate, open-ended research effort and should not be
sequenced behind that.

## 7. What went wrong in the session that produced this

Stated plainly so it is not repeated: the bottom line — *we have not moved
the constant* — was never surfaced in one place. It was true throughout
and buried under working record. A large share of the session went into
correcting my own errors and re-sizing the same table three times. The
markdown sprawl is self-inflicted. This file exists to replace it.
