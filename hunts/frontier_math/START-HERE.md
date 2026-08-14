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
* **The Lean root does not load.** See §4b.

## 4b. What the first Lean build found (2026-08-14)

Until this date no session in this hunt had a toolchain, so `zeta23ext` had
**never been compiled**. It did not build.

* **Seven modules failed**, in three cascading layers (each reachable only
  once the layer before it compiled): `EForm2/{Bridge,Estimates}`,
  `EForm3/Numerics`, `TruncEst/{Kernel,Decay,Autocorrelation}`,
  `RetentionWired`. All seven were Mathlib drift, not mathematics, and all
  seven are now fixed. `EForm3/Numerics` is on the `k = 1` chain.
* **`RetentionWired.margin_identity` was carrying a `sorryAx`** induced by
  its own build error. Nobody wrote a `sorry`; the failed proof supplied one.
  The tree now reports zero.
* **The root still does not load, and not because of drift.**
  `Zeta23Ext.lean` imports both arms and both define `Retention.Aconst` and
  `Retention.c2` (`EForm/Basic.lean` over `gker` with `u - w`;
  `EForm3/Defs.lean` over `g` with `u + w`). Deciding which arm owns those
  names is an architecture call, not a rename — ~200 references each, across
  four arms — and it is left to whoever holds `zeta23ext/` assembly.
* **The `k = 1` retention chain does build**, as a target rather than through
  the root: `lake build Zeta23Ext.EForm3.{Master,Main,Refutation}
  Zeta23Ext.RetentionWired Zeta23Ext.BandCert.Main` → 0 errors, 0 `sorryAx`.
* **O9 is now a two-variable table needing no depth-reduction lemma**
  (`o9_leaf2d.py`, 1939 leaves, depth 20, 0 undecided), and **the kernel
  accepts it**: all 49 `decide +kernel` chunks pass, `O9Check2.lean` builds
  in 211 s, axioms `[propext]` only. That makes the *numeric* content of O9
  kernel-checked over the whole rectangle. Of the two membership lemmas that
  are the seam to `Dam`, **O9a (`shfnIv_mem`) is proved** and **O9b
  (`o9Field_mem`) is not**, with no `sorry` standing in — so the kernel has
  checked a table and not yet an inequality about the damage.
* **A caveat that was load-bearing turned out to be false.** Both O9 tables
  predicted the kernel's verdict using Arb leaves, on the claim that Arb and
  `Leaves.lean` "agree to well under `2^-60`". They do not, on wide cells —
  Arb encloses by range, Lean evaluates a Taylor interval and doubles twice.
  The first 2-D table was rejected by `decide +kernel` on 14 of 15 chunks.
  `o9_leaf2d.py` now mirrors Lean's algorithms bit-for-bit;
  **`o9_leaf.py` still does not, and its 344 has never met the kernel.**

Build cost, for whoever plans the next one: Mathlib cache ~8 GB,
`BandCert/Verify.lean` alone takes **640 s**, peak RSS ~9.4 GB.

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

*Superseded 2026-08-14 — the build has now been run; see §4b. What it asked
for is done, and the list of what actually fails is above.*

The next action is now **the `Retention.Aconst` / `Retention.c2` collision**,
because until it is resolved the root module cannot load and no amount of
staged work can be checked through it. That is an architecture decision, not
a rename.

After it: prove O9a/O9b (the two membership lemmas for the 2-D table), and
re-cost `o9_leaf.py` against the kernel rather than against Arb.

`k >= 2` is a separate, open-ended research effort and should not be
sequenced behind any of that.

## 7. What went wrong in the session that produced this

Stated plainly so it is not repeated: the bottom line — *we have not moved
the constant* — was never surfaced in one place. It was true throughout
and buried under working record. A large share of the session went into
correcting my own errors and re-sizing the same table three times. The
markdown sprawl is self-inflicted. This file exists to replace it.
