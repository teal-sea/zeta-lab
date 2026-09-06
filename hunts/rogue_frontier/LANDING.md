# LANDING: what of this campaign is on `main`, and what is not

This hunt was worked on `claude/riemann-hypothesis-research-ofds8s` between
2026-08-17 and 2026-08-18 and never landed. Hunt R-F00E48 (2026-08-21) landed
part of it. **A reader of `main` is seeing a deliberate subset**, so this page
says which subset and why, rather than letting the gaps read as loss.

Source commit: `7043621a2606353819aa937f83d6e0d0b35a2936`
(`origin/claude/riemann-hypothesis-research-ofds8s`, 2026-08-18 22:38 UTC).

## Landed

| path | what it is |
|---|---|
| `weil_trunc/` | independent Galerkin implementation of the truncated Weil form, 8-gate replication, enclosure grid, and the campaign's first Davenport-Heilbronn control with a positivity-failure cell |
| `sine_gram/` | exact finite-N engine for the sine-Gram moments, with m5(1) = 101/18 and m6(1) = 640/63 |
| `window_opt/` | RF-C003, the campaign's one promoted claim, re-run independently by its assessor |
| `nyman_beurling/` | Baez-Duarte distances to N = 2048, against `main`'s previous N = 50 |
| `FRONTIER_MAP.md`, `IDEA_PORTFOLIO.md`, `data/frontier_surveys.json` | the survey the portfolio was scored from |
| `MISSION.md`, `REPRODUCE.md` | the charter and the reproduction steps |

## Not landed, and why

**`fkappa/`, held back on purpose.** Its corrected kappa = 2 table
contradicts `main`'s landed `hunts/higher_xi/` table from i = 2 onward, with a
conflicting diagnosis of the cause. Merging both would put two mutually
inconsistent tables in one tree and let whichever a reader met first pass for
settled. That is an **adjudication**, and an adjudication is somebody's
decision, not a cherry-pick's side effect. The arm is intact on the source
branch and the reproduction commands for it are preserved in `REPRODUCE.md`
under a NOT-LANDED heading. See also `docs/31`, which records an erratum to
Bian's Lemma 12 and is the other half of the same dispute.

**56 MB of pickle, and one lock.** `fkappa/c4cache_row3.pkl` (31 MB),
`c4cache_diag.pkl` (23 MB), `c4cache_row2.pkl` (2.2 MB) are regenerable
caches, and `fkappa/.ext_lock` is a stale coordination file from a run that
ended three days before this landing. None of them is evidence.

**The campaign ledgers**, `RESULTS_LEDGER.md`, `NOVELTY_LEDGER.md`,
`FAILURE_LEDGER.md`, `REPORT.md`, `RUNS.md`, `CATCHUP-2026-08-18.md`: stayed
behind because three of them summarise the unlanded `fkappa/` claim in their
own voice. Landing them would import the contested table's verdict as prose
while withholding the code that could be checked against it, which is the
worse half of both options. They are readable on the source branch.

**`erdos_scan/` and `matchings/`, landed 2026-08-28, after being recovered
from a force-push.** This entry previously said they were unreviewed. When
someone went to review them they were not on the branch at all: the source
commit this page cites, `7043621a` (2026-08-18 22:38 UTC), is not an ancestor
of the branch tip, which is `a19ac11` and dated **2026-08-17 16:27**, thirty
hours EARLIER. The branch was force-pushed backwards at some point after this
landing was written, and took both arms with it.

They were recovered by fetching the orphaned commit from the remote by SHA
while it was still unreachable-but-present, and pinned as
`origin/rescue/rogue-frontier-7043621a` so it cannot be collected. Anyone
reading this can check the recovery against that ref.

What was verified before landing, and what was not:

* `matchings/Matchings.lean`: 430 lines, **0** `sorry`, **0** `sorryAx`,
  **0** `axiom` declarations, 21 theorems. `RESULTS_LEDGER.md`'s claim of "no
  `native_decide` in any proof" was checked and holds: the single occurrence
  of that string in the file is inside a comment explaining that `decide` is
  used instead.
* The STATEMENT was checked against reality rather than taken on trust.
  `matchings/oracle.py` enumerates the count three independent ways and
  agrees; an independent brute-force enumeration of fixed-point-free
  involutions written for this landing agrees with both, and with `(n-1)!!`,
  for n = 0..10.
* **NOT verified: the proof was not recompiled.** No Lean toolchain is
  available in the environment that landed this, so the kernel-checked grade
  rests on the coordinator's recorded recompilation (EXIT=0, axioms
  `[propext, Classical.choice, Quot.sound]`), not on a fresh one. A run with
  `lake` should confirm it before the grade is cited anywhere outside this
  hunt.
* `erdos_scan/FINDINGS.md` is a feasibility survey and says so in its own
  second line, "Status: exploratory. Nothing here is a result." It lands as
  a survey, not as mathematics.

`matchings/` is not incidental: Hunt #48 (`hunts/r_8c3b94`) priced Erdos-Kac
in Lean and named this exact count at step A2c as something "Mathlib does not
have". That is a blocker in this tree, closed by a file that sat destroyed on
a rewound branch for ten days.

## What was corrected in flight

`REPRODUCE.md` carried three references that did not resolve:

1. `functional.exact_F_quartic(1467, 1159)`: no such symbol. The function is
   `moments_polyeven_exact(OPT_Q)`, and it returns `(m2, m3, F)`, so the
   headline rational is element `[2]`. The signature was wrong as well as the
   name; `hunts/r_f00e48/probe.py` recomputes the rational and pins it.
2. `weil_trunc/run_dh_control.py`: the driver is `run_dh.py`.
3. `RESULTS_LEDGER.md`, cited for the blinded verifier's outputs, is not in
   this tree (see above); the citation now says so.
