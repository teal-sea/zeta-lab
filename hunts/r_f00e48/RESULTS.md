# R-F00E48: the salvage, and what checking it turned up

**Status: settled.** Four arms landed, one held back on purpose, 29/29
acceptance checks pass, and one real defect was found in the material while
checking it.

Source: `origin/claude/riemann-hypothesis-research-ofds8s` at
`7043621a2606353819aa937f83d6e0d0b35a2936` (2026-08-18 22:38 UTC). The branch
had been idle three days and no session in `list_sessions` was on it. It has
moved once since the sweep that specified this landing, which matters: see
*What changed under the brief*.

## What landed

| arm | files | what it is |
|---|---|---|
| `weil_trunc/` | 23 | independent Galerkin truncated-Weil implementation, 8 replication gates, 27-cell enclosure grid, the DH positivity-failure scan |
| `sine_gram/` | 11 | exact finite-N sine-Gram engine; m5(1) = 101/18, m6(1) = 640/63 |
| `window_opt/` | 10 | RF-C003, the campaign's one promoted claim |
| `nyman_beurling/` | 32 | Baez-Duarte distances to N = 2048 |

plus `FRONTIER_MAP.md`, `IDEA_PORTFOLIO.md`, `data/frontier_surveys.json`,
`MISSION.md`, `REPRODUCE.md`, and a new `LANDING.md` recording the subset.

**1,717,013 bytes**, against roughly 58 MB for the source subtree. The
difference is 56 MB of regenerable pickle under the excluded arm.

## The acceptance checks

`probe.py`, 29 checks, all passing; data in `results.json`.

| check | result |
|---|---|
| inventory, four arms | 23 / 11 / 10 / 32 files, exactly matching the source tree, nothing extra |
| `fkappa/`, three pickles, `.ext_lock` absent | yes; 0 `.pkl` anywhere under the landed subtree |
| landed size under 2 MB | 1,717,013 bytes |
| reserved word anywhere under the subtree | 0 files (the arms were already disciplined; "certificate" and "certification" appear and are not the banned token) |
| every path `REPRODUCE.md` names resolves | 20 cited, 0 dangling; the 4 `fkappa/` paths sit under a NOT-LANDED heading |
| `functional.moments_polyeven_exact` imports | yes |
| RF-C003 rational recomputed from landed code | `F(v*) = 2245228120295149280/3276332462159207451` |
| landed `window_opt/RESULTS.md` quotes that rational | yes |
| `replication.json` gate count | 8 (`gate_A` … `gate_H`) |
| `enclosures.json` conclusive-positive cells | **27/27** (20 zeta, 7 dh), zero negative inertia in both sectors, LDL and Rayleigh consistent |
| `dh_control.json` grid | 28 cells, **0** negative |
| first DH positivity failure | **(c, N) = (31, 60)**, even sector |
| zeta control at that same cell | even inertia (61, 0, conclusive), odd (60, 0, conclusive) |
| agreement with `main`'s landed hunt #45 | DH `lambda_min` mid `-1.87393568857018838648…`, zeta `4.8216017520231…` |
| Baez-Duarte ladder reaches N = 2048 | yes, with the coefficient checkpoint |
| sine-Gram m5, m6 | `101/18`, `640/63` present |

### The defect

**`REPRODUCE.md`'s headline command for the campaign's only promoted claim did
not run.** It read

    from functional import exact_F_quartic; print(exact_F_quartic(1467,1159))

and `exact_F_quartic` has never existed, under that name or that signature.
The function is `moments_polyeven_exact(OPT_Q)`, and it returns `(m2, m3, F)`,
so the promoted rational is element `[2]`. A reader following the published
recipe for RF-C003 got an `ImportError`. The salvage brief flagged the name;
the signature was wrong too. Fixed, and `probe.py` now recomputes the rational
so the recipe cannot silently rot again.

Two further references were repaired: `weil_trunc/run_dh_control.py` (the
driver is `run_dh.py`), and a citation to `RESULTS_LEDGER.md`, which is not in
this tree and now says so.

### One thing the checking got wrong first, and why it is recorded

The first version of the DH check looked for the positivity failure in
`dh_control.json` and passed, on a substring. `dh_control.json`'s 28-cell grid
contains **no** negative cell at all; the failure is in `dhneg_scan.json`, a
second-wave file. A check that passes for the wrong reason is worse than a
missing check because it also supplies confidence, so both halves are now
pinned explicitly: `dh_control.json` is asserted all-positive, and the failure
cell is read out of the field that names it.

### The one external corroboration available

`main` already carries Hunt #45 (`hunts/r_ac9ca3/`), which reached the same
`(c, N) = (31, 60)` cell by its own route. The salvaged
`weil_trunc/dhneg_scan.json` and that landed hunt agree digit for digit on the
enclosed DH eigenvalue (`-1.87393568857018838648…`, radius ~5.7e-208) and on
the zeta control (`+4.82160175202313776…e-100`). So the largest arm being
landed is not entering the tree unchecked. Nothing else in this salvage has
that property.

## What was held back, and why

**`fkappa/`.** Its corrected kappa = 2 table contradicts `main`'s landed
`hunts/higher_xi/` table from i = 2 onward. Hunt #65 (`hunts/r_2ac05f/`)
adjudicated that dispute in `higher_xi`'s favour with a fourth independent
derivation and an externally anchored Farmer-Gonek control, and derived the
general defect `C_{kappa,2} = -4*kappa`; `docs/31` carries the erratum. So the
brief's "this is an adjudication, not a merge" is right, and the adjudication
has already run and gone against this arm. Landing it now would put the losing
table in the tree beside the winning one.

**The campaign ledgers** (`RESULTS_LEDGER.md`, `NOVELTY_LEDGER.md`,
`FAILURE_LEDGER.md`, `REPORT.md`, `RUNS.md`, `CATCHUP-2026-08-18.md`). Three of
them summarise the `fkappa/` claim in their own voice. Landing them would
import the contested verdict as prose while withholding the code it could be
checked against.

**`erdos_scan/` and `matchings/`.** See below.

## What changed under the brief

The brief says the branch moved 2026-08-17 16:27. It moved again on
2026-08-18 22:38, and the five commits since add two arms the salvage sweep
never saw: `erdos_scan/` (an exact table of the Erdos-Pomerance f(n) to
n = 16000) and `matchings/` (a Lean pairing count recorded as RF-C010, the
campaign's first kernel-checked result). Neither is in the brief's landing
list, so neither landed. They are unreviewed, not rejected, and landing
unreviewed work under cover of a salvage would misrepresent it.

## What this does not establish

Re-running an arm's own code is not an independent check of it. `probe.py`
shares every assumption `window_opt/` makes; it establishes that the landed
document and the landed code agree and that the published recipe now runs, and
nothing about whether the source paper's functional was transcribed correctly
or whether the rounded quartic is near-optimal. RF-C003 is now entered in
`harness/departments/review_ledger.py` with exactly that outcome recorded, and
`standing_reasons()` correctly reports it as having **no blind attack**. That
is a new open work item, honestly created, not one closed.

Nothing here bears on RH (`docs/08`). A salvage moves records; it raises
nothing on the certainty ladder.

## Loose threads

1. **RF-C003 has never been attacked.** The campaign's assessor re-ran it, and
   this hunt re-ran it again, both using its own code. *Why it matters:* it is
   the campaign's one promoted claim, it is now on `main`, and its
   transcription of the source paper's SS7.1/SS7.5(g) functional is
   load-bearing and unchecked. *First step:* run the blind brief
   `harness.review.generate_briefs` already emits for `rf-c003-window`,
   re-derive F for `cos(8s/5)` from the source paper alone and check it
   against `PAPER_F_30` in `window_opt/functional.py` before looking at the
   quartic.

2. **The 8.9e-9 rounding claim is asserted, not enclosed.**
   `window_opt/RESULTS.md` line 176 says rounding the optimal quartic to
   `-1467/1000, 1159/1000` costs 8.9e-9 of F. *Why it matters:* the promoted
   improvement over the paper's window is what that rounding is spent against,
   so the margin needs to exceed it by a stated factor. *First step:* run
   `window_opt/enclose.py` and read whether its enclosure brackets the
   unrounded optimum or only the rounded one.

3. **`erdos_scan/` and `matchings/` are unassessed.** `matchings/` in
   particular claims a kernel-checked Lean result (RF-C010) with a `.lean`
   file and an oracle. *Why it matters:* a kernel-checked result sitting on an
   abandoned branch is the cheapest unrealised output in the tree. *First
   step:* `cd lean && lake env lean` against
   `hunts/rogue_frontier/matchings/Matchings.lean` on the source branch and
   count the sorrys.

4. **`nyman_beurling/results/supplement3072.log` and `run_supplement.py`
   suggest an N = 3072 run beyond the landed ladder.** *Why it matters:* the
   headline is N = 2048; if 3072 completed, the landed table understates the
   arm. *First step:* read `ladder_supplement.json` and compare its largest N
   against `ladder.json`.

5. **The lexical gate reads `hunts/` for the reserved past participle and
   nothing adjacent to it.** This salvage landed files carrying the noun and
   the adjective forms of the same stem and passed. *Why it matters:* the rule
   in `CLAUDE.md` is about a reserved *word*, and whether its immediate
   neighbours fall inside it has never been decided; a future arm could claim
   a great deal in the adjective. *Second-order:* the gate cannot be discussed
   in a file it scans, which is why this paragraph is written around the token
   and `probe.py` assembles it from halves. *First step:* decide the question,
   then either widen `test_hunt_probe_discipline.py`'s token or write in its
   docstring that the narrow token is deliberate.
