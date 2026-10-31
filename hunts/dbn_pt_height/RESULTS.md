# RESULTS: hunt #147, `dbn_pt_height`

**Status: closed at landing, 2026-10-31. No claim promoted, no bound on Lambda
stated, nothing here bears on RH (`docs/08`).**

Written at landing by a session other than the lanes' author. Most of this
directory was written by an agent whose claims the owner asked to have
checked, so this file states only what the committed record supports, says
where the landing session re-checked a claim (section 7), and says where it
could not. The sources of the record are `CHAIN.md`, `REDUCTION.md`,
`chain.json`, `sources.json`, `evaluator/*.md`, the JSON and JSONL results in
`evaluator/`, and `RUNS.md`.

## 0. How to read this file

Every finding is one of two kinds, or a stated mix of both, and says which.

- **Read.** A statement found in a published or archived source, at a pinned
  version, graded as what that source shows. The lab did not check the
  mathematics behind it. `[Q:ID]` names a quotation in `chain.json`; its
  source's URL, SHA-256 and retrieval time are in `sources.json`. A digest is
  written `sha256:` and its first twelve hex digits.
- **Computed.** A number or a decision the lab produced, graded on the ladder:
  *measured* (one route, float grade), *hardened* (independent routes agree, or
  ball enclosures carry every step), *kernel-checked* (none here). A
  computation that uses a published lemma takes the lemma's status, and a
  composite takes the grade of its weakest step.

"CI" below means what runs where the private download cache is absent, which
is every CI runner (section 6). "Cache only" means a claim whose only check
skips there.

## 1. Dispositions of the questions in MISSION.md

The four words are those of `ALIGNMENT.md` section 5: refuted, obstructed,
unresolved (attempt unresolved), paused (paused by allocation).

| question | answer | disposition | grade |
|---|---|---|---|
| Q1. Was Polymath 15 Table 1 row 2's asymptotic-region hypothesis (Theorem 1.2 (ii)) verified over all N >= N0 anywhere, or only at N = N0? | Only at N = N0 = 630783 and y = y0 = 0.16733, in every source read (section 3). The one report of a sweep over N >= N0 is an unpublished 2024 blog comment by a reader outside the project, with no stated precision or y-range. | The published chain's step: **attempt unresolved**. Its cited source did not establish it, and nothing found suggests it is false, so it is not refuted. The lab's own attempt to close it, the evaluator's sweep: **paused by allocation**. It was gated on the Davenport-Heilbronn control and never launched; its cost is projected in `RUNS.md` E3, as estimates. | Read. The negative-existence parts are bounded by the searched set. Cache only. |
| Q2. What does the self-archived 0.1875 package reduce Lambda <= 3/16 to? | Polymath's criterion instantiated at X' = 6000000185827: the Platt-Trudgian height for (i), a barrier slab of its own for (iii), and for (ii) finite windows N in [690988, 2745000] through a banked lower bound, a tail device and a y-transfer lemma of its own (`REDUCTION.md`, part A, rows A0 to A7). The banked window bound is cited and not reproduced in the bundle: its producer ships, its run at those tiles does not [Q:Z8] [Q:Z10] [Q:Z24] [Q:Z27]. | Answered, as a reading. The 0.1875 claim itself is **unresolved** here: this hunt did not run the shipped producer, so it neither checked nor refuted the claim. | Read; cache only. The parameter identities (3/16, X'/2, its margin 350479773/2, N = 690988 on the slab) are computed, hardened, and run in CI. |
| Q3. Which of the 0.16 and 0.1595 rows depend on it? | Both, through the anchor b = 3/16, which is the 0.1875 package's assembly [Q:F5] [Q:G7] [Q:C3] [Q:C4]. The 0.172422 row, in version 1.1, which the catalogue cites, derives its own Lambda <= 0.2 anchor and depends on neither the 0.1875 reduction nor row 2 [Q:K4] [Q:K5]; its version 1 stated the published 0.2 as its anchor [Q:K1]. | Answered, as a reading. The rows' own claims are not adjudicated (unresolved here). An outside reader recorded the 0.1595 claim as refused on the evidence [Q:C9]; this hunt reports that and did not check it. | Read; cache only. |
| Q4. Which of the reduction's inputs are specific to zeta? | Two: the RH verification height (input 1) and the Euler-mollified lower bound to the right of the barrier (input 2) (`REDUCTION.md`, part D). Davenport-Heilbronn fails input 1: its zero 0.8085 + 85.699i lies in the region hypothesis (i) excludes. Input 2 has no DH analogue (DH has no Euler product) and was not tested. | Answered, as a reading plus the lab's analysis. Whether a rival also fails input 2 is **unresolved**: no DH analogue of the mollified bound exists, and the DH gate (section 4) does not reach it. | The inventory is read. The DH zero's position is computed, measured (mpmath, \|F_DH\| < 1e-20 at dps 40, agreeing with Spira 1994 as `zeta/epstein.py` records); runs in CI. |

Context for Q4, not a finding of this hunt: hunt #145 records a kernel-checked
theorem placing a zero of its Davenport-Heilbronn function off the critical
line below height 100 (`dh_separation_hundred`, pending external
verification). This hunt did not check that #145's function is the one pinned
in `zeta/epstein.py`, so the grade here stays measured.

## 2. Findings, graded, with sources

### 2a. Read in sources (the chain lane)

Every row here is cache only: on a CI runner its quotations are checked
against `chain.json`, not against the source (section 6). Row R10 was also
re-checked at landing against its hashed source, as was the project's barrier
log behind E4 (section 7).

| # | finding | source and locator | grade |
|---|---|---|---|
| R1 | Platt and Trudgian take Lambda <= 0.2 from Table 1 row 2, given their RH height 3000175332800. | arXiv 2004.09765 v1 TeX (sha256:c6c29099c943), lines 62, 144, 146 [Q:PT1] [Q:PT3] [Q:PT4] | read |
| R2 | Row 2's last column, 0.0376, is the Euler-2 bound at N = N0 and y = y0; the paper says the rest is expected to be verifiable. | Polymath 15 v2 `debruijn.tex` (sha256:560a28fe31be), lines 1950, 1965, 1994, 2002 [Q:P9] [Q:P10] [Q:P11] [Q:P12]; the same sentence in v1 (sha256:3f54d0a68bbe), line 2004 [Q:V1A] | read |
| R3 | No sweep at row 2's parameters exists at any commit of the project repository; the one sweep file starting at N = 630783 is at (t, y) = (0.17, 0.2). | `km-git-acc/dbn_upper_bound`, clone head `5fde84e`, all refs [Q:R5]; the expect-to-verify text entered the writeup at `4a460d9` [Q:R2] | read (a history search) |
| R4 | A project author wrote that the calculation at N0 alone is not quite enough and gave a heuristic reason for not verifying the rest. | issue #131, comment 483072037, 2019-04-15 (sha256:d52df1d593b4) [Q:I1] [Q:I10] | read |
| R5 | The only reported sweep over N >= N0 at row 2's parameters: a blog comment of 2024, unpublished code, no stated precision or y-range, the barrier's winding assumed. | tenth Polymath15 thread, comment-685281 (sha256:6fd3356790bc) [Q:B1] [Q:B12] [Q:B14] | read |
| R6 | Section 10 swaps the labels (ii) and (iii) of Theorem 1.2, in both arXiv versions; only labels move, the displayed regions are unambiguous. | v2 line 2002 [Q:P12] [Q:P13]; v1 line 2004 [Q:V1A] | read |
| R7 | Two unpublished 2018 points, (0.17, 0.2) at row 2's X and (0.18, 0.2) at X = 10^12 + 46880, have a barrier and a finite sweep at y = y0; their open steps are the y-direction and the region past the last swept N. | barrier commits `e8cd27b`, `97a8088` [Q:R7] [Q:R9]; sweeps [Q:R5] [Q:R11]; the tenth-thread results table, read once in an image reader and not re-readable by the test | read; the table entries are one reading |
| R8 | The 0.1875 package's finite-window leg consumes a banked bound that the bundle cites and does not reproduce. | Zenodo 21175533 archive (sha256:d6f76c7351a8), member `LWIN2_COMPOSE.md` (sha256:d10488fc5032), lines 124, 181 [Q:Z8] [Q:Z10] | read |
| R9 | The bundle attributes row 2's right region to a Polymath lemma-bound sweep that the Polymath record does not contain. | member `THEOREM_LAMBDA_CRITERION.md` (sha256:9a187fc6e27b), lines 126 to 127 [Q:Z11] | read |
| R10 | The 0.16 and 0.1595 rows are anchored at the 0.1875 row. | catalogue `constants/21a.md` at `46dbf03` (sha256:e8b198b124d2), lines 26, 27, 43 [Q:C3] [Q:C4] [Q:C2]; fork exports at `6baae4c` and `cc81078` [Q:F5] [Q:G7] | read; re-checked at landing (section 7) |
| R11 | The 0.172422 row's version 1.1 derives its own 0.2 anchor. | its TeX (sha256:cb79cfa1b9bd), lines 41, 92 [Q:K4] [Q:K5] | read |

### 2b. Computed by the lab (both lanes)

| # | finding | grade | pinned by, and where it runs |
|---|---|---|---|
| E1 | Row 2's arithmetic: t0 + y0^2/2 = 3999993289/20000000000 = 0.19999966445 <= 1/5; X/2 = 2500000097429, below the Platt-Trudgian height by 500175235371; floor(sqrt(x/(4 pi) + t/16)) = 630783 on the whole slab x in [X, X + 1], t in [0, 0.186]. | hardened (exact rationals; N by mpmath `iv` and Arb, which agree) | `test_chain.py`, CI; recomputed at landing (section 7) |
| E2 | The printed 0.0376 is reproduced as 0.037617, the Lemma 10.1 numerator, which bounds the Euler-2 mollified \|E_2 f_t\|; the bound it gives on \|f_t\| itself is 0.0292 (0.029195). Both are far above the error terms there (e_A + e_B + e_{C,0} near 1.03e-7). | enclosure-carrying evaluation of a published lemma used as published (not reviewed); reading the printed column as the numerator is a measured three-digit match in five rows plus the project's PARI source | `evaluator/test_effective.py`, CI (slow tier) |
| E3 | The evaluator's A + B - C balls contain 124 oracle values at x <= 2000 and 12 at large x; dropping e_C breaks containment at 7 of 60 grid points. | measured (the oracles are floating point) | `evaluator/test_effective.py`, CI |
| E4 | One rectangle [X, X + 1] x [y0, 1] winds 0 at t = 0.186 and at t = 0. One rectangle is not a barrier; the project's own log of the barrier [Q:R3] [Q:R4] is not re-graded. | enclosure-carrying given Theorem 1.3 and Corollary 6.4 as published, and at t = 0 the lab's unreviewed extension to t -> 0+ | `evaluator/test_effective.py`, CI (slow tier) |
| E5 | Observations about the source: Proposition 6.6(vi)'s printed bound fails just above small jumps (by a factor 1.02 to 1.15 at N = 4, 5, 6, 10); the step at line 1107 holds only for a >= 187; the printed Euler 5 value 0.0263 is reproduced by none of the variants tried. | measured | `evaluator/test_effective.py`, CI |
| E6 | The Davenport-Heilbronn gate, stages 1 and 2 (section 4). | enclosure-carrying given hunt #61's M2 derivation, its Phi_DH representation and kappa's functional equation, which this hunt did not review | `evaluator/test_dh_gate.py` pins both recorded runs and recomputes the development boxes, in CI; the gate runs are not repeated in CI |
| E7 | The DH zero 0.80851718... + 85.69934848...i: \|F_DH\| < 1e-20 at dps 40, in the region hypothesis (i) excludes at row 2 and at the 0.1875 site. | measured | `test_chain.py`, CI |

## 3. The gap in the published chain, stated exactly

This is a claim about other people's work, so it is stated at the strength
the evidence carries and no further.

**The claim.** In the published and archived record read for this hunt,
at the versions listed below, the asymptotic-region hypothesis of Polymath
15's Theorem 1.2 at Table 1 row 2 (X = 5e12 + 194858, t0 = 0.186,
y0 = 0.16733) is evaluated only at N = N0 = 630783 and y = y0. The paper says
the rest is expected to be verifiable [Q:P12]; a project author wrote in 2019
that it had not been verified carefully, with a heuristic reason [Q:I1]; and
the project repository holds no sweep at those parameters [Q:R5]. Platt and
Trudgian's Lambda <= 0.2 reads that row [Q:PT3], so their published chain
contains one step that its cited source did not carry out.

**What it does not say.** It does not say the hypothesis is false, that
Lambda > 0.2, or that Platt and Trudgian erred in a computation of their own:
their Theorem 1, the verification height, is not questioned. The margins
reported at N0 (0.0376 for \|E_2 f\|, 0.0292 for \|f\|, against error terms
near 1e-7) and the unpublished 2024 check point toward the hypothesis
holding. It does not say no verification exists anywhere: three sources that
could hold one were not read, namely the published Res. Math. Sci. text (a
client challenge blocked it), the published Bull. London Math. Soc. text of
Platt and Trudgian (closed access) and Broughan's book chapter (closed
access). Terence Tao, who led the project, wrote on his blog in 2020 that the
Platt-Trudgian height immediately improves the bound to 0.20 [Q:B9]; that is
the contrary-leaning record, and it adds no computation.

**Versions read** (retrieved 2026-10-21; URL, size and SHA-256 of each in
`sources.json`):

- arXiv 1904.12438 v1 and v2 e-prints, `debruijn.tex` sha256:3f54d0a68bbe and
  sha256:560a28fe31be; the arXiv comment calls v2 the final version with the
  referee's corrections [Q:ABS1];
- arXiv 2004.09765 v1, its only arXiv version, TeX sha256:c6c29099c943;
- `km-git-acc/dbn_upper_bound` cloned at `5fde84e` (all refs), its issue and
  pull-request list, and the comments of issues 81, 107, 113, 118, 126, 131;
- the Polymath wiki through dated Wayback snapshots (the live wiki returned
  404), and the empty GitHub wiki;
- the ninth, tenth and eleventh Polymath15 threads and the 2019 paper post,
  with their comments;
- the two 2019 referee reports linked from that post, read once in a PDF
  reader (not re-readable by the test).

**Grade.** A reading of those sources, with its negative-existence parts
bounded by them. Its source ties are cache only (section 6), last run on the
lanes' own machine; the landing session could not re-read the arXiv TeX,
because it had no cache and downloaded no papers. The observation is original
to this lab. It is not claimed novel: the search behind it was the newest 60
de Bruijn-Newman abstracts on arXiv and an author search, abstracts only
(`CHAIN.md`, section 4). `CLAUDE.md` routes such an observation to a public
GitHub issue; none was opened, and whether to raise it outside this repository
is the owner's decision. *Owner decision, 2026-10-31:* not raised outside this
repository for now. Its source ties are cache only and have not been re-run
on another machine.

## 4. The Davenport-Heilbronn gate: what it catches, and what rests on it

The gate asks whether the evaluator's barrier rule, run with DH's heat flow in
place of zeta's, refuses a box that holds a DH zero. Stage 1 was
preregistered (`evaluator/DH_GATE_PREREG.md`, commit 2ba8cbba3) and run on
2026-10-26 (`RUNS.md` E7). Stage 2 was preregistered at landing
(`evaluator/DH_GATE_PREREG_2.md`, commit de7cd593a) and run from that commit
(`RUNS.md` E8). Stage 1 is not changed or rerun.

| run | stage 1 (Z1 to Z4, C1, C2) | stage 2 (Z5, C3) | combined |
|---|---|---|---|
| clean | PASS | PASS | PASS |
| `one_corner` | FAIL, caught | FAIL | FAIL |
| `main_terms_only` | FAIL, caught | FAIL | FAIL |
| `no_margin` | PASS, not caught | **FAIL, caught** | FAIL |
| `no_M2` | PASS, not caught | PASS, not caught | PASS |
| `narrow_frame` | FAIL, caught | INCONCLUSIVE | FAIL |

**Why stage 1 could not see the margin faults.** A principal-argument count
goes wrong only where the zeros on one side of a segment subtend more than a
half turn. Every stage-1 box holds one zero, and Z1, the one box beside a close
pair, is centred on it, so its four-point mesh splits the pair's angle over two
segments, about 142.5 degrees each. `RUNS.md` E7's own reason ("|H| on the
boundary is far above any margin") is not the operative one: the clean rule
refined on Z1, Z3 and Z4, so the margin did bind (corrected in E8). Stage 2
centres a four-point segment over the pair, about 296 degrees, and
`no_margin` is caught there, as preregistered.

**Why `no_M2` stays uncaught.** Near an isolated zero or a close pair, H is
close to quadratic along a short segment, so the endpoint maximum of \|H'\|
already bounds \|H'\| on it and the dropped term M2 h/2 changes no decision. A
gate that checks outcomes on boxes the truth step can decide is not expected
to see it; a per-segment audit of the acceptance inequality would.

**Is the gate enough?** It is enough for what it shows: with the right H in
balls, the barrier rule refuses the five gate boxes that hold a DH zero and
decides the three zero-free controls, while a one-corner check (the row-2
pattern of `CHAIN.md`), a main-terms-only evaluation and a margin-free count
are caught. It is not enough, on its own, to license a zeta barrier or sweep:

1. it checks outcomes, not inequalities, so it cannot see `no_M2`;
2. it runs `dh_gate.dh_barrier`, a copy of the rule with DH's H and D, not
   `effective.barrier_rectangle`, so it tests the rule and not the zeta code
   path; for zeta the margin's soundness rests on `_audit_barrier` in
   `evaluator/test_effective.py`, which audits two rectangles at finitely many
   points;
3. it does not exercise Theorem 1.3's error terms (on DH, E = 0) or the
   Euler-mollified sweep, input 2 of `REDUCTION.md` part D, which is the step
   row 2 left open.

**What rests on it.** Nothing among this hunt's findings. No sweep, no
barrier and no Lambda statement was run under its licence, and the row-2
rectangles of E4 were computed on 2026-10-21, before the gate existed, so their
grade does not depend on it. Whether a later zeta sweep may proceed on this
gate plus `_audit_barrier`, or needs a per-segment audit and an error-term
control first, is the owner's decision.

## 5. Claims corrected at landing

Each correction is dated 2026-10-31 where it is made; the earlier text is left
on record where the file's convention keeps it.

1. The case-log status said the barrier rule refuses every box holding a DH
   zero. It refuses the gate boxes that hold one (four in stage 1, one in
   stage 2), which is all a finite gate can show.
2. `RUNS.md` E7 and a docstring in `evaluator/test_dh_gate.py` gave the margin
   faults' invisibility as \|H\| being far above any margin. The clean rule
   refined on Z1, Z3, Z4 and the development box D0, so the margin did bind;
   the operative reason is the geometry of section 4 (E8, and the docstring).
3. The case log, `CHAIN.md` and `REDUCTION.md` said every quotation is
   re-read from its hashed source by `test_chain.py`. That holds only where the
   download cache exists, which no CI runner has (section 6).
4. The two quotations of this repository's own `zeta/epstein.py` ([Q:L1],
   [Q:L2]) were skipped with the rest when the cache was absent, though they
   need no cache. They now run everywhere.

## 6. What CI checks, and what only the cache machine checks

The download cache (`<cache>/dbn/`) holds third-party documents, so it is not
committed, and no CI runner has it. Counts measured in the landing worktree
on 2026-10-31, without the cache, slow tests included:

- `test_chain.py`: 49 pass and 223 skip. Before landing, 43 passed and 225
  skipped. Of the six added runs, two are the [Q:L1] and [Q:L2] quotations,
  which no longer skip; three check the landing's dated notes; one checks this
  file's citations.
- `evaluator/`: 146 pass and 2 skip (the comparison with the project's
  barrier log, and the arXiv-source digest). Before landing, 143 passed; the
  three added pin stage 2 of the gate.

So 195 tests run in CI for this hunt and 225 skip there.

**What the skipped tests pin**, and so what is cache only: that each of 167
quotations occurs at its locator in the source whose SHA-256 is recorded; the
46 registered facts that read a source (comment authors, dates and parents,
commit dates, commit and issue counts, the outsider status of the 2024
commenter, the 2018 sweep minima); and ten history and bundle checks (the
cached digests, a planted misquote, the DOIs, the commit that introduced the
expect-to-verify sentence, the absence of a row-2 sweep at every commit, the
0.16733 string, the files naming the 2018 points, the absence of a run of the
banked window bound, the record's PDF, and the frozen anchor copy). Each skip
says so in its reason.

**What CI does check.** That the notes agree with the committed record: every
number in the notes occurs in `chain.json` or `sources.json`, every date and
named person sits inside a registered fact, every inline quotation is
verbatim in the recorded quotation text, every citation tag exists and sits
beside its fact, and the headline verdict and the dependency table are the
recorded ones. Also the stated arithmetic, the DH pin and the lexical rules.
`planted_faults.py`, run without the cache on 2026-10-31, had all 17 of its
planted prose edits refused, because each breaks agreement with `chain.json`.
What CI cannot see is a quotation in `chain.json` that is wrong about its
source, or an edit made consistently to a note and to `chain.json`.

**So:** every row of section 2a, and every date, name and count in `CHAIN.md`
and `REDUCTION.md`, is checked against its source only where the cache
exists. The last such run on record is the lanes' own (`RUNS.md` C3, 264
passed with the cache), by the author whose claims are under check; the
landing session could not repeat it and re-checked two sources by digest
instead (section 7). No paper text was added at landing; the quotations
already in `chain.json` are the lanes' own.

## 7. Spot-checks made at landing (2026-10-31)

- **Recomputed independently** (mpmath at 50 digits and exact rationals, not
  the hunt's code): N = floor(sqrt(x/(4 pi) + t/16)) = 630783 at all four
  corners of the slab x in [X, X + 1], t in {0, 0.186} (the expression is
  increasing in both); t0 + y0^2/2 = 3999993289/20000000000; X/2 =
  2500000097429 and its margin 500175235371; the 2018 points' 19/100 and 1/5
  and heights 2500000097429 and 500000023440; the 0.1875 site's 3/16, margin
  350479773/2 and N = 690988. All agree with the record.
- **Recomputed through the hunt's code:** the evaluator lane's tests, slow tier
  included, pass (section 6), among them the trib2 numerator 0.037617 and the
  t = 0 rectangle.
- **A source re-checked against its digest:** the catalogue file
  `constants/21a.md` at `46dbf03`, fetched from GitHub into an empty directory,
  has 6986 bytes and sha256:e8b198b124d2, as `sources.json` records, and its
  five quotations [Q:C1] [Q:C2] [Q:C3] [Q:C4] [Q:C12] are verbatim at their
  lines.
- **A second source:** the project's row-2 barrier log
  (`output/windingnumbers/windnum_nolemma_x5000000194858_y_0.16733_1_t_0_0.186.txt`
  at `5fde84e`), fetched the same way, has sha256:340617569529, the digest
  `evaluator/EVALUATOR.md` records, and [Q:R3] and [Q:R4] are verbatim at
  lines 4 and 442.
- **Not re-checked:** the arXiv TeX quotations, on which section 3 rests most
  (no paper was downloaded); the commit and issue counts (the GitHub API
  refused the request from this session).
- **Hunt number:** #147 is used by no other case-log entry or file on
  `origin/main` as of this landing.

## 8. Why there is no doors section

`CLAUDE.md` asks a hunt that measures a ceiling to end with its doors. This
hunt measures none. The chain lane audits a published argument; the evaluator
lane reproduces one printed number, winds one rectangle and runs a refusal
gate; no bound was optimized and nothing was driven until it stopped moving.
The re-optimisation of (t0, y0) at the Platt-Trudgian height was only costed
(`RUNS.md` E3(b)), never run. What would change the verdict is listed in
`CHAIN.md` section 5: a deposited or published sweep of row 2's right region
that this hunt missed, or a ball-arithmetic sweep with a y-direction argument
and a tail, either at row 2 or at one of the 2018 points.
