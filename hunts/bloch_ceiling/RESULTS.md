# Results: where the variable-radius Bloch certificate ends

> Bounded outcome of Hunt #80. Labels: VERIFIED means run here and compared against the
> archive's published record; MEASURED means computed here with no published counterpart
> to compare against, so it is a number this hunt owns rather than one it checked;
> REPORTED means stated by the paper or the archive and not re-established; INFERRED
> means a float search or a float LP value with no interval enclosure. Nothing here
> audits the paper's hand proofs (Bonk's theorem, the moment inequality, the three-atom
> reduction, the centre-placement lemma).

## 1. The published verification reproduces

Archive `bloch-computations-1.0.0.zip` (Zenodo `10.5281/zenodo.21975862`), sha256
`bdaa1ff3…408e7` verified, all 28 entries of `CHECKSUMS.sha256` verified. Pinned
environment as documented (`python-flint` 0.9.0, `numpy` 2.5.1, `scipy` 1.18.0, CPython
3.12). Every statistic the archive publishes in `expected-output/verification.md`, and the
two it publishes in `src/VARIABLE_RADIUS_FINDINGS.md`, was reproduced both locally and in
a Modal container (`compare_expected.py`, 22 of 22 match):

| program | statistic | expected | observed | status |
|---|---|---|---|---|
| `certify_bloch.py certificates.npz` | (A) `|a_3| <=` | 3.28877762819 | 3.28877762819 | VERIFIED |
| | (B) `Phi(-1,0) - sqrt3/4 >=` | 0.0149407644273 | 0.0149407644273 | VERIFIED |
| | (C) `B - sqrt3/4 >=` | 0.0114402996202 | 0.0114402996202 | VERIFIED |
| | (C) `B >=` | 0.444453001512 | 0.444453001512 | VERIFIED |
| | displayed-minorant margin | -5.756e-8 | -5.756091347e-8 | VERIFIED |
| | `min_theta R >=` | 0.41491575 | 0.41491575 | VERIFIED |
| `certify_bloch.py certificates_coarse.npz` | (A) | 3.29102479849 | 3.29102479849 | VERIFIED |
| | (B) | 0.0150346379669 | 0.0150346379669 | VERIFIED |
| | (C) gain, `B >=` | 0.0113729923988, 0.444385694291 | same | VERIFIED |
| | `min_theta R >=` | 0.41480041 | 0.41480041 | VERIFIED |
| `certify_fixed_radius_ceiling.py` | `Phi_even - sqrt3/4 <=` | 0.01519720970909415 | 0.01519720970909415 (53302 boxes, 33051 terminal) | VERIFIED |
| `variable_radius_certificate.py verify --mesh 20` | uniform positivity margin | +0.000936855231 | +0.000936855231 | VERIFIED |
| | near moment slope margin | 0.03317907018 | 0.0331790701855 | VERIFIED |
| | near centre `|c| <=`, `min R` | 0.136904745959, 0.436558987993 | same | VERIFIED |
| | near moment gain | 0.0153040536989472 | 0.0153040536989472 | VERIFIED |
| | 20x20 mesh away minimum | 0.015866072532 (sectors 6, 18) | 0.015866072531958 | VERIFIED |
| | finer rotated-antipodal boundary minimum | 0.015648602353 | not produced by any archived command | REPORTED, see §4 |

Wall times: the four programs take 0.3 s, 0.3 s, 3.5 s and 52 s locally; 0.7 s, 0.4 s,
8.9 s and 112 s on one Modal core.

**The 24 away sectors.** Not reproduced by the commands above, which are the
sub-minute ones. The archive records them in `reference-run/logs/`, 23 as fresh
runs and sector 0 as a checkpoint resume, at a combined 105.6 core-hours. Two of
those counts are reproduced exactly at the published target in section 5
(sectors 0 and 1: 270,744 and 292,931, to the integer), and all 24 sectors are
run there at a *higher* target. The other 22 counts at `0.0153` itself remain
REPORTED.

## 2. The functional and its parameters

The theorem's gain is `min(near, away)` over a dichotomy in `|a_3|`:

    near(eta, R) = Phi_R(-1,0) - sqrt(3)/4, one integral cut at radius R, valid
                   only while point cuts prove Re f > 0 on 1/sqrt(3) <= |z| <= R
                   for |a_2| <= 1, |a_3| <= eta  (Arb, the author's machinery);
    away(eta)    = min over the 24 phase sectors, balanced three-atom measures
                   and the polyhedral coefficient body with |a_3| >= eta of the
                   47-cut envelope of Phi_{r0}, minus sqrt(3)/4.

Free parameters: `ETA = 0.70` (the one round number; `src/variable_radius_certificate.py:30`),
`LARGE_RAD = 0.5815218918243517` (a search output), `POINT_BOXES = 16` and
`POINT_SUBDIV = 32` (the positivity certificate's resolution), and the target.
`C = 3.2888` and the row grid/K are shared with the fixed-radius certificates and were
not moved.

**What each parameter is worth, measured with the author's own code** (every `near` value
below is his LP search plus his Arb verification, run here; every `R_acc` is his
`verify_positivity` accepting that radius with re-searched point cuts; every `away` value
is a float LP minimum, INFERRED):

- **The radius is limited by the node count, not by positivity.** The accepted radius at
  `eta = 0.70` is 0.581664 with the shipped 16-node layout (margin +7.3e-6; the shipped
  0.5815218918243517 leaves +0.000937 unused), 0.581836 with 32 nodes, and the float zero
  of the point-cut value sits at 0.582095. A cut evaluated half a node step from its
  anchor loses ~0.0029 of margin (measured), which is 20x the whole shipped margin scale:
  the node count is load-bearing at the 1e-5 level of the final constant.
- **The near gain buys ~0.045 per unit radius**: `d near / dR ~ 0.045`, so the dense-node
  limit at `eta = 0.70` is `near = 0.015331`, only 2.7e-5 above the published certificate.
- **`eta` trades the branches at ~2.2e-3 per unit**: lowering `eta` raises the admissible
  radius by ~0.0086 per unit of `eta` (hence `near` by ~3.9e-4 per unit), and lowers the
  away floor by ~2.2e-3 per unit.

| eta | R accepted (16 nodes) | near (Arb) | R accepted (32 nodes) | near (Arb) | R float zero | near there (Arb) | away floor (float) | binding |
|---|---|---|---|---|---|---|---|---|
| 0.40 | 0.584285 | 0.015422244 | | | 0.584982 | ~0.015444 | 0.015100427 | away |
| 0.50 | 0.583340 | 0.015384932 | 0.583598 | 0.015396040 | 0.583950 | ~0.015408 | 0.015238824 | away |
| 0.55 | 0.582867 | 0.015366186 | | | 0.583450 | ~0.015390 | 0.015316485 | away |
| 0.60 | 0.582437 | 0.015347624 | 0.582695 | 0.015358444 | 0.582968 | ~0.015371 | 0.015427191 | near |
| 0.65 | 0.582051 | 0.015329841 | | | 0.582525 | ~0.015352 | 0.015537896 | near |
| **0.70** | 0.581664 | 0.015310272 | 0.581836 | **0.015317984** | 0.582095 | 0.015331135 | **0.015648602** | **near** |
| 0.75 | 0.581277 | 0.015290567 | | | 0.581675 | ~0.015311 | 0.015759308 | near |
| 0.80 | 0.580891 | 0.015269847 | | | 0.581263 | ~0.015291 | 0.015870014 | near |

(`artifacts/floor-sweep.json`, `artifacts/local/near-gain-at-accepted-radii.txt`,
`artifacts/local/near-gain-sweep.txt`. The float positivity zeros and away floors are
INFERRED; each `R accepted` and each `near` is an Arb-verified certificate at that point.)

The away floor here is the minimum over the **rotated antipodal pairs** `(tau, tau+pi)`,
the `v = 1` edge of the author's `(u, v)` rectangle. At `eta = 0.70` this scan gives
0.015648602, which is exactly the paper's "finer rotated-antipodal boundary minimum
0.015648602353" - reproduced here from an LP the archive does not ship (the archived
`verify --mesh` skips that edge; its 20x20 interior mesh and 24 sector-centre antipodal
LPs give 0.015866..., which this hunt also matches). The away branch's true relaxation
minimum is on that edge in every sector examined.

## 2a. Where the published run sits

At the published constants the branches are far from balanced: `near = 0.0153040536989`
against `away ~ 0.0156486`. The whole certificate is pinned by the near branch, 4.05e-6
above its round target, and the away branch idles 3.4e-4 above it. The certificate is
**not** at the floor of its own dichotomy; it is at the floor of the near branch at
`eta = 0.70` with 16 nodes and the shipped radius.


## 3. Soundness read of the verifier

The verifier separates float search from Arb verification and, unlike the zeta
seven-point verifier of Hunt #79, carries **no prune whose justification encodes the
target**: the away subdivision discards a box only against `goal = sqrt(3)/4 + target`
with the target a run parameter, and the near branch aborts unless its Arb gain exceeds
the same parameter (`variable_radius_certificate.py:380-381`). The findings, none of which
overturns the published run:

1. **Duplicated constants with no cross-check (latent).** The dichotomy threshold and the
   larger radius live in three places each: the source constants
   (`variable_radius_certificate.py:30-31`), the stored data (`eta`, `large_rad`,
   `point_edges[-1]` in `variable_radius_certificate.npz`), and the two verification
   routines read *different* copies: `verify_positivity` uses the source `LARGE_RAD`
   (lines 218, 227) while `verify_near_moment` integrates to the data's `large_rad` (line
   257); `verify`/`rigorous` use the source `ETA` (lines 346, 379, 390) and ignore the
   data's `eta`. Nothing asserts they agree. If the data were regenerated with one
   constant changed and the source not edited (exactly what Gohms did to the zeta
   verifier's target), positivity could silently be checked on a shorter annulus than the
   integral uses. As shipped all copies are bit-identical (checked), so this is latent,
   not load-bearing. The paper's sentence "the symbols r1 and eta denote the same binary64
   values stored with the certificate data" is enforced by no code path.
2. **`C = 3.2888` encodes another certificate's result, unasserted (load-bearing,
   justified elsewhere).** Every away cut, halfspace and box penalty uses
   `C = 3.2888` (`variable_radius_certificate.py:100`, `multicut_certificate.py:118`,
   default at `variable_radius_certificate.py:288`), valid because the *fine* fixed-radius
   certificate proves `|a_3| <= 3.28877762819 < 3.2888`. The variable-radius programs
   never check this; `verify_all.py` establishes it only by running `certify_bloch.py
   certificates.npz` first. A standalone `rigorous --sector J` run trusts the stored
   number. Note the coarse certificate the away cuts are *searched* from proves only
   `|a_3| <= 3.29102479849 > 3.2888` - the justification deliberately crosses
   certificates, and only the driver script closes the loop.
3. **One binary64 comparison inside the rigorous loop (formal, 5e-17).** `branch_verify`
   compares Arb lower bounds against `goal = SQRT3_4 + target` computed in binary64
   (`multicut_certificate.py:479`), and `float(sqrt(3)/4 + 0.0153)` sits 4.5e-17 *below*
   the exact value. What an accepted sector literally proves is therefore
   `> sqrt(3)/4 + 0.0153 - 4.5e-17`. Same pattern, opposite sign of harm, in the target
   itself (`float(0.0153) < 153/10000` by 6e-22). Swamped by the 4.05e-6 near margin;
   reported for completeness. The fix is one line (round the goal up in Arb).
4. **The documented reproduction command cannot reproduce the run (reproducibility, not
   soundness).** `verify_all.py --all` runs the away sectors at the argparse default
   `--max-boxes 200000` (`variable_radius_certificate.py:434`), and `branch_verify`
   *refuses* (`RIGOROUS INCOMPLETE`) when the open frontier reaches that cap
   (`multicut_certificate.py:531`). The reference logs peak above 200,000 open boxes in
   eight sectors (4, 5, 6, 15, 16, 17, 18, 19; maximum 280,593 in sector 17), so the
   README command stops short on those. Demonstrated mechanically by the control run
   (below). The reference run itself used undocumented larger caps: logs 4, 5 and 6 show
   a first attempt dying at exactly `open=200001` and a resumed attempt sailing past
   200,000, and logs 15-19 never hit any cap. The cap refuses rather than accepts, so
   soundness is untouched.
5. **Sector 0's archived log is not a fresh run (provenance).** `reference-run/logs/0.log`
   records a checkpoint *resume* with 0 boxes of work (elapsed 00:00:00.019); the fresh
   sector-0 computation is the one run this archive documents but does not contain. This
   hunt's fresh sector-0 run lands on the same 270,744 terminal boxes, closing the gap.
6. **Checked and clean.** The `j == 0` one-ulp extension of the first positivity interval
   below the binary64 value of `1/sqrt(3)` is present (line 226); the subinterval balls
   over-cover their intervals because python-flint rounds the radius up to mag precision;
   the point-objective tail matches the closed form of `(e/2) sum_(k>K) (k+2) r^k`; the
   `region_min` vertex logic and the second-order Taylor bounds of
   `certify_fixed_radius_ceiling.py` (checked term by term against the derivatives of
   `(1-t)^2 |P|^2`) are sound; the two regression assertions in `certify_bloch.py` (lines
   173, 210) quote published outputs but fail loudly in the sound direction; the resume
   path discards checkpointed boxes only when their stored bound clears the *current*
   goal, and a weaker-target checkpoint is refused outright (lines 491-499).

## 4. The variable-radius ceiling, which the author did not compute

**INFERRED** (the near side of each bracket is an Arb certificate; the away side is a
float LP minimum; no rigorous away subdivision was run at the crossing):

Balancing the two branches by moving `eta` down and the radius up to its admissible
maximum gives the ceiling of the dichotomy with the author's cut families, row grid and
K:

| positivity layout | crossing | ceiling of min(near, away) |
|---|---|---|
| 16 nodes (as shipped) | eta ~ 0.569 | ~ 0.015359 |
| 32 nodes | eta ~ 0.573 | ~ 0.015368 |
| dense-node limit | eta ~ 0.578 | ~ 0.015378 |

    variable-radius ceiling  ~  sqrt(3)/4 + 0.01538        INFERRED

against the author's rigorous fixed-radius ceiling 0.01519720970909415 and his published
0.0153. Reading: the variable radius buys at most ~1.8e-4 over the fixed-radius cap with
these cuts, the published constant extracts about 59% of that (0.0153040 - 0.0151972 =
1.07e-4), and **no tuning of ETA, LARGE_RAD, the node counts or the target reaches
0.0154** with the author's relaxation. The remaining lever is the relaxation itself
(rows, K, more cut anchors): the paper's own reconnaissance puts the fixed-radius dual
gap at ~4e-5, so even a perfect LP at this K and grid moves the ceiling by at most a few
1e-5.

What would make the ceiling rigorous: (i) the near side already is, at every tabulated
point (the author's `verify_positivity` + `verify_near_moment` at the accepted radius);
(ii) the away side needs the author's own sector subdivision run at target T at the
crossing eta, which certifies `away > T` - the same machinery as the reproduction, at a
cost that diverges as T approaches the float floor. The bracket delivered by the runs
here: the away branch at `eta = 0.70` is rigorously above 0.015316 (section 5) and, by the
float boundary scan, below 0.0156487; the ceiling of the dichotomy lies in
[0.015316 accepted, ~0.015378 float] with the binding constraint switching from near to
away at eta ~ 0.57.

## 5. A higher target, accepted by the author's own verifier

**The author's own verifier accepts `sqrt(3)/4 + 0.0153040536`.** Every one of
the 24 away sectors, all 1600 initial cells of each, at a target `4.0536e-6`
above the paper's published `0.0153`, with **no cell refused anywhere**. The
near branch clears the same target on the shipped certificate data, in Arb, at
the head of every shard. Nothing about the certificate data was changed: only
the acceptance threshold moved.

    target accepted by his verifier, run here   0.0153040536
    target published in the paper               0.0153
    the near branch's rigorous cap              0.0153040536989472

**This is a statement about the finite certificate, not about Bloch's
constant.** What the paper turns an accepted target into is `B >= sqrt(3)/4 +
target`, and that step is Bonk's theorem, the moment inequality, the three-atom
reduction and the centre-placement lemma, none of which this hunt audits. What
is established here is exactly what the header claims: his verifier, unmodified,
on his data, accepts a larger number than he published.

**And that is the end of the road for the shipped data.** The near branch's own
Arb gain is `0.0153040536989472`, a rigorous lower bound (`verify_near_moment`
returns `float_lower` of its ball), and the dichotomy's gain is
`min(near, away)`. So `0.0153040536989472` is not merely the target that was
reached, it is the supremum of the targets this certificate can support without
regenerating a single stored number. The published `0.0153` was leaving
`4.05e-6` of its own certificate unclaimed, and there is nothing else there.

### Why this target

The dichotomy's gain is `min(near, away)` and the near branch caps it. On the
shipped `variable_radius_certificate.npz`, the author's own routines give a
uniform positivity margin `+0.000936855231` and a near gain
`0.0153040536989472`, re-established at the head of every shard in this run and
identical every time. The away branch, whose float floor sits at `0.0156486`
(section 2), is the part that has to be paid for: 24 phase sectors, each an
adaptive Arb subdivision of the author's `(u, v)` rectangle from a 40x40 initial
grid, every box shown to clear `sqrt(3)/4 + target`.

### How it was sharded, and why that is the same computation

`branch_verify`'s recursion on a box depends on nothing but that box: it pops
the box, compares its Arb lower bound to the goal, and either closes it or
splits it in two. The set of terminal boxes is therefore a function of the
initial boxes and the goal, not of the order they are processed in. Running each
of a sector's 1600 initial cells as its own `branch_verify` call with
`domain = cell` produces exactly the box set his
`branch_verify(initial_grid=(40,40))` produces for the whole sector.

That is an assumption until it is checked, so it was checked two ways.

**Machine independence.** Cell 1599 of sector 17, the most expensive single cell
in the run, returns **exactly 6888 terminal boxes** at this target on an Apple
Silicon laptop under CPython 3.14.0 with `numpy` 2.5.2, and on a GitHub standard
runner under CPython 3.12 with the archive's pinned `numpy` 2.5.1. Same count,
across a different machine, interpreter and `numpy`. VERIFIED.

**Against the archive's own reference logs.** Sectors 0 and 1 were additionally
run at the *published* target `0.0153`, where the archive's `reference-run/logs`
record a terminal-box count to match. Both match exactly:

| sector | this run, at target 0.0153 | `reference-run/logs/N.log` |
|---|---|---|
| 0 | 270,744 | 270,744 |
| 1 | 292,931 | 292,931 |

Not "agrees to three figures": the same integer, assembled from 3200 independent
`branch_verify` calls on a machine the author never used. Sector 0 is the
interesting one of the two, because its archived log is not a fresh run at all
but a checkpoint resume recording 0 boxes of work (section 3, finding 5). This
is the second time this hunt lands on its 270,744, now cell by cell. VERIFIED.

A third figure is a consistency check rather than an equality, and is worth
naming as such: at the raised target each sector's terminal count comes out
slightly *above* the archive's count at `0.0153`, because a stronger goal closes
fewer boxes early and sends them to be split instead. The excess is **+0.87%
overall**, and every sector lands between **+0.58%** and **+1.25%**, against the
+0.2% to +1.0% the calibration measured on single cells. MEASURED.

Splitting per cell has a second consequence that is not bookkeeping. The open
frontier of a single cell never approaches `--max-boxes`, so this run never
meets the cap that stops the archive's own documented command in eight sectors
(section 3, finding 4). The reference run needed undocumented larger caps to get
past it. This one needs none, and the whole away branch is reproduced without
one.

### The result

Every sector, every cell, at target `0.0153040536`. The reference column is the
archive's own terminal-box count at its own weaker target `0.0153`, so the ratio
is the price of the raise and not a discrepancy.

| sector | cells | terminal boxes | archive at 0.0153 | ratio | verdict |
|---|---|---|---|---|---|
| 0 | 1600/1600 | 272,587 | 270,744 | 1.006807 | ACCEPTED |
| 1 | 1600/1600 | 295,147 | 292,931 | 1.007565 | ACCEPTED |
| 2 | 1600/1600 | 354,961 | 352,172 | 1.007919 | ACCEPTED |
| 3 | 1600/1600 | 444,514 | 440,355 | 1.009445 | ACCEPTED |
| 4 | 1600/1600 | 544,544 | 539,188 | 1.009933 | ACCEPTED |
| 5 | 1600/1600 | 617,100 | 609,488 | 1.012489 | ACCEPTED |
| 6 | 1600/1600 | 601,578 | 594,330 | 1.012195 | ACCEPTED |
| 7 | 1600/1600 | 517,360 | 512,148 | 1.010177 | ACCEPTED |
| 8 | 1600/1600 | 428,050 | 424,756 | 1.007755 | ACCEPTED |
| 9 | 1600/1600 | 352,776 | 350,497 | 1.006502 | ACCEPTED |
| 10 | 1600/1600 | 318,362 | 316,278 | 1.006589 | ACCEPTED |
| 11 | 1600/1600 | 317,113 | 315,121 | 1.006321 | ACCEPTED |
| 12 | 1600/1600 | 345,592 | 343,434 | 1.006284 | ACCEPTED |
| 13 | 1600/1600 | 403,355 | 400,711 | 1.006598 | ACCEPTED |
| 14 | 1600/1600 | 491,040 | 487,564 | 1.007129 | ACCEPTED |
| 15 | 1600/1600 | 604,609 | 599,578 | 1.008391 | ACCEPTED |
| 16 | 1600/1600 | 721,021 | 714,647 | 1.008919 | ACCEPTED |
| 17 | 1600/1600 | 806,587 | 797,875 | 1.010919 | ACCEPTED |
| 18 | 1600/1600 | 791,430 | 782,603 | 1.011279 | ACCEPTED |
| 19 | 1600/1600 | 688,898 | 682,817 | 1.008906 | ACCEPTED |
| 20 | 1600/1600 | 553,539 | 549,771 | 1.006854 | ACCEPTED |
| 21 | 1600/1600 | 433,373 | 430,735 | 1.006124 | ACCEPTED |
| 22 | 1600/1600 | 348,606 | 346,583 | 1.005837 | ACCEPTED |
| 23 | 1600/1600 | 291,038 | 289,192 | 1.006383 | ACCEPTED |
| **all 24** | **38,400/38,400** | **11,543,180** | **11,443,518** | **1.008709** | **ACCEPTED** |

**Zero cells refused, anywhere.** `branch_verify` refuses in exactly one way,
by hitting its open-frontier cap, and returns `RIGOROUS INCOMPLETE`; no cell in
this run did, because a single cell's frontier never comes near the cap. Each
accepted cell means every box covering it was shown in Arb to have
`Phi > sqrt(3)/4 + 0.0153040536`.

Read together with section 2a, this closes the gap that section described. The
certificate was pinned by its near branch at `0.0153040536989472` while
publishing the round `0.0153` below it; the away branch, idling `3.4e-4` above,
was never what stopped it. That is now shown rather than inferred: the away
branch clears the near branch's own value with `3.4e-4` still to spare.

### What it cost

**MEASURED**, and it is worth writing down because the whole point of the retry
was that the first attempt was launched without an estimate.

| | |
|---|---|
| workflow runs | 5 (one calibration, two halves of the away branch, two sweeps) |
| jobs | 476, of which 466 were away shards |
| GitHub-hosted machine time | 6,886 runner-minutes, **114.8 runner-hours** |
| billed | **zero.** Public repository, standard runners |
| compute delivered | **324.1 core-hours**: 307.4 at the raised target, 16.7 for the oracle |
| terminal boxes | 11,543,180 at the raised target, 563,675 at `0.0153` |
| realised rate | 0.0959 s per box, against the 0.10008 the calibration projected |
| projection error | 321 core-hours projected, 307.4 spent, **4.2% over** |
| wall clock | 9.1 hours, 14:25 to 23:33 UTC, at 20 concurrent jobs |
| jobs lost to their own timeout | 9, all in the first away run, all of which still uploaded the cells they had reached |

Two of those lines are the retry working. **The projection was published in
`RUNS.md` before anything was launched and came in 4.2% high**, which is what
lets a run this size be started deliberately rather than hopefully. And **the
nine lost jobs cost nine partial shards, not nine shards**: their finished cells
were already in the artifact, and a sweep did the remainder. The first attempt
lost a whole shard every time it was preempted, which is why six hours bought
nothing.

The comparison worth having: the author's own reference run at the *weaker*
target took **105.6 core-hours** across the 23 sectors whose logs record a fresh
run. A standard runner is 2.9x slower per core than his machine, which accounts
for essentially all of the difference between his 105.6 and this run's 307.4.
The raise itself is only 0.87% of it.

### What was not done

- **The target was not pushed past what the shipped data supports.** Reaching
  `0.015316`, let alone the `~0.015359` crossing of section 4, means moving
  `ETA`, `LARGE_RAD` and the node count and having the author's search
  regenerate the certificate data. The calibration says the away side of that is
  affordable: `0.015316` costs 4.2% more boxes than `0.0153` at the worst cell
  measured, against 1.0% for the target actually run. So what stops it is not
  compute. It is that every shard would have to load the same regenerated
  `.npz`, which needs a prepare-and-publish step this instrument does not have.
  It is the top-ranked door below.
- **The away branch was not run at the crossing `eta`,** which is what would
  turn section 4's INFERRED ceiling into a bracket with a rigorous away side.
- **Only two sectors were re-run at the published target `0.0153`.** They are
  the exact-count oracle, not a reproduction. A full 24-sector run at `0.0153`
  would cost a second time what this one cost and would establish nothing the
  raised-target run does not already imply, since a target that is accepted
  implies every weaker one.
- **The three soundness findings of section 3 were not patched.** They are
  reported, and none of them turns an acceptance into a refusal.
- **The paper's hand proofs were not audited**, as stated at the top of this
  document. Nothing here is a statement about Bloch's constant; it is a
  statement about what Wikström's verifier accepts.
- **Nothing was posted to the author, to Zenodo or to arXiv.**

## The doors

What to unfreeze next, ranked. A wall computation that publishes the wall
without this list gives the information away and keeps none of its value.

### 1. Active constraints at the optimum

The gain is `min(near, away)` and the two branches are not balanced at the
published constants: `near = 0.0153040536989` binds, `away ~ 0.0156486` idles
3.4e-4 above it. Ranked by how hard each binds, with the slope measured in
section 2 where one exists:

| rank | constraint | binds through | measured slope | headroom it holds |
|---|---|---|---|---|
| 1 | the point-cut **node count** limiting the admissible radius | `near` | `d near/dR ~ 0.045`; 16 -> 32 nodes buys R 0.581664 -> 0.581836 | measured from the 16-node accepted radius (`near` 0.015310272): +7.7e-6 at 32 nodes, +2.09e-5 at the dense-node limit |
| 2 | **ETA**, which trades the branches against each other | both | `near` +3.9e-4 per unit `eta` down, `away` -2.2e-3 per unit | 5.5e-5, from 0.0153040 to the ~0.015359 crossing at 16 nodes |
| 3 | the **away relaxation** (47 cuts, 5676 rows, K = 260) | `away` at the crossing | not measured here; the paper's own fixed-radius dual gap is ~4e-5 | caps the whole dichotomy at ~0.015378 |
| 4 | the **24 phase sectors** | `away` | `eta_eff = eta*cos(pi/24) = 0.694011`; 48 sectors gives 0.698501, worth ~9.9e-6 of away floor at the measured slope, INFERRED | ~1e-5 of `away`, which only pays at the crossing |
| 5 | the **target** itself | neither; it is the acceptance threshold | +4.05e-6 of target costs **+0.87% of away boxes over the whole run** (section 5, 11,543,180 against 11,443,518); at the worst single cell measured, +1.6e-5 costs +4.2% | none: it is a readout, not a resource |

Ranks 1 and 2 are where the published constant actually sits. Rank 3 is the one
that would move the ceiling rather than close the gap to it.

### 2. The frozen-constant inventory

Every chosen-not-optimized number in the variable-radius construction, and what
relaxing it trades against.

| constant | value | where | trade shape |
|---|---|---|---|
| `ETA` | 0.70 | `variable_radius_certificate.py:30`, and stored | **Genuine trade.** Down raises the admissible radius and `near`, lowers the `away` floor. The crossing is at `eta ~ 0.569` (16 nodes) to `~0.578` (dense). The one round number in the construction |
| `LARGE_RAD` | 0.5815218918243517 | line 31, and stored | **Slack, free to spend.** It leaves +0.000937 of positivity margin unused, where the accepted maximum at 16 nodes, 0.581664, leaves only +7.3e-6. Moving to it raises `near` from 0.0153040536989 to 0.015310272, **+6.22e-6**, and costs nothing but a re-search |
| `POINT_BOXES` | 16 | line 32 | **Cheapest door in the hunt.** More nodes buy radius, and the near verification costs seconds, not hours. The whole of rank 1 is behind this one number |
| `POINT_SUBDIV` | 32 | line 33 | Resolution of the Arb positivity check itself (`verify_positivity` line 228). More subdivisions tighten the enclosure at linear cost, so it buys admissible radius indirectly. Not separated from `POINT_BOXES` by any measurement here |
| `C` | 3.2888 | line 288 default, and stored | **Crosses certificates.** Every away cut, halfspace and box penalty uses it, valid because the *fine* fixed-radius certificate proves `\|a_3\| <= 3.28877762819`. Tightening it tightens every away constraint, and requires re-running that certificate. Nothing in the variable-radius programs asserts the relation (section 3, finding 2) |
| `K`, the row grid | 260, 5676 rows | stored | The relaxation's resolution. This is rank 3 and it is the expensive one |
| `nsector` | 24 | line 354 | **Genuine trade.** More sectors tighten `eta*cos(pi/nsector)`; 48 buys ~9.9e-6 of `away` floor for 2x the away cost |
| initial grid | 40 x 40 | `--initial` default | Cost and robustness only. Finer means more terminal boxes for the same result |
| `--max-boxes` | 200000 | `variable_radius_certificate.py:434` | Cost and robustness only, and **retired** by this hunt's per-cell sharding: the open frontier never approaches it (section 3, finding 4) |
| the target | 0.0153 | `--target` default | A round number, and the only one this hunt moved |

### 3. The information class

Every door in the two tables above stays **inside** the information the current
family reads: the polyhedral coefficient body in `(a_2, a_3)`, the three-atom
balanced measures, and the two cut families. They re-tune a fixed construction
over the same objects, so they are all under its configuration ceiling, which
section 4 puts at `sqrt(3)/4 + 0.01538` INFERRED. No amount of turning them
reaches 0.0154.

Getting past that ceiling requires reading more than this family reads, and the
two candidates are both **outside**:

- **Higher Taylor coefficients.** Pinning `a_4` and beyond would shrink the
  body the away branch minimises over. The paper's own last section excludes
  this at fixed radius by an even-function antipodal argument, and it is
  recorded as a dead route in `MISSION.md`. Whether the same argument closes it
  at variable radius is not established here, and that is the sharpest open
  question this hunt leaves.
- **A better starting radius than Bonk's `1/sqrt(3)`.** Everything above takes
  Bonk's theorem as given and extends outward from it by point cuts. A stronger
  distortion theorem would move the whole construction, and no tuning inside the
  family substitutes for it.
