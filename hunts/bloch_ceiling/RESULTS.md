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

**The 24 away sectors.** SECTORS-PLACEHOLDER

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

SECTION5-BODY

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
| 5 | the **target** itself | neither; it is the acceptance threshold | +4.05e-6 of target costs +1.0% of away boxes, +1.6e-5 costs +4.2% (section 5) | none: it is a readout, not a resource |

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
