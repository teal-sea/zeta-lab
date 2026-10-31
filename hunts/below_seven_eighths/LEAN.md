# LEAN.md: OpenAI's pinned 7/8 closure, built on the campaign box

**Hunt #136, Lean lane, 2026-10-21. Status: done for this wave.** This page is written
by the only agent in the hunt's first workflow that runs `lake` or `lean`. The lane ran
in two sessions. The first (14:39Z to 18:06Z) set up the pinned environment, built the
closure, printed the axioms and ran every check below, then was stopped at 18:10Z by the
campaign-wide pause before it wrote anything after section 2. The second (21:22Z to
22:05Z) found no live Lean process of this lane and no holder of the cache
lock, re-ran every check from the same cache with fresh logs, and wrote sections 0 and
3 onward. Both sessions' numbers are given; where they could differ, they agree.

No number on this page is pinned by a test: the lane owns no test file. Every number
is therefore graded where it appears. *(cited)* marks a quoted line of a file in this
tree or of OpenAI's source at the pinned commit; *(measured)* marks a reading taken on
the campaign box by this lane, from a log, `/proc` or `/usr/bin/time`; *(hardened)*
marks a measured fact that two independent routes agree on; *(kernel-checked)* marks a
Lean declaration that Lean 4.34.1's kernel accepted, with `#print axioms` reporting
only `propext`, `Classical.choice` and `Quot.sound`; *(inferred)* marks a reading or
an estimate that no computation here checks; *(arithmetic)* marks a product or
quotient of graded numbers, done by hand and checked by no test.

Three of OpenAI's declaration names contain the word this tree reserves for
`zeta/rigor.py`. This page writes that word as `[R]`, so the module
`Detector/FinalAssembly[R]Bands.lean` is the one OpenAI's tree spells out in full.

## 0. What the lane found

1. **The build.** `lake build OAI.NumberTheory.DirichletL.Nonvanishing`, the solution
   module that OpenAI's `ComparatorChallenges/QuasiRiemannHypothesis.json` names for
   the zeta statement *(cited)*, exited 0 with `Build completed successfully (7061
   jobs).` after 3 h 9 min 51 s on 16 Lean workers *(measured)*. Peak memory: 5.77 GiB
   in one process, 10.2 GiB of summed PSS for the whole build, and `MemAvailable` never
   below 67.2 GiB, so the 25 GiB kill floor was never approached *(measured)*. The
   second session's rebuild of the same target did nothing in 18.8 s and reported the
   same 7061 jobs *(measured)*.
2. **The axioms.** Both 7/8 statements depend on exactly `propext`,
   `Classical.choice` and `Quot.sound` *(kernel-checked, in both sessions)*. A gate
   adapted from `lean/qrh/scripts/check-axioms.py` accepted those reports, rejected
   three planted faults and accepted a control *(measured)*.
3. **The estimate was wrong, and why.** Section 1 estimated 30 to 60 minutes of build
   wall time; the build took 190 minutes. CPU was close to budget (10.4 CPU-hours against 9).
   Time was not: the closure's longest import chain is 404 modules, its critical path
   weighted by this build's own per-module times is 170.7 minutes, 150 consecutive
   levels of the import graph hold at most two modules each, and half of the 5,172
   watchdog samples saw exactly one `lean` process *(measured)*. The build is bound by
   its dependency chain, not by cores *(inferred from those measurements)*.
4. **`OAI.SevenEighths.Parameters.compensated_geometry`** is in
   `OAI/NumberTheory/DirichletL/Parameters.lean`, lines 12 to 26, and transcribes the
   paper's length inequalities (lines 8593 to 8597) and its identity
   C_II(7/8) = 3/16 = l_x/2 + b/12 (line 8642) *(cited; the correspondence is a
   reading)*. **Nothing depends on it.** It
   lies outside the dependency cone of both 7/8 theorems, and so do the other three
   theorems of that file *(hardened: the environment's dependency graph and a text scan
   of OpenAI's whole repository agree)*. Editing it changes nothing the 7/8 theorems use.
5. **`OAI.SevenEighths.Endpoint.balancedExponent`** is in
   `OAI/NumberTheory/DirichletL/Endpoint.lean`, lines 29 to 31 *(cited)*. It has 5 direct
   users *(hardened)* and 33 public declarations downstream in 21 modules, 21 of them
   inside the cone, including both 7/8 theorems, which it reaches by a chain of 16
   declarations *(measured)*.
6. **There is no parameter object.** The formal proof carries the Part II geometry and
   the row counts as literals. 449 declarations in 147 modules carry a derived geometry
   constant (17/48, 23/48, 13/16, 11/16, 3/16, 1/48, 5/16), a row-count definition or
   literal, or the target 7/8 in their statement or definition; 329 of them, in 120
   modules, are inside the cone *(measured, literal-level scan, section 5.4)*. With
   everything downstream of them they touch 478 of the cone's 18,766 public
   declarations (2.5%), or 1,190 (6.3%) if the ambiguous raw values 1/6, 5/6 and 1/8
   are counted too *(measured)*.
7. **One step of generalization is done.** Hunt 134's general-geometry formulas,
   written in Lean over any field, specialize exactly to OpenAI's `balancedExponent`,
   `relativeExponent`, `sourceExponent` and `compensated_geometry` at
   (l, M, b) = (1/6, 5/6, 1/8) *(kernel-checked identities about formulas, scratch files
   reproduced in section 6)*. Changing the slope to 4/5 or b to 1/9 makes them fail;
   changing the contour does not, as the general theorem says it should *(measured)*.
8. **What generalizing would take** (section 7): re-instantiating the proof at one new
   rational point means editing the constants at the census sites, recomputing one exact
   polynomial identity, and rebuilding 1,539 of the 2,924 closure modules (8.17 h of this
   build's module time, critical path 47.6 min) *(measured surface; effort inferred)*.
   A symbolic version is a larger refactor whose main risk is mathematical: the endpoint
   margin rests on an identity whose coefficients are tuned to the paper's numbers
   *(inferred)*.

## 1. Estimate, written before the build

Written at 2026-10-21T14:41Z, before any `lake` command ran.

**The baseline.** `lean/qrh/RUNS.md` names one measured baseline, "135 minutes on a
GitHub-hosted runner with Lake's default parallelism of four" *(cited)*, which is the
replay recorded in `docs/38` section 7: `lake build
OAI.NumberTheory.DirichletL.Nonvanishing OAI.NumberTheory.SiegelZeros.Main` on a
four-core `ubuntu-24.04` runner, 04:09:27Z to 06:24:37Z, ending `Build completed
successfully (12186 jobs)` *(cited)*. Its pilot measured a peak RSS of 4.2 GB on one
leaf module, `DirichletL.Arithmetic.EisensteinCoordinates` *(cited)*.

**Scaled to this box.**

- CPU: at most 4 x 135 = 540 core-minutes for both targets *(arithmetic)*. This lane
  builds only the first target, whose closure holds 2,924 of OpenAI's modules and
  25.0 MB of source against the Siegel closure's 306 modules and 3.1 MB *(cited,
  `docs/38` section 4)*, so most of that budget is needed.
- Thirty-two workers with perfect scaling: 540 / 32, about 17 minutes *(arithmetic)*.
  Memory forbids it: 32 concurrent modules at 4.2 GB is about 134 GB, more than the
  box's 115 GiB (about 123.6 GB) *(arithmetic)*.
- The box is shared. At 14:37Z the load average was 9.4 and another project's seven
  Python workers and one Lean replay checker were running *(measured)*.
  `MemAvailable` was 108864740 kB, about 103.8 GiB *(measured)*. With the floor this
  workflow sets, 25 GiB, about 78 GiB is usable, which allows at most 18 workers at
  4.2 GB if every worker peaks at once *(arithmetic)*.
- Chosen cap: `LEAN_NUM_THREADS=16`. Lake 4.34.1 rejects `-j` *(cited, `docs/38`
  section 7)*; the variable bounds the Lean runtime's worker pool, which is expected
  to bound the number of concurrent `lean` children. That expectation is checked by
  sampling the process table during the build, not assumed. At 16 workers the CPU
  bound is 540 / 16, about 34 minutes *(arithmetic)*; allowing for the dependency
  graph's critical path and for the other tenants, **30 to 60 minutes of build wall
  time**, plus 10 to 20 minutes for the clone, toolchain, `lake update` and the
  Mathlib cache *(estimate, unmeasured)*. Worst-case build memory is 16 x 4.2, about
  67 GB, on top of the tenants' 12 GiB *(arithmetic)*.
- **Kill rule.** A watchdog samples `/proc/meminfo` every two seconds and sends TERM,
  then KILL, to the build's process group if `MemAvailable` falls below 25 GiB
  (26214400 kB). Its samples also give the peak summed RSS of the build's processes.
- Cost: the campaign box is already provisioned, so the run buys no compute. Disk:
  about 15 GB expected against 243 GB free *(estimate; free space measured)*.

The cache is `<cache>/qrh-build` (outside the tree) in place of
the Modal volume, with `ELAN_HOME` and `XDG_CACHE_HOME` inside it, as
`lean/qrh/scripts/namespace-build.sh` sets them.

## 2. Setup, following `namespace-build.sh`

`namespace-build.sh` refuses to run outside Namespace or Modal, and its second half
builds hunt 125's own package and bridge, which this hunt does not need. So the lane
ran its upstream half as two local scripts with the same pins, the same checks and the
same per-stage logging (`stage` became `guarded.sh`, which adds the memory watchdog).
The scripts and every log are in the cache under `evidence/20261021T143950Z/`, which is
outside the tree and is not durable; this page is the durable record. No file in
OpenAI's checkout was edited; the lane's Lean files live in the cache's `scratch/`.

| stage | what ran | wall | exit | grade |
| --- | --- | ---: | ---: | --- |
| upstream-clone | `git clone --no-checkout https://github.com/openai/math.git`, then `git checkout --detach adc7f1241b42e322a6451854ab7e4b4c146bf78a` | 27.5 s | 0 | measured |
| toolchain | `elan toolchain install leanprover/lean4:v4.34.1` (elan 4.2.4 from `~/.elan/bin`, `ELAN_HOME` in the cache) | 17 s | 0 | measured |
| upstream-update | `lake update` in `lean/` | 187 s | 0 | measured |
| upstream-cache | `lake exe cache get` | 29 s | 0 | measured |

The checks the script makes, all passed *(measured)*:

- `HEAD` is `adc7f1241b42e322a6451854ab7e4b4c146bf78a`, the checkout is clean before the
  update, and `lean/lean-toolchain` reads `leanprover/lean4:v4.34.1`.
- After `lake update`, `.lake/packages/mathlib` is at
  `d13f23b723b8a846827a245b89c10fc7d3f11612`.
- `PrimeNumberTheoremAnd/Wiener.lean` no longer contains `prelim_decay_2`, so the PNT+
  patch that removes the two placeholder theorems `docs/38` section 4 describes was
  applied.
- OpenAI's hooks reported 23 patch applications: 11 before dependency resolution, each
  verified again after it, and 12 by the post-update hook. The `patches/` directory
  holds 23 patch files of 160,187 lines in total, the figure `docs/38` section 7
  records *(measured; the line count is `wc -l`)*.
- `lake update` left `lake-manifest.json` byte-identical to the committed file (empty
  `git diff`), so no dependency moved off its pin *(measured)*.
- Mathlib's own post-update hook downloaded 8,908 cache files; the explicit
  `lake exe cache get` then found nothing to download *(measured)*.
- Lake warned "toolchain not updated; multiple toolchain candidates": OpenAI's fixed
  v4.34.1, TauCeti's v4.35.0-rc3 and fixed-point-theorems' v4.32.0. OpenAI's
  `fixedToolchain := true` keeps v4.34.1. The compiler processes sampled during the
  build ran the v4.34.1 binary *(measured, process table)*.

**Second session, 21:30Z.** Before re-running anything the second session checked the
same pins again *(measured)*: `HEAD` `adc7f1241b42e322a6451854ab7e4b4c146bf78a` with no
modified or untracked file in OpenAI's checkout (`git status --porcelain
--untracked-files=all` printed nothing, so no OpenAI source was edited by either
session); Mathlib at `d13f23b723b8a846827a245b89c10fc7d3f11612`, whose `git
rev-parse --show-toplevel` names the Mathlib package itself, not this tree
(`CLAUDE.md` compute rule 7); `lake-manifest.json` with SHA-256 `cf6105a2...0794`,
equal to the committed file's; `prelim_decay_2` absent; `lean --version` printing
`Lean (version 4.34.1, x86_64-unknown-linux-gnu, commit 5045d0056413, Release)`.

## 3. The build

**What ran** *(measured, `evidence/20261021T143950Z/` in the cache)*: `timeout
--foreground --signal=TERM --kill-after=60s 210m lake build
OAI.NumberTheory.DirichletL.Nonvanishing` in OpenAI's `lean/` directory, with
`LEAN_NUM_THREADS=16`, under `/usr/bin/time -v`, in its own process group, with the
memory watchdog attached.

| quantity | value | grade |
| --- | --- | --- |
| start and end | 2026-10-21 14:47:53Z to 17:57:46Z | measured |
| wall time | 11,393 s by the stage timer; 3:09:51 by `/usr/bin/time` | measured |
| exit code | 0 (`/usr/bin/time` and the stage record agree) | measured |
| last line | `Build completed successfully (7061 jobs).`, job counter 7061/7061 | measured |
| modules compiled | 2,924 `OAI` modules (every module of the closure has a `Built` line), 4 `PrimeNumberTheoremAnd`, 15 `RellichKondrachov` | measured |
| placeholders and errors in the log | 0 lines with `declaration uses`, 0 occurrences of `sorry`, 0 `error:` lines | measured |
| warnings | 23, every one "repository ... has local changes", one per dependency OpenAI's hooks patch | measured |
| CPU | 30,362.67 s user, 7,133.44 s system: 10.42 CPU-hours, 329% of one core on average | measured; total is arithmetic |
| peak RSS of one process | 6,050,300 kB (5.77 GiB), from `/usr/bin/time` and the watchdog alike | measured |
| concurrent `lean` processes | at most 16 (never above the cap), mean 4.99; exactly one in 2,603 of 5,172 samples | measured |
| summed RSS of the build's processes | peak 71,062,904 kB (67.8 GiB) at 17:08:56Z; this counts each shared, read-only `.olean` mapping once per process, so it overstates the footprint | measured |
| summed PSS of the build's processes | peak 10,681,644 kB (10.2 GiB) at 17:15:52Z with 19 processes; sampled every 5 s from 14:59:31Z only, because the sampler started 12 minutes into the build | measured |
| `MemAvailable` | 100.2 GiB at the start, minimum 70,445,492 kB (67.2 GiB) at 16:10:44Z; the floor was 26,214,400 kB (25 GiB); the watchdog killed nothing | measured |
| box load | 1-minute load average 89.32 at 15:45:55Z and 134.30 at 16:08:02Z on 32 vCPUs, from other workflows' jobs | measured |

**Why it took three hours.** The second session recomputed the closure from import
lines alone: 2,924 `OAI` modules and 25,009,201 bytes of source, the same list as the
first session's and the same 2,924 and 25.0 MB `docs/38` section 4 records *(measured
here; the docs figure cited)*. Its import graph has 404 levels, so the longest import
chain is 404 modules; levels 51 to 200 hold at most two modules each, 195 modules in
all; levels 201 to 300 hold 1,960 *(measured, `levels.py`)*. Weighting each module by
its own logged build time gives a critical path of 170.7 minutes, against 190 minutes
of wall time and 16.08 hours of summed module time *(measured, `depth.py` and
`rebuild.py`)*. The slowest modules were `GaussSum/ActiveReindexing.lean` (502 s) and
`RowCompletion/FreePrimePools.lean` (387 s) *(measured)*. So the build spends most of
its time walking a chain one or two modules wide, and more workers would not have
shortened it; on an idle box the per-module times, and with them the critical path,
would be shorter *(inferred: the box was oversubscribed during the build, and no
uncontended run was made)*. Section 1's CPU estimate held within a sixth (9 CPU-hours
estimated, 10.42 measured) *(arithmetic)*; its wall-time estimate assumed the work
would spread over 16 workers, which the graph does not allow.

The `docs/38` replay built both targets, 12,186 jobs, in 135 minutes on four cores
*(cited)*; this build compiled one target, 7,061 jobs, in 190 minutes on 16 workers.
The two runs differ in hardware, load and target set, so this page draws no conclusion
from the comparison.

**The outputs are current.** At 21:30:05Z the second session ran the same `lake build`
command. It finished in 18.77 s with exit 0 and `Build completed successfully (7061
jobs).`, printed no `Built` or `Replayed` line and never started a `lean` process
*(measured, `evidence/20261021T2130Z-session2/noop-build.log`)*. The compiled closure
on disk is therefore the first session's and is up to date with OpenAI's sources.

## 4. The axioms

From a scratch file that imports `OAI.NumberTheory.DirichletL.Nonvanishing` and asks
`#print axioms` of both statements, run as `lake env lean`, the first session at
17:57:56Z and the second at 21:30:25Z printed the same two reports *(kernel-checked)*:

```
'OAI.riemannZeta_ne_zero_of_seven_eighths_lt_re' depends on axioms: [propext, Classical.choice, Quot.sound]
'OAI.DirichletCharacter.LFunction_ne_zero_of_seven_eighths_lt_re' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

These are the reports the `docs/38` section 7 replay printed on a GitHub runner on
2026-10-08 *(cited)*, now reproduced on a second machine from the same pinned sources.
`#print axioms` walks every constant the proofs use, through the patched dependencies
and Mathlib, so the result covers the whole closure. Every `OAI` module of it, and the
19 modules it imports from the patched `PrimeNumberTheoremAnd` and `RellichKondrachov`
packages, were compiled and kernel-checked on this box; Mathlib's own modules came from Mathlib's
cache, as in every replay this tree records, so the kernel checked them when Mathlib
built that cache, not here *(measured from the build log; the rest inferred)*.

**The gate, and the faults planted in it** *(measured, both sessions)*. The gate is
`lean/qrh/scripts/check-axioms.py` with the expected names passed on the command line:
it fails closed on a missing, duplicated or extra report, on any axiom outside the
three, and on any `sorryAx` or `error:` in the log.

| input | expected | result |
| --- | --- | --- |
| the two real reports | accept | `ACCEPT: 2 axiom reports` |
| planted fault 1: a theorem proved by `sorry` | reject | `REJECT: ... forbidden axioms ['sorryAx']` |
| planted fault 2: a theorem using an added `axiom` | reject | `REJECT: ... forbidden axioms ['Lab136Scratch.planted_axiom']` |
| planted fault 3: the real log with the Dirichlet report deleted | reject | `REJECT: expected exactly [...] received [...]` |
| control: zeta has no zero with real part above 15/16, proved from OpenAI's theorem by `linarith` | accept | `ACCEPT: 1 axiom reports` |

What this does and does not establish. The two formal statements are theorems of Lean
4.34.1 with Mathlib `d13f23b7` and OpenAI's 23 patched dependencies, as `docs/38`
already records *(kernel-checked)*. Only Lean's own kernel ran here: the comparator run
through the independent NanoDa kernel that `docs/38` sections 5 and 7 record was not
repeated. No person has reviewed the paper's argument (`MISSION.md`), and a kernel
check of the formal statements is not such a review.

## 5. Where the Part II geometry and the row counts live

**Method** *(measured)*. A scratch Lean file, `scratch/Analysis.lean`, imports the
built module and walks the environment: for each of the 52,321 constants declared in
an `OAI` module it writes the module, the kind, whether Lean generated it, every
numeral quotient `n/d` in its type (and, for a definition, in its body), and an edge to
every other `OAI` constant its type or value uses. The dump has 350,632 edges and the
environment 8,596 modules. The second session's dump is byte-identical to the first's
(SHA-256 `15f57893...f66c` for the nodes, `f7f5898e...c1d9` for the edges). Walking
the edges from the two 7/8 theorems gives their dependency cone: 26,697 constants, of
which 18,766 are public (written by an author, not generated), in 2,656 modules
*(measured)*. A declaration outside the cone is not used, at any depth, by the
kernel terms of either theorem.

### 5.1 `Parameters.compensated_geometry`

```lean
theorem compensated_geometry {d : ℝ} (_hd0 : 0 ≤ d) (hd1 : d ≤ 1 / 6) :
    (1 / 2 : ℝ) ≤ 5 / 6 - 2 * d ∧
    3 / 16 ≤ 17 / 48 - d ∧
    5 / 16 ≤ 23 / 48 - d ∧
    1 / 12 ≤ 23 / 48 - d - 11 * (1 / 8) / 6 ∧
    (17 / 48 : ℝ) / 2 + (1 / 8) / 12 = 3 / 16
```

`OAI/NumberTheory/DirichletL/Parameters.lean`, lines 12 to 26, proved by `linarith`
four times and `norm_num` once *(cited)*. Its five conjuncts are the paper's
"M' ≥ 1/2", "l_x - d ≥ 3/16, l_y - d ≥ 5/16, l_y - d - 11b/6 ≥ 1/12" (lines 8593 to
8597) and "C_II(7/8) = 3/16 = l_x/2 + b/12" (line 8642), at the geometry of lines 6857
to 6866, `b=\frac18,\qquad h=\frac{13}{16},\qquad \ell=\frac16`, with
`M'=M-2d,\qquad \ell'=\ell-d,\qquad 0\le d\le\ell=1/6` (line 8079) *(cited; the match
is a reading, inferred)*.

- **Downstream declarations: none.** It is outside the cone of both theorems and has
  no user at all *(measured, dump)*. A text scan of OpenAI's whole checkout at the
  pinned commit, excluding `.lake`, finds the string `compensated_geometry` exactly
  once, at its own declaration *(measured, `grep -rn`)*. The two routes agree
  *(hardened)*.
- The same holds for the file's other three theorems, `exists_height_cutoff`,
  `exists_tail_order` and `cumulative_frequency_bound`: outside the cone, no user in
  the dump, and no occurrence of their names in any other file *(hardened)*. The only
  importer of `Parameters.lean` is `ParametersSlotLengths.lean` *(measured, text)*.
- So the geometry facts the proof needs are proved again where they are used, at
  literal values: for example `Detector/LowSourceScales.lean` states
  `Z^(23/48:ℝ)/Z^(17/48:ℝ)=Z^(1/8:ℝ)` (lines 10 to 11) and
  `Detector/LowNominalGeometry.lean` states `Z^(17/48:ℝ)*Z^(23/48:ℝ)=Z^(5/6:ℝ)`
  (line 59) *(cited)*.

### 5.2 `Endpoint.balancedExponent`

```lean
def balancedExponent (δ y : ℝ) : ℝ :=
  -(1 / 48) + (2 / 3) * δ + δ * (1 / 2 - y) / 6 -
    (13 / 16) * (1 - balancedRowCount δ y)
```

`OAI/NumberTheory/DirichletL/Endpoint.lean`, lines 29 to 31, built on the module's
other definitions `denominator` ((37 + 34y)/18), `primeWeight` ((7 + 18y + 8y²)/9),
`balanceDenominator` (with the slope 5/6), `balancedCutoff` and `balancedRowCount`
*(cited)*. It is the E_* of the paper's lemma at line 15994,
`\begin{lemma}[Compensated endpoint certificate]\label{lem:balanced-endpoint}`,
and the module's `endpoint_identity` and `balanced_endpoint_margin` formalize that
lemma's identity (lines 16040 to 16047) and its bound
`-E_*\ge\frac{49}{440640}>\frac1{10000}.` (line 16000) *(cited; the match is a reading
of names and statements, inferred)*.

- **Direct users** (5): `Endpoint.endpoint_identity`, `Endpoint.balanced_endpoint_margin`,
  `Endpoint.balanced_endpoint_strict`, `HeckeDetectorRowCount.balanced_endpoint_with_loss`
  and `ProbeCentralExponent.balanced_source_margin` *(measured, dump)*. The text scan
  finds `balancedExponent` in exactly three files, at those declarations:
  `Endpoint.lean`, `Detector/CentralExponent.lean` line 49 (inside
  `balanced_source_margin`) and `Hecke/DetectorRowCountEndpoint.lean` line 103 (inside
  `balanced_endpoint_with_loss`) *(hardened)*.
- **All downstream public declarations** (33, in 21 modules; *measured*), with the 12
  that lie outside the cone marked †:
  - `Endpoint.lean`: `balanced_endpoint_margin`, `balanced_endpoint_strict` †, `endpoint_identity`
  - `Hecke/DetectorRowCountEndpoint.lean`: `HeckeDetectorRowCount.balanced_endpoint_with_loss` †
  - `Detector/CentralExponent.lean`: `ProbeCentralExponent.balanced_source_margin`
  - `Detector/CentralMixedMargins.lean`: `ProbeHighRowFamily.balanced_mixed_margin`, `balanced_mixed_saving`
  - `PrimeRows/NonfloorExponent.lean`: `ProbeHighRowFamily.adaptive_mixed_saving`
  - `PrimeRows/NonfloorArithmetic.lean`, `NonfloorIntegral.lean`, `NonfloorNormalized.lean`, `NonfloorCollected.lean`, `HighFromMoments.lean`: `ProbeHighRowFamily.actual_nonfloor_cube_arithmetic` †, `actual_nonfloor_cube_norm` †, `actual_normalized_nonfloor_cube` †, `actual_nonfloor_rows_saving` †, `actual_high_probe_from_raw_moments` †
  - `Detector/FinalAssemblyArithmetic.lean`, `FinalAssemblyIntegral.lean`, `FinalAssemblyNormalized.lean`, `FinalAssemblyCollected.lean`, `FinalAssemblyHigh.lean`, `FinalAssemblyFixedHigh.lean`: `ProbeFinalAssembly.actual_nonfloor_cube_arithmetic`, `actual_nonfloor_cube_norm`, `actual_normalized_nonfloor_cube`, `actual_nonfloor_rows_saving`, `actual_high_probe_from_raw_moments`, `fixed_high_bound`
  - `Detector/FinalAssemblyChosenData.lean`: `ProbeFinalAssembly.common_probe_of_chosen_moments`, `zeta_of_chosen_moments`, `dirichlet_of_chosen_moments`, `hecke_of_chosen_moments` †
  - `Detector/FinalAssembly.lean`: `ProbeFinalAssembly.common_probe_of_raw_moments` †, `zeta_of_raw_moments` †, `dirichlet_of_raw_moments` †, `hecke_of_raw_moments` †
  - `Detector/FinalAssembly[R]Bands.lean`: `ProbeFinalAssembly[R]Bands.zeta_of_[R]`, `dirichlet_of_[R]`
  - `Detector/FinalAssemblyUnconditional.lean`: `ProbeFinalAssemblyUnconditional.zeta_nonzero`, `dirichlet_nonzero`
  - `Nonvanishing.lean`: `OAI.riemannZeta_ne_zero_of_seven_eighths_lt_re`, `OAI.DirichletCharacter.LFunction_ne_zero_of_seven_eighths_lt_re`
- **A shortest chain to the zeta theorem** (16 declarations, *measured*):
  `balancedExponent` → `ProbeCentralExponent.balanced_source_margin` →
  `ProbeHighRowFamily.balanced_mixed_margin` → `balanced_mixed_saving` →
  `adaptive_mixed_saving` → `ProbeFinalAssembly.actual_nonfloor_cube_arithmetic` →
  `actual_nonfloor_cube_norm` → `actual_normalized_nonfloor_cube` →
  `actual_nonfloor_rows_saving` → `actual_high_probe_from_raw_moments` →
  `fixed_high_bound` → `common_probe_of_chosen_moments` → `zeta_of_chosen_moments` →
  `ProbeFinalAssembly[R]Bands.zeta_of_[R]` →
  `ProbeFinalAssemblyUnconditional.zeta_nonzero` →
  `OAI.riemannZeta_ne_zero_of_seven_eighths_lt_re`.

### 5.3 The other carriers, by downstream reach

Every count *measured* on the dump; "distance" is the number of public declarations on
the path a breadth-first search finds from the declaration up to the zeta theorem,
counting the theorem and not the declaration.

| declaration | file (under `OAI/NumberTheory/DirichletL/`) | kind | in cone | downstream decls | downstream modules | direct public users | distance | what it fixes |
| --- | --- | --- | :-: | ---: | ---: | ---: | ---: | --- |
| `HeckeDetectorRawFiber.Fiber` | `Hecke/DetectorRawFiber.lean` | structure | yes | 159 | 61 | 103 | 6 | field `supply : 7/37≤∑ s∈slots,widths s` (line 46) |
| `Parameters.HighData` | `ParametersHighData.lean` | structure | yes | 116 | 32 | 103 | 3 | fields `slots_sum : (∑j,ell j)=1/6` (line 25) and `central_budget`, which ends `≤49/440640` (lines 42 to 43) |
| `HeckeDetectorBatch.Batch` | `Hecke/DetectorBatch.lean` | structure | yes | 83 | 47 | 46 | 6 | field `supply : 7/37≤∑ s∈slots,widths s` (line 33) |
| `Endpoint.denominator` | `Endpoint.lean` | def | yes | 79 | 36 | 6 | 9 | D = (37 + 34y)/18 |
| `Endpoint.primeWeight` | `Endpoint.lean` | def | yes | 79 | 36 | 8 | 8 | P = (7 + 18y + 8y²)/9 |
| `Endpoint.balanceDenominator` | `Endpoint.lean` | def | yes | 76 | 36 | 6 | 8 | J with slope 5/6 |
| `Endpoint.balancedCutoff` | `Endpoint.lean` | def | yes | 74 | 36 | 11 | 7 | the cutoff R_* |
| `Endpoint.balancedRowCount` | `Endpoint.lean` | def | yes | 61 | 31 | 16 | 7 | 1 - 5/6 + (5/6 - δ)R_* |
| `ProbeCentralExponent.sourceExponent` | `Detector/CentralExponent.lean` | def | yes | 43 | 25 | 14 | 10 | E(d) at 17/48, 23/48, 17/50, 1/6 |
| `HeckeDetectorRowCount.denominator` | `Hecke/DetectorRowCountCrossing.lean` | def | yes | 40 | 22 | 11 | 9 | 3 - 17x/9, that is c = 4/9 |
| `HeckeInverseAmplification.amplificationPower` | `Hecke/InverseAmplificationBudget.lean` | def | yes | 39 | 25 | 7 | 13 | the amplification power |
| `ProbeCentralExponent.relativeExponent` | `Detector/CentralExponent.lean` | def | yes | 37 | 22 | 5 | 11 | E(d) relative to 3/16 |
| `HeckeDetectorRowCount.primeWeight` | `Hecke/DetectorRowCountCrossing.lean` | def | yes | 36 | 21 | 7 | 9 | (2 - 8x/9)(1 - x) |
| `HeckeInverseAmplification.sourceExponent` | `Hecke/InverseAmplificationBudget.lean` | def | yes | 35 | 24 | 7 | 10 | source exponent |
| `HeckeDetectorRowCount.shortExponent` | `Hecke/DetectorRowCountCrossing.lean` | def | yes | 34 | 21 | 12 | 8 | short-row exponent |
| `Endpoint.certificateWeight` | `Endpoint.lean` | def | yes | 33 | 21 | 2 | 16 | v = 51 + 41y |
| `Endpoint.balancedExponent` | `Endpoint.lean` | def | yes | 33 | 21 | 5 | 15 | E_* |
| `HeckeDetectorRowCount.crossing` | `Hecke/DetectorRowCountCrossing.lean` | def | yes | 32 | 21 | 7 | 10 | the crossing point |
| `HeckeDetectorRowCount.inverseExponent` | `Hecke/DetectorRowCountCrossing.lean` | def | yes | 32 | 21 | 7 | 10 | inverse-side exponent |
| `Endpoint.endpoint_identity` | `Endpoint.lean` | thm | yes | 32 | 21 | 1 | 16 | the exact identity of paper lines 16040 to 16047 |
| `Endpoint.balanced_endpoint_margin` | `Endpoint.lean` | thm | yes | 31 | 21 | 3 | 15 | -E_* ≥ 49/440640 |
| `HeckeDetectorRowCount.plainExponent` | `Hecke/DetectorRowCountCrossing.lean` | def | yes | 31 | 20 | 5 | 11 | plain-side exponent |
| `HeckeDetectorRowCount.longExponent` | `Hecke/DetectorRowCountCrossing.lean` | def | yes | 30 | 21 | 8 | 8 | 1 - δ + (5/6 - δ)(t - 1) |
| `Parameters.exists_central_budget` | `ParametersCentralBudget.lean` | thm | yes | 14 | 7 | 2 | 6 | the budget behind `central_budget` |
| `Parameters.exists_distinct_slot_lengths` | `ParametersSlotLengths.lean` | thm | yes | 15 | 8 | 1 | 7 | slot lengths summing to 1/6 |
| `Parameters.compensated_geometry` | `Parameters.lean` | thm | no | 0 | 0 | 0 | none | section 5.1 |
| `Endpoint.balanced_endpoint_strict` | `Endpoint.lean` | thm | no | 0 | 0 | 0 | none | -E_* > 1/10000 |

### 5.4 The census of hardcoded constants

The census reads, for every public declaration of an `OAI.NumberTheory.DirichletL`
module, the numeral quotients in its statement and, for a definition, in its body. It
sorts them into four classes *(measured, both sessions, identical output)*:

| class | what it looks for | declarations | in the cone | modules | modules with a cone declaration |
| --- | --- | ---: | ---: | ---: | ---: |
| derived geometry | 17/48 (l_x), 23/48 (l_y), 13/16 (h), 11/16 (offset of C_II), 3/16 (C_II(7/8)), 1/48 (C_0), 5/16 (l_y - l) | 117 | 98 | 69 | 57 |
| row counts | the row-count definitions of `Endpoint`, `HeckeDetectorRowCount` and `HeckeInverseAmplification`, or the literals 37/18, 23/37, 35/54, 7/9, 49/440640, 139/96, 8/39, 7/37 | 77 | 62 | 38 | 31 |
| target | 7/8 | 301 | 204 | 81 | 64 |
| union of the three | | 449 | 329 | 147 | 120 |
| raw only | 1/6, 5/6 or 1/8 and no derived constant (this row overlaps the target and row-count rows) | 419 | 308 | 247 | 202 |

Per constant, declarations carrying it (all / in the cone) *(measured)*: 1/6 399/297,
5/6 152/116, 1/8 38/28, 17/48 78/67, 23/48 73/62, 13/16 52/43, 11/16 39/32, 3/16 41/33,
1/48 16/11, 5/16 1/0, 7/8 301/204, 37/18 1/1, 23/37 4/3, 35/54 1/1, 7/9 2/2,
49/440640 15/10, 139/96 1/0, 8/39 1/0, 7/37 12/9. The paper sources of the row-count
literals: `D_x\ge37/18>0` (line 15352), `r_*(1)=...\ge\frac{23}{37}` (line 15355),
`\((1-23/37)/2=7/37\)` (line 15382), `\frac8{39}-\frac7{37}=\frac{23}{1443}>0.`
(line 15387) and `\frac{35}{54}\le\mathcal J\le\frac52.` (line 15976) *(cited)*.

**Reach** *(measured)*. The 449 union declarations and everything downstream of them
are 690 public declarations, 478 of them in the cone: 2.5% of its 18,766, in 173 of its
2,656 modules. 364 declarations carry a raw 1/6, 5/6 or 1/8 and nothing in the union,
266 of them in the cone, in 190 modules; counting them as well gives 1,190 cone
declarations (6.3%) in 552 modules. The 120 modules with a union declaration in the cone hold
15,510 lines (837,116 bytes) of source, 3.3% of the closure's 25.0 MB *(measured;
the percentages are arithmetic)*. 62 union declarations have no downstream user at all.

**A text cross-check, and a fault planted in it** *(measured)*. For each derived
constant, 7/8, 49/440640 and 37/18, every module where the Lean-level census finds the
constant must contain it in its source text. All ten pass, and the text finds the
constant in as many files or a few more (13/16: 38 modules in Lean, 39 files in text;
3/16: 32 and 36; 1/48: 14 and 16; 7/8: 81 and 82; 49/440640: 15 and 17; the rest
equal), the extra files holding the constant only inside proofs or comments, which the
census does not read. A fake census row placing 17/48 in `Endpoint.lean`, whose text
has none, turns the check red: `TEXT CROSS-CHECK FAIL (1)`, naming that module. The
first session's script printed that verdict but exited 0 either way; the second
session made it exit 1 on failure, so it now fails closed.

**Limits of the census** *(inferred)*. It sees a constant only as a quotient of two
numerals: `2/12`, `0.125`, `6⁻¹` or a number computed from other definitions would
escape it, and it does not read the proofs of theorems. Raw 1/6 also
denotes the pole z = 1/6 and the sextic power, and raw 5/6 also denotes the slope α, so
the raw-only class over-counts the geometry. Downstream reach is complete for
dependence through definitions, because the dump follows every constant a kernel term
names.

### 5.5 The full lists

The row-count class, every declaration with its file and its downstream reach
*(measured; "constants" lists the literals found and the row-count definitions its
statement uses)*:

<details>
<summary>77 declarations, 62 in the cone</summary>

| declaration | file (under `OAI/NumberTheory/DirichletL/`) | kind | in cone | downstream decls | downstream modules | constants |
| --- | --- | --- | :-: | ---: | ---: | --- |
| `HeckeDetectorRawFiber.Fiber` | `Hecke/DetectorRawFiber.lean` | induct | yes | 159 | 61 | 7/37 |
| `Parameters.HighData` | `ParametersHighData.lean` | induct | yes | 116 | 32 | 13/16, 49/440640, 7/8 |
| `HeckeDetectorBatch.Batch` | `Hecke/DetectorBatch.lean` | induct | yes | 83 | 47 | 7/37 |
| `Endpoint.balanceDenominator` | `Endpoint.lean` | def | yes | 76 | 36 | uses Endpoint.denominator, Endpoint.primeWeight |
| `Endpoint.balancedCutoff` | `Endpoint.lean` | def | yes | 74 | 36 | uses Endpoint.balanceDenominator, Endpoint.primeWeight |
| `HeckeDetectorFiberPartition.toFiber` | `Hecke/DetectorFiberPartition.lean` | def | yes | 74 | 43 | 7/37 |
| `Endpoint.balancedRowCount` | `Endpoint.lean` | def | yes | 61 | 31 | uses Endpoint.balancedCutoff |
| `HeckeDetectorAdaptiveCutoff.cutoff` | `Hecke/DetectorAdaptiveCutoff.lean` | def | yes | 59 | 31 | uses Endpoint.balancedCutoff |
| `Endpoint.denominator_bounds` | `Endpoint.lean` | thm | yes | 48 | 29 | 7/9; uses Endpoint.denominator |
| `Endpoint.primeWeight_bounds` | `Endpoint.lean` | thm | yes | 48 | 29 | 7/9; uses Endpoint.primeWeight |
| `Endpoint.balanceDenominator_bounds` | `Endpoint.lean` | thm | yes | 47 | 29 | 35/54; uses Endpoint.balanceDenominator |
| `HeckeDetectorRowCount.balanced_cutoff_bounds` | `Hecke/DetectorRowCountEndpoint.lean` | thm | yes | 41 | 26 | uses Endpoint.balancedCutoff |
| `HeckeInverseAmplification.amplified_exponent` | `Hecke/InverseAmplificationBudget.lean` | thm | yes | 35 | 24 | uses HeckeInverseAmplification.amplificationPower |
| `HeckeDetectorRowCount.shortExponent` | `Hecke/DetectorRowCountCrossing.lean` | def | yes | 34 | 21 | uses HeckeDetectorRowCount.denominator, HeckeDetectorRowCount.primeWeight |
| `HeckeInverseAmplification.amplificationPower_upper` | `Hecke/InverseAmplificationBudget.lean` | thm | yes | 34 | 24 | uses HeckeInverseAmplification.amplificationPower |
| `HeckeInverseAmplification.amplified_exponent_le` | `Hecke/InverseAmplificationBudget.lean` | thm | yes | 34 | 24 | uses HeckeInverseAmplification.amplificationPower, HeckeInverseAmplification.sourceExponent |
| `Endpoint.balancedExponent` | `Endpoint.lean` | def | yes | 33 | 21 | 1/48, 13/16; uses Endpoint.balancedRowCount |
| `HeckeInverseAmplification.amplificationPower_nonneg` | `Hecke/InverseAmplificationBudget.lean` | thm | yes | 33 | 23 | uses HeckeInverseAmplification.amplificationPower |
| `HeckeInverseAmplification.amplified_norm_dominates` | `Hecke/InverseAmplificationPowers.lean` | thm | yes | 33 | 23 | uses HeckeInverseAmplification.amplificationPower |
| `HeckeInverseAmplification.exists_amplification_budget` | `Hecke/InverseAmplificationBudget.lean` | thm | yes | 33 | 23 | uses HeckeInverseAmplification.amplificationPower, HeckeInverseAmplification.sourceExponent |
| `Endpoint.endpoint_identity` | `Endpoint.lean` | thm | yes | 32 | 21 | uses Endpoint.balanceDenominator, Endpoint.balancedExponent, Endpoint.certificateWeight |
| `HeckeDetectorRowCount.crossing` | `Hecke/DetectorRowCountCrossing.lean` | def | yes | 32 | 21 | uses HeckeDetectorRowCount.denominator |
| `HeckeInverseAmplification.no_slot_endpoint` | `Hecke/InverseAmplificationEndpoint.lean` | thm | yes | 32 | 22 | uses HeckeInverseAmplification.sourceExponent |
| `Endpoint.balanced_endpoint_margin` | `Endpoint.lean` | thm | yes | 31 | 21 | 49/440640; uses Endpoint.balancedExponent |
| `HeckeDetectorRowCount.denominator_lower` | `Hecke/DetectorRowCountCrossing.lean` | thm | yes | 31 | 21 | 37/18; uses HeckeDetectorRowCount.denominator |
| `HeckeInverseAmplification.no_slot_rowwise_endpoint` | `Hecke/InverseAmplificationRowwise.lean` | thm | yes | 31 | 21 | uses HeckeInverseAmplification.sourceExponent |
| `HeckeDetectorNoSlotInverseCount.no_slot_inverse_count` | `Hecke/DetectorNoSlotInverseCount.lean` | thm | yes | 30 | 20 | uses HeckeInverseAmplification.sourceExponent |
| `ProbeHighRowFamily.adaptiveRowExponent` | `PrimeRows/NonfloorSourceCount.lean` | def | yes | 30 | 21 | uses Endpoint.balancedRowCount |
| `ProbeHighRowFamily.physical_slot_widths` | `Detector/DetectorBatch.lean` | thm | yes | 29 | 20 | 7/37 |
| `ProbeHighRowFamily.retainedSourceBatch` | `Detector/DetectorBatch.lean` | def | yes | 29 | 20 | 7/37 |
| `HeckeDetectorRowCount.crossing_bounds` | `Hecke/DetectorRowCountCrossing.lean` | thm | yes | 28 | 20 | 23/37; uses HeckeDetectorRowCount.crossing |
| `HeckeDetectorRowCount.inverse_at_crossing` | `Hecke/DetectorRowCountCrossing.lean` | thm | yes | 28 | 20 | uses HeckeDetectorRowCount.crossing, HeckeDetectorRowCount.denominator, HeckeDetectorRowCount.inverseExponent, HeckeDetectorRowCount.shortExponent |
| `HeckeDetectorRowCount.plain_at_crossing` | `Hecke/DetectorRowCountCrossing.lean` | thm | yes | 28 | 20 | uses HeckeDetectorRowCount.crossing, HeckeDetectorRowCount.denominator, HeckeDetectorRowCount.plainExponent, HeckeDetectorRowCount.shortExponent |
| `ProbeCentralExponent.balanced_source_margin` | `Detector/CentralExponent.lean` | thm | yes | 28 | 18 | 13/16, 3/16; uses Endpoint.balancedRowCount |
| `ProbeHighRowFamily.balanced_count_range` | `Detector/CentralMixedMargins.lean` | thm | yes | 28 | 18 | uses Endpoint.balancedRowCount |
| `HeckeDetectorRowCount.long_count_bound` | `Hecke/DetectorRowCountCrossing.lean` | thm | yes | 27 | 19 | uses HeckeDetectorRowCount.longExponent |
| `HeckeDetectorRowCount.plain_capacity_comparison` | `Hecke/DetectorRowCountCrossing.lean` | thm | yes | 27 | 19 | uses HeckeDetectorRowCount.plainExponent |
| `HeckeDetectorRowCount.selected_short_bound` | `Hecke/DetectorRowCountCrossing.lean` | thm | yes | 27 | 19 | uses HeckeDetectorRowCount.crossing, HeckeDetectorRowCount.inverseExponent, HeckeDetectorRowCount.plainExponent, HeckeDetectorRowCount.shortExponent |
| `HeckeDetectorRowCount.short_ge_base` | `Hecke/DetectorRowCountCrossing.lean` | thm | yes | 27 | 19 | uses HeckeDetectorRowCount.shortExponent |
| `ProbeHighRowFamily.balanced_mixed_margin` | `Detector/CentralMixedMargins.lean` | thm | yes | 27 | 18 | 13/16, 3/16; uses Endpoint.balancedRowCount |
| `HeckeDetectorBranchBudget.inverse_marked_loss` | `Hecke/DetectorBranchBudget.lean` | thm | yes | 26 | 18 | uses HeckeDetectorRowCount.inverseExponent |
| `HeckeDetectorBranchBudget.inverse_requested_capacity` | `Hecke/DetectorBranchBudget.lean` | thm | yes | 26 | 18 | 23/37, 7/37 |
| `HeckeDetectorBranchBudget.plain_requested_capacity` | `Hecke/DetectorBranchBudget.lean` | thm | yes | 26 | 18 | 7/37; uses HeckeDetectorRowCount.crossing |
| `HeckeDetectorRawFiber.Fiber.inverse_marked_count` | `Hecke/DetectorRawBranches.lean` | thm | yes | 26 | 18 | 7/37 |
| `HeckeDetectorRawFiber.Fiber.plain_marked_count` | `Hecke/DetectorRawBranches.lean` | thm | yes | 26 | 18 | 7/37 |
| `HeckeDetectorRowCount.count_bound_of_source_branches` | `Hecke/DetectorRowCountOptimization.lean` | thm | yes | 26 | 18 | 23/37; uses HeckeDetectorRowCount.crossing, HeckeDetectorRowCount.inverseExponent, HeckeDetectorRowCount.longExponent, HeckeDetectorRowCount.shortExponent |
| `ProbeHighRowFamily.balanced_mixed_saving` | `Detector/CentralMixedMargins.lean` | thm | yes | 26 | 17 | 13/16, 3/16, 49/440640; uses Endpoint.balancedRowCount |
| `HeckeDetectorCountFromMoments.count_from_raw_moments` | `Hecke/DetectorCountFromMoments.lean` | thm | yes | 25 | 17 | uses HeckeDetectorRowCount.longExponent, HeckeDetectorRowCount.shortExponent |
| `HeckeDetectorRowCount.denominator_endpoint` | `Hecke/DetectorRowCountEndpoint.lean` | thm | yes | 25 | 16 | uses Endpoint.denominator, HeckeDetectorRowCount.denominator |
| `HeckeDetectorRowCount.primeWeight_endpoint` | `Hecke/DetectorRowCountEndpoint.lean` | thm | yes | 25 | 16 | uses Endpoint.primeWeight, HeckeDetectorRowCount.primeWeight |
| `ProbeHighRowFamily.adaptive_mixed_saving` | `PrimeRows/NonfloorExponent.lean` | thm | yes | 25 | 16 | 13/16, 3/16, 49/440640 |
| `HeckeDetectorRowCount.balanced_count_identity` | `Hecke/DetectorRowCountEndpoint.lean` | thm | yes | 24 | 16 | uses Endpoint.balancedCutoff, Endpoint.balancedRowCount, HeckeDetectorRowCount.longExponent, HeckeDetectorRowCount.shortExponent |
| `HeckeDetectorAdaptiveCutoff.cutoff_eq_balanced` | `Hecke/DetectorAdaptiveCutoff.lean` | thm | yes | 23 | 15 | uses Endpoint.balancedCutoff |
| `HeckeDetectorFixedAmplitudeCount.fixed_amplitude_count_from_raw_moments` | `Hecke/DetectorFixedAmplitudeCount.lean` | thm | yes | 23 | 15 | uses HeckeDetectorRowCount.longExponent, HeckeDetectorRowCount.shortExponent |
| `ProbeFinalAssembly.balanced_source_count_from_raw_moments` | `Detector/FinalAssemblySourceCount.lean` | thm | yes | 22 | 13 | uses Endpoint.balancedRowCount |
| `ProbeHighRowFamily.balanced_adaptive_count_from_raw_moments` | `PrimeRows/NonfloorCount.lean` | thm | yes | 22 | 14 | uses Endpoint.balancedRowCount |
| `ProbeFinalAssembly.actual_nonfloor_cube_arithmetic` | `Detector/FinalAssemblyArithmetic.lean` | thm | yes | 19 | 10 | 13/16, 3/16, 49/440640 |
| `ProbeFinalAssembly.actual_nonfloor_cube_norm` | `Detector/FinalAssemblyIntegral.lean` | thm | yes | 18 | 9 | 13/16, 17/48, 23/48, 3/16, 49/440640 |
| `ProbeFinalAssembly.actual_normalized_nonfloor_cube` | `Detector/FinalAssemblyNormalized.lean` | thm | yes | 17 | 8 | 13/16, 17/48, 23/48, 3/16, 49/440640 |
| `ProbeFinalAssembly.actual_nonfloor_rows_saving` | `Detector/FinalAssemblyCollected.lean` | thm | yes | 16 | 7 | 13/16, 17/48, 23/48, 3/16, 49/440640 |
| `ProbeFinalAssembly.actual_high_probe_from_raw_moments` | `Detector/FinalAssemblyHigh.lean` | thm | yes | 15 | 6 | 1/48, 11/16, 13/16, 17/48, 23/48, 49/440640, 7/8 |
| `Parameters.exists_central_budget` | `ParametersCentralBudget.lean` | thm | yes | 14 | 7 | 13/16, 3/16, 49/440640, 7/8 |
| `ProbeHighRowFamily.balanced_source_count_from_raw_moments` | `PrimeRows/NonfloorSourceCount.lean` | thm | no | 7 | 7 | uses Endpoint.balancedRowCount |
| `ProbeHighRowFamily.actual_nonfloor_cube_arithmetic` | `PrimeRows/NonfloorArithmetic.lean` | thm | no | 4 | 4 | 13/16, 3/16, 49/440640 |
| `ProbeHighRowFamily.actual_nonfloor_cube_norm` | `PrimeRows/NonfloorIntegral.lean` | thm | no | 3 | 3 | 13/16, 17/48, 23/48, 3/16, 49/440640 |
| `ProbeHighRowFamily.actual_normalized_nonfloor_cube` | `PrimeRows/NonfloorNormalized.lean` | thm | no | 2 | 2 | 13/16, 17/48, 23/48, 3/16, 49/440640 |
| `ProbeHighRowFamily.actual_nonfloor_rows_saving` | `PrimeRows/NonfloorCollected.lean` | thm | no | 1 | 1 | 13/16, 17/48, 23/48, 3/16, 49/440640 |
| `Endpoint.balanced_endpoint_strict` | `Endpoint.lean` | thm | no | 0 | 0 | uses Endpoint.balancedExponent |
| `HeckeDetectorBatchCount.batch_count_from_raw_moments` | `Hecke/DetectorBatchCount.lean` | thm | no | 0 | 0 | uses HeckeDetectorRowCount.longExponent, HeckeDetectorRowCount.shortExponent |
| `HeckeDetectorRawFiber.Fiber.mk.congr_simp` | `Moments/NaturalFixedRaySourceCapacity.lean` | thm | no | 0 | 0 | 7/37 |
| `HeckeDetectorRowCount.balanced_endpoint_with_loss` | `Hecke/DetectorRowCountEndpoint.lean` | thm | no | 0 | 0 | 1/48, 13/16; uses Endpoint.balancedCutoff, HeckeDetectorRowCount.longExponent, HeckeDetectorRowCount.shortExponent |
| `HeckeDetectorRowCount.crossing_average` | `Hecke/DetectorRowCountCrossing.lean` | thm | no | 0 | 0 | uses HeckeDetectorRowCount.denominator, HeckeDetectorRowCount.inverseExponent, HeckeDetectorRowCount.plainExponent, HeckeDetectorRowCount.shortExponent |
| `HeckeDetectorRowCount.inverse_capacity_exponent` | `Hecke/DetectorRowCountCrossing.lean` | thm | no | 0 | 0 | uses HeckeDetectorRowCount.inverseExponent |
| `HeckeDetectorRowCount.prime_supply_margin` | `Hecke/DetectorRowCountCrossing.lean` | thm | no | 0 | 0 | 7/37, 8/39 |
| `HeckeDetectorRowCount.strict_inverse_capacity` | `Hecke/DetectorRowCountCrossing.lean` | thm | no | 0 | 0 | 23/37, 7/37 |
| `ProbeCentralExponent.frequency_slope_bounds` | `Detector/CentralExponent.lean` | thm | no | 0 | 0 | 139/96 |
| `ProbeHighRowFamily.actual_high_probe_from_raw_moments` | `PrimeRows/HighFromMoments.lean` | thm | no | 0 | 0 | 1/48, 11/16, 13/16, 17/48, 23/48, 49/440640, 7/8 |

</details>

The derived-geometry class, likewise *(measured)*:

<details>
<summary>117 declarations, 98 in the cone</summary>

| declaration | file (under `OAI/NumberTheory/DirichletL/`) | kind | in cone | downstream decls | downstream modules | constants |
| --- | --- | --- | :-: | ---: | ---: | --- |
| `Parameters.HighData` | `ParametersHighData.lean` | induct | yes | 116 | 32 | 13/16, 49/440640, 7/8 |
| `ProbeCentralExponent.sourceExponent` | `Detector/CentralExponent.lean` | def | yes | 43 | 25 | 17/48, 23/48 |
| `ProbeCentralExponent.relativeExponent` | `Detector/CentralExponent.lean` | def | yes | 37 | 22 | 13/16 |
| `ProbeCentralExponent.original_exponent_identity` | `Detector/CentralExponent.lean` | thm | yes | 35 | 22 | 3/16 |
| `ProbeCentralExponent.relative_extend` | `Detector/CentralExponent.lean` | thm | yes | 35 | 22 | 13/16 |
| `Endpoint.balancedExponent` | `Endpoint.lean` | def | yes | 33 | 21 | 1/48, 13/16; uses Endpoint.balancedRowCount |
| `PrincipalSignalComparison.slotResidue` | `PrincipalSignalComparison.lean` | def | yes | 32 | 14 | 11/16 |
| `ProbePhysical.source_scale_ratio` | `Detector/LowSourceScales.lean` | thm | yes | 31 | 17 | 17/48, 23/48 |
| `ProbePhysical.source_scale_square` | `Detector/LowSourceScales.lean` | thm | yes | 31 | 17 | 17/48, 23/48 |
| `PrincipalSignalComparison.kernelEnvelope` | `PrincipalSignalComparison.lean` | def | yes | 30 | 14 | 11/16 |
| `ProbeHighRowFamily.large_geometric_scale` | `PrimeRows/GeometricTail.lean` | thm | yes | 30 | 20 | 13/16 |
| `ProbePhysical.source_compensated_scale_admissible` | `Detector/LowSourceScales.lean` | thm | yes | 30 | 17 | 17/48, 23/48 |
| `ProbePhysical.source_gram_power` | `Detector/LowGramScale.lean` | thm | yes | 30 | 17 | 17/48, 23/48 |
| `ProbeCentralExponent.physical_scale_identity` | `Detector/CentralExponent.lean` | thm | yes | 29 | 20 | 17/48, 23/48 |
| `ProbeHighRowFamily.large_source_scale` | `PrimeRows/TailScales.lean` | thm | yes | 29 | 20 | 13/16, 17/48, 23/48 |
| `ProbeHighRowFamily.small_source_scale` | `PrimeRows/TailScales.lean` | thm | yes | 29 | 20 | 11/16, 17/48, 23/48 |
| `ProbePhysical.source_compensated_gram_scale` | `Detector/LowSourceScales.lean` | thm | yes | 29 | 17 | 17/48, 23/48 |
| `ProbePhysical.source_gram_sqrt_power` | `Detector/LowGramScale.lean` | thm | yes | 29 | 17 | 23/48, 3/16 |
| `ProbeCentralExponent.balanced_source_margin` | `Detector/CentralExponent.lean` | thm | yes | 28 | 18 | 13/16, 3/16; uses Endpoint.balancedRowCount |
| `ProbeHighRowFamily.large_geometric_sum` | `PrimeRows/GeometricTail.lean` | thm | yes | 28 | 19 | 13/16 |
| `ProbeHighRowFamily.large_geometric_summable` | `PrimeRows/GeometricTail.lean` | thm | yes | 28 | 19 | 13/16 |
| `ProbeHighRowFamily.large_physical_dyad_bound` | `PrimeRows/LargeDyad.lean` | thm | yes | 28 | 19 | 13/16, 17/48, 23/48 |
| `ProbePhysical.lowPhysicalScale_source` | `Detector/LowNominalGeometry.lean` | thm | yes | 28 | 18 | 17/48, 23/48 |
| `ProbePhysical.source_compensated_gram_sqrt` | `Detector/LowSourceScales.lean` | thm | yes | 28 | 17 | 17/48, 23/48, 3/16 |
| `PrincipalSignalComparison.slotResidue_bound_of_reciprocal_bound` | `PrincipalSignalComparison.lean` | thm | yes | 27 | 14 | 11/16, 7/8 |
| `ProbeCentralExponent.high_source_margin` | `Detector/CentralExponent.lean` | thm | yes | 27 | 18 | 13/16, 3/16 |
| `ProbeHighRowFamily.balanced_mixed_margin` | `Detector/CentralMixedMargins.lean` | thm | yes | 27 | 18 | 13/16, 3/16; uses Endpoint.balancedRowCount |
| `ProbeHighRowFamily.central_arithmetic_cost_bound` | `PrimeRows/CentralErrorSaving.lean` | thm | yes | 27 | 18 | 1/48, 13/16 |
| `ProbeHighRowFamily.central_source_crude_scale` | `PrimeRows/CentralErrorSaving.lean` | thm | yes | 27 | 18 | 17/48, 23/48 |
| `ProbeHighRowFamily.exists_large_tail_line` | `PrimeRows/GeometricTail.lean` | thm | yes | 27 | 18 | 13/16 |
| `ProbeHighRowFamily.large_physical_dyads_summable` | `PrimeRows/LargeTail.lean` | thm | yes | 27 | 18 | 13/16, 17/48, 23/48 |
| `ProbePhysical.lowGramFactor_source_bound` | `Detector/LowSourceScales.lean` | thm | yes | 27 | 17 | 17/48, 23/48, 3/16 |
| `PrincipalSignalComparison.exists_slotResidue_bound` | `PrincipalSignalComparison.lean` | thm | yes | 26 | 14 | 11/16, 7/8 |
| `PrincipalSignalComparison.source_power_identity` | `PrincipalSignalComparison.lean` | thm | yes | 26 | 14 | 11/16, 17/48 |
| `ProbeHighRowFamily.balanced_mixed_saving` | `Detector/CentralMixedMargins.lean` | thm | yes | 26 | 17 | 13/16, 3/16, 49/440640; uses Endpoint.balancedRowCount |
| `ProbeHighRowFamily.high_mixed_margin` | `Detector/CentralMixedMargins.lean` | thm | yes | 26 | 17 | 13/16, 3/16 |
| `ProbeHighRowFamily.large_physical_tail_arbitrary_saving` | `PrimeRows/LargeSaving.lean` | thm | yes | 26 | 17 | 13/16, 17/48, 23/48 |
| `ProbeHighRowFamily.small_physical_dyads_sum` | `PrimeRows/SmallTail.lean` | thm | yes | 26 | 17 | 11/16, 17/48, 23/48, 7/8 |
| `ProbePhysical.eventually_compensated_source_scales` | `Detector/LowSourceScales.lean` | thm | yes | 26 | 16 | 17/48, 23/48, 3/16 |
| `ProbePrincipalRemainderBounds.source_scale_identity` | `Detector/PrincipalRemainderBounds.lean` | thm | yes | 26 | 14 | 11/16, 13/16, 17/48, 23/48 |
| `PrincipalSignalComparison.normalized_source_double_residue` | `PrincipalSignalComparison.lean` | thm | yes | 25 | 14 | 11/16, 17/48 |
| `ProbeHighRowFamily.adaptive_mixed_saving` | `PrimeRows/NonfloorExponent.lean` | thm | yes | 25 | 16 | 13/16, 3/16, 49/440640 |
| `ProbeHighRowFamily.large_original_physical_tail` | `PrimeRows/PhysicalLargeTail.lean` | thm | yes | 25 | 16 | 13/16, 17/48, 23/48 |
| `ProbeHighRowFamily.small_original_physical_tail` | `PrimeRows/PhysicalSmallTail.lean` | thm | yes | 25 | 16 | 11/16, 17/48, 23/48, 7/8 |
| `ProbePhysical.eventually_original_slot_scales` | `Detector/LowSlotScales.lean` | thm | yes | 25 | 15 | 17/48, 23/48, 3/16 |
| `ProbePhysical.lowPhysicalScale_nominal_bound` | `Detector/LowNominalGeometry.lean` | thm | yes | 25 | 15 | 17/48, 23/48 |
| `PrincipalSignalComparison.raw_slot_integrable` | `PrincipalSignalComparison.lean` | thm | yes | 24 | 14 | 11/16 |
| `ProbeHighRowFamily.canonical_large_original_tail` | `PrimeRows/CanonicalTails.lean` | thm | yes | 24 | 15 | 13/16, 17/48, 23/48 |
| `ProbeHighRowFamily.canonical_small_original_tail` | `PrimeRows/CanonicalTails.lean` | thm | yes | 24 | 15 | 11/16, 17/48, 23/48, 7/8 |
| `ProbeHighRowFamily.original_row_cube_arbitrary_saving` | `PrimeRows/CubeErrorSaving.lean` | thm | yes | 24 | 15 | 1/48, 13/16, 17/48, 23/48 |
| `ProbePhysical.low_physical_inverse_normalized` | `Detector/LowPhysicalInverseBound.lean` | thm | yes | 24 | 14 | 17/48, 23/48 |
| `ProbePrincipalRemainderBounds.source_w_scale_identity` | `Detector/PrincipalRemainderBounds.lean` | thm | yes | 24 | 14 | 11/16, 13/16, 17/48, 23/48 |
| `ProbePrincipalRemainderBounds.source_z_scale_identity` | `Detector/PrincipalRemainderBounds.lean` | thm | yes | 24 | 14 | 11/16, 17/48, 23/48 |
| `PrincipalSignalComparison.sourceResidueIntegral_normalized` | `PrincipalSignalComparison.lean` | thm | yes | 23 | 14 | 17/48 |
| `PrincipalSignalComparison.source_double_residue_integrable` | `PrincipalSignalComparison.lean` | thm | yes | 23 | 14 | 17/48 |
| `ProbeHighRowFamily.canonical_probe_minus_central` | `PrimeRows/CanonicalReduction.lean` | thm | yes | 23 | 14 | 11/16, 13/16, 17/48, 23/48, 7/8 |
| `ProbeHighRowFamily.finite_cube_arbitrary_saving` | `PrimeRows/CubeFiniteError.lean` | thm | yes | 23 | 14 | 1/48, 13/16, 17/48, 23/48 |
| `ProbePhysical.low_central_compensated_tuple` | `Detector/LowCentralTuple.lean` | thm | yes | 23 | 13 | 17/48, 23/48, 3/16 |
| `ProbePrincipalRemainderBounds.source_remainders_power_bound` | `Detector/PrincipalRemainderBounds.lean` | thm | yes | 23 | 14 | 11/16, 13/16, 17/48, 23/48, 7/8 |
| `ProbePrincipalRemainderBounds.source_w_strict_exponent` | `Detector/PrincipalRemainderBounds.lean` | thm | yes | 23 | 14 | 11/16, 13/16 |
| `ProbePrincipalRemainderBounds.source_z_strict_exponent` | `Detector/PrincipalRemainderBounds.lean` | thm | yes | 23 | 14 | 11/16 |
| `PrincipalSignalComparison.exists_normalized_actual_source_bound` | `PrincipalSignalComparison.lean` | thm | yes | 22 | 13 | 11/16, 17/48, 7/8 |
| `ProbeHighRowFamily.canonical_probe_minus_cube` | `PrimeRows/CanonicalCubeReduction.lean` | thm | yes | 22 | 13 | 1/48, 11/16, 13/16, 17/48, 23/48, 7/8 |
| `ProbePhysical.compensation_scale_mass_bound` | `Detector/LowRemoteMass.lean` | thm | yes | 22 | 12 | 17/48, 23/48 |
| `ProbePhysical.eventually_low_physical_scales` | `Detector/LowGaussianRemote.lean` | thm | yes | 22 | 12 | 17/48, 23/48 |
| `ProbePhysical.low_central_gaussian_dyad` | `Detector/LowGaussianDyad.lean` | thm | yes | 22 | 12 | 17/48, 23/48, 3/16 |
| `ProbePrincipalRemainderBounds.source_remainders_strict_saving` | `Detector/PrincipalRemainderBounds.lean` | thm | yes | 22 | 13 | 11/16, 17/48, 23/48, 7/8 |
| `ProbeHighRowFamily.actual_global_floor_cube_norm` | `PrimeRows/CubeFloorGlobalIntegral.lean` | thm | yes | 21 | 12 | 17/48, 23/48 |
| `ProbeHighRowFamily.canonical_probe_exists_cube` | `PrimeRows/CanonicalCubeChoice.lean` | thm | yes | 21 | 12 | 1/48, 11/16, 13/16, 17/48, 23/48, 7/8 |
| `ProbePhysical.low_central_gaussian_dyads` | `Detector/LowGaussianCentral.lean` | thm | yes | 21 | 11 | 17/48, 23/48, 3/16 |
| `ProbePhysical.low_remote_gaussian_dyads` | `Detector/LowGaussianRemote.lean` | thm | yes | 21 | 11 | 17/48, 23/48 |
| `ProbePrincipalPhysical.physical_principal_residue_remainder` | `Detector/PrincipalPhysicalRemainder.lean` | thm | yes | 21 | 12 | 11/16, 17/48, 23/48, 7/8 |
| `ProbePrincipalResidueActual.normalized_actual_window_residue` | `Detector/PrincipalResidueActual.lean` | thm | yes | 21 | 12 | 11/16, 17/48, 7/8 |
| `ProbeCentralExponent.floor_source_margin` | `Detector/CentralExponent.lean` | thm | yes | 20 | 11 | 13/16, 3/16 |
| `ProbeHighRowFamily.actual_normalized_floor_cube` | `PrimeRows/CubeFloorNormalized.lean` | thm | yes | 20 | 11 | 17/48, 23/48 |
| `ProbeHighRowFamily.canonical_probe_exists_ray_cube` | `PrimeRows/CanonicalRayCube.lean` | thm | yes | 20 | 11 | 1/48, 11/16, 13/16, 17/48, 23/48, 7/8 |
| `ProbePhysical.low_all_gaussian_dyads` | `Detector/LowGaussianSum.lean` | thm | yes | 20 | 10 | 17/48, 23/48, 3/16 |
| `ProbePrincipalNormalized.actual_ray_principal_comparison` | `Detector/PrincipalNormalized.lean` | thm | yes | 20 | 11 | 11/16, 17/48, 23/48, 7/8 |
| `HeckeCommonProbe.PrimitiveContract` | `Hecke/CommonProbe.lean` | def | yes | 19 | 6 | 11/16, 3/16, 7/8 |
| `ProbeFinalAssembly.actual_nonfloor_cube_arithmetic` | `Detector/FinalAssemblyArithmetic.lean` | thm | yes | 19 | 10 | 13/16, 3/16, 49/440640 |
| `ProbeHighRowFamily.actual_floor_cube_saving` | `PrimeRows/CubeFloorSaving.lean` | thm | yes | 19 | 10 | 13/16, 17/48, 23/48, 3/16 |
| `ProbeHighRowFamily.actual_normalized_probe_transport` | `PrimeRows/NormalizedTransport.lean` | thm | yes | 19 | 10 | 1/48, 11/16, 13/16, 17/48, 23/48, 7/8 |
| `ProbePhysical.compensatedPhysicalProbe_low` | `Detector/LowCommonBound.lean` | thm | yes | 19 | 10 | 17/48, 23/48, 3/16 |
| `ProbeFinalAssembly.actual_nonfloor_cube_norm` | `Detector/FinalAssemblyIntegral.lean` | thm | yes | 18 | 9 | 13/16, 17/48, 23/48, 3/16, 49/440640 |
| `ProbeFinalAssembly.normalizedProbe` | `Detector/FinalAssemblySource.lean` | def | yes | 18 | 8 | 17/48, 23/48 |
| `ProbeHighRowFamily.actual_floor_rows_saving` | `PrimeRows/CubeFloorCollected.lean` | thm | yes | 18 | 9 | 13/16, 17/48, 23/48, 3/16 |
| `ProbeHighRowFamily.actual_normalized_probe_transport_saving` | `PrimeRows/NormalizedTransportSaving.lean` | thm | yes | 18 | 9 | 1/48, 11/16, 13/16, 17/48, 23/48, 3/16, 7/8 |
| `ProbePhysical.original_ray_compensatedPhysicalProbe_low` | `Detector/LowCommonBound.lean` | thm | yes | 18 | 9 | 17/48, 23/48, 3/16 |
| `ProbeFinalAssembly.actual_normalized_nonfloor_cube` | `Detector/FinalAssemblyNormalized.lean` | thm | yes | 17 | 8 | 13/16, 17/48, 23/48, 3/16, 49/440640 |
| `ProbeHighRowFamily.actual_nonfloor_probe_transport` | `PrimeRows/NonfloorTransport.lean` | thm | yes | 17 | 8 | 1/48, 11/16, 13/16, 17/48, 23/48, 3/16, 7/8 |
| `ProbePhysical.original_ray_compensatedPhysicalProbe_low_loss` | `Detector/LowWindowBound.lean` | thm | yes | 17 | 8 | 17/48, 23/48, 3/16 |
| `ProbeFinalAssembly.actual_nonfloor_rows_saving` | `Detector/FinalAssemblyCollected.lean` | thm | yes | 16 | 7 | 13/16, 17/48, 23/48, 3/16, 49/440640 |
| `ProbePhysical.original_normalized_compensatedPhysicalProbe_low` | `Detector/LowNormalized.lean` | thm | yes | 16 | 7 | 17/48, 23/48, 3/16 |
| `ProbeFinalAssembly.actual_high_probe_from_raw_moments` | `Detector/FinalAssemblyHigh.lean` | thm | yes | 15 | 6 | 1/48, 11/16, 13/16, 17/48, 23/48, 49/440640, 7/8 |
| `ProbeFinalAssembly.normalizedProbe_low` | `Detector/FinalAssemblySource.lean` | thm | yes | 15 | 6 | 3/16 |
| `Parameters.exists_central_budget` | `ParametersCentralBudget.lean` | thm | yes | 14 | 7 | 13/16, 3/16, 49/440640, 7/8 |
| `ProbeFinalAssembly.SourceData.probe_low` | `Detector/FinalAssemblyData.lean` | thm | yes | 14 | 5 | 3/16 |
| `ProbeFinalAssembly.fixed_high_bound` | `Detector/FinalAssemblyFixedHigh.lean` | thm | yes | 14 | 5 | 11/16, 7/8 |
| `ProbeHighRowFamily.actual_nonfloor_cube_arithmetic` | `PrimeRows/NonfloorArithmetic.lean` | thm | no | 4 | 4 | 13/16, 3/16, 49/440640 |
| `ProbeHighRowFamily.actual_nonfloor_cube_norm` | `PrimeRows/NonfloorIntegral.lean` | thm | no | 3 | 3 | 13/16, 17/48, 23/48, 3/16, 49/440640 |
| `ProbeHighRowFamily.actual_normalized_nonfloor_cube` | `PrimeRows/NonfloorNormalized.lean` | thm | no | 2 | 2 | 13/16, 17/48, 23/48, 3/16, 49/440640 |
| `PrincipalSignalComparison.slotResidue_isBigO` | `PrincipalSignalComparison.lean` | thm | no | 1 | 1 | 11/16, 7/8 |
| `ProbeHighRowFamily.actual_nonfloor_rows_saving` | `PrimeRows/NonfloorCollected.lean` | thm | no | 1 | 1 | 13/16, 17/48, 23/48, 3/16, 49/440640 |
| `ProbeHighRowFamily.original_row_rectangle_arbitrary_saving` | `PrimeRows/CentralErrorSaving.lean` | thm | no | 1 | 1 | 1/48, 13/16, 17/48, 23/48 |
| `ProbeHighRowFamily.small_row_scale_bound` | `PrimeRows/TailScales.lean` | thm | no | 1 | 1 | 11/16, 17/48, 23/48 |
| `HeckeDetectorRowCount.balanced_endpoint_with_loss` | `Hecke/DetectorRowCountEndpoint.lean` | thm | no | 0 | 0 | 1/48, 13/16; uses Endpoint.balancedCutoff, HeckeDetectorRowCount.longExponent, HeckeDetectorRowCount.shortExponent |
| `HeckeDetectorRowCount.high_bin_endpoint` | `Hecke/DetectorRowCountEndpoint.lean` | thm | no | 0 | 0 | 1/48, 13/16 |
| `Parameters.compensated_geometry` | `Parameters.lean` | thm | no | 0 | 0 | 17/48, 23/48, 3/16, 5/16 |
| `PrincipalSignalComparison.actualSlotResidue_isBigO` | `PrincipalSignalComparison.lean` | thm | no | 0 | 0 | 11/16, 7/8 |
| `PrincipalSignalComparison.exists_actualSlotResidue_bound` | `PrincipalSignalComparison.lean` | thm | no | 0 | 0 | 11/16, 7/8 |
| `ProbeCentralExponent.intermediate_source_margin` | `Detector/CentralExponent.lean` | thm | no | 0 | 0 | 3/16 |
| `ProbeHighRowFamily.actual_high_probe_from_raw_moments` | `PrimeRows/HighFromMoments.lean` | thm | no | 0 | 0 | 1/48, 11/16, 13/16, 17/48, 23/48, 49/440640, 7/8 |
| `ProbeHighRowFamily.finite_rectangle_arbitrary_saving` | `PrimeRows/CentralFiniteError.lean` | thm | no | 0 | 0 | 1/48, 13/16, 17/48, 23/48 |
| `ProbeHighRowFamily.mixed_physical_exponent` | `Detector/CentralDyadicWeight.lean` | thm | no | 0 | 0 | 17/48, 23/48 |
| `ProbeHighRowFamily.small_physical_dyad_bound` | `PrimeRows/SmallDyad.lean` | thm | no | 0 | 0 | 11/16, 17/48, 23/48, 7/8 |
| `ProbePhysical.originalPools_low_scales` | `Detector/LowOriginalPools.lean` | thm | no | 0 | 0 | 17/48, 23/48, 3/16 |
| `Supremum.max_normalized_signal_exponents` | `Supremum.lean` | thm | no | 0 | 0 | 11/16, 3/16 |

</details>

The union class by module, under `OAI/NumberTheory/DirichletL/`: declarations / of
them in the cone *(measured)*.

<details>
<summary>147 modules, 120 with a cone declaration</summary>

**(top level)** (9 modules): `PrincipalSlotEstimate` 33/21; `PrincipalSignalComparison` 23/20; `Endpoint` 10/9; `Supremum` 8/5; `Continuation` 2/2; `Nonvanishing` 2/2; `ParametersCentralBudget` 1/1; `ParametersHighData` 1/1; `Parameters` 1/0

**Hecke** (24 modules): `DetectorRowCountCrossing` 14/10; `Signal` 13/13; `CommonProbe` 6/6; `DetectorRowCountEndpoint` 6/4; `InverseAmplificationBudget` 5/5; `SignalShift` 5/3; `DetectorBranchBudget` 3/3; `SignalIdentity` 3/2; `DetectorAdaptiveCutoff` 2/2; `DetectorRawBranches` 2/2; `Dirichlet` 2/2; `SignalBounds` 2/1; `DetectorBatch` 1/1; `DetectorCountFromMoments` 1/1; `DetectorFiberPartition` 1/1; `DetectorFixedAmplitudeCount` 1/1; `DetectorNoSlotInverseCount` 1/1; `DetectorRawFiber` 1/1; `DetectorRowCountOptimization` 1/1; `InverseAmplificationEndpoint` 1/1; `InverseAmplificationPowers` 1/1; `InverseAmplificationRowwise` 1/1; `DetectorBatchCount` 1/0; `ZeroSupremum` 1/0

**Detector** (58 modules): `FiniteProductBounds` 30/21; `PrincipalContours` 21/16; `PrincipalRemainderBounds` 17/17; `PrincipalTransport` 14/10; `CentralExponent` 10/8; `FiniteProductX` 10/5; `LowSourceScales` 7/7; `GlobalCorrection` 6/6; `FinalAssemblyChosenData` 5/4; `CentralMixedMargins` 4/4; `GlobalHolomorphic` 4/4; `HighRowsFiniteBounds` 4/0; `PrincipalProduct` 4/0; `FinalAssembly[R]Bands` 3/3; `FinalAssemblySource` 3/3; `FinalAssemblyMomentInput` 3/1; `HighRowsSelectedRamified` 3/1; `FinalAssembly` 3/0; `HighRowsHolomorphic` 3/0; `DetectorBatch` 2/2; `FinalAssemblyUnconditional` 2/2; `HighRowsSelectedBound` 2/2; `HighRowsSelectedUnramified` 2/2; `LowCommonBound` 2/2; `LowGaussianRemote` 2/2; `LowGramScale` 2/2; `LowNominalGeometry` 2/2; `EulerRegion` 1/1; `FinalAssemblyArithmetic` 1/1; `FinalAssemblyCollected` 1/1; `FinalAssemblyData` 1/1; `FinalAssemblyFixedHigh` 1/1; `FinalAssemblyHigh` 1/1; `FinalAssemblyIntegral` 1/1; `FinalAssemblyNormalized` 1/1; `FinalAssemblySourceCount` 1/1; `GlobalRegion` 1/1; `HighRowsSelectedActual` 1/1; `HighRowsSelectedError` 1/1; `HighRowsSelectedTerms` 1/1; `LowCentralTuple` 1/1; `LowGaussianCentral` 1/1; `LowGaussianDyad` 1/1; `LowGaussianSum` 1/1; `LowNormalized` 1/1; `LowPhysicalInverseBound` 1/1; `LowRemoteMass` 1/1; `LowSlotScales` 1/1; `LowWindowBound` 1/1; `PrincipalNormalized` 1/1; `PrincipalPhysical` 1/1; `PrincipalPhysicalRemainder` 1/1; `PrincipalResidueActual` 1/1; `RayPoolThresholds` 1/1; `CentralDyadicWeight` 1/0; `EulerHolomorphic` 1/0; `HighRowsRamified` 1/0; `LowOriginalPools` 1/0

**PrimeRows** (54 modules): `Continuation` 7/0; `Product` 6/2; `GeometricTail` 4/4; `MarkedHolomorphic` 4/0; `SelectedBounds` 3/3; `CentralErrorSaving` 3/2; `TailScales` 3/2; `SelectedAnalytic` 3/0; `SelectedHolomorphic` 3/0; `Series` 3/0; `CanonicalTails` 2/2; `NonprincipalShift` 2/2; `PhysicalDyad` 2/2; `SourceTransport` 2/2; `NonfloorSourceCount` 2/1; `Ramified` 2/0; `CanonicalCubeChoice` 1/1; `CanonicalCubeReduction` 1/1; `CanonicalRayCube` 1/1; `CanonicalReduction` 1/1; `CubeErrorSaving` 1/1; `CubeFiniteError` 1/1; `CubeFloorCollected` 1/1; `CubeFloorGlobalIntegral` 1/1; `CubeFloorNormalized` 1/1; `CubeFloorSaving` 1/1; `DyadBound` 1/1; `DyadIntegral` 1/1; `FixedIntegral` 1/1; `LargeDyad` 1/1; `LargeSaving` 1/1; `LargeTail` 1/1; `NonfloorCount` 1/1; `NonfloorExponent` 1/1; `NonfloorTransport` 1/1; `NormalizedTransport` 1/1; `NormalizedTransportSaving` 1/1; `PhysicalBound` 1/1; `PhysicalLargeTail` 1/1; `PhysicalSmallTail` 1/1; `SlotSums` 1/1; `SmallTail` 1/1; `TupleBound` 1/1; `TupleSums` 1/1; `WGrowth` 1/1; `WZTransport` 1/1; `CentralFiniteError` 1/0; `HighFromMoments` 1/0; `NonfloorArithmetic` 1/0; `NonfloorCollected` 1/0; `NonfloorIntegral` 1/0; `NonfloorNormalized` 1/0; `PrincipalMask` 1/0; `SmallDyad` 1/0

**Energy** (1 modules): `ReferenceDeletionCapacity` 2/0

**Moments** (1 modules): `NaturalFixedRaySourceCapacity` 1/0

</details>

The raw-only class: 364 declarations in 235 modules carry 1/6, 5/6 or 1/8 and nothing
in the union, 266 of them in the cone *(measured)*. They are candidates, not confirmed
carriers of the geometry. Of the 10 that carry 1/8, for example,
`CenteredMomentFirstAnnularMajorant.weight_zero_low` bounds the support of a smooth
weight, `lemma weight_zero_low (x:ℝ)(hx:x≤1/8):weight x=0` (`Moments/FirstAnnularMajorant.lean`
line 23), and `ConcreteCompactWeight.bumpData` is a bump function with radii 1/8 and 1/4
(`Mellin/CompactWeights.lean` lines 169 to 170); neither uses b *(cited)*. The ten:

| declaration | file (under `OAI/`) | in cone | downstream decls | raw values |
| --- | --- | :-: | ---: | --- |
| `CenteredMomentFirstAnnularMajorant.weight_zero_low` | `NumberTheory/DirichletL/Moments/FirstAnnularMajorant.lean` | yes | 53 | 1/8 |
| `CenteredMomentFirstAnnularMajorant.weight_support` | `NumberTheory/DirichletL/Moments/FirstAnnularMajorant.lean` | yes | 52 | 1/8 |
| `CenteredMomentFirstAmplificationChoice.primeTest` | `NumberTheory/DirichletL/Moments/FirstAmplificationChoice.lean` | yes | 41 | 1/8 |
| `ProbeFinalAssembly.CountParameters` | `NumberTheory/DirichletL/Detector/FinalAssemblyCountParameters.lean` | yes | 39 | 1/8, 5/6 |
| `HeckeDetectorRowCount.capacity_loss` | `NumberTheory/DirichletL/Hecke/DetectorRowCountCrossing.lean` | yes | 28 | 1/8 |
| `ProbeFinalAssembly.adaptive_source_count_from_raw_moments` | `NumberTheory/DirichletL/Detector/FinalAssemblySourceCount.lean` | yes | 21 | 1/8, 5/6 |
| `ProbeFinalAssembly.actual_nonfloor_class_from_raw_moments` | `NumberTheory/DirichletL/Detector/FinalAssemblyClass.lean` | yes | 20 | 1/6, 1/8, 5/6 |
| `ConcreteCompactWeight.bumpData` | `NumberTheory/DirichletL/Mellin/CompactWeights.lean` | no | 30 | 1/8 |
| `ProbeHighRowFamily.adaptive_source_count_from_raw_moments` | `NumberTheory/DirichletL/PrimeRows/NonfloorSourceCount.lean` | no | 6 | 1/8, 5/6 |
| `ProbeHighRowFamily.actual_nonfloor_class_from_raw_moments` | `NumberTheory/DirichletL/PrimeRows/NonfloorClass.lean` | no | 5 | 1/6, 1/8, 5/6 |

By module, declarations / of them in the cone *(measured)*; the per-declaration list,
with downstream counts, is `analysis-session2/census_downstream.tsv` in the cache and is
regenerated in seconds from the dump:

<details>
<summary>235 modules, 364 declarations, 266 in the cone</summary>

**(top level)** (10 modules): `CenteredExceptionalCount` 14/6; `PrincipalMellinResidues` 6/5; `PrincipalSlotEstimate` 6/5; `PrincipalSignalComparison` 4/2; `CenteredExceptionalProfile` 3/2; `ContinuationContour` 2/2; `ParametersSlotLengths` 2/2; `RayPrimeNormalizer` 2/1; `PrincipalMellinGrowth` 2/0; `Continuation` 1/1

**Hecke** (7 modules): `DetectorRowCountCrossing` 2/2; `Signal` 2/2; `DetectorAdaptiveCutoff` 1/1; `DetectorHighBatchCount` 1/1; `DetectorHighCount` 1/1; `DetectorRowCountEndpoint` 1/1; `SignalShift` 1/1

**Detector** (64 modules): `HighRowsLocal` 5/4; `CompensationActual` 3/3; `InitialRows` 3/3; `MarkedLocal` 3/3; `RayNormalization` 3/3; `RaySlots` 3/3; `HighEulerLocal` 3/2; `MarkedProduct` 3/2; `FinalAssemblySourceCount` 2/2; `GramPrefactor` 2/2; `HighExcludedLocal` 2/2; `HighRowsRegion` 2/2; `LowGramExceptional` 2/2; `LowInverseNormalize` 2/2; `PrincipalResidueActual` 2/2; `SpectralCompensation` 2/2; `FiniteProductBounds` 2/1; `GlobalCorrection` 2/1; `RadialMellin` 2/1; `SourceExclusions` 2/1; `HighEuler` 2/0; `PrincipalContours` 2/0; `CentralClassArithmetic` 1/1; `DetectorInverseFields` 1/1; `DetectorInverseRawField` 1/1; `FinalAssemblyClass` 1/1; `FinalAssemblyCountParameters` 1/1; `GramBound` 1/1; `GramFrequencyMass` 1/1; `GramFrequencySummation` 1/1; `GramIdealMass` 1/1; `GramIdealSummation` 1/1; `GramInfiniteEstimate` 1/1; `GramSourceEstimate` 1/1; `HighAbsolute` 1/1; `HighDeletion` 1/1; `HighEulerRational` 1/1; `HighExcludedEuler` 1/1; `HighLFactorization` 1/1; `HighRowsExcluded` 1/1; `HighSeries` 1/1; `HighValuations` 1/1; `LowGaussianRemote` 1/1; `LowGramApplied` 1/1; `LowGramIntegrated` 1/1; `LowGramScale` 1/1; `LowNominalEnergy` 1/1; `LowNominalGeometry` 1/1; `LowReflectedLength` 1/1; `LowRemoteMass` 1/1; `LowSelectedBound` 1/1; `LowSlotScales` 1/1; `LowTupleGram` 1/1; `MarkedEuler` 1/1; `MarkedRational` 1/1; `MellinBoundary` 1/1; `NormalProduct` 1/1; `PrincipalInput` 1/1; `SourceAmplitudeClasses` 1/1; `SourceBatch` 1/1; `TuplePrincipal` 1/1; `HighRowsEuler` 1/0; `LowReflectedExponent` 1/0; `PrincipalProduct` 1/0

**PrimeRows** (27 modules): `CubeSlotExponent` 3/3; `MarkedLocal` 3/3; `SelectedAgreement` 3/3; `Euler` 3/1; `MarkedContinuation` 2/2; `MarkedSubset` 2/2; `Agreement` 2/1; `Ideal` 2/1; `MarkedCompensation` 2/1; `MarkedNormalization` 2/0; `MarkedProduct` 2/0; `NonfloorSourceCount` 2/0; `CentralErrorSaving` 1/1; `CentralFiniteError` 1/1; `CubeFloorArithmetic` 1/1; `CubeFloorGlobal` 1/1; `CubeNormalizer` 1/1; `FiniteNormalization` 1/1; `FirstTail` 1/1; `MarkedCoordinates` 1/1; `MarkedEuler` 1/1; `NonfloorCount` 1/1; `Ramified` 1/1; `Unramified` 1/1; `NonfloorClass` 1/0; `Origin` 1/0; `Series` 1/0

**Energy** (37 modules): `NaturalSourceAdmission` 3/2; `CanonicalRightSourceColumn` 2/2; `FirstHighExceptionalPowers` 2/2; `FirstRightAdmission` 2/2; `FirstLiveAdmission` 2/1; `FirstTwoSeedAdmission` 2/1; `CanonicalAmplifiedUniform` 1/1; `CanonicalAnnularPower` 1/1; `CanonicalErrorAdmitted` 1/1; `CanonicalErrorGaussian` 1/1; `CanonicalErrorHomogeneous` 1/1; `CanonicalErrorPaid` 1/1; `CanonicalErrorPower` 1/1; `CanonicalErrorSubsets` 1/1; `CanonicalErrorUniform` 1/1; `CanonicalHighColumn` 1/1; `CanonicalHighPhysical` 1/1; `CanonicalHighSource` 1/1; `CanonicalLowColumn` 1/1; `CanonicalLowPhysical` 1/1; `CanonicalLowSource` 1/1; `CanonicalMainGaussian` 1/1; `CanonicalMainHomogeneous` 1/1; `CanonicalMainPaid` 1/1; `CanonicalMainSeparated` 1/1; `CanonicalMainSeparatedPower` 1/1; `CanonicalMainSubsets` 1/1; `CanonicalMainUniform` 1/1; `CanonicalNestedReference` 1/1; `CanonicalReferencePaid` 1/1; `CanonicalUniformReference` 1/1; `ChildEnvelopeFitting` 1/1; `InputParentCapacity` 1/1; `NaturalLowSourceBound` 1/1; `PositiveLowBandSource` 1/1; `PositiveLowSourceControlled` 1/1; `ReferenceDeletionCapacity` 1/0

**Moments** (65 modules): `SecondPhysicalLedger` 5/5; `FirstNestedSeededGaussianPower` 5/4; `FirstExceptionalPrefactor` 5/0; `FirstAmplifiedFourCoefficients` 4/4; `FirstMixedExceptionalLow` 4/2; `FirstAmplifiedPaidAdmission` 3/3; `AllocatedChildCapacity` 3/0; `FiniteProfileExceptionalPhysicalBudget` 2/2; `FirstAnnularMajorant` 2/2; `FirstMixedNormalizationActual` 2/2; `FixedQForcingCount` 2/2; `FirstAmplifiedActiveAffine` 2/1; `FirstExceptionalPrefactorActual` 2/0; `FirstMixedExceptionalCap` 2/0; `FirstMixedExceptionalDeclared` 2/0; `HeckeExceptionalEnergy` 2/0; `SecondExceptionalBudget` 2/0; `SecondExceptionalPhysicalSaving` 2/0; `ChildRows` 1/1; `FiniteProfileExceptionalFixedQCanonical` 1/1; `FiniteProfileExceptionalFixedQPair` 1/1; `FiniteProfileExceptionalFixedQSaved` 1/1; `FiniteProfileExceptionalFixedQUniform` 1/1; `FiniteProfileExceptionalFixedQWindow` 1/1; `FiniteProfileExceptionalPhysicalBlock` 1/1; `FiniteProfileExceptionalPhysicalSaving` 1/1; `FirstAmplificationChoice` 1/1; `FirstAmplifiedCapacitySource` 1/1; `FirstMixedNormalization` 1/1; `FirstSeededGaussianPower` 1/1; `SecondExceptionalFixedQChosenBlock` 1/1; `SecondExceptionalFixedQSource` 1/1; `SecondExceptionalUniformSource` 1/1; `SecondFrozenLiveDescent` 1/1; `SecondFrozenLiveSource` 1/1; `SecondFrozenRatioCost` 1/1; `SecondFrozenReferenceSeededPowerDescent` 1/1; `SecondFrozenSeededPowerDescent` 1/1; `SecondFrozenUniformSubset` 1/1; `SecondLedger` 1/1; `SecondSourcePowerDescent` 1/1; `SecondSourceRemainder` 1/1; `AddedZero` 1/0; `AllocatedCenteredCapped` 1/0; `CommonExceptionalCanonical` 1/0; `CommonExceptionalCanonicalWindow` 1/0; `ExceptionalAsymmetricCanonical` 1/0; `ExceptionalCanonicalShell` 1/0; `ExceptionalCappedAmplitude` 1/0; `FiniteProfileExceptionalCommonCanonical` 1/0; `FiniteProfileExceptionalCommonWindow` 1/0; `FiniteProfileExceptionalPhysicalPair` 1/0; `FiniteProfileExceptionalPhysicalSaved` 1/0; `FiniteProfileExceptionalPhysicalUniform` 1/0; `Forcing` 1/0; `NaturalFixedRaySourceInternal` 1/0; `SecondExceptionalCanonicalPair` 1/0; `SecondExceptionalCount` 1/0; `SecondExceptionalEnergy` 1/0; `SecondExceptionalOriginalBlock` 1/0; `SecondFrozenPowerDescent` 1/0; `SecondLiveSourceDescent` 1/0; `SecondRetainedRatioCost` 1/0; `SecondUniformSubsetSource` 1/0; `SuccessorPaidParameters` 1/0

**Mellin** (3 modules): `ReflectedKernel` 2/2; `InverseContour` 1/1; `CompactWeights` 1/0

**PrimeCounting** (1 modules): `AnnularPrimeMass` 7/5

**QuadraticSieve** (2 modules): `InitialBound` 1/1; `MainTermDifference` 1/1

**Reflection** (19 modules): `LowBranchSum` 1/1; `LowCaps` 1/1; `LowChoiceEnergy` 1/1; `LowCompletedFiber` 1/1; `LowCompletedRows` 1/1; `LowDyads` 1/1; `LowExponent` 1/1; `LowFixedMember` 1/1; `LowFrozenEnergy` 1/1; `LowFull` 1/1; `LowFullBudget` 1/1; `LowGlobalBudget` 1/1; `LowInactiveEnergy` 1/1; `LowMemberBudget` 1/1; `LowMemberGeometry` 1/1; `LowOriginalEnergy` 1/1; `LowRetained` 1/1; `LowRetainedBudget` 1/1; `LowSector` 1/1

</details>

## 6. One step of generalization, done: hunt 134's formulas against OpenAI's

To price generalization with a measurement rather than a guess, the first session wrote
hunt 134's general-geometry formulas (`hunts/seven_eighths_pin/probe.py` on its
unlanded branch, commit `9456b4da`: `target`, `high_exponent`, `c0`, `d_x`, `p_x`,
`r_star`, `endpoint_neg_e`) as Lean definitions over any field of characteristic zero,
in two scratch files outside both trees, and proved them equal to OpenAI's definitions
at the paper's point. Compiled against OpenAI's built modules, every theorem below
reports exactly `[propext, Classical.choice, Quot.sound]` *(kernel-checked, both
sessions; source in full below)*. They are identities about formulas; none is a
statement about zeros.

| theorem | statement |
| --- | --- |
| `target_closed` | the matched target is 5/6 + (M - 2l)/12, for every (l, M, b) |
| `c0_closed` | C_0 = 1/2 + l/2 - 3M/4 + b/6 |
| `endpoint_contour_free` | at d = h the endpoint exponent does not depend on the contour, for every geometry, slope and capacity |
| `endpoint_closed` | E_* = C_0 - δ(l + b)/2 + lxδ + (h/2)(α - δ)δP/((α - δ)D + δP) |
| `target_paper` | the target at (1/6, 5/6, 1/8) is 7/8 |
| `endpoint_bridge` | the general E_* at (1/6, 5/6, 1/8), slope 5/6, capacity 4/9, contour 17/50 and x = 1/2 - y is `Endpoint.balancedExponent δ y`, wherever `Endpoint.balanceDenominator δ y ≠ 0` |
| `relative_bridge`, `source_bridge` | the general E(d) at the same point is `ProbeCentralExponent.relativeExponent`, and `sourceExponent` is 3/16 plus it |
| `compensated_geometry_from_general` | OpenAI's `compensated_geometry` follows from a version for free (l, M, b) in which each bound is attained at d = l; an `example` elaborates OpenAI's own theorem against the same statement |
| `gram_margin_iff` | the fourth conjunct at d = l is positive exactly when b < 3(M - 2l)/8 |

**Faults planted in the bridges** *(measured, both sessions)*. With the slope in
`endpoint_bridge` changed from 5/6 to 4/5, Lean stops with `error: unsolved goals` at
line 59, the report for `endpoint_bridge` gains `sorryAx`, and the gate rejects it.
With b changed from 1/8 to 1/9 in `relative_bridge`, Lean stops at line 21 with the
two sides differing in their constant and δ coefficients, and the gate rejects it. With
the contour changed from 17/50 to 33/100, `endpoint_bridge` still elaborates and the
gate accepts it, as `endpoint_contour_free` predicts: the check reacts to the inputs
that matter and not to the one the general theorem says cannot matter.

**The Lean values against hunt 134's Python** *(measured)*. `BridgeEndpoint.lean` ends
with four `#eval`s in `ℚ`. They print -7/30672 and -6641/29101824 for E_* at the
paper's geometry with δ = 79/204 and δ = 223/576 (x = 1/2), 29/820 at
(l, M, b) = (1/5, 4/5, 0) with δ = 1/3 and x = 1/4, and 13/15 for the target at
(1/5, 4/5, 0). Hunt 134's `probe.py` (SHA-256 `20c4bff7...f2cc8` at that commit),
evaluated with Python's `Fraction`s, gives the same four values exactly; moving one Lean
value by 10⁻⁹ makes the comparison report one disagreement.

**What it cost** *(measured)*. The two files hold 150 and 35 lines. Each elaborates in
under a minute on the loaded box (bridge-endpoint 32.9 s, bridge-central 27.2 s in the
second session), at 2.5 and 4.2 GiB peak RSS; the specializations close by `ring`,
`field_simp; ring`, `linarith` and `norm_num`.

<details>
<summary>scratch/BridgeEndpoint.lean (SHA-256 156d5ad06abec945724da27d3a4fa17c2c6417fbad70e8db731f35c4094e5272)</summary>

```lean
import OAI.NumberTheory.DirichletL.Endpoint
import OAI.NumberTheory.DirichletL.Parameters

/-! Hunt 136, Lean lane, scratch (outside OpenAI's tree and the laboratory's).

Hunt 134's general-geometry formulas, transcribed from
`hunts/seven_eighths_pin/probe.py` on its unlanded branch, written over any
field so they can be evaluated in `ℚ`, and their specialization at the paper's
geometry (ℓ, M, b) = (1/6, 5/6, 1/8), slope α = 5/6, capacity coefficient
c = 4/9 and contour 17/50 to OpenAI's formal definitions. Identities about
formulas only: nothing here is a statement about zeros. -/

namespace Lab136Bridge

section General
variable {K : Type*} [Field K] [CharZero K]

/-- `probe.high_exponent`: E(d), with ℓ, M, b, the target σ₀ and the contour free. -/
def highExponent (ℓ M b σ₀ zc d δ q R : K) : K :=
  ((1 + δ) / 2) - σ₀ + (1 - (M - b) / 2 + ℓ) * (zc - 1 / 6) - ((1 + δ) / 2) * ((M + b) / 2)
    - (1 - (1 + δ) / 2) * ℓ - (δ / 2 - q) * ℓ + d * (R + δ / 2 - zc)

/-- `probe.target`: the low exponent l_x/2 + b/12 plus the Mellin shift 1 - l_x/2 - h/6. -/
def target (ℓ M b : K) : K :=
  (M - b) / 2 / 2 + b / 12 + (1 - (M - b) / 2 / 2 - (1 - (M - b) / 2 + ℓ) / 6)

/-- `probe.d_x` and `probe.p_x` with capacity coefficient c. -/
def dx (c x : K) : K := 3 - (1 + 2 * c) * x
def px (c x : K) : K := (2 - 2 * c * x) * (1 - x)

/-- `probe.r_star` with amplification slope α. -/
def rStar (α c δ x : K) : K :=
  1 - δ + (α - δ) * δ * px c x / (2 * ((α - δ) * dx c x + δ * px c x))

/-- Minus `probe.endpoint_neg_e`: E(h) at q = xδ, R = R_*, matched target. -/
def endpointExponent (ℓ M b α c zc δ x : K) : K :=
  highExponent ℓ M b (target ℓ M b) zc (1 - (M - b) / 2 + ℓ) δ (x * δ) (rStar α c δ x)

theorem target_closed (ℓ M b : K) : target ℓ M b = 5 / 6 + (M - 2 * ℓ) / 12 := by
  unfold target; ring

/-- `probe.c0_closed`: C_0 = E(h) at δ = q = 0, R = 1, matched target. -/
theorem c0_closed (ℓ M b zc : K) :
    highExponent ℓ M b (target ℓ M b) zc (1 - (M - b) / 2 + ℓ) 0 0 1 =
      1 / 2 + ℓ / 2 - 3 * M / 4 + b / 6 := by
  unfold highExponent target; ring

/-- The contour cancels at d = h, for every geometry, slope and capacity. -/
theorem endpoint_contour_free (ℓ M b α c zc zc' δ x : K) :
    endpointExponent ℓ M b α c zc δ x = endpointExponent ℓ M b α c zc' δ x := by
  unfold endpointExponent highExponent; ring

/-- `probe.endpoint_neg_e_closed`, negated: E_* = C_0 - δ(ℓ + b)/2 + ℓxδ + (h/2)K. -/
theorem endpoint_closed (ℓ M b α c zc δ x : K)
    (hJ : (α - δ) * dx c x + δ * px c x ≠ 0) :
    endpointExponent ℓ M b α c zc δ x =
      (1 / 2 + ℓ / 2 - 3 * M / 4 + b / 6) - δ * (ℓ + b) / 2 + ℓ * x * δ +
        (1 - (M - b) / 2 + ℓ) / 2 *
          ((α - δ) * δ * px c x / ((α - δ) * dx c x + δ * px c x)) := by
  unfold endpointExponent highExponent target rStar
  field_simp
  ring

end General

open OAI.SevenEighths

theorem target_paper : target (1 / 6 : ℝ) (5 / 6) (1 / 8) = 7 / 8 := by
  rw [target_closed]; norm_num

theorem balanceDenominator_bridge (δ y : ℝ) :
    (5 / 6 - δ) * dx (4 / 9 : ℝ) (1 / 2 - y) + δ * px (4 / 9) (1 / 2 - y) =
      Endpoint.balanceDenominator δ y := by
  unfold dx px Endpoint.balanceDenominator Endpoint.denominator Endpoint.primeWeight
  ring

/-- Hunt 134's general endpoint exponent, at the paper's geometry, row counts and
contour, is OpenAI's `Endpoint.balancedExponent` (with x = 1/2 - y). -/
theorem endpoint_bridge (δ y : ℝ) (hJ : Endpoint.balanceDenominator δ y ≠ 0) :
    endpointExponent (1 / 6 : ℝ) (5 / 6) (1 / 8) (5 / 6) (4 / 9) (17 / 50) δ (1 / 2 - y) =
      Endpoint.balancedExponent δ y := by
  have hJ' := hJ
  rw [← balanceDenominator_bridge] at hJ'
  unfold endpointExponent rStar
  rw [target_paper]
  have hbal : Endpoint.balancedExponent δ y =
      -(1 / 48) + (2 / 3) * δ + δ * (1 / 2 - y) / 6 -
        (13 / 16) * (1 - (1 - 5 / 6 + (5 / 6 - δ) *
          (1 + δ * px (4 / 9 : ℝ) (1 / 2 - y) /
            (2 * ((5 / 6 - δ) * dx (4 / 9) (1 / 2 - y) + δ * px (4 / 9) (1 / 2 - y)))))) := by
    unfold Endpoint.balancedExponent Endpoint.balancedRowCount Endpoint.balancedCutoff
    rw [← balanceDenominator_bridge]
    unfold dx px Endpoint.primeWeight
    ring_nf
  rw [hbal]
  unfold highExponent
  field_simp
  ring

/-- The five facts of OpenAI's `Parameters.compensated_geometry`, for free (ℓ, M, b):
each lower bound is the value at d = ℓ. -/
theorem compensated_geometry_general {ℓ M b d : ℝ} (_hd0 : 0 ≤ d) (hd1 : d ≤ ℓ) :
    M - 2 * ℓ ≤ M - 2 * d ∧ (M - b) / 2 - ℓ ≤ (M - b) / 2 - d ∧
      (M + b) / 2 - ℓ ≤ (M + b) / 2 - d ∧
      (M + b) / 2 - ℓ - 11 * b / 6 ≤ (M + b) / 2 - d - 11 * b / 6 ∧
      (M - b) / 2 / 2 + b / 12 = M / 4 - b / 6 :=
  ⟨by linarith, by linarith, by linarith, by linarith, by ring⟩

/-- OpenAI's statement, recovered from the general one at (1/6, 5/6, 1/8). -/
theorem compensated_geometry_from_general {d : ℝ} (hd0 : 0 ≤ d) (hd1 : d ≤ 1 / 6) :
    (1 / 2 : ℝ) ≤ 5 / 6 - 2 * d ∧
    3 / 16 ≤ 17 / 48 - d ∧
    5 / 16 ≤ 23 / 48 - d ∧
    1 / 12 ≤ 23 / 48 - d - 11 * (1 / 8) / 6 ∧
    (17 / 48 : ℝ) / 2 + (1 / 8) / 12 = 3 / 16 := by
  obtain ⟨h1, h2, h3, h4, -⟩ :=
    compensated_geometry_general (ℓ := 1 / 6) (M := 5 / 6) (b := 1 / 8) hd0 hd1
  refine ⟨by linarith, by linarith, by linarith, by linarith, by norm_num⟩

/-- The same statement is OpenAI's theorem (checked by elaboration against it). -/
example {d : ℝ} (hd0 : 0 ≤ d) (hd1 : d ≤ 1 / 6) :
    (1 / 2 : ℝ) ≤ 5 / 6 - 2 * d ∧
    3 / 16 ≤ 17 / 48 - d ∧
    5 / 16 ≤ 23 / 48 - d ∧
    1 / 12 ≤ 23 / 48 - d - 11 * (1 / 8) / 6 ∧
    (17 / 48 : ℝ) / 2 + (1 / 8) / 12 = 3 / 16 :=
  Parameters.compensated_geometry hd0 hd1

/-- The fourth conjunct at d = ℓ is positive exactly under the Gram condition
b < 3(M - 2ℓ)/8 that hunt 134 records. -/
theorem gram_margin_iff (ℓ M b : ℝ) :
    0 < (M + b) / 2 - ℓ - 11 * b / 6 ↔ b < 3 * (M - 2 * ℓ) / 8 := by
  constructor <;> intro h <;> linarith

end Lab136Bridge

#print axioms Lab136Bridge.target_closed
#print axioms Lab136Bridge.c0_closed
#print axioms Lab136Bridge.endpoint_contour_free
#print axioms Lab136Bridge.endpoint_closed
#print axioms Lab136Bridge.target_paper
#print axioms Lab136Bridge.endpoint_bridge
#print axioms Lab136Bridge.compensated_geometry_from_general
#print axioms Lab136Bridge.gram_margin_iff

-- Evaluation in ℚ, to compare with probe.py's Fractions at the same points.
#eval Lab136Bridge.endpointExponent (1/6 : ℚ) (5/6) (1/8) (5/6) (4/9) (17/50) (79/204) (1/2)
#eval Lab136Bridge.endpointExponent (1/6 : ℚ) (5/6) (1/8) (5/6) (4/9) (17/50) (223/576) (1/2)
#eval Lab136Bridge.endpointExponent (1/5 : ℚ) (4/5) (0) (5/6) (4/9) (17/50) (1/3) (1/4)
#eval Lab136Bridge.target (1/5 : ℚ) (4/5) 0
```
</details>

<details>
<summary>scratch/BridgeCentral.lean (SHA-256 da127da798b17df4ce3a48c3603d08202f7dfbb830f48e5d9681dafc772e9c8b)</summary>

```lean
import OAI.NumberTheory.DirichletL.Detector.CentralExponent

/-! Hunt 136, Lean lane, scratch (outside OpenAI's tree and the laboratory's).
Hunt 134's general high exponent `probe.high_exponent`, specialized at the
paper's geometry, target and contour, against OpenAI's two formal forms in
`Detector/CentralExponent.lean`. Identities about formulas only. -/

namespace Lab136Bridge

/-- `probe.high_exponent`, as in `BridgeEndpoint.lean`, over ℝ. -/
noncomputable def highExponentR (ℓ M b σ₀ zc d δ q R : ℝ) : ℝ :=
  ((1 + δ) / 2) - σ₀ + (1 - (M - b) / 2 + ℓ) * (zc - 1 / 6) - ((1 + δ) / 2) * ((M + b) / 2)
    - (1 - (1 + δ) / 2) * ℓ - (δ / 2 - q) * ℓ + d * (R + δ / 2 - zc)

open OAI.SevenEighths

/-- The paper's second form of E(d) (OpenAI's `relativeExponent`) is hunt 134's
general E(d) at (ℓ, M, b) = (1/6, 5/6, 1/8), σ₀ = 7/8 and contour 17/50. -/
theorem relative_bridge (δ d R q : ℝ) :
    highExponentR (1 / 6) (5 / 6) (1 / 8) (7 / 8) (17 / 50) d δ q R =
      ProbeCentralExponent.relativeExponent δ d R q := by
  unfold highExponentR ProbeCentralExponent.relativeExponent
  ring

/-- OpenAI's `sourceExponent` is 3/16 plus the same specialization, with a = (1 + δ)/2. -/
theorem source_bridge (a d R q : ℝ) :
    ProbeCentralExponent.sourceExponent a d R q =
      3 / 16 + highExponentR (1 / 6) (5 / 6) (1 / 8) (7 / 8) (17 / 50) d (2 * a - 1) q R := by
  unfold highExponentR ProbeCentralExponent.sourceExponent
  ring

end Lab136Bridge

#print axioms Lab136Bridge.relative_bridge
#print axioms Lab136Bridge.source_bridge
```
</details>

## 7. What generalizing to symbolic parameters would take

The surface numbers below are *measured* (sections 3 and 5); the effort ranges are
*inferred*, because beyond the formula bridges of section 6 the lane generalized no
census declaration.

**Three tiers of work.**

1. **Formulas.** The exponent and row-count definitions: seven in `Endpoint.lean`,
   seven in `Hecke/DetectorRowCountCrossing.lean`, two in
   `Hecke/InverseAmplificationBudget.lean`, two in `Detector/CentralExponent.lean`,
   and the few other definitions of the derived class (section 5.5). Section 6 shows
   the general forms exist, specialize by `ring`, and elaborate in seconds. Small.
2. **Statements.** The 329 cone declarations of the union class, in 120 modules and
   15,510 source lines, whose statements carry the constants; for example the exponent
   literals inside `Real.rpow` in `Detector/LowSourceScales.lean`, and the structures
   `Parameters.HighData`, `HeckeDetectorRawFiber.Fiber` and `HeckeDetectorBatch.Batch`,
   which hold the geometry and the row counts in their fields and carry 116, 159 and 83
   downstream declarations. 266 more cone declarations, in 190 modules, carry only a raw
   1/6, 5/6 or 1/8 and must be read one by one, since those values have other meanings. The
   proofs the lane read close their numeric side conditions with `norm_num`,
   `linarith`, `nlinarith` and `positivity` at fixed numerals (inferred from
   `Endpoint.lean`, the `Parameters*.lean` files, `Detector/CentralExponent.lean` and
   `Detector/LowSourceScales.lean`; not counted across the census). With symbolic
   parameters each such step needs the constraint hypotheses as inputs, and some become
   nonlinear in the parameters.
3. **The endpoint identity.** `Endpoint.endpoint_identity` is the paper's exact identity
   `10368v\mathcal J(-E_*)` = (3 + 5y){(4vδ - 79)² + 49} + 4y{...} (lines 16042 to
   16047, cited), whose integer coefficients are fixed by the geometry, the slope 5/6
   and the capacity 4/9; `balanced_endpoint_margin` derives the 49/440640 margin from
   it, and 20 cone declarations, including both theorems, depend on it. A symbolic
   version needs a positivity proof for the general E_* of `endpoint_closed` that
   holds as the parameters vary. The lane has none, and finding one is a mathematical
   question before it is a formalization one.

**Two routes.**

- **Re-instantiate at one new rational point.** This is what a candidate from this hunt
  would need. Change the constants at the census sites, compute a new exact identity
  for the endpoint at the new numbers (exact rational arithmetic of the kind this hunt's
  other lanes use), and rebuild. The rebuild covers every closure module
  that imports a module with a union declaration in the cone: 1,539 of 2,924 modules,
  8.17 hours of this build's module time, with a critical path of 47.6 minutes; after
  an edit to `Endpoint.lean` alone it is 259 modules, 1.54 hours and 22.7 minutes;
  after an edit to `Hecke/DetectorRowCountCrossing.lean`, 585 modules, 3.16 hours and
  30.5 minutes *(measured from this build's log; wall times on another box would
  differ)*. A step whose numeric side condition fails at the new point stops the build
  at a named declaration, so the formal development doubles as a locator for where a
  candidate breaks the argument *(inferred)*. Effort: the editing surface is the 120
  modules above; if the numeric facts survive at the new point, days of agent editing
  plus one or two rebuilds of about an hour each on this box; if a fact fails, the
  lemma behind it has to be redone on paper first *(inferred)*.
- **Symbolic parameters.** Thread a structure of parameters (l, M, b, the slope, the
  capacity and the contour, with M + l ≤ 1 and the length inequalities of paper lines
  8593 to 8597 as hypotheses) through the statement tier, replace the `Real.rpow`
  exponents by expressions in it, re-prove each numeric step under hypotheses, and
  supply the parametric positivity proof. Weeks of formalization, with that proof as
  the main risk *(inferred)*. A measurable first step: generalize `Endpoint.lean`
  alone (113 lines, importing only Mathlib) in the slope and the capacity with the
  geometry fixed, since that is the file the row-count lanes would change.

**What a generalization would not settle** *(inferred)*. It makes a candidate's
assembly checkable at the level of formulas. It does not show that the analytic lemmas
the paper proves at its own numbers hold at another geometry: those lemmas sit in the
same 2,924-module closure, and a constant they hide in a form the census cannot see
would surface only when the rebuild fails.

## 8. Open issues

- The comparator run through NanoDa, the second kernel, was not repeated (section 4).
- The census reads statements and definition bodies only, and quotients of numerals
  only (section 5.4).
- The raw-only class is listed by module, not by declaration, on this page (section 5.5).
- Every effort figure in section 7 is an estimate; the only generalization measured is
  the formula tier.
- The evidence lives in the cache, `<cache>/qrh-build/`
  (`evidence/20261021T143950Z/` and `evidence/20261021T2130Z-session2/`, the dumps in
  `analysis/` and `analysis-session2/`, the scripts and Lean files in `scratch/`),
  outside the tree and not durable. This page is the durable record; the bridge files
  are reproduced in section 6 so that it does not depend on the cache.
- **2026-10-26: the cache is gone.** When the lane was resumed in place on 2026-10-26,
  `<cache>/qrh-build/` no longer existed on the campaign box (measured, `ls`), so none of
  the evidence directories, dumps or scratch scripts named above can be re-read, and the
  logs behind every *(measured)* number on this page are lost. The numbers stay as
  recorded; nothing on this page was rebuilt or re-checked, and the resumed lane ran no
  Lean build (the box is shared and its disk is near its floor). A replay needs a fresh
  pinned checkout and build on a machine sized for it (`CLAUDE.md` compute rule 1).
- `scratch/closure.py` in the cache reads hunt 137's vendored tree and was not used by
  this lane.
- `OAI.NumberTheory.DirichletL.Hecke.Nonvanishing` was not built or checked; 12 of
  `balancedExponent`'s downstream declarations, among them `hecke_of_chosen_moments`,
  lie outside the cone of the two theorems this lane checked.

## 9. Reproduction

From the cache, on the campaign box, with `ELAN_HOME` and `XDG_CACHE_HOME` inside it
and `LEAN_NUM_THREADS=16`:

```sh
cd <cache>/qrh-build
PY=.venv/bin/python
L=openai-math-adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean
scratch/setup.sh                      # pins, toolchain, lake update, lake exe cache get
scratch/build.sh                      # lake build OAI.NumberTheory.DirichletL.Nonvanishing
scratch/session2.sh $PWD/evidence/NEW # absolute path: no-op rebuild, axioms, gate, faults, bridges, dump
$PY -I scratch/closure_s2.py $L OAI.NumberTheory.DirichletL.Nonvanishing closure.txt
$PY -I scratch/postprocess.py analysis-session2 $L \
  OAI.SevenEighths.Parameters.compensated_geometry OAI.SevenEighths.Endpoint.balancedExponent
$PY -I scratch/census_downstream.py analysis-session2
$PY -I scratch/textcensus.py $L closure.txt analysis-session2/census.tsv
$PY -I scratch/s2_tables.py analysis-session2 $L closure.txt \
  evidence/20261021T143950Z/upstream-build.log analysis-session2/tables
```

```runmanifest
id: below_seven_eighths-2026-10-21-lean-session1
hunt: below_seven_eighths
started: 2026-10-21T14:39Z
finished: 2026-10-21T18:06Z
ran:
  - scratch/setup.sh (clone of openai/math at adc7f124, elan toolchain v4.34.1, lake update, lake exe cache get), under the memory watchdog
  - scratch/build.sh (lake build OAI.NumberTheory.DirichletL.Nonvanishing, LEAN_NUM_THREADS=16)
  - scratch/post.sh (axioms, gate with three planted faults and a control, environment dump)
  - lean on scratch/BridgeEndpoint.lean, BridgeCentral.lean and their planted-fault copies
outcome: recorded by the second session from this run's evidence directory; the closure built with exit 0 in 11393 s, both 7/8 statements report only the three standard axioms, and the run was stopped by the campaign pause before it wrote its page
artifacts:
  - <cache>/qrh-build/evidence/20261021T143950Z/
  - <cache>/qrh-build/analysis/
  - hunts/below_seven_eighths/LEAN.md (sections 1 and 2)
```

```runmanifest
id: below_seven_eighths-2026-10-21-lean-session2
hunt: below_seven_eighths
started: 2026-10-21T21:22Z
finished: 2026-10-21T22:05Z
ran:
  - scratch/session2.sh evidence/20261021T2130Z-session2 (no-op lake build, axioms, gate, planted faults, bridges, environment dump), under the memory watchdog
  - scratch/closure_s2.py, levels.py, depth.py and rebuild.py on the import graph and the first session's build log
  - scratch/postprocess.py, census_downstream.py, targets_table.py and s2_tables.py on the session-two dump
  - scratch/textcensus.py on the census and on a census with one planted fake row
  - evalcheck.py comparing the four Lean evaluations with hunt 134's probe.py
  - grep over OpenAI's checkout for compensated_geometry, the other Parameters theorems and balancedExponent
outcome: every check of the first session reproduced with fresh logs, the dependency census located the geometry and row-count literals with their downstream reach, and the page was completed
artifacts:
  - hunts/below_seven_eighths/LEAN.md
  - <cache>/qrh-build/evidence/20261021T2130Z-session2/
  - <cache>/qrh-build/analysis-session2/
  - <cache>/qrh-build/analysis-session2-text/closure.txt
```
