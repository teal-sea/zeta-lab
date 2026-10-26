# PILOT: one prime tower, composite atoms and one big-box site at Lean v4.35.0-rc2

Hunt #145, lane `rung3-pilot`, 2026-10-21. **Grade: measured** (one box, one session, one
route per number) for every cost below. The kernel outcomes are observations of what Lean
accepted and refused on this box. The only kernel-checked objects are the pilot site's two
theorems, whose axioms are printed in section 2; they say that `‖DH s‖ ≤ 25499/10000` on
one box of the big square's boundary, and nothing more. No production shard was launched,
and `davenport_heilbronn` is still unproved: no file emits the assembly module (section
6).

Every table between `<!-- table:... -->` markers is rendered by `report.py` from
`pilot.json` (`render_docs.py` writes them in), and `test_rung3_ball_production.py` fails
if a table here differs from what `pilot.json` renders. Numbers in the prose restate those
tables or are pinned by that test.

## 1. Environment and what ran

<!-- table:setup -->
| item | value |
|---|---|
| box | `<box>`: 32 vCPU (Intel Core Processor (Haswell, no TSX)), 115.1 GiB, no swap, shared |
| Lean | `leanprover/lean4:v4.35.0-rc2`; Lean (version 4.35.0-rc2, x86_64-unknown-linux-gnu, commit 11acb17ec6b07a8f9e9173e6845197929540936b, Release) |
| Mathlib | `065356127b1d` (`lean/lake-manifest.json`) |
| Lake packages | 9; every package's git toplevel is the package itself: yes; every HEAD equals its manifest revision: yes |
| `ZetaLean` modules built | 15: `Ball`, `BallCertSupport`, `BallTerm`, `DHAnalytic`, `DHAssembly`, `DHCertSupport`, `DHTailBound`, `DHTailBound2`, `DHZeroCriterion`, `DavenportHeilbronn`, `DirichletEval`, `IntervalCExp`, `IntervalExp`, `OracleDH`, `Rigor` |
<!-- /table:setup -->

Lake ran only in this worktree's `lean/.lake`, which `lake exe cache get` filled from
scratch in the first attempt; no `.lake` was copied (compute rule 7), and each package's
git toplevel and HEAD were checked again when `pilot.json` was written. The 15 `ZetaLean`
modules are `Ball`, `BallTerm`, `BallCertSupport`, `DHCertSupport`, `DHAssembly` and
`DHTailBound2` with their imports, built from this branch's sources. `scripts/72` is
`main`'s version (`MISSION.md`, "Starting point"); `tests/test_rung3_ball_compile.py`
passes against it (22 tests). Every Lean process ran through `pilot.py`, which waits
before each run while the 1-minute load average is above a threshold (64 before the site
compile and the fault recompiles, 96 before single small files) or `MemAvailable` is below
30 GiB, and records argv, working directory, `LEAN_PATH`, wall time, user and system CPU
and peak RSS from `wait4`, and the load before and after.

The pilot site was generated and compiled with these two command lines, which `pilot.py
site` ran and `pilot.json` records verbatim. The work directory is outside the tree, and
any empty directory replays it. The generator is deterministic: the first attempt's ten
sources and this run's are byte-identical (`generator_replay` in `pilot.json` compares
their SHA-256), and `pilot.json` keeps each source's hash:

<!-- table:commands -->
```bash
# from the worktree root; Lean from elan
export PATH="$HOME/.elan/bin:$PATH"
cd .
.venv/bin/python scripts/60_rung3_generate.py lean/cert/rung3_plan2.json <cache>/rung3-ball-production-pilot-2/site/B_right_06/gen --arith ball --shard --only B_right_06
cd .
.venv/bin/python scripts/72_rung3_ball_compile.py --lean-project lean --output-root <cache>/rung3-ball-production-pilot-2/site/B_right_06/out --jobs 1 --module-jobs 1 <cache>/rung3-ball-production-pilot-2/site/B_right_06/gen/CB_right_06.manifest.json
```
<!-- /table:commands -->

## 2. Kernel outcomes

`B_right_06` is one of the three big boxes with the smallest K in plan v2 (K = 17, with
`B_bottom_23` and `B_top_22`; big boxes run to K = 61, grid points from 85 to 114, the
centre is 361), the same K as the unsharded whole-file record in `scripts/67`. It has 23
prime towers (p = 2 to 89), 48 composites, 68 nonzero terms and N = 85 series terms, 774
atoms by `scripts/67`'s count. `scripts/60` split it into 10 modules: `Base`, five prime
shards, the `Primes` barrel, `Composites`, `Terms` and the root `CB_right_06`, which
states

```lean
theorem upper_B_right_06 {s : ℂ} (hS : SI_B_right_06.contains s) :
    ‖DH s‖ ≤ (((25499/10000 : ℚ)) : ℝ)
```

`scripts/72` compiled the ten in manifest order at one process, each with exit 0, and
recorded the site `ok` (section 3 has the per-module record). `pilot.py axioms` then
printed the axioms of `upper_B_right_06` and of `enc_B_right_06` (the enclosure theorem it
rests on) from the compiled oleans: `propext`, `Classical.choice` and `Quot.sound`, and no
`sorryAx`. That is the kernel-checked content of the pilot, one box of the big square's
boundary bounded by `M`.

### Planted faults in the site

<!-- table:faults -->
| fault | change planted | expected refusal | errors at | driver exit | module refused | modules recompiled |
|---|---|---|---|---|---|---|
| tower-rad | `Prime_89.Sq_10` radius lowered by one unit of its denominator (`13609794713164397/18446744073709551616` to `3402448678291099/4611686018427387904`) | `Prime_89.ev_mul_29` | `Prime_89.ev_mul_29`, `hp_B_right_06_89` | 1 | `CB_right_06/Primes04.lean` | 1 |
| tail-rad | tail radius `r` set 9.6e-13 below the tail bound, all 3 occurrences | `enc_B_right_06` | `enc_B_right_06` | 1 | `CB_right_06.lean` | 1 |
| M | `M` set 9.1e-13 below `u + rad` of the inflated ball | `upper_B_right_06` | `upper_B_right_06` | 1 | `CB_right_06.lean` | 1 |
<!-- /table:faults -->

Each fault was planted by `pilot.py fault` in a copy of the generated sources, and the
copy was recompiled by the same driver against a copy of the clean output root, so
`scripts/72` skipped every module whose source hash was unchanged and recompiled only the
touched one. Two of the three are emitted radii: the last squaring of the largest prime's
tower (`Prime_89.Sq_10`, radius lowered by one unit of its denominator 2^64) and the tail
radius `r` of `enc_B_right_06` (set just below the tail bound that its hypothesis `hr`
must clear, in all three places it occurs). The third lowers `M` in `upper_B_right_06` to
just below the bound the enclosure delivers. In each case Lean refused the module at the
declaration named in the table: the `norm_num` step that proves the perturbed equality or
inequality fails, so no proof term for it reaches the kernel, the module writes no olean,
and the driver marks the site failed and schedules none of its dependents. The radius
fault was caught twice inside its module: at `ev_mul_29`, whose product no longer equals
the literal, and at `hp_B_right_06_89`, where the site's own copy of that ball
(`Pow_B_right_06_89`, the ball the rest of the site reads for 89^(-s)) no longer matches
the perturbed `Sq_10`.

### eps': the centre theorem's last step, with the enclosure as a hypothesis

<!-- table:centre -->
| probe | eps' stated | u + rad of the centre ball | lean exit |
|---|---|---|---|
| control | 5.000000e-04 | 3.855242e-04 | 0 |
| eps-above-bound | 3.855242e-04 | 3.855242e-04 | 0 |
| eps-at-bound | 3.855242e-04 | 3.855242e-04 | 1 |
| eps-half | 2.500000e-04 | 3.855242e-04 | 1 |
<!-- /table:centre -->

eps' (`1/2000` in plan v2) appears in one emitted theorem, `centre_lt_centre : ‖DH
z_centre‖ < ((1/2000 : ℚ) : ℝ)`. Its site has K = 361, 278 prime towers and 10,233 atoms
by `scripts/67`'s count; compiling it is production, so it was generated (Python only) and
not compiled. `pilot.py centre-eps` compiles that theorem's last step verbatim, from the
emitted `B_centre` and `z_centre` literals, with the enclosure `henc : (B_centre.inflate
r).contains (DH z_centre)` taken as a hypothesis instead of proved, at four values of
eps'. The step needs `u + rad < eps'`, where `u` bounds the centre's modulus and `rad` is
the inflated radius. Lean accepted the plan's value and the next multiple of 2^-64 above
`u + rad`, and refused `u + rad` itself (the claim is strict) and half the plan's value,
each refusal an error inside the probe's theorem. This shows that the eps' literal is
checked against the emitted enclosure, to the last unit; it does not show that the
centre's enclosure compiles. The other place eps' enters, the cell hypotheses `eps' +
L*h/2 <= beta`, lives in the assembly module (section 6).

### The mirror and the kernel on `B_right_06`

The kernel accepted every emitted equality of the site, ending with `evB_B_right_06`,
which says that the computed partial sum plus correction equals the literal
`B_B_right_06`. So the kernel's value of that ball is the emitted literal. `pilot.py
mirror` compares it with the bit-exact Fraction mirror as `scripts/65` runs it. The
centres agree exactly. The radii do not: `scripts/65`'s ball is wider by exactly
738083614955/2^64 (about 4.0e-8), which is the radius `scripts/63`'s `cpowBox` gives to
1^(-s), because `scripts/65` evaluates the m = 1 term through the generic power chain
while the generator seeds it as the exact ball (1, 0, 0) (`Pow_B_right_06_1` in the site's
`Base` module). A copy of `scripts/65`'s assembly with m = 1 seeded the same way
reproduces the emitted literal bit for bit, and the unseeded copy reproduces
`scripts/65`'s value. So on this site the mirror and the kernel agree once that seed is
accounted for, and `scripts/65`'s recorded normBound (the value in
`lean/cert/rung3_ball_validation.json`) is the larger, conservative one. The hunt test
pins each of these equalities.

## 3. Cost per atom and per module

<!-- table:cost -->
| quantity | v4.33.0-rc2 record | this pilot | ratio |
|---|---|---|---|
| CPU-s per prime-tower atom, `scripts/68` tower at p = 2, 171 KB of text (net of import) | 1.2504 | 2.0896 (1.7822 to 2.3673, 3 runs) | 1.67 |
| CPU-s per prime-tower atom, `scripts/68` tower at p = 2, with `lean -j1` | not measured | 2.2548 (2.1798 to 2.3951, 3 runs) | 1.80 |
| CPU-s per prime-tower atom, `scripts/68` tower at p = 2, with Lean's linters off (`-Dlinter.all=false`) | not measured | 2.2527 (2.1989 to 2.3045, 3 runs) | 1.80 |
| CPU-s per prime-tower atom, `scripts/68` tower at p = 1801, 532 KB of text | not measured | 2.2259 (2 runs) | 1.78 |
| CPU-s per prime-tower atom in the site's prime shards (p = 2 to 89, 23 towers) | not measured | 2.4219 | 1.94 |
| CPU-s per composite atom, `scripts/66`, 100 atoms (net of import) | 0.55 | 0.4865 (3 runs) | 0.88 |
| CPU-s per composite in the site's `Composites` module (48 composites) | not measured | 0.6741 | 1.23 |
| CPU-s per nonzero term in the site's `Terms` module (68 terms) | not measured | 0.513 | |
| root module net CPU-s (term function, partial sums, assembly; N = 85) | not measured | 16.0 | |
| import-only CPU-s per module, `Base` imports (median) | 4.576 | 10.079 | 2.20 |
| import-only CPU-s per module, root imports (whole site loaded) | not measured | 9.805 | |
| peak RSS added by importing the site's other oleans (root probe minus `Base` probe), per olean byte imported | not measured | 0.66 | |
| peak RSS per process, largest module (wait4) | not recorded | 7.83 GiB | |
| of which anonymous, largest module (sampled each second; the rest is file-backed olean mappings, shared between processes) | not recorded | 1.91 GiB | |
| cores busy per process, site compile at one process (CPU / wall) | not recorded | 1.38 | |
<!-- /table:cost -->

<!-- table:modules -->
| module | towers | composites | terms | source KB | olean MB | wall s | CPU s | import CPU s | net CPU s | peak RSS GiB | anon RSS GiB | load | warnings |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| `CB_right_06/Base.lean` |  |  |  | 1.4 | 0.1 | 18.0 | 11.1 | 10.1 | 1.0 | 6.33 | 0.40 | n/a | 2 |
| `CB_right_06/Primes00.lean` | 7 |  |  | 1,853.4 | 47.7 | 217.1 | 521.6 | 9.9 | 511.7 | 7.83 | 1.91 | 70 | 308 |
| `CB_right_06/Primes01.lean` | 5 |  |  | 1,685.8 | 35.6 | 261.9 | 375.6 | 10.3 | 365.3 | 7.44 | 1.47 | 91 | 220 |
| `CB_right_06/Primes02.lean` | 5 |  |  | 1,789.8 | 35.9 | 323.3 | 387.6 | 10.8 | 376.8 | 7.44 | 1.50 | 112 | 220 |
| `CB_right_06/Primes03.lean` | 5 |  |  | 1,961.1 | 36.5 | 258.3 | 358.2 | 10.2 | 348.1 | 7.43 | 1.48 | 95 | 220 |
| `CB_right_06/Primes04.lean` | 1 |  |  | 396.8 | 7.9 | 167.8 | 82.1 | 12.9 | 69.2 | 6.58 | 0.66 | 85 | 44 |
| `CB_right_06/Primes.lean` |  |  |  | 0.2 | 0.0 | 24.4 | 10.2 | 10.5 | -0.3 | 6.40 | 0.40 | 84 | 0 |
| `CB_right_06/Composites.lean` |  | 48 |  | 55.3 | 7.0 | 30.7 | 43.3 | 11.0 | 32.4 | 6.62 | 0.59 | 84 | 0 |
| `CB_right_06/Terms.lean` |  |  | 68 | 89.8 | 5.4 | 25.5 | 45.8 | 10.9 | 34.9 | 6.59 | 0.58 | 74 | 0 |
| `CB_right_06.lean` |  |  |  | 35.0 | 3.8 | 20.6 | 25.8 | 9.8 | 16.0 | 6.56 | 0.52 | 65 | 0 |
| **site total** | 23 | 48 | 68 | 7,868.6 | 179.8 | 1,347.5 | 1,861.4 | 106.3 | | | | | 1014 |
<!-- /table:modules -->

Every rate is CPU net of an import-only run with the same imports: `import
ZetaLean.BallTerm` for the `scripts/68` and `scripts/66` files, and for each site module a
probe file holding that module's own import lines (`pilot.py imports`, two runs each, the
median taken). The import itself is a large and noisy share on this box, so a file must
carry enough atoms to rise above it: ten composite atoms cost a few CPU-s against an
import of about ten, and the composite rate is taken from a file of 100 (`pilot.json`
keeps both). In the site, the five prime shards give the in-situ tower rate, and the
`Composites`, `Terms` and root modules give the composite, term and root rates; those
three modules import every prime shard's olean, and their probes say what that import
costs. The modules table also counts the Lean warnings in each module's log, almost all of
them Mathlib's `<;>` style linter.

### Threads per process

<!-- table:threads -->
| `CB_right_06/Primes02.lean` (5 towers) | default threads (`scripts/72`) | `lean -j1` |
|---|---|---|
| CPU-s | 387.6 | 369.3 |
| wall s | 323.3 | 463.7 |
| CPU-s net of the module's import probe | 376.8 | 358.5 |
| net CPU-s per tower atom | 2.512 | 2.390 |
| peak RSS GiB (anonymous) | 7.44 (1.50) | 7.28 (1.33) |
<!-- /table:threads -->

`scripts/72` runs `lean` with its default thread count. Across the two attempts the same
prime shards ran at very different parallelism (CPU over wall, from the replay table
below) while their CPU totals stayed within the spread shown there, so on this evidence
threads move wall time and not CPU. One shard was also recompiled with `lean -j1`
(`pilot.py shard`, into a scratch olean, the site's own oleans untouched), and the
`scripts/68` tower was run at `-j1` as well (the cost table's `-j1` row). At `-j1` the
shard's CPU net of import came out slightly below its default-thread figure (threads
table), and the tower's CPU per atom at `-j1` fell inside the spread of its default-thread
runs, while each single-threaded run's wall time was its CPU time stretched by the load.
So threads per process change how production shares cores, not what it costs: a driver
could run one thread per process and as many processes as it is given cores, at the
anonymous memory per process the `-j1` shard recorded (threads table, last row).

### Replaying the timings

<!-- table:replay -->
| module | same source | first attempt CPU s (wall s) | this run CPU s (wall s) | CPU ratio | wall ratio |
|---|---|---|---|---|---|
| `CB_right_06/Base.lean` | yes | 13.6 (19.1) | 11.1 (18.0) | 0.82 | 0.94 |
| `CB_right_06/Primes00.lean` | yes | 560.4 (166.3) | 521.6 (217.1) | 0.93 | 1.30 |
| `CB_right_06/Primes01.lean` | yes | 402.7 (135.1) | 375.6 (261.9) | 0.93 | 1.94 |
| `CB_right_06/Primes02.lean` | yes | 372.5 (117.4) | 387.6 (323.3) | 1.04 | 2.75 |
<!-- /table:replay -->

The four modules the interrupted first attempt compiled are byte-identical to this run's
(same SHA-256), so they are a replay at a different load: the table gives the CPU and wall
ratios. A second agent replaying the site with the two command lines of section 1 should
compare CPU (user plus system), not wall time, and should expect agreement of the kernel
outcome (every module exit 0) exactly and of CPU to roughly the spread shown here, given a
similar load. Wall time moved far more than CPU between the two attempts for the same
files (the last column).

## 4. Projection to the 215 sites

<!-- table:projection -->
| component | core-hours |
|---|---|
| prime towers (468,240 atoms) | 380.5 |
| composites | 9.1 |
| term products | 9.1 |
| root and partial sums | 4.2 |
| imports (4,696 modules) | 13.2 |
| **total, projected from this pilot** | **416.0** |
| atom-only, `scripts/67` formula at the `scripts/68` and `scripts/66` rates of this box | 282.7 |
| atom-only, `scripts/67` formula at the in-situ rates of this site | 330.2 |
| atom-only, `scripts/67` as recorded (v4.33.0-rc2 rates) | 175.0 |
| *oleans left on disk, GB (scaled per tower, or per byte of tower text)* | *123 to 146* |
<!-- /table:projection -->

<!-- table:wall -->
| concurrent processes | wall hours, one core per process | wall hours at 1.38 cores per process (capped at 32 vCPU) |
|---|---|---|
| 16 | 26.0 | 18.8 |
| 20 | 20.8 | 15.1 |
| 24 | 17.3 | 13.0 |
<!-- /table:wall -->

<!-- table:sensitivity -->
| tower cost model | tower core-hours | total core-hours | wall hours at 16 | wall hours at 24 |
|---|---|---|---|---|
| in-situ shard CPU per source byte (the request uses this one) | 380.5 | 416.0 | 18.8 | 13.0 |
| in-situ shard CPU per tower, flat in the prime | 315.0 | 350.5 | 15.9 | 10.9 |
| least-squares fit, per tower plus per byte, over `scripts/68` towers and the shards | 311.6 | 347.1 | 15.7 | 10.8 |
| `lean -j1` shard CPU per source byte, one core per process | 350.6 | 386.1 | 24.1 | 16.1 |
<!-- /table:sensitivity -->

How the projection is built (`report.py`, `projection`): for each of the 215 sites, from
its K alone, the primes up to 5K + 4 (multiples of 5 skipped, as the generator skips them)
each get a tower whose Lean text `scripts/69` emits at one representative point per site
kind; the rest are composites; there are 4K nonzero terms and N = 5K series terms. Modules
are packed under `scripts/69`'s 2 MB cap, and every module pays the `Base` import probe,
plus, for the modules that import the site's prime shards, a per-byte cost of those oleans
(zero when the pilot's probes could not resolve it). Composite, term and root costs are
the pilot's in-situ rates, scaled linearly. Towers are priced two ways from the five prime
shards, per byte of tower text and flat per tower, and the request uses the larger. That
rule was fixed at 22:07 UTC, before the p = 1801 tower ran, from four shards of which two
had been miscounted (`RUNS.md`, with its correction). With the right counts the shards
cost about the same CPU per tower (69 to 75 CPU-s net) from p = 2 to p = 89 while their
text roughly doubled, which favours the flat model in that range; above p = 89 only the
`scripts/68` tower at p = 1801 speaks (cost table). That tower cost close to the same CPU
per atom as the p = 2 tower with about three times the text, so the flat model holds at
the top of the plan's primes as well, and the per-byte total most likely overprices the
towers. The rule is kept as recorded, so the flat total is the low end of the range and
the per-byte total is what the request uses. The wall table divides the core-hours by the
cores n processes would hold, at one core each or at the pilot site's measured cores per
process, capped at the box's 32 vCPU. That measured figure comes from a loaded box; the
replay table shows the same shards running at roughly twice the parallelism at a lower
load, so on a free box the cap binds sooner and the capped column is the one to read. Both
columns assume the CPU per atom stays at this pilot's rate when production saturates the
box, which this pilot could not test.

## 5. What these numbers do not say

- **One site, one K.** `B_right_06` has K = 17. Plan v2's sites run to K = 361 (the
  centre), and the grid sites carry most of the work (341,718 of the 549,149 atoms that
  `scripts/67` counts). The projection scales the pilot's tower, composite, term and
  series-term rates linearly; nothing here tests that linearity beyond K = 17, except that
  the two tower models are set against one `scripts/68` tower at p = 1801 (section 3).
- **A shared, loaded box.** Each run records its 1-minute load. CPU time (user plus
  system, from `wait4`) is the quantity priced; wall time on this box says more about the
  other workflows than about Lean. The replay table in section 3 shows how far CPU time
  moved between two runs of the same modules at different loads.
- **Not a version comparison.** The `v4.33.0-rc2` rates were measured on a machine the
  record does not name, so each ratio column mixes the Lean version, the machine and the
  load. Separating them would take a `v4.33.0-rc2` toolchain and Mathlib on this box.
- **Memory.** `wait4`'s peak RSS counts the file-backed mappings of Mathlib's oleans,
  which concurrent processes share through the page cache; the anonymous column is what
  each extra process costs.
- **Disk and the assembly.** The site's oleans are large next to its sources (the modules
  table). Production would leave the estimate in section 4's last row on disk, and the
  assembly module, importing 215 site roots as the sites are generated today, would load
  all of them into one process. Neither the disk nor that import was tested.

## 6. What is not built

`scripts/60` emits one site theorem per point or box: `upper_<id>` (big boxes),
`beta_<id>` (grid points) and `centre_lt_centre`. No script emits the module that combines
the 215 of them with `norm_deriv_DH_le`, `DH_lower_on_hcell`, `DH_lower_on_vcell` and the
square criterion (`lean/ZetaLean/DHZeroCriterion.lean`, line 185) into `theorem
davenport_heilbronn : davenport_heilbronn_statement`. The cell hypotheses of that module,
`eps' + L*h/2 <= beta`, are today checked only in Python by the generator
(`cell_requirements` in `scripts/60`); in Lean they would be discharged in the assembly
module, which does not exist. On this route, production of the 215 site theorems is
necessary for the target and not sufficient.

## 7. Resumed 2026-10-26: the tower under `decide +kernel`

**Measured**, one session on the shared box, one Lean process at a time under `nice -n 10`,
each run gated on a 1-minute load of at most 64 (the load before each run was 33 to 60).
The instrument is `decide_pilot.py`; its raw records are in
`<cache>/rung3-ball-production-decide/runs.jsonl` and its summary is the `decide_kernel`
section of `pilot.json`, written by `decide_pilot.py summarize` (not by `report.py`, whose
tables above are unchanged). Every file imports `ZetaLean.BallCertSupport`; "net" is CPU
(user plus system, `/usr/bin/time -v`) minus the median of two import-only runs, 10.8
CPU-s, whose own spread is 1.2 CPU-s.

The threshold, written in `RUNS.md` before any run: a full tower at most 10 CPU-s net
confirms a repricing of production to roughly 20 to 90 core-hours; above that the
`norm_num` price (416 core-hours) stands.

| file (prime 2 at the `scripts/68` oracle point unless named) | net CPU-s |
|---|---|
| `scripts/68` tower, staged equalities by `norm_num`, full file (1 run) | 66.1 |
| the same, equalities only (1 run) | 13.0 |
| every staged equality by `decide +kernel`, full file (2 runs) | 43.4 |
| the same, equalities only (2 runs) | 4.8 |
| whole tower, `dirichletTermBallB 32 20 64 2 10 2 S = lit := by decide +kernel` (1 run) | 2.5 |
| full tower through the whole decision: `contains_dirichletTermBallB`, its norm side condition by `decide +kernel`, then the decision (2 runs) | 3.4 |
| the same at p = 1801 on `B_right_06`'s input ball (radius 357/32768) (2 runs) | 5.3 |
| one composite product (6 = 2 x 3), `decide +kernel` (2 runs) / `norm_num` (1 run) | within the baseline's spread / 1.0 |
| one kappa product (`coeffBall 2` times the p = 2 ball), `decide +kernel` (2 runs) / `norm_num` (1 run) | 0.5 / 1.8 |

What the kernel did:

- **Every `decide +kernel` file with correct literals was accepted**, and both whole-route
  towers print only `propext`, `Classical.choice` and `Quot.sound`. The literal for the
  whole decision is the mirror's `dirichletTermBox2`; an `#eval decide (...)` of the same
  equality printed `true` before the kernel run.
- **Planted faults.** In the staged file, `Sq_10`'s radius one unit of 2^-64 low is refused
  at `ev_mul_29` and nowhere else. In the whole decision, the final ball's radius one unit
  of 2^-64 low is refused at `ev_p2`. The tactic's message there says it "failed to reduce"
  the proposition, because after the kernel rejects it the tactic retries the reduction in
  the elaborator, which stops at `round`. The file with the correct literal is accepted, and
  the two files differ in that literal only, so the kernel evaluated the tower in both.
- **The whole decision did not need its ten-minute timeout**: `Nat.sqrt`
  (`lean/ZetaLean/Ball.lean`, `sqrtUpperQ`) and the recursive `expCrB` evaluate in the
  kernel in about 2.5 CPU-s for the p = 2 tower.

**Verdict against the threshold.** The staged variant misses it: 43.4 CPU-s net, because
the staged equalities were never most of the tower's cost (13.0 of 66.1 CPU-s under
`norm_num`); the containment theorem around them is. The whole-decision route meets it at
3.4 and 5.3 CPU-s net for the two towers measured. So the repricing holds **for the
whole-decision route**. Priced the same way as section 4 (15,608 prime towers in the 215
sites, every other component kept at its 2026-10-21 price of 35.5 core-hours), production
comes to **50 to 58 core-hours** (`decide_kernel.reprice` in `pilot.json`) against the
416 of section 4.

That figure is an extrapolation, hedged here at its point of use. It comes from two
towers in standalone files, not from shards. The 2026-10-21 shards cost 10 to 20 percent
more per tower than standalone `scripts/68` files. The other 35.5 core-hours could also
fall under `decide +kernel`, which has not been measured beyond one composite and one
kappa product. Most importantly, **no generator emits the whole-decision tower yet**:
`scripts/69` emits the staged form, and changing it is outside this hunt's write scope. A
site compiled from today's generator still costs the section 4 price. `PRODUCTION.md`
lists that change as a decision for the owner before launch.

## 8. Resumed 2026-10-26: the assembly module, emitted and elaborated against stubs

`assembly.py` reads `lean/cert/rung3_plan2.json` alone and emits `Assembly.lean` and
`Separation.lean` on top of the committed module `lean/Rung3Assembly/Support.lean`. The two
emitted files are written to a work directory, not committed. `Assembly.lean` imports the
site roots `scripts/69` emits, which are not `module` files, and Lean refuses that import
from a `module` ("cannot import non-`module` ... from `module`", tried here); the tree
requires every committed `.lean` file to be a `module` (`tests/test_palomar_module_port.py`,
which failed CI on the first push of these files). `pilot.json` pins their SHA-256
(`assembly_emitted`). The hunt test checks that the text is byte-stable and matches the pin,
that it imports each of the 215 site roots `C<id>` once, and that it uses each `upper_<id>`
once, each grid point's `beta_<id>` once at a corner of its edge and twice inside, and
`centre_lt_centre` once.

How the module argues, every step a lemma of `lean/ZetaLean` or of `Support.lean`:

1. The 110 big boxes tile the four edges of the big square (half-width 7/32) end to end;
   the emitter asserts it. `hseg_of_box` / `vseg_of_box` turn each `upper_<id>` into
   `‖DH‖ ≤ 25499/10000` on its piece, `icc_merge` chains the pieces, and `frontier_cover`
   (through `frontier_dhSquare`) gives the bound on the big square's frontier.
2. `deriv_bound` applies `norm_deriv_DH_le` to that bound and weakens M / (w2 - w) to
   L = 16 on the closed small square.
3. The 104 grid points span each edge of the small square (half-width 3/64) corner to
   corner. Each pair of neighbours closes one cell by `hcell` / `vcell`, which wrap
   `DH_lower_on_hcell` / `DH_lower_on_vcell`. Each `beta_<id>` enters as
   `le_trans (by norm_num) beta_<id>`, so Lean reads β off the site theorem and `norm_num`
   checks it against the cell's need eps' + L h / 2. The emitter needs no β literal.
4. `centre_lt_centre` and the lower bound on the small frontier feed `dh_zero_of_square`,
   which gives `dh_zero_located` (a zero of `DH` with real part in
   [808517/1000000 - 3/64, 808517/1000000 + 3/64] and imaginary part within 3/64 of
   21424837/250000), and `dh_statement_of_square`, which gives
   `theorem davenport_heilbronn : davenport_heilbronn_statement`.
5. `dh_separation_of` pairs that zero (in the open strip, off the line, at height at most
   100) with RH to height 100 for Mathlib's `riemannZeta`, taken as a hypothesis whose
   text is the body of hunt #137's `RHUpToHeight 100`. `Separation.lean` discharges the
   hypothesis with `RHHeight100.rh_height_hundred`.

`dh_zero_of_square` and `dh_statement_of_square` restate the square criterion at
`lean/ZetaLean/DHZeroCriterion.lean`, line 185, with the same proof. The criterion's name
carries the word this directory may not use, so no file here names it; this was the
coordinator's decision of 2026-10-26. The hunt test scans every file here for that word,
`.lean` included. The location corollary is stated with the plan's exact square. The
task's rounded figures do not follow from it: Re s >= 0.7619 is above the square's left
edge 0.761642, and |Im s - 85.699| <= 3/64 ignores the centre's 0.000348.

**Elaborated, measured.** On the shared box, one process at a time: `Support.lean` (as a
`module`) compiled to an olean, with no errors. Then the emitted body (the text of `Assembly.lean` after its import
lines) was compiled under a harness, with `B_right_06` taken from its compiled 2026-10-21
oleans and the other 214 sites as stub interfaces. A stub is the site's `SI_<id>` or
`z_<id>` as `scripts/69` emits it, plus its theorem as an `axiom` with the generator's
statement (each β at its cell need). Result: exit 0, no errors, 124.1 CPU-s, peak RSS 6.8
GiB. `davenport_heilbronn`, `dh_zero_located'` and `dh_separation_of` each print exactly
`propext`, `Classical.choice`, `Quot.sound` and the 214 stubs, and never
`upper_B_right_06`, whose real theorem was used (`assembly_harness` in `pilot.json`). This
shows that the assembly's logic closes over the site statements. It does not prove
`davenport_heilbronn`, which needs the 214 real sites.

**Untested, precisely:**

- the 214 real sites, and whether each compiled statement matches its stub (for
  `B_right_06` it does, since it replaced its stub);
- `Assembly.lean` itself, which imports the 215 site roots in one process: 81 to 96 GB of
  mapped oleans by section 4's ratio, with no measurement;
- `Separation.lean`, which needs hunt #137's olean closure (built against the Mathlib
  vendored in `lean/vendor/zeta23`) in the same process as `lean/.lake`'s Mathlib. Both
  pin revision `065356127b1d`, but no run has combined them; only its last line and the
  import are untested, since `dh_separation_of` elaborated.

## 9. Follow-up 2026-10-26: the pilot site under `--tower whole`, and production again

**The mode.** `scripts/60 ... --tower whole` (backend `scripts/69`, `tower_mode="whole"`)
proves each prime tower by one `decide +kernel` of `dirichletTermBallB ... = Sq_10` plus
`contains_dirichletTermBallB`, as in section 7. It exports the names the staged fragment
does, so composites, terms and the root are unchanged. The default stays `staged` and is
byte-identical (`RUNS.md`). The generator refuses to emit a whole-mode tower whose
literal differs in any field from the staged chain's last ball. Generating all 215 sites
in whole mode (the census below) passed that check for all 15,608 towers.

**`B_right_06` end to end, measured.** One process on the shared box, `nice -n 10`,
generated by `scripts/60 --arith ball --shard --tower whole --only B_right_06` and
compiled by `scripts/72 --jobs 1 --module-jobs 1` (`whole_site` in `pilot.json`):

| module | CPU-s | wall s | peak RSS GiB | olean bytes |
|---|---|---|---|---|
| `CB_right_06/Base.lean` | 12.6 | 13.4 | 6.30 | 124,152 |
| `CB_right_06/Primes.lean` (23 towers) | 38.6 | 41.2 | 6.48 | 481,672 |
| `CB_right_06/Composites.lean` | 44.9 | 18.7 | 6.49 | 6,976,512 |
| `CB_right_06/Terms.lean` | 43.7 | 19.4 | 6.49 | 5,369,688 |
| `CB_right_06.lean` | 23.8 | 18.6 | 6.41 | 3,806,416 |
| **whole mode, 5 modules** | **163.6** | **111.3** | **6.49** | **16,758,440** |
| staged, 2026-10-21, 10 modules | 1,861.4 | 1,347.5 | 7.83 | 179,767,088 |

So the site costs 11 times less CPU and leaves 11 times fewer olean bytes. In situ, the 23
towers cost 1.19 CPU-s each net of the 11.1 CPU-s import, less than the 3.4 to 5.3 of the
standalone files in section 7, which each paid for their own declarations. The composites,
terms and root now carry most of the site's cost; their rates here (0.70 CPU-s per
composite, 0.48 per nonzero term, 0.15 per series term) match the 2026-10-21 in-situ rates.

**The kernel refused both planted faults.** Each fault is one tower literal one unit of
2^-64 off: Prime_2's `Sq_10` radius low, and Prime_89's real centre high. Each was
recompiled alone against the clean site's `Base`. Each was refused at that tower's
`ev_whole`, and the power lemma that uses it (`hp_B_right_06_2`, `hp_B_right_06_89`)
then failed to match.

**Import probe.** `import CB_right_06` peaked 11.7 MB above `import
ZetaLean.BallCertSupport` (6.73 GB) for 16.8 MB of site oleans: 0.70 bytes of RSS per
olean byte, against 0.66 measured on the staged site.

**Re-projection** (`whole_projection` in `pilot.json`). This is an extrapolation from
one site, hedged here at its point of use. A census emitted every site in whole mode in
memory. All 215 come to 5 modules each (1,075 in all), with 0.19 GB of sources. Per site,
CPU = modules x 11.1 + towers x 1.19 + composites x 0.70 + 4K x 0.48 + 5K x 0.15
CPU-s; the model gives `B_right_06` 162.1 against the 163.6 measured. The oleans are
scaled from the pilot site by towers, composites and K, or by source byte.

| | staged (section 4) | whole mode |
|---|---|---|
| CPU, 215 sites | 416 core-hours | **29.8 core-hours** |
| largest site | the centre, 31,817 CPU-s | the centre, 2,173 CPU-s (next: 734) |
| oleans, 215 sites | 123 to 146 GB | **14.8 to 16.0 GB** (centre at most 0.37 GB) |
| assembly import, RSS above the support modules | 81 to 96 GB | **10.3 to 11.1 GB**, on top of 6.7 GB |
| peak RSS per compile process | 7.8 GiB | 6.5 GiB |

**Where production fits** (assessed against these projections, not tested):

- **(a) This box: not as it is run today.** CPU and memory would fit: 29.8 core-hours is
  about 1 hour at 32 cores, about 2 at 16, and the assembly needs about 18 GB. But about
  16 GB of oleans plus a Mathlib build do not fit the disk while the co-tenant holds its
  floor, and the owner's decision keeps this box to pilots under one core-hour.
- **(b) GitHub Actions shards (4 vCPU, 16 GB, 14 GB disk, 6 h), with the assembly on one
  larger machine: yes, on these numbers.** The largest site is 2,173 CPU-s, about 36
  minutes at one core. Twenty jobs of about 1.5 core-hours each stay far inside 6 hours.
  One process at 6.5 GiB peak fits 16 GB. Each job keeps its share of oleans, 0.8 GB on
  average, beside the restored Mathlib build (7.6 GB here) within 14 GB. The assembly
  needs every olean (about 16 GB) plus Mathlib (about 8 GB) on one disk, and about 17 to
  18 GB of resident memory in one process. That is over a 16 GB runner, so it runs on one
  machine with 32 GB of RAM and at least 40 GB of disk. Not measured: an Actions runner's
  speed, restoring the Mathlib cache inside 14 GB, and whether the artifact quota holds
  16 GB.
- **(c) A big cloud machine is no longer required.** It remains the simplest single
  route: 32 cores, 32 GB and 40 GB of disk, about 1 to 2 hours.

## 10. Calibration on a GitHub runner, 2026-10-26

**Measured** on one `ubuntu-latest` runner (4 vCPU, 16 GB) by `rung3-production.yml` in
calibrate mode, run 40340279740 at commit `c697df4f0`, which succeeded
(`calibration_runner` in `pilot.json`). Both sites compiled under `--tower whole` at one
Lean process. Both site theorems print exactly `propext`, `Classical.choice` and
`Quot.sound`, and the verdict job counted the run.

| site | CPU-s | wall s | peak RSS GB | olean bytes | projected CPU-s (this box) | runner / projected |
|---|---|---|---|---|---|---|
| centre (K = 361) | 1,348.1 | 556.6 | 11.32 | 343,533,352 | 2,173.2 | 0.620 |
| `B_right_06` (K = 17) | 65.9 | 39.7 | 7.20 | 16,758,408 | 162.1 | 0.407 |

The job took 928 s in all, of which 295 s was setup. That setup was 119 s to free disk,
91 s for `lake exe cache get` into a fresh `lean/.lake` (the archive cache was empty on
this first run), 1 s of preflight, 50 s to build the `ZetaLean` closure and uploads.
Generation took 28 s, the compile 596 s and the axiom audit 9 s.

What changes:

- **The runner is faster than the shared box.** It used 0.41 to 0.62 of the CPU this box
  projects; the import alone, which dominates a small site, is much cheaper there.
  Scaled by the larger ratio, production is about **18.5 core-hours** on runners against
  29.8 at this box's rates. This is still an extrapolation, from two sites.
- **The centre's olean bytes fall inside the projection** (316 to 371 MB projected,
  343.5 MB measured), which supports the 14.8 to 16.0 GB total for the assembly.
- **Peak RSS grows with the site.** It was 11.3 GB for the centre, against 6.5 to 7.2
  GiB for small sites, so two centre-sized processes do not fit a 16 GB runner. The full
  plan therefore runs one Lean process per job (`lean_jobs: 1`), and `production.py`
  refuses a request in which `lean_jobs` times the calibrated peak exceeds 14 GB.

**The full plan, re-sized:** 20 jobs as before, assigned by projected CPU. Each job is
bounded by setup plus 1.5 times its runner-scaled CPU at one core: 1.43 to 1.49 hours,
against the 4-hour target and the 350-minute limit. At 6 jobs at once, the 21 jobs (20
plus the fault job) run in 4 waves.

## 11. A miss: site roots could not be imported together, and the fix

**What was wrong.** While writing the assembly runbook, an import of two runner-built
site roots (`import Ccentre` and `import CB_right_06`, from calibration run 40340279740)
failed: `environment already contains 'ZetaLean.DH.Cert.Prime_79.S' from
Ccentre.Primes`. `scripts/69` put every prime tower's public declarations in
`ZetaLean.DH.Cert.Prime_<p>`, which is not qualified by site, so any two sites sharing a
prime declare the same names. The assembly imports all 215 roots in one environment, so
it could not have elaborated with that output in either tower mode. The harness of
section 8 used one real site and stubs for the rest, so it never imported two real towers
together. That was this lane's miss, and the full run started at 14:50 was cancelled for
it (`RUNS.md`).

**The fix.** In `--tower whole` only, the tower namespace is now `Prime_<sid>_<p>`
(`scripts/69` `tower_namespace`). The staged default is unchanged and still
byte-identical: the 94 files of `B_right_06` and the centre hash equal before and after.
The staged default therefore keeps the collision, recorded below.

**Checked, measured on this box:**

- **Statically, the whole mode qualifies every name.**
  `tests/test_rung3_ball_whole_tower.py` checks that the three K = 17 sites declare
  disjoint public names, each containing its site id, and that two staged sites still
  collide. A census of all 215 sites counts every public name in whole mode
  (`namespace_census` in `pilot.json`, figures below).
- **Two real sites import together.** `B_right_06` and `B_bottom_23` were recompiled in
  whole mode, at 153.8 and 159.2 CPU-s. One probe module importing both roots elaborated
  with no error, and each site's `Prime_<sid>_2.pilot_contains_cpow` resolves.
- **The harness now uses two real sites.** The assembly body elaborated against the
  oleans of `B_right_06` and `B_bottom_23` plus 213 stubs: exit 0, no errors, 126.8
  CPU-s. `davenport_heilbronn` rests on the three standard axioms and the 213 stubs only
  (`assembly_harness`).
- **The renamed towers are still refused when faulted.** One unit of 2^-64 off is refused
  at `Prime_B_right_06_2.ev_whole` and at `Prime_B_right_06_89.ev_whole`, both in the
  re-run pilot (`whole_site`) and through `production.py fault` and `refused`.
  `whole_site_v1` keeps the first run, on which section 9's numbers and projection rest.
- **The import ratio on a large site:** importing the runner-built centre oleans (343.5
  MB) from `/dev/shm` raised peak RSS by 0.708 bytes per olean byte
  (`import_probe_centre`). That matches the 0.70 of section 9. The small renamed site's
  probe gave 0.87, on a 15 MB difference, which is within that probe's noise.

**The census of names** (`namespace_census`). All 215 sites emitted in whole mode
declare 532,652 public names, and **none repeats**. Under the staged default, each of the
15,608 towers declares the same 79 public names in `Prime_<p>`, so 1,211,070 repeated
declarations would collide (8,216 distinct names). Prime 2's tower alone appears in all
215 sites. That is the defect the staged default keeps, by the ruling that it stay
byte-identical.

## 12. Calibration again, with the renamed towers (attempt 2)

**Measured**, run 40350287309 at commit `4bac8d79d`, the same request with `"attempt":
2`, which succeeded (`calibration_runner`; section 10's run is kept as
`calibration_runner_v1`). Both sites compiled with the site-qualified tower namespaces,
and both site theorems print exactly `propext`, `Classical.choice` and `Quot.sound`.

| site | CPU-s | wall s | peak RSS GB | olean bytes | projected CPU-s (this box) | runner / projected |
|---|---|---|---|---|---|---|
| centre (K = 361) | 1,229.1 | 533.8 | 11.31 | 343,535,408 | 2,173.2 | 0.566 |
| `B_right_06` (K = 17) | 58.1 | 37.6 | 7.19 | 16,758,616 | 162.1 | 0.358 |

The job took 909 s in all, of which 308 s was setup: 146 s to free disk, 71 s for the
cache fetch (from the archive cache saved by the first run), 2 s of preflight and 43 s
for the `ZetaLean` build. The results match attempt 1 within runner variation (centre
CPU 9 percent lower, olean bytes equal to within 2.1 kB, the same peak RSS). The rename cost
nothing measurable.

**Full plan, re-sized from attempt 2:** 20 jobs, one Lean process each (11.31 GB
peak). Every job is bounded at 1.32 to 1.37 hours, setup included. On runners that comes
to about 16.9 core-hours, scaled by the larger ratio.
