# PRODUCTION: runbook for the 215 sites of plan v2 and their assembly

Hunt #145, written 2026-10-26, revised the same day after the whole-tower re-pilot. The
owner granted the production window on cloud compute that day (`MISSION.md`, "Owner
decision, 2026-10-26"). The Novita account had zero balance, so **nothing here has been
launched**. This page is what the coordinator runs once compute is funded. Every cost
below is a projection from one pilot site (`PILOT.md` sections 4 and 9), not a
measurement of production.

## 0. Decide before launch

1. **Use `--tower whole`.** The generator now has an opt-in whole-tower mode
   (`scripts/60 --tower whole`). Each prime tower is one `decide +kernel` of
   `dirichletTermBallB ... = lit` plus `contains_dirichletTermBallB`. The pilot site
   compiled in it end to end with both planted tower faults refused (`PILOT.md` section
   9). Projected: **30 core-hours** (29.8) against **416 core-hours** for the default
   `staged` mode, and 14.8 to 16.0 GB of oleans against 123 to 146 GB.
2. **Where.** On these projections the sites fit GitHub Actions shards and the assembly
   fits one 32 GB machine (section 1). That is assessed, not tested. One single cloud
   machine is the simpler alternative.
3. **One thread per process.** `scripts/72` runs `lean` at its default threads. `-j1`
   buys predictable sharing and no saving (`OWNER_MEMO.md`, item 3).

## 1. Machine shape

| resource | `--tower whole` (recommended) | `staged` (default) |
|---|---|---|
| CPU, 215 sites | 29.8 core-hours; largest site the centre, 2,173 CPU-s | 416 core-hours; the centre 31,817 CPU-s |
| wall clock, 32 dedicated cores | about 1 h plus generation | about 13 to 19 h |
| RAM per compile process | peak RSS 6.5 GiB, most of it Mathlib's oleans in the shared page cache | peak RSS 7.8 GiB, at most 1.91 GiB anonymous |
| oleans, 215 sites | 14.8 to 16.0 GB (centre at most 0.37 GB) | 123 to 146 GB |
| assembly, one process | about 17 to 18 GB RSS: 6.7 GB of support modules plus 0.70 x the oleans | 81 to 96 GB above the support modules |
| disk | about 16 GB of oleans, 0.19 GB of sources, 7.6 GB of Mathlib build | a 250 GB volume |

Where production fits, in whole mode (`PILOT.md` section 9 gives the reasons):

- **(a) The shared box: no**, while the co-tenant holds its disk floor and the owner's
  decision keeps it to pilots. Its CPU and memory would suffice.
- **(b) GitHub Actions shards of 4 vCPU, 16 GB, 14 GB disk and 6 h, with the assembly on
  one larger machine: yes, on these numbers.** Use about 20 jobs of about 11 sites each,
  balanced by projected CPU (`whole_projection.rows` in `pilot.json`). That is about 1.5
  core-hours and 0.8 GB of oleans per job. Each job uploads its `$OUT` oleans and its site
  records. The assembly machine needs at least 32 GB of RAM and 40 GB of disk; a 16 GB
  runner falls short. Not measured: a runner's speed, restoring the Mathlib cache within
  14 GB, and whether the artifact quota holds 16 GB.
- **(c) One cloud machine** of 32 cores, 32 GB and 40 GB of disk does everything in about
  1 to 2 hours. It is not required.

Never run Lake in a copied `.lake` (`CLAUDE.md`, compute rule 7).

## 2. Commands

From a fresh clone of the branch commit, on the production machine (or in each job):

```bash
python3 -m venv .venv && .venv/bin/pip install -r requirements.txt && .venv/bin/pip install -e .
cd lean && lake exe cache get          # production machine only, never on the shared box
for p in .lake/packages/*; do git -C "$p" rev-parse --show-toplevel; done   # each names itself
lake build ZetaLean.BallCertSupport ZetaLean.BallTerm   # the 15 ZetaLean modules the sites import
cd ..
```

Generate the sites. This is Python only: the census of all 215 sites in whole mode took
51 CPU-minutes, the centre 69 s and a grid point about 20 s. It parallelises per site
with `--only <id>`:

```bash
GEN=/data/rung3/gen OUT=/data/rung3/out
.venv/bin/python scripts/60_rung3_generate.py lean/cert/rung3_plan2.json "$GEN" \
  --arith ball --shard --tower whole            # or --only <id>, once per site of a job
ls "$GEN"/*.manifest.json | wc -l      # 215 on one machine
```

Compile, resume-safe. `--jobs` (sites) times `--module-jobs` (modules per site) is the
number of concurrent `lean` processes. Keep it at or below the cores (2 on a 16 GB
runner), and keep MemAvailable above 20 GiB on a large machine:

```bash
nice -n 10 .venv/bin/python scripts/72_rung3_ball_compile.py --lean-project lean \
  --output-root "$OUT" --jobs 24 --module-jobs 1 "$GEN"/*.manifest.json
```

## 3. Checkpoints

- **Per module:** `scripts/72` writes `$OUT/checkpoints/<root>/...` atomically after each
  module, with the source hash, CPU, peak RSS and return code. A restart with the same
  command skips verified modules and recompiles only what changed and its dependents.
- **Per site:** `$OUT/results/C<id>.json`, written whatever the outcome. Production is
  done when 215 records say `ok`.
- **Records:** before launch, write the estimate (one site timed, multiplied) in this
  hunt's `RUNS.md`. After it, write a runmanifest with the machine, the commit, the start
  and end times and the totals. The detached job has a watcher that records a terminal
  outcome (`CLAUDE.md`, compute rule 5).

Then the assembly, in one process, with every site root's olean on `LEAN_PATH` (they are
linked beside their sources in `$GEN`):

```bash
A=/data/rung3/assembly
.venv/bin/python hunts/rung3_ball_production/assembly.py --out "$A" --check   # emits; the pin must match
H=hunts/rung3_ball_production/lean
cd lean
lake env lean --root=../$H -o "$A/Rung3Assembly/Support.olean" ../$H/Rung3Assembly/Support.lean
lake env sh -c "LEAN_PATH=$A:$GEN:\$LEAN_PATH lean --root=$A -o $A/Rung3Assembly/Assembly.olean $A/Rung3Assembly/Assembly.lean"
```

`Assembly.lean` and `Separation.lean` are emitted, not committed: they import the
generator's site roots, which are not `module` files (`PILOT.md` section 8).

`Separation.lean` also needs hunt #137's olean closure (`hunts/rh_height_lean/lean/build.sh
--full`, built against `lean/vendor/zeta23`'s Mathlib at the same revision) on the same
`LEAN_PATH`. That combination has never been run; if the two Mathlib builds conflict,
record it and keep `dh_separation_of`, which takes RH to height 100 as a hypothesis.

## 4. Planted faults to re-run on production output

On one compiled big-box site (`B_right_06`, as in the pilot), with `pilot.py`'s work
directory set by `RUNG3_PILOT_WORK`. Each must be refused at the named declaration, and
the clean site must still compile:

```bash
export RUNG3_PILOT_WORK=/data/rung3/faults
.venv/bin/python hunts/rung3_ball_production/pilot.py site --site B_right_06
.venv/bin/python hunts/rung3_ball_production/pilot.py fault --site B_right_06 --kind tower-rad   # a tower radius 1 unit of 2^-64 low
.venv/bin/python hunts/rung3_ball_production/pilot.py fault --site B_right_06 --kind tail-rad    # the tail radius just under its bound
.venv/bin/python hunts/rung3_ball_production/pilot.py fault --site B_right_06 --kind M           # M just under the enclosure's bound
.venv/bin/python hunts/rung3_ball_production/pilot.py centre-eps                                 # eps' refused at and below the bound
```

In whole mode, also re-run the two tower faults on that site (`whole_pilot.py faults`
with `RUNG3_WHOLE_WORK` pointing at a whole-mode compile of `B_right_06` made by
`whole_pilot.py site`). Each must be refused at the faulted tower's `ev_whole`. The four
`pilot.py` faults above run on the staged sources that `pilot.py site` generates. The
tail-rad, M and centre faults sit in modules that whole mode leaves unchanged.

## 5. Axiom audit

- Every site theorem prints only `propext`, `Classical.choice` and `Quot.sound`: the check
  `pilot.py axioms` ran for `B_right_06`, which is one file per root holding
  `import C<id>` and `#print axioms ZetaLean.DH.Cert.<upper_|beta_|centre_lt_><id>`,
  compiled with `$GEN` on `LEAN_PATH`. `pilot.py` runs it only inside its own work
  layout, so for the 215 roots loop it over `$GEN` directly.
- The assembly: `#print axioms ZetaLean.DH.Rung3Assembly.Plan2.davenport_heilbronn` and
  `#print axioms ZetaLean.DH.Rung3Assembly.Plan2.dh_zero_located'` print exactly those
  three. The pilot's stub harness printed those three plus the 214 stubs
  (`assembly_harness` in `pilot.json`). With the real sites, the stubs must be gone.
- The sources: no `sorry`, `axiom`, `native_decide`, `implemented_by` or
  `Lean.ofReduceBool` in `$GEN`, `lean/ZetaLean` or `hunts/rung3_ball_production/lean`.
  `decide +kernel` adds no axiom; `native_decide` would, and is not used.

Only after that audit does `davenport_heilbronn` get a grade, through the hunt's case log
and review (`ALIGNMENT.md`). It is a statement about the Davenport-Heilbronn function and
says nothing about RH (`docs/08`).
