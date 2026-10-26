# PRODUCTION: runbook for the 215 sites of plan v2 and their assembly

Hunt #145, written 2026-10-26. The owner granted the production window on cloud compute
that day (`MISSION.md`, "Owner decision, 2026-10-26"). The Novita account had zero
balance, so **nothing here has been launched**. This page is what the coordinator runs
once compute is funded. Every cost below is a projection from one pilot site and a few
towers (`PILOT.md` sections 4 and 7), not a measurement of production.

## 0. Decide before launch

1. **Which tower route.** The generator today (`scripts/69`) emits each prime tower as 75
   staged equalities closed by `norm_num` plus a containment theorem. Priced that way,
   production is **416 core-hours** (`PILOT.md` section 4). A tower proved through one
   `decide +kernel` of `dirichletTermBallB ... = lit` and `contains_dirichletTermBallB`
   cost 3.4 to 5.3 CPU-s net in the pilot, against about 66 under `norm_num`. With every
   tower emitted that way, production is projected at **50 to 58 core-hours**
   (`PILOT.md` section 7). That route needs a change to `scripts/69`, which is outside
   this hunt's write scope, then one pilot site recompiled from the new generator and the
   faults in section 4 re-run on it, before any shard launches. Recommendation: make the
   change first. It costs about one site compile and cuts the bill by a factor of about 7.
2. **One thread per process.** `scripts/72` runs `lean` at its default threads. `-j1`
   buys predictable sharing and no saving (`OWNER_MEMO.md`, item 3).
3. **Where the assembly runs** (section 3). It needs the whole olean output on one disk
   and, by the pilot's ratio, 81 to 96 GB of resident memory in one process. That is
   untested.

## 1. Machine shape

| resource | staged route (today's generator) | whole-decision route (after the change) |
|---|---|---|
| CPU | 416 core-hours | 50 to 58 core-hours |
| wall clock, 32 dedicated cores | about 13 to 19 h (`OWNER_MEMO.md` wall table) | about 2 h plus generation, by the same scaling |
| RAM per compile process | peak RSS 7.8 GiB, at most 1.91 GiB anonymous; the rest is Mathlib's oleans in the page cache, shared | not measured in shards; standalone whole-route towers peaked at 6.6 GB |
| RAM for the assembly | 81 to 96 GB projected for one process (untested): **128 GiB machine** | the same, if the tower oleans are about as large (unmeasured) |
| disk | 123 to 146 GB of site oleans, 6.3 GB of tower sources, 7.6 GB of Mathlib build: **a 250 GB volume** | not measured; plan for the same |

Shape: one machine of 32 or more cores, 128 GiB RAM and 250 GB of disk carries both the
sites and the assembly. Sites are independent, so several smaller machines can run them
in parallel (16 GB is enough per process). Their oleans must then be copied to the
assembly machine. Never run Lake in a copied `.lake` (`CLAUDE.md`, compute rule 7).

## 2. Commands

From a fresh clone of the branch commit, on the production machine:

```bash
python3 -m venv .venv && .venv/bin/pip install -r requirements.txt && .venv/bin/pip install -e .
cd lean && lake exe cache get          # production machine only, never on the shared box
for p in .lake/packages/*; do git -C "$p" rev-parse --show-toplevel; done   # each names itself
lake build ZetaLean.BallCertSupport ZetaLean.BallTerm   # the 15 ZetaLean modules the sites import
cd ..
```

Generate every site (Python only; `B_right_06` took 2 s and the centre 27 s, so the 215
sites take at most about 1.6 hours serially and parallelise per site with `--only <id>`):

```bash
GEN=/data/rung3/gen OUT=/data/rung3/out
.venv/bin/python scripts/60_rung3_generate.py lean/cert/rung3_plan2.json "$GEN" --arith ball --shard
ls "$GEN"/*.manifest.json | wc -l      # 215
```

Compile, resume-safe. `--jobs` (sites) times `--module-jobs` (modules per site) is the
number of concurrent `lean` processes. Keep it at or below the cores, and keep
MemAvailable above 20 GiB:

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

If the whole-decision route is adopted, also re-run `decide_pilot.py`'s two faults
(`TowerDecideFault.lean`, `TowerWholeFault_p2.lean`) against the new generator's output.

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
