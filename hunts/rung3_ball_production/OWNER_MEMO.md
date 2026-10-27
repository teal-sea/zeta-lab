# OWNER MEMO: a production window for the rung-3 ball certificate

Hunt #145, 2026-10-21. To the owner, from the `rung3-pilot` lane. This memo asks for a
decision; it launches nothing. Every measured number below comes from `pilot.json`
(**measured** on the swarm box in one session); the tables are rendered from it by
`report.py`, and the hunt test checks that they still are.

## The request

A production window for the 215 sites of plan v2 (`lean/cert/rung3_plan2.json`), compiled
by `scripts/72` from `scripts/60 --arith ball --shard` output at Lean `v4.35.0-rc2`. In
short:

<!-- table:headline -->
- **Projected CPU for the 215 sites: 416 core-hours** (the larger of the two in-situ tower models; 347 to 416 across the 4 models in `PILOT.md` section 4), against the 175.0 atom-only core-hours `scripts/67` records.
- **Wall clock on this box, if it were free:** 19 hours at 16 processes and 13 hours at 24, at the 1.38 cores per process the pilot site used, capped at 32 vCPU; 26 and 17 hours if each process holds one core.
- **Memory per process:** peak RSS 7.8 GiB, of which at most 1.91 GiB anonymous; the rest is Mathlib's oleans mapped from the page cache and shared between processes.
- **Disk:** 123 to 146 GB of oleans for the 215 sites (the pilot site's 180 MB scaled per tower or per byte of tower text), against 24 GB free on this box's disk at 2026-10-21T22:46Z.
- **The assembly's import, untested:** importing the pilot site's other oleans raised a probe's peak RSS by 0.66 bytes per olean byte; at that ratio one process importing every site's oleans would map 81 to 96 GB, against this box's 115 GiB.
<!-- /table:headline -->

The owner chooses where, when and with how much disk; section "What binds" lists the
choices. Nothing runs until then.

## What the pilot established

- **The shipped pipeline compiles a site end to end at `v4.35.0-rc2`.** `B_right_06` (one of
  the three smallest big boxes, K = 17) went from `scripts/60` to ten oleans through
  `scripts/72` at one process with no edit to any generated file, after the two driver
  fixes now on `main`. Its theorem `upper_B_right_06` (`‖DH s‖ ≤ 25499/10000` on that box)
  and the enclosure under it print only the three standard axioms.
- **Lean checks what the certificate states, to the last unit.** A prime-tower radius
  one unit of 2^-64 low, the tail radius just under its bound and `M` just under the
  enclosure's bound were each refused at the named declaration (the tactic step fails, so
  no proof term reaches the kernel), and the centre's eps' step was refused at the bound
  itself and accepted at the next multiple of 2^-64 above it.
- **The mirror agrees with the kernel on the pilot site**, once the exact seed for 1^(-s)
  is accounted for; `scripts/65`'s recorded figure is the conservative one.
- **The cost is measured, not estimated, for one site.** The rates in `PILOT.md` section 3
  replace `scripts/67`'s `v4.33.0-rc2` figures on this box, with the load of every run
  recorded. The projection in the next section is an extrapolation from that one site.

## The price

Projected from the one pilot site by the model in `PILOT.md` section 4, which also shows
the spread across tower-cost models. These are measured rates extrapolated from K = 17 to
the plan's K, not a measurement of production. The tables use the larger of the two
in-situ tower models, by a rule fixed before all the data were in; section 4 of `PILOT.md`
says why the smaller, flat-per-tower total is likely the better estimate (a tower's CPU
barely grew from p = 2 to p = 1801 while its text tripled).

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

The same totals under each tower-cost model:

<!-- table:sensitivity -->
| tower cost model | tower core-hours | total core-hours | wall hours at 16 | wall hours at 24 |
|---|---|---|---|---|
| in-situ shard CPU per source byte (the request uses this one) | 380.5 | 416.0 | 18.8 | 13.0 |
| in-situ shard CPU per tower, flat in the prime | 315.0 | 350.5 | 15.9 | 10.9 |
| least-squares fit, per tower plus per byte, over `scripts/68` towers and the shards | 311.6 | 347.1 | 15.7 | 10.8 |
| `lean -j1` shard CPU per source byte, one core per process | 350.6 | 386.1 | 24.1 | 16.1 |
<!-- /table:sensitivity -->

## What binds, and what the owner decides

1. **CPU, and where it comes from.** Prime towers are most of the projected cost (the
   table above), and on this box CPU is the binding resource: 32 vCPU, shared with other
   workflows. Under Lean's default threading the pilot site's modules used anywhere from
   under one core to more than three, depending on the module and the load, while their
   CPU totals moved much less (`PILOT.md` section 3). So the wall clock depends on how
   many cores production gets more than on how many processes it runs: the wall table
   brackets it between one core per process and the pilot's measured cores per process,
   capped at the box's 32 vCPU. **Decision: where, and for how long.** On the swarm box, a
   window in which other workflows stay off it, or a longer one shared. On GitHub Actions,
   which `CLAUDE.md` makes the default compute (20 parallel jobs, 16 GB runners), sites
   are independent jobs; this pilot did not time an Actions runner, so the rates here do
   not transfer without a one-site timing there. Modal only if neither fits.
2. **Disk.** Production leaves the olean estimate in the headline on disk, far above what
   this box has free. **Decision: free space, or a volume**, before the first shard.
   Deleting a site's oleans after it compiles would keep the kernel check of that site
   but forfeit the assembly, which must import them (item 4).
3. **Threads and linters per process.** `scripts/72` runs `lean` with its default
   threads, and the generated files trip Mathlib's style linters on every tower (the
   modules table in `PILOT.md` counts the warnings). Measured here:

<!-- table:levers -->
   - **`lean -j1`:** the `scripts/68` tower cost 2.25 CPU-s per atom against 2.09 under default threads.
   - **`lean -j1` on `CB_right_06/Primes02.lean`:** 359 CPU-s net of import against 377 under default threads in the site compile.
   - **Linters off (`-Dlinter.all=false`):** the `scripts/68` tower cost 2.25 CPU-s per atom against 2.09 with them on.
<!-- /table:levers -->

   Neither moved the tower's CPU outside the spread of its default runs: threads only
   change how processes share cores, and the linters are not where the time goes.
   **Decision: whether to run one thread per process** (`-j1` passed by the driver, one
   process per core granted), which buys predictable sharing of a busy box and no saving;
   it is a small, reviewable change that touches no mathematics.
4. **The assembly first, or in parallel.** No script emits the module that proves
   `davenport_heilbronn` from the 215 site theorems. As the sites are generated today, a
   module importing all 215 site roots also loads every tower's olean, so the assembly
   needs the whole production output on disk at once, and its memory is untested.
   Lean's module system (`module` files with private imports, which Mathlib at this
   revision uses) is the candidate mechanism for importing only each root's statement;
   it is untested here too. **Decision: whether to fund an assembly prototype on two or
   three sites** before committing the window.

## What production does not give

Production as specified gives 215 kernel-checked site theorems, one per point or box of
plan v2: `upper_<id>` on the 110 big boxes, `beta_<id>` at the 104 grid points and
`centre_lt_centre`. It does not give `theorem davenport_heilbronn :
davenport_heilbronn_statement`. That needs an assembly module, which no script emits yet,
combining the site theorems with `norm_deriv_DH_le`, `DH_lower_on_hcell`,
`DH_lower_on_vcell` and the square criterion (`lean/ZetaLean/DHZeroCriterion.lean`, line
185). The pilot priced the sites, not that module, and the assembly's import closure is
the largest unpriced item in this memo. Nothing here bears on RH (`docs/08`).
