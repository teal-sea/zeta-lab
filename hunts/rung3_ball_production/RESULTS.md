# RESULTS: rung 3, the Davenport-Heilbronn zero off the critical line, kernel-checked

Hunt #145, closed 2026-10-26. Grade: **kernel-checked** (Lean 4 `v4.35.0-rc2`, Mathlib
`065356127b1d`, zero `sorry`, only `propext`, `Classical.choice` and `Quot.sound`),
*pending external verification*. The details below are in `PILOT.md` sections 9 to 13,
`RUNS.md` and the `production` section of `pilot.json`. The result says nothing about RH
(`docs/08`). On 2026-10-27 Lean's own kernel replayed the whole assembled closure into an
empty environment and accepted it (`leanchecker --fresh`, section 3). That is a
same-kernel replay, not an independent check, and it leaves the grade where it was. The
same day a second kernel, `con-ron --verified` (different code), checked the closure split
site by site on a fleet of cloud VMs: **accepted by an independent checker on a site-wise
split, with coverage shown** (door 1, Stage B, section 3). That does not move the grade
either: the ladder ends at kernel-checked, and no person has reviewed the result.

## 1. The theorems, exactly as compiled

**What carries the result** is one theorem, `davenport_heilbronn_strip`: some entire
function with the Davenport-Heilbronn Dirichlet series for Re s > 1 and its functional
equation has a zero in the open critical strip, off the line. It was added on 2026-10-26
(door 2 of section 6) in a module of its own, by a re-assembly of the same 215 site oleans.
Before it, the result was two theorems read together: `dh_separation_hundred` (below
height 100, `DH` has a zero in the open strip off the line, and Mathlib's `riemannZeta`
has none there) and `dh_zero_located` (a zero of `DH` in the plan's closed square), with
`dh_analytic_half` (`lean/ZetaLean/DHAnalytic.lean`: `DH` is entire, has the series for
Re s > 1 and satisfies the functional equation). All of them have the grade above:
kernel-checked, pending external verification. `dh_separation_hundred` still says more
than the bundled theorem, since it adds the comparison with `riemannZeta`. The assembly's
`davenport_heilbronn` is weaker than its name: the statement it proves is also met by the
trivial zero s = -1, as the paragraphs after the second listing say.

In `ZetaLean.DH.Rung3Assembly.Plan2` (module `Rung3Assembly.Strip`, emitted by
`assembly.py`, SHA-256 `c763fa289c8b7285...` pinned in `pilot.json` `assembly_emitted`;
it imports `Rung3Assembly.Assembly` alone, so it lies outside the sites' import closure,
which ends at `ZetaLean.BallCertSupport`):

```lean
theorem davenport_heilbronn_strip :
    ∃ (f : ℂ → ℂ) (s : ℂ), Differentiable ℂ f ∧ dh_series_rep f ∧ dh_functional_eq f ∧
      f s = 0 ∧ 0 < s.re ∧ s.re < 1 ∧ s.re ≠ 1/2
```

The witness is `f = DH` and `s` is the zero of `dh_zero_located`, whose real part lies in
[380821/500000, 26731/31250] = [0.761642, 0.855392]; `linarith` and `norm_num` give the
three strip conditions from those two bounds. `dh_analytic_half` states only
`∃ f, Differentiable ℂ f ∧ dh_series_rep f ∧ dh_functional_eq f` and so hides its witness;
the proof uses the three theorems it bundles (`DH_differentiable`, `DH_series_rep`,
`DH_functional_eq`), as `dh_analytic_half`'s own proof term does.

In `ZetaLean.DH.Rung3Assembly.Plan2` (module `Rung3Assembly.Assembly`, emitted by
`assembly.py` from `lean/cert/rung3_plan2.json`, SHA-256 `5ae46eb4a6030349...` pinned in
`pilot.json` `assembly_emitted`):

```lean
theorem davenport_heilbronn : davenport_heilbronn_statement

theorem dh_zero_located : ∃ z : ℂ, DH z = 0 ∧
    z.re ∈ Icc ((808517/1000000 - 3/64 : ℚ) : ℝ) ((808517/1000000 + 3/64 : ℚ) : ℝ) ∧
    z.im ∈ Icc ((21424837/250000 - 3/64 : ℚ) : ℝ) ((21424837/250000 + 3/64 : ℚ) : ℝ)

theorem dh_zero_located' : ∃ z : ℂ, DH z = 0 ∧
    ((380821/500000 : ℚ) : ℝ) ≤ z.re ∧ |z.im - ((21424837/250000 : ℚ) : ℝ)| ≤ ((3/64 : ℚ) : ℝ)
```

`dh_zero_located` puts a zero of `DH` in the closed square of half-width 3/64 about
0.808517 + 85.699348 i. That is the plan's exact square; the task's rounded bounds
(Re s ≥ 0.7619) do not follow from it.

`davenport_heilbronn_statement` (`lean/ZetaLean/DavenportHeilbronn.lean`, line 129) says:
some entire function has the Davenport-Heilbronn Dirichlet series for Re s > 1, satisfies
its functional equation, and has a zero s with Re s ≠ 1/2. **As defined, it is also met
by the trivial zero s = -1**: `DH` combines the L-functions of two odd characters mod 5,
which vanish at s = -1, -3, -5, …, so `davenport_heilbronn_statement_of_trivial_zero`
(`lean/ZetaLean/DHTrivialZero.lean`) proves it from `DH (-1) = 0` and
`dh_analytic_half` alone, with none of the 215 sites. The same statement for
`riemannZeta` holds at s = -2. The adversarial review of PR #353 found this on
2026-10-26. So `davenport_heilbronn` is a true theorem that carries none of the result;
the definition stays as it is because the site oleans were compiled against its module.

In module `Rung3Assembly.Separation`:

```lean
theorem dh_separation_hundred :
    (∃ s : ℂ, DH s = 0 ∧ 0 < s.re ∧ s.re < 1 ∧ 0 < s.im ∧ s.im ≤ 100 ∧ s.re ≠ 1 / 2) ∧
      ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.re → ρ.re < 1 → 0 < ρ.im → ρ.im ≤ 100 →
        ρ.re = 1 / 2 :=
  dh_separation_of RHHeight100.rh_height_hundred
```

That is: below height 100, `DH` has a zero off the line in the open strip, and Mathlib's
`riemannZeta` has none (hunt #137). Both functions satisfy a functional equation of the
same shape; only one obeys RH there.

## 2. The axioms, verbatim

`#print axioms` of all 17 final declarations, from the on-box assembly (`production.py
assemble`, log kept in the receipts):

```
'ZetaLean.DH.Rung3Assembly.Plan2.big_bottom' depends on axioms: [propext, Classical.choice, Quot.sound]
'ZetaLean.DH.Rung3Assembly.Plan2.big_top' depends on axioms: [propext, Classical.choice, Quot.sound]
'ZetaLean.DH.Rung3Assembly.Plan2.big_left' depends on axioms: [propext, Classical.choice, Quot.sound]
'ZetaLean.DH.Rung3Assembly.Plan2.big_right' depends on axioms: [propext, Classical.choice, Quot.sound]
'ZetaLean.DH.Rung3Assembly.Plan2.big_frontier' depends on axioms: [propext, Classical.choice, Quot.sound]
'ZetaLean.DH.Rung3Assembly.Plan2.deriv_bound_small' depends on axioms: [propext, Classical.choice, Quot.sound]
'ZetaLean.DH.Rung3Assembly.Plan2.small_bottom' depends on axioms: [propext, Classical.choice, Quot.sound]
'ZetaLean.DH.Rung3Assembly.Plan2.small_top' depends on axioms: [propext, Classical.choice, Quot.sound]
'ZetaLean.DH.Rung3Assembly.Plan2.small_left' depends on axioms: [propext, Classical.choice, Quot.sound]
'ZetaLean.DH.Rung3Assembly.Plan2.small_right' depends on axioms: [propext, Classical.choice, Quot.sound]
'ZetaLean.DH.Rung3Assembly.Plan2.small_frontier' depends on axioms: [propext, Classical.choice, Quot.sound]
'ZetaLean.DH.Rung3Assembly.Plan2.centre_small' depends on axioms: [propext, Classical.choice, Quot.sound]
'ZetaLean.DH.Rung3Assembly.Plan2.dh_zero_located' depends on axioms: [propext, Classical.choice, Quot.sound]
'ZetaLean.DH.Rung3Assembly.Plan2.dh_zero_located'' depends on axioms: [propext, Classical.choice, Quot.sound]
'ZetaLean.DH.Rung3Assembly.Plan2.davenport_heilbronn' depends on axioms: [propext, Classical.choice, Quot.sound]
'ZetaLean.DH.Rung3Assembly.Plan2.dh_separation_of' depends on axioms: [propext, Classical.choice, Quot.sound]
'ZetaLean.DH.Rung3Assembly.Plan2.dh_separation_hundred' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Each of the 215 site theorems (`upper_<id>`, `beta_<id>`, `centre_lt_centre`) printed the
same three axioms, in the per-job audit of `rung3-production.yml`.

The strip re-assembly (section 3) printed the same 17 lines, and this one for the new
theorem (`pilot.json` `production.strip_assembly`, log in its receipts):

```
'ZetaLean.DH.Rung3Assembly.Plan2.davenport_heilbronn_strip' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## 3. How it was built

- **Sites (GitHub Actions, run 40353536947 at `85cabd55b`).** 20 jobs compiled all 215
  sites of plan v2 under `scripts/60 --tower whole`, one Lean process per job. All 215
  were `ok` and all 215 axiom audits were clean, in 16.1 runner core-hours. The oleans
  total 15,123,966,128 bytes, the largest site was the centre (1,458 CPU-s) and the peak
  RSS was 11.3 GB.
- **The fault, paired (run 40372531479 at `78e91a542`).** The full run's fault job left
  no verdict: GitHub's `bash -e` ended the step before the exit code was captured
  (`PILOT.md` section 13). That evidence is void, not negative. After the fix, the fault
  ran alone: `B_right_06` with `Prime_B_right_06_2`'s radius one unit of 2^-64 low was
  refused at `Prime_B_right_06_2.ev_whole`. `production.py verdict --runs 40353536947
  40372531479` counts the pair: 215/215 sites, 215 clean audits, the fault refused.
- **Assembly (this box, oleans on `/dev/shm`).** `production.py collect` downloaded the
  20 job artifacts (4,744,646,464 bytes zipped) and checked every zip's SHA-256 against
  GitHub's recorded digest. `Assembly.lean`, which imports all 215 roots, compiled in 85.3
  CPU-s at 17.87 GB peak RSS (projected 17.0 to 17.9). `MemAvailable` stayed at 48.9 GiB
  or more, against the 20 GiB guard. `Separation.lean` compiled with hunt #137's oleans,
  using one `ZetaLean` overlay: `lean/CompareOleans.lean` shows that the two builds'
  shared modules have identical constants. `/dev/shm` was cleared afterwards. The
  receipts (site-root and assembly olean SHA-256, logs) are in
  `<cache>/rung3-ball-production-full/receipts`.
- **The strip re-assembly (this box, oleans on disk), 2026-10-26, 23:36 to 23:43 UTC.**
  The same steps, with `Strip.lean` added after `Separation.lean`, from this branch at
  `6bbe67707` plus the emitter change. A guarded `leanchecker` job held about 7 GB, so
  the oleans went under `<cache>`, not `/dev/shm`. `collect` downloaded the same 20 artifacts again,
  every digest equal to GitHub's and to the first collect's, in 116.8 CPU-s and 192 s of
  wall. The 215 root oleans are byte-identical to the first receipts, and every site has
  its root checkpoint. `assemble` used this checkout's `ZetaLean` oleans of 2026-10-21
  with no Lake build: their 195 files hash the same before and after. Support 8.2 CPU-s,
  Assembly 73.8 CPU-s at 18.03 GB peak RSS, Separation 10.9, Strip 10.7, the axioms print
  10.8. `MemAvailable` never fell below 63.7 GiB. The Support, Assembly and Separation
  oleans hash exactly as the first assembly's, so nothing they declare moved. The
  receipts are in `<cache>/rung3-ball-production-full/receipts-strip-20261026`.
- **Door 1, Stage A: the same-kernel fresh replay (this box, 2026-10-27, 00:35:12 to
  07:52:58 UTC).** A third collect and assemble, as above, with one more emitted module,
  `Final.lean`, which imports `Separation` and `Strip` and so holds all 18 final
  declarations in its closure; the 20 digests, the 215 root oleans and the Support,
  Assembly, Separation and Strip oleans came back byte for byte. Then
  `leanchecker --fresh Rung3Assembly.Final` (Lean `v4.35.0-rc2`'s checker, SHA-256
  `9e36e955a251b131...`), under a guard with no wall limit and a 20 GiB `MemAvailable`
  floor: it loads the closure and replays its constants into an empty kernel
  environment, sending each to the kernel (it skips only unsafe and partial constants).
  The closure is 11,955 modules and 1,569,505 constants: the 215 sites' 761,387,
  Mathlib's 580,690, Lean's core and dependencies' 202,353, hunt #137's 24,311 (because
  `Separation` imports `RHHeight100.Main100`), `ZetaLean`'s 733 and the assembly's 31.
  **Exit 0, empty output, in 7 h 17 min 46 s of one core, at 22.76 GB peak RSS**;
  `MemAvailable` never fell below 49.3 GiB. A module that does not exist exits 1, and a
  scratch olean with one radius literal changed is refused by the kernel (section 4).
  The estimate written before the run, from a seeded sample of 175 modules each replayed
  apart, was 6 to 10 hours and 18 to 26 GB. The tool's own docstring calls it "not an
  external verifier": it re-runs the same kernel on the same constants. What it adds is
  that every constant the assembly rests on, site proofs included, passed that kernel
  again in one environment, from nothing, on this box, which closes the `ZetaLean` join
  (section 5) and re-checks hunt #137's closure as well. Receipts:
  `<cache>/rung3-ball-production-full/receipts-replay-20261027` (`leanchecker-fresh.receipt.json`,
  the census, the sample and its estimate, every log); record: `pilot.json`
  `production.replay`.
- **Door 1, Stage B: the independent kernel on a site-wise split (2026-10-27, 15:03 to
  19:12 UTC).** `con-ron --verified` (the toolchain's second kernel, SHA-256
  `4e5616d94374cae3...`) checked 216 shards on InstaBox VMs (8 vCPU, 16 GiB) and Novita
  sandboxes (2 vCPU, 4 GiB), each VM checking one shard and deleted when it ended. A site
  shard holds every constant of one site's five modules, with its closure (Mathlib's and
  `ZetaLean`'s part included). `con-ron` declines any axiom but the three standard ones, so
  the top shard cannot take the site theorems as axioms; instead `lean/ExportShard.lean`
  abstracts them: for each of the 435 site theorems the assembly modules name (the 215
  site theorems and the 220 proof fields of the big boxes' interval structures) a
  definition `Rung3Glue.T.S : Prop := <type of S>`, and for each of the 18 final
  declarations, the only assembly constants that reach a site theorem, `Rung3Glue.c :
  ∀ (h₁ : Rung3Glue.T.S₁) … (h₄₃₅ : Rung3Glue.T.S₄₃₅), <type of c>`, whose value is `c`'s own
  compiled value with each `Sᵢ` replaced by `hᵢ`. Lean's kernel checked each glue
  declaration as it was added; every shard was written by the toolchain's own exporter
  (`LeanExport.dumpEnv`, byte-identical to `leanexport` on a control). The assembly oleans,
  deleted after Stage A, were rebuilt on this box and hash exactly as Stage A's. **All 216
  shards accepted**, 13,982,741 declarations in all, each shard's count equal to the
  declaration records of its stream; the export's SHA-256 was checked on each VM before
  the run. The join (`conron_fleet.py coverage`, `shard_manifest.py`): every constant held
  by more than one shard has the same kernel hash in all of them (5,140 differ only in
  binder names or binder info, which the exporter takes from whichever equal expression it
  wrote first and the kernel ignores); each of the 435 `Rung3Glue.T.S` hashes as the type
  of `S` in its site shard; and of the **675,388 constants in the dependency closure of the
  18 final declarations**, computed in the real assembled environment, 675,370 are in
  accepted shards and the other 18, the final declarations themselves, are checked through
  their `Rung3Glue` forms. By Stage A's census:

  | origin | constants | in the closure of the 18 | in an accepted shard |
  |---|---|---|---|
  | the 215 sites | 761,387 | 583,346 | 761,387 |
  | Mathlib | 580,690 | 61,252 | 61,252 |
  | Lean's core | 182,964 | 7,869 | 7,869 |
  | dependencies | 19,389 | 192 | 192 |
  | hunt #137 | 24,311 | 22,288 | 22,288 |
  | `ZetaLean` | 733 | 411 | 411 |
  | the assembly | 31 | 30 | 12 (and the 18 final declarations through `Rung3Glue`) |
  | all | 1,569,505 | 675,388 | 853,411 |

  Every site constant is in an accepted shard, the 178,041 outside the closure included.
  Outside the sites the shards hold exactly the closure; the 716,076 constants in no shard
  are all outside it (Mathlib 519,438, core 175,095, dependencies 19,197, hunt #137 2,023,
  `ZetaLean` 322, the assembly 1), and Stage A's replay covered them with Lean's kernel.
  The planted one-byte fault, exported as a whole site shard, was rejected on both
  providers (section 4). Wall: the first VM at 15:07, the last deleted at 19:12, set by
  the centre, whose shard took 3.2 hours on 8 cores (24.8 core-hours, 14.8 GB peak RSS);
  834 core-hours of `con-ron` in all. Cost: InstaBox USD 8.25 (its usage API, per
  machine), Novita USD 0.68 at list price; 222 VMs, none left on either provider. Receipts:
  `<cache>/rung3-conron-fleet-20261027` (the state files, the VM registry, every
  receipt, manifest and log); record: `pilot.json` `production.replay.stage_b_fleet`;
  `RUNS.md` has the run.

## 4. What the kernel refused

All on production output, recorded in `pilot.json` `production.box_faults` and
`production.fault_run`:

| planted fault | refused at |
|---|---|
| a prime tower's radius one unit of 2^-64 low (runner, run 40372531479) | `Prime_B_right_06_2.ev_whole` |
| the same, on this box against the downloaded oleans | `Prime_B_right_06_2.ev_whole` |
| the tail radius just under its bound | `ZetaLean.DH.Cert.enc_B_right_06` |
| M just under the enclosure's bound | `ZetaLean.DH.Cert.upper_B_right_06` |
| the centre's eps' at the bound, and at 1/4000 | `centre_lt_centre` (the probe of its last step) |
| the tower radius one unit low, one byte of a scratch `CB_right_06/Primes.olean`, exported as a whole site shard and checked by `con-ron --verified` on InstaBox and on Novita (door 1, Stage B) | `Prime_B_right_06_2.ev_whole._proof_1_1`, "application type mismatch", on both |

The eps' bracket holds: the probe is accepted at 1/2000 and at the next multiple of 2^-64
above the bound, and refused at the bound and at 1/4000.

On the strip theorem, two faults were planted in scratch copies of `Strip.lean`, compiled
against the re-assembled environment (`production.py strip-faults`; `pilot.json`
`production.strip_assembly.strip_faults`). Lean refused both at
`davenport_heilbronn_strip`, in its tactics, before any proof term reached the kernel:

| planted fault in the statement | Lean's error |
|---|---|
| `s.re < 19/25` (0.76, just left of the square's edge 0.761642) for `s.re < 1` | `linarith failed to find a contradiction` |
| `s.re ≠ 4/5` (a line through the square) for `s.re ≠ 1/2` | `unsolved goals` |

The unchanged copy, compiled the same way, was accepted.

For door 1 a fault went into a compiled olean itself (`pilot.json`
`production.replay.olean_fault`). In a scratch copy of the downloaded
`CB_right_06/Primes.olean`, the radius literal of `Prime_B_right_06_2.Sq_10`,
36391283805789411/2^63, was lowered by one unit: one byte of the file, the literal's only
occurrence. `leanchecker CB_right_06.Primes` accepts the unchanged olean and refuses the
copy at `Prime_B_right_06_2.ev_whole._proof_1_1` with "(kernel) application type
mismatch", the decision no longer evaluating to `true`. Exported, the two differ in one
record, and `con-ron --verified` accepts the clean export and rejects the planted one at
the same declaration, with the same error.

The standing test
`tests/test_epstein.py::test_no_offline_zero_below_the_pinned_one` passes. It is
measured, not rigorous: the mpmath argument principle at 20 digits counts no zero with
Re s in [0.55, 2] and 0.3 < Im s < 80.3, and one with 80.3 < Im s < 90.3. Within that
range, which covers non-trivial zeros only and leaves out 1/2 < Re s < 0.55 and
0 < Im s ≤ 0.3, no off-line zero lies below this one, so the target was forced there,
not chosen.

## 5. What this is and is not

- **Original**: this lab produced it. **Searched-and-absent**, not a novelty claim:
  the four queries in `PRIOR_ART.md` found no kernel-checked or formally verified proof
  of a non-trivial Davenport-Heilbronn zero off the line, in the critical strip, and
  that file lists the sources not searched. The zero itself is Spira's (1994), and the
  delta is its enclosure by the Lean kernel.
- **Trust.** Each site olean was produced by the runner's kernel. The assembly imports
  them without re-checking their proofs. Since 2026-10-27 the same kernel has re-checked
  the whole assembled closure from an empty environment (section 3, door 1 Stage A), and
  a second kernel, `con-ron --verified`, has accepted it on a site-wise split with coverage
  shown (door 1 Stage B). That split rests on two things a single run would not: the
  abstraction of the site theorems in the top shard, and the hash join of the shards,
  both recorded and both mechanical.
- **The ZetaLean join.** The sites were kernel-checked against each runner's own
  `ZetaLean` build at `85cabd55b`, which the workflow did not upload. The assembly
  imported them against this box's `ZetaLean` oleans of 2026-10-21, through the overlay.
  The sources of the sites' import closure have not changed since 2026-09-28 apart from
  comments, so the two builds' constants are expected to agree, but they were never
  compared. The replay would close this as well. The strip re-assembly used the same
  `ZetaLean` oleans, unchanged, so it inherits this join and adds no new one. **Closed
  on 2026-10-27**: the fresh replay re-checked, in one empty kernel environment, the
  constants actually loaded through the overlay, so every site proof passed the kernel
  against the `ZetaLean` constants the assembly uses.
- The staged default of `scripts/60` cannot produce an assemblable output: its tower
  namespaces collide across sites (`PILOT.md` section 11). Only `--tower whole` can.

## 6. The doors

This hunt priced a production and then ran it; the ceiling it measured is the cost of the
kernel check. **Active constraints at the optimum**, by measured cost share:

1. The non-tower work dominates now: on the pilot site, composites, terms and root are
   112 of 164 CPU-s in whole mode (`PILOT.md` section 9); other sites were not split.
2. The per-module import, 11 CPU-s on the box, is the floor of every module.
3. Peak RSS of the centre (11.3 GB) is the constraint that fixes one Lean process per
   runner.

The tower cost, 416 projected core-hours staged, is no longer binding at 16 runner
core-hours.

**The frozen-constant inventory** (chosen, not optimized):

- the plan's geometry (w = 3/64, eps' = 1/2000, w2 = 7/32, L = 16, M = 2.5499);
- the tower precision (nLog 32, nExp 20, p = 64, kE 10);
- the shard cap of 2 MB;
- `lean_jobs` 1 and 20 jobs;
- `decide +kernel` for the whole tower but `norm_num` for composites and terms.

Of these, two have genuine trade shape. The decision procedure for composites and terms
(measured 0.5 CPU-s against 1.8 for one kappa product, PILOT section 7) trades a
generator change for most of the remaining cost. The plan's square (w, eps') trades the
number of sites against K.

**The information class of each door**:

1. An independent kernel replay of the assembled environment, which reads more: the same
   oleans in another checker. **Stage A done, 2026-10-27**: the same-kernel fresh replay
   (section 3) accepted the closure of all 18 final declarations; it is not the
   independent half. **Stage B done, 2026-10-27, site by site** (section 3): accepted by
   an independent checker on a site-wise split, with coverage shown; 834 core-hours
   of `con-ron` on cloud VMs, USD 8.93. The pricing that came first, for one run over
   the whole closure: on samples, `con-ron` accepted the exported closure of
   `upper_B_right_06` (61,782 declarations, 690 s, 2.2 GB) and of the centre's towers for
   p = 2, 401 and 1801 (26,575 declarations), and rejected the one-byte olean fault at
   `Prime_B_right_06_2.ev_whole` (section 4). Those are second-kernel acceptances of
   samples, not of the theorem. The whole closure would be an export of 14 to 15 GB (20
   to 30 minutes at 30 to 40 GB, by the samples) and a `con-ron` run at 56 to 102 GB of
   peak RSS whose 15,608 whole-tower decisions alone cost about 1,300 core-hours: each
   took 16 s at p = 2, 400 s at p = 401 and 648 s at p = 1801, against about 1 s in Lean's
   kernel. That is 81 hours of wall at 16 workers, past this box's 24-hour and memory
   bounds, so it waits for a machine of about 128 GB and 64 cores (about 20 hours).
   Exporting site by site would hold `con-ron` to about 4 GB a run but not cut the CPU, and
   would leave the assembly's own closure to check apart. That is what ran: the VMs' cores
   did a tower in about half the time this box's did, and the assembly's closure became
   the glued top shard. `RUNS.md` has the samples and the run.
2. **Done, 2026-10-26.** A bundled strip statement, inside the data the current family
   reads. The theorem, in module `Rung3Assembly.Strip`, emitted by `assembly.py`
   (`STRIP_STATEMENT`, pinned by the hunt test) and importing `Rung3Assembly.Assembly`
   alone, outside the sites' import closure:
   `theorem davenport_heilbronn_strip : ∃ (f : ℂ → ℂ) (s : ℂ), Differentiable ℂ f ∧
   dh_series_rep f ∧ dh_functional_eq f ∧ f s = 0 ∧ 0 < s.re ∧ s.re < 1 ∧ s.re ≠ 1/2`.
   It compiled by re-running `production.py collect` and `assemble` on the box, and it
   prints `propext`, `Classical.choice` and `Quot.sound` only (section 2). Both planted
   faults in the strip condition were refused (section 4). It replaces the
   reading-together of `dh_separation_hundred` and `dh_analytic_half`, and
   `davenport_heilbronn_statement`, which the trivial zero s = -1 meets. Cost: 116.8
   CPU-s for `collect` and 114.4 CPU-s of Lean for `assemble`, against 106 and 118 the
   first time. Receipts: `<cache>/rung3-ball-production-full/receipts-strip-20261026`
   (the zips' SHA-256 in `collected.json`, the 215 root and the assembly oleans' SHA-256,
   the `ZetaLean` build's SHA-256 before and after, the emitted sources, the fault copies
   and every log).
3. Composites and terms by `decide +kernel`, inside the data the current family reads.
4. A smaller square or a different eps', inside the same data, but it needs a new plan
   and mirror validation.
5. The next off-line zeros (Spira's 114.16, 166.48, 176.70), which read more: new
   plans. Allocation among these is the owner's.

Doors 1 and 2 are cheapest before the site oleans' GitHub artifacts expire, about
2026-11-25 (30-day retention from run 40353536947). The box kept only their SHA-256 and
the logs, so after that date both need the 215 sites compiled again, 16.1 runner
core-hours at the measured rate. Doors 1 and 2 are both done, so the deadline binds
neither now; the exports' SHA-256 and manifests are kept, not the exports.
