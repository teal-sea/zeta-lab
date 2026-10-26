# RESULTS: rung 3, the Davenport-Heilbronn zero off the critical line, kernel-checked

Hunt #145, closed 2026-10-26. Grade: **kernel-checked** (Lean 4 `v4.35.0-rc2`, Mathlib
`065356127b1d`, zero `sorry`, only `propext`, `Classical.choice` and `Quot.sound`),
*pending external verification*. The details below are in `PILOT.md` sections 9 to 13,
`RUNS.md` and the `production` section of `pilot.json`. The result says nothing about RH
(`docs/08`).

## 1. The theorems, exactly as compiled

**What carries the result** is `dh_separation_hundred` (below height 100, `DH` has a zero
in the open strip off the line, and Mathlib's `riemannZeta` has none there) and
`dh_zero_located` (a zero of `DH` in the plan's closed square), read with
`dh_analytic_half` (`lean/ZetaLean/DHAnalytic.lean`: `DH` is entire, has the series for
Re s > 1 and satisfies the functional equation). Their grade is the one above:
kernel-checked, pending external verification. The assembly's `davenport_heilbronn` is
weaker than its name, as the paragraph after the first listing says.

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

The eps' bracket holds: the probe is accepted at 1/2000 and at the next multiple of 2^-64
above the bound, and refused at the bound and at 1/4000. The standing test
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
  them without re-checking their proofs. No independent replay (`leanchecker`, a second
  kernel) has run over the assembled environment; that is the first door below.
- **The ZetaLean join.** The sites were kernel-checked against each runner's own
  `ZetaLean` build at `85cabd55b`, which the workflow did not upload. The assembly
  imported them against this box's `ZetaLean` oleans of 2026-10-21, through the overlay.
  The sources of the sites' import closure have not changed since 2026-09-28 apart from
  comments, so the two builds' constants are expected to agree, but they were never
  compared. The replay would close this as well.
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
   oleans in another checker.
2. A bundled strip statement, inside the data the current family reads: one theorem
   `∃ f s, Differentiable ℂ f ∧ dh_series_rep f ∧ dh_functional_eq f ∧ f s = 0 ∧
   0 < s.re ∧ s.re < 1 ∧ s.re ≠ 1/2`, defined outside the sites' import closure (for
   example in `Support.lean`), emitted by `assembly.py` and compiled by re-running
   `production.py collect` and `assemble` on the box (on 2026-10-26 these took 106 CPU-s
   and 118 CPU-s, about 4 core-minutes together). It would replace the
   reading-together of `dh_separation_hundred` and `dh_analytic_half`, and
   `davenport_heilbronn_statement`, which the trivial zero s = -1 meets.
3. Composites and terms by `decide +kernel`, inside the data the current family reads.
4. A smaller square or a different eps', inside the same data, but it needs a new plan
   and mirror validation.
5. The next off-line zeros (Spira's 114.16, 166.48, 176.70), which read more: new
   plans. Allocation among these is the owner's.

Doors 1 and 2 are cheapest before the site oleans' GitHub artifacts expire, about
2026-11-25 (30-day retention from run 40353536947). The box kept only their SHA-256 and
the logs, so after that date both need the 215 sites compiled again, 16.1 runner
core-hours at the measured rate.
