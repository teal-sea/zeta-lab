# hardy_ten_zeros: run manifests

One 4-core, 15 GB container, 2026-10-14, times UTC. Lean compiles ran one at a time, each
after a check that no other `lean` process was running, and the numerics waited for Lean,
with one small exception recorded in the notes (`CLAUDE.md`, compute discipline). The Lean
environment is the main clone's pinned Mathlib build (`lean/.lake`, Mathlib `065356127b1d`, toolchain `v4.35.0-rc2`),
read-only. The four `ZetaLean` modules and the six `HardyFirstZero` modules this hunt imports
were compiled from this worktree's own sources into a scratch directory by hunt #132's
`lean/build.sh`, and this hunt's files were compiled against that directory with
`lean --root=hunts/hardy_ten_zeros/lean ... -o <scratch>`, which is what `lean/build.sh` here
does. No `lake build` was run and nothing was built inside the tree.

## Estimate before spending, 2026-10-14

Measured units (runs `term-cost` and `first-bracket` below): one exp tower for a prime term
box at `t = 49.77` costs about 1.2 to 1.3 s of kernel time at `(nLog, nExp, p, kE) =
(36, 16, 80, 8)`, against 2.2 to 2.9 s at hunt #132's `(40, 24, 96, 8)`; the whole generated
file for the `(21.02, 21.03)` bracket, 17 towers, 28 composite products and the assembly,
compiles in 52 s wall. The order-4 plan of `sizing.py` needs 219 towers and 447 composites
over the nine new brackets, so the projection is 219 x 52/17 s, about 11 minutes, plus about
4 minutes for the dependencies. Well inside the stop rule's few hours; no run is long enough
to need more than the per-bracket checkpoint the one-file-per-bracket layout gives.

```runmanifest
id: hardy_ten_zeros-2026-10-14-dependency-build
hunt: hardy_ten_zeros
started: 2026-10-14T12:33Z
finished: 2026-10-14T12:50Z
ran:
  - LAKE_DIR=/home/user/zeta-lab/lean/.lake bash hunts/hardy_first_zero/lean/build.sh <scratch>/build
outcome: ZetaLean Rigor, IntervalExp, IntervalCExp, HardyZ and the six HardyFirstZero modules compiled from this worktree's sources, the nine hunt 132 axiom reports standard; 1042 s wall, most of it the first Mathlib import from a cold page cache
artifacts:
  - hunts/hardy_first_zero/lean/build.sh
```

```runmanifest
id: hardy_ten_zeros-2026-10-14-term-cost
hunt: hardy_ten_zeros
started: 2026-10-14T12:32Z
finished: 2026-10-14T12:51Z
ran:
  - lean on a scratch file of six decide +kernel checks of one term box at s = 1/2 + 49.77i (m = 51 and m = 3) with set_option profiler true, in two orders
  - .venv/bin/python mirror widths of dirichletTermBox2 at five parameter sets, t = 21.02 and 49.77, m < 70
outcome: the profiler's type-checking times are cumulative; differenced, one box costs 2.2 to 2.9 s at (40, 24, 96, 8), 1.2 to 1.3 s at (36, 16, 80, 8), 0.9 to 1.3 s at (36, 12, 64, 10) and 1.2 to 1.4 s at (32, 16, 64, 8), and the normBound side condition 0.16 to 0.21 s; worst mirror widths at t = 49.77 are 9.3e-10, 1.5e-8, 1.4e-8 and 2.4e-7, against radii near 1e-3; (36, 16, 80, 8) was chosen
artifacts:
  - hunts/hardy_ten_zeros/sizing.py
```

```runmanifest
id: hardy_ten_zeros-2026-10-14-sizing
hunt: hardy_ten_zeros
started: 2026-10-14T12:30Z
finished: 2026-10-14T12:56Z
ran:
  - .venv/bin/python hunts/hardy_ten_zeros/sizing.py --no-write
outcome: hunt 132's phase window leaves the quarter turn at two-decimal brackets from (30.42, 30.43) on (lower end -2.31 there, -6.19 at 49.77); the tail window with m = 8 stays in [-0.0581, 0.0307] with true constants and [-0.0889, 0.0357] with the Lean instantiation's crude ones; order 4 with per-endpoint truncations and the Lean radii at margin 1.5 needs 684 term boxes over brackets 2 to 10, order 6 needs 334 and order 8 needs 246 with sharp bounds
artifacts:
  - hunts/hardy_ten_zeros/sizing.py
  - hunts/hardy_ten_zeros/artifacts/sizing.json
```

```runmanifest
id: hardy_ten_zeros-2026-10-14-support-lean
hunt: hardy_ten_zeros
started: 2026-10-14T12:51Z
finished: 2026-10-14T12:57Z
ran:
  - lean --root=hunts/hardy_ten_zeros/lean HardyTenZeros/PhaseShort.lean, two compile cycles of about 7 to 10 s
  - lean --root=hunts/hardy_ten_zeros/lean HardyTenZeros/TenSupport.lean, four compile cycles of about 10 s
outcome: le_phi_tail, gammaR_re_pos_tail and gammaR_re_pos_short (the phase lemma for every bracket of width at most 1/100 below 50), emN_bound (the order-4 remainder at any truncation), cBox_contains, zeta_mem_mainBox, contains_cpow_mul_coarsen and zero_of_tables compile with zero sorrys
artifacts:
  - hunts/hardy_ten_zeros/lean/HardyTenZeros/PhaseShort.lean
  - hunts/hardy_ten_zeros/lean/HardyTenZeros/TenSupport.lean
```

```runmanifest
id: hardy_ten_zeros-2026-10-14-first-bracket
hunt: hardy_ten_zeros
started: 2026-10-14T12:57Z
finished: 2026-10-14T12:59Z
ran:
  - .venv/bin/python hunts/hardy_ten_zeros/gen_boxes.py --only 2102
  - lean --root=hunts/hardy_ten_zeros/lean HardyTenZeros/Box2102.lean
outcome: zero_in_2102 compiles in 52 s wall (17 exp towers, 28 composite products, the product decision and the assembly); the generator's exact pre-check puts the upper end of the product at -7.20e-6, and at -1.90e-7 with the radii multiplied by 1.5
artifacts:
  - hunts/hardy_ten_zeros/gen_boxes.py
  - hunts/hardy_ten_zeros/lean/HardyTenZeros/Box2102.lean
```

```runmanifest
id: hardy_ten_zeros-2026-10-14-all-brackets
hunt: hardy_ten_zeros
started: 2026-10-14T12:59Z
finished: 2026-10-14T13:11Z
ran:
  - .venv/bin/python hunts/hardy_ten_zeros/gen_boxes.py
  - lean --root=hunts/hardy_ten_zeros/lean HardyTenZeros/Box<tag>.lean for the eight brackets after 2102, serially, each olean a checkpoint
  - lean --root=hunts/hardy_ten_zeros/lean HardyTenZeros/PhaseShort.lean (with window_132_fails_at_4977 added), TenZeros.lean (two compile cycles, the second after normalizing 1/2 to 2⁻¹ in the hypotheses) and CheckAxioms.lean
  - .venv/bin/python hunts/hardy_ten_zeros/lean/check_axioms.py on the CheckAxioms output
outcome: every bracket file compiles (wall seconds 2102 52, 2501 69, 3042 65, 3293 67, 3758 78, 4091 91, 4332 83, 4800 91, 4977 97; 692 in all against 11.2 minutes projected); ten_zeros_on_line_below_fifty compiles in 22 s; the audit accepts exactly the twenty reports, each propext, Classical.choice, Quot.sound
artifacts:
  - hunts/hardy_ten_zeros/gen_boxes.py
  - hunts/hardy_ten_zeros/lean/HardyTenZeros/TenZeros.lean
  - hunts/hardy_ten_zeros/lean/CheckAxioms.lean
  - hunts/hardy_ten_zeros/lean/check_axioms.py
```

```runmanifest
id: hardy_ten_zeros-2026-10-14-planted-faults
hunt: hardy_ten_zeros
started: 2026-10-14T13:12Z
finished: 2026-10-14T13:45Z
ran:
  - lean on a scratch file importing Box2102 with a control and four faults (one digit of the m = 13 literal, the box of 7 claimed as the product of the boxes of 2 and 3, a radius half the remainder bound, both radii doubled in the product)
  - lean on a scratch file proving the negations of the first, second and fourth faults by decide +kernel
  - .venv/bin/python -m pytest -q -o addopts='' hunts/hardy_ten_zeros with the remainder constant 720 changed to 700 in sizing.lean_radius, then gen_boxes.py --check, then both again after restoring
outcome: the control is accepted and all four faults refused (three by decide +kernel, one by norm_num reducing the side condition to False); the three negations are accepted, so the kernel decides those statements false; the planted 700 turned 6 of the 41 tests then present red and made gen_boxes.py --check exit 1, repeated at 13:37Z against 43 tests it turned 7 red, and at 13:44Z against the final 45 it turns 8 red, gen_boxes.py --check exiting 1 each time; restored, 45 of 45 pass and the check exits 0
artifacts:
  - hunts/hardy_ten_zeros/test_hardy_ten_zeros.py
```

```runmanifest
id: hardy_ten_zeros-2026-10-14-prior-art
hunt: hardy_ten_zeros
started: 2026-10-14T13:02Z
finished: 2026-10-14T13:06Z
ran:
  - arXiv API, six queries listed in RESULTS.md section 6
  - zbMATH Open API, eight queries listed in RESULTS.md section 6, three of them retried after an empty first response
  - web search, four queries
outcome: no formal localization of several explicit nontrivial zeros found; new since hunt 132's search are arXiv 2609.33043, 2610.08965 (proportions) and 2610.03728 (a Riemann-Siegel decomposition with a Lean corollary), none locating a zero; GitHub code search and the Lean Zulip were not reachable
artifacts:
  - hunts/hardy_ten_zeros/RESULTS.md
```

```runmanifest
id: hardy_ten_zeros-2026-10-14-clean-build
hunt: hardy_ten_zeros
started: 2026-10-14T13:17Z
finished: 2026-10-14T13:35Z
ran:
  - LAKE_DIR=/home/user/zeta-lab/lean/.lake bash hunts/hardy_ten_zeros/lean/build.sh <fresh scratch dir>
  - .venv/bin/python hunts/hardy_ten_zeros/lean/check_axioms.py on that log
outcome: exit 0 in 1029 s wall; ZetaLean Rigor, IntervalExp, IntervalCExp, HardyZ and the six HardyFirstZero modules compiled from this tree's sources in 240 s, the two support files in 17 s, the nine bracket files in 738 s (53, 68, 72, 76, 79, 99, 89, 97, 105 s), TenZeros in 28 s and CheckAxioms in 6 s; the statement prints as ∃ ts, StrictMono ts ∧ ∀ (k : Fin 10), 0 < ts k ∧ ts k < 50 ∧ riemannZeta (1 / 2 + ↑(ts k) * I) = 0; the audit accepts exactly the twenty reports; the only warnings are two linter notes in ZetaLean/IntervalCExp.lean and ZetaLean/HardyZ.lean, which this hunt does not edit
artifacts:
  - hunts/hardy_ten_zeros/lean/build.sh
  - hunts/hardy_ten_zeros/lean/check_axioms.py
```

```runmanifest
id: hardy_ten_zeros-2026-10-14-sizing-final
hunt: hardy_ten_zeros
started: 2026-10-14T13:13Z
finished: 2026-10-14T13:44Z
ran:
  - .venv/bin/python hunts/hardy_ten_zeros/sizing.py, after the Lean runs, writing artifacts/sizing.json
  - the same truncation rule at margin 1, and the mirror's normBound for m = 151, 157, 163, 167 at t = 49.78
outcome: the Arb defect sits inside every Lean radius with ratios 6.85 to 14.94; keeping hunt 132's window at the last ordinate would need the bracket (49.7728, 49.7748) with 80 and 83 terms (45 towers) against 55 and 50 (31 towers); margin 1.5 costs 684 terms against 615 at margin 1; kE = 8 covers every prime up to 157 at t = 49.78 (normBound 254.2) and 163 would need kE = 9; the cost model per tower projects 11.2 minutes for order 4, 6.7 for order 6 and 5.3 for order 8
artifacts:
  - hunts/hardy_ten_zeros/sizing.py
  - hunts/hardy_ten_zeros/artifacts/sizing.json
```

## Notes

- **Timings are wall clock on a shared container** with a warm page cache after the first
  run; the first dependency build took 1042 s, most of it the first Mathlib import.
- **The profiler's `type checking took` lines are cumulative within a file**, which the
  `term-cost` run found by reordering the same six checks; the per-check costs above are
  differences.
- **No `lake build` was run and no two Lean processes ran together.** One breach of the
  numerics rule: a small mirror-width computation (about a second of CPU, at reduced
  priority) ran at 12:44Z while the first dependency build was importing Mathlib. Every
  other numerical run waited for Lean to finish.
  The scratch directory used for builds also holds files from earlier sessions of this
  container; none of them was read or used.
