# ZetaLean

The kernel-checked arm of zeta-lab: Lean 4 and Mathlib. A statement here counts
only when it compiles with zero `sorry`s on the standard axioms. This page is an
index; what the arm proves, rung by rung, is `docs/doors/certify.md`.

(This page replaced the Lean project template's GitHub setup text on 2026-11-21,
regrade board correction C4, `docs/reviews/2026-11-20-rh-claim-regrade-board.md`.)

## What it holds

- `ZetaLean/`: the certified arm proper, rooted at `ZetaLean.lean` (with
  subdirectories such as `ZetaLean/Pub1/`). No `sorry` is allowed anywhere in it.
- `Challenge.lean` / `Solution.lean` and `DHChallenge.lean` / `DHSolution.lean`:
  the Palomar submission surfaces; see `PALOMAR.md`. A challenge file states its
  theorems with a deliberate `sorry` for each, as that format requires; its
  solution file proves the same statements.
- `Erdos359.lean`: statement only, one deliberate `sorry`, kept outside
  `ZetaLean/` for that reason. `Erdos/`: one file per Erdős problem, whose
  advertised statements may end in `sorry` (each file says which).
- `lakefile.toml` explains each library; `lean-toolchain` pins the toolchain
  (`leanprover/lean4:v4.35.0-rc2`) and `lakefile.toml` pins Mathlib by commit.

## How to build

```bash
cd lean
PATH="$HOME/.elan/bin:$PATH" lake exe cache get   # Mathlib oleans; without them Mathlib builds from source
PATH="$HOME/.elan/bin:$PATH" lake build           # the default targets in lakefile.toml
```

The repository's `CLAUDE.md` (compute discipline) applies: one `lake build` at a
time and never beside heavy numerics on a small machine, and never run Lake in a
copied `.lake`.

## The gates (`.github/workflows/full.yml`, job "lean arm, zero sorrys")

Nightly at 07:00 UTC and on manual dispatch, after `lake build`:

- **Zero `sorry`s**: every `.lean` file under `ZetaLean/` is scanned recursively,
  comment lines and backticked mentions excepted; the step refuses to report a
  pass if it finds fewer than 20 files.
- **Axioms**: `#print axioms` audits files under `hunts/`: the Mertens chain
  (`mertens_second_theorem` must rest on `propext`, `Classical.choice`,
  `Quot.sound` and nothing else), the Gabcke coefficient recursion (two theorems
  depending on no axioms) and the Davenport-Heilbronn negative-cell
  certificates (every axiom one of the standard three). A `sorry` in any of
  these reports fails the job.
- The `zeta23ext` hunt package must assemble without `sorryAx`.
- A separate job, "the lean arm produced a verdict", turns a cancelled or
  skipped Lean job into a failure, so silence never reads as a pass.
