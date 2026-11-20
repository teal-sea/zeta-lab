# alpoge_replay: build the Alpöge archive, print its axioms

Opened 2026-11-20, the day the archive appeared. Hunt #159.

## What this is

On 2026-11-20 Levent Alpöge posted a four-page note (`https://alpo.ge/remark.pdf`)
saying that he and Claude have a proof of the Riemann hypothesis and of the
generalized Riemann hypothesis for Dirichlet L-functions, formalized in Lean,
and released only the Lean: fourteen archive parts on the same site. This hunt
does one thing with that archive. It builds it with the toolchain it names, on
compute this laboratory controls, and prints the axioms behind its final
theorems.

This is a replay, not mathematics. It reads no proof and judges no idea.

## The object, measured from the archive itself

Text-level facts, read on 2026-11-20 from the joined archive
(sha256 `9631b4f020199e580ba86178cb56c6e9b09f690c2369a80dc4334aa93f49c7fc`,
239,275,554 bytes). No kernel was involved in any of them.

| | |
| --- | --- |
| files | 175,187 `.lean`, one `lakefile.toml`, one `lake-manifest.json`, one `lean-toolchain` |
| size | 1,030,531,854 bytes of Lean source, 17,374,215 lines |
| toolchain | `leanprover/lean4:v4.33.1` |
| Mathlib | pinned at `0df444a360ea`, which is upstream's tag `v4.33.1` (2026-08-21); the eight transitive pins equal Mathlib's own manifest at that tag |
| import graph | 753,261 edges inside the archive, longest chain 203, every file in the import closure of `Main` |
| external imports | `Mathlib`, `Batteries`, `Lean` only |
| the claim | `Main.lean`, twelve lines, five theorems; the first is `theorem riemannHypothesis : RiemannHypothesis`, where `RiemannHypothesis` is Mathlib's definition and nothing in the archive redefines or shadows it |
| the other four | stated in `Statements.lean`, which imports Mathlib only: zeros of `riemannZeta`, nonvanishing of every `DirichletCharacter.LFunction` for real part above one half, zeros in the strip on the line, and the primitive case |
| not in it | Dedekind zeta functions (the note says the extended hypothesis is expected, not done) |
| words absent from every file | `sorry`, `admit`, `axiom`, `native_decide`, `unsafe`, `implemented_by`, `extern`, `#eval`, `skipKernelTC` |
| notation | 1,722 declarations, every one `local` or `scoped`; none can reach `Main.lean` |
| metaprogramming | five `run_cmd` lines that add names to a suggestion deny-list; three small elaborators (`kexactB`, `kcopy`, `cpt_copy_thms`) and two unification hints, used in about fifty files, all of which hand a term to the kernel without the elaborator's own check |

The last row matters for what a replay means. In those files the elaborator is
bypassed on purpose and the kernel is the only checker.

## What a pass would establish, and what it would not

A pass is: every one of the 175,187 modules elaborated by Lean 4.33.1 with no
error, no `declaration uses 'sorry'` warning, and `#print axioms` on the five
theorems listing nothing outside `propext`, `Classical.choice`, `Quot.sound`.
On this tree's ladder that is the third rung for the five statements, with
these limits stated at the point of use:

1. **One kernel.** The Lean kernel inside `lean`, nothing else. A second
   kernel is a separate job and is not in this hunt's first stage.
2. **Outputs travel between runners.** The archive does not fit one job, so a
   module is elaborated on one runner against `.olean` files produced on
   others. Lean trusts an imported `.olean`. The archive's own code was read at
   text level and does no input or output, but that is a reading. Replaying the
   finished environment through a kernel on one machine would remove this
   trust; until that is done the claim is "built in shards", said that way.
3. **The statements are Mathlib's.** That `riemannZeta` is the zeta function
   is Mathlib's content, pinned there by its Dirichlet series for real part
   above one and its differentiability away from one. This hunt adds nothing
   to that and takes nothing from it.
4. **Nothing about the mathematics.** Whether the argument is what the note
   describes, whether it can be read, and whether any of it is new are not
   questions a build answers.

A failure is as informative as a pass and is recorded the same way: the first
module that does not elaborate, with its error, on a clean pinned toolchain.

## How

`replay_plan.py` reads the import graph and cuts the unbuilt part into rounds
of independent shards. `replay_shard.py` runs one shard under a deadline and
records what finished. `.github/workflows/replay-alpoge-rh.yml` runs a round on
hosted runners, bundles its outputs, and can dispatch the next round by
itself. Allocations, estimates and outcomes are in `RUNS.md`.

The archive is never built on a laboratory machine or in an assistant's
container. It is data from outside this repository and is elaborated only on
hosted runners that hold a read-only token.

## HuntSpec

```huntspec
id: alpoge_replay
question: Does Lean 4.33.1 with Mathlib v4.33.1 accept every module of the archive posted at alpo.ge on 2026-11-20, and which axioms do the five theorems of its Main.lean depend on?
frontier: text-level reading only as of 2026-11-20, 175187 modules, zero built, no kernel run by anyone outside the authors that this laboratory has seen
proposed_attack: sharded lake build on hosted runners with outputs carried between rounds, then an axiom printout on the whole environment
dead_routes:
  - one six-hour job, the archive is about sixty times the October replay by module count
  - building in an assistant container, refused, the archive is outside data and elaboration runs its code
  - reading the 17 million lines by eye
required_oracles:
  - the Lean 4.33.1 kernel, run by lake build on a hosted runner
  - the output of print axioms on the five theorem names
  - the sha256 of the joined archive
kill_conditions:
  - a module fails to elaborate on the pinned toolchain with an error that is not a resource limit
  - the build log reports a declaration using sorry
  - print axioms lists sorryAx or any axiom outside propext, Classical.choice, Quot.sound
  - a restored module is rebuilt on a later runner with a different result
agents_may:
  - plan and run the shards
  - record timings, sizes and failures
  - report the axiom printout verbatim
agents_may_not:
  - call the proof correct
  - call anything here reviewed mathematics
  - promote their own claim
  - edit the archive or its build configuration
```

## What this hunt may touch

`hunts/alpoge_replay/` and `.github/workflows/replay-alpoge-rh.yml`, on branch
`claude/bold-ramanujan-x7z42m`. Not `zeta/`, `lean/`, `docs/`, `README.md` or
`ROADMAP.md`. A lab record of the outcome is a `docs/` page and is not written
from here.
