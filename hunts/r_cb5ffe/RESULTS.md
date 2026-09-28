# Results: the detection power of `tests/test_doors.py`

**Status: settled, at the level a mutation battery can settle it.** Ten
mutants built, ten run, one null control. The guard's power against this
battery is **5/10**, and the five it misses are not scattered, they are one
structural gap plus its consequences.

Nothing here is evidence for or against RH (`docs/08`). Nothing here is a
result about ζ; it is a measurement of one of this tree's own guards.

## Null control

An unmutated `git worktree` at HEAD `40e42f7` passes both tiers, so a
non-zero exit below is attributable to the mutant and not to the container.

| tier | command | outcome |
|---|---|---|
| fast | `pytest tests/test_doors.py -m "not slow"` | 2 passed, 0.2 s |
| slow | `pytest tests/test_doors.py -m slow` | 2 passed, 25.0 s |

## The table

| id | mutant | fast | slow | caught |
|---|---|---|---|---|
| M1 | doors README names a script that does not exist | **caught** |, | ✅ |
| M2 | a door's script renamed on disk, README stale | **caught** |, | ✅ |
| M3 | a door *page* names a missing script; README untouched | escaped | escaped | ❌ |
| M4 | a command quoted only by a door page exits non-zero | escaped | escaped | ❌ |
| M5 | the README refute row's command exits non-zero | escaped | **caught** | ✅ |
| M6 | a README row's command replaced by one naming no script | escaped | escaped | ❌ |
| M7 | the certify door's Lean command misspelled | escaped | escaped | ❌ |
| M8 | the adopt door's pytest command names a missing test file | escaped | escaped | ❌ |
| M9 | an `interactive_lab` page loads code from another host | **caught** |, | ✅ |
| M10 | an `interactive_lab` page loses its `<title>` | **caught** |, | ✅ |

M1, M2 fail on `test_the_doors_readme_names_only_scripts_that_exist`;
M9, M10 on `test_interactive_lab_pages_are_single_file_and_script_free`;
M5 on `test_the_refute_door_command_runs`. Raw exit statuses, durations and
failing node names are in `results.json`.

The five escapes were also applied **simultaneously** to one tree. That tree,
five broken doors at once, passes the fast tier in 0.2 s and the slow tier
in 27.1 s, both green. The escape is measured, not inferred from reading the
source.

## What the numbers say

**The guard reads one file, and it is not a door page.** Its whole notion of
"a door's command" is the regex `scripts/[\w.]+\.py` applied to
`docs/doors/README.md`. Two consequences fall straight out:

* Every command quoted *inside* a door page is unguarded (M3, M4). `learn.md`
  offers `scripts/03_primes_from_zeros.py` as "the one that makes the subject
  real"; that script can be deleted, renamed, or made to exit 1 and every
  test in this file stays green.
* A README row that stops naming a `scripts/*.py` path leaves the guard's
  field of view entirely (M6, M7, M8). The `assert commands` line only checks
  that the table names *some* script, so losing one row costs nothing. The
  certify door (a Lean build) and the adopt door (a pytest invocation) are
  never checked at all, neither for existence nor for exit status.

**Existence and exit status are different checks with different reach.** Of
the five doors, existence of a `scripts/*.py` target is checked for three
(learn, refute, discover) and exit status for two (learn, refute). M5,
the ledger's own named mutant, "a command that exits non-zero", is invisible
to the fast tier and caught only by the slow tier, so a contributor running
`-m "not slow"` (the tier `AGENTS.md` recommends for a green check before
changing anything) does not detect it.

**The guard's stated intent is wider than the guard.** The ledger says it
guards against *a `docs/doors/` entry page whose quoted command no longer
runs*. What it measurably does is check the commands in the `docs/doors/`
README **table**, for existence, plus run two of them. That is a useful
guard; it is a narrower one than its sentence.

None of this is a defect report against `tests/test_doors.py`. A guard's
scope is bounded by its misses, and until now this one's misses were the
empty tuple because nobody had looked.

## Proposed ledger amendment: reported, not applied

`harness/departments/guard_ledger.py` is in the demoted half of `harness/`
(`harness/VERDICT.md`), and a hunt may not promote its own claim. The record
this measurement would support, for an operator to apply or refuse:

```
fired           True
demonstrated_by hunts/r_cb5ffe/probe.py  (5/10 against a ten-mutant battery)
scope           the commands in the docs/doors/README.md *table* that name a
                scripts/*.py path, existence for all of them, exit status for
                two (learn, refute); plus the two interactive_lab contract
                clauses. Door pages themselves are never read.
known_misses    a command quoted inside a door page rather than in the README
                  table (learn.md's scripts/03_primes_from_zeros.py is
                  entirely unguarded)
                a README row whose command names no scripts/*.py path, the
                  certify door (Lean) and the adopt door (pytest) are checked
                  neither for existence nor for exit status
                a README row deleted or emptied: only the whole table going
                  empty is detected
                a command that exists and exits non-zero, when the fast tier
                  is the tier being run
```

## Method notes and what could go wrong with them

* Every mutant is applied to a throwaway `git worktree` at HEAD and discarded;
  the working tree is never mutated. `probe.py` is runnable end to end and
  rewrites `results.json`.
* `_break_script` inserts `sys.exit(n)` after the module docstring, so a
  "command that exits non-zero" mutant fails at once rather than part-way
  through. A mutant that fails *late* would be caught by the same assertion,
  so this makes the guard's job easier, not harder.
* Cost control: the slow tier was run three times, not eleven, on the null
  control, on M5, and on the combined five-escape tree. A mutant whose fast
  verdict is "caught" needs no slow verdict, and the combined tree gives the
  five escapes their slow verdicts in one run.
* **A caching artifact worth stating.** `scripts/06_tour.py` took 118 s on
  its first run in this container and 2.0 s on every run after, in the
  worktree included: `zeta` is pip-installed editable from the main checkout,
  so a worktree shares that checkout's warm `data/` cache. No mutant here
  touches `zeta/`, so this changes no catch/escape verdict, but a timing
  measured in a hunt worktree is not independent of the main checkout, and
  anything that mutated `zeta/` in a worktree might not take effect at all.

## What was not settled

* **The discover door was not mutated.** Its command is executed by
  `tests/test_script_13_discovery_run.py`, not by this file, so a mutant would
  have measured a different guard. Whether *that* test runs the door's exact
  command (`--dry-run`) is unmeasured here.
* **Only one `interactive_lab` page exists** (`prime_genesis.html`), so M9 and
  M10 measure the contract check against a single page. Whether the loop
  would catch a second page's violation is untested, it iterates, so it
  presumably would, but "presumably" is what this hunt exists to replace.
* **No mutant was built for the `<title>`-present-but-empty case**, or for a
  page loading code via `<link rel=modulepreload>`, `<iframe>` or an inline
  `import()`. The parser only inspects `<script src=…>`, so an inline
  `import("https://…")` is a plausible further miss that was not measured.
* **The battery is a sample, not a census.** 5/10 is this battery's number.
  Ten mutants chosen by one reader of the source is not an unbiased sample of
  the ways a door can break.

## Loose threads

* **`learn.md` promotes an unguarded command.** The page calls
  `scripts/03_primes_from_zeros.py` "the one that makes the subject real",
  and nothing in the tree runs it. *Why it might matter:* it is the second
  command a new reader types, and the first one nobody checks. *First step:*
  add it to the README table, or widen `_door_script_commands()` to glob
  `docs/doors/*.md` instead of reading only the README, a one-line change
  that would have caught M3 and M4.
* **The certify and adopt doors are wholly unchecked.** *Why it might
  matter:* `docs/doors/README.md` states the cost of a purpose as "a guide
  page plus a test that the page's command still works", and two of the five
  do not pay it. *First step:* a cheap existence check on the non-script
  commands too, that `lean/lakefile` exists and the named test files exist,
  which is static and costs no runtime.
* **The fast/slow split hides the ledger's own named mutant.** M5 is exactly
  the mutant the guard record names, and `-m "not slow"` misses it. *Why it
  might matter:* the fast tier is what `AGENTS.md` tells a fresh clone to run.
  *First step:* decide whether a ~25 s exit-status check on the refute door
  belongs in the fast tier; the tour at 118 s cold plainly does not.
* **Worktrees share the main checkout's `data/` cache and editable install.**
  *Why it might matter:* any future hunt that mutates `zeta/` in a worktree
  and measures the result may be measuring the unmutated package. *First
  step:* have such a probe assert `zeta.__file__` starts with the worktree
  path before it trusts a number.
