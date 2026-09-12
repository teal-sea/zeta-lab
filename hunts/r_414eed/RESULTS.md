# Hunt r-414eed: results

**Question.** Does `scripts/make_context.py --check` catch its declared smallest
mutant, and where does its sensitivity stop?

**Answer.** It catches it, and it catches every one of the seventeen in-scope
mutants tried. The guard's ledger entry can move from `fired=None` to
`fired=True`. Its scope, previously `"undetermined until demonstrated"`, is now
mapped: **four blind regions and one narrow miss**, all listed below.

Reproduce: `python3 hunts/r_414eed/probe.py` (~50 s, standard library only,
no `.venv` and no `zeta` import needed, because the guard itself needs neither).
Raw data: `results.json`.

## Controls

Both ran, both held, and without them no row below would mean anything.

| control | what it rules out | outcome |
|---|---|---|
| the unmutated sandbox is run through the guard first | a "catch" produced by the copy rather than by the mutant | exit 0, `CONTEXT.md is up to date.` |
| after every mutant the undo is checked with a second guard run | row *n+1* inheriting row *n*'s mutation | quiet after all 24 |

The repository under test was never written to: every mutation is applied to a
throwaway copy under `/tmp`.

## The table

`diff` is how many lines of the regenerated `CONTEXT.md` move. `token` is
whether the mutant's own new name appears among them, the difference between
the guard *seeing the symbol* and the guard merely noticing that a file changed
length.

### In scope: the guard should fire

| id | mutant | fired | diff | token |
|---|---|---|---|---|
| M01 | **the ledger's declared mutant**: public function appended to `zeta/core.py`, `__all__` untouched | yes | 2 | **no** |
| M02 | public function appended to `zeta/core.py`, added to `__all__` | yes | 3 | yes |
| M03 | public function appended to `zeta/adele.py` (declares no `__all__`) | yes | 3 | yes |
| M04 | public function added to `ontology/domains/zeta_domain.py` | yes | 3 | yes |
| M05 | public class added to `harness/guards.py` | yes | 3 | yes |
| M06 | public function added to `dossier/status.py` | yes | 3 | yes |
| M07 | public function renamed in place (`xi` → `xi_renamed`) | yes | 2 | yes |
| M08 | public signature gains a keyword-only argument, in place | yes | 2 | yes |
| M09 | public docstring's *first* line changed, in place | yes | 2 | yes |
| M10 | a whole new module `zeta/mutant_module.py` | yes | 6 | yes |
| M11 | an upper-case module constant added | yes | 6 | yes |
| M12 | a new document `docs/mutant-probe.md` | yes | 1 | yes |
| M13 | a document's H1 title changed in place | yes | 2 | yes |
| M14 | a new script `scripts/99_mutant.py` | yes | 1 | yes |
| M15 | a test function added to an existing `tests/test_*.py` | yes | 4 | yes |
| M16 | `CONTEXT.md` hand-edited, tree untouched | yes | 0 | n/a |
| B08 | one blank line appended to `zeta/core.py`, no symbol at all | yes | 2 | n/a |

**17 / 17.**

### Boundary probes: where the guard is silent

| id | mutant | fired | is that right? |
|---|---|---|---|
| B01 | public function added to `meta/ledger.py` | no | scope: `meta/` is not indexed |
| B02 | public function added to `compiler/semantics.py` | no | scope: `compiler/` is not indexed |
| B03 | a document added under `docs/doors/` | no | scope: `doc_index` globs `docs/*.md`, not `docs/**/*.md` |
| B04 | a test file added as `tests/mutant_helper.py` | no | scope: `test_counts` globs `test_*.py` |
| B05 | a **private** function appended to `zeta/core.py` | **yes** | my prediction was wrong, not the guard, see below |
| B06 | private helper promoted to public **in place**, not added to `__all__` | no | **the one genuine miss** |
| B07 | public docstring changed *below* its first line | no | by design: only the first line is indexed |

## What the numbers say, in order of how much they matter

**1. The guard has power, and the ledger entry is now answerable.** The declared
smallest mutant (M01) fires. So do sixteen siblings spanning every category the
entry's `guards_against` names: added symbols, renames, new docs, new scripts,
new modules, changed signatures. Proposed amendment to
`harness/departments/guard_ledger.py` in `HANDBACK.json`; this hunt does not
apply it.

**2. M01 fires for the wrong reason, and that matters.** `CONTEXT.md` prints a
per-module line count (`*NNN lines*`), so *any* edit that changes a file's
length makes the artifact stale. B08 isolates this: appending a single blank
line, with no symbol of any kind, fires the guard. M01's token never reaches
`CONTEXT.md` at all, `module_api` filters by `__all__` when a module declares
one, and twenty-three of the `zeta/` modules do. The guard caught M01 by
accounting, not by comprehension.

**3. Hence B06, the one genuine miss.** Renaming `zeta/core.py`'s private
`_num` to `pubnum` in place adds a public symbol, changes no file's length, and
leaves the name out of `__all__`, so the regenerated `CONTEXT.md` is
byte-identical and the guard says "up to date". This is the ledger's declared
mutant with the line-count tell removed, and it slips through. It is narrow (it
needs a length-neutral edit in an `__all__`-declaring module) but it is exactly
the shape of a real promote-a-helper-to-public commit that then adds the export
in a later edit.

**4. B05 was my expectation being wrong, not a false alarm.** I predicted a
private function would be ignored; it fires, because it lengthens the file. The
guard's real invariant is not "the public API index is current" but
**"`CONTEXT.md` is a byte-exact function of the tree"**, which is strictly
broader. That is the more useful way to describe it in the ledger, and it is
why B08 belongs in the in-scope table rather than the boundary one.

**5. Four blind regions, none of them accidental-looking, none of them
documented.** `meta/` and `compiler/` are real packages with real public
functions and no presence in the index at all; `docs/doors/` is a directory the
repository's own front matter treats as first-class; `tests/*.py` that are not
`test_*.py` are invisible. Whether any of these *should* be indexed is a design
call this hunt does not make. What it can say is that the ledger's
`known_misses=()` is currently understating the scope, and now has candidates
to hold.

## What I chose, and why

**A copy of the tree rather than the tree itself.** Mutating the live checkout
would have been simpler, but a guard test that leaves the repository dirty on
an interrupt is indistinguishable from an ordinary work-in-progress edit, and
this branch is unsupervised. The sandbox also made control 2 (undo re-checked after
every mutant) cheap, which is what lets twenty-four rows share one baseline.

**Exit code *and* diff, not exit code alone.** CI only sees the exit code. Had I
recorded only that, the honest summary would have been "17/17, guard is strong",
and finding 3, the actual miss, would not exist. The extra measurement cost
one subprocess per mutant.

**Twenty-four mutants rather than one.** The brief asked for the declared
mutant. One mutant answers `fired`; it cannot answer `scope`, and `scope` is the
other field the ledger entry leaves blank.

## What I could not settle

- **Whether the four blind regions are defects or design.** `meta/`, `compiler/`,
  `docs/doors/` and non-`test_*` test files are outside the index. Whether the
  index *should* cover them is a judgment about what `CONTEXT.md` is for, and
  the answer changes what `known_misses` should say. Not mine to make.
- **Whether B06 has ever happened.** I did not search the history for a commit
  that promoted a helper to public in a length-neutral edit. Cheap to check with
  `git log -p`, and it would tell you whether the miss is theoretical.
- **The ledger amendment itself, and its test.** Recording `fired=True` would
  break `tests/test_guard_ledger.py::test_the_worklist_surfaces_the_undemonstrated_entries`,
  which asserts this guard is *still* on the worklist. That is the ledger working
  as designed, but it means the amendment is a two-file edit, both files outside
  this hunt's scope.
- **`hunts/README.md`'s case log.** `tests/test_hunt_probe_discipline.py::test_every_hunt_directory_is_covered_by_the_case_log`
  requires every `hunts/` subdirectory to be named in that file. `r_414eed` is
  not, and adding it means writing outside `hunts/r_414eed/`, which this hunt's
  scope forbids. Left undone deliberately, **that test is expected to fail on
  this branch until a one-line case-log entry is added.** Reported rather than
  worked around.
- **The rest of the suite.** No `.venv` was built: the guard, the probe and this
  question are all pure standard library, and installing mpmath/numpy/scipy to
  run tests unrelated to the guard would have spent the budget on nothing.
  `scripts/make_context.py --check` itself passes on this branch.

## Loose threads

- **`CONTEXT.md`'s line counts make the guard fire on formatting.** Adding a
  blank line, reflowing a comment, or deleting a docstring paragraph all mark the
  index stale even though the public API is unchanged. This is a cost paid on
  every commit that touches a scanned file, and it is also what masks B06.
  *Why it might matter:* a guard that fires on noise gets regenerated
  reflexively, which is the failure mode where nobody reads what changed.
  *First step:* count how many of the last hundred commits touching `zeta/`
  changed `CONTEXT.md` in the `*NNN lines*` field only.
- **`ontology/01_f1_geometry.py` … `16_*.py` are indexed as part of the
  discovery layer's API.** They are the rogue-lab prototypes that `AGENTS.md`
  describes as historical and explicitly outside the domain-agnostic seam, yet
  `DISCOVERY.glob("*.py")` sweeps them into the "Discovery layer API" section of
  `CONTEXT.md` alongside `schema.py` and `funnel.py`. *Why it might matter:* the
  index is what a fresh agent reads to learn what is live. *First step:* look at
  that section of `CONTEXT.md` and decide whether the numbered prototypes belong
  under their own heading.
- **The `--flat` path has no guard at all.** `CONTEXT_FLAT.md` is generated by
  the same script, but `--check` compares only `CONTEXT.md`, and `build_flat`
  additionally reads `AGENTS.md` and `README.md`, which the check never touches.
  `git ls-files CONTEXT_FLAT.md` is empty, so today the file is untracked and
  regenerated on demand and the exposure is nil, the thread is that nothing
  *keeps* it untracked. *Why it might matter:* the day someone commits it for a
  context-window paste, it can go arbitrarily stale under a green CI.
  *First step:* add `CONTEXT_FLAT.md` to `.gitignore` if it is not already
  covered, or give `--check` a `--flat` mode.

The three above are what I noticed and did not chase. One candidate I did check
and can rule out: the ledger's `known_misses` field is **not** generally empty,
all five records that carry an outcome populate it, so the blank on this guard
is because nobody had run a mutant, not because the field is decorative.
