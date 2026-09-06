# Hunt R-CB5FFE: what `tests/test_doors.py` actually catches

`harness/departments/guard_ledger.py` carries this record:

```
name            tests/test_doors.py
guards_against  a docs/doors/ entry page whose quoted command no longer runs,
                a front door that opens onto a wall
smallest_mutant a door page quoting a command that exits non-zero
                (e.g. a renamed script)
fired           None
scope           undetermined until demonstrated
```

`harness/guards.py` says what `fired=None` means: nobody has demonstrated
anything, and the state is kept visible instead of defaulting to trust. The
question it asks of every guard is *what exact incorrect computation is this
guard supposed to detect, and has that detection power actually been
demonstrated?*

This hunt builds the named mutant, plus the nine nearest neighbours that the
guard's own docstring implies it should or should not see, and records which
tier of the guard notices each one. The output is a power measurement and a
miss list, the two fields the ledger record is missing.

## Scope

`hunts/r_cb5ffe/` only. No mutation is ever applied to the working tree: each
one goes into a throwaway `git worktree` checked out at HEAD and is discarded.
Nothing here is evidence for or against RH (`docs/08`).

The hunt does **not** edit `harness/departments/guard_ledger.py`. Flipping a
ledger record from `None` to a measured value is a change to a demoted package
(`harness/VERDICT.md`) and is the operator's call, not the probe's; the
measurement is reported so that call can be made.

```huntspec
id: r_cb5ffe
question: Which door-breaking mutants does tests/test_doors.py detect, and which pass it?
frontier: fired=None, scope "undetermined until demonstrated", no mutant has ever been built against this guard
proposed_attack: build ten mutants spanning the guard's three stated checks and its unstated gaps, run both tiers against each in an isolated worktree, and report the catch/escape table
dead_routes:
  - trusting the guard because it exists, harness/guards.py records three guards that failed exactly that way
required_oracles:
  - the pytest process exit status of tests/test_doors.py on the mutated worktree
  - the exit status of the door scripts themselves, run directly
kill_conditions:
  - the null control (unmutated worktree) fails either tier, which would make every catch unattributable
  - a mutant cannot be built without editing outside hunts/r_cb5ffe/ or the throwaway worktree
  - the slow tier cannot be run inside budget, in which case only fast-tier verdicts are reported and said to be partial
agents_may:
  - build mutants and run them in a throwaway worktree
  - record catch and escape outcomes as data
  - report a proposed ledger amendment
agents_may_not:
  - edit tests/test_doors.py, docs/doors/, interactive_lab/ or scripts/ in the working tree
  - write the measured value into harness/departments/guard_ledger.py
  - describe an escape as a defect in the guard rather than a bound on its scope
```

## The ten mutants

| id | mutant | family |
|---|---|---|
| M1 | the doors README names a script that does not exist | README command unrunnable |
| M2 | a door's script is renamed on disk, README left pointing at the old name | README command unrunnable |
| M3 | a door *page* names a missing script; README untouched | door-page command unrunnable |
| M4 | a command quoted only by a door page exits non-zero | door-page command unrunnable |
| M5 | the command quoted by the README refute row exits non-zero | README command unrunnable |
| M6 | a README row's command is replaced by one naming no script at all | README command unrunnable |
| M7 | the certify door's Lean command is misspelled | README command unrunnable |
| M8 | the adopt door's pytest command names a missing test file | README command unrunnable |
| M9 | an `interactive_lab` page loads code from another host | interactive_lab contract |
| M10 | an `interactive_lab` page loses its `<title>` | interactive_lab contract |

M4 and M5 are the ledger's named mutant, split by *where the command is
quoted*: M5 in the README table the guard reads, M4 in a door page it does not.

## Files

- `probe.py`: the mutation harness, runnable end to end
- `results.json`: every run's exit status, duration and failing node
- `RESULTS.md`: the table, the reading, and what was not settled
