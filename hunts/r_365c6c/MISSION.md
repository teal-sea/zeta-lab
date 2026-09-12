# Hunt R-365C6C: file-type boundary of the hunt reserved-word guard

## The question

`tests/test_hunt_probe_discipline.py::test_no_hunt_claims_the_reserved_word`
is the lexical guard that scans `hunts/` to ensure probe files do not claim
the certainty regime reserved for `zeta/rigor.py` and the Lean arm.

The attention queue identified the following known miss:

> guard 'tests/test_hunt_probe_discipline.py::test_no_hunt_claims_the_reserved_word' does not detect: file types outside .py/.md/.json (a .txt overclaim passes)

This hunt measures:
1. The exact file extension breakdown across `hunts/` in the repository today.
2. The empirical detection boundary of the unmodified guard against a battery of 40 file formats across 12 distinct categories.
3. Whether unscanned files under `hunts/` currently contain the reserved word or related morphology.

## Scope

Writes only inside `hunts/r_365c6c/`, `hunts/README.md` (for Hunt #51 case-log entry), `harness/departments/guard_ledger.py` (closing the loop), and telemetry.
Runs the real guard source unmodified against a sandbox repository root in an isolated temporary directory.
Nothing here is mathematics and nothing here is evidence for or against RH.

```huntspec
id: r_365c6c
question: Does test_no_hunt_claims_the_reserved_word detect file types outside .py/.md/.json?
frontier: the guard filters on path.suffix.lower() in {'.py', '.md', '.json'}; 76 of 447 files under hunts/ are currently outside that set
proposed_attack: run the unmodified guard source in an isolated sandbox repository root against a battery of 40 file specimens spanning scanned formats, plain text, structured config, scripts, code, markup, extensionless files, compound extensions, dotfiles, and binary formats
dead_routes:
  - inspecting the guard source without executing it against planted specimens
  - mutating the live repository tree during testing
required_oracles:
  - pytest executing the unmodified guard source test_no_hunt_claims_the_reserved_word in a sandbox repository root
  - exhaustive enumeration of file paths and extensions across hunts/
kill_conditions:
  - the sandbox baseline with an empty specimen fails pytest, indicating sandbox contamination
  - positive control files (.py, .md, .json) fail to trip the guard
  - clean control files trip the guard
agents_may:
  - read any file in the repository
  - run the test suite
  - execute the guard against an isolated sandbox repository root
  - measure and record detection outcomes across all file types
agents_may_not:
  - touch hunts/frontier_math/, meta/, lean/, or any root markdown file
  - use the reserved word in probe files or hunt artifacts
  - modify the guard logic in tests/ without authorization
```
