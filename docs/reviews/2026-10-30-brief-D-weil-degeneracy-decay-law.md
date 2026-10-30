# Brief D: is the covering margin's decay law universal?

## Goal
The three existing studies all show the covering margin going to zero. Nobody has
checked whether it does so at the same rate in two unrelated families. If the
exponent is universal, that is a candidate statement about the shape of any proof.
If it is family-specific, the lead is weaker and should be recorded as such.

## What exists
`hunts/weil_split/RESULTS.md` gives, for rectangles `b = 2, 3, 4.5, 6, 8`:
margin `cover - 1 = 3.04e-2, 6.44e-3, 1.50e-3, 7.91e-4, 1.59e-4`, roughly
`b^-2.5`. That is one family and three points would be enough to fit anything.

## Deliverable
A new hunt `hunts/decay_law/` with `MISSION.md` carrying a `huntspec` block (copy
the shape from any hunt added in PR #371 or from `hunts/HUNTSPEC.md`), `split.py`-style
module, `RESULTS.md`, and `results.json`.

Measure the same margin for a second family with an independent shape, for
example a triangular or a smooth compact bump, at six or more widths. Then:
- fit the exponent in each family and give the fit residual;
- state whether the two exponents agree within the residual;
- state explicitly what would kill the "universal" reading.

## Constraints
- Every number from the arithmetic side must be checked against the zero side,
  and where they disagree the covering ratio must be taken from the zero side.
- Keep the reserved vocabulary out of `hunts/`.
- Add a case-log entry to `hunts/README.md` with the next free number (check the
  file, #156 is the current maximum).

## Definition of done
- `pytest tests/test_hunt_probe_discipline.py tests/test_huntspec.py tests/test_hunt_numbering.py`
  passes with `-o addopts=""`.
- RESULTS states the two exponents, the residual, and the kill condition.
- Commit on a new branch `hunt/decay-law`, push, open a PR, report the link.

## Shared context (read first)

Repository: the repo root, remote `github.com/teal-sea/zeta-lab`, branch
`hunt/weil-degeneracy`, PR #371. Everything you need is on that branch.

Run Python as `cd the repo root && env -u PYTHONPATH .venv/bin/python`.
A `PYTHONPATH` inherited from the Hermes venv shadows the repo `.venv` and numpy
fails to import. pytest needs `-o addopts=""` because pytest-xdist is absent:

    env -u PYTHONPATH .venv/bin/python -m pytest -q -o addopts="" <files>

House rules that will fail CI if broken:
- No em dashes in prose. Use a period, a colon or a pair of commas.
- One word is reserved for `zeta/rigor.py` and is banned outright in
  any file under `hunts/` (see `docs/17`). Do not reintroduce that word there, even in a disclaimer.
- Nothing under `hunts/` is a result. A hunt measures; it does not claim.
- Composite claims take the grade of their weakest step.
- Derive conventions numerically, never from memory.
- Do not modify `zeta/`, `ontology/`, `harness/` without explicit permission.
