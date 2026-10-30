# Brief A: reader-facing page for the degeneracy result

## Goal
Turn three exploratory hunts into one citable `docs/` page, so the finding stops
being three `hunts/` directories that the repo itself says do not count.

## Deliverable
1. `docs/48-weil-degeneracy.md`. Number 48 is the next free number (47 exists).
   Every bare `docs/NN` reference you write must resolve to a real file.
2. Regenerate `CONTEXT.md` with `env -u PYTHONPATH .venv/bin/python scripts/make_context.py`.
3. Commit on `hunt/weil-degeneracy` and push, so it lands in PR #371.

## Source material (do not invent numbers)
- `hunts/arch_cover/RESULTS.md`: the three pieces, the depth law
  `depth = a*gamma_1^2/ln 10` with measured/predicted pairs 4.34/4.34, 17.38/17.36,
  39.1/39.07; the 33-digit floor set by the `n_max = 2e6` prime truncation cap.
- `hunts/weil_gram/RESULTS.md`: `lambda_min` 2.404e-3, 3.574e-7, 2.223e-7,
  2.649e-13, 5.029e-22 for k=2..6; the `plus2` row that must stay unresolved.
- `hunts/weil_split/RESULTS.md`: the exact per-place identity to 1e-16, the cost
  table, top-three share 0.977 down to 0.126, margin 3.04e-2 down to 1.59e-4.

## Content requirement
- The object in plain terms first (`W(h) = pole + arch + prime`, and the zero side
  is a sum of non-negative terms so all cancellation is on the arithmetic side).
- The three measurements, each with its numbers and its grade.
- The consequence, stated as a constraint on proof strategy: there is no uniform
  positive lower bound, so a proof must be an identity or a decomposition whose
  constant degenerates with the test function.
- A scope section carrying every defect already recorded: eigenvalues not
  enclosed, the `plus2` row unresolved, the three-digit quadrature in
  `weil_split`, one-parameter families only, no human review.
- A line saying no prior-art search has been run yet, until Brief B returns.

## Definition of done
- `pytest tests/test_docs_numbering.py tests/test_doors.py` passes, and
  `scripts/make_context.py --check` passes.
- No em dashes; no new claim anywhere; the page never says a hunt is a result.
- Push to the PR branch and report the commit hash and the doc path.

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
