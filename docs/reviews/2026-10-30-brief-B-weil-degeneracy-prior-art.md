# Brief B: prior-art scan for the per-place decomposition

## Goal
Find out whether the decomposition and the covering statement in Brief A are
already in the literature. This is the cheapest way to protect the claim, and it
must run before the doc is finalised.

## Questions, in priority order
1. Is the per-place split of the prime side, `cost_p = log p (Q_p - 1)` with
   `Q_p = (1 - 1/p) ||Phi_p f||^2` and `Phi_p f = sum_m p^{-m/2} f(. - m log p)`,
   standard? It is close to Weil's explicit formula, to local-factor positivity,
   and to Connes' trace-formula setting. Cite who has it and in what notation.
2. Is the covering statement known: the archimedean plus pole contribution must
   dominate the sum of local costs, with the margin decaying as more places enter?
3. Is "no uniform positive lower bound on `W`" known or folklore? The Gaussian
   computation makes it elementary, so look for a citation that says it.

## Deliverable
`docs/reviews/2026-10-30-weil-degeneracy-prior-art.md`: one to two pages, every
assertion cited with arXiv id or DOI, and an explicit verdict per question, one of
KNOWN (citation), PARTIAL (citation plus the exact gap), NOT FOUND (state every
search string and the date it was run).

Close with a short list: what Brief A must add, soften or cite.

## Tools
Undermind, the arXiv API, zbMATH Open, and Google Scholar if reachable. Quote
abstracts rather than paraphrasing from memory. Do not cite anything you have not
opened.

## Definition of done
- Three verdicts, each with evidence or with the search record.
- No claim of novelty anywhere.
- Commit on `hunt/weil-degeneracy`, push, report the path.

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
