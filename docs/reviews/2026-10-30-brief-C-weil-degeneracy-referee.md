# Brief C: independent referee for the one exact identity

## Goal
Recompute, by a route you design yourself, the only number in PR #371 that is more
than a measurement:

    sum_p cost_p = -prime_term,      to 1e-16, at b = 3 and b = 6

## The object (specification, not code)
`f = b^{-1/2} * 1_{[-b/2, b/2]}`, so `||f||^2 = 1`, `g = f * f` is the triangle
of half width `b`, and `h` is the transform of `g`, `h(r) = (2/b)(1 - cos(br))/r^2`.
`cost_p = log p (Q_p - 1)`, `Q_p = (1 - 1/p) ||Phi_p f||^2`,
`Phi_p f = sum_{m>=0} p^{-m/2} f(. - m log p)`.

## Independence rules
- Do NOT read `hunts/weil_split/split.py`. That is the implementation under test.
- Compute `||Phi_p f||^2` by your own route: numerical quadrature over the
  overlapping intervals, or exact interval arithmetic on the same rectangles.
- Compute the prime side by your own route: `-2 sum_n Lambda(n) n^{-1/2} g(log n)`
  with your own sieve and your own `Lambda`, not by calling the hunt's module.
  You may call `zeta.weil.explicit_formula_sides` afterwards only to compare.
- Report agreement to more digits than 1e-16 if you can, and say where your own
  rounding binds.

## Deliverable
`hunts/weil_split/REFEREE.md`: a five-line verdict (agree or disagree, at what
magnitude, for which `b`), the route in one paragraph, the numbers, and anything
you found suspicious in the specification itself.

## Definition of done
- Two values of `b`, both sides computed twice by different means if cheap.
- If you disagree, say by how much and on which place, and do not adjust the
  specification to make it match.
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
