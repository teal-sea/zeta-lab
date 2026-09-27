# PROGRESS: theory worker, hunt oob_envelope

Branch `teal-sea/oob-cert-theory`. Writes only in `hunts/oob_envelope/theory/`.
Brief: `theory/BRIEF.md`. Output: `theory/RESULTS.md`.

## Log

- 2026-09-27: started. Read MISSION.md, AGENTS.md, BRIEF.md, method skill,
  seed probes. Fetched arXiv:2608.24827v2 LaTeX source (scratchpad, not in repo).
- Task 1 written (RESULTS.md §1): Lemma 1 for complex f and H = μ̂ with μ
  carried by |λ| ≥ 2L (boundary via a null overlap), Theorem 1′, line-by-line
  table. Four changed places: sup|Ψ+H−β*| constant, H inside [0,T#] in the
  assembly, Bernstein-ellipse constant (cosh(0.4·70) ≈ 8e11 at D=64), and an
  incidental missing length factor in Zhu's §4 row bound. Main caveat: T# now
  sits near the resolution height T* ≈ 31 at L = 0.8 (Zhu used 200).
- Measured side checks for task 2 (float64, one route): at L = 0.6 the window
  graph splits into paths of 1, 2, 4 vertices, λ_max = 0.9009276 (4-path,
  exact formula) vs Galerkin 0.90077 at M = 800. At L = 0.8 three component
  types (4, 7, 12 vertices), λ_max = 1.2191380 (12-type) vs Galerkin 1.21863.
  A 13-vertex "type" seen once was a float-merge artifact (two copies of one
  point 3e-17 apart). Components percolate once 5 enters the comb (L > 0.805):
  at L = 0.85 90% of samples exceed 3000 vertices, at L ≥ 0.9 all do.

## Task status

| # | task | status |
|---|---|---|
| 1 | out-of-band lemma + modified Theorem 1.1 | done (RESULTS §1) |
| 2 | weak / strong duality for the optimal constant | in progress |
| 3 | asymptotics of S*_L | not started |
| 4 | prior art and the current record | not started |
| 5 | Liu's obstruction vs the out-of-band route | not started |
