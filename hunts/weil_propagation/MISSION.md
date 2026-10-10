# MISSION: Weil positivity propagation across window size

Opened 2026-09-23 on branch `teal-sea/weil-propagation`, which merges
`teal-sea/rh-strategy-council-sep17` (the Davenport-Heilbronn negativity
result at (c, N) = (31, 60)) onto `origin/main`.

## The question

RH is equivalent to nonnegativity of the Weil quadratic form on every
compact window. Positivity is established on small windows: classically
for support log 2 (Yoshida; Connes-Consani), and by a computer-checked
argument for support 1.6 (arXiv:2608.24827). The positive margin decays
doubly exponentially in the window length L, so no window-by-window
certificate can reach RH.

This hunt asks for a **propagation mechanism**: a statement of the form

    positivity on window L  +  the Euler product  =>  positivity on window L + delta

or any structural relation between the ground states at L and L + delta that
could carry positivity forward uniformly.

## The kill-control

Davenport-Heilbronn (DH) shares the functional equation and gamma factor
class of an L-function but has no Euler product, and its truncated Weil form
turns negative at c = 31 (`hunts/rogue_frontier/weil_trunc/RESULTS.md` s8,
`THEOREM_FEASIBILITY.md`). Any candidate mechanism that does not use the
Euler product must also hold for DH, and is therefore refuted. Every
candidate is tested against DH between c = 30 and c = 31 before it is
developed further.

## Workers and ownership

- `numerics/`: measurement of ground-state transport between windows, for
  zeta and DH. Branch `teal-sea/weil-propagation`.
- `theory/`: literature and candidate lemmas. Branch
  `teal-sea/weil-propagation-theory`.

Each worker writes only in its own subdirectory. Other hunts are read-only
inputs.

## Rules

- No claim about RH. A candidate lemma is a candidate until proved, and the
  certainty ladder in `AGENTS.md` governs every statement.
- Nothing heavy on the laptop. Local runs stay under 10 minutes and a few GB.
  Anything larger goes to GitHub Actions with an estimate in `RUNS.md` first.
- No `lake build` locally.
- No publication, deployment, or edits outside `hunts/weil_propagation/`.
- The reserved word banned under `hunts/` stays banned
  (`tests/test_hunt_probe_discipline.py`).

## Kill conditions

- A candidate mechanism holds for DH across c = 30 -> 31: refuted.
- A candidate reduces to a restatement of RH with no new estimate: record it
  as a reformulation, not progress.
- A claimed transport relation fails an independent precision or basis-size
  check: measurement artifact.
