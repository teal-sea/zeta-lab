# R-F00E48: salvage four research arms from an unlanded branch

`claude/riemann-hypothesis-research-ofds8s` ran a wide-portfolio RH-adjacent
campaign on 2026-08-17/18 and never landed. The salvage sweep of 2026-08-18
found five arms on it, four of which exist nowhere on `main`. This hunt lands
those four, holds the fifth back, and checks that what landed is intact and
says true things about the tree it landed in.

The fifth arm, `fkappa/`, is held back because its corrected kappa = 2 table
contradicts `main`'s landed `hunts/higher_xi/` table from i = 2 onward, with a
conflicting diagnosis of the cause. That dispute was adjudicated separately by
Hunt #65 (`hunts/r_2ac05f/`), which found `higher_xi` right and derived
`C_{kappa,2} = -4*kappa`; `docs/31` carries the resulting erratum. Landing the
losing table now would put two mutually inconsistent tables in one tree.

```huntspec
id: r_f00e48
question: Do the four unlanded rogue_frontier arms land intact on main, and does what they claim about themselves survive being checked in the tree they land in?
frontier: not a mathematical frontier; the frontier here is the repository's own record, and the claim under test is that a cherry-pick preserved it
proposed_attack: land the four named arms and nothing else, then check inventory against the source tree, the lexical gate, every path and symbol the reproduction page names, the promoted rational recomputed from the landed code, and every JSON gate the landed documents quote
dead_routes:
  - landing fkappa/ (an adjudication, already decided against it by hunts/r_2ac05f/, not a merge)
  - landing the campaign ledgers (three of them summarise the unlanded arm in their own voice)
  - landing erdos_scan/ or matchings/ (added to the branch after the sweep that specified this landing; unreviewed)
required_oracles:
  - the source branch tree itself, read with git ls-tree, as the inventory reference
  - exact rational arithmetic, recomputing the promoted constant from the landed source
  - the landed JSON checkpoints, read against the definitions their own documents give rather than against guessed key names
  - hunts/r_ac9ca3/ on main, which reached the same (c, N) = (31, 60) cell independently
kill_conditions:
  - any landed arm is missing a file the source branch carries
  - the reserved word appears anywhere under the landed subtree
  - a path or symbol REPRODUCE.md names does not resolve
  - the promoted rational recomputed from landed code differs from the landed document
  - the salvaged Weil arm contradicts the landed hunt that reached the same cell
agents_may:
  - read the source branch
  - land the named subset
  - correct broken references in the material being landed
  - record the landing and its exclusions
agents_may_not:
  - adjudicate the kappa = 2 dispute
  - land the excluded arm or the campaign ledgers
  - promote any salvaged claim beyond the rung its own arm gave it
  - describe re-running an arm's own code as an independent check of it
```

## Scope

May write: `hunts/r_f00e48/**`, `hunts/rogue_frontier/**` (the landing itself),
one case-log entry in `hunts/README.md`, and an append to
`harness/departments/review_ledger.py`. May not touch `zeta/`, `ontology/`,
`meta/`, `lean/`, other hunts, or any root markdown file.

## Standing

Nothing here is evidence for or against RH (`docs/08`). A salvage moves
records; it does not raise anything on the certainty ladder.
