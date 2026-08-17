# MISSION `r_401bbf`: the k=2 table with `zone_trade`'s inner prune disabled

## The question

`hunts/frontier_math/k2_closure.py::zone_trade` maximises, over integer zone
multiplicities with `sum m <= 10`, the adversary's zone trade

    V(m) = sum_i cap_i*m_i - sum_i q_ii*m_i*(m_i-1) - 2*sum_{j<i} q_ji*m_j*m_i

by depth-first search. One of its two cuts is the line

    if v > val - 1e-18 or m == 0:

which refuses to descend into a multiplicity that does not immediately improve
the running value. That cut restricts the **adversary's** search, and a cut on
the adversary's side is the **unsound direction**: wherever it bites, the trade
comes out too small, the cell's deficit is understated, and the published
margin is optimistic.

Run `78b4ce8e` (`hunts/r_a97060/`, the enclosure pass) recorded the assumption
in its §4 as unstated and load-bearing, with a measured delta of 0.0, but on
six binding cells only, not on the 6600 the table publishes.

**This hunt settles it on every cell.** It does not extend the result, does not
touch `k >= 3`, and does not touch the unequal-depth quantifier.

## What "disabled" was taken to mean, and why it was widened

The brief says: re-run with the inner prune disabled. Merely deleting that line
would leave the other cut in place:

    if val + rem * caps[idx] <= best: return

an ordinary branch-and-bound bound whose admissibility rests on the *same*
hypothesis the inner prune needs (nonnegative pair charges, so that no
completion can gain more than `rem` copies of the largest remaining cap). Since
the surviving components in this table are small (at most eight zones with a
nonzero cap in any connected component of the whole 6600-cell table, six in the
signed mode), the honest instrument is to drop **both** cuts and enumerate
every one of the `C(Z+10, Z) <= 43758` admissible multiplicity vectors, taking
the exact maximum.
That is a strict superset of what the inner-prune-free search explores, so a
zero delta against it settles the brief's question a fortiori, and it settles
the outer bound at the same cost.

Both trades are evaluated on the **same** zone data, cell by cell, so each
cell's delta is an exact difference and not a comparison of two independently
scanned tables.

## Scope

**May write**: `hunts/r_401bbf/`; and, by the operator addendum of 2026-08-17
which overrides the generic "do not touch `hunts/frontier_math/`" line for this
run only, `hunts/frontier_math/k2_closure.py`, its tests, and
`K2-TWO-SPECIES.md`; plus the case-log entry in `hunts/README.md`.

**May not write**: `zeta/`, `ontology/`, `harness/`, `meta/`, `lean/`, any root
markdown file, `hunts/frontier_math/zeta23ext/` (a concurrent run owns it).

**Standing**: nothing here is evidence for or against RH (`docs/08`). The
reserved word of `zeta/rigor.py` and the Lean arm does not appear in this
directory, disclaimers included. The lexical guard reads the bytes.

```huntspec
id: r_401bbf
question: Does the inner prune in k2_closure.zone_trade ever understate the adversary's zone trade on any of the 6600 published k=2 tau-cells?
frontier: measured delta 0.0 on six binding cells (run 78b4ce8e, hunts/r_a97060 section 4); unchecked on the other 6594
proposed_attack: solve every cell's zone trade twice on identical zone data, once with the published search and once by exhaustive enumeration of all multiplicity vectors with sum m <= 10, and report the per-cell delta
dead_routes:
  - sampling binding cells only, which is what left the assumption open
  - re-tuning zones or widening a cap to rescue a cell, forbidden by the brief
required_oracles:
  - exhaustive integer enumeration of the multiplicity lattice
  - the published table's own recorded numbers as a reproduction check
  - a planted instance with a negative pair charge, on which the prune must be seen to bite
kill_conditions:
  - the exhaustive solver ever returns less than the pruned search on a real component
  - the transcription of the published search disagrees with the published search
  - the planted prune-biting instance is not detected, leaving a zero delta meaningless
agents_may:
  - search
  - derive
  - code
  - attack
agents_may_not:
  - declare novelty
  - declare theorem status
  - promote their own claim
  - re-tune the table
```

```runmanifest
id: r_401bbf-2026-08-17-2b9b08aa
hunt: r_401bbf
started: 2026-08-17T21:50Z
finished: 2026-08-17T22:45Z
ran:
  - python hunts/r_401bbf/probe.py --quick --charges
  - python hunts/r_401bbf/probe.py --charges
outcome: the inner prune never bites on any of the 13200 cell evaluations, and it is sound by argument because every pair charge in this table is a square over 200
artifacts:
  - hunts/r_401bbf/results.json
  - hunts/r_401bbf/RESULTS.md
```
