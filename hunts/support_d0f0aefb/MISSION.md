# MISSION: support run `d0f0aefb`, graph/Ramsey arm of Erdős #126

**A hunt, not a department and not a result.** Nothing here is evidence for or
against RH (`docs/08`).

## What this is

A bounded support run launched from `fulcrum` by the run working
`hunts/r_186989` (Erdős #126 scout). One question, assigned:

> For each $p \in S$, analyse the graph or ultrametric relation induced by
> $p \mid a_i + a_j$ and by its exact valuation. The union covers all edges of
> $K_n$. Seek a structural cover, Ramsey, rank or container bound exploiting
> that these are not arbitrary graphs. Prove a sharper cover theorem or exhibit
> a realizable obstruction showing why generic graph methods stall.

Audit `hunts/r_186989/RESULTS.md` rather than trusting it.

## What it may touch

`hunts/support_d0f0aefb/` and one case-log entry in `hunts/README.md`. Nothing
else: not `zeta/`, `harness/`, `lean/`, `meta/`, any other hunt directory, or
any root markdown file.

## Standing constraints

* `probe.py` is stdlib only, runs in seconds, and writes `results.json`.
* Finite data is not a proof and is labelled *measured*; proofs are written out
  and labelled *proved*.
* The reserved word belongs to `zeta/rigor.py` and the Lean arm, and is not
  used here.
* Implication directions are stated explicitly, because the parent hunt already
  found one arm whose lemma pointed the opposite way from the one briefed.
