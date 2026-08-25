# MISSION — support run 8ea74995, formulation arm for Erdős #126

**This is a hunt. Nothing here is a result, and nothing here bears on RH
(`docs/08`).**

## What this run is

The formulation / equivalence-audit arm of a multi-arm attempt on Erdős
Problem #126. Its bounded question:

> Derive and prove the useful equivalent formulations of #126 — the inverse
> relation between $f(n)$ and $g(k)$, uniformity over the choice of $S$, the
> graph/clique and $S$-unit formulations — and settle the exact implication
> direction of construction, composition and pruning statements. Red-team
> `hunts/r_186989/RESULTS.md`. Deliver a direction-safe target list for the
> other arms.

It is a **statement-level** arm. It does not try to bound $g(k)$ and it does
not try to build a large set.

## What it may touch

`hunts/support_8ea74995/` and its own case-log entry in `hunts/README.md`.

Nothing else. Not `zeta/`, `ontology/`, `harness/`, `lean/`, `meta/`, any
other hunt directory, or any root markdown file. Not the parent's branch.

## Standing constraints

- The reserved word belonging to `zeta/rigor.py` and the Lean arm does not
  appear in this directory, in any sentence, including a disclaiming one.
- Every claim below is labelled **proved**, **measured** or **literature**.
  A measured table is a lower bound on $g$, never an upper bound.
