# Erdos problem scan: where this laboratory's built machinery has an edge

Sub-study of `hunts/rogue_frontier/`. Opened 2026-08-18.

**Status: exploratory. Nothing here is a result.** This is a feasibility survey,
not mathematics. Every "best known" line below carries the URL actually fetched
while writing it; anything not fetched is marked UNVERIFIED.

## Question

Of the ~1100 problems on erdosproblems.com, which OPEN ones does this tree's
existing, validated machinery make unusually cheap to attack, such that a first
signal is reachable in hours rather than months?

The bar is deliberately not "interesting problem". It is: *this specific tooling
changes what is feasible here.*

## Method (reproducible)

1. `https://raw.githubusercontent.com/teorth/erdosproblems/main/data/problems.yaml`
   gives structured status/prize/tags for 1217 problems (604 `open`, plus the
   finite-computation classes below). Fetched 2026-08-18.
2. All 1217 problem pages fetched from `https://www.erdosproblems.com/<n>`
   (a plain user agent is required; the default agent gets 403), rendered to
   text, split into statement and remarks.
3. The site carries a status field that is exactly the discriminator this scan
   wants, and it is not visible from the YAML alone:
   - `open` (604): "cannot be resolved with a finite computation"
   - `falsifiable` (27): "could be disproved with a finite counterexample"
   - `verifiable` (7): "could be proved with a finite example"
   - `decidable` (9): "resolved up to a finite check"
   - plus `not provable` / `not disprovable` / `independent` (set-theoretic)
4. Page metadata also gives a **mining indicator** the YAML lacks: comment
   count, who has flagged "currently working on this problem", and the
   "looks tractable" / "looks difficult" votes. Recorded per candidate below.
5. Pool restricted to number-theory / analysis / combinatorics tags where this
   tree's tools could bite: 437 open-ish problems. Statements read in full.

## What this laboratory actually brings

| Tool | Where | What it buys |
|---|---|---|
| exact rational / integer engines, generating-function collapse | `hunts/rogue_frontier/fkappa/` | 14-fold combinatorial sums in polynomial time, validated exactly to i=81 |
| exact finite-N lattice counts, Wick/pairing enumeration | `hunts/rogue_frontier/sine_gram/` | exact finite-N combinatorial objects, no floating point |
| ball / interval arithmetic (Arb via python-flint) | `zeta/rigor.py` | rigorous enclosures, proven signs, safe failure |
| high-precision mpmath, sympy, scipy | repo-wide | thousands of digits, symbolic reduction, constrained optimisation |
| exact Sturm sequences in Q[X] | `zeta/li.py` | exact real-root counting without floating point |
| Lean 4 + Mathlib, pinned and building | `lean/` | kernel-checked finite lemmas; Mertens I/II and Hardy-Ramanujan already in tree |
| large exact prime / arithmetic-function computation | repo-wide | sieves to 1e7+ demonstrated, segmented sieving routine |
| structure-matched negative controls | `zeta/epstein.py`, `hunts/README.md` | a claim a matched rival also satisfies has distinguished nothing |

## Scoring

Each candidate carries: **F** feasibility of a first signal in hours (0-5),
**N** chance anything new comes out (probability, honest), **M** how heavily
mined (0 = untouched, 5 = crowded), **V** value if it lands.

---
