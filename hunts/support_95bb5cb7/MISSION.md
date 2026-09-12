# MISSION: Erdős #126, the size-dichotomy arm (support run 95bb5cb7)

**This is a hunt. Nothing in `hunts/` is a result, and nothing here is
evidence for or against RH (`docs/08`).**

A support run launched by a parent session working `hunts/r_186989`, to answer
one bounded question independently and hand the answer back.

## The bounded question

Let $S$ be $k$ primes and $A$ a set of distinct positive integers with every
off-diagonal sum $a+b$ $S$-smooth; $g(k) = \max|A|$; the target is
$\log g(k) = o(k)$.

Seek a clean size dichotomy: either $A$ is spread out enough that a
descent/large-gap argument applies, or $A$ lies in a controlled interval where
smooth-number counts apply. Optimise uniformly over $S$ and the scale of $A$.
Return an explicit bound, or the exact normalisation/height barrier. Audit
`hunts/r_186989/RESULTS.md` on the way.

## Scope

May write: this directory and one case-log entry in `hunts/README.md`.
May not write: any other hunt, `zeta/`, `harness/`, `lean/`, `meta/`, or any
root markdown file.

## What it measures

`probe.py`, stdlib only, ~20 s:

1. re-verification from scratch of every witness in `r_186989/RESULTS.md` §3;
2. exhaustive enumeration of primitive admissible 3-, 4- and 5-element sets
   through their **sums** (not their elements), across growing cutoffs, to see
   whether any height bound exists after normalisation;
3. a rigorous two-sided sandwich (Rankin upper, simplex-volume lower) on
   $\log\Psi(N,S)/k$ as a function of $\log N/\log\mathrm{rad}(S)$, which is
   the counting horn's threshold.

```huntspec
id: support_95bb5cb7
question: Does a size dichotomy (large-gap descent vs smooth-number counting in a controlled interval) yield log g(k) = o(k) for Erdos 126, and if not, where exactly does it fail?
frontier: f(n) >> log n classical, unimproved since 1934; equivalently g(k) <= exp(O(k)). No upper bound on g(k) is established anywhere in this tree.
dead_routes:
  - element-bounded clique search: reports one witness per k and licenses false claims about all optimal witnesses (Hunt #91, corrected here)
  - a multiplicative composition law for g: it would refute the conjecture, not prove it (Hunt #91 section 4)
required_oracles:
  - full trial division of every off-diagonal sum, recomputed from scratch, never reusing the search predicate
  - Rankin's inequality for Psi(x,S), valid for every sigma > 0
  - simplex lattice-point volume as an unconditional lower bound on Psi
kill_conditions:
  - the counting horn's threshold turns out to depend on the choice of S or the scale, so no uniform statement exists
  - primitive admissible sets of sub-extremal size turn out to have bounded height, which would revive the descent horn
  - the two horns are found to overlap, which would settle the arm positive
agents_may:
  - write hunts/support_95bb5cb7/ and one case-log entry in hunts/README.md
  - report corrections to sibling hunts without editing them
agents_may_not:
  - write any other hunts/ directory, zeta/, ontology/, harness/, lean/, meta/, or any root markdown file
  - claim any upper bound on g(k), or any bearing on RH
  - use the reserved word belonging to zeta/rigor.py and the Lean arm
```
