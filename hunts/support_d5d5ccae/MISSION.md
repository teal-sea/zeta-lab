# MISSION: Erdős #126, the S-unit arm (support run `d5d5ccae`)

**This is a hunt. Nothing in `hunts/` is a result, and nothing here is
evidence for or against RH (`docs/08`).**

## The question, as briefed

A support run launched by run `0897a5a7` and answering to it. Arm label
`sunit-equations`. The bounded question, verbatim in substance:

> Fix a few base elements and derive exact S-unit equations or cross-ratio
> identities constraining every other element. Apply the strongest quantitative
> theorems on unit equations or the Subspace Theorem and calculate the
> dependence on `k` honestly. Look for injectivity that turns bounds on
> solutions into bounds on `|A|`. Deliver either a general improved bound on
> `g(k)`, one concrete missing injectivity lemma, or a proof that standard
> S-unit bounds are quantitatively too weak.

Common objective: `S` is a set of `k` primes, `A` a finite set of distinct
positive integers with every off-diagonal sum `a+b` supported on `S`, and
`g(k) = max |A|`. Erdős #126 asks for `log g(k) = o(k)`. Sources:
<https://www.erdosproblems.com/126>,
<https://combinatorica.hu/~p_erdos/1934-03.pdf>. The prior scout
`hunts/r_186989/` was read and audited rather than trusted; its witnesses were
re-verified from scratch here.

## Scope

Writes only `hunts/support_d5d5ccae/` plus one case-log entry in
`hunts/README.md`. No ledger under `harness/departments/` is touched.

```huntspec
id: support_d5d5ccae
question: Does the two-variable S-unit equation route, with injectivity from fixed base elements, produce a bound on g(k) better than the classical 2^k, or is it provably too weak?
frontier: Erdos-Turan 1934 gives g(k) < 3*2^(k-1) and Erdos-Suranyi g(k) <= 2^k; nothing better in 92 years. The conjecture log g(k) = o(k) is open.
proposed_attack: fix two base elements a > b of A, observe that x -> (a+x, b+x) injects A minus the base pair into the solutions of U - W = a-b in positive S-smooth U, W, then charge the strongest applicable unit-equation solution-count theorem and compare the resulting exponential base against 2
dead_routes:
  - three or more fixed base elements: the linear identity (b-c)(a+x) + (c-a)(b+x) + (a-b)(c+x) = 0 is a consequence of the two-element statement and its coefficients are differences of elements of A, which are not S-smooth, forcing the more expensive rank-based bounds
  - cross-ratios of four elements: the differences (a+b)(c+d) - (a+c)(b+d) = (a-d)(c-b) reintroduce the same non-S coefficient primes
  - rank-based bounds (Beukers-Schlickewei) for the two-element equation: rank 2k+1 gives 2^(16k+16), worse than Evertse's S-based 3*7^(2k+3)
required_oracles:
  - exact enumeration of S-smooth integers inside a stated box, with pair counts computed by set membership
  - Lehmer's published Stormer counts of consecutive S-smooth pairs as an external reference for the d = 1 column
  - independent re-verification of every inherited witness by full trial-division prime support
kill_conditions:
  - the strongest applicable theorem yields an exponential base above 2, so no improvement on the classical bound is possible from it
  - the injectivity map fails to be injective or fails to land in the solution set
  - the measured solution counts are reproduced only inside a box and cannot be turned into an upper bound
agents_may:
  - search
  - derive
  - code
  - attack
agents_may_not:
  - declare novelty
  - declare theorem status
  - promote their own claim
  - present a box-truncated count as an upper bound on g(k)
```
