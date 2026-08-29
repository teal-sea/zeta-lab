# The pairing count: a blocker in this tree, borrowed from combinatorics

**Opened 2026-08-18.** A scope extension of `rogue_frontier`, recorded here
rather than assumed: the campaign's HuntSpec question is about the
RH-adjacent frontier, and this sub-study is not about zeta at all. It is
here because the campaign went looking for a place where this tree's own
active work is blocked on something finite, and found one.

## The blocker

`hunts/r_8c3b94/RESULTS.md` (Hunt #48, 2026-08-18) prices a Lean proof of
Erdos-Kac. Its step A2c reads:

> a partition into `r` blocks all of size `>= 2` contributes `~lambda^r`,
> maximised at `r = k/2` by the perfect matchings, of which there are
> `(k-1)!!`. **Includes proving that count, which Mathlib does not have.**

That count is not number theory. It is the statement that a set of size
`2m` has `(2m-1)!!` partitions into blocks of size two, equivalently that
many fixed-point-free involutions. It is also the Wick / Isserlis pairing
count, which is why it recurs far outside Erdos-Kac, including inside this
campaign's own `sine_gram` moment engine, which enumerates exactly these
objects to compute `m_k`.

## The gap, checked rather than remembered

In the pinned Mathlib (`lean/lake-manifest.json`, toolchain
`v4.33.0-rc2`):

- `Nat.doubleFactorial` **exists**, with usable arithmetic:
  `doubleFactorial_two_mul : (2*n)‼ = 2^n * n !`,
  `factorial_eq_mul_doubleFactorial`, `doubleFactorial_add_two`.
- `SimpleGraph.Subgraph.IsPerfectMatching` **exists as a predicate**, and
  the only cardinality lemma attached to it is `even_card`. There is no
  counting API.
- `Isserlis` and `Wick` appear nowhere in Mathlib.

So the object has a name and the arithmetic exists; the bridge between
them does not.

## What this sub-study does

Proves the count in Lean 4 with zero sorrys, against an independent
enumeration oracle (`oracle.py`, three routes: brute force over
permutations, the partner recursion, and `(2m)!/(2^m m!)`, agreeing on
n = 0..10 at 1, 0, 1, 0, 3, 0, 15, 0, 105, 0, 945).

Nothing here is a claim about zeta or RH. Erdos-Kac is a theorem of 1940
and this is a lemma inside one route to formalizing it; the contribution,
if it lands, is library content and one named blocker removed.
