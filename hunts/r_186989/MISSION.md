# MISSION: Erdős #126, bounded reconnaissance (r_186989)

**This is a hunt. Nothing in `hunts/` is a result, and nothing here is
evidence for or against RH (`docs/08`).**

## The question

Erdős #126. For a set $A$ of $n$ distinct positive integers write

$$P(A) = \{\,p \text{ prime} : p \mid a+b \text{ for some } a \ne b \in A\,\},
\qquad f(n) = \min_{|A|=n} |P(A)|.$$

Classical work gives $f(n) \gg \log n$ and nothing better in 92 years. Erdős
asks for $f(n)/\log n \to \infty$. The prize is \$250, paid only on a full
solution published in a reputable journal.

This run is a **parallel scout on a 30 minute cap**, not the primary lane. It
was launched to decide one thing: is there anything here worth funding, or is
the wall exactly where the literature says it is?

The brief specified three capped arms and a preliminary:

- **arm 0**, resolve the Formal Conjectures positivity mismatch: its
  statement is over `Finset ℕ`, which admits `0`, while Erdős assumes positive
  integers.
- **arm 1**: blockwise $p$-adic pruning, seeking $\exp(o(k))$ retention.
- **arm 2**: an $S$-unit clique reduction, seeking an $\exp(o(k))$ clique bound.
- **arm 3**: exact composition search through $k \le 8$ for a
  multiplicative-size / additive-support gadget.

Promotion required an iterable lemma, an $\exp(o(k))$ reduction, or a rigorous
composition law. Constant improvements, a Lean statement, or suggestive finite
data kill the scout.

## What this hunt actually measures

It does not attack $f$. It measures the inverse staircase

$$g(k) \;=\; \max\{\, n : \text{some } n\text{-set of positive integers has }
|P(A)| \le k \,\},$$

because $|P(A)| \le k$ for some $n$-set iff $f(n) \le k$ iff $n \le g(k)$, and
therefore

$$f(n)/\log n \to \infty \iff g(k) = \exp(o(k)) \iff g(k)^{1/k} \to 1 .$$

All three arms then speak about one integer sequence. `probe.py` computes
$g_N(k)$, the exact maximum inside the bounded universe $[1,N]$, by
branch-and-bound clique search on the graph $a \sim b \iff a+b$ is
$S$-smooth. Every $g_N(k)$ is a **rigorous lower bound** on $g(k)$ with an
explicit witness that is re-verified from scratch. **No upper bound on $g(k)$
is established here**, because the universe is bounded.

Sources: <https://www.erdosproblems.com/126>,
<https://combinatorica.hu/~p_erdos/1934-03.pdf>.

```huntspec
id: r_186989
question: Does bounded reconnaissance on Erdos 126 find an iterable lemma, an exp(o(k)) reduction, or a rigorous composition law strong enough to promote the pair-sum prime-support problem to a funded lane?
frontier: f(n) >> log n classical, unimproved since 1934; the conjecture f(n)/log n -> infinity is open. Equivalently g(k)^(1/k) -> 1, where measured exact maxima inside bounded universes give g(k) >= 2, 4, 5, 6, 8, 10, 11 for k = 1..7.
proposed_attack: invert the problem to the growth rate of g(k) and measure g_N(k) exactly by branch-and-bound clique search on the S-smooth pair-sum graph inside [1, N]
dead_routes:
  - composition/gadget search for a multiplicative-size additive-support law: it points the wrong way, since g(1) = 2 plus supermultiplicativity gives g(k) >= 2^k by Fekete and so refutes the conjecture rather than proving it
  - reading the conjecture off finite data: the measured k-th roots decrease monotonically over the whole range searched, which is equally consistent with a limit above 1
required_oracles:
  - exact branch-and-bound clique enumeration inside a stated bounded universe
  - independent re-verification of every witness set by full trial-division prime support
  - exhaustive small-n subset enumeration for the positivity comparison
kill_conditions:
  - the run produces only suggestive finite data and no iterable lemma
  - the only improvement available is to a constant
  - the deliverable degenerates to a Lean restatement of the conjecture
  - a witness set fails independent re-verification
agents_may:
  - search
  - derive
  - code
  - attack
agents_may_not:
  - declare novelty
  - declare theorem status
  - promote their own claim
  - claim an upper bound on g(k) from a bounded search
```

## Scope

Writes only `hunts/r_186989/` plus one case-log entry in `hunts/README.md`.
Touches no ledger under `harness/departments/`: see `RESULTS.md`, "Closing the
loop", for why there was nothing there to close.
