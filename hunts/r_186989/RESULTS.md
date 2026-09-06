# RESULTS: Erdős #126, bounded reconnaissance (r_186989)

**Hunt, not a result. Nothing here is evidence for or against RH (`docs/08`).**

**Verdict: the scout is dead, on a kill condition the brief pre-registered.**
Arm 1 produced suggestive finite data and no iterable lemma; arm 2 produced no
$\exp(o(k))$ clique bound; arm 3 turned out to point the wrong way. Three
things are worth keeping anyway, and they are the reason this file is longer
than "no".

Reproduce with `python hunts/r_186989/probe.py` (~2 min, stdlib only, writes
`results.json`).

---

## 1. The restatement, which is what made the arms comparable

$f$ and $g$ are inverse non-decreasing staircases:

$$g(k) = \max\{n : f(n) \le k\}, \qquad
f(n)/\log n \to \infty \iff g(k) = \exp(o(k)) \iff g(k)^{1/k} \to 1 .$$

$g(k)$ is finite for every $k$ precisely because the classical
$f(n) \gg \log n$ holds; the conjecture is the statement that its exponential
growth rate is exactly $1$. Everything below is a measurement of $g$.

## 2. Arm 0: the Formal Conjectures positivity mismatch. **Settled.**

Let $f$ be the minimum over $n$-sets of positive integers and $f_0$ the minimum
over $n$-sets of non-negative integers (the `Finset ℕ` version). Then for
$n \ge 2$:

$$f(n-1) \;\le\; f_0(n) \;\le\; f(n).$$

*Upper:* every positive set is a non-negative set. *Lower:* let $A$ attain
$f_0(n)$. If $0 \notin A$ then $A$ is a positive $n$-set and
$|P(A)| \ge f(n) \ge f(n-1)$. If $0 \in A$, then $A' = A \setminus \{0\}$ is a
positive $(n-1)$-set and every off-diagonal sum of $A'$ is an off-diagonal sum
of $A$, so $P(A') \subseteq P(A)$ and $|P(A)| \ge f(n-1)$. $\square$

So the two staircases differ by at most one step, and

$$f(n)/\log n \to \infty \iff f_0(n)/\log n \to \infty .$$

**The mismatch is harmless for the limit statement and is not harmless for
pinned finite values.** Exhaustive search over subsets of $[0,40]$:

| $n$ | 1 | 2 | 3 | 4 | 5 |
|---|---|---|---|---|---|
| $f(n)$ (positive) | 0 | **1** | 2 | 2 | 3 |
| $f_0(n)$ (0 allowed) | 0 | **0** | 2 | 2 | 3 |

$f(2)=1$ (best is $\{1,2\}$, sum $3$); $f_0(2)=0$ (take $\{0,1\}$, sum $1$,
empty prime support). A formalisation that pins a finite value of $f$ from the
`Finset ℕ` statement is wrong at $n=2$. The asymptotic statement is unaffected,
so the Formal Conjectures entry is a faithful formalisation *of the limit* and
need not be repaired for that purpose.

(The table entries are exhaustive over $[0,40]$ and are therefore upper bounds
on the true $f$, $f_0$; the inequality above is proved, not measured.)

## 3. Arms 1 and 2: $g_N(k)$, exact inside a bounded universe

Branch-and-bound clique search on $a \sim b \iff a+b$ is $S$-smooth,
$S$ = the first $k$ primes. Each row completed its search **exhaustively
inside $[1,N]$** (no timeout), and each witness was re-verified from scratch by
full trial-division prime support.

| $k$ | $S$ | $N$ | $g_N(k)$ | $g_N(k)^{1/k}$ | witness |
|---|---|---|---|---|---|
| 1 | {2} | 200 000 | 2 | 2.000 | 1, 3 |
| 2 | {2,3} | 100 000 | 4 | 2.000 | 1, 5, 7, 11 |
| 3 | {2,3,5} | 60 000 | 5 | 1.710 | 1, 3, 7, 17, 47 |
| 4 | {2,3,5,7} | 30 000 | 6 | 1.565 | 1, 2, 3, 5, 7, 13 |
| 5 | {2,3,5,7,11} | 20 000 | 8 | 1.516 | 1, 2, 5, 9, 13, 19, 23, 31 |
| 6 | {2,…,13} | 12 000 | 10 | 1.468 | 1, 2, 3, 5, 7, 9, 13, 19, 23, 47 |
| 7 | {2,…,17} | 6 000 | 11 | 1.409 | 1, 3, 5, 6, 7, 11, 15, 19, 21, 29, 49 |

**These are lower bounds on $g(k)$, and only that.** The search universe is
bounded, so a witness with a larger element would raise any row. No upper bound
on $g(k)$ is established anywhere in this hunt.

Two things are worth reporting about the run itself.

**The optima are tiny and the universe does not matter.** A first pass used
$N = 4000, 1200, 700, 400, 260, 200$. Widening to the table's $N$, a factor of
30 to 60, changed **not one row**. Every optimal witness lives well below 50.
Whatever is capping these sets is not the size of the search box.

**Arm 2: the choice of $S$ buys something, and it is a constant.** At $k=3$,
$N = 20\,000$, exhaustive:

| $S$ | $g_N$ | witness |
|---|---|---|
| {2,3,5} | 5 | 1, 3, 7, 17, 47 |
| {2,3,7} | 5 | 1, 3, 5, 11, 13 |
| {2,3,13} | 5 | 1, 2, 7, 11, 25 |
| {2,5,7} | 4 | 1, 3, 7, 13 |
| {3,5,7} | **2** | 1, 2 |

Dropping $2$ from $S$ is catastrophic: $\{3,5,7\}$ admits no 3-element set at
all inside $20\,000$, because among any three integers two have the same parity
and their sum is even. That is the whole of the $S$-dependence we could see:
$2 \in S$ or not, then a wobble of one. **No $\exp(o(k))$ clique bound came out
of it.** Arm 2 is a constant-level observation, which is itself a
pre-registered kill condition.

## 4. Arm 3: the composition gadget points the wrong way

This is the finding that changes how the problem should be briefed.

$g$ is non-decreasing and $g(1) = 2$. The witness is $\{1,3\}$, sum $4$. For
$g(1) \le 2$: if $a<b<c$ are positive with $a+b=2^x$, $a+c=2^y$, $b+c=2^z$ then
$x<y<z$, so $2a = 2^x + 2^y - 2^z \le 2^x + 2^y - 2^{y+1} = 2^x - 2^y < 0$,
impossible. (Any single-prime $S=\{p\}$ with $p$ odd gives $g \le 2$ by parity:
two of any three integers share a parity class and their sum is even.) Suppose
a rigorous **multiplicative-size / additive-support**
composition law existed: $g(k_1+k_2) \ge g(k_1)\,g(k_2)$. Then $\log g$ is
superadditive, and Fekete's lemma gives

$$\lim_k g(k)^{1/k} = \sup_k g(k)^{1/k} \;\ge\; g(1) = 2,$$

hence $g(k) \ge 2^k$ and $f(n) \le \log_2 n + O(1)$, **the conjecture is
false.**

So arm 3, as briefed, is a refutation search wearing the clothes of a proof
route. Erdős #126 is not asking for a composition law; it is asking, in this
formulation, for an **anti-composition theorem**, a proof that prime supports
cannot be combined multiplicatively. That is a structurally harder object than
the brief's promotion criterion assumed, and it is why "find the gadget" is not
a fundable direction unless the goal is to refute.

The measured data is consistent with no such gadget, in a bounded sense worth
stating precisely. Supermultiplicativity at $k_1=1, k_2=2$ would need
$g(3) \ge 8$: an 8-element set with all pairwise sums supported on 3 primes.
Exhaustive search to $N = 60\,000$ found a maximum of 5. Every one of the 11
tested $(k_1,k_2)$ pairs fails the same way, by a wide margin
($g(3)\cdot g(3) = 25$ vs. $g_N(6) = 10$). **This does not disprove
supermultiplicativity**, the products are lower bounds on both sides and a
gadget could produce elements past $N$, but it does say that any gadget must
leave the small-integer regime where all the measured optima live, which is a
real constraint on its shape.

## 5. What we could not settle

- **No upper bound on $g(k)$**, therefore no contribution to
  $f(n) \gg \log n$ or to improving it. The bounded search is structurally
  incapable of one.
- **No iterable lemma.** The $p$-adic pruning in arm 1 is a smoothness table
  lookup, not an induction with a loss we could track across $k$. Nothing in it
  iterates.
- **The trend in $g_N(k)^{1/k}$ decides nothing.** It falls monotonically,
  $2.00 \to 1.41$ over $k=1..7$, which is exactly what a sequence converging to
  $1.3$ looks like as well as one converging to $1$. Seven points cannot
  separate those. This is the "suggestive finite data" the brief named as a
  kill condition, and we are calling it that rather than dressing it up.

## 6. Closing the loop

The brief's CLOSE THE LOOP section assumes this task was returned by a function
reading a ledger under `harness/departments/`. It was not: the brief records
`Source: operator`, `Reference: prize:erdos-126:bounded-scout`. We enumerated
the ledger anyway. `harness.review.standing_reasons` reports exactly two claims
whose review is not standing, `rf-c003-window` and `k2-far-constant-depth1`,
both wanting a blind attack, and neither has anything to do with Erdős #126.
Writing an `AttackOutcome` against either would be recording an attack that did
not happen.

**So no ledger was appended, and the generator's two open items are still
open.** That is a report, not a completion: this run did not close them and
does not claim to.

## The doors

This hunt measured a ceiling ($g_N(k)$, and the wall at $\log n$), so it owes
the door list.

**1. Active constraints at the optimum.** Ranked by how hard they bind.

| Rank | What binds | Evidence |
|---|---|---|
| 1 | **Parity.** $2 \in S$ is worth more than every other structural choice combined. | $g_N(3) = 5$ with $2 \in S$, $= 2$ without. |
| 2 | **The smooth-sum graph is locally starved.** The candidate set collapses after two or three elements, not after many. | Every optimal witness has all elements $< 50$ while $N$ is up to $2\cdot10^5$; a 60× wider box added nothing. |
| 3 | **Size of $S$, weakly.** Adding a prime buys 1 or 2 elements. | $g_N$: 2, 4, 5, 6, 8, 10, 11. |

**2. Frozen-constant inventory.** Every chosen-not-optimised number:

| Frozen | Value | What relaxing it trades |
|---|---|---|
| $S$ = first $k$ primes (arm 1) | fixed | $g(k)$ is a max over *all* $k$-subsets. Arm 2 sampled 5 subsets at $k=3$ and found $\pm 1$, but only at $k=3$. **This is the door with genuine trade shape**: optimising $S$ per $k$ costs $\binom{\pi(P)}{k}$ searches and could in principle change the growth rate, not just the constant. |
| $N$ per $k$ | 6 000 – 200 000 | Already shown slack: a 60× widening moved nothing. Low value. |
| $k_{\max}$ | 7 | The only way to extend the trend. Cost is exponential in $k$ in the clique search; $k=8,9$ need a better solver, not a bigger box. |
| universe for arm 0 | $[0,40]$ | Only affects the small-$n$ table, which the proof in §2 already supersedes. |
| the greedy branch order in `expand` | ascending | Affects runtime, not the maximum (the search is exhaustive when it reports so). |

**3. Information class.** Doors 1 and 3 (optimise $S$; push $k$) stay **inside**
the data this family already reads: sets of integers and the smoothness of
their pairwise sums. They are under the configuration ceiling and cannot
produce an upper bound on $g(k)$ no matter how far they are pushed, because a
bounded search never sees the whole set. **Any door that could actually move
Erdős #126 requires reading more**, the $S$-unit equation machinery
(Evertse–Győry style bounds on the number of solutions of $x+y=1$ in $S$-units)
rather than enumeration. That is a different information class, and it is where
the 92-year wall actually sits.

The top-ranked door is therefore *not* one of ours: it is the $S$-unit
counting bound, and this hunt has no purchase on it at scout cost.

## Loose threads

- **$g(k)$'s exact values look like a sequence someone has already tabulated.**
  2, 4, 5, 6, 8, 10, 11 for $k=1..7$. *Why it might matter:* if this is a known
  OEIS sequence, the literature attached to it names the best known
  constructions and would immediately tell us whether our lower bounds are
  sharp or badly weak. *First step:* query OEIS for `2,4,5,6,8,10,11` with the
  smooth-pair-sum description; the repo already has an OEIS backend behind
  `ontology/knownness.py`.
- **The optimal witnesses are all tiny, and nobody knows why.** Every maximum
  is attained below 50 with $N$ up to $2\cdot 10^5$. *Why it might matter:* a
  proof that optima can be normalised into $[1, C^k]$ would turn the bounded
  search into an exact computation of $g(k)$, which is the missing upper-bound
  half. *First step:* test whether every maximum witness can be scaled/shifted
  into $[1, 2^{k+2}]$ for $k \le 6$ by re-running the search with $N = 2^{k+2}$
  and comparing.
- **$\{3,5,7\}$ giving $g_N = 2$ generalises.** Any $S$ omitting 2 caps the set
  at 2 by parity. *Why it might matter:* it is the only clean iterable
  statement the run found, and the same argument mod small primes may cap sets
  whose $S$ omits 3, mod 3 residue classes. *First step:* prove
  $|A| \le p-1$ when $p \notin S$ is small, by pigeonhole on residues mod $p$
  against the pairing $r \leftrightarrow -r$; check it against the measured
  table.
- **The $S$-optimisation door was sampled at $k=3$ only.** *Why it might
  matter:* it is the one frozen constant with real trade shape, per the doors
  table. *First step:* at $k=4$, search all $\binom{8}{4}=70$ subsets of the
  first 8 primes at $N=5\,000$ and see whether any beats 6.
