# RESULTS — Erdős #126, descent arm (support run 7ddfee4b)

**Hunt, not a result. Nothing here is evidence for or against RH (`docs/08`).**

**Answer to the arm, in three lines.**

1. The suggested claim is **false as stated for every prime**, including 2.
   Omitting an odd prime from $S$ does not cap $|A|$ at all: $A \subseteq 1 + p\mathbb{Z}$
   of any size has no pairwise sum divisible by $p$. What omission caps is the
   number of occupied **residue classes**, and that caps $|A|$ only when every
   class is self-paired, which happens only at $p=2$.
2. The descent the arm asks for exists, is clean, and is an induction on $k$:
   for **primitive** sets $g^*(k) \le 2^k$, proved by deleting one odd prime
   with loss exactly 2, and **tight at $k=1,2$**.
3. **The per-prime loss cannot be pushed below 2 by this route, and that is a
   theorem, not an impression.** The combinatorial relaxation that residue
   classes + parity + prime deletion sees has optimum *exactly* $2^k$
   (Theorem 5). Any $\exp(o(k))$ bound must read something the relaxation
   discards.

Reproduce with `python hunts/support_7ddfee4b/probe.py` (stdlib only, ~1 min at
the default `PROBE_N=1500`; writes `results.json`).

---

## 0. Notation, and what an extremal example may be normalised to

$S$ is a finite set of primes, $A$ a finite set of distinct positive integers,
and $(S,A)$ is **admissible** when every $a+b$ with $a\neq b$ in $A$ is
$S$-smooth. $g(k) = \max |A|$ over admissible $(S,A)$ with $|S| = k$.

Call $A$ **primitive for $S$** when no element of $A$ is divisible by any prime
of $S$, and write $g^*(k)$ for the maximum of $|A|$ over primitive admissible
pairs.

Two normalisations, both free:

**(N1) Scaling.** For $m$ an $S$-smooth positive integer, $(S,A)$ is admissible
iff $(S, mA)$ is. So no extremal example is unique and no extremal example has a
canonical size.

**(N2) gcd removal.** $d = \gcd A$ is $S$-smooth: any prime $q \mid d$ divides
every $a+b$, so $q \in S$. Hence $(S, A/d)$ is admissible with $\gcd = 1$.

**(N2) is weaker than primitivity and the difference is the whole of §6.**
$\gcd\{1,3,5\} = 1$ while $3 \mid 3$, and $(\{2,3\},\{1,3,5\})$ is admissible.
So gcd removal does *not* deliver a primitive extremal example, and the arm's
"minimal counterexample" normalisation buys less than it looks like it buys.

## 1. The omission claim, tested and refuted

`r_186989`'s loose thread proposed: *prove $|A| \le p-1$ when $p \notin S$ is
small, by pigeonhole on residues mod $p$ against the pairing $r \leftrightarrow -r$.*

**Theorem 1 (what omission actually gives).** Let $p \notin S$. For distinct
$a,b \in A$, $p \nmid a+b$. Therefore, writing $A_c$ for the elements of $A$ in
residue class $c$ mod $p$:

* a class with $2c \equiv 0 \pmod p$ (that is $c=0$, and also $c=1$ when $p=2$)
  satisfies $|A_c| \le 1$;
* for $c \not\equiv -c$, at most one of $A_c, A_{-c}$ is non-empty;
* consequently at most $\tfrac{p+1}{2}$ classes are occupied, and **no bound
  whatever holds on the size of a non-self-paired class**. $\square$

**Corollary 1a.** $p = 2 \notin S \Rightarrow |A| \le 2$, because *every* class
mod 2 is self-paired. This is `r_186989`'s parity observation, and it is the
only case where class-counting caps $|A|$.

**Corollary 1b (refutation).** For every odd prime $p$ and every $m$, there is
an admissible $(S,A)$ with $p \notin S$ and $|A| = m$: take
$A = \{1, 1+p, \dots, 1+(m-1)p\}$, whose pairwise sums are $\equiv 2 \not\equiv 0
\pmod p$, and let $S$ be the (finite) set of primes dividing some pairwise sum.
$\square$

The claim also fails at $p=2$, by one: $A = \{1,2\}$, $S=\{3\}$ has
$|A| = 2 > p-1 = 1$. So the proposed bound $|A| \le p-1$ is false for **every**
prime; the true dichotomy is $|A| \le 2$ at $p = 2$ and unbounded otherwise.

Measured (`results.json`, key `omission`): explicit refuting instances at
$p = 3, 5, 7, 11$ with $|A| = p+2 > p-1$ in each case, each pair $(S,A)$
re-verified admissible by full trial division and each $S$ confirmed to exclude
$p$. The size $p+2$ is a choice, not a ceiling: Corollary 1b gives every $m$.

**Why the thread was tempting and what it confused.** Pigeonhole against
$r \leftrightarrow -r$ is a correct argument about the *support* of $A$ in
$\mathbb{Z}/p$, and the support is what it bounds. Turning a bound on the number
of occupied classes into a bound on $|A|$ needs each class to be small, and only
self-pairing makes a class small. That is the entire content of "2 is special".

## 2. The descent that does work: deleting one odd prime

**Theorem 2 (deletion lemma).** Let $(S,A)$ be admissible and $p \in S$ odd.
Put $A_p = \{a \in A : p \mid a\}$ and, for $1 \le c \le \frac{p-1}{2}$, let
$A_c, A_{-c}$ be the elements in those classes mod $p$. Set
$B_1 = \bigcup_c A_c$ and $B_2 = \bigcup_c A_{-c}$. Then
$A = A_p \sqcup B_1 \sqcup B_2$, and **each $B_i$ is admissible for
$S \setminus \{p\}$**.

*Proof.* For $a,b \in B_1$ in classes $c,c' \in [1,\frac{p-1}{2}]$ we have
$a+b \equiv c+c' \pmod p$ with $2 \le c+c' \le p-1$, so $p \nmid a+b$; $a+b$ is
$S$-smooth, hence $(S\setminus\{p\})$-smooth. Same for $B_2$. $\square$

**Corollary 2a.** $|A| \le 2\,g(k-1) + |A_p|$ for every odd $p \in S$.

**Theorem 3 (base cases).** $g^*(1) = 2$. For $S = \{p\}$ with $p$ odd, primitive
or not, $|A| \le 2$ by parity. For $S = \{2\}$, a primitive $A$ is all-odd, so
every pairwise sum is a power of 2; if $a<b<c$ had $a+b=2^x, a+c=2^y, b+c=2^z$
then $x<y<z$ and $2a = 2^x+2^y-2^z < 0$. So $|A| \le 2$, attained by $\{1,3\}$.
$\square$ (The power-of-2 step is `r_186989` §4; it is used again in Theorem 5.)

**Theorem 4 (primitive descent bound).** $g^*(k) \le 2^k$ for all $k \ge 1$.

*Proof.* Induction. $k=1$ is Theorem 3. For $k \ge 2$: if $2 \notin S$ then
$|A| \le 2 \le 2^k$ (Corollary 1a). Otherwise $S$ contains an odd prime $p$;
$A$ primitive gives $A_p = \emptyset$, so Theorem 2 splits $A$ into two sets
admissible for $S \setminus \{p\}$, and each remains primitive for
$S\setminus\{p\}$. Hence $|A| \le 2\,g^*(k-1) \le 2^k$. $\square$

**This is the arm's recurrence, and its per-prime loss is exactly 2**:
$g^*(k) \le 2 g^*(k-1)$, with the 2 coming from the two halves
$[1,\frac{p-1}{2}]$ and $[\frac{p+1}{2},p-1]$ of $(\mathbb{Z}/p)^\times$ under
$r \mapsto -r$.

**Tight at $k=2$.** $A = \{1,5,7,11\}$, $S = \{2,3\}$: sums
$6,8,12,12,16,18$, all $\{2,3\}$-smooth, and $A$ is primitive. So
$g^*(2) = 4 = 2^2$ exactly. Its structure is exactly the extremal shape of
Theorem 5 below: the classes mod 3 are $\{1,7\} \mapsto 1$ and
$\{5,11\}\mapsto 2$, and each same-class pair sums to a power of two
($8$ and $16$).

## 3. The obstruction: loss 2 is optimal for this whole family of arguments

Everything in §2 — parity, residue classes mod each odd prime, prime deletion,
the power-of-2 lemma — sees an admissible pair only through the following data.

**The residue relaxation.** Fix $k \ge 1$. A *relaxed instance of order $k$* is:
a finite set $V$, odd primes $p_1,\dots,p_{k-1}$, maps
$r_i : V \to (\mathbb{Z}/p_i)^\times$, and a graph $G$ on $V$, such that

* **(R1)** for all distinct $u,v \in V$, either $r_i(u) + r_i(v) \equiv 0 \pmod{p_i}$
  for some $i$, or $\{u,v\} \in E(G)$;
* **(R2)** $G$ is triangle-free.

Every primitive admissible pair with $2 \in S$, $S = \{2,p_1,\dots,p_{k-1}\}$,
yields a relaxed instance of order $k$ on $V = A$: take $r_i(a) = a \bmod p_i$
(non-zero by primitivity) and let $G$ be the pairs whose sum is a power of 2.
(R1) holds because an $S$-smooth number divisible by no $p_i$ is a power of 2;
(R2) is Theorem 3's computation.

**Theorem 5 (the relaxation is exactly $2^k$).** The maximum of $|V|$ over
relaxed instances of order $k$ is $2^k$.

*Proof.* *Upper.* Let $H_i = \{1,\dots,\frac{p_i-1}{2}\}$ and
$\varepsilon_i(u) = [\,r_i(u) \in H_i\,] \in \{0,1\}$. If
$\varepsilon(u) = \varepsilon(v)$ then for each $i$ either both residues lie in
$H_i$, whose pairwise sums lie in $[2,p_i-1]$, or both lie in $-H_i$, whose
pairwise sums lie in $-[2,p_i-1]$; either way $r_i(u)+r_i(v) \not\equiv 0$. So by
(R1) every fibre of $\varepsilon$ is a clique of $G$, hence has at most 2
elements by (R2). Thus $|V| \le 2 \cdot 2^{k-1}$.

*Lower.* Take any $k-1$ distinct odd primes, $V = \{0,1\}^{k-1} \times \{0,1\}$,
$r_i(x,j) = 1$ if $x_i = 0$ and $p_i - 1$ if $x_i = 1$, and let $G$ be the
perfect matching $\{(x,0),(x,1)\}$. Distinct $x,x'$ differ in some coordinate
$i$, where the residues are $1$ and $p_i-1$ and sum to $0$; the remaining pairs
are matching edges; a perfect matching is triangle-free. $|V| = 2^k$. $\square$

**Consequence, which is the arm's answer.** No bound better than $2^k$ follows
from (R1) and (R2) alone. Parity, residue classes mod every prime of $S$,
deletion of primes, deletion of elements and the power-of-2 lemma are all
consequences of (R1)+(R2), so **no recurrence built from them can have
per-prime loss below 2.** The requested loss $\to 1$ is not merely undiscovered
along this route; it is unavailable along it.

What the relaxation throws away, and therefore what an improvement must use:

| Discarded | Why it could bite |
|---|---|
| $a+b$ must be an $S$-smooth **number**, not merely divisible by one $p_i$ | the extremal instance of Theorem 5 needs, for each of $2^{k-1}$ residue patterns, an actual pair summing to a power of 2 *and* all cross sums smooth |
| the residues are residues **of the same integer** across all $p_i$ (CRT rigidity + Archimedean size) | fixing $a \bmod p_i$ for all $i$ pins $a$ mod $\prod p_i$, while $a+b$ must stay smooth and therefore small in a multiplicative sense |
| $A \subset \mathbb{Z}_{>0}$ is ordered | the power-of-2 lemma is the only place §2 uses order at all |

That is the same door `r_186989` ranked first ($S$-unit equations,
Evertse–Győry counting), now with a proof that the cheaper doors are shut
rather than a judgement that they look shut.

## 4. How far the loss actually is from 2, measured

Exhaustive branch-and-bound over **all** $k$-subsets of the first 8 primes,
inside $[1,N]$, for both general and primitive $A$ (`results.json`,
`max_over_subsets`; $N = 1500$).

| $k$ | $g_N(k)$ | witness | $g^*_N(k)$ (primitive) | $2^k$ (Thm 4/5) |
|---|---|---|---|---|
| 1 | 2 | $\{1,3\}$, $S=\{2\}$ | 2 | 2 |
| 2 | 4 | $\{1,5,7,11\}$, $S=\{2,3\}$ | 4 | 4 |
| 3 | 5 | $S=\{2,3,5\}$ | 5 | 8 |

These are lower bounds on $g$, $g^*$ (bounded universe), so the measured
*ratios* $g_N(k)/g_N(k-1) = 2.00, 1.25$ are neither upper nor lower bounds on
the true loss. What they do establish, jointly with Theorem 4, is that at $k=3$
the descent bound is not tight in a $60\times$-widened box (`r_186989` §3 already
found the box irrelevant), i.e. **the slack between the relaxation and the
arithmetic opens at $k=3$, and it opens for primitive sets too.** Also worth
recording: at every $k \le 3$ the best primitive set is as large as the best set,
so primitivity costs nothing here.

## 5. Extremal / minimal-counterexample normalisations: the audit

The arm asked for scaling, gcd removal, parity, residue classes, and deletion.
Verdict on each:

| Tool | Status |
|---|---|
| scaling by an $S$-smooth $m$ | exact symmetry (N1); no extremal example is minimal in any absolute sense, only up to this action |
| gcd removal | legal (N2), and **weaker than needed**: $\gcd = 1$ does not give primitivity |
| parity | the whole of the $S$-dependence, and the base case of Theorem 4 |
| residue classes mod $p \in S$ | the deletion lemma (Theorem 2), loss 2 |
| residue classes mod $p \notin S$ | caps the *support*, not $|A|$ (Theorem 1); refutes the proposed claim |
| deleting an element | nothing found: $g$ is a max over an unbounded family, so removing an element of a putative extremal set gives a smaller admissible set with the same $S$, which is no contradiction |

## 6. What I could not settle, and the honest limit on Theorem 4

**Theorem 4 is about primitive sets only, and I did not close the gap to
$g(k)$.** The deletion lemma leaves $A_p = \{a : p \mid a\}$ untouched, and
$A_p$ cannot be handled by descent on $k$, because $A_p/p$ is again admissible
**for the same $S$**: for any admissible $(S,A)$ and $p \in S$, $(S, pA)$ is
admissible with $A_p = pA$ of full size. So $|A_p| \le g(k)$ is the only bound
the split supplies, and Corollary 2a is circular as it stands. Descent on the
$p$-adic valuations terminates but the number of levels is bounded only by
$\log_p \max A$, which the scaling symmetry (N1) makes unbounded. **This is a
genuine hole, not a formality**, and closing it — bounding $g$ by $g^*$ — is the
first thing I would fund. The classical Erdős–Turán bound $g(k) < 3\cdot 2^{k-1}$
covers the general case and is not improved anywhere in this file.

Also unsettled: whether $g(k) = g^*(k)$ (true for $k \le 3$ inside the measured
box), and every asymptotic question. Nothing here moves Erdős #126.

## The doors

This run measured a ceiling (the per-prime loss), so it owes the door list.

**1. Active constraints at the optimum.**

| Rank | What binds | Evidence |
|---|---|---|
| 1 | **The relaxation itself.** Loss 2 per prime is the exact optimum of (R1)+(R2). | Theorem 5, both directions |
| 2 | **Primitivity.** The descent controls only $A_p = \emptyset$; the divisible part is invariant under the scaling symmetry and escapes. | §6, $(S,pA)$ |
| 3 | **Parity.** $2 \notin S \Rightarrow |A| \le 2$; every other omitted prime is free. | Theorem 1 and Cor. 1b |

**2. Frozen-constant inventory.**

| Frozen | Value | What relaxing it trades |
|---|---|---|
| the half $H_i = [1,\frac{p_i-1}{2}]$ used to 2-colour each prime | the standard half | **No trade shape at all, and that is the finding**: any 2-colouring separating $r$ from $-r$ gives the same factor 2, and Theorem 5 shows no choice does better. |
| triangle-freeness as the only property of the power-of-2 graph $G$ | (R2) | **Genuine trade shape.** $G$ is far more special than triangle-free: it is the graph of pairs summing to a power of 2, which is very sparse (each $a$ has at most $O(\log)$ partners below any bound). Feeding a real sparsity bound for $G$ into Theorem 5's upper proof would still only save a factor $\le 2$ overall — worth one afternoon, not a campaign. |
| $S$-smoothness used only as "divisible by some $p_i$" | (R1) | The expensive door: replacing it by $S$-unit counting is the only relaxation-escaping move identified. |
| search box $N=1500$, first 8 primes, $k \le 3$ | | Cheap to widen, and `r_186989` already showed the box is slack. Low value. |

**3. Information class.** Doors 1 and 2 stay **inside** the residue relaxation
and are provably capped at $2^k$ by Theorem 5 — that is the point of proving it.
The only door that reads more is the $S$-unit / Evertse–Győry one, plus the
narrower "bound $g$ by $g^*$" question of §6, which reads $p$-adic valuations
that the relaxation discards. **The correct reading of this run is that it
closed doors rather than opened them**, and closed them with proofs.

## Loose threads

- **Bound $g(k)$ by $g^*(k)$.** *Why it matters:* it would upgrade Theorem 4 to
  a general $g(k) \le C\cdot 2^k$ by a self-contained descent, and it is the one
  gap between this file and the classical bound. *First step:* pick an extremal
  $A$ minimising $\sum_{a\in A}\sum_{p\in S} v_p(a)$ and ask whether
  $A_p \ne \emptyset$ and $A \setminus A_p \ne \emptyset$ can coexist at the
  optimum; the measured witnesses (e.g. $\{1,3,7,17,47\}$) say yes, so the
  answer is a bound and not a normalisation.
- **How special is the power-of-2 graph?** *Why it matters:* it is the one
  ingredient of (R2) that is enormously weakened by the relaxation. *First
  step:* bound the number of edges of $\{a+b = 2^t\}$ on $[1,N]$ and re-run
  Theorem 5's upper proof with that bound in place of "clique $\le 2$".
- **$g^*(2) = 4$ is exactly $2^2$ and $g^*(3)$ looks like 5, not 8.** *Why it
  matters:* if the true $g(k)$ ever reaches $2^k$ again, Erdős #126 is false by
  the Fekete argument `r_186989` §4 gives. *First step:* decide $g^*(3)$
  outright — Theorem 4 caps it at 8, so an exhaustive search over the finitely
  many residue patterns mod $\{3,5\}$ plus the power-of-2 pairing might close it
  by hand.
