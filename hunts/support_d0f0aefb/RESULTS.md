# RESULTS: Erdős #126, graph/Ramsey arm (support run `d0f0aefb`)

**Hunt, not a result. Nothing here is evidence for or against RH (`docs/08`).**

Reproduce with `.venv/bin/python hunts/support_d0f0aefb/probe.py` (a few
seconds, stdlib only, writes `results.json`; re-run on landing and reproduced
byte for byte). Every claim marked *measured* below is produced by that
script; every claim marked *proved* is proved in this file and, where it is
checkable on finite data, confirmed by the script.

Notation, following `hunts/r_186989/RESULTS.md`: $S$ is a set of $k$ primes,
$A$ a finite set of distinct positive integers with every off-diagonal sum
$a+b$ $S$-smooth, $n = |A|$, and $g(k)$ the maximum $n$. For $p \in S$ let
$G_p$ be the graph on $A$ with $a \sim b \iff p \mid a+b$. The briefed premise
is that $\bigcup_{p \in S} G_p = K_n$, which is true and is the point of
contention.

**Landing note (2026-10-21).** Landed on main as Hunt #98 from a local-only
branch, `support/d0f0aefb`, that was never pushed; PR #144 counted this arm
among the seven that "produced no branch at all". The run's files are as it
wrote them apart from punctuation and the dated notes marked as added on
landing.

**Grading (added on landing, 2026-10-21).** Theorems 1 to 4 and Proposition P,
labelled *proved*, are this lab's ordinary arguments, unreviewed and pending
external verification; none is kernel-checked. *Measured* claims are exact
checks on the seven `r_186989` witnesses and searches in bounded boxes (the
coprime table of §3 gives lower bounds only). The two literature bounds behind
Theorem 4's door were checked by web search, not read in the sources (the
run's `HANDBACK.json` says so), and the reduction's prior art is unsearched;
the run's own advice is to assume it is folklore. In the terms of
`ALIGNMENT.md` §5 the dispositions are a **restricted-class obstruction** for
incidence and cover data (Theorem 3: the cover is realizable at every $n$ with
$k=2$ and $\gcd 1$, so no bound on $n$ follows from which pairs are related) and
a **refuted candidate** (`r_186989`'s loose thread 3, §1). Theorem 2 is a bound
under a hypothesis and Theorem 4 a one-way reduction; neither improves
$3\cdot2^{k-1}$ unconditionally. Two statements did not survive landing and are
corrected in place rather than deleted: the level-set clause of Theorem 1,
which fails above level 0 and takes the chromatic corollary and the
unconditional peel of §3 with it (§2), and §5's claim that a two-variable
reduction must enlarge $S$.

**Overlap with arms already on main.** Theorem 2 is the bound of Hunt #101's
primitive descent, $g^*(k)\le 2^k$ (`support_7ddfee4b`), under the same
hypothesis (no element divisible by a prime of $S$), and of Hunt #94's Lemma 2
(`support_d176e366`, landed with this arm). Theorem 4 belongs next to the
four-element reductions of Hunts #93, #95 and #105 (`support_8ea74995`,
`support_baf4cde6`, `support_eccd5f5e`), which send each 4-subset of $A$ to a
nondegenerate three-term solution without injectivity, a gap all three name;
fixing three anchors and letting the fourth element vary makes the map
injective, and that is what this arm adds. It also sits beside the two-term
reduction $g(k)\le 2+N_2(k)$ of Hunts #96 and #104 (and #97, #99 and #106,
landed with this arm), which keeps $S$ fixed too, through the uniformity of
Evertse's bound in the coefficients. The refutation of `r_186989`'s loose
thread 3 (§1) was on main before this arm landed (Hunts #93, #95, #101, #103),
with other witnesses. Theorem 3's point, that the local data is realizable at
every size, is the cover-level relative of Hunt #95's Theorem B.

---

## Verdict, in three lines

1. **The cover premise is true and it is worthless on its own.** There are
   $k=2$ configurations satisfying "every edge of $K_n$ is covered by some
   $G_p$", with $\gcd = 1$, for every $n$. So **no** theorem of the form
   "cover by $k$ residue graphs $\Rightarrow n \le h(k)$" exists. That is the
   realizable obstruction the arm asked for, and it is proved, not observed.
2. **The graph structure does buy one sharper cover theorem, under a
   hypothesis:** if no element of $A$ shares a factor with $\prod S$, then
   $n \le 2^k$, which beats Erdős–Turán's $3\cdot 2^{k-1}$ by a factor $3/2$ in
   that case. Unconditionally the same argument degrades to
   $n \le 2^k \prod_p T_p$ with $T_p$ the number of distinct values of $v_p$ on
   $A$, and $T_p$ is not bounded, so it is *weaker* than Erdős–Turán in general.
   *(Corrected on landing, 2026-10-21: the unconditional form is not
   established; its proof uses the level-set clause of Theorem 1, which fails
   above level 0. See the correction after Theorem 1 in §2.)*
3. **The exact-valuation refinement is not a graph problem at all.** Pushed to
   its end it gives a rigorous reduction, $g(k) \le 3 + N_3(k)$, where $N_3(k)$
   counts nondegenerate solutions of the three-term $S$-unit equation
   $x+y+z=1$ over the *same* $k$ primes. Erdős #126 follows from
   $N_3(k) = \exp(o(k))$, and the known lower bounds for such counts are
   $\exp(k^{1/2+o(1)})$, so **nothing known closes this door**. It is the same
   exponential-versus-subexponential gap that Evertse's bound leaves open.

Generic graph methods stall because of (1): the combinatorial shadow of the
problem has no bound in it. The content lives in the arithmetic that the shadow
throws away.

---

## 1. Audit of `hunts/r_186989/RESULTS.md`

Audited rather than trusted, as instructed. Everything I could check
independently holds.

| Claim in r_186989 | Status here |
|---|---|
| The seven witnesses are genuinely $S$-smooth-sum sets | **Confirmed**, re-verified by full trial division (`witness_audit[*].good`). All seven also have $\gcd = 1$. |
| $\bigcup_p G_p = K_n$ for each witness | **Confirmed** (`cover_holds`). |
| Restatement $f(n)/\log n \to \infty \iff g(k) = \exp(o(k))$ | **Confirmed** by re-derivation. $f$ is non-decreasing (a subset of an $n$-set has a subset of its sums), $f(n) \le k \iff n \le g(k)$, and the two limit statements are each other's contrapositive. |
| Arm 3: a composition law $g(k_1+k_2) \ge g(k_1)g(k_2)$ would *refute* the conjecture | **Confirmed.** Their proof of $g(1) = 2$ is correct as written ($x<y<z$ forces $2a = 2^x + 2^y - 2^z < 0$), Fekete applies to $\log g$, and $\sup_k g(k)^{1/k} \ge g(1) = 2$ gives $g(k) \ge 2^k$. This is the most valuable thing in that file and it survives audit. |
| Arm 0: $f(n-1) \le f_0(n) \le f(n)$ | Proof reads correctly; not re-derived in depth, it is orthogonal to this arm. |
| Loose thread: "prove $\lvert A\rvert \le p-1$ when $p \notin S$" | **Refuted.** See §2. |

**The refuted thread.** r_186989 conjectured that the parity argument
generalises: $p \notin S$ should cap $|A|$ at $p-1$ by pigeonhole on residues
mod $p$ against the pairing $r \leftrightarrow -r$. That pairing argument does
not close, because several elements may share one residue class. Explicit
counterexample, verified: $S = \{2,5\}$, $p = 3 \notin S$,

$$A = \{1, 4, 124\}: \quad 1+4 = 5, \quad 1+124 = 125 = 5^3, \quad 4+124 = 128 = 2^7 .$$

All three elements are $\equiv 1 \pmod 3$, so no sum is divisible by $3$, and
$|A| = 3 > p - 1 = 2$. **The correct general statement is much weaker:** if
$p \notin S$ then the residues of $A$ mod $p$ avoid $0$ and use at most one of
each pair $\{r, -r\}$, which bounds nothing, because a single class may hold
arbitrarily many elements. The only $p$ for which the argument does bound
anything is $p=2$, where every class is its own negative:

> **Proposition P (proved).** If $2 \notin S$ then $|A| \le 2$.
> *Proof.* Among any three integers two share a parity, and their sum is even,
> hence divisible by $2 \notin S$. $\square$

Brute force over $S = \{3,5,7\}$ inside $[1,400)$ finds pairs and no triples,
consistent (`parity_bound`).

## 2. What $G_p$ actually is (proved, and confirmed on all seven witnesses)

> **Theorem 1 (structure).** Fix $p \in S$ and write $t(a) = v_p(a)$,
> $a = p^{t(a)}a'$ with $p \nmid a'$. Then, in $G_p$:
> * $a \sim b$ for **every** pair with $t(a) \ne t(b)$, $\min(t(a),t(b)) \ge 1$;
> * no pair with $\min(t(a),t(b)) = 0 < \max(t(a),t(b))$ is an edge;
> * within a level set $V_t = \{a : t(a) = t\}$, $a \sim b \iff a' + b' \equiv 0 \pmod p$.
>
> Consequently $G_p$ is the disjoint union of $G_p|_{V_0}$ and a complete
> multipartite join of the graphs $G_p|_{V_t}$, $t \ge 1$; and for **odd** $p$
> each $G_p|_{V_t}$ is a disjoint union of complete bipartite graphs (between
> the classes $r$ and $-r$, which are distinct since $p \nmid a'$ and $p$ is
> odd). For $p = 2$ each $G_2|_{V_t}$ is a *clique*, because the only unit
> class mod $2$ is its own negative.

*Proof.* $v_p(a+b) = \min(t(a),t(b))$ when the valuations differ, and
$a + b = p^t(a'+b')$ when they agree. $\square$

**Correction on landing (2026-10-21).** The third clause holds only at level
$t=0$. For $t \ge 1$ and $a, b \in V_t$, $a+b = p^t(a'+b')$ is divisible by $p$
whatever $a'+b'$ is, so in $G_p$ every pair of multiples of $p$ is an edge: the
multiples of $p$ form **one clique**, and $G_p$ is the disjoint union of
$G_p|_{V_0}$ (complete bipartite blocks between the classes $r$ and $-r$ for odd
$p$, a clique for $p=2$) and that clique. The clause as written describes the
finer relation $p^{t+1} \mid a+b$, not $G_p$. It fails on the run's own $k=7$
witness: $3, 21 \in V_1$ for $p=3$ have $a'+b' = 1+7 \not\equiv 0 \pmod 3$, yet
$3+21 = 24$, and the same happens for $(6,15)$ at $p=3$, $(5,15)$ at $p=5$ and
$(7,21)$ at $p=7$. The probe's `structure_ok` could not see this, because it
checks only that each component is a clique, complete bipartite or isolated,
which the corrected structure also satisfies. What depends on the clause: the
chromatic bound $\chi(G_p) \le 2T_p$ for odd $p$ below (false in general:
$A=\{3,15,21,33\}$, $S=\{2,3\}$ is admissible, $G_3 = K_4$ and $T_3 = 1$), and
the unconditional peel $n \le \prod_p 2T_p$ of §3, which is therefore not
established here. What does not: Theorem 2, whose hypothesis puts every
element in $V_0$, and Theorems 3 and 4. The run's measured
$\chi \le 2T_p$ on all 27 odd-prime instances stands as a measurement on those
gcd-1 witnesses.

Equivalently and more suggestively: mod $p$ the matrix $(a_i + a_j)$ has rank
$\le 2$, and $G_p$ is its zero pattern. The complete-bipartite blocks are
forced by that rank; there is no freedom in them. **This is why the arm's
"these are not arbitrary graphs" instinct is right and also why it does not
pay: the graphs are so rigid that they carry almost no information.**

*Measured:* the component classification predicted by Theorem 1 holds for every
prime of every one of the seven r_186989 witnesses
(`per_prime.*.structure_ok`, no component of any other kind), and
$\chi(G_2) = \max(\#\text{odd}, \#\text{even})$ in every case.

**The chromatic corollary, and why it dies.** Proper colourings of the $G_p$
multiply into a proper colouring of $K_n$, so
$n \le \prod_{p\in S}\chi(G_p)$. Theorem 1 gives $\chi(G_p) \le 2T_p$ for odd
$p$ (two colours per level set, level sets joined completely; *corrected on
landing: this step uses the clause that fails above level 0, and the bound is
false in general, see the correction after Theorem 1*), where
$T_p = \#\{v_p(a) : a \in A\}$, and $\chi(G_2) = \max(\#\text{odd},\#\text{even})$.
The $p=2$ term alone is $\ge n/2$, so **the bound is vacuous on every real
witness**: measured $\prod_p \chi(G_p)$ is $2, 8, 20, 40, 112, 288, 1920$
against $n = 2,4,5,6,8,10,11$ (`product_of_chi`). Confirmed for odd $p$:
$\chi \le 2T_p$ in all 27 odd-prime instances.

## 3. The sharper cover theorem it does buy

> **Theorem 2 (proved).** If every $a \in A$ is coprime to $\prod_{p\in S} p$,
> then $|A| \le 2^k$.
>
> *Proof.* Induction on $k$. For $k=1$: if $S = \{p\}$ with $p$ odd, $G_p$ is a
> disjoint union of complete bipartite graphs by Theorem 1 ($T_p = 1$), so its
> vertex set splits into two independent sets $B_1, B_2$; a pair inside $B_i$
> has a sum with empty prime support, which is impossible for distinct
> positives, so $|B_i| \le 1$ and $|A| \le 2$. If $S = \{2\}$, all elements are
> odd and $|A| \le 2$ is r_186989's $g(1) = 2$ argument. For $k > 1$ pick an
> odd $p \in S$ if one exists; $G_p$ splits $A$ into two $G_p$-independent sets,
> each of whose pairwise sums is $(S\setminus\{p\})$-smooth and whose elements
> are still coprime to the rest of $S$, so each has size $\le 2^{k-1}$. If $S$
> has no odd prime then $k=1$. $\square$

$2^k < 3\cdot2^{k-1}$, so this is a genuine sharpening of the 1934 bound, on the
sub-family where it applies. *Measured tightness* (exhaustive branch and bound
over $[1,N]$, elements restricted to be coprime to $\prod S$):

| $k$ | $S$ | $N$ | max $\lvert A\rvert$ found | witness | Theorem 2 |
|---|---|---|---|---|---|
| 1 | {2} | 3000 | 2 | 1, 3 | 2 |
| 2 | {2,3} | 3000 | 4 | 1, 5, 7, 11 | 4 |
| 3 | {2,3,5} | 2000 | 5 | 1, 19, 31, 89, 161 | 8 |
| 4 | {2,3,5,7} | 1500 | 6 | 1, 11, 17, 19, 31, 53 | 16 |

Tight at $k \le 2$, slack from $k=3$ on. (Lower bounds only: bounded universe.)

**Why the hypothesis cannot be normalised away, which is the honest limit of
this route.** Unconditionally the same peel gives
$n \le \big(\prod_{p} 2T_p\big)$ (*corrected on landing, 2026-10-21: not
established, since the peel above level 0 needs the bipartite level-set
structure that the correction after Theorem 1 withdraws; the multiples of $p$
form a single clique in $G_p$*), and $T_p$ is unbounded: $\{1,2,4\}$ with
$S = \{2,3,5\}$ has $T_2 = 3$, and the r_186989 witnesses themselves reach
$T_3 = 3$ ($k=6$) and $T_7 = 3$ ($k=7$). The obstruction is exact and
structural: if $A_0 = \{a \in A : p \mid a\}$ then $A_0/p$ is **again** a set
with all pairwise sums $S$-smooth over the *same* $S$, so the level structure is
self-similar and no induction on $k$ sees it. Dividing by $\gcd(A)$ (legitimate:
$\gcd(A)$ divides an $S$-smooth sum, hence is $S$-smooth) removes only the
global case.

## 4. The realizable obstruction: the cover premise has no bound in it

> **Theorem 3 (proved).** For every $n$ there is a set $A$ of $n$ distinct
> positive integers with $\gcd(A) = 1$ and a set $S$ of $k=2$ primes such that
> $\bigcup_{p\in S} G_p = K_n$.
>
> *Proof.* $A = \{1\} \cup \{2(3j+1) : 0 \le j \le n-2\}$, $S = \{2,3\}$. Any
> two elements of the second block are even, so $2$ covers that edge. An edge
> from $1$ to $2(3j+1)$ has sum $6j + 3$, so $3$ covers it. $\gcd = 1$. $\square$

Verified for $n \in \{5,20,60\}$ (`residue_cover_unbounded`). These sets are of
course **not** $S$-smooth-sum sets (`actually_good: false`), and that is exactly
the point:

**The map "configuration $\mapsto$ its cover data" is not injective enough to
support any bound.** Ramsey, container, rank and cover arguments all take as
input which pairs are related, and this input is realizable at every $n$ with
$k=2$. Any argument that bounds $n$ must therefore use information that
survives past the cover: the *exact* valuations, or equivalently the sums
themselves. The same is true of the weaker relaxation "each $G_p$ is a residue
graph mod $p$", which is what Theorem 1 supplies, since the family above is
built from residue graphs.

A second, softer stall, measured on real witnesses rather than constructed: the
class-$0$ cliques make $\chi(G_p)$ as large as $n-1$ even for genuine optimal
witnesses ($k=4$, $A = \{1,2,3,5,7,13\}$: $G_2$ is a clique on the five odd
elements). So the one general graph inequality available here, the chromatic
product, is not merely weak but vacuous.

## 5. Where the exact valuation actually leads: a reduction, not a graph

The valuation data is far stronger than the graph data: knowing every
$v_p(a_i+a_j)$ determines every sum, and three sums determine three elements
($2a_1 = (a_1+a_2)+(a_1+a_3)-(a_2+a_3)$). So the configuration has $O(1)$
degrees of freedom once a few sums are fixed, which is the opposite of the
regime where extremal graph theory has anything to say. Following that to its
end:

> **Theorem 4 (proved).** Let $N_3(k)$ be the maximum, over sets $S$ of $k$
> primes, of the number of solutions $(x,y,z)$ of $x+y+z=1$ in $S$-units of
> $\mathbb{Q}$ with no vanishing subsum. Then
> $$g(k) \;\le\; 3 + N_3(k).$$
>
> *Proof.* Let $A$ be an $S$-smooth-sum set, $n \ge 4$, and fix three elements
> $a_1,a_2,a_3$. Put $c = a_2+a_3$ and $c' = a_1+a_3$, both $S$-smooth. For any
> other $a_i$ put $s_i = a_1+a_i$ and $t_i = a_2+a_i$, both $S$-smooth. Since
> $s_i - t_i = a_1 - a_2 = c' - c$, we get $s_i + c = t_i + c'$, and dividing by
> $t_i$,
> $$X + Y + Z = 1, \qquad X = \frac{s_i}{t_i},\quad Y = \frac{c}{t_i},\quad Z = -\frac{c'}{t_i},$$
> a ratio of $S$-smooth integers in each coordinate, hence $S$-units. No subsum
> vanishes: $X+Y = (t_i+c')/t_i > 0$, $X+Z = (a_i-a_3)/t_i \ne 0$, and
> $Y+Z = (a_2-a_1)/t_i \ne 0$. The map $a_i \mapsto (X,Y,Z)$ is injective
> because $Y$ determines $t_i$ and $t_i$ determines $a_i$. $\square$

*Measured:* the triples are constructed, checked to be $S$-units, checked
nondegenerate and checked pairwise distinct for all six applicable witnesses
(`s_unit_reduction[*].all_checks_pass`, counts $n-3$ as claimed). Example,
$k=3$, $A = \{1,3,7,17,47\}$: $(9/10,\,1/2,\,-2/5)$ and
$(24/25,\,1/5,\,-4/25)$.

**Check the implication direction, since the brief asks for it explicitly.**
Theorem 4 runs one way only. $N_3(k) = \exp(o(k))$ **implies** Erdős #126;
Erdős #126 does **not** imply anything about $N_3$, since a solution triple need
not come from a set $A$. This is the mirror image of r_186989's arm 3, which
found a proposed lemma whose truth would *refute* the conjecture. Here the
proposed lemma would prove it.

**Is the door open?** As far as the literature we could check goes, yes.

* The three-variable trick is what keeps $S$ fixed. The naive two-variable
  reduction $s_i - t_i = a_1 - a_2$ needs the primes of $a_1-a_2$ adjoined to
  $S$, and $\omega(a_1-a_2)$ is unbounded, so it proves nothing. Using
  $c' - c$ for the same difference makes every quantity in the equation
  $S$-smooth. That is the whole content of the third term. *(Corrected on
  landing, 2026-10-21: the two-variable reduction does not need $S$ enlarged.
  Evertse's 1984 bound for $\alpha X + \beta Y = 1$ is uniform in the
  coefficients $\alpha, \beta \in \mathbb{Q}^*$, so $s_i - t_i = a_1 - a_2$ can
  keep $a_1-a_2$ in the coefficient at rank $k$; that is the reduction
  $g(k) \le 2 + N_2(k)$ of Hunts #96 and #104, and of #97, #99 and #106 landed
  with this arm. Even a coefficient-free version adjoins $a_1 - a_2$ as one
  generator, not its $\omega(a_1-a_2)$ primes (Hunt #104's rank $k+1$). Theorem
  4 stands; what the third term buys is a coefficient-free equation over the
  same $S$, not the fixing of $S$.)*
* The best general upper bound is exponential in $k$: Evertse's
  $3\cdot 7^{2s+3}$ for the two-term equation, and the
  Evertse–Schlickewei–Schmidt subspace bounds for more terms. Substituted into
  Theorem 4 these give a bound far worse than $3\cdot2^{k-1}$, so **the
  reduction does not currently improve anything numerically.**
* The best known *lower* bounds are subexponential: Erdős–Stewart–Tijdeman
  exhibit $S$ with $\exp\{(4+o(1))(s/\log s)^{1/2}\}$ solutions of $ax+by=1$.
  Since $x+y=1 \Rightarrow x + y/2 + y/2 = 1$ is nondegenerate and injective
  when $2 \in S$, $N_3(k) \ge N_2(k)$, so the same lower bound applies to
  $N_3$. It is $\exp(o(k))$, hence **consistent with the conjecture**.

So Erdős #126 sits inside the same open gap as $S$-unit counting: upper bounds
exponential in $k$, lower bounds $\exp(k^{1/2+o(1)})$, ninety years of nobody
closing it. That is a sharper statement of the wall than "the $S$-unit machinery
is a different information class", which is where r_186989's door list stopped.

**Novelty is unsearched.** Theorem 4 is derived here and is *original* to this
run in the provenance sense, but three-term $S$-unit reductions of this shape
are standard technique and we would expect this to be folklore in the
Győry–Evertse literature. Do not claim it as new without a literature search.

## 6. What I could not settle

* **No unconditional improvement on $3\cdot2^{k-1}$.** Theorem 2 needs
  coprimality to $\prod S$, and §3 explains precisely why the hypothesis
  resists normalisation: the $p$-divisible part is a scaled copy of the whole
  problem.
* **No Ramsey or container bound, and §4 says there cannot be one** at the level
  of the cover. I did not investigate whether a container argument applied to
  the *sums* rather than the pairs could work; that is a different object.
* **$N_3(k)$'s true growth.** Not settled and not cheaply settleable. A finite
  count of small-height solutions would not bound it.
* **Whether Theorem 4 is known.** No literature search was run beyond
  confirming the two cited bounds.

## The doors

This arm measured a ceiling (the cover-theoretic ceiling), so it owes the list.

**1. Active constraints at the optimum.**

| Rank | What binds | Evidence |
|---|---|---|
| 1 | **The cover relation is not injective enough to bound anything.** Every downstream graph method inherits this. | Theorem 3: $k=2$, $\gcd = 1$, every $n$. |
| 2 | **The $p$-divisible part is self-similar**, so induction on $k$ cannot see it, and $T_p$ enters every cover bound. | $A_0/p$ is again an $S$-smooth-sum set; $T_3 = 3$ and $T_7 = 3$ occur in real witnesses. |
| 3 | **$p=2$ is not like the odd primes**: its unit class is its own negative, so $G_2$ is two cliques and $\chi(G_2) \ge n/2$. | Measured on all seven witnesses; it is also why Theorem 2's base case needs a separate argument. |

**2. Frozen-constant inventory.**

| Frozen | Value | What relaxing it trades |
|---|---|---|
| choice of the three pinned elements $a_1,a_2,a_3$ in Theorem 4 | the three smallest | Free. Any choice works, and averaging over choices might cut the count by a factor, never by an exponential. Low value. |
| number of terms in the reduced equation | 3 | **Genuine trade shape.** Two terms give a better-understood equation but enlarge $S$ by $\omega(a_1-a_2)$; four or more terms keep $S$ fixed and might allow extra constraints (all terms positive, one term fixed) that the general subspace bounds do not exploit. This is the door with real shape. *(Corrected on landing: two terms need not enlarge $S$; see the note at the end of the first bullet of "Is the door open?" in §5.)* |
| coprimality hypothesis in Theorem 2 | $\gcd(a,\prod S)=1$ | Relaxing costs the factor $\prod_p T_p$. Bounding $T_p$ in terms of $k$ would give an unconditional bound of the form $2^k\prod T_p$; nobody has bounded $T_p$. |
| search universe $N$ in the coprime table | 1500–3000 | Slack, as r_186989 already measured for the unrestricted problem. Low value. |

**3. Information class.** Everything in §§2–4 stays **inside** the cover data
and is therefore under the ceiling Theorem 3 sets: it cannot produce a bound.
Theorem 2 escapes only by adding an arithmetic hypothesis. Theorem 4 changes
information class deliberately, reading the sums rather than the incidences, and
that is the only door here with a path to the conjecture. **The top-ranked door
is the three-term $S$-unit count $N_3(k)$**, and specifically whether the
positivity and fixed-coefficient structure that Theorem 4's solutions carry
allows a subexponential count where the general equation does not.

## Loose threads

* **Bound $T_p$ in terms of $k$.** Each extra $p$-adic level in $A$ appears to
  cost new primes ($1+p^j$ must be $S$-smooth for the powers-of-$p$ family).
  If $T_p \le C$ absolutely, or even $T_p \le k^{o(1)}$, Theorem 2 becomes
  unconditional and near-$2^k$. *(Landing note: this rests on the
  unconditional peel of §3, which the correction after Theorem 1 leaves
  unestablished; bounding $T_p$ alone would not suffice as stated.)* *First step:* measure $\max_p T_p$ over
  exhaustive optimal witnesses for $k \le 6$, then try to prove
  $T_p \le 1 + \log_p(\text{something in } k)$.
* **The restricted three-term equation.** Theorem 4's solutions satisfy
  $X > 0$, $Y > 0$, $Z < 0$, and $Y$'s numerator is fixed across all of them.
  General $S$-unit counts do not use sign or fixed-numerator constraints.
  *Why it might matter:* it is the only visible slack between the reduction and
  the literature bound. *First step:* count, for $k \le 3$ and a height cutoff,
  how many nondegenerate solutions satisfy those sign constraints versus all
  solutions.
* **$\{1,4,124\}$ and its relatives.** Sets whose elements all lie in one
  residue class mod a prime outside $S$ are not rare, which is what refuted
  r_186989's thread. *Why it might matter:* the residue structure mod primes
  *outside* $S$ is completely unconstrained, which is more evidence for §4.

---

*Run `d0f0aefb`, arm `graph-ramsey`, launched by the run working
`hunts/r_186989`. Sources consulted for the two cited bounds:
[Erdős, Stewart, Tijdeman, "Some diophantine equations with many solutions",
Compositio Math. 66 (1988)](http://www.numdam.org/item/?id=CM_1988__66_1_37_0)
and [Győry, "Some recent applications of S-unit equations",
Astérisque 209 (1992)](https://www.numdam.org/article/AST_1992__209__17_0.pdf).*
