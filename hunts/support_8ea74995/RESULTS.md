# RESULTS: Erdős #126, formulation and equivalence audit (support 8ea74995)

**Hunt, not a result. Nothing here is evidence for or against RH (`docs/08`).**

**Headline.** The equivalences `hunts/r_186989/RESULTS.md` used are correct and
are proved here in full. Its arm-3 finding is correct and *understated*: the
refutation direction does not need supermultiplicativity or Fekete, and it
generalises to every amplification law with bounded prime cost. One of its
loose threads is **false**, and false in a way that mattered, if true it would
have settled #126 in three lines, which is the tell. The load-bearing new
statement is a quantifier observation: **#126 is a $\forall S$ statement, every
enumeration produces $\exists S$ statements, so the entire computational arm of
this problem is a refutation instrument and can never contribute to a proof.**

Reproduce with `python hunts/support_8ea74995/probe.py` (stdlib only, writes
`results.json`).

Every claim below is labelled **[proved]**, **[measured]** or **[literature]**.

---

## 0. Definitions, fixed once

For a finite $A \subset \mathbb{Z}_{>0}$ with $|A| \ge 2$,

$$P(A) \;=\; \{\,p \text{ prime} : p \mid a+b \text{ for some } a \ne b \in A\,\},$$

and $P(A) = \varnothing$ when $|A| \le 1$. Then

$$f(n) = \min_{|A| = n} |P(A)|, \qquad
g_S = \max\{|A| : P(A) \subseteq S\}, \qquad
g(k) = \max_{|S| = k} g_S .$$

**The distinctness convention is load-bearing.** $a \ne b$ is a condition on
the *indices*, and dropping it (letting $a = b$, i.e. admitting the sums $2a$)
is a different problem: $\{1,3,7,17,47\}$ has all off-diagonal sums
$\{2,3,5\}$-smooth while $47$ itself is not, so the diagonal terms would drag
in new primes. Any formalisation must range over unordered pairs of *distinct*
elements. Flagged for the Lean arm; this is the cheapest available way to get a
formal statement of #126 wrong.

## 1. Well-posedness and the exact inverse relation **[proved]**

**Lemma 1.1.** $f$ is non-decreasing.
*Proof.* For $n \ge 3$ and $A$ with $|A| = n$ attaining $f(n)$, drop one
element: $A'$ has $n-1$ elements and $P(A') \subseteq P(A)$, so
$f(n-1) \le |P(A')| \le f(n)$. For $n = 2$, $f(1) = 0 \le f(2)$. $\square$

**Lemma 1.2 (Erdős–Turán 1934) [literature].** $g_S \le 3 \cdot 2^{|S|-1}$,
with the bound depending on $|S|$ only and not on $S$. Used as published; not
reproved here.

**Proposition 1.3.** $g(k)$ is a genuine maximum (not a supremum) and
$g(k) = \max\{n : f(n) \le k\}$.
*Proof.* Each $g_S$ is an integer in $[1, 3\cdot 2^{k-1}]$ by 1.2, uniformly in
$S$, so the supremum over the infinitely many $k$-sets $S$ is attained. If
$f(n) \le k$, take $A$ with $|A| = n$, $|P(A)| \le k$, pad $P(A)$ to any $S$
with $|S| = k$: then $n \le g_S \le g(k)$. Conversely if $g(k) = |A|$ with
$P(A) \subseteq S$, $|S| = k$, then $f(|A|) \le |P(A)| \le k$. $\square$

**Theorem 1.4 (Galois connection).** For all $n \ge 1$, $k \ge 0$:
$$f(n) \le k \iff n \le g(k).$$
*Proof.* ($\Rightarrow$) 1.3. ($\Leftarrow$) $n \le g(k)$ and $f$
non-decreasing give $f(n) \le f(g(k)) \le k$. $\square$

This is the precise sense in which $f$ and $g$ are inverse staircases. It is
what makes the three formulations below interchangeable, and `r_186989` §1
asserted it without proof; it is correct.

## 2. The equivalent asymptotic forms **[proved]**

**Theorem 2.1.** The following are equivalent.

1. $f(n)/\log n \to \infty$: Erdős #126 as stated.
2. $\log g(k) = o(k)$.
3. $g(k)^{1/k} \to 1$.
4. $f(2^m)/m \to \infty$.
5. For every $c > 0$, $g(k) \le e^{ck}$ for all sufficiently large $k$.
6. $\frac{1}{k}\sum_{j<k} \log\!\big(g(j+1)/g(j)\big) \to 0$: the *average
   multiplicative gain per added prime* tends to $1$.

*Proof.* $g$ is non-decreasing and $g(k) \to \infty$ (given $n$, $g(f(n)) \ge n$
by 1.4); $f \to \infty$ by 1.2 with 1.4. (2)$\iff$(3)$\iff$(5) is arithmetic,
and (2)$\iff$(6) is the telescoping sum with $g(0)=1$, using that the summands
are non-negative so Cesàro convergence to $0$ is equivalent to the mean of the
partial sums vanishing.

(1)$\Rightarrow$(2): fix $\varepsilon > 0$, take $n_0$ with
$f(n) > \varepsilon^{-1}\log n$ for $n \ge n_0$. For $k$ large enough that
$g(k) \ge n_0$, put $n = g(k)$: $k \ge f(g(k)) > \varepsilon^{-1}\log g(k)$,
so $\log g(k) < \varepsilon k$.

(2)$\Rightarrow$(1): write $\log g(k) = \varepsilon(k)\,k$ with
$\varepsilon(k) \to 0$. For $n \ge 2$ put $k = f(n)$; then $n \le g(k)$ by 1.4,
so $\log n \le \varepsilon(f(n)) f(n)$, i.e.
$\log n / f(n) \le \varepsilon(f(n)) \to 0$ since $f(n) \to \infty$.

(1)$\Rightarrow$(4) is immediate. (4)$\Rightarrow$(1): for
$2^m \le n < 2^{m+1}$, $f(n) \ge f(2^m)$ and $\log n < (m+1)\log 2$, so
$f(n)/\log n \ge f(2^m)/\big((m+1)\log 2\big) \to \infty$. $\square$

**Form (6) is the one worth carrying.** Read through 1.4, Erdős–Turán says
*"one new prime buys at most a factor of two"*, and #126 says *"on average, one
new prime buys a factor tending to one"*, equivalently, in $f$-language, that
the marginal number of primes needed to double $|A|$ tends to infinity in
Cesàro mean. That framing makes the direction results in §5 obvious rather than
surprising.

**A correction to `r_186989` §1.** It says $g(k)$ is finite "precisely because
the classical $f(n) \gg \log n$ holds". Finiteness of $g$ is *equivalent* to
$f(n) \to \infty$, which is strictly weaker than $f(n) \gg \log n$. Harmless to
its arms, wrong as an "iff".

## 3. Uniformity over the choice of $S$

**Proposition 3.1 (monotone) [proved].** $S \subseteq S' \Rightarrow g_S \le g_{S'}$.
Immediate from the definition.

**Proposition 3.2 (parity forces $2 \in S$) [proved].** If $2 \notin S$ then
$g_S \le 2$. *Proof.* Among any three integers two share a parity class and
their sum is even. $\square$ Hence for $k \ge 2$ the maximum defining $g(k)$ is
attained at some $S \ni 2$, and the search over $k$-sets may be restricted to
those **without loss of generality**. This upgrades `r_186989`'s *measured*
parity observation to a theorem, and it is the only $S$-restriction we can
prove.

**Proposition 3.3 (normalisations that are safe) [proved].**
(a) If $d = \gcd A$ then $P(A/d) \subseteq P(A)$ and $|A/d| = |A|$, so $g_S$ is
attained by a primitive set: **"WLOG $\gcd A = 1$" is valid for upper bounds.**
(b) If $u$ is a positive $S$-unit (every prime factor of $u$ lies in $S$) then
$P(uA) \subseteq P(A) \cup P(u) \subseteq S$ and $|uA| = |A|$, so the $S$-unit
scaling group acts on $\{A : P(A) \subseteq S\}$ size-preservingly. $g_S$ is therefore attained on an infinite orbit, and no
bounded search box can be justified by "the optimum must be small".

**Normalisations that are NOT valid** (this is where the prior hunt's
uncertainty actually lives):

| Proposed pruning | Valid for a *lower* bound | Valid for an *upper* bound |
|---|---|---|
| $\gcd A = 1$ | yes | **yes** (3.3a) |
| $2 \in S$ | yes | **yes** (3.2) |
| $1 \in A$ (translate) | yes | **no**, translation does not preserve smooth sums |
| $\max A \le N$ | yes | **no**, 3.3b gives arbitrarily large equivalent optima |
| $S = $ the first $k$ primes | yes | **no, open** |

**The first-$k$-primes question is open [measured, not proved].** No argument
here shows $g(k) = g_{\{p_1,\dots,p_k\}}$. We swept it: see §6. Every table row
in `r_186989` §3 is therefore a lower bound on $g(k)$ for *two* independent
reasons, bounded box and fixed $S$; that hunt states the first and mentions the
second only in passing.

## 4. The residue lemma, and a false thread in the prior handback

`r_186989` loose thread 3 proposes: *"prove $|A| \le p-1$ when $p \notin S$ is
small, by pigeonhole on residues mod $p$ against the pairing
$r \leftrightarrow -r$."*

**That claim is false [proved], and it is false for every odd $p$.**

*Counterexample.* For any odd $p$ and any $m$, take
$A = \{1, 1+p, 1+2p, \dots, 1+(m-1)p\}$. Every off-diagonal sum is
$\equiv 2 \not\equiv 0 \pmod p$, so $p \notin P(A)$ while $|A| = m$ is
arbitrary. $\square$ (Verified in `results.json` for $p = 3,5,7$.)

**What the pigeonhole actually proves [proved].** Let $P(A) \subseteq S$ and
let $p \notin S$ be an odd prime. Then

- at most **one** element of $A$ lies in the class $0 \bmod p$;
- the set $R$ of nonzero classes occupied by $A$ satisfies $R \cap (-R) =
  \varnothing$, hence $|R| \le (p-1)/2$;
- so $A$ occupies at most $(p-1)/2 + 1$ **residue classes** mod $p$.

It bounds the number of *classes*, not the number of *elements*: two elements
in the same nonzero class $r$ have sum $\equiv 2r \not\equiv 0$, which is
allowed. $p = 2$ is the unique exception, because $2r \equiv 0$ holds for every
$r$ mod $2$, that, and not anything about small primes generally, is why
parity is special.

**Why this matters more than a typo.** Had the thread been true, applying it
with $S$ the first $k$ primes and $p = p_{k+1}$ would give
$g(k) \le p_{k+1} - 1 = O(k \log k)$, a three-line solution of a 92-year-old
problem. The measured table in `r_186989` §3 is *consistent* with the bound at
every $k \le 7$ (it gives $2,4,6,10,12,16,18$ against measured
$2,4,5,6,8,10,11$). A claim strong enough to settle the problem, agreeing with
seven data points, is a warning and not evidence.

**Thread [heuristic, not proved here].** The class restriction holds
simultaneously for *every* prime outside $S$, so $A$ is a sieved set omitting
$\ge (p-1)/2$ classes mod $p$ for all $p \notin S$. A large-sieve application
should then give $|A| \ll_\varepsilon (\max A)^{1/2+\varepsilon}$. That is a
bound in terms of $\max A$, not in terms of $k$, and by 3.3b $\max A$ is
unbounded on the orbit, so it is not a route to $g(k)$ unless someone first
proves the *primitive* optimum is bounded by a function of $k$. We did not
carry out the sieve computation; it is stated as a lead, not a result.

## 5. Implication directions: which lemmas would prove, and which would refute

This is the part the other arms were asked for.

**Theorem 5.1 (amplification refutes) [proved].** Suppose there are constants
$C \ge 1$, $\lambda > 1$ and $k_0$ with
$$g(k + C) \;\ge\; \lambda\, g(k) \qquad \text{for all } k \ge k_0 .$$
Then $\log g(k) \ge \frac{\log \lambda}{C}\,(k - k_0) - O(1)$, so
$\log g(k) \gg k$ and **#126 is false**.
*Proof.* Iterate: $g(k_0 + mC) \ge \lambda^m g(k_0)$, then use monotonicity of
$g$ to fill in between. $\square$

**Corollary 5.2 [proved].** Supermultiplicativity $g(k_1+k_2) \ge g(k_1)g(k_2)$
refutes #126. *Proof.* Take $k_2 = 1$, $\lambda = g(1) = 2$, $C = 1$ in 5.1,
or directly by induction, $g(k) \ge g(1)^k = 2^k$. **Fekete's lemma is not
needed**; `r_186989` §4 invokes it, correctly but unnecessarily, and the direct
induction gives the same $2^k$ with no subadditivity theory.

**Lemma 5.3 ($g(1) = 2$) [proved].** `r_186989`'s proof is correct and we
restate it because 5.2 rests on it. $\{1,3\}$ gives $g(1) \ge 2$. If
$a<b<c$ have $a+b = 2^x$, $a+c = 2^y$, $b+c = 2^z$ then $x<y<z$, so
$2a = 2^x + 2^y - 2^z \le 2^x + 2^y - 2^{y+1} = 2^x - 2^y < 0$. And $g_{\{p\}}
\le 2$ for odd $p$ by 3.2. $\square$

**The generalisation is the point.** 5.1 is strictly stronger than 5.2 and it
is what a proof arm needs to know: *any* lemma that buys a constant factor in
$|A|$ at a bounded cost in primes refutes the conjecture. Composition gadgets,
tensor/product constructions, "glue two witnesses with $c$ extra primes",
doubling tricks, all of them, however weak, land on the refutation side the
moment their prime cost is $O(1)$ per constant factor. Conversely a
construction whose prime cost per doubling grows, e.g. $g(k + C(k)) \ge 2g(k)$
with $C(k) \to \infty$, is fully consistent with #126 and settles nothing.

**Theorem 5.4 (quantifier shape) [proved].** #126 is equivalent to:
$$\forall \varepsilon>0 \;\exists k_0 \;\forall k \ge k_0 \;\forall S,\,|S|=k
\;\forall A,\, P(A) \subseteq S: \quad |A| \le e^{\varepsilon k}.$$
The quantifier over $S$ and over $A$ is universal. Every bounded computation,
clique search in a box, sweep over a finite family of $S$, table of witnesses,
establishes a statement of the form $\exists S \,\exists A$. **Therefore no
enumeration can contribute to a proof of #126; it can only refute it.**

That is the coherent reading of `r_186989`: its arms 1 and 2 were lower-bound
instruments pointed at an upper-bound question, and arm 3 was a refutation
instrument mislabelled as a proof route. The three failures have one cause, and
it is a quantifier, not a budget.

**A direction note the common objective needs.** "A smaller exponential base"
is listed as progress. It is progress *on Erdős–Turán*: proving
$g(k) < C\lambda^k$ with $1 < \lambda < 2$ is a strictly stronger theorem than
the 1934 bound and is worth having. It is **not** partial progress on #126:
any $\lambda > 1$ leaves $\log g(k) \asymp k$, on the same side of the wall.
#126 needs $\lambda \to 1$, i.e. form (5) of 2.1. Both things are true at once
and a report should say which one it is claiming.

## 6. The graph/clique and $S$-unit formulations

**Clique form [proved, restatement].** Let $G_S$ be the (loopless, infinite)
graph on $\mathbb{Z}_{>0}$ with $a \sim b$ iff $a+b$ is $S$-smooth. Then
$g_S = \omega(G_S)$, finite by 1.2, and $g(k) = \max_{|S|=k}\omega(G_S)$. The
distinctness convention of §0 is exactly what makes $G_S$ loopless; a version
with loops would restrict to $S$-smooth vertices and is a different graph.

**$S$-unit form [proved].** Let $\{a,b,c,d\} \subseteq A$ be four distinct
elements. The identity
$$(a+b) + (c+d) \;=\; (a+c) + (b+d)$$
has all four terms $S$-smooth. Dividing by $b+d$ and setting
$x = \frac{a+b}{b+d},\; y = \frac{c+d}{b+d},\; z = -\frac{a+c}{b+d}$ gives
$$x + y + z = 1, \qquad x,y,z \in \mathcal{O}_S^\times \text{ (the $S$-units of }\mathbb{Q}).$$
The solution is **non-degenerate** (no vanishing proper subsum): $x + y = 1$
would force $z = 0$; $x + z = 1$ would force $y = 0$; $y + z = 1$ would force
$x = 0$; and none of $x,y,z$ is zero since all of $a+b, c+d, a+c, b+d$ are
positive. $\square$

So every 4-subset of $A$ produces a non-degenerate solution of the three-term
$S$-unit equation over $\mathbb{Q}$, whose unit group has rank $k$ (rank $k+1$
with $-1$).

**What that buys, honestly.**

- If the map (4-subset) $\mapsto$ (solution) has multiplicity at most $M$, then
  $\binom{|A|}{4} \le M \cdot N_3(S)$ where $N_3(S)$ counts non-degenerate
  solutions, so $g(k) \le \big(4!\,M\,N_3(S)\big)^{1/4}$. **We did not bound
  $M$**; that is the gap in this route and it is a concrete, cheap-looking
  sub-question for another arm.
- $N_3(S) = \exp(o(k))$ would give $g(k) = \exp(o(k))$ and prove #126.
- **[literature]** For the *two*-term equation $x+y=1$ over $\mathbb{Q}$ with
  $|S| = s$, Evertse (1984) gives $\le 3 \cdot 7^{2s+1}$ solutions, while
  Erdős–Stewart–Tijdeman construct $S$ with
  $\exp\big((4+o(1))(s/\log s)^{1/2}\big)$ solutions. Upper bound exponential,
  lower bound **sub**exponential. That gap is exactly the shape of #126's gap,
  and it is where the 92-year wall sits: nobody knows the true growth rate of
  $S$-unit solution counts in $|S|$.

This is the honest version of `r_186989`'s "the top-ranked door is not one of
ours". It is the right door, and the general-purpose bounds behind it are, as
stated, **worse** than Erdős–Turán: $3 \cdot 7^{2k+1}$ is base $49$, and the
three-term Evertse–Schlickewei–Schmidt bounds are far worse still. An
improvement must come from the structure of *this* family of solutions, not
from citing a counting theorem.

## 7. What we measured

`probe.py`, stdlib only. All of it is lower-bound data and none of it is
offered as evidence about the limit.

1. **Re-verification.** All seven witnesses published in `r_186989` §3 were
   re-derived from scratch by trial-division prime support: sizes and supports
   check out, elements distinct, $|P(A)| \le k$ in every row. No defect found.
2. **$f$ and $f_0$ small values,** exhaustive over $[1,30]$ and $[0,30]$,
   independent of that hunt's $[0,40]$ run: same table, including the
   $f(2) = 1$ vs $f_0(2) = 0$ split that its §2 lemma predicts. Its §2 proof
   ($f(n-1) \le f_0(n) \le f(n)$) was checked line by line and is correct.
3. **The residue counterexamples** of §4, for $p = 3,5,7$.
4. **The $S$-sweep**: the frozen constant `r_186989`'s doors table named as
   the one with genuine trade shape, and the subject of its loose thread 4.
   Exact maximum clique in $[1,N]$ for **every** $k$-subset of the first eight
   primes:

   | $k$ | $N$ | subsets | best $g_N$ over all of them | at $S=$ | first $k$ primes | best with $2 \notin S$ |
   |---|---|---|---|---|---|---|
   | 3 | 4 000 | 56 | 5 | $\{2,3,5\}$ | 5 | 2 |
   | 4 | 2 500 | 70 | 6 | $\{2,3,5,7\}$ | 6 | 2 |

   **`r_186989` thread 4 is closed in the negative:** at $k=4$ no subset of the
   first eight primes beats 6 inside $N = 2\,500$. The first $k$ primes are
   optimal *in this family and this box*, not uniquely so ($\{2,3,7\}$ and
   $\{2,3,13\}$ tie at $k=3$, as that hunt reported). This is a lower-bound
   sweep over a finite family and it does not touch the open question of
   Proposition 3.3's last row. The $2 \notin S$ column is Proposition 3.2
   showing up as a number: every such subset caps at exactly 2.

## 8. What this arm could not settle

- **Whether the first $k$ primes are optimal for $g(k)$.** The sweep is a
  finite family in a bounded box; it can only ever say "not beaten here".
- **The multiplicity $M$ in the $S$-unit count.** Bounding it turns §6 into a
  real reduction of #126 to a unit-equation counting problem.
- **Any upper bound on $g(k)$ at all.** By 5.4 this arm was structurally
  incapable of one too, and says so rather than implying otherwise.
- **The large-sieve consequence of the residue lemma**, which is stated as a
  lead only.

## The doors

This arm measured a ceiling only incidentally (the $S$-sweep), so the list is
short and mostly inherited.

**1. Active constraints.** At the level of *statements* rather than numbers,
the binding constraint is the quantifier of 5.4: the universal $\forall S$ is
what every cheap instrument fails to reach. Below that, parity (3.2) is the
only $S$-restriction that is proved rather than observed.

**2. Frozen-constant inventory.**

| Frozen | Value | What relaxing it trades |
|---|---|---|
| the prime pool for the $S$-sweep | first 8 primes | wider pool costs $\binom{\pi(P)}{k}$ clique searches; can only raise a lower bound |
| $N$ in the sweep | 2 500–4 000 | by 3.3b no box is justified; widening cannot produce an upper bound at any $N$ |
| $k$ in the sweep | 3, 4 | the only way to extend; cost grows fast in $k$ |
| multiplicity $M$ in §6 | unbounded | **the door with real trade shape.** A bound on $M$ converts #126 into "count 3-term $S$-unit solutions", a stated open problem rather than an unstated one |

**3. Information class.** The clique searches and $S$-sweeps stay inside the
data the family already reads and, by 5.4, are confined to the refutation side
forever. The $S$-unit route reads *more*: it uses the multiplicative structure
of the sums rather than their enumeration, and it is the only door listed here
that could produce a proof.

## Direction-safe target list for the other arms

| Target | If proved, it | Grade of the direction claim |
|---|---|---|
| $g(k) < C\lambda^k$ for some $\lambda < 2$, all $S$ | improves Erdős–Turán; does **not** approach #126 | proved (§5, note) |
| $g(k) \le e^{\varepsilon k}$ eventually, every $\varepsilon$, all $S$ | **is** #126 | proved (2.1) |
| any $g(k+C) \ge \lambda g(k)$, $\lambda>1$, $C$ constant | **refutes** #126 | proved (5.1) |
| supermultiplicativity of $g$ | refutes #126 | proved (5.2) |
| a family with $\vert A\vert \ge 2^{ck}$, $\vert S\vert = k$ | refutes #126 | proved (5.1) |
| better lower bounds $g(k) \ge \mathrm{poly}(k)$ | settles nothing either way | proved (2.1) |
| $\vert A\vert \le p-1$ for $p \notin S$ | **false** | disproved (§4) |
| $A$ meets $\le (p-1)/2 + 1$ classes mod $p$, $p \notin S$ odd | true, and unexploited | proved (§4) |
| bound the multiplicity $M$ of §6 | reduces #126 to counting 3-term $S$-unit solutions | proved conditionally (§6) |
| $N_3(S) = \exp(o(\vert S\vert))$ | proves #126, given $M$ | proved conditionally (§6) |
| WLOG $\max A \le N$ | **invalid** for upper bounds | disproved (3.3b) |
| WLOG $\gcd A = 1$, WLOG $2 \in S$ | valid for upper bounds | proved (3.2, 3.3a) |

## Loose threads

- **Multiplicity of the 4-subset $\to$ $S$-unit map.** *Why:* it is the one
  cheap-looking step between this problem and a named open problem in
  Diophantine counting. *First step:* for the measured witnesses at $k=3,4$,
  compute all $\binom{|A|}{4}$ triples $(x,y,z)$ and count collisions; if $M$ is
  1 or small on real witnesses, the general bound is worth chasing.
- **The large sieve against the residue lemma.** *Why:* it is the only
  consequence of §4 that has not been extracted. *First step:* decide whether
  the primitive optimum for $g_S$ can be bounded by a function of $k$, without
  that, 3.3b makes the sieve vacuous.
- **Is $g_S$ maximised at the first $k$ primes?** *Why:* every published table
  in this tree silently assumes it, and §7 confirms it only for $k \le 4$ over
  the first eight primes in a small box. *First step:* ask whether any
  monotonicity in $p$ can be proved at all, the smooth-number density argument
  is suggestive and the arithmetic is not monotone, so a proof is not obviously
  available and a counterexample at larger $k$ is not obviously unavailable.
