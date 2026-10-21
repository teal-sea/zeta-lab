# RESULTS: Erdős #126, the p-adic block-pruning arm (support run d176e366)

**Hunt, not a result. Nothing here is evidence for or against RH (`docs/08`).**

**Headline, and it contradicts the brief.** The target the brief names,
"a block of $r$ primes can be removed while retaining more than
$2^{-r+o(r)}$ of $A$", is **not progress even if proved**. Retention
$2^{-r+o(r)}$ is exactly the Erdős–Turán bound restated (§4), and the block
programme is not a proxy for Erdős #126 but a *reformulation of it*, exact to
within a factor of 2 (§5). So the arm is well aimed and the threshold in the
brief is set one notch too low: only $c^{-r}$ with $c<2$ buys a smaller base,
and only $e^{-o(r)}$ settles the problem.

What is argued here (ordinary arguments, unreviewed; the run's draft said
"rigorous", see the grading note below): the pruning problem is an
independent-set problem (§3, Lemma 1), the joint block lemma holds at exactly
$2^{-r}$ (§4, Lemma 2), that constant cannot be improved by any argument
reading only residue data (§6, Theorem 3, with the extremal configurations
characterised), and the whole programme is equivalent to the problem (§5,
Theorem 4). What is not settled: no block lemma with base $<2$, and no
unconditional obstruction. §8 says what it would take.

One correction to `hunts/r_186989`: its loose thread 3 is false (§2).

**Landing note (2026-10-21).** Landed on main as Hunt #94 from a local-only
branch, `support/d176e366`, that was never pushed; PR #144 counted this arm
among the seven that "produced no branch at all". The run's files are as it
wrote them apart from punctuation and the dated notes marked as added on
landing.

**Grading (added on landing, 2026-10-21).** Lemmas 1 and 2, the endgame
lemma, and Theorems 3, 3′ and 4 are this lab's ordinary arguments, unreviewed
and pending external verification; none is kernel-checked, and the run's
labels are names, not grades. Theorem 3's formula matching exhaustive branch
and bound four times out of four (§6) and Lemma 1's zero mismatches on 200
random instances (§3) are exact finite checks on blocks of at most three
primes, not proofs. The §7 retention tables and the cross-prime correlation
are measurements on witnesses with $|A| \le 11$, a direction indicator only,
as the run says. In the terms of `ALIGNMENT.md` §5 the disposition is a
**restricted-class obstruction**: Theorem 3 rules out beating base 2 for
arguments that read only the residues of $A$ modulo $\prod_{p\in T}p$
(residue-only pruning), and says nothing about arguments that use the
smoothness of the sums; the attempt below base 2 is unresolved. `probe.py` was
re-run on landing and reproduced `results.json` byte for byte; no test in
`tests/` pins these numbers.

**Overlap with arms already on main.** That residue data cannot beat base 2 was
reached on main by two other routes: Hunt #92 (`support_517b887f`), whose CRT
configuration has $2^s$ points and largest jointly clean subset 1, and Hunt
#101 (`support_7ddfee4b`), whose residue relaxation (the negation pairings of
$k-1$ odd primes plus a triangle-free graph) has optimum exactly $2^k$. That
relaxation is this arm's covering reformulation (Loose threads), there solved
exactly. Theorem 4's verdict, that the programme restates the problem, is the
kind of verdict #92 reaches for the 1934 architecture ($c(A)\ge|A|/\varphi(k)$
is equivalent to $g(k)\le 2\varphi(k)$), by a different quantity. Lemma 2 with
$T=S\setminus\{2\}$ (§4) gives the bound $2^k$ of #101's primitive descent and
of Hunt #98 (`support_d0f0aefb` Theorem 2, landed with this arm), here for the
elements coprime to the odd primes of $S$. The refutation of `r_186989`'s
loose thread 3 (§2) was on main before this arm landed (Hunts #93, #95, #101,
#103). This arm's own contributions are Lemma 1's independent-set form, Lemma 2
as a one-shot joint argument, Theorem 3's exact optimum on a full residue system
with its check, Theorem 3′'s equality conditions, Theorem 4's two-sided
equivalence $g(k)\le 2/\rho_{\min}(k)\le 2g(k)$, and the false sign-orbit claim
kept with its counterexample (§6).

Reproduce with `.venv/bin/python hunts/support_d176e366/probe.py` (stdlib only,
about a second on landing, writes `results.json`).

---

## 1. Setting and notation

$S = \{p_1,\dots,p_k\}$ a set of primes. $A$ a finite set of distinct positive
integers is **admissible for $S$** when every $a+b$ with $a\neq b$ in $A$ has
no prime factor outside $S$. $g(k) = \max |A|$ over all such $S$ and $A$.
Erdős #126 asks for $\log g(k) = o(k)$; Erdős–Turán (1934) give
$g(k) < 3\cdot 2^{k-1}$.

For $T \subseteq S$ write

$$\varphi(A,T) \;=\; \max\{\,|A'| : A' \subseteq A,\ \gcd(a+b, \textstyle\prod_{p\in T} p) = 1 \ \ \forall a\neq b \in A'\,\}.$$

This is *the* quantity of the pruning programme: if $A'$ attains it then $A'$
is admissible for $S \setminus T$, so a lower bound on $\varphi$ that iterates
is a bound on $g$. Write $\rho(A,T) = \varphi(A,T)/|A|$ for the **retention
ratio** and $r = |T|$.

Throughout, $A^{\circ}_T = \{a \in A : \gcd(a, \prod_{p \in T} p) = 1\}$.

## 2. Audit of `hunts/r_186989`

Re-verified from scratch by trial division (`check_witness_audit`): **all seven
witnesses in that hunt's table are admissible**, with the stated $S$, and each
row's pairwise-sum prime support is contained in $S$. Its arm-3 lemma (no three
positive integers have all three pairwise sums powers of $2$) is re-proved
independently in §5 below and re-checked numerically over all exponent triples
$x,y,z < 60$: no triples. An independent exhaustive re-run inside $[1,120]$
reproduces $g_N(k) = 2,4,5,6,8$ for $k=1..5$ with the same witnesses, which
confirms that hunt's observation that the optima live in the small integers.
*(Annotated on landing, 2026-10-21: that observation did not survive on
main. Admissible sets are closed under $S$-smooth dilation, so a wider box only
adds larger copies of the same sets (Hunts #103 and #105), and a primitive
extremal 5-set for $S=\{2,3,5\}$ reaches 475 (Hunt #107,
$\{5,11,25,245,475\}$). What the re-run above confirms is the table rows and
their witnesses, not where the optima live.)*

**One loose thread there is false.** Its thread 3 proposes to "prove
$|A| \le p-1$ when $p \notin S$ is small, by pigeonhole on residues mod $p$
against the pairing $r \leftrightarrow -r$." The pairing argument constrains
which residue *classes* $A$ may use; it does not constrain how many elements
sit in one class. For odd $q$ and $c \not\equiv 0$, two elements both $\equiv c$
have sum $\equiv 2c \not\equiv 0$, so a class may be occupied without limit.
$A = \{1, 1+q, 1+2q, \dots\}$ has every pair sum $\equiv 2 \pmod q$ and is of
unbounded size with $q \nmid a+b$ throughout (`check_outside_prime_claim`, sizes
$3q$ for $q = 3,5,7,11,13$, verified). The one class where the pigeonhole does
bite is $c \equiv -c$, i.e. $c=0$ for odd $q$ and *both* classes for $q=2$,
which is why $2 \notin S$ forces $|A| \le 2$ and no odd $q$ does. That parity
statement, which the same hunt reports separately, is the correct residual of
the thread.

## 3. Lemma 1: the pruning problem is an independent-set problem

**Lemma 1.** Fix $T$ and let $G(A,T)$ be the graph on $A$ with
$a \sim b \iff p \mid a+b$ for some $p \in T$. Then
$\varphi(A,T) = \alpha(G(A,T))$, the independence number, and
$G(A,T) = \bigcup_{p \in T} G_p$ where $G_p$ is the **antipodal graph mod $p$**:
the disjoint union of the complete bipartite graphs between residue class $c$
and residue class $-c$ (for $c \not\equiv -c$), together with a **clique** on
the class $c \equiv -c$ (i.e. $c=0$ for odd $p$; $c \in \{0,1\}$ for $p=2$).

*Proof.* Immediate from $\gcd(a+b, \prod T) = 1 \iff$ no $p \in T$ divides
$a+b \iff a \not\equiv -b \pmod p$ for all $p \in T$. $\square$

Two consequences worth stating because they are what makes the arm's language
("valuation vectors", "ultrametric structure") *not* buy anything extra.

- **Valuations beyond the first digit are invisible to this problem.** Whether
  $p \mid a+b$ depends only on $a, b \bmod p$; $v_p(a)$ enters only through the
  indicator $v_p(a) = 0$. So the natural p-adic object here is the residue
  vector in $\prod_{p \in T} \mathbb{Z}/p$, not the valuation vector, and
  ultrametric refinement adds nothing until one asks for *fixed* $v_p(a+b)$
  rather than $v_p(a+b) = 0$, which is §8's door 3.
- **The clique on the zero class is the whole difficulty.** If all of $A$ is
  divisible by $p$ then $G_p = K_{|A|}$ and one prime covers everything. That
  is not a counterexample (dividing $A$ by $p$ returns the same problem), but
  it is exactly why the covering bound of §7 does not close.

Checked (`check_factorisation_lemma`, 200 random instances, blocks
$\{3,5\},\{3,7\},\{5,7\},\{3,5,7\},\{3,11\}$): the brute-force optimum equals
the optimum over products of half-systems with the zero classes handled by hand.
**0 mismatches.**

## 4. Lemma 2: the joint block lemma, at exactly $2^{-r}$

**Lemma 2.** For any $A$ and any block $T$ of $r$ odd primes,
$\varphi(A,T) \ \ge\ 2^{-r}\,|A^{\circ}_T|$.

*Proof.* For each $p \in T$ the $p-1$ nonzero classes split into $(p-1)/2$
antipodal pairs $\{c,-c\}$. Choose, independently for each $p$ and each such
pair, one of the two classes uniformly at random; let $H_p$ be the union of the
chosen classes, a random "half-system". These $\sum_{p} (p-1)/2$ coin flips are
independent. For $a \in A^{\circ}_T$, $\Pr[a \bmod p \in H_p] = 1/2$ for each
$p$, and the events over distinct $p$ depend on disjoint coin sets, hence are
independent: $\Pr[a \in \prod_p H_p] = 2^{-r}$. So
$\mathbb{E}\,|A \cap \prod_p H_p| = 2^{-r}|A^{\circ}_T|$ and some choice attains
it. Any such set is independent in $G(A,T)$ by Lemma 1, since
$c, -c \in H_p$ never both hold. $\square$

This is genuinely joint (one shot over all $r$ primes, no sequential
conditioning), and it lands on **exactly** the same constant as pruning one
prime at a time. That is not a coincidence; §6 shows it cannot be beaten from
residue data.

Applied with $T = S \setminus \{2\}$ and combined with Theorem 4's
$\varphi \le 2$: $|A^{\circ}_{S\setminus\{2\}}| \le 2^{k}$. That is weaker than
Erdős–Turán, which also controls the elements divisible by a prime of $S$; the
random half-system argument never captures those (they are in no $H_p$), and
closing that gap is the zero-class clique of Lemma 1 again. **We did not close
it.**

## 5. Theorem 4: the block programme *is* the problem

**Endgame lemma.** If $A'$ is admissible for $S$ and every pair sum of $A'$ is
coprime to $S \setminus \{2\}$, then $|A'| \le 2$.

*Proof.* Every pair sum is $S$-smooth and coprime to every odd prime of $S$,
hence a power of $2$ (if $2 \notin S$, a pair sum would be $1$, impossible, so
$|A'| \le 1$). Suppose $a<b<c$ in $A'$ with $a+b = 2^x$, $a+c = 2^y$,
$b+c = 2^z$. Then $a+b < a+c < b+c$ gives $x<y<z$, so
$2a = 2^x + 2^y - 2^z \le 2^x + 2^y - 2^{y+1} = 2^x - 2^y < 0$, impossible.
$\square$

(Independently re-derived; `hunts/r_186989` has the same argument. Numerically
re-checked over all $x,y,z<60$: no triples.)

**Theorem 4 (equivalence).** Let
$\rho_{\min}(k) = \min \{\varphi(A, S\setminus\{2\})/|A|\}$ over all $S$ with
$|S| = k$ and all $A$ admissible for $S$. Then

$$g(k) \;\le\; \frac{2}{\rho_{\min}(k)} \;\le\; 2\,g(k),$$

and therefore $\log g(k) = o(k) \iff \rho_{\min}(k) = e^{-o(k)}$.

*Proof.* Left: for any admissible $A$, $|A| = \varphi/\rho \le 2/\rho(A) \le
2/\rho_{\min}(k)$ by the endgame lemma. Right: $\varphi \ge 1$ always and
$|A| \le g(k)$, so $\rho(A) \ge 1/g(k)$ for every admissible $A$, hence
$\rho_{\min}(k) \ge 1/g(k)$. $\square$

**What this settles about the brief.** Retention $2^{-r+o(r)}$ at $r = k-1$
gives $g(k) \le 2^{k+o(k)}$: the Erdős–Turán bound, with a worse $o(k)$. The
block lemma is worth something only strictly below base $2$. Nothing in the
brief's framing is wrong; its threshold is.

## 6. Theorem 3: the obstruction to residue-only pruning

**Theorem 3.** Let $T$ be a block of $r$ odd primes, $M = \prod_{p\in T} p$,
and let $A$ be a full residue system mod $M$ (e.g. $A = \{1,\dots,M\}$). Then

$$\varphi(A,T) \;=\; \prod_{p \in T}\frac{p-1}{2} \;+\; r
\;=\; |A|\prod_{p\in T}\frac{p-1}{2p} \;+\; r,$$

so the retention ratio is $\prod_{p}\frac{p-1}{2p} + r/M$, which is **strictly
below $2^{-r}$** as soon as $M$ is large.

*Proof.* Upper: by Lemma 1 an independent set uses, mod each $p$, at most one
class from each antipodal pair, plus at most one element in class $0$; the
elements with a zero coordinate number at most $r$ (one per prime), and the
rest lie in $\prod_p H_p$ for some half-systems, of which there are
$\prod_p (p-1)/2$ residues mod $M$, one element each. Lower: take those
$\prod_p (p-1)/2$ elements, and for each $p \in T$ add by CRT an element
$\equiv 0 \bmod p$ and in $H_q$ for every $q \neq p$; all new pairs are checked
coordinatewise. $\square$

Verified against exhaustive branch-and-bound for $T = \{3,5\}, \{3,7\},
\{5,7\}, \{3,5,7\}$ (`check_tightness`): predicted $4, 5, 8, 9$, brute force
$4, 5, 8, 9$. **Exact match, four for four.**

| $T$ | $\|A\|$ | $\varphi$ | ratio | $2^{-r}$ |
|---|---|---|---|---|
| $\{3,5\}$ | 15 | 4 | 0.267 | 0.250 |
| $\{3,7\}$ | 21 | 5 | 0.238 | 0.250 |
| $\{5,7\}$ | 35 | 8 | 0.229 | 0.250 |
| $\{3,5,7\}$ | 105 | 9 | 0.086 | 0.125 |
| $\{3,5,7,11\}$ | 1155 | 34 | 0.029 | 0.063 |
| $\{3,5,7,11,13\}$ | 15015 | 185 | 0.012 | 0.031 |

(The one row above $2^{-r}$ is $15 \cdot \tfrac{1}{3}\cdot\tfrac{2}{5} = 2$
plus the additive $r=2$; the main term is below $2^{-r}$ in every row and the
additive term is $O(r/|A|)$.)

**Theorem 3' (when Lemma 2 is tight).** Suppose every element of $A$ is coprime
to $M$, and give $\prod_{p\in T}(\mathbb{Z}/p)^\times$ the coordinatewise sign
action of $\{\pm 1\}^T$, whose orbits all have size $2^r$. Write
$N(\varepsilon)$ for the number of elements of $A$ captured by the half-system
$\varepsilon$. Then:

1. $\mathbb{E}_\varepsilon N = |A|2^{-r}$, so $\varphi(A,T) = \max_\varepsilon N
   \ge |A|2^{-r}$ (Lemma 2 again), **with equality iff $N$ is constant**;
2. if the residue image of $A$ is a union of full sign-orbits, each occupied
   with the same multiplicity, then $N \equiv |A|2^{-r}$ and Lemma 2 is tight;
3. equality forces $|A| \ge 2^r$, since $\varphi \ge 1$.

*Proof.* (1) is the computation of Lemma 2. (2): a half-system meets each full
orbit in exactly one point. (3) is immediate. $\square$

**What is *not* true, and cost us a draft.** $\varphi(A,T)$ is not the number of
sign-orbits $A$ meets, even though each orbit is captured by one bit per prime.
Distinct orbits can share a bit: mod $(3,5)$, the elements $\equiv(1,1)$ and
$\equiv(2,2)$ lie in different orbits but both need the sign at the pair
$\{1,2\}$ mod $3$, and they need it opposite. Two orbits met, $\varphi = 1$.
Independence across primes is real (Lemma 2); independence across orbits is not.
This is why §3's independent-set formulation, and not any closed form, is the
right object.

**What Theorem 3 and 3' rule out.** Any argument that lower-bounds
$\varphi(A,T)$ *using only the reduction of $A$ modulo $\prod_{p\in T}p$* is
capped at $\prod_p \frac{p-1}{2p} + r/|A| < 2^{-r} + r/|A|$, because a residue
configuration attaining that cap exists and the argument would have to be valid
for it. So **no coordinatewise-or-joint pruning scheme that ignores the
smoothness hypothesis can beat base $2$**, and by Theorem 4 no such scheme can
improve on Erdős–Turán. Any improvement must prove that an admissible $A$
cannot look like the extremal configuration.

**And that is not vacuous, in a way worth naming.** Tightness in Theorem 3'
forces $|A| \ge 2^r$ and a capture count that does not vary with the
half-system. An admissible $A$ in the regime of interest is far smaller than
$\prod_{p\in T} p$, so the slack the programme needs is real and it is located
precisely at: **how far is the residue image of an admissible $A$ from being
closed under coordinatewise negation?** That is the door.

## 7. The measured signal, and why it is only half a signal

For each verified witness we computed $\varphi(A,T)$ exactly for **every**
block $T \subseteq S \setminus \{2\}$ (`check_full_block_pruning`).

Retention ratios, $k=7$, $|A|=11$:

| $r$ | 1 | 2 | 3 | 4 | 5 | 6 |
|---|---|---|---|---|---|---|
| min ratio over blocks | 0.455 | 0.364 | 0.273 | 0.273 | 0.273 | 0.182 |
| $2^{-r}$ | 0.500 | 0.250 | 0.125 | 0.063 | 0.031 | 0.016 |

The $r=1$ ratio sits slightly *below* $1/2$ (consistent with $(p-1)/2p$), yet
the $r=2$ ratio is $0.364$ where independence would predict $\approx 0.45^2
\approx 0.20$. **Survival across primes is strongly positively correlated in
every measured witness**, and the gap widens with $r$: at $r=6$ the ratio beats
$2^{-r}$ by a factor of $11.6$. Same picture at $k=5,6$.

The honest caveat, and it is severe: at the full block $r = k-1$ the ratio is
$2/|A|$ by Theorem 4, so *that* column is the conjecture restated at small $k$
and is not independent evidence. The intermediate columns ($r=2,3,4$) are not
forced by Theorem 4 and do carry information, but $|A| \le 11$, and finite
data alone is not progress. We report it as a direction indicator only.

`check_full_block_pruning` also confirms $\varphi(A, S\setminus\{2\}) = 2$ for
all seven witnesses, as the endgame lemma requires.

## 8. What we could not settle, and what it would take

- **No block lemma with base $< 2$.** Lemma 2 is joint and lands exactly on
  $2^{-r}$; Theorem 3 says residue data cannot do better. Not settled.
- **No unconditional obstruction.** Theorem 3 is an obstruction to
  residue-only arguments, not to all arguments, precisely because the extremal
  configuration it exhibits is *not* realisable by an admissible $A$ once
  $|A| < 2^r$. A stronger obstruction would need extremal configurations that
  are themselves admissible, and §7's measurements say those do not exist at
  small $k$.
- **The zero-class gap in Lemma 2.** The random half-system never captures an
  element divisible by a prime of $T$, so Lemma 2 bounds $|A^\circ_T|$ and not
  $|A|$. Erdős–Turán handle this; we did not.

## The doors

This hunt measured a ceiling (the $2^{-r}$ retention wall), so it owes the list.

**1. Active constraints at the optimum.**

| Rank | What binds | Evidence |
|---|---|---|
| 1 | **Sign-orbit closure of the residue image.** Lemma 2 is tight there (Thm 3'(2)) and nothing else in the argument is lossy. | Theorem 3' equality condition; Theorem 3's exact formula matching brute force 4/4. |
| 2 | **The zero-class clique of $G_p$.** It is why Lemma 2 bounds $A^\circ$ and not $A$, and why the covering reformulation (below) does not close. | §3; $G_p = K_{\|A\|}$ when $p$ divides every element. |
| 3 | **Parity.** $2$ can never be pruned: mod $2$ both classes satisfy $c \equiv -c$, so $\varphi(A,\{2\}) \le 2$. This is what fixes the endgame constant at $2$. | Endgame lemma; §2. |

**2. Frozen-constant inventory.**

| Frozen | Value | What relaxing it trades |
|---|---|---|
| the pruning target $v_p(a+b) = 0$ | $0$ | **The door with genuine trade shape.** Demanding a *fixed* $v_p(a+b) = m_p$ instead of $0$ reads deeper p-adic digits and is the only version in which "valuation vector" means more than "residue" (§3). Cost: infinitely many classes per prime, so the clean $1/2$ per prime is gone and must be replaced by a counting argument over levels of the p-adic tree. |
| half-systems chosen uniformly | uniform | Lemma 2 could weight the coin by the observed class frequencies of $A$. Buys nothing against a generic configuration (Thm 3) and could buy something against a structured one; costs nothing to try. |
| $T$ = the odd primes of $S$ | fixed | Which $r$ primes form the block is free. Small primes have retention $(p-1)/2p$, strictly worse than $1/2$; large primes approach $1/2$ from below. Ordering the block cannot beat $2^{-r}$ but changes the $e^{o(r)}$. |
| $|A| \le 11$ in §7 | measured witnesses | The correlation signal is real but tiny-$n$; the only way to strengthen it is a better clique solver, not a bigger box. |

**3. Information class.** Doors 2 and 3 stay **inside** what the current family
reads (residues mod $\prod T$) and are therefore under Theorem 3's ceiling: they
can change the $e^{o(r)}$ and never the base. Door 1 (fixed valuations / the
p-adic tree) and the covering reformulation below **require reading more**:
deeper p-adic digits, or the size constraint $a+b \le 2\max A$ together with
$\sum_p v_p(a+b)\log p = \log(a+b)$, which is the only place the *smoothness*
hypothesis (as opposed to the divisibility hypothesis) has entered nothing so
far. That is where the base-$2$ wall actually sits.

## Loose threads

- **The covering reformulation.** By Lemma 1 plus the endgame lemma, $A$
  admissible for $S = \{2\} \cup T$ forces $K_{|A|} = G_2' \cup \bigcup_{p\in T}
  G_p$ where $G_2'$ is the graph of pairs whose sum is a power of $2$, which
  is *triangle-free* by the endgame lemma. Off the zero classes each $G_p$ is a
  disjoint union of complete bipartite graphs, so Hansel's bipartite-covering
  bound applies and reproduces $|A| \le 2^{r}$ up to the $G_2'$ handling.
  *Why it might matter:* bipartite-covering bounds have refinements
  (Radhakrishnan–Srinivasan) that are sensitive to exactly the structure
  $G_p$ has, and the problem becomes finite combinatorics rather than number
  theory. *First step:* bound $\alpha(G_2')$ or the covering cost of a
  triangle-free graph well enough to avoid the $\sqrt{|A|}$ loss of the naive
  independent-set route, then run Hansel on the rest.
- **The smoothness hypothesis has not been used at all.** Everything above uses
  only "$a+b$ is divisible by primes of $S$", never "$a+b$ is *exhausted* by
  primes of $S$", except in the endgame lemma. *Why it might matter:* it is the
  entire remaining slack, and the size constraint $\sum_p v_p(a+b)\log p =
  \log(a+b) \le \log(2\max A)$ is a genuine budget across primes that no
  pruning argument here has spent. *First step:* bound the number of admissible
  $A$ with $\max A \le X$ via $S$-unit equation counts, which is the door
  `hunts/r_186989` already ranked first, and which this hunt did not touch.
- **Weighted half-systems against real witnesses.** For each measured witness,
  compare Lemma 2's uniform choice against a frequency-weighted one and see how
  much of §7's factor $11.6$ a *proof technique* can recover. *Why it might
  matter:* it separates "the correlation is real" from "the correlation is
  reachable by an argument". *First step:* a 20-line addition to `probe.py`.
