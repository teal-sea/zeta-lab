# RESULTS — Erdős #126, entropy/combinatorics arm (support run baf4cde6)

**Hunt, not a result. Nothing here is evidence for or against RH (`docs/08`).**

Reproduce with `python hunts/support_baf4cde6/probe.py` (~10 s, stdlib only,
writes `results.json`).

Setting: $S$ is a set of $k$ primes; $A$ is a finite set of distinct positive
integers with $a+b$ free of primes outside $S$ for all distinct $a,b \in A$
(call such an $A$ *$S$-summable*); $g(k) = \max|A|$. Erdős–Turán 1934 gives
$g(k) < 3\cdot 2^{k-1}$; #126 asks for $g(k) = \exp(o(k))$.

---

## Verdict

**The lane is closed, and closed by a proof rather than by a failed attempt.**

The natural signature model does not merely fail to beat $2^k$. It proves
nothing at all: **for every prime bound $P$, arbitrarily large sets satisfy
every divisibility constraint the hypothesis imposes at primes $\le P$**
(Theorem B). So no entropy, VC, container, dependent-random-choice or
forbidden-pattern argument whose input is the $p$-adic signature of $A$ at a
fixed finite prime set can bound $|A|$ by any function of $k$, because the
input is consistent with $|A| = \infty$. The whole force of the hypothesis
sits at primes larger than the elements of $A$, where "signature" is not local
data but the cofinite smoothness condition itself.

Three things survive and are worth the parent's attention:

1. **Lemma A**, the exact local obstruction (a *residue-class* cap, not an
   element cap), which corrects a thread the parent left open in a form that
   is false.
2. **Proposition C**, the entropy accounting: pushing the residue constraint to
   all primes $\le P$ with CRT injectivity saves exactly one bit per prime
   outside $S$, and lands at $2^{53}$ where Erdős–Turán gives $2^{k+1.6}$.
   Quantified, not guessed.
3. **The $S$-unit door survives this arm.** Each 4-subset of $A$ gives a
   non-degenerate solution of a three-variable unit equation. Today's counting
   theorem is worse than 1934 by a factor $\approx 10^{11}$ *in the exponent*,
   but nothing known forbids it being subexponential, so the parent's
   top-ranked door is not closed by anything I found. The gap in that route is
   the fiber problem, named in §6.

---

## 1. Audit of `hunts/r_186989/RESULTS.md`

Re-derived independently, not read off.

| Claim | Verdict |
|---|---|
| $f(n-1) \le f_0(n) \le f(n)$, and $f(2)=1 \ne 0 = f_0(2)$ | **Correct.** Proof reads cleanly; the witness $\{0,1\}$ checks. |
| $g(1) = 2$ via $2a = 2^x+2^y-2^z < 0$ | **Correct** ($x<y<z$ forces $z \ge y+1$). |
| Supermultiplicativity $\Rightarrow$ $g(k) \ge 2^k$ $\Rightarrow$ conjecture false | **Correct, and the direction is right.** Fekete gives $\lim g(k)^{1/k} = \sup_k g(k)^{1/k} \ge g(1) = 2$. A composition law refutes #126; it does not prove it. |
| $g_N(3) = 5$ with witness $\{1,3,7,17,47\}$; $g_N(4)=6$ with $\{1,2,3,5,7,13\}$ | **Reproduced** by an independently written branch-and-bound search at $N = 3000$ and $1500$. |
| All seven tabulated witnesses are $S$-summable | **Re-verified** by full trial division (`parent_witnesses_all_valid: true`). |
| Loose thread: "prove $\|A\| \le p-1$ when $p \notin S$" | **False as stated. Refuted.** |

The refutation is explicit: $A = \{1,3,7,13\}$, $S = \{2,5,7\}$, with sums
$4, 8, 14, 10, 16, 20$. Here $3 \notin S$ and $|A| = 4 > p - 1 = 2$. A small
exhaustive sweep over $S$ with $2 \in S$, $3 \notin S$, $|S| \in \{3,4\}$,
$N = 400$ reaches $|A| = 5$ (e.g. $S=\{2,5,11,17\}$, $A = \{1,9,31,79,241\}$),
so the guess fails by a growing margin and not by an edge case.

What the parent was reaching for is true in a different shape, and it is
Lemma A.

## 2. Lemma A: the exact local obstruction

**Lemma A.** Let $A$ be $S$-summable and let $p \notin S$ be prime. Then

1. $A$ contains at most one element $\equiv 0 \pmod p$;
2. $A$ never meets both classes $r$ and $-r \bmod p$ for $r \not\equiv 0$;
3. hence $A$ meets at most $(p+1)/2$ of the $p$ residue classes mod $p$;
4. and for $p = 2$ this forces $|A| \le 2$.

*Proof.* If $a \equiv -b \pmod p$ with $a \ne b$ in $A$, then $p \mid a+b$, so
$p \in S$. That is (1) with $r=0$ and (2). Nonzero classes pair off as
$\{r,-r\}$ into $(p-1)/2$ pairs for odd $p$, and $A$ uses at most one class
from each, plus possibly class $0$, giving (3). For $p=2$ both classes are
self-paired ($r \equiv -r$), so each holds at most one element. $\square$

Two things to notice, because they are the whole reason the naive guess fails.
The lemma caps **classes, not elements**: for odd $p$ any number of elements
may share one class $r$ with $2r \not\equiv 0$, since their sums are
$\equiv 2r \not\equiv 0$. And prime powers add nothing: when $p \notin S$ the
condition is $p \nmid a+b$, which lives entirely mod $p$.

Verified on all seven of the parent's witnesses at every prime $\le 37$ outside
their $S$ (`lemma_A_holds_on_all_witnesses: true`), including the sharp cases:
$\{1,3,7,13\}$ uses exactly $2 = (3+1)/2$ classes mod 3.

Part (4) is the clean proof of the parent's "parity is worth more than every
other structural choice", uniform in $k$ and not tied to a search box.

## 3. Theorem B: the signature model has no ceiling at all

This is the extremal abstract pattern the brief asked for. It is not a pattern
of size $2^k$; it is unbounded, which is a stronger statement about the model.

Fix $P$. Call *$P$-local data* everything an argument can read from the
divisibility of the off-diagonal sums by primes $\le P$: the residue vectors
$(a \bmod p)_{p \le P}$, the valuations $v_p(a+b)$ for $p \le P$, and any
constraint derived from them (this is exactly what an entropy, VC, container or
forbidden-pattern argument over prime-valuation signatures consumes).

**Theorem B.** Let $S$ be any prime set with $2 \in S$ and let $P$ be any
bound. Then for every $n$ there is an $A$ with $|A| = n$ satisfying every
constraint that $S$-summability imposes at primes $\le P$, namely
$p \nmid a+b$ for all primes $p \le P$ with $p \notin S$ and all distinct
$a,b \in A$.

*Proof.* Let $M = \prod \{p \le P : p \notin S,\ p \text{ odd}\}$ and
$A = \{1 + iM : 0 \le i < n\}$. For distinct $a,b \in A$, $a+b \equiv 2
\pmod M$, so no odd $p \mid M$ divides $a+b$. The prime $2$ lies in $S$ and is
unconstrained. $\square$

Checked computationally at $P = 60$, $S = \{2,3,5\}$: $|A| = 200$ against the
Erdős–Turán bound $3 \cdot 2^{2} = 12$ for that $k$, with zero violations at
any of the 14 absent odd primes below 60 (`local_model_unbounded`).

**Consequence.** Any argument of the briefed families, applied to $P$-local
data alone, is vacuous: its hypotheses admit sets of unbounded size, so it
cannot output a finite bound. To beat $2^k$, or to reach any bound whatsoever,
an argument must use divisibility information at primes exceeding $\max A$.
That is not a signature; it is the statement "$a+b$ is an $S$-unit", i.e. the
original hypothesis. The model has no proper subset of the hypothesis to work
with.

This also explains the parent's puzzled measurement that every optimal witness
lives below 50 while the search box ran to $2\cdot 10^5$. Nothing local is
binding. What binds is a condition about primes bigger than the elements, and
that condition tightens as elements grow.

## 4. Proposition C: the entropy bound, and exactly how far short it falls

The one non-vacuous way to use Lemma A is to take $P$ large enough that CRT
makes the residue vector injective on $A$. That is a genuine entropy argument
and it does produce a theorem. It is also strictly worse than 1934.

**Proposition C.** Let $A \subseteq [1,N]$ be $S$-summable, $|S| = k$, and let
$P$ satisfy $\prod_{p \le P,\, p \notin S} p > N$. Then
$$|A| \;\le\; \prod_{p \le P,\ p \notin S} \frac{p+1}{2}.$$

*Proof.* By CRT the map $a \mapsto (a \bmod p)_{p \le P, p \notin S}$ is
injective on $[1,N]$, and by Lemma A(3) each coordinate takes at most $(p+1)/2$
values. $\square$

In entropy form: with $a$ uniform on $A$, $\log_2|A| = H(a) \le \sum_p H(a
\bmod p) \le \sum_p \log_2\frac{p+1}{2}$. Since $\sum_{p\le P}\log_2\frac{p+1}{2}
= \sum_{p \le P}\log_2 p - \pi(P) + O(\log\log P)$, the method **saves exactly
one bit per prime outside $S$**, against a modulus that must already exceed
$N$. So it says
$$|A| \;\lesssim\; N \cdot 2^{k}\cdot 2^{-(1+o(1))\log N/\log\log N},$$
a real saving over the trivial $N$, and a bound in $N$ rather than in $k$.
Measured at $\log_2 N = 64$: the bound is $2^{53.1}$ ($k=5$), $2^{57.1}$
($k=10$), $2^{54.2}$ ($k=20$), against Erdős–Turán's $2^{5.6}$, $2^{10.6}$,
$2^{20.6}$ (`entropy_accounting`). It is never competitive, for any $N$: to
save the $\log_2 N$ bits that would make it a $k$-only bound you would need
$\pi(P) \approx \log_2 N$ primes, but those primes multiply to
$e^{\theta(P)} \gg N$ long before that.

**This is the quantitative reason the arm is dead**, and it is more useful than
the qualitative one: the residue constraint is worth one bit per prime, and the
problem needs $\log N$ bits.

## 5. The other briefed tools, briefly and honestly

- **VC dimension.** The natural set system is the neighbourhood system of the
  smooth-sum graph $a \sim b \iff a+b$ is $S$-smooth. Bounding $|A|$ needs the
  graph to be $K_{s,s}$-free or of bounded VC dimension, but $A$ itself is a
  clique, so any bound on cliques of size $t$ is the statement $g(k) < t$. The
  tool assumes what is wanted.
- **Containers / DRC.** Both need a supersaturation input: many copies of the
  forbidden configuration in any dense set. Here the host is $\mathbb{Z}$, the
  forbidden configuration is "a pair whose sum has a prime outside $S$", and
  supersaturation for it is a statement about smooth numbers in shifted sets
  that is at least as hard as the target. Neither tool is blocked in principle;
  both are blocked by having no cheaper input than the conclusion.
- **Forbidden patterns.** Lemma A is the honest yield: the only clean forbidden
  pattern is $\{r, -r\}$ mod $p$ for $p \notin S$, and Theorem B says the whole
  family of such patterns is jointly satisfiable by unbounded sets.

## 6. Where the constraint actually lives (for the parent's door ranking)

Four distinct $a,b,c,d \in A$ satisfy $(a+b) + (c+d) = (a+c) + (b+d)$.
Dividing by $a+b$,
$$x + y + z = 1, \qquad
x = \frac{a+c}{a+b},\quad y = \frac{b+d}{a+b},\quad z = -\frac{c+d}{a+b},$$
with $x,y,z$ in the group of rationals supported on $S$ (rank $k$, plus sign).
The solution is **non-degenerate**: $x+y = 0$ is impossible for positive
elements, $x+z=0 \iff a=d$ and $y+z=0 \iff b=c$, both excluded. So every
4-subset of $A$ yields a non-degenerate solution of a three-variable $S$-unit
equation.

**Direction check, stated explicitly.** Let $E_3(k)$ bound the number of
non-degenerate solutions and $m$ bound the fibers of the map (4-subsets)
$\to$ (solutions). Then $\binom{|A|}{4} \le m\, E_3(k)$, so
$|A| \le (24\,m\,E_3(k))^{1/4}$. This is an **upper**-bound route, unlike the
composition law the parent killed, which was a lower-bound route wearing the
wrong clothes.

Two facts about it:

- **With today's constants it is far worse than 1934.** The
  Evertse–Schlickewei–Schmidt bound for $n$ variables and rank $r$ is
  $\exp((6n)^{3n}(r+1))$; at $n=3$ that is $\exp(18^9(k+2))$, so after the
  fourth root the exponent constant is $18^9/4 \approx 5\cdot 10^{10}$ against
  Erdős–Turán's $\log 2 \approx 0.69$. Anyone
  ranking this door should rank the *improvement* of unit-equation counting,
  not the door as it stands.
- **Nothing known closes it.** The Erdős–Stewart–Tijdeman lower bound for the
  two-variable equation is $\exp(c(k/\log k)^{1/2})$, which is itself
  $\exp(o(k))$. So subexponential counting bounds are not excluded by any
  known construction. This is the one place where $\exp(o(k))$ is still on the
  table.
- **The gap is the fibers.** $m$ is not obviously bounded: a solution
  $(x,y,z)$ of ratios does not determine $a,b,c,d$. Bounding $m$, or replacing
  the map by one with small fibers, is the concrete missing lemma. It is a
  counting question about the smooth-sum graph, not about unit equations, and
  it is where an entropy or container argument might yet be worth something,
  which is the one qualification I would put on this arm's verdict.

## 7. What I could not settle

- **No improvement to $3\cdot 2^{k-1}$.** None of the tools in my lane produce
  any upper bound on $g(k)$, and Theorem B says why.
- **No bound on the fiber multiplicity $m$ in §6.** That is the live question
  and I did not touch it.
- **Whether Lemma A can be combined with the archimedean structure.** Lemma A
  restricts classes; the ordering of $\mathbb{Z}$ restricts which classes can
  be reused at scale. I did not find a way to make the two interact.

## The doors

This arm measured a ceiling (the signature model's), so it owes the list.

**1. Active constraints at the optimum.**

| Rank | What binds | Evidence |
|---|---|---|
| 1 | **Cofiniteness.** The hypothesis constrains all primes above $\max A$, and no finite-prime restriction of it constrains anything. | Theorem B: unbounded sets satisfy every constraint at primes $\le P$, for every $P$. |
| 2 | **One bit per absent prime.** Lemma A's saving is additive in $\pi(P)$ while the CRT cost is $\theta(P)$. | Proposition C, measured: $2^{53}$ vs $2^{5.6}$ at $\log_2 N = 64$. |
| 3 | **Parity.** $p = 2$ is the only prime whose absence caps $|A|$ rather than the class count. | Lemma A(4), proved, uniform in $k$. |

**2. Frozen-constant inventory.**

| Frozen | Value | What relaxing it trades |
|---|---|---|
| the signature level (residues mod $p$, $p \le P$) | primes only | Prime powers give nothing when $p \notin S$ (§2), so this door is provably shut, not merely unexplored. |
| $P$ in Theorem B | any | Already universally quantified. No trade. |
| the identity used in §6 | the 4-point additive relation | **The door with real trade shape.** Longer relations ($5$- and $6$-point) give unit equations in more variables: worse ESS constants, but possibly smaller fibers. Nobody has looked at the trade. |
| $\log_2 N = 64$ in the accounting | display only | Proposition C is proved for all $N$; the table is an illustration. |
| the search box $N \le 400$ in the $3 \notin S$ sweep | 400 | Affects only the size of the refutation margin, not the refutation. |

**3. Information class.** Doors 1 and 2 stay **inside** the data the signature
family reads, and Theorem B proves they cannot produce a bound at any depth.
Door 3 (the fiber count for the 4-point relation) requires reading **more**:
the joint distribution of sums, which is exactly the information the local
model discards. That is the only door in this arm with anything behind it, and
it points at the parent's $S$-unit door rather than away from it.

## Loose threads

- **Fiber multiplicity of the 4-subset $\to$ unit-solution map.** *Why it might
  matter:* it is the single missing lemma in the only upper-bound route either
  arm found. *First step:* measure it. For the parent's witnesses at $k=5,6,7$,
  compute all $\binom{|A|}{4}$ solutions $(x,y,z)$ and count collisions; if the
  map is close to injective on real witnesses, the hypothesis $m = \exp(o(k))$
  becomes worth stating.
- **Longer additive relations.** *Why it might matter:* $n$-point relations
  trade a worse ESS constant against $\binom{|A|}{n}$ on the left, and the
  optimum in $n$ has not been computed even heuristically. *First step:*
  compare $\binom{|A|}{n} \le m_n \exp((6n)^{3n}(k+1))$ across $n = 4,5,6$
  under the optimistic assumption $m_n = 1$.
- **Lemma A as a Lean target.** *Why it might matter:* it is a two-line proof
  with an exact statement, in a problem where the Formal Conjectures entry
  already exists (the parent's arm 0). *First step:* state
  `p ∉ S → A.card ≤ 2` for `p = 2` and the class-count form for odd `p`.
