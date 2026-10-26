# RESULTS: the arithmetic difference graph arm (support run 6da47ca3)

**Hunt, not a result. Nothing here is evidence for or against RH (`docs/08`).**

**Answer to the parent, in three lines.**

1. The bipartite picture is correct but the bipartiteness is not what carries
   the weight. All the quantitative force sits in one sub-pattern, $K_{2,m}$,
   and it converts the problem into a **two-term** $S$-unit equation with a
   fixed coefficient. That gives an unconditional explicit bound
   $g(k) \le 3\cdot 7^{2k+3} + 2$, hence $f(n) \ge 0.2569\log n - 1.79$.
2. **Erdős #126 follows from the standard (open) conjecture that a two-term
   $S$-unit equation has $\exp(o(k))$ solutions.** (The run calls it the
   standard conjecture and cites no source; annotated on landing, see §4.)
   That is the theorem-level
   reduction asked for, and it is the honest location of the wall: every known
   uniform upper bound on that count is $\exp(O(k))$, and $\exp(O(k))$ is
   exactly $\log g(k) = O(k)$, which is the classical statement, not the target.
3. **The extra within-part pair-sum structure yields no improvement in the
   exponent.** It buys one real thing, a free nondegeneracy guarantee, and
   nothing else, because using it forces three-term unit equations whose best
   uniform bounds are worse in $k$ by eleven orders of magnitude in the slope.

The audit of `hunts/r_186989/RESULTS.md` found it sound in every checkable
claim, reproduced its table independently, and **refutes one of its four loose
threads** with an explicit counterexample.

**Landing note (2026-10-21).** Landed on main as Hunt #106 from a local-only
branch, `support/6da47ca3`, that was never pushed; PR #144 counted this arm
among the seven that "produced no branch at all". The run's files are as it
wrote them apart from punctuation, the dated notes marked as added on landing,
and one word: the noun in "nondegeneracy guarantee" is a landing substitution,
made here, in `probe.py`, in `HANDBACK.json` and in the regenerated
`results.json`, because the run's word was a form of the one reserved to
`zeta/rigor.py` and the Lean arm.

**Grading (added on landing, 2026-10-21).** Theorem 1, Corollaries 2 and 3 and
Lemma 4 are this lab's ordinary arguments, unreviewed and pending external
verification; none is kernel-checked. Corollary 2's constant uses Evertse's
$3\cdot7^{d+2s}$ "as I recall it", not re-read in the run; it agrees with
Győry–Stewart–Tijdeman's quotation of Evertse, which the sibling literature
arm read in primary text (Hunt #143, T4), but this arm did not check it. §4's
"standard conjecture" and "believed conjecture" cite no source and are
annotated in place. §8 rests on the published abstracts, since both PDFs came
back undecoded, and the run says so. The §6 table is exhaustive inside bounded
boxes, so every entry is a lower bound. Disposition (`ALIGNMENT.md` §5): the
attempt is unresolved. The reduction is sufficient, not necessary; Corollary 2
re-proves the classical $f(n)\gg\log n$ with a tracked constant and moves
nothing; the verdict that the within-part structure buys no improvement in the
exponent is a comparison with the known three-term bounds, not an obstruction;
and `r_186989`'s loose thread 3 is a refuted candidate. `probe.py` was re-run
on landing after the rewording; `results.json` changed in that one string and
nowhere else.

**Overlap with arms already on main.** Theorem 1 is the reduction of Hunts #96
(`support_d5d5ccae`) and #104 (`support_f3ab3e34`), and of Hunts #97 and #99
landed with this arm; Győry–Stewart–Tijdeman 1986 §3 has it too (quoted by
Hunt #143). Corollary 2's explicit $3\cdot7^{2k+3}$ is #96's constant. Lemma 4
is the nondegeneracy step of the four-element reductions of Hunts #93, #95 and
#105. Konyagin–Soundararajan's lower bound is also cited on main by Hunt #102
(from the abstract). The refutation of loose thread 3 (§7) was on main before
this arm landed (Hunts #93, #95, #101, #103), and the OEIS thread was closed by
the literature arm (Hunt #143). This arm's own contributions are the exactness
of the $K_{2,m}$ correspondence, the measured crown-versus-$K_{2,m}$ loss of §6
($g_N(5)=8$ against $N_2^{(N)}(5)\ge 141$), and the Győry–Hajdu–Tijdeman
specialisation of §8, that their theorems are representability results with
no bound of the form $|A|\le F(|S|)$.

Reproduce with `.venv/bin/python hunts/support_6da47ca3/probe.py` (a few
seconds, stdlib only, writes `results.json`).

---

## 0. Notation

$S = \{p_1,\dots,p_k\}$ a set of $k$ primes, $\mathbb{Z}_S$ the rationals with
denominators supported on $S$, $\Gamma = \mathbb{Z}_S^*$ the group of $S$-units
(rank $k$, torsion $\{\pm 1\}$). $A$ is a set of distinct positive integers
with every off-diagonal sum $a+b$ an $S$-unit, and
$g(k) = \max |A|$ over all such $A$ and all $S$ with $|S| = k$. Following
`r_186989`, Erdős #126 ($f(n)/\log n \to \infty$) is exactly
$\log g(k) = o(k)$.

## 1. The bipartite pattern, and what is actually in it

Put $B = -A$ and take the vertex set $A \sqcup B \subset \mathbb{Z}$. Then for
$a \in A$ and $-b \in B$,

$$a - (-b) = a + b ,$$

so the hypothesis says exactly: **in the $S$-unit difference graph
$\mathcal{G}_S(A \cup -A)$, the crown graph $K_{n,n}$ minus its perfect
matching is a subgraph.** The parent's framing is right. Two riders that
matter, and the second is the load-bearing one.

*Rider 1: subgraph, not induced subgraph.* Nothing constrains $a_i - a_j$
(within-part differences) or $2a_i$ (the removed matching). The
Győry–Hajdu–Tijdeman notion of *representation* is the induced one, so their
theorems are about a strictly stronger relation than ours. For an upper bound
on $n$ that is the safe direction (a subgraph statement is what we may use);
for lower bounds it means their constructions do **not** transfer.

*Rider 2: the crown is triangle-free, and that is normally fatal.* The
standard route from a difference graph to a unit equation needs a triangle:
$x,y,z$ pairwise joined gives $(x-y) + (y-z) = (x-z)$, i.e. $u + v = w$ with
$u,v,w \in \Gamma$, i.e. after division the coefficient-free equation
$u/w + v/w = 1$. A bipartite graph has no triangle, so that route is closed
here. What replaces it is the 4-cycle, and a 4-cycle in a difference graph
gives a **two-term equation with a fixed inhomogeneous coefficient**:
$u - v = c$ with $c$ a fixed non-zero rational. This is the whole technical
content of the arm.

## 2. The reduction

Define, for $k \ge 1$,

$$N_2(k) \;=\; \max_{|S| = k} \; \max_{c \in \mathbb{Q}^*} \;
\#\{(u,v) \in \Gamma^2 \;:\; u - v = c\} .$$

(The inner maximum is over *all* non-zero rationals $c$, not just $S$-units.)

> **Theorem 1 (reduction).** $\;g(k) \le N_2(k) + 2$.

*Proof.* Let $A$ be admissible with $|A| = n \ge 3$. Fix two distinct elements
$a_1, a_2 \in A$ and set $c = a_1 - a_2 \ne 0$. For every $x \in A \setminus
\{a_1,a_2\}$ both $u_x = x + a_1$ and $v_x = x + a_2$ are $S$-units (they are
off-diagonal sums), and $u_x - v_x = c$. The map $x \mapsto (u_x, v_x)$ is
injective, since $x = u_x - a_1$. Hence $n - 2 \le N_2(k)$. $\square$

Three things to notice about this proof, because they are the answer to the
parent's three sub-questions.

- It uses **only** the sub-pattern $K_{2,m}$: two vertices of one part joined
  to $m$ vertices of the other. Neither the bipartiteness, nor the removed
  matching, nor the antisymmetric labelling $B = -A$, nor positivity is used.
  Theorem 1 therefore holds verbatim for any $A \subset \mathbb{Q}$ all of
  whose differences to a fixed 2-element set are $S$-units.
- Conversely the correspondence is **exact**: given $x_1, x_2$ with
  $c = x_1 - x_2$, the vertices $y$ joined to both are in bijection with the
  solutions of $u - v = c$. So $N_2(k)$ *is* the largest $m$ with
  $K_{2,m} \subseteq \mathcal{G}_S(\cdot)$ for some $|S| = k$. Nothing is
  thrown away at this step; the loss is entirely in going from the crown
  down to $K_{2,m}$ (measured in §5).
- This is also, I believe, the reason the GHT threshold is *cubical*
  (= subgraph of a hypercube): in $Q_d$ two vertices have at most two common
  neighbours, so $K_{2,3} \not\subseteq Q_d$. The crown $K_{n,n}$ minus a
  matching has two vertices with $n-2$ common neighbours, so it is cubical
  exactly for $n \le 4$ (and the $n=4$ crown *is* $Q_3$). The one place where
  our pattern leaves the cubical world is precisely the place where the
  quantitative content lives.

## 3. The unconditional consequence, with the constant tracked

> **Corollary 2.** $g(k) \le 3\cdot 7^{2k+3} + 2$, hence
> $\log g(k) \le (2\log 7)\,k + \log 3 + 3\log 7 = 3.8918\,k + 6.936$, hence
> for $n \ge 3$
> $$f(n) \;\ge\; \frac{\log(n-2) - \log 3}{2\log 7} - \frac{3}{2}
> \;=\; 0.25695\log n - 1.782 + o(1).$$

*Input.* Evertse (*Invent. Math.* **75** (1984), 561–584): for a number field
$K$ of degree $d$ and a set $S$ of $s$ places of $K$ containing the
archimedean ones, and fixed $\alpha,\beta \in K^*$, the equation
$\alpha x + \beta y = 1$ has at most $3\cdot 7^{d+2s}$ solutions
$x,y \in O_S^*$. Uniform in $\alpha,\beta$, which is what lets $c$ be
arbitrary. Apply with $K = \mathbb{Q}$, $d = 1$, $s = k+1$, and
$(\alpha,\beta) = (1/c, -1/c)$ applied to $u - v = c$. So
$N_2(k) \le 3\cdot 7^{2k+3}$.

(Beukers–Schlickewei's $2^{8(r+1)}$ for the coefficient-free equation gives
$2^{8(k+2)}$ after absorbing $c$ into the group, slope $8\log 2 = 5.545$;
Evertse's slope $3.892$ is better here. Both are $\exp(O(k))$, which is the
point.)

Corollary 2 is a re-proof of the classical $f(n) \gg \log n$ with an explicit
constant, obtained from the bipartite picture rather than from whatever the
original argument was. **It does not move the problem**, and I want to be flat
about that: $\log g(k) = O(k)$ is the known statement, and the target is
$o(k)$.

## 4. Where the wall actually is, stated as a conditional

> **Corollary 3 (the reduction the parent asked for).** If
> $\log N_2(k) = o(k)$, then $\log g(k) = o(k)$, i.e. Erdős #126 holds.

So Erdős #126 is *implied by* a purely Diophantine counting statement:
**two-term $S$-unit equations, uniformly in the coefficients, have
subexponentially many solutions in $|S|$.** That statement is open, and its
status is worth stating precisely because it decides whether this arm is
fundable:

| | best known | in $\log$ |
|---|---|---|
| upper bound on $N_2(k)$ | $3\cdot 7^{2k+3}$ (Evertse 1984) | $\Theta(k)$ |
| lower bound, $x+y=1$ | $\exp\!\big(c\,(k/\log k)^{1/2}\big)$ (Erdős–Stewart–Tijdeman 1988) | $k^{1/2+o(1)}$ |
| lower bound, improved | $\exp\!\big(k^{2-\sqrt 2-o(1)}\big)$ (Konyagin–Soundararajan 2007) | $k^{0.5857\ldots}$ |

Every known lower bound is $\exp(k^{\theta})$ with $\theta < 1$. So
$\log N_2(k) = o(k)$ is consistent with everything known, and it is what the
$S$-unit-equation literature expects to be true. **Erdős #126 is therefore a
consequence of a believed conjecture in a different field**, and the 92-year
wall on it is the same wall as the gap between $\exp(O(k))$ and
$\exp(k^{0.59})$ in unit-equation counting.

*Annotated on landing (2026-10-21).* "What the literature expects" and "a
believed conjecture" cite no source, and the run's second caveat below says
as much. The sibling literature arm looked for exactly this statement and did
not find it in a source it read (Hunt #143, `support_fcffa3b9` §5, first
bullet, which names Evertse–Győry, *Unit Equations in Diophantine Number
Theory*, Ch. 6, as the place to check). Read the two sentences above as the
run's reading of the field, not as a citation: what is established is the
table (every known lower bound is $\exp(k^{\theta})$ with $\theta<1$), so
$\log N_2(k) = o(k)$ is consistent with everything known. Whether it is a
stated conjecture of that field is open.

Two honest caveats.

- **Sufficient, not necessary.** The reduction throws away most of the crown
  (§5 measures how much), so $\log g(k) = o(k)$ could be provable without
  $\log N_2(k) = o(k)$.
- The conjecture is needed *uniformly in $c$*. The many-solution constructions
  are built for particular equations, and I did not verify in-session whether
  the expected subexponential truth is asserted uniformly in the coefficients
  in the literature. Treat "expected truth" as my reading, not as a citation.

## 5. Does the within-part pair-sum structure buy anything? No.

The parent's specific question. Three attempts, all measured or argued:

**(a) More anchor pairs.** The crown gives Theorem 1 for *every* pair
$(a_i,a_j)$, so $n - 2 \le \min_{i<j} \#\mathrm{Sol}(a_i - a_j)$. A minimum of
quantities each bounded only by the uniform $N_2(k)$ is still bounded only by
$N_2(k)$. No gain.

**(b) More anchors at once.** Using $a_1,\dots,a_j$ as anchors asks for
$x$ with $x + a_1,\dots,x+a_j$ all $S$-units: the $S$-integral points on
$\mathbb{P}^1$ minus $j+1$ points. Every known bound for that is proved by
reducing to two-term unit equations and so inherits $\exp(O(k))$; the gain is
in the constant, not the exponent, and the constant is already the min in (a).

**(c) Use the within-part sums as unknowns.** This is where the extra
structure genuinely appears, and it does give one real thing:

> **Lemma 4 (free nondegeneracy).** For distinct $a,b,c,d \in A$, the relation
> $$(a+b) + (c+d) - (a+c) - (b+d) = 0$$
> is a non-degenerate $S$-unit relation: no proper subsum vanishes.

*Proof.* All four terms are positive, so any vanishing proper subsum contains
one $+$ and one $-$ term. The four possibilities force $b=c$, $a=d$, $a=d$,
$b=c$ respectively; the two triple subsums are non-zero because
$(a+b)+(c+d) > \max\{a+c, b+d\}$. $\square$

Nondegeneracy is normally exactly where these arguments die, so this is worth
recording. It is nonetheless useless for the exponent: after dividing by
$a+c$, Lemma 4 gives a solution of $X + Y - Z = 1$ in $\Gamma$, and the best
uniform bound for non-degenerate solutions of a three-term unit equation in a
group of rank $r$ is Evertse–Schlickewei–Schmidt's
$\exp\big((6n)^{3n}(r+1)\big)$ with $n = 3$, i.e. $\exp(1.98\times 10^{11}\,k)$.
Even after $\binom{n}{4}$ quadruples inject into that solution set, the
resulting bound $\log n \lesssim 5\times10^{10}k$ is worse than Corollary 2 by
eleven orders of magnitude in the slope. **The within-part structure is a
qualitative gift and a quantitative loss.**

## 6. How lossy the reduction is, measured

$g$ and $N_2$ measured inside a bounded universe (both are lower bounds on the
true quantities; the search is exhaustive inside the box):

| $k$ | $g_N(k)$ (this run, exhaustive) | $N_2^{(N)}(k)$ | argmax $c$ | Cor. 2 bound on $g(k)$ |
|---|---|---|---|---|
| 1 | 2 | 1 | 1 | 50 423 |
| 2 | 4 | 7 | 24 | 2 470 631 |
| 3 | 5 | 32 | 10 800 | 121 060 823 |
| 4 | 6 | 75 | 2 520 | 5 931 980 231 |
| 5 | 8 | 141 | 2 520 | $2.9\times10^{11}$ |

Read this as three separate facts. The reduction (col 2 vs col 3) is lossy by
a factor ~18 already at $k=5$ and the gap is widening: the crown is a much
stronger hypothesis than $K_{2,m}$. Evertse's uniform bound (col 5) is
astronomically weaker than the measured $N_2$, as expected of a bound proved
for all number fields and all coefficients. And $N_2^{(N)}$ itself
($1, 7, 32, 75, 141$) is growing far slower than $7^{2k}$, which is a
(bounded-universe, therefore non-probative) sighting of the conjecture in §4.

## 7. Audit of `hunts/r_186989/RESULTS.md`

Everything checkable was checked from scratch; nothing was taken on trust.

**Sound.**
- All seven printed witnesses re-verified by independent trial division: every
  off-diagonal sum is $S$-smooth, sizes $2,4,5,6,8,10,11$ as claimed.
- Independent exhaustive branch-and-bound (different code) reproduces
  $g_N(k) = 2,4,5,6,8$ for $k = 1..5$ **and the identical optimal witnesses**,
  inside boxes 60–1000× smaller than theirs. Their claim that the box is slack
  and the optima live below 50 is confirmed. *(Annotated on landing,
  2026-10-21: the second half did not survive on main. Admissible sets are
  closed under $S$-smooth dilation, so a wider box only adds larger copies of
  the same sets (Hunts #103 and #105), and a primitive extremal 5-set for
  $S=\{2,3,5\}$ reaches 475 (Hunt #107, $\{5,11,25,245,475\}$). What this
  re-run confirms is the table rows and their witnesses.)*
- §2's inequality $f(n-1) \le f_0(n) \le f(n)$ and the $f(2)=1$ vs $f_0(2)=0$
  mismatch: proof read, correct.
- §4's composition-law argument (a supermultiplicative gadget would *refute*
  the conjecture via Fekete, since $g(1) = 2$) is correct, and Corollary 3
  sharpens it: supermultiplicativity would also contradict the expected
  subexponential unit-equation count. The parent should keep treating "find
  the gadget" as a refutation search.
- Their §6 "the top door is the $S$-unit counting bound, and this hunt has no
  purchase on it" is exactly right. This run's contribution is to make that
  door precise enough to walk through: it is $N_2(k)$, uniformly in $c$.

**Refuted.** Loose thread 3, *"$|A| \le p-1$ when $p \notin S$, by pigeonhole
on residues mod $p$ against the pairing $r \leftrightarrow -r$"*, is **false
for every odd $p$**. The pigeonhole works at $p=2$ only, because $2r \equiv 0$
has a non-zero solution mod 2 and none mod odd $p$; several elements may share
one non-zero residue class $r$ with $2r \not\equiv 0$, and nothing forbids it.
Explicit counterexamples, all verified:

| $S$ | $p \notin S$ | claimed cap $p-1$ | actual (exhaustive) | witness |
|---|---|---|---|---|
| $\{2,5\}$ | 3 | 2 | **3** | $1,3,7$ ($4, 8, 10$) |
| $\{2,7\}$ | 3 | 2 | **3** | $1,3,13$ |
| $\{2,5,7\}$ | 3 | 2 | **4** | $1,3,7,13$ |
| $\{2,3,7\}$ | 5 | 4 | **5** | $1,3,5,11,13$ |

So the parity fact ($2 \notin S \Rightarrow |A| \le 2$) is a $p=2$ accident and
is not the seed of an iterable lemma. *(Landing note, 2026-10-21: this thread
was refuted on main before this arm landed, in Hunts #93, #95, #101 and #103;
the third row's witness is the one #95 and #103 use.)* Their door-1 ranking ("parity binds
hardest") stays true as a description of the data; the generalisation does not.

**Unverified.** Rows $k = 6, 7$ of their table were re-verified as witnesses
but their *exhaustiveness* was not re-run here (cost). I have no reason to
doubt it.

## 8. The Győry–Hajdu–Tijdeman line: what it does and does not give

Located: Győry–Hajdu–Tijdeman, *Representation of finite graphs as difference
graphs of $S$-units, I*, J. Combin. Theory Ser. A **127** (2014) 314–335
([arXiv:1408.5873](https://arxiv.org/abs/1408.5873)); *II*, Acta Math. Hungar.
**149** (2016) 423–447; and Hajdu–Tijdeman(-et al.), *On conjectures and
problems of Ruzsa concerning difference graphs of $S$-units*, Acta Math.
Hungar. (2015) ([arXiv:1409.2218](https://arxiv.org/abs/1409.2218)).

**Specialised verdict: these are representability theorems, not counting
theorems, and they do not contain the bound this arm needs.** Their objects are
(i) *which* finite graphs occur as $\mathcal{G}_S(A)$: every finite graph
does, for infinitely many $S$; (ii) *representable with every $S$ iff cubical*;
(iii) induced non-degenerate cycle lengths (the Ruzsa problems). None of these
is of the form $|A| \le F(|S|)$ for a fixed pattern, because for a *fixed*
graph the answer is "yes for suitable $S$" and $|S|$ is allowed to grow. The
one place the line touches ours is the cubical criterion, and its relevance is
the $K_{2,3}$ obstruction noted in §2, which is exactly the pattern
Theorem 1 exploits, so the specialisation is: *the crown leaves the cubical
class through $K_{2,3}$, and the quantitative price of leaving it is
$N_2(k)$.*

Method caveat, stated because it bears on how far to lean: I could not read
either PDF in-session (the fetcher returned undecoded binary), so §8 rests on
the published abstracts plus the standard structure of that literature. The
citations are located, not line-verified. **A reader who needs the exact
theorem numbers must open the papers.** Nothing in §§1–7 depends on §8.

## 9. What I could not settle

- **Whether $\log N_2(k) = o(k)$.** Open, in the unit-equation literature, and
  not settleable at support-run cost.
- **Whether the crown hypothesis is strictly stronger in a usable way.** §6
  shows it is strictly stronger in the data (18× at $k=5$). I found no
  argument that converts the surplus into a better exponent, and §5(c) shows
  the obvious conversion loses.
- **Whether $g(k)$ is polynomially bounded.** The measured $2,4,5,6,8,10,11$
  looks linear, but that is the same seven points `r_186989` correctly refused
  to read a limit out of, and I am refusing likewise.

## The doors

This run measured a ceiling (the exponent in $\log g(k) \le Ck$), so it owes
the list.

**1. Active constraints at the optimum.**

| Rank | What binds | Evidence |
|---|---|---|
| 1 | **The uniform two-term $S$-unit count $N_2(k)$.** Everything else in the chain is exact or nearly so. | Cor. 2's slope $3.892$ is exactly $2\log 7$, i.e. entirely Evertse's constant. |
| 2 | **The step crown $\to K_{2,m}$**, which discards the other $\binom{n}{2}-2(n-2)$ edges. | §6: measured loss $8$ vs $141$ at $k=5$. |
| 3 | The choice of anchor pair (a min over $\binom{n}{2}$ equations). | §5(a); worth at most a constant. |

**2. Frozen-constant inventory.**

| Frozen | Value | What relaxing it trades |
|---|---|---|
| Evertse's $3\cdot 7^{d+2s}$ | slope $2\log 7 = 3.892$ | The only door with real trade shape. Any improvement to the uniform two-term count improves $f(n) \gg \log n$'s constant immediately and linearly; an improvement to $\exp(o(k))$ settles Erdős #126. |
| the number of anchors, $2$ | 2 | §5(b): more anchors = $S$-integral points on $\mathbb{P}^1$ minus $j+1$ points. Constant-factor at best with current technique. |
| the field, $\mathbb{Q}$ | $d=1$ | Already optimal ($d$ enters Evertse's exponent additively). Nothing to buy. |
| the equation's term count, $2$ | 2 | §5(c) prices the 3-term route at $\exp(2\times10^{11}k)$. Do not go there. |
| the search box in §6 | $N \le 10^6$ | Cheap to widen; §7 shows widening moved nothing for $g_N$. Low value. |

**3. Information class.** Doors 2–5 stay **inside** the data the current
argument reads (finite sub-patterns of the $S$-unit difference graph) and are
all capped by $N_2(k)$; none of them can produce $\exp(o(k))$. Door 1,
improving the uniform bound on two-term $S$-unit equations, requires reading
**more**: it is a Diophantine-approximation question (subspace theorem /
quantitative $S$-unit counting), a different information class from anything
enumerable here. That is where the top-ranked door is, and it is not this
lab's door at support cost.

## Loose threads

- **Is the expected $\exp(k^{\theta})$ truth for $S$-unit equations asserted
  uniformly in the coefficients $\alpha,\beta$?** *Why it matters:* Corollary 3
  needs the uniform form; if the expectation is only for $x+y=1$, the
  reduction is weaker than stated. *First step:* Evertse–Győry, *Unit
  Equations in Diophantine Number Theory* (CUP 2015), the chapter on the
  number of solutions; check whether the conjectural upper bound is stated for
  $\alpha x + \beta y = 1$.
- **The crown surplus.** $8$ vs $141$ at $k=5$, and widening. *Why it matters:*
  it is the only measured evidence that the full pattern is much stronger than
  $K_{2,m}$, which is the one place a better-than-$N_2$ bound could come from.
  *First step:* measure $g_N(k)$ against $N_2^{(N)}(k)$ for $k \le 7$ and see
  whether the ratio grows like a power of $k$ or an exponential.
- **$N_2^{(N)}$'s argmax $c$ is $2520$ twice and $10800$ once**, and all three are
  themselves $S$-smooth. *Why it matters:* in the application $c = a_1 - a_2$ is a difference
  of elements of $A$ and is not required to be smooth, so restricting $c$ to
  the realizable set might sharpen Theorem 1. *First step:* recompute
  $N_2^{(N)}$ restricted to $c$ arising as a difference within a maximal $A$.
- **`r_186989`'s OEIS thread is still open.** $2,4,5,6,8,10,11$ was not queried
  here. *(Closed on landing, 2026-10-21: the sibling literature arm ran it.
  The sequence matches twenty OEIS entries, all coincidental, and a keyword
  search for the concept returns nothing; Hunt #143, `support_fcffa3b9` §4.4.)*
