# RESULTS: Erdős #126, literature arm (`support_fcffa3b9`)

**Support run for `0897a5a7` / `r_186989`. A literature map, not a new theorem.**
**Nothing here is evidence for or against RH (`docs/08`).**

Notation throughout, following the parent hunt: $S$ is a set of $k$ primes,
$g(k)$ is the largest $|A|$ over sets $A$ of distinct positive integers all of
whose off-diagonal sums $a+b$ are $S$-smooth, maximised over $S$. Erdős #126
asks whether $f(n)/\log n \to \infty$, equivalently $g(k) = \exp(o(k))$.

**Landing note (2026-10-21).** Landed on main as **Hunt #143** from a
local-only branch, `support/fcffa3b9`, that was never pushed; PR #144 counted
this arm among the seven that "produced no branch at all". The run's brief
assigned #91, which `r_186989` already held, so the run took #92 on its branch;
#92 is `support_517b887f` on main, so the entry takes the next free number.
`HANDBACK.json` keeps the run's own record of #92. The run's files are as it
wrote them apart from punctuation and the dated notes marked as added on
landing.

**Grading (added on landing, 2026-10-21).** This is a literature map from a
**targeted** search (the problem page's bibliography, a forward and backward
citation chase from GST 1986, the $S$-unit counting literature, an OEIS
sequence query and keyword search), not an exhaustive one, and it closes no
route. Primary text was read
for T1, T1′ and T1″ (Erdős–Turán 1934) and for T3 (Győry–Stewart–Tijdeman
1986, including the §3 proof). T2 (Erdős–Surányi's $2^k$) and T5 (the
Erdős–Stewart–Tijdeman constant $1/8$, and with it the $4+o(1)$ of §0 and
§2(d)) are secondary citations through Füredi–Gyarmati 2026 and were not
checked against the originals. T4 (Evertse's $3\cdot7^{2w+3}$) is primary only
as quoted inside GST; T6, T7 and T9 are secondary. Step (a) of §2 is this
lab's ordinary argument, unreviewed and pending external verification; step
(b) is GST's, quoted. Nothing here is kernel-checked, and no test in `tests/`
pins anything in this directory.

**Overlap with arms already on main.** This arm ran in the same fan-out as
Hunts #92 to #107, and most of its mathematics reached main by other routes.
The two-set reduction of §2 is the reduction of Hunts #96
(`support_d5d5ccae`) and #104 (`support_f3ab3e34`), and of three sibling arms
landed with this one (Hunts #97, #99 and #106). §4.2's 3/2-corridor point about
the composition law is Hunt #105's (`support_eccd5f5e`), and Hunt #99
(`support_311c14a5` §5, landed with this one) sharpens it to $g(k)=2^k$
exactly. #105 already cites GST 1986, EST 1988 and Füredi–Gyarmati. The
frozen constant this arm ranks as its door ($|B|=2$) is Hunt #104's first
door (its $m$-base-point version), while Hunt #96 argues that fixing three or
more base elements is strictly worse under current counting bounds, because
the extra coefficients carry primes outside $S$. What this arm adds is the
primary-text reading: GST's reduction quoted from its own proof, the 1934
authors' conjecture $n(k)=O(k^{1+\varepsilon})$ (T1″), the parity argument on
page 1 of the 1934 paper (§4.1), and the negative OEIS check (§4.4) that closes
the OEIS thread Hunts #99 and #106 left open.

---

## 0. The answer, in five lines

1. **The 1934 bound is still the record.** $g(k) \le 3\cdot 2^{k-1} - 1$
   (Erdős–Turán, primary text read). Nothing found in 92 years improves the
   *base* 2; the only improvement located is the constant, to $g(k) \le 2^k$
   (Erdős–Surányi's book, secondary citation).
2. **The $S$-unit machinery is in the literature and it is quantitatively
   worse**, not better: Győry–Stewart–Tijdeman 1986 reproves $f(n) \gg \log n$
   through Evertse's bound and lands at $g(k) \le 3\cdot 7^{2k+3} \approx 49^k$.
3. **It is nevertheless the right lever**, because the whole loss is in one
   named quantity: the number of solutions of a two-variable $S$-unit equation.
   **A uniform bound $\exp(o(|S|))$ on that count implies Erdős #126.** That is
   the closest theorem, and it is a known open problem in Diophantine
   approximation, not a lemma.
4. **That route is not blocked.** Erdős–Stewart–Tijdeman 1988 proves the
   relaxed two-set problem has $\exp\big((4+o(1))\sqrt{k/\log k}\big)$-sized
   witnesses, a hard obstruction to *polynomial* bounds, and still comfortably
   inside $\exp(o(k))$. The entire gap between $\exp(\tilde\Theta(\sqrt k))$ and
   $\exp(O(k))$ is open, and any part of it settles #126.
5. **What Erdős and Turán actually conjectured in 1934 is far stronger than
   #126**: $n(k) = O(k^{1+\varepsilon})$, i.e. $f(n) = n^{1-o(1)}$. #126 is the
   first inch of that.

---

## 1. Citation-checked map

Verification status is stated per row. "primary" = I read the paper text.
"secondary" = stated in a paper I read, but I did not read the original.

| # | Result | Statement | Dependence on $k$ | Status |
|---|---|---|---|---|
| T1 | **Erdős–Turán 1934** (Amer. Math. Monthly **41**, 608–611) | The two-term sums of $3\cdot2^{k-1}$ positive integers cannot all be composed of $k$ given primes. | $g(k) \le 3\cdot2^{k-1}-1$ | **primary** (full text read) |
| T1′ | Erdős–Turán 1934, Thm II | $\omega(n) > \log_2 \pi(n)$-shaped corollary from $A=\{1,\dots,\lceil n/2\rceil\}$ | $f(n) \gg \log n$ | **primary** |
| T1″ | Erdős–Turán 1934, remark | "The bound given in theorem I is probably not exact. The order of the maximum $n(k)$ … is probably $n(k)=O(k^{1+\varepsilon})$ … but actually we cannot prove this relation." | conjectured $k^{1+\varepsilon}$ | **primary** |
| T2 | **Erdős–Surányi**, *Topics in the Theory of Numbers*, Springer 2003 | same conclusion for $\lvert A\rvert \ge 2^k+1$ | $g(k)\le 2^k$ | **secondary** (Füredi–Gyarmati 2026, §1) |
| T3 | **Győry–Stewart–Tijdeman 1986**, *On prime factors of sums of integers I*, Compositio Math. **59**, 81–88, Thm 1 | $A,B$ finite, $\lvert B\rvert\ge 2$, $k=\lvert A\rvert$: $\omega\!\big(\prod_{a\in A,b\in B}(a+b)\big) > c_4\log k$ | $g_2(k)\le 3\cdot7^{2k+3}$ | **primary** (numdam PDF, incl. the §3 proof) |
| T4 | **Evertse 1984**, Invent. Math. **75** (used as GST Lemma 4) | $\lambda x+\mu y=\nu z$ has $\le 3\cdot7^{2w+3}$ coprime triples composed of $w$ given primes | $49^{k}$ | **primary as quoted in T3**; original not read |
| T5 | **Erdős–Stewart–Tijdeman 1988**, *Some Diophantine equations with many solutions*, Compositio Math. **66**, 37–56 | For all $\varepsilon>0$ and large $k$ there are $A$, $B$ with $\lvert A\rvert=k$, $\lvert B\rvert=2$ and $\omega\big(\prod(a+b)\big) < (\tfrac18+\varepsilon)(\log k)^2\log\log k$ | $g_2(w)\ge \exp\!\big((4+o(1))\sqrt{w/\log w}\big)$ | **secondary** (Füredi–Gyarmati 2026, Thm C; independently corroborated by the same paper's own abstract line and by the standard statement of the $S$-unit "many solutions" result) |
| T6 | **Beukers–Schlickewei 1996** | $x+y=1$ in a rank-$r$ group: $\le 2^{8r+8}$; weighted version $2^{9(r+1)}$ | $256^k$ / $512^k$ | **secondary** |
| T7 | **Evertse–Schlickewei–Schmidt 2002** | $a_1x_1+\dots+a_nx_n=1$, non-degenerate: $\le e^{(6n)^{3n}(r+1)}$ | $\exp(c_nk)$, $c_n$ astronomical | **secondary** |
| T8 | Sárközy–Stewart; Balog–Sárközy (cited in T3 §1) | if $A,B \subseteq [1,N]$ are *dense* then $P(a+b)\gg N$ for some pair | n/a | **primary as quoted in T3** |
| T9 | Győry–Sárközy–Stewart 1996, Acta Arith. **74**, 365–385 | prime factors of $ab+1$ | n/a | **secondary** |
| T10 | Füredi–Gyarmati, arXiv:2602.07545 (Feb 2026) | Erdős–Turán over Eulerian integers; $\omega_E > (\log(\lvert A\rvert-1)-\log 18)/\log 2$ | analogue, same $\log$ order | **primary (HTML)** |
| T11 | trivial construction $A=\{1,\dots,m\}$ | all sums $<2m$, so $k=\pi(2m-1)$ | $g(k)\ge(\tfrac12+o(1))\,k\log k$ | **derived here**, matches the $f(n)\ll n/\log n$ on erdosproblems.com/126 |

The problem page (erdosproblems.com/126, accessed 2026-08-24, T. F. Bloom):
**open, $250 prize**, cites only `[ErTu34] [Er95c] [Er97] [Er97e]`, and records
$\log n \ll f(n) \ll n/\log n$ with no intermediate result. A February 2026
paper on the problem (T10) writes the same history and cites no improvement of
T1 or T3 either. That is two independent recent surveys of the same wall.

**No literature result found improves $f(n)\gg\log n$ for the single-set
problem, or the base $2$ in $g(k)$.** The search was targeted (problem page
bibliography, GST-I citation chase forward and back, $S$-unit counting
literature, OEIS), not exhaustive.

---

## 2. The reduction chain, derived rather than cited

Define $g_2(k)$ = the largest $|A|$ such that there exist $b_1 \ne b_2$ with
$a+b_1$ and $a+b_2$ both $S$-smooth for every $a \in A$, $|S| = k$.

**(a) $g(k) \le g_2(k) + 2$.** Take $A$ extremal for $g$, pick $b_1,b_2\in A$,
apply the definition to $A\setminus\{b_1,b_2\}$. $\square$

**(b) $g_2(k) \le N(k)$**, where $N(k)$ is the maximum, over non-zero
$\lambda,\mu,\nu$, of the number of coprime triples $(x,y,z)$ composed of $k$
given primes with $\lambda x+\mu y=\nu z$. This is exactly GST 1986 §3, quoted
verbatim: *"Each element $a_i$ yields a solution $x=a_i+b_1$, $y=a_i+b_2$,
$z=1$ of the equation $x-y=(b_1-b_2)z$."* The triples are coprime because
$z=1$, and distinct $a_i$ give distinct triples. $\square$

**(c) Therefore, conditionally:**

> **If $\log N(k) = o(k)$, then $g(k)=\exp(o(k))$ and Erdős #126 holds.**

The implication direction is one-way. **#126 does not imply the $S$-unit
improvement**: the single-set problem constrains all $\binom n2$ sums while
(b) throws away everything but $2(n-2)$ of them, so $g$ may be far below $g_2$.
Indeed it must be: $g_2(k) \ge \exp(c\sqrt{k/\log k})$ by T5, while T1 already
gives $g(k)\le 3\cdot2^{k-1}$. The two-set relaxation is genuinely lossy, and
that loss is why the $S$-unit route ($49^k$) is worse than the 1934 elementary
argument ($2^k$) despite being the deeper machinery.

**(d) The room, stated precisely.** For the *two-set* quantity the literature
brackets

$$\exp\big((4+o(1))\sqrt{k/\log k}\big) \;\le\; g_2(k) \;\le\; 3\cdot7^{2k+3},$$

lower bound T5, upper bound T3+T4. Every value in that range is
$\exp(o(k))$ except the top end. So: **the $S$-unit route has enough headroom
to settle #126 and is not obstructed by any known construction.** What it
cannot do is prove the 1934 authors' own conjecture $g(k)=O(k^{1+\varepsilon})$:
T5 kills polynomial bounds for $g_2$ outright, so that stronger target needs
an argument using more than two of the elements.

---

## 3. Does each bound help? One line each

| Bound | Helps? | Why |
|---|---|---|
| T1 Erdős–Turán $3\cdot2^{k-1}$ | **it is the incumbent** | Only bound of the right shape. The base 2 comes from the halving lemma: per prime $p$, one keeps the residues in $(0,p/2)$, and density $1/2$ is *exactly optimal* for "no two distinct elements sum to $0 \bmod p$" (the interval attains it). So no per-prime improvement exists; beating $2^k$ needs a joint argument over the primes, not a better lemma. |
| T2 Erdős–Surányi $2^k$ | marginal | Constant factor $3/2$. Same base. |
| T3 GST Thm 1 | **structurally, yes; numerically, no** | Gives $49^k$, worse than $2^k$. Its value is that it isolates the bottleneck into one counting problem and shows $\lvert B\rvert=2$ suffices. |
| T4 Evertse $3\cdot7^{2w+3}$ | **the single lever** | $\exp(o(k))$ here $\Rightarrow$ #126, by §2(c). |
| T6 Beukers–Schlickewei | no | $2^{9(r+1)} = 512^k$; worse than T4 for this application. Cleaner proof, same shape. |
| T7 Evertse–Schlickewei–Schmidt ($n$-term) | no | $e^{(6n)^{3n}(r+1)}$. Needed only if one uses the 4-element identity $(a+c)+(b+d)=(a+d)+(b+c)$ instead of GST's 3-term one; that route is strictly worse. |
| T5 EST 1988 | **yes, as a map** | Proves where the route's ceiling is: no polynomial bound on $g_2$. Leaves all of $\exp(k^{1/2+o(1)}) \ldots \exp(o(k))$ open. |
| Effective height bounds (Baker; van der Poorten; Győry–Yu; Bugeaud–Győry; Le Fourn) | **no** | They bound the *size* of solutions, and the problem is a *counting* problem. See §5 for the one place they looked useful and were not. |
| T8 Balog–Sárközy, Sárközy–Stewart (circle method / large sieve) | no | Require $A,B$ dense in $[1,N]$. The extremal sets here are extraordinarily sparse (parent hunt: every optimal witness is $<50$ with $N$ up to $2\cdot10^5$; *annotated on landing, see the note below this table*). Wrong regime. |
| T9, T10 | no | Different forms ($ab+1$; Eulerian integers). T10 is an analogue at the same $\log$ order, using T1's own method. |

*Landing note on the T8 row (2026-10-21).* Its parenthetical relies on
`r_186989`'s "every optimal witness lives below 50", which did not survive on
main: admissible sets are closed under $S$-smooth dilation, so a wider box only
adds larger copies of the same sets (Hunts #103 and #105), and a primitive
extremal 5-set for $S=\{2,3,5\}$ reaches 475 (Hunt #107, $\{5,11,25,245,475\}$).
This note withdraws that evidence only; the row's verdict is the run's.

---

## 4. Audit of `hunts/r_186989/RESULTS.md`

Audited as instructed, not trusted. Four findings.

1. **Arm 2's headline is 1934 knowledge, verbatim.** The parent reports as a
   measured discovery that dropping 2 from $S$ is catastrophic. Erdős–Turán's
   first page: *"Plainly we can suppose $p_1=2$, because if the $p_1,\dots,p_k$
   are all odd, we find $n\le2$."* Same parity argument, same conclusion. The
   parent's proof is correct; its novelty is nil. Their loose thread
   "prove $|A|\le p-1$ when $p\notin S$" is subsumed by the Erdős–Turán lemma,
   which does the general-$p$ case as a halving, not a cap. *(Annotated on
   landing, 2026-10-21: the proposed cap is in fact false for every odd $p$,
   because many elements may share one nonzero residue class; it was refuted
   on main before this arm landed, in Hunts #93, #95, #101 and #103; the
   witness $A=\{1,3,7,13\}$, $S=\{2,5,7\}$ used by #95 and #103 sits in
   `r_186989`'s own table.)*
2. **Arm 3's kill is right, and stronger than the parent claims.**
   Supermultiplicativity would give $g(k)\ge 2^k$, which must live inside
   T1's $3\cdot2^{k-1}-1$, a corridor of relative width $3/2$. So a
   composition law would not merely refute #126, it would force the 1934 bound
   to be sharp up to a constant, against the explicit expectation of its own
   authors ($n(k)=O(k^{1+\varepsilon})$, T1″). The parent should record that its
   arm-3 gadget contradicts a published conjecture as well as #126.
3. **The measured table is below the trivial literature construction
   asymptotically.** $A=\{1,\dots,m\}$ gives $g(k)\ge(\frac12+o(1))k\log k$
   (T11), so $g$ is superlinear for free. The parent's $2,4,5,6,8,10,11$ beat
   $\{1,\dots,m\}$ at each measured $k$ (e.g. $k=7$: $11$ vs $9$) but the
   sequence carries no asymptotic information the literature lacks. Their own
   "seven points decide nothing" verdict stands and is if anything generous.
4. **The OEIS thread is closed, negatively.** `2,4,5,6,8,10,11` matches 20
   OEIS sequences, all coincidental (top hit A340932, "numbers whose least
   prime index is odd"). A keyword search for the concept returns nothing.
   No tabulation of $g(k)$ exists in OEIS.

The parent's "top-ranked door is the $S$-unit counting bound, and this hunt has
no purchase on it at scout cost" is **correct**, and §2 above makes it precise:
the door is $\log N(k)=o(k)$, and the room to walk through it is proved to
exist by T5.

---

## 5. What I could not settle

- **Is $\log N(k)=o(k)$ conjectured true?** T5 shows the count can be as large
  as $\exp(c\sqrt{k/\log k})$, and it is folklore-plausible that this is close
  to the truth, but I did not find an explicit conjecture in a source I read.
  Settling this costs one look at Evertse–Győry, *Unit Equations in Diophantine
  Number Theory* (CUP 2015), Ch. 6, a book I could not access in-session.
  **This matters:** if the subexponential bound is a stated conjecture of the
  field, then #126 is a corollary of a believed conjecture, which changes how
  the problem should be briefed.
- **Is $\max A$ effectively bounded in terms of $S$?** This is the parent's
  thread "the optima are all tiny". The obvious route is circular: effective
  $S$-unit bounds (Baker/Győry–Yu) bound $\max(x,y)$ for $\lambda x+\mu y=\nu z$
  in terms of the height of the coefficients, and here $\nu = b_1-b_2$ is itself
  bounded only by $\max A$. Whether a non-circular effective bound exists, which
  would turn the parent's bounded search into an exact computation of $g(k)$, I
  could not decide in the time. *(Annotated on landing, 2026-10-21: answered
  in part on main. Hunt #107 measured that the height of a primitive
  admissible set of sub-extremal size is unbounded at $S=\{2,3\}$, tracking the
  search cutoff over eleven orders of magnitude, so no such bound holds below
  extremal size. Whether sets of extremal size have bounded height is still
  open there, and Hunt #103 states uniformly bounded height as a conjecture.)*
- **T2 and T5 are secondary citations.** Both come from Füredi–Gyarmati 2026,
  a peer of ours rather than the source. T5's constant $1/8$ and T2's $2^k+1$
  should be checked against Compositio Math. 66 and the Erdős–Surányi book
  before either is leaned on.

## The doors

This run mapped a ceiling (the 92-year wall at $\log n$), so it owes the list.

**1. Active constraints.**

| Rank | What binds | Evidence |
|---|---|---|
| 1 | **The count $N(k)$ of two-variable $S$-unit solutions.** Every exponential in every route passes through it. | GST §3: $g_2(k)\le N(k)$, and $N(k)\le 49^k$ is the only input. |
| 2 | **The per-prime halving in Erdős–Turán.** Density $1/2$ is extremal for residue sets avoiding $r+r'\equiv0$, so the base 2 is the lemma's exact price, paid $k$ times. | ET34 §2 lemma; the interval $(0,p/2)$ attains the density. |
| 3 | **The two-set relaxation is lossy.** Discarding $\binom n2 - 2(n-2)$ sums is what makes the deep machinery weaker than the 1934 argument. | $49^k$ vs $2^k$; T5 says the relaxation's own truth is $\exp(\tilde\Theta(\sqrt k))$. |

**2. Frozen constants.**

| Frozen | Value | What relaxing it trades |
|---|---|---|
| $\lvert B\rvert = 2$ in the GST reduction | 2 | Using 3 or more fixed elements gives a *system* of unit equations rather than one, with more structure and no off-the-shelf count. **This is the door with genuine trade shape**: T5's obstruction is stated for $\lvert B\rvert=2$ and says nothing about $\lvert B\rvert=3$. |
| Evertse's constant $7^{2}$ | 49 | Improving it improves the constant in $f(n)\gg\log n$ and nothing else. Only a subexponential-in-$k$ improvement changes the answer. |
| the halving density $1/2$ | $1/2$ | Provably extremal per prime; the only relaxation is to stop treating the primes one at a time. |
| "coprime triples" in Evertse's lemma | n/a | Not slack: GST's application has $z=1$, so coprimality is free. |

**3. Information class.** Door 1 (better $N(k)$) and door 2 ($\lvert B\rvert\ge3$)
both stay inside Diophantine-approximation data and are where the field's tools
already point. The halving door requires reading something the current
arguments do not: joint information across the $k$ primes about a single set of
integers: an inverse-theorem or entropy statement, not a unit-equation count.
That door is the only one that could reach the 1934 authors' own conjecture
$g(k)=O(k^{1+\varepsilon})$, since T5 blocks the unit-equation route from ever
proving a polynomial bound.

---

## Sources

- T. F. Bloom, *Erdős Problem #126*, https://www.erdosproblems.com/126, accessed 2026-08-24.
- P. Erdős, P. Turán, *On a problem in the elementary theory of numbers*, Amer. Math. Monthly **41** (1934), 608–611. https://combinatorica.hu/~p_erdos/1934-03.pdf (read in full).
- K. Győry, C. L. Stewart, R. Tijdeman, *On prime factors of sums of integers I*, Compositio Math. **59** (1986), 81–88. http://www.numdam.org/item/CM_1986__59_1_81_0/ (read in full).
- P. Erdős, C. L. Stewart, R. Tijdeman, *Some Diophantine equations with many solutions*, Compositio Math. **66** (1988), 37–56.
- P. Erdős, J. Surányi, *Topics in the Theory of Numbers*, Springer, 2003.
- E. Füredi, K. Gyarmati, *Erdős–Turán Theorem and Eulerian Integers*, arXiv:2602.07545 (Feb 2026).
- J.-H. Evertse, *On equations in S-units and the Thue–Mahler equation*, Invent. Math. **75** (1984). GST's reference [6], the source of their Lemma 4. GST's reference list was truncated in the scan I read at entry [4], so the exact title/pages of [5] and [6] are inferred from the standard bibliography and are **not** citation-checked.
- F. Beukers, H. P. Schlickewei, *The equation x+y=1 in finitely generated groups*, Acta Arith. (1996).
- J.-H. Evertse, H. P. Schlickewei, W. M. Schmidt, *Linear equations in variables which lie in a multiplicative group*, Ann. of Math. **155** (2002).
- K. Győry, *Some recent applications of S-unit equations*, Astérisque **209** (1992), 17–38.
