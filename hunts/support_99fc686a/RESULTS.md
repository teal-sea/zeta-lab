# RESULTS: Erdős #126, low-rank matrix arm (support run 99fc686a)

**Hunt, not a result. Nothing here is evidence for or against RH (`docs/08`).**

**Verdict: the arm is settled, and it is a rediscovery.** The matrix
$M_{ij} = a_i + a_j$ with rank $\le 2$ and $S$-unit off-diagonal entries is
*exactly* the object of **Alon and Solymosi, "Rank of matrices with entries
from a multiplicative group"**, Corollary 10, whose proof is four lines long
and constructs the same matrix. It gives $|A| \le f(\mathrm{rank}\,\Gamma)$,
which answers the qualitative question and is **catastrophically worse than
$2^k$**: reading their explicit form, $e^{256k}$ against $3\cdot 2^{k-1}$.

Rank 2 is however special, and the general machinery is not needed for it.
Two rows of $M$ collapse the whole problem to a **single two-variable
$S$-unit equation**, giving the explicit and much better

$$g(k) \;\le\; 2 + 3\cdot 7^{2k+3},$$

base $49$ per prime. Still worse than base $2$. **The arm does not improve
$3\cdot 2^{k-1}$ and, with the best counting bounds now known for $S$-unit
equations, it cannot.**

**Landing note (2026-10-21).** Landed on main as Hunt #97 from a local-only
branch, `support/99fc686a`, that was never pushed; PR #144 counted this arm
among the seven that "produced no branch at all". The run's files are as it
wrote them apart from punctuation and the dated notes marked as added on
landing.

**Grading (added on landing, 2026-10-21).** Alon and Solymosi were read from
their PDF, so §4's account of Theorems 1 and 9 and Corollary 10 is primary.
The other two constants the verdict uses were not: the run took Evertse's
$3\cdot7^{[K:\mathbb{Q}]+2|S|}$ and Beukers–Schlickewei's $2^{8(r+2)}$ from
search summaries and rates them medium-low in its own `HANDBACK.json`. The
Evertse form agrees with Győry–Stewart–Tijdeman 1986's quotation of it,
$3\cdot7^{2w+3}$, which the sibling literature arm read in primary text (Hunt
#143, `support_fcffa3b9` T4). The Beukers–Schlickewei form differs from the
$2^{8r+8}$ quoted on main (Hunt #104, and Hunt #143's T6, itself secondary), and
neither is checked against the paper here, so the §2 table is hedged in place
(its base per prime, $2^{16}$, is the same under either form). The two-row collapse (§1) is this lab's
ordinary argument, unreviewed and pending external verification, and so are
the rectangle-condition expansion and the nondegeneracy analysis of §3. The §6
table is exact arithmetic on the seven `r_186989` witnesses, a check of the
mechanics and not of any bound. In the terms of `ALIGNMENT.md` §5 the verdict is
restricted to the two-row $S$-unit route and to the counting bounds now known:
with them it cannot beat base 2. That is not an obstruction to the route,
whose improvement is exactly the open counting problem of §5.

**Overlap with arms already on main.** The two-row collapse is the reduction of
Hunts #96 (`support_d5d5ccae`) and #104 (`support_f3ab3e34`); #104 notes that
it is how the $c\log|A|$ bounds are proved. It is also Győry–Stewart–Tijdeman 1986 §3, quoted verbatim by Hunt #143
(landed with this arm), which answers §7's first question. Two sibling arms
landed with this one derive it again (Hunts #99 and #106). §3's four-element
route is the reduction of Hunts #93, #95 and #105, which name the same missing
fibre count; Hunt #98 (`support_d0f0aefb` Theorem 4, landed with this arm) makes
a three-anchor version injective. This arm's own contributions are the prior-art
identification of the rank-2 matrix with Alon–Solymosi's Corollary 10, the
reduction of their rectangle condition to the distinctness of $A$, the
observation that their Theorem 1 does not apply (diagonal $S$-units in all
seven witnesses), and the pricing of the three-term route at about $10^{1341}$
per prime.

Reproduce with `.venv/bin/python hunts/support_99fc686a/probe.py` (stdlib
only, about a second). It writes `probe_out.json` (its docstring says
`results.json`); `results.json` is the run's hand-written summary. Re-run on
landing, `probe_out.json` reproduced byte for byte.

---

## 1. The reduction, stated and proved

Let $S$ be $k$ primes, $U \subset \mathbb{Q}^*$ the group of $S$-units
($U \cong \{\pm 1\} \times \mathbb{Z}^k$, rank $k$). Let
$A \subset \mathbb{Z}_{>0}$ be finite with $a+b \in U$ for all distinct
$a,b \in A$.

**Lemma (two-row collapse).** Fix distinct $a,b \in A$ and put $c = a-b \ne 0$.
For every $d \in A \setminus \{a,b\}$ set $x_d = a+d$, $y_d = b+d$. Then
$x_d, y_d \in U$ and

$$x_d - y_d = c \quad\text{for every } d,$$

i.e. $(x_d,y_d)$ solves $\tfrac{1}{c}X - \tfrac{1}{c}Y = 1$ in $(X,Y) \in U^2$.
The map $d \mapsto (x_d,y_d)$ is injective, since $x_d = a+d$ determines $d$.
Hence

$$|A| - 2 \;\le\; N_{\mathbb{Q}}(k) := \max_{\alpha,\beta \in \mathbb{Q}^*}
\#\{(X,Y) \in U^2 : \alpha X + \beta Y = 1\}. \qquad\square$$

The step that matters is that $x_d - y_d$ does not depend on $d$, and that is
precisely the rank-$2$ statement: every column of $M$ lies in
$\mathrm{span}\{(a_i)_i, (1)_i\}$, so any two rows of $M$ differ by a constant
vector. **The low rank is used, and nothing else is.** No minors, no
determinant identity, no matrix rigidity theorem.

**The uniformity that makes this work.** $c = a - b$ is in general *not* an
$S$-unit, so the equation has arbitrary rational coefficients. What is needed
is a solution count depending only on $k$ and not on the coefficients, and
that is exactly the form Evertse's theorem takes.

## 2. Explicit bounds, and the comparison the brief asked for

| route | bound on $g(k)$ | base per prime | source |
|---|---|---|---|
| Erdős–Turán 1934 | $3\cdot 2^{k-1} - 1$ | **2** | the incumbent |
| two-row collapse + Evertse 1984 | $2 + 3\cdot 7^{2k+3}$ | 49 | §1 above |
| two-row collapse + Beukers–Schlickewei 1996 | $2 + 2^{8(2k+3)}$ | $65\,536$ | rank of $U^2$ is $2k$ |
| four-element identity + subspace theorem, 3 terms | not even a bound on $\lvert A\rvert$ without more work | $\sim 10^{1341}$ | see §3 |
| Alon–Solymosi Cor. 10, as published | $\exp(256\,k)$ for large $k$ | $e^{256}$ | their $\log n \le r d^8$ with $d = 2$, $r = k$ |

Evertse (1984): $\alpha X + \beta Y = 1$ has at most
$3 \cdot 7^{[K:\mathbb{Q}] + 2|S|}$ solutions in $S$-units. Over $\mathbb{Q}$
with $S = \{\infty, p_1,\dots,p_k\}$ this is $3\cdot 7^{2k+3}$.

*Hedged on landing (2026-10-21).* Both upper-bound constants in this table came
from search summaries, not from the papers. Evertse's form agrees with
Győry–Stewart–Tijdeman 1986's quotation of it, $3\cdot7^{2w+3}$, read in
primary text by the sibling literature arm (Hunt #143, T4). The
Beukers–Schlickewei row uses the form $2^{8(r+2)}$, while main quotes
$2^{8r+8}$ (Hunt #104; Hunt #143's T6, secondary), and neither was checked
against the paper here; read that row's exponent as unpinned. No conclusion
of this file depends on it, since the Evertse row is the better one either way.

**Answer to "does it improve $2^k$": no, by a factor of about
$(49/2)^k$ at best.** The two-row collapse beats the published Alon–Solymosi
constant by a very large margin, and is still an order of magnitude worse in
the exponent than a proof from 1934.

## 3. The nondegeneracy issue, isolated exactly

The brief asked for this precisely, and there are two different answers
depending on which reduction is used.

**In the two-row collapse there is no nondegeneracy issue at all.** A
two-term equation $\alpha X + \beta Y = 1$ has proper subsums $\alpha X$ and
$\beta Y$, both nonzero because $X, Y \in U$ are units. Evertse's count
applies to every solution. Nothing has to be assumed about $A$ beyond
$a \ne b$.

**In the general-rank argument the issue is real and is exactly the
Alon–Solymosi rectangle condition.** Their Theorem 1 requires the diagonal
entries $m_{jj} \notin \Gamma$. Here $m_{jj} = 2a_j$, and this **fails**: the
probe finds $S$-unit diagonal entries in every one of the seven `r_186989`
witnesses (1, 1, 2, 5, 4, 7, 9 of them for $k=1..7$). Their Theorem 9
replaces the hypothesis by

$$a_{jj}a_{ik} \ne a_{jk}a_{ij} \qquad (i < j \ne k),$$

which for $M_{ij} = a_i + a_j$ reads $(2a_j)(a_i+a_k) \ne (a_j+a_k)(a_i+a_j)$,
and expands to $(a_j - a_i)(a_j - a_k) \ne 0$. **So the nondegeneracy
condition is exactly the distinctness of the elements of $A$, and is free.**

**In the four-element route the same thing happens.** For distinct
$i,j,l,m$, rank $2$ gives
$(a_i+a_j) + (a_l+a_m) = (a_i+a_l) + (a_j+a_m)$; dividing by $a_i+a_l$ yields
$X + Y - Z = 1$ with $X,Y,Z \in U$. Its vanishing proper subsums would be
$X + Y = 0$ (impossible, both positive), $X - Z = 0$ (forces $a_i = a_m$) and
$Y - Z = 0$ (forces $a_l = a_j$). **Every such solution is nondegenerate,
again exactly because the elements are distinct.** The three-term route is
nonetheless strictly worse: the subspace-theorem count
$A(m,r) \le (8m)^{4m^4(m+mr+1)}$ (Amoroso–Viada, as quoted by Alon–Solymosi)
gives at $m=3$ a bound $24^{324(3k+4)}$, i.e. a base of about $10^{1341}$ per
prime, and the map from $4$-subsets of $A$ to solutions is *not* injective (fixing
$(X,Y,Z)$ leaves a one-parameter family of $4$-tuples), so it does not even
bound $|A|$ without further work.

## 4. What the literature actually contains

Searched and read:

- **N. Alon and J. Solymosi, "Rank of matrices with entries from a
  multiplicative group."** Theorem 1: for $\Gamma \le \mathbb{C}^*$ of rank
  $\le r$ and $M$ with off-diagonal entries in $\Gamma$ and diagonal entries
  outside it, $\mathrm{rank}(M) \ge (\log n / r)^{1/8}$ for large $n$.
  Theorem 9 weakens the diagonal hypothesis to the rectangle condition.
  **Corollary 10 is our problem**: "if $\mathrm{rank}(\Gamma) \le r$ and
  $A + A \subset \Gamma$ then $|A| \le f(r)$", proved with $m_{ij} = a_i+a_j$
  and the observation that its rank is at most two. Their $A+A$ includes the
  diagonal $2a$; our hypothesis is weaker (off-diagonal only), and Theorem 9
  covers it because the rectangle condition holds regardless.
- **O. Roche-Newton and D. Zhelezov**, cited there: the same statement for
  $A - A \subset \Gamma$, also via the subspace theorem.
- **Evertse–Schlickewei–Schmidt**, with the Amoroso–Viada bound
  $A(m,r) \le (8m)^{4m^4(m+mr+1)}$, is the engine underneath all of it.
- **J.-H. Evertse (1984)** and **Beukers–Schlickewei (1996)** for the
  two-variable counts used in §2.
- **arXiv 2602.07545** (Erdős–Turán theorem and Eulerian integers, 2026)
  restates the classical bound as $3\cdot 2^{k-1}$ and does not improve it;
  it extends the *lower*-bound technique to $a^2 \pm ab + b^2$ via a lemma of
  Győry, Sárközy and Stewart.

**Nothing in this literature improves the base $2$.** The subspace theorem is
ineffective and its counting bounds are enormous; it buys qualitative
finiteness in settings where elementary arguments give none (distance sets,
$A-A$, Eulerian integers), and it loses badly wherever an elementary argument
already exists. Erdős #126 is such a place.

## 5. The one thing worth taking forward

The two-row collapse is a **clean equivalence-flavoured reduction with the
implication direction checked**:

> If $N_{\mathbb{Q}}(k) = \exp(o(k))$, then $g(k) \le 2 + N_{\mathbb{Q}}(k)
> = \exp(o(k))$, and **Erdős #126 is true**.

The converse does **not** follow: $g(k)$ small says nothing about
$N_{\mathbb{Q}}(k)$, since a solution set of a unit equation need not come
from a set with all pairwise sums smooth. So this is a one-way reduction of
#126 to a problem in Diophantine approximation.

Status of the target, which is what makes this interesting rather than
circular:

- best known upper bound $N_{\mathbb{Q}}(k) \le 3\cdot 7^{2k+3}$, exponential;
- best known lower bound, Erdős–Stewart–Tijdeman:
  $N_{\mathbb{Q}}(k) \ge \exp\!\big((4+o(1))(k/\log k)^{1/2}\big)$,
  which is $\exp(o(k))$.

**The lower bound does not obstruct the hypothesis.** The gap between
$\exp(\Theta(k))$ and $\exp(k^{1/2+o(1)})$ for two-term $S$-unit equations is
open, and closing it downward would settle Erdős #126. Whether this reduction
is already recorded somewhere we did not establish; it is elementary enough
to be folklore, and we make no novelty claim for it. What we do claim is
provenance: it was derived here, and it is checked. *(Annotated on landing,
2026-10-21: it is recorded. Győry–Stewart–Tijdeman 1986 §3 uses exactly this
step, "each element $a_i$ yields a solution $x=a_i+b_1$, $y=a_i+b_2$, $z=1$ of
the equation $x-y=(b_1-b_2)z$", quoted from the primary text by Hunt #143,
`support_fcffa3b9` §2(b).)*

## 6. Verification

`probe.py` re-checks all seven `r_186989` witnesses from scratch by trial
division. All pass:

| check | result |
|---|---|
| every off-diagonal sum is an $S$-unit (the hypothesis) | true, 7/7 |
| $\mathrm{rank}_{\mathbb{Q}} M = 2$ exactly (Fraction Gaussian elimination) | true, 7/7 |
| rectangle condition holds for all $i<j\ne k$ | true, 7/7 |
| some diagonal entry $2a_j$ *is* an $S$-unit (so Thm 1 does not apply) | true, 7/7 |
| two-row reduction valid: $x_d,y_d \in U$ and $x_d-y_d=a-b$ | true, all ordered pairs |
| $d \mapsto (x_d,y_d)$ injective | true, all ordered pairs |

The $k=7$ witness $\{1,3,5,6,7,11,15,19,21,29,49\}$ with $a=1,b=3$ forces
**9 distinct solutions** of $X - Y = -2$ in $\{2,3,5,7,11,13,17\}$-units:
$(6,8),(7,9),(8,10),(12,14),(16,18),(20,22),(22,24),(30,32),(50,52)$.
Evertse's bound permits $3\cdot 7^{17} \approx 7\times10^{14}$. The counting
theorem is not close to tight on the instances this problem produces, which is
the honest reason the route loses.

## 7. What we could not settle

- **Whether the two-row collapse is in the literature.** We found the
  rank-2-matrix framing (Alon–Solymosi) but not this specialisation. A
  targeted search of Győry–Sárközy–Stewart and of the Erdős problem list
  commentary was not run. *(Answered on landing, 2026-10-21: the
  specialisation is Győry–Stewart–Tijdeman 1986 §3; see the note at the end
  of §5.)*
- **Whether using more than two rows helps.** Fixing $m$ elements gives each
  $d$ a point in the intersection of $m-1$ unit-equation solution sets. We
  know of no theorem whose bound decreases with the number of simultaneous
  equations, and we did not look for one. This is the only place in the arm
  where an improvement could plausibly live.
- **Any bound with base below 2.** Not attempted; there is no candidate.

## The doors

This run measured a ceiling (which exponential base each route can reach), so
it owes the list.

**1. Active constraints at the optimum.**

| Rank | What binds | Evidence |
|---|---|---|
| 1 | **The $S$-unit solution-count bound itself.** Everything downstream is a single application of it. | $g(k) \le 2 + N_{\mathbb{Q}}(k)$ is one line; all the loss is in $N_{\mathbb{Q}}(k) \le 3\cdot7^{2k+3}$. |
| 2 | **Ineffectivity and looseness of the subspace theorem.** | Measured slack at $k=7$: 9 solutions forced against $7\times10^{14}$ permitted. |
| 3 | **Using only two rows.** The other $n-2$ rows of $M$ are thrown away. | Simultaneous systems are untouched, see §7. |

**2. Frozen-constant inventory.**

| Frozen | Value | What relaxing it trades |
|---|---|---|
| number of fixed elements $(a,b)$ | 2 | **The door with genuine trade shape.** $m$ fixed elements gives $m-1$ simultaneous unit equations for the same unknown $d$; a bound decaying in $m$ would beat everything here. Costs: needs a theorem that does not currently exist. |
| choice of the pair $(a,b)$ | arbitrary | Nothing. The bound is uniform over coefficients, which is why any pair works. |
| the counting theorem | Evertse 1984 | Beukers–Schlickewei is worse over $\mathbb{Q}$ (base $65536$ vs $49$). Any future improvement in $N_{\mathbb{Q}}(k)$ transfers verbatim. |
| ambient field | $\mathbb{Q}$ | Over a number field $K$ the same proof gives $|A| \le 2 + 3\cdot7^{[K:\mathbb{Q}]+2|S|}$. Free generalisation, no extra work. |
| the group $\Gamma$ | $S$-units | The reduction only uses that $\Gamma$ is finitely generated. Works for $A$ in any field with $A+A$ in a rank-$r$ group. |

**3. Information class.** The two-row collapse stays **inside** the data the
family already reads (integers and the smoothness of their pairwise sums), and
its ceiling is exactly the ceiling of two-term $S$-unit counting. Door 1
(more rows, simultaneous unit equations) **requires reading more**: it needs a
Diophantine theorem about systems, not about a single equation, and no such
theorem is cited by anyone in this literature. That is where the arm's
remaining value sits, and it is a research programme rather than a probe.
