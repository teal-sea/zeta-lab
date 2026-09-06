# RESULTS: red-team audit of the Erdős #126 scout (`r_186989`)

**Hunt, not a result. Nothing here is evidence for or against RH (`docs/08`).**

**Verdict: the scout's mathematics survives. Its literature claim and one of its
loose threads do not.** Five of the six audited claims are correct as stated and
are re-proved below. One thread (`|A| \le p-1$ for omitted $p$`) is **false**,
and is contradicted by a row of the scout's own table. The "no progress beyond
1934" framing is **misleading**: the order of magnitude is indeed unimproved,
but there is directly relevant literature from 1986, 1988 and February 2026 that
the scout cites none of, and one of those papers bears on whether the route it
recommends can work at all.

Reproduce with `python3 hunts/support_eccd5f5e/audit.py` (~4 min, stdlib only,
writes `results_audit.json`). The search was written from the problem statement,
not from `hunts/r_186989/probe.py`.

Notation throughout: $S$ a set of $k$ primes, $A$ a finite set of distinct
positive integers with every off-diagonal sum $a+b$ being $S$-smooth,
$g(k) = \max |A|$, and $f(n) = \min_{|A|=n} \omega\!\left(\prod_{a\neq b}(a+b)\right)$.

---

## 0. The scoreboard

| # | Scout claim | Verdict |
|---|---|---|
| 1 | $g(k) = \max\{n : f(n)\le k\}$, and $f(n)/\log n\to\infty \iff g(k)^{1/k}\to 1$ | **Verified.** Two hypotheses were load-bearing and unflagged. |
| 2 | $f(n-1)\le f_0(n)\le f(n)$, positivity mismatch harmless for the limit | **Verified**, proof correct. Sharpened: $f(1..4)$ are now *exactly* known. |
| 3 | A supermultiplicative composition law refutes the conjecture | **Verified**, and stronger than stated: such a law would also be within a factor $3/2$ of the 1934 upper bound. Fekete is not needed. |
| 4 | $g_N(k) \ge 2,4,5,6,8,10,11$ for $k=1..7$; box size does not bind | **Reproduced independently.** Interpretation corrected on two points. |
| 5 | Thread: $\|A\|\le p-1$ when $p\notin S$, by pigeonhole on $r \leftrightarrow -r$ | **Refuted.** Proof of why, plus a counterexample inside the scout's own data, plus an unbounded family. |
| 6 | "No progress beyond 1934" | **Misleading.** Corrected in §6 with sources. |

---

## 1. The inverse reformulation. Verified.

$f(n)\le k$ means some $n$-set has prime support of size $\le k$; padding that
support to exactly $k$ primes gives $g(k)\ge n$. Conversely a witness for $S$
with $|S|=k$, $|A|=n$ gives $f(n)\le k$. So $g(k)=\max\{n : f(n)\le k\}$. If
$f(n)/\log n\to\infty$ then with $n_k=g(k)$ we have $k\ge f(n_k)$, so
$k/\log n_k\to\infty$, i.e. $\log g(k)=o(k)$. Conversely with $k=f(n)$ we get
$g(k)\ge n$, so $\log n \le \log g(f(n)) = o(f(n))$. Both directions hold, and
$\log g(k) = o(k) \iff g(k)^{1/k}\to 1$ is immediate. $\square$

**Two hypotheses are load-bearing and the scout does not flag them.** The
forward direction needs $g(k)\to\infty$ and the reverse needs $f(n)\to\infty$;
both come from Erdős-Turán, so the *equivalence itself* is conditional on the
1934 theorem, not merely the finiteness of $g$. Also, the scout writes that $g$
is finite "precisely because the classical $f(n)\gg\log n$ holds". Finiteness
needs only $f(n)\to\infty$, which is strictly weaker. Cosmetic, but "precisely
because" is doing work it has not earned.

## 2. The positivity equivalence. Verified, and sharpened.

The scout's proof of $f(n-1)\le f_0(n)\le f(n)$ is correct as written; we
checked each step and found no gap. Independent exhaustive recomputation over
$[1,30]$ and $[0,30]$ reproduces its table exactly:
$f = 0,1,2,2,3$ and $f_0 = 0,0,2,2,3$ for $n=1..5$.

**Sharpening the scout left on the table.** It reports these as search upper
bounds. Four of them are in fact exact and provable:

- $f(1)=0$ (no off-diagonal sums), $f(2)=1$ (the least sum of two distinct
  positives is $3$, so the support is non-empty; $\{1,2\}$ attains $1$).
- $f(3)=2$: three distinct positives cannot have all three pairwise sums powers
  of one prime $p$. For odd $p$, two of the three share a parity and their sum is
  even. For $p=2$, with $a<b<c$ and $a+b=2^x<a+c=2^y<b+c=2^z$ we get
  $2a = 2^x+2^y-2^z \le 2^x-2^y<0$. Witness $\{1,3,5\}$ gives $2$.
- $f(4)=2$: $f(4)\ge f(3)=2$ by monotonicity, and $\{1,5,7,11\}$ with
  $S=\{2,3\}$ attains $2$.
- $f(5)=3$ **is not proved**. $f(5)\le 3$ is a witness; $f(5)\ge 3$ is exactly
  the statement $g(2)\le 4$, which nothing in either hunt establishes. See §7.

So the honest small-$n$ table is $f = 0,1,2,2$ known exactly, and $f(5)\in\{3\}$
conditional on $g(2)=4$.

## 3. The Fekete / composition claim. Verified, and it is stronger than stated.

The scout's argument is sound: $g(1)=2$ (both directions of which we re-checked
above) plus $g(k_1+k_2)\ge g(k_1)g(k_2)$ gives $\lim g(k)^{1/k}\ge 2$, so the
conjecture fails.

Two corrections, both in the scout's favour.

**Fekete is unnecessary.** Supermultiplicativity applied $k$ times gives
$g(k)\ge g(1)^k = 2^k$ directly. Invoking Fekete's lemma adds a hypothesis
(the limit's existence) that the direct induction does not need.

**The conclusion is much sharper than "the conjecture is false".** Erdős-Turán
1934 states that $|A|\ge 3\cdot 2^{k-1}$ forces at least $k+1$ prime factors,
i.e. $g(k)\le 3\cdot 2^{k-1}-1$. A composition law would therefore squeeze
$g(k)$ into $[2^k,\; 1.5\cdot 2^k]$, pinning the growth constant to within a
factor $3/2$. That is not a side effect. It is why no such gadget is likely to
be found cheaply: it would be an essentially optimal construction against a
92-year-old bound, not merely a counterexample. The scout's "anti-composition
theorem" framing is right, but it undersells its own finding.

**A finite refutation target follows.** Supermultiplicativity at $(1,2)$ needs
$g(3)\ge 8$. Erdős-Turán gives $g(3)\le 11$. So **any proof that $g(3)\le 7$
refutes supermultiplicativity outright**, and that is a bounded Diophantine
question, not an asymptotic one. Nobody has to find the gadget to kill the idea.

Note also that the 1934 bound is *exactly sharp at $k=1$*: $3\cdot 2^0-1 = 2 = g(1)$.

## 4. The finite data. Reproduced, interpretation corrected on two points.

Independent branch-and-bound clique search on the $S$-smooth pair-sum graph,
exhaustive inside $[1,N]$, every witness re-verified by trial division:

| $k$ | $S$ | our $N$ | our $g_N(k)$ | scout's $g_N(k)$ |
|---|---|---|---|---|
| 1 | {2} | 2 000 | 2 | 2 |
| 2 | {2,3} | 2 000 | 4 | 4 |
| 3 | {2,3,5} | 1 200 | 5 | 5 |
| 4 | {2,3,5,7} | 800 | 6 | 6 |
| 5 | {2,…,11} | 600 | 8 | 8 |
| 6 | {2,…,13} | 400 | 10 | 10 |
| 7 | {2,…,17} | 300 | 11 | 11 |

Every row agrees. (Our first attempt returned $g_N=1$ on every row: the
adjacency bitset was built one-directionally, which silently caps every clique
at a single vertex. It is recorded in the file as a comment because a search
that reports 1 everywhere is obviously broken, whereas a search that reports 5
where the truth is 6 is not, and the same class of bug produces both.)

**Correction A: "every optimal witness lives below 50" is an artifact of search
order, not a phenomenon.** Our search enumerates largest-first and returned
$\{162,810,1134,1782\} = 162\cdot\{1,5,7,11\}$ at $k=2$ and
$\{48,2000\}$ at $k=1$. The reason is elementary and the scout files it under
"nobody knows why": **the witness set is closed under multiplication by any
$S$-unit, and under division by $\gcd$.** If $d\mid a$ for all $a\in A$ then the
prime factors of $(a+b)/d$ are among those of $a+b$, so $A/\gcd(A)$ is again a
witness and is smaller. Optima therefore come in infinite scaling orbits with a
unique $\gcd$-1 representative, and any search reporting the lexicographically
first optimum reports that representative. The open half of the scout's thread
(can optima be normalised into $[1,C^k]$?) survives, but the observation that
motivated it does not need explaining.

**Correction B: the table is never compared against the known construction, and
it should be.** The trivial upper bound $f(n)\ll n/\log n$ comes from
$A=\{1,\dots,m\}$, whose sums lie in $[3,2m-1]$: that gives
$g(\pi(2m-1))\ge m$, i.e. $g(k)\ge (p_k+1)/2 \sim \tfrac12 k\log k$. At $k=7$
this reads $g(7)\ge 9$ against the search's 11, so the exhaustive search beats
the 1934 construction by 2 at $k=7$ and by less at smaller $k$. **Any $g_N$
table must be reported as $\max(g_N(k), \lceil (p_k+1)/2\rceil)$**, and
asymptotically the 1934 construction wins against any bounded search. This also
re-confirms the scout's §5: $(\tfrac12 k\log k)^{1/k}\to 1$ too, so the falling
$k$-th roots separate nothing, exactly as the scout says.

**New data point, closing one of the scout's doors.** Its loose thread #4 asks
whether optimising $S$ over all $k$-subsets beats the first $k$ primes at $k=4$.
Exhaustive over all $\binom{8}{k}$ subsets of $\{2,\dots,19\}$:

| $k$ | best over all $k$-subsets | best $S$ | first-$k$-primes value |
|---|---|---|---|
| 2 | 4 | {2,3} | 4 |
| 3 | 5 | {2,3,13} (ties with {2,3,5}) | 5 |
| 4 | 6 | {2,3,7,13} (ties with {2,3,5,7}) | 6 |

**Optimising $S$ buys nothing at $k\le 4$.** The scout's guess that this door has
"genuine trade shape" is not supported at the only sizes where it can be checked
exhaustively. It remains open at $k\ge 5$.

## 5. The omitted-prime heuristic. **Refuted.**

The scout's loose thread proposes proving $|A| \le p-1$ when $p\notin S$, "by
pigeonhole on residues mod $p$ against the pairing $r\leftrightarrow -r$". This
is false for every odd $p$, and it is contradicted by a row inside the scout's
own arm-2 table.

**Why the pigeonhole fails.** The constraint from $p\notin S$ is that no two
distinct elements sum to $0 \bmod p$. That forbids: two elements in class $0$,
and one element in class $r$ together with one in class $-r$. It does **not**
forbid many elements in a single class $r$ with $2r\not\equiv 0$. So $A$ may
occupy up to $(p+1)/2$ classes and each class may be occupied arbitrarily often;
no cardinality bound follows. $p=2$ is the unique prime for which the argument
works, because $\mathbb{Z}/2$ is the only $\mathbb{Z}/p$ in which *every* class
is self-annihilating ($2r\equiv 0$ for all $r$), which is exactly why the scout's
parity observation is a genuine obstruction and does not generalise one step.

**Counterexample, from the scout's own §3 table.** $S=\{2,5,7\}$, so $3\notin S$,
and $A=\{1,3,7,13\}$: sums $4,8,14,10,16,20$, all $S$-smooth. $|A|=4 > p-1 = 2$.
Verified by trial division in `audit.py`.

**Unbounded family.** $A=\{1,4,7,\dots,3m-2\}$ has all off-diagonal sums
$\equiv 2 \bmod 3$, so $3$ divides no sum, for every $m$. Taking $S$ to be the
primes actually occurring, $|A|=m$ is arbitrary with $3\notin S$ (measured:
$m=8$ needs $k=10$ primes). So omitting an odd prime bounds nothing.

**The correct salvage.** The residue condition is a sieve condition: for every
prime $p\notin S$, $A$ occupies at most $(p+1)/2$ residue classes mod $p$. That
is a density-$\tfrac12$ condition at every prime above $\max S$, so a large-sieve
argument bounds $|A|$ in terms of the *diameter* of $A$, not in terms of $k$.
Since $A$ can be scaled by $S$-units freely (§4), a diameter bound is not a
cardinality bound, and this route cannot reach $g(k)$ without first proving the
normalisation the scout's thread #2 asks for. We did not push the sieve constant.

## 6. "No progress beyond 1934". Misleading, and the scout cites nothing.

The authoritative page (T. F. Bloom, Erdős Problem #126, accessed 2026-08-24)
states the problem as open, $250, with Erdős-Turán [ErTu34] proving
$\log n \ll f(n) \ll n/\log n$, the upper bound trivial from $A=\{1,\dots,n\}$,
and Erdős remarking that even $f(n)=o(n/\log n)$ has never been proved "but
perhaps never seriously attacked". So the *order of magnitude* of the lower
bound is unimproved, and to that extent the scout is right.

It is misleading as a statement about the literature, and neither hunt document
cites a single paper. Directly relevant and unmentioned:

- **Győry, Stewart and Tijdeman (1986)** generalise Erdős-Turán to two sets:
  for finite $A,B\subset\mathbb{Z}^+$ with $|A|\ge|B|\ge 2$,
  $\omega\!\left(\prod_{a\in A,b\in B}(a+b)\right) \ge c\log|A|$ with $c$
  effectively computable.
- **Erdős, Stewart and Tijdeman (1988)** show that bound is close to best
  possible: for every $\varepsilon>0$ and large $k$ there are $A,B$ with
  $|A|=k$, $|B|=2$ and $\omega(\prod(a+b)) < (\tfrac18+\varepsilon)(\log|A|)^2/\log\log|A|$.
- **Füredi and Gyarmati, arXiv:2602.07545 (February 2026)**, submitted to *Acta
  Arithmetica*, prove an Erdős-Turán analogue over the Eulerian integers and, via
  a lemma of Győry, Sárközy and Stewart, a $\log|A|$ lower bound for
  $\omega(\prod f(a,b))$ for a class of binary forms. The classical statement
  they quote is the unimproved $3\cdot 2^{k-1}$, which independently confirms
  that the constant has *not* been beaten.

The 1988 result is the one that matters strategically: it says the two-set
analogue of $f$ can be as small as $(\log n)^2/\log\log n$, which is $\omega(\log n)$
and $o(\log^2 n)$. That is the shape the conjecture would have to have if true,
and it is the first quantitative guess about $f$ that either hunt could have had
for the price of one literature search.

## 7. The new route we attacked, and how far it got

**The route: reduce to $S$-unit equations, explicitly, and see what it costs.**
The scout names "$S$-unit equation machinery" as the door and says it has no
purchase on it. Here is the purchase, which is elementary and which we did prove.

> **Proposition.** Let $A=\{a,b,c,d\}$ be four distinct positive integers whose
> six off-diagonal sums are all $S$-smooth. Then
> $X+Y-Z=1$ has a solution in positive $S$-units with no vanishing subsum.
>
> *Proof.* Put $u=a+b$, $v=c+d$, $w=a+c$, $x=b+d$, all positive $S$-units. Then
> $u+v = a+b+c+d = w+x$. Divide by $u$: $1 + v/u = w/u + x/u$, i.e.
> $X+Y-Z=1$ with $X=w/u$, $Y=x/u$, $Z=v/u$, all $S$-units. Degeneracy would need
> a vanishing subsum: $X+Y=0$ is impossible for positives; $X-Z=0$ gives
> $a+c=c+d$, so $a=d$; $Y-Z=0$ gives $b+d=c+d$, so $b=c$. Both are excluded by
> distinctness. $\square$

So a 4-element witness is a nondegenerate three-term $S$-unit equation, and an
$n$-element witness supplies $\binom{n}{4}$ of them (not obviously distinct as
solutions, which is the gap below). This is not a new idea in the field, but it
is the concrete bridge the scout says it lacks, and it lets us price the route.

**What the route would need, and why it is not dead.** Bounds on the number of
nondegenerate solutions of the three-term $S$-unit equation (Evertse; Evertse,
Schlickewei and Schmidt via the quantitative subspace theorem) are exponential
in $s=|S|$. Feeding an exponential-in-$s$ solution count back through the
proposition reproduces an exponential bound on $g(k)$, which is what 1934
already gives. **What #126 needs from this route is a solution count of the form
$\exp(o(s))$.** The known lower bound on the number of solutions is
$\exp(c\sqrt{s}/\log s)$ (Erdős, Stewart and Tijdeman, 1988, for the two-term
equation), and $\exp(c\sqrt{s}/\log s) = \exp(o(s))$. **So the known lower bounds
do not obstruct the route.** A subexponential-in-$s$ upper bound for the $S$-unit
equation would prove Erdős #126, and no counterexample forbids one.

**What we did not settle, and it is the load-bearing gap.** The step from
"$\binom{n}{4}$ nondegenerate unit-equation instances" to "$\binom{n}{4}$
*distinct* solutions" is not proved here, and without it the counting does not
close. That step is presumably the content of the 1934 induction, which we did
not reconstruct. We are stating a sufficient condition and a reduction, not a
theorem about $g(k)$.

## 8. What we could not settle

- **$g(2)$.** Is it $4$ or $5$? Erdős-Turán gives $g(2)\le 5$, search gives
  $g(2)\ge 4$, and the gap is one integer. Settling it would make $f(5)=3$
  unconditional and would be the first improvement of the 1934 constant at
  $k=2$. It is a bounded question about $S$-units in two primes, and we ran out
  of budget before attacking it.
- **$g(3)\le 7$**, which would kill the composition idea outright (§3). Range
  from Erdős-Turán is $[5,11]$.
- **The distinctness step in §7.** Named, not closed.
- **The large-sieve constant in §5.** Named, not computed.

## The doors

This audit measured no new ceiling of its own; it re-measured the scout's. Its
door list stands with three amendments.

1. **Closed.** "Optimise $S$ per $k$" (the scout's rank-1 trade-shape door) buys
   zero at $k=2,3,4$, exhaustively over all subsets of the first eight primes.
   It is not a promising door at reachable $k$.
2. **Downgraded.** "Why are optima tiny" is answered by $S$-unit scaling and
   $\gcd$ normalisation (§4). What survives is the genuinely open normalisation
   question, which is smaller than the thread implied.
3. **Re-ranked to first.** The top door is not the asymptotic $S$-unit bound,
   which the scout correctly identifies as out of reach. It is the pair of
   **finite** targets $g(2)\le 4$ and $g(3)\le 7$: both are bounded Diophantine
   statements, both would be the first movement on the 1934 constants, and
   $g(3)\le 7$ retires the composition programme without needing a gadget.

**Information class.** Targets $g(2)$ and $g(3)$ require reading *more* than the
current family reads (they are upper bounds, and no bounded search can produce
one), but far less than the asymptotic route: they need finiteness results for
$S$-unit equations in 2 and 3 primes, where explicit resolution is within reach
of standard machinery rather than of a new theorem.

## Loose threads

- **$g(2)=4$?** *Why it matters:* one integer separates a search lower bound
  from the 1934 upper bound, and closing it makes $f(5)$ unconditional.
  *First step:* by §5, $2\in S$, so $S=\{2,q\}$; enumerate solutions of
  $2^{a_1}q^{b_1} + 2^{a_2}q^{b_2} = 2^{a_3}q^{b_3} + 2^{a_4}q^{b_4}$ for small
  $q$ with an existing $S$-unit-equation solver and check no 5-element witness
  arises.
- **The distinctness step (§7).** *Why it matters:* it is the only missing link
  between the reduction and a bound on $g(k)$. *First step:* read the
  Erdős-Turán 1934 proof (`combinatorica.hu/~p_erdos/1934-03.pdf`) and see
  whether its induction is already this counting argument.
- **The $\exp(o(s))$ target for $S$-unit equations.** *Why it matters:* it is a
  clean sufficient condition for #126 that is not excluded by known lower
  bounds. *First step:* check the current best upper bound's dependence on $s$ in
  Evertse-Schlickewei-Schmidt and state the gap as a ratio.
- **A witness-scaling normalisation lemma.** *Why it matters:* it would convert
  bounded search from a lower-bound instrument into an exact computation of
  $g(k)$, which is the missing half of every finite arm here. *First step:*
  test whether every $\gcd$-1 optimal witness for $k\le 6$ lies in $[1,2^{k+2}]$.
