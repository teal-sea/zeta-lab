# RESULTS: Erdős #126, analytic-prime-divisors arm (support run 95a76f59)

**Hunt, not a result. Nothing here is evidence for or against RH (`docs/08`).**

**Verdict: the arm is closed, with a proof that it is closed.** The product
$P = \prod_{a\neq b}(a+b)$ cannot yield a bound better than $k \ge 2$, no matter
which counting, gcd or sieve estimate is fed into it. That is not a report of
failure to find one. It is Theorem 4 below, with two explicit adversarial
families, both of which have $\gcd = 1$ and satisfy every hypothesis such an
estimate is entitled to use. The separate smooth-counting lane is capped at
$k \gtrsim \log n / \log\log X$, which beats Erdős–Turán's $\log_2 n$ only if the
largest element $X$ is bounded, and nothing bounds $X$.

*Scope note added on landing (2026-10-21).* "Closed" in this file means closed
for a named class, not for the product idea in general. Theorem 4 covers the
**unweighted** product $P=\prod_{a\ne b}(a+b)$ read through Theorem 1, with
$e_p$ estimated from distinctness, range and residue counts, plus whole-set gcd
normalisation and the one-step recursion on multiples of $p$. The run's own
doors section names what escapes it: weighted or subset products, and any
estimate that reads the additive structure of $A$.

**Landing note (2026-10-21).** Landed on main as Hunt #100 from a local-only
branch, `support/95a76f59`, that was never pushed; PR #144 counted this arm
among the seven that "produced no branch at all" (and cited it as the closed
"Analytic NT" lane). The run's files are as it wrote them apart from
punctuation, one reworded comment in `probe.py` (a form of the reserved word
became "establish"), and the dated notes marked as added on landing.

**Grading (added on landing, 2026-10-21).** Theorems 1 to 4, the occupancy
lemma (5a), the large-sieve bound (5b) and the smooth-counting cap (5d) are
this lab's ordinary arguments, unreviewed and pending external verification;
none is kernel-checked. The run itself flags (5b): the derivation follows
Montgomery's large sieve but its normalisation was not re-checked, so the
constant in $n = O(\sqrt X\log X)$ is unconfirmed. The values of $B$ (1.041,
2.125 and the empirical rider) are floating-point measurements. In the terms of
`ALIGNMENT.md` §5 the disposition is a **restricted-class obstruction**
(disposition 2) for the class named in the scope note above, and the audit of
loose thread 3 is a refuted candidate (disposition 1). `probe.py` was re-run on
landing: `results.json` reproduced to floating-point rounding (20 values differ
in the last digits, relative difference at most $3\times10^{-15}$), and the
committed file is the run's.

**Overlap with arms already on main.** The normalisation of §0 is Hunt #103's
normalization lemma (`support_60982bf6`). The occupancy lemma (5a) is the
residue-class form of the pigeonhole on main in Hunts #93 and #95 (#95's Lemma
A), with the same $(q+1)/2$ count. The inequality $n \le 1+\Psi(2X;S)$ of (5d)
is Hunt #107's counting horn (`support_95bb5cb7`), which pins
$\log\Psi(2X,S)/k$ from both sides; (5d) is the cruder upper estimate of the
same quantity. The refutation of loose thread 3 (§6) was on main before this
arm landed (Hunts #93, #95, #101, #103). The open question of §7, whether $X$
is bounded in terms of $(n,k)$ after normalisation, is answered for
sub-extremal sizes by Hunt #107 (annotated there). This arm's own contributions
are Theorem 1's identification of $B(A)$ as the exact strength of the product
route, the two adversarial families of Theorem 4 with their measured ceilings,
and the large-sieve sparsity bound (5b).

Reproduce with `.venv/bin/python hunts/support_95a76f59/probe.py` (a few
seconds, stdlib only, writes `results.json`). The probe checks arithmetic; the
proofs are here.

---

## 0. Setup and normalisation

$S=\{p_1<\dots<p_k\}$ primes, $A=\{a_1<\dots<a_n\}$ distinct positive integers
with every $a_i+a_j$ ($i \ne j$) $S$-smooth. $X = a_n$. Write

$$P=\prod_{i<j}(a_i+a_j),\qquad e_p=\sum_{i<j}v_p(a_i+a_j),\qquad
N_t(p)=\#\{i<j:\ p^t \mid a_i+a_j\}.$$

**Normalisation.** $\gcd(A)$ is $S$-smooth (a prime $q \mid \gcd(A)$ divides
every $a_i+a_j$, so $q \in S$), and $A/\gcd(A)$ is again valid with the same
$S$. So we may and do assume $\gcd(A)=1$. Two further closures, both immediate
and both used below: $mA$ is valid for every $S$-smooth $m$, and
$\{a/p : a\in A,\ p\mid a\}$ is valid for every $p\in S$.

## 1. What the product can possibly say (Theorem 1)

$$\log P=\sum_{p\in S}e_p\log p\ \le\ k\cdot\max_{p\in S}e_p\log p
\qquad\Longrightarrow\qquad
k\ \ge\ B(A):=\frac{\log P}{\max_{p\in S}e_p\log p}.$$

This is an identity followed by one application of "a sum of $k$ terms is at
most $k$ times the largest", so **$B(A)$ is exactly the strength of the product
route**: any argument that lower-bounds $\omega(P)$ from $P$ must lower-bound
$\log P$ and upper-bound the largest per-prime mass $e_p\log p$, and $B(A)$ is
what those two inputs give. Nothing is lost in this step that a cleverer
assembly could recover: $\omega(P)=\#\{p: e_p>0\}$ and the masses are all the
product knows.

The target is $k/\log n \to \infty$; Erdős–Turán give $k \ge \log_2 n - O(1)$.

## 2. Structure of the divisibility graphs (Theorem 2)

Let $H_{p,t}$ be the graph on $A$ with $a\sim b$ iff $p^t\mid a+b$, and let $m_r$
be the number of elements of $A$ in class $r$ mod $p^t$. Since $a+b\equiv 0$
iff $b\equiv-a$,

$$E(H_{p,t})=\bigsqcup_{r\ne -r}K_{m_r,m_{-r}}\ \sqcup\ \bigsqcup_{2r\equiv 0}K_{m_r},
\qquad
N_t(p)=\sum_{0<r<-r}m_rm_{-r}+\sum_{2r\equiv 0\ (p^t)}\binom{m_r}{2}.$$

The self-antipodal classes are $r\equiv 0$ always, plus $r=p^t/2$ when $p=2$.
Two consequences used repeatedly:

* **(2a)** If $p$ is odd and $N_t(p)=\binom n2$ with $n\ge 3$, then all of $A$
  lies in one self-antipodal class, so $p^t\mid \gcd(A)$: impossible after
  normalisation. A single odd prime power cannot cover all pairs.
* **(2b)** With the class-$0$ block excluded, the maximum of $N_t$ is $n^2/4$,
  attained by two antipodal classes of size $n/2$. **With** the class-$0$ block,
  the maximum is $\binom n2$, approached by putting $n-O(1)$ elements in class
  $0$. That gap is the whole story of §4.

## 3. The counting cap on a prime's mass (Theorem 3)

For every prime $p$ and every $t\ge 1$,

$$N_t(p)\ \le\ \min\Big(\tbinom n2,\ \tfrac n2\big(\tfrac{X}{p^t}+1\big)\Big).$$

*Proof.* Ordered pairs with $a\equiv -b$ number $\sum_r m_rm_{-r}$, so
$N_t\le\frac12\sum_r m_rm_{-r}\le\frac12(\max_r m_r)\sum_r m_r=\frac n2\max_r m_r$,
and a class mod $p^t$ meets the distinct integers of $[1,X]$ in at most
$X/p^t+1$ of them. $\square$

Summing over $t$, with $\tau=\max\{t:p^t\le X/n\}$ and $v_p(a+b)\le\log_p(2X)$:

$$e_p\log p\ \le\ \frac{n^2}{2}\log\frac Xn\ +\ \frac{n^2}{2}\cdot\frac{p\log p}{p-1}
\ +\ \frac n2\log(2X).$$

This is the best bound available from distinctness, the range $[1,X]$ and
residue counts. It is also, by §4, not good enough, and neither is anything
else in that class.

## 4. The ceiling: two adversarial families (Theorem 4)

Both families consist of distinct positive integers with $\gcd=1$. Neither is
claimed to be a valid Erdős configuration; that is the point. They satisfy
every hypothesis a counting estimate on $P$ is entitled to use (distinctness,
range, residue distribution mod every prime power, whole-set gcd
normalisation), so any bound proved from those hypotheses alone must hold for
them, and on them the bound reads $k\ge B$ with $B$ as computed.

**(4a) Near-common divisor.**
$\Omega'(n,p,m)=\{1\}\cup\{i\,p^m: 1\le i\le n-1\}$. Then $\gcd=1$, and
$\binom{n-1}{2}$ of the $\binom n2$ pairs have $v_p\ge m$, while
$\log P\le\binom n2\log(2np^m)$. Hence

$$B(\Omega')\ \le\ \frac{\binom n2\,(m\log p+\log 2n)}{\binom{n-1}2\, m\log p}
\ \xrightarrow[m\to\infty]{}\ \frac{n}{n-2}\ \xrightarrow[n\to\infty]{}\ 1 .$$

Measured: $n=60,\ p=101,\ m=128$ gives $B=1.041$ against the limit
$n/(n-2)=1.0345$.

**(4b) Two antipodal classes, stable under every closure in §0.**
$\Omega(n,p,m)=\{i\,p^m+1\}_{i\le n/2}\cup\{j\,p^m-1\}_{j\le n/2}$, $p$ odd.
No element is divisible by $p$, so the "divide the multiples of $p$ by $p$"
recursion does nothing to it, and $\gcd=1$. The $n^2/4$ cross pairs are
$(i+j)p^m$; the within-block pairs are $(i+j)p^m\pm 2$, with $v_p=0$. Hence

$$B(\Omega)\ \longrightarrow\ 2\cdot\frac{m\log p+\log n}{m\log p}\ \longrightarrow\ 2 .$$

Measured: $n=60,\ p=1009,\ m=6$ gives $B=2.125$, mass fraction $0.4707$.

**Corollary (the arm is closed).** Any bound on $e_p$ proved from distinctness,
range and residue data, combined with Theorem 1, yields at most
$k \ge 1+o(1)$; adding whole-set gcd normalisation and the recursion on
multiples of $p$ raises that to at most $k\ge 2+o(1)$. Neither reaches
$\log_2 n$, let alone $\omega(\log n)$. **The product route cannot reproduce
Erdős–Turán, so it cannot improve it.**

The reason is visible in (2b): the $2^k$ of Erdős–Turán is the price of the
class-$0$/antipodal split, paid by an induction that loses elements at each
step. $P$ aggregates over all pairs and cannot see the split.

**Empirical rider (data, not proof).** On the seven measured optima of
`hunts/r_186989`, all of which this run re-verified valid by trial division,
$B(A)$ is $1.00,\,1.61,\,1.85,\,2.38,\,2.76,\,2.66,\,2.73$ for $k=1..7$, while
$\log_2 n$ is $1.00,\dots,3.46$. On real configurations the product route
already loses to Erdős–Turán at $k\ge 6$, and it is flat where $\log_2 n$ is
still climbing.

## 5. The sieve lane: one real inequality, and why it cannot close

**(5a) Occupancy lemma.** For every prime $q\notin S$, no two distinct elements
of $A$ are antipodal mod $q$. Hence $A$ occupies at most $(q+1)/2$ classes mod
$q$ (at most one of each pair $\{r,q-r\}$, plus at most one element in class
$0$), so it *avoids* at least $(q-1)/2$ classes. For $q=2$ every class is
self-antipodal, which gives $|A|\le 2$ whenever $2\notin S$ and recovers the
parity observation of `r_186989` §3.

**(5b) Large sieve.** With $\omega(q)\ge (q-1)/2$ avoided classes for every
prime $q\le Q$ outside $S$, and $(q-1)/(q+1)\ge 1/3$,

$$n\ \le\ \frac{X+Q^2}{L(Q)},\qquad L(Q)=\!\!\sum_{q\le Q,\,q\notin S}\!\!\frac{\omega(q)}{q-\omega(q)}\ \ge\ \frac{\pi(Q)-k}{3},$$

so $n \le 3(X+Q^2)/(\pi(Q)-k)$ for any $Q$ with $\pi(Q)>k$, and taking
$Q=\sqrt X$, $n=O(\sqrt X\log X)$. This is a genuine structural fact: valid
sets are thin, of density at most about $\log X/\sqrt X$. (Derived here from
the standard large sieve in Montgomery's form; constants not optimised and the
normalisation not independently re-checked in this run. The shape is what is
used.)

**(5c) Why it closes nothing.** Every sieve statement here bounds $n$ in terms
of $X$, and there is no bound on $X$ in terms of $(n,k)$: $\{1,2^m-1\}$ is
valid for $S=\{2\}$ with $\gcd=1$ and $X$ arbitrary, and $A\mapsto mA$ for
$S$-smooth $m$ moves $X$ freely. Worse, (5b) pushes $X$ *up* ($X\gtrsim
n^2/\log^2 X$), which is the wrong direction for (5d).

**(5d) The smooth-counting lane is capped below Erdős–Turán.** The $n-1$ sums
$X+a_i$ are distinct $S$-smooth numbers in $(X,2X]$, so

$$n\ \le\ 1+\Psi(2X;S)\ \le\ 1+\prod_{i=1}^k\Big(1+\frac{\log 2X}{\log p_i}\Big)
\ \le\ 1+\big(1+\log_2 2X\big)^k,$$

giving $k\ \ge\ \log n/\log\log(2X)\,(1+o(1))$. **This exceeds $\log_2 n$ only
when $\log\log 2X<\log 2$, i.e. $X<e^{2}$**. So even granting an unproven and
very strong bound on $X$ (say $X\le n^C$), this lane returns
$k\gtrsim \log n/\log\log n$, which is *weaker* than Erdős–Turán. The lane is
not merely unproven, it is capped. This is the sharpest negative statement in
this file after Theorem 4, and it disposes of "count the $S$-smooth pair sums"
as a route to #126.

## 6. Audit of `hunts/r_186989/RESULTS.md`

| Claim | Verdict |
|---|---|
| §2, $f(n-1)\le f_0(n)\le f(n)$ | **Correct.** Both halves check; the case split on $0\in A$ is exhaustive. |
| §4, $g(1)=2$ via $2a=2^x+2^y-2^z<0$ | **Correct.** $x<y<z$ follows from $a<b<c$, and $2^z\ge 2^{y+1}$ closes it. |
| §4, odd single prime gives $g\le 2$ by parity | **Correct**, and generalised in (5a). |
| §3 table, the seven witnesses | **Re-verified valid** here by independent trial division (`probe.py`, `all_witnesses_valid: true`). The *exhaustiveness* of the searches was not re-run in this run. |
| §4, supermultiplicativity would refute the conjecture | **Correct and worth keeping.** Fekete plus $g(1)=2$ does give $g(k)\ge 2^k$. |
| Loose thread 3: "prove $\lvert A\rvert\le p-1$ when $p\notin S$ by pigeonhole on $r\leftrightarrow -r$" | **False as stated, and the suggested first step cannot succeed.** For odd $q$ the only self-antipodal class is $0$, so an arbitrarily large $A$ can sit inside one non-antipodal class. Witness: $A=\{1+iM\}_{i<n}$ with $M=\prod_{2<q\le Q}q$ has no antipodal pair mod any odd $q\le Q$, for every $n$; verified for all odd $q\le 31$ at $n=40$. The correct replacement is the occupancy lemma (5a), which bounds *classes*, not elements, and whose sieve consequence is (5b). *(Landing note: refuted on main before this arm landed, in Hunts #93, #95, #101 and #103.)* |

The rest of that file's self-description ("no upper bound on $g(k)$", "the trend
decides nothing") is accurate and this run does not disturb it. Its door
ranking, which puts $S$-unit machinery outside the reach of enumeration, is
reinforced by Theorem 4: the elementary product route is not merely unexplored,
it has a ceiling of $2$.

## 7. What this run did not settle

* No upper bound on $g(k)$ of any kind, and no improvement of $3\cdot 2^{k-1}$.
* Whether $X$ can be bounded in terms of $(n,k)$ after normalisation. Only
  $n=2$ examples with unbounded $X$ are exhibited here. This is the pivot of
  §5 and it is open in both directions. *(Answered in part on main,
  annotated on landing 2026-10-21: Hunt #107 found primitive admissible
  3-element sets for $S=\{2,3\}$ whose height tracks the search cutoff over
  eleven orders of magnitude, from $\{217,1241,7975\}$ to
  $\{3772777922353,\,41980806987569,\,559177175498959\}$, so $X$ is not
  bounded in terms of $(n,k)$ at that sub-extremal size. Whether it is bounded
  for sets of extremal size is still open; Hunt #103 states uniformly bounded
  height as a conjecture.)*
* Whether the $S$-unit route ($x+y=1$ in $S$-units, Evertse–Győry) can be made
  uniform enough to help. Not attempted; out of budget and out of lane.

## The doors

This arm measured a ceiling ($B \le 2+o(1)$), so it owes the list.

**1. Active constraints at the optimum.**

| Rank | What binds | Evidence |
|---|---|---|
| 1 | **Aggregation.** $P$ sums over pairs, and the extremal configurations put almost all mass on one prime. | Theorem 4: $B\to1$ (4a), $B\to2$ (4b). |
| 2 | **No control on $X$.** Every sieve and smooth-count estimate is stated in $X$, which is unbounded. | (5c); $\{1,2^m-1\}$. |
| 3 | **The class-$0$ block.** Removing it caps $N_t$ at $n^2/4$; keeping it allows $\binom n2$. The entire gap between $B\to1$ and $B\to2$ is this block. | (2b), (4a) vs (4b). |

**2. Frozen-constant inventory.**

| Frozen | Value | What relaxing it trades |
|---|---|---|
| The aggregation functional | $\prod_{a\ne b}(a+b)$, i.e. an unweighted product over all pairs | **The one door with genuine trade shape.** A *weighted* or *subset* product, $\prod_{(a,b)\in E}(a+b)$ over a chosen graph $E$, is not subject to Theorem 4 as stated: the adversarial families concentrate mass on a specific pair structure that a chosen $E$ could avoid. Cost: the size lower bound on $\log P$ falls with $|E|$, so the trade is mass-concentration against total size. |
| The normalisation | $\gcd(A)=1$, plus the one-step recursion on multiples of $p$ | Relaxing to the *full* recursion (iterate the closure of §0 to exhaustion) is exactly Erdős–Turán's induction. It escapes (4a) but not (4b). |
| The estimate class | distinctness + range + residue counts | Any estimate that reads the *additive* structure of $A$ (not just residues) escapes Theorem 4. Nothing in this lane produced one. |
| $q$ in the sieve | primes outside $S$ only | Only $k$ primes are lost, so this is slack. Low value. |

**3. Information class.** Doors 1 and 2 stay **inside** the data the product
reads (multiset of pair sums with their factorisations) and are under the
ceiling of Theorem 4 in every version this run could formulate. Door 3
requires reading more: a genuinely additive input, which in practice means the
$S$-unit equation machinery. The top-ranked door is therefore the weighted or
subset product, and it is worth exactly one bounded probe before the lane is
declared dead, because it is the only one Theorem 4 does not already cover.
