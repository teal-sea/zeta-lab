# RESULTS — Erdős #126, the size-dichotomy arm (support run 95bb5cb7)

**Hunt, not a result. Nothing here is evidence for or against RH (`docs/08`).**

**Verdict: the size dichotomy cannot close, and the place it fails is exact.**
The "controlled interval" horn works if and only if
$\max A = \mathrm{rad}(S)^{o(1)}$. That threshold is now pinned from both
sides. The "spread out" horn cannot supply it. For every set size strictly
below the extremal one, the height of a primitive admissible set is
**unbounded**, with explicit witnesses, and even a best-possible
$abc$-shaped height bound would land at $\mathrm{rad}(S)^{1+o(1)}$, one full
power of the radical above what the counting horn needs.

Reproduce with `python3 hunts/support_95bb5cb7/probe.py` (~20 s, stdlib only).

Notation follows `hunts/r_186989`: $S$ is a set of $k$ primes, $A$ a set of
distinct positive integers with every off-diagonal sum $a+b$ $S$-smooth,
$g(k) = \max |A|$, and the target is $\log g(k) = o(k)$. Write
$\mathrm{rad}(S) = \prod_{p\in S} p$ and $\theta = \log \mathrm{rad}(S)$.

---

## 1. Normalisation, first, because it decides what "small diameter" can mean

Two facts, both proved, that fix the coordinates the dichotomy has to work in.

**(N1) $S$-smooth scaling is a symmetry.** If $A$ is admissible and $\lambda$
is $S$-smooth then $\lambda A$ is admissible, with the same cardinality.
Conversely if $d = \gcd(A)$ then every off-diagonal sum is $d\cdot(\text{sum
of }A/d)$, and a product is $S$-smooth iff both factors are, so $A/d$ is
admissible and $d$ is $S$-smooth. **Hence WLOG $\gcd(A) = 1$**, and $g(k)$ is
unchanged. Without this normalisation "diameter" is meaningless: $\lambda A$
has diameter $\lambda\cdot\mathrm{diam}(A)$ for every smooth $\lambda$.

**(N2) Translation is not available.** $A + t$ shifts every sum by $2t$, which
destroys smoothness. So the only scale freedom is (N1), and after (N1) the
height $\max A$ is a genuine invariant of the set. Everything below is about
that invariant.

## 2. The counting horn, pinned from both sides

**Lemma 1 (the correct counting step).** Let $a_n = \max A$, $|A| = n$. The
$n-1$ sums $a_j + a_n$ ($j<n$) are distinct $S$-smooth integers lying in
$(a_n,\,a_n + a_{n-1}] \subseteq (N, 2N]$ with $N = \max A$. Hence

$$|A| \;\le\; 1 + \#\{\,m \le 2N : m \text{ is } S\text{-smooth}\,\}
        \;=\; 1 + \Psi(2N, S).$$

(The dyadic-block refinement $\Psi(2N)-\Psi(N)$ and the short-interval
refinement $(N, N+a_{n-1}]$ are both available and neither changes anything on
the logarithmic scale, which is the scale the target lives on. That is the
whole of what the "large gaps" idea buys on this horn.)

**Lemma 2 (threshold).** Write $\log 2N = c\,\theta$. Then, uniformly in $k$,

$$\frac{\log \Psi(2N,S)}{k} \;=\; \Theta_c(1),\qquad
\text{and } \to 0 \iff c \to 0 .$$

Both directions are rigorous and measured, with $S$ = the first $k$ primes
(the choice that maximises $\Psi$, so this is the worst case, i.e. the
statement is uniform over all $S$ with $|S| = k$):

* **upper**, Rankin: $\Psi(x,S) \le x^{\sigma}\prod_{p \in S}(1-p^{-\sigma})^{-1}$
  for every $\sigma>0$, minimised numerically;
* **lower**, every lattice point of $\{e \ge 0: \sum e_i \log p_i \le \log x\}$
  is an $S$-smooth integer $\le x$, and the point count is at least the
  simplex volume $(\log x)^k / (k!\prod_i \log p_i)$.

| $c=\log 2N/\theta$ | $\log\Psi/k$ lower | $\log\Psi/k$ upper ($k=10$) | ($k=200$) | ($k=5000$) |
|---|---|---|---|---|
| 0.001 | 0 | 0.0023 | 0.0059 | 0.0091 |
| 0.01 | 0 | 0.0226 | 0.0590 | 0.0592 |
| 0.1 | 0 | 0.2259 | 0.3605 | 0.3418 |
| 0.5 | **0.32** | 1.0465 | 0.9864 | 0.9635 |
| 1.0 | **1.01** | 1.4821 | 1.4191 | 1.3954 |
| 2.0 | **1.70** | 1.9893 | 1.9429 | 1.9189 |

Read the table in both directions. Above $c \approx 1/2$ the *lower* bound is
bounded away from zero, so at $\max A \ge \mathrm{rad}(S)^{1/2}$ the counting
horn is not merely unproven, it is **false**: $\Psi$ really does have
$e^{\Omega(k)}$ elements to hide a large $A$ in. Below $c \to 0$ the Rankin
bound goes to zero, so the horn works. There is no third regime.

**Consequence.** The controlled-interval horn delivers $\log g(k) = o(k)$
**iff** it is handed $\max A = \mathrm{rad}(S)^{o(1)}$, equivalently
$\log\max A = o(\theta(p_k)) = o(k\log k)$. Optimising the choice of $S$, the
scale of $A$, the interval split, or the smooth-count estimate cannot move
this: the threshold is a property of $\Psi$, not of the argument.

## 3. The other horn cannot supply it. Two independent reasons.

### 3.1 Measured: admissible sets of sub-extremal size have unbounded height

Exhaustive enumeration of **primitive** ($\gcd = 1$) admissible triples,
through their three sums rather than through their elements: the sums are
what is constrained, so bounding them is the honest universe. Every witness
re-verified from scratch by full trial division.

$S=\{2,3\}$ (so $k=2$, $\mathrm{rad}=6$, $g(2)=4$):

| sums $\le$ | primitive 3-sets | largest element of a 3-set | witness |
|---|---|---|---|
| $10^4$ | 224 | 7 975 | 217, 1241, 7975 |
| $10^6$ | 550 | 522 397 | 1891, 37475, 522397 |
| $10^9$ | 1 482 | 773 296 457 | 1544521, 32009911, 773296457 |
| $10^{12}$ | 2 782 | 562 932 791 521 | 1926281441, 272951625503, 562932791521 |
| $10^{15}$ | 4 411 | 559 177 175 498 959 | 3772777922353, 41980806987569, 559177175498959 |

The height tracks the cutoff linearly over eleven orders of magnitude. **There
is no height bound for $|A| = 3$**, even at $k=2$, even after the only
available normalisation. The same holds one size up: for $S=\{2,3,5\}$ the
largest primitive 4-set element is 7 213 at cutoff $10^4$ and 98 099 at
cutoff $10^6$.

This is what kills any *descent*. A descent argument reaches a smaller
admissible set and asks for interval control there; at sub-extremal sizes
there is none to be had.

### 3.2 Structural: the clique supplies no three-term $S$-unit relation

Height bounds for $S$-smooth numbers (Baker–Győry effectively, $abc$
conjecturally) are theorems about $x + y = z$ with all three terms
$S$-smooth (or two smooth and one fixed). **An admissible clique produces no
such relation.** The relations it does produce are

$$(a+b) + (c+d) \;=\; (a+c) + (b+d),$$

a *four*-term $S$-unit equation. For four terms there is no height theorem at
all, only the Evertse–Schlickewei–Schmidt bound on the **number** of
non-degenerate solutions, which is $\exp(O(k))$: the right order for the
classical $f(n) \gg \log n$, and provably not improvable to $\exp(o(k))$ in
general, since Erdős–Stewart–Tijdeman exhibit $S$ for which $x+y=1$ already
has more than $\exp(c(k/\log k)^{1/2})$ $S$-unit solutions. A count is not a
height, and the target needs a height.

And even granting the best imaginable outcome, a three-term relation plus
$abc$, one gets $\max A \ll_\varepsilon \mathrm{rad}(S)^{1+\varepsilon}$,
which is $c \to 1$ in Lemma 2, exactly where the table's **lower** bound reads
$1.01\,k$. Not close: one full power of the radical, permanently.

## 4. Where the measured optima actually sit

$\varepsilon$ with $\max A = \mathrm{rad}(S)^{\varepsilon}$, over the witnesses
of `hunts/r_186989` §3 (all seven re-verified here, see §5):

| $k$ | 1 | 2 | 3 | 4 | 5 | 6 | 7 |
|---|---|---|---|---|---|---|---|
| $\mathrm{rad}(S)$ | 2 | 6 | 30 | 210 | 2310 | 30030 | 510510 |
| $\max A$ | 3 | 11 | 47 | 13 | 31 | 47 | 49 |
| $\varepsilon$ | 1.58 | 1.34 | 1.13 | 0.48 | 0.44 | 0.37 | 0.30 |

$\varepsilon$ falls, which is the only encouraging number in this file, and it
is not encouraging enough: Lemma 2 needs $\varepsilon \to 0$ and these are
seven points of a staircase whose witnesses are not known to be the extremal
ones (see §5, where $\varepsilon$ at $k=3$ turns out to be 1.81, not 1.13).

## 5. Audit of `hunts/r_186989/RESULTS.md`

**Verified.**

* All seven witnesses of §3 are admissible: distinct, positive, every
  off-diagonal sum $S$-smooth by full trial division. The lower bounds
  $g(k) \ge 2,4,5,6,8,10,11$ for $k=1..7$ stand.
* §2, $f(n-1)\le f_0(n)\le f(n)$: the proof is correct, and $f(2)=1$,
  $f_0(2)=0$ check out.
* §4, the Fekete argument: correct, and it is the most useful thing in that
  file. $g(1)=2$ (their 2-adic argument for $S=\{2\}$ is right, and parity
  handles odd $p$), so supermultiplicativity would force
  $\lim g(k)^{1/k} = \sup_k g(k)^{1/k} \ge 2$ and refute the conjecture. A
  composition law is a refutation route, not a proof route.

**Corrected.** §3 and door 2 assert *"Every optimal witness has all elements
$< 50$"* and rank "the smooth-sum graph is locally starved" on that evidence.
**That is false.** Growing all admissible triples with sums $\le 10^5$ for
$S=\{2,3,5\}$ gives exactly six primitive extremal ($|A|=5$) sets:

| set | max | $\varepsilon = \log\max/\log 30$ |
|---|---|---|
| 1, 3, 7, 17, 47 | 47 | 1.13 |
| 3, 7, 13, 17, 47 | 47 | 1.13 |
| 3, 7, 17, 33, 47 | 47 | 1.13 |
| 1, 5, 31, 49, 59 | 59 | 1.20 |
| 1, 19, 31, 89, 161 | 161 | 1.49 |
| **5, 11, 25, 245, 475** | **475** | **1.81** |

$\{5,11,25,245,475\}$: the sums are $16, 30, 250, 480, 36, 256, 486, 270, 500,
720$, all $\{2,3,5\}$-smooth, $\gcd = 1$. Their branch-and-bound reported one
witness per $k$ and the file generalised from it. The correct statement is
that the *smallest* optimal witness is tiny; the optimal witnesses are not.
Door 2's ranking should be re-read with that in mind.

**Added.** A small upper bound in a better universe. Their searches bound the
*elements*; bounding the *sums* is exhaustive for the property being tested.
For $S=\{2,3,5\}$ there is **no 6-element admissible set all of whose
pairwise sums are $\le 10^5$** (every such set contains a triple with sums
$\le 10^5$, and the enumeration of those is complete). Likewise for
$S=\{2,3\}$ there are exactly 8 primitive 4-sets with sums $\le 10^9$, all
inside $[1,47]$. These are still bounded-universe statements and are not upper
bounds on $g(k)$.

## 6. What we could not settle

* **Whether extremal sets have bounded height.** The data hints yes, at
  $k=3$ the six extremal 5-sets are identical at cutoffs $10^4$ and $10^5$,
  while 3-sets and 4-sets keep growing, but a proof would be circular for the
  dichotomy's purposes: it would presuppose knowing $g(k)$. And $475 =
  \mathrm{rad}^{1.81}$ is on the wrong side of Lemma 2 anyway.
* **The ladder for $k=4$.** The set-growing enumeration is $O(|{\rm sets}|
  \cdot \Psi)$ per level and exceeded ten minutes at $S=\{2,3,5,7\}$. A real
  clique solver over the sum-bounded universe would settle it.
* **Nothing improves $f(n) \gg \log n$.** This arm produces no upper bound on
  $g(k)$ and was never going to; it produces the reason.

## The doors

This run measured a ceiling (the threshold in Lemma 2), so it owes the list.

**1. Active constraints at the optimum.**

| Rank | What binds | Evidence |
|---|---|---|
| 1 | **$\log\max A$ vs $\theta(p_k)$.** The whole dichotomy is this one ratio $c$. | Lemma 2's two-sided table; $c \ge 1/2$ makes the horn false, not just unproven. |
| 2 | **Arity of the available $S$-unit relation.** Three terms have heights, four terms have only counts. | §3.2; ESS vs Erdős–Stewart–Tijdeman. |
| 3 | **Primitivity is the only normalisation.** Translation is unavailable, so height is an invariant and cannot be argued away. | (N1)/(N2). |

**2. Frozen-constant inventory.**

| Frozen | Value | What relaxing it trades |
|---|---|---|
| $S$ = first $k$ primes in Lemma 2 | fixed | This is the $\Psi$-maximising choice, so the lemma is already uniform over $S$. Zero trade shape. Relaxing it can only help the bound, never hurt it. |
| the counting step (top element only) | $\Psi(2N,S)$ | Dyadic and short-interval refinements are both available and both change nothing at log scale. **This is the door with the least trade shape in the file** and it is where the brief expected the gain. |
| sum cutoffs $10^4$–$10^{15}$ | per $S$ | Already shown slack for the height question (linear tracking) and binding for the extremal question (the $k=4$ ladder did not finish). |
| $\sigma$ in Rankin | optimised | Genuinely optimised, not frozen. |
| set sizes probed | 3, 4, 5 | The real door: sizes near $g(k)$ for $k \ge 4$ are unmeasured, and that is where the height question is actually decided. |

**3. Information class.** Every door above stays **inside** the data this
family reads, integers and the smoothness of their pairwise sums, and
therefore cannot produce an upper bound on $g(k)$. Moving Erdős #126 requires
reading more: a height theorem for four-term $S$-unit equations, which does not
exist and is not a parameter of anything here. That is the same conclusion
`r_186989` reached from the other side, and this run makes it quantitative:
the missing object is not "a better estimate", it is one power of
$\mathrm{rad}(S)$.

## Loose threads

* **Four-term $S$-unit heights.** The clique's only relation is
  $(a+b)+(c+d)=(a+c)+(b+d)$. *Why it might matter:* it is the exact
  obstruction, stated as a request to the literature rather than as a wall.
  *First step:* search for any height result (even conditional on $abc$) for
  $x_1+x_2 = x_3+x_4$ in $S$-units with a non-degeneracy hypothesis that a
  clique can supply.
* **Extremal-height boundedness.** *Why it might matter:* if extremal sets
  provably sit in $[1, \mathrm{rad}(S)^{C}]$ then $g(k)$ becomes computable
  exactly, which is the missing upper-bound half of `r_186989`'s thread 2.
  *First step:* run the sum-bounded ladder at $k=4,5$ with a real clique
  solver and see whether the extremal sets stop moving as the cutoff grows.
* **The $\varepsilon$ staircase.** 1.58, 1.34, 1.81, 0.48, 0.44, 0.37, 0.30,
  and the $k=3$ entry only rose because we looked harder. *Why it might
  matter:* $\varepsilon \to 0$ *is* the conjecture, restated in the one
  coordinate that Lemma 2 says matters. *First step:* recompute $\varepsilon$
  at $k=4..7$ over **all** extremal witnesses rather than one, as done here
  for $k=3$; the entries will rise and the shape of the rise is the datum.
