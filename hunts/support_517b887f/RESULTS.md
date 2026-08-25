# RESULTS — Erdős #126, ORIGINAL-PROOF arm (support run 517b887f)

**Hunt, not a result. Nothing here is evidence for or against RH (`docs/08`).**

**Answer to the question asked: no. Processing several primes jointly, or
reordering them, cannot replace $2^k$ by $(2-\delta)^k$, because the quantity
that the whole Erdős–Turán architecture reduces to is order-blind by
definition, and bounding it below by $|A|/(2-\delta)^k$ is not a refinement of
the 1934 bookkeeping: it is logically equivalent to the conjectured bound
itself.** Details in §4. Two further findings that were not asked for and that
change how the classical step must be written down are in §3.

Reproduce with `python3 hunts/support_517b887f/probe.py` (~30 s, stdlib only,
writes `results.json`).

---

## 1. The proof, reconstructed

Notation. $A \subset \mathbb{Z}^+$ finite, $|A| = n$, and
$S = \{p : p \mid a+b \text{ for some } a \ne b \in A\}$, $|S| = k$. Write
$s$ for the number of *odd* primes in $S$. Define

$$c(A) \;=\; \max\{|A'| : A' \subseteq A,\ a+b \text{ is a power of } 2
\text{ for all } a \ne b \in A'\}.$$

**Step 1 (base case, archimedean).** $c(A) \le 2$. *Proof.* Suppose
$a<b<c$ positive with $a+b = 2^x$, $a+c = 2^y$, $b+c = 2^z$. Then $x<y<z$, so
$z \ge y+1$ and
$2a = (a+b)+(a+c)-(b+c) = 2^x + 2^y - 2^z \le 2^x + 2^y - 2^{y+1} = 2^x - 2^y < 0$,
impossible. $\square$

This is the only step that uses the ordering of $\mathbb{Z}$. Every other step
is local (residues mod $p$).

**Step 2 (selection, one binary choice per odd prime).** For an odd prime $q$
and a finite $B$, the residue classes mod $q$ pair up as $\{r,-q+r\}$ under
$r \mapsto -r$, with $0$ its own partner. Two elements in the same nonzero
class sum to $2r \not\equiv 0$; two elements in opposite classes sum to $0$;
two elements of class $0$ sum to $0$. So keeping the larger side of each
$\{r,-r\}$ pair and at most one element of class $0$ gives $B' \subseteq B$
with $q \nmid a+b$ throughout and

$$|B'| \;\ge\; \tfrac{1}{2}\bigl(|B| - n_0(q)\bigr) + \min(n_0(q),1),
\qquad n_0(q) = \#\{a \in B : q \mid a\}. \tag{$\star$}$$

**Step 3 (assembly).** Iterating Step 2 over the $s$ odd primes and *assuming*
the clean form $|B'| \ge |B|/2$ of ($\star$) gives $c(A) \ge n/2^s$. With
Step 1, $n \le 2 \cdot 2^{s} = 2^{k}$ when $2 \in S$ (and $n \le 2$ when
$2 \notin S$, by parity). That is the Erdős–Surányi form
$g(k) \le 2^k$; the 1934 paper's $3 \cdot 2^{k-1}$ is the same architecture
with the base case used as "$\ge 3$ elements is impossible" and a weaker
selection.

**So the factor 2 per prime enters in exactly one place: the $\pm$ choice in
Step 2.** There is no second leak. The "3" of $3\cdot 2^{k-1}$ is the base
case, and Erdős–Surányi already collected it.

Tightness of the endpoints, against the measured lower bounds for $g$
(`hunts/r_186989`, audited below): $g(1) = 2 = 2^1$ and $g(2) \ge 4 = 2^2$,
so **the Erdős–Surányi bound is attained at $k=1,2$**. Any $(2-\delta)^k$ must
therefore carry a constant $> 1$ and can only bite for $k \ge 3$.

## 2. Audit of `hunts/r_186989/RESULTS.md`

Checked, not trusted. Its arm-3 composition argument is correct as written
(a superadditive $\log g$ plus Fekete forces $g(k) \ge g(1)^k = 2^k$, refuting
the conjecture), and its $g(1) \le 2$ proof is the Step 1 argument above. Its
$g_N$ witnesses re-verify: this probe recomputed the extremal sets
independently in smaller boxes and reproduced $n = 2,4,5,6,8$ for
$k = 1,\dots,5$ with the same or equivalent witnesses. Its claim that the
optima live below 50 held in every box used here. One thing it does not say
and should: at $k = 1, 2$ its lower bounds **meet** the classical upper bound
$2^k$, which is the sharpest single fact available about how much room the
1934 argument has.

## 3. Two defects in the standard statement of Step 2

Both are stated as sketches in the literature summaries with the clean
$|B'| \ge |B|/2$; both are false as stated. Witnesses are exact and
re-verified by trial division in `results.json`.

**3.1 The per-prime halving is false.** Take
$A = \{1, 3, 15, 21, 33\}$. Every off-diagonal sum is
$\{2,3,11,17\}$-smooth ($4, 16, 22, 34, 18, 24, 36, 36, 48, 54$), so $A$ is
admissible with $k=4$. For $q = 3$: four of the five elements are divisible by
$3$, so any subset in which $3$ divides no sum contains at most one of them.
The maximum is $\{1,3\}$, of size $2 < 5/2$. ($\star$) is what actually holds;
the class-0 term is not removable. The unbounded version is
$B = q\cdot C \cup \{x\}$: the $q$-clean subset of $B$ has size $2$ however
large $C$ is, so **there is no constant halving lemma for a single odd
prime**.

**3.2 The assembled bound $c(A) \ge n/2^s$ is false without primitivity.**
$A = \{3, 9, 21, 51, 141\} = 3 \cdot \{1,3,7,17,47\}$ has all off-diagonal
sums $\{2,3,5\}$-smooth, $n = 5$, $s = 2$, and **no** pairwise sum is a power
of $2$, so $c(A) = 1 < 5/4$. The repair is the scaling descent that the
sketches leave implicit: divide by $\gcd(A)$ first. Here that returns
$\{1,3,7,17,47\}$, for which $1+3 = 4$ and $c = 2$.

Both defects are about the *route*, not the theorem: $n = 5 \le 2^4$ and
$n = 5 \le 2^3$ respectively, so nothing published is contradicted. What is
contradicted is the line-by-line reconstruction the brief asked for. A correct
write-up needs primitivity plus ($\star$), not "halve once per prime".

**Order matters for the intermediate step, and only there.** In 3.1, taking
$q = 11$ first instead of $q = 3$ gives a clean subset of size $4 = 0.8n$, so
reordering rescues that instance. This is the strongest form of the brief's
"changing the order" idea that survives, and §4 says why it buys nothing.

**Exhaustive check of the repaired form.** Over all $104{,}183$ admissible
sets of size $\ge 2$ inside the boxes $[1,300]$, $[1,200]$, $[1,150]$ for
$S = \{2,3,5\}, \{2,3,5,7\}, \{2,3,5,7,11\}$: **zero** primitive violations of
$c(A) \ge n/2^s$, and $11$ non-primitive violations, all of them scaled
copies. The repaired lemma is measured-true in that range and is exactly tight
at $A = \{1,2,4,8\}$, where $n = 4$, $s = 2$, $c = 1 = n/2^s$.

## 4. The barrier

**Theorem (order-blindness).** Everything the architecture can deliver is
contained in the single quantity $c(A)$. Step 1 gives $c(A) \le 2$
unconditionally, and $c(A) \ge 1$ trivially, so $c(A) \in \{1,2\}$ for every
admissible $A$. Consequently, for any function $\varphi$:

$$\bigl[\,\forall A \text{ admissible}: c(A) \ge |A|/\varphi(k)\,\bigr]
\iff \bigl[\,g(k) \le 2\varphi(k)\,\bigr] \text{ up to a factor } 2 .$$

$c(A)$ is defined by a maximum over subsets and does not mention any prime
ordering, any grouping of primes, or any valuation. Hence **no reordering and
no joint processing of primes can change what this architecture proves**; they
can only change whether a particular greedy selection attains the maximum.
Proving the selection lemma with $\varphi(k) = (2-\delta)^k$ is precisely as
hard as proving $g(k) \le 2(2-\delta)^k$. It is not a sharpening of the 1934
bookkeeping; it is the target restated.

**Corollary (why "joint" was the natural guess, and why it fails).** At the
level of residues alone, joint processing is provably worthless: for any
distinct odd primes $q_1,\dots,q_s$, the CRT configuration
$x_\varepsilon \equiv \varepsilon_i \pmod{q_i}$, $\varepsilon \in \{\pm1\}^s$,
has $2^s$ points, and $x_\varepsilon + x_\delta \equiv 0 \pmod{q_i}$ exactly
when $\varepsilon_i = -\delta_i$, so a subset clean for **every** $q_i$ must
have $\varepsilon = \delta$: the maximum jointly clean subset is $1$ out of
$2^s$. Verified by brute force for $s = 2,3,4$. Worst-case residue data
realises the $2^s$ loss exactly, whether the primes are taken one at a time or
all at once.

**And the worst case is realisable by genuine admissible sets, not only by
residue patterns.** The sweep found, for each $S$ tested, admissible sets with
$c(A) = 1$ and $|A|$ equal to the box maximum:

| $S$ | witness | $n$ | $s$ | $c(A)$ | $n/2^s$ |
|---|---|---|---|---|---|
| $\{2,3,5\}$ | $1,2,4,8$ | 4 | 2 | 1 | 1.00 |
| $\{2,3,5,7\}$ | $1,19,29,41,71,79$ | 6 | 3 | 1 | 0.75 |
| $\{2,3,5,7,11\}$ | $1,2,13,23,43,47,97$ | 7 | 4 | 1 | 0.44 |

$\{1,2,4,8\}$ is the sharp one: a primitive admissible set on which the
repaired selection lemma holds with equality. So the constant $2$ cannot be
lowered at $s=2$ by any argument that proves the selection lemma, and any
$(2-\delta)^k$ statement must be asymptotic with a constant in front.

## 5. The smallest missing lemma

The only place where new information could enter is the class-0 term of
($\star$), i.e. the interaction between $A_0 = \{a \in A : q \mid a\}$ and
$A_* = A \setminus A_0$. Everything the architecture currently knows about
$A_0$ is that it is a scaled copy problem, and the descent handles it at zero
cardinality cost only when $A_0 = A$. The missing lemma is:

> **(L)** There is a function $\psi$ with $\log\psi(k) = o(k)$ such that for
> every primitive admissible $A$ and every odd $q \in S$,
> $\#\{a \in A: q \mid a\} \le \psi(k) \cdot \#\{a \in A : q \nmid a\}$.

(L) plus ($\star$) gives a selection loss of $2(1+\psi)$ per prime, which is
still exponential, so **(L) alone does not suffice** and I want to be explicit
about that. Its interest is that it is the only sub-question in the
architecture that is not already equivalent to the full conjecture, and it is
a *two-set* smoothness question: the cross sums $x + qc$ ($x \in A_*$,
$qc \in A_0$) must all be $S$-smooth, which is exactly the regime of
Győry–Stewart–Tijdeman 1986 ($\omega\bigl(\prod_{a\in A, b\in B}(a+b)\bigr)
\gg \log|A|$ for two sets). That is the effective tool the 1934 argument does
not use, and it is where an original contribution would have to sit.

## 6. What this arm could not settle

- **No improvement was proved.** No $(2-\delta)^k$ bound, and §4 argues that
  none is reachable inside this architecture without solving the problem.
- **(L) is untested.** It could be false; the probe did not search for
  counterexamples to it, and one primitive admissible set with $A_0$
  dominating would kill it. That is one cheap follow-up sweep.
- **The barrier is against the architecture, not against the problem.** A
  proof that abandons "pass to a subset with power-of-2 sums" is untouched by
  §4. The $S$-unit route (Evertse–Győry counting for $x+y=1$) is such a proof
  and is where the prior hunt also pointed.
- **All witnesses are exhaustive only inside small boxes.** The measured
  $g_N(k)$ are lower bounds on $g(k)$; nothing here bounds $g$ from above
  beyond the classical $2^k$.

## The doors

This arm measured a ceiling (the $2$ per prime), so it owes the list.

**1. Active constraints at the optimum.**

| Rank | What binds | Evidence |
|---|---|---|
| 1 | **$c(A) \le 2$ and $c(A) \ge 1$**, i.e. the target quantity has range $\{1,2\}$, so the selection lemma carries the entire statement. | §4, proved. |
| 2 | **The class-0 term of ($\star$).** It is the only term the argument does not control, and it is what breaks the naive halving. | §3.1, explicit witness. |
| 3 | **Primitivity.** Without it the assembled bound is false outright. | §3.2, explicit witness. |

**2. Frozen-constant inventory.**

| Frozen | Value | What relaxing it trades |
|---|---|---|
| the $\pm$ partition of $(\mathbb{Z}/q)^*$ | 2 parts | The only partition making within-part sums nonzero mod $q$. Refining it costs more parts, not fewer. **No trade shape**: this is a group-theoretic fact, not a tuning choice. |
| base case size | 3 elements / $c \le 2$ | Sharp (the pair $\{1,3\}$ realises $c=2$). No slack. |
| prime order in the selection | ascending | Real trade shape at the *instance* level (§3.1: $q=11$ before $q=3$ turns $0.4n$ into $0.8n$) and provably none at the theorem level (§4). |
| search boxes | 150–300 | Slack: the prior hunt's 60× widening moved nothing, and this arm reproduced its optima in boxes 20× smaller. |

**3. Information class.** The whole architecture reads only
$\bigl(a \bmod q\bigr)_{q \in S}$ plus one archimedean comparison in the base
case. It discards the valuations $v_q(a+b)$ entirely. Any door that could move
$g(k)$ below $2^k$ must **read more**: either the valuation vectors (the
$S$-unit equation regime) or the two-set structure of (L). Both are outside
this family's configuration ceiling.

## Threads

- **(L) is one sweep away from a verdict.** Search the admissible sets already
  enumerated for a primitive one whose class-0 part exceeds its class-$*$ part
  for some odd $q$. If one exists, (L) is dead and §5 loses its only
  non-circular sub-question.
- **$\{1,2,4,8\}$ generalises to $\{1,2,4,\dots,2^m\}$**, whose sums are
  $2^i(1+2^{j-i})$ and whose prime support is $\{2\} \cup \{$primes dividing
  $2^t+1, t \le m\}$. This is a cheap explicit family relating $g(k)$ to the
  factorisations of Fermat-type numbers $2^t+1$, and it is where the
  selection lemma is tight at small $s$. Worth checking whether it, or a
  variant, gives a better lower bound on $g(k)$ than the clique search for
  large $k$, since it needs no search at all.
