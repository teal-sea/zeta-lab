# RESULTS — Erdős #126, exact search over choices of $S$ (support_60982bf6)

**Hunt, not a result. Nothing here is evidence for or against RH (`docs/08`).**

Support run for `0897a5a7`, arm label *exact-theorem-mining*. The bounded
question: redo the `hunts/r_186989` computation so it ranges over choices of $S$
rather than freezing the first $k$ primes, and use the computation only to
**discover and falsify structural lemmas**.

**Answer, in four lines.**

1. Ranging over $S$ **does not** beat the first $k$ primes for $k \le 5$
   (exhaustive over all $\binom{9}{k}$ subsets of the first nine primes, inside
   a box). The frozen constant `r_186989` flagged as its one door with real
   trade shape is, so far, slack.
2. A **proved normalization theorem** now explains why widening the search box
   in `r_186989` "changed not one row": the admissible sets are exactly the
   $S$-smooth dilates of primitive ones, so a wider box only produces bigger
   copies of the same set.
3. `r_186989`'s cleanest proposed lemma — *"$|A| \le p-1$ when $p \notin S$,
   by pigeonhole on residues mod $p$"* — is **false**, and false structurally,
   not just numerically. Explicit counterexamples for $p = 3, 5, 7$ below;
   $p = 2$ is the only prime for which the argument works at all.
4. The one **conjectural lemma** offered is *uniformly bounded height*: for
   each $k$ there is a $B(k)$ such that every $S$ with $|S|=k$, $2 \in S$ has a
   maximum-size admissible set inside $[1, B(k)]$. If it is true, $g(S)$ for
   fixed $S$ becomes a finite computation. Two natural explicit forms for $B$
   were tried and **killed by our own data**; see §5.

Reproduce: `python hunts/support_60982bf6/probe.py` (~30 s, the $S$-sweep),
then `probe2.py` and `probe3.py` (~2 min each). stdlib only; writes
`raw.json`, `raw2.json`, `raw3.json`, and `results.json` is the digest.

---

## 0. Setup, and which way the inequalities point

$S$ a finite set of primes; $A \subset \mathbb{Z}_{>0}$ finite is
**$S$-admissible** when every $a+b$ with $a \ne b$ in $A$ has all prime factors
in $S$. $g(S) = \max |A|$, and $g(k) = \max_{|S|=k} g(S)$.

Everything computed here is an exact maximum clique **inside a box** $[1,N]$ in
the graph $a \sim b \iff a+b$ is $S$-smooth. Write $g_N(S)$ for that. So:

- $g_N(S) \le g(S)$ always: **every number here is a lower bound on $g$.**
- A claim of the form *"$|A|$ can exceed $B$"* is refuted or confirmed
  **unconditionally** by a witness.
- A claim of the form *"$X$ is the maximum"* can never be refuted by this
  machinery, because refuting it needs an *upper* bound on $X$. Where a result
  below has that shape it is labelled **box-conditional** and the box is stated.

The solver was rewritten relative to `r_186989`: edges are generated from the
$S$-smooth sums themselves ($s$ smooth, $s = a+b$) rather than by scanning
$O(N^2)$ pairs, which is what made an exhaustive sweep over hundreds of $S$
affordable. Every reported witness is re-verified from scratch by full
trial-division prime support (`verify`), not by the smoothness table that found
it.

## 1. Ranging over $S$ — the sweep

All $\binom{9}{k}$ subsets $S$ of $\{2,3,5,7,11,13,17,19,23\}$, exhaustive
inside the box:

| $k$ | box $N$ | #$S$ | $\max_S g_N(S)$ | maximizers |
|---|---|---|---|---|
| 1 | 2000 | 9 | 2 | all nine |
| 2 | 2000 | 36 | 4 | $\{2,3\}$ only |
| 3 | 1200 | 84 | 5 | $\{2,3,5\}, \{2,3,7\}, \{2,3,13\}$ |
| 4 | 800 | 126 | 6 | $\{2,3,5,7\}$, $\{2,3,5,11\}$, $\{2,3,5,13\}$, $\{2,3,5,17\}$, $\{2,3,5,23\}$, $\{2,3,7,13\}$, $\{2,3,7,23\}$ |
| 5 | 600 | 126 | 8 | $\{2,3,5,7,11\}$, $\{2,3,5,7,13\}$, $\{2,3,5,7,19\}$, $\{2,3,5,11,13\}$ |

Three readings, in decreasing order of how much they are worth.

**(a) The first $k$ primes are among the maximizers at every $k \le 5$, and
never strictly beaten.** This is the answer to the brief's actual question.
`r_186989` froze $S$ = first $k$ primes and flagged that as "the door with
genuine trade shape … could in principle change the growth rate". Inside the
first nine primes and inside these boxes, it does not change even the constant.
The freeze is safe as far as this evidence reaches, and the door is narrower
than that hunt guessed.

**(b) $2 \notin S \Rightarrow g_N(S) = 2$, in all 218 such rows.** That
reproduces `r_186989`'s parity observation exhaustively rather than at one $S$.
It is a theorem, not a measurement — see Lemma 3.

**(c) Every maximizer at $k \ge 2$ contains $\{2,3\}$; every maximizer at
$k = 5$ contains $\{2,3,5\}$.** This is the sharpest *unproved* regularity the
sweep found. It is not implied by (a), and it is a much more useful shape than
"the first $k$ primes win", because it is a statement about $S$ that could be
iterated. We have no proof and no mechanism for it beyond $p=2$.

## 2. Lemma 1 (normalization). **Proved.**

> Let $S$ be a set of primes and $A$ an $S$-admissible set with $|A| \ge 2$, and
> put $d = \gcd(A)$. Then:
> 1. $d$ is $S$-smooth;
> 2. $A/d$ is $S$-admissible and primitive;
> 3. for any $S$-smooth $m \ge 1$, $A$ is $S$-admissible $\iff$ $mA$ is.
>
> Hence the $S$-admissible sets are **exactly** the sets $m A_0$ with $m$
> $S$-smooth and $A_0$ primitive $S$-admissible, and $g(S)$ is attained on a
> primitive set.

*Proof.* (1) Pick $a \ne b$ in $A$. Then $d \mid a$ and $d \mid b$, so
$d \mid a+b$, and $a+b$ is $S$-smooth; a divisor of an $S$-smooth number is
$S$-smooth. (2) For $a \ne b$, $(a+b)/d$ divides $a+b$, hence is $S$-smooth.
(3) $m(a+b)$ is $S$-smooth iff both $m$ and $a+b$ are, and $m$ is $S$-smooth by
hypothesis. $\square$

**What it buys.** `r_186989` reported, as a puzzle, that widening the box by a
factor of 30–60 "changed not one row" while "every optimal witness lives well
below 50". Lemma 1 is the explanation and it removes the puzzle: a wider box
contains the dilates $2A_0, 3A_0, 6A_0, \dots$ of every small optimum, so the
number of optima explodes with $N$ while the maximum size does not move. Our own
solver, run at $N = 20000$ on $S=\{2,3,5\}$, returns
$\{120, 2280, 3720, 10680, 19320\}$ — which is $40 \cdot \{3, 57, 93, 267, 483\}$,
a dilate, not a new phenomenon.

It also says the right question about the search box is **not** "how big is $N$"
but "how tall is the smallest primitive optimum". That is Conjecture 1.

**Evidence that the lemma is stated right:** all 381 witnesses produced by the
sweep were checked; $\gcd(A)$ was $S$-smooth in 381/381 and $A/\gcd(A)$ was
admissible in 381/381 (`raw2.json`, `normalization_checks`).

## 3. Refutation: the mod-$p$ pigeonhole lemma is false. **Unconditional.**

`r_186989`, loose thread 3, proposes:

> *"prove $|A| \le p-1$ when $p \notin S$ is small, by pigeonhole on residues
> mod $p$ against the pairing $r \leftrightarrow -r$"*

and calls it "the only clean iterable statement the run found". It is false for
every odd $p$, and the reason is structural.

**Why the pigeonhole does not close.** $p \notin S$ forces
$a + b \not\equiv 0 \pmod p$ for distinct $a,b \in A$. That constrains the set
$R$ of residues *occupied* by $A$: $R \cap (-R) \subseteq \{0\}$, and at most
one element of $A$ lies in the class $0$. But for odd $p$ and $r \not\equiv 0$,
$r + r = 2r \not\equiv 0 \pmod p$, so **arbitrarily many elements of $A$ may
share one nonzero class**. The pigeonhole bounds the number of occupied classes
by $\tfrac{p-1}{2} + 1$; it bounds $|A|$ by nothing. $p = 2$ is the unique prime
for which $2r \equiv 0$ for *every* $r$, which is exactly why the parity
argument works there and nowhere else.

**Counterexamples** (each $A$ re-verified by trial division; $p \notin S$;
search over all $S$ of size 5 and 6 inside the first nine primes with $2\in S$,
box $N = 400$):

| $p$ | lemma claims $|A| \le$ | found $|A|$ | $S$ | $A$ |
|---|---|---|---|---|
| 3 | 2 | **6** | $\{2,5,7,11,23\}$ | $\{5,45,65,95,155,395\}$ |
| 5 | 4 | **8** | $\{2,3,7,11,13,17\}$ | $\{12,36,60,132,156,252,276,372\}$ |
| 7 | 6 | **8** | $\{2,3,5,11,13\}$ | $\{8,24,40,56,64,136,152,376\}$ |
| 11 | 10 | 9 | $\{2,3,5,7,13,17\}$ | — (not refuted at this reach) |
| 13 | 12 | 9 | $\{2,3,5,7,11,17\}$ | — (not refuted at this reach) |

The smallest counterexample is already inside `r_186989`'s own arm-2 table:
$S = \{2,5,7\}$, $A = \{1,3,7,13\}$, sums $4,8,14,10,16,20$, and $3 \notin S$
with $|A| = 4 > 2$. The hunt had a counterexample to its own proposed lemma in
its own data.

$p = 11, 13$ are **not refuted here**, and that is a reach limit rather than
evidence: refuting them needs $|A| \ge 11$, and the largest admissible set we
can exhibit at $k \le 6$ has $|A| = 10$. The structural argument above says the
*proof method* cannot work for any odd $p$; whether the *bound* happens to hold
for larger $p$ at small $k$ is a different and uninteresting question, since
$g(k)$ grows and $p$ does not.

**Repaired statement (proved), Lemma 3.**

> Let $p \notin S$. Then $A$ meets at most one of $\{r, -r\}$ for each
> $r \not\equiv 0 \pmod p$, and $|A \cap p\mathbb{Z}| \le 1$. Consequently
> $|A| \le 2$ when $p = 2$, and **no bound on $|A|$ follows when $p$ is odd**.

The $p=2$ half is the parity statement `r_186989` already had. The general half
is a constraint on the *residue support* of $A$, not on its size. It is still
worth having — it is a real restriction, it holds simultaneously for every prime
outside $S$, and it is the natural place a counting argument would start — but
it is not the iterable size bound the thread hoped for.

## 4. Refutation: $g$ is not monotone in the size of the primes. **Box-conditional.**

The most natural way to *prove* claim 1(a) would be a monotonicity lemma:
replacing a prime of $S$ by a larger one cannot increase $g$. That is false in
the box.

$$g_{20000}(\{2,3,11\}) = 4 \qquad\text{while}\qquad g(\{2,3,13\}) \ge 5,$$

witness $\{1,2,7,11,25\}$ (sums $3, 8, 12, 26, 9, 13, 27, 18, 32, 36$). The
sweep contains **29** such violations among $k \le 5$; other clean ones are
$g(\{2,3,7,11\}) \le 5 < 6 \le g(\{2,3,7,13\})$ and
$g(\{2,3,5,19\}) \le 5 < 6 \le g(\{2,3,5,23\})$.

*Direction of the conditionality:* the "$\ge$" halves are witnesses and
unconditional; the "$\le$" halves are exhaustive only inside the stated box. So
this refutes the monotonicity lemma **conditional on** $g(\{2,3,11\}) = 4$,
which is exhaustive to $N = 20000$ and is where the height conjecture below
would make it unconditional.

*Why it fails, informally:* what matters is not how large a prime is but where
its multiples sit relative to the smooth semigroup. $13$ is useful because
$13 = 1 + 12$ and $26 = 2 + 24$ put it one smooth step from small $\{2,3\}$-smooth
numbers; $11$ is not. A lemma about $S$ will have to be about additive position,
not about size, and that is a genuine finding about the shape of the problem.

## 5. Conjecture 1 (uniformly bounded height) — the lemma offered

> **Conjecture (uniformly bounded height).** For an admissible family define
> $$h(S) \;=\; \min\{\max A \;:\; A \text{ is } S\text{-admissible},\; |A| = g(S)\}.$$
> Then for every $k$ there is a finite $B(k)$ with
> $$h(S) \;\le\; B(k) \qquad \text{for every } S \text{ with } |S| = k,\ 2 \in S,$$
> **uniformly over all $k$-element sets of primes**, not merely over $S$ built
> from small primes.

Two remarks on what is and is not being claimed. $h(S)$ is finite for each
individual $S$ for trivial reasons ($g(S)$ is finite by Erdős–Turán, and any
maximum set has a largest element); the content is the **uniformity in $S$**.
And by Lemma 1 the minimum is attained on a *primitive* set, so $h$ is a
statement about genuinely distinct sets rather than about dilates — without
Lemma 1 the quantity would not even be the right one to bound.

**Two explicit forms were tried and killed by this run's own data.** This is
worth recording because both are the fits a reader would guess from the
`r_186989` remark that "every optimal witness lives well below 50":

| Proposed $B(k)$ | Killed by |
|---|---|
| $2^{k+2}$ | $h(\{2,3,5\}) = 47 > 32$ |
| $2^{k+3}$ | $h(\{2,3,7,13\}) = 159 > 128$ |

So the conjecture is offered **without a constant**, and the absence of one is
the honest state of the evidence, not an omission. Fifteen data points cannot
choose between $C^k$, $2^{2^k}$ and worse.

**Why it is the right thing to conjecture.** `r_186989`'s stated structural gap
is that "the bounded search is structurally incapable" of an upper bound on
$g(k)$. Uniform height bounding is the missing ingredient for *half* of that:

- With $B(k)$ explicit, **$g(S)$ for a fixed $S$ becomes a finite computation** —
  a maximum clique inside $[1, B(k)]$ — and every "$\le$" in §4 and in
  `r_186989`'s table stops being box-conditional.
- It is **not** by itself enough for $g(k) = \max_{|S|=k} g(S)$. That needs a
  second ingredient: a bound on which primes can appear in a maximizing $S$.
  §4 shows that ingredient is delicate — large primes are not automatically
  worse — so we flag it as a separate open gap rather than folding it in. Any
  claim that Conjecture 1 alone finitises $g(k)$ would be wrong.

One encouraging measurement about that second gap: even where an individual $S$
needs a tall witness ($h(\{2,3,7,13\}) = 159$), the *maximum over $S$* at that
$k$ is attained at small height ($g(\{2,3,5,7\}) = 6$ at $h = 11$). So the
height that matters for $g(k)$ may be much smaller than $\max_S h(S)$.

**Evidence.** Two independent kinds, both in §7.

- *Exact heights.* $h_{\text{box}}(S)$ computed by bisection for 15 sets $S$,
  $k \le 6$, all 15 primitive-normalised witnesses re-verified.
- *Box stability.* For each of those $S$, the maximum over the full box
  ($20000$ for $k \le 3$, $4096$ for $k = 4$, $1024$ for $k \ge 5$) equals the
  maximum already found inside $[1,256]$. This is `assert`ed inside `probe3.py`,
  so the run fails loudly rather than silently if it ever stops holding.

**Limits, stated plainly.**

- The heights are $h_{\text{box}}(S)$, not $h(S)$: the smallest $N$ at which the
  *box* maximum is reached. If some $S$ has a larger optimum outside the box,
  its true $h$ is larger and that row is void. **The conjecture is verified for
  no $S$**; it is *consistent with* every $S$ measured.
- $k \le 6$, and $S$ drawn only from the first nine primes — which is precisely
  the regime the conjecture's uniformity clause is about, so the evidence is
  weakest exactly where the statement is strongest.
- $2 \in S$ is required; without it $g = 2$ (Lemma 3) and the statement is
  vacuous.
- **No route to a proof was found here.** The conjecture is offered because it
  is sharp, cheap to attack, and would be *disproved* by a single $S$ with a
  tall optimum — a search this machinery can run and which we did not have the
  budget to run broadly.

## 6. Audit of `hunts/r_186989/RESULTS.md`

The brief asked for an audit rather than trust. Independently re-derived with a
different solver:

| Claim in `r_186989` | Verdict here |
|---|---|
| $g(k) \ge 2,4,5,6,8,10$ for $k \le 6$ (first $k$ primes) | **Reproduced**, independent solver, witnesses re-verified. |
| $f$/$g$ inverse-staircase restatement, $f(n)/\log n \to \infty \iff g(k)^{1/k} \to 1$ | **Correct.** |
| §2 lemma $f(n-1) \le f_0(n) \le f(n)$ | **Correct**; proof is sound as written. |
| §4: a composition law $g(k_1+k_2) \ge g(k_1)g(k_2)$ would *refute* #126, via Fekete and $g(1)=2$ | **Correct**, and the $g(1) \le 2$ argument is sound. This is the most valuable thing in that hunt. |
| "$2 \in S$ or not, then a wobble of one" is the whole $S$-dependence | **Understated.** At $k=5$ the range over $S$ with $2 \in S$ is $4$ to $8$ — a factor of two, not a wobble. The conclusion (first $k$ primes are not beaten) survives; the characterisation of the $S$-landscape does not. |
| "the optima are tiny and the universe does not matter" | **Correct but unexplained there.** Lemma 1 explains it. |
| loose thread 3: $|A| \le p-1$ for $p \notin S$ | **False.** §3. |
| doors table: $S$ is "the door with genuine trade shape" | **Not supported.** Exhaustive over the first nine primes for $k \le 5$, optimising $S$ buys nothing over the first $k$ primes. |

## 7. Measured heights

$g_{\text{box}}$ is the exact maximum inside the stated box; $h$ is the smallest
$N$ at which that maximum is already attained, by bisection. Every witness
re-verified by trial division. Generated by `probe3.py`; also in
`results.json`.

| $S$ | $k$ | box | $g_{\text{box}}$ | $h$ | smallest witness |
|---|---|---|---|---|---|
| $\{2\}$ | 1 | 20000 | 2 | 3 | $\{1,3\}$ |
| $\{2,3\}$ | 2 | 20000 | 4 | 11 | $\{1,5,7,11\}$ |
| $\{2,3,5\}$ | 3 | 20000 | 5 | 47 | $\{3,7,17,33,47\}$ |
| $\{2,3,7\}$ | 3 | 20000 | 5 | 13 | $\{1,3,5,11,13\}$ |
| $\{2,3,11\}$ | 3 | 20000 | 4 | 11 | $\{1,5,7,11\}$ |
| $\{2,3,13\}$ | 3 | 20000 | 5 | 25 | $\{1,2,7,11,25\}$ |
| $\{2,3,5,7\}$ | 4 | 4096 | 6 | 11 | $\{1,3,5,7,9,11\}$ |
| $\{2,3,5,11\}$ | 4 | 4096 | 6 | 17 | $\{1,3,5,7,15,17\}$ |
| $\{2,3,7,11\}$ | 4 | 4096 | 5 | 13 | $\{1,3,5,11,13\}$ |
| $\{2,3,7,13\}$ | 4 | 4096 | 6 | **159** | $\{3,9,23,33,75,159\}$ |
| $\{2,3,5,7,11\}$ | 5 | 1024 | 8 | 31 | $\{1,2,5,9,13,19,23,31\}$ |
| $\{2,3,5,7,13\}$ | 5 | 1024 | 8 | 47 | $\{1,2,3,5,7,23,25,47\}$ |
| $\{2,3,5,11,13\}$ | 5 | 1024 | 8 | 47 | $\{1,3,5,7,8,17,19,47\}$ |
| $\{2,3,5,7,11,13\}$ | 6 | 1024 | 10 | 47 | $\{1,3,5,7,9,13,17,19,23,47\}$ |
| $\{2,3,5,7,11,17\}$ | 6 | 1024 | 9 | 69 | $\{1,3,6,15,21,27,29,39,69\}$ |

Two things to read off. **Height is not monotone in $k$** — $159$ at $k=4$,
$47$ at $k=6$ — so it is not a quantity that will yield to a naive induction.
And **$h$ is far below the box in every row**, by factors of $7$ to $6700$,
which is the actual content of `r_186989`'s "the universe does not matter".

## 8. What we could not settle

- **No upper bound on $g(k)$.** Unchanged from `r_186989`, and Conjecture 1 is
  the only route this arm can see to one.
- **No proof of any $S$-level regularity beyond $p=2$.** The observation that
  every maximizer contains $\{2,3\}$ is unexplained.
- **$k \ge 6$ over all $S$.** The sweep stops at $k=5$ over all subsets; $k=6,7$
  were only spot-checked. The clique search cost grows quickly and the honest
  statement is that we did not run it, not that it is impossible.
- **Whether the growth rate depends on $S$ at all.** The sweep bounds the
  constant, not the rate; nothing here separates $g(k)^{1/k} \to 1$ from
  $g(k)^{1/k} \to c > 1$, and we agree with `r_186989` that finite data cannot.

## The doors

This hunt measured a ceiling ($g_N(S)$ over all $S$), so it owes the list.

**1. Active constraints at the optimum.**

| Rank | What binds | Evidence |
|---|---|---|
| 1 | **$2 \in S$.** Proved, total. | 218/218 rows with $2 \notin S$ give exactly 2 (Lemma 3). |
| 2 | **The additive position of the primes of $S$ relative to the smooth semigroup**, not their size. | 29 violations of prime-size monotonicity; $\{2,3,13\}$ beats $\{2,3,11\}$. |
| 3 | **Height, not box width.** The optimum is reached inside $[1,256]$ in every case measured, with boxes up to $20000$. | §7. |
| 4 | **$|S|$, weakly.** $2,4,5,6,8,10$ for $k=1..6$. | §1. |

**2. Frozen-constant inventory.**

| Frozen | Value | What relaxing it trades |
|---|---|---|
| prime pool for $S$ | first 9 primes | The sweep cannot see an $S$ using a large prime. Cheap to widen at $k \le 3$; the count $\binom{\pi(P)}{k}$ is the cost. **This is the door with real trade shape now**, because §4 shows large primes are not automatically worse. |
| $k_{\max}$ over all $S$ | 5 | The only way to test claim 1(a) further. Cost is $\binom{9}{6} = 84$ searches at $k=6$, affordable; $k=8,9$ needs a better clique solver. |
| box $N$ | 600–20000 | Shown slack twice over. **Low value** — and Lemma 1 says why, which is more useful than the measurement. |
| the exponent $k+2$ in Conjecture 1 | fitted to $k\le 6$ | Any $C^k$ fits the same data. Relaxing it costs nothing and buys honesty; tightening it is what would make the conjecture bite. |
| requiring $A \subset \mathbb{Z}_{>0}$ | yes | `r_186989` §2 already handles the $0 \in A$ variant. |

**3. Information class.** Doors 1–3 stay **inside** the data this family reads
(integers and the smoothness of their pairwise sums), so — as `r_186989`
correctly said — they cannot produce an upper bound on $g(k)$ *by enumeration*.
The exception, and the reason this arm is not a repeat of that one, is
**Conjecture 1**: it is a statement about this same data whose *truth* would
license a finite computation of $g(k)$, i.e. it converts an in-class search into
an out-of-class conclusion. Proving it almost certainly requires the $S$-unit
machinery (Evertse–Győry bounds on $x + y = 1$ in $S$-units) that `r_186989`
identified as the real wall. The difference is that Conjecture 1 gives that
machinery a **concrete finite target** — bound the height of a solution, not the
number of them — which is a smaller ask than the full problem.

## Loose threads

- **Every maximizer contains $\{2,3\}$, and at $k=5$ contains $\{2,3,5\}$.**
  *Why it might matter:* it is an $S$-level statement that could be iterated
  into an induction on $k$, which is what an upper-bound proof needs and what
  neither hunt has. *First step:* test it at $k=6,7$ over all subsets of the
  first ten primes, and look for the first counterexample.
- **Prime-size monotonicity fails, additive position seems to be what matters.**
  *Why:* it says any $S$-level lemma must be stated in terms of $p$'s relation to
  the $S$-smooth semigroup. *First step:* for $k=3$, correlate $g(\{2,3,p\})$
  against the distance from $p$ to the nearest $\{2,3\}$-smooth number, over the
  first 30 primes.
- **The height ladder is the cheap attack on Conjecture 1.** *First step:* for a
  few hundred random $S$ of size 4–6 drawn from the first 25 primes, check
  whether the box maximum at $N = 4096$ is ever bigger than at $N = 2^{k+2}$. One
  hit kills the conjecture.
- **`r_186989`'s OEIS thread is still open.** We did not run it.
