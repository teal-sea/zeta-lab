# RESULTS: Erdős #126, counterexample arm (support_6cdfd2e3)

**Hunt, not a result. Nothing here is evidence for or against RH (`docs/08`).**
Support run for `r_186989`, arm label `construction-refutation`.

**Verdict: no counterexample construction, and the tensor lane is closed
conditionally.** The arm was asked for an algebraic / CRT / recursive / tensor /
composition construction with $|A|$ exponential in $|S|$. It found none, and it
proves why the most promising of those five is blocked: **every mixed pair of a
tensor construction is a solution of the $S$-unit equation $x+y=1$**, so a
tensor with $|A|$ exponential in $k$ would require that equation to have
exponentially many solutions in $|S|$. The best construction known for that
equation is subexponential, $\exp(c(s/\log s)^{1/2})$ (Erdős–Stewart–Tijdeman).
The lane therefore cannot refute #126 without first breaking a separate,
well-studied barrier.

Two corrections to the parent go the other way and matter more than the
non-result:

1. **The refutation bar is far lower than a composition law.** $r\_186989$ §4
   asks for $g(k_1+k_2)\ge g(k_1)g(k_2)$. A *bounded prime cost per doubling*
   already refutes #126. That is a much smaller gadget to hunt for.
2. **An anti-composition theorem does not prove #126.** The converse of §4's
   implication fails, by an explicit staircase. This is a live trap for the
   proof arm, which the parent's closing sentence walks into.

Reproduce with `python3 hunts/support_6cdfd2e3/probe.py` (~2 min, stdlib only,
writes `results_probe.json`). Everything measured below is inside a bounded box
and is a lower bound on $g(k)$ and only that.

---

## 0. Notation

$S$ is a set of $k$ primes; $A$ a finite set of distinct positive integers is
**admissible for $S$** when $a+b$ is $S$-smooth for every $a\ne b$ in $A$;
$g(k)=\max|A|$ over all $S$ with $|S|=k$. $P(n)$ is the set of prime factors of
$n$. #126 is $\log g(k)=o(k)$. $N(S)$ denotes the number of solutions of
$x+y=1$ in positive $S$-units $x,y\in\mathbb{Q}^{*}$ (Evertse 1984:
$N(S)\le 3\cdot 7^{2|S|+3}$).

## 1. Audit of `r_186989`

**Sound.** Every witness in its §3 table re-verified from scratch by trial
division (`parent_witness_audit` in `results_probe.json`, 7/7 admissible). Its
§2 sandwich $f(n-1)\le f_0(n)\le f(n)$ is correct as written. Its $g(1)=2$
proof is correct, and so is the Fekete step in §4.

**Independently reproduced, in a much smaller box.** A separate branch-and-bound
(bitset, greedy-colouring bound) exhaustive inside $[1,N]$:

| $k$ | $N$ | $g_N(k)$ | $g_N^{1/k}$ | witness |
|---|---|---|---|---|
| 1 | 400 | 2 | 2.000 | 113, 399 |
| 2 | 400 | 4 | 2.000 | 16, 80, 112, 176 |
| 3 | 400 | 5 | 1.710 | 6, 30, 186, 294, 354 |
| 4 | 400 | 6 | 1.565 | 24, 72, …, 312 |
| 5 | 400 | 8 | 1.516 | 9, 27, …, 351 |
| 6 | 400 | 10 | 1.468 | 6, 10, …, 390 |
| 7 | 300 | 11 | 1.409 | 6, 18, …, 294 |
| 8 | 260 | **14** | 1.390 | 2, 4, 8, 12, 20, 28, 32, 36, 52, 68, 76, 100, 124, 188 |
| 9 | 200 | **15** | 1.351 | 5, 10, …, 185 |

Rows 1–7 agree with the parent's, from a box 15–500× smaller. Rows 8 and 9 are
new: $g(8)\ge 14$, $g(9)\ge 15$. The $k$-th root continues to fall.

**One claim of the parent is false as stated**, and its falsity is a one-line
theorem rather than a search artifact.

> **Lemma 1 (dilation invariance).** If $A$ is admissible for $S$ and $c\ge 1$
> has $P(c)\subseteq S$, then $cA$ is admissible for $S$ and $|cA|=|A|$.
> *Proof.* $ca+cb=c(a+b)$ and $P(c(a+b))=P(c)\cup P(a+b)\subseteq S$. $\square$

So optimal witnesses are never unique and are **unbounded**: from any optimum,
$2^t A$ is another for every $t$ when $2\in S$. The parent's door-table entry
"every optimal witness has all elements $<50$" and the loose thread "the optimal
witnesses are all tiny, and nobody knows why" are both artifacts of ascending
branch order. The witnesses recovered here are $\{113,399\}$ at $k=1$ and
$\{16,80,112,176\}$ at $k=2$: same sizes, not tiny. The correct normalisation
is: divide out $\gcd(A)$, or state the claim as "*some* optimum is small".
The parent's follow-up suggestion (re-run with $N=2^{k+2}$ and compare) would
have measured nothing, since Lemma 1 already predicts the answer.

## 2. A rigorous superlinear lower bound

> **Lemma 2 (interval construction).** Let $S=\{p_1,\dots,p_k\}$ be the first
> $k$ primes and $m=\lfloor (p_{k+1}-1)/2\rfloor$. Then $A=\{1,\dots,m\}$ is
> admissible for $S$, so
> $$g(k)\;\ge\;\Big\lfloor \tfrac{p_{k+1}-1}{2}\Big\rfloor\;=\;\big(\tfrac12+o(1)\big)\,k\log k .$$
> *Proof.* Off-diagonal sums lie in $[3,2m-1]\subseteq[3,p_{k+1}-2]$. Any
> integer $n<p_{k+1}$ has every prime factor $\le n<p_{k+1}$, hence $\le p_k$,
> hence in $S$. The asymptotic is the prime number theorem. $\square$

This is elementary and is very likely folklore, but the parent's file contains
no lower bound on $g$ at all beyond finite search, and this one is *asymptotic*:
it proves $g(k)/k\to\infty$, which no bounded search can. It is also far from
the target: superlinear, not exponential.

It is weaker than the measured table for every $k$ tested ($m=11$ at $k=8$
against a measured 14), so it is not sharp either. Both facts are worth having:
the sequence 2, 4, 5, 6, 8, 10, 11, 14, 15 is bracketed below by
$\sim\frac12 k\log k$ and above by nothing.

## 3. The refutation bar, corrected downward

$r\_186989$ §4 shows that a full composition law $g(k_1+k_2)\ge g(k_1)g(k_2)$
refutes #126. True, and much more than is needed.

> **Proposition 3 (bounded-cost doubling suffices).** Suppose there are
> integers $k_0\ge 1$, a real $c>1$ and a $K$ with $g(k+k_0)\ge c\,g(k)$ for all
> $k\ge K$. Then $g(k)\ge g(K)\,c^{\lfloor (k-K)/k_0\rfloor}$, so
> $\liminf_k \log g(k)/k \ge (\log c)/k_0>0$ and #126 is **false**.
> *Proof.* Induction along the arithmetic progression $K,K+k_0,K+2k_0,\dots$,
> and $g$ is non-decreasing between the steps. $\square$

The gadget the counterexample arm should hunt is therefore not a tensor law but
the much weaker object: *a repeatable way to multiply $|A|$ by any fixed
$c>1$ at a fixed prime cost $k_0$.* Doubling for ten extra primes, forever,
refutes #126. That reframing is the most usable thing this run produces.

**Measured, against exactly that.** The cheapest repeatable doubling to try is
the dilated union $A\cup cA$, which by Lemma 1 is free only when $c$ is
$S$-smooth (and then it is not a doubling: $cA$ may overlap, and the cross sums
$a+ca'$ are new conditions). Exhaustive over $c\le 200$ with up to 12 extra
primes allowed:

| $k$ | $A$ | best union | extra primes needed |
|---|---|---|---|
| 2 | 1, 5, 7, 11 | $c=3$, size 8 | **6** (5, 7, 11, 13, 17, 19) |
| 3 | 1, 3, 7, 17, 47 | none exists |, |
| 4 | 1, 2, 3, 5, 7, 13 | $c=2$, size 11 | **7** (11, …, 31) |

Doubling cost 6 and 7 extra primes at $k=2$ and $k=4$; at $k=3$ no dilation
works at all inside the scan. The measured prime cost of doubling is growing
with $k$, not bounded, which is what Proposition 3 says #126 requires. This is
three data points and a bounded scan; it is evidence about the gadget's shape,
not a theorem.

## 4. Anti-composition is **not** sufficient for #126

The parent closes: "Erdős #126 … is asking for an **anti-composition theorem**".
That overstates the implication, and the overstatement would misdirect the proof
arm.

> **Proposition 4.** There exist non-decreasing $G:\mathbb{N}\to\mathbb{N}$ with
> $\limsup_k \log G(k)/k>0$ (i.e. #126 false for $G$) such that for every fixed
> $k_0$ and $c>1$, the law $G(k+k_0)\ge c\,G(k)$ fails for all but a density-zero
> set of $k$.
> *Proof.* Take a rapidly increasing $k_1<k_2<\cdots$ with $k_{j+1}/k_j\to\infty$
> and set $G(k)=2^{k_j}$ for $k_j\le k<k_{j+1}$. Then
> $\log G(k_j)/k_j=\log 2$, so $\limsup>0$. But $G(k+k_0)=G(k)$ unless
> $k\in[k_{j+1}-k_0,k_{j+1})$ for some $j$, a set of density zero. $\square$

$\log g$ is non-decreasing, so refutation of #126 is exactly
$\limsup_k \log g(k)/k>0$: a *sparse* sequence of jumps refutes it while every
uniform composition law fails. Killing all composition gadgets leaves #126
open. The honest statement of the parent's §4 is the one direction it proved:
composition ⟹ refutation. Not the converse.

## 5. The tensor lane, closed conditionally

This is the arm's main object. Let $A$ be admissible for $S$, $B$ for $T$, and
$C=A\cdot B=\{ab\}$ (assume the $|A||B|$ products are distinct). The
"grid lines" of $C$ are free: $ab+ab'=a(b+b')$ and $ab+a'b=b(a+a')$ are
$(S\cup T)$-smooth automatically. All the content is in the **mixed** pairs
$ab+a'b'$ with $a\ne a'$, $b\ne b'$. Write

$$u=ab+a'b',\qquad v=ab'+a'b,\qquad M=(a+a')(b+b').$$

> **Identity.** $u+v=M$ and $u-v=(a-a')(b-b')$.

$M$ is $(S\cup T)$-smooth for free. So the tensor is admissible exactly when the
smooth number $M$ splits as $u+v$ with both parts smooth, and dividing by $M$:

> **Theorem 5 (tensor ⟹ $S$-unit equation).** If $C=A\cdot B$ is admissible for
> $S\cup T$, then for every $a\ne a'\in A$, $b\ne b'\in B$ the pair
> $$x=\frac{ab+a'b'}{(a+a')(b+b')},\qquad y=\frac{ab'+a'b}{(a+a')(b+b')}$$
> is a solution of $x+y=1$ in positive $(S\cup T)$-units of $\mathbb{Q}^{*}$.
> *Proof.* $x+y=1$ by the identity. Numerators are $(S\cup T)$-smooth by
> admissibility of $C$; the denominator is $(a+a')(b+b')$ with $a+a'$
> $S$-smooth and $b+b'$ $T$-smooth. $\square$

> **Corollary 5.1 (the factors are bounded by the unit count).** Fix
> $a\ne a'\in A$ and put $\beta=b/b'$. Then
> $x=\dfrac{a\beta+a'}{(a+a')(\beta+1)}$ is a non-constant Möbius function of
> $\beta$ (non-constant because $a\ne a'$), hence injective in $\beta$. The
> ordered ratios $b_1/b_j$, $j=2,\dots,|B|$, are $|B|-1$ distinct values, so
> $$|B|\;\le\;N(S\cup T)+1,\qquad\text{and symmetrically}\qquad |A|\le N(S\cup T)+1 .$$

Unconditionally this is **weaker** than Erdős–Turán: Evertse gives
$N\le 3\cdot 7^{2s+3}$, far above $3\cdot 2^{k-1}$. Say that plainly, Theorem 5
buys no new upper bound on $g$. Its value is directional:

- **Conditional obstruction.** If $N(S)=\exp(o(|S|))$, the expected truth, and
  the standard conjecture in this area, then any tensor construction has
  $|A|,|B|=\exp(o(k))$ and so $|C|=\exp(o(k))$. **No tensor construction can
  refute #126.**
- **What a tensor counterexample would cost.** Conversely, an exponential
  tensor construction *forces* $N(S)\ge\exp(ck)$, which would beat the best
  known lower bound for $S$-unit solution counts,
  $\exp\big((4+o(1))(s/\log s)^{1/2}\big)$ (Erdős–Stewart–Tijdeman 1988), and
  would be a significant independent result. The counterexample lane is not
  cheap; it is at least as hard as an open problem in a different field.

**Why the argument does not extend to general $A$**, which is exactly why this
closes the *tensor* lane and no more. For an arbitrary admissible $A$ and four
elements $a,b,c,d$ one has $(a+b)+(c+d)=(a+c)+(b+d)=\sigma$, four smooth numbers
in two smooth-summing pairs, but $\sigma=a+b+c+d$ need **not** be $S$-smooth,
so the ratios are not $S$-units and Theorem 5 has nothing to divide by. In the
tensor case the denominator $M$ factors as (an $A$-sum)$\times$(a $B$-sum) and is
smooth for free. That factorisation *is* the tensor hypothesis, and it is the
whole of what the argument uses.

**Measured, consistently.** Small tensors fail on their mixed pairs by wide
margins: $\{1,3\}\otimes\{1,2\}$ over $S\cup T=\{2,3,5\}$ gives $C=\{1,2,3,6\}$
with $2+3=5$ fine but $1+6=7$ outside; $\{1,5,7,11\}\otimes\{1,4\}$ over
$\{2,3,5\}$ fails on 10 of its 28 pairs (`tensor` in `results_probe.json`).
Finite, and not evidence, the theorem is the finding.

## 6. A lemma that turned out too weak to use

Recorded because the proof arm may otherwise spend a run rediscovering it.

> **Lemma 6 (sumset counting).** If $A$ is admissible for $S$, $|A|=n\ge 2$,
> $M=\max A$, then $2n-3\le\Psi(2M,S)$, the number of $S$-smooth integers
> $\le 2M$. *Proof.* $a_1+a_2<a_1+a_3<\cdots<a_1+a_n<a_2+a_n<\cdots<a_{n-1}+a_n$
> are $2n-3$ distinct $S$-smooth integers in $[1,2M]$. $\square$
> Sharper: the $n-1$ sums $a_n+a_i$ all lie in $(M,2M]$, so $n-1$ is at most the
> count of $S$-smooth integers in that dyadic window.

**It does not obstruct anything.** $\Psi(2M,S)\le\prod_{i\le k}(1+\log 2M/\log p_i)$,
so forcing $\Psi\ge 2^k$ needs only $\log M\gtrsim\log k$: the lemma places any
exponential construction outside a box of size polynomial in $k$, and no
further. The parent's box ($N\le 2\cdot 10^5$) is already past that threshold,
so the lemma explains nothing about why the searches stall. Smooth numbers are
too plentiful in exponent space for counting alone to bite. Stated as a
negative so it is not re-attempted.

## 7. What this run could not settle

- **No counterexample, and no proof that none exists.** The tensor lane is
  closed only *conditionally* on subexponential $S$-unit counts, and that is
  itself open. CRT and recursive lanes were considered and not developed: a CRT
  splicing has the same defect as the dilated union, the cross sums are
  $|A|^2$ unconstrained conditions against $O(1)$ free parameters, but I have
  no theorem for them, only the measured scan of §3 and the counting argument,
  which §6 shows is too weak. Calling those lanes closed would be an overclaim.
- **No upper bound on $g(k)$.** Corollary 5.1 is one for tensors only, and it is
  worse than the 1934 bound.
- **Whether $g(k)\ge\frac12 k\log k$ is the best known.** Lemma 2 is elementary
  enough that it is very likely in the literature; I did not search. If the
  published lower bound is larger, the bracket in §2 tightens from the other end.

## The doors

This run measured a ceiling (the tensor lane's ceiling, and $g_N(k)$ to $k=9$),
so it owes the list.

**1. Active constraints at the optimum.**

| Rank | What binds | Evidence |
|---|---|---|
| 1 | **The $S$-unit solution count $N(S)$.** It is the exact ceiling on tensor factors. | Corollary 5.1; the whole lane sits under it. |
| 2 | **The prime cost of doubling.** 6 and 7 extra primes to double at $k=2,4$; impossible at $k=3$. | §3 scan, exhaustive over $c\le200$. |
| 3 | **Denominator smoothness.** Every composition scheme that works does so because its denominator factors; every one that fails, fails there. | §5, closing paragraph. |

**2. Frozen-constant inventory.**

| Frozen | Value | What relaxing it trades |
|---|---|---|
| $S$ = first $k$ primes | fixed | Same door the parent named, still unopened. $g(k)$ is a max over all $k$-subsets. |
| dilation multiplier $c\le200$, extra primes $\le 12$ | §3 scan | **The one with real trade shape.** A wider scan could find a cheaper doubling; the quantity to report is the *prime cost*, not the size. |
| tensor factors tested | two small pairs | Cheap to widen and it would tell us little: Theorem 5 already governs all of them. Low value. |
| box $N$ | 200–400 | Lemma 1 says widening buys nothing but dilates. Confirmed: rows 1–7 match the parent's 15–500× larger boxes. Dead door. |
| $k_{\max}=9$ | clique search | Each row costs exponentially. $k=10$ needs a better solver, and by §4 the trend decides nothing anyway. |

**3. Information class.** Doors 2 and the box stay **inside** what this family
reads (integers and the smoothness of their sums) and are under its ceiling.
Door 1 requires reading **more**: the $S$-unit counting literature
(Evertse–Győry, Erdős–Stewart–Tijdeman). That is the same door $r\_186989$
ranked first and could not open. This run's contribution is to show it is not
optional for the counterexample side either, Theorem 5 puts the tensor lane
*underneath* it rather than beside it.

## Loose threads

- **Erdős–Stewart–Tijdeman transfer.** Their construction gives $S$ with
  $\exp(c(s/\log s)^{1/2})$ solutions to $x+y=1$. *Why it might matter:* if it
  can be pushed through Theorem 5 backwards it would give
  $g(k)\ge\exp(c(k/\log k)^{1/2})$, superpolynomial, still consistent with
  #126, and far above $\frac12 k\log k$. *First step:* check whether their
  $S$-unit solutions can be arranged with a common denominator $(a+a')(b+b')$
  of the required product shape.
- **The parity fact generalises and the parent's version is right.** $S$
  omitting 2 caps $|A|\le2$. The parent's suggested extension ($|A|\le p-1$ when
  a small $p\notin S$) is worth doing; it is the only iterable statement in
  either file. *First step:* pigeonhole on residues mod $p$ against
  $r\leftrightarrow -r$.
- **CRT lane never developed.** *Why it might matter:* it is the one of the five
  named schemes with no theorem against it here. *First step:* ask whether
  $A=\{a: a\equiv r_i \bmod m_i\}$ can force $a+b\equiv 0$ mod a large smooth
  modulus for *all* pairs, which is the only way to beat the $|A|^2$-conditions
  problem.
