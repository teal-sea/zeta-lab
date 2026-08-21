# PRIOR-ART.md: who owns what

**Written 2026-08-16, after an adjudication that the prior art owns the core
of this hunt.** The verdict is settled and this file does not relitigate it.
The purpose here is narrower and it is a verification job: read the two
load-bearing sources directly rather than through a summary, check that the
quoted statements are accurate, and work out whether the general theorem
really specializes to the prime zeta function before this hunt commits that
claim to writing.

Every line below carries a grade. The grades used are:

- **read verbatim**: the source was fetched in this session and the quoted
  text was copied from it.
- **cited, not read**: the source is named by a source that was read, but was
  not fetched here. Nothing rests on it that is not also witnessed elsewhere.
- **proved here**: an argument written out in this file and checked step by
  step.
- **measured**: one floating-point route, this session.
- **decided**: an interval or ball enclosure with exact endpoint sign logic.
  Decided values quoted here come from the hunt's `decided.json`; the
  independent floats computed for this file are graded *measured*.
- **adjudicated**: accepted from the prior-art ruling, not re-searched here.

Bottom line, stated first: **the specialization verifies and the bridge
verifies.** No gap was found in either. Two corrections to the adjudication's
own text are recorded in section 8, one of them a wrong digit string that must
not be reprinted.

---

## 1. Verification log

| action | result |
|---|---|
| Downloaded the Belovas et al. PDF from the journal (2.2 MB) and extracted its text | succeeded, 1224 lines; **read verbatim** |
| Fetched Sepulcre and Vidal arXiv:1805.02041 via ar5iv HTML | succeeded; **read verbatim** |
| Fetched the published Sepulcre and Vidal PDF (Carpathian J. Math.) and extracted its text | succeeded; **read verbatim** |
| Cross-checked preprint numbering against journal numbering | preprint Theorem 6 = journal Theorem 4.3, confirmed |
| Recomputed sigma_c, sigma_3, x* independently of the hunt's instruments | agree with the hunt's decided enclosures; **measured** |
| Recomputed sigma_3 by a third route (own Mobius / log-zeta implementation of the analytic continuation) | agrees with mpmath's `primezeta` to 36 digits; **measured** |
| Instantiated condition (4.8) numerically at seven values of sigma0 | binding index is always j = 1 (p = 2), as the proof predicts; **measured** |
| Spot-checked Rosser and Schoenfeld (3.8) and the Theorem C2 algebra | holds at every x tried; **measured** |
| Re-ran the hunt's failing literature query | the failure reproduces exactly (section 10) |

Not fetched this session, and therefore not witnessed here: Moreno (1973),
Sepulcre and Vidal JMAA 437 (2016), and Math.StackExchange 3894479. See
sections 5 and 6.

---

## 2. Source 1: Belovas, Cepaityte and Sabaliauskas (2025)

Igoris Belovas, Rugile Cepaityte and Martynas Sabaliauskas, *On the zero-free
region and the distribution of zeros of the prime zeta function*, An. St. Univ.
Ovidius Constanta Ser. Mat. **33**(2) (2025), 27-44. DOI
`10.2478/auom-2025-0017`. Received 07.10.2024, accepted 28.02.2025. Open
access. PDF:
`https://www.anstuocmath.ro/mathematics/anale2025v2/2_Igoris_Belovas_et_al.pdf`

Grade: **read verbatim**.

### 2.1 Theorem 1, verbatim

> **Theorem 1.** The prime zeta function has no zeros in the half-plane
> sigma > sigma_0. Here sigma_0 = 1.77954465354699... is the zero of the
> function U(sigma) = 2^{1-sigma} - zeta_P(sigma).

Grade: **read verbatim**. This is the hunt's Theorem A(a), same constant and
same proof. Their proof, verbatim:

> First we note that |zeta_P(s)| = |1/2^s + 1/3^s + 1/5^s + ...| >
> 1/2^sigma - 1/3^sigma - 1/5^sigma - ... = 2^{1-sigma} - zeta_P(sigma) =
> U(sigma).

That is the triangle inequality against the first term, which is exactly the
hunt's argument.

### 2.2 Lemma 1, verbatim

> **Lemma 1.** Let the function U(sigma) be defined as above and
> sigma_1 = 2.18, then U'(sigma) > 0 if 1 < sigma <= sigma_1, and
> U(sigma) > 0 if sigma >= sigma_1.

Grade: **read verbatim**. This is the hunt's Lemma 1 (uniqueness of the root),
published. Their uniqueness argument: U(1.77) < 0, U(1.78) > 0, so a root lies
in (1.77, 1.78); monotonicity below 2.18 and positivity above make it unique.
They add, in parentheses, "note that we can calculate it numerically with any
necessary precision".

### 2.3 Remark 1, verbatim

> **Remark 1.** Let M = 200000 and define
>
>     sigma_T = max_{|t| < T} { sigma | zeta_P(sigma) = 0 },        (2)
>
> then we receive sigma_M = 1.682628788045196... . Thus, the result of Theorem
> 1 can not be refined by more than Delta = 0.097.

Grade: **read verbatim**. Note the printed definition writes
`zeta_P(sigma) = 0` where it plainly means `zeta_P(s) = 0` with s = sigma + it;
the max is over the real parts of zeros of height below T. The typo is in the
source and the meaning is unambiguous. Quote it as printed if it is quoted.

### 2.4 Conjecture 1, verbatim

> **Conjecture 1.** The estimate for the zero-free plane given by Theorem 1 can
> not be improved, that is, if sigma_T is defined as above (see (2)), then
>
>     lim_{T -> infinity} sigma_T = sigma_0.                        (3)

Grade: **read verbatim**. **Left open in the paper.** Sections 5 and 6 of that
paper test it only numerically, and their numerics stop at sigma_M = 1.6826...,
which is 0.097 short of sigma_0 and, relevantly for this hunt, *below* x* =
1.7286... . Their Conjectures 2 and 3 concern the vertical distribution of the
zeros (uniformity of imaginary parts, and a linear-in-T zero count) and are not
engaged by this hunt.

### 2.5 What the paper does not contain

Their bibliography has exactly seven items: Belovas-Sabaliauskas-Kuzma (2022),
Cohen (1998 preprint), Fischer (arXiv 2017), Froberg (1968), Landau and Walfisz
(1920), Titchmarsh (1986), and their own GitHub repository. Grade: **read
verbatim**.

Word-level absence check over the extracted text, grade **measured**:

| term | occurrences |
|---|---|
| `A107311`, `Jasinski`, `1.72864` | 0 |
| `almost period`, `Moreno`, `Sepulcre`, `Vidal` | 0 |
| `Kronecker`, `Bohr`, `exponential polynomial` | 0 |
| `subset` | 0 |
| `OEIS` | 1, and see below |

The single `OEIS` hit is an incidental URL inside reference [2]: Cohen's
Hardy-Littlewood-constants preprint is hosted at `oeis.org/A221712/a221712.pdf`.
It is not a reference to A107311 and the paper nowhere engages the Jasinski
conjectures. The adjudication's substance is confirmed; its wording ("the paper
never mentions OEIS") needs this caveat.

---

## 3. Source 2: Sepulcre and Vidal, the general theorem

J. M. Sepulcre and T. Vidal, *On the real projections of zeros of analytic
almost periodic functions*, Carpathian J. Math. **38** (2022), no. 2, 489-501.
Received 13.10.2020, revised 07.09.2021, accepted 14.09.2021. MSC 30B50, 30D20,
30Axx, 11J72. Preprint: arXiv:1805.02041 [math.CV], 5 May 2018, titled *On the
real projections of zeros of almost periodic functions* (the published title
adds the word "analytic").

Grade: **read verbatim**, both versions.

### 3.1 Numbering: the discrepancy resolved

The preprint numbers its results in one flat sequence (Theorems 4, 5, 6,
Proposition 7, Corollaries 8, 10, 13, Example 9, Lemma 11, Theorem 12, Remark
14). The journal renumbers by section (Theorem 3.2, Theorem 4.3, Proposition
4.1, Theorem 4.4, ...).

**Preprint Theorem 6 = journal Theorem 4.3.** Grade: **read verbatim**, both
texts compared side by side; the statements are word for word identical apart
from the label. Cite the journal numbering (4.3) as primary and give the
preprint number in parentheses, because a reader who reaches for arXiv will
find "Theorem 6" and needs the bridge.

### 3.2 Theorem 4.3, verbatim (journal text)

> **Theorem 4.3.** Let f(s) be an almost periodic function in a vertical strip
> U = {s = sigma + it : alpha < sigma < beta} whose Dirichlet series is given by
> sum_{n >= 1} a_n e^{lambda_n s} with {lambda_1, lambda_2, ..., lambda_k, ...}
> Q-linearly independent and k > 2. Let sigma_0 in (alpha, beta). Then
> sigma_0 in R_f if and only if
>
>     |a_j| e^{sigma_0 lambda_j} <= sum_{i >= 1, i != j} |a_i| e^{sigma_0 lambda_i}
>                                                   (j = 1, 2, ..., k, ...).   (4.8)

Grade: **read verbatim**.

**A precision point on the adjudication's phrasing.** The adjudication renders
the conclusion as "sigma_0 in closure(R_f)". The printed statement says
"sigma_0 in R_f", and R_f is *already defined as a closure*, at equation (1.4):

> R_f := closure{Re s : f(s) = 0, s in U} intersect (alpha, beta).

Grade: **read verbatim**; the closure bar is explicit in the ar5iv LaTeX
(`\overline{\left\{\operatorname{Re}s:f(s)=0,\ s\in U\right\}}`) and is lost in
naive text extraction of the journal PDF, which is presumably how the extra
"closure" crept in. The two readings agree in substance. Quote it as printed:
`sigma_0 in R_f`, with R_f's definition given alongside, because the closure is
the whole subtlety of section 7 below.

### 3.3 The aggregated-tail polygon device, verbatim from the proof

The "if" direction of Theorem 4.3 is where the device lives:

> We recall that [...] it is accomplished that sum_{j >= 1} |a_j| e^{sigma_0
> lambda_j} < infinity. Thus, given eps > 0 there exists n_0 in N such that
> sum_{j >= n_0} |a_j| e^{sigma_0 lambda_j} < eps. Hence, for eps > 0
> sufficiently small we can index the terms in decreasing order so that [...]
> Therefore, by taking r := sum_{j >= n_0} |a_j| e^{sigma_0 lambda_j}, there is
> at least one n_0-sided polygon whose sides have the lengths |a_{m_j}|
> e^{sigma_0 lambda_{m_j}}, j = 1, 2, ..., n_0 - 1 and r [14, p.71]. That means
> that there exist real numbers theta_1, theta_2, ..., theta_{n_0} satisfying
> sum_{k=1}^{n_0 - 1} |a_k| e^{sigma_0 lambda_k} e^{i theta_k} + r e^{i
> theta_{n_0}} = 0.

Grade: **read verbatim**. Two things are settled by this paragraph:

1. The **aggregated-tail device** is in print: the infinite tail is collapsed
   into a single polygon side of length r. This is the hunt's device.
2. The polygon step itself is attributed to **[14, p.71]**, which the
   bibliography gives as Moreno, Compos. Math. 26 (1973), no. 1, 69-78. That
   is Moreno's Geometric Principle, and it is the hunt's Lemma 2.

### 3.4 Proposition 4.1, and why it is a consistency check on this hunt

> **Proposition 4.1.** Let f(s) be an almost periodic function in a vertical
> strip U [...] whose Fourier exponents {lambda_1, lambda_2, ..., lambda_k,
> ...}, with k > 2, are Q-linearly independent. Let sigma_0 in (alpha, beta).
> If sigma_0 is a boundary point of R_f, then it satisfies all the inequalities
> (4.8) and only one of them is an equality.

Grade: **read verbatim**. Section 6 below confirms numerically that for the
prime zeta function the single equality at the boundary point sigma_c is the
j = 1 (p = 2) one, exactly as this proposition requires. That is an independent
check that the specialization has been carried out correctly.

### 3.5 The definition of almost periodicity, which turns out to matter

From section 1 of the journal text:

> A function f(s), s = sigma + it, analytic in a vertical strip
> U = {s = sigma + it in C : alpha < sigma < beta} (-infinity <= alpha < beta
> <= infinity), is called almost periodic in U if to any eps > 0 there exists a
> number l = l(eps) such that each interval t_0 < t < t_0 + l of length l
> contains a number tau satisfying |f(s + i tau) - f(s)| <= eps for all s in U.

Grade: **read verbatim**. The quantifier is **for all s in U**, over the whole
open strip, not over each closed substrip. Section 6 shows this is the
hypothesis that constrains which strip may be used, and it constrains it in the
opposite direction from what one might guess.

Note also that the strip convention explicitly admits `beta = infinity`.

---

## 4. Source 3: Moreno (1973)

C. J. Moreno, *The zeros of exponential polynomials (I)*, Compositio Math. **26**
(1973), no. 1, 69-78.

Grade: **cited, not read**. This session did not fetch it. What is witnessed
here is that Sepulcre and Vidal cite it at `[14, p.71]` for precisely the
polygon construction (section 3.3), and at `[14, Lemma, p.73]` elsewhere in
their paper. Both page references match the adjudication's account of the
Geometric Principle (p. 71-72) and the Main Theorem (p. 73). The adjudication's
further statement that Moreno himself applies the principle to
`sum_{p <= M} p^{-s}` is **adjudicated**, not verified here.

Nothing in sections 6 and 7 rests on Moreno directly. The chain used there runs
through Sepulcre and Vidal Theorem 4.3, which was read in full.

---

## 5. Supporting sources

**Sepulcre and Vidal**, *On the non-isolation of the real projections of the
zeros of exponential polynomials*, J. Math. Anal. Appl. **437** (2016), no. 1,
513-525. Grade: **cited, not read**; the citation is confirmed as item [18] of
the Carpathian bibliography, **read verbatim**. The adjudication assigns its
Proposition 5 and Corollary 6 (supremum of real parts equals the balance root;
supremum not attained) as the finite ancestor of the hunt's Theorem A(b) and
Corollary B1. Accepted as **adjudicated**, with one honest precision note in
section 8.

**Math.StackExchange 3894479**, comment by K. Conrad, 2020-11-05. Grade:
**adjudicated**, not checked this session.

**Borwein, Fee, Ferguson and van der Waall**, *Zeros of partial sums of the
Riemann zeta function*, Exp. Math. **16** (2007), no. 1, 21-39. Grade: **cited,
not read**; confirmed as item [6] of the Carpathian bibliography. This is the
line of work to which x* = 1.7286... genuinely belongs, which is the root of
the OEIS entry's confusion.

---

## 6. The specialization, worked out

**Question.** Does Sepulcre and Vidal Theorem 4.3 genuinely apply to

    P(s) = sum_p p^{-s} = sum_p e^{-(log p) s} ?

**Answer: yes.** Each hypothesis is checked below. Grade: **proved here**,
with the numerical instantiations graded **measured**.

Match the notation: a_n = 1 for every n, and lambda_n = -log p_n, so that
a_n e^{lambda_n s} = e^{-s log p_n} = p_n^{-s}. The lambda_n are distinct
negative reals, which the theorem allows (it asks only for distinct reals).

### (i) Almost periodicity, and which strip

This is the hypothesis that needs care, and it does not behave the way a first
guess suggests.

By section 3.5 the estimate must hold **uniformly on the whole open strip U**.
An almost periodic function in that sense is bounded on U: given s = sigma + it
in U, choose tau in [-t, -t + l] with |f(s + i tau) - f(s)| <= 1; then
s + i tau = sigma + i(t + tau) with t + tau in [0, l], so
|f(sigma + it)| <= sup{|f(sigma + iu)| : 0 <= u <= l} + 1, and boundedness on U
follows from boundedness on the block {alpha < sigma < beta, 0 <= u <= l}.

Therefore **U = {1 < Re s < infinity} is not admissible**: P is unbounded there,
since P(sigma) -> +infinity as sigma -> 1+. Any attempt to take alpha = 1 fails
at the hypothesis, not at the conclusion.

The correct instantiation fixes a strip that stays away from 1. Let
delta in (0, sigma_c - 1) and put

    U_delta = { s : 1 + delta < Re s < +infinity },

which the paper's own convention permits since it allows beta = infinity. On
U_delta:

- the series converges absolutely and uniformly, because
  sum_p p^{-sigma} <= sum_p p^{-(1+delta)} = P(1 + delta) < infinity;
- hence P is the uniform limit on U_delta of the exponential polynomials
  S_N(s) = sum_{p <= N} p^{-s}, since
  |P(s) - S_N(s)| <= sum_{p > N} p^{-(1+delta)} -> 0;
- each S_N is almost periodic on U_delta in the uniform sense (finitely many
  frequencies, so a relatively dense set of tau makes every |p^{-i tau} - 1|
  small simultaneously), and a uniform limit of almost periodic functions on U
  is almost periodic on U;
- so P is in AP(U_delta, C), and P is bounded there by P(1 + delta).

**The fixed-strip hypothesis is respected exactly, and no shrinking-delta limit
is needed for anything this hunt or the bridge claims.** Since sigma_c =
1.7795... , a single fixed choice such as delta = 1/2, giving
U = {3/2 < Re s < infinity}, already contains sigma_c in its interior. One
application of the theorem, in one fixed strip, suffices.

The union over delta is *optional*, and it is legitimate when wanted. Condition
(4.8) does not mention delta (see (iv) below), so applying the theorem in
U_delta gives the same threshold for every admissible delta:

    R_P^{(delta)} = (1 + delta, sigma_c]   for each delta in (0, sigma_c - 1).

Any sigma_0 in (1, sigma_c] lies in R_P^{(delta)} for any delta < sigma_0 - 1,
so the union over delta gives

    closure{Re s : P(s) = 0, Re s > 1} intersect (1, infinity) = (1, sigma_c].

The union is taken *after* each application, outside the theorem, so no single
application ever uses a moving strip.

### (ii) Q-linear independence of the exponents

**Claim.** {-log p : p prime} is linearly independent over Q. Grade: **proved
here** (this is the hunt's Lemma 3, and it is standard).

*Proof.* Suppose sum_{p in F} q_p (-log p) = 0 with F a finite set of primes
and q_p in Q. Multiplying by a common denominator gives integers n_p with
sum_{p in F} n_p log p = 0, that is prod_{p in F} p^{n_p} = 1. Separate the
signs:

    prod_{p : n_p > 0} p^{n_p} = prod_{p : n_p < 0} p^{-n_p}.

Both sides are positive integers, and the two sides have disjoint sets of prime
divisors. By uniqueness of prime factorization each side equals 1, so every
n_p = 0 and hence every q_p = 0. QED (two lines, as advertised).

Independence of {-log p} is equivalent to independence of {log p}, so the sign
convention costs nothing.

### (iii) The condition k > 2

Lambda = {-log p : p prime} is countably infinite, so there are far more than
two Fourier exponents. Satisfied with room to spare. Grade: **proved here**.

The paper's "k > 2" is terse and is not defined at the point of use; read
against the notation {lambda_1, lambda_2, ..., lambda_k, ...} it is a condition
on how many Fourier exponents there are (at least three). Every reading of it is
satisfied by an infinite exponent set, so the ambiguity is harmless here. Say so
rather than papering over it.

One implicit hypothesis is worth naming: the Dirichlet series in the theorem
must be the Fourier series of f. Sepulcre and Vidal note that under Q-linear
independence the Dirichlet expansion converges absolutely to f in U (their
citations [9, Theorem 3.6] and [3, p.154]); for P on U_delta the identification
is direct, since the series is the definition.

### (iv) Instantiating condition (4.8)

With a_n = 1 and lambda_n = -log p_n,

    |a_j| e^{sigma_0 lambda_j} = e^{-sigma_0 log p_j} = p_j^{-sigma_0},
    sum_{i != j} |a_i| e^{sigma_0 lambda_i} = P(sigma_0) - p_j^{-sigma_0}.

So (4.8) reads, for every j,

    p_j^{-sigma_0} <= P(sigma_0) - p_j^{-sigma_0},
        equivalently   2 p_j^{-sigma_0} <= P(sigma_0).

**The j = 1 instance is the binding one.** For sigma_0 > 0 the map
p |-> 2 p^{-sigma_0} is strictly decreasing in p, so the left-hand side is
largest at the smallest prime, p_1 = 2. Hence the whole infinite family of
inequalities holds if and only if its p = 2 member holds:

    2 * 2^{-sigma_0} <= P(sigma_0),
        that is   P(sigma_0) >= 2^{1 - sigma_0},
        that is   U(sigma_0) := 2^{1 - sigma_0} - P(sigma_0) <= 0,

with U exactly Belovas et al.'s U. Grade: **proved here**.

Numerical instantiation over all primes p < 200, grade **measured** this
session:

| sigma_0 | indices j failing (4.8) | P(sigma_0) - 2^{1-sigma_0} |
|---|---|---|
| 1.5 | none | +0.1424559 |
| 1.70 | none | +0.02776089 |
| 1.7795446535 | none | +1.4333e-11 |
| 1.7795446536 | {p = 2} only | -1.6167e-11 |
| 1.79 | {p = 2} only | -0.0031345 |
| 1.90 | {p = 2} only | -0.0303235 |
| 2.50 | {p = 2} only | -0.0798727 |

Exactly one inequality ever fails, and it is always the p = 2 one. This is the
predicted behaviour and it also confirms Proposition 4.1 (section 3.4) for this
function: at the boundary point sigma_c precisely one of the (4.8) inequalities
is an equality, the j = 1 one.

By Belovas et al.'s Lemma 1, U is strictly increasing on (1, 2.18] and positive
on [2.18, infinity), and U(sigma) -> -infinity as sigma -> 1+ because
P(sigma) -> +infinity while 2^{1-sigma} -> 1. So U has a unique root sigma_c in
(1, infinity), and on (1, infinity),

    U(sigma_0) <= 0   if and only if   sigma_0 <= sigma_c.

### (v) Conclusion of the specialization

    closure{Re s : P(s) = 0, Re s > 1} intersect (1, infinity) = (1, sigma_c],

with sigma_c the unique root of P(sigma) = 2^{1-sigma}. Grade: **proved here**,
resting on Theorem 4.3 as published and read.

Independent recomputation of the constant, grade **measured** this session, by
two implementations (mpmath `primezeta`, and an independent implementation of
the Mobius / log-zeta continuation P(s) = sum_n mu(n)/n log zeta(ns)), agreeing
to 36 digits:

    sigma_c = 1.77954465354699411644589878696551...

which matches Belovas et al.'s printed `1.77954465354699...` in all 15 digits
they print, and lies inside the hunt's decided enclosure.

### (vi) Does this give the hunt's Theorem B in full?

This is the subtle part and the answer has three layers, strictly ordered.

    (S1)  closure of the real projections, intersected with (1, infinity),
          is exactly (1, sigma_c].                    [Theorem 4.3, above]

    (S2)  for every window (a, b) contained in (1, sigma_c], P has
          infinitely many zeros with Re s in (a, b).

    (S3)  for every such window, P has at least one zero with Re s in (a, b).
                                        [the hunt's Theorem B, existence part]

**S1 implies S2.** Grade: **proved here**. Suppose only finitely many zeros had
Re s in (a, b). Pick sigma_0 in (a, b) and a neighbourhood N of sigma_0 with N
contained in (a, b). Every projection lying in N is one of those finitely many,
so the closure of the projection set meets (a, b) in a finite set. But S1 says
that intersection is (a, b), an uncountable interval. Contradiction.

**S2 implies S3.** Immediate.

**Neither converse holds.** Grade: **proved here**. A function whose zeros all
had real part exactly 1.5 would satisfy S2 for every window containing 1.5 while
its closure set is the single point {1.5}, so S2 does not recover S1.

So the hunt's Theorem B existence claim is **strictly weaker** than what
Theorem 4.3 delivers, and its "infinitely many" clause is exactly S2, also
delivered. The hunt's further clause that the imaginary parts are unbounded
above is likewise implied: infinitely many zeros in a bounded real-part window,
together with the fact that a non-vanishing-identically analytic function has
only finitely many zeros in any compact box, forces the heights to be unbounded.
Grade: **proved here**.

**What Theorem 4.3 does not give**, and the hunt's Lemma 4 does: a *positive
lower density* of admissible heights, liminf |G intersect [0,T]| / T >=
(delta / 2 pi)^n. Theorem 4.3 is silent about the distribution in t.

Honesty note on that residue, and it is a warning rather than a credit: the
density of zeros of an analytic almost periodic function in a strip is classical
territory (Jessen and Tornehave), and Belovas et al.'s own Conjecture 3 is a
statement of exactly that shape. **This session did not search that literature**
and makes no claim that the hunt's density statement is new. Grade: **unverified
lead**, flagged so nobody mistakes silence for absence. It is the same failure
mode that produced this adjudication in the first place.

---

## 7. The bridge claim: does Theorem 4.3 imply Belovas et al.'s Conjecture 1?

**Answer: yes, and no gap was found.** Grade: **proved here**, standing on
Theorem 4.3 as read verbatim. Not refereed, not kernel-checked.

**Claim.** With sigma_T = max{sigma : P(sigma + it) = 0, |t| < T} as in Belovas
et al. (2), Theorem 4.3 gives lim_{T -> infinity} sigma_T = sigma_c.

*Proof.*

**Upper bound.** Take the "only if" direction of Theorem 4.3. If
sigma_0 > sigma_c then (4.8) fails at sigma_0 by section 6(iv), so sigma_0 is
not in R_P. But if P had a zero with Re s = sigma_0, then sigma_0 would lie in
the projection set, hence in its closure, hence in R_P (sigma_0 being interior
to the strip). So P has no zero with Re s > sigma_c in the half-plane of
almost periodicity. Zeros of the analytic continuation in 0 < Re s <= 1 have
Re s <= 1 < sigma_c. Hence every zero of P satisfies Re s <= sigma_c, and
sigma_T <= sigma_c for every T.

**Lower bound.** Fix eps > 0. By section 6(v), sigma_c is in R_P, which is by
definition the *closure* of the set of real projections. So sigma_c is a limit
of real projections, and there exists an honest zero s_eps = sigma_eps +
i t_eps of P with sigma_eps > sigma_c - eps. Its height t_eps is a finite real
number. For every T > |t_eps| that zero is counted by sigma_T, so
sigma_T >= sigma_eps > sigma_c - eps.

**Conclusion.** sigma_T is non-decreasing in T, since the max is taken over a
larger set as T grows, and is bounded above by sigma_c. So the limit exists,
and it exceeds sigma_c - eps for every eps > 0. Hence
lim_{T -> infinity} sigma_T = sigma_c. QED.

### 7.1 Gap analysis

The three concerns raised against this bridge were checked one at a time. None
of them is a gap.

**"Does closure membership guarantee zeros at finite height?"** Yes, by
definition, and this is the concern worth stating explicitly because it sounds
like it should bite. R_f is the closure of {Re s : f(s) = 0, s in U}, where s
ranges over points of U. Every point of U is a complex number with a finite
imaginary part. No point at infinity, and no limiting object, enters the
definition. The approximating zeros are honest zeros at finite heights. What is
*not* controlled is how large those heights are, and they may be astronomical:
Belovas et al.'s search to |t| < 200000 reaches only sigma_M = 1.6826..., still
0.097 short. That is exactly why the conjecture looked open. But an uncontrolled
finite height is not a gap in a limit statement, because each eps only needs to
be achieved at *some* finite T.

**"Does the sup over |t| < T converge, and does that need zeros at every finite
height?"** It converges because it is monotone non-decreasing and bounded above,
and monotone plus bounded is enough. No hypothesis about zeros existing at each
height beyond some point is needed anywhere in the argument.

**Two technicalities, both harmless.** First, sigma_T is undefined for T small
enough that no zero has |t| < T; the limit statement is untouched, and Belovas
et al. exhibit 10318 zeros with t < 10^4 in any case. Second, as printed
sigma_T is a *max* over the open condition |t| < T, which need not be attained
if projections accumulate only as |t| approaches T; replacing max by sup removes
the issue and changes neither the upper nor the lower bound. Neither affects the
limit.

### 7.2 The bridge is stronger than advertised

Worth recording, because it sharpens the observation rather than inflating it.
The upper-bound half of the argument above uses only the "only if" direction of
Theorem 4.3, and what it produces *is* Belovas et al.'s Theorem 1: the half-plane
Re s > sigma_c is zero-free. So:

- the **"only if"** half of Theorem 4.3 (2022, preprint 2018) already contains
  Belovas et al.'s **Theorem 1** (2025);
- the **"if"** half of the same theorem settles their **Conjecture 1**.

Their theorem and their open conjecture are the two directions of one published
characterization that predates both. Grade: **proved here**.

This is the observation the hunt may claim, and it is a claim about the
literature, not about mathematics: two papers that do not cite each other, filed
under different subject classes, jointly close a stated open problem. It should
be stated in exactly those terms, with no suggestion that the hunt proved
Theorem 4.3 or Conjecture 1.

---

## 8. Ownership map

Grades in the last column are for **this hunt's** claim on the item, not for the
truth of the item.

| hunt item | statement | owned by | grade for the hunt |
|---|---|---|---|
| Lemma 1 | U has a unique root sigma_c in (1, infinity) | Belovas et al. Lemma 1 (2025) | pure rediscovery |
| Lemma 2 | polygon lemma | Moreno (1973) Geometric Principle, p. 71; used verbatim as the tail device by Sepulcre and Vidal Thm 4.3 proof | pure rediscovery |
| Lemma 3 | {log p} Q-linearly independent | standard (unique factorization) | not a claim |
| Lemma 4 | phase steering with positive lower density | classical Kronecker/Weyl; density of a.p. zeros is classical (Jessen and Tornehave) | pure rediscovery, and the density residue is an **unverified lead**, not a claim |
| Theorem A(a) | wall at sigma_c by triangle inequality | Belovas et al. Theorem 1 (2025); earlier, the "only if" half of Sepulcre and Vidal Thm 4.3 (2022, preprint 2018) | pure rediscovery |
| Theorem A(b) | no zero with Re s = sigma_c | Sepulcre and Vidal JMAA (2016) Cor. 6 for the finite case; see note below | pure rediscovery (adjudicated) |
| Theorem B | zeros fill every window below sigma_c | strictly implied by Sepulcre and Vidal Thm 4.3, which is stronger (section 6(vi)) | pure rediscovery |
| Corollary B1 | sup of real parts = sigma_c, not attained | Sepulcre and Vidal JMAA (2016) Prop. 5 and Cor. 6, finite ancestor | pure rediscovery (adjudicated) |
| Corollary B2 | OEIS A107311 Conjecture 1 is false | no source engages the OEIS entry | **new as a connection; zero new mathematics** |
| Theorem C1 | sigma_3 = 1.8252... , a subset out-walls the full series | instance of the prior-art framework | **new instance of prior-art theory** |
| Theorem C2 | tail-subset walls >= log2(3 p_k / (5 log p_k)), unbounded | no prior art located by four independent searches | **new, small, elementary corollary** of published framework plus Rosser and Schoenfeld |
| Corollary C3 | Conjecture 2 fails for every replacement constant | as C2 | **new, small** |
| decided enclosures | two-backend enclosures of sigma_c, sigma_3, x* with exact endpoint signs | Belovas et al. print 15 digits and note any precision is available | rediscovery with sharper form |
| the bridge | Belovas et al. Conjecture 1 follows from Sepulcre and Vidal Thm 4.3 | nobody; neither paper cites the other | **new as a literature observation; most publishable item here** |
| value of sigma_c | 1.77954465354699... | Belovas et al. Theorem 1 (2025) | pure rediscovery |

**Precision note on Theorem A(b) and Corollary B1.** The adjudication assigns
these to Sepulcre and Vidal JMAA (2016), Proposition 5 and Corollary 6, and that
assignment stands. Recorded for accuracy and not as a defence: those results are
stated for *exponential polynomials*, that is finite sums, whereas P is an
infinite series, and the finite-to-infinite step is not automatic. Neither
Belovas et al. Theorem 1 (which covers only sigma > sigma_0, saying nothing at
sigma = sigma_0) nor Sepulcre and Vidal Theorem 4.3 (whose conclusion is about a
closure, and which places sigma_c *inside* R_P) decides on its own whether a
zero sits exactly on Re s = sigma_c. The hunt should write "the same argument
gives the infinite-series case" rather than cite Corollary 6 as though it
applied verbatim. The mathematics is easy either way: equality in the triangle
inequality at sigma_c would force p^{-it} to take a common value for all p >= 3
and the opposite value at p = 2, and taking any two of p = 3, 5, 7 gives
t log(5/3) = 2 pi m and t log(7/5) = 2 pi n, whence 5^{n+m} = 3^n 7^m, so
m = n = 0 and t = 0, where P(sigma_c) > 0. Grade: **proved here**.

---

## 9. What survives as this hunt's own

Restated from the adjudication, with this session's verification status
attached. Nothing is added to the list.

**(a) The line-by-line refutation of OEIS A107311's two conjectures.** No source
in the literature engages that entry. Belovas et al. do not refute Conjecture 1:
their bound 1.7795 is *weaker* than the conjectured 1.72864, and their numerics
stop at 1.6826, which is below x*, so their paper is consistent with the OEIS
entry as far as it goes. Grade: **new as a connection, zero new mathematics.**
Verified this session that their paper contains no engagement with the entry
(section 2.5).

**(b) Theorem C2 and Corollary C3.** Tail subsets {p >= p_k} have walls at least
log2(3 p_k / (5 log p_k)), which grows without bound, so no constant bounds the
real parts of zeros across all prime subsets and Conjecture 2 fails for every
replacement constant. Grade: **new, small, elementary corollary** of published
framework plus Rosser and Schoenfeld. Spot-checked this session, grade
**measured**: Rosser and Schoenfeld's (3.8), 3x/(5 log x) < pi(2x) - pi(x),
holds at x = 23, 29, 101, 1009, 10007, 100003; the bound
B(p_k) = log2(3 p_k / (5 log p_k)) takes the values 2.1379, 3.7149, 6.4517,
9.3484, 15.4064 at p_k = 23, 101, 1009, 10007, 1000003, and grows like
log2(p_k) - log2(log p_k) - log2(5/3); and direct computation of the true walls
gives sigma_c(23) = 4.4875..., sigma_c(29) = 7.1729..., sigma_c(101) = 8.8316...,
against B(23) = 2.1379..., B(29) = 2.3694..., B(101) = 3.7149..., so the bound
holds in every case checked and is loose in every case checked. The
non-monotonicity (the wall at 29 exceeds the wall at 101) is expected rather
than suspicious: the balance for {p >= q} is governed by how close the next
prime sits to q, and 29 has 31 immediately above it.

**(c) The constant sigma_3 for {p >= 3}, and that a subset out-walls the full
series by more than 0.045.** Grade: **new instance of prior-art theory**.
Recomputed this session, grade **measured**: sigma_3 - sigma_c = 0.0456813...,
which exceeds 0.045.

**(d) Two-backend enclosures of sigma_c, sigma_3 and x* with exact endpoint sign
logic, and the decided separation and margin.** Grade: **rediscovery with
sharper form**; Belovas et al. print 15 digits and remark that any precision is
available. Recomputed this session, grade **measured**: sigma_c - x* =
0.0508974..., which exceeds 1/20, and P(x*) - 2^{1-x*} = 0.0169073... > 0. Both
agree with the hunt's decided values.

**(e) The bridge.** Belovas et al.'s Conjecture 1, left open in their paper, is
a corollary of Sepulcre and Vidal Theorem 4.3. Grade: **new as a literature
observation**, and section 7 verifies it with no gap found. Section 7.2 records
that the same theorem also subsumes their Theorem 1, which strengthens the
observation.

### 9.1 Two corrections to the adjudication's own text

Both are small and both must be applied before anything here is published.

1. **A wrong digit string for sigma_3.** The adjudication prints
   `sigma_3 = 1.82522595607384576238787271088892...`. That value is **below**
   the hunt's own decided flint enclosure
   `[1.8252259560738457623878727108889264, 1.8252259560738457623878727108890054]`
   and is not the constant. It appears to be the enclosure's lower endpoint
   truncated toward zero at 32 decimals, which lands outside the enclosure. The
   value, computed this session by two independent implementations agreeing to
   36 digits and lying inside the hunt's decided enclosure, is

       sigma_3 = 1.82522595607384576238787271088898855...

   Grade: **measured**, and consistent with the hunt's **decided** enclosure. Do
   not reprint the adjudication's string.

2. **"The paper never mentions OEIS."** Belovas et al. contain one incidental
   `oeis.org` URL, in reference [2], hosting Cohen's Hardy-Littlewood-constants
   preprint. It is not a reference to A107311 and the substance of the
   adjudication is unaffected, but the sentence as written is falsifiable by
   anyone who runs a text search. Grade: **read verbatim**.

Two further bibliographic notes, neither affecting substance. The Belovas et
al. PDF's own header line reads "Vol. 33(2), 2025, 27-43" while the last printed
folio of the article is 44 and external indexing gives 27-44; cite 27-44 and do
not be surprised by the header. And the Sepulcre and Vidal preprint and journal
titles differ by one word, the journal adding "analytic"; cite the journal title
for the journal version.

---

## 10. The search-failure lesson

Recorded because it is the transferable output of this episode, and it
reproduces on demand.

**Failure 1: the specific paper.** The hunt's exact-phrase query
`"zeros of the prime zeta function"` is a literal substring of the Belovas et
al. title, *On the zero-free region and the distribution of zeros of the prime
zeta function*. The query was re-run this session and the failure **reproduces
exactly**: ten results came back, including MathWorld's prime zeta page and a
mention of Froberg (1968), and the Belovas et al. paper was **not among them**.
Grade: **measured**, this session.

Contributing causes, all of which defeat a standard sweep:

- the paper was never preprinted on arXiv;
- it lives in a Sciendo/DOAJ journal that an arXiv-plus-MathWorld-plus-zbMATH
  title sweep does not reach;
- its PDF is image-scanned, so naive text extraction of the landing page yields
  nothing. This session only got the text by downloading the 2.2 MB PDF and
  running a proper extractor. A retrieval pipeline that reads pages rather than
  files would have missed it even after finding it.

**Failure 2: the general theorem, missed for a completely different reason.**
Sepulcre and Vidal Theorem 4.3 is filed under **almost periodic functions**, MSC
30B50 and 30D20, not number theory, and the paper **never names a prime**. No
query about prime zeta functions can reach it. It was reachable only by
searching for the *shape* of the argument, that is, real projections of zeros of
Dirichlet series with rationally independent frequencies.

**The lesson, stated so it can be applied to the next hunt.** Two distinct
search failures need two distinct countermeasures, and having one does not
protect against the other:

1. *Against the venue gap*: an exact-title-substring query proves nothing when
   it returns nothing. Search the DOI registries and the open-access aggregators
   (Crossref, DOAJ, Sciendo) by title, not only the engines and arXiv, and treat
   an image-scanned PDF as a document that must be downloaded and extracted
   rather than fetched.
2. *Against the classification gap*: when an argument's engine is a general
   device (here, rational independence of frequencies plus a polygon
   construction), search for **the device under its own name in its own field**,
   not for the application. The hunt's own Lemma 2 and Lemma 4 were the
   signposts, and a search for "real projections of zeros", "exponential
   polynomials", or "almost periodic Dirichlet series" would have landed on the
   right MSC class immediately.

A corollary worth keeping: `ontology/knownness.py` defaults to "the literature
was not consulted", and this episode is the argument for that default. Four
independent searches returned nothing on the core result while two published
papers owned it outright. **An unrun or an unsuccessful search is not evidence
of absence**, and the two failures above show that a search can be run
competently and still fail for reasons that have nothing to do with effort.

---

## 11. Verdict

- **The specialization verifies.** Sepulcre and Vidal Theorem 4.3 applies to
  P(s) = sum_p p^{-s} on any fixed strip {1 + delta < Re s < infinity} with
  0 < delta < sigma_c - 1, and yields closure{Re s : P(s) = 0} intersect
  (1, infinity) = (1, sigma_c]. Every hypothesis checks: almost periodicity on
  a fixed strip bounded away from Re s = 1, Q-linear independence by unique
  factorization, k > 2 by countable infinitude, and condition (4.8) collapsing
  to its p = 2 member. One correction to the framing of the question: the
  fixed-strip hypothesis forbids alpha = 1, and a shrinking-delta union is
  *optional* rather than required, since one fixed strip already contains
  sigma_c.

- **The bridge verifies, with no gap found.** Theorem 4.3 implies Belovas et
  al.'s Conjecture 1, and its "only if" half also re-proves their Theorem 1.
  The concern that closure membership might only supply zeros "at infinity" is
  answered by the definition of R_f, whose approximating zeros are points of U
  and therefore sit at finite, if uncontrolled, heights.

- **What the hunt may claim** is section 9's five items and nothing more, with
  the two corrections in 9.1 applied first.

- **The strongest item is the bridge**, and it is a claim about the literature
  rather than about mathematics. Say that plainly.
