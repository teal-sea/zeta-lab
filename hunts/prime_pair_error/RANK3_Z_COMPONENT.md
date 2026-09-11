# The fourth residual moment \(Z_{q\le R_0}\): its \(q=1\) structure, its rank-1 pin, and a bound below \(N^3\log N\)

2026-09-11, corrected the same day (section 4 rewritten around a cited
theorem; the first version carried a reversed density-exponent condition
and an overstated zero-free-region saving, both recorded in section 4).
Continues `RANK3_CONDUCTOR_SUM.md`, which bounded the \(U\)-side of
`UPPER_BOUND.md` (23) at rank 1's order. This document treats the one
component of (23) that had no estimate at all: the fourth residual moment
over the small moduli,
\[
 Z_{q\le R_0}=\sum_{q\le R_0}Z_{(q)},\qquad
 Z_{(q)}=\sum_{a\bmod q}^*\int_{I_{q,a}}|R_{q,a}|^4,
\]
with \(Q=\lfloor\sqrt N/3\rfloor\), \(R_0=Q/L\), \(L=\log N\), the arcs
\(I_{q,a}=\{\|\alpha-a/q\|\le\delta_q\}\), \(\delta_q=Q/(qN)\), and
\(R_{q,a}=F_N-P_{q,a}\) as in `UPPER_BOUND.md` sections 3 and 6.

**Result, stated first.**

1. **The exact \(q=1\) structure.** \(Z_{(1)}=\int_{|\beta|\le Q/N}|D(\beta)|^4d\beta\)
   with \(D=F_N-K_N=\sum_{n\le N}(\Lambda(n)-1)\exp1(n\beta)\). Its full-circle
   version is a Goldbach-type mean square of order \(N^3\) (section 2) and
   is not a useful proxy; the arc-restricted quantity is controlled by the
   sequence \(\Lambda(n)-1\) summed over windows of length
   \(H=N/(2Q)\asymp\sqrt N\), by Gallagher's lemma.
2. **The pin exists.** By Cauchy-Schwarz against \(|K_N|^2\),
   \[
    \boxed{\ Z_{(1)}\ \ge\ \frac{3\,U_1^2}{2N^3+N}\ \ge\ \frac{3}{2N^3}\big(T_N-O(N^2L)\big)^2(1+o(1)),\ }
   \tag{Z'}
   \]
   and the same for \(Z_{q\le R_0}\ge Z_{(1)}\). It is quadratic where (K')
   of `RANK3_CONDUCTOR_SUM.md` was linear. Its consequence: a bound
   \(Z_{q\le R_0}\ll N^{3-\eta}\) for a fixed \(\eta>0\) would establish
   \(\zeta(s)\ne0\) for \(\operatorname{Re}s>1-\eta/4\) (section 3).
3. **The first bound below the trivial \(N^3L\).** For every fixed \(A>0\),
   unconditionally,
   \[
    \boxed{\ Z_{q\le R_0}\ \ll_A\ N^3L^{-A}.\ }
   \tag{Z}
   \]
   Moduli \(q\le L^C\) go through Gallagher's lemma and Koukoulopoulos's
   Theorem 1.1 on primes in short arithmetic progressions, applied at the
   interval lengths \(H_q=qN/(2Q)\), between \(\tfrac32\sqrt N\) and
   \(\tfrac32L^C\sqrt N\) (section 4). Moduli \(L^C<q\le R_0\) go through
   Vaughan's bound (V) and the disjointness of the arcs, exactly as (28)
   does above \(R_0\) (section 5).
4. **The complete budget (23) is now priced** (section 6): every component
   is bounded unconditionally, the total it yields is
   \(N^3L^{-A}+N^{13/5}L^6\), which is (1) again, and the two pins (K') and
   (Z') state what a stronger bound on any pinned component would
   establish: \(N^{3-\delta}\) on a pinned component gives a zero-free
   half-plane, and the target \(N^{2+\epsilon}\) gives RH.

Grade: derived, one route, with one theorem cited from its arXiv text and
one classical lemma cited from memory (section 1), finite checks at
\(q=1\) in section 7. Nothing here is evidence about the zeros of \(\zeta\)
or of any \(L\)-function; the one statement involving zeros is the
consequence of a hypothetical bound, in the form `UPPER_BOUND.md` section 1
already uses.

## 1. Inputs

- (23): \(E(N)\le32U_Q+8Z_Q+4I_Q+O(N^2L^3)\), with \(Z_Q=Z_{q\le R_0}+Z_{q>R_0}\)
  and \(Z_{q>R_0}\ll N^{13/5}L^6\) by (28).
- The arcs \(I_{q,a}\), \(q\le Q\), are pairwise disjoint (`UPPER_BOUND.md`
  section 3), so \(\sum_{q\le Q}\sum_a^*\int_{I_{q,a}}|F_N|^2\le\int_{\mathbb T}|F_N|^2=d_N\ll NL\),
  and \(\sum_{q,a}\int_{I_{q,a}}|P_{q,a}|^2\le N\sum_{q\le Q}\mu(q)^2/\phi(q)\ll NL\).
  Hence the trivial bound \(Z_Q\le\sup|R|^2\sum_{q,a}\int_{I_{q,a}}|R_{q,a}|^2\ll N^2\cdot NL=N^3L\).
- (V), valid on \(I_{q,a}\) for \(q\le R_0\) since \(\delta_q\le q^{-2}\) there:
  \(|F_N(\alpha)|\ll(Nq^{-1/2}+N^{4/5}+\sqrt{Nq})L^{5/2}\).
- **Gallagher's lemma** (Montgomery, *Topics in Multiplicative Number
  Theory*, LNM 227, Lemma 1.9; cited from memory, not re-read here): for
  \(0<\theta\le\tfrac12\) and any finitely supported \(a_n\),
  \[
   \int_{-\theta}^{\theta}\Big|\sum_na_n\exp1(n\beta)\Big|^2d\beta
   \ \ll\ \theta^2\int_{-\infty}^{\infty}\Big|\sum_{x<n\le x+1/(2\theta)}a_n\Big|^2dx.
  \tag{G}
  \]
  Scaling check: \(a_n=1\) for \(n\le N\), \(\theta\ge1/N\), both sides
  \(\asymp N\).
- **Koukoulopoulos, Theorem 1.1** (D. Koukoulopoulos, *Primes in short
  arithmetic progressions*, arXiv:1405.6592v2, read from the arXiv text in
  this session). With
  \[
   E(y,h;q)=\max_{(a,q)=1}\Big|\sum_{\substack{y<p\le y+h\\ p\equiv a\ (q)}}\log p-\frac h{\phi(q)}\Big|,
  \]
  and (1.2) there the zero-density hypothesis
  \(\sum_{q\le Q_K}\sum^*_{\chi\bmod q}N(\sigma,T,\chi)\ll(Q_K^2T)^{c(1-\sigma)}\log^M(Q_KT)\):
  *Assume that (1.2) holds for some \(c\in[2,4]\). Fix \(A\ge1\) and
  \(\epsilon\in(0,1/3]\). If \(x\ge h\ge1\) and \(1\le Q_K^2\le h/x^{1-2/c+\epsilon}\),
  then*
  \[
   \int_x^{2x}\sum_{q\le Q_K}E(y,h;q)\,dy\ \ll_{\epsilon,A}\ \frac{hx}{(\log x)^A}.
  \tag{K}
  \]
  The paper records that (1.2) is known with \(c=12/5+\epsilon\), \(M=14\)
  (Montgomery, Theorem 12.2, and Huxley 1975), so the range \(Q_K^2\le h/x^{1/6+\epsilon}\)
  is unconditional. It is also known with \(c=3\), \(M=9\) (Montgomery,
  Theorem 12.1), which gives the range \(Q_K^2\le h/x^{1/3+\epsilon}\); that
  weaker input already covers everything used below. His \(Q_K\) is a bound
  on moduli and is not `UPPER_BOUND.md`'s arc parameter \(Q\).

## 2. The exact \(q=1\) structure

At \(q=1\), \(P_{1,1}=K_N\), \(R_{1,1}=D:=F_N-K_N=\sum_{n=1}^Nd(n)\exp1(n\beta)\),
\(d(n)=\Lambda(n)-1\), and
\[
 Z_{(1)}=\int_{|\beta|\le Q/N}|D(\beta)|^4\,d\beta.
\]

**The full circle is the wrong object.** \(\int_{\mathbb T}|D|^4=\sum_{m=2}^{2N}|c_m|^2\)
with \(c_m=\sum_{n_1+n_2=m,\ n_i\le N}d(n_1)d(n_2)\). Expanding,
\(c_m=G_N(m)-2S_N(m)+r_N(m)\), where \(G_N(m)=\sum_{n_1+n_2=m}\Lambda(n_1)\Lambda(n_2)\)
is the Goldbach count truncated at \(N\), \(S_N(m)=\sum\Lambda(n_1)\) over
the same pairs, and \(r_N(m)\) is their number. For \(m\le N\) this is
\(c_m=\big(G_N(m)-m\mathfrak S(m)\big)+m\big(\mathfrak S(m)-1\big)-2\Delta(m-1)+O(1)\),
and the middle term alone has square sum \(\asymp N^3\), because
\(\mathfrak S(m)-1\) is \(-1\) on every odd \(m\) and does not average
to zero over short ranges. So \(\int_{\mathbb T}|D|^4\asymp N^3\)
unconditionally, measured at \(0.87N^3\) in section 7 and at
\(1.53\,\phi(q)N^3\) for general \(q\) in `RANK3_QUARTIC_TOOLS.md`. On the
full circle \(D\) still contains every major arc with \(q\ge2\);
subtracting \(K_N\) removes only the one at \(0\). This is why a
full-circle identity in the style of (D5) does not help \(Z\), as
`RANK3_ROUTE_D.md` section 7 already recorded: the \(N^3\) is the
\(q\ge2\) arcs, not a bookkeeping artifact.

**The arc is a short-interval statement.** By (G) with \(\theta=Q/N\),
\(H:=1/(2\theta)=N/(2Q)\), and \(d(n)\) supported on \(1\le n\le N\),
\[
 \int_{|\beta|\le Q/N}|D|^2\ \ll\ \frac{Q^2}{N^2}\,V_H,\qquad
 V_H:=\int_{-H}^{N}\Big(\sum_{\substack{x<n\le x+H\\ n\le N}}d(n)\Big)^2dx,
\tag{1}
\]
the mean square of the prime-counting error over windows of length
\(H\asymp\tfrac32\sqrt N\), with the windows at the two ends truncated.
This is the structure: the \(q=1\) arc of width \(Q/N\) sees primes at
resolution \(\sqrt N\), and nothing pointwise. Partial summation on the arc
gives only \(|D(\beta)|\le\max_t|\Delta(t)|(1+2\pi|\beta|N)\), which at
\(|\beta|=Q/N\) is \(\asymp\sqrt N\max|\Delta|\), worse than the trivial
\(2N\) unconditionally; the arc is too wide for the classical major-arc
approximation and too close to \(0\) for (V). The mean square (1) is the
object that can be bounded.

## 3. The pin, and what a stronger bound would establish

**Lemma.** For every \(N\), \(Z_{(1)}\ge3U_1^2/(2N^3+N)\).

*Proof.* \(U_1=\int_{|\beta|\le Q/N}|K_N|^2|D|^2\le\big(\int_{|\beta|\le Q/N}|K_N|^4\big)^{1/2}Z_{(1)}^{1/2}\)
by Cauchy-Schwarz, and \(\int_{|\beta|\le Q/N}|K_N|^4\le\int_{\mathbb T}|K_N|^4
=\#\{n_1+n_2=n_3+n_4:\,1\le n_i\le N\}=(2N^3+N)/3\). \(\square\)

With (30), \(U_1\ge T_N-O(N^2L)\), this is (Z'). The same argument at any
squarefree \(q\) gives \(Z_{(q)}\ge3\phi(q)\,U_{(q)}^2/(2N^3+N)\) (Cauchy-Schwarz
on each arc, then on the sum over \(a\)), so also \(Z_{(2)}\ge\tfrac{3}{8N^3}(T_N-O(N^2L))^2\)
by (K'). Only \(q=1\) is needed below.

**Consequence.** Suppose \(Z_{q\le R_0}\ll N^{3-\eta}\) for one fixed
\(0<\eta<1\). Then \(Z_{(1)}\ll N^{3-\eta}\), so by (Z') \(T_N\ll N^{3-\eta/2}\),
so \(\sum_{t\le N}\Delta(t)^2\ll N^{3-\eta/2}\), and by the dyadic
Cauchy-Schwarz and Mellin argument of `RANK3_CONDUCTOR_SUM.md` section 5,
\(\zeta(s)\ne0\) for \(\operatorname{Re}s>1-\eta/4\). So the \(Z\)-side of
(23) has a rank-1 pin with the constant \(\eta/4\) in place of \(\delta/2\):
a quadratic pin delivers half the exponent. Under RH the pin is far from
the truth, \(Z_{(1)}\gg NL^{c}\) against a conjectural \(Z_{(1)}\ll N^{5/2}L^{2}\);
the numbers in section 7 sit between the two, at \(Z_{(1)}/N^{5/2}\) falling
from \(4\times10^{-4}\) to \(1\times10^{-4}\) over the ladder. The pin's
content is what a successful stronger bound would carry with it, and it
answers the question this document was asked: a bound \(Z_{q\le R_0}\ll N^{3-\eta}\)
would be a theorem about the zeros of \(\zeta\), of exactly the stated
width.

## 4. Upper bound for \(q\le L^C\): Gallagher plus Koukoulopoulos

**Correction notice.** The first version of this section claimed a
short-interval variance bound for all \(H\ge N^{1/6+\epsilon}\) from
Montgomery's Theorem 12.1, whose density exponent is \(3/(2-\sigma)\le3\).
That is reversed: with exponent \(c\) the argument needs
\(G^c\le N^{2-\epsilon}\) for \(G\asymp N/H\), i.e. \(H\ge N^{1-2/c+\epsilon}\),
which is \(N^{1/3+\epsilon}\) for \(c=3\) and \(N^{1/6+\epsilon}\) only for
Huxley's \(c=12/5\). It also claimed that a zero-free region of Littlewood
width \(c\log\log T/\log T\) gives an arbitrary log-power saving. It does
not: \(N^{-\eta/2}\) with that \(\eta\) is \((\log N)^{-c/2}\), one fixed
power, which the \(\log^MN\) in the density estimate can outweigh. Both
statements are withdrawn. The section now rests on (K), whose own inputs
are the density estimate (1.2) and its author's proof, and it is applied
only at the interval lengths that actually occur, \(H_q\in[\tfrac32\sqrt N,\tfrac32L^C\sqrt N]\).

Fix \(C>0\) and \(1\le q\le L^C\) (non-squarefree \(q\) have \(P_{q,a}=0\)
and are handled identically with the \(\mu(q)/\phi(q)\) term absent).
Coefficients: \(R_{q,a}(\beta)=\sum_{n\le N}r_{q,a}(n)\exp1(n\beta)\),
\(r_{q,a}(n)=\Lambda(n)\exp1(na/q)-\mu(q)/\phi(q)\). Then
\[
 Z_{(q)}\le\sum_a^*\sup_{I_{q,a}}|R_{q,a}|^2\int_{I_{q,a}}|R_{q,a}|^2
 \le4N^2\sum_a^*\int_{|\beta|\le\delta_q}|R_{q,a}|^2
 \ll N^2\delta_q^2\sum_a^*\int\Big|\sum_{\substack{x<n\le x+H_q\\ n\le N}}r_{q,a}(n)\Big|^2dx,
\tag{2}
\]
by (G) with \(H_q=1/(2\delta_q)=qN/(2Q)\), windows truncated to \(n\le N\)
as in (1), \(x\) from \(-H_q\) to \(N\). Grouping \(n\) by residue class,
with \(\psi_{x,H}(q,b)=\sum_{x<n\le x+H,\,n\le N,\ n\equiv b}\Lambda(n)\) and
\(H'=H'(x)\) the truncated window length, and using \(\sum_b^*\exp1(ab/q)=\mu(q)\),
\[
 \sum_{x<n\le x+H_q}r_{q,a}(n)
 =\sum_{b\bmod q}^*\exp1(ab/q)\Big[\psi_{x,H_q}(q,b)-\frac{H_q'}{\phi(q)}\Big]
 +\sum_{\substack{b\bmod q\\(b,q)>1}}\exp1(ab/q)\psi_{x,H_q}(q,b)+O(1).
\]
The non-coprime classes contain only prime powers of primes dividing
\(q\), at most \(\omega(q)\log_2N\) of them in any window, each weighted by
at most \(L\), so that sum is \(O(\omega(q)L^2)=O(L^3)\). Extending the sum
over \(a\) from the reduced residues to all residues mod \(q\) (every term
is nonnegative) and applying Parseval on \(\mathbb Z/q\mathbb Z\),
\[
 \sum_a^*\Big|\sum_{x<n\le x+H_q}r_{q,a}(n)\Big|^2
 \le2q\sum_b^*\Big|\psi_{x,H_q}(q,b)-\frac{H_q'}{\phi(q)}\Big|^2+O(qL^6).
\tag{3}
\]
(The first version wrote \(2\phi(q)\) here, which would need orthogonality
over the reduced residues alone; that gives Ramanujan sums, not a delta.
The factor \(q\) is the correct one and is harmless.)

**Corollary of (K), in the shape needed.** Let \(1\le q\le L^C\) and
\(h\in[\tfrac32\sqrt N,\tfrac32L^C\sqrt N]\). For every fixed \(A\),
\[
 \int_{1}^{N-h}\sum_{b\bmod q}^*\Big(\psi(y{+}h;q,b)-\psi(y;q,b)-\frac h{\phi(q)}\Big)^2dy
 \ \ll_{A,C}\ q\,h^2N\,L^{-A}.
\tag{4}
\]

*Proof.* Write \(\theta\) for the prime-only count. In a window \((y,y+h]\)
with \(y\le N\), the prime powers \(p^k\), \(k\ge2\), number at most
\(h/\sqrt y+\log_2N\) and weigh at most \(L\) each, so
\(\psi(y{+}h;q,b)-\psi(y;q,b)=\theta(y{+}h;q,b)-\theta(y;q,b)+O((h/\sqrt y+L)L)\).
For \(y\ge h\) and \(h\le\tfrac32L^C\sqrt N\) that error is \(O(L^{C+2})\),
and its square integrates to \(O(NL^{2C+4})=O(h^2NL^{-A})\). For \(y<h\)
bound everything trivially: the integrand is \(O(h^2L^2)\) on a range of
length \(h\), contributing \(O(h^3L^2)=O(h^2N\cdot hL^2/N)\ll h^2NL^{-A}\)
since \(h/N\ll N^{-1/2}L^C\). So it suffices to treat \(\theta\) on
\(y\in[h,N-h]\), which we cover by dyadic blocks \([x,2x]\) with \(h\le x\le N\).
On each block, \(\theta(y{+}h;q,b)-\theta(y;q,b)-h/\phi(q)\) is bounded
in modulus by \(E(y,h;q)\) for every reduced \(b\), and also, trivially, by
\(\theta(y{+}h)-\theta(y)+h\ll h\) (Brun-Titchmarsh, \(h\ge N^{1/3}\)). Hence
\[
 \sum_b^*\Big(\theta(y{+}h;q,b)-\theta(y;q,b)-\frac h{\phi(q)}\Big)^2
 \le\phi(q)\cdot E(y,h;q)^2\ll\phi(q)\,h\,E(y,h;q).
\]
Apply (K) with \(Q_K=q\) (the sum over \(q'\le q\) has nonnegative terms
and dominates the single term \(q'=q\)), \(c=3\), \(\epsilon=1/12\): the
hypothesis \(Q_K^2=q^2\le h/x^{1/3+1/12}\) holds since \(q^2\le L^{2C}\) and
\(h/x^{5/12}\ge\tfrac32\sqrt N/N^{5/12}=\tfrac32N^{1/12}\) for \(x\le N\),
and \(x\ge h\) holds on every block used. So
\(\int_x^{2x}\phi(q)hE(y,h;q)dy\ll_A\phi(q)h\cdot hx(\log x)^{-A}\), and
summing over the \(O(L)\) dyadic blocks gives (4) with one more power of
\(L\), absorbed by renaming \(A\). \(\square\)

The corollary is the theorem's \(L^1\) statement multiplied by the trivial
pointwise bound; nothing sharper than (K) is used, and the ranges are
exactly those of (K) with Ingham's exponent. With Huxley's \(c=12/5\) the
same proof runs for \(h\ge N^{1/6+\epsilon}\), a range not needed here.

Insert (3) and (4) into (2), using \(N^2\delta_q^2=Q^2/q^2\) and
\(H_q^2=q^2N^2/(4Q^2)\), and the trivial bound on the truncated windows at
both ends exactly as in the proof above:
\[
 Z_{(q)}\ll_{A,C}\frac{Q^2}{q^2}\Big[q\cdot qH_q^2NL^{-A}+qNL^6\Big]
 =\tfrac14q^2N^3L^{-A}+\frac{Q^2NL^6}{q},
\]
and summing over \(q\le L^C\),
\[
 \boxed{\ Z_{q\le L^C}\ \ll_{A,C}\ N^3L^{3C-A}+N^2L^{6}.\ }
\tag{5}
\]

## 5. Upper bound for \(L^C<q\le R_0\): Vaughan plus disjointness

On \(I_{q,a}\) with \(q\le R_0\), (V) gives
\(|F_N|\ll(NL^{-C/2}+N^{4/5}+N^{3/4})L^{5/2}\ll NL^{5/2-C/2}\), and
\(|P_{q,a}|\le N/\phi(q)\le\zeta(2)N(1+\log q)/q\ll NL^{1-C}\), so
\(\sup_{I_{q,a}}|R_{q,a}|^2\ll N^2L^{5-C}\) uniformly. Then, by the
disjointness of the arcs (section 1),
\[
 Z_{L^C<q\le R_0}\le\max_{L^C<q\le R_0}\sup_{I_{q,a}}|R_{q,a}|^2\cdot\sum_{q,a}\int_{I_{q,a}}|R_{q,a}|^2
 \ll N^2L^{5-C}\cdot NL,
\]
\[
 \boxed{\ Z_{L^C<q\le R_0}\ \ll\ N^3L^{6-C}.\ }
\tag{6}
\]
This is (28)'s argument with the cut at \(L^C\) instead of \(R_0\). What it
cannot reach is \(q\) below \(L^C\), where (V) saves nothing, which is why
section 4 is needed and why the two ranges meet at a power of \(\log\).

## 6. The result, and the complete budget

Take \(C=A+6\) in (6) and \(A\to A+3C\) in (5): for every fixed \(A\),
\[
 Z_{q\le R_0}\ll_AN^3L^{-A}+N^2L^6\ll_AN^3L^{-A},
\]
which is (Z). Together with (28) for \(q>R_0\): \(Z_Q\ll_AN^3L^{-A}+N^{13/5}L^6\).

The budget of `UPPER_BOUND.md` (23), every component now bounded
unconditionally:

| Component | Bound | Pin | Where |
| --- | --- | --- | --- |
| Tail and geometric leakage | \(O(N^2L^3)\) | none needed | (16) |
| \(U_1\) | \(O_H(N^3L^{-2H})\) | \(=T_N-O(N^2L)\) | (29), (30) |
| \(U_{2\le q\le R_0}\) | \(O_A(N^3L^{-A})+O(N^2L^{2+o(1)})\) | \(\ge\tfrac12T_N-O(N^2L)\) | (K), (K') |
| \(U_{q>R_0}\) | \(O(N^2L^5)\) | none needed | (27) |
| \(Z_{q\le R_0}\) | \(O_A(N^3L^{-A})\) | \(\ge3U_1^2/(2N^3+N)\) | (Z), (Z') |
| \(Z_{q>R_0}\), \(I_Q\) | \(O(N^{13/5}L^6)\) | none | (28), (22) |

Consequences:

- **(23) now yields (1).** \(E(N)\ll_AN^3L^{-A}+N^{13/5}L^6\): the same
  order `UPPER_BOUND.md` section 5 reached with polylogarithmic arcs, now
  reached with square-root arcs and every component priced. No new total
  bound.
- **What a stronger bound on a pinned component would establish.** By
  (K') at \(q=2\) and (Z') at \(q=1\), a bound \(N^{3-\delta}\) on any of
  \(U_1\), \(U_{2\le q\le R_0}\), \(Z_{(1)}\), \(Z_{q\le R_0}\) would give
  \(\Theta\le1-\delta/2\) (the \(U\)-side) or \(\Theta\le1-\delta/4\) (the
  \(Z\)-side): a zero-free half-plane for \(\zeta\), which is not known. The
  two unpinned components, \(I_Q\) and \(Z_{q>R_0}\), are already at
  \(N^{13/5}\).
- **The target through (23).** Reaching \(N^{2+\epsilon}\) would prove RH
  (`UPPER_BOUND.md` section 1); reaching \(N^{3-\delta}\) would prove a
  zero-free strip, by the pins. Ranks 1 and 3 are one quantity seen in two
  moments, so a bound of either strength on either component carries the
  same consequence. This replaces `RANK3_SCOPE.md` section 4's rank
  ordering with an equivalence.
- **The log powers.** Sharpening \(L^{-A}\) to a sub-power saving in (K)
  and (Z) is a matter of replacing (SW) and the inputs of Theorem 1.1 by
  Vinogradov-Korobov-strength inputs throughout; it leaves both pins
  unchanged and is not attempted.

## 7. Finite checks at \(q=1\)

`rank3_z_component_probe.py`, results in `results_rank3_z_component_probe.json`,
\(N\in\{10^3,5\times10^3,2\times10^4,6\times10^4\}\), numpy only:

- \(Z_{(1)}\) and \(U_1\) on grids of \(32N\) and \(64N\) points agree to
  relative \(10^{-3}\) or better; \(\int_{\mathbb T}|D|^4/N^3\) is
  \(0.82,\ 0.86,\ 0.86,\ 0.87\), the full circle at order \(N^3\) as
  section 2 says.
- The pin (Z') holds at every \(N\), with \(Z_{(1)}\) above \(3U_1^2/(2N^3+N)\)
  by factors \(1.8\times10^4\) to \(2.3\times10^5\): far from binding at
  these \(N\), as expected of a quadratic pin at scales where
  \(U_1\ll N^2L^c\).
- \(Z_{(1)}/N^3\) falls \(1.4\times10^{-5}\to4.9\times10^{-7}\) and
  \(Z_{(1)}/N^{5/2}\) falls \(4.3\times10^{-4}\to1.2\times10^{-4}\) across
  the ladder; the measured \(Z_{(1)}\) is below \(N^{5/2}\) at every \(N\)
  tried. The ratio \(Z_{(1)}/(N\,V_H)\) is \(3\times10^{-4}\) and falling:
  the sup bound \(|D|\le2N\) used in (2) is lossy by that much at these
  \(N\), which is where a sharper bound would have to look.

These check identities, an inequality and measured ratios at small \(N\).
They test no asymptotic statement, and in particular (4) is not measured
here.

## 8. Scope

This document is one exact lower bound (Cauchy-Schwarz), one reduction
(Gallagher's lemma to short-interval mean squares in bounded-modulus
progressions), one cited theorem applied in its stated range, and one
two-line extension of (28). It establishes the first unconditional bound
below \(N^3\log N\) for the fourth residual moment over the small moduli,
at rank 1's order, together with the pin that states what a stronger bound
would establish. It proves no power saving, claims none, and establishes
nothing about the zeros of \(\zeta\) or of any \(L\)-function.
