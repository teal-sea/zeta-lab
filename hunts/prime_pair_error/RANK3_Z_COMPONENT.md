# The fourth residual moment \(Z_{q\le R_0}\): its \(q=1\) structure, its rank-1 pin, and a bound below \(N^3\log N\)

2026-09-11. Continues `RANK3_CONDUCTOR_SUM.md`, which closed the \(U\)-side
of `UPPER_BOUND.md` (23) at rank 1's order. This document treats the one
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
   is useless; the arc-restricted quantity is controlled by the sequence
   \(\Lambda(n)-1\) summed over windows of length \(H=N/(2Q)\asymp\sqrt N\),
   by Gallagher's lemma.
2. **The pin exists.** By Cauchy-Schwarz against \(|K_N|^2\),
   \[
    \boxed{\ Z_{(1)}\ \ge\ \frac{3\,U_1^2}{2N^3+N}\ \ge\ \frac{3}{2N^3}\big(T_N-O(N^2L)\big)^2(1+o(1)),\ }
   \tag{Z'}
   \]
   and the same for \(Z_{q\le R_0}\ge Z_{(1)}\). It is quadratic where (K')
   of `RANK3_CONDUCTOR_SUM.md` was linear, and it prices the same way:
   \(Z_{q\le R_0}\ll N^{3-\eta}\) for a fixed \(\eta>0\) forces
   \(\zeta(s)\ne0\) for \(\operatorname{Re}s>1-\eta/4\) (section 3).
3. **The first bound below the trivial \(N^3L\).** For every fixed \(A>0\),
   unconditionally,
   \[
    \boxed{\ Z_{q\le R_0}\ \ll_A\ N^3L^{-A}.\ }
   \tag{Z}
   \]
   Moduli \(q\le L^C\) go through Gallagher's lemma and the mean square of
   primes in short intervals, in arithmetic progressions of bounded modulus,
   which a zero-density estimate plus a zero-free region of Littlewood width
   control with an arbitrary log-power saving (section 4). Moduli
   \(L^C<q\le R_0\) go through Vaughan's bound (V) and the disjointness of
   the arcs, exactly as (28) does above \(R_0\) (section 5).
4. **The complete budget (23) is now priced** (section 6): every one of its
   components is bounded unconditionally, the total it yields is
   \(N^3L^{-A}+N^{13/5}L^6\), which is (1) again, and the two pins (K') and
   (Z') show that no component can be taken below \(N^3\) by a fixed power
   without a zero-free strip. The route through (23) is exactly as hard as
   its target.

Grade: derived, one route, two classical theorems cited whose exact
published form is flagged where it matters (section 4), finite checks at
\(q=1\) in section 7. Nothing here is evidence about the zeros of \(\zeta\)
or of any \(L\)-function; the one statement involving zeros is a priced
implication of a hypothetical bound, in the form `UPPER_BOUND.md` section 1
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
  Theory*, LNM 227, Lemma 1.9): for \(0<\theta\le\tfrac12\) and any finitely
  supported \(a_n\),
  \[
   \int_{-\theta}^{\theta}\Big|\sum_na_n\exp1(n\beta)\Big|^2d\beta
   \ \ll\ \theta^2\int_{-\infty}^{\infty}\Big|\sum_{x<n\le x+1/(2\theta)}a_n\Big|^2dx.
  \tag{G}
  \]
  Scaling check: \(a_n=1\) for \(n\le N\), \(\theta\ge1/N\), both sides
  \(\asymp N\).
- **Explicit formula** for \(\psi(x,\chi)\), \(\chi\) of conductor \(q\),
  \(2\le T\le x\): \(\psi(x,\chi)=\delta_\chi x-\sum_{|\gamma|\le T}x^\rho/\rho+O((x/T)\log^2(qx)+\log^2(qx))\),
  \(\delta_\chi=1\) for the principal character and \(0\) otherwise
  (Davenport, Chapters 17 and 19).
- **Zero density** (Montgomery, LNM 227, Theorem 12.1):
  \(\sum_{q\le Q'}\sum_{\chi\ \mathrm{prim}\bmod q}N(\sigma,T,\chi)\ll(Q'^2T)^{3(1-\sigma)/(2-\sigma)}\log^9(Q'T)\).
  Only the exponent \(3/(2-\sigma)\le3<4\) at \(\sigma\) near \(1\) is used.
- **Zero-free region.** Every \(L(s,\chi)\), \(\chi\) primitive of conductor
  \(q\le L^C\), has no zero with \(\sigma\ge1-\eta(T)\), \(|\gamma|\le T\),
  \(T\le N\), except possibly one real zero \(\beta_1\) of one real
  \(\chi_1\) (Page), where \(\eta(T)\) may be taken as
  \(c\log\log T/\log T\) (Littlewood's region; for \(\zeta\) this is
  Titchmarsh, Theorem 5.17; for \(L(s,\chi)\) the same argument, or the
  Vinogradov-Korobov region \(c/((\log q)+(\log T)^{2/3}(\log\log T)^{1/3})\),
  Iwaniec and Kowalski, Chapter 8). For the exceptional zero, Siegel's
  theorem \(\beta_1\le1-c(\epsilon)q^{-\epsilon}\), ineffective, exactly
  the input (SW) already carries.
- **Mean value over zeros** (Saffari and Vaughan, *Ann. Inst. Fourier* 27
  (1977), Lemma 6, in the form used by Selberg's method): for coefficients
  \(c_\rho\) indexed by the zeros with \(|\gamma|\le T\),
  \[
   \int_X^{2X}\Big|\sum_\rho c_\rho x^{\rho}\Big|^2dx\ \ll\ X\log^2(XT)\sum_\rho|c_\rho|^2X^{2\beta}.
  \tag{MV}
  \]
  This follows from \(|\int_X^{2X}x^{\rho+\bar\rho'}dx|\ll X^{\beta+\beta'+1}/(1+|\gamma-\gamma'|)\),
  Cauchy-Schwarz, and \(\sum_{\rho'}(1+|\gamma-\gamma'|)^{-1}\ll\log^2T\).

The exact theorem numbers for (G), (MV) and the Littlewood-type region for
\(L(s,\chi)\) were not re-read from the sources in this session; each is
standard, the derivations below are self-contained given the displayed
statements, and the only role of the citations is provenance.

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
and the middle term alone has square sum \(\asymp N^3\) because
\(\mathfrak S(m)-1\) does not average to zero over short ranges in \(m\):
it is \(-1\) on odd \(m\). So \(\int_{\mathbb T}|D|^4\asymp N^3\)
unconditionally, measured at \(0.87N^3\) in section 7 and at
\(1.53\,\phi(q)N^3\) for general \(q\) in `RANK3_QUARTIC_TOOLS.md`. What
\(D\) still contains, on the full circle, is every major arc with \(q\ge2\);
subtracting \(K_N\) removes only the one at \(0\). This is why no full-circle
identity (a (D5) for \(Z\)) can exist, as `RANK3_ROUTE_D.md` section 7
already recorded: the \(N^3\) is real, not a bookkeeping artifact.

**The arc is a short-interval statement.** By (G) with \(\theta=Q/N\),
\(H:=1/(2\theta)=N/(2Q)\), and \(d(n)\) supported on \(1\le n\le N\),
\[
 \int_{|\beta|\le Q/N}|D|^2\ \ll\ \frac{Q^2}{N^2}\,V_H,\qquad
 V_H:=\int_{-H}^{N}\Big(\sum_{\substack{x<n\le x+H\\ n\le N}}d(n)\Big)^2dx
 =\int_{-H}^N\big(\psi(\min(x{+}H,N))-\psi(x^+)-(\text{length})\big)^2dx,
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

## 3. The pin, and its price

**Lemma.** For every \(N\), \(Z_{(1)}\ge3U_1^2/(2N^3+N)\).

*Proof.* \(U_1=\int_{|\beta|\le Q/N}|K_N|^2|D|^2\le\big(\int_{|\beta|\le Q/N}|K_N|^4\big)^{1/2}Z_{(1)}^{1/2}\)
by Cauchy-Schwarz, and \(\int_{|\beta|\le Q/N}|K_N|^4\le\int_{\mathbb T}|K_N|^4
=\#\{n_1+n_2=n_3+n_4\le\ldots\}=(2N^3+N)/3\). \(\square\)

With (30), \(U_1\ge T_N-O(N^2L)\), this is (Z'). The same argument at any
squarefree \(q\) gives \(Z_{(q)}\ge3\phi(q)\,U_{(q)}^2/(2N^3+N)\) (Cauchy-Schwarz
on each arc, then on the sum over \(a\)), so also \(Z_{(2)}\ge\tfrac{3}{8N^3}(T_N-O(N^2L))^2\)
by (K'). Only \(q=1\) is needed below.

**Price.** Suppose \(Z_{q\le R_0}\ll N^{3-\eta}\) for one fixed \(0<\eta<1\).
Then \(Z_{(1)}\ll N^{3-\eta}\), so by (Z') \(T_N\ll N^{3-\eta/2}\), so
\(\sum_{t\le N}\Delta(t)^2\ll N^{3-\eta/2}\), and by the dyadic
Cauchy-Schwarz and Mellin argument of `RANK3_CONDUCTOR_SUM.md` section 5,
\(\zeta(s)\ne0\) for \(\operatorname{Re}s>1-\eta/4\). The \(Z\)-side of
(23) therefore has a rank-1 pin, with the constant \(\eta/4\) in place of
\(\delta/2\): quadratic pins pay half the exponent. Under RH the pin is
weak, \(Z_{(1)}\gg N L^{c}\) against a conjectural \(Z_{(1)}\ll N^{5/2}L^{2}\);
the numbers in section 7 sit between the two, at \(Z_{(1)}/N^{5/2}\) falling
from \(4\times10^{-4}\) to \(1\times10^{-4}\) over the ladder. The point of
the pin is not its size but that it converts any power saving on \(Z\) into
a statement about zeros, and so closes the question this document was
asked: there is no \(Z\)-side route to \(N^{3-\eta}\) that is easier than a
zero-free strip.

## 4. Upper bound for \(q\le L^C\): Gallagher plus the short-interval variance

Fix \(C>0\) and a squarefree \(q\le L^C\) (non-squarefree \(q\) have
\(P_{q,a}=0\) and \(R_{q,a}=F_N\); they are handled identically with the
\(\mu(q)/\phi(q)\) term absent). Coefficients:
\(R_{q,a}(\beta)=\sum_{n\le N}r_{q,a}(n)\exp1(n\beta)\),
\(r_{q,a}(n)=\Lambda(n)\exp1(na/q)-\mu(q)/\phi(q)\). Then
\[
 Z_{(q)}\le\sum_a^*\sup_{I_{q,a}}|R_{q,a}|^2\int_{I_{q,a}}|R_{q,a}|^2
 \le4N^2\sum_a^*\int_{|\beta|\le\delta_q}|R_{q,a}|^2
 \ll N^2\delta_q^2\sum_a^*\int\Big|\sum_{x<n\le x+H_q}r_{q,a}(n)\Big|^2dx,
\tag{2}
\]
by (G) with \(H_q=1/(2\delta_q)=qN/(2Q)\), windows truncated to \(n\le N\)
as in (1). Grouping \(n\) by residue class and using
\(\sum_b^*\exp1(ab/q)=\mu(q)\),
\[
 \sum_{x<n\le x+H_q}r_{q,a}(n)
 =\sum_{b\bmod q}^*\exp1(ab/q)\Big[\psi_{x,H_q}(q,b)-\frac{H_q'}{\phi(q)}\Big]
 +\sum_{\substack{b\bmod q\\(b,q)>1}}\exp1(ab/q)\psi_{x,H_q}(q,b)+O(1),
\]
where \(\psi_{x,H}(q,b)=\sum_{x<n\le x+H,\ n\equiv b}\Lambda(n)\) and
\(H_q'\) is the truncated window length. The non-coprime classes carry only
prime powers of primes dividing \(q\), at most \(\omega(q)\log_2N\) of them
in any window (a window of length \(\le N\) contains at most \(\log_2N\)
powers of each such prime, each weighted by at most \(L\)), so that sum is
\(O(\omega(q)L^2)=O(L^3)\).
Orthogonality over \(a\) (the identity of `RANK3_BDH_VERIFY.md` section 2)
gives
\[
 \sum_a^*\Big|\sum_{x<n\le x+H_q}r_{q,a}(n)\Big|^2
 \le2\phi(q)\sum_b^*\Big|\psi_{x,H_q}(q,b)-\frac{H_q'}{\phi(q)}\Big|^2+O(\phi(q)L^6).
\tag{3}
\]
Now decompose by characters mod \(q\): \(\psi_{x,H}(q,b)=\phi(q)^{-1}\sum_\chi\bar\chi(b)\psi_{x,H}(\chi)\)
with \(\psi_{x,H}(\chi)=\psi(x{+}H,\chi)-\psi(x,\chi)\), so
\[
 \sum_b^*\Big|\psi_{x,H}(q,b)-\frac{H'}{\phi(q)}\Big|^2
 =\frac1{\phi(q)}\Big[\big|\psi_{x,H}(\chi_0)-H'\big|^2+\sum_{\chi\ne\chi_0}|\psi_{x,H}(\chi)|^2\Big].
\tag{4}
\]
The principal term is the short-interval error of \(\psi\) itself up to
the same \(O(L^2)\) prime-power correction; an imprimitive \(\chi\) differs
from the primitive \(\chi^*\) inducing it by the same correction. So, from
(2), (3), (4),
\[
 Z_{(q)}\ll N^2\delta_q^2\Big[\int\big(\psi(x{+}H_q)-\psi(x)-H_q'\big)^2dx
 +\sum_{\substack{\chi^*\ \mathrm{prim}\\ \mathrm{cond}\mid q,\ \mathrm{cond}>1}}\int|\psi_{x,H_q}(\chi^*)|^2dx\Big]
 +O(N^2\delta_q^2\phi(q)NL^6),
\tag{5}
\]
all integrals over \(-H_q\le x\le N\) with the end windows truncated. The
last term is \(O(N^2\cdot Q^2q^{-2}N^{-2}\cdot\phi(q)NL^6)=O(NL^6\,Q^2/q)=O(N^2L^6)\).

**Lemma (short-interval variance, bounded conductor).** Let \(\chi\) be
primitive of conductor \(q\le L^C\), \(\delta_\chi\) as in section 1, and
\(N^{1/6+\epsilon}\le H\le N\). Then for every fixed \(A\),
\[
 \int_{1}^{N}\big|\psi(x{+}H,\chi)-\psi(x,\chi)-\delta_\chi H\big|^2dx\ \ll_{A,C,\epsilon}\ NH^2L^{-A}.
\tag{6}
\]
The truncated end windows change nothing: on \(x\in[-H,0]\) and
\(x\in[N-H,N]\) the integrand is at most \((\psi(2H)+H)^2\ll H^2L^2\) and
the range has length \(2H\), contributing \(O(H^3L^2)=O(NH^2L^2\cdot H/N)\),
which is \(\ll NH^2L^{-A}\) for \(H\le N^{1/2}L^{C'}\), the only case used.

*Proof sketch, the standard one.* Apply the explicit formula at \(x+H\) and
\(x\) with \(T=NL^{A+3}/H\le N\): the truncation error is
\(O(HL^{-A-1})\) per point, contributing \(O(NH^2L^{-2A-2})\). What remains
is \(\int_1^N|\sum_{|\gamma|\le T}c_\rho(x)|^2dx\) with
\(c_\rho(x)=((x{+}H)^\rho-x^\rho)/\rho\), and \(|c_\rho(x)|\le\min(Hx^{\beta-1},2x^\beta/|\gamma|)\).
By (MV) on dyadic blocks of \(x\), the integral is
\(\ll L^2N\sum_{|\gamma|\le T}\min(H^2N^{2\beta-2},N^{2\beta}\gamma^{-2})\).
Split at \(|\gamma|\le N/H\) and dyadically above. In the range
\(|\gamma|\le G\) with \(G\le T\le NL^{A+3}/H\), write the sum as
\(\int_0^1N^{2\sigma-2}\,d_\sigma N(\sigma,G,\chi)\); by the density bound
with \(Q'=q\le L^C\), \(N^{2\sigma-2}N(\sigma,G,\chi)\ll(N^{-2}(L^{2C}G)^{3/(2-\sigma)})^{1-\sigma}L^9
\le(N^{-2}(L^{2C}G)^{3})^{1-\sigma}L^9\), and since \(G\le NL^{A+3}/H\le N^{5/6-\epsilon}L^{A+3}\)
the base is \(\le N^{-1/2+3\epsilon}L^{O(1)}<1\), so the integrand is largest at
the largest admissible \(\sigma\), which is \(1-\eta(G)\) by the zero-free
region: \(\le N^{-(1/2-3\epsilon)\eta(G)}L^{O(1)}\). With Littlewood's
\(\eta(G)\ge c\log\log N/\log N\) this is \(\le L^{-c'\log\log N\cdot(1/2-3\epsilon)+O(1)}\),
smaller than any fixed power of \(L\); with the Vinogradov-Korobov region
it is \(\exp(-c''L^{1/3}(\log\log N)^{-1/3})\). The exceptional zero, if
\(\chi=\chi_1\), contributes \(H^2N^{2\beta_1-2}\le H^2\exp(-2c(\epsilon)L^{1-C\epsilon})\),
smaller still. Multiplying back by \(NL^2\) and by \(H^2\) or
\(N^2/G^2\le H^2\) gives (6). \(\square\)

For \(\chi=\chi_0\) this is Selberg's unconditional theorem for
\(\psi(x+H)-\psi(x)-H\); the range \(H\ge N^{1/6+\epsilon}\) is where the
density exponent \(3/(2-\sigma)<4\) keeps the base below \(1\). Here
\(H_q=qN/(2Q)\asymp q\sqrt N\ge N^{1/6+\epsilon}\) with room.

Insert (6) into (5), once for the principal term and once for each of the
at most \(\phi(q)\) primitive characters of conductor dividing \(q\):
\[
 Z_{(q)}\ll_{A,C}N^2\frac{Q^2}{q^2N^2}\cdot\phi(q)\cdot N\frac{q^2N^2}{4Q^2}L^{-A}+N^2L^6
 =\tfrac14\phi(q)N^3L^{-A}+N^2L^6,
\]
and summing over the at most \(L^C\) moduli,
\[
 \boxed{\ Z_{q\le L^C}\ \ll_{A,C}\ N^3L^{2C-A}+N^2L^{C+6}.\ }
\tag{7}
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
\tag{8}
\]
This is (28)'s argument with the cut at \(L^C\) instead of \(R_0\); it was
available all along. What it cannot do is reach \(q\) below \(L^C\), where
(V) saves nothing, which is why section 4 is needed and why the two ranges
meet at a power of \(\log\).

## 6. The result, and the complete budget

Take \(C=A+6\) in (8) and \(A\to2A+2C\) in (7): for every fixed \(A\),
\[
 Z_{q\le R_0}\ll_AN^3L^{-A}+N^2L^{O_A(1)}\ll_AN^3L^{-A},
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
  bound; the route is closed, not improved.
- **No component can go below \(N^3\) by a power without a zero-free
  strip.** (K') at \(q=2\) and (Z') at \(q=1\) pin both moment types to
  \(T_N\); a fixed power saving on any of \(U_1\), \(U_{2\le q\le R_0}\),
  \(Z_{(1)}\), \(Z_{q\le R_0}\) forces \(\Theta\le1-\delta/2\) or
  \(1-\eta/4\). The only components without pins, \(I_Q\) and
  \(Z_{q>R_0}\), are already at \(N^{13/5}\) and are not what blocks
  \(N^{3-\delta}\).
- **The target \(N^{2+\epsilon}\) through (23) is RH** in both directions
  now: reaching it would prove RH (`UPPER_BOUND.md` section 1), and any
  step toward it below \(N^3\) needs a zero-free strip first. This
  supersedes `RANK3_SCOPE.md` section 4's "rank 1 is the current
  bottleneck": there is no rank ordering left, because ranks 1 and 3 are
  one quantity in two moments.
- **The log powers are not harmless here and not worth chasing.** Sharpening
  \(L^{-A}\) to \(\exp(-c(\log N)^{\kappa})\) in (K) and (Z) is a matter of
  replacing (SW) and Littlewood's region by Vinogradov-Korobov throughout,
  and it changes nothing about the pins. It is not attempted.

## 7. Finite checks at \(q=1\)

`rank3_z_component_probe.py`, results in `results_rank3_z_component_probe.json`,
\(N\in\{10^3,5\times10^3,2\times10^4,6\times10^4\}\), numpy only:

- \(Z_{(1)}\) and \(U_1\) on grids of \(32N\) and \(64N\) points agree to
  relative \(10^{-3}\) or better; \(\int_{\mathbb T}|D|^4/N^3\) is
  \(0.82,\ 0.86,\ 0.86,\ 0.87\), the full circle at order \(N^3\) as
  section 2 says.
- The pin (Z') holds at every \(N\), with \(Z_{(1)}\) above \(3U_1^2/(2N^3+N)\)
  by factors \(1.8\times10^4\) to \(2.3\times10^5\): the pin is far from
  binding at these \(N\), as expected of a quadratic pin at scales where
  \(U_1\ll N^2L^c\).
- \(Z_{(1)}/N^3\) falls \(1.4\times10^{-5}\to4.9\times10^{-7}\) and
  \(Z_{(1)}/N^{5/2}\) falls \(4.3\times10^{-4}\to1.2\times10^{-4}\) across
  the ladder; the measured \(Z_{(1)}\) is below \(N^{5/2}\) at every \(N\)
  tried. The ratio \(Z_{(1)}/(N\,V_H)\) is \(3\times10^{-4}\) and falling:
  the sup bound \(|D|\le2N\) used in (2) is lossy by that much at these
  \(N\), which is where a sharper bound would have to look.

These check identities, an inequality and measured ratios at small \(N\).
They test no asymptotic statement, and in particular (6) is not measured
here.

## 8. Scope

This document is one exact lower bound (Cauchy-Schwarz), one reduction
(Gallagher's lemma to short-interval mean squares in bounded-modulus
progressions), one classical mean-square estimate reproduced with its
inputs named, and one two-line extension of (28). It establishes the first
unconditional bound below \(N^3\log N\) for the fourth residual moment over
the small moduli, at rank 1's order and no better, and the pin that says
no better is available without a zero-free strip. It proves no power
saving, claims none, and establishes nothing about the zeros of \(\zeta\)
or of any \(L\)-function.
