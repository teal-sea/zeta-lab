# The minor arcs do not need the model: an arc-split budget for \(E_{\rm corr}^{(Z)}\)

2026-09-11. Base: `ENDPOINT_SHARP.md` (commit 367573c, the endpoint checkpoint,
unchanged), `UPPER_BOUND.md` sections 2 to 5, `LOCALIZED_MIXED_ENERGY.md`
section 6, `SIEGEL_UNIFORMITY.md` (19). Assignment: take equation (22) of
`LOCALIZED_MIXED_ENERGY.md` as the route, retain every cross term including the
model remainder, and use the actual arithmetic coefficients to look for
cancellation, with the enlarged-\(Z\) corrected target held fixed.

**Result, stated first.** With the notation of `ENDPOINT_SHARP.md` section 1,
\(Z=\exp(\sqrt\ell)\), \(\ell=\log N\), and \(\gamma\) the constant of its
progression input (1\('\)), for every fixed \(c''<\min(2\gamma/3,\ 2c_m)\),
\[
 \boxed{\ E_{\rm corr}^{(Z)}(N)\ \ll\ N^3\exp\!\big(-c''\sqrt{\log N}\big).\ }
\tag{S$'$}
\]
`ENDPOINT_SHARP.md` (18\('\)) gives the same shape with the exponent constant
\(c'=\tfrac12\min(2\gamma-7\sigma,\ \sigma/6,\ c,\ 2c_m)\) at
\(\sigma=\min(\gamma/20,1/20)\), i.e. \(c'=\gamma/240\); the best that budget
allows over \(\sigma\) is \(\gamma/43\). Here the constant is \(2\gamma/3\), and
three of the four inputs `ENDPOINT_SHARP.md` section 6 names as capping the
exponent are no longer consumed: the divisor approximant (its section 2, both
variants), the minor-arc character estimates of `ENDPOINT_BOUND.md` section 4,
and the terms \(N^3R^{-1/6}\), \(N^{14/5}\), \(N^{2+A(N)}e^{\sqrt\ell/2}\) of
the budget. The rate \(\sqrt\ell\) is unchanged; this is a better constant in
the exponent and a shorter chain, not a power saving.

**The mechanism, in one paragraph.** Equation (22) splits the corrected
residual \(G_{\rm corr}=X+Y+R_{\rm mod}\) along the model: \(X+Y\) is what the
model leaves of \(|F|^2\), \(R_{\rm mod}\) is what the model misses of the target.
In coefficient space the model cancels identically in the sum (section 1), so
the split is not intrinsic, and the previous chain paid for it twice: on the
minor arcs it had to bound the model exponential sum \(H\) (which is what the
divisor approximant, the Type I estimate and the character cases were for), and
it lost the cross term between \(|F|^2\) and \(|H|^2\) there by writing
\((|F|^2-|H|^2)^2\le2|F|^4+2|H|^4\). The repair is to split by **arcs** instead:
insert the model only on the major arcs, where \(|F|^2-|H|^2\) is small because
the model reproduces the main term of \(|F|^2\) at every rational with
denominator \(r\le R\), and on the minor arcs keep \(G_{\rm corr}\) whole, where
it is \(|F|^2\) minus the singular-series polynomial and the minor-arc size of
that polynomial is governed by the arithmetic coefficients
\(\mu(q)^2/\phi(q)^2\) of the Ramanujan expansion of \(\mathfrak S(h)\), through
the large sieve. Every cross term of (22) is retained on the minor arcs because
nothing is split there. This is the architecture of `UPPER_BOUND.md` section 5,
whose baseline (1) is the classical \(N^3L^{-C}\), moved to the corrected target
with the major-arc cutoff \(R=\exp(\sigma\sqrt\ell)\) that the model and its
progression input make available.

Grade: derived, one route, finite checks in section 8, independently read.
No power saving, no statement about exceptional zeros beyond what the
inputs carry, nothing about the zeros of \(\zeta\).

**Independent check, 2026-09-12** (attempt `a-0078`,
`ARC_SPLIT_BUDGET_REVIEW.md`). No defect in any of the five sections. It
verified (2) and (3) to floating-point precision on its own toy model,
recomputed sections 3 and 5 against the cited equations including the
account of \(R^7\) becoming \(R^2\) and both budgets' optima
(\(\gamma/43\) for the old one at its own optimum, \(\gamma/240\) as stated,
\(2\gamma/3\) here), confirmed that on the minor arcs the document cites
`UPPER_BOUND.md` and nothing of the divisor approximant, and re-derived the
quadratic piece of 4.1 in full with its three ranges and the consistency
check against `SIEGEL_UNIFORMITY.md` (23). Two things it checked at the
level of orders rather than symbol by symbol, and said so: the auxiliary
sieve-tail bound \(\sum_{m>X,\,g\mid m}\phi(m)^{-2}\ll g\,\phi(g)^{-2}X^{-1}\ell^{O(1)}\)
in the \(m>\sqrt N\) range, and the constants of the linear pieces. Neither
is a binding term, so an error there confined to logarithmic factors would
not change (S\('\)); both are named here so that they are redone if 4.1 is
ever consumed by something that binds on them.

## 1. Notation, and the identity that makes (22) non-intrinsic

From `UPPER_BOUND.md` section 2, with \(y=\lfloor\sqrt N\rfloor\):
\(\mathfrak S_y(h)=\sum_{q\le y}\mu(q)^2c_q(h)/\phi(q)^2\),
\(V_y(\alpha)=\sum_{q\le y}\mu(q)^2\phi(q)^{-2}\sum_a^*|K_N(\alpha-a/q)|^2\),
\(d_N=\sum_{n\le N}\Lambda(n)^2\), \(a_0(N,y)=d_N-N\mathfrak S_y(0)\),
\(G_y=|F|^2-V_y-a_0(N,y)\), and the tail
\(D_{\rm tail}(N,y)=2\sum_{h\le N}(N-h)^2|\mathfrak S(h)-\mathfrak S_y(h)|^2\ll N^2\)
(its (6)). From `LOCALIZED_MIXED_ENERGY.md` section 6, with the exceptional
correction \(C_N(h)=C_{q,\beta,Z}(h)\) of `SIEGEL_UNIFORMITY.md` (19) at this
\(Z\) (zero when no exceptional zero exists):
\[
 \widehat C_N(\alpha)=2\sum_{h=1}^NC_N(h)\cos(2\pi h\alpha),\qquad
 G_{\rm corr}=G_y-\widehat C_N=X+Y+R_{\rm mod},
\]
\(X=\mathcal C(2\operatorname{Re}\overline HW)\), \(Y=\mathcal C(|W|^2)\),
\(R_{\rm mod}=\mathcal C(|H|^2-V_y)-\widehat C_N\), \(\mathcal C\) removing the
constant coefficient. Its (24), from `UPPER_BOUND.md` (4):
\[
 \big|\sqrt{E_{\rm corr}^{(Z)}}-\|G_{\rm corr}\|_2\big|\le\sqrt{D_{\rm tail}(N,y)}\ll N,
 \qquad\text{so}\qquad
 E_{\rm corr}^{(Z)}\le2\|G_{\rm corr}\|_2^2+O(N^2).
\tag{1}
\]

**Coefficients.** For \(1\le h\le N\), with \(\psi_2(N,h)=\sum_{n\le N-h}\Lambda(n)\Lambda(n+h)\)
and \(\psi_2^a(N,h)=\sum_{n\le N-h}a(n)a(n+h)\):
\[
 \begin{aligned}
 [X+Y]_h&=\psi_2(N,h)-\psi_2^a(N,h),\\
 [R_{\rm mod}]_h&=\psi_2^a(N,h)-(N-h)\mathfrak S_y(h)-C_N(h),\\
 [G_{\rm corr}]_h&=\psi_2(N,h)-(N-h)\mathfrak S_y(h)-C_N(h).
 \end{aligned}
\tag{2}
\]
The model appears in the first two lines with opposite signs and not in the
third. Whatever \(a(n)\) is, \(X+Y\) and \(R_{\rm mod}\) carry equal and
opposite copies of \(\psi_2^a\), of the sieve remainder inside it, and of the
part of the truncated singular series the model reproduces. So
\(2\operatorname{Re}\langle X+Y,R_{\rm mod}\rangle=\|G_{\rm corr}\|^2-\|X+Y\|^2-\|R_{\rm mod}\|^2\)
is not a quantity with independent arithmetic content; it is the accounting
correction for having split a model-independent object along a model. A bound
that keeps \(G_{\rm corr}\) whole retains it exactly. That is what the minor arcs
below do.

The same identity in the other direction is what the major arcs use:
pointwise on the whole circle,
\[
 G_{\rm corr}=\big(|F|^2-|H|^2\big)+R_{\rm mod}-\kappa,\qquad
 \kappa:=d_N-\sum_{n\le N}a(n)^2,
\tag{3}
\]
since \(\mathcal C(|F|^2)-\mathcal C(|H|^2)=|F|^2-|H|^2-\kappa\) and
\(\mathcal C(|F|^2)-\mathcal C(V_y)-\widehat C_N=[\mathcal C(|F|^2)-\mathcal C(|H|^2)]+R_{\rm mod}\).
Section 8 item (1) checks (3) numerically, including the sign of \(\kappa\).
Here \(|\kappa|\ll N\ell\): \(d_N\le\ell\,\psi(N)\) and
\(\sum a(n)^2\le4b^2N\) with \(b\sim e^{\gamma_E}\sqrt\ell\).

## 2. The arcs

`UPPER_BOUND.md` (7) with \(Q:=R\):
\[
 R=\lfloor\exp(\sigma\sqrt\ell)\rfloor,\quad 2R^2<N,\quad
 I_{r,a}=\{\alpha:\|\alpha-a/r\|\le R/(rN)\},\quad
 \mathfrak M=\bigcup_{r\le R}\bigcup_a^*I_{r,a},\quad
 \mathfrak m=\mathbb T\setminus\mathfrak M .
\]
The arcs are disjoint and \(|\mathfrak M|\le2R^2/N\). On \(\mathfrak m\),
Dirichlet approximation with \(\lceil N/R\rceil\) gives a reduced \(a/r\) with
\(R<r\le2N/R\) and \(|\alpha-a/r|\le r^{-2}\) (`UPPER_BOUND.md` section 5).
The radius \(R/(rN)\) rather than `ENDPOINT_BOUND.md`'s \(2R/N\) is used below;
it costs nothing and it removes one factor of \(R\) from the major arcs. By
(1),
\[
 E_{\rm corr}^{(Z)}\le2\int_{\mathfrak M}|G_{\rm corr}|^2+2\int_{\mathfrak m}|G_{\rm corr}|^2+O(N^2).
\tag{4}
\]

## 3. Major arcs: the model, inserted where it cancels

By (3), \(\int_{\mathfrak M}|G_{\rm corr}|^2\le3\int_{\mathfrak M}(|F|^2-|H|^2)^2+3\|R_{\rm mod}\|_2^2+3\kappa^2|\mathfrak M|\).

*(a) The intensity difference.* \(|F|^2-|H|^2=W\overline F+H\overline W\), so
\(||F|^2-|H|^2|\le|W|(|F|+|H|)\). For \(\alpha=a/r+\theta\in I_{r,a}\), split
\(W\) into residue classes modulo \(r\); each class is a progression, so
(1\('\)) of `ENDPOINT_SHARP.md` section 4 (uniform over every prefix \(y\le N\),
every \(r\le R\), every residue) and partial summation give
\[
 |W(\alpha)|\le\sum_{b\bmod r}\Big|\sum_{n\equiv b\ (r)}w_ne(n\theta)\Big|
 \le r\,(1+2\pi N|\theta|)\,C_1Ne^{-\gamma\sqrt\ell}
 \le(r+2\pi R)\,C_1Ne^{-\gamma\sqrt\ell}\le8C_1RNe^{-\gamma\sqrt\ell},
\tag{5}
\]
using \(N|\theta|\le R/r\). Then, by Parseval on the whole circle,
\[
 \int_{\mathfrak M}(|F|^2-|H|^2)^2\le\sup_{\mathfrak M}|W|^2\int_{\mathbb T}(|F|+|H|)^2
 \le64C_1^2R^2N^2e^{-2\gamma\sqrt\ell}\cdot2\Big(d_N+\sum a(n)^2\Big)
 \ll N^3\ell\,R^2e^{-2\gamma\sqrt\ell}.
\tag{6}
\]
`ENDPOINT_BOUND.md` (9) has \(N^3\ell^2R^7e^{-2\gamma t}\) for the same integral:
\(R^3\) from \(|\mathfrak M|\) times the pointwise bound \(|F|+|H|\ll N\ell\),
which Parseval replaces by \(\int(|F|+|H|)^2\ll N\ell\), and two more powers of
\(R\) from the arc radius \(2R/N\) in place of \(R/(rN)\). Nothing else in (6)
differs from that derivation; the prime-model cancellation is retained in the
same way.

*(b) The model remainder.* By (2), \([R_{\rm mod}]_h=[\psi_2^a(N,h)-(N-h)\mathfrak S(h)-C_N(h)]+(N-h)(\mathfrak S(h)-\mathfrak S_y(h))\),
and the first bracket is input (2) of `ENDPOINT_SHARP.md` section 5 at this
\(Z\): \(O(Ne^{-c_m\sqrt\ell})\) uniformly in \(h\). So
\[
 \|R_{\rm mod}\|_2^2\le4\sum_{h\le N}\big|\psi_2^a-(N-h)\mathfrak S-C_N\big|^2+2D_{\rm tail}(N,y)
 \ll N^3e^{-2c_m\sqrt\ell}+N^2 .
\tag{7}
\]
This is `LOCALIZED_MIXED_ENERGY.md` (24), squared. It is integrated here over
\(\mathfrak M\) only, but bounded by its whole-circle norm; no gain and no loss.

*(c) The constant.* \(\kappa^2|\mathfrak M|\ll N^2\ell^2\cdot R^2/N=NR^2\ell^2\).

Altogether
\[
 \int_{\mathfrak M}|G_{\rm corr}|^2\ll N^3\ell R^2e^{-2\gamma\sqrt\ell}+N^3e^{-2c_m\sqrt\ell}+NR^2\ell^2+N^2 .
\tag{8}
\]

## 4. Minor arcs: no model, the singular-series polynomial instead

On \(\mathfrak m\) the arc model \(A_R\) of `UPPER_BOUND.md` section 3 vanishes,
so its identity (10), \(G_y=B_R-H_R-a_0(N,R)-T_{y,R}\) with \(B_R=|F|^2-A_R\),
reads
\[
 G_{\rm corr}\big|_{\mathfrak m}=|F|^2-H_R-a_0(N,R)-T_{y,R}-\widehat C_N ,
\]
where \(H_R=V_R-A_R\ge0\) is the leakage of the \(q\le R\) kernels outside their
arcs and \(T_{y,R}=\mathcal C(V_y-V_R)\) is the truncation between \(R\) and
\(y\). Hence
\[
 \int_{\mathfrak m}|G_{\rm corr}|^2\le5\Big[I_R+\int_{\mathfrak m}H_R^2+a_0(N,R)^2|\mathfrak m|
 +\int_{\mathfrak m}|T_{y,R}|^2+\int_{\mathfrak m}|\widehat C_N|^2\Big],
\qquad I_R=\int_{\mathfrak m}|F|^4 .
\tag{9}
\]
Four of the five are `UPPER_BOUND.md`'s, valid for any \(R\) with \(2R^2<N\):

- \(I_R\le\sup_{\mathfrak m}|F|^2\int_{\mathbb T}|F|^2\ll(N^3/R+N^{13/5})L^6\), its (20), from
  Vaughan's bound on \(\mathfrak m\) where every approximating denominator exceeds \(R\).
- \(\int_{\mathfrak m}H_R^2\le\|H_R\|_2^2\ll N^3R^{-2}\log(2R)\,w(R)^2\ll N^3\ell^3R^{-2}\), its (13) and (15).
- \(a_0(N,R)=N\log(N/R)+O(N)\), so \(a_0(N,R)^2|\mathfrak m|\ll N^2\ell^2\).
- \(\int_{\mathfrak m}|T_{y,R}|^2\le\|T_{y,R}\|_2^2\ll N^3/R^2\), its (9).

The fifth is new and is proved in 4.1:
\[
 \int_{\mathfrak m}|\widehat C_N|^2\ll N^3\ell^{O(1)}/R,
\tag{10}
\]
with \(\widehat C_N=0\) when no exceptional zero exists. Therefore
\[
 \int_{\mathfrak m}|G_{\rm corr}|^2\ll N^3\ell^{O(1)}R^{-1}+N^{13/5}\ell^6+N^2\ell^2 .
\tag{11}
\]
Compare `ENDPOINT_BOUND.md` (17): \(\ell^{O(1)}[N^3R^{-1/6}+N^{14/5}+N^2D_0\sqrt Z]+N^3e^{-c\sqrt\ell}\).
The \(R^{-1/6}\) was the model's minor-arc bound (15), the \(N^{14/5}\) came
from bounding \(\int_{\mathfrak m}|H|^4\) through a cubic moment, and the
\(N^2D_0\sqrt Z\) was the approximant's level. None of the three objects is
present in (9).

### 4.1 The correction polynomial on the minor arcs

By `SIEGEL_UNIFORMITY.md` (19), (17), with \(\mathcal L_h=(q/\phi(q))^2S_*(h)\),
\(S_*(h)=\prod_{p<Z,\,p\nmid q}\alpha_p(h)=\sum_{d\mid P,(d,q)=1}c_d(h)/\phi(d)^2\),
\[
 C_N(h)=\mathcal L_h\Big[\frac{c_q(h)}qJ_{12}(h)\Big]
 -1_{q\ \rm odd}\,\mathcal L_h\frac{\mu(q)}q\big[\chi(-h)J_1(h)+\chi(h)J_2(h)\big],
\]
\(J_1,J_2\ll N^\beta\le N\), \(J_{12}\ll N^{2\beta-1}\le N\), all three
nonnegative and nonincreasing in \(h\) on \(1\le h\le N\) (their integrands are;
\(J_1(h)\) has \(T=N-h\)), and all zero at \(h=N\). For a nonnegative
nonincreasing weight \(J\) write \(\Phi_J(x)=\sum_{0<|h|\le N}J(|h|)e(hx)\); Abel
summation gives \(|\Phi_J(x)|\le J(1)/\|x\|\) and \(|\Phi_J(x)|\le2NJ(1)\).

*The quadratic piece.* `LOCALIZED_MIXED_ENERGY.md` (5):
\(\mathcal L_hc_q(h)/q=\sum_{d\mid P,(d,q)=1}q\,\phi(qd)^{-2}c_{qd}(h)\), so
\[
 \widehat C_N^{\rm quad}(\alpha)=\sum_{\substack{d\mid P\\(d,q)=1}}\frac q{\phi(qd)^2}
 \sum_{a\bmod qd}^{*}\Phi_{J_{12}}\big(\alpha-\tfrac a{qd}\big).
\]
Split the fractions by their denominator \(m=qd\).

- \(R<m\le\sqrt N\). Bound the whole-circle norm in coefficient space: the
  coefficient at \(h\) is \(J_{12}(h)\) times a sum over fractions with
  denominators in \((R,\sqrt N]\), which are \(1/N\)-spaced, so the dual large
  sieve gives
  \[
   \sum_{h\le N}\Big|J_{12}(h)\sum_{R<qd\le\sqrt N}\frac q{\phi(qd)^2}c_{qd}(h)\Big|^2
   \le4N^2\cdot2N\sum_{R<qd\le\sqrt N}\phi(qd)\frac{q^2}{\phi(qd)^4}
   \le8N^3\frac{q^2}{\phi(q)^3}\sum_{d>R/q}\frac{\mu(d)^2}{\phi(d)^3}
   \ll N^3\ell^{O(1)}\min\Big(\frac1q,\frac q{R^2}\Big)\le\frac{N^3\ell^{O(1)}}R,
  \]
  using \(q/\phi(q)\ll\log\log q\le\ell\), \(\sum_{d>D}\mu(d)^2/\phi(d)^3\ll D^{-2}\ell^{O(1)}\)
  for \(D\ge1\) and \(O(1)\) for \(D<1\). Both cases of the minimum are at most \(1/R\):
  if \(q\le R\) then \(q/R^2\le1/R\), and if \(q>R\) then \(1/q<1/R\).
- \(m>\sqrt N\). With \(|c_m(h)|\le\gcd(m,h)\) and \(\sum_{m>X,\,g\mid m}\phi(m)^{-2}\ll g\,\phi(g)^{-2}X^{-1}\ell^{O(1)}\),
  the coefficient at \(h\) is \(\ll N\,q\,\tau(h)\ell^{O(1)}/\sqrt N\), and with
  \(q<Z=e^{\sqrt\ell}\), \(\sum_{h\le N}\tau(h)^2\ll N\ell^3\), the mean square is
  \(\ll N^2e^{2\sqrt\ell}\ell^{O(1)}=N^{2+o(1)}\).
- \(m\le R\), present only when \(q\le R\). These centres lie in \(\mathfrak M\); on
  \(\mathfrak m\), \(\|\alpha-a/m\|>R/(mN)\). The \(\phi(m)\) points \(a/m\) are
  \(1/m\)-spaced, so \(\sum_a^*\|\alpha-a/m\|^{-1}\le mN/R+2m(1+\log m)\le4mN/R\)
  for large \(N\), and
  \[
   \sup_{\mathfrak m}\Big|\sum_{qd\le R}\cdots\Big|\le\sum_{d\le R/q}\frac q{\phi(qd)^2}\cdot2N\cdot\frac{4qdN}R
   \ll\frac{N^2q^2}{\phi(q)^2R}\sum_{d\le R/q}\frac d{\phi(d)^2}\ll\frac{N^2\ell^{O(1)}}R,
  \]
  \[
   \int_{\mathfrak m}\Big|\sum_{qd\le R}\cdots\Big|\le\sum_{d\le R/q}\frac q{\phi(qd)}\int_{\|x\|>R/(qdN)}\frac{2N}{\|x\|}dx
   \ll N\ell\frac q{\phi(q)}\sum_{d\le R/q}\frac1{\phi(d)}\ll N\ell^{O(1)},
  \]
  so this part has \(\int_{\mathfrak m}|\cdot|^2\le\sup\cdot\int|\cdot|\ll N^3\ell^{O(1)}/R\).

*The linear pieces* (odd \(q\) only). For primitive \(\chi\),
\(\chi(h)\tau(\overline\chi)=\sum_{a\bmod q}\overline\chi(a)e(ah/q)\) for every
\(h\), with \(|\tau(\overline\chi)|=\sqrt q\), so \(\chi(\pm h)S_*(h)\) is a sum
over fractions with denominators dividing \(qd\), \(d\mid P\), \((d,q)=1\), with
coefficients of modulus at most \(q^{-1/2}\phi(d)^{-2}\); the weight in front
is \((q/\phi(q))^2q^{-1}\), and \(J_1,J_2\le2N\). The same three ranges give:
for \(R<qd\le\sqrt N\), by the large sieve,
\(\ll N^3(q^2/\phi(q)^4)\sum_{d>R/q}d\,\phi(d)^{-4}\ll N^3\ell^{O(1)}q^{-2}\min(1,q^2/R^2)\le N^3\ell^{O(1)}/R^2\);
for \(qd>\sqrt N\), \(N^{2+o(1)}\) as above; for \(qd\le R\), the same tail
argument with the weight \(q^{1/2}/(\phi(q)^2\phi(d)^2)\), giving
\(\ll N^3\ell^{O(1)}/R\). This proves (10). Consistency check: for \(q>R\) every
fraction is in the first two ranges and the bound is \(\ll N^3\ell^{O(1)}/q\),
which is `SIEGEL_UNIFORMITY.md` (23)'s whole-circle energy
\(N^{4\beta-1}q^2/\phi(q)^3+N^{2\beta+1}q^2/\phi(q)^4\) up to logarithms, as it
must be.

## 5. The budget

From (4), (8), (11):
\[
 E_{\rm corr}^{(Z)}(N)\ll N^3\ell R^2e^{-2\gamma\sqrt\ell}+N^3e^{-2c_m\sqrt\ell}
 +N^3\ell^{O(1)}R^{-1}+N^{13/5}\ell^6+NR^2\ell^2+N^2\ell^2 .
\tag{12}
\]
Take \(R=\lfloor\exp(\sigma\sqrt\ell)\rfloor\) with \(\sigma=2\gamma/3\). The
constraints are \(2R^2<N\) and \(\sigma\le1/\sqrt2\) (`ENDPOINT_SHARP.md`
section 4 needs \(R\le e^{\sqrt{\ell/2}}\)), both satisfied since
\(\gamma<1/2\) gives \(\sigma<1/3\). Then \(R^2e^{-2\gamma\sqrt\ell}\le e^{-(2\gamma/3)\sqrt\ell}\)
and \(R^{-1}\le2e^{-(2\gamma/3)\sqrt\ell}\), so
\[
 E_{\rm corr}^{(Z)}(N)\ll N^3\ell^{O(1)}e^{-(2\gamma/3)\sqrt\ell}+N^3e^{-2c_m\sqrt\ell},
\]
which is (S\('\)). Here \(c_m=1/4-o(1)\) (the fundamental lemma at level
\(N^{1/4}\) in input (2), `ENDPOINT_HALF.md` section 2.1), and \(\gamma<1/2\), so
\(2c_m>2\gamma/3\) and the model term is not the binding one; the boxed
statement keeps it in the minimum so that nothing is assumed about which
constant is smaller.

**Against the previous budget.** Both budgets balance a major-arc term
\(N^3R^ke^{-2\gamma\sqrt\ell}\) against a minor-arc term \(N^3R^{-j}\). The
previous one had \(k=7\), \(j=1/6\): optimum at \(\sigma=12\gamma/43\), exponent
\(\gamma/43\), and the stated \(\sigma=\gamma/20\) gives \(\gamma/240\). This one
has \(k=2\), \(j=1\): optimum at \(\sigma=2\gamma/3\), exponent \(2\gamma/3\).
The gain in \(k\) is bookkeeping (Parseval, arc radius); the gain in \(j\) is
the mechanism: Vaughan's \(R^{-1}\) for \(|F|^4\) replaces the approximant's
\(R^{-1/6}\) for \(|H|^2\), because \(H\) is not bounded on the minor arcs at all.

## 6. What the arc split removes, and what it keeps

Not consumed by (S\('\)): `ENDPOINT_BOUND.md` section 2 (the Bonferroni
approximant \(B_m\), its (4)-(6)), section 4 (Type I (10), the character
estimate (12), Cases A and B (13)-(14), the minor-arc model bound (15)),
section 5 (the cubic moment (16) and the minor-arc integral (17)); and in
`ENDPOINT_SHARP.md`, section 2 in both variants (the Mertens correction, the
retuned cutoff and (A), the \(\beta\)-sieve alternative) and section 3. The
level \(D_0\), the function \(A(N)\), the properties (P1)-(P4) and the term
\(N^{2+A(N)}e^{\sqrt\ell/2}\) do not appear. Those statements remain correct
as statements about the divisor approximant; the complete bound no longer
routes through it.

Consumed: input (1\('\)) with (DF), (Pg), (FL) at level \(D_1\) and (Cmp), all
from `ENDPOINT_SHARP.md` section 4; input (2) from its section 5; the
arc estimates of `UPPER_BOUND.md` (7), (9), (13), (15), (20); and 4.1 above.

`ENDPOINT_SHARP.md` section 6 names four inputs that cap the exponent at
\(\sqrt\ell\) and attain it. After this document, the divisor approximation is
not one of them for the complete bound. The cap now rests on (1\('\)) (a
zero-free region question for the \(L\)-functions of conductor at most \(R\)),
on (2) (the fundamental lemma at a level fixed by \(Z\)), and on the arc
balance itself: the minor-arc term decays only polynomially in \(R\), because
\(|F|^2\) is of size \(N^2/\phi(r)^2\) at every rational with denominator just
above \(R\), while the major-arc term decays like \(e^{-2\gamma\sqrt\ell}\) with
\(\gamma\) tied to \(\log R\) through the zero-free region. Balancing a power of
\(R\) against \(\exp(-c\,\ell/\log R)\) puts \(\log R\) at \(\sqrt\ell\)
whatever the constants. That statement is about this architecture.

## 7. The route through (22), and the refuted sub-candidate

The assignment asked for cancellation in the cross terms of (22). Section 1
records what they are: the cross term \(2\operatorname{Re}\langle X,Y\rangle\)
was already retained by `ENDPOINT_BOUND.md`, which never separates \(X\) from
\(Y\) (its \(D=\|X+Y\|^2\)); the cross term
\(2\operatorname{Re}\langle X+Y,R_{\rm mod}\rangle\) is the accounting correction
for a split along the model, and the minor arcs retain it exactly by not
splitting. The model is inserted only on the major arcs, in the form (3),
where its purpose is to cancel the main term of \(|F|^2\) at each \(a/r\).

**Refuted sub-candidate: cancellation between \(X+Y\) and \(R_{\rm mod}\)
improves the exponent.** It does not, in either budget. Whatever the sign of
\(2\operatorname{Re}\langle X+Y,R_{\rm mod}\rangle\), the term it can remove is
at most \(2\|R_{\rm mod}\|^2\ll N^3e^{-2c_m\sqrt\ell}+N^2\) by (7), and
\(2c_m\) is not the binding constant: `ENDPOINT_SHARP.md` (18\('\)) binds at
\(\sigma/6=\gamma/120\), and (12) binds at \(2\gamma/3\). Retaining or
discarding that cross term changes the constant in front, not the exponent.
There is a genuine cancellation inside it (by (2), the part of the truncated
singular series that the model reproduces, and the model's own sieve
remainder, appear with opposite signs in \(X+Y\) and \(R_{\rm mod}\)), but it is
cancellation of a term that was never binding. The candidate is refuted as an
improvement, with the witness being the two budgets' binding terms.

What did move the exponent constant is section 4: the model's presence on the
minor arcs, not any cross term, was the cost.

**Checked against previous attempts.** `UPPER_BOUND.md` section 5 is this
argument for the original \(E\) with \(Q=L^B\) and Siegel-Walfisz in place of
(1\('\)); its (1) is \(N^3L^{-C}\), and the reason it stops at logarithms is
that Siegel-Walfisz caps the major-arc cutoff at a power of \(L\). The model
and (1\('\)) lift that cap to \(e^{\sigma\sqrt\ell}\); nothing else changes.
`UPPER_BOUND.md` section 6 with \(Q=\sqrt N/3\) is the rank-3 programme and is
not touched. `RANK3_QUARTIC_LITERATURE.md` and `w-bound-raw-arc-quartic-moment`
record that no bound on \(\int_{\mathfrak m}|F|^4\) below Vaughan's \(N^3L^6/R\)
is available to the hunt; (9) uses exactly Vaughan's. The two judged proposals
of `a-0071`, `w-corr-longwindow-meansquare` (equation (20)) and
`w-corr-crossterm-cancellation` (the two cross terms), are addressed as
follows: the second is answered in this section; the first concerns the
\(q=1\) positive-kernel majorant of `LOCALIZED_MIXED_ENERGY.md`, which is a
bound on a majorant of the mixed energy and not a component of (12); (12)
does not route through it.

**What a stronger bound would establish.** A fixed power saving
\(E_{\rm corr}^{(Z)}\ll N^{3-\delta}\) would, through the correlation identity
of `CORRECTED_RH_BRIDGE.md` section 4, bound \(\psi(N)-N\) by
\(N^{1-\delta/2}\) up to the exceptional term, which is the strength of a
zero-free strip for \(\zeta\). Nothing of that kind is claimed or approached
here; (S\('\)) is subpolynomial, like everything before it.

## 8. Finite checks

`arc_split_probe.py`, results in `results_arc_split_probe.json`, about three
seconds. No exceptional zero exists at these \(N\), so \(C_N=0\) and
\(E_{\rm corr}=E\); nothing below tests 4.1 or any asymptotic statement.

**(1) The identity (3)**, with the toy model \(\nu(n)=b\,1_{(n,30)=1}\)
(\(Z=7\), \(b=35/8\)) at \(N=2000\) on a grid of \(2^{14}\) points: the maximum
of \(|G_y-(|F|^2-|H|^2)-R_{\rm mod}+\kappa|\) is \(1.0\times10^{-10}\) against
\(\max|G_y|=8.0\times10^4\), with \(\kappa=d_N-\sum a(n)^2=5483.7\) entering with
the minus sign as written.

**(2) The arc split at \(N=8000\)**, grid \(2^{19}\), \(y=89\):
\(E=6.198\times10^8\) from the \(h\)-sum, \(J_{\rm ms}(N,y)=6.972\times10^8\)
from the \(h\)-sum and from the grid (relative defect \(2\times10^{-15}\)),
\(D_{\rm tail}(N,y)=1.0085\,N^2\), and
\((\sqrt E-\sqrt{J_{\rm ms}})/\sqrt{D_{\rm tail}}=-0.19\), inside (1). With the
arcs of section 2 at \(Q=R\):

| \(R\) | \(|\mathfrak M|/(2R^2/N)\) | \(\int_{\mathfrak M}|G_y|^2/J\) | \(I_R/(N^3/R)\) | \(I_R\,R^2/N^3\) | \(\int_{\mathfrak m}(V_y+a_0)^2/(N^3/R^2)\) | \(\sup_{\mathfrak m}|F|^2/(N^2/R)\) |
| --- | --- | --- | --- | --- | --- | --- |
| 3 | 0.72 | 0.037 | 0.354 | 1.06 | 1.09 | 0.74 |
| 6 | 0.63 | 0.064 | 0.153 | 0.92 | 0.93 | 0.38 |
| 12 | 0.62 | 0.101 | 0.136 | 1.63 | 1.59 | 0.33 |
| 24 | 0.62 | 0.207 | 0.122 | 2.92 | 2.51 | 0.38 |
| 48 | 0.61 | 0.464 | 0.087 | 4.20 | 2.52 | 0.19 |

Read: the minor-arc fourth moment sits between \(N^3/R^2\) and \(N^3/R\) at this
\(N\), below Vaughan's \(N^3L^6/R\) by a factor of order \(10^6\); the
minor-arc energy of the main-term polynomial \(V_y+a_0(N,y)\), which is
\(H_R+a_0(N,R)+T_{y,R}\) there, is \(1\) to \(2.5\) times \(N^3/R^2\), the
order (9)'s second and fourth terms predict; at \(N=8000\) the minor arcs carry
most of the mean square at every \(R\) shown, which is what one expects while
\(e^{-\gamma\sqrt\ell}\) is not yet small. None of these numbers tests (S\('\)).

**(3) The tail mean square** behind the large-sieve step of 4.1, at
\(N=8000\): \(\sum_{h\le N}|\mathfrak S(h)-\mathfrak S_R(h)|^2\) against
\(N\,\mathcal T(R)\), \(\mathcal T(R)=\sum_{q>R}\mu(q)^2/\phi(q)^3\), is
\(0.99,\ 0.93,\ 0.90,\ 0.79,\ 0.65\) at \(R=5,10,20,40,80\): the tail is at the
orthogonality prediction and below the large-sieve bound \(2N\mathcal T(R)\)
by a factor \(2\) to \(3\).

## 9. Scope

One mechanism, attempted to a checked budget. The result is a better constant
in the exponent of the same subpolynomial bound, obtained by not using the
sieve model on the minor arcs, and a shorter list of inputs. The divisor
approximant of the previous chain is not refuted; it is unused. The refuted
candidate is the cross term with the model remainder as a lever on the
exponent. No fixed power saving, no novelty claim, no statement about
exceptional zeros beyond the inputs, nothing about the zeros of \(\zeta\).
Sections 3 to 5 have had an independent read (`ARC_SPLIT_BUDGET_REVIEW.md`);
the two order-level steps of 4.1 it names are recorded at the top.
