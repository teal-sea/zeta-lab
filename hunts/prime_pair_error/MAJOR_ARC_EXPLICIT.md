# The major arcs through the explicit formula: the exponent is the target's own threshold

2026-09-12. Base: `ARC_SPLIT_BUDGET.md` (commit a537765; its arcs, its minor-arc
bound (11) and its budget (12) are reused unchanged), `ENDPOINT_SHARP.md`
sections 1, 4 and 5 (the model at \(Z=\exp\sqrt\ell\), the exceptional data of
TT Definition 2.1 with threshold \(c_0\), the four sieve cases of its section 4,
input (2)), `UPPER_BOUND.md` (7), `SIEGEL_UNIFORMITY.md` (17), (19), (23).
Assignment: attack the binding term of the complete budget with the target
\(E_{\rm corr}^{(Z)}\) and every existing control held fixed.

**Result, stated first.** Let \(c_0\) be the threshold in the target's exceptional
data (\(\beta>1-c_0/\log Z\)), \(c\) the constant of the zero-free region (ZF)
below, \(b\) Page's constant in the form (Pg\('\)) below, and \(c_P\) the Page
constant `ENDPOINT_SHARP.md` calls \(c\). Under
\[
 c_0\le\min\big(2/9,\ \sqrt c/2,\ \sqrt b/2,\ c_P\big),
\tag{H}
\]
which TT's "sufficiently small" \(c_0\) satisfies, for every fixed \(c''<c_0\),
\[
 \boxed{\ E_{\rm corr}^{(Z)}(N)\ \ll\ N^3\exp\!\big(-c''\sqrt{\log N}\big).\ }
\tag{S$''$}
\]
`ARC_SPLIT_BUDGET.md` (S\('\)) has the constant \(2\gamma/3\) with
\(\gamma<c_0/2\) from `ENDPOINT_SHARP.md` section 4, so at most \(c_0/3\).
The rate \(\sqrt\ell\) is unchanged.

**What changed, and why it is structural.** The major arcs are now bounded by
the explicit formula for the character sums \(\sum_n\Lambda(n)\chi(n)e(n\theta)\)
on each arc, with the zero-free region evaluated at the arc's own modulus and
height rather than at a worst case over all \(r\le R\). Two consequences.
First, every zero other than the ones the target already subtracts contributes
\(N^{1-c/\log(rT)}\) with \(rT\le R^4\), which is \(N\exp(-(c/(4\sigma))\sqrt\ell)\):
far below the balance once \(\sigma\) is small. Second, the one thing that does
not shrink is a possible real zero \(\tilde\beta\) of a real character of
conductor \(\tilde q\le R\) that Page's theorem allows but the target does not
subtract, because \(\tilde\beta\le1-c_0/\sqrt\ell\): it contributes
\(N^{\tilde\beta}\le N\exp(-c_0\sqrt\ell)\), with no loss. **The binding term
of the complete budget is therefore the target's own threshold \(c_0\)**, and
not the progression constant \(\gamma\) of a black-box theorem. Section 5
makes this two-sided: if such a zero exists at \(1-\kappa/\sqrt\ell\) with
\(c_0<\kappa\) (in a window), then \(E_{\rm corr}^{(Z)}\gg N^3e^{-2\kappa\sqrt\ell}/\tilde q^2\),
so an unconditional exponent above \(2c_0\) would exclude real zeros
\(1-\tilde\beta\le c'/\log\tilde q\) for every real character, which is a
Siegel-zero statement nobody has. The exponent of this target is pinned to
\([c_0,\,2c_0]\) by what is known.

Grade: derived, one route, finite checks in section 7, not yet independently
read. No power saving, nothing about the zeros of \(\zeta\) beyond the
classical inputs named, and the lower bound of section 5 is conditional on a
zero that may not exist.

## 1. Inputs

The model, arcs and target are those of `ARC_SPLIT_BUDGET.md` sections 1 and
2: \(R=\lfloor e^{\sigma\sqrt\ell}\rfloor\), arcs \(I_{r,a}\) of radius
\(R/(rN)\), \(\mathfrak M\), \(\mathfrak m\). Write, for \(\chi\bmod r\),
\[
 F_\chi(\theta)=\sum_{n\le N}\Lambda(n)\chi(n)e(n\theta),\qquad
 H_\chi(\theta)=\sum_{n\le N}a(n)\chi(n)e(n\theta),\qquad
 I_\rho(\theta)=\int_1^Nt^{\rho-1}e(t\theta)\,dt .
\]

(EF) *The explicit formula* (Davenport, Chapters 17 and 19; for imprimitive
\(\chi\) the difference from the primitive inducing character is
\(O(\omega(r)\log y)\)): for \(\chi\bmod r\), \(2\le T\le y\), \(r\le y\),
\[
 \psi(y,\chi)=\delta_\chi y-\sum_{|\gamma_\rho|\le T}\frac{y^\rho}\rho
 +O\Big(\frac yT\log^2(ry)+y^{1/4}\log y\Big),
\]
the sum over zeros \(\rho=\beta+i\gamma\) of \(L(s,\chi)\) with \(0<\beta<1\).

(ZF) *The zero-free region*: there is an absolute \(c>0\) such that for every
\(r\ge1\) and \(\chi\bmod r\), \(L(s,\chi)\ne0\) in
\(\sigma\ge1-c/\log(r(|t|+2))\), except possibly for one real simple zero when
\(\chi\) is real (Davenport, Chapter 14).

(Pg\('\)) *Page's theorem*, in the form quoted from Drappeau and Fiorilli in
`ENDPOINT_SHARP.md` section 4: there is an absolute \(b>0\) such that for
\(Q,T\ge2\) the product \(\prod_{q\le Q}\prod_{\chi\bmod q}L(s,\chi)\) has at
most one zero in \(\mathrm{Re}\,s>1-b/\log(QT)\), \(|\mathrm{Im}\,s|\le T\), and it
is real and belongs to a unique primitive real \(\tilde\chi\) of conductor
\(\tilde q\).

(GS) *Gauss sums*: for \((a,r)=1\) and any \(\chi\bmod r\) induced by the
primitive \(\chi^*\bmod r^*\), \(\sum_{b\bmod r}\chi(b)e(ab/r)=\overline\chi(a)\tau(\chi)\)
with \(\tau(\chi)=\mu(r/r^*)\chi^*(r/r^*)\tau(\chi^*)\) (Montgomery and Vaughan,
Theorem 9.10), so \(|\sum_b\chi(b)e(ab/r)|\le\sqrt{r^*}\le\sqrt r\).

(Md) *The model in progressions*: the four cases of `ENDPOINT_SHARP.md`
section 4 with the sieve level \(D_1\), which give, for every \(r\le R\), every
\(b\) with \((b,r)=1\) and every prefix \(y\le N\), with \(\chi_e,q_e,\beta_e\)
the TT-exceptional data when they exist,
\[
 \sum_{\substack{n\le y\\n\equiv b\ (r)}}\nu(n)=\frac y{\phi(r)}+O(E_{\rm md}),\qquad
 \sum_{\substack{n\le y\\n\equiv b\ (r)}}\nu(n)\chi_e(n)n^{\beta_e-1}
 =1_{q_e\mid r}\,\chi_e(b)\frac{y^{\beta_e}-1}{\beta_e\phi(r)}+O(E_{\rm md}),
\]
\(E_{\rm md}\ll N(\log\ell)e^{9-\sqrt\ell/2}+\ell^{1/2}e^{\sqrt\ell}N^{1/2}\ll Ne^{-\sqrt\ell/3}\).
For \((b,r)>1\) both sums vanish, since every prime factor of \(r\le R<Z\)
divides \(P\).

(In2) *Input (2)*: \(\|R_{\rm mod}\|_2^2\ll N^3e^{-2c_m\sqrt\ell}+N^2\),
\(c_m=1/4-o(1)\), `ARC_SPLIT_BUDGET.md` (7).

## 2. The exponential-sum explicit formula on an arc

Fix \(r\le R\), \((a,r)=1\), \(|\theta|\le R/(rN)\), and \(T\) with \(2\le T\le N\).
Integrating \(e(t\theta)\) against \(d\psi(t,\chi)\) and inserting (EF), whose
remainder is at most \((N/T)\log^2(rN)+N^{1/4}\log N\) uniformly for \(t\le N\),
partial summation against \(e(t\theta)\) (total variation \(2\pi|\theta|N\))
gives
\[
 F_\chi(\theta)=\delta_\chi K_N(\theta)-\sum_{|\gamma_\rho|\le T}I_\rho(\theta)
 +O\Big((1+N|\theta|)\Big[\frac NT\ell^2+N^{1/4}\ell\Big]\Big)+O(\ell^2),
\tag{1}
\]
the last term being the prime powers of primes dividing \(r\) that
\(\delta_\chi K_N\) counts and \(F_{\chi_0}\) does not.

**The integrals.** Write \(\phi(t)=\gamma\log t+2\pi\theta t\), so
\(I_\rho(\theta)=\int_1^Nt^{\beta-1}e^{i\phi(t)}dt\), \(\phi'(t)=\gamma/t+2\pi\theta\),
\(\phi''(t)=-\gamma/t^2\). Three bounds, each on dyadic blocks \([U,2U]\)
where \(t^{\beta-1}\le U^{\beta-1}\), summed over \(U\le N\):

- trivially \(|I_\rho|\le N^\beta/\beta\le2N^\beta\);
- if \(|\gamma|\ge4\pi N|\theta|\) and \(|\gamma|\ge1\): \(|\phi'(t)|\ge|\gamma|/(2t)\ge|\gamma|/(4U)\)
  on the block and \(\phi'\) is monotone, so the first-derivative test gives
  \(\ll U^{\beta-1}\cdot U/|\gamma|\), and summing, \(|I_\rho|\ll N^\beta/|\gamma|\);
- if \(1\le|\gamma|<4\pi N|\theta|\): \(|\phi''|\ge|\gamma|/(4U^2)\) on the block,
  so the second-derivative test gives \(\ll U^{\beta-1}\cdot U/\sqrt{|\gamma|}\),
  and summing, \(|I_\rho|\ll N^\beta/\sqrt{|\gamma|}\).

**The zero sum.** Let \(\mathcal Z_\chi(T)\) be the zeros of \(L(s,\chi)\) with
\(|\gamma|\le T\) other than a possible exceptional real zero, put
\(H_0=4\pi N|\theta|\le4\pi R/r\), and let \(\beta_\chi(U)\) be the largest
\(\beta\) among them with \(|\gamma|\le U\). By (ZF),
\(N^{\beta_\chi(U)}\le N\exp(-c\,\ell/\log(r(U+2)))\). With the zero count
\(N(U,\chi)\ll U\log(rU)+\log r\) (Davenport, Chapter 16),
\[
 \sum_{\rho\in\mathcal Z_\chi(T)}|I_\rho(\theta)|
 \ll N^{\beta_\chi(H_0)}\Big[\log r+\sqrt{H_0}\log(rH_0)\Big]
 +\sum_{\substack{U=2^jH_0\\ U\le T}}N^{\beta_\chi(2U)}\log(rU).
\tag{2}
\]
The first bracket is the zeros with \(|\gamma|<1\) (at most \(O(\log r)\) of them,
trivial bound) and the stationary range \(1\le|\gamma|<H_0\) (second-derivative
bound, \(\sum_{|\gamma|\le H_0}|\gamma|^{-1/2}\ll\sqrt{H_0}\log(rH_0)\)); the
sum is the far range, where each dyadic block costs its zero count times
\(N^\beta/U\). Since \(rH_0\le4\pi R\), the first term is
\(\ll N\exp(-(c/\sigma)\sqrt\ell\,(1+o(1)))\sqrt{R/r}\,\ell\). In the far range
\(\beta_\chi(2U)\) increases with \(U\), so the sum is at most
\(\ell\cdot N\exp(-c\,\ell/\log(3rT))\log(rT)\).

**Choice of \(T\).** Take \(T=R^3\). Then \(rT\le R^4\), so the far range is
\(\ll N\ell^2\exp(-(c/(4\sigma))\sqrt\ell\,(1+o(1)))\); and the remainder in (1)
is \(\ll(1+R/r)(N/R^3)\ell^2\ll N\ell^2R^{-2}\), while \(RN^{1/4}\ell\) is
negligible. Altogether, for every \(\chi\bmod r\), with the exceptional real
zero \(\beta_\chi\) (if any) kept aside,
\[
 F_\chi(\theta)=\delta_\chi K_N(\theta)-1_{\beta_\chi}I_{\beta_\chi}(\theta)+O(N\,\Upsilon(r)),\qquad
 \Upsilon(r):=\ell^2\Big[e^{-(c/\sigma)\sqrt\ell(1+o(1))}\sqrt{R/r}+e^{-(c/(4\sigma))\sqrt\ell(1+o(1))}+R^{-2}\Big].
\tag{3}
\]

## 3. The major-arc lemma

For \(\alpha=a/r+\theta\in I_{r,a}\), splitting into residue classes and
expanding the coprime ones in characters,
\[
 F(\alpha)=\sum_{(b,r)>1}e(ab/r)F_b(\theta)+\frac1{\phi(r)}\sum_{\chi\bmod r}
 \Big(\sum_{(b,r)=1}\overline\chi(b)e(ab/r)\Big)F_\chi(\theta)
 =O(\ell^2)+\frac1{\phi(r)}\sum_\chi\chi(a)\tau(\overline\chi)F_\chi(\theta),
\]
by (GS); the first sum is the prime powers of primes dividing \(r\). The same
expansion of \(H\) uses (Md) with partial summation, which costs
\((1+2\pi N|\theta|)\le1+2\pi R/r\) per class and \(r\) classes:
\[
 H(\alpha)=\frac1{\phi(r)}\sum_\chi\chi(a)\tau(\overline\chi)H_\chi(\theta),\qquad
 H_\chi(\theta)=\delta_\chi K_N(\theta)-1_{\rm exc}1_{q_e\mid r}1_{\chi=\chi_{e,r}}I_{\beta_e}(\theta)+O\big(rE_{\rm md}(1+R/r)\big),
\]
where \(\chi_{e,r}\) is the character mod \(r\) induced by \(\chi_e\), and the
identification of the twisted main term uses \(\chi_e(n)=\chi_e(b)\) on the
class \(b\) when \(q_e\mid r\), and its vanishing when \(q_e\nmid r\), exactly
as in `ENDPOINT_SHARP.md` section 4. (For \(\chi_e^2=\chi_0\) on \((n,r)=1\) the
twisted sum with \(\chi=\chi_{e,r}\) is the untwisted model sum with the weight
\(n^{\beta_e-1}\), whose main term is \(\int_1^Nt^{\beta_e-1}e(t\theta)dt=I_{\beta_e}(\theta)\)
by (Md) and partial summation.) Subtracting, with \(|\tau(\overline\chi)|\le\sqrt r\):
\[
 |W(\alpha)|\le\sqrt r\,\max_{\chi\bmod r}\big|F_\chi(\theta)-H_\chi(\theta)\big|+O(\ell^2)
 \le\sqrt r\,\max_\chi\big|F_\chi-\delta_\chi K_N+1_{\rm exc}1_{q_e\mid r}1_{\chi=\chi_{e,r}}I_{\beta_e}\big|
 +8R\,E_{\rm md}+O(\ell^2).
\tag{4}
\]

**Matching the exceptional zeros.** Apply (Pg\('\)) with \(Q=R\), \(T=R^3\): at
most one zero \(\tilde\beta\) of \(\prod_{r\le R}\prod_\chi L(s,\chi)\) lies in
\(\mathrm{Re}\,s>1-b/\log(R^4)=1-b/(4\sigma\sqrt\ell)\), \(|\mathrm{Im}\,s|\le R^3\),
and it is a real zero of a unique primitive real \(\tilde\chi\) of conductor
\(\tilde q\le R\). Three cases for the exceptional real zero \(\beta_\chi\) of a
real \(\chi\bmod r\) in (3), and for the model's \(\beta_e\):

- If \(\chi\) is induced by \(\tilde\chi\) and \(\tilde\chi=\chi_e\) (the TT-exceptional
  character; this happens exactly when \(\beta_e>1-b/(4\sigma\sqrt\ell)\), which
  \(\beta_e>1-c_0/\sqrt\ell\) implies under (H), \(c_0\le b/(4c_0)\)): then
  \(\beta_\chi=\beta_e\), \(1_{q_e\mid r}=1\), and the two terms in (4) cancel.
- If \(\chi\) is induced by \(\tilde\chi\ne\chi_e\): \(\tilde\chi\) is not
  TT-exceptional at \(Z\) (it has conductor \(\tilde q\le R<Z\), so the failing
  condition is the threshold), hence \(\tilde\beta\le1-c_0/\sqrt\ell\) and
  \(|I_{\tilde\beta}(\theta)|\le2N^{\tilde\beta}\le2Ne^{-c_0\sqrt\ell}\). This is
  the term (4) cannot make smaller. It is present only for \(r\) with
  \(\tilde q\mid r\).
- Every other zero of every \(L(s,\chi)\), \(\chi\bmod r\le R\), with
  \(|\gamma|\le T\) lies outside the Page region, hence has
  \(\beta\le1-b/(4\sigma\sqrt\ell)\); it also lies outside (ZF)'s region. It is
  in \(\mathcal Z_\chi(T)\) and is covered by (3). (A real zero of a real
  character that is not the Page-exceptional one is not exceptional for (ZF)
  either, since by (ZF) each real \(L(s,\chi)\) has at most one real zero in
  its region and that one would be the Page zero.)

So, with \(\tilde\chi\) the Page-exceptional character at \((R,R^3)\) when it
exists and differs from \(\chi_e\),
\[
 \boxed{\ \sup_{\alpha\in I_{r,a}}|W(\alpha)|\ \ll\ \sqrt r\,N\,\Upsilon(r)
 +1_{\tilde q\mid r}\sqrt r\,Ne^{-c_0\sqrt\ell}+RNe^{-\sqrt\ell/3}.\ }
\tag{5}
\]
Compared with `ARC_SPLIT_BUDGET.md` (5), which is \(\ll RNe^{-\gamma\sqrt\ell}\)
with \(\gamma<c_0/2\): the residue-class factor \(r\) has become \(\sqrt r\)
by (GS); the partial-summation factor \(1+2\pi N|\theta|\) is gone on the
\(\Lambda\) side, because the explicit formula is applied to the exponential
sum itself and the height enters only through the zero-free region; and the
loss of the factor \(1/2\) in \(c_0/2\), which came from the small-\(y\)
reduction \(\log y\ge\ell/2\) in the proof of (1\('\)), does not occur,
because there is no prefix \(y<N\) anywhere in (4).

## 4. The budget

Squaring (5) and using \(\sqrt r\le\sqrt R\), \(\sqrt{R/r}\cdot\sqrt r=\sqrt R\):
\[
 \sup_{\mathfrak M}|W|^2\ll N^2\ell^4\Big[R^2e^{-(2c/\sigma)\sqrt\ell(1+o(1))}+Re^{-(c/(2\sigma))\sqrt\ell(1+o(1))}+R^{-3}
 +Re^{-2c_0\sqrt\ell}\Big]+R^2N^2e^{-2\sqrt\ell/3}.
\]
By `ARC_SPLIT_BUDGET.md` (3) and (6), \(\int_{\mathfrak M}(|F|^2-|H|^2)^2\le\sup_{\mathfrak M}|W|^2\int_{\mathbb T}(|F|+|H|)^2\ll\sup_{\mathfrak M}|W|^2\cdot N\ell\),
and its (8), (11) carry the rest unchanged. Hence
\[
 E_{\rm corr}^{(Z)}(N)\ll N^3\ell^{O(1)}\Big[Re^{-2c_0\sqrt\ell}+R^2e^{-(2c/\sigma)\sqrt\ell(1+o(1))}+Re^{-(c/(2\sigma))\sqrt\ell(1+o(1))}+R^{-3}+R^2e^{-2\sqrt\ell/3}+R^{-1}\Big]
 +N^3e^{-2c_m\sqrt\ell}+N^{13/5}\ell^6+N^2\ell^2 .
\tag{6}
\]
With \(R=\lfloor e^{\sigma\sqrt\ell}\rfloor\) the exponents are
\(2c_0-\sigma,\ 2c/\sigma-2\sigma,\ c/(2\sigma)-\sigma,\ 3\sigma,\ 2/3-2\sigma,\ \sigma\).
The first and last balance at \(\sigma=c_0\), where the others are at least
\(\sigma\) provided \(c_0^2\le2c/3\), \(c_0^2\le c/4\), \(c_0\le2/9\); together
with \(2c_m=1/2-o(1)>c_0\) and the matching conditions \(c_0^2\le b/4\),
\(c_0\le c_P\) of section 3, this is (H). Therefore
\[
 E_{\rm corr}^{(Z)}(N)\ll N^3\ell^{O(1)}\exp(-c_0\sqrt\ell),
\]
which is (S\(''\)).

**Against (S\('\)).** Same architecture, same minor arcs, same (In2). The
major-arc term changed from \(N^3\ell R^2e^{-2\gamma\sqrt\ell}\) to
\(N^3\ell^{O(1)}Re^{-2c_0\sqrt\ell}\) plus terms that decay faster than any
fixed multiple of \(\sqrt\ell\) as \(\sigma\to0\). The balance moved from
\(\sigma=2\gamma/3\) to \(\sigma=c_0\), and since \(\gamma<c_0/2\), the
exponent constant improved by a factor of more than \(3\).

**A repair of (1\('\)) recorded in passing.** The factor \(1/2\) in
\(\gamma<c_0/2\) came from assuming \(\log y\ge\ell/2\) after discarding
\(y\le Ne^{-\gamma\sqrt\ell}\). The discarded range in fact gives
\(\log y\ge\ell-\gamma\sqrt\ell\), so \(y^{\tilde\beta-1}\le e^{-c_0(\sqrt\ell-\gamma)}\)
and (1\('\)) holds with any \(\gamma<\min(c_0,\delta/\sqrt2,1/2)\); the
arc-split budget then gives \(2c_0/3\). That is a local improvement of the
checkpoint's constant, not used here, recorded so the comparison is fair:
against the repaired checkpoint the present gain is a factor \(3/2\), and
the change of binding term is the same.

## 5. The ceiling: a conditional lower bound

**Proposition (conditional).** Let \(\tilde\chi\) be a primitive real
character of odd conductor \(\tilde q\le e^{\varepsilon\sqrt\ell}\) with
\(\tilde\chi(-1)=1\), and suppose \(L(s,\tilde\chi)\) has a real zero
\(\tilde\beta=1-\kappa/\sqrt\ell\) with
\[
 c_0<\kappa<\min(\sqrt c,\sqrt b)-3\varepsilon,\qquad\kappa+3\varepsilon<1/3 .
\]
Then \(\tilde\chi\) is not TT-exceptional at \(Z\), and for large \(N\)
\[
 E_{\rm corr}^{(Z)}(N)\ \ge\ c_1\,\frac{N^3e^{-2\kappa\sqrt\ell}}{\tilde q^{\,2}}\,(1+o(1)),
\tag{7}
\]
with an absolute \(c_1>0\).

*Proof.* Take one arc: by `ARC_SPLIT_BUDGET.md` (1), (3),
\(E_{\rm corr}^{(Z)}\ge\tfrac12\int_J|G_{\rm corr}|^2-O(N^2)\) for any
\(J\subset\mathbb T\), and \(\int_J|G_{\rm corr}|^2\ge\tfrac12\int_J(|F|^2-|H|^2)^2-2\|R_{\rm mod}\|^2-2\kappa_0^2|J|\).
Let \(J\) be the union over \((a,\tilde q)=1\) of \(J_a=\{a/\tilde q+\theta:\ |\theta|\le1/(8N)\}\).
On \(J_a\), run sections 2 and 3 with \(r=\tilde q\), \(\sigma\) replaced by
the actual height: \(H_0\le\pi/2\), so there is no stationary range; take
\(T=\tilde q^{2}e^{\kappa\sqrt\ell}\ell^4\), so the remainder in (1) is
\(\ll N\ell^2/T\ll Ne^{-\kappa\sqrt\ell}\tilde q^{-2}\ell^{-2}\) and the far range is
\(\ll N\ell^2\exp(-c\ell/\log(3\tilde qT))\ll N\ell^2\exp(-(c/(\kappa+3\varepsilon))\sqrt\ell)\).
Page at \((Q,T)=(\tilde q,T)\): \(\tilde\beta>1-b/\log(\tilde qT)\) since
\(\kappa<b/(\kappa+3\varepsilon)\), so \(\tilde\beta\) is the Page zero and every
other zero of every \(\chi\bmod\tilde q\) is covered by (3). Hence, by (4) with
\(r=\tilde q\), and (GS) with \(\tau(\tilde\chi)=\sqrt{\tilde q}\) for even
primitive real \(\tilde\chi\),
\[
 W(a/\tilde q+\theta)=-\frac{\tilde\chi(a)\sqrt{\tilde q}}{\phi(\tilde q)}I_{\tilde\beta}(\theta)+O\big(\sqrt{\tilde q}\,N\ell^2e^{-(c/(\kappa+3\varepsilon))\sqrt\ell}+Ne^{-\kappa\sqrt\ell}\tilde q^{-3/2}\ell^{-2}+\tilde qNe^{-\sqrt\ell/3}\big),
\]
and the error is \(o(N^{\tilde\beta}/\sqrt{\tilde q})\) under the stated
window: the first term because \(c/(\kappa+3\varepsilon)>\kappa+\varepsilon\),
the second by the factor \(\ell^{-2}\) (this is why \(T\) carries \(\ell^4\);
with \(\ell^2\) the ratio would be \(\phi(\tilde q)/\tilde q^2\), not small for
\(\tilde q=3\)), the last because \(\kappa+3\varepsilon<1/3\). If the
TT-exceptional \(\chi_e\) exists and \(q_e\mid\tilde q\), both \(F\) and \(H\)
carry the \(\beta_e\) term with the same coefficient and it cancels inside
\(W\) by the first case of section 3; it changes \(|H|\) by a relative
\(O(\sqrt{\tilde q}N^{\beta_e-1})=o(1)\). So
\(H(a/\tilde q+\theta)=(\mu(\tilde q)/\phi(\tilde q))K_N(\theta)(1+o(1))+O(\tilde qNe^{-\sqrt\ell/3})\).
For \(|\theta|\le1/(8N)\): \(|K_N(\theta)|\ge N/2\),
\(|I_{\tilde\beta}(\theta)|\ge N^{\tilde\beta}/4\), and the arguments of
\(K_N(\theta)\) and \(I_{\tilde\beta}(\theta)\) both lie within \(\pi/8\) of
\(\pi(N+1)\theta\), so \(\mathrm{Re}(\overline{K_N}I_{\tilde\beta})\ge\cos(\pi/4)|K_N||I_{\tilde\beta}|\).
Since \(\tilde q\) is odd and squarefree, \(\mu(\tilde q)=\pm1\), and
\[
 |F|^2-|H|^2=2\operatorname{Re}(\overline HW)+|W|^2
 =-\frac{2\mu(\tilde q)\tilde\chi(a)\sqrt{\tilde q}}{\phi(\tilde q)^2}\operatorname{Re}\big(\overline{K_N}I_{\tilde\beta}\big)(1+o(1)),
\]
of modulus \(\ge c_2N^{1+\tilde\beta}\sqrt{\tilde q}/\phi(\tilde q)^2\) on
\(J_a\). Integrating over \(|\theta|\le1/(8N)\) and summing over the
\(\phi(\tilde q)\) values of \(a\):
\(\int_J(|F|^2-|H|^2)^2\ge c_3N^{2\tilde\beta+1}\tilde q/\phi(\tilde q)^3\ge c_3N^{2\tilde\beta+1}/\tilde q^2\).
The subtracted terms are \(\ll N^3e^{-2c_m\sqrt\ell}+N^2\ell^2\), and
\(N^{2\tilde\beta+1}/\tilde q^2=N^3e^{-2\kappa\sqrt\ell}\tilde q^{-2}\gg N^3e^{-(1/2)\sqrt\ell}\)
since \(2\kappa+2\varepsilon<1/2\). This gives (7). \(\square\)

The order \(N^{2\tilde\beta+1}/\tilde q^2\) is the first term of
`SIEGEL_UNIFORMITY.md` (23) for the correction that the target *would* carry
if \(\tilde\chi\) were counted as exceptional; (7) says the target, which does
not count it, carries it as error instead. For odd \(\tilde\chi\) the cross
term's real part is smaller by a factor \(\asymp(1-\tilde\beta)N|\theta|\) and
the same argument gives (7) with an extra \(\ell^{-1}\), or the \(|W|^4\) term
gives \(N^{4\tilde\beta-1}/\tilde q^2\); neither is needed for the corollary.

**Corollary (what an exponent above \(2c_0\) would establish).** Suppose
\(E_{\rm corr}^{(Z)}(N)\ll N^3\exp(-\kappa'\sqrt\ell)\) unconditionally for
some fixed \(\kappa'>2c_0\), and fix \(\varepsilon\) small. Let \(\tilde\chi\)
be as in the Proposition with a real zero \(\tilde\beta<1\). Choose \(N\) with
\(\sqrt{\log N}=(c_0+\kappa'/2)/(2(1-\tilde\beta))\), so that
\(\kappa=(1-\tilde\beta)\sqrt\ell=(c_0+\kappa'/2)/2\in(c_0,\kappa'/2)\).
If \(\tilde q\le e^{\varepsilon\sqrt\ell}\), i.e. \(1-\tilde\beta\le\varepsilon(c_0+\kappa'/2)/(2\log\tilde q)\),
then (7) and the assumed bound contradict each other once
\(\tilde q^2<e^{(\kappa'-2\kappa)\sqrt\ell}\), which the same inequality
supplies for small \(\varepsilon\). Hence: *no even primitive real character
of odd conductor \(\tilde q\) has a real zero \(\tilde\beta\) with
\(1-\tilde\beta\le c'/\log\tilde q\)*, \(c'=c'(\kappa',c_0,\varepsilon)>0\),
for all \(\tilde q\) beyond an effective bound. That is an effective
zero-free interval \((1-c'/\log\tilde q,1)\) for real zeros of real
characters, i.e. the non-existence of Siegel zeros in the classical form.
Landau and Page give at most one such zero per range; excluding it is open.

**Consequence for this hunt.** With the target fixed as it is, the exponent
constant in \(N^3\exp(-c''\sqrt\ell)\) lies in \([c_0,2c_0]\): (S\(''\))
gives the lower end unconditionally, and passing the upper end needs the
Siegel-zero statement above. The remaining gap, a factor \(2\), is the
minor-arc term: (6) balances \(Re^{-2c_0\sqrt\ell}\) against \(R^{-1}\), and
the true size of the minor-arc fourth moment is \(N^3/R^2\) (measured in
`ARC_SPLIT_BUDGET.md` section 8 between \(N^3/R^2\) and \(N^3/R\)). With
\(R^{-2}\) in place of \(R^{-1}\) the balance would move to \(\sigma=2c_0/3\)
and the exponent to \(4c_0/3\); with the true major-arc size (the term
\(Re^{-2c_0\sqrt\ell}\) is itself an upper bound for what (7) shows is
\(\asymp e^{-2\kappa\sqrt\ell}/\tilde q^2\) on the arcs that carry it) and
\(R^{-2}\), to \(2c_0\). Both steps are the rank-3 quartic problem
(`RANK3_QUARTIC_LITERATURE.md`, `w-bound-raw-arc-quartic-moment`): a bound
\(\int_{\mathfrak m}|F|^4\ll N^3\ell^{O(1)}R^{-2+\epsilon}\) for
\(R=e^{\sigma\sqrt\ell}\). Nothing in this hunt or its literature record
gives it.

## 6. Routes killed on the way, with the witness

- **The shape \(\sqrt\ell\).** Every unconditional input here decays like
  \(\exp(-c\,\ell/\log(rT))\) on an arc of modulus \(r\) and height \(T\), and
  the minor arcs decay polynomially in \(R\). Balancing a power of \(R\)
  against \(\exp(-c\ell/\log R)\) puts \(\log R\asymp\sqrt\ell\) whatever the
  constants. The one input with a better rate, the Vinogradov-Korobov region
  for \(\zeta\) (rate \(\ell^{3/5}\), `LOCALIZED_MIXED_ENERGY.md` (19) for the
  \(r=1\) arc), has no analogue in the conductor aspect: for \(L(s,\chi)\) the
  \(\log r\) term of the region is not improved, and \(\log r\) dominates
  \((\log T)^{2/3}\) for every \(r>e^{(\log T)^{2/3}}\), which at
  \(T\le R^3\) is every \(r\) beyond \(e^{(3\sigma)^{2/3}\ell^{1/3}}\). So (1) of
  the assignment is out of reach of the inputs the hunt has.
- **The minor arcs through the explicit formula.** On the Farey arcs that
  cover \(\mathfrak m\), of radius \(1/(q\sqrt N)\), the heights reach
  \(N|\theta|\asymp\sqrt N/q\), so \(\log(qT)\asymp\ell/2\) and (ZF) gives
  \(N^\beta\le Ne^{-2c}\): no decay. The inner parts \(|\theta|\le R'/(qN)\)
  of those arcs are exactly the major arcs at cutoff \(R'\), so this route is
  the present one with a different name, and the outer parts are Vaughan's.
- **Averaging over moduli instead of the pointwise zero-free region**
  (Bombieri-Vinogradov in Drappeau and Fiorilli's form, `ENDPOINT_SHARP.md`
  section 4): its error \(xe^{-\delta\sqrt{\log x}}\) has the \(\sqrt\ell\)
  rate built in, from the \(x/Q_1\) term at the lower cutoff of its
  large-sieve range. Summing (5) over \(r\) with it instead of the pointwise
  bound would trade \(2\gamma\) for \(\gamma+\delta\) in the old budget, a
  constant, and is superseded by section 3.
- **Koukoulopoulos's short-interval theorem** (`RANK3_Z_COMPONENT.md` input)
  as a variance bound on the major arcs through Gallagher's lemma: its
  \(E(y,h;q)\) is a first moment with a maximum over residues, so it yields
  \((\log x)^{-A}\) and not a power; recorded in the Ostoyae log of the
  previous round and not repeated.
- **The cross terms of (22)**: `ARC_SPLIT_BUDGET.md` section 7.

## 7. Finite checks

`major_arc_explicit_probe.py`, results in `results_major_arc_explicit_probe.json`.
Zeros of \(\zeta\) from `mpmath.zetazero`. Nothing here tests an asymptotic
statement, (ZF), or (Pg\('\)); no exceptional zero is reachable, so section 5
is untested.

**(1) The integral bounds of section 2.** For the first \(60\) zeros of
\(\zeta\) (\(\gamma\le163.0\)), \(N\in\{10^4,10^6\}\) and \(N\theta\in\{0,1,10,100\}\),
\(480\) integrals \(I_\rho(\theta)\) by composite Gauss-Legendre with panels
at a quarter oscillation. In the far regime \(|\gamma|\ge4\pi N|\theta|\) the
largest value of \(|I_\rho|/(N^\beta/|\gamma|)\) is \(1.010\); in the
stationary regime the largest value of \(|I_\rho|/(N^\beta/\sqrt{|\gamma|})\)
is \(0.064\). Both bounds hold with constants at most \(1.01\) on this
sample; the second has room, as expected of a worst-case test.

**(2) The exponential-sum explicit formula (1).** At \(N=2000\), with the
\(202\) zeros of \(\zeta\) with \(|\gamma|\le400\), the defect
\(|F(\theta)-K_N(\theta)+\sum_\rho I_\rho(\theta)|\) is \(1.76,\ 4.48,\ 1.76,\ 1.77\)
at \(N\theta=0,\ 0.5,\ 2,\ 5\), against \(|F(\theta)|=1994,\ 1273,\ 14.7,\ 14.8\):
between \(0.001\) and \(0.010\) of the displayed remainder scale
\((N/T)\log^2N\,(1+N|\theta|)\). At \(N\theta=2\) and \(5\) the main term
\(K_N\) is small and the zero sum alone reproduces \(F\) to within \(1.8\).
This checks the sign and normalisation of (1); it says nothing about the
zero-free region.

**(3) The Gauss-sum expansion of section 3.** With the toy model
\(\nu=b1_{(n,30)=1}\) at \(N=3000\), modulus \(r=7\) and all six characters
mod \(7\), the exact identity
\(\sum_{(a,7)=1}|W(a/7+\theta)|^2+|W(\theta)|^2=\frac76\sum_\chi|V_\chi(\theta)|^2+7|W_0(\theta)|^2\)
(with \(W_0\) the class \(0\bmod7\)) holds to a relative \(4\times10^{-13}\)
at \(\theta=3/(7N)\). In the toy the class \(0\) is not small
(\(7|W_0|^2=6.6\times10^5\) against \(1.2\times10^5\) for the character side),
because \(Z=7\) does not exceed the modulus; in the document's setting
\(r<Z\), the class is empty on the model side and carries only prime powers
of primes dividing \(r\) on the \(\Lambda\) side.

## 8. Scope

One mechanism, the explicit formula on the major arcs with the zero-free
region at the arc's own modulus and height, attempted to a checked budget.
It improves the exponent constant of the same subpolynomial bound and, more
usefully, identifies the binding term of the complete budget as the target's
own exceptional threshold \(c_0\), with a conditional lower bound that puts
the reachable exponent in \([c_0,2c_0]\) short of a Siegel-zero theorem. No
power saving; no change to the \(\sqrt\ell\) shape, which section 6 argues is
inherent to the inputs; nothing about the zeros of \(\zeta\); the lower bound
is conditional on a zero that may not exist and is stated for even
characters of odd conductor. Awaits an independent read of sections 2 to 5.
