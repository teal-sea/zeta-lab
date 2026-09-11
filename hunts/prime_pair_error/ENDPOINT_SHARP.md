# The sharp endpoint \(\kappa=1/2\): \(E_{\rm corr}^{(Z)}(N)\ll N^3\exp(-c\sqrt{\log N})\)

2026-09-11, corrected the same day (sections 2 and 4; both corrections are
recorded in place below rather than silently applied). Base: the chain
`SIEGEL_UNIFORMITY.md` -> `EXCEPTIONAL_ENERGY.md` -> `ENDPOINT_BOUND.md`
(reviewed in `ENDPOINT_BOUND_REVIEW.md`), and `ENDPOINT_HALF.md`. None of
those files is changed by this document; `ENDPOINT_HALF.md` carries a
pointer to section 2 below, which refutes one of its conclusions.

**Result, stated first.** For some fixed \(c>0\) and all sufficiently large
\(N\), unconditionally,
\[
 \boxed{\ E_{\rm corr}^{(Z)}(N)\ \ll\ N^3\exp\!\big(-c\sqrt{\log N}\big),
 \qquad Z=\exp\big(\sqrt{\log N}\big).\ }
\tag{S}
\]
This is the endpoint \(\kappa=1/2\) of `ENDPOINT_HALF.md`'s family (A),
attained rather than approached.

**The superscript is not decoration.** \(E_{\rm corr}^{(Z)}\) is defined
through the exceptional correction \(C_N\), and \(C_N\) depends on the model
parameter \(Z\): which zeros count as exceptional, and therefore what is
subtracted, changes with \(Z\). At the enlarged \(Z=\exp(\sqrt\ell)\) the
conductor range \(q<Z\) is wider than at \(Z=\exp(\ell^{1/10})\) while the
threshold \(\beta>1-c_0/\log Z\) is stricter, so the two corrected
quantities are genuinely different, neither one dominating the other.
(S) is a statement about the \(Z=\exp(\sqrt\ell)\) quantity. It does not
strengthen `ENDPOINT_BOUND.md`'s bound on the \(Z=\exp(\ell^{1/10})\)
quantity; it is a different bound on a different object, reached by the
same architecture. Section 1 fixes the notation and section 6 states what
each carries for the original \(E\).

Two things make the endpoint available, and the first is a correction
rather than a construction:

1. **`ENDPOINT_HALF.md`'s wall at \(\kappa=1/2\) is an artifact of a lossy
   estimate, not a feature of the argument.** Its section 2.3 concludes
   that no choice of the Bonferroni cutoff \(m\) works at \(\kappa=1/2\).
   That conclusion propagates `ENDPOINT_BOUND.md` section 2's own
   *elementary* estimate \(H_Z\le1+\log Z\) for \(H_Z=\sum_{p<Z}1/p\).
   By Mertens' second theorem \(H_Z=\log\log Z+M+O(1/\log Z)\), so at
   \(Z=\exp(\ell^\kappa)\) the truth is \(H_Z\sim\kappa\log\ell\), not
   \(\ell^\kappa\): a double logarithm where the bound supplies a power.
   With the true \(H_Z\) and a retuned \(m\), the existing device reaches
   \(D_0=N^{o(1)}\) at \(\kappa=1/2\) (section 2). Nothing needs replacing.
2. **The progression input is classical at the endpoint.**
   `ENDPOINT_BOUND.md` takes its input (1) from Tao and Teräväinen's
   Proposition 2.2 at \(Z=\exp(\ell^{1/10})\), and `ENDPOINT_HALF.md`'s
   family beyond that leaned on their Remark 2.8, which those authors state
   without proof. At \(\kappa=1/2\) the input is instead the prime number
   theorem in progressions with the exceptional zero retained (Davenport,
   Chapter 20), Page's theorem, and the fundamental lemma of sieve theory
   applied to the model inside a progression (section 4). Remark 2.8 is
   not used.

Everything else in the chain was already verified at \(\kappa=1/2\) by
`ENDPOINT_HALF.md` sections 2.1 and 2.2 and is reused, not redone.

Grade: derived, one route, awaiting an independent check. The classical
inputs are named where used. The finite checks in section 7 test the
Mertens correction, the retuned cutoff, and the character cancellation of
section 4; they test no asymptotic statement. This establishes no fixed
power saving, no exclusion of exceptional zeros, and nothing about the
zeros of \(\zeta\).

## 1. Parameters at the endpoint

Write \(\ell=\log N\) and take, in place of `ENDPOINT_BOUND.md` section 1,
\[
 t=\sqrt\ell,\qquad Z=e^{t},\qquad P=\prod_{p<Z}p,\qquad b=P/\phi(P)=V(Z)^{-1},
 \qquad V(Z)=\prod_{p<Z}(1-1/p),
\]
\(\nu(n)=b\,1_{(n,P)=1}\), \(a(n)=\nu(n)(1-1_{\rm exc}\chi(n)n^{\beta-1})\),
with the exceptional data of TT Definition 2.1 **at this \(Z\)**: \(\chi\)
primitive real of conductor \(q<Z=e^{\sqrt\ell}\), and
\(1-c_0/\log Z=1-c_0/\sqrt\ell<\beta<1\), with \(c_0\) a fixed sufficiently
small absolute constant (constrained once more in section 4). \(F,H,W,r,r_a\)
are as there, \(C_N=C_{q,\beta,Z}(h)\) is `SIEGEL_UNIFORMITY.md` (19) at this
\(Z\), and
\[
 E_{\rm corr}^{(Z)}(N)=2\sum_{h=1}^N\big|r(h)-C_N(h)\big|^2 .
\]
By Mertens' third theorem \(b\sim e^{\gamma_{\rm E}}\log Z=e^{\gamma_{\rm E}}\sqrt\ell\),
so \(b\ll\sqrt\ell\). The major-arc parameter is
\(R=\lfloor\exp(\sigma t)\rfloor\), \(\sigma\) fixed in section 6. The level
of the divisor approximant is \(D_0\), fixed in section 2.

## 2. The divisor approximation at the endpoint

**Correction.** The first version of this section replaced
`ENDPOINT_BOUND.md`'s Bonferroni approximant by the linear \(\beta\)-sieve,
on the ground that the Bonferroni device "needs level \(D_0=Z^m\) with
\(m>eH_Z\sim e\log Z\), so \(\log D_0>e(\log Z)^2=e\ell\) at \(\kappa=1/2\)".
The step \(H_Z\sim\log Z\) is wrong, and it was inherited from
`ENDPOINT_BOUND.md` section 2's own elementary bound \(H_Z\le1+\log Z\),
which `ENDPOINT_HALF.md` section 2.3 then used as if it were the size of
\(H_Z\). Mertens' second theorem gives
\[
 H_Z=\sum_{p<Z}\frac1p=\log\log Z+M+O\Big(\frac1{\log Z}\Big),
 \qquad M=0.26149\ldots,
\tag{M}
\]
so at \(Z=\exp(\ell^\kappa)\), \(H_Z=\kappa\log\ell+M+o(1)\). The
elementary bound overstates it by a factor \(\asymp\ell^\kappa/\log\ell\),
measured at \(3.2\) to \(5.0\) over \(\log Z\in[5,13]\) in section 7. With
(M) the original device reaches the endpoint, and the \(\beta\)-sieve is an
alternative rather than a repair. Both are recorded below.

### 2.1 The retuned Bonferroni cutoff

`ENDPOINT_BOUND.md` section 2 takes
\(B_m(n)=\sum_{d\mid P,\ d\mid n,\ \omega(d)\le m}\mu(d)\), \(m\) even,
\(D_0=Z^m\), and proves its (5),
\(\sum_{n\le N}|B_m(n)-1_{(n,P)=1}|\le NH_Z^{m+1}/(m+1)!\). Nothing in that
derivation depends on the value of \(m\), so the cutoff is free. With
\((m+1)!\ge((m+1)/e)^{m+1}\),
\[
 \sum_{n\le N}\big|B_m(n)-1_{(n,P)=1}\big|\ \le\ N\Big(\frac{eH_Z}{m+1}\Big)^{m+1}
 =N\exp\Big(-(m+1)\log\frac{m+1}{eH_Z}\Big).
\tag{5$'$}
\]
Given a target decay \(\exp(-c\ell^\kappa)\), choose
\[
 m+1=\Big\lceil\frac{2c}{\kappa}\cdot\frac{\ell^\kappa}{\log\ell}\Big\rceil
 \quad(\text{rounded up to an even }m).
\]
Then, by (M), \(\log\frac{m+1}{eH_Z}=\kappa\log\ell-2\log\log\ell+O(1)
=\kappa\log\ell\,(1+o(1))\), so the exponent in (5\('\)) is
\(2c\,\ell^\kappa(1+o(1))\ge c\,\ell^\kappa\) for large \(N\), and
\[
 A(N):=\frac{\log D_0}{\log N}=\frac{m\log Z}{\ell}
 =\frac{2c}{\kappa}\cdot\frac{\ell^{2\kappa-1}}{\log\ell}\,(1+o(1)).
\tag{A}
\]
At \(\kappa=1/2\) this is \(4c/\log\ell\to0\), so \(D_0=N^{o(1)}\), which is
exactly what `ENDPOINT_BOUND.md` section 2 asserts of its own \(D_0\) and
what the budget consumes. The retuning is the whole of the change: the
fixed cutoff \(m=2\lceil\sqrt\ell\rceil\) is not too small at the endpoint,
it is too **large**, and it pins \(A(N)=2\) (section 7 measures \(2.000\)
at every \(N\) tried, matching `ENDPOINT_HALF.md` section 2.4's own table).

Two consequences worth stating separately.

- **`ENDPOINT_HALF.md` section 2.3's claim that no \(m\) works at
  \(\kappa=1/2\) does not survive.** That argument writes \(m=\lambda H_Z\),
  requires \(\lambda>e\), and concludes \(\log D_0=\lambda H_Z\log Z\sim\lambda\ell^{2\kappa}\).
  The last step is (M) again: \(H_Z\log Z=\kappa(\log\ell)\ell^\kappa\), not
  \(\ell^{2\kappa}\). Its numerical section 2.4 is unaffected as
  *measurement*, because it evaluates \(A(N)\) for the **fixed** cutoff,
  which is genuinely pinned at \(2\); what does not follow is the claim
  about every other cutoff.
- **The device caps at \(\kappa=1/2\) and attains it.** By (A),
  \(A(N)\to0\) for \(\kappa<1/2\), \(A(N)\to0\) at \(\kappa=1/2\) (the
  \(\log\ell\) in the denominator is what saves the endpoint), and
  \(A(N)\to\infty\) for \(\kappa>1/2\). So the divisor approximation is
  available up to and including the endpoint and not past it, matching the
  three other inputs of section 6.

Honest numerics, from section 7: \(A(N)<1\) from about \(\log N=400\)
onward, and \(A(N)<1/2\) only from about \(\log N=4.7\times10^4\), i.e.
\(N\) around \(10^{20000}\). The budget needs \(A(N)<1\) with a margin
\(\asymp\ell^{-1/2}\) (section 6), not \(A(N)<1/2\), so the relevant
crossover is the first one. \(A(N)\) decays like \(1/\log\ell\), which is
slow; (S) is an asymptotic statement and this is where its "sufficiently
large \(N\)" lives.

### 2.2 The \(\beta\)-sieve, as an alternative with a fixed level

The chain uses exactly four properties of the approximant, visible by
reading every place `ENDPOINT_BOUND.md` touches \(B_m\) (its (4)-(6), the
prefix bound after (10), the untwisted prefix in 4.2, Cases A and B in 4.3,
and the \(D_0\) terms of (13), (14), (17), (18)):

- (P1) coefficients \(|\lambda_d|\le1\);
- (P2) support \(d\mid P(Z)\), \(d<D_0\le N\);
- (P3) an \(\ell^1\) approximation \(\sum_{n\le y}|b\lambda(n)-\nu(n)|\ll N\exp(-c\sqrt\ell)\)
  uniform over prefixes \(y\le N\), stable under multiplication of the
  summand by \(\chi(n)\), by \(n^{\beta-1}\), or by a unit phase;
- (P4) the level enters only through \(N^2D_0\sqrt Z\) in (17)-(18) and the
  \(D_0\) terms of (13)-(14).

\(B_m\) with the retuned cutoff has all four. So does Rosser's upper-bound
weight \(\lambda^+\) of the linear (\(\beta=2\)) sieve at level \(D_0\),
supported on \(\mathcal D^+=\{d=p_1\cdots p_r:\ p_1>\cdots>p_r,\
p_1\cdots p_{l-1}p_l^{\,3}<D_0\ \text{for every odd }l\le r\}\): (P1) and
(P2) hold by construction, and the fundamental lemma of sieve theory
(Friedlander and Iwaniec, *Opera de Cribro*, Lemma 6.3, at dimension
\(\kappa=1\); the same lemma `SIEGEL_UNIFORMITY.md` section 3 consumes as
TT Lemma 5.1) gives, for \(D_0=Z^s\), \(s\ge10\), and every \(y\le N\),
\[
 \sum_{n\le y}\big|b\Lambda^+(n)-\nu(n)\big|
 =b\sum_{n\le y}\big(\Lambda^+(n)-1_{(n,P)=1}\big)\ll Ne^{9-s}+bD_0 ,
\tag{6$'$}
\]
one-sided because \(\Lambda^+\ge1_{(n,P)=1}\) pointwise. At \(D_0=N^{1/2}\),
\(s=\tfrac12\sqrt\ell\) and (6\('\)) is (P3) with any \(c<1/2\). This fixes
\(A(N)=1/2\) at every \(N\) rather than letting it decay, so it is
asymptotically weaker than 2.1 and numerically stronger at accessible
\(N\). Either choice proves (S); section 6 uses \(A(N)=o(1)\) from 2.1 and
notes where \(A(N)=1/2\) would also serve.

## 3. Sections 3 to 5 of `ENDPOINT_BOUND.md` at the endpoint

With \(t=\sqrt\ell\), \(D_0=N^{o(1)}\) from 2.1, and input (1) replaced by
(1\('\)) of section 4:

- **(8)-(9), major arcs**: \(\int_{\mathfrak M}(|F|^2-|H|^2)^2\ll N^3\ell^2R^7\exp(-2\gamma\sqrt\ell)\).
- **(10)**: unchanged; needs \(D_0\le N\), which holds.
- **(11)**: unchanged, \(\sup_{\mathfrak m}|F|\ll(NR^{-1/2}+N^{4/5})\ell^{5/2}\).
- **untwisted prefix**: \(O(b(N/R+D_0)\ell^2+N\exp(-c\sqrt\ell))\).
- **(13), Case A** (\(q\ge R^{1/3}\)): \(|V_s|\ll\ell^{O(1)}[NR^{-1/6}+D_0\sqrt Z]+N\exp(-c\sqrt\ell)\).
- **(14), Case B** (\(q<R^{1/3}\)): \(|V_s|\ll\ell^{O(1)}[NR^{-1/2}+D_0R^{1/6}]+N\exp(-c\sqrt\ell)\).
- **(15)**: \(\sup_{\mathfrak m}|H|\ll\ell^{O(1)}[NR^{-1/6}+D_0\sqrt Z]+N\exp(-c\sqrt\ell)\).
- **(16)-(17)**: \(\int_{\mathfrak m}(|F|^2-|H|^2)^2\ll\ell^{O(1)}[N^3R^{-1/6}+N^{14/5}+N^2D_0\sqrt Z]+N^3\exp(-c\sqrt\ell)\).

Each line is the corresponding line of `ENDPOINT_BOUND.md` with \(t\) and
\(D_0\) substituted; no argument there is altered.

## 4. Input (1) at the endpoint, from classical sources

**Claim (1\('\)).** There is a fixed \(\gamma>0\) such that, uniformly over
every progression \(B=\{n\le y:\ n\equiv a\ (\mathrm{mod}\ r)\}\) with
\(y\le N\), \(r\le R\), and every residue \(a\),
\[
 \Big|\sum_{n\in B}\big(\Lambda(n)-a(n)\big)\Big|\ll N\exp(-\gamma\sqrt\ell).
\tag{1$'$}
\]

*Inputs.* (D) Davenport, *Multiplicative Number Theory*, Chapter 20: for
\(r\le\exp(C\sqrt{\log y})\) and \((a,r)=1\),
\(\psi(y;r,a)=y/\phi(r)-\chi_1(a)y^{\beta_1}/(\phi(r)\beta_1)+O(y\exp(-c_3\sqrt{\log y}))\),
the middle term present exactly when \(L(s,\chi_1)\) has an exceptional real
zero \(\beta_1\) for a real \(\chi_1\bmod r\) induced by a primitive
\(\chi_1^*\) of conductor \(q_1\mid r\); \(c_3=c_3(C)\). (Pg) Page: among
primitive real characters of conductor at most \(\exp(C\sqrt\ell)\) at most
one has a zero \(\beta>1-c_4/\sqrt\ell\). (FL) the fundamental lemma as in
2.2. (Cmp) Fix \(c_0\le c_4\) in section 1. Then a TT-exceptional zero at
this \(Z\) is the unique Page exceptional zero, and every other real zero of
a real \(L(s,\chi')\) of conductor \(<Z\) has \(\beta'\le1-c_0/\sqrt\ell\),
contributing \(y^{\beta'}/\phi(r)\le N\exp(-c_0\sqrt\ell)\), absorbed.
Small \(y\): if \(y\le N\exp(-\gamma\sqrt\ell)\) both sides of (1\('\)) are
\(O(y\ell)\); so assume \(\log y\ge\ell/2\), which puts \(r\le R\) inside
(D)'s range for \(C\ge2\sigma\) and gives \(\exp(-c_3\sqrt{\log y})\le\exp(-c_3\sqrt\ell/2)\).

*Case \((a,r)>1\).* A prime \(p\mid(a,r)\) divides every \(n\in B\) and
\(p\le r<Z\), so \(a(n)=0\) on \(B\); the \(\Lambda\) side counts prime
powers of primes dividing \(r\), at most \(\omega(r)\ell\ll\ell^2\).

*Case \((a,r)=1\), untwisted part.* Sieve \(B\) by the primes \(p<Z\):
\(g(p)=0\) for \(p\mid r\), \(g(d)=1/d\) for \((d,r)=1\), \(X=y/r\),
\(|r_d|\le1\). (FL) at level \(D_0\), \(s=\log D_0/\log Z\to\infty\), gives
\(\#\{n\in B:(n,P)=1\}=(y/r)\prod_{p<Z,\,p\nmid r}(1-1/p)(1+O(e^{9-s}))+O(D_0)\).
Every prime factor of \(r\) is below \(Z\) (as \(r\le R<Z\)), so
\(b\prod_{p<Z,\,p\nmid r}(1-1/p)=r/\phi(r)\) and
\[
 \sum_{n\in B}\nu(n)=\frac y{\phi(r)}+O\big(Ne^{9-s}+bD_0\big),
\]
matching (D)'s main term.

*Case \((a,r)=1\), twisted part, \(q\mid r\).* Then \(\chi\) is constant on
\(B\), \(\chi(n)=\chi(a)\), so with
\(T(u)=\sum_{n\in B,\,n\le u,\,(n,P)=1}\chi(n)\) the untwisted computation
applies at every \(u\), and since \(u\mapsto u^{\beta-1}\) is positive,
decreasing, of total variation at most \(1\) on \([1,y]\),
\[
 b\int_1^yu^{\beta-1}\,dT(u)=\chi(a)\frac{y^\beta-1}{\phi(r)\beta}\big(1+O(e^{9-s})\big)+O(bD_0).
\]
By (Cmp) and (Pg), \(\chi\) is the primitive character inducing (D)'s
\(\chi_1\) and \(\beta=\beta_1\), and \(\chi_1(a)=\chi(a)\) since
\((a,r)=1\), so this cancels (D)'s middle term.

*Case \((a,r)=1\), twisted part, \(q\nmid r\).* **Corrected.** Put
\(g=\gcd(q,r)\); \(q\nmid r\) means exactly \(g<q\). Write \(M=\mathrm{lcm}(r,q)=rq/g\).
The conditions \(n\equiv a\ (r)\) and \(n\equiv c\ (q)\) with \((c,q)=1\)
are compatible exactly when \(c\equiv a\ (g)\), and then determine one class
\(n_c\bmod M\). If \((a,g)>1\) no such \(c\) exists and \(T\equiv0\);
assume \((a,g)=1\). The admissible \(c\) form a coset of
\(K=\ker\big((\mathbb Z/q)^*\to(\mathbb Z/g)^*\big)\), of size
\(\phi(q)/\phi(g)\). Sieving each class by (FL) at level \(D_0\),
\[
 S_c(u):=\#\{n\le u:\ n\equiv n_c\ (M),\ (n,P)=1\}
 =XW\big(1+O(e^{9-s})\big)+O(D_0),
\]
\[
 X=\frac uM=\frac{ug}{rq},\qquad
 W=\prod_{\substack{p<Z\\ p\nmid M}}\Big(1-\frac1p\Big)=V(Z)\frac M{\phi(M)} .
\]
Both \(X\) and \(W\) are **independent of \(c\)**, since \(M\) is. Hence
\[
 T(u)=\sum_c\chi(c)S_c(u)
 =XW\underbrace{\sum_c\chi(c)}_{=\,0}
 \ +\ O\Big(\frac{\phi(q)}{\phi(g)}\Big[XWe^{9-s}+D_0\Big]\Big).
\tag{4.1}
\]
The main term vanishes by cancellation of \(\chi\) over a complete period of
the fibre: writing the coset as \(c_0K\), \(\sum_c\chi(c)=\chi(c_0)\sum_{k\in K}\chi(k)\),
and \(\sum_{k\in K}\chi(k)=0\) unless \(\chi|_K\) is trivial, which would
make \(\chi\) induced by a character mod \(g\) and force
\(\mathrm{cond}(\chi)=q\mid g\), contradicting \(g<q\).

**What the correction is.** The first version of this document stated the
vanishing correctly but wrote the error of (4.1) with the factor
\(\phi(q)/\phi(g)\) applied to the wrong bracket, and its next line then
dropped that factor from the first term while keeping it on the second. The
factor is real and belongs to both: the main terms cancel across the
classes, the **remainders do not**, and each of the \(\phi(q)/\phi(g)\)
classes incurs its own sieve remainder \(O(D_0)\). Carrying it explicitly,
with \(\phi(q)/\phi(g)\le q/g\) and \(M/\phi(M)\ll\log\log M\ll\log\ell\)
(since \(M\le rq<Z^2\)),
\[
 \frac{\phi(q)}{\phi(g)}XW\le\frac qg\cdot\frac{ug}{rq}\cdot V(Z)\frac M{\phi(M)}
 \ll\frac ur\,V(Z)\log\ell,
 \qquad
 \frac{\phi(q)}{\phi(g)}D_0\le qD_0 ,
\]
so \(T(u)\ll(u/r)V(Z)(\log\ell)e^{9-s}+qD_0\) uniformly in \(u\le y\), and
by the same total-variation bound as above, using \(bV(Z)=1\), \(u/r\le N\),
\(b\ll\sqrt\ell\), \(q<Z=e^{\sqrt\ell}\),
\[
 b\Big|\int_1^yu^{\beta-1}\,dT(u)\Big|
 \ \ll\ N(\log\ell)e^{9-s}+bqD_0
 \ \ll\ N(\log\ell)e^{9-s}+\ell^{1/2}e^{\sqrt\ell}D_0 .
\tag{4.2}
\]
With \(D_0=N^{o(1)}\) from 2.1 the second term is \(N^{o(1)}e^{(1+o(1))\sqrt\ell}\),
far below \(N\exp(-\gamma\sqrt\ell)\); with the \(\beta\)-sieve's
\(D_0=N^{1/2}\) it is \(\ell^{1/2}e^{\sqrt\ell}N^{1/2}\), also far below it.
The modulus factor is therefore absorbed in both variants, with a full
power of \(N\) to spare. On the \(\Lambda\) side, by (Pg) and (Cmp), no
character mod \(r\) is induced by the exceptional \(\chi\) when \(q\nmid r\),
so (D) carries no middle term, and the two sides agree.

Collecting the four cases, (1\('\)) holds with
\(\gamma=\min(c_3/2,\ c_0,\ c)\) reduced by an \(o(1)\), uniformly in \(a\),
\(r\le R\), \(y\le N\).

## 5. Input (2) at the endpoint

`ENDPOINT_HALF.md` section 2.1 verified that `SIEGEL_UNIFORMITY.md`'s model
comparison (10)-(11) survives at \(\kappa=1/2\): its own use of the
fundamental lemma is at the free level \(D=\lfloor N^{1/4}\rfloor\),
\(s=\tfrac14\sqrt\ell\), dimension \(2\), remainder \(O(Ne^{-c\sqrt\ell})\);
and the singular-series truncation contributes \(O(N\ell e^{-\sqrt\ell})\)
per shift. So (2) reads \(r_a(h)=C_N(h)+O(N\exp(-c_m\sqrt\ell))\) uniformly
in \(h\), and (3) reads \(E_{\rm corr}^{(Z)}\le2D+O(N^3\exp(-2c_m\sqrt\ell))\).
`EXCEPTIONAL_ENERGY.md`'s range bookkeeping becomes \((\log q)^2<\ell\),
i.e. \(q<Z\), as `ENDPOINT_HALF.md` section 2.2 records.

## 6. The budget at the endpoint

Combining (3), (9) and (17) as in `ENDPOINT_BOUND.md` section 6, with
\(t=\sqrt\ell\), \(R=\lfloor\exp(\sigma\sqrt\ell)\rfloor\), \(D_0=N^{A(N)}\):
\[
 E_{\rm corr}^{(Z)}(N)\ll\ell^{O(1)}\Big[N^3e^{-(2\gamma-7\sigma)\sqrt\ell}
 +N^3e^{-\sigma\sqrt\ell/6}+N^{14/5}+N^{2+A(N)}e^{\sqrt\ell/2}\Big]
 +N^3e^{-c\sqrt\ell}+N^3e^{-2c_m\sqrt\ell}.
\tag{18$'$}
\]
Take \(\sigma=\min(\gamma/20,1/20)\). The first two terms are then
\(N^3\exp(-c'\sqrt\ell)\); the third is a fixed power below \(N^3\); the
fourth needs \(A(N)\le1-(c'+\tfrac12)/\sqrt\ell\), which holds for large
\(N\) since \(A(N)=4c/\log\ell\to0\) by (A) (and would also hold, with more
room, at the \(\beta\)-sieve's \(A(N)=1/2\)); the last two are direct. So
every term is \(N^3\exp(-c'\sqrt\ell)\) with
\(c'=\tfrac12\min(2\gamma-7\sigma,\ \sigma/6,\ c,\ 2c_m)\), which is (S).

**What fixes the exponent at \(1/2\).** Four inputs, each capping there and
each attaining it: the divisor approximation, by (A), since \(A(N)\to\infty\)
for \(\kappa>1/2\); the prime number theorem in progressions with the
exceptional term, whose classical error is \(\exp(-c\sqrt{\log y})\); the
fundamental lemma, whose parameter \(s=\log D_0/\log Z\le\ell/\ell^\kappa\)
is \(o(\ell^\kappa)\) once \(\kappa>1/2\), so its error \(e^{-s}\) can no
longer match \(\exp(-\ell^\kappa)\); and the singular-series truncation
\(\ell e^{-\ell^\kappa}\) at \(Z=\exp(\ell^\kappa)\), which is the one input
that improves as \(\kappa\) grows. Moving past the endpoint therefore needs
the first three moved together, of which the second is a zero-free-region
question and the third is a constraint on the level that no choice of
weights inside this architecture relaxes. That statement is about this
chain.

**For the original \(E\).** As in `ENDPOINT_BOUND.md` section 7,
\(E\le2E_{\rm corr}^{(Z)}+2A_{\rm exc}^{(Z)}\) with
\(A_{\rm exc}^{(Z)}=2\sum_h C_N(h)^2\), so
\[
 E(N)\ll N^3\exp(-c\sqrt\ell)+1_{q\ {\rm odd}}N^{2\beta+1}\frac{q^2}{\phi(q)^4}
 +N^{4\beta-1}\frac{q^2}{\phi(q)^3},
\]
the exceptional terms present exactly when a TT-exceptional zero exists
**at this \(Z\)**, and not deletable otherwise. Because the exceptional
class differs between the two values of \(Z\), this is not comparable term
by term with `ENDPOINT_BOUND.md` section 7's version; both are
unconditional statements about \(E\), with different exceptional sets.

## 7. Finite checks

`endpoint_sharp_mertens_probe.py` and `endpoint_sharp_probe.py`, results in
`results_endpoint_sharp_mertens_probe.json` and
`results_endpoint_sharp_probe.json`.

**(1) Mertens against the elementary bound.** \(H_Z\) summed over the
primes, against \(\log\log Z+M\) and against \(1+\log Z\), at
\(\log Z=5,7,9,11,13\): the exact values are \(1.880,\ 2.212,\ 2.460,\ 2.660,\ 2.827\),
Mertens gives \(1.871,\ 2.207,\ 2.459,\ 2.659,\ 2.826\) (agreeing to the
\(O(1/\log Z)\)), and the elementary bound gives \(6,\ 8,\ 10,\ 12,\ 14\),
overstating by \(3.2\times\) to \(5.0\times\) and growing. This is the
estimate section 2's correction turns on.

**(2) The retuned cutoff at \(\kappa=1/2\)**, target decay
\(\exp(-\sqrt\ell)\), comparing the fixed \(m=2\lceil\sqrt\ell\rceil\) with
the least even \(m\) meeting the target:

| \(\log N\) | \(H_Z\) | fixed \(m\) | \(A\) fixed | retuned \(m\) | \(A\) retuned |
| --- | --- | --- | --- | --- | --- |
| \(10^2\) | 2.56 | 20 | 2.000 | 12 | 1.200 |
| \(4\times10^2\) | 3.26 | 40 | 2.000 | 20 | 1.000 |
| \(10^4\) | 4.87 | 200 | 2.000 | 62 | 0.620 |
| \(10^6\) | 7.17 | 2000 | 2.000 | 346 | 0.346 |
| \(10^{10}\) | 11.77 | 200000 | 2.000 | 16078 | 0.161 |
| \(10^{20}\) | 23.29 | \(2\times10^{10}\) | 2.000 | \(6.2\times10^8\) | 0.062 |

The fixed cutoff is pinned at \(A=2\), reproducing `ENDPOINT_HALF.md`
section 2.4. The retuned cutoff decays, and the measured values track
\(4/\log\ell\) from (A) (predicted \(0.29\) and \(0.174\) at
\(\log N=10^6,10^{10}\); measured \(0.346\) and \(0.161\)). \(A<1\) from
about \(\log N=400\); \(A<1/2\) from about \(\log N=4.7\times10^4\).

**(3) Complete-period cancellation** for the coset sums of section 4: for
every primitive real \(\chi\bmod q\) with \(q\in\{3,5,7,11,13,15,21,33,105\}\)
(Jacobi symbol, primitive since these \(q\) are odd squarefree) and both
even conductors \(q\in\{4,8\}\), and every proper divisor \(g\mid q\) with
every residue \(a\) coprime to \(g\): the sum of \(\chi(c)\) over
\(c\bmod q\), \((c,q)=1\), \(c\equiv a\ (g)\) is exactly zero, in all 96
cosets tested.

**(4) The \(\beta\)-sieve properties**, from the earlier probe: Rosser's
support enumerated from its definition at \(Z=50\), coefficients in
\(\{0,\pm1\}\) and support below \(D_0\) by construction, one-sidedness on
every \(n\le10^6\) at levels \(Z^s\), \(s=2,\dots,6\), and \(\ell^1\) error
over \(NV(Z)\) of \(0.41,\ 0.043,\ 0.0031,\ 0.0000,\ 0.0000\) against
\(e^{-s}=0.135,\ 0.050,\ 0.018,\ 0.0067,\ 0.0025\).

These check an estimate, an arithmetic retuning, a character identity and
four approximant properties. They test neither (S) nor (1\('\)).

## 8. Scope

Two corrections and one substitution inside an existing argument. The
corrections are to a lossy elementary estimate that had been read as an
asymptotic (section 2) and to a misplaced modulus factor in an error term
(section 4); both are recorded in place. The substitution replaces a cited
proposition and an unproved remark by the classical prime number theorem in
progressions with its exceptional term. The conclusion is the endpoint
\(\kappa=1/2\) for the corrected CHHL error **at the enlarged model
parameter \(Z=\exp(\sqrt{\log N})\)**, which is a different corrected
quantity from the one bounded at \(Z=\exp((\log N)^{1/10})\). It awaits an
independent check. No fixed power saving, no exclusion of exceptional
zeros, no statement about the zeros of \(\zeta\), and no novelty claim.
