# The sharp endpoint \(\kappa=1/2\): \(E_{\rm corr}^{(Z)}(N)\ll N^3\exp(-c\sqrt{\log N})\)

2026-09-11, corrected the same day in three revisions (sections 2 and 4;
every correction is recorded in place below rather than silently applied:
the Mertens estimate in section 2, the modulus factor in section 4, and, in
the third revision, section 4's progression input and its sieve level).
Base: the chain
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
   theorem in progressions with the exceptional zero retained, in the
   published form of Drappeau and Fiorilli's Lemma 2.2 (read and quoted in
   section 4; its exceptional datum is Page's theorem at
   \(Q=T=e^{\sqrt{\log x}}\), which at \(x=N\) is this document's \(Z\)),
   Page's theorem, and the fundamental lemma of sieve theory applied to the
   model inside a progression at its own level \(D_1=\lfloor N^{1/2}\rfloor\)
   (section 4). Remark 2.8 is not used.

Everything else in the chain was already verified at \(\kappa=1/2\) by
`ENDPOINT_HALF.md` sections 2.1 and 2.2 and is reused, not redone.

Grade: derived, one route, independently checked (see below). The classical
inputs are named where used. The finite checks in section 7 test the
Mertens correction, the retuned cutoff, and the character cancellation of
section 4; they test no asymptotic statement. This establishes no fixed
power saving, no exclusion of exceptional zeros, and nothing about the
zeros of \(\zeta\).

**Independent check, 2026-09-11** (attempt `a-0075`, judged by `a-0076`,
which recomputed the arithmetic with its own script). It confirmed equation
(A), the attainment of the endpoint, the failure at \(\kappa>1/2\), the
character cancellation and error assembly of section 4, the scoping of
\(E_{\rm corr}^{(Z)}\), and the budget assembly, and it found **one
defect**: section 7's table and section 2.1's crossover sentences understated
the least admissible cutoff \(m\) by \(2\), because the probe searched
against the exact factorial \(H_Z^{m+1}/(m+1)!\) while the document's own
displayed inequality (5\('\)) is the Stirling-weakened
\((eH_Z/(m+1))^{m+1}\). Corrected below; the table now matches the
reviewer's independent recomputation exactly. It also reported that it had
no network access and so could not check input (D) and (Pg) against primary
sources. Those were checked in the orchestrator session instead: (Pg) was
verified verbatim, and (D) was found unread and has since been replaced
(section 4, section 7 item (5)).

**The third revision's own check** (attempt `a-0077`,
`ENDPOINT_SHARP_REVIEW_2.md`). The third revision postdates `a-0075`. Its
two substitutions, the progression input (DF) in place of (D) and the
separate sieve level \(D_1\) in section 4, were checked in the orchestrator
session against the source and by recomputing every error term of section
4, then independently by `a-0077`, which recomputed \(s_1\) and the
\(D_1\ge Z^{10}\) threshold directly from \(N\) (equality at exactly
\(\log N=400\)), rederived the range \(\gamma<\min(c_0/2,\delta/\sqrt2,1/2)\)
from the four error sources, confirmed the matching of exceptional data
with no missed case, and tested the frozen-at-\(x\) remark of section 4
numerically (the ratio of the discrepancy to the lemma's error term grows
like \(e^{\delta\sqrt{\log x}}/\log x\) at \(1-\beta=1/\log x\)). It found
no defect. It had no network access, so the word-for-word comparison of the
(DF) quotation against the source rested on the orchestrator session until
a scoped source check by a GPT session, against commit 08e05bd and the
published Lemma 2.2, equation (2.1), passed it (operator's report,
2026-09-11; section 7 item (5)). **The endpoint review is closed** with
that check: every section of this document has had a second independent
reader, no further paid check is planned, and what remains is the standing
footnote that any published claim carries until an outside reader has
walked the chain.

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
\(R=\lfloor\exp(\sigma t)\rfloor\), \(\sigma\) fixed in section 6. Two
levels, with different roles: the level of the divisor approximant is
\(D_0\), fixed in section 2 and consumed by the budget; the level at which
section 4 sieves a progression to prove input (1\('\)) is
\(D_1=\lfloor N^{1/2}\rfloor\), fixed there and consumed nowhere else.

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

Honest numerics, from section 7, and note that \(A(N)=m/\sqrt\ell\) is
sawtooth rather than monotone (it falls between the jumps of \(m\) and
rises by \(2/\sqrt\ell\) at each jump), so the crossover that matters is the
**last** one, not the first. Under the criterion (5\('\)) actually states:
\(A(N)\) first dips below \(1\) at \(\log N\approx677\) and stays below it
for every \(\log N>784\); it stays below \(1/2\) for every
\(\log N>5.38\times10^4\), i.e. \(N\) beyond about \(10^{23000}\). The
budget needs \(A(N)<1\) with a margin \(\asymp\ell^{-1/2}\) (section 6),
not \(A(N)<1/2\), so the operative threshold is \(\log N>784\). \(A(N)\)
decays like \(1/\log\ell\), which is slow; (S) is an asymptotic statement
and this is where its "sufficiently large \(N\)" lives.

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

**Revised 2026-09-11 (third revision), two substitutions, both recorded
here rather than silently applied.**

(i) *The progression input.* The first two versions cited (D) to Davenport,
Chapter 20, and section 7 item (5) recorded that the citation had not been
read. It is replaced by Drappeau and Fiorilli's Lemma 2.2, which was read
and is quoted below, and whose exceptional datum is Page's theorem at
\(Q=T=e^{\sqrt{\log x}}\): at \(x=N\) that is exactly this document's
\(Z\), so the two exceptional data are matched rather than compared.

(ii) *The sieve level.* The first two versions applied the fundamental
lemma inside this section at the approximant level \(D_0\) of section 2.
That was too small. With the retuned cutoff, \(D_0=N^{A(N)}\) and
\(A(N)=4c/\log\ell\), so the sieve parameter is
\[
 s=\frac{\log D_0}{\log Z}=A(N)\sqrt\ell=\frac{4c}{\log\ell}\sqrt\ell\,(1+o(1)),
\]
and the displayed fundamental-lemma error \(e^{9-s}=\exp(-(4c/\log\ell)\sqrt\ell\,(1+o(1)))\)
decays more slowly than \(\exp(-\gamma\sqrt\ell)\) for every fixed
\(\gamma>0\). As written, (1\('\)) did not follow. The repair is to
separate the two roles the one symbol was carrying. \(D_0\) is the level of
the divisor approximant \(b\lambda\) that replaces \(\nu\) on the minor
arcs; it enters the budget through (P4) and is constrained by (A). The level
at which this section sieves a progression is a free parameter of the proof
of (1\('\)), enters nothing outside this section, and has no reason to
equal \(D_0\). Fix it at
\[
 D_1=\lfloor N^{1/2}\rfloor,\qquad
 s_1:=\frac{\log D_1}{\log Z}=\frac{\sqrt\ell}{2}\,(1+o(1)),\qquad
 e^{9-s_1}=e^{9}\exp\big(-\tfrac12\sqrt\ell\,(1+o(1))\big),
\]
with sieve remainders \(O(D_1)=O(N^{1/2})\). The fundamental lemma's
hypothesis \(D_1\ge Z^{10}\) is \(\ell\ge400\), i.e. \(N\ge e^{400}\), inside
the "sufficiently large \(N\)" of (S). The \(\beta\)-sieve alternative of
2.2 also uses a fixed level \(N^{1/2}\), for the approximant; that is a
coincidence of convenient values, not the same parameter.

**Claim (1\('\)).** There is a fixed \(\gamma>0\) such that, uniformly over
every progression \(B=\{n\le y:\ n\equiv a\ (\mathrm{mod}\ r)\}\) with
\(y\le N\), \(r\le R\), and every residue \(a\),
\[
 \Big|\sum_{n\in B}\big(\Lambda(n)-a(n)\big)\Big|\ll N\exp(-\gamma\sqrt\ell).
\tag{1$'$}
\]

*Inputs.*

(DF) Drappeau and Fiorilli, *The first moment of primes in arithmetic
progressions: beyond the Siegel-Walfisz range*, Trans. London Math. Soc.
8 (2021), no. 1, 174-185, doi 10.1112/tlm3.12030, **Lemma 2.2, equation
(2.1)**; arXiv:2003.02201v1. The published statement is the one cited;
its display (2.1) carries a prefix factor on the right-hand side, the
logarithmic factor placed in front of the whole bound rather than on the
second term alone. The text quoted below is the arXiv version, which is
the one read in this session. *Version comparison, kept on the record:* in
the arXiv version the lemma's display carries no number and (2.1) is the
decomposition that consumes it; in the published version the lemma's
display is (2.1). The published wording was not read here (the publisher
returned 403 to this environment); the comparison of this quotation with
the published lemma was made in a scoped source check by a GPT session
against commit 08e05bd, reported PASS by the operator on 2026-09-11 and
recorded in section 7 item (5). Where the logarithmic factor sits changes
nothing below: on \(xe^{-\delta\sqrt{\log x}}\) it is absorbed by lowering
\(\delta\), and (D\('\)) is stated with that done.

> *Fix \(a\in\mathbb Z\setminus\{0\}\). There exists \(\delta>0\) such that
> for all \(x,Q\ge1\) we have the bound*
> \[
>  \sum_{q\le Q}\ \max_{y\le x}\ \max_{(a,q)=1}
>  \Big|\psi(y;q,a)-\big(1-\eta_{x,a}1_{\tilde q\mid q}\big)\frac y{\phi(q)}\Big|
>  \ll xe^{-\delta\sqrt{\log x}}+Q\sqrt x\,(\log x)^{O(1)},
> \]
> *where \(\eta_{x,a}\) was defined in (1.6).*

Their (1.6) is \(\eta_{x,a}:=\tilde\chi(a)/(\beta x^{1-\beta})\in(-1,1)\),
and their exceptional datum is their Theorem 1.2 (Page's theorem, cited to
Iwaniec and Kowalski, Theorems 5.26 and 5.28) with the definition that
follows it: *there is an absolute constant \(b>0\) such that for all
\(Q,T\ge2\) the function \(\prod_{q\le Q}\prod_{\chi\bmod q}L(s,\chi)\) has
at most one zero \(s=\beta\) with \(\mathrm{Re}(s)>1-b/\log(QT)\) and
\(|\mathrm{Im}(s)|\le T\); if it exists it is real and is the zero of a
unique \(L(s,\tilde\chi)\) for some primitive real character \(\tilde\chi\)*
(of conductor \(\tilde q\)); *\(\tilde\chi\) is \(x\)-exceptional if the
above conditions are met with \(Q=T=e^{\sqrt{\log x}}\).* So the
\(x\)-exceptional character has \(\tilde q\le e^{\sqrt{\log x}}\) and its
zero satisfies \(\beta>1-b/(2\sqrt{\log x})\).

The lemma is applied here with \(x:=y\) for each prefix \(y\) separately,
with \(Q:=R\), and a single term of the sum is bounded by the whole sum. For
\((a,r)=1\), \(r\le R\), writing \(\tilde\chi_y\), \(\tilde q_y\),
\(\tilde\beta_y\) for the \(y\)-exceptional data,
\[
 \psi(y;r,a)=\frac y{\phi(r)}-1_{\tilde q_y\mid r}\,\tilde\chi_y(a)\frac{y^{\tilde\beta_y}}{\tilde\beta_y\,\phi(r)}
 +O\big(ye^{-\delta\sqrt{\log y}}+R\sqrt y\,(\log y)^{O(1)}\big),
\tag{D$'$}
\]
since \(\eta_{y,a}\,y=\tilde\chi_y(a)y^{\tilde\beta_y}/\tilde\beta_y\).

Two remarks on the reading, recorded because this document leans on the
statement. First, "Fix \(a\)" and the inner maximum over \((a,q)=1\) do not
sit together; (D\('\)) is read as uniform in \(a\), which is what the inner
maximum asserts and what the proof they cite (Davenport, Chapter 28,
p. 164, with the exceptional character separated) supplies. Second, as
printed the maximum over \(y\le x\) is taken with \(\eta_{x,a}\) frozen at
\(x\), while the exceptional main term at \(y\) is
\(\tilde\chi(a)y^\beta/(\beta\phi(q))\); the two differ by
\(\tilde\chi(a)\,y\,x^{\beta-1}\big((x/y)^{1-\beta}-1\big)/(\beta\phi(q))\),
and when \(1-\beta\) and \(\log(x/y)/\sqrt{\log x}\) are both small
compared with \(\delta\), that difference summed over \(\tilde q\mid q\le Q\)
is not \(O(xe^{-\delta\sqrt{\log x}})\). The uniformity in \(y\) therefore
appears not to hold literally as printed; the paper itself uses the lemma
only at \(y=x\) (its (2.1) and (2.2)), where nothing is affected. This
document does not rely on it: taking \(x:=y\) in (D\('\)) is exactly what
removes the issue, at the price that the exceptional datum now depends on
\(y\), which the matching below handles.

(Pg) Page's theorem, in the form verified against a primary source in
section 7 item (5): *there is an absolute \(c>0\) such that for any
\(Q\ge2\), among the primitive real characters of conductor at most \(Q\),
at most one has an \(L\)-function with a real zero in \([1-c(\log Q)^{-1},1)\).*
At \(Q=Z=e^{\sqrt\ell}\): at most one primitive real character of conductor
\(<Z\) has a real zero \(\beta>1-c/\sqrt\ell\). This is the same theorem as
(DF)'s Theorem 1.2 with a differently normalised constant; both are used,
(Pg) for the uniqueness of the TT-exceptional datum at \(Z\), (DF)'s form
for the \(y\)-exceptional datum.

(FL) The fundamental lemma as in 2.2, applied in this section at level
\(D_1\), parameter \(s_1\).

(Cmp) Fix \(c_0\le\min(c,\ b/2)\) in section 1.

*Small \(y\).* If \(y\le N\exp(-\gamma\sqrt\ell)\) both sides of (1\('\))
are \(O(y\ell)\); so assume \(\log y\ge\ell/2\). Then
\(e^{\sqrt{\log y}}\ge e^{\sqrt{\ell/2}}\ge R\) (as \(\sigma\le1/20<1/\sqrt2\)),
\(e^{\sqrt{\log y}}\le Z\), \(b/(2\sqrt{\log y})\ge b/(2\sqrt\ell)\ge c_0/\sqrt\ell\),
\(ye^{-\delta\sqrt{\log y}}\le Ne^{-\delta\sqrt\ell/\sqrt2}\), and
\(R\sqrt y(\log y)^{O(1)}\le e^{\sigma\sqrt\ell}N^{1/2}\ell^{O(1)}\le Ne^{-\sqrt\ell}\)
for large \(N\).

*Matching the exceptional data.* Let \(\chi\bmod q\), \(\beta\) be the
TT-exceptional data at \(Z\) when they exist. For \((a,r)=1\), \(r\le R\),
\(\log y\ge\ell/2\):

- If \(\chi\) exists and \(q\mid r\): then \(q\le r\le R\le e^{\sqrt{\log y}}\),
  \(\beta>1-c_0/\sqrt\ell\ge1-b/(2\sqrt{\log y})\), and \(\beta\) is real,
  so \(\beta\) lies in the region of (DF)'s Theorem 1.2 at
  \(Q=T=e^{\sqrt{\log y}}\); by its uniqueness, \(\tilde\chi_y=\chi\) and
  \(\tilde\beta_y=\beta\). (D\('\)) carries the term
  \(-\chi(a)y^\beta/(\beta\phi(r))\).
- If a \(y\)-exceptional \(\tilde\chi_y\) exists with \(\tilde q_y\mid r\)
  and is not TT-exceptional at \(Z\): since \(\tilde q_y\le r\le R<Z\), the
  failing condition is \(\tilde\beta_y\le1-c_0/\sqrt\ell\), so
  \(y^{\tilde\beta_y-1}\le\exp(-c_0\log y/\sqrt\ell)\le\exp(-c_0\sqrt\ell/2)\)
  and the term is at most \(2ye^{-c_0\sqrt\ell/2}/\phi(r)\ll Ne^{-c_0\sqrt\ell/2}\).
- If \(\chi\) exists and \(q\nmid r\): either \(\tilde\chi_y=\chi\), and
  then \(1_{\tilde q_y\mid r}=0\); or \(\tilde\chi_y\ne\chi\), and then
  \(\tilde\chi_y\) is not TT-exceptional at \(Z\) (uniqueness from (Pg),
  \(c_0\le c\)), so the previous point applies.
- If no TT-exceptional character exists at \(Z\), any \(\tilde\chi_y\) with
  \(\tilde q_y\mid r\) falls under the second point.

Hence, in every case, with \(1_{\rm exc}\) the indicator that the
TT-exceptional data exist at \(Z\),
\[
 \psi(y;r,a)=\frac y{\phi(r)}-1_{\rm exc}1_{q\mid r}\,\chi(a)\frac{y^\beta}{\beta\phi(r)}
 +O\big(N\exp(-c_4\sqrt\ell)\big),\qquad c_4=\min\big(c_0/2,\ \delta/\sqrt2\big).
\tag{D$''$}
\]
This is the statement the first two versions attributed to Davenport; the
form (D\('\))-(D\(''\)) is what is now actually consumed.

*Case \((a,r)>1\).* A prime \(p\mid(a,r)\) divides every \(n\in B\) and
\(p\le r<Z\), so \(a(n)=0\) on \(B\); the \(\Lambda\) side counts prime
powers of primes dividing \(r\), at most \(\omega(r)\ell\ll\ell^2\).

*Case \((a,r)=1\), untwisted part.* Sieve \(B\) by the primes \(p<Z\):
\(g(p)=0\) for \(p\mid r\), \(g(d)=1/d\) for \((d,r)=1\), \(X=y/r\),
\(|r_d|\le1\). (FL) at level \(D_1\), parameter \(s_1\), gives
\(\#\{n\in B:(n,P)=1\}=(y/r)\prod_{p<Z,\,p\nmid r}(1-1/p)(1+O(e^{9-s_1}))+O(D_1)\).
Every prime factor of \(r\) is below \(Z\) (as \(r\le R<Z\)), so
\(b\prod_{p<Z,\,p\nmid r}(1-1/p)=r/\phi(r)\) and
\[
 \sum_{n\in B}\nu(n)=\frac y{\phi(r)}+O\big(Ne^{9-s_1}+bD_1\big)
 =\frac y{\phi(r)}+O\big(Ne^{9-\sqrt\ell/2}+\ell^{1/2}N^{1/2}\big),
\]
matching (D\(''\))'s main term.

*Case \((a,r)=1\), twisted part, \(q\mid r\).* Then \(\chi\) is constant on
\(B\), \(\chi(n)=\chi(a)\), so with
\(T(u)=\sum_{n\in B,\,n\le u,\,(n,P)=1}\chi(n)\) the untwisted computation
applies at every \(u\), and since \(u\mapsto u^{\beta-1}\) is positive,
decreasing, of total variation at most \(1\) on \([1,y]\),
\[
 b\int_1^yu^{\beta-1}\,dT(u)=\chi(a)\frac{y^\beta-1}{\phi(r)\beta}\big(1+O(e^{9-s_1})\big)+O(bD_1).
\]
By the matching above, this is (D\(''\))'s exceptional term up to
\(O(Ne^{9-\sqrt\ell/2}+\ell^{1/2}N^{1/2})\).

*Case \((a,r)=1\), twisted part, \(q\nmid r\).* Put \(g=\gcd(q,r)\);
\(q\nmid r\) means exactly \(g<q\). Write \(M=\mathrm{lcm}(r,q)=rq/g\). The
conditions \(n\equiv a\ (r)\) and \(n\equiv c\ (q)\) with \((c,q)=1\) are
compatible exactly when \(c\equiv a\ (g)\), and then determine one class
\(n_c\bmod M\). If \((a,g)>1\) no such \(c\) exists and \(T\equiv0\); assume
\((a,g)=1\). The admissible \(c\) form a coset of
\(K=\ker\big((\mathbb Z/q)^*\to(\mathbb Z/g)^*\big)\), of size
\(\phi(q)/\phi(g)\). Sieving each class by (FL) at level \(D_1\),
\[
 S_c(u):=\#\{n\le u:\ n\equiv n_c\ (M),\ (n,P)=1\}
 =XW\big(1+O(e^{9-s_1})\big)+O(D_1),
\]
\[
 X=\frac uM=\frac{ug}{rq},\qquad
 W=\prod_{\substack{p<Z\\ p\nmid M}}\Big(1-\frac1p\Big)=V(Z)\frac M{\phi(M)} .
\]
Both \(X\) and \(W\) are **independent of \(c\)**, since \(M\) is. Hence
\[
 T(u)=\sum_c\chi(c)S_c(u)
 =XW\underbrace{\sum_c\chi(c)}_{=\,0}
 \ +\ O\Big(\frac{\phi(q)}{\phi(g)}\Big[XWe^{9-s_1}+D_1\Big]\Big).
\tag{4.1}
\]
The main term vanishes by cancellation of \(\chi\) over a complete period of
the fibre: writing the coset as \(c_0K\), \(\sum_c\chi(c)=\chi(c_0)\sum_{k\in K}\chi(k)\),
and \(\sum_{k\in K}\chi(k)=0\) unless \(\chi|_K\) is trivial, which would
make \(\chi\) induced by a character mod \(g\) and force
\(\mathrm{cond}(\chi)=q\mid g\), contradicting \(g<q\).

**The modulus factor** (the second revision's correction, kept). The first
version stated the vanishing correctly but wrote the error of (4.1) with
the factor \(\phi(q)/\phi(g)\) applied to the wrong bracket, and its next
line then dropped that factor from the first term while keeping it on the
second. The factor is real and belongs to both: the main terms cancel across
the classes, the **remainders do not**, and each of the \(\phi(q)/\phi(g)\)
classes incurs its own sieve remainder \(O(D_1)\). Carrying it explicitly,
with \(\phi(q)/\phi(g)\le q/g\) and \(M/\phi(M)\ll\log\log M\ll\log\ell\)
(since \(M\le rq<Z^2\)),
\[
 \frac{\phi(q)}{\phi(g)}XW\le\frac qg\cdot\frac{ug}{rq}\cdot V(Z)\frac M{\phi(M)}
 \ll\frac ur\,V(Z)\log\ell,
 \qquad
 \frac{\phi(q)}{\phi(g)}D_1\le qD_1 ,
\]
so \(T(u)\ll(u/r)V(Z)(\log\ell)e^{9-s_1}+qD_1\) uniformly in \(u\le y\), and
by the same total-variation bound as above, using \(bV(Z)=1\), \(u/r\le N\),
\(b\ll\sqrt\ell\), \(q<Z=e^{\sqrt\ell}\), \(D_1\le N^{1/2}\),
\[
 b\Big|\int_1^yu^{\beta-1}\,dT(u)\Big|
 \ \ll\ N(\log\ell)e^{9-s_1}+bqD_1
 \ \ll\ N(\log\ell)e^{9-\sqrt\ell/2}+\ell^{1/2}e^{\sqrt\ell}N^{1/2}.
\tag{4.2}
\]
The second term is \(N^{1/2+o(1)}\), below \(N\exp(-\gamma\sqrt\ell)\) with
half a power of \(N\) to spare, so the modulus factor is absorbed. On the
\(\Lambda\) side, (D\(''\)) carries no exceptional term when \(q\nmid r\),
and the two sides agree.

Collecting the four cases and (D\(''\)), (1\('\)) holds for every fixed
\[
 \gamma<\min\big(c_0/2,\ \delta/\sqrt2,\ 1/2\big),
\]
uniformly in \(a\), \(r\le R\), \(y\le N\); the \(1/2\) is the sieve level
\(D_1=N^{1/2}\) through \(e^{-s_1}\), and is the term the first two versions
had, in effect, at \((4c/\log\ell)\) instead.

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
exceptional term, whose error in (DF) is \(\exp(-\delta\sqrt{\log y})\); the
fundamental lemma inside the proof of (1\('\)), whose parameter
\(s_1=\log D_1/\log Z\le\ell/\ell^\kappa\) at any level \(D_1\le N\) is
\(o(\ell^\kappa)\) once \(\kappa>1/2\), so its error \(e^{-s_1}\) can no
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
the least even \(m\) meeting the target **under the criterion (5\('\))
states**, namely \((eH_Z/(m+1))^{m+1}\le e^{-\sqrt\ell}\):

| \(\log N\) | \(H_Z\) | fixed \(m\) | \(A\) fixed | retuned \(m\) | \(A\) retuned |
| --- | --- | --- | --- | --- | --- |
| \(10^2\) | 2.56 | 20 | 2.000 | 14 | 1.400 |
| \(4\times10^2\) | 3.26 | 40 | 2.000 | 22 | 1.100 |
| \(10^4\) | 4.87 | 200 | 2.000 | 64 | 0.640 |
| \(10^6\) | 7.17 | 2000 | 2.000 | 348 | 0.348 |
| \(10^{10}\) | 11.77 | 200000 | 2.000 | 16078 | 0.161 |
| \(10^{20}\) | 23.29 | \(2\times10^{10}\) | 2.000 | \(6.2\times10^8\) | 0.062 |

**Correction.** The first version of this table searched against the exact
factorial \(H_Z^{m+1}/(m+1)!\), which is smaller than the bound the
document displays and so admits an \(m\) smaller by \(2\) at these scales.
`a-0075` found this and `a-0076` recomputed the corrected column with an
independent script, obtaining \(m=14,22,64,348\) and
\(A=1.400,1.100,0.640,0.348\), which is what now stands. The probe reports
both criteria; only the stated one is tabulated.

The fixed cutoff is pinned at \(A=2\), reproducing `ENDPOINT_HALF.md`
section 2.4. The retuned cutoff decays, and the measured values track
\(4/\log\ell\) from (A) (predicted \(0.29\) and \(0.174\) at
\(\log N=10^6,10^{10}\); measured \(0.348\) and \(0.161\)). Because
\(A(N)=m/\sqrt\ell\) is sawtooth, the thresholds are stated as last
crossings: \(A<1\) for every \(\log N>784\) (first dip at \(\approx677\)),
and \(A<1/2\) for every \(\log N>5.38\times10^4\).

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

**(5) The classical inputs of section 4, against primary sources.** Checked
in the orchestrator session, which had network access the cell did not.

- **(Pg), Page's theorem: verified verbatim.** Basak and Pratt, *A
  Conditional Refinement of Page's Theorem on zeros of Dirichlet
  \(L\)-functions*, arXiv:2607.06433v1, Theorem 1.1, attributed there to
  Page (Lemma 9) and to Davenport, p. 95: *"There exists an absolute
  constant \(c>0\) such that the following holds. For any \(Q\ge2\), we have
  \(\#\{\chi\in S(Q): L(s,\chi)\ \text{has a real zero in}\ [1-c(\log Q)^{-1},1)\}\le1\),"*
  with \(S(Q)=\{\chi\bmod q_\chi:\chi\ \text{primitive and real},\ 1\le q_\chi\le Q\}\).
  Section 4's (Pg) is this at \(Q=Z\), and its \(1/\sqrt\ell\) threshold is
  \(c/\log Q\) with \(\log Q=\sqrt\ell\), so the two agree with the same
  absolute constant. The same source states the zero-free region
  \(\sigma\ge1-c_0/\log(q(|t|+2))\) containing at most a single zero,
  necessarily real and with \(\chi\) quadratic (its (1.1), citing Davenport
  p. 93), which is what makes the TT-exceptional data well defined, and
  Siegel's ineffective \(\beta\le1-c(\varepsilon)q_\chi^{-\varepsilon}\)
  (its (1.2)).
- **(D), as cited in the first two versions: never read, now withdrawn.**
  It was cited to Davenport, Chapter 20. The volume this hunt already
  cites, Montgomery and Vaughan *Multiplicative Number Theory II*, was
  fetched and searched: it contains no statement of Page's theorem and no
  occurrence of "Siegel zero" or "exceptional zero", its Chapter 20 being a
  different part of the subject, so it was not the source. The closest
  reachable corroboration was explicit work in the style of Baker, Faber
  and Kinlaw, arXiv:1802.00085v3, which carries the exceptional zero through
  the explicit formula as the \(x^{\beta-1}\) term of the zero sum (its
  Definition 6.1 and (2.5)-(2.6)) but never states (D) in the
  corrected-main-term form. Rather than keep an unread citation, the third
  revision replaced it.
- **(DF), Drappeau and Fiorilli Lemma 2.2: verified verbatim** against
  arXiv:2003.02201v1, pages 2 to 4, and quoted in section 4 together with
  their Theorem 1.2, their definition of the \(x\)-exceptional character
  (\(Q=T=e^{\sqrt{\log x}}\)) and their (1.6). Three things were checked
  beyond the wording. (i) The exceptional datum matches: at \(x=N\) their
  conductor bound \(e^{\sqrt{\log x}}\) is \(Z\), and their threshold
  \(1-b/(2\sqrt{\log x})\) is this document's \(1-c_0/\sqrt\ell\) with
  \(c_0\le b/2\), which (Cmp) now imposes. (ii) The lemma's proof is cited
  to Davenport, Chapter 28, p. 164, the Bombieri-Vinogradov argument with
  the exceptional character separated, and its error terms are the
  Bombieri-Vinogradov ones, \(xe^{-\delta\sqrt{\log x}}+Q\sqrt x(\log x)^{O(1)}\);
  section 4 uses them at \(Q=R\), where the second is \(N^{1/2+o(1)}\).
  (iii) The statement's uniformity in \(y\le x\) with \(\eta_{x,a}\) frozen
  at \(x\) appears not to hold literally, for the reason given in section
  4; section 4 applies the lemma at \(x=y\) and does not use that
  uniformity. The paper's own use is at \(y=x\) only. The numbering
  quoted is the arXiv version's, where the lemma's display is unnumbered
  and (2.1) is the decomposition that consumes it; in the published
  version (Trans. London Math. Soc. 8 (2021) 174-185) the lemma's display
  is equation (2.1) and carries its logarithmic factor as a prefix on the
  whole right-hand side. The published page could not be fetched from
  this environment (403). **Scoped source check, PASS.** A GPT session
  with access to the published text compared the quotation and its use in
  section 4 against the published Lemma 2.2, equation (2.1), at commit
  08e05bd, and passed it; the operator reported the result on 2026-09-11.
  That check was not run from this session and its transcript is not in
  this repository; what is recorded here is the operator's report of it,
  which is the same standing as every other operator-supplied fact in
  this hunt. With it, every input of section 4 has been read against a
  primary source by at least two readers.
- **The level \(D_1\).** Every error term of section 4 was recomputed with
  \(D_1=\lfloor N^{1/2}\rfloor\) in place of \(D_0\): \(s_1=\sqrt\ell/2\),
  \(e^{9-s_1}=e^9\exp(-\sqrt\ell/2)\), remainders \(bD_1\ll\ell^{1/2}N^{1/2}\)
  and \(bqD_1\ll\ell^{1/2}e^{\sqrt\ell}N^{1/2}\), and the hypothesis
  \(D_1\ge Z^{10}\) at \(\ell\ge400\). The defect this repairs, \(s=A(N)\sqrt\ell\)
  with \(A(N)=4c/\log\ell\), was checked against (A) directly.

These check an estimate, an arithmetic retuning, a character identity, four
approximant properties, two classical citations verbatim, and the
substitution of a level. They test neither (S) nor (1\('\)).

## 8. Scope

Three corrections and one substitution inside an existing argument. The
corrections are to a lossy elementary estimate that had been read as an
asymptotic (section 2), to a misplaced modulus factor in an error term
(section 4), and to a sieve level that had been tied to the approximant's
and was too small for the error it was asked to deliver (section 4); all
three are recorded in place. The substitution replaces a cited proposition
and an unproved remark by the prime number theorem in progressions with its
exceptional term, in Drappeau and Fiorilli's published form, read and quoted
rather than cited from memory. The conclusion is the endpoint
\(\kappa=1/2\) for the corrected CHHL error **at the enlarged model
parameter \(Z=\exp(\sqrt{\log N})\)**, which is a different corrected
quantity from the one bounded at \(Z=\exp((\log N)^{1/10})\). The first two
revisions were independently checked (`ENDPOINT_SHARP_REVIEW.md`), and the
third revision's two substitutions were checked separately
(`ENDPOINT_SHARP_REVIEW_2.md`), and the quotation of (DF) was passed by a
scoped source check against the published lemma (section 7 item (5)). The
endpoint review is closed. No fixed power saving, no exclusion of exceptional
zeros, no statement about the zeros of \(\zeta\), and no novelty claim.

**Forward pointer, added after this checkpoint closed.** `ARC_SPLIT_BUDGET.md`
(2026-09-11, later the same day) reaches the same shape of bound with the
exponent constant \(2\gamma/3\) in place of this document's \(\gamma/240\), by
splitting the corrected residual by arcs rather than by model, so that the
divisor approximant of section 2 and the minor-arc estimates of
`ENDPOINT_BOUND.md` section 4 are not consumed. Nothing in this document is
changed by it; section 6's four-input account describes this chain.
