# The sharp endpoint \(\kappa=1/2\): \(E_{\rm corr}(N)\ll N^3\exp(-c\sqrt{\log N})\)

2026-09-11. Base: the chain `SIEGEL_UNIFORMITY.md` -> `EXCEPTIONAL_ENERGY.md`
-> `ENDPOINT_BOUND.md` (reviewed in `ENDPOINT_BOUND_REVIEW.md`), and
`ENDPOINT_HALF.md`, which found that the chain tolerates every
\(Z=\exp((\log N)^\kappa)\) with \(\kappa<1/2\) and breaks at \(\kappa=1/2\)
in exactly one place, the bounded-order (Bonferroni) divisor approximation
of `ENDPOINT_BOUND.md` section 2. Attempt `a-0070` walled on the same
endpoint. None of the base files is changed by this document.

**Result, stated first.** For some fixed \(c>0\) and all sufficiently large
\(N\), unconditionally,
\[
 \boxed{\ E_{\rm corr}(N)\ \ll\ N^3\exp\!\big(-c\sqrt{\log N}\big).\ }
\tag{S}
\]
This is the endpoint \(\kappa=1/2\) of `ENDPOINT_HALF.md`'s family (A),
attained rather than approached, and it no longer rests on Tao and
Teräväinen's Remark 2.8. Two replacements in `ENDPOINT_BOUND.md` do it:

1. **Section 2.** The Bonferroni truncation \(B_m\), which truncates the
   Möbius sum over \(d\mid P(Z)\) by the number of prime factors and
   therefore needs level \(D_0=Z^m\) with \(m>eH_Z\), is replaced by the
   upper-bound weights \(\lambda^+_d\) of the linear \(\beta\)-sieve, which
   truncate by the size of \(d\) and reach the same one-sided approximation
   at level \(D_0=Z^s\) with error \(e^{-s}\) for any \(s\ge10\). The chain
   uses exactly four properties of the approximant (section 2 below);
   \(\lambda^+\) has all four, and at the endpoint the level can be taken
   as \(D_0=N^{1/2}\), where the Bonferroni device needed \(N^{e}\).
2. **Section 1, input (1).** The progression input, cited there from TT
   Proposition 2.2 at \(Z=\exp((\log N)^{1/10})\), is at the endpoint the
   prime number theorem for progressions with the exceptional zero retained
   (Davenport, Chapter 20) combined with the same fundamental lemma applied
   to the model in a progression. Section 4 derives it in the uniform form
   the chain needs. Remark 2.8 is not used.

Everything else in the chain was already checked at \(\kappa=1/2\) by
`ENDPOINT_HALF.md` sections 2.1 and 2.2 and is reused, not redone.

Grade: derived, one route. The two classical inputs are the fundamental
lemma of sieve theory in the form `SIEGEL_UNIFORMITY.md` already consumes,
and the prime number theorem in progressions with the exceptional term.
The finite check in section 7 tests the properties of the new approximant,
not the asymptotic conclusion. This establishes no fixed power saving, no
exclusion of exceptional zeros, and nothing about the zeros of \(\zeta\).

## 1. Parameters at the endpoint

Write \(\ell=\log N\) and take, in place of `ENDPOINT_BOUND.md` section 1,
\[
 t=\sqrt\ell,\qquad Z=e^{t},\qquad P=\prod_{p<Z}p,\qquad b=P/\phi(P)=V(Z)^{-1},
 \qquad V(Z)=\prod_{p<Z}(1-1/p),
\]
\(\nu(n)=b\,1_{(n,P)=1}\), \(a(n)=\nu(n)(1-1_{\rm exc}\chi(n)n^{\beta-1})\),
with the exceptional data of TT Definition 2.1 at this \(Z\): \(\chi\)
primitive real of conductor \(q<Z\), \(1-c_0/\log Z<\beta<1\), \(c_0\) a
fixed sufficiently small absolute constant. \(F,H,W,r,r_a,C_N,E_{\rm corr},D\)
are as there. The major-arc parameter is \(R=\lfloor\exp(\sigma t)\rfloor\)
with \(\sigma\) fixed as in section 6. The level of the divisor approximant
is
\[
 D_0=\lfloor N^{1/2}\rfloor,\qquad s:=\frac{\log D_0}{\log Z}=\frac{\ell}{2\sqrt\ell}(1+o(1))=\tfrac12\sqrt\ell\,(1+o(1)).
\]

## 2. The four properties the chain uses, and the replacement

`ENDPOINT_BOUND.md` uses its approximant \(B_m\) in exactly these places:
(4)-(6) in section 2; the prefix Type I bound after (10) in 4.1; the
untwisted model prefix in 4.2; Cases A and B of 4.3 through (13)-(15); and
the resulting \(N^2D_0\sqrt Z\) and \(N^3\exp(-c\sqrt\ell)\) terms of (17)
and (18). Reading those steps, the properties consumed are:

- (P1) the coefficients \(\lambda_d\) of the divisor sum satisfy \(|\lambda_d|\le1\)
  ("every divisor coefficient is \(0,1\), or \(-1\)");
- (P2) the support is \(d\mid P(Z)\), \(d<D_0\), with \(D_0\le N\) ("every
  divisor present is less than \(D_0\)"; (10) needs \(D_0\le N\));
- (P3) the \(\ell^1\) approximation \(\sum_{n\le y}|b\Lambda(n)-\nu(n)|\ll N\exp(-c\sqrt\ell)\)
  uniformly for every prefix \(y\le N\) (equation (6), "it also bounds
  every prefix"); multiplication of the summand by \(\chi(n)\), by
  \(n^{\beta-1}\), or by a unit phase does not increase it;
- (P4) the level enters the budget only through \(N^2D_0\sqrt Z\) in (17)-(18)
  and through the \(D_0\) terms of (13)-(14), which must be dominated by
  \(NR^{-1/6}\).

No other property of \(B_m\) is used: not the binomial identity (4) beyond
its consequences (P1)-(P3), not the exact value \(m\), not \(\omega(d)\le m\).
In particular (P3) is used only in \(\ell^1\), never in \(\ell^2\); the
\(\ell^2\) objects in section 5 there are \(F\) and \(H\) themselves, with
coefficient bounds \(\ell\) and \(2b\), which the replacement leaves unchanged.

**The replacement.** Let \(\lambda^+_d\) be the upper-bound weights of the
linear (\(\beta=2\)) Rosser sieve of level \(D_0\) for the sifting set
\(\{p<Z\}\): \(\lambda^+_d=\mu(d)\) for \(d\) in Rosser's support
\(\mathcal D^+=\{d=p_1\cdots p_r:\ p_1>\cdots>p_r,\ p_1\cdots p_{l-1}p_l^{\,3}<D_0
\text{ for every odd }l\le r\}\), and \(\lambda^+_d=0\) otherwise. Put
\[
 \Lambda^+(n)=\sum_{\substack{d\mid P,\ d\mid n}}\lambda^+_d .
\]
Then (P1) and (P2) hold by construction (\(d\in\mathcal D^+\) forces \(d<D_0\):
for \(r\) odd take \(l=r\); for \(r\) even take \(l=r-1\) and use
\(p_r<p_{r-1}\)). The two sieve facts used are the ones
`SIEGEL_UNIFORMITY.md` section 3 already cites as TT Lemma 5.1, the
fundamental lemma of sieve theory in the form of Friedlander and Iwaniec,
*Opera de Cribro*, Lemma 6.3, at sieve dimension \(\kappa=1\):

- **one-sidedness**, \(\Lambda^+(n)\ge1_{(n,P)=1}\) for every \(n\), the
  defining property of an upper-bound sieve;
- **the fundamental lemma**: for a sequence \((a_n)\) with
  \(\sum_{d\mid n}a_n=Xg(d)+r_d\), \(g\) multiplicative,
  \(\prod_{w\le p<z}(1-g(p))^{-1}\le K(\log z/\log w)^\kappa\), and level
  \(D=Z^s\) with \(s\ge9\kappa+1\),
  \[
   \sum_na_n\Lambda^\pm(n)=XV_g(Z)\big(1+O(e^{9\kappa-s}K^{10})\big)+O\Big(\sum_{d<D}|r_d|\Big),
   \qquad V_g(Z)=\prod_{p<Z}(1-g(p)),
  \tag{FL}
  \]
  and the same for the sifted sum \(\sum_{(n,P)=1}a_n\), which lies between
  the two.

For \(a_n=1_{n\le y}\), \(X=y\), \(g(p)=1/p\), \(|r_d|\le1\), \(K\) absolute
(Mertens), (FL) gives \(\sum_{n\le y}\Lambda^+(n)=yV(Z)(1+O(e^{9-s}))+O(D_0)\)
and \(\#\{n\le y:(n,P)=1\}=yV(Z)(1+O(e^{9-s}))+O(D_0)\). By one-sidedness
the difference is the \(\ell^1\) error, so for every \(y\le N\)
\[
 \sum_{n\le y}\big|b\Lambda^+(n)-\nu(n)\big|
 =b\sum_{n\le y}\big(\Lambda^+(n)-1_{(n,P)=1}\big)
 \ll Ne^{9-s}+bD_0\ll N\exp(-\tfrac12\sqrt\ell\,(1+o(1)))+\sqrt\ell\,N^{1/2},
\tag{6$'$}
\]
which is (P3) with \(c\) any constant below \(1/2\). The three
multiplications in (P3) are by factors of modulus at most \(1\), so they do
not increase a sum of absolute values. Where `ENDPOINT_BOUND.md` had
\(\sum_n|bB_m-\nu|\ll N\exp(-c\sqrt\ell)\) from \(H_Z^{m+1}/(m+1)!\), it now
has (6\('\)) from (FL). (P4) is checked in section 6.

What has changed and why it matters at the endpoint: the Bonferroni device
ties the level to the decay through \(D_0=Z^m\) with \(m>eH_Z\sim e\log Z\),
so \(\log D_0>e(\log Z)^2=e\,\ell^{2\kappa}\), which at \(\kappa=1/2\) is
\(e\ell\): the level is a power of \(N\) above the budget. The
\(\beta\)-sieve decouples the two: the decay is \(e^{-s}\) with
\(s=\log D_0/\log Z\), so any \(D_0=Z^{s}\) with \(s\to\infty\) works, and
\(D_0=N^{1/2}\) gives \(s=\tfrac12\sqrt\ell\) with a full power of \(N\) to
spare in (P4). This is the only step at which the two devices differ, and
it is the step `ENDPOINT_HALF.md` section 2.3 identified as the break.

## 3. Sections 3 to 5 of `ENDPOINT_BOUND.md` at the endpoint, unchanged

With \(B_m\) replaced by \(\Lambda^+\) and \(t=\sqrt\ell\):

- **(8)-(9), major arcs**: use input (1) at the endpoint, established in
  section 4 below with some fixed \(\gamma>0\); (9) reads
  \(\int_{\mathfrak M}(|F|^2-|H|^2)^2\ll N^3\ell^2R^7\exp(-2\gamma\sqrt\ell)\).
- **(10)**: unchanged, needs \(D_0\le N\); holds.
- **(11)**: unchanged, \(\sup_{\mathfrak m}|F|\ll(NR^{-1/2}+N^{4/5})\ell^{5/2}\).
- **the untwisted prefix after (11)**: \(O(b(N/R+D_0)\ell^2+N\exp(-c\sqrt\ell))\)
  with (6\('\)) in place of (6).
- **(13), Case A**: \(|V_s|\ll b[N\log(2D_0)/\sqrt q+D_0\sqrt q\log(2q)]+N\exp(-c\sqrt\ell)
  \ll\ell^{O(1)}[NR^{-1/6}+N^{1/2}e^{\sqrt\ell/2}]+N\exp(-c\sqrt\ell)\),
  using \(q\ge R^{1/3}\) in the first term and \(q<Z\) in the second.
- **(14), Case B**: \(|V_s|\ll\ell^{O(1)}[NR^{-1/2}+N^{1/2}R^{1/6}]+N\exp(-c\sqrt\ell)\).
- **(15)**: \(\sup_{\mathfrak m}|H|\ll\ell^{O(1)}[NR^{-1/6}+N^{1/2}e^{\sqrt\ell/2}]+N\exp(-c\sqrt\ell)\).
- **(16)-(17)**: unchanged in form, giving
  \(\int_{\mathfrak m}(|F|^2-|H|^2)^2\ll\ell^{O(1)}[N^3R^{-1/6}+N^{14/5}+N^{5/2}e^{\sqrt\ell/2}]+N^3\exp(-c\sqrt\ell)\).

Each line is the corresponding line of `ENDPOINT_BOUND.md` with \(D_0\)
and \(t\) substituted; no argument is altered.

## 4. Input (1) at the endpoint, from classical sources

**Claim.** There is a fixed \(\gamma>0\) such that, uniformly over every
progression \(B=\{n\le y:\ n\equiv a\ (\mathrm{mod}\ r)\}\) with \(y\le N\),
\(r\le R=\lfloor\exp(\sigma\sqrt\ell)\rfloor\), and every residue \(a\),
\[
 \Big|\sum_{n\in B}\big(\Lambda(n)-a(n)\big)\Big|\ll N\exp(-\gamma\sqrt\ell).
\tag{1$'$}
\]

*Inputs.* (D) Davenport, *Multiplicative Number Theory*, Chapter 20: for
\(r\le\exp(C\sqrt{\log y})\) and \((a,r)=1\),
\(\psi(y;r,a)=y/\phi(r)-\chi_1(a)\,y^{\beta_1}/(\phi(r)\beta_1)+O(y\exp(-c_3\sqrt{\log y}))\),
where the middle term is present exactly when \(L(s,\chi_1)\) has an
exceptional real zero \(\beta_1\) for a real character \(\chi_1\bmod r\),
induced by a primitive \(\chi_1^*\) of conductor \(q_1\mid r\), and \(c_3\)
depends on \(C\). (Pg) Page's theorem: among all primitive real characters
of conductor at most \(\exp(C\sqrt\ell)\) at most one has a zero
\(\beta>1-c_4/\sqrt\ell\), for \(c_4=c_4(C)\) small. (FL) as in section 2.
(Cmp) Compatibility of the two notions of exceptional zero: TT's threshold
is \(\beta>1-c_0/\log Z=1-c_0/\sqrt\ell\) with \(c_0\) sufficiently small;
choose \(c_0\le c_4\). Then a TT-exceptional zero is the unique Page
exceptional zero, and any real zero of a real \(L(s,\chi')\), conductor
\(<Z\), that is not TT-exceptional has \(\beta'\le1-c_0/\sqrt\ell\), so its
term \(y^{\beta'}/\phi(r)\le N\exp(-c_0\sqrt\ell)\) is absorbed into the
error on the \(\Lambda\) side. Small \(y\): if \(y\le N\exp(-\gamma\sqrt\ell)\)
both sides of (1\('\)) are trivially \(O(y\,\ell)\), so assume
\(\log y\ge\ell/2\), which puts \(r\le R\) inside (D)'s range for
\(C\ge2\sigma\) and makes \(\exp(-c_3\sqrt{\log y})\le\exp(-c_3\sqrt\ell/2)\).

*Case \((a,r)>1\).* Some prime \(p\mid(a,r)\) divides every \(n\in B\), and
\(p\le r<Z\), so \(a(n)=0\) on \(B\); the \(\Lambda\) side counts prime
powers of primes dividing \(r\), at most \(\omega(r)\ell\ll\ell^2\). Done.

*Case \((a,r)=1\), the untwisted part.* \(\sum_{n\in B}\nu(n)=b\,\#\{n\in B:(n,P)=1\}\).
Sieve \(B\) by the primes \(p<Z\): for \(p\mid r\) no \(n\in B\) is divisible
by \(p\), so \(g(p)=0\); for \(p\nmid r\), \(\#\{n\in B:d\mid n\}=y/(rd)+O(1)\)
for \(d\) coprime to \(r\), so \(g(d)=1/d\) and \(X=y/r\). (FL) at level
\(D_0=N^{1/2}\), \(s=\tfrac12\sqrt\ell\ge10\), gives
\(\#\{n\in B:(n,P)=1\}=(y/r)\prod_{p<Z,\,p\nmid r}(1-1/p)\,(1+O(e^{9-s}))+O(D_0)\).
Every prime factor of \(r\) is below \(Z\) (as \(r\le R<Z\)), so
\(b\prod_{p<Z,\,p\nmid r}(1-1/p)=\prod_{p\mid r}(1-1/p)^{-1}=r/\phi(r)\), and
\[
 \sum_{n\in B}\nu(n)=\frac y{\phi(r)}\big(1+O(e^{9-s})\big)+O(bD_0)
 =\frac y{\phi(r)}+O\big(N\exp(-\tfrac12\sqrt\ell\,(1+o(1)))\big).
\]
This matches the main term of (D).

*Case \((a,r)=1\), the twisted part, present only with a TT-exceptional
\(\chi\) of conductor \(q<Z\).* Write \(T(u)=\sum_{n\in B,\,n\le u,\,(n,P)=1}\chi(n)\).
Since \(u\mapsto u^{\beta-1}\) is positive, decreasing, and of total
variation at most \(1\) on \([1,y]\), Abel summation gives
\(\sum_{n\in B,(n,P)=1}\chi(n)n^{\beta-1}=\int_1^yu^{\beta-1}\,dT(u)\), and it
suffices to evaluate \(T(u)\) for \(u\le y\).

If \(q\mid r\): \(\chi(n)=\chi(a)\) on \(B\) (a character mod \(q\) is
constant on a class mod \(r\)), so \(T(u)=\chi(a)\#\{n\in B,n\le u,(n,P)=1\}\),
and by the untwisted computation at every \(u\),
\(b\int_1^yu^{\beta-1}dT(u)=\chi(a)\frac{y^\beta-1}{\phi(r)\beta}(1+O(e^{9-s}))+O(bD_0)\).
By (Cmp) and (Pg), \(\chi\) is the primitive character inducing (D)'s
\(\chi_1\) mod \(r\), with \(\beta=\beta_1\), so this matches (D)'s middle
term up to \(O(N\exp(-\tfrac12\sqrt\ell(1+o(1))))\).

If \(q\nmid r\): put \(g=\gcd(q,r)<q\). The conditions \(n\equiv a\ (r)\),
\(n\equiv c\ (q)\) with \((c,q)=1\) are compatible exactly when \(c\equiv a\ (g)\),
and then define one class mod \(rq/g\). Sieving each such class as above,
\[
 T(u)=\Big[\frac{ug}{rq}\prod_{p<Z,\,p\nmid rq/g}\Big(1-\frac1p\Big)\Big]\big(1+O(e^{9-s})\big)
 \sum_{\substack{c\bmod q,\ (c,q)=1\\ c\equiv a\ (g)}}\chi(c)
 +O\Big(\frac qg\Big[\frac ugV(Z)e^{9-s}\cdot\frac{g}{r}+D_0\Big]\Big).
\]
The character sum vanishes: it is \(\chi(a')\sum_{c\equiv1\,(g)}\chi(c)\) for
a suitable \(a'\), and a primitive character mod \(q\) is nontrivial on the
kernel of \((\mathbb Z/q)^*\to(\mathbb Z/g)^*\) whenever \(g\) is a proper
divisor of \(q\). Hence \(T(u)\ll(u/r)V(Z)e^{9-s}+qD_0\) and
\(b\int u^{\beta-1}dT\ll Ne^{9-s}+bqD_0\ll N\exp(-\tfrac12\sqrt\ell(1+o(1)))\),
using \(q<Z=e^{\sqrt\ell}\) and \(D_0=N^{1/2}\). On the \(\Lambda\) side, by
(Pg) and (Cmp) no character mod \(r\) is induced by the exceptional
\(\chi\) when \(q\nmid r\), so (D) carries no middle term. Both sides agree
to \(O(N\exp(-\gamma\sqrt\ell))\).

Collecting the three cases, (1\('\)) holds with
\(\gamma=\min(c_3/2,\ c_0,\ 1/2)\) reduced by an \(o(1)\), uniformly in
\(a\), \(r\le R\) and \(y\le N\). This is the statement `ENDPOINT_BOUND.md`
takes from TT Proposition 2.2 at \(\kappa=1/10\); at the endpoint it is the
classical theorem plus the sieve, with no \(\epsilon\)-loss, which is why
Remark 2.8 is not needed.

## 5. Input (2) at the endpoint

`ENDPOINT_HALF.md` section 2.1 verified that `SIEGEL_UNIFORMITY.md`'s model
comparison (10)-(11) survives at \(\kappa=1/2\): its own use of (FL) is at
the free level \(D=\lfloor N^{1/4}\rfloor\), \(s=\log D/\log Z=\tfrac14\sqrt\ell\),
sieve dimension \(2\), remainder \(O(Ne^{-c\sqrt\ell})\); and the
singular-series truncation \(|\mathfrak S(h)-\sigma_Z(h)|\ll\omega(h)/Z\ll\ell e^{-\sqrt\ell}\)
contributes \(O(N\ell e^{-\sqrt\ell})\) per shift. So (2) reads
\(r_a(h)=C_N(h)+O(N\exp(-c_m\sqrt\ell))\) uniformly in \(h\), and (3) reads
\(E_{\rm corr}\le2D+O(N^3\exp(-2c_m\sqrt\ell))\). `EXCEPTIONAL_ENERGY.md`'s
range bookkeeping becomes \((\log q)^2<\log N\), i.e. \(q<Z\), as
`ENDPOINT_HALF.md` section 2.2 records.

## 6. The budget at the endpoint

Combining (3), (9) and (17) as in `ENDPOINT_BOUND.md` section 6, with
\(t=\sqrt\ell\), \(R=\lfloor\exp(\sigma\sqrt\ell)\rfloor\), \(D_0=\lfloor N^{1/2}\rfloor\):
\[
 E_{\rm corr}(N)\ll\ell^{O(1)}\Big[N^3e^{-(2\gamma-7\sigma)\sqrt\ell}
 +N^3e^{-\sigma\sqrt\ell/6}+N^{14/5}+N^{5/2}e^{\sqrt\ell/2}\Big]
 +N^3e^{-c\sqrt\ell}+N^3e^{-2c_m\sqrt\ell}.
\tag{18$'$}
\]
Take \(\sigma=\min(\gamma/20,1/20)\). Then every term is
\(N^3\exp(-c'\sqrt\ell)\) for \(c'=\tfrac12\min(2\gamma-7\sigma,\ \sigma/6,\ c,\ 2c_m)\)
and large \(N\): the first two by the choice of \(\sigma\), the third and
fourth because a fixed power of \(N\) below \(N^3\) beats any
\(\exp(-c\sqrt\ell)\), the last two directly. This is (S). Property (P4)
holds with a power of \(N\) to spare: \(N^2D_0\sqrt Z=N^{5/2}e^{\sqrt\ell/2}\)
against the \(N^3e^{-c'\sqrt\ell}\) it must fit under, and in (13)-(14)
\(D_0\sqrt Z\) and \(D_0R^{1/6}\) are \(N^{1/2+o(1)}\) against \(NR^{-1/6}=N^{1-o(1)}\).

**What now sets the exponent.** With the divisor device out of the way,
\(1/2\) is fixed by three inputs that each carry exactly \(\exp(-c\sqrt\ell)\):
the prime number theorem in progressions with the exceptional term (the
classical zero-free region), the fundamental lemma at level \(Z^{s}\) with
\(s\ll\sqrt\ell\) forced by \(\log D_0\le\ell\), and the singular-series
truncation \(\ell e^{-\sqrt\ell}\) at \(Z=e^{\sqrt\ell}\). Moving past \(1/2\)
would need all three moved: a Vinogradov-Korobov-strength version of (D)
for the moduli \(r\le R\), a model parameter \(Z\) beyond \(e^{\sqrt\ell}\)
with the exceptional-zero bookkeeping of TT Definition 2.1 redone at that
\(Z\), and the level constraint \(s\log Z\le\ell\) then forces
\(s\le\ell/\log Z=o(\sqrt\ell)\), so the sieve error \(e^{-s}\) would fall
below \(e^{-\sqrt\ell}\)-strength. The last is the genuine wall: at
\(Z=\exp(\ell^\kappa)\) with \(\kappa>1/2\), the fundamental lemma at any
level \(D_0\le N\) has \(s\le\ell^{1-\kappa}<\ell^{\kappa}\), and its error
\(e^{-s}\) cannot match \(\exp(-\ell^\kappa)\). Past the endpoint the model
comparison itself, not the divisor device, is what would have to change.
That statement is about this chain, not about other constructions.

**For the original \(E\).** As in `ENDPOINT_BOUND.md` section 7,
\(E\le2E_{\rm corr}+2A_{\rm exc}\), so
\[
 E(N)\ll N^3\exp(-c\sqrt\ell)+1_{q\ {\rm odd}}N^{2\beta+1}\frac{q^2}{\phi(q)^4}+N^{4\beta-1}\frac{q^2}{\phi(q)^3},
\]
the exceptional terms present exactly when a TT-exceptional zero exists at
this \(Z\), and not deletable otherwise.

## 7. Finite check

`endpoint_sharp_probe.py`, results in `results_endpoint_sharp_probe.json`:
\(N=10^6\), \(Z=50\) (fifteen primes, \(V(Z)=0.1387\), \(H_Z=1.662\),
\(eH_Z=4.52\)). Rosser's upper-bound support \(\mathcal D^+\) is enumerated
from its definition at levels \(D_0=Z^s\), \(s=2,\dots,6\), and
\(\Lambda^+\) is compared with the exact indicator on every \(n\le N\):

- coefficients are \(\mu(d)\) on the support, so in \(\{0,\pm1\}\), and every
  \(d\) in the support is below \(D_0\) (P1, P2);
- \(\Lambda^+(n)\ge1_{(n,P)=1}\) at every \(n\le N\) and every level tested
  (one-sidedness);
- the \(\ell^1\) error divided by \(NV(Z)\) is \(0.41,\ 0.043,\ 0.0031,\ 0.0000,\ 0.0000\)
  at \(s=2,3,4,5,6\), against \(e^{-s}=0.135,\ 0.050,\ 0.018,\ 0.0067,\ 0.0025\):
  below \(e^{-s}\) from \(s=3\) on, and the ratio to \(NV(Z)e^{-s}\) falls
  \(3.0,\ 0.87,\ 0.17,\ 0.00,\ 0.00\) (the lemma's \(e^{9-s}K^{10}\) is a far
  weaker statement than what the data show, as expected of a worst-case
  constant);
- Bonferroni at the same levels \(D_0=Z^m\), \(m=2,3,4,5,6\): error over
  \(NV(Z)\) is \(2.57,\ 0.68,\ 0.11,\ 0.0091,\ 0.0001\), one-sided only at
  even \(m\), and it only starts to decay once \(m\) passes \(eH_Z\approx4.5\).
  At equal level \(Z^4\) the \(\beta\)-sieve error is \(37\) times smaller.

These check the four properties and illustrate the mechanism of section 2
at one small \(Z\). They do not test (S), (1\('\)), or any asymptotic
statement.

## 8. Scope

Two substitutions in an existing argument, each resting on a classical
theorem this hunt already cites or that is standard: the fundamental lemma
of sieve theory with Rosser's weights in place of Brun's pure sieve, and the
prime number theorem in progressions with the exceptional term in place of
a cited proposition and an unproved remark. It attains the endpoint
\(\kappa=1/2\) of the corrected CHHL error and names the three inputs that
now fix that exponent. No fixed power saving, no exclusion of exceptional
zeros, no statement about the zeros of \(\zeta\), and no novelty claim.
