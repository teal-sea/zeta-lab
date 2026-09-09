# Exceptional energy and the original total prime-pair error

2026-09-09. Continuation of PR #212 at
76ed1155d087d9137306d3632f66dba7555aadc3.
SIEGEL_UNIFORMITY.md and the completed records in PRs #209-#211 are unchanged.

**Result.** The quadratic exceptional term from #212 has a matching
lower bound in the explicit correction energy. For the actual exceptional
data in the source's range, for sufficiently large \(N\),
\[
 \left|\sqrt{E(N)}-\sqrt{\mathcal A_{\rm exc}}\right|
 \le \Xi_\kappa(N):=K_\kappa N^{3/2}e^{-c_\kappa(\log N)^\kappa},
 \qquad 0<\kappa<1/10,                                  \tag{1}
\]
and
\[
 \mathcal A_{\rm exc}:=2\sum_{h=1}^N|C_{q,\beta,Z}(h)|^2
 \ \ge\ \frac1{192}N^{4\beta-1}\frac{q^2}{\phi(q)^3}.
                                                               \tag{2}
\]
The elementary proof of (2) only needs \(N\ge8q\), \(Z>2\), and
\(0<\beta<1\), besides the stated conductor structure. The source's
range implies these conditions eventually. In the no-exception case
we define \(C=0\), so \(\mathcal A_{\rm exc}=0\) and (1) still holds;
(2) is asserted only when an exceptional zero exists.

Consequently the original prime quantity satisfies
\[
 \boxed{\quad
 \sqrt{E(N)}\ge
 \left[\frac1{\sqrt{192}}N^{2\beta-1/2}
          \frac q{\phi(q)^{3/2}}-\Xi_\kappa(N)\right]_+ .
 \quad}                                                        \tag{3}
\]
Section 5 gives the precise regime where this lower estimate is
positive and where it detects a fixed fraction of the quadratic scale.
This is a handwritten deduction, pending external verification.
There is no novelty claim.

## 1. Original target, inherited input, and exact correction

Use the original CHHL convention, as in
[UPPER_BOUND.md](UPPER_BOUND.md):
\[
 \psi_2(N,h)=\sum_{n=1}^{N-h}\Lambda(n)\Lambda(n+h),\qquad
 r(h)=\psi_2(N,h)-(N-h)\mathfrak S(h),\qquad
 E(N)=2\sum_{h=1}^N|r(h)|^2.                            \tag{4}
\]
Here \(\Lambda(p^j)=\log p\) for every \(j\ge1\), and
\(\mathfrak S\) is the original infinite singular series. Neither
the function nor the prediction is changed.

The source is Tao and Teräväinen, [Quantitative bounds for Gowers
uniformity of the Möbius and von Mangoldt functions, arXiv:2107.02158v4,
9 November 2023](https://arxiv.org/html/2107.02158v4), abbreviated TT.
Its Definition 2.1 and Theorem 2.7 were checked again on 2026-09-09
for the range used here. The source is consumed through the deductions
already proved in [SIEGEL_UNIFORMITY.md](SIEGEL_UNIFORMITY.md), not
through a new uniformity theorem.

Write
\[
 L=\log N,\quad Z=e^{L^{1/10}},\quad
 P(Z)=\prod_{p<Z}p,\quad
 \nu(n)=\frac{P(Z)}{\phi(P(Z))}1_{(n,P(Z))=1}.
\]
When the exceptional data exist, they satisfy
\[
 q<Z,\qquad 1-\frac{c_0}{\log Z}<\beta<1,\qquad
 L(\beta,\chi)=0,                                      \tag{5}
\]
where \(\chi\) is the primitive real character in TT Definition 2.1
and \(c_0\) is the source's sufficiently small fixed constant.
The model is \(a(n)=\nu(n)(1-n^{\beta-1}\chi(n))\).
Without an exceptional zero it is \(a(n)=\nu(n)\).
Set \(F=\sum_{n\le N}\Lambda(n)e(n\alpha)\) and
\(H=\sum_{n\le N}a(n)e(n\alpha)\).

For precision, the complete correction inherited from #212 is
\[
 \begin{split}
 \rho_h(p)&=1_{p\mid h}+2\,1_{p\nmid h},&
 \alpha_p(h)&=\frac{1-\rho_h(p)/p}{(1-1/p)^2},\\
 S_*(h)&=\prod_{\substack{p<Z\\p\nmid q}}\alpha_p(h),&
 C(h)&=\left(\frac q{\phi(q)}\right)^2 S_*(h)
 \left[-u_q(h)J_1(h)-v_q(h)J_2(h)
                         +\frac{c_q(h)}q J_{12}(h)\right].
 \end{split}                                                    \tag{6}
\]
Here \(c_q(h)=\sum_{a\bmod q}^*e(ah/q)\), and, putting
\(\delta=1-\beta\), \(T=N-h\),
\[
 \begin{split}
 f(t)&=\max(1,t)^{-\delta},&g_h(t)&=(t+h)^{-\delta},\\
 J_1(h)&=\int_0^T f(t)\,dt,&
 J_2(h)&=\int_0^T g_h(t)\,dt,&
 J_{12}(h)&=\int_0^T f(t)g_h(t)\,dt .
 \end{split}                                                    \tag{7}
\]
The extension to \(t<1\) fixes the endpoint and equals the actual
model factors at every integer \(n\ge1\).
For odd \(q\),
\[
 u_q(h)=\mu(q)\chi(-h)/q,\qquad
 v_q(h)=\mu(q)\chi(h)/q;                                \tag{8}
\]
for even primitive-real \(q\), both are zero. These finite identities,
including the 4- and 8-parts, are proved in #212.

Such an odd conductor is squarefree and at least 3; an even conductor
is \(4r\) or \(8r\), with \(r\) odd squarefree. Conductor one cannot
supply the zero in (5): for \(0<s<1\), the alternating series
\(\sum_{n\ge1}(-1)^{n-1}n^{-s}\) is positive and equals
\((1-2^{1-s})\zeta(s)\), so \(\zeta(s)<0\).

## 2. The vector estimate before reverse triangle inequality

Give a vector indexed by \(1\le h\le N\) the norm
\[
             \|x\|_{\pm,2}:=\left(2\sum_{h=1}^N|x(h)|^2\right)^{1/2}.
\]
Define \(r_a(h)=\sum_{n\le N-h}a(n)a(n+h)-(N-h)\mathfrak S(h)\).
Write the two inputs proved in #212 with distinct constants:
\[
 \begin{split}
 \mathcal D
 &:=\|\mathcal C(|F|^2-|H|^2)\|_2^2
       \le A_\kappa N^3e^{-d_\kappa L^\kappa},\\
 |r_a(h)-C(h)|&\le B N e^{-bL^{1/10}}
                    \qquad(1\le h\le N).              \tag{9}
 \end{split}
\]
All these constants are positive and have the effectivity of the
source results. Here \(\mathcal C\) removes the constant Fourier
coefficient. The first estimate uses TT's arithmetic \(U^2\)
control and the integrated transfer from #212. The second is its
uniform model-to-original-singular-series estimate, including the
sharp endpoint.

Parseval gives the exact identity
\[
                       \|r-r_a\|_{\pm,2}=\sqrt{\mathcal D}.
\]
No model subtraction is dropped: the singular-series terms cancel in
this vector difference. Therefore
\[
 \begin{split}
 \|r-C\|_{\pm,2}
 &\le \|r-r_a\|_{\pm,2}+\|r_a-C\|_{\pm,2}\\
 &\le N^{3/2}\left[
      \sqrt{A_\kappa}e^{-(d_\kappa/2)L^\kappa}
          +\sqrt2 B e^{-bL^{1/10}}\right]\\
 &\le K_\kappa N^{3/2}e^{-c_\kappa L^\kappa},           \tag{10}
 \end{split}
\]
where, for \(L\ge1\), one may take
\[
 c_\kappa=\min(d_\kappa/2,b),\qquad
 K_\kappa=\max(1,\sqrt{A_\kappa}+\sqrt2 B).
                                                               \tag{11}
\]
This explicitly accounts for the halving of the exponent constant
on taking a square root. Reverse triangle inequality applied to
(10) proves (1). Equivalently,
\[
 [\sqrt{\mathcal A_{\rm exc}}-\Xi_\kappa]_+^2
 \le E(N)\le(\sqrt{\mathcal A_{\rm exc}}+\Xi_\kappa)^2. \tag{12}
\]
The vector (4) still contains odd shifts, proper prime powers, and
the zero endpoint \(h=N\). The shift restriction below is used only
to lower-bound \(\mathcal A_{\rm exc}\).

## 3. A set of shifts where the linear corrections vanish

Let
\[
 \mathcal H=\{h\in\mathbb Z:N/4\le h\le N/2,\ 2\mid h\},
\]
and let \(\mathcal H_q\) consist of the members of \(\mathcal H\)
with \((h,q)>1\) if \(q\) is odd. For even \(q\), set
\(\mathcal H_q=\mathcal H\).
For odd \(q\), the Dirichlet character vanishes at these \(h\), so
(8) removes both linear corrections. For even \(q\), those corrections
already vanish. Thus on every selected shift,
\[
 C(h)=\left(\frac q{\phi(q)}\right)^2 S_*(h)
                                  \frac{c_q(h)}q J_{12}(h).
                                                               \tag{13}
\]

There are uniform elementary lower bounds for its other factors:
\[
                    S_*(h)\ge\frac12,\qquad
                    J_{12}(h)\ge\frac12N^{2\beta-1}.
                                                               \tag{14}
\]
For the first, at an odd prime
\[
 \alpha_p(h)=
 \begin{cases}
 p/(p-1)>1,&p\mid h,\\
 1-(p-1)^{-2},&p\nmid h.
 \end{cases}
\]
At \(p=2\), an even shift has factor 2 if that prime is included.
Discarding factors greater than 1, and adjoining all missing factors
\(1-m^{-2}\), \(m=2,3,\ldots\), can only decrease the product.
The finite telescoping identity
\[
 \prod_{m=2}^R(1-m^{-2})=\frac{R+1}{2R}
\]
then gives \(S_*(h)\ge1/2\). This argument is independent of \(q,Z,h\).

For the second bound, \(T=N-h\ge N/2\), and throughout \(0\le t\le T\)
both \(\max(1,t)\) and \(t+h\) are at most \(N\). Since \(\delta>0\),
\(f(t)g_h(t)\ge N^{-2\delta}\). Integration gives
\(J_{12}(h)\ge(N/2)N^{-2\delta}\), exactly as in (14).

## 4. Complete-period mass and the retained end errors

Write \(h=2j\) and put
\[
 a=\lceil N/8\rceil,\quad b_0=\lfloor N/4\rfloor,\quad
 m=b_0-a+1\ge\lfloor N/8\rfloor.                       \tag{15}
\]

For odd squarefree \(q\ge3\), \(c_q(2j)=c_q(j)\) and
\((2j,q)=(j,q)\). Finite Fourier orthogonality gives
\(\sum_{j\bmod q}c_q(j)^2=q\phi(q)\).
If \((j,q)=1\), then \(c_q(j)=\mu(q)\); those \(\phi(q)\) residues
each contribute exactly 1. Hence the retained period mass is
\[
 P_q:=\sum_{\substack{j\bmod q\\(j,q)>1}}c_q(j)^2
                                      =(q-1)\phi(q). \tag{16}
\]
Writing \(m=kq+s\), \(0\le s<q\), the actual sum is
\[
 \sum_{h\in\mathcal H_q}c_q(h)^2=kP_q+R,\quad
 0\le R\le P_q,\qquad
 \left|\sum_{h\in\mathcal H_q}c_q(h)^2-\frac m qP_q\right|
 \le P_q.                                             \tag{17}
\]
This uses consecutive complete periods starting at \(a\), so no
alignment of the left endpoint is assumed. Since
\(\lfloor m/q\rfloor\ge\lfloor N/(8q)\rfloor\) and
\(\lfloor x\rfloor\ge x/2\) for \(x\ge1\),
\[
 \sum_{h\in\mathcal H_q}c_q(h)^2
 \ge\frac N{16q}(q-1)\phi(q)
 \ge\frac{N\phi(q)}{24}\qquad(N\ge8q).                 \tag{18}
\]

For even primitive-real \(q\), write \(q=4r\) or \(q=8r\), with
\(r\) odd squarefree. The exact local formulas are
\[
 c_{4r}(2j)^2=4c_r(j)^2,\qquad
 c_{8r}(2j)^2=16\,1_{2\mid j}c_r(j)^2.                \tag{19}
\]
They follow by multiplicativity of Ramanujan sums and by evaluating
the 4- and 8-factors. Both squared sequences have period \(d=q/4\);
their complete-period mass is
\[
                       P_q=\frac{q\phi(q)}2.           \tag{20}
\]
Indeed the \(4r\) case sums to \(4r\phi(r)\). In the \(8r\) case,
the even \(j\) in a period of length \(2r\) cover all residues
modulo \(r\), giving \(16r\phi(r)\). These statements include \(r=1\).
Thus
\[
 \begin{split}
 \sum_{h\in\mathcal H}c_q(h)^2
     &=\lfloor m/d\rfloor P_q+R,\qquad 0\le R\le P_q,\\
 \left|\sum_{h\in\mathcal H}c_q(h)^2-2m\phi(q)\right|
     &\le q\phi(q)/2,\\
 \sum_{h\in\mathcal H}c_q(h)^2
     &\ge\frac{N\phi(q)}8\qquad(N\ge2q).
 \end{split}                                                    \tag{21}
\]
For the last line use
\(\lfloor m/d\rfloor\ge\lfloor N/(2q)\rfloor\ge N/(4q)\).
In particular the common lower bound \(N\phi(q)/24\) holds
for all cases when \(N\ge8q\).

Now combine (13), (14), (18), and (21), keeping the original factor 2:
\[
 \begin{split}
 \mathcal A_{\rm exc}
 &\ge 2\sum_{h\in\mathcal H_q}|C(h)|^2\\
 &\ge\frac18 N^{4\beta-2}\frac{q^2}{\phi(q)^4}
                              \sum_{h\in\mathcal H_q}c_q(h)^2\\
 &\ge\frac1{192}N^{4\beta-1}\frac{q^2}{\phi(q)^3}.
 \end{split}                                                    \tag{22}
\]
This proves (2), rather than inferring it from the upper estimate.
There is no cancellation with the two linear terms on the selected set.

## 5. When the lower estimate detects an error for actual primes

Let
\[
 \Delta_q(N,\beta)=2(1-\beta)L+\frac32\log\phi(q)-\log q.
\]
The right side of (3) is positive whenever
\[
 \Delta_q(N,\beta)<c_\kappa L^\kappa
                              -\log(\sqrt{192}K_\kappa).
                                                               \tag{23}
\]
More quantitatively, under
\[
 \Delta_q(N,\beta)\le c_\kappa L^\kappa
                              -\log(2\sqrt{192}K_\kappa),
                                                               \tag{24}
\]
the transfer error is at most half the signal, and
\[
             E(N)\ge\frac1{768}N^{4\beta-1}
                                      \frac{q^2}{\phi(q)^3}.
                                                               \tag{25}
\]
A simpler sufficient condition, for sufficiently large \(N\), is
\[
 2(1-\beta)L+\tfrac12\log q\le\tfrac12c_\kappa L^\kappa,
                                                               \tag{26}
\]
because \(\phi(q)\le q\), and the remaining half of the exponential
eventually absorbs the constant in (24).
The source range (5) alone does not imply any of (23)-(26).
Outside the positivity regime no detection of the quadratic
contribution for actual primes is claimed.

Every use of (1), (3), or (25) remains inside TT's \(N\)-dependent
range. In particular, for a specified pair \(q,\beta\) with
\(\delta=1-\beta>0\), (5) restricts
\[
                  (\log q)^{10}<\log N<(c_0/\delta)^{10}.
                                                               \tag{27}
\]
The additional large-\(N\) thresholds, \(N\ge8q\), and the detection
condition must also hold. There is no fixed-conductor asymptotic
obtained by sending \(N\) to infinity past the upper endpoint of (27).

The consequence for the original upper-bound objective is limited but
concrete: in the regime (24), the quadratic scale in #212 is present
in the actual total \(E(N)\), so a sharper triangle inequality cannot
delete it while leaving the arithmetic approximation unchanged.
This does not establish an exceptional zero, exclude one, prove RH,
or improve the uniform unconditional upper bound.
The upper estimate from #212 and the established
\(E(N)\ll_A N^3/(\log N)^A\) both remain available with their stated scopes.

## 6. Evidence and division between inputs and deductions

TT supplies the exceptional model/range, arithmetic uniformity, and
sieve theorem used in #212. This continuation uses the two quantified
consequences (9). The vector estimate (10), the lower factors (14),
the incomplete-period formulas (17), (21), the energy lower bound
(22), and the parameter implications (23)-(27) are deductions here.
No new prime-distribution hypothesis or unproved estimate is inserted.
The source check is an application/range check, not a novelty search.

The bounded diagnostic at artifacts/exceptional_energy/check.py has
one fixed cutoff \(N=128\), one numerical thread, and a 60-second cap.
Three fixed local fixtures represent odd conductor, 4-part, and 8-part.
It checks their exact period masses and truncated-period errors,
then checks the lower factors and full correction energy for \(q=3\)
with a toy \(\beta\). No zero is asserted to exist. The even-conductor
fixtures test finite local algebra only, not the source's \(q<Z\)
condition at this small \(N\).
The finite norm check uses the explicitly labeled truncated Euler
product and retains its errors; it does not claim a numerical value
for the original infinite-singular-series \(E(N)\).
The proofs above, not that fixture, supply the transfer to the
original target. Proof, script, and parent proof hashes accompany
the saved output. Earlier diagnostics are unchanged and are not rerun.
