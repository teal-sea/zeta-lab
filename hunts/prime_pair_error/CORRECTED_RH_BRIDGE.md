# A signed correction bridge to the Riemann hypothesis

2026-09-09. Base: PR #213 at
284a52fbb369f48fe011578bc7e0299b23b5bce0.
The records in PRs #209-#213 and the completed literature comparison
are unchanged. This pass studies a sufficient criterion, not a new
upper-bound attempt or an extension of the exceptional lower bounds.

**Verdict.** With the exact exceptional correction \(C_N\) of
#212/#213, the alternative family
\[
 E_{\rm corr}(N):=2\sum_{h=1}^N|r_N(h)-C_N(h)|^2
                  \ll_\epsilon N^{2+\epsilon}
 \quad\hbox{for every }\epsilon>0                     \tag{1}
\]
for all sufficiently large integers \(N\) implies RH. The substantive
new ingredient is the uniform signed estimate
\[
 \left|\sum_{h=1}^N C_N(h)\right|
                  \ll N(\log N)^{2/5}.                \tag{2}
\]
It gives the bridge
\[
 \boxed{\quad
 |\psi(N)-N|\ll
             \sqrt{E_{\rm corr}(N)/N}+\log N .
 \quad}                                               \tag{3}
\]
The correction's conductor, zero, and presence may change with \(N\).
No first-moment estimate here uses \(\sum_h|C_N(h)|\) or its second
moment.

This establishes RH-sufficiency only. It neither proves (1) nor an
equivalence with RH, excludes exceptional zeros, bounds original
\(E\) by \(E_{\rm corr}\), or improves the original \(E\).
The original objective is not replaced by this criterion.
This is a handwritten deduction, pending external verification,
without a novelty claim.

## 1. Exact definitions and inherited inputs

The original quantity remains
\[
 \psi_2(N,h)=\sum_{n=1}^{N-h}\Lambda(n)\Lambda(n+h),\quad
 r_N(h)=\psi_2(N,h)-(N-h)\mathfrak S(h),\quad
 E(N)=2\sum_{h=1}^N|r_N(h)|^2.                         \tag{4}
\]
The function \(\Lambda\) includes every proper prime power.
The singular series \(\mathfrak S\) is the original infinite one,
and the endpoint is exactly \(N-h\).

Use Tao and Teräväinen, [arXiv:2107.02158v4](https://arxiv.org/html/2107.02158v4),
Definition 2.1, with its parameter named \(Z\) here:
\[
 L=\log N,\quad Z=e^{L^{1/10}},\quad
 P(Z)=\prod_{p<Z}p,\quad b_Z=P(Z)/\phi(P(Z)).
\]
If a source exceptional zero exists, let \(q,\chi,\beta\) be its data,
so \(q<Z\), \(1-c_0/\log Z<\beta<1\), and \(\chi\) is primitive real.
For sufficiently large \(N\), \(\beta\ge3/4\).
If no such zero exists, set \(C_N(h)=0\) for every \(h\).

The exact correction, inherited from
[SIEGEL_UNIFORMITY.md](SIEGEL_UNIFORMITY.md), is
\[
 C_N(h)=\left(\frac q{\phi(q)}\right)^2 S_*(h)
 \left[-u_q(h)J_1(h)-v_q(h)J_2(h)
                         +\frac{c_q(h)}qJ_{12}(h)\right].       \tag{5}
\]
Here
\[
 \begin{aligned}
 \alpha_p(h)&=\frac{1-\rho_h(p)/p}{(1-1/p)^2},
 &\rho_h(p)&=1\ (p\mid h),\quad 2\ (p\nmid h),\\
 S_*(h)&=\prod_{\substack{p<Z\\p\nmid q}}\alpha_p(h),
 &c_q(h)&=\sum_{a\bmod q}^{*}e(ah/q).
 \end{aligned}
\]
An odd exceptional conductor is squarefree and at least 3.
In that case \(u_q(h)=\mu(q)\chi(-h)/q\) and
\(v_q(h)=\mu(q)\chi(h)/q\). For even primitive-real conductors,
whose 2-part is 4 or 8, both linear averages are zero.

With \(\delta=1-\beta\), the sharp-endpoint weights are
\[
 \begin{aligned}
 f(t)&=\max(1,t)^{-\delta},&g_h(t)&=(t+h)^{-\delta},\\
 J_1(h)&=\int_0^{N-h}f(t)\,dt,&
 J_2(h)&=\int_0^{N-h}g_h(t)\,dt,\\
 J_{12}(h)&=\int_0^{N-h}f(t)g_h(t)\,dt .
 \end{aligned}                                                \tag{6}
\]
All three vanish at \(h=N\).
The extension below \(t=1\) is exactly that used in #212.

The elementary Mertens product bound
\(b_Z\ll\log(2Z)\) is already an input in #212; TT uses
Mertens' theorem in Lemma 2.4 and Section 5.
The prime-counting source used below is
[CHHL, arXiv:2308.14888v1, Section 3](https://arxiv.org/html/2308.14888v1#S3).
Its exact correlation identity and singular-series first moment
were read for this continuation. No distribution estimate beyond
those established inputs is assumed.

## 2. Divisor expansion with the parity factor retained

For odd \(p\nmid q\),
\[
 \alpha_p(h)=\left(1-\frac1{(p-1)^2}\right)
                         \left(1+\frac{1_{p\mid h}}{p-2}\right).
                                                               \tag{7}
\]
Let
\[
 P_*=\prod_{\substack{2<p<Z\\p\nmid q}}p,\quad
 b_*=\prod_{p\mid P_*}\left(1-\frac1{(p-1)^2}\right),\quad
 w(d)=\prod_{p\mid d}\frac1{p-2}\quad(d\mid P_*).
\]
These divisor coefficients are nonnegative, squarefree-supported,
odd, and coprime to \(q\). The exact expansion is
\[
 S_*(h)=
 \begin{cases}
 2\,1_{2\mid h}\,b_*\displaystyle\sum_{\substack{d\mid P_*\\d\mid h}}w(d),
                                                   &q\ {\rm odd},\\
 b_*\displaystyle\sum_{\substack{d\mid P_*\\d\mid h}}w(d),
                                                   &q\ {\rm even}.
 \end{cases}                                                   \tag{8}
\]
In the odd case the factor at 2 is \(2\,1_{2\mid h}\).
In the even case it is absent from \(S_*\); the Ramanujan factor
itself vanishes on odd shifts.

The coefficient mass, including \(b_*\), has an exact simple product:
\[
 b_*\sum_{d\mid P_*}w(d)
  =\prod_{p\mid P_*}
      \left(1-\frac1{(p-1)^2}\right)\left(1+\frac1{p-2}\right)
  =\prod_{p\mid P_*}\frac p{p-1}\le\frac{b_Z}{2}.       \tag{9}
\]
Also \(\sum_{d\mid P_*}w(d)\ll\log(2Z)\):
each factor \((p-1)/(p-2)\) differs from \(p/(p-1)\)
by \(1+1/[p(p-2)]\), whose product converges.
Neither estimate depends on the particular exceptional conductor.

## 3. Cancellation and weighted incomplete sums

A nonprincipal character has zero sum over a full period.
Consequently, for all real \(x\ge0\),
\[
                  \left|\sum_{j\le x}\chi(j)\right|\le q.       \tag{10}
\]
For \(q>1\), the Ramanujan divisor formula gives
\[
 \begin{aligned}
 \sum_{j\le x}c_q(j)
 &=\sum_{a\mid q}a\mu(q/a)\lfloor x/a\rfloor\\
 &=-\sum_{a\mid q}a\mu(q/a)\{x/a\},
 \end{aligned}
\]
because \(\sum_{a\mid q}\mu(q/a)=0\). Thus
\[
 \left|\sum_{j\le x}c_q(j)\right|\le
                \sum_{a\mid q}a=\sigma_1(q).           \tag{11}
\]
Also \(c_q(dj)=c_q(j)\) whenever \((d,q)=1\), directly from the
divisor formula. These assertions hold for the 4- and 8-parts too.
Equations (10)-(11) bound the remaining incomplete period, not
the sum of magnitudes of its terms.

The weights in (6) are nonnegative and decreasing in \(h\).
For \(J_1\) only the interval shrinks. For \(J_2\),
\[
                   J_2(h)=\int_h^N s^{-\delta}\,ds.
 \]
For \(J_{12}\), increasing \(h\) both shrinks the interval and
decreases \(g_h(t)\) at every retained \(t\).
Uniformly for \(\beta\ge3/4\),
\[
 J_1(1),J_2(1)\le\frac43N^\beta,\qquad
 J_{12}(1)\le2N^{2\beta-1}.                            \tag{12}
\]
For the last bound use \(g_1(t)\le f(t)\) and integrate \(f(t)^2\):
\[
 \int_0^N f(t)^2\,dt
 =1+\frac{N^{2\beta-1}-1}{2\beta-1}
 \le\frac{N^{2\beta-1}}{2\beta-1}.
 \]

For completeness, if \(A(j)=\sum_{i\le j}a_i\), \(|A(j)|\le K\),
and \(W_j\) is nonnegative decreasing, discrete partial summation is
\[
 \sum_{j=1}^M a_jW_j
 =A(M)W_M+\sum_{j=1}^{M-1}A(j)(W_j-W_{j+1}),
 \quad
 \left|\sum_{j=1}^M a_jW_j\right|\le K W_1.            \tag{13}
\]
This retains the last endpoint even if the last multiple is below
\(N\). An empty sum is zero. No extension of the sharp cutoff is used.

When \(q\) is odd, insert (8) and put \(h=2dj\).
Since \((2d,q)=1\),
\(\chi(\pm2dj)=\chi(\pm2d)\chi(j)\) and
\(c_q(2dj)=c_q(j)\).
Apply (13) to the three weights \(J_i(2dj)\), using (10)-(12).
The character bound \(q\) cancels the \(1/q\) in \(u_q,v_q\).
The Ramanujan bound contributes \(\sigma_1(q)/q\).
Summing the nonnegative divisor coefficients only after this
cancellation, and using (9), gives
\[
 \left|\sum_{h=1}^N C_N(h)\right|
 \le\left(\frac q{\phi(q)}\right)^2 b_Z
 \left[J_1(1)+J_2(1)+\frac{\sigma_1(q)}qJ_{12}(1)\right].
                                                               \tag{14}
\]

When \(q\) is even, the linear terms are identically zero.
Use \(h=dj\) over all shifts, rather than extracting a step 2:
\((d,q)=1\) now preserves \(c_q(dj)=c_q(j)\).
Odd shifts contribute zero automatically.
The same argument proves (14) with the first two weights removed.
This avoids incorrectly treating 2 as a unit modulo an even conductor.

Together the cases prove the quantitative signed estimate
\[
 \boxed{\quad
 \left|\sum_{h=1}^N C_N(h)\right|
 \le\left(\frac q{\phi(q)}\right)^2 b_Z
 \left[\frac83\,1_{q\ {\rm odd}}N^\beta
       +2\frac{\sigma_1(q)}qN^{2\beta-1}\right].
 \quad}                                                        \tag{15}
\]
In particular this proves the proposed candidate with
\(\log(2Z)\) in place of \(b_Z\).

Since all prime divisors of \(q\) lie below \(Z\),
\[
 \frac{\sigma_1(q)}q
 =\prod_{p^a\parallel q}(1+p^{-1}+\cdots+p^{-a})
 \le\frac q{\phi(q)}\le b_Z.
 \]
Also \(N^\beta,N^{2\beta-1}\le N\). Thus, for example,
\[
 \left|\sum_h C_N(h)\right|
 \le \frac{14}{3}N b_Z^4
 \ll N(\log(2Z))^4
 \ll N(\log N)^{2/5},                                 \tag{16}
\]
which is (2). The no-exception case is identically zero.
All constants are uniform across changes of \(q,\chi,\beta\) with \(N\);
partial summation above was in the shift variable for each fixed \(N\).

## 4. The exact bridge to prime counting

CHHL Section 3 starts from the exact identity
\[
 \psi(N)^2=d_N+2\sum_{h=1}^N\psi_2(N,h),\qquad
 d_N=\sum_{n\le N}\Lambda(n)^2.
 \]
It uses the established singular-series first moment
\[
                2\sum_{h=1}^N(N-h)\mathfrak S(h)
                         =N^2+O(N\log N).
 \]
Together with \(d_N=O(N\log N)\), also stated in CHHL, this gives
\[
                 \psi(N)^2-N^2=2\sum_{h=1}^N r_N(h)+O(N\log N).
                                                               \tag{17}
\]
Proper prime powers, the diagonal \(d_N\), and both signs of every
nonzero difference have all been accounted for.

Insert \(r_N=(r_N-C_N)+C_N\). Apply Cauchy-Schwarz only to the
first vector:
\[
 2\left|\sum_h(r_N(h)-C_N(h))\right|
 \le 2\sqrt{N\sum_h|r_N(h)-C_N(h)|^2}
 =\sqrt{2N E_{\rm corr}(N)}.
 \]
Therefore
\[
 |\psi(N)^2-N^2|
 \le\sqrt{2N E_{\rm corr}(N)}
             +2\left|\sum_h C_N(h)\right|+O(N\log N).
 \]
The denominator \(\psi(N)+N\) is at least \(N\), since \(\Lambda\ge0\).
No approximation to this denominator is needed. Hence
\[
 \boxed{\quad
 |\psi(N)-N|
 \le \sqrt{\frac{2E_{\rm corr}(N)}N}
       +\frac2N\left|\sum_h C_N(h)\right|+O(\log N).
 \quad}                                                        \tag{18}
\]
Now (16) proves (3). In particular \(B=1\) suffices for the logarithm
in the requested prime-counting bridge.

## 5. Epsilon quantifiers, real endpoints, and RH

Assume (1). For any fixed \(\theta>0\), choose
\(\epsilon=2\theta\) in that hypothesis. Equation (3) gives
\[
          \psi(N)-N=O_\theta(N^{1/2+\theta})
 \]
for all sufficiently large integers \(N\).
For real \(x\ge2\), put \(N=\lfloor x\rfloor\).
Then \(\psi(x)=\psi(N)\) and \(0\le x-N<1\), so
\[
                \psi(x)-x=O_\theta(x^{1/2+\theta})
                 \quad\hbox{for every }\theta>0.       \tag{19}
\]
No extension or regularity of \(C_N\) between integers is required.

Here is the usual analytic implication, to specify exactly what is
being used. The Euler product and integration of the von Mangoldt
Dirichlet series give, for \({\rm Re}\,s>1\),
\[
 -\frac{\zeta'(s)}{\zeta(s)}
 =s\int_1^\infty\psi(x)x^{-s-1}\,dx
 =\frac{s}{s-1}
       +s\int_1^\infty(\psi(x)-x)x^{-s-1}\,dx.          \tag{20}
\]
For each half-plane \({\rm Re}\,s>1/2+\theta\), (19) makes the last
integral holomorphic there, with local uniform convergence.
As \(\theta>0\) is arbitrary, (20) continues
\(-\zeta'/\zeta-s/(s-1)\) holomorphically to \({\rm Re}\,s>1/2\).
A zero of \(\zeta\) there would give a pole, which is impossible.
The functional equation reflects nontrivial zeros across the
critical line, so all nontrivial zeros have real part \(1/2\).
This proves the asserted RH implication.

## 6. What is currently proved for the alternative target

The vector bound inherited from #212 and recorded in #213 says
\[
 \|r_N-C_N\|_{\pm,2}
       \le K_\kappa N^{3/2}e^{-c_\kappa(\log N)^\kappa},
 \qquad 0<\kappa<1/10.
 \]
Consequently it already proves, unconditionally for the chosen
source correction at each \(N\),
\[
 E_{\rm corr}(N)\le
 K_\kappa^2N^3e^{-2c_\kappa(\log N)^\kappa}.             \tag{21}
\]
This is \(N^{3-o(1)}\), not a fixed power saving.
The near-quadratic family (1) is unproved; the exponent gap is still
essentially one power of \(N\). The bridge is established, not its
input estimate. No upper estimate for original \(E\) is inferred
by deleting or reversing the exceptional correction.

The source inputs are the exact correction and residual bounds from
#212/#213, the Mertens product bound used there, and CHHL's
correlation identity, diagonal bound, and singular-series first moment.
Equations (8)-(16), (18), and the criterion implication are deductions
in this continuation. The historical exceptional lower-bound and
literature-comparison tasks remain concluded.

## 7. Bounded identity checks

The argument was completed before its diagnostic. The fixed script
at artifacts/corrected_rh_bridge/check.py uses \(N=128\), one numerical
thread, and a 60-second cap. Fixed odd, 4-part, and 8-part fixtures
test the divisor expansion, coefficient mass, complete-period
cancellation, incomplete Ramanujan bound, monotone weights, Abel
identity, and signed first moment. Toy zero parameters assert no
exceptional-zero existence.

The exact correlation identity includes all 13 proper prime powers
at this cutoff. A finite bridge check keeps the singular-series
comparison remainder explicitly and does not numerically assert
the infinite-series asymptotic or RH. Proof, script, and parent
hashes accompany the saved output. No earlier diagnostic is rerun.
