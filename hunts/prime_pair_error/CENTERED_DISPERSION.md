# Centered dispersion through a finite Ramanujan model

2026-09-09. Base: `2da62eb9842db72d4f6bad09c6f13efe384d6ab7`.
PRs #209 and #210 are completed, separate attempts and are unchanged.

**Outcome.** This attempt does not improve the bound for total CHHL error.
It cancels the rational diagonal before estimating a shifted correlation,
obtaining a uniform remainder of size \(O(R^2)\) for the finite Ramanujan
model. Its complete centered model error is \(O(NR^4+N^3/R^2)\), hence
\(O(N^{7/3})\) at \(R=\lfloor N^{1/3}\rfloor\). The attempted transfer to
the actual primes retains the mixed terms, but its proved upper bound is
only \((8/3+o(1))N^3\log N\). The precise loss is evaluated below.
The previously proved \(E(N)\ll_C N^3/(\log N)^C\), for every fixed \(C\),
remains the stronger unconditional result. Neither bound is an improvement
of that result.

The arguments here are handwritten, with bounded algebraic and numerical
checks. There is no novelty or formal-proof claim. In particular, the
Ramanujan approximant itself already appears in CHHL, Section 7.

## 1. Centering and the actual arithmetic coefficients

Let \(N\ge36\) be an integer, \(L=\log N\), \(y=\lfloor\sqrt N\rfloor\),
\(e(t)=\exp(2\pi it)\), and \(\mathcal C f=f-\int_{\mathbb T}f\).
Use \(F_N,K_N,V_z,d_N,a_0(N,z),\mathfrak S_z\) exactly as in
`UPPER_BOUND.md`. In particular,
\[
 G_y=\mathcal C(|F_N|^2-V_y),\qquad
 \|G_y\|_2^2=2\sum_{h=1}^N
 [\psi_2(N,h)-(N-h)\mathfrak S_y(h)]^2.                 \tag{1}
\]
Its expansion is
\[
 \|G_y\|_2^2=\int|F_N|^4-2\int|F_N|^2V_y
                  +\int V_y^2-a_0(N,y)^2.             \tag{2}
\]
The sign of the constant term follows by applying the orthogonal
projection \(\mathcal C\). No three separate upper bounds are applied to
the large integrals in (2).

For later use put
\[
 D_z=2\sum_{h=1}^N(N-h)^2
               |\mathfrak S(h)-\mathfrak S_z(h)|^2.
\]
The established tail comparison is
\[
 |\sqrt E-\|G_y\|_2|\le\sqrt{D_y},\qquad
 D_z\ll N^3/z^2\quad(1\le z\le\sqrt N).                \tag{3}
\]
Thus \(E\le2\|G_y\|_2^2+O(N^2)\). The tail sum in
[GHN Theorem 2](https://arxiv.org/html/1409.2151#S1.Thmtheorem2)
is one-sided; \(D_z\) is twice that sum. This is the normalization in
`UPPER_BOUND.md`, not a new normalization argument.

Keep \(U=V=\lfloor N^{2/5}\rfloor\). With Dirichlet convolution,
\[
 \Lambda=\Lambda_{\le V}+\mu_{\le U}*\log
 -\mu_{\le U}*1*\Lambda_{\le V}
 +\mu_{>U}*1*\Lambda_{>V}.                              \tag{4}
\]
Indeed \(\log=1*\Lambda\) and \(\mu*1=\delta\), so the last three
terms sum to \(\Lambda_{>V}\). Let \(a_t,b_t\) be the actual coefficients
of \(A=S_0+T_{\log}-T_{\rm prod}\) and \(B=T_{\rm II}\). Explicitly,
\[
\begin{split}
 a_t={}&1_{t\le V}\Lambda(t)
  +\sum_{d\mid t,d\le U}\mu(d)\log(t/d)
  -\sum_{dc\mid t,d\le U,c\le V}\mu(d)\Lambda(c),\\
 b_t={}&\sum_{m\mid t,m>U}\mu(m)
                   \sum_{c\mid(t/m),c>V}\Lambda(c).
\end{split}                                                    \tag{5}
\]
All sums have \(t\le N\). Before any norm estimate, group by this total
integer \(t\), so \(a_t+b_t=\Lambda(t)\). For distinct primes \(p,q>U\),
\(a_{pq}=\log p+\log q\) and \(b_{pq}=-\log p-\log q\). For \(p>U\),
\(a_{p^2}=2\log p\), \(b_{p^2}=-\log p\). The surviving square coefficient
is \(\log p\). All higher prime powers remain in (4) as well.

This grouping makes every Type I and Type II coefficient participate.
There is no blockwise fourth-power inequality and no dyadic recombination
cost. The boundary cancellation is bookkeeping for the following estimate.

## 2. The dispersion grouping and its uniform remainder

Introduce an auxiliary integer \(2\le R\le y\), without changing \(U,V\):
\[
 \lambda_R(t)=\sum_{q\le R}\frac{\mu(q)}{\phi(q)}c_q(t),
 \qquad H_R(\alpha)=\sum_{t\le N}\lambda_R(t)e(t\alpha),
 \qquad h_R=\sum_{q\le R}\frac{\mu(q)^2}{\phi(q)}.
                                                               \tag{6}
\]
This is [CHHL (19)-(20)](https://arxiv.org/html/2308.14888v1#S7),
with their \(\mathscr S_R\) called \(H_R\) here. The evenness of \(c_q\)
makes its sign convention identical. Equivalently,
\[
 H_R(\alpha)=\sum_{x=a/q\in\mathcal F_R}w_x K_N(\alpha-x),
 \quad w_{a/q}=\mu(q)/\phi(q),                           \tag{7}
\]
where \(\mathcal F_R\) contains each reduced fraction modulo one once,
including \(0/1\). Zero weights may be retained.

For arbitrary integers \(T\ge0\) and \(h\), expand the shifted product
using the conjugate representation of the second real factor:
\[
 \sum_{n=1}^T\lambda_R(n)\lambda_R(n+h)
 =T\mathfrak S_R(h)+\eta_R(T,h),
\quad
 \eta_R(T,h)=\sum_{x\ne z}w_xw_z e(-hz)K_T(x-z).
                                                               \tag{8}
\]
The equal-frequency terms give exactly \(T\mathfrak S_R(h)\). They
cancel the entire proposed model coefficient before absolute values.
Both rational-frequency variables still vary in the remainder.

Here is a bound for the signed remainder, uniform even for \(T=0\):
\[
 \boxed{\ |\eta_R(T,h)|\le B_R,
 \quad B_R=\frac32 R\sum_{q\le R}\frac{\mu(q)^2q}{\phi(q)}
                    \le\frac32 C_0R^2,\quad
 C_0=\sum_{d\ge1}\frac{\mu(d)^2}{d\phi(d)}<\infty.\ }   \tag{9}
\]
For the proof, let \(\delta_x\) be the distance from \(x\) to its nearest
other point of \(\mathcal F_R\). If \(x=a/q\), then
\(\delta_x\ge1/(qR)\). The weighted circular Hilbert inequality states
\[
 \left|\sum_{x\ne z}\frac{u_xv_z}{\sin\pi(x-z)}\right|
 \le\frac32
 \left(\sum_x\frac{|u_x|^2}{\delta_x}\right)^{1/2}
 \left(\sum_z\frac{|v_z|^2}{\delta_z}\right)^{1/2}.       \tag{10}
\]
This is [Montgomery and Vaughan, Theorem G.20, (G.45), printed p.434](https://personal.science.psu.edu/rcv4/571s25/montgomery-vaughanII.pdf).
It applies to arbitrary complex \(u,v\) at distinct points modulo one.
Use the exact sharp-interval identity
\[
 K_T(t)=\frac{e((T+1/2)t)-e(t/2)}{2i\sin\pi t}.
\]
For each numerator, take \(u_x=w_xe(cx)\) and
\(v_z=w_ze(-(c+h)z)\), where \(c=T+1/2\) or \(1/2\). Both weighted
squared norms in (10) are bounded by
\[
 \sum_x|w_x|^2/\delta_x
 \le R\sum_{q\le R}\mu(q)^2q/\phi(q).
\]
The half-difference of the two forms proves (9). Finally,
\(q/\phi(q)=\sum_{d\mid q}\mu(d)^2/\phi(d)\) gives
\(\sum_{q\le R}q/\phi(q)\le C_0R\). The Euler product for \(C_0\)
converges since its nonconstant local term is \(1/[p(p-1)]\).

For comparison, taking absolute values of each geometric kernel first
would give only \(O(R^2\log(2R))\): for fixed denominators \(q,r\),
the differences of all numerator pairs run \(\gcd(q,r)\) times through
the grid of spacing \(1/\operatorname{lcm}(q,r)\). Summing reciprocal
distances gives \(O(qr\log(2qr))\), and then summing the weights gives
the claimed loss. Inequality (10) retains this off-diagonal cancellation.

## 3. The complete model budget and the choice of R

Set \(d_R=\sum_{n\le N}\lambda_R(n)^2\) and
\[
 Z_R=\mathcal C(|H_R|^2-V_R).
\]
Taking \(T=N-h\) in (8), Parseval gives a bound on all nonzero shifts:
\[
 \|Z_R\|_2^2
 =2\sum_{h=1}^N|\eta_R(N-h,h)|^2\le2NB_R^2\ll NR^4.    \tag{11}
\]
There is no contribution from \(h=0\); at that index (8) says
\[
 d_R=Nh_R+\eta_R(N,0),\qquad |d_R-Nh_R|\le B_R.         \tag{12}
\]
Using (3) with the same sharp weight \(N-h\), the model's error against
the full singular series satisfies
\[
 \left(2\sum_{h=1}^N
  \left[\sum_{n\le N-h}\lambda_R(n)\lambda_R(n+h)
                -(N-h)\mathfrak S(h)\right]^2\right)^{1/2}
 \le\sqrt{2N}B_R+\sqrt{D_R^{\rm tail}},                 \tag{13}
\]
where \(D_R^{\rm tail}=D_z|_{z=R}\), to distinguish it from \(d_R\).
Thus its squared budget is \(O(NR^4+N^3/R^2)\).
Balancing \(1+4\theta=3-2\theta\) selects \(R=\lfloor N^{1/3}\rfloor\)
and proves \(O(N^{7/3})\) for this model alone. This is the quantitative
reason for the auxiliary truncation. It is not a change in cutoff or a
bound for the prime error \(E\).

## 4. Transfer with all mixed terms retained

Write \(W_R=F_N-H_R=A+B-H_R\) and
\[
 X_R=\mathcal C(|F_N|^2-|H_R|^2)
     =\mathcal C\left(2\Re(\overline{H_R}W_R)+|W_R|^2\right),
 \qquad \mathcal D_R=\|X_R\|_2^2.                       \tag{14}
\]
In particular, the coefficient of \(W_R\) is exactly
\(a_t+b_t-\lambda_R(t)=\Lambda(t)-\lambda_R(t)\). The long Type I
term and the nonpaired Type II terms have not been separately estimated.
The full centered residual is the exact combination
\[
 G_y=X_R+Z_R-\mathcal C(V_y-V_R).                       \tag{15}
\]
For the strongest total budget, apply the triangle inequality directly
to the nonzero coefficient vectors with the full singular series:
\[
 \boxed{\ \sqrt{E(N)}\le\sqrt{\mathcal D_R}
                    +\sqrt{2N}B_R+\sqrt{D_R^{\rm tail}}.\ }     \tag{16}
\]
This also follows from (15) and (3), with an extra harmless \(O(N)\)
in the square-root budget. There is no smoothing or discarded shift.

To estimate the complete transfer, put
\[
 s_R=\sum_{n\le N}|\Lambda(n)-\lambda_R(n)|^2,
 \qquad T_R=\psi(N)+N+R^2(1+2\log R).
\]
The following is the integrated estimate attempted here:
\[
 \boxed{\ \mathcal D_R
       \le T_R^2s_R-(d_N-d_R)^2.\ }                    \tag{17}
\]
Indeed, pointwise
\[
 |F_N|^2-|H_R|^2=\Re((F_N+H_R)\overline{W_R}),
\]
so centering gives
\[
 \mathcal D_R
 \le\int|F_N+H_R|^2|W_R|^2-(d_N-d_R)^2
 \le\|F_N+H_R\|_\infty^2s_R-(d_N-d_R)^2.               \tag{18}
\]
The real part includes the full mixed term in (14).
For completeness, the exact difference between the first inequality and
equality is \(4\int(\Im(F_N\overline{H_R}))^2\ge0\). Thus the phase
information removed at this step is identified, rather than assumed zero.

To bound the envelope, the points in (7) are \(R^{-2}\)-spaced, their
number is at most \(R^2\), and \(|w_x|\le1\). Keep the nearest kernel
with bound \(N\). The \(j\)-th remaining distance is at least
\(j/(2R^2)\), since an interval of length \(2t\) contains at most
\(1+2tR^2\) points. Using
\(|K_N(t)|\le\min(N,1/(2\|t\|))\) gives
\[
 \|H_R\|_\infty\le N+R^2(1+2\log R).
\]
Also \(|F_N|\le\psi(N)\), proving (17). This is a supremum only of
the final combined transfer multiplier, after the rational dispersion
and arithmetic cancellation. Its quantitative loss is still decisive.

## 5. Evaluating the transfer cost on the actual primes

For every prime power \(p^a\), the exact Ramanujan coefficient is
\[
 \lambda_R(p^a)=h_R-\frac{p}{p-1}
       \sum_{\substack{r\le R/p\\(r,p)=1}}
                            \frac{\mu(r)^2}{\phi(r)}.   \tag{19}
\]
To derive this, only squarefree \(q\) contribute in (6). If \(p\nmid q\),
\(c_q(p^a)=\mu(q)\). If \(q=pr\), then
\(c_q(p^a)=(p-1)\mu(r)\), which changes the contribution relative to
\(h_R\) by \(-p\mu(r)^2/((p-1)\phi(r))\). In particular (19) holds
for every \(a\ge1\), with no prime-power replacement.

Consequently, with \(D_{N,R}\ge0\) defined by the following exact sum,
\[
\begin{split}
 \sum_{n\le N}\Lambda(n)\lambda_R(n)&=h_R\psi(N)-D_{N,R},\\
 D_{N,R}&=\sum_{p\le R}
  \left\lfloor\frac{\log N}{\log p}\right\rfloor\log p
  \frac{p}{p-1}
  \sum_{\substack{r\le R/p\\(r,p)=1}}\frac{\mu(r)^2}{\phi(r)},\\
 0\le D_{N,R}&\le2L\sum_{r\le R}\frac{\mu(r)^2}{\phi(r)}\pi(R/r)
                     \le2C_0RL.                       \tag{20}
\end{split}
\]
Only the elementary bound \(\pi(x)\le x\) was used for the remainder.
Together with (12), this evaluates the energy before bounding it:
\[
 \boxed{\ s_R=d_N+Nh_R-2h_R\psi(N)
                   +2D_{N,R}+\eta_R(N,0).\ }           \tag{21}
\]
The signed cross contribution cancels \(Nh_R\) of the original prime
energy. This reproduces and refines the remainder bookkeeping of the
prime-model inner product in CHHL Section 7.

Use the unconditional prime number theorem, \(\psi(N)=N+o(N)\),
\(d_N=N\log N+O(N)\), and \(h_R=\log R+O(1)\). The latter two formulas
are recorded in [CHHL (3) and (9)](https://arxiv.org/html/2308.14888v1).
For every fixed \(0<\theta<1/2\) and \(R=\lfloor N^\theta\rfloor\),
the evaluated remainder in (21) gives
\[
 s_R=(1-\theta+o(1))N\log N.                            \tag{22}
\]
The error \(O(R^2+RL)\) is \(o(N\log N)\). No distribution in a
growing modulus or unproved correlation estimate enters (22).

Furthermore \(H_R(0)=N+O(R^2\log(2R))\): in (7) separate \(0/1\)
and use the same spacing argument. Hence
\(\|F_N+H_R\|_\infty=(2+o(1))N\), not just an upper bound of order
\(N\). Also \(d_N-d_R=O(NL)\). Both right sides in (17) and the last
inequality of (18) therefore have the evaluated size
\[
 (4(1-\theta)+o(1))N^3\log N.                           \tag{23}
\]
The negative centering term is only \(O(N^2L^2)=o(N^3L)\).
At the selected \(R=\lfloor N^{1/3}\rfloor\), (16)-(23) prove
\[
 \sqrt E\le
 \sqrt{(8/3+o(1))N^3\log N}+O(N^{7/6}),
 \qquad E(N)\le(8/3+o(1))N^3\log N.                    \tag{24}
\]
The asymptotic coefficient in (24) describes this weak proved upper
bound; it is not an asymptotic for \(E\).

## 6. Where the attempt loses strength and the resulting total budget

The first insufficient quantitative step is the envelope extraction in
(18). Even if no loss occurred in taking its real part, its right side
has size \(N^3\log N\) by (22)-(23). It cannot prove a power saving
below 3. Closing it by a smaller unweighted estimate such as
\(s_R\ll N^{1-\delta}\) is false for every fixed \(\delta>0\) in
this parameter range, by (22). Increasing a fixed exponent
\(\theta<1/2\) only changes the positive factor \(1-\theta\);
the model budget also grows as \(N^{1+4\theta}\).

To obtain a complete \(N^{3-\delta}\) bound by (16) at \(R=N^{1/3}\)
for \(0<\delta\le2/3\), one would need to improve the *centered,
phase-sensitive* quantity in (18) to \(O(N^{3-\delta})\).
The executed envelope step does not do that. Its precise excess is
\(N^\delta\log N\), rather than an unidentified Type II sum. There is
no implication here that the true transfer norm has that large size.
The quadratic target also requires a better model remainder than the
balance in (13), or cancellation between it and the transfer in (15).

Every Type I term, every Type II range, their cross terms, and every
proper prime power is included in (17)-(24). These are whole-circle
bounds, so there is no omitted \(M_Q\). They control the whole error
only at the weak scale displayed in (24). Combining this attempt with
the existing stronger estimate leaves exactly
\[
 \boxed{\ E(N)\ll_C N^3/(\log N)^C
                  \quad\hbox{for every fixed }C>0.\ }  \tag{25}
\]
This is the unchanged result of `UPPER_BOUND.md`, not a new consequence
claimed as progress. The alternative square-root arc budget there also
remains \(4M_Q+O(N^{13/5}L^6)+O(N^2L^3)\), with \(M_Q\) unresolved at
a scale that would improve the total bound. This attempt supplies no
improved estimate for that term.

## 7. Sources and bounded checks

Primary sources inspected for this argument on 2026-09-09:

- [CHHL](https://arxiv.org/html/2308.14888v1), Sections 1, 4 and 7:
  the original quantity, centering, prime energies and the already known
  finite Ramanujan approximant. Its \(L^1\) conclusion is not imported
  as a fourth-moment bound.
- [Goldston, Hunts and Ngotiaoco](https://arxiv.org/html/1409.2151),
  Theorem 2 and Lemmas 2-3: the sharp weighted singular-series tail.
- [Montgomery and Vaughan](https://personal.science.psu.edu/rcv4/571s25/montgomery-vaughanII.pdf),
  Section 17.1 for (4), and Theorem G.20, (G.45), printed p.434, for
  the signed uniform estimate (9). The source's letters for the two
  Vaughan cutoffs may be interchanged; (4) is derived here.

The fixed diagnostic is `artifacts/centered_dispersion/check.py`; its
output is saved alongside it. It uses one numerical thread, a 60-second
limit, and only \(N=216\), \(U=V=8\), \(R=6\), \(y=14\). Exact rational
arithmetic checks the Ramanujan coefficients, the uniform shifted
remainder bound and the prime-power deficit. Integer coefficients of
\(\log p\) check the Vaughan identity, including the semiprime and
square boundaries. A finite Fourier-grid integration independently
checks (2), (14)-(15), and the phase loss in (18) against direct shifted
coefficients. The grid is longer than the degree of every integrated
polynomial, so its trapezoidal identity is exact in exact arithmetic;
the evaluations are explicitly ordinary floating-point checks.
They do not verify an asymptotic assertion. No larger cutoff, numerical
fleet, or scientific CI experiment is part of this attempt.
