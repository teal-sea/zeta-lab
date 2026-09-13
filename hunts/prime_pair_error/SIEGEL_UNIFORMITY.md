# Arithmetic U2 transfer with an explicit exceptional-zero contribution

2026-09-09. Base: 2da62eb9842db72d4f6bad09c6f13efe384d6ab7.
The completed attempts in PRs #209-#211 are unchanged.

**Result of this attempt.** For every fixed \(0<\kappa<1/10\), there is
\(c_\kappa>0\) such that the original sharp-cutoff CHHL error satisfies
\[
 \boxed{\ E(N)\ll_\kappa N^3\exp(-c_\kappa(\log N)^\kappa)
 +1_{q\ {\rm odd}}N^{2\beta+1}\frac{q^2}{\phi(q)^4}
 +N^{4\beta-1}\frac{q^2}{\phi(q)^3}.\ }                 \tag{1}
\]
The last two terms are present only if the exceptional character/zero
\((q,\chi,\beta)\) in the precise range below exists; otherwise both
are zero. The constants are effective in the sense of the source
theorems. This is a handwritten deduction, pending external verification,
with finite checks of its algebra. It is not a novelty claim.

In the no-exception case, the displayed total bound is stronger than
\(N^3/(\log N)^A\) for every fixed \(A\), but it is not a fixed power
saving. Without excluding or further controlling the exceptional terms,
this argument does not give a uniformly stronger unconditional estimate
than that already recorded in UPPER_BOUND.md. The near-quadratic target
remains unresolved.

## 1. Source input, exact model, and normalization

The primary source is Tao and Teräväinen, [Quantitative bounds for Gowers
uniformity of the Möbius and von Mangoldt functions, v4](https://arxiv.org/html/2107.02158v4),
abbreviated TT. All its uses below refer to this version.

Let \(N\) be a sufficiently large integer and write
\[
 L=\log N,\quad Z=\exp(L^{1/10}),\quad
 P(Z)=\prod_{p<Z}p,\quad b_Z=P(Z)/\phi(P(Z)),\quad
 \nu(n)=b_Z1_{(n,P(Z))=1}.
\]
Here \(Z\) is TT's parameter \(Q\), not our old arc denominator.
TT Definition 2.1 specifies at most one primitive real character
\(\chi\) of conductor \(q<Z\) with a real zero
\[
          1-c_0/\log Z<\beta<1,                         \tag{2}
\]
for its fixed sufficiently small absolute \(c_0>0\).
Define the actual source model on \([1,N]\) by
\[
 a(n)=\begin{cases}
       \nu(n),&\text{if no zero in (2) exists},\\
       \nu(n)(1-n^{\beta-1}\chi(n)),&\text{otherwise}.
       \end{cases}                                    \tag{3}
\]
This is neither the Ramanujan model \(\lambda_R\) from #211 nor a
primes-only replacement of \(\Lambda\). Put
\[
 F=\sum_{n\le N}\Lambda(n)e(n\alpha),\quad
 H=\sum_{n\le N}a(n)e(n\alpha),\quad W=F-H,\quad
 \mathcal Cf=f-\int_{\mathbb T}f.
\]

TT Definition 1.1 uses zero extension outside \([1,N]\). Exactly,
\[
 A_N:=\|1_{[N]}\|_{\widetilde U^2(\mathbb Z)}^4
    =N^2+2\sum_{j=1}^{N-1}j^2=\frac{2N^3+N}{3},
 \qquad
 \|\widehat f\|_4=A_N^{1/4}\|f\|_{U^2[N]},             \tag{4}
\]
where \(\widehat f(\alpha)=\sum_{n\le N}f(n)e(n\alpha)\).
The equality is obtained by counting \(n_1+n_2=n_3+n_4\), not by
replacing the interval with a cyclic group of length \(N\).

The particular consequence of TT Theorem 2.7 we use is
\[
 \|\Lambda-a\|_{U^2[N]}\ll_\kappa
                          \exp(-c_\kappa L^\kappa).
                                                               \tag{5}
\]
Here is an explicit deduction of its exponent, rather than an appeal to
the weaker general higher-order theorem. In TT (2.13), take \(k=2\),
the fixed one-dimensional torus, \(g(n)=\alpha n\), and test function
\(e(t)\), with \(P=[N]\) and \(\epsilon=1/10-\kappa\).
The dimension, complexity and Lipschitz restrictions hold for large \(N\).
Thus uniformly in \(\alpha\),
\[
 |W(\alpha)|\ll_\kappa N e^{-L^\kappa}.
\]
TT Lemma 2.4 gives \(|\Lambda(n)-a(n)|\ll L\). Therefore
\(\int|W|^4\ll_\kappa N^3L^2e^{-2L^\kappa}\), which proves (5)
using (4), after decreasing the exponential constant. The concluding
discussion of TT Section 2 explicitly records this stronger \(U^2\)
consequence. No higher-order inverse theorem is used here.

## 2. Arithmetic transfer in the required norm

The elementary transfer is
\[
 \boxed{\ \|\mathcal C(|F|^2-|H|^2)\|_2
        \le\|W\|_4(\|F\|_4+\|H\|_4).\ }               \tag{6}
\]
Indeed \(|F|^2-|H|^2=W\overline F+H\overline W\), centering contracts
the \(L^2\) norm, and Hölder bounds the two products. This retains the
combined difference before estimating it.

For a sequence bounded in magnitude by \(CL\), expansion of its Fourier
fourth moment and the count \(A_N\) give a bound \(C^4L^4A_N\).
TT Lemma 2.4 and (4)-(5) now imply
\[
 \mathcal D:=\|\mathcal C(|F|^2-|H|^2)\|_2^2
        \ll_\kappa N^3e^{-c_\kappa L^\kappa}.          \tag{7}
\]
Polynomial factors in \(L\) are absorbed into the exponential. The
arithmetic input is (5) for the actual residual. No assertion that its
coefficient \(L^2\) distance is small is made.

Define, only for the model comparison,
\[
 E_a=2\sum_{h=1}^N
 \left[\sum_{n=1}^{N-h}a(n)a(n+h)-(N-h)\mathfrak S(h)\right]^2.
\]
Parseval on nonzero Fourier coefficients gives the exact transfer
\[
             \sqrt E\le\sqrt{\mathcal D}+\sqrt{E_a},
 \qquad E\le2\mathcal D+2E_a.                          \tag{8}
\]
The zero coefficient is removed exactly by \(\mathcal C\).
Both signs of every nonzero shift are counted through the factor 2.
No arc decomposition, smoothing, or moving endpoint has been introduced.

## 3. A uniform sieve calculation with the sharp endpoint

For \(h\ge1\), put
\[
 \rho_h(p)=\begin{cases}1,&p\mid h,\\2,&p\nmid h,\end{cases}
 \quad
 \alpha_p(h)=\frac{1-\rho_h(p)/p}{(1-1/p)^2},\quad
 \sigma_Z(h)=\prod_{p<Z}\alpha_p(h).                   \tag{9}
\]
This truncates by primes, unlike the denominator truncation
\(\mathfrak S_y\) in UPPER_BOUND.md.

The source theorem used here is **TT Lemma 5.1**, the fundamental lemma
of the sieve. TT Proposition 5.2 is not applicable to the parallel
one-variable forms \(n,n+h\); we do not apply it to them.

First handle odd \(h\): for \(Z>2\), \(\nu(n)\nu(n+h)=0\) and
\(\sigma_Z(h)=\mathfrak S(h)=0\). This also avoids the forbidden sieve
local density \(g(2)=1\).

For even \(h\), let \(q=1\) in the no-exception case, or let \(q\) be
the conductor in (2). All prime divisors of \(q\) are below \(Z\).
For a residue \(r\bmod q\) with \((r(r+h),q)=1\), define
\[
 B_r(t,h)=\sum_{\substack{1\le n\le t\\n\equiv r\pmod q}}
                              \nu(n)\nu(n+h),\quad 0\le t\le N-h,
 \qquad
 \mathcal L_h=\left(\frac q{\phi(q)}\right)^2
                    \prod_{\substack{p<Z\\p\nmid q}}\alpha_p(h).
\]
The assertion needed, including its uniform error before residue
summation, is
\[
 B_r(t,h)=\frac{t}{q}\mathcal L_h+
 O\left(b_Z^2\left[\frac Nq e^{-cL^{9/10}}
                         +D(1+\log D)\right]\right),
 \qquad D=\lfloor N^{1/4}\rfloor.                     \tag{10}
\]

To prove it, apply TT Lemma 5.1 to the nonnegative sequence that counts
values \(n(n+h)\) for the indicated \(n\). For squarefree \(d\mid P(Z)\)
coprime to \(q\), the Chinese remainder theorem gives
\[
 \#\{n\le t:n\equiv r\pmod q,\ d\mid n(n+h)\}
       =\frac tq\,\frac{\rho_h(d)}d+O(\rho_h(d)),
 \quad \rho_h(d)=\prod_{p\mid d}\rho_h(p).
\]
For \(d\) sharing a prime with \(q\), the count is zero. Thus take
\(g(p)=\rho_h(p)/p\) for \(p\nmid q\) and \(g(p)=0\) otherwise.
For even \(h\), \(g(p)<1\) for every prime, and
\[
 \prod_{w\le p<z}(1-g(p))^{-1}
                 \ll(\log z/\log w)^2
\]
uniformly in \(h,q\). This follows from \(\rho_h(p)\le2\), treating
\(p=2\) separately, the convergent \(O(p^{-2})\) factors, and the
Mertens product estimate used in TT Section 5. The sieve dimension is
2 and its constant \(K\) is absolute.

For large \(N\), \(D\ge Z^{19}\), as required by that lemma, and
\(s=\log D/\log Z\asymp L^{9/10}\). Its remainder sum is at most
\(\sum_{d\le D}2^{\omega(d)}\le\sum_{d\le D}\tau(d)
\le D(1+\log D)\). Multiplying by \(b_Z^2\) proves (10).
The argument is uniform even when \(t\) is short; \(t=0\) is immediate.
In particular it does not replace \(N-h\) by \(N\).

Summing (10) over at most \(q<Z\) classes, its total error is
\[
 O\left(b_Z^2[N e^{-cL^{9/10}}+qD(1+\log D)]\right)
                         =O(N e^{-c'L^{9/10}}).        \tag{11}
\]
Here \(b_Z\ll\log Z\), \(q<e^{L^{1/10}}\), and the second term is
\(O(N^{1/2})\) for large \(N\).

This estimate is stable under any nonnegative decreasing weight on
\([0,N-h]\) bounded by 1. Stieltjes partial summation applied to (10)
has total variation at most 1 and replaces \(t\) by the weight's
integral, with at most twice the same error. This fact is used below
with the three explicit weights, not with an unspecified smoothing.

The comparison with the original infinite singular series is uniform:
\[
        |\sigma_Z(h)-\mathfrak S(h)|\ll L^2/Z
                           \quad(1\le h\le N).         \tag{12}
\]
For even \(h\), compare the Euler products. The logarithm of their
ratio has magnitude at most a constant times
\[
 \sum_{p\ge Z}p^{-2}+\sum_{\substack{p\mid h\\p\ge Z}}p^{-1}
       \ll Z^{-1}+L/(Z\log Z).
\]
Both products are \(O(L)\): their factors for primes dividing \(h\)
are bounded by a constant times \(h/\phi(h)\ll\log(2h)\), since the
extra factors \(1+1/[p(p-2)]\) for \(p>2\) have convergent product.
The ratio tends uniformly to 1, proving (12); odd \(h\) was handled
exactly. Equations (10)-(12), with \(q=1\), give
\[
 \sum_{n\le N-h}\nu(n)\nu(n+h)
       =(N-h)\mathfrak S(h)+O(N e^{-cL^{1/10}}).
                                                               \tag{13}
\]
Consequently, when no zero in (2) exists,
\[
                  E_a\ll N^3e^{-cL^{1/10}}.            \tag{14}
\]

## 4. Explicit correction when an exceptional zero exists

Now let \(q,\chi,\beta\) be as in (2), and put \(\delta=1-\beta\).
For large \(N\), \(\beta\ge3/4\). Set \(T=N-h\), and define
\[
 f(t)=\max(1,t)^{-\delta},\quad g_h(t)=(t+h)^{-\delta},
 \quad
 J_1(h)=\int_0^T f(t)\,dt,\quad
 J_2(h)=\int_0^T g_h(t)\,dt,\quad
 J_{12}(h)=\int_0^T f(t)g_h(t)\,dt.                    \tag{15}
\]
At every integer \(n\ge1\), these weights are exactly the factors in
(3). Their extension to \(0\le t<1\) merely fixes the partial-summation
endpoint. They have total variation at most 1. For \(T\ge1\),
\[
 J_1=1+(T^\beta-1)/\beta,\quad
 J_2=(N^\beta-h^\beta)/\beta,
 \quad J_1,J_2\ll N^\beta,\quad J_{12}\ll N^{2\beta-1}.
                                                               \tag{16}
\]
The last bound uses \(g_h(t)\le f(t)\) and integrates \(f(t)^2\).
All three integrals vanish for \(h=N\).

Introduce the finite residue averages
\[
 u_q(h)=q^{-1}\!\sum_{\substack{r\bmod q\\(r(r+h),q)=1}}\chi(r),
 \quad
 v_q(h)=q^{-1}\!\sum_{\substack{r\bmod q\\(r(r+h),q)=1}}\chi(r+h).
\]
The exact arithmetic identities are
\[
 \begin{array}{ll}
 u_q(h)=\mu(q)\chi(-h)/q,\quad v_q(h)=\mu(q)\chi(h)/q,
                                      &q\ \text{odd},\\
 u_q(h)=v_q(h)=0,                     &4\mid q,
 \end{array}
 \qquad
 \sum_{r\bmod q}\chi(r)\chi(r+h)=c_q(h).                \tag{17}
\]
Here \(c_q(h)\) is the Ramanujan sum. To check (17), a primitive real
conductor has squarefree odd part and 2-part \(1,4,\) or \(8\), as
recorded in TT Section 5.2. At an odd prime \(p\), removing \(r=0,-h\)
from \(\sum_r\chi_p(r)=0\) leaves \(-\chi_p(-h)\).
The quadratic correlation is \(p-1\) if \(p\mid h\), and \(-1\)
otherwise. For the latter identity, scaling \(h\ne0\) reduces to
\(\sum_x\chi_p(x(x+1))=-1\); count
\((v-u)(v+u)=1\) to obtain it. At 4 and 8, summing the primitive
character on all odd residues gives zero for the linear expressions
when \(h\) is even; for odd \(h\) there are no admissible residues.
Their autocorrelations are respectively \(c_4(h)\) and \(c_8(h)\)
by direct evaluation. The Chinese remainder theorem multiplies these
identities to give (17), including both primitive characters at 8.

Expanding (3) inside each residue class and using (10)-(12) with
partial summation gives the following actual model-to-target formula:
\[
 \boxed{\ \sum_{n\le N-h}a(n)a(n+h)-(N-h)\mathfrak S(h)
     =C_{q,\beta,Z}(h)+O(N e^{-cL^{1/10}}),\ }          \tag{18}
\]
uniformly for every \(1\le h\le N\), where
\[
 C_{q,\beta,Z}(h)=\mathcal L_h
 \left[-u_q(h)J_1(h)-v_q(h)J_2(h)
                       +\frac{c_q(h)}q J_{12}(h)\right].
                                                               \tag{19}
\]
The constant part uses
\(q^{-1}\#\{r:(r(r+h),q)=1\}
 =\prod_{p\mid q}(1-\rho_h(p)/p)\).
For odd \(h\), both sides' main expressions vanish: if \(q\) is odd
the local factor at 2 is zero, and if \(q\) is even the residue
averages vanish. These shifts of the original prime count remain
covered by (7)-(8).

## 5. Summing the explicit exceptional terms over every shift

Write \(S_*(h)=\prod_{p<Z,p\nmid q}\alpha_p(h)\).
For every \(h\ge1\),
\[
 0\le S_*(h)^2
 \le\prod_{\substack{p\mid h\\p\nmid q}}\left(\frac p{p-1}\right)^2
 =\sum_{\substack{d\mid h\\(d,q)=1}}f_0(d),             \tag{20}
\]
where \(f_0\) is supported on squarefree integers and
\(f_0(p)=(2p-1)/(p-1)^2\). Its Euler products give
\(\sum_d f_0(d)/d<\infty\) and
\(\sum_d f_0(d)/\sqrt d<\infty\). Hence
\[
 \sum_{h\le N}S_*(h)^2\ll N,\qquad
 \sum_{d\le N}f_0(d)\ll\sqrt N.                        \tag{21}
\]

Finite Fourier orthogonality gives
\(\sum_{h\bmod q}c_q(h)^2=q\phi(q)\). Also
\(c_q(dj)=c_q(j)\) if \((d,q)=1\). Therefore (20) implies
\[
 \begin{split}
 \sum_{h\le N}c_q(h)^2 S_*(h)^2
 &\le \phi(q)\sum_{\substack{d\le N\\(d,q)=1}}
                   f_0(d)(N/d+q)\\
 &\ll \phi(q)(N+q\sqrt N)\ll N\phi(q),                 \tag{22}
 \end{split}
\]
since \(q<Z<\sqrt N\) for large \(N\).

Apply (16)-(17) to (19), only now bounding the linear and quadratic
pieces separately. Since \(\mathcal L_h=(q/\phi(q))^2S_*(h)\),
(21)-(22) prove
\[
 \sum_{h=1}^N|C_{q,\beta,Z}(h)|^2
 \ll 1_{q\ {\rm odd}}N^{2\beta+1}\frac{q^2}{\phi(q)^4}
                         +N^{4\beta-1}\frac{q^2}{\phi(q)^3}.
                                                               \tag{23}
\]
Thus (18) bounds the entire \(E_a\), with exactly these two terms
and \(O(N^3e^{-cL^{1/10}})\). Combining with (7)-(8) proves (1).
There is no unspecified model error or mixed norm left in that bound.

## 6. Scope and comparison with the original objective

The proof is unconditional as a dichotomy, with the actual exceptional
term present when required by TT Definition 2.1. The no-exception
branch alone is not an unconditional deletion of that term.
The source leaves open whether such a zero exists in its range.

Writing the two correction terms relative to \(N^3\) displays their
size without suppressing the zero location:
\[
 1_{q\ {\rm odd}}\,e^{-2(1-\beta)L}\frac{q^2}{\phi(q)^4}
       +e^{-4(1-\beta)L}\frac{q^2}{\phi(q)^3}.           \tag{24}
\]
For example, if \(q\ge\exp(bL^\kappa)\), or if
\((1-\beta)L\ge bL^\kappa\), for fixed \(b>0\), these terms are
absorbed into a stretched exponential after reducing its constant.
Use \(q/\phi(q)\ll\log(2q)\) to check this assertion. Neither
condition is imposed on an arbitrary exceptional zero.

For each fixed \(A\), \(e^{-cL^\kappa}=o(L^{-A})\).
However \(e^{-cL^\kappa}\) is larger than \(N^{-\epsilon}\) eventually
for every fixed \(\epsilon>0\). Hence even the no-exception conclusion
is not a first fixed power saving below exponent 3.
In the general exceptional case, the existing
\(E(N)\ll_A N^3L^{-A}\) from UPPER_BOUND.md remains available and may
be combined with (1) by taking the better bound. No uniformly stronger
unconditional total estimate is claimed after suppressing \(q,\beta\).

All separations, the original singular series, the exact endpoint
\(N-h\), and the proper prime powers in \(\Lambda\) have been retained.
The major and minor arcs are both included in the whole-circle transfer.
There is no separate \(M_Q\) left unaccounted for in (1).
No RH, GRH, random-sign input, or unproved prime correlation is used.

The source statements used are TT Definition 1.1, Definition 2.1,
Lemma 2.4, Theorem 2.7, Lemma 5.1, and the standard local character and
sieve setup of Section 5. The precise normalization (4), transfer
(6)-(8), uniform two-form sieve calculation, local identities
(17), and bound (23) are deductions given here. No step in (1) is
left as a conjectural estimate. External checking of the written
argument remains distinct from the finite checks below.

## 7. Bounded algebra checks

The exponent calculation and the complete bound (1) were derived before
running diagnostics. The fixed script at
artifacts/siegel_uniformity/check.py uses one numerical thread, one
cutoff \(N=128\), and a 60-second limit. It checks exact local character
averages, Ramanujan orthogonality, and the sharp \(U^2\) denominator.
Finite Fourier-grid integration independently checks the centered
transfer using the full von Mangoldt function. A corrected-model
fixture uses a chosen real character and a toy value of \(\beta\);
it does not assert the existence of any exceptional zero or test the
source's asymptotic theorem. The finite residue-counting errors and
partial-summation errors are retained explicitly in that fixture.
Saved output distinguishes exact rational checks from floating checks
and includes hashes of this proof and the script.
