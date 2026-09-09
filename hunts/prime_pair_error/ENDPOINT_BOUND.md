# Endpoint logarithmic exponent for the complete corrected CHHL error

## Status

This is the coordinator's candidate argument in the exact mathematical version
reviewed on 2026-09-09. It had no endpoint commit when reviewed. This file is
its first durable repository copy; the separate review record identifies and
pins the commit containing it.

Proposed result, for some fixed \(c>0\) and all sufficiently large \(N\):

\[
E_{\rm corr}(N)\ll N^3\exp(-c(\log N)^{1/10}).
\]

The model and exceptional correction are exactly those of #212-#215. This does
not exclude exceptional zeros, prove RH, provide a fixed power saving, or
establish novelty.

Reference checkpoint: #215 at
`3645324cf69497e197592fdcc2f630c4ed6504b0`.

## Primary sources and project dependencies

[S1] Tao-Teräväinen, "Quantitative bounds for Gowers uniformity of the
Möbius and von Mangoldt functions," arXiv:2107.02158v4. Definition 2.1,
Proposition 2.2, especially (2.5), and Lemma 2.4.
https://arxiv.org/html/2107.02158v4

[S2] Montgomery-Vaughan, "Multiplicative Number Theory II: Primes and
Sieves," Theorem 17.1 and (17.28)-(17.32), printed pages 65-66.
https://personal.science.psu.edu/rcv4/571s25/montgomery-vaughanII.pdf

[P1] Project `SIEGEL_UNIFORMITY.md`, Sections 3-5, especially the model
comparison (18)-(19), at `76ed1155d087d9137306d3632f66dba7555aadc3`.

[P2] `CORRECTED_RH_BRIDGE.md` at
`cb0189db3863ac43b2314c7df1008636bd4da477`. This defines the unchanged
corrected target and its RH-sufficiency.

## 1. Definitions and complete target

Let

\[
\ell=\log N,\qquad t=\ell^{1/10},\qquad Z=\exp(t),
\qquad P=\prod_{p<Z}p,\qquad b=P/\phi(P),
\]

and \(e(x)=\exp(2\pi i x)\). Define

\[
\nu(n)=b1_{(n,P)=1},
\]

and

\[
a(n)=\nu(n)(1-1_{\rm exc}\chi(n)n^{\beta-1}).
\]

When exceptional data exist, they are exactly those of [S1], Definition 2.1:
\(\chi\) is primitive real, its conductor \(q<Z\), and
\(1-c_0/\log Z<\beta<1\). Without an exception, \(a=\nu\). The exceptional
data may change with \(N\).

All sequences are supported on the original interval \([1,N]\). The function
\(\Lambda\) includes all proper prime powers.

Write

\[
F(\alpha)=\sum_{n\le N}\Lambda(n)e(n\alpha),\qquad
H(\alpha)=\sum_{n\le N}a(n)e(n\alpha),\qquad W=F-H.
\]

Let \(\mathcal C\) remove a Fourier polynomial's constant coefficient. Using
the original infinite singular series \(\mathfrak S(h)\), put

\[
r(h)=\sum_{n\le N-h}\Lambda(n)\Lambda(n+h)-(N-h)\mathfrak S(h),
\]

\[
r_a(h)=\sum_{n\le N-h}a(n)a(n+h)-(N-h)\mathfrak S(h).
\]

Use exactly the exceptional correction \(C_N(h)\) defined in [P1]:

\[
E_{\rm corr}(N)=2\sum_{h=1}^N|r(h)-C_N(h)|^2.
\]

Two inputs are consumed.

### Arithmetic-progression input

The assertion taken from [S1], Proposition 2.2, (2.5), is that some
\(\gamma>0\) satisfies, uniformly over arithmetic progressions \(B\) contained
in \([1,N]\),

\[
\left|\sum_{n\in B}(\Lambda(n)-a(n))\right|
\ll N\exp(-\gamma t).                                      \tag{1}
\]

This uses the endpoint progression theorem, not substitution of
\(\kappa=1/10\) into Theorem 2.7 with its epsilon loss.

### Inherited model comparison

[P1], equations (18)-(19), supplies uniformly for \(1\le h\le N\):

\[
r_a(h)=C_N(h)+O(N\exp(-c_m t)).                            \tag{2}
\]

This is the project's dimension-two sieve and character argument, including
comparison with the original infinite singular series. It is a project-proof
dependency, not a separately published theorem.

Parseval with the constant coefficient removed gives

\[
D:=\|\mathcal C(|F|^2-|H|^2)\|_2^2
=2\sum_{h=1}^N|r(h)-r_a(h)|^2.
\]

Therefore

\[
E_{\rm corr}(N)\le 2D+O(N^3\exp(-2c_m t)).                \tag{3}
\]

The task is to bound the complete intensity transfer \(D\). Its mixed term and
centered \(|W|^2\) term remain combined.

## 2. Bounded-order divisor approximation

Choose

\[
m=2\lceil\sqrt\ell\rceil,\qquad D_0=Z^m=N^{o(1)},
\]

and define

\[
B_m(n)=\sum_{\substack{d\mid P,\ d\mid n\\\omega(d)\le m}}\mu(d).
\]

If \(s\) counts the distinct primes below \(Z\) dividing \(n\), the alternating
binomial identity gives \(B_m(n)=1\) when \(s=0\). For \(s>0\), since \(m\)
is even,

\[
B_m(n)=\binom{s-1}{m},\qquad
0\le B_m(n)-1_{s=0}\le\binom{s}{m+1}.                   \tag{4}
\]

Use \(\binom uv=0\) when \(v>u\). Every divisor coefficient is \(0,1\), or
\(-1\). Every divisor present is less than \(D_0\).

With \(H_Z=\sum_{p<Z}1/p\), summation gives

\[
\sum_{n\le N}|B_m(n)-1_{(n,P)=1}|
\le\sum_{\substack{d\mid P\\\omega(d)=m+1}}\left\lfloor\frac Nd\right\rfloor
\le N\frac{H_Z^{m+1}}{(m+1)!}.                           \tag{5}
\]

There is no accumulated \(O(D_0)\) remainder: \(\lfloor N/d\rfloor\le N/d\)
is used directly.

The elementary estimate \(H_Z\le1+\log Z\) and
\(k!\ge(k/e)^k\) yield

\[
\text{right side of (5)}\ll N\exp(-c\sqrt\ell\log\ell).
\]

Since \(b\ll\log Z\), retain the weaker convenient bound

\[
\sum_{n\le N}|bB_m(n)-\nu(n)|
\ll N\exp(-c\sqrt\ell).                                 \tag{6}
\]

Multiplication by \(\chi(n)\), \(n^{\beta-1}\), or a unit complex phase does
not increase this error. It also bounds every prefix \(s\le N\).

## 3. Major arcs: retain prime-model cancellation

Choose fixed

\[
0<\sigma\le\min(\gamma/20,1/20),\qquad
R=\lfloor\exp(\sigma t)\rfloor.
\]

Let \(\mathfrak M\) be the union of circular arcs

\[
|\alpha-a/r|\le2R/N
\]

around reduced rationals with \(r\le R\). Let \(\mathfrak m\) be the
complement. For sufficiently large \(N\), \(R^3=o(N)\), and

\[
|\mathfrak M|\ll R^3/N.                                  \tag{7}
\]

Only the union-measure upper bound is required.

For \(\alpha=a/r+\theta\in\mathfrak M\), split \(W\) into residue classes
modulo \(r\). Prefixes in each class are arithmetic progressions. Applying (1)
and partial summation gives

\[
|W(\alpha)|\ll r(1+N|\theta|)N\exp(-\gamma t)
\ll NR^2\exp(-\gamma t).                                \tag{8}
\]

This keeps \(\Lambda-a\) together on the major arcs.

The coefficient bounds \(\Lambda(n)\le\ell\) and \(|a(n)|\le2b\) imply

\[
|F|+|H|\ll N\ell.
\]

Since

\[
\bigl||F|^2-|H|^2\bigr|\le|W|(|F|+|H|),
\]

equations (7)-(8) give

\[
\int_{\mathfrak M}(|F|^2-|H|^2)^2\,d\alpha
\ll N^3\ell^2R^7\exp(-2\gamma t).                       \tag{9}
\]

All exceptional conductors are included through (1), whether their conductor
is below or above \(R\).

## 4. Minor arcs: Type I and character estimates

### 4.1 Type I estimate

For \((a,r)=1\), \(r\ge2\), \(|\alpha-a/r|\le r^{-2}\), and \(D_0\le N\),
the proposed elementary estimate is

\[
\sum_{d\le D_0}\min\left(\frac Nd,\frac1{2\|d\alpha\|}\right)
\ll (N/r+D_0+r)\log^2(2N).                              \tag{10}
\]

At zero distance, use the \(N/d\) cap.

Proposed proof: partition \(d\) into dyadic intervals. On an interval with
length comparable to \(A\ge r/4\), subdivide into blocks of length at most
\(r/2\). Within a block the phases are separated by at least \(1/(2r)\). One
nearest point costs at most \(N/A\); the others cost \(O(r\log(2r))\). The
interval contributes

\[
O(N/r+(A+r)\log(2r)).
\]

For the initial interval \(d\le r/2\), separation from zero gives
\(O(r\log(2r))\). Summing the dyadic intervals gives (10). Compare with [S2],
(17.30)-(17.32).

For every prefix \(s\le N\), the Fourier sum of \(bB_m\) on \([1,s]\) is
bounded by \(b\) times the right side of (10).

### 4.2 Prime sum on the minor set

Dirichlet approximation with \(\lfloor N/R\rfloor\) gives a reduced \(a/r\)
with \(r\le N/R\) and error at most \(1/(r\lfloor N/R\rfloor)\), which is at
most \(r^{-2}\) and at most \(2R/(rN)\).

For \(\alpha\in\mathfrak m\), necessarily \(r>R\).

[S2], Theorem 17.1, for the full von Mangoldt sum yields

\[
\sup_{\mathfrak m}|F|
\ll (NR^{-1/2}+N^{4/5})\ell^{5/2}.                      \tag{11}
\]

Equations (6) and (10) similarly bound every untwisted model prefix by

\[
O\bigl(b(N/R+D_0)\ell^2+N\exp(-c\sqrt\ell)\bigr).
\]

### 4.3 Character estimate: all conductor ranges

The primitive Gauss expansion has Fourier coefficients of absolute magnitude
\(q^{-1/2}\) on unit frequencies and zero otherwise. It gives uniformly in
\(\theta\) and \(K\):

\[
\left|\sum_{k\le K}\chi(k)e(k\theta)\right|
\ll K/\sqrt q+\sqrt q\log(2q).                           \tag{12}
\]

To obtain this, expand \(\chi\) by its \(q\)-point Fourier transform. Among
\(q\) equally spaced geometric-kernel centers, one contributes at most \(K\)
and the remainder contributes \(O(q\log(2q))\). Divide by \(\sqrt q\).

This applies to primitive real characters with odd conductor and with 4- or
8-part.

Put

\[
V_s(\alpha)=\sum_{n\le s}\nu(n)\chi(n)e(n\alpha).
\]

#### Case A: \(q\ge R^{1/3}\)

Use (12) on each divisor sum from (6), retaining \(\chi(d)\) through
multiplicativity. If \((d,q)>1\), its contribution is zero.

Uniformly for \(s\le N\),

\[
|V_s|\ll b\left[\frac{N\log(2D_0)}{\sqrt q}
+D_0\sqrt q\log(2q)\right]+N\exp(-c\sqrt\ell)
\]

and hence

\[
|V_s|\ll\ell^{O(1)}[NR^{-1/6}+D_0\sqrt Z]
+N\exp(-c\sqrt\ell).                                   \tag{13}
\]

#### Case B: \(q<R^{1/3}\)

Apply the approximation error (6) to the original character-weighted sequence
first. It is not multiplied by \(\sqrt q\).

For the approximating divisor sum, expand \(\chi(n)\) by its Gauss sum. For
each shifted phase \(\gamma=\alpha+j/q\), apply Dirichlet approximation with
denominator \(r\le N/R\).

That denominator must exceed \(R/q\). Otherwise \(\alpha\) lies within
\(2R/N\) of a rational with reduced denominator at most \(rq\le R\),
contradicting \(\alpha\in\mathfrak m\).

Equation (10) then bounds each shifted Type I sum by

\[
O\bigl(b(Nq/R+D_0)\ell^2\bigr).
\]

The sum of absolute Gauss coefficients costs at most \(\sqrt q\). Thus

\[
|V_s|\ll b\ell^2[Nq^{3/2}/R+D_0\sqrt q]
+N\exp(-c\sqrt\ell)
\]

and hence

\[
|V_s|\ll\ell^{O(1)}[NR^{-1/2}+D_0R^{1/6}]
+N\exp(-c\sqrt\ell).                                   \tag{14}
\]

The factor \(n^{\beta-1}\) is incorporated by exact discrete Abel summation
of the prefixes \(V_s\). Its nonnegative coefficients have total mass one.

Combining (13), (14), and the untwisted estimate gives

\[
\sup_{\mathfrak m}|H|
\ll\ell^{O(1)}[NR^{-1/6}+D_0\sqrt Z]
+N\exp(-c\sqrt\ell).                                   \tag{15}
\]

Without an exceptional zero, omit the entire character component. No conductor
range or frequency range is omitted.

## 5. Integrate the complete minor-arc expression

For any Fourier polynomial \(J\) supported on \([1,N]\) with coefficient
magnitudes at most \(B\), orthogonality and additive-quadruple counting give

\[
\int|J|^2\le NB^2,
\]

\[
\int|J|^4\le\frac{2N^3+N}{3}B^4\le N^3B^4.
\]

Cauchy-Schwarz therefore gives

\[
\int|J|^3\le N^2B^3.                                   \tag{16}
\]

Use \(B=\ell\) for \(F\) and \(B=2b\) for \(H\).

On the minor set, bound the fourth moment by its local supremum times this
global third moment. This is not the global residual supremum times
coefficient-energy estimate used in the failed earlier attempt.

Since

\[
(|F|^2-|H|^2)^2\le2|F|^4+2|H|^4,
\]

equations (11), (15), and (16) imply

\[
\int_{\mathfrak m}(|F|^2-|H|^2)^2\,d\alpha
\ll\ell^{O(1)}[N^3R^{-1/6}+N^{14/5}+N^2D_0\sqrt Z]
+N^3\exp(-c\sqrt\ell).                                 \tag{17}
\]

## 6. Complete budget and parameter choice

Centering contracts the \(L^2\) norm. Combining (3), (9), and (17) therefore
yields

\[
\begin{aligned}
E_{\rm corr}(N)\ll\ell^{O(1)}[&N^3R^7\exp(-2\gamma t)
+N^3R^{-1/6}\\
&+N^{14/5}+N^2D_0\sqrt Z]
+N^3\exp(-c\sqrt\ell)+N^3\exp(-2c_mt).                 \tag{18}
\end{aligned}
\]

This includes the full intensity difference, all major and minor arcs, every
conductor range, divisor approximation error, and the model-to-original-
singular-series comparison. It does not leave a separate \(M_Q\) or an unnamed
model norm.

Take \(R=\lfloor\exp(\sigma t)\rfloor\), \(\sigma\le\gamma/20\). Then

\[
R^7\exp(-2\gamma t)\ll\exp(-(2\gamma-7\sigma)t),
\]

\[
R^{-1/6}\ll\exp(-\sigma t/6).
\]

Also

\[
\log(D_0\sqrt Z)
=(2\lceil\sqrt\ell\rceil+1/2)\ell^{1/10}=o(\ell),
\]

so \(N^2D_0\sqrt Z=N^{2+o(1)}\).

The \(N^{14/5}\) term, \(N^{2+o(1)}\) term, divisor error, and logarithmic
factors are all absorbed after reducing \(c\). The proposed conclusion is

\[
E_{\rm corr}(N)\ll N^3\exp(-c\ell^{1/10}).
\]

This conclusion depends on the external progression input (1), the project
model comparison (2), and validity of all estimates above.

## 7. What is and is not claimed

The project previously recorded

\[
E_{\rm corr}(N)\ll_\kappa N^3\exp(-c_\kappa\ell^\kappa)
\]

for each fixed \(\kappa<1/10\). The proposed argument reaches the endpoint
\(1/10\) for the complete corrected quantity.

It does not establish a fixed \(\eta>0\) with
\(E_{\rm corr}\ll N^{3-\eta}\), since

\[
\eta\ell-c\ell^{1/10}\longrightarrow\infty.
\]

In this argument, choosing \(R=N^\rho\) would make the first term of (18)
\(N^{3+7\rho-o(1)}\). The inherited model-comparison error also remains
\(N^{3-o(1)}\). Neither is polynomially small.

For original \(E\), with

\[
A_{\rm exc}=2\sum_{h=1}^NC_N(h)^2,
\]

we retain

\[
E\le2E_{\rm corr}+2A_{\rm exc}.
\]

Using [P1]'s exceptional-energy upper bound gives

\[
E(N)\ll N^3\exp(-c\ell^{1/10})
+1_{q\ {\rm odd}}N^{2\beta+1}\frac{q^2}{\phi(q)^4}
+N^{4\beta-1}\frac{q^2}{\phi(q)^3}.
\]

The last two terms disappear only in the no-exception case. They cannot simply
be deleted otherwise.

No RH proof, fixed power saving, exceptional-zero exclusion, or improvement to
the published state of the art is claimed.

## 8. Existing evidence and review request

The coordinator ran one small \(N=64\) diagnostic of exact Bonferroni,
multiplicativity, and Abel identities. Those checks do not establish the
asymptotic conclusion.

No repository changes or new PR were made for this candidate before review.
The previous local file was `ENDPOINT_BOUND.md`; the reviewed argument was
supplied directly in the review request, without a file transfer.
