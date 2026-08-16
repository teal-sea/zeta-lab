# Global variational optimality for the `xi'` window

**Snapshot:** `8b10ede734258e9e966f6b889176d81a4d59964d`  
**Verdict:** Outcome A. The full Hilbert-space window optimization is a
coercive quadratic minimization, and its unique optimizing ray has a strictly
positive representative.

This note closes the functional-analytic obligation left implicit in
`RESULTS-xiprime.md`. It does not change the source derivation of the
functional or supply an interval enclosure for the reported decimal.

## Theorem

Let

\[
 I=[-1/2,1/2],\qquad
 \mathcal H=L^2_{\mathrm{even}}(I;\mathbb R)
\]

with inner product \(\langle f,g\rangle=\int_I f(s)g(s)\,ds\). For
\(|x|\leq1\), put

\[
 F_1(x)=|x|-4x^2+
 \sum_{k=1}^{\infty}\frac{(k-1)!}{(2k)!}(2|x|)^{2k+1},
\]

and define

\[
 (T_{F_1}v)(s)=\int_I F_1(s-t)v(t)\,dt,\qquad A=I+T_{F_1}.
\]

Then:

1. \(T_{F_1}\) is a bounded compact self-adjoint operator on \(\mathcal H\),
   and \(\|T_{F_1}\|_{2\to2}\leq4/9\).
2. \(A\) is bounded and self-adjoint, and
   \[
   \langle Av,v\rangle\geq\frac59\|v\|_2^2
   \quad(v\in\mathcal H).
   \]
   In particular, \(A^{-1}\) exists on all of \(\mathcal H\) and
   \(\|A^{-1}\|_{2\to2}\leq9/5\).
3. If \(w=A^{-1}\mathbf1\), then \(w\) has a continuous even representative
   satisfying
   \[
   w(s)\geq\frac15\qquad(s\in I).
   \]
4. The exact global value of the scale-one window quotient is
   \[
   c_1^*=\sup_{\substack{0\ne v\in\mathcal H\\v\geq0\ \mathrm{a.e.}}}
   \frac{\left(\int_Iv\right)^2}
   {\int_Iv^2+\iint_{I^2}F_1(s-t)v(s)v(t)\,ds\,dt}
   =\langle\mathbf1,A^{-1}\mathbf1\rangle.
   \]
   Equality holds exactly on the positive rays \(v=cw\), \(c>0\).
5. For the source functional
   \[
   c_\lambda(v)=
   \frac{\lambda(\int_Iv)^2}
   {\int_Iv^2+\lambda\iint_{I^2}
       F_1(\lambda(s-t))v(s)v(t)\,ds\,dt},
   \qquad0<\lambda\leq1,
   \]
   the optimized value \(c_\lambda^*\) is nondecreasing in \(\lambda\).
   Hence the global bandwidth-one optimum occurs at \(\lambda=1\), and its
   optimizing profile is proportional to \(A^{-1}\mathbf1\).

Equality with the source paper's physical-window class is not a consequence of
density in the whole nonnegative cone: Section 7.1 also requires radial
monotonicity.  `RESULTS-xiprime-admissible-closure.md` discharges that missing
condition.  It gives an exact-rational strict-concavity bound for
\(w=A^{-1}\mathbf1\), proves that \(w\) decreases strictly in \(|s|\), and
constructs source-admissible endpoint tapers converging to \(w\) in \(L^2\).

Farmer, Gonek, and Lee state the form-factor asymptotic for \(|x|<1\), and
Chirre, Goncalves, and de Laat give the uniformly convergent infinite-series
form on compact subintervals. The value at \(|x|=1\) above is its continuous
extension. Changing a kernel at that measure-zero boundary would not change
the quadratic form, and Remark 6.1 of the source paper separately admits the
bandwidth endpoint \(\lambda=1\).

## Proof

The series for \(F_1\) and its termwise integral converge uniformly on
\([-1,1]\). For \(0\leq x\leq1\), isolate the \(k=1\) term:

\[
 F_1(x)=x(1-2x)^2+
 \sum_{k=2}^{\infty}a_kx^{2k+1},\qquad
 a_k=2^{2k+1}\frac{(k-1)!}{(2k)!}>0.
\]

In particular, \(F_1\geq0\) on \([-1,1]\). Let

\[
 M=\int_0^1F_1(x)\,dx
   =\frac16+\sum_{k=2}^{\infty}b_k,
 \qquad b_k=\frac{a_k}{2k+2}.
\]

Here \(b_2=2/9\), and for \(k\geq2\),

\[
 \frac{b_{k+1}}{b_k}
 =\frac{2k}{(2k+1)(k+2)}\leq\frac15,
\]

because \((2k+1)(k+2)-10k=(2k-1)(k-2)\geq0\). Therefore

\[
 M\leq\frac16+\frac{2/9}{1-1/5}=\frac49.
\]

This integral also controls every row of the kernel. Write
\(a=s+1/2\in[0,1]\), and let

\[
 J(x)=\int_0^x u(1-2u)^2\,du.
\]

Then

\[
 J(1)-J(a)-J(1-a)
 =a(1-a)(2a^2-2a+1)\geq0.
\]

For every \(q\geq1\), \(a^q+(1-a)^q\leq1\). Applying this to every positive
monomial in the remaining series gives

\[
 \int_I F_1(s-t)\,dt
 =\int_0^aF_1(u)\,du+\int_0^{1-a}F_1(u)\,du
 \leq M\leq\frac49. \tag{1}
\]

The kernel is continuous and symmetric on \(I^2\). Hence \(T_{F_1}\) is
Hilbert-Schmidt, compact, and self-adjoint. The Schur test and (1) give
\(\|T_{F_1}\|_{2\to2}\leq M\leq4/9\). Notice that this says nothing about
compactness of \(A\), and no such claim is needed. It follows that

\[
 \langle Av,v\rangle
 \geq(1-\|T_{F_1}\|)\|v\|_2^2
 \geq\frac59\|v\|_2^2.
\]

The bounded coercive self-adjoint operator \(A\) is bijective, by the standard
coercive-operator theorem, and its inverse has norm at most \(9/5\).

Set \(w=A^{-1}\mathbf1\). The integral operator maps \(L^2(I)\) into
continuous functions, so \(w=\mathbf1-T_{F_1}w\) has a continuous
representative. Reflection invariance and uniqueness make it even. Let
\(m=\sup_s\int_I F_1(s-t)\,dt\leq4/9\). The same row bound on \(L^\infty\)
gives

\[
 \|w\|_\infty\leq1+m\|w\|_\infty,
 \qquad \|w\|_\infty\leq\frac1{1-m}.
\]

Since the kernel is pointwise nonnegative,

\[
 w(s)=1-\int_I F_1(s-t)w(t)\,dt
 \geq1-m\|w\|_\infty
 \geq\frac{1-2m}{1-m}\geq\frac15.
\]

This is optimizer positivity, separate from operator coercivity.

Define \(\langle f,g\rangle_A=\langle Af,g\rangle\). For every
\(v\in\mathcal H\),

\[
 \langle\mathbf1,v\rangle
 =\langle Aw,v\rangle
 =\langle w,v\rangle_A.
\]

Cauchy-Schwarz in the \(A\)-inner product yields

\[
 \langle\mathbf1,v\rangle^2
 \leq\langle Aw,w\rangle\langle Av,v\rangle
 =\langle\mathbf1,w\rangle\langle Av,v\rangle.
\]

Equality holds exactly when \(v\) is proportional to \(w\). Since
\(w\geq1/5\), the nonnegative cone contains the optimizing ray. This proves
the scale-one assertion.

Finally, put \(I_\lambda=[-\lambda/2,\lambda/2]\) and
\(f(u)=v(u/\lambda)\). A change of variables gives

\[
 c_\lambda(v)=
 \frac{(\int_{I_\lambda}f)^2}
 {\int_{I_\lambda}f^2+
   \iint_{I_\lambda^2}F_1(u-u')f(u)f(u')\,du\,du'}.
\]

If \(0<\lambda_1<\lambda_2\leq1\), extension by zero embeds every admissible
profile on \(I_{\lambda_1}\) into the class on \(I_{\lambda_2}\) without
changing this quotient. Thus \(c_\lambda^*\) is nondecreasing and the endpoint
\(\lambda=1\) is globally optimal.

## Numerical status

The theorem identifies the exact constant as

\[
 c^*=\langle\mathbf1,A^{-1}\mathbf1\rangle,
 \qquad H^*=2-\frac1{c^*}.
\]

The existing computations in `xiprime.py` give

\[
 c^*=0.8838931253605797508\ldots,
 \qquad H^*=0.8686415005297670641\ldots.
\]

After the argument above, the latter is legitimately the numerical evaluation
of the global variational optimum over \(0<\lambda\leq1\) and the full
nonnegative even window class. The displayed decimal remains a converged
high-precision numerical evaluation, not an interval enclosure of its last
digit.

## Sources and in-repository evidence

- The source paper, *More than two thirds of the zeros of the Riemann zeta
  function lie on the critical line*, equation (7.3), Theorem D, and Remark
  7.3: <https://www-cdn.anthropic.com/564f962e60643842f5fcb4a17c9dbc8f608f1c37.pdf>.
- D. W. Farmer, S. M. Gonek, and Y. Lee, *Pair correlation of the zeros of the
  derivative of the Riemann xi-function*, Theorem 1.1:
  <https://arxiv.org/abs/0803.0425>.
- A. Chirre, F. Goncalves, and D. de Laat, *Pair correlation estimates for the
  zeros of the zeta function via semidefinite programming*, the infinite-series
  form used above before its `xi'` lemma:
  <https://arxiv.org/abs/1810.08843>.
- `hunts/wide_search/RESULTS-xiprime.md` fixes the functional, normalization,
  comparison constants, and independent numerical evaluations.
- `hunts/wide_search/xiprime.py` evaluates the exact kernel and the Galerkin
  quotient.
