# Minor-arc level sets: the restriction estimate and its exact limitation

2026-09-08. Continuation from `UPPER_BOUND.md` at
`2da62eb9842db72d4f6bad09c6f13efe384d6ab7`.
This is one attempted replacement of the minor-arc supremum estimate:
retain the amplitude distribution and apply the prime restriction theorem.
The replacement fails to save a power. The written derivation below proves
the surviving component bound and constructs finite Fourier polynomials
showing that the analytic inputs used cannot imply a smaller exponent.
It makes no novelty claim. The mathematical arguments are not formalized.

## 1. Exact target and surviving budget

Use precisely the definitions in `UPPER_BOUND.md`, with
\[
 F_N(\alpha)=\sum_{n=1}^N\Lambda(n)e(n\alpha),\quad
 L=\log N,\quad Q=\lfloor\sqrt N/3\rfloor,\quad N\ge36.
\]
Here \(e(t)=\exp(2\pi it)\), and \(\Lambda(p^a)=\log p\) for every
integer \(a\ge1\). The major arcs have radii \(Q/(qN)\) at every reduced
\(a/q\), \(q\le Q\), including the circular arc at zero. Their complement
is \(\mathfrak m_Q\). In particular
\[
 |\mathfrak m_Q|\ge 1-2Q^2/N\ge7/9.
\tag{1}
\]
The total target is still
\[
 E(N)=2\sum_{k=1}^N
 \left[\sum_{n=1}^{N-k}\Lambda(n)\Lambda(n+k)
             -\mathfrak S(k)(N-k)\right]^2.
\]
There is no change of cutoff, separation range, weights, or target norm.
Write \(M_Q\) for the combined intensity error on the major arcs, as in
`UPPER_BOUND.md` (8), and \(I_Q=\int_{\mathfrak m_Q}|F_N|^4\).
Its proved reduction (16) is
\[
 E(N)\le4M_Q+4I_Q+O(N^2L^3).
\tag{2}
\]

The result of this attempt is
\[
 \boxed{I_Q\ll N^{13/5}L^6,\qquad
 E(N)\le4M_Q+O(N^{13/5}L^6)+O(N^2L^3).}
\tag{3}
\]
These are the existing exponent and budget, not improvements. The major-arc
term remains unestimated at the target strength. The existing unconditional
bound \(E(N)\ll_C N^3/L^C\), for every fixed \(C\), remains the available
bound with no unresolved component. It is not a result newly obtained here.

## 2. The source input, in the required normalization

Checked on 2026-09-08:

* Ben Green and Terence Tao, *Restriction theory of the Selberg sieve, with
  applications*, Journal de Theorie des Nombres de Bordeaux **18** (2006),
  147--182, [publisher PDF](https://jtnb.centre-mersenne.org/article/JTNB_2006__18_1_147_0.pdf).
  Proposition 4.2, (4.8), printed p.158 is the continuous extension estimate.
  The Remark on printed p.160 states its consequence for products of von
  Mangoldt functions. With their \(k=1,a_1=1,b_1=0\), every local density is
  \(1-1/p\), so their singular series is 1. It gives, for each **fixed**
  real \(p>2\),
  \[
     \int_{\mathbb T}|F_N(\alpha)|^p\,d\alpha
           \le C_p N^{p-1}.
  \tag{4}
  \]
  The source explicitly uses \(\Lambda\) and \(n\le N\) in this consequence.
  Thus (4) includes proper prime powers and the sharp cutoff directly.
  The general consequence is stated as a straightforward modification of
  the preceding proof. No minor-arc localization is in its statement.
* Hugh L. Montgomery and Robert C. Vaughan, *Multiplicative Number Theory II:
  Primes and Sieves*, [author-hosted manuscript](https://personal.science.psu.edu/rcv4/571s25/montgomery-vaughanII.pdf),
  Theorem 17.1, printed p.65, equations (17.28)--(17.29). The hypotheses
  \((a,q)=1\), \(|\alpha-a/q|\le q^{-2}\), and the full \(\Lambda\) sum
  were checked. Dirichlet approximation with \(\lceil N/Q\rceil\) on our
  minor set supplies \(Q<q\le2N/Q\). Consequently
  \[
    |F_N(\alpha)|\le B:=C_VN^{4/5}L^{5/2}
                    \quad(\alpha\in\mathfrak m_Q).
  \tag{5}
  \]
  The \(Nq^{-1/2}\) and \(\sqrt{Nq}\) terms are \(O(N^{3/4})\) here.
* For the existing reduction (2), the external tail input was rechecked in
  Goldston, Hunts and Ngotiaoco, *The Tail of the Singular Series for the
  Prime Pair and Goldbach Problems*, [arXiv:1409.2151v1](https://arxiv.org/html/1409.2151v1),
  Theorem 2, (1.16), and the definition of \(\mathcal T(y)\) in (1.14).
  Its one-sided sum has range \(1\le y\le\sqrt N\). Doubling that sum,
  as done in `UPPER_BOUND.md`, gives the two-sided tail budget used in (2).

These inputs are unconditional. This is a bounded applicability check, not
a search for the best theorem in all of the literature.

## 3. Execute the level-set replacement

Define the **minor-arc** distribution function
\[
   \mu_Q(V)=|\{\alpha\in\mathfrak m_Q:|F_N(\alpha)|>V\}|,
       \qquad V>0.
\]
It vanishes for \(V\ge B\). Tonelli applied to
\(x^4=\int_0^x4V^3\,dV\) gives the exact identity
\[
       I_Q=4\int_0^B V^3\mu_Q(V)\,dV.
\tag{6}
\]
There is no discretization or smoothing in (6).

Put \(d_N=\sum_{n\le N}\Lambda(n)^2\). Parseval and
\(d_N\le L\psi(N)\ll NL\) give one envelope. Markov applied to (4)
gives a second, retaining the distribution rather than only its support:
\[
 \mu_Q(V)\le
 \min\{1,\ d_N/V^2,\ C_pN^{p-1}/V^p\}.
\tag{7}
\]
If we use the restriction envelope alone, for fixed \(2<p<4\), (6) gives
\[
 I_Q\le\frac{4C_p}{4-p}N^{p-1}B^{4-p}
 \ll_p N^{13/5+(p-2)/5}L^{(5/2)(4-p)}.
\tag{8}
\]
The exponent calculation is
\(p-1+(4/5)(4-p)=13/5+(p-2)/5\). It is strictly worse than \(13/5\).
Equivalently, direct interpolation gives
\(I_Q\le B^{4-p}\int_{\mathfrak m_Q}|F_N|^p\), with the same powers.

Taking the minimum in (7) does not cure this. Fix constants so that
\(d_N\le C_dNL\). For \(0<V\le B\), the ratio of the restriction
envelope to this Parseval envelope is at least
\[
 \frac{C_pN^{p-1}V^{-p}}{C_dNLV^{-2}}
 \ge \frac{C_p}{C_dC_V^{p-2}}
      N^{(p-2)/5}L^{-1-(5/2)(p-2)}\longrightarrow\infty.
\tag{9}
\]
Thus for every fixed \(p>2\), throughout the entire available minor-arc
amplitude range, (4) supplies an asymptotically larger upper envelope.
The crossover would be
\(V\asymp_p N/L^{1/(p-2)}\), above \(B\), not below it.
Using (6) with the remaining envelope gives
\[
 I_Q\le4d_N\int_0^B V\,dV=2d_NB^2\ll N^{13/5}L^6.
\tag{10}
\]
The original pointwise inequality saves the harmless factor 2. Substitution
in (2) gives precisely (3).

Taking \(p=p(N)\downarrow2\) in (4) without an estimate for \(C_p\) is
unsupported. Even a hypothetical bounded endpoint constant would only
recover the exponent \(13/5\) in (8), not a smaller fixed exponent.
The obstruction below also rules out a power saving from the whole family
of global norm bounds, independently of this constant issue.

## 4. A polynomial obstruction to the proposed inference

This section proves a limitation of the inputs actually used in (7).
The examples are not von Mangoldt sums. They show that degree, coefficient
bounds, the minor-arc supremum, and all the global restriction-sized moments
do not suffice. Additional prime arithmetic would have to enter the argument.

For integers \(r\ge2\) put
\[
 d=2^{2r},\quad m=2^{3r},\quad N=dm=2^{5r}.
\]
Define two polynomials by
\[
 A_0(z)=B_0(z)=1,\qquad
 A_{s+1}=A_s+z^{2^s}B_s,\quad
 B_{s+1}=A_s-z^{2^s}B_s.
\tag{11}
\]
The coefficient blocks do not overlap, so each polynomial at level \(s\)
has degree \(2^s-1\) and coefficients in \(\{-1,1\}\). On \(|z|=1\),
expansion of the two squares proves inductively
\[
       |A_s(z)|^2+|B_s(z)|^2=2^{s+1}.
\tag{12}
\]
This proves the required property of the recursion directly.

Write \(D_m(t)=\sum_{j=0}^{m-1}e(jt)\), and form
\[
 H_A(\alpha)=e(\alpha)A_{2r}(e(\alpha))D_m(d\alpha),\qquad
 H_B(\alpha)=e(\alpha)B_{2r}(e(\alpha))D_m(d\alpha).
\tag{13}
\]
Both have exactly the frequencies \(1,\ldots,N\), with coefficients
\(\pm1\). Thus Parseval and (12) imply
\[
 \|H_j\|_2^2=N,\qquad
 \|H_j\|_\infty\le\sqrt{2d}\,m=\sqrt2N^{4/5}.
\tag{14}
\]
Counting equal sums of two indices in \(\{0,\ldots,m-1\}\) gives
\[
 \int_{\mathbb T}|D_m(d\alpha)|^4\,d\alpha
    =m^2+2\sum_{h=1}^{m-1}(m-h)^2=(2m^3+m)/3.
\tag{15}
\]
Also \(|A_{2r}|^4+|B_{2r}|^4\ge2d^2\) by (12). Consequently at least
one of the two polynomials, denoted \(H\), satisfies
\[
 \int|H|^4\ge d^2(2m^3+m)/3\ge(2/3)N^{13/5}.
\tag{16}
\]

The peaks can be placed in the **actual** minor set. Fubini gives
\[
 \int_0^1\int_{\mathfrak m_Q}|H(\alpha-\theta)|^4\,d\alpha\,d\theta
     =|\mathfrak m_Q|\int|H|^4.
\]
There is therefore a translate \(g(\alpha)=H(\alpha-\theta)\) with
\[
       \int_{\mathfrak m_Q}|g|^4\ge(14/27)N^{13/5}.
\tag{17}
\]
Translation preserves the frequencies and all global norms; its coefficients
have modulus 1. For **every** \(p>2\), even without fixing it first,
\[
 \int|g|^p\le\|g\|_\infty^{p-2}\|g\|_2^2
  \le2^{(p-2)/2}N^{(4p-3)/5}
  \le2^{(p-2)/2}N^{p-1}.
\tag{18}
\]
Thus these exact finite Fourier polynomials satisfy all the scalar norm
estimates imported in (7), but violate any proposed consequence
\(\int_{\mathfrak m_Q}|g|^4\ll N^{13/5-\delta}\) with fixed \(\delta>0\).

Their large-value distribution is explicit enough to locate the loss.
Set \(V_0=\sqrt{7/27}N^{4/5}\). The part of (17) with \(|g|\le V_0\)
is at most \(V_0^2\int|g|^2=(7/27)N^{13/5}\). Since
\(\|g\|_\infty^4\le4N^{16/5}\), the remaining part forces
\[
 |\{\alpha\in\mathfrak m_Q:|g(\alpha)|>V_0\}|
                \ge(7/108)N^{-3/5}.
\tag{19}
\]

Even nonnegative bounded coefficients do not remove this example's
limitation. If \(g=\sum c_ne(n\alpha)\), set
\[
 f_\omega(\alpha)=\sum_{n=1}^N[1+\Re(\omega c_n)]e(n\alpha),
       \qquad\omega\in\{1,-1,i,-i\}.
\]
The coefficients belong to \([0,2]\). Write
\(h(\alpha)=\overline{g(-\alpha)}\). Pairing the choices \(\omega\) and
\(-\omega\), and using
\(|u+v|^4+|u-v|^4\ge2|u|^4+2|v|^4\) twice, gives pointwise
\[
 \frac14\sum_\omega|f_\omega|^4
          \ge\frac1{16}(|g|^4+|h|^4).
\tag{20}
\]
The minor set is reflection invariant, so some \(f_\omega\) satisfies
\(\int_{\mathfrak m_Q}|f_\omega|^4\ge(7/108)N^{13/5}\).
On that set \(|K_N|\le N/(2Q)\le3\sqrt N\), and
\(f_\omega=K_N+(\omega g+\overline\omega h)/2\). Hence
\(\sup_{\mathfrak m_Q}|f_\omega|\le5N^{4/5}\), while
\(\|f_\omega\|_2^2\le4N\). Finally
\(\int|K_N|^p\ll_pN^{p-1}\), by integrating
\(\min(N,(2\|\alpha\|)^{-1})^p\); (18) and the triangle inequality
give \(\int|f_\omega|^p\ll_pN^{p-1}\). These examples still do not have
prime support or von Mangoldt coefficients.

## 5. The precise missing inequality and its effect on total E

For any threshold \(T\le B\), (6) also gives
\[
 I_Q\le T^2d_N+4\int_T^B V^3\mu_Q(V)\,dV.
\tag{21}
\]
Indeed the omitted interval integrates to
\(\int_{\mathfrak m_Q}\min(|F_N|,T)^4\le T^2d_N\).
At \(T=\sqrt N\), this part already costs only \(O(N^2L)\).

For example, the additional estimate
\[
 \mu_Q(V)\ll_\eta N^{2+\eta}V^{-4}
     \quad(\sqrt N\le V\le B),\quad\text{every fixed }\eta>0,
\tag{22, unproved}
\]
would imply \(I_Q\ll_\eta N^{2+\eta}L\) by (21). Taking
\(\eta=\epsilon/2\) would put the minor component within
\(O_\epsilon(N^{2+\epsilon})\). Even then (2) would give only
\[
       E(N)\le4M_Q+O_\epsilon(N^{2+\epsilon});
\]
the major component would still need its own estimate.

The first unsupported step of the attempted improvement is inferring (22),
or any fixed-power improvement of the Parseval envelope in the upper
amplitude range, from the global theorem (4). At \(V\asymp N^{4/5}\),
(22) asks for \(N^{-6/5+\eta}\); Parseval supplies only
\(O(N^{-3/5}L)\). Equation (9) shows that (4) cannot bridge that factor,
and (19) exhibits a polynomial distribution realizing the larger size.
This is a proved failure of that inference, not a refutation of (22) for
\(F_N\), and not a bound on a replacement target for \(E\).

## 6. Bounded verification

The self-contained polynomial identities (11)--(16) and (20) have a small
diagnostic in `artifacts/minor_level_sets/check.py`. It uses one process,
no worker threads, exact integer convolutions at \(N=32,1024\), and exact
Gaussian-integer checks of (20). Its saved JSON reports every case and
explicit pass counts. The \(N=32\) row checks algebra only; the asymptotic
example uses \(r\ge2\). A 20-second alarm bounds the run. No numerical
estimate of a discontinuous arc integral, no larger prime-pair computation,
and no scientific CI run is used. The translation argument is analytic.

These checks pin finite algebra, not an asymptotic prime estimate. The
source extraction and the polynomial argument also received a bounded
independent agent check. This is not external mathematical verification.
