# Localized mixed energy for the corrected prime-pair target

2026-09-09. Base: #214 at cb0189db3863ac43b2314c7df1008636bd4da477.
The accepted bridge and #209-#214 are unchanged. This pass explicitly
uses the complete \(E_{\rm corr}\) as an RH-sufficient research target,
distinct from original \(E\). It does not revisit the bridge or the
exceptional lower bounds.

**Outcome.** The rational-kernel argument below gives a fixed power
saving for a specified part of the actual model's mixed energy:
denominators at least \(N^{1/10}\) contribute at most
\(N^{14/5+o(1)}\). Short kernels of length at most \(N^{3/5}\)
contribute at most \(N^{11/5+o(1)}\). The denominator-one, length-\(N\)
kernel admits a stronger arithmetic estimate than the inherited
uniform Fourier bound, using the classical prime number theorem.
Its decay is still subpolynomial.

These estimates do **not** save a fixed power in complete
\(E_{\rm corr}\). The first failed quantitative step in this positive
kernel approach is explicitly the long-window mean square in (20),
not a generic Fourier-polynomial obstruction. Other small denominators,
the centered \(|W|^2\) term, the model error, and their interactions
remain in the final budget (25). The best complete bound obtained
remains the inherited \(N^3\exp(-c_\kappa(\log N)^\kappa)\).

This is a handwritten deduction with finite algebra checks, pending
external verification. No novelty or optimality claim is made.

## 1. Definitions, inputs, and the brief guardrail

Write \(\ell=\log N\), \(Z=\exp(\ell^{1/10})\),
\(P=\prod_{p<Z}p\), \(b_Z=P/\phi(P)\), and
\(\nu(n)=b_Z1_{(n,P)=1}\). The model is exactly #212's
\[
 a(n)=\nu(n)\bigl(1-1_{\rm exc}\chi(n)n^{\beta-1}\bigr),
 \quad 1\le n\le N,\qquad
 w_n=\Lambda(n)-a(n).
\]
The exceptional data obey \(q<Z\) and
\(1-c_0/\log Z<\beta<1\). In their absence \(a=\nu\).
The function \(\Lambda\) includes every proper prime power.
Extend \(w\) by zero outside \([1,N]\). Set
\[
 F(\alpha)=\sum_{n\le N}\Lambda(n)e(n\alpha),\quad
 H(\alpha)=\sum_{n\le N}a(n)e(n\alpha),\quad W=F-H,\quad
 D_w=\sum_{n\le N}|w_n|^2.
\]

Since \(|a|\le2b_Z\), \(b_Z\ll\ell^{1/10}\), and
\(\sum\Lambda^2\sim N\ell\), the cross term is \(O(Nb_Z)\)
and \(\sum a^2=O(Nb_Z^2)=o(N\ell)\). Thus \(D_w\sim N\ell\).
Parseval and Cauchy give
\(\|W\|_4^2\ge D_w\). The coefficients of \(F^2\) have support
of size \(2N-1\) and sum \(\psi(N)^2\), so
\(\|F\|_4^4\ge\psi(N)^4/(2N-1)\).
The squared global Holder envelope is therefore
\(\gg N^{5/2}\ell\). This is only a lower bound on that envelope,
not on \(E_{\rm corr}\), and is not used in the attempt below.

Source inputs used:

- [Tao--Teravainen, arXiv:2107.02158v4](https://arxiv.org/html/2107.02158v4),
  Definition 2.1 for the model; Lemma 5.1 for the sieve estimate;
  Theorem 1.3(i) for the classical prime number theorem rate in (19).
  The existing linear-phase consequence of Theorem 2.7 is used only
  to bound ranges not improved here:
  \(\sup_\alpha|W(\alpha)|\ll_\kappa N e^{-c_\kappa\ell^\kappa}\),
  \(0<\kappa<1/10\). No stronger rate is requested from it.
- The sharp two-form sieve calculation in
  [SIEGEL_UNIFORMITY.md](SIEGEL_UNIFORMITY.md), equations (10)-(11),
  and its model-to-target comparison (18).
- The singular-series tail comparison in
  [UPPER_BOUND.md](UPPER_BOUND.md), Section 2.

The sampling estimate below is proved here, rather than invoking a
short-interval distribution theorem with an incompatible model or range.

## 2. Exact windows, including both boundary regions

For every integer \(1\le s\le N\) and real \(\theta\), define
\[
 T_s(\theta)=\int_{\mathbb T}|K_s(\alpha-\theta)|^2
                                      |W(\alpha)|^2\,d\alpha .
\]
Expansion and orthogonality give exactly
\[
 \boxed{\quad T_s(\theta)=
 \sum_{t=1-s}^{N-1}
 \left|\sum_{\max(1,t+1)\le n\le\min(N,t+s)}
                         w_ne(n\theta)\right|^2 .\quad}       \tag{1}
\]
Indeed the pair \(n,m\) occurs in precisely
\((s-|n-m|)_+\) integer windows. Expansion of the left side gives
the same weight and phase \(e((n-m)\theta)\).
The term \(s=1\) is \(D_w\). No interval is made periodic, and
the partially occupied windows at both endpoints are present.

## 3. Positive kernels derived from the actual sieve model

These kernels are not an asserted replacement for \(H\).
Their approximation error is derived and carried below. Define
\[
 \begin{aligned}
 U_s(\alpha)&=\sum_{n\le s}\nu(n)e(n\alpha),\\
 {\cal V}^0_s(\alpha)&=
 \sum_{d\mid P}\frac1{\phi(d)^2}
               \sum_{a\bmod d}^{*}|K_s(\alpha-a/d)|^2 .
 \end{aligned}                                               \tag{2}
\]
For an exceptional character define
\[
 \begin{aligned}
 T^\chi_s(\alpha)&=\sum_{n\le s}\nu(n)\chi(n)e(n\alpha),\\
 {\cal V}^\chi_s(\alpha)&=
 \sum_{\substack{d\mid P\\(d,q)=1}}\frac{q}{\phi(qd)^2}
               \sum_{a\bmod qd}^{*}|K_s(\alpha-a/(qd))|^2 .
 \end{aligned}                                               \tag{3}
\]
Every term is nonnegative. The sums are finite, though \(P\) is
large; they are mathematical sums, not a proposed computation.
In each family the sum of scalar weights over all frequencies is
exactly \(b_Z\):
\[
 \sum_{d\mid P}\frac1{\phi(d)}=b_Z,\qquad
 \sum_{\substack{d\mid P\\(d,q)=1}}\frac q{\phi(qd)}
 =\frac q{\phi(q)}
   \prod_{\substack{p<Z\\p\nmid q}}\frac p{p-1}=b_Z.             \tag{4}
\]

Here is the derivation, including the character weights. The
complete-period covariance of \(\nu\) at separation \(h\) is
\[
 \sigma_Z(h)=\prod_{p<Z}\alpha_p(h)
           =\sum_{d\mid P}\frac{c_d(h)}{\phi(d)^2}.
\]
For \(\nu\chi\) it is
\[
 \begin{aligned}
 \sigma^\chi_Z(h)
 &=\left(\frac q{\phi(q)}\right)^2
          S_*(h)\frac{c_q(h)}q\\
 &=\sum_{\substack{d\mid P\\(d,q)=1}}
                          \frac q{\phi(qd)^2}c_{qd}(h).
 \end{aligned}                                               \tag{5}
\]
Use the complete character autocorrelation
\(\sum_{r\bmod q}\chi(r)\chi(r+h)=c_q(h)\) from #212,
and \(c_qc_d=c_{qd}\) for \((d,q)=1\).
At \(h=0\), both covariances equal \(b_Z\).
This treats odd conductors and the 4- and 8-parts without changing
the frequency denominators.

Apply #212's sieve calculation with endpoint \(s-h\), retaining
the original \(N,Z\) and level \(D=\lfloor N^{1/4}\rfloor\).
For even \(h\) it yields, uniformly for \(0<h<s\le N\),
\[
 \begin{aligned}
 \sum_{n\le s-h}\nu(n)\nu(n+h)
      &=(s-h)\sigma_Z(h)+O(N e^{-c\ell^{9/10}}),\\
 \sum_{n\le s-h}\nu(n)\chi(n)\nu(n+h)\chi(n+h)
      &=(s-h)\sigma^\chi_Z(h)+O(N e^{-c\ell^{9/10}}).
 \end{aligned}                                               \tag{6}
\]
For the second formula sieve each admissible residue modulo \(q\)
and then multiply its count by the sign \(\chi(r)\chi(r+h)\).
There are at most \(q<Z\) residues. The remainder is bounded by
\[
 O\bigl(b_Z^2[N e^{-c\ell^{9/10}}+qD(1+\log D)]\bigr),
\]
as in #212, which is the stated error after reducing \(c\).
Odd \(h\) gives zero exactly in both formulas.

The diagonal uses the dimension-one version of the same lemma:
\(\sum_{n\le s}\nu(n)^2=s b_Z+O(N e^{-c\ell^{9/10}})\).
Also \((\nu\chi)^2=\nu^2\), since primes dividing \(q\) divide
\(P\). Thus (6), its diagonal, and Fourier expansion imply
\[
 \begin{aligned}
 |U_s|^2&={\cal V}^0_s+O(N^2e^{-c\ell^{9/10}}),\\
 |T^\chi_s|^2&={\cal V}^\chi_s+O(N^2e^{-c\ell^{9/10}})
 \end{aligned}                                               \tag{7}
\]
uniformly in \(s,\alpha\). This error is retained, not set to zero.
There is no truncation of the prime product in (2)-(7).

For the factor \(f(n)=n^{\beta-1}\), put
\[
 \lambda_s=f(s)-f(s+1)\ (s<N),\qquad \lambda_N=f(N).
\]
These are nonnegative and sum to \(f(1)=1\). Exact Abel summation
gives \(\sum_{n\le N}\nu(n)\chi(n)f(n)e(n\alpha)
=\sum_{s=1}^N\lambda_sT^\chi_s(\alpha)\).
Convexity and (7) therefore prove
\[
 |H|^2\le
 2{\cal V}^0_N+2\sum_{s=1}^N\lambda_s{\cal V}^\chi_s
                 +O(N^2e^{-c\ell^{9/10}}).                    \tag{8}
\]
With no exception one uses \(|H|^2={\cal V}^0_N+O(\cdots)\)
and omits the entire character family.
The factor 2 in (8) explicitly pays for the discarded cross term
between the two model components. It does not cost a power of \(N\).

Let \({\cal A}\) be the integral of the positive kernel sum on the
right of (8), without its error, against \(|W|^2\).
Then the actual mixed energy satisfies
\[
 {\cal M}:=\int|H|^2|W|^2
 \le{\cal A}+O(N^2D_we^{-c\ell^{9/10}}).                       \tag{9}
\]
Equation (1) expresses every summand in \({\cal A}\) as a window
energy for the actual arithmetic \(w_n\).

## 4. One rational aggregate estimate with all overlaps included

For a polynomial \(B(\alpha)\) with frequencies in any interval
of \(s\) consecutive integers and \(\Delta\)-separated points
\(\theta_j\) on the circle,
\[
 \sum_j|B(\theta_j)|^2
 \le C(s+\Delta^{-1})\sum_n|B_n|^2 .                         \tag{10}
\]
For an elementary proof modulate the polynomial so its frequencies
are \(0,\ldots,s-1\). Average \(|B|^2\) on the disjoint arcs of
length \(h=\min(\Delta,1/s)\) centered at the points. The discrepancy
from the value at the center is at most the integral of
\(|(|B|^2)'|\) on that arc. Summing and using
\(\|B'\|_2\le2\pi s\|B\|_2\) proves (10), with
\(C=16\) more than sufficient in the form
\(16(s+\Delta^{-1})\).

Apply (10) in each window in (1), then sum over its starting point.
Each coefficient occurs in exactly \(s\) windows, including boundary
windows. For reduced rationals with denominators in \([D,2D)\),
separation is at least \(1/(4D^2)\), so
\[
 \sum_{D\le r<2D}\sum_{a\bmod r}^{*}T_s(a/r)
                  \ll (s+D^2)sD_w.                         \tag{11}
\]
In (2), the scalar weight is at most \(b_Z^2/D^2\).
In (3), it is at most \(qb_Z^2/D^2\), because all prime
divisors of \(r=qd\) are below \(Z\). Within each family, a
reduced fraction occurs only once. The families can overlap;
they are bounded separately and retain their multiplicities.
No disjointness of the kernel tails is asserted.

For the portion \({\cal A}_{\ge R}\) with reduced denominator
at least \(R\), dyadic summation of (11) gives
\[
 \boxed{\quad
 {\cal A}_{\ge R}\ll
 b_Z^2(1+q)ND_w
       \left[\log(2qP)+\frac N{R^2}\right].
 \quad}                                                     \tag{12}
\]
In the no-exception formula take \(q=1\) just in this bound.
The \(N/R^2\) sum is geometric; it does not acquire the
\(\log(2qP)\) factor. The convex \(\lambda_s\) sum costs at most
its mass 1 and \(s\le N\).

Since \(q<Z\), \(b_Z\ll\ell^{1/10}\), and
\(\log P\le Z\log Z\), (12) implies for every fixed
\(0<\rho<1/2\), with \(R=N^\rho\),
\[
 {\cal A}_{\ge R}
           \ll N^{2+o(1)}+N^{3-2\rho+o(1)}.                 \tag{13}
\]
Take \(\rho=1/10\): this contribution is at most
\(N^{14/5+o(1)}\). All denominators beyond \(N\), up to the
full period, remain included in the first term of (12).
This is a denominator partition of positive kernels on the whole
circle, not a claim about disjoint major arcs.

For completeness, Cauchy in each window gives
\(T_s(\theta)\le s^2D_w\). Hence the portion with
\(s\le L_0=\lfloor N^{3/5}\rfloor\), over every frequency,
is at most
\[
       {\cal A}_{s\le L_0}\ll b_ZL_0^2D_w
                          \ll N^{11/5+o(1)}.                \tag{14}
\]
Only the character family has these shorter lengths in (8).
Partition first by \(s\le L_0\), then by \(r\ge R\);
this avoids double counting in the budget below.
The chosen cutoffs require no change to \(Z\), the source model,
or any endpoint.

## 5. The controlling long window: an arithmetic calculation

The remaining range includes \(s=N,r=1,\theta=0\), with scalar
weight 1 in (2). Let the actual residual prefix be
\[
                   A(k)=\sum_{n\le k}(\Lambda(n)-a(n)).
\]
The full-length window identity (1) becomes
\[
 \begin{aligned}
 T_N(0)
 &=\sum_{k=1}^N|A(k)|^2+
                      \sum_{k=1}^{N-1}|A(N)-A(k)|^2\\
 &=2\sum_{k=1}^{N-1}|A(k)-A(N)/2|^2
                         +\frac{N+1}{2}|A(N)|^2.             \tag{15}
 \end{aligned}
\]
Both incomplete boundary regions matter. The aggregate varies over
all prefixes, rather than fixing variables until no sum remains.

Here is an unconditional estimate for this actual arithmetic
quantity, including the exceptional model. The dimension-one sieve
with level \(D=N^{1/4}\) gives uniformly \(0\le t\le N\)
\[
 \sum_{n\le t}\nu(n)=t+O(N e^{-c\ell^{9/10}}).
                                                                    \tag{16}
\]
If an exceptional character is present, the corresponding count
in each reduced residue modulo \(q\) has main term \(t/\phi(q)\)
and error
\[
 O\bigl(b_Z[(N/q)e^{-c\ell^{9/10}}+D]\bigr).
\]
This follows by sieving primes not dividing \(q\); the CRT
remainder per divisor is \(O(1)\). Sum after multiplication by
\(\chi(r)\) and use \(\sum_r\chi(r)=0\).
Partial summation with \(n^{\beta-1}\), which has total variation
at most 1, gives
\[
 \sum_{n\le t}\nu(n)\chi(n)n^{\beta-1}
                     =O(N e^{-c'\ell^{9/10}}).               \tag{17}
\]
Here \(qD b_Z\le N^{1/3}\) for sufficiently large \(N\).
Thus in both cases, with no fixed-data assumption as \(N\) varies,
\[
              A(k)=\psi(k)-k+O(N e^{-c\ell^{9/10}})
                         \quad(0\le k\le N).                \tag{18}
\]
This step is a signed complete-period calculation for the model,
not a small coefficient-\(L^2\) assertion.

Put \(\mathcal L(N)=\ell^{3/5}(\log\ell)^{-1/5}\).
The classical prime number theorem, as stated in TT Theorem
1.3(i), bounds \(|\psi(k)-k|\) by
\(O(N e^{-c\mathcal L(N)})\) uniformly for \(k\ge\sqrt N\).
For smaller \(k\), \(O(\sqrt N\log N)\) suffices and is absorbed.
Equations (15)-(18) prove
\[
 \boxed{\qquad T_N(0)\ll
                  N^3e^{-c\mathcal L(N)}.\qquad}             \tag{19}
\]
This is an integrated estimate for a controlling kernel of the
actual mixed energy, stronger than using the inherited uniform
Fourier estimate for this kernel. It is still \(N^{3-o(1)}\).

The precise power estimate that this route has not established is,
for some fixed \(\eta>0\),
\[
 2\sum_{k=1}^{N-1}|A(k)-A(N)/2|^2
       +\frac{N+1}{2}|A(N)|^2
                        \ll N^{3-\eta}.                    \tag{20}
\]
Equation (19) does not imply (20): the ratio of its upper-bound
scale to \(N^{3-\eta}\) is
\(\exp(\eta\ell-c\mathcal L(N))\to\infty\).
This is a specific residual prime-counting mean square.
It is only necessary to power-bound this positive kernel
majorant separately, not a lower bound on \(E_{\rm corr}\).

Shortening the windows does not silently remove this issue.
If \(N=mL+r\), \(0\le r<L\), split a length-\(N\) window into
\(m\) length-\(L\) windows and its final remainder. Cauchy and
translation of the start variable give exactly the bound
\[
 T_N(\theta)\le(m+1)\bigl(mT_L(\theta)+T_r(\theta)\bigr),
 \qquad T_0=0.                                             \tag{21}
\]
A bound of size \(NL^2\varepsilon_N\) at those lengths returns
\(N^3\varepsilon_N\), not \(N^2L\varepsilon_N\).
For \(L=N^{3/5}\), the recombination cost is of order
\((N/L)^2=N^{4/5}\). A logarithmic mean-square saving in short
intervals therefore would not by itself give the required power.
No such theorem is assumed for \(w\) in this argument.

All other remaining kernels can still be bounded by the inherited
linear-phase input:
\[
 T_s(\theta)\le s\sup_\alpha|W(\alpha)|^2
             \ll_\kappa N^3e^{-c_\kappa\ell^\kappa}.
\]
Using their total scalar mass at most \(4b_Z\), the long,
small-denominator portion other than (15) satisfies the same
order bound after reducing \(c_\kappa\). This is a fallback
bound at its existing rate, not the arithmetic advance in
(12) and (19).

## 6. The complete corrected norm and where cancellation was lost

Use the unchanged \(y=\lfloor\sqrt N\rfloor\), \(V_y\), centering
operator \(\mathcal C\), and exact correction polynomial
\(\widehat C_N=2\sum_{h=1}^NC_N(h)\cos(2\pi h\alpha)\). Put
\[
 \begin{aligned}
 X&=\mathcal C(2\operatorname{Re}(\overline H W)),\\
 Y&=\mathcal C(|W|^2),\\
 R_{\rm mod}&=\mathcal C(|H|^2-V_y)-\widehat C_N .
 \end{aligned}
\]
The complete residual is exactly \(G_{\rm corr}=X+Y+R_{\rm mod}\),
and before making any upper estimate its squared norm is
\[
 \begin{aligned}
 \|G_{\rm corr}\|_2^2
 ={}&\|X\|_2^2+\|Y\|_2^2+\|R_{\rm mod}\|_2^2\\
    &+2\operatorname{Re}\langle X,Y\rangle
     +2\operatorname{Re}\langle X+Y,R_{\rm mod}\rangle .
 \end{aligned}                                               \tag{22}
\]
No sign or cancellation estimate for the last two terms has been
proved here. The rigorous upper bound at this point uses
\[
 \|X\|_2\le2\sqrt{\mathcal M},\qquad
 \|Y\|_2^2=\int|W|^4-D_w^2.                                 \tag{23}
\]
The exact subtraction \(D_w^2\) is retained.
The inherited model comparison and singular-series tail give
\[
 \|R_{\rm mod}\|_2
        \ll N^{3/2}e^{-c\ell^{1/10}}+N,\qquad
 |\sqrt{E_{\rm corr}}-\|G_{\rm corr}\|_2|\ll N.                \tag{24}
\]
Thus a complete, unconditional budget from this attempt is
\[
 \boxed{\quad
 \sqrt{E_{\rm corr}}\le
 2\sqrt{\mathcal M}
 +\sqrt{\int|W|^4-D_w^2}
 +C N^{3/2}e^{-c\ell^{1/10}}+C'N .
 \quad}                                                     \tag{25}
\]
This last triangle inequality explicitly relinquishes the
interaction in (22). It is not a claim that the terms of (22)
are independent or that their separate sizes lower-bound the norm.

The estimates above give, for every fixed \(0<\kappa<1/10\),
\[
 \begin{aligned}
 \mathcal M\ll_\kappa{}&
 N^{11/5+o(1)}+N^{14/5+o(1)}
 +N^3e^{-c\mathcal L(N)}
 +N^3e^{-c_\kappa\ell^\kappa}
 +N^3e^{-c\ell^{9/10}},\\
 \int|W|^4-D_w^2\ll_\kappa{}&
                         N^3e^{-c_\kappa\ell^\kappa}.
 \end{aligned}                                               \tag{26}
\]
The last line is the already available arithmetic \(U^2\) input,
not a new global Holder transfer. Substitution in (25) still yields
only
\[
                  E_{\rm corr}(N)
                  \ll_\kappa N^3e^{-c'_\kappa\ell^\kappa}.    \tag{27}
\]
Even a hypothetical improvement to (20) alone would leave the
other rational windows, \(Y\), and the explicitly quantified
model comparison in (24). Their cancellation with \(X\) has
not been estimated. Improving the transfer alone also cannot
delete the model term of squared size \(N^3e^{-c\ell^{1/10}}\).

The attempted localized estimate is therefore incomplete for a
power saving of total \(E_{\rm corr}\), at the explicit quantitative
steps just identified. It does establish (12)-(14) and (19) for
the actual model and actual von Mangoldt residual. It does not
improve original \(E\), prove a near-quadratic estimate, change
the sharp cutoff, or assert a new sufficient criterion.

## 7. Bounded evidence

The argument above was completed before the diagnostic.
The fixed check at artifacts/localized_mixed_energy/check.py uses
one numerical thread, \(N=64\), and a 60-second cap. It checks
the sharp window identity, complete-period spectra and their
weights, the positive Abel combination, the elementary rational
sampling bound on fixed finite blocks, the exact prefix identity
(15), and window recombination. Character fixtures are algebraic,
not assertions of exceptional zeros. The 4- and 8-part fixtures
need not meet \(q<Z_N\) at this small cutoff.

Finite checks do not validate the asymptotic sieve remainder,
the prime number theorem, or a scaling law for either error.
No earlier numerical batch is rerun.
