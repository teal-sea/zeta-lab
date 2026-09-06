# Sharp-cutoff transfer for a square-root-scale prime frequency band

**Date:** 2026-09-06. **Status:** self-contained written proof draft, with an executed finite checker. No independent referee, novelty claim, formal verification, or improvement to the total prime-pair error is claimed. Prepared in this conversation; not committed to Zeta Lab.

## 0. Result, scope, and change from the previous attempt

Let

\[
 F_N(\alpha)=\sum_{n=1}^{N}\Lambda(n)e(n\alpha),\qquad
 K_N(\alpha)=\sum_{n=1}^{N}e(n\alpha),\qquad e(t)=\exp(2\pi i t).
\]

For fixed \(0<a<b<\infty\), the argument below establishes, as a written derivation,

\[
 \boxed{\int_{a/\sqrt N}^{b/\sqrt N}|F_N(\alpha)-K_N(\alpha)|^4\,d\alpha
 \ll_{a,b,\epsilon}N^{5/2+\epsilon}\quad(\epsilon>0).}\tag{S1}
\]

The same holds on the reflected negative interval, for \(|F_N|^4\), and for the intensity discrepancy:

\[
 \boxed{\int_{a/\sqrt N}^{b/\sqrt N}
       (|F_N(\alpha)|^2-|K_N(\alpha)|^2)^2\,d\alpha
       \ll_{a,b,\epsilon}N^{5/2+\epsilon}.}\tag{S2}
\]

These use the actual cutoff \(n\le N\), not exponential damping. The elementary localization lemma in Section 2 repairs the failed de-smoothing inequality in the previous FEASIBILITY.md. The repair uses a global **second** moment for the input away from the band, rather than paying for its global fourth moment. It requires no new oscillatory cancellation estimate.

This controls the outer part of the report's q=1 major arc and one adjacent part of its minor arcs. It does **not** bound the complete q=1 arc, all minor arcs, all residual moments, or total \(E(N)\). In particular it does not remove the zero-frequency/prime-counting obstruction.

The comparison \(13/5\to5/2\) is an exponent improvement over the elementary Vaughan-plus-supremum bound **restricted to these same bands**. It is not an improvement to the report's bound on its complete \(I_Q\) or \(Z_Q\). No search sufficient to establish new-to-literature status has been performed. Classical Ingham--Huxley zero-density estimates suffice; the newest zero-energy envelope is unnecessary for this conclusion.

## 1. Inputs and provenance

The original target and accounting come from `hunts/prime_pair_error/UPPER_BOUND.md`, content blob `d7efa161f3e2c690d50868d622293f9304552d86`, equations (12), (16), and (18)--(31). The source read on 2026-09-06 has not changed from that blob.

Published analytic inputs used here:

1. Languasco--Zaccagnini, *A Cesaro Average of Goldbach numbers*, equation (15) and its contour-error proof:
   <https://arxiv.org/html/1206.0251>.
2. Gafni--Tao, *On the number of exceptional intervals to the prime number theorem in short intervals*, definitions of zero density and additive energy, the bound \(A^*\le3A\), and the soft-energy argument in Lemma 2.4:
   <https://arxiv.org/html/2505.24017v1>.
3. The classical Ingham and Huxley zero-density estimates as stated in Guth--Maynard, *New large value estimates for Dirichlet polynomials*, equations (1.2)--(1.3):
   <https://arxiv.org/html/2405.20552v1>.
   Taking the better of \(3/(2-\sigma)\) and \(3/(3\sigma-1)\) gives \(A(\sigma)\le12/5\) for \(1/2\le\sigma<1\).
4. Chebyshev's \(\psi(x)\ll x\), the unit-interval zero count \(O(\log(2+|t|))\), Stirling's formula, Parseval, Young's convolution inequality, and Cauchy--Schwarz.
5. CHHL, *The error term in counting prime pairs*, Theorem 2 and Section 4, for the full-error objective, not for an unproved prime-pair estimate:
   <https://arxiv.org/html/2308.14888v1>.

The preceding inputs are distinguished from the transfer and component deductions proved below. No RH, GRH, prime-pair independence, zero spacing, zero simplicity, or random-phase hypothesis is used.

## 2. A local de-smoothing lemma with an explicit distant-frequency budget

Work on \(\mathbb T=\mathbb R/\mathbb Z\), with normalized Lebesgue measure. For any sequence whose damped sum is in \(L^4\), put

\[
 B_N(\alpha)=\sum_{n\ge1}a_n e^{-n/N}e(n\alpha),\quad
 h_N(\beta)=\sum_{m=1}^{N}e^{m/N}e(m\beta),\quad
 S_N(\alpha)=\sum_{n=1}^{N}a_ne(n\alpha).
\]

For our coefficients the series is absolutely convergent, so the identity

\[
 S_N=B_N*h_N\tag{L1}
\]

follows directly by integration: equal positive Fourier indices survive and the exponential factors cancel. In the general \(L^4\) case it follows by the finite Fourier multiplier identity.

The geometric sum gives, for \(N\ge2\),

\[
 |h_N(t)|\le \min(eN,2/\|t\|),\qquad
 \|h_N\|_1\le 2e+4\log N=:L_N.\tag{L2}
\]

For the second pointwise bound, write \(r=e^{1/N}\). The denominator satisfies
\(|1-re(t)|\ge4\sqrt r\|t\|\), and the numerator is at most \(r(1+e)\). The resulting constant \(\sqrt e(1+e)/4\) is less than 2. Splitting the integral at \(1/N\) proves the displayed \(L^1\) bound.

Let \(0<\delta\le1/16\), \(I=[\delta,2\delta]\), and \(J=[\delta/2,4\delta]\), viewed in the circle. Split

\[
 S_N=(B_N1_J)*h_N+(B_N1_{J^c})*h_N=:S_{\rm near}+S_{\rm far}.
\]

Young's inequality yields

\[
 \int_I|S_{\rm near}|^4\le L_N^4\int_J|B_N|^4.\tag{L3}
\]

For \(\alpha\in I\) and \(u\notin J\), their circular separation is at least \(\delta/2\). Therefore

\[
 \int_{J^c}|h_N(\alpha-u)|^2du
 \le8\int_{\delta/2}^{1/2}t^{-2}dt\le16/\delta.
\]

Cauchy--Schwarz and then \(|I|=\delta\) give

\[
 |S_{\rm far}(\alpha)|^2\le(16/\delta)\|B_N\|_2^2,
 \qquad \int_I|S_{\rm far}|^4\le(256/\delta)\|B_N\|_2^4.\tag{L4}
\]

Combining with \(|u+v|^4\le8(|u|^4+|v|^4)\) proves the fully explicit lemma

\[
 \boxed{\int_I|S_N|^4
 \le8L_N^4\int_J|B_N|^4+
       \frac{2048}{\delta}\|B_N\|_2^4.}\tag{LT}
\]

**The central frequencies have not been omitted.** They belong to \(J^c\) and are controlled, together with all other distant frequencies, by (L4). At \(\delta\asymp N^{-1/2}\) and \(\|B_N\|_2^2\ll N\log N\), the distant-frequency cost is \(O(N^{5/2}\log^2N)\). The previous global-fourth-moment/Jensen estimate was too coarse to show this.

This lemma is elementary Fourier localization. Its correctness and its novelty are separate questions; no novelty is asserted.

## 3. The smoothed input, with its proof reproduced here

We reproduce the argument so this file does not depend on a missing earlier attachment.

For \(X\ge4\), set

\[
 z=X^{-1}-2\pi i\alpha,\qquad
 \widetilde F_X(\alpha)=\sum_{n\ge1}\Lambda(n)e^{-n/X}e(n\alpha).
\]

The contour identity in the cited Languasco--Zaccagnini source gives

\[
 \widetilde F_X-1/z
 =-\sum_\rho\Gamma(\rho)z^{-\rho}
  -(\zeta'/\zeta)(0)
  +O\bigl(|z|^{1/2}[1+\log^2(2+X|\alpha|)]\bigr).\tag{Z1}
\]

The sum is over nontrivial zeros, with multiplicity. The constant term is retained. All powers use the principal logarithm, with \(\Re z>0\).

### 3.1 A finite four-zero kernel on an annulus

Take \(T\asymp\sqrt X\) and \(\alpha\in[T/(2\pi X),2T/(2\pi X)]\). Stirling gives uniform exponential decay in \(|\gamma|/T\), so we may truncate the zeros at \(H=T(\log X)^2\) with an error smaller than every fixed negative power of \(X\). More explicitly, the modulus of a term is at most a constant times

\[
 (X/\sqrt T)(1+|\gamma|/T)^{1/2}e^{-c|\gamma|/T};
\]

sum this above \(H\), using the unit-interval zero count. This justifies expanding finite sums first.

Fix a strip \(\sigma\le\beta\le\sigma+\eta\), with \(1/2\le\sigma<\sigma+\eta\le1\). Set

\[
 s=\log(X|z|/T),\quad
 \alpha(s)=\frac{\sqrt{T^2e^{2s}-1}}{2\pi X},\quad
 \theta(s)=\arg z=-\arccos((Te^s)^{-1}).
\]

Then exactly

\[
 \Gamma(\rho)z^{-\rho}=b_\rho(s)e^{-i\gamma s},
 \quad
 b_\rho(s)=\Gamma(\rho)(T/X)^{-\rho}e^{-\beta s}
             e^{\gamma\theta(s)}e^{-i\beta\theta(s)}.\tag{Z2}
\]

On a fixed smooth enlargement of the annulus the Jacobian and its fixed-order derivatives are \(O(T/X)\); positive-order derivatives of \(\theta\) are \(O(T^{-1})\). Stirling consequently gives, for every fixed \(j\),

\[
 |b_\rho^{(j)}(s)|\ll_j X^{\sigma+\eta}/\sqrt T.\tag{Z3}
\]

For \(|\gamma|\le T\), the additional factor \((|\gamma|/T)^{\beta-1/2}\) is at most one, with bounded-height terms absorbed in constants. For larger heights, factors \((|\gamma|/T)^j\) are absorbed in the exponential decay. Negative ordinates on the positive annulus have the weaker damping; the same estimate covers both signs.

Insert a fixed smooth nonnegative majorant of the annulus and expand the fourth power. Two integrations by parts bound each four-zero kernel by

\[
 \frac{C X^{4(\sigma+\eta)-1}}{T}
 (1+|\gamma_1+\gamma_2-\gamma_3-\gamma_4|)^{-2}.\tag{Z4}
\]

There are no boundary terms. If \(\mathcal Z\) is the finite zero multiset in the strip, bin the ordered pair sums of ordinates into intervals \([m,m+1)\), with counts \(b_m\). Cauchy--Schwarz gives

\[
 \sum_{\mathcal Z^4}(1+|\gamma_1+\gamma_2-\gamma_3-\gamma_4|)^{-2}
 \le(1+\pi^2/3)\sum_m b_m^2
 \le(1+\pi^2/3)\operatorname{Energy}_1(\mathcal Z).\tag{Z5}
\]

Here \(\operatorname{Energy}_1\) counts quadruples whose displayed ordinate difference has absolute value at most 1. For bins separated by a nonzero integer \(j\), the weight is at most \(1/j^2\); this proves (Z5) without a zero-spacing hypothesis.

Thus

\[
 \int_{\alpha\asymp T/X}
       \left|\sum_{\rho\in\mathcal Z}\Gamma(\rho)z^{-\rho}\right|^4d\alpha
 \ll \frac{X^{4(\sigma+\eta)-1}}{T}
       N^*(\sigma,H).\tag{Z6}
\]

### 3.2 Only classical density bounds are needed here

The classical Ingham--Huxley envelope gives \(A(\sigma)\le12/5\). Choosing three zeros freely and using unit-interval zero counting for the fourth proves

\[
 N^*(\sigma,H)\ll_{\sigma,\nu}
 H^{(36/5)(1-\sigma)+\nu}\quad(\nu>0).\tag{Z7}
\]

At \(T\asymp\sqrt X\), the narrow-strip exponent in (Z6) is

\[
 4\sigma-\tfrac32+\tfrac{18}{5}(1-\sigma)
 =\tfrac{21}{10}+\tfrac25\sigma\le\tfrac52.\tag{Z8}
\]

Choose a finite strip partition fine enough for the prescribed epsilon. Absorb the strip-width and logarithmic losses by reducing the epsilon in the inputs. Only finitely many fixed sigma values occur; no uniform bound for a moving sigma approaching 1 is being assumed.

For zeros with \(\beta\le1/2\), (Z3) can be replaced by \(O_j((X/T)^{1/2})\). The unit-interval zero count gives energy \(O(H^3\log^4H)\); their fourth-moment contribution at \(T\asymp\sqrt X\) is \(O_\epsilon(X^{2+\epsilon})\). The constant and contour remainder in (Z1) are smaller still.

Using the triangle inequality in \(L^4\) over the finitely many strips proves, for any fixed \(0<a<b\),

\[
 \int_{a/\sqrt X}^{b/\sqrt X}|\widetilde F_X(\alpha)-1/z|^4d\alpha
 \ll_{a,b,\epsilon}X^{5/2+\epsilon}.\tag{SM}
\]

A finite dyadic annulus cover handles any such fixed interval.

## 4. Apply the local transfer to the actual sharp cutoff

Use \(a_n=\Lambda(n)-1\), so

\[
 B_N(\alpha)=\sum_{n\ge1}(\Lambda(n)-1)e^{-n/N}e(n\alpha),
 \quad S_N=F_N-K_N.
\]

Parseval, \(\Lambda(n)^2\le\Lambda(n)\log n\), and Chebyshev give

\[
 \|B_N\|_2^2=\sum_{n\ge1}(\Lambda(n)-1)^2e^{-2n/N}
 \ll N\log(2N).\tag{P2}
\]

For example, split \(n>N\) into dyadic blocks; their Chebyshev bounds are multiplied by exponentially small weights. The terms \(n\le N\) are bounded directly. This proof uses no information on cancellation in \(\psi(N)-N\).

Its baseline satisfies

\[
 \sum_{n\ge1}e^{-n/N}e(n\alpha)=\frac1{e^z-1}=\frac1z+O(1)
\]

uniformly on every fixed square-root-scale interval. Therefore (SM), with \(X=N\), supplies the local fourth moment required by (LT).

Take \(\delta=c/\sqrt N\), for fixed \(c>0\), and \(N\) large enough that \(\delta\le1/16\). The near part in (LT) is \(O_\epsilon(N^{5/2+\epsilon}\log^4N)\); choose a smaller epsilon first to absorb the logarithms. The far part is

\[
 O\left(\delta^{-1}(N\log N)^2\right)
 =O_c(N^{5/2}\log^2N).
\]

This proves (S1) on \([\delta,2\delta]\). A finite cover proves its stated \([a/\sqrt N,b/\sqrt N]\) version, and real coefficients give the reflected negative band.

On this band, \(|K_N|\ll_{a,b}\sqrt N\), while

\[
 \int_{\mathbb T}|F_N-K_N|^2
 =\sum_{n\le N}(\Lambda(n)-1)^2\ll N\log(2N).
\]

Writing \(D=F_N-K_N\), we have the exact identity

\[
 |F_N|^2-|K_N|^2=2\Re(\overline K_ND)+|D|^2.
\]

Its square is at most \(8|K_N|^2|D|^2+2|D|^4\). The first part integrates to \(O(N^2\log N)\), and the second has (S1)'s bound. This proves (S2). Separately \(|F_N|^4\le8|D|^4+8|K_N|^4\), with the kernel integral only \(O(N^{3/2})\), proving the stated \(|F_N|^4\) consequence.

### Same-band benchmark

For \(\alpha\asymp N^{-1/2}\), take \(q=\lfloor1/\alpha\rfloor\). Then \(q\asymp\sqrt N\) and \(|\alpha-1/q|<q^{-2}\). The Vaughan bound recorded in the lab gives \(|F_N|\ll N^{4/5}\log^{5/2}N\). Combining its square with the global second moment gives \(N^{13/5}\log^6N\) for the band's fourth moment (and the same exponent for the residual/intensity estimates). The written derivation above replaces that restricted bound by \(N^{5/2+\epsilon}\). This is not a claim that \(13/5\) was the strongest published estimate for this restricted band.

## 5. Explicit contribution to the report's TOTAL error inequality

Keep the report's \(Q=\lfloor\sqrt N/3\rfloor\), its disjoint arcs of radii \(Q/(qN)\), and its quantities \(M_Q\) and \(I_Q\). It established

\[
 E(N)\le4M_Q+4I_Q+O(N^2\log^3N).\tag{B0}
\]

Define the two symmetric bands

\[
 \mathcal A_N=\{Q/(2N)\le|\alpha|\le Q/N\},\quad
 \mathcal B_N=\{Q/N<|\alpha|\le2Q/N\}.
\]

The first is contained in the q=1 major arc, where its model is \(K_N\). The second is contained in the minor arcs. To check the latter, the nearest nonzero positive major-arc point starts no earlier than \(1/Q-1/N\); the inequality \(2Q^2+Q<N\) holds for these Q and large N. Endpoints have measure zero. The negative side follows by reflection.

Let

\[
 M_{\rm out}=\int_{\mathcal A_N}(|F_N|^2-|K_N|^2)^2,
 \quad I_{\rm adj}=\int_{\mathcal B_N}|F_N|^4.
\]

Both are \(O_\epsilon(N^{5/2+\epsilon})\) by (S1)--(S2); \(Q/\sqrt N\) stays between fixed positive constants, so the finite-cover uniformity applies. Set

\[
 M_{\rm remaining}=M_Q-M_{\rm out}\ge0,\qquad
 I_{\rm remaining}=I_Q-I_{\rm adj}\ge0.
\]

Substitution into (B0) gives the honest total-error budget

\[
 \boxed{E(N)\le4M_{\rm remaining}+4I_{\rm remaining}
             +O_\epsilon(N^{5/2+\epsilon}).}\tag{B1}
\]

No contribution has been dropped, subtracted without proof, or reclassified as noise. Formula (B1) says exactly how the restricted estimate enters the original problem.

## 6. What is still missing on the RH route

- The q=1 central interval \(|\alpha|<Q/(2N)\) remains in \(M_{\rm remaining}\). The endpoint obstruction in the earlier feasibility note still applies to the full q=1 arc.
- Other rational centers and the rest of the minor arcs remain uncontrolled at the desired near-quadratic scale.
- Even this band's \(5/2+\epsilon\) exponent is above \(2+\epsilon\). The local transfer's distant-frequency budget is also of \(5/2\) size; an improved smoothed estimate alone would not automatically lower it.
- The established total bound remains the lab's \(E(N)\ll_C N^3/(\log N)^C\), not (S1) or (S2).
- The CHHL aim remains an unconditional \(E(N)\ll_\epsilon N^{2+\epsilon}\) for every epsilon. Nothing here proves that family, RH, or a new zero-free strip.

Thus the specific smooth-to-sharp gap is closed for a square-root-scale band by this draft, but a global upper-bound advance is not. This is one component result to subject to independent proof review, not a completed route to RH or a reason to reopen the finished A/B audit.

## 7. Validation and handoff

`check_sharp_transfer.py` verifies the finite convolution identity using independently evaluated quadrature and Fourier coefficients, geometric-kernel bounds, a discretized version of the local split and Cauchy--Schwarz/Young inequalities, the rational-arc inclusion, exact exponent arithmetic, and direct finite von Mangoldt band calculations. Numerical integrations are diagnostics, not outward-rounded certificates; they are not a proof of an asymptotic estimate.

The JSON records precisely which tests ran, their tolerances, and the finite values. No zero ordinates were numerically estimated and no prediction coefficients were fitted.

This package is self-contained. For a lab handoff, its new source document is this file; there is no missing earlier UPPER_BOUND.md to find. The existing repository UPPER_BOUND.md is an input for the full-error accounting, with the exact blob pinned above. This conversation has not written to or merged any repository branch.
