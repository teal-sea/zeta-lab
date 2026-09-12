# Multiscale sharp-frequency bounds in the CHHL upper-bound investigation

**Date:** 2026-09-06. **Status:** mathematical proof draft with executed finite/symbolic checks. No independent referee review, formal verification, novelty claim, or improved bound on total E(N) is claimed. Prepared in this conversation.

## 0. What this pass actually changes

The preceding `SHARP_TRANSFER.md` treated frequencies of order N^(-1/2). This pass extends its calculation to a range of scales, substitutes an established additive-energy estimate for its coarse density-based substitute, and accounts for all rational models in the resulting frequency region.

Put

\[
 c_* = 13-4\sqrt3 = 6.071796769724\ldots,\qquad
 \tau_* = 4/c_* = 0.658783577860\ldots,
\]
\[
 \kappa_* = 1-\tau_* = 0.341216422139\ldots,
 \qquad p_*=3-\tau_*=2.341216422139\ldots.
\]

Write e(t)=exp(2 pi i t), and use the actual sharp sums

\[
 F_N(\alpha)=\sum_{n=1}^{N}\Lambda(n)e(n\alpha),\qquad
 K_N(\alpha)=\sum_{n=1}^{N}e(n\alpha),\qquad D_N=F_N-K_N.
\]

The main derived estimate is, uniformly for 4 <= T <= N^(tau_*),

\[
 \boxed{\int_{T/(2\pi N)}^{2T/(2\pi N)}|D_N(\alpha)|^4d\alpha
        \ll_\epsilon \frac{N^{3+\epsilon}}{T}.}\tag{M1}
\]

The same bound holds for |F_N|^4 and for (|F_N|^2-|K_N|^2)^2, and on the reflected negative band. Fixed constant multiples of the T-range are allowed, with constants depending on those fixed multiples.

In particular:

* T=sqrt(N) recovers N^(5/2+epsilon), **not an improvement of that same band's exponent**.
* T=N^(tau_*) gives N^(p_*+epsilon) on a **different band**, at frequencies of order N^(-kappa_*).
* Summing the bands from T0 to N^(tau_*) costs O_epsilon(N^(3+epsilon)/T0), not the sum of worst-case independently chosen exponents.

For example, the whole symmetric frequency range

\[
 \frac{N^{-1/2}}{2\pi}\le |\alpha|\le\frac{N^{-\kappa_*}}\pi
\]

has that N^(5/2+epsilon) fourth-moment budget. Taking the inner edge down to N^(-11/20)/(2 pi) instead gives N^(51/20+epsilon). These are bounds on different regions and must not be compared as if their domains were equal.

Sections 5 and 6 respectively insert this growing region into the **original total-error inequality**, and show explicitly why shrinking the central interval does not remove the prime-counting obstruction. The central interval and the rest of the circle stay in the accounting.

## 1. Inputs, references, and assumptions

### Existing laboratory input

`teal-sea/zeta-lab/hunts/prime_pair_error/UPPER_BOUND.md`, content blob `d7efa161f3e2c690d50868d622293f9304552d86`, read in this session. For Q=floor(sqrt(N)/3), its equations (7), (8), and (16) define disjoint rational arcs and give

\[
 E(N)\le4M_Q+4I_Q+O(N^2\log^3N).\tag{B0}
\]

The definitions and decomposition needed to use this are restated in Section 5. The earlier A/B Wronskian project is not an input to any bound here, and its completed audit is not reopened.

### Published analytic inputs

1. Languasco--Zaccagnini, *A Cesaro Average of Goldbach numbers*, Section 4, equation (15) and its contour-error proof: https://arxiv.org/html/1206.0251
   We retain the constant residue in the explicit formula. We do not use their Cesaro theorem outside its range.
2. Heath-Brown's unconditional zero-additive-energy bounds, as stated in Gafni--Tao, *On the number of exceptional intervals to the prime number theorem in short intervals*, Section 3.2, and reproduced with a proof as Theorem 12.6 in the Analytic Number Theory Exponent Database: https://arxiv.org/html/2505.24017v1 and https://teorth.github.io/expdb/blueprint/zero-density-energy-chapter.html
3. The unit-interval zeta-zero count O(log(2+H)), with multiplicity; Stirling's formula; Chebyshev's psi(x) << x; Parseval; Young's inequality; Cauchy--Schwarz.
4. CHHL, *The error term in counting prime pairs*, Theorem 2 and Section 4: https://arxiv.org/html/2308.14888v1
   This fixes the total-error/RH objective, not an assumed pair-count estimate.

For a fixed sigma in [1/2,1), define

\[
 N^*(\sigma,H)=\#\{(\rho_1,\rho_2,\rho_3,\rho_4):
 \Re\rho_j\ge\sigma,\ |\Im\rho_j|\le H,
 |\gamma_1+\gamma_2-\gamma_3-\gamma_4|\le1\}.
\]

The convention includes multiplicity and both signs of the ordinates. The published bound is N^*(sigma,H) <<_(sigma,nu) H^((1-sigma) A*(sigma)+nu), for every fixed nu>0. We use only finitely many fixed sigma values for a prescribed final epsilon.

No RH, GRH, prime-pair independence, random-phase hypothesis, simplicity, zero-spacing condition, or moving-sigma uniformity is assumed. A priority search adequate to claim these component formulations are new has not been performed. The calculations below are our deductions from the stated inputs, not the statements of the cited short-interval theorem.

## 2. An exact, usable bound for the energy exponent

Use the following established Heath-Brown envelope:

\[
 A^*(\sigma)\le
 \begin{cases}
 (10-11\sigma)/[(2-\sigma)(1-\sigma)],&1/2\le\sigma\le2/3,\\
 (18-19\sigma)/[(4-2\sigma)(1-\sigma)],&2/3\le\sigma\le3/4,\\
 12/(4\sigma-1),&3/4\le\sigma<1.
 \end{cases}\tag{HB}
\]

It implies the uniform **bound on exponent values**

\[
 A^*(\sigma)\le c_*=13-4\sqrt3.\tag{E0}
\]

This is not a claim that the constants in the density estimates are uniform in sigma. Here is the exact maximization.

For the first branch set u=1-sigma. If u1=(1+2 sqrt(3))/11, then

\[
 c_*u(1+u)-(11u-1)=c_*(u-u_1)^2\ge0.\tag{E1}
\]

The root u1 lies in [1/3,1/2], so this branch attains c_*. Its location is sigma=1-u1=0.594172580442....

For the second branch, set c2=21/2-2 sqrt(5), u2=(1+2 sqrt(5))/19. Then

\[
 2c_2u(1+u)-(19u-1)=2c_2(u-u_2)^2\ge0.
\]

Thus this branch is bounded by c2=6.027864045000... < c_*. The third branch is at most 6 < c_*. These radical comparisons are exact. In particular c_*>6, and so tau_*<2/3.

The constant is the maximum of this **selected known envelope**, not an asserted optimal bound for A* or an optimal research route. More recent improvements near other real parts are not needed for this pass.

## 3. Extend the smoothed energy calculation to variable T

This section reproduces the necessary kernel calculation; no missing earlier attachment is required.

For z=N^(-1)-2 pi i alpha, set

\[
 \widetilde F_N(\alpha)=\sum_{n\ge1}\Lambda(n)e^{-n/N}e(n\alpha).
\]

The published contour formula gives

\[
 \widetilde F_N-1/z=-\sum_\rho\Gamma(\rho)z^{-\rho}
 -\frac{\zeta'}{\zeta}(0)
 +O\left(|z|^{1/2}[1+\log^2(2+N|\alpha|)]\right).\tag{Z0}
\]

All powers use the principal logarithm. The zero sum is absolutely convergent for each alpha because Re z>0. On alpha of order T/N, with 2 <= T <= C N^(tau_*) and fixed C, Stirling bounds a term at large |gamma| by

\[
 C_1\frac{N}{\sqrt T}(1+|\gamma|/T)^{1/2}e^{-c_1|\gamma|/T}.
\]

Consequently truncating at H=T(log N)^2 has error smaller than every fixed inverse power of N, uniformly in this T-range, using the unit-interval zero count. This permits finite sums before fourth powers and integrals are expanded.

### The four-zero kernel

For a finite strip sigma <= beta <= sigma+eta, sigma>=1/2, write

\[
 s=\log(N|z|/T),\quad
 \alpha(s)=\frac{\sqrt{T^2e^{2s}-1}}{2\pi N},\quad
 \vartheta(s)=-\arccos((Te^s)^{-1}).
\]

Exactly,

\[
 \Gamma(\rho)z^{-\rho}=b_\rho(s)e^{-i\gamma s},\qquad
 b_\rho(s)=\Gamma(\rho)(T/N)^{-\rho}e^{-\beta s}
             e^{\gamma\vartheta(s)}e^{-i\beta\vartheta(s)}.
\]

On a fixed smooth enlargement of the band, the Jacobian and its fixed-order derivatives are O(T/N), and derivatives of vartheta of positive order are O(1/T). For every fixed j, Stirling gives

\[
 |b_\rho^{(j)}(s)|\ll_j N^{\sigma+\eta}/\sqrt T.\tag{Z1}
\]

For |gamma|<=T the factor (|gamma|/T)^(beta-1/2) is bounded; the bounded-height zeros are absorbed in constants. Above T, differentiation's powers of |gamma|/T are absorbed by exponential decay. This proof does not require T=sqrt(N).

Insert a smooth nonnegative majorant and integrate twice by parts. Each four-zero kernel is bounded by

\[
 C\frac{N^{4(\sigma+\eta)-1}}T
 (1+|\gamma_1+\gamma_2-\gamma_3-\gamma_4|)^{-2}.\tag{Z2}
\]

There are no boundary terms. If b_j counts ordered pair sums of ordinates in [j,j+1), then Cauchy--Schwarz gives

\[
 \sum_{\mathcal Z^4}(1+|\gamma_1+\gamma_2-\gamma_3-\gamma_4|)^{-2}
 \le(1+\pi^2/3)\sum_jb_j^2
 \le(1+\pi^2/3)\operatorname{Energy}_1(\mathcal Z).
\]

For bins separated by a nonzero integer r, use the weight bound 1/r^2, then sum over r. This argument makes no spacing assumption on the individual zeros.

Inserting (E0) into (Z2) gives, with logarithmic and arbitrarily small power losses displayed schematically,

\[
 \int_{\alpha\asymp T/N}\left|\sum_{\rho\in\mathcal Z}
       \Gamma(\rho)z^{-\rho}\right|^4d\alpha
 \ll_{\sigma,\eta,\nu}
 N^{4(\sigma+\eta)-1}T^{c_*(1-\sigma)-1+\nu}
 (\log N)^{O(1)}.\tag{Z3}
\]

The key algebra is

\[
 N^{4\sigma-1}T^{c_*(1-\sigma)-1}
 =\frac{N^3}{T}\left(\frac{T^{c_*}}{N^4}\right)^{1-\sigma}.
\]

For T<=C N^(tau_*) the parenthesis is bounded by a fixed constant. The strip-width loss N^(4eta), the H^nu loss, and logarithms are absorbed in N^epsilon by choosing the fixed parameters small enough first. A finite strip partition then gives O_epsilon(N^(3+epsilon)/T) for all beta>=1/2. No limit through a moving sigma is taken.

For beta<=1/2, the derivative bound is instead O_j((N/T)^(1/2)), and the unit-interval zero count gives energy O(H^3 log^4 H). The resulting contribution is

\[
 O_\epsilon(N^{1+\epsilon}T^2).
\]

This is at most O_epsilon(N^(3+epsilon)/T) since T^3<=C^3 N^(3tau_*) and 3tau_*<2. The constant and contour error in (Z0) are smaller. Thus

\[
 \int_{\alpha\asymp T/N}|\widetilde F_N-1/z|^4d\alpha
 \ll_\epsilon N^{3+\epsilon}/T.\tag{SM}
\]

This extends the previous smoothed input to variable T using the stronger actual energy bound.

## 4. Return to the sharp cutoff, uniformly at these scales

For a sequence a_n with absolutely convergent damped series, define

\[
 B_N(\alpha)=\sum_{n\ge1}a_ne^{-n/N}e(n\alpha),\quad
 h_N(\beta)=\sum_{m=1}^{N}e^{m/N}e(m\beta),\quad
 S_N(\alpha)=\sum_{n=1}^{N}a_ne(n\alpha).
\]

The exact periodic convolution is S_N=B_N*h_N. The geometric sum gives

\[
 |h_N(t)|\le\min(eN,2/\|t\|),\qquad
 \|h_N\|_1\le L_N:=2e+4\log N.
\]

For I=[delta,2delta], J=[delta/2,4delta], 0<delta<=1/16, split B_N into its restrictions to J and J-complement. Young bounds the nearby part; Cauchy--Schwarz bounds the distant part because |alpha-u| on the circle is at least delta/2 there. In detail,

\[
 \int_I|(B_N1_J)*h_N|^4\le L_N^4\int_J|B_N|^4,
\]
\[
 \int_{J^c}|h_N(\alpha-u)|^2du\le16/\delta,
 \quad
 \int_I|(B_N1_{J^c})*h_N|^4\le256\|B_N\|_2^4/\delta.
\]

It follows that

\[
 \int_I|S_N|^4\le8L_N^4\int_J|B_N|^4
                  +2048\|B_N\|_2^4/\delta.\tag{LT}
\]

Set a_n=Lambda(n)-1. Parseval and Chebyshev imply ||B_N||_2^2 << N log(2N). The discrete damped baseline 1/(exp(z)-1) differs from 1/z by O(1) uniformly in our shrinking bands. Apply (SM) to J and take delta=T/(2 pi N). The distant term costs

\[
 \delta^{-1}(N\log N)^2\ll N^3\log^2N/T.
\]

A smaller initial epsilon absorbs the logarithms. This proves (M1), including the center's contribution to the convolution; nothing near zero was thrown away.

On I, |K_N|<<N/T and integral over the circle |D_N|^2 << N log N. Therefore

\[
 \int_I(|F_N|^2-|K_N|^2)^2
 \le8\int_I|K_N|^2|D_N|^2+2\int_I|D_N|^4
 \ll N^3\log N/T^2+N^{3+\epsilon}/T.
\]

Also integral_I |K_N|^4 << N^3/T^3. These imply the stated intensity and |F_N|^4 versions of (M1). Real coefficients give the negative band.

### Combine the bands rather than treating one at a time

Let 4<=T0<=N^(tau_*). Define

\[
 \mathcal B_N(T_0)=
 \{\alpha\in[-1/2,1/2]:T_0/(2\pi N)\le|\alpha|\le N^{\tau_*}/(\pi N)\}.
\]

Cover it by dyadic bands T=2^j T0, with the last band possibly truncated. Uniformity of (M1), and the geometric sum of 1/(2^j T0), give

\[
 \int_{\mathcal B_N(T_0)}|F_N|^4,
 \quad\int_{\mathcal B_N(T_0)}|D_N|^4,
 \quad\int_{\mathcal B_N(T_0)}(|F_N|^2-|K_N|^2)^2
 \ll_\epsilon N^{3+\epsilon}/T_0.\tag{COR}
\]

Each of the three quantities is bounded separately. This is a growing range of scales, not just finitely many bands at a fixed multiple of sqrt(N).

The best exponent from (M1) at its outermost scale is p_*=3-tau_*. This is an optimization of this derived bound and chosen published envelope. It does not claim the actual moment has this growth or that its exponent is optimal.

## 5. Insert the entire region into the original total-E accounting

Use Q=floor(sqrt(N)/3). The report's arcs are

\[
 I_{q,a}=\{\alpha:\|\alpha-a/q\|\le Q/(qN)\},\quad
 1\le q\le Q,\ (a,q)=1.
\]

Their union is the major-arc set; its complement is the minor-arc set. On I_(q,a) the model is

\[
 P_{q,a}(\alpha)=\mu(q)K_N(\alpha-a/q)/\phi(q).
\]

The disjointness and baseline inequality (B0) are the existing laboratory inputs. Define nonnegative restricted components

\[
 M_{\mathcal B}=\sum_{q,a}\int_{I_{q,a}\cap\mathcal B}
             (|F_N|^2-|P_{q,a}|^2)^2,
 \qquad
 I_{\mathcal B}=\int_{\mathfrak m_Q\cap\mathcal B}|F_N|^4.
\]

**The region is not assumed to consist only of q=1 and minor arcs.** At these larger frequencies it can meet many nonzero rational centers. Their model costs must be included.

Set delta_max=N^(tau_*)/(pi N). If an arc with q>=2 meets the region, its center's circular distance from zero is at least 1/q. Therefore

\[
 1/q\le\delta_{\max}+Q/(qN),\qquad
 q\ge(1-Q/N)/\delta_{\max}\ge1/(2\delta_{\max})
\]

for sufficiently large N. Since integral |K_N|^4=(2N^3+N)/3 <= N^3,

\[
 \sum_{q\ge2,a}\int_{I_{q,a}\cap\mathcal B}|P_{q,a}|^4
 \le N^3\sum_{q\ge1/(2\delta_{\max})}\frac{\mu(q)^2}{\phi(q)^3}
 \ll N^3\delta_{\max}^2\log^3N
 \ll N^{1+2\tau_*}\log^3N.\tag{RP}
\]

For the elementary tail estimate one may use q/phi(q) << log(2q) and sum q^(-3) log^3(2q). No estimate for primes in varying progressions is imported here.

The q=1 model, if present, contributes at most

\[
 \int_{|\alpha|\ge T_0/(2\pi N)}|K_N|^4\ll N^3/T_0^3.
\]

The intensity inequality gives

\[
 M_{\mathcal B}+I_{\mathcal B}
 \le2\int_{\mathcal B}|F_N|^4
      +2\sum_{q,a}\int_{I_{q,a}\cap\mathcal B}|P_{q,a}|^4.
\]

Since 1+2 tau_* < 3-tau_* and T0<=N^(tau_*), all model costs in (RP) fit into (COR). Consequently

\[
 \boxed{M_{\mathcal B}+I_{\mathcal B}
        \ll_\epsilon N^{3+\epsilon}/T_0.}\tag{PART}
\]

Define M_rest=M_Q-M_B>=0 and I_rest=I_Q-I_B>=0. Substitution into (B0) gives the explicit full-error statement

\[
 \boxed{E(N)\le4M_{\rm rest}+4I_{\rm rest}
                    +O_\epsilon(N^{3+\epsilon}/T_0).}\tag{TOTAL}
\]

The existing O(N^2 log^3 N) geometric budget is absorbed because 3-tau_*>2. The remaining integrals are not claimed small.

Two useful, distinct choices are:

| T0 | Inner edge of controlled region | Cost of controlled region |
|---|---|---|
| N^(1/2) | N^(-1/2)/(2 pi) | O_epsilon(N^(5/2+epsilon)) |
| N^(9/20) | N^(-11/20)/(2 pi) | O_epsilon(N^(51/20+epsilon)) |

The upper edge in both cases is N^(-kappa_*)/pi. The second choice extends further **toward zero** but has a worse bound, 2.55 instead of 2.5, on its larger region. The p_*=2.3412... bound concerns the outermost band alone, not either entire region in this table.

## 6. Test whether shrinking the central region actually evades the obstacle

It does not remove the necessary endpoint control. This can be quantified without an asymptotic prime theorem.

For an integer m>=1, define

\[
 \kappa_{N,m}(\alpha)=
 \left(\sum_{|j|\le(m+1)N}e(j\alpha)\right)
 \left|\frac{K_N(\alpha)}{N}\right|^{2m}.
\]

The second factor has nonnegative Fourier coefficients, total sum one, and support |j|<=m(N-1). Thus the Fourier coefficients of kappa lie in [0,1], equal one on |j|<=N+m, and vanish beyond |j|<=(2m+1)N-m. It follows that

\[
 \|\kappa_{N,m}\|_2^2\le(4m+2)N-2m+1.
\]

For the degree-(N-1) polynomial L_N(alpha)=|F_N(alpha)|^2-|K_N(alpha)|^2,

\[
 \psi(N)^2-N^2=L_N(0)=\int_{\mathbb T}L_N\kappa_{N,m}.
\]

For 0<|alpha|<=1/2, the geometric-sum bound yields

\[
 |\kappa_{N,m}(\alpha)|\le
 \frac1{2^{2m+1}N^{2m}|\alpha|^{2m+1}},
\]

and for 0<R<=N/2,

\[
 \int_{|\alpha|>R/N}|\kappa_{N,m}|\le
          \frac1{m2^{2m+1}R^{2m}}.
\]

Let

\[
 C_N(R)=\int_{|\alpha|\le R/N}(|F_N|^2-|K_N|^2)^2.
\]

Nonnegativity of Lambda gives |L_N(alpha)|<=psi(N)^2+N^2. Cauchy--Schwarz only on the core therefore proves the exact finite inequality

\[
 \boxed{|\psi(N)^2-N^2|\le
 \sqrt{[(4m+2)N-2m+1]C_N(R)}
 +\frac{\psi(N)^2+N^2}{m2^{2m+1}R^{2m}}.}\tag{CORE}
\]

For fixed tau0>0, put R=N^(tau0)/(2 pi) and choose a fixed m with 2m tau0>=2. By Chebyshev and division by psi(N)+N>=N,

\[
 |\psi(N)-N|\ll_m\sqrt{C_N(R)/N}+O_m(N^{-1}).\tag{END}
\]

Therefore a near-quadratic bound C_N(R)<<_epsilon N^(2+epsilon) for every epsilon is still RH-strength, even in this narrower core. For tau0<1/2 the core is contained in the original q=1 major arc for all sufficiently large N.

This is an exact localization deduction, not a claim that the core bound is impossible, a new proof of RH, or a new-to-literature result. It explains why summing the current annular estimates is not yet a global solution. Moving T0 toward a constant in (TOTAL) makes its proved cost tend back to the cubic scale, and it still leaves the other frequencies outside the controlled region.

## 7. What was achieved and what remains

**Derived in this pass:** the multiscale sharp bounds (M1), a complete frequency-region contribution (PART)/(TOTAL) including other rational models, and the general central localization inequality (CORE). These have written proofs above, based on the stated published inputs and existing laboratory baseline.

**Not achieved:** a stronger upper bound for total E(N); a near-quadratic bound on its core or on the complete minor arcs; an estimate for all frequency regions; a novelty determination; independent proof review.

The closest next analytic requirement is not another band count. The central term in (TOTAL) needs an estimate that addresses its prime-counting component, while the outer complement needs its own total-error bound. An improved envelope or a more efficient transfer could improve restricted costs, but cannot be presented as control of those missing pieces.

The original target is still unconditional E(N)<<_epsilon N^(2+epsilon) for every epsilon, which would imply RH through CHHL Theorem 2. This pass does not claim that target or a new fixed zero-free strip.

## 8. Reproduction and handoff

Run:

```bash
python -m pip install -r requirements.txt
OPENBLAS_NUM_THREADS=1 python check_multiscale.py
```

`checks.json` records the environment and exactly what ran:

* Two exact symbolic completed-square certificates for the energy-envelope maximization, plus exact exponent identities and a 5,000-point rational diagnostic grid.
* 512 exact signed-integer-weight reproducing identities, and 128 coefficient-plateau/norm checks, for N=1,...,32 and m=1,...,4.
* Three finite convolution checks and nine localized-transfer diagnostics at three frequency scales, including tau_*.
* Nine restricted major/minor-arc accounting diagnostics, including nonzero rational centers.
* Nine von Mangoldt central-localization diagnostics.

The integer and symbolic checks are exact. The integrations use floating-point Fourier grids and are not outward-rounded certificates. None verifies an infinite-zero estimate or an asymptotic theorem; those depend on the written argument and published inputs.

The package is self-contained as a new proof draft. `MULTISCALE.md` is a NEW OUTPUT, not a missing repository file. The only repository input for total-E accounting is the pinned `UPPER_BOUND.md` noted above.
