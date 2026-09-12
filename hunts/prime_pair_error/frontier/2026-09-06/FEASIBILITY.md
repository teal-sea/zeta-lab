# Zero-energy feasibility check for the CHHL upper-bound investigation

Date: 2026-09-06. Prepared in this conversation.

## Result and scope

Two deductions are written out below.

1. A **smoothed, frequency-localized** fourth moment admits a direct zero-additive-energy estimate. Using even a coarse published energy bound gives an unconditional `X^(5/2+epsilon)` upper bound for this smoothed annulus. This is NOT a bound for the report's sharp-cutoff `I_Q`, `Z_Q`, `M_1`, or total `E(N)`. No novelty or new record is claimed.
2. An explicit finite Fourier kernel shows that the **unsplit sharp q=1 intensity discrepancy itself** retains the endpoint prime-counting obstruction. It was inaccurate to suggest that this obstruction appears only because the positive-moment decomposition discarded cancellation.

An elementary attempt to remove the exponential damping is recorded. It does not close the transfer to the report: taking absolute values in that transfer reintroduces the uncontrolled central-frequency moment.

Status: written mathematical derivations with finite identity checks. They have not received independent proof review or formal verification. The computations do not certify the asymptotic arguments. The original total-error upper-bound objective remains unchanged and unresolved by this check.

### Source of the target

Read `hunts/prime_pair_error/UPPER_BOUND.md` from `teal-sea/zeta-lab`, content blob `d7efa161f3e2c690d50868d622293f9304552d86`, especially equations (18), (22), (23), and (28)--(31). Its target uses a sharp integer cutoff. Its reported `N^(13/5) log^6 N` estimates concern specific unsmoothed components, not the smoothed object introduced here.

## 1. Published inputs versus deductions in this note

Published inputs used:

- CHHL, *The error term in counting prime pairs*, Theorem 2 and Section 4: https://arxiv.org/html/2308.14888v1
- Languasco--Zaccagnini, *A Cesaro Average of Goldbach numbers*, Section 4, especially equation (15), the contour representation underlying Lemma 1, and the gamma estimate (13): https://arxiv.org/html/1206.0251
- Gafni--Tao, *On the number of exceptional intervals to the prime number theorem in short intervals*, definition of zero additive energy, `A*(sigma) <= 3 A(sigma)`, the uniform bound `A(sigma) <= 30/13`, and the soft-energy argument in Lemma 2.4: https://arxiv.org/html/2505.24017v1
- ANTEDB, zero-density energy chapter, for the distinction between zero counts and zero additive energy: https://teorth.github.io/expdb/blueprint/zero-density-energy-chapter.html

The frequency change of variables, resulting annular estimate, and localization application are deductions written out here. The Fourier and complex-analytic tools are standard. A complete literature/priority search for these particular formulations has not been performed.

The published exceptional-set exponent is NOT substituted as a Fourier-moment exponent. The conversion below is derived directly for a different, explicitly defined integral.

## 2. A precise smoothed object

Write `e(t)=exp(2*pi*i*t)`. For `X>=4`, let

```
z(alpha) = X^(-1) - 2*pi*i*alpha,
S_X(alpha) = sum_{n>=1} Lambda(n) exp(-n/X) e(n*alpha),
B_X(alpha) = S_X(alpha) - 1/z(alpha).
```

The prime series converges absolutely. This exponential damping differs from the sharp cutoff in the report.

For `2 <= T <= X/10`, use the positive annulus

```
A(X,T) = [T/(2*pi*X), 2T/(2*pi*X)].
```

The negative annulus is its complex conjugate. In particular, `T=sqrt(X)` is the frequency scale `alpha ~ X^(-1/2)`.

The contour identity gives

```
B_X(alpha) = -sum_rho Gamma(rho) z(alpha)^(-rho)
             - (zeta'/zeta)(0) + R_X(alpha),

R_X(alpha) << |z(alpha)|^(1/2)
             [1 + log^2(2 + 2*pi*X*|alpha|)].
```

The constant term is kept explicitly. This uses the contour representation rather than silently dropping its residue at zero. All powers use the principal logarithm; `Re z>0`.

For fixed `X,alpha`, Stirling and `|arg z|<pi/2` give absolute convergence of the zero sum. On this annulus, zeros above height

```
H = T (log X)^2
```

may be removed with `O_A(X^(-A))` error, for any fixed `A`, once `X` is sufficiently large. Indeed the modulus of a term is at most a constant times

```
(X/sqrt(T)) (1+|gamma|/T)^(1/2) exp(-c |gamma|/T),
```

and the unit-interval zero count is `O(log(2+|gamma|))`. Summing the tail starting at `H` gives exponential decay in `log^2 X`; it is uniform for the stated range of `T`. Taking a larger constant in `H` is harmless. This permits working with finite sums before expanding a fourth power.

## 3. The actual zero-energy transfer

Fix `1/2 <= sigma < sigma+eta <= 1`. Let `Z` be any finite multiset of zeta zeros with

```
sigma <= Re rho <= sigma+eta,  |Im rho| <= H.
```

Write

```
G_Z(alpha) = sum_{rho in Z} Gamma(rho) z(alpha)^(-rho),
Energy_1(Z) = #{(rho1,rho2,rho3,rho4) in Z^4:
               |gamma1+gamma2-gamma3-gamma4| <= 1}.
```

Multiplicity is included. The following bound is obtained by the calculation below:

```
integral_{A(X,T)} |G_Z(alpha)|^4 d alpha
    << X^(4(sigma+eta)-1) / T * Energy_1(Z).                 (ZE)
```

The constant is uniform in `X,T,H` and in the particular zeros. It can depend on a fixed smooth majorizing cutoff. A finite set of bounded-height zeros only affects absolute constants.

### 3.1 Exact change of variables

Put

```
s = log(X |z| / T),
alpha(s) = sqrt(T^2 exp(2s)-1)/(2*pi*X),
theta(s) = arg z = -arccos(1/(T exp(s))).
```

Then

```
d alpha/ds = (T/(2*pi*X)) exp(2s)/sqrt(exp(2s)-T^(-2)),
theta'(s) = -1/sqrt(T^2 exp(2s)-1).
```

On any fixed smooth enlargement of the annulus, `s` ranges over an interval of bounded length, the Jacobian and its fixed-order derivatives are `O(T/X)`, and `theta`'s positive-order derivatives are `O(1/T)`.

For `rho=beta+i*gamma`, exactly

```
Gamma(rho) z^(-rho) = b_rho(s) exp(-i*gamma*s),

b_rho(s) = Gamma(rho) (T/X)^(-rho)
           exp(-beta*s) exp(gamma*theta(s)) exp(-i*beta*theta(s)).
```

The `gamma*s` oscillation is now separated. This is the missing conversion between averaging in Fourier frequency and additive relations among zero ordinates.

Stirling gives, for every fixed derivative order `j`,

```
|d^j b_rho(s)/ds^j| <<_j X^(sigma+eta) / sqrt(T).           (S)
```

To check uniformity, for `|gamma|<=T` and `beta>=1/2`, the additional factor is at most `(abs(gamma)/T)^(beta-1/2) <= 1`, apart from bounded-height constants. For larger heights, derivatives introduce powers of `abs(gamma)/T` but these are absorbed by `exp(-c abs(gamma)/T)`. Opposite signs of gamma have stronger, not weaker, damping on one side. No RH, spacing, simplicity, or random-phase assumption is used.

### 3.2 Four-zero kernel

Choose a fixed nonnegative smooth cutoff in `2*pi*X*alpha/T`, supported in `[1/2,4]` and at least one on `[1,2]`. Expand the fourth power after inserting that cutoff.

Each four-zero kernel is the integral of

```
b1(s) b2(s) conjugate(b3(s) b4(s))
* exp(-i*(gamma1+gamma2-gamma3-gamma4)*s)
* cutoff(s) * (d alpha/ds).
```

Two integrations by parts, using (S) and the compact support, bound its modulus by

```
C X^(4(sigma+eta)-1) / T
  * [1+|gamma1+gamma2-gamma3-gamma4|]^(-2).                 (K)
```

There are no boundary terms. The integral over the original annulus is bounded above by this smoothly majorized fourth moment.

For completeness, the soft energy is controlled by the unit energy without a spacing assumption. Let `b_m` count ordered pair sums `gamma1+gamma2` in `[m,m+1)`. Then

```
sum_{quadruples} [1+|gamma1+gamma2-gamma3-gamma4|]^(-2)
 <= (1+pi^2/3) sum_m b_m^2
 <= (1+pi^2/3) Energy_1(Z).
```

For bins whose indices differ by `j!=0`, use the weight bound `1/j^2`, then Cauchy--Schwarz on `sum_m b_m b_(m+j)`. Pairs of sums in the same bin differ by less than one. This proves (ZE).

### 3.3 Inserting a published energy estimate

By inclusion and the definition of `A*`, for fixed sigma and any `nu>0`,

```
Energy_1(Z) <= N*(sigma,H)
            <<_(sigma,nu) H^((1-sigma) A*(sigma)+nu).
```

With `H=T log^2 X`, (ZE) therefore gives, up to logarithmic factors and an arbitrarily small exponent allowance,

```
integral_{A(X,T)} |G_Z|^4
 << X^(4(sigma+eta)-1)
    T^((1-sigma) A*(sigma)-1+nu).                          (ZE-power)
```

The factor `T^(-1)` is part of this directly derived frequency kernel. It is not obtained by transplanting the exceptional-set formula.

At `T=sqrt(X)`, the narrow-strip exponent is

```
b(sigma) = 4*sigma - 3/2 + (1/2)(1-sigma) A*(sigma).
```

Even the coarse published inputs

```
A*(sigma) <= 3 A(sigma),   A(sigma) <= 30/13
```

give

```
b(sigma) <= 51/26 + (7/13)*sigma <= 5/2.
```

Divide `[1/2,1]` into a fixed, sufficiently fine number of strips, depending on the final epsilon, and use the triangle inequality in L4. The strip-width losses and the logarithms are absorbed in that epsilon. No uniform estimate for an infinitesimally moving sigma is assumed.

For zeros with `beta<=1/2`, Stirling instead gives the derivative bound `O_j((X/T)^(1/2))`; the unit-interval zero count gives total additive energy `O(H^3 log^4 H)`. Their contribution at `T=sqrt(X)` is `O_epsilon(X^(2+epsilon))`. The contour remainder and the retained constant are smaller still.

Consequently the calculation gives the restricted estimate

```
integral_{1/(2*pi*sqrt(X))}^{1/(pi*sqrt(X))}
  |sum_{n>=1} Lambda(n) exp(-n/X) e(n*alpha)
    - 1/(X^(-1)-2*pi*i*alpha)|^4 d alpha
       <<_epsilon X^(5/2+epsilon).                        (SMOOTH)
```

This is unconditional and uses no newest optimized envelope: the coarse energy bound already suffices. It is a derivation for a smoothed annulus, not a claim of a new theorem in the literature or an improvement to the report's total error.

## 4. The unsplit sharp q=1 term retains the endpoint obstruction

Return to the report's actual sharp sums

```
F_N(alpha) = sum_{n=1}^N Lambda(n)e(n*alpha),
K_N(alpha) = sum_{n=1}^N e(n*alpha),
D_N(alpha) = |F_N(alpha)|^2 - |K_N(alpha)|^2,
Q = floor(sqrt(N)/3),
M1(N,Q) = integral_{|alpha|<=Q/N} |D_N(alpha)|^2 d alpha,
R(N) = psi(N)-N.
```

The integral is on the circle represented by `[-1/2,1/2]`. For `N>=36`, `Q>=1`.

### 4.1 An explicit reproducing kernel

Define

```
Dir_{3N}(alpha) = sum_{|j|<=3N} e(j*alpha),
kappa_N(alpha) = Dir_{3N}(alpha) * |K_N(alpha)/N|^4.
```

The Fourier coefficients of `|K_N/N|^4` are nonnegative, supported on `|j|<=2N-2`, and have total sum one. Therefore the coefficients of kappa:

- lie in `[0,1]`;
- are supported on `|j|<=5N-2`;
- equal one on `|j|<=N+2`.

Since `D_N` has degree at most `N-1`, this gives the exact identity and bound

```
D_N(0) = integral_T D_N(alpha) kappa_N(alpha) d alpha,
||kappa_N||_2^2 <= 10N-3.
```

For `0<|alpha|<=1/2`,

```
|kappa_N(alpha)| <= 1/(32 N^4 |alpha|^5).
```

This follows from the usual geometric-sum formula and `sin(pi |alpha|)>=2|alpha|`. Consequently

```
integral_{|alpha|>Q/N} |kappa_N(alpha)| d alpha <= 1/(64 Q^4).
```

Also `|D_N(alpha)|<=psi(N)^2+N^2`, since Lambda is nonnegative. Applying Cauchy--Schwarz only on the selected arc gives the explicit finite inequality

```
|psi(N)^2-N^2|
 <= sqrt((10N-3) M1(N,Q)) + [psi(N)^2+N^2]/(64 Q^4).      (LOC)
```

No prime-pair conjecture enters this proof. Using `Q~sqrt(N)` and Chebyshev's `psi(N)<<N`, the last term is O(1). Even the elementary `psi(N)<=N log N` gives `O(log^2 N)`, which suffices.

As `psi(N)+N>=N`, (LOC) implies

```
|R(N)| <= sqrt(10 M1(N,Q)/N) + O(log^2 N/N).
```

Thus `M1(N,Q)<<_epsilon N^(2+epsilon)` for every epsilon would itself force the classical RH-strength bound on `R(N)`.

**Correction to the earlier framing:** keeping `|F|^2-|K|^2` intact can matter, but it does not eliminate the one-point obstruction. That obstruction is already present in this unsplit local expression. This is not an impossibility result: proving that bound is an RH-strength task, which is the original research ambition.

## 5. Attempted transfer back to the sharp cutoff

The difference between damping and cutting off cannot be ignored. There is an exact periodic de-smoothing formula. Let

```
B_disc,N(alpha) = sum_{n>=1} (Lambda(n)-1) exp(-n/N) e(n*alpha),
H_N(beta) = sum_{n=1}^N exp(n/N) e(n*beta).
```

Then

```
F_N(alpha)-K_N(alpha) = integral_T B_disc,N(alpha-beta) H_N(beta) d beta. (DS)
```

On the small annulus, `B_disc,N` differs from the object in (SMOOTH) by O(1), because its discrete baseline is `1/(exp(z)-1)=1/z+O(1)`.

The elementary geometric-series formula gives

```
|H_N(beta)| << min(N,1/||beta||),   ||H_N||_1 << log(2N).
```

Applying the direct absolute-value/Jensen estimate to (DS), for an annulus A, gives

```
integral_A |F_N-K_N|^4
 <= ||H_N||_1^3 integral_T |B_disc,N(u)|^4
       [integral_A |H_N(alpha-u)| d alpha] du.              (DS-abs)
```

For `A=[delta,2delta]`, `delta~N^(-1/2)`, and `|u|<=1/N`, the bracket is of constant order, not a negative power of N. In fact the numerator of H's geometric sum is bounded below by `e-1`, and its denominator has size comparable to delta there. Thus the available bound pays for the uncontrolled central-frequency fourth moment even when the output annulus is away from zero.

The annular estimate (SMOOTH) does not control that central moment. This elementary de-smoothing attempt therefore does **not** preserve the proposed gain. It is an identified failure of this inequality, not a theorem that no sharp-cutoff transfer can be proved.

There are also two independent scope gaps:

- The q=1 smoothed annulus is not the union of the report's minor arcs, which involves frequencies near other rational centers. Applying an explicit formula near those centers introduces Dirichlet L-functions with varying conductors and potentially mixed-character energy, not just the zeta energy used here.
- Even a sharp residual fourth-moment estimate would not by itself control the full intensity discrepancy or total E: the mixed term and the other arc components remain in the report's budget. Formula (LOC) makes the endpoint requirement explicit.

## 6. Computational checks and disposition

`check_feasibility.py` was executed successfully and writes `checks.json`.

It verifies:

- the exact reproducing identity on 512 integer-weight cases, with N=1,...,64;
- the soft-energy binning inequality on 80 synthetic ordinate sets;
- the gamma-term change of variables and the finite four-index expansion using six synthetic complex parameters (NOT zero data);
- the reproducing formula and local inequality with von Mangoldt weights at N=144,400,900.

The gamma-term reconstruction has relative error below 8e-14; the independently integrated change of variables below 5e-15. These are floating-point diagnostics, not outward-rounded certificates. The reproducing-kernel coefficient tests use integer numerators and exact integer equalities.

### What can be carried back to the lab

- The explicit inequality (LOC), with its short proof and checker.
- The gamma-kernel transfer (ZE) and restricted consequence (SMOOTH), as a written proof draft for review.
- The exact de-smoothing formula (DS) and the demonstrated loss in its absolute-value estimate.

### What must not be claimed

- No improvement to sharp `I_Q`, `Z_Q`, `M1`, or total `E(N)` was established here.
- No RH or GRH assumption was used in the deductions, but the desired sharp bound remains RH-strength.
- No new-to-literature status, independent referee endorsement, or formal verification is claimed.
