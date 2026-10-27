# BOUNDS: P1 to P4, the a priori quadrature and tail bounds of the rebuild

Written 2026-10-26 for PREREG s1 (with amendment 1). Code: `bounds.py`;
tests: `test_bounds.py`. **Grade of everything in this file: derived
(ordinary arguments), unreviewed**, resting on the two cited inequalities of
s0. Where a test checks a bound against data, the check is measured: it can
show a bound is violated, never that it holds. Nothing here is a claim about
RH.

## 0. Objects, conventions, cited inequalities

- Modes (PREREG s1): φ̃_n = Σ_r c_r P_{k_r} on [0, 1] (even k_r ≤ 648 at
  280 modes), ∫_0^1 φ̃_n² = 1, read as exact decimals from kernel/'s
  `prolate_vectors(40, 0, nvec)`. ξ_n is φ̃_n on [−1, 1], so ‖ξ_n‖_2 = √2
  and ‖ξ_n‖_1 ≤ 2. For w ≥ 1, ζ_n(w) = norm_n η_n(w), η_n(w) =
  ∫_{−1}^{1} ξ_n(t) e^{2πiwt} dt = Σ_r c_r 2(−1)^{k_r/2} j_{k_r}(2πw), with
  norm_n = (1 − λ_n²)^{−1/2}. b_n(v) = Σ_{k≥0} ζ_n(2^k v) for v ≥ 1 (α = 1).
- Hats: ŵ(s) = ∫_1^∞ w(v) v^{−1/2−is} dv = ∫_0^∞ k(u) e^{−isu} du with
  k(u) = w(e^u) e^{u/2}.
- **(Landau)** |J_ν(x)| ≤ c x^{−1/3} for ν ≥ 0, x > 0, c = 0.7857468704…
  (L. J. Landau, J. London Math. Soc. (2) 61 (2000) 197–215); used with
  c ≤ 0.7858. Hence |j_k(x)| ≤ JB x^{−5/6}, JB = √(π/2)·0.7858 ≤ 0.98487,
  and **|ζ_n(v)| ≤ C_n v^{−5/6}**, C_n = 2·JB·norm_n·Σ_r|c_r|·(2π)^{−5/6};
  |b_n(v)| ≤ C_n v^{−5/6}/(1 − 2^{−5/6}).
- **(Kapteyn)** |J_ν(νt)| ≤ t^ν e^{ν√(1−t²)}/(1 + √(1−t²))^ν for
  0 < t ≤ 1 (DLMF 10.14.5). Used only to bound j_k(x) for k + ½ ≥ x beyond
  the order where the ball recurrence stops (`bessel_table`).
- **(Gauss)** For f analytic in the Bernstein ellipse E_ρ of [−1, 1] with
  |f| ≤ M there, the n-point Gauss-Legendre error is at most
  (64/15) M ρ^{−2n}/(ρ² − 1) (Trefethen, SIAM Rev. 50 (2008) 67–87,
  Thm 4.5). On a panel [a, b] the error scales by (b − a)/2 and E_ρ maps to
  the ellipse with semi-axes (b − a)(ρ ± 1/ρ)/4. Nodes and weights are
  arb's `legendre_p_root` balls, so the rule is the exact Gauss rule.
  **Corrected 2026-10-27 (s5):** that is the rate of the (n + 1)-point
  rule. The n-point bound is ρ² larger, (64/15) M ρ^{2−2n}/(ρ² − 1).
- `test_bounds.py` spot-checks Landau and Kapteyn against arb's J_ν on grids
  (measured).

## 1. P1: the Gauss panels in w (E3)

The w-integral of ζ̂_n(s) on [1, 2^K] is split into two_adic/'s panels
(`ta_mellin.w_nodes`): width h ≤ 2π/(2π + S/left), never straddling a
power of 2. Endpoints are exact floats, each panel ending where the next
begins (s1.1).

**Prop P1.** For |s| ≤ S and every panel [a, b] with ρ chosen so that
x_min = (a + b)/2 − (b − a)(ρ + 1/ρ)/4 > 0, with β = (b − a)(ρ − 1/ρ)/4,
the integrand g(w) = η_n(w) w^{−1/2−is} satisfies, on the image ellipse,

    |g| ≤ 2 e^{2πβ + Sβ/x_min} x_min^{−1/2},

so the panel error is at most (b − a)/2 · (64/15) · that · ρ^{−24}/(ρ² − 1)
for 12 nodes, and the hat error is norm_n times the sum over panels
(`e3_hat_bound`). **Corrected 2026-10-27 (s5):** ρ^{−24} is the 13-node
rate; for 12 nodes it is ρ^{−22}, and production now runs 13 nodes.

*Proof.* |e^{2πizt}| = e^{−2π Im(z) t} ≤ e^{2π|Im z|} for |t| ≤ 1, so
|η_n(z)| ≤ e^{2πβ}‖ξ_n‖_1 ≤ 2e^{2πβ}. |z^{−1/2−is}| = |z|^{−1/2}e^{s arg z},
with |z| ≥ x_min and |arg z| ≤ arctan(β/x_min) ≤ β/x_min. Then (Gauss). ∎

Since h(2π + S/a) ≤ 2π, the exponent is at most (π/2)(ρ − 1/ρ)(a/x_min), so
the panel error falls like e^{(π/2)ρ}ρ^{−24}: ρ = 15 where the ellipse fits
(1.8·mid/h ≥ 15), smaller near w = 1. **Value:** at the toy grid
(K = 6, S = 16) and at the production grid (K = 14, S' = 10^4) the totals
are pinned in `test_bounds.py`.

**For b̂.** b̂ = Σ_{k<K} r^k T(2^k) + …, with T(2^k) = Σ_{j≥k} lev_j + tail
and |r| = 2^{−1/2}, so the level errors enter b̂ with weight at most
Σ_k 2^{−k/2} = 1/(1 − 2^{−1/2}).

### 1.1 A defect this caught

The first G_z run (s4) used panel midpoints and widths computed in float64
(`mid = left + h/2`). Adjacent panels then overlap or leave gaps of one ulp,
and the balls cannot see it: G_z of four prolates came out as
0.9999999999999998 ± 6.5e−17 on the diagonal and 2e−16 ± 5e−17 off it, a
ball excluding the exact value 1 (the modes are orthonormal on [0, 1] to
1e−62). With exact shared endpoints, every entry contains δ_ij
(`test_bounds.py::test_gram_z_is_the_identity`). The same rule now holds for
the w-panels of the hats.

## 2. P2: the tail beyond W (E4)

For W ≥ 2^K, T_n(W; s) = ∫_W^∞ ζ_n(w) w^{−1/2−is} dw is computed from the
M-term integration-by-parts form of η_n and, per term, the J-term
asymptotic series of ∫_W^∞ e^{iaw} w^β dw.

**Prop P2.** (i) η_n(w) = Σ_{m<M} (−1)^m φ̃_n^{(m)}(1)[e^{iω}/(iω)^{m+1}
+ e^{−iω}/(−iω)^{m+1}] + R_M(w), ω = 2πw, with
|R_M(w)| ≤ ‖φ̃_n^{(M)}‖_{L1[−1,1]}/ω^M ≤ 2Σ_r|c_r|P_{k_r}^{(M)}(1)/ω^M.
(ii) For real a ≠ 0 and Re β < −1,
∫_W^∞ e^{iaw}w^β dw = −e^{iaW}Σ_{j<J}(−1)^j (β)_j W^{β−j}/(ia)^{j+1} + ρ_J,
(β)_j the falling factorial, |ρ_J| ≤ |(β)_J| a^{−J} W^{Re β−J+1}/(J − Re β − 1).
Hence |T_n − expansion| ≤ norm_n[‖φ̃^{(M)}‖_1(2π)^{−M}W^{1/2−M}/(M − ½)
+ Σ_{m<M} 2|φ̃^{(m)}(1)|(2π)^{−(m+1)}|ρ_J(β_m)|], β_m = −(m + 1) − ½ − is
(`e4_tail_bound`).

*Proof.* (i) M integrations by parts on [−1, 1]; ξ even gives
φ̃^{(m)}(−1) = (−1)^m φ̃^{(m)}(1); |P_k^{(m)}| ≤ P_k^{(m)}(1) on [−1, 1]
(the derivatives are positive multiples of Gegenbauer polynomials, maximal
at 1). Integrate |R_M| w^{−1/2} from W. (ii) J integrations by parts; the
remainder is (−1)^J(β)_J(ia)^{−J}∫_W^∞ e^{iaw}w^{β−J}dw. ∎

**The k-series of b̂** (k ≥ K): terms K ≤ k < k_b by the same expansion
at W = 2^k, the rest by Landau: |T_n(2^k; s)| ≤ ∫_{2^k}^∞ C_n w^{−4/3} =
3C_n 2^{−k/3}, so Σ_{k≥k_b} 2^{−k/2}|T| ≤ 3C_n 2^{−5k_b/6}/(1 − 2^{−5/6})
(`b_kseries_tail`).

**An observation about the stored route (not a defect claim).**
two_adic/'s `hats_modes` sums the k ≥ Kmax terms with only 5 derivatives
and 8 series terms (`_tail_modes(..., mmax=4, terms=8)`). By (i), the
remainder of that truncation at W = 2^14 for the highest modes is not small
a priori. The value is pinned in `test_bounds.py`. Its effect on the
stored rows is not measured here.

## 3. P3: the s-rule (amendment 1)

### 3.1 Why the Gauss s-panels did not close

A Gauss bound needs |ρ(z)| on an ellipse in the strip |Im z| < ½, i.e. the
hats continued off the line: |ŵ_i(s + iτ)| ≤ ∫|w_i| v^{−1/2+τ}. With the
pointwise bounds available (Landau, or one integration by parts), this is of
order 10^3 per hat at 280 modes, so |ρ| ≲ ‖G^{−1}‖ Σ_i|ŵ_i|² ~ 10^10 per
panel against ρ_B^{−16} ~ 10^{−6} at panel width ½. It does not close.

### 3.2 The trapezoid rule and its aliasing (Prop P3a)

With s_k = kΔ, k ∈ ℤ: if F(s) = (1/2π) φ̂_1(s) conj(φ̂_2(s)), with
φ̂(s) = ∫ φ(u)e^{−isu}du and φ_1, φ_2 ∈ L¹ ∩ L², then (Poisson summation)

    Δ Σ_k F(kΔ) − ∫ F ds = Σ_{μ≠0} ∫ φ_1(y + 2πμ/Δ) conj(φ_2(y)) dy.

The window entry (m, n) of M_Q is Σ_ij G^{−1}_ij times such an F with
φ_1 = k_i ∗ U_n and φ_2 = k_j ∗ U_m: ŵ_i V̂_n is the transform of the
convolution, and V̂ is the transform of U on [−L/2, L/2]. From Landau,
|k_i(u)| ≤ C_i e^{−u/3} on u ≥ 0, so |φ(u)| ≤ L^{1/2}C_i e^{−(u−L/2)/3} on
u ≥ −L/2 (zero below), and for U > 0

    ∫ |φ_1(y + U)||φ_2(y)| dy ≤ 1.5 L C_i C_j e^{2L/3} e^{−U/3}.

With q = e^{−2π/(3Δ)}: **|alias(m, n)| ≤ Σ_ij|G^{−1}_ij|C_iC_j ·
1.5 L e^{2L/3} · 2q/(1 − q)**, and the spectral norm is at most (2N + 1)
times that, for each family (`p3_alias_entry`). The same argument without U
gives the aliasing of the Gram sums: (Δ/2π)Σ_k ŵ_i conj(ŵ_j)(kΔ) =
G_ij + alias_ij, |alias_ij| ≤ 1.5 C_iC_j · 2q/(1 − q).

*Sharpness check.* For k(u) = e^{−u/3}: (Δ/2π)Σ_k|k̂(kΔ)|² − ‖k‖² =
(3/2)(coth(π/(3Δ)) − 1) = 3q/(1 − q), exactly the bound
(`test_bounds.py::test_poisson_bound_is_sharp_on_the_model`).

At Δ = 1/16, q = e^{−33.5} = 2.8e−15. With Σ_n C_n² = 5.2e4 at 280
modes (RUNS.md), the ζ family's aliasing is of order 1e−6 per entry.
The b family's G_b^{−1} enters only once G_b exists (P4).

### 3.3 The truncation |s| > S' (Prop P3b)

Since ρ_Q ≥ 0 pointwise and |g_v(s)|² ≤ κ(S') for |s| > S' (bound_quad/
Prop 2), the omitted nodes contribute at most κ(S')·(Δ/2π)Σ_{all k}ρ(kΔ) =
κ(S')(nvec + Σ_ij G^{−1}_ij alias_ij) in each family, and so at most that
to ΔT (a difference of two such non-negative forms). **P3 total** =
(2N + 1)(alias_z + alias_b) + κ(S')(nvec + max alias_ρ) (`p3_total`).

## 4. P4: the Gram matrices in v-space

### 4.1 The quadrature region

∫_a^b ζ_i(u)ζ_j(2^m u) du by 12-node Gauss panels of width at most
min(1/(1 + 2^m), 1.8a/15), with exact shared endpoints. On the panel
ellipse, |ζ_i(z)ζ_j(2^m z)| ≤ 4 norm_i norm_j e^{2πβ(1+2^m)} (as in P1), so
the (Gauss) bound applies (`quad_pair`). Values ζ_n at the nodes come from
`bessel_table`. It runs the upward recurrence in balls at raised precision
(nodes and 2πw recomputed at that precision), stops at the first order whose
ball radius passes 2^{−(prec+8)}, and from there uses [0 ± Kapteyn]. The
extra precision doubles until the Kapteyn bound at the hand-over order is
below 2^{−(prec+8)}.

### 4.2 G_z: closed (Prop P4z)

G_z = ∫_1^{2^K} ζ_iζ_j + ∫_{2^K}^∞ ζ_iζ_j. The first part is s4.1 with m = 0.
For the second, multiply the two M-term expansions of P2 (i). The products
are e^{i(σ+τ)ω}ω^{−(p+q+2)} terms: σ + τ = 0 integrates exactly to
W^{−(p+q+1)}/(p + q + 1), and σ + τ = ±2 by P2 (ii) with its remainder. The
expansion remainders contribute at most ∫(C_i u^{−5/6} r_j + r_i C_j u^{−5/6}
+ r_i r_j), r(u) = norm‖φ̃^{(M)}‖_1(2πu)^{−M} (`gram_z_tail`). M is the
smallest with norm‖φ̃^{(M)}‖_1(2πW)^{−M} < 1e−30 for every mode
(`choose_M`). **Check:** on four prolates at K = 10, every entry contains
δ_ij, with radius 6.2e−13 at (0, 0) and below 1e−15 elsewhere. That is an
independent check of the tables, the panels, the expansion and its bounds,
since the identity is the prolates' double orthogonality, used nowhere in
the computation.

### 4.3 G_b: the decomposition, and the region that is built

With l ≥ k and u = 2^k v,
∫_1^∞ ζ_i(2^k v)ζ_j(2^l v) dv = 2^{−k}∫_{2^k}^∞ ζ_i(u)ζ_j(2^{l−k}u) du.
Write P_ij(m, t) = ∫_{2^t}^{2^{t+1}} ζ_i(u)ζ_j(2^m u) du. Summing over k ≤ t
gives the weight w_t = Σ_{k≤t}2^{−k} = 2 − 2^{−t}, so

    G_b = Σ_{t≥0} w_t [P(0, t) + Σ_{m≥1}(P(m, t) + P(m, t)ᵀ)].

The (m, t) plane splits into three regions:

- **A** (t + m + 1 ≤ K): both factors are below the asymptotic threshold;
  quadrature, s4.1. **Built** (`gram_b_region_a`). At most 12·2^K nodes per
  piece, about K²/2 pieces.
- **B** (t < K ≤ t + m + 1): the second factor is in its expansion range,
  the first is not. The piece is ∫ ζ_i(u) e^{±2πi2^m u}(2^m u)^{−q−1} du at
  frequency 2π2^m. For m ≤ 3 it is quadrature as in A (at most 9·12·2^K
  nodes). For m ≥ 4, R integrations by parts with endpoint derivatives
  ζ_i^{(a)} (a linear map of the Bessel table) and remainder
  ∫|f^{(R)}|/Ω^R, the ratio per step being about 2^{−m}. **Not built.**
- **C** (t ≥ K): both factors are expansions. That is s4.2 with σ2^0 + τ2^m
  frequencies; only m = 0 has non-oscillating terms. **Not built** for m ≥ 1.
- **The m-tail:** by Landau, |P(m, t)| ≤ 1.5 C_iC_j 2^{−5m/6}(2^{−2t/3} −
  2^{−2(t+1)/3}), so Σ_{m≥m₀} contributes at most
  10.9 C_iC_j 2^{−5m₀/6}. That is about 5.7e5·2^{−5m₀/6} in norm at
  280 modes, which forces m₀ ≈ 50, so regions B and C must be built for m
  up to about 50.

### 4.4 Status

**P4 is not closed**: G_z is, G_b's region A is, and regions B and C are
derived in outline (s4.3) and not built. `bounds.gram_b` raises
`NotImplementedError`, and a run with the exact provider stops before any
block, which is PREREG row D0 (coordinator, 2026-10-26: 'go' waits for
P4). The toy provider `toy-region-a` (G_b from region A only) exists for the
pipeline tests and is never read as a bound: `rebuild.assemble` marks such a
run D0.

## 4.5 G_b, regions B and C (2026-10-26, third unit)

`bounds.ibp_pieces`, `bounds.gram_b`; tests `test_p4.py`. **Grade: derived
(ordinary argument), unreviewed; each region checked against direct
quadrature at toy size (measured), each with a planted fault that the check
catches.**

**The fast factor.** For m ≥ 1 and u in a piece with 2^m u ≥ 2^K, write
ζ_j(2^m u) by its M-term expansion (P2 (i)):
ζ_j(λu) = Σ_{p<M} D_jp Σ_{σ=±1} (σi)^{−(p+1)}(2πλu)^{−(p+1)} e^{σi2πλu} + R_j,
D_jp = norm_j (−1)^p φ̃_j^{(p)}(1), |R_j| ≤ norm_j‖φ̃_j^{(M)}‖_1 (2πλu)^{−M}.
This holds in regions B (t < K ≤ t + m) and C (t ≥ K, m ≥ 1) alike.

**Prop P4b (one term).** For f(u) = ζ_i(u)u^{−(p+1)}, Ω = 2πλ, λ = 2^m ≥ 2
and an exact interval [a, b] ⊂ [1, ∞):

    ∫_a^b f e^{iσΩu} du = Σ_{r<R} (−1)^r [f^{(r)}(u) e^{iσΩu}/(iσΩ)^{r+1}]_a^b + ρ_R,
    |ρ_R| ≤ (b − a) · 2 norm_i Σ_{k≤R} C(R, k)(2π)^k (p + 1)↑_{R−k} a^{−(p+1+R−k)} / Ω^R.

*Proof.* R integrations by parts. Leibniz with
|ζ_i^{(k)}(u)| = norm_i|∫ξ_i(y)(2πiy)^k e^{2πiuy}dy| ≤ 2 norm_i (2π)^k
and |d^b u^{−(p+1)}| = (p + 1)↑_b u^{−(p+1+b)}. ∎ The ratio of successive
terms is about (2π + (p + R)/a)/Ω ≈ 1/λ: the slowest is m = 1 (ratio ½).

**Endpoint derivatives.** f^{(r)} at the dyadic endpoints follows by Leibniz
from ζ_i^{(a)}(u) = Σ_r CM[r, i] (d/du)^a j_{k_r}(2πu). The Bessel
derivatives come from j_k' = (k j_{k−1} − (k + 1) j_{k+1})/(2k + 1)
applied a times to a ball table j_0 .. j_{kmax+R} (`zeta_derivs`, checked by
a Taylor expansion and by the bound |ζ^{(a)}| ≤ 2 norm (2π)^a).

**Assembly.** P_ij(m, t) = Σ_{p,σ} D_jp (σi)^{−(p+1)}(2πλ)^{−(p+1)} J^σ_i(p)
+ the expansion remainder, which is at most
C_i norm_j‖φ̃_j^{(M)}‖_1(2πλ)^{−M} ∫_a^b u^{−5/6−M}du (Landau for ζ_i). In
matrix form this is one product per piece, the endpoint sums being shared by
every piece that meets the endpoint.

**Region C, m = 0.** Σ_{t≥K} w_t P(0, t) = 2 Z(2^K) − Σ_{t≥K} 2^{−t}(Z(2^t) −
Z(2^{t+1})), Z(W) = ∫_W^∞ ζ_iζ_j (the G_z tail of s4.2, a ball matrix).

**The remainders beyond m_max and t_max** (Landau, s0):
Σ_{m>m_max} ≤ 6 C_iC_j 2^{−5(m_max+1)/6}/(1 − 2^{−5/6});
Σ_{t>t_max, m≥1} ≤ 6 C_iC_j W^{−2/3}/(1 − 2^{−5/6}), W = 2^{t_max+1};
the m = 0 correction beyond t_max ≤ 2^{−(t_max+1)}·1.5 C_iC_j W^{−2/3}.
`gram_b` picks m_max and t_max from these for a target radius and adds
them to every entry.

**Checks (toy, 2 modes, K = 6; `test_p4.py`):**
- Region B: pieces (m, t) = (3, 4), (2, 5) and (5, 1) overlap direct
  quadrature. **Planted:** R = 2 with the remainder suppressed does not.
- Region C, m ≥ 1: (1, 6), (3, 6) and (2, 7) overlap. **Planted:** a
  2-term expansion with its remainder suppressed does not.
- Region C, m = 0: Z(64) − Z(128) overlaps quadrature on [64, 128].
  **Planted:** Z(64) alone does not.
- The whole G_b at target 1e−8: symmetric, positive definite in balls,
  m_max = 53, t_max = 66, radius below 1e−6.
- **Two routes** (slow test): G_b in v-space against the hats' Plancherel
  sum (Δ/2π)Σ|b̂|² on |s| ≤ 200 (w-quadrature, P1, P2). The gap is a tail,
  non-negative up to aliasing, a few percent, and the off-diagonal gap
  obeys Cauchy-Schwarz.

## 4.6 Status against PREREG row D0

**P4 is closed** as a derivation with an implementation: G_z (s4.2) and
G_b (s4.3 region A, s4.5 regions B and C, with all truncations bounded).
With P1 to P3 (s1 to s3), every prerequisite of PREREG s1 now has a
derivation, code and a test. **PREREG row D0's precondition is lifted.**
A run with the exact provider no longer stops at setup. Whether any
rebuilt row closes (its ε_q finite) is decided by the run, not by this
file. All of it is ordinary argument, unreviewed, on the cited inequalities
of s0. The production cost of the Gram at 280 modes is an estimate, not a
measurement (RUNS.md s9).

## 5. Correction, 2026-10-27: the Gauss bound was the (n + 1)-point bound

An adversarial review of PR #362 found that s0's (Gauss) inequality, used
for n-point rules in P1 (s1) and in P4's quadrature (s4.1), is the bound of
the (n + 1)-point rule. This section verifies that independently and records
the fix. s0 to s4.6 above stay as written, apart from two dated pointers.
The text in question, as written in s0:

> **(Gauss)** For f analytic in the Bernstein ellipse E_ρ of [−1, 1] with
> |f| ≤ M there, the n-point Gauss-Legendre error is at most
> (64/15) M ρ^{−2n}/(ρ² − 1) (Trefethen, SIAM Rev. 50 (2008) 67–87,
> Thm 4.5).

and in s1: "so the panel error is at most (b − a)/2 · (64/15) · that ·
ρ^{−24}/(ρ² − 1) for 12 nodes". `bounds.gauss_panel_error` coded exactly
that, and `e3_hat_bound` and `_quad_pair_core` called it with n = 12.

**The bound, derived here.** Let f = Σ a_k T_k on [−1, 1], analytic in the
open ellipse E_ρ with |f| ≤ M there, so |a_k| ≤ 2Mρ^{−k}. The n-point rule
G_n is exact to degree 2n − 1 and symmetric, so odd T_k contribute nothing
to I or G_n. For even k ≥ 2n, |I(T_k) − G_n(T_k)| ≤ 2/(k² − 1) + Σ_j w_j
= 2 + 2/(k² − 1), the weights being positive with sum 2. Hence

    |I − G_n| ≤ Σ_{k even ≥ 2n} 2Mρ^{−k}(2 + 2/(k² − 1))
              ≤ 4M · 4n²/(4n² − 1) · ρ^{2−2n}/(ρ² − 1)
              ≤ (64/15) M ρ^{2−2n}/(ρ² − 1)        (n ≥ 2).

The old formula is this bound at n + 1 nodes. It agrees with the cited
theorem if that theorem's rule has n + 1 points, as an index counted from 0
would give. The source was not re-read here (its PDF did not extract on the
box), so the code now rests on the derivation above, not on the citation.
The derivation is an ordinary argument and is unreviewed, like the rest of
this file.

**The counterexample** (measured, 256-bit balls; `test_bounds.py`).
T_24 is entire and is the first even Chebyshev polynomial the 12-point rule
misses; its maximum on E_ρ is (ρ^24 + ρ^{−24})/2. Its 12-point error is
1.54. The old formula gives 0.267 at ρ = 3 and 0.0095 at ρ = 15; the
corrected one gives 2.40 and 2.14. A non-polynomial integrand also breaks
it: exp(3x) at 12 points, ρ = 15, errs by 9.1e−20 against an old bound of
7.4e−21 (corrected: 1.7e−18). Over 90 cases (T_2n, exp(3x), exp(10x) and
cos(20x), n = 2, 4, 12, 13, 16, ρ from 1.2 to 40) the old formula fails
in 25 and the corrected one in none
(`test_gauss_bound_holds_on_entire_functions`,
`test_gauss_old_formula_fails_on_entire_functions`). A check of this kind
can refute a bound, never prove it.

**What it changed.** Every Gauss term the code computed was too small by
ρ² of its panel, up to 225 at ρ = 15. At the production grid (K = 14,
S' = 2,700), measured with the panel loops of `e3_hat_bound` and
`_quad_pair_core`:

| term | old formula, 12 nodes | corrected, 12 nodes | corrected, 13 nodes |
|---|---|---|---|
| E3 per hat, divided by norm_n | 4.53e−18 | 1.02e−15 | 4.53e−18 |
| G_z quadrature on [1, 2^14], times norm_i norm_j | 5.71e−16 | 1.28e−13 | 5.71e−16 |
| G_b region A, r_quad, times norm_i norm_j | 3.42e−15 | 7.68e−13 | 3.42e−15 |

So the radii of the committed `gram.json` (run 40342895119) are not bounds.
At (0, 0), where the quadrature term dominates, they are 9.97e−12 (G_z) and
5.97e−11 (G_b), against about 2.2e−9 and 1.3e−8 under the corrected bound
at 12 nodes (the review's figures). Every ball built from them, and so
ε_q of run 40371181784, is not established as a bound (RESULTS.md,
correction of 2026-10-27). s1's remark that the panel error "falls like
e^{(π/2)ρ}ρ^{−24}" should read ρ^{−22} at 12 nodes. The E3 claim "below
1e−15 per hat" (RESULTS.md, second unit) holds at 13 nodes, not at 12.

**The fix.** `gauss_panel_error` returns (h/2)(64/15) M ρ^{2−2n}/(ρ² − 1)
and refuses n < 2. Production now uses **13 nodes per panel**, in the hat
table (request key `per_panel`) and in the Gram (`gram_per_panel`). Panels,
ρ and M do not depend on the node count, so the corrected 13-node bound
equals the old 12-node formula term by term
(`test_corrected_bound_at_n_plus_one_is_the_old_formula_at_n`). The rerun's
radii are therefore the sizes run 40371181784 carried, now as bounds, at
13/12 of the hat products, the phases and the region-A quadrature. Requests
without the keys mean 12 (what the earlier runs used).

**Observed with it.** Under the corrected bound at 12 nodes, G_z of four
prolates at K = 10 has radius 1.4e−10 at (0, 0), and the one-ulp float
endpoint fault of s1.1 hides inside it. At 13 nodes the radius is 6.2e−13
again and the planted fault is caught (`test_gram_z_is_the_identity`,
`test_planted_float_endpoints_exclude_the_identity`).

**What it did not change.** P2 (the integration-by-parts and series
remainders), P3 (the trapezoid in s and its Poisson aliasing), P4's
regions B and C (integration by parts) and C with m = 0 (the G_z tail), and
the Landau tails: no Gauss rule enters them.

**Also added with the rerun** (PREREG items the first run did not meet;
RESULTS.md lists them as deviations): `ball_pd` decides positive
definiteness of each Gram by a ball LDLᵀ (every pivot > 0) and the rebuild
stops otherwise (in the merge job and in every process's setup); ρ is still
formed with the ball inverse, not by triangular solves. And every replay
block keeps its own window sum in the checkpoint (PREREG s6).
