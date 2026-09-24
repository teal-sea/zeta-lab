# DERIVATION: bound_trunc/, the prolate-mode truncation tail of ΔT

Worker `bound_trunc/`, 2026-09-24, branch `teal-sea/weil-c4-s2`, from
17:35. Every argument here is an ordinary argument by this worker,
**unreviewed** until referee/ has read it. Nothing here is a claim about RH.

## 0. Notation

Everything follows two_adic/ s0, s5 and kernel/ INTERFACE s3.

- H = L²(ℝ₊*, d*u), equivalently the even half-line picture L²([0, ∞), dv).
  P = multiplication by 1_{v<1}. F = the even Fourier transform, unitary,
  F² = 1. P̂ = FPF.
- D = unitary dilation moving support outward, (Dh)(v) = 2^{−1/2} h(v/2), so
  FD = D^{−1}F (two_adic/ s6). For ζ, α = 1 and a := α 2^{−1/2} = 2^{−1/2}.
  Θ = 1 − aD, Θ* = 1 − aD^{−1}, ΘF = FΘ*. Θ^{−1} = Σ_{k≥0} a^k D^k and
  Θ*^{−1} = Σ_{k≥0} a^k D^{−k}. Since D maps functions supported in
  [1, ∞) into [2, ∞) and D^{−1} maps [0, 1] into [0, 1/2]:
  PΘ(1 − P) = 0, and Θ*, Θ*^{−1} map ran P onto itself.
- ϑ(f), f a window function, is multiplication by f̂(s) on the Mellin side;
  it commutes with D and Θ. For a bounded Hermitian X write
  τ_f(X) := Tr(ϑ(f) X ϑ(f)*) whenever that is defined. The delivered matrix of
  a form is M with τ_f(X) = v* M v for f = Σ v_n U_n.
- ξ_j (j = 0, 1, …): the even prolates, an orthonormal basis of ran P with
  PFP ξ_j = λ_j ξ_j. ζ_j = (1 − P)Fξ_j / √(1 − λ_j²), orthonormal.
  Q_∞ = Σ_j |ζ_j⟩⟨ζ_j|, S_∞ = 1 − P − Q_∞ (CC arXiv:2006.13771 eq. 81).
- b_j = (1 − P)Θ*^{−1}ζ_j. Q_S = projection onto the closed span of all b_j.
  Π_S := 1 − P − Q_S is the projection onto Θ(ran S_∞) (two_adic/ s5 item 2).
- Truncation at n modes (two_adic/'s nvec): V_n = span{ξ_j : j < n},
  U_n = ran P ⊖ V_n, Q_∞^(n) = projection onto span{ζ_j : j < n},
  Q_S^(n) = projection onto span{b_j : j < n}.

## 1. Feasibility (milestone 1)

**Verdict: no bound on the truncation error is derivable along the route the
brief names, and I see no route that closes inside the box. This is outcome
4 for bound_trunc/.** Section 1.3 names the step that does not close.
Section 1.4 gives a weaker, mode-free statement that still serves the count:
a one-sided inequality T_S ≥ κ T_∞ with κ = (√2 − 1)⁴, which bounds n_−(R_S)
from below without ΔT.

### 1.1 (a) What ΔT_exact is

**Definition.** ΔT_exact(f) := T_S(f) − T_∞(f) = τ_f(Π_S) − τ_f(S_∞). Both
traces are finite: T_∞ by CC Thm 4.7 (eq. 83), T_S by two_adic/ s5 item 1
(ordinary argument, unreviewed), which bounds τ_f(Π_S) by a constant times
τ_f(S_∞). CCM arXiv:2310.18423 Thm 4.6 enters only to identify the object:
θ_S maps S_λ(ℝ) onto the semilocal Sonin space boundedly with bounded
inverse, so ran Π_S = Θ(ran S_∞) is that space in the w_S picture. As
operators Π_S − S_∞ = Q_∞ − Q_S, so ΔT_exact = τ_f(Q_∞ − Q_S), a difference
that is trace class after sandwiching although neither term is (Lemma 1).

**What two_adic/ computes** (before bound_quad/'s errors: s cutoff, w
quadrature, float64 mode data, the Gram step, rounding) is

    ΔT^(n)(f) := τ_f(Q_∞^(n) − Q_S^(n)),

finite rank, whose Mellin densities are ta_prolate's ρ_∞ − ρ_S. "ΔT_exact as
a limit over modes" would be ΔT_exact = lim_n ΔT^(n). Whether that holds is
item (b).

**Identity A (the truncated object, exact).** Put
S^(n) := 1 − P − Q_∞^(n) = S_∞ + R_n with R_n := Q_∞ − Q_∞^(n), the
projection onto W_n := closed span{ζ_j : j ≥ n}, and
Π^(n) := 1 − P − Q_S^(n). Then

1. ran Π^(n) = Θ(ran S^(n)). Proof: ran(1 − Π^(n)) = ran P ⊕ span{b_j}_{j<n}
   = Θ*^{−1}(ran P ⊕ span{ζ_j}_{j<n}), because Θ*^{−1} maps ran P onto itself
   and Θ*^{−1}ζ_j = PΘ*^{−1}ζ_j + b_j. Taking orthogonal complements,
   ran Π^(n) = (Θ*^{−1} ran(1 − S^(n)))^⊥ = Θ(ran S^(n)).
2. So ΔT^(n) = τ_f(Π^(n) − S^(n)): the stored construction is the same 2-adic
   functional applied to the enlarged space ran S_∞ ⊕ W_n, not to the Sonin
   space.
3. ran Π^(n) = Θ ran S_∞ + ΘW_n (Θ bounded with bounded inverse), so
   Π^(n) = Π_S + Π'_n with Π'_n the projection onto the closure of
   (1 − Π_S)ΘW_n.
4. Hence the truncation error is exactly

       E_n := ΔT_exact − ΔT^(n) = τ_f(R_n − Π'_n).                        (A)

   E_n is finite for every n: it is (Π_S − S_∞) − (Π^(n) − S^(n)), a τ-trace
   class operator minus a finite-rank one.

**Identity B (one mode).** Since the ζ_j are orthonormal,
S^(n) = S^(n+1) ⊕ ℂζ_n, and Gram-Schmidt on the b_j gives

    ΔT^(n) − ΔT^(n+1) = ‖ϑ(f) b̃_n‖² / ‖b̃_n‖² − ‖ϑ(f) ζ_n‖²,   b̃_n = (1 − Q_S^(n)) b_n.   (B)

Every measured mode response is a sum of such rank-one differences. Each
term alone is of order ‖f‖²/n for f in the window space (heuristic, s1.2),
so a response of 1e−3 over 20 modes is a cancellation of terms each much
larger than it.

### 1.2 (b) Is the limit proven to exist? No.

- **Not in the sources.** two_adic/ s5b and s7b measure responses and say
  so ("six differences establish no rate"). CCM Thm 4.6 is a statement about
  the exact Sonin spaces, not about a mode truncation. In CC the modes enter
  T_∞ through eq. 83 weighted by v_j = λ_j²/(1 − λ_j²), a positive series
  that converges super-exponentially; ΔT carries no such weight.
- **Strong convergence does not reach it, and no positivity argument can.**

  **Lemma 1.** For every n and every window function f ≠ 0,
  τ_f(R_n) = +∞ and τ_f(Π'_n) = +∞.

  *Proof.* In the log variable x = log v, ϑ(f) is convolution by f and 1 − P
  is multiplication by 1_{x ≥ 0}, so ϑ(f)(1 − P) has kernel
  f(x − y) 1_{y≥0} and τ_f(1 − P) = ∫_0^∞ ‖f‖² dy = ∞. Now
  1 − P = S_∞ + Q_∞^(n) + R_n, a sum of positive operators, with
  τ_f(S_∞) = T_∞(f) < ∞ and τ_f(Q_∞^(n)) < ∞ (finite rank); traces of
  positive operators add, so τ_f(R_n) = ∞. Likewise
  1 − P = Π_S + Π'_n + Q_S^(n) with τ_f(Π_S) = T_S(f) < ∞. ∎

  So E_n in (A) is the difference of two divergent positive traces, and
  E_n → 0 is a cancellation statement that nothing in the construction
  supplies. Heuristically each mode carries |ζ̂_j(s)|² ≈ 4j/(s² + 4j²) (a
  Poisson kernel: stationary phase on the WKB form of the spherical Bessel
  function j_{2j}(2πw), normalized by Plancherel), so a window with f̂
  concentrated at |s| ≪ j picks up about (1/2π)‖f̂‖²/j per mode, and the tails
  diverge like log n. That rate is heuristic; Lemma 1 is not.
- **Consequence for the band.** Successive differences ΔT^(n+20) − ΔT^(n)
  tending to 0 would show that ΔT^(n) converges, not that it converges to
  ΔT_exact: a limit ΔT_exact + β with β ≠ 0, a bias left at the truncation
  front, produces the same responses. The measured response is therefore not
  a bound even in principle without a separate argument identifying the
  limit.

### 1.3 (c) Is a tail bound derivable? Which step does not close

By (A), a bound needs |τ_f(R_n − Π'_n)| ≤ ε‖f‖² on the window space. The
error has three mechanisms. The first closes; the second does not; the third
says how large ε would be even if the second closed.

**Mechanism 1, Θ moving the tail (closes for a degree truncation).**

**Lemma 2.** Let L_m = even polynomials of degree < 2m on [0, 1] and
U^L_m = ran P ⊖ L_m. Then PD maps L_m into L_m, so D^{−1}, Θ* and Θ*^{−1}
map U^L_m into itself and Θ* U^L_m = U^L_m. With
W^L_m := closure of (1 − P)F U^L_m,

    Θ W^L_m = { (1 − P)F Θ* u − (1 − P)Θ PFP u : u ∈ U^L_m },

so Θ W^L_m differs from W^L_m only by the operator (1 − P)ΘPFP on U^L_m,
of norm at most (1 + a)‖PFP|U^L_m‖, which is super-exponentially small in m.

*Proof.* For v ∈ [0, 1], (Dp)(v) = 2^{−1/2}p(v/2) is a polynomial of the same
degree and parity. For u ∈ U^L_m and p ∈ L_m, ⟨p, D^{−1}u⟩ = ⟨PDp, u⟩ = 0.
Θ*^{−1} = Σ a^k D^{−k} converges in norm. For the last display:
Θ(1 − P)Fu = (1 − P)Θ(1 − P)Fu (as PΘ(1 − P) = 0)
= (1 − P)FΘ*u − (1 − P)ΘPFu, and PFu = PFPu for u ∈ ran P. ∎

So with a degree truncation the tail is carried into itself by Θ up to
λ-sized terms. The stored builds truncate by prolate index (V_n), not by
degree (L_n). The leak is the rank-≤n operator u ↦ P_{V_n} Θ* u on U_n,
bounded by 2a times the largest principal sine between V_n and L_n; that
sine is computable with enclosures from kernel/'s Legendre coefficients
(`prolate_vectors(...)["coef"]`) and a residual bound on each prolate
vector. This part is derivable; it is not done yet.

**Mechanism 2, the Sonin overlap (does not close).** Π'_n is the projection
onto (1 − Π_S)ΘW_n, not onto ΘW_n, because ΘW_n is not orthogonal to
ran Π_S = Θ ran S_∞. For σ ∈ ran S_∞ and w ∈ W_n, ⟨σ, w⟩ = 0, so

    ⟨Θσ, Θw⟩ = ⟨σ, Θ*Θ w⟩ = −a ⟨σ, (D + D^{−1}) w⟩.

With w = (1 − P)Fu, u ∈ U_n (up to the factor √(1 − λ²)):
- the D term is λ-small: D(1 − P)Fu = FD^{−1}u − DPFPu, FD^{−1}u ∈ ran P̂ is
  orthogonal to σ, and ‖PFPu‖ ≤ λ_n‖u‖;
- the D^{−1} term is not: D^{−1}(1 − P)Fu = FDu − D^{−1}PFu, the second piece
  lies in ran P, FPDu ∈ ran P̂, so ⟨σ, D^{−1}w⟩ = ⟨σ, F(1 − P)Du⟩ exactly.
  (1 − P)Du is u(v/2)/√2 on [1, 2], of norm ‖u 1_{[1/2,1]}‖, which is not
  small for a high-degree u.

So the overlap is governed by the operator Y_n := S_∞ F (1 − P) D on U_n,
whose operator norm does not decay in n. Its effect on τ_f is small only if
F(1 − P)DU_n sits at Mellin frequencies where the window weight |f̂(s)|² is
small. The phase-space picture (mode j on the curve (2πw)² − s² ≈ (2j)², the
Sonin space at s² > (2πw)², D^{−1} halving w at fixed s) puts it at
|s| ≳ 2n/√3, but that is a heuristic. A bound needs a quantitative estimate
of how ran S_∞ meets F(1 − P)DU_n, frequency by frequency, and S_∞ itself is
defined through the whole mode family. **This is the step that does not
close.** I found no available estimate of that kind, and deriving one is a
research problem, not a three-hour task.

**Mechanism 3, the size any such bound would have.** Even with mechanism 2
closed by a density bound of order one on |s| > σ_n, the window basis
limits ε. As a function on ℝ, f = Σ v_n U_n jumps at 0 and L by
f(0) = L^{−1/2}Σ v_n, so |f̂(s)|² ≈ 4|f(0)|² sin²(sL/2)/s² at large s, and
sup over unit v of (1/2π)∫_{|s|>σ}|f̂|² ds is about 2(2N + 1)/(πLσ). At
c = 2.9 and σ_n = 2n/√3 that is about 0.1 on every stored build (0.11 at
N = 8, n = 80; 0.09 at N = 32, n = 364), ten times the band. So a completed
argument of this shape gives outcome 3 at best. (These sizes are estimates
at this stage; section 2 computes the exact window quantity and a test pins
it.)

**On the inputs the brief names.**
- Prolate eigenvalue decay: enters only through λ-sized terms (Lemma 2 and
  the D term above), which are harmless; kernel/ resolves λ_j only for
  j < n_max (20 at dps 40), and a bound would need an analytic tail estimate
  beyond it, which exists in the literature for prolates and is not the
  obstacle.
- The dilation series of |Θ|^{−1}: norm-wise harmless (‖Θ^{−1}‖ ≤ 1/(1 − a)
  = 3.41), but its D^{−1} steps are exactly what carries tail content into
  the Sonin region (mechanism 2).
- The ρ step's dependence on the mode count: in exact arithmetic ρ is the
  density of a projection for every n, so the truncation error has no ρ
  term; the conditioning of the Gram factor (two_adic/ s10) is bound_quad/'s.

### 1.4 A weaker statement that still serves the count (mode-free)

**Lemma 3.** With κ := ((1 − a)/(1 + a))² = (√2 − 1)⁴ = 0.029437…,

    κ T_∞ ≤ T_S ≤ κ^{−1} T_∞   as forms on window functions.

*Proof.* Let (σ_i) be an orthonormal basis of ran S_∞. (Θσ_i) is a Riesz
basis of ran Π_S with Gram matrix G = S_∞Θ*ΘS_∞, and
(1 − a)² ≤ G ≤ (1 + a)² because 1 − a ≤ ‖Θx‖/‖x‖ ≤ 1 + a (D unitary). Then
T_S(f) = Tr(G^{−1}M) with M_ij = ⟨ϑΘσ_i, ϑΘσ_j⟩ ≥ 0, and
Tr(M) = ‖ϑ(f)ΘS_∞‖²_HS = ‖Θϑ(f)S_∞‖²_HS lies in
[(1 − a)², (1 + a)²]·T_∞(f). For positive G^{−1} and M,
Tr(M)/‖G‖ ≤ Tr(G^{−1}M) ≤ ‖G^{−1}‖Tr(M). ∎

Consequently R_S = Q − T_S ≤ Q − κT_∞ as forms, the Galerkin compression
keeps the inequality, and by min-max

    n_−(R_S on the window space) ≥ n_−(Q − κT_∞).

This uses no prolate truncation and no ΔT at all: only Q (checker/) and T_∞
(kernel/), both at dps 40. A float64 probe of Q − κT_∞ from dps-30 matrices
(this session, not yet pinned) gives **2 negative eigenvalues at c = 2.9**
(−9.9e−5, −1.6e−5 at N = 8; −1.0e−4, −1.7e−5 at N = 16), 1 at c = 2.5, 0 at
c = 2.2, the same at N = 8 and 16. So on its own it gives n_−(R_S) ≥ 2 at
c = 2.9 (a remainder of rank below 2 is ruled out there), with no growth in
N. It does not resolve the 4, 10, 20 count; it is a floor that no mode count
can move. Milestone 3 pins it by exact inertia and extends it to N = 32.
