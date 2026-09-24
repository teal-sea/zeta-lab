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

**Verdict: no bound on the truncation error was derived in the box. This is
outcome 4 for bound_trunc/, and its ALIGNMENT s5 status is unresolved
(paused by the box), not obstructed.** Two claims, kept apart (s2.5):
(i) the limit of ΔT^(n) as n → ∞ is proven nowhere in the record (a gap,
with where I looked); (ii) the Sonin-overlap operator S_∞F(1 − P)D on the
prolate tail has a norm that does not decay in n, which blocks the route the
brief names. (ii) kills that route; it is not a proof that no bound exists,
which would need the effect bounded from below. Section 1.3 names the step.
Section 1.4 gives a weaker, mode-free statement that still serves the count:
T_S ≥ κ T_∞ with κ = (√2 − 1)⁴ (Lemma 3), so n_−(R_S) ≥ n_−(Q − κT_∞)
without ΔT. The count itself is assembler/'s.

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
defined through the whole mode family. **This is the step that did not
close.** I found no available estimate of that kind in the box. That kills
this route and says nothing about whether a bound exists by another one:
showing that would need the overlap's effect on τ_f bounded from below,
which I have not done.

**Mechanism 3, the size any such bound would have** (Proposition 4, s2.7,
states this with its dependence). Even with mechanism 2
closed by a density bound of order one on |s| > σ_n, the window basis
limits ε. As a function on ℝ, f = Σ v_n U_n jumps at 0 and L by
f(0) = L^{−1/2}Σ v_n, so |f̂(s)|² ≈ 4|f(0)|² sin²(sL/2)/s² at large s, and
sup over unit v of (1/2π)∫_{|s|>σ}|f̂|² ds is about 2(2N + 1)/(πLσ) once σ
is above the window band 2πN/L. At c = 2.9 and σ_n = 2n/√3 that estimate is
about 0.1 (0.11 at N = 8, n = 80; 0.09 at N = 32, n = 364), ten times the
band. So a completed argument of this shape gives outcome 3 at best.
*Corrected at 18:15 the same day by the exact computation of s2.7:* the
window quantity itself is 0.098 to 0.21 at c = 2.9, N = 32, 0.12 at N = 8,
and up to 0.88 at c = 2.9 and 1.0 at c = 2.2 on the builds whose σ_n falls
inside the window band (80 modes at N = 16; 200 modes at c = 2.2, N = 32).
The sentence "about 0.1 on every stored build" first written here was wrong
for those builds.

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
c = 2.2, the same at N = 8 and 16. **These are a labelled float probe
(float64 eigenvalues of dps-30 matrices, this session, not pinned); the
count belongs to assembler/** (its PREREG addendum e174d19, exact rational
route, nine cells). If the probe holds there, the floor gives n_−(R_S) ≥ 2
at c = 2.9, with no growth in N: it does not resolve the 4, 10, 20 count,
and no mode count can move it. (An exact-inertia script written here before
that allocation, 91ce087, was removed on the coordinator's instruction; git
history keeps it.)

## 2. The derivation (milestone 2, for referee/)

Section 1 argued in prose; this section states what is claimed, under which
numbered assumptions, with each proof in one place. Every statement is an
ordinary argument by this worker, **unreviewed**. Constants are closed forms
or exact rationals; there is no numerical constant in any proof.

### 2.1 Assumptions

- **A1 (the objects).** H, P, F, D, Θ, ϑ(f) as in s0; D is unitary and
  commutes with ϑ(f); a = 2^{−1/2}. S_∞ is the orthogonal projection of CC
  arXiv:2006.13771 eq. 81 (1 − S_∞ = P + Q_∞, the ζ_j orthonormal). Π_S is
  the orthogonal projection onto Θ(ran S_∞) (two_adic/ s5, the module form;
  CCM arXiv:2310.18423 Thm 4.6, used as published, identifies ran Π_S with
  the semilocal Sonin space).
- **A2 (finiteness).** T_∞(f) = τ_f(S_∞) < ∞ for window functions f (CC
  Thm 4.7). T_S(f) := τ_f(Π_S); its finiteness follows from Lemma 3 below.
- **A3 (what is stored).** Before bound_quad/'s error sources, the ΔT that
  two_adic/ stores at nvec = n is ΔT^(n) = τ_f(Q_∞^(n) − Q_S^(n)): ta_prolate's
  ρ_∞ and ρ_S are the Mellin densities of those two finite-rank projections
  (ta_mellin docstring; two_adic/ s5b). The stored T_S is kernel/'s T_∞ plus
  that ΔT.
- **A4 (the other matrices).** Q is checker/'s (`checker_q.Q_matrix`, dps 40)
  and T_∞ is kernel/'s (`sonin.T_inf_matrix`, dps 40). Their distance to the
  exact forms is assembler/'s to state (BRIEF.md); nothing here re-derives it.

Standard facts used without comment: traces of positive operators add
(values in [0, ∞]); Tr(AB) ≤ ‖A‖ Tr(B) and Tr(AB) ≥ Tr(B)/‖A^{−1}‖ for
A, B ≥ 0, A invertible; Courant-Fischer min-max; Weyl's inequality.

### 2.2 Identity A (uses A1, A3)

Statement and proof: s1.1, items 1 to 4. The step that carries the weight is
item 1, ran(1 − Π^(n)) = Θ*^{−1}(ran P ⊕ span{ζ_j}_{j<n}); it needs only
that Θ*^{−1} maps ran P onto itself (Θ*^{−1} = Σ a^k D^{−k} and D^{−1}
compresses supports toward 0) and the orthogonal decomposition
Θ*^{−1}ζ_j = PΘ*^{−1}ζ_j + (1 − P)Θ*^{−1}ζ_j. Identity B is Gram-Schmidt.

### 2.3 Lemma 1 (uses A1, A2)

Statement and proof: s1.2. The only analytic input is
τ_f(1 − P) = ∞, which is the Hilbert-Schmidt norm of a convolution operator
restricted to a half-line.

### 2.4 Lemma 2 and the prolate leak (uses A1)

Lemma 2: s1.3. Add:

**Lemma 2'.** Let θ_n be the largest principal angle between V_n (the first
n even prolates) and L_n (even polynomials of degree < 2n); both have
dimension n. Then for u ∈ U_n = ran P ⊖ V_n,
‖P_{V_n} Θ* u‖ ≤ 2a sin θ_n ‖u‖.

*Proof.* P_{V_n}Θ*u = −a P_{V_n}D^{−1}u since u ⊥ V_n. Its adjoint is
−a P_{U_n} P D P_{V_n}. For v ∈ V_n write v = v_L + v_⊥ with v_L ∈ L_n and
v_⊥ ⊥ L_n. PDv_L ∈ L_n (Lemma 2), so ‖P_{U_n}PDv_L‖ ≤ ‖P_{U_n}P_{L_n}‖‖v‖
= sin θ_n ‖v‖; and ‖PDv_⊥‖ ≤ ‖v_⊥‖ ≤ sin θ_n ‖v‖ because ‖PD‖ ≤ 1. ∎

sin θ_n is the norm of the block of kernel/'s Legendre coefficient matrix
that maps the first n prolates onto P_{2k}, k ≥ n; enclosing it needs an
enclosure of each prolate vector (a residual bound and a spectral gap). It
was not computed: Lemma 2' controls only mechanism 1, and without mechanism
2 it bounds nothing.

### 2.5 The open step (why there is no bound), in two separate claims

**Claim (i), a gap in the record.** That ΔT^(n) → ΔT_exact as n → ∞ is
proven nowhere I looked: two_adic/ RESULTS s5 (items 1 to 6), s5b, s6, s7,
s7b and s10; the docstrings of `ta_prolate.py` and `ta_mellin.py`; kernel/
INTERFACE s3 (which proves convergence of the z-sum on vectors supported in
u ≤ X, a different statement); checker/ RESULTS s7.2, s7.3a, s7.8. For the
two papers I used the record's statements of them (two_adic/ s0 for CCM
arXiv:2310.18423 Thm 4.6, kernel/ INTERFACE s3 for CC arXiv:2006.13771
Thm 4.7), not the papers themselves. Grade: a statement about the record.

**Claim (ii), the route is blocked.** The overlap operator below has a norm
that does not decay in n, and I have no estimate of its τ_f-effect. That
blocks the route; it does not show the error fails to vanish. Status:
unresolved (paused by the box).

A bound ε_trunc would be a proof of:

> **Open statement O.** For each stored build there is an explicit
> ε(c, N, n) with |τ_f(R_n − Π'_n)| ≤ ε(c, N, n)‖f‖² on the window space.

By Lemma 1 no proof of O can bound the two terms separately. A proof must
pair them, and the pairing splits (s1.3) into mechanism 1, controlled by
Lemma 2 and 2' up to λ-sized terms, and mechanism 2, the overlap of ΘW_n
with Θ ran S_∞, which by the computation in s1.3 is
−a⟨Fσ, (1 − P)Du⟩ up to λ-sized terms (σ ∈ ran S_∞, u ∈ U_n), an operator
S_∞F(1 − P)D on U_n whose norm does not decay in n. O would follow from a
bound on the τ_f-weighted size of that operator. Its natural route is a
Mellin-frequency localization of F(1 − P)DU_n at |s| ≳ 2n/√3 combined with
the window weight above that frequency; the second half is s2.7, the first
half is the missing piece.

### 2.6 Lemma 3 and the floor (uses A1, A2, A4)

**Lemma 3.** κ T_∞ ≤ T_S ≤ K T_∞ as forms on window functions, with
κ = ((1 − a)/(1 + a))² = (√2 − 1)⁴ = 17 − 12√2 and
K = κ^{−1} = ((1 + a)/(1 − a))² = (√2 + 1)⁴ = 17 + 12√2.

Enclosures (`eps_trunc.kappa_ball`, `K_ball`, arb at 53 bits):
κ ∈ [0.02943725152286 ± 3.6e−15], K ∈ [33.9705627484771 ± 4.6e−14], and
the rationals κ_lo = 2224215839029675522499/75557863725914323419136 <
κ < κ_hi = 8896863356118702089999/302231454903657293676544 (width 12·2^{−80},
`kappa_bounds`, from an integer square root).

**The coordinator's question, answered in one line:** yes, the same argument
gives the matching upper constant K = (√2 + 1)⁴ = 1/κ, under A1 and A2 only
(the upper half of the proof below), hence R_S ≥ Q − K T_∞ and
n_−(R_S) ≤ n_−(Q − K T_∞) on the window space (Corollary 3.2).

*Proof.* s1.4. Two points a referee should check: (i) (Θσ_i) is a Riesz
basis of ran Π_S and Π_S = Σ_ij |Θσ_i⟩(G^{−1})_ij⟨Θσ_j| with
G = S_∞Θ*ΘS_∞ restricted to ran S_∞, (1 − a)² ≤ G ≤ (1 + a)²; (ii)
ϑ(f)Θ = Θϑ(f), so ‖ϑ(f)ΘS_∞‖_HS lies between (1 − a) and (1 + a) times
‖ϑ(f)S_∞‖_HS. (1 − a)²/(1 + a)² = (√2 − 1)²/(√2 + 1)² = (√2 − 1)⁴ since
(√2 + 1)(√2 − 1) = 1. ∎

(Lemma 3 also reproves A2's finiteness of T_S, the content of two_adic/ s5
item 1, with the explicit constant 17 + 12√2 = 33.97.)

**Corollary 3.1 (the floor).** Let κ_lo ≤ κ be rational, let Q̃ and T̃_∞ be
the stored matrices, A := Q̃ − κ_lo T̃_∞, and let t ≥ 0 satisfy
‖Q̃ − Q‖₂ + κ_lo‖T̃_∞ − T_∞‖₂ ≤ t on the window space (A4). If A has k
eigenvalues strictly below −t, then the Galerkin compression of the exact
R_S = Q − T_S has at least k negative eigenvalues.

*Proof.* T_∞ ≥ 0 (a trace of positive operators), so by Lemma 3
R_S ≤ Q − κT_∞ ≤ Q − κ_lo T_∞ = A + (Q − Q̃) − κ_lo(T_∞ − T̃_∞) ≤ A + t as
forms on the window space. By min-max, λ_j(R_S) ≤ λ_j(A) + t < 0 for
j ≤ k. ∎

If assembler/ rounds A to float64 before an exact inertia, that rounding
enters t as well.

**Corollary 3.2 (the other side).** R_S ≥ Q − K T_∞ with K = 17 + 12√2, so
n_−(R_S) ≤ n_−(Q − K T_∞), by the same min-max step with the inequality
reversed (and the errors of A4 entering with K in place of κ_lo). Whether it
is sharp enough to matter is assembler/'s to measure.

**Lemma 3' (a sharper lower form, stated, not built).** The proof of Lemma 3
wastes a factor: Tr(M) = τ_f(ΘS_∞Θ*) is itself a trace functional of S_∞,
and Tr(G^{−1}M) ≥ Tr(M)/‖G‖ with ‖G‖ ≤ (1 + a)². Since
Θ*Θ = (1 + a²) − a(D + D^{−1}) commutes with ϑ(f),
τ_f(ΘS_∞Θ*) = Φ_∞(k), k = (1 + a²)g − a(g(· − h) + g(· + h)), h = log 2,
with g the autocorrelation and Φ_∞(k) = Tr(ϑ(k)S_∞) = W_∞(k) + ∫kε (CC
Thm 4.7, kernel/ INTERFACE s3). So

    T_S(f) ≥ [(1 + a²) T_∞(f) − a Φ_∞(g(· − h) + g(· + h))] / (1 + a)²,

which dominates κT_∞: it keeps Tr(M) = τ_f(ΘS_∞Θ*) exactly where Lemma 3
used Tr(M) ≥ (1 − a)²T_∞.
Its matrix needs the archimedean form W_∞ at the shifted autocorrelation,
which kernel/ does not build ("the shifted W_∞ matrix is not built here");
the singular point of W_∞ moves to |x| = log 2, inside the window, and has to
be regularised there. Not built in this box; a heuristic reading (the prime
atom −Wp acts like the symbol −√2 log2 cos(s log 2), and T_∞ − this bound like
σ(s)·2a(1 + cos(s log 2))/(1 + a)²) suggests it too gives a count that does
not grow with N, which is why it was not pursued.

### 2.7 Proposition 4: the window-tail constant of mechanism 3

With U_n centred on [−L/2, L/2] (a translation, which leaves |f̂| alone),
Û_k(s) = 2L^{−1/2} sin(sL/2)/(s − κ_k), κ_k = 2πk/L, real. For
f = Σ v_k U_k, (1/2π)∫_{|s|>σ}|f̂|² ds = v* M_σ v with

    M_σ[k, l] = (2/(πL)) [ J(κ_k, κ_l; σ) + J(−κ_k, −κ_l; σ) ],
    J(α, β; σ) = ∫_σ^∞ sin²(sL/2) / ((s − α)(s − β)) ds.

Since sin²(sL/2) = sin²((s − κ)L/2) for every κ = κ_k (κL ∈ 2πℤ):
for α ≠ β, J = (G(σ − β) − G(σ − α))/(α − β) with
G(u) = (log|u| − Ci(L|u|))/2, the antiderivative of (1 − cos Lu)/(2u) on
both sides of 0; for α = β, J = Lπ/4 + (1 − cos Lu₀)/(2u₀) − (L/2)Si(Lu₀),
u₀ = σ − α. The window quantity of s1.3 is λ_max(M_σ).
`eps_trunc.window_tail` evaluates it with mpmath at dps 30 and numpy's
eigenvalue; a test checks it against direct quadrature of I − M_{[−σ, σ]}
(agreement within 1e−11 on the three cases it runs). It is a size of a
hypothetical bound, not a bound on anything.

**Proposition 4.** Let κ_N = 2πN/L, W(σ) := λ_max(M_σ), v_1 := (1, …, 1)/√(2N+1)
and f_1 = Σ (v_1)_k U_k, the unit window with the largest jump at the window
edges, |f_1(0)| = √((2N+1)/L) (for every unit v, |f(0)| = L^{−1/2}|Σ v_k|
≤ √((2N+1)/L)). For σ > κ_N:

(a) W(σ) ≤ 4(2N + 1)/(πL(σ − κ_N)).
(b) W(σ) ≥ v_1* M_σ v_1, and v_1* M_σ v_1 = 2(2N + 1)/(πLσ)·(1 + O(κ_N/σ) + O(1/(Lσ))).
(c) On the continuous windows Σ v_k = 0 (codimension 1, f continuous on ℝ),
    W₀(σ) := sup (1/2π)∫_{|s|>σ}|f̂|² ≤ 4K₂/(3πL(σ − κ_N)³),
    K₂ = Σ_k κ_k² = (2π/L)² N(N + 1)(2N + 1)/3.

*Proof.* (a) For |s| > κ_N, |Σ v_k/(s − κ_k)| ≤ Σ|v_k|/(|s| − κ_N)
≤ √(2N+1)/(|s| − κ_N), and sin² ≤ 1, so |f̂|² ≤ (4/L)(2N+1)/(|s| − κ_N)²;
integrate over |s| > σ and divide by 2π. (b) The first inequality is the
Rayleigh quotient. For the asymptotic form, f̂_1(s) = 2L^{−1/2} sin(sL/2)
(Σ(v_1)_k)/s · (1 + O(κ_N/s)) and ∫_σ^∞ sin²(sL/2)/s² ds = 1/(2σ) + O(1/(Lσ²)).
(c) With Σ v_k = 0, Σ v_k/(s − κ_k) = Σ v_kκ_k/(s(s − κ_k)), bounded by
√K₂/(|s|(|s| − κ_N)) ≤ √K₂/(|s| − κ_N)² by Cauchy-Schwarz; integrate. ∎

So the mass above σ comes from the jump of f at the window edges, and the
worst window is the one with the largest jump. Measured on the stored builds
at the heuristic σ_n = 2n/√3 (`size_if_closed` in eps_trunc.json): where
σ_n > κ_N the top eigenvector of M_σ has overlap 0.94 to 0.999 with v_1,
W(σ_n) = 0.098 to 0.30, and W₀(σ_n) on the continuous windows is 0.0025 to
0.080 (at c = 2.9, N = 32: W = 0.21, 0.16, 0.13, 0.11, 0.098 and
W₀ = 0.028, 0.012, 0.0063, 0.0040, 0.0025 for 200 to 364 modes). Where
σ_n ≤ κ_N (80 modes at N = 16 for every c; 200 modes at c = 2.2, N = 32) the
proposition does not apply, the heuristic overlap region contains window
basis vectors outright and W(σ_n) is 0.88 to 1.0. For the allocation: a
bound of mechanism 2's shape is limited by the edge jump; restricted to
Σ v_k = 0 (which costs at most one eigenvalue in any count, by interlacing)
the same shape is 8 to 39 times smaller at c = 2.9, N = 32.

### 2.8 Grades

| statement | grade |
|---|---|
| Identity A, Identity B, Lemmas 1, 2, 2', 3, Corollaries 3.1, 3.2 | ordinary argument, unreviewed |
| no bound on the truncation error (outcome 4): statement O open | the obstruction is a missing lemma, not a counterexample; ALIGNMENT s5: unresolved |
| the float probe of Q − κT_∞ (s1.4) | a labelled probe, not pinned; the count is assembler/'s |
| Proposition 4 (a), (b), (c) | ordinary argument, unreviewed |
| W(σ_n), W₀(σ_n), overlaps (s2.7) | measured (closed form in mpmath, float eigenvalues, checked by quadrature) |
| Lemma 1's measured companion (s2.9) | measured (kernel/'s closed-form transforms, one window, one c) |

### 2.9 Lemma 1's measured companion (`lemma1_companion.py`, `lemma1_companion.json`)

One window, f = U_0 at c = 2.9 (unit norm), with the s-integral restricted
to |s| ≤ 60, which holds w_f = 0.9899 of the window's mass. Per-mode
contributions c_j = (1/2π)∫_{|s|≤60}|f̂|²|ζ̂_j|² ds use kernel/'s closed-form
Mellin transforms (`sonin.zeta_mellin_all`, Tate's local functional
equation at dps 20), a route independent of two_adic/'s w-quadrature.

- The partial sums P(n) = Σ_{j<n} c_j, a lower bound for τ_f(Q_∞^(n)), are
  3.162 at 80 modes and 4.251 at 240, and grow by 0.9900, 0.9910 and 0.9909
  per unit of log n on [40, 80], [80, 160] and [120, 240]. The heuristic of
  s1.2 predicts w_f = 0.9899 per unit of log n: each mode well above the
  window's frequencies adds about w_f/j.
- The Poisson form 4j/(s² + 4j²) reproduces c_j to a relative 0.47/j at
  j = 20 and 0.27/j at j = 239.
- Along the measured slope, τ_f(Q_∞^(n)) grows by about
  w_f log(364/200) = 0.593 between 200 and 364 modes (P was measured to 240
  modes; the 364-mode value is this extrapolation). Over the same five
  stored c = 2.9, N = 32 builds, the stored ΔT's U_0 entry (T_S − T_∞ at
  n = 0) stays between 5.06e−3 and 6.73e−3, a spread of 1.67e−3, 0.28 percent
  of that growth.

That is Lemma 1 in numbers: the stored ΔT is a small difference of two pieces,
each of which diverges like log n. Grade: measured (one window, one c, float
of mpmath values). It gives referee/ a falsifiable statement: a slope that
flattened as n grows, or a Poisson form that stopped matching, would
contradict the heuristic rate (not Lemma 1 itself, which is a proof).
