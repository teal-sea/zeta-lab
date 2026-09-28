1. **Verdict: gap, stated exactly, plus a bound, plus one refutation. The product-ball cutoff is not Γ_S-invariant, so it defines no operator on L²(X_S), the space where Connes' eq. (22) lives.** It yields a finite trace term in three readings only: taken on L²(A_S) it is the archimedean term T_∞ and the place 2 drops out; pushed to X_S with the open ball at 2 it is exactly the module term T^mod (Connes-Consani-Moscovici arXiv:2310.18423 Thm 4.6, used as published: the Sonin subspace transfers, and its orthogonal projection gives T^mod; transporting the product-side projection itself gives an oblique projection and T_∞ again, §3); pushed with the self-dual vector 1_{Z_2} it is a third term T^η. Theory §7.3's formula Π_S = S_∞ ⊗ P_2 + 1 ⊗ (1 − P_2) gives +∞ in every reading. Grade: ordinary argument, unreviewed, on cited theorems; local facts at 2 exact.
2. **Refuted: C4 with the product-side trace term T_∞, on every window c ∈ (2, 3).** R_S = Q − T_∞ equals a Hilbert-Schmidt form minus √2 log 2 · H, where H, the n = 2 atom's shift form, has spectrum {−1/2, 0, 1/2} with infinite multiplicities. So R_S has infinite negative index and no bounded-rank remainder exists. Grade: ordinary argument, unreviewed, using Connes-Consani arXiv:2006.13771 Thm 4.7 as published. On the shared basis the count of eigenvalues of H above 1/4 grows as 2, 3, 7 (c = 2.2), 4, 8, 15 (c = 2.5), 5, 11, 23 (c = 2.9) at N = 8, 16, 32 (measured, dps 40; two independent routes to H agree to 5e−40 at N = 8 and 16).
3. **Bound: κ^{−1} T_∞ ≤ T^mod ≤ κ T_∞ and the same for T^η, with κ = 17 + 12√2 ≈ 33.97.** κ is the ratio of the extremes of the 2-adic multiplier m(s) = |1 − 2^{−1/2−is}|² ∈ [3/2 − √2, 3/2 + √2] = [0.0858, 2.914]. Grade: the lemma is an ordinary argument, unreviewed; κ and the range of m are exact; the multiplier identities CCM (47) and (57) are hardened at S = {∞, 2} by two routes (relative agreement between 7e−32 and 1.5e−11 over s ∈ {0, 1.3, 5.7, 14.1347}, quadrature-limited at large s, dps 30).
4. **Exact gap.** On X_S the module Sonin space equals the image of the product (open-ball) Sonin space, but the two trace terms use different projections onto it: T^mod the orthogonal one, the product side the oblique one θ_S S_∞ θ_S^{−1}. These coincide only if the archimedean Sonin space is invariant under the multiplier m, which would force S_1 = S_2 (ordinary argument; strictness of the Sonin chain not checked here). Compressed to window functions the same multiplier is exactly the prime atom: Gram(θ_S) = 3/2 − W_2/log 2 on c ∈ (2, 4) (exact; three routes agree to 6e−31 at dps 30). Theory §7.3 item 2's local claim is false: at 2, time and frequency limiting to Z_2 are different projections that commute with rank-one product (exact).
5. **Open (attempt unresolved):** whether T^mod, the only reading consistent with (22), leaves a bounded-rank R_S. That needs the semilocal analogue of the Connes-Consani function ε(ρ), which does not exist yet. If that analogue holds, T^mod − T_∞ = −W_2 + (ε_S − ε_∞), so the two terms differ on these windows by exactly the 2-adic atom (derivation, conditional). The matrix comparison on the mission cells was not computed because it needs kernel/'s S_∞ (cost in §6). ALIGNMENT s5: product-side construction **refuted**; module construction **unresolved**.

# RESULTS: cutoff/, gap (c), product-ball cutoff against the module cutoff

Worker `cutoff/`, 2026-09-23, branch `teal-sea/weil-c4-s2`. Nothing here
is a claim about RH. The conclusion on c ∈ [2, 3) is known (Zhu
arXiv:2608.24827); this folder only asks which cutoff the C4 trace term can
use. Grades follow the `AGENTS.md` ladder. No kernel-checked statement is
made (AXLE not attempted, §7). Every number below is pinned in
`test_cutoff.py`; raw values in `cutoff_cells.json`.

## 0. Conventions and sources

S = {∞, 2}, A_S = ℝ × Q_2, Γ = Γ_S = {±2^n}, X_S = A_S/Γ,
C_S = (ℝ^* × Q_2^*)/Γ, module |x|_S = |x_∞| · |x_2|_2, K_S = its kernel
(≅ Z_2^*). The C4 trace terms only see the K_S-invariant sector
H := L²(X_S)^{K_S}. As in CCM arXiv:2310.18423 s4:

- w_S : H → L²(ℝ_+^*, d^*u) is unitary, w_S(ξ)(u) = u^{1/2} ξ(1 × u)
  (fundamental domain x_2 ∈ Z_2^*, x_∞ = u > 0, where |x|_S = u);
- w_∞(f)(u) = u^{1/2} f(u) on L²(ℝ)^{ev};
- F_μ(w)(s) = ∫ w(u) u^{−is} d^*u, and U_S = F_μ ∘ w_S, U_∞ = F_μ ∘ w_∞;
- the scaling action ϑ(g) of the archimedean ℝ_+^* becomes multiplication
  by ĝ(s) := F_μ(g)(s) under both U_∞ and U_S.

Windows are centred as in Connes-Consani: g ∈ C_c^∞ with support in
[c^{−1/2}, c^{1/2}], so g ∗ g^* lives on [c^{−1}, c] and the only prime
power inside is 2. The C4 class also imposes ĝ(±i/2) = ĝ(0) = 0, which
removes the pole terms; on it Q = Q_∞ − W_2 with
W_2 = √2 log 2 · (the shift form H of §5).

Sources read 2026-09-23 (PDFs in the session scratchpad, not committed):
Connes arXiv:math/9811068 s VII (eq. (5), (12), (13), Thm 4, and its proof
eq. (27)-(29)); Connes arXiv:2602.04022 s7.1-7.4, eq. (19), (22), footnote
11; Connes-Consani arXiv:2006.13771 Thm 1, Thm 4.7 (eq. (83)-(84));
Connes-Consani-Moscovici arXiv:2310.18423 s4 (Prop 4.1-4.7, Def 4.4-4.5,
Thm 4.6). The last one was found during this task and is the key input:
it constructs the module Sonin space and relates it to product data.

## 1. The two cutoffs, exactly (task 1)

### 1.1 Module cutoff (Connes)

Connes 1999 s VII (12): P_λ^S is multiplication by 1{|x|_S ≤ λ} on
L²(X_S); P̂_λ^S = F_S P_λ^S F_S^* with F_S = F_∞ ⊗ F_2 (self-dual, 1_{Z_2}
fixed), unitary on L²(X_S) by his Lemma 1(b). It is Γ-invariant because
|γ|_S = 1 for γ ∈ Γ. Via w_S it is the plain interval cutoff 1_{(0, λ]}(u)
on L²(ℝ_+^*); all the arithmetic sits in F_S. The module Sonin space is
S_λ(X_S) = {ξ ∈ H : ξ = 0 and F_S ξ = 0 on |x|_S < λ} (CCM Def 4.5), with
orthogonal projection Σ^mod. This is the cutoff of (22): Connes 2026
footnote 11 says the projections there are "defined using the module".

**Trace term:** T^mod(g) = Tr(ϑ(g) Σ^mod ϑ(g)^*) on H, λ = 1.

Where the module is used in the proof of the trace formula: Connes 1999
eq. (28)-(29). After Parseval the cutoff region {|x| ≤ Λ, |ξ| ≤ Λ} is
rewritten with u = xξ as |u|/Λ ≤ |x| ≤ Λ, which depends on x only through
|x|. That step is what a product ball does not allow.

### 1.2 Product-ball cutoff (theory §7.3 item 2)

On L²(A_S) = L²(ℝ) ⊗ L²(Q_2): P = P_λ^∞ ⊗ M_B and P̂ = F P F^* =
P̂_λ^∞ ⊗ M̂_B, with M_B multiplication by 1_B for a ball B at 2 and
M̂_B = F_2 M_B F_2^*. At ∞ open and closed balls differ by a null set; at 2
they do not, so both are recorded. Exact facts at 2 (radial functions, in
the finite model of `BallModel`, which is the space of radial functions on
the finite group 2^{−K}Z_2 / 2^K Z_2 and so exact; K = 3 and 5 pinned):

| ball | M_B = M̂_B? | commute? | M_B M̂_B | radial local Sonin space |
|---|---|---|---|---|
| closed, Z_2 | **no** | yes | rank one, onto 1_{Z_2} | {0} |
| open, 2Z_2 = {\|x\|_2 < 1} | no | **no** | | ℂ σ_2, σ_2 = ε_0 − ε_1/2, F_2 σ_2 = σ_2, ‖σ_2‖² = 3/4 |

(ε_n is the indicator of |x|_2 = 2^n. The open-ball row is CCM Prop 4.5,
rechecked here exactly.) So theory §7.3 item 2 ("1_{Z_p} is its own
Fourier transform, so time and frequency limiting to Z_p are the same
projection") is false as an operator statement. What is true: 1_{Z_2} is
the common fixed vector, and the two projections commute with product
|1_{Z_2}⟩⟨1_{Z_2}|. **Grade: exact.**

**Not Γ-invariant (exact).** x = (3/4, 1) is in the product ball B_1 =
{|x_∞| ≤ 1, |x_2|_2 ≤ 1}; 2x = (3/2, 2) is not; |2x|_S = |x|_S = 3/4. So
P is a projection on L²(A_S) that does not commute with Γ and defines no
operator on L²(X_S). Two exact facts tie it to the module ball: the
Γ-saturation of B_1 is the module ball, and the Γ-sum of its indicator is
n(x) = ⌊log_2(1/|x|_S)⌋ + 1 on |x|_S ≤ 1 (pinned on five points), a
function of the module that is not an indicator, so it is not a cutoff
projection on X_S.

### 1.3 The trace term each reading of "product ball" defines

ϑ(g) acts on L²(A_S) only through a section of C_S → ℝ^* × Q_2^*; the
level-0 section u ↦ (u, 1) gives ϑ(g) = ϑ_∞(g) ⊗ 1 on radial functions.

| reading | where | projection | trace term |
|---|---|---|---|
| (A) tensor of local Sonin spaces, open ball | L²(A_S) | S_∞ ⊗ \|σ_2⟩⟨σ_2\|/‖σ_2‖² | **T_∞(g)**, exactly (level-0 section); another section gives T_∞ of a dilate of g, so it is not canonical |
| (A') same, closed ball | L²(A_S) | 0 | 0 |
| (A'') theory formula S_∞ ⊗ P_2 + 1 ⊗ (1 − P_2), any P_2 with 1 − P_2 of infinite rank (M_{Z_2}, its Fourier conjugate, or the rank-one projection onto 1_{Z_2} or σ_2) | L²(A_S) | | **+∞** for every g ≠ 0: ϑ_∞(g)ϑ_∞(g)^* is a convolution on ℝ_+^*, not trace class |
| (A''') full joint kernel of P and P̂ | L²(A_S) | contains ker P_λ^∞ ⊗ (infinite-dimensional) | **+∞** |
| (X) (A) pushed through E_S | H | orthogonal onto θ_S(S_1(ℝ)) | **T^mod(g)**, exactly (§2) |
| (Xη) S_∞ ⊗ \|1_{Z_2}⟩ pushed through E_S | H | orthogonal onto η_S(S_1(ℝ)) | T^η(g), finite (§4) |
| (X'') the summand 1 ⊗ (1 − P_2) pushed through E_S | H | everything | **+∞**: E_S maps functions supported on \|x_2\|_2 > 1 onto H, since every Γ-orbit meets \|x_2\|_2 = 2 |

**Grade:** ordinary argument, unreviewed. The +∞ rows use only that a
convolution operator on ℝ_+^* with a nonzero kernel is not Hilbert-Schmidt.

## 2. What transfers: the Sonin subspace (prove, for reading X)

CCM Prop 4.6-4.7 and Thm 4.6: θ_S(f) := class of σ_2 ⊗ f in L²(X_S) is a
bounded bijection with bounded inverse L²(ℝ)^{ev} → H, and it maps the
archimedean Sonin space S_λ(ℝ) **onto** the module Sonin space S_λ(X_S).
The class map E_S applied to the tensor product of the local Sonin spaces
(open ball at 2, reading A) is θ_S by definition. So after the Γ-quotient
the product-ball Sonin space and the module Sonin space are **the same
closed subspace of H**, and the orthogonal projection onto it gives the
same trace: **T^(X) = T^mod exactly.**

Grade: ordinary argument (the identification of reading A's image with
θ_S), unreviewed, on CCM Thm 4.6 used as published. What was rechecked
here, at S = {∞, 2} with f = exp(−πx²), dps 30, by two routes (route 1:
the Γ-sum from the definition, Mellin transform by quadrature; route 2:
the local Euler factor times the closed-form archimedean transform
½ π^{−z/2} Γ(z/2), z = 1/2 − is):

| s | η_S, CCM (47): L_2(1/2 − is) | θ_S, CCM (57): 1 − 2^{−1/2−is} | route-1 ratio θ/η, real part |
|---|---|---|---|
| 0 | 2.7e−22 | 6.9e−32 | 0.08578643762690 = m(0) |
| 1.3 | 3.7e−21 | 1.9e−31 | 0.62212024700620 = m(1.3) |
| 5.7 | 1.7e−17 | 1.6e−31 | 2.47576743448401 = m(5.7) |
| 14.1347 | 1.5e−11 | 2.3e−15 | 2.8171503962, m(14.1347) to 4e−11 |

(relative deviations; the quadrature of the oscillatory integral limits
both columns, worst at the largest s.) **Grade: hardened** for these
identities at these points; Thm 4.6 itself is not rechecked.

## 3. What does not transfer: the projection (the exact gap)

In the Mellin picture let Ŝ := U_∞(S_1(ℝ)^{ev}) and a(s) := 1 − 2^{−1/2−is}.
From CCM (57), (47) and Thm 4.6:

- U_S(module Sonin space) = a · Ŝ;
- U_S(η_S(S_1)) = ā^{−1} · Ŝ, since L_2(1/2 − is) = 1/conj(a(s));
- every trace term above is T_W(g) = Tr(M_ĝ Π_W M_ĝ^*) = ‖Π_W M_ĝ^*‖²_HS
  for a closed subspace W, and T_∞ = T_Ŝ.

**The product side is an oblique projection onto the module space.** By
CCM Prop 4.7(iii), ⟨θ_S f, η_S h⟩ = ⟨f, h⟩, so θ_S^{−1} = η_S^*. Then
Π^obl := θ_S S_∞ η_S^* is an idempotent with range θ_S(S_1) = S_1(X_S), the
module Sonin space, and since θ_S commutes with ϑ(g),
Tr(ϑ(g) Π^obl ϑ(g)^*) = Tr(ϑ_∞(g) S_∞ ϑ_∞(g)^*) = T_∞(g). So reading (A)
and reading (X) are traces against two projections onto **the same
subspace**: oblique (A) and orthogonal (X).

**The same multiplier is the atom on window functions (exact).** In the
additive variable θ_S g = g − 2^{−1/2} g(· − log 2) (CCM Prop 4.6 proof),
so for g on the window ‖θ_S g‖² = (3/2)‖g‖² − √2 ⟨g, H g⟩ with H the shift
form of §5. Hence on the window space

    Gram(θ_S) = 3/2 − √2 H = 3/2 − W_2 / log 2      (2 < c < 4).

The non-isometry of θ_S is what separates the orthogonal from the oblique
projection, and compressed to window functions it is exactly the 2-adic
atom. The trace terms see a different compression of the same multiplier,
G = Π_Ŝ M_m Π_Ŝ on the Sonin space, which is not computed here. Checked by
direct quadrature of Gram(θ_S) (N = 2, the three cells, dps 30) against
3/2 − √2 H (at most 5.9e−31) and against the prime block of
`weil_trunc/galerkin.py` (at most 1.7e−31): hardened, three routes.
two_adic/ (commit f1e912d) derived and pinned this identity first; this
folder rechecks it by direct quadrature as a third route.

**When they coincide.** In Mellin form Π^obl = M_a Π_Ŝ M_a^{−1}; it is
self-adjoint iff Π_Ŝ commutes with M_m, m = |a|² = 3/2 − √2 cos(s log 2),
i.e. iff S_1(ℝ) is invariant under D_2 + D_{1/2} (the unitary dilations by
2 and 1/2). On |x| < 1, D_2 f vanishes but D_{1/2} f(x) = √2 f(2x) vanishes
only if f = 0 on |x| < 2; the Fourier side is the same with f̂. So
invariance forces S_1 = S_2. Grade: ordinary argument, unreviewed.
Whether the Sonin chain is strict between λ = 1 and 2 was **not checked
here**, and operator equality is not necessary for equal traces on window
functions: a trace term only sees the diagonal of Π_W, i.e. a distribution
τ_W with T_W(g) = ⟨τ_W, g ∗ g^*⟩, and two cutoffs give the same T on window
c iff their τ agree on (c^{−1}, c).

**Which term fails to transfer, conditionally.** Connes-Consani Thm 4.7
gives τ_Ŝ = W_∞ + ε_∞ with ε_∞ (their ε, eq. (84)) a bounded function.
The semilocal analogue, obtained by running their argument on (22) with
the module projections, would read τ_mod = W_∞ − W_2 + ε_S. It needs the
exact finite-cutoff form of (22) at S = {∞, 2} and the spectral
decomposition of the module pair (P^S, P̂^S), neither of which exists yet
(CCM say the semilocal prolate operator is still a candidate). If it
holds,

    T^mod(g) − T_∞(g) = −W_2(g ∗ g^*) + ⟨ε_S − ε_∞, g ∗ g^*⟩,

and on c ∈ (2, 3) the atom at u = 2 cannot be cancelled by a bounded
function, so T^mod ≠ T_∞ there: **the 2-adic atom is the term that fails
to transfer.** Grade: derivation, conditional on the unproved semilocal
analogue; not checked numerically.

## 4. The bound (task 2)

**Lemma.** Let W ⊂ L²(ℝ, ds) be closed, b measurable with
0 < β₋ ≤ |b|² ≤ β₊. Then for every g,

    (β₋/β₊) T_W(g) ≤ T_{bW}(g) ≤ (β₊/β₋) T_W(g).

*Proof.* A := M_b Π_W has closed range bW and A^*A = Π_W M_{|b|²} Π_W =: G
with β₋ ≤ G ≤ β₊ on W, so Π_{bW} = A G^{−1} A^* lies between β₊^{−1}AA^*
and β₋^{−1}AA^*. Conjugating by M_ĝ, which commutes with M_b, and taking
traces of positive operators: T_{bW}(g) ≤ β₋^{−1}‖Π_W M_{b̄ ĝ̄}‖²_HS =
β₋^{−1} Tr(Π_W M_{|b|²|ĝ|²} Π_W) ≤ (β₊/β₋) T_W(g). The lower bound is the
same with the roles swapped. ∎

With b = a (module) and b = ā^{−1} (η), β₊/β₋ = max m / min m for both:

    κ = (3/2 + √2)/(3/2 − √2) = (3 + 2√2)² = 17 + 12√2 ≈ 33.97,
    κ^{−1} T_∞ ≤ T^mod ≤ κ T_∞,   κ^{−1} T_∞ ≤ T^η ≤ κ T_∞,   so T^mod/T^η ∈ [κ^{−2}, κ²].

Grade: ordinary argument, unreviewed; κ and the range of m exact.
Finite-dimensional sanity check (n = 40, random 12-dimensional W, random
|b|² ∈ [min m, max m] and ĝ, seed 7, 400 trials): every ratio
T_{bW}/T_W lies in [0.8099, 1.1624], well inside [1/κ, κ] (measured). The
bound is far from tight on random data; it is what survives the worst case
of m.

What the bound does **not** give: control of the inertia of R_S. The
difference T^mod − T_∞ is not of finite rank, so the negative index of
Q − T^mod and of Q − T_∞ are not related by it.

## 5. Consequence for C4: the product-side term is refuted

C4 (theory §7.2) asks for Q(g) ≥ T_S(g) − R_S(g) on the class with R_S of
bounded rank. Take T_S = T_∞, reading (A), which is what a T_S built on
L²(A_S) with the level-0 section computes. On the class,

    R := Q − T_∞ = (W_∞ − T_∞) − W_2 = −⟨ε_∞, g ∗ g^*⟩ − √2 log 2 · ⟨g, H g⟩.

1. The first term is Hilbert-Schmidt on L²(window): Connes-Consani
   eq. (84), with ξ_n and ζ_n unit vectors (their Prop 4.5) and the prolate
   values 0 < λ(n) < 1 decaying to 0, gives |ε_∞| ≤ Σ_n λ(n)(1 − λ(n)²)^{−1/2}
   < ∞, a bounded kernel on a compact square. (Read off their formula, used
   as published.)
2. H is the shift form v ↦ Re ∫ f(y) conj f(y − log 2) dy on L²[0, ℓ]. For
   log 2 < ℓ < log 4 the collars I₁ = [0, ℓ − log 2] and I₂ = [log 2, ℓ]
   are disjoint, the shift is unitary from L²(I₁) onto L²(I₂), and H acts
   as ½[[0, S^*], [S, 0]] there and as 0 on the middle interval. Its
   spectrum is {−1/2, 0, 1/2}, each of infinite multiplicity (exact
   argument).
3. By Weyl's theorem the essential spectrum of R contains
   −(√2/2) log 2 = −0.4901. So R has infinite negative index, also on the
   finite-codimension C4 class. No finite-rank R_S can make the inequality
   hold.

**Candidate refuted (ALIGNMENT s5, disposition 1): C4 with the
product-side trace term, on every window c ∈ (2, 3).** Grade: ordinary
argument, unreviewed; its inputs are Connes-Consani Thm 4.7 (used as
published) and the assumption that Q and T_∞ are in the same normalization
(the one C4 itself presupposes). The prime atom enters Q and is absorbed by
no trace term: this is the arithmetic failure of reading (A).

**Galerkin measurement (dps 40, shared basis).** H on the mission cells;
two routes to the matrix (the closed form in `shift_form_matrix`, and the
prime block of `weil_trunc/galerkin.py`) agree to at most 5.0e−40
entrywise at N = 8 and 16 (N = 32 not run through the second route). The negative directions of −W_2 are the eigenvalues of H above
1/4:

| c | N | H > 1/4 | H < −1/4 | (2N+1)(ℓ − log 2)/ℓ | max eig H |
|---|---|---|---|---|---|
| 2.2 | 8 | 2 | 2 | 2.05 | 0.4911 |
| 2.2 | 16 | 3 | 4 | 3.99 | 0.49997 |
| 2.2 | 32 | 7 | 8 | 7.86 | 0.5000 |
| 2.5 | 8 | 4 | 4 | 4.14 | 0.49999 |
| 2.5 | 16 | 8 | 8 | 8.04 | 0.5000 |
| 2.5 | 32 | 15 | 16 | 15.83 | 0.5000 |
| 2.9 | 8 | 5 | 6 | 5.93 | 0.5000 |
| 2.9 | 16 | 11 | 12 | 11.52 | 0.5000 |
| 2.9 | 32 | 23 | 22 | 22.68 | 0.5000 |

The counts grow with N at every c and track the collar fraction within 1
(measured; counts unchanged at dps 25 for N = 16). **Prediction for
checker/**, not a measurement: if two_adic/'s T_S reduces to kernel/'s
T_inf_matrix on the ζ data, the negative inertia of R_S = Q − T_S will
grow with N at every cell at about this rate, up to a bounded number
coming from the Hilbert-Schmidt part.

## 6. Matrix comparison on the cells (task 3): not computed

T^mod − T_∞ on the shared basis needs an orthonormal basis of a truncation
of Ŝ, which is kernel/'s gap (a) and was not delivered in this box
(kernel/ held only its brief). The cost once it exists: with J Sonin
vectors φ_j, one J × J Gram matrix G_{jk} = ⟨φ_j, m φ_k⟩ (m acts as
3/2 − (D_2 + D_{1/2})/√2, so each φ_j is needed on the dilated range
[c^{−1/2}/2, 2c^{1/2}]), one inversion, and then T^mod_{nm} =
Σ_{jk} ⟨U_n-image, a φ_j⟩ (G^{−1})_{jk} ⟨a φ_k, U_m-image⟩ against
T_∞'s Σ_j ⟨·, φ_j⟩⟨φ_j, ·⟩. That is the same order of work as T_∞ itself
plus 2J² extra inner products per cell, so no CI proposal is needed; it is
a follow-up for whoever holds S_∞.

## 7. Lean / AXLE (task 4): not attempted

The only clean lemma is §4's, and its content is operator theory (ranges
of multiplication operators, traces of positive operators) whose Mathlib
statement would take longer than the box. The scalar core
(3/2 − √2 ≤ 3/2 − √2 cos t ≤ 3/2 + √2 and κ = 17 + 12√2) is pinned exactly
by sympy in the tests instead.

## 8. Grading summary and status

| statement | grade |
|---|---|
| local facts at 2 (§1.2 table); Γ-non-invariance; Γ-sum formula | exact |
| theory §7.3 item 2 local claim is false | exact |
| trace terms of readings A, A', A'', A''', X'' (§1.3) | ordinary argument, unreviewed |
| product Sonin space = module Sonin space after Γ (reading X) | ordinary argument on CCM Thm 4.6, used as published |
| CCM (47), (57) at S = {∞, 2} | hardened (two routes, dps 30) |
| Gram(θ_S) = 3/2 − W_2/log 2 on the window space, 2 < c < 4 | exact; hardened numerically (three routes, dps 30, N = 2) |
| product side = oblique projection; coincidence iff M_m-invariance ⇒ S_1 = S_2 | ordinary argument, unreviewed |
| T^mod − T_∞ = −W_2 + ⟨ε_S − ε_∞, ·⟩ | derivation, conditional on an unproved semilocal analogue of CC Thm 4.7 |
| bound with κ = 17 + 12√2 | ordinary argument, unreviewed; constants exact |
| C4 with T_∞ refuted on c ∈ (2, 3) | ordinary argument, unreviewed, on CC Thm 4.7 |
| Galerkin counts of H (§5 table) | measured |

**ALIGNMENT s5 status.**

- C4 with the product-side trace term (reading A): **candidate refuted**,
  every window c ∈ (2, 3), for the stated reason.
- Readings A'', A''', X'' (the theory formula as written): no finite trace
  term exists, so there is nothing to test.
- C4 with the module trace term T^mod (reading X, the one in (22)):
  **attempt unresolved.** Its remainder is −⟨ε_S, ·⟩ if the semilocal
  analogue holds, and whether that has bounded negative rank is exactly
  the semilocal prolate problem.
- Nothing here closes C4 as a family, and nothing is claimed about RH.

**Original versus known.** The module Sonin space, θ_S, η_S and Thm 4.6
are CCM's. Original to this folder: the table of readings (§1.3), the
identification of the product side as an oblique projection (§3), the
comparison bound (§4) and the refutation of the product-side reading
(§5). The window identity Gram(θ_S) = 3/2 − W_2/log 2 is two_adic/'s
(f1e912d), rechecked here. Novelty was not searched.

## 9. Reproduction

    PYTHONPATH=$PWD /Users/thomas/zeta-lab/.venv/bin/python hunts/weil_propagation/c4_s2/cutoff/cutoff.py   # about 100 s, writes cutoff_cells.json
    PYTHONPATH=$PWD /Users/thomas/zeta-lab/.venv/bin/python -m pytest -q -n 2 hunts/weil_propagation/c4_s2/cutoff tests/test_hunt_probe_discipline.py tests/test_docs_numbering.py
