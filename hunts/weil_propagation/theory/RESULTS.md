# RESULTS: theory worker, Weil positivity propagation across window size

1. **Strongest candidate, C2 (Levy-Markov + pole). Grade: ordinary argument, unreviewed (checked by nobody outside this session).** With the pole term removed, the zeta Weil form on any window is exactly a jump Dirichlet form minus a constant C_ℓ. The jumps are the digamma Levy density ½K(|u|), K(x) = 2e^{−x/2}/(1 − e^{−2x}), plus jumps ±log n at rate Λ(n)/√n, killed outside the window; C_ℓ = log π − ψ(1/4) + Σ_{log n<ℓ} 2Λ(n)/√n up to terms that vanish as ℓ grows (exact form in §2.6). Λ ≥ 0 (Markov), together with the irreducibility hypothesis (K continuous and strictly positive on (0, ℓ]), makes the pole-free operator's ground state simple and a.e. positive on every window.
2. **What it would give.** Simplicity transfers to the even sector of the full form with the pole by rank-one interlacing. This needs neither condition (a) nor positivity. The bottom is min(r₁, μ_k) over pole-free even eigenvalues μ_k with an eigenvector orthogonal to the pole vector c = cosh((x−x₀)/2), where r₁ is the smallest secular root. Simplicity fails only on a tie r₁ = μ_k, or a degenerate such μ_k below r₁. **Grade: derivation, not measured.** Evenness (even bottom below odd bottom) is not obtained. Positivity reduces exactly to (a), at most one even Dirichlet eigenvalue below C_ℓ, plus (b), a scalar pole-capacity inequality (derivation). **As a propagation lemma, (a)+(b) is a reformulation of RH (even sector), not progress** in the mission's sense. The output is the unconditional Proposition M. **Measured** at (c, N) = (13, 24) and (31, 32): (b) is 1.1e6 and 1.6e6 times tighter than (a), and (a)'s own margin is 3.5e−37 and 6.5e−63. The Poincaré attempt on (a) (§6) is unresolved.
3. **What refutes it.** DH lies outside C2's hypotheses: its jump measure is signed (Λ_f(3) = −0.312) and it has no pole. **So DH does not test C2 at all.** Neither does the lab's Euler-product rival W_a = ζ(s+a)ζ(s−a), which is Markov but has two pole directions. **C2 has so far faced no rival that satisfies its hypotheses.** It stays a candidate until the Epstein (1,1,6) control runs (one pole, Λ_Q ≥ 0 for n ≤ 47; handed to numerics): a negative Epstein window form below c = 48 refutes "Markov + one pole". Separately: C1 (propagation through entering atoms) is refuted at every band N = 64 … 256. DH's sign flips at hardened brackets c*(N) ∈ [30.617, 30.818], inside the step (29, 31), where no atom with nonzero weight enters (numerics `crossing.json`; Λ_f(30) = 0 here). For the continuum form this holds provided the continuum crossing lies above c = 29: the N-ladder indicates about 30.61 (measured) but does not establish it. C3 (norm-level ground-state transport) is refuted by DH (measured).
4. **New or known:** the Markov reading of the full Weil form, primes included, and the prime-entry kink formula are original to this session. They were not in the 10 sources read, and one web search found nothing. Suzuki (arXiv:2606.09096 s5) uses a Dirichlet form for the archimedean part only, and only for small windows. The fixed-window dilation formula is Suzuki's s4.2. Novelty is not established: the search was shallow.
5. **Next step.** Numerics (handed off): the Epstein (1,1,6) floor for c ≤ 48, and μ₂ against λ₁, λ₂ over c ∈ [2, 60]. Theory: the Poincaré attempt (§6) shows the extremal of (a) is e₂, the second pole-free eigenvector, which is orthogonal to the pole to 2⟨c,e₂⟩² = 4.4e−63 (measured). That points to CCM's near-radical vectors, so the next step is to show that the near-radical subspace orthogonal to the Perron-Frobenius state has nonnegative pole-free energy: CCM step 2 at the eigenvalue scale.

Study of 2026-09-23, branch `teal-sea/weil-propagation-theory`. Nothing
here is a claim about RH. Grades follow the `AGENTS.md` ladder: *measured*,
*hardened*, or an ordinary mathematical argument with its review status
stated. No kernel-checked statement is made. Checks: `checks.py`,
raw numbers in `checks.json` (total runtime about 2 minutes).

## 0. Conventions

A window is an interval I of length ℓ in the additive variable x = log u.
Then c = e^ℓ (the CCM cutoff), λ = √c (CCM), a = ℓ/2 (Suzuki), and Zhu's
L equals a. Test functions f ∈ L²(I) have autocorrelation
g(x) = ∫ f(y) f(y − x) dy, supported in [−ℓ, ℓ]. The Weil form, in the
normalization of Zhu arXiv:2608.24827 eq. (2)-(3) and Lemma 2.5, is

    Q(f) = P(f) + A(f) − Σ_{log n < ℓ} 2Λ(n) n^{-1/2} g(log n),
    P(f) = 2 ∫ g(x) cosh(x/2) dx                                  (pole),
    A(f) = −[γ + log π + log(1 − e^{−2ℓ})] g(0)
           + ∫_0^ℓ 2[e^{−2x} g(0) − e^{−x/2} g(x)] / (1 − e^{−2x}) dx.

Check E confirms the constants against `zeta/weil.py`, whose convention the
lab calibrated independently. λ*(ℓ) is the infimum of Q(f)/‖f‖². λ_N(c) is
the lowest even-sector eigenvalue of the CCM Galerkin matrix at band N
(`hunts/rogue_frontier/weil_trunc/galerkin.py`).

Conversions for the landmarks: Yoshida's range is ℓ = log 2 (c = 2). Zhu's
support-1.6 theorem is ℓ = 1.6 (c ≈ 4.95). The DH lattice crossing is
c = 31 (ℓ = 3.434, Zhu L = 1.717).

## 1. Primary sources: what each proves about window dependence

Read in full or in the cited sections, 2026-09-23. Local PDFs were kept in
the session scratchpad and are not committed.

| source | what it proves about the window | role of an entering prime | where it says it is stuck |
|---|---|---|---|
| Connes, arXiv:math/9811068 (Selecta 1999), s VII Thm 4, s VIII | Semilocal trace formula: for every finite set S of places, the geometric side of the trace of the scaling action is exactly Σ_{v∈S} W_v. The window picks S = {∞} ∪ {p < c}. | A prime enters as a new place in S; the formula holds for every S. | The global case (all places) is shown equivalent to RH for all Grössencharakter L-functions (s VIII, Thm 5), and is not proved. |
| Connes-Consani, arXiv:2006.13771 (Selecta 2021), Intro, s3, Thm 6.11 | Positivity only for the archimedean place, support in (1/2, 2), i.e. ℓ < log 2 with prescribed zeros of the transform: W_∞(g∗g*) ≥ Tr(ϑ(g) S ϑ(g)*) − c|ĝ(0)|², 13 < c < 17. Cor 3.8 and Rem 3.9 give the simplest version on (1/1.15, 1.15). | None: the range is chosen so that no prime enters. The stated plan (Intro) is to add places {2, …, p} for support in (p^{−1}, p). | The prime places. Only S = {∞} is done, and step 6 of s4 needs a numerically identified eigenvector. |
| Yoshida 1992 (ASPM 21, 281-325) | **Not read: the full text sits behind Project Euclid's bot wall.** Per Bombieri 2000 s1 and Zhu s1.2, Yoshida reduced fixed-window positivity to a finite computation (depending on the window), verified it at half-width (log 2)/2, and showed RH ⟺ nondegeneracy on every window. | none (window below log 2) | no window mechanism |
| Bombieri, Rend. Lincei 11 (2000) 183-233 | Minimizers exist (Thm 3/4). The even and odd infima are claimed continuous and decreasing in the window (Thm 5; Suzuki says the details are incomplete). A Yoshida-type bound for window length < log 2 (Thm 12). **In finite zero models the number of negative eigenvalues equals the number of off-line pairs, for every window (Thm 8).** Passage to the limit (Thm 10): a negative eigenvalue stays bounded away from 0, or a linear relation among x^{−ρ} holds on a window; small windows cannot see off-line zeros. §13 (numerics, fake zero at 0.52 + 3.14i): there is a critical window t_c, below which the negative eigenvalue → 0 as N → ∞. | none | Linear independence of {x^{−ρ}} on windows, "probably quite difficult". |
| CCM, arXiv:2511.22755, s3.1-3.2, s5, s7-8 | μ_λ is nonincreasing in λ (3.27). Cor 3.8: lim μ_λ = 0 ⇒ RH. Discrete spectrum (Thm 3.6). Truncated ground state gives real zeros (Thm 1.1). (Display note: (3.19) prints the prime sum over n ≤ λ; with L = 2 log λ and the abstract, it must run over n ≤ λ².) | Prime-power block Wp (4.3); no structural role. | s8, two missing steps: (1) the smallest eigenvalue is simple with an even eigenvector; (2) the prolate guess k_λ approximates ξ_λ well enough to make the zeros converge. |
| CvS, arXiv:2511.23257, s1, s4 (Prop 4.1) | For **any** real distribution D on [0, L]: if the lowest eigenvalue is simple and isolated with an even eigenfunction, its Fourier transform has only real zeros. Nothing depends on the window, and no sign is required. | none: the theorem is arithmetic-free | "The key difficulty … becomes the verification that zero is indeed the (simple) minimal eigenvalue." |
| Connes, arXiv:2602.04022, s6, s7.2-7.4 | Strategy: as x → ∞, the minimal eigenvectors θ_x → E(h), with FT → Ξ (s6.5 Fact 6.4). s7.4 writes QW_λ through the semilocal trace formula (22). | Enters through the semilocal S. | s6.6: the same two steps as CCM s8. |
| Zhu, arXiv:2608.24827 v2 | λ*(0.8) ≥ 8.9e−18 (support 1.6, Thm 1.2). A simple even ground state at support 1.6 (Thm 6.2). Unconditional upper bounds down to 3.2e−283 at L = 2, fitted by −ln λ* ≈ 2π² N(T*)/ln N(T*) with T* = 2πe^{2L} (Conj 12.1). Under RH, λ* ≤ exp(−L e^L) (Thm 1.3). | Each prime power adds 2Λ(n)/√n to the comb mass A_L. By Thm 1.4 any pointwise-envelope argument needs frequencies up to T₁ = 2π e^{A_L}, which is doubly exponential in L. | Passing the barrier "requires cancellation in the prime comb, a concrete arithmetic problem" (abstract, s14.3). |
| Suzuki, arXiv:2606.09096 v2 | A_a is the Friedrichs extension of D*G_aD, with screw function g_ζ (Thm 1.1). **λ_a is continuous in a** (Thm 1.3, full proof). For small a, λ_a = log(1/a) + μ₁ − log 2π + ψ(2) − 1 + O(a), and is simple and even (Thm 1.4, via a Dirichlet form for the archimedean part). Real zeros of W(a, θ; z) for every a, using only that the prime sum is finite (Thm 1.5). **s4.2 gives the scaling to a fixed interval** (eq. 4.5). | Treated as an O(a) bounded perturbation. | Cor 1.6's limit formula would give RH. "Control of λ (< λ_a) … is expected to require a detailed analysis of the arithmetic contribution" (s1.2). |

**Summary of the literature on the question asked.** No source gives a
mechanism by which positivity on one window forces positivity on a larger
one. The window dependence that *is* established:

- monotone decrease of the infimum (nested domains);
- continuity (Suzuki);
- positivity on small windows (Yoshida, Bombieri, Connes-Consani, Suzuki);
- a finite reduction per window (Yoshida, Zhu);
- measured and conditional decay laws (Zhu);
- a detection threshold for off-line zeros (Bombieri §13, numerics).

No source assigns a positive role to an entering prime. Every program
reports being stuck at the same place, the arithmetic content beyond a
fixed window: the global trace formula, the prime places, the simplicity
and proximity steps, and comb cancellation.

## 2. Derivations: how the form depends on the window

### 2.1 The form does not move; the domain grows

Q(f) = ⟨D, f ⋆ f̃⟩ for one fixed even distribution D on ℝ: the pole, the
archimedean principal value, and atoms Λ(n)n^{−1/2} at ±log n. In §0,
log(1 − e^{−2ℓ}) is the exact integral of the archimedean kernel beyond ℓ,
where g = 0, so the ℓ in the formula is bookkeeping, not dependence. The
window only restricts supp f. Hence H_ℓ ⊂ H_ℓ' gives λ*(ℓ') ≤ λ*(ℓ) (as in
CCM (3.27)), and the question is purely whether a positive form extends
from a subspace to a larger one.

### 2.2 Fixed-window form (the "archimedean change")

For f ∈ L²[−1, 1], ‖f‖ = 1, set f_a(x) = a^{−1/2} f(x/a) ∈ L²[−a, a]
(unitary) and g = f ⋆ f̃ on [−2, 2]. Substituting x = ay:

    Q(f_a) = 2a P₊(a) P₋(a) − γ − log π − log(1 − e^{−4a})
             + ∫_0^2 2a [e^{−2ay} − e^{−ay/2} g(y)] / (1 − e^{−2ay}) dy
             − Σ_{log n < 2a} 2Λ(n) n^{−1/2} g(log n / a),
    P_±(a) = ∫ f(u) e^{±au/2} du.

This is the Weil-form version of Suzuki's (4.5). **Check E:** for the box
f = 1_{[−1,1]}/√2 it equals 2a·W(h) of `zeta.weil.fejer_pair(a)`, with
|dev| = 5.4e−16, 8.6e−19, 2.0e−21 at a = 0.3, 0.8, 1.2 (dps 30; the three
cells include 0, 3 and 5 prime powers).

In these coordinates, growing the window leaves the function space alone
and changes the form smoothly:

- the pole weight changes;
- the archimedean kernel is rescaled (its leading effect is Suzuki's −log a
  shift);
- every existing atom drifts inward to log n/a;
- new atoms enter at the edge y = 2.

If the ground state φ_a is simple (so the envelope theorem applies),
dλ*/da = ∂_a Q(φ_a) evaluated with the formula above. Grade: derivation.
The differentiability assumptions are stated here and not proved.

### 2.3 New prime-power atoms: zero weight, then a slope kink

An atom at n enters at ℓ = log n, where g(ℓ) = 0: it enters with **zero
weight**, so λ* stays continuous. For ℓ slightly above log n,
g(log n) ≈ (ℓ − log n) f(0⁺) f(ℓ⁻). The slope therefore jumps:

    Δ (dλ*/dℓ) at ℓ = log n  =  −2 Λ(n) n^{−1/2} φ(0) φ(ℓ)      (continuum; φ the ground state on [0, ℓ])
    Δ (dλ_N/dL)               =  −Λ(n) n^{−1/2} (2/L) (Σ_{|k|≤N} u_k)²   (exact at finite N, CCM basis)

The finite-N line holds because the CCM entries of the atom,
q_{jk}(log n) with L near log n, vanish at L = log n and have derivative
exactly (2/L)·𝟙𝟙ᵀ (differentiate CCM (2.9)-(2.10) in L). Hellmann-Feynman
then applies, assuming a simple eigenvalue.

**Check C** (ζ, N = 16, dps 45, one-sided second-order differences at
h = 1e−6), measured jump against predicted jump:

| q | λ_N at log q | slope left | slope right | rel. dev |
|---|---|---|---|---|
| 3 | 7.31e−8 | −1.83e−6 | −3.29e−6 | 3.8e−9 |
| 4 | 1.06e−12 | −4.03e−11 | −5.18e−11 | 1.7e−8 |
| 5 | 1.77e−17 | −7.35e−16 | −1.19e−15 | 2.5e−8 |
| 7 | 4.32e−25 | −1.49e−23 | −2.48e−23 | 6.1e−8 |

For ζ, Λ ≥ 0 and the ground state is reflection-even (φ(0) = φ(ℓ)), so
**every entering prime power makes the decrease steeper**; each entry adds
50-80% to the slope in these N = 16 cells. That magnitude is band-specific.
The numerics worker finds the band-N edge amplitude μ₀ falling and κ rising
with N, with κμ₀² stable. So the continuum edge value may vanish slowly,
the finite-N formula (exact) is the operative one, and the continuum line
is a limiting form whose edge factor must be read as the N-stable
combination, not as a pointwise value. An entering prime never helps
positivity at first order. For DH, atoms with Λ_f(n) < 0 do the opposite.

### 2.4 The admissible space: the collar criterion

Grow [0, ℓ] to [0, ℓ'] and split H_ℓ' = H_ℓ ⊕ C with collar
C = L²(ℓ, ℓ']. If Q > 0 on H_ℓ, then

    Q ≥ 0 on H_ℓ'  ⟺  S := Q_CC − Q_CI Q_II^{−1} Q_IC ≥ 0 on C     (exact)
    necessary:  Q(φ_ℓ, h)² ≤ λ*(ℓ) · Q(h)  for every h ∈ C          (one-mode test)

since Q_II^{−1} ≥ φ_ℓφ_ℓᵀ/λ*(ℓ). The arithmetic sits in the blocks as
follows:

- Q_CC involves shifts smaller than ℓ' − ℓ, so for steps shorter than
  log 2 it contains **no atoms**, only archimedean and pole terms.
- Q_CI carries the old atoms (shifts up to ℓ').
- Q_II^{−1} carries the interior.

The one-mode test needs every collar function's coupling to the ground
state to be O(√λ*), and λ* ≈ exp(−2π² N/ln N) (Zhu). Grade: elementary
linear algebra (ordinary argument).

### 2.5 The DH lattice step 30 → 31 adds no arithmetic

**Check A/B** (exact arithmetic, confirmed numerically):

- Λ_f(n) = 0 for every n divisible by 5. f is supported on the
  multiplicative semigroup {5 ∤ n}, and so is −f′/f. So Λ_f(30) = 0.
- Λ_f(31) = log 31 exactly (31 is prime and 31 ≡ 1 mod 5).
- At c = 31 the n = 31 atom sits at y = L, where every CCM entry vanishes
  (largest contribution 8.4e−50).

Between the windows log 30 and log 31, the set of atoms with nonzero weight
is {n ≤ 29, 5 ∤ n} at both ends. The same holds for ζ (prime powers ≤ 29).
**The DH sign flip at (31, 60) happens with no new arithmetic entering.**
Only the window length changed (by 0.033), with the archimedean kernel on
the new shell. (My milestone-1 note in `PROGRESS.md` said the entering atom
was n = 31 with ζ's weight; that was incomplete. The effective entering set
is empty.)

### 2.6 The Levy-Markov structure (the new structural fact)

Using the exact identity g(0) − g(x) = ½ ∫_ℝ (f(y) − f(y − x))² dy:

    Q(f) = P(f) + 𝓔(f) − C_ℓ ‖f‖²,
    𝓔(f) = ½ ∫_0^ℓ K(x) ∫_ℝ (f(y) − f(y−x))² dy dx + Σ_{log n<ℓ} Λ(n) n^{−1/2} ∫_ℝ (f(y) − f(y − log n))² dy,
    K(x) = 2 e^{−x/2} / (1 − e^{−2x}) > 0,
    C_ℓ  = γ + log π + log(1 − e^{−2ℓ}) + ∫_0^ℓ 2(e^{−x/2} − e^{−2x})/(1 − e^{−2x}) dx + A_ℓ,   A_ℓ = Σ_{log n<ℓ} 2Λ(n) n^{−1/2}.

In Fourier form, 𝓔(f) = (1/2π) ∫ |F|² ψ_ℓ(t) dt with

    ψ_ℓ(t) = ∫_0^ℓ K(x)(1 − cos tx) dx + Σ_{log n<ℓ} 2Λ(n) n^{−1/2} (1 − cos(t log n)).

That is a Levy-Khintchine exponent, and ψ_∞ minus its comb part is
Re ψ(1/4 + it/2) − ψ(1/4), Gauss's representation as in Zhu (9). As
ℓ → ∞, C_ℓ − A_ℓ → log π − ψ(1/4), which recovers Zhu's symbol
Ψ_L = ψ_ℓ − C_ℓ.

**Proposition M (ordinary argument, unreviewed; checked by nobody outside
this session).** Take ζ and any window I, and let Q° = Q − P (pole
removed). The hypotheses used are:

- (H1) **Λ(n) ≥ 0 for every n**, so the jump measure (½K(|u|)du plus atoms
  Λ(n)n^{−1/2} at u = ±log n) is nonnegative;
- (H2) **irreducibility**: the digamma Levy density ½K(|u|) is continuous
  and strictly positive for 0 < |u| ≤ ℓ, so every pair of points of I is
  joined by a jump of positive intensity;
- (H3) the form domain is that of the archimedean part. P, the atoms and
  the constant are bounded on L²(I), and Q has discrete spectrum
  (CCM Thm 3.6; Suzuki s4.1 for the compact embedding).

Under (H1)-(H3), 𝓔 is an irreducible Dirichlet form on L²(I): a pure jump
form, with killing from jumps that leave I. Q° = 𝓔 − C_ℓ. Consequences:

- Its semigroup is positivity improving (the Beurling-Deny criterion, then
  irreducibility, via the same Dirichlet-form route as Suzuki s5.2).
- Its lowest eigenvalue μ₁ is simple, and the eigenfunction is a.e.
  positive and reflection-even about the window centre.

In probability terms: **the pole-free Weil operator on a window is the
generator of the zeta jump process killed outside the window, shifted down
by C_ℓ.**

**Corollary (sector reduction).** The pole is P = 2⟨f, c⟩² on even f and
−2⟨f, s⟩² on odd f, with c = cosh((x − x₀)/2), s = sinh((x − x₀)/2) about
the centre x₀, and no cross term (Zhu Lemma 6.1). Rank-one interlacing
then gives:

- μ₁(Q°) ≤ λ₁(Q_e) ≤ μ₂(Q°_e) ≤ λ₂(Q_e).
- **Simplicity of the full form's even bottom (derivation, not
  measured).** The eigenvalues of Q_e are the roots of the secular function
  f(λ) = 1 + 2 Σ_k ⟨c, e_k⟩² / (μ_k − λ) (one in each gap between
  consecutive μ_k with ⟨c, e_k⟩ ≠ 0), together with every μ_k whose
  eigenvector is orthogonal to c. μ₁ is simple and ⟨c, e₁⟩ > 0 (both e₁
  and c are positive), so the smallest root lies strictly above μ₁ and is
  simple. Hence λ₁(Q_e) = min(r₁, μ_k : e_k ⊥ c), with r₁ the smallest
  root. Since μ₁ is simple with ⟨c, e₁⟩ > 0, every c-orthogonal μ_k has
  k ≥ 2. **The nongeneric coincidence, exactly:** either r₁ equals a
  c-orthogonal μ_k (a tie), or a *degenerate* c-orthogonal μ_k lies below
  r₁. If a simple c-orthogonal μ_k lies below r₁, the bottom is still
  simple, but its eigenvector e_k changes sign. Neither condition (a) nor
  positivity is needed.
  Measured caution: e₂ is orthogonal to c to 2⟨c, e₂⟩² = 4.4e−63
  (c = 13) and 4.2e−113 (c = 31), so half of the coincidence is nearly
  realised. The other half fails by a factor of about 1e6 (λ₁(Q) = 3.1e−43
  against μ₂ = 3.5e−37 at c = 13), so the bottom is simple in both cells.
- **Even-sector positivity:** Q_e ≥ 0 ⟺ (a) μ₂(Q°_e) ≥ 0, and (b)
  μ₁ ≥ 0 or Φ_ℓ := 1 + 2⟨c, (A°_e)^{−1} c⟩ ≤ 0.
- **Under RH:** on every window the killed zeta process has at most one
  even Dirichlet eigenvalue below C_ℓ.
- **Odd sector:** μ₁(Q°_o) ≥ μ₂(Q°), because the Perron-Frobenius state is
  even, and Q_o ≥ 0 ⟺ Q°_o ≥ 0 and 1 − 2⟨s, (A°_o)^{−1} s⟩ ≥ 0.

Whether the even bottom lies below the odd one, the other half of CCM
step 1, is not decided here.

**Check D** (measured; CCM basis; ground-state profile on a 400-point grid):

| cell | pole-free μ₁ | pole-free μ₂ | Weil λ₁ | Weil λ₂ | pole-free ground state |
|---|---|---|---|---|---|
| ζ, c = 13, N = 24 | −5.850 | 3.50e−37 | 3.07e−43 | 5.44e−37 | positive, min/max 0.80 |
| ζ, c = 31, N = 32 | −8.782 | 6.48e−63 | 4.05e−69 | 1.01e−62 | positive, min/max 0.71 |

In both cells the pole-free form has exactly one negative even eigenvalue,
as Proposition M plus positivity require. μ₂(Q°) = 0.64·λ₂(Q), which is
1.1e6 and 1.6e6 times λ₁(Q). So the pole capacity (b) is the tight
condition. But (a) is not easy either: its margin is 1e−37 absolute
against an O(6) gap.

## 3. Numerical checks, summary

All in `checks.py`, raw values in `checks.json`. Grade: measured, float
arithmetic at the stated dps. Sign statements for DH at c = 30, 31 are the
lab's hardened ones (`hunts/rogue_frontier/weil_trunc/RESULTS.md` s8.1).

| check | content | result |
|---|---|---|
| A | DH arithmetic, n ≤ 40 | Λ_f(5m) = 0; Λ_f(30) = 0; Λ_f(31) = log 31; negative at n ∈ {3,4,9,12,13,14,19,23,27,29}; composite atoms {6,12,14,18,21,22,24,26,28} |
| B | edge atom | n = 31 contributes ≤ 8.4e−50 at c = 31 |
| C | prime-entry kink | predicted jump confirmed to 4e−9 … 6e−8 relative at q = 3, 4, 5, 7 |
| D | Perron-Frobenius structure | see §2.6 |
| E | fixed-window formula vs `zeta/weil.py` | agreement 5e−16 … 2e−21 |
| F | ground-state transport 30 → 31 | DH (N = 60): ‖v₃₁ − v₃₀‖ = 7.7e−3, λ: +1.37e−28 → −1.87e−31. ζ (N = 32): ‖Δ‖ = 4.4e−3, λ: 4.38e−69 → 4.05e−69. Rayleigh quotient of the transported old ground state at the new window: 5.2e−5 (DH), 6.8e−8 (ζ) |
| G | ζ boundary mass φ_N(0)²/λ_N | 12.6 … 24.2 while λ ranges over 5.9e−8 … 2.8e−60 (c = 3 … 20) |
| H | same ratio for DH toward the crossing | 11.4, 14.1, 18.4, 13.5, 17.8 at c = 13, 20, 25, 29, 30 (N = 60); ζ 20.3, 20.7, 18.3 at c = 25, 29, 31 (N = 32). **This sampling stops short of DH's crossing at N = 60** (c*(64) = 30.818, so c*(60) is above 30.8); the matched-N reading is in §5 |
| I | Poincaré attempt (§6) | comparison bound 0.579 / 0.443 against required gap 5.850 / 8.782 at c = 13 / 31; true gap equals the requirement to 6.0e−38 / 7.4e−64 relative; 2⟨c,e₂⟩² = 4.4e−63 / 4.2e−113; Weil ground state overlaps 0.52 / 0.43 with e₁ and 0.60 / 0.60 with e₂ |

## 4. Candidate propagation lemmas

### C1. Boundary-arithmetic propagation: **refuted**

*Statement (as a class).* If Q_D ≥ 0 on a window of length ℓ, and the
atoms of D with log n ∈ [ℓ, ℓ') satisfy a local condition 𝒫 (for example:
prime powers only, weight Λ(n)n^{−1/2} ≥ 0, a local Ramanujan bound as in
`docs/24`), then Q_D ≥ 0 on the window of length ℓ'.

*Would imply.* RH by chaining from Zhu's ℓ = 1.6, provided ζ's entering
atoms satisfy 𝒫.

*Euler product enters* only through 𝒫, on the new atoms.

*DH test.* Across c = 30 → 31 no atom gains weight (§2.5), so any 𝒫 holds
vacuously. DH is positive at (30, N) for every N ≤ 128 (hardened) and
negative at (31, 60) (hardened). **Refuted at the lattice level.** The
numerics worker's bisection puts the flip strictly inside the step. Hardened
brackets from their `crossing.json` (branch `teal-sea/weil-propagation`,
commit 75865a7), positive at c_pos and negative at c_neg:

| N | c_pos | c_neg |
|---|---|---|
| 64 | 30.817383 | 30.818359 |
| 96 | 30.695312 | 30.696289 |
| 128 | 30.646484 | 30.647461 |
| 192 | 30.628906 | 30.629883 |
| 256 | 30.616211 | 30.617188 |

ζ is conclusively positive at every c_neg (ball LDLᵀ). By their nesting
argument (Fact B, ordinary), DH's continuum form is negative for every
c ≥ 30.617188.

For the continuum form, DH's floor is:

- continuous (Suzuki's Thm 1.3 argument uses only compact embedding and a
  finite prime sum, so it ports);
- positive on small windows (Bombieri Thm 12's argument ports, with the
  pole term simply absent);
- negative at log 31.

So a first crossing ℓ* ≤ log 30.617188 exists. DH has no atom with nonzero
weight in (29, 31). If ℓ* > log 29, the step from ℓ* to log 30.617188 is
atom-free, and C1 is refuted for the continuum form with no lattice caveat.
The N-ladder of c*(N) extrapolates to about 30.61 (numerics, measured),
which supports ℓ* > log 29 but does not establish it.

*Kink formula (§2.3):* for ζ, each entering atom only steepens the
decrease. **Scoped obstruction:** the Euler product cannot drive
propagation through the atoms that enter. It has to act through the
interior block and the interior-collar coupling (§2.4).

*Smallest check.* Done: checks A and B here, and the numerics worker's
`crossing.json` for the location.

*Restatement of RH?* Not applicable: refuted.

### C2. Levy-Markov + pole capacity: **strongest; survives DH; exact reduction**

*Statement.* Proposition M and its Corollary (§2.6). As a propagation
lemma: for all ℓ, (a) μ₂(Q°_{ℓ,e}) ≥ 0, which says the zeta jump process
killed outside a window of length ℓ has at most one even Dirichlet
eigenvalue below C_ℓ, and (b) Φ_ℓ ≤ 0.

*Would imply.* (a) and (b) for all ℓ ⟺ even-sector Weil positivity on all
windows. Together with the odd-sector analogue, that is RH. The
unconditional part (Proposition M) already gives a simple positive ground
state of the pole-free operator on every window, and generic simplicity of
the even Weil ground state on every window. That is half of CCM s8 step 1,
which was previously known only for small windows (Suzuki Thm 1.4) and at
support 1.6 (Zhu Thm 6.2).

*Euler product enters* as **Λ(n) ≥ 0**, the nonnegative Dirichlet
coefficients of −ζ′/ζ, which come from the Euler product with all local
parameters equal to 1. The same holds for Dedekind zeta functions, not for
Dirichlet L-functions with complex characters, so Markov structure is not
necessary for positivity. Then the pole pays for exactly one negative
Markov direction (μ₁ = −5.85 at c = 13).

*DH test.* DH violates the hypothesis on every window with c > 3, since
Λ_f(3) = −0.312: its jump measure is signed and there is no Markov
structure. It also has no pole, so its analogue of (a)+(b) is μ₁ ≥ 0,
which fails at c = 31 with exactly one negative eigenvalue. **This means DH
does not test C2 at all.** It is not a pass. C2 has so far faced no rival
that satisfies its hypotheses.

*The lab's Euler-product rival does not test it either, and shows what is
load-bearing.* W_a(s) = ζ(s+a)ζ(s−a), a = 1/4 (`zeta/epstein.py`; it
killed Euler-product positivity in `hunts/epp_herglotz/RESULTS.md`). Its
zeros are ρ ± a, so its explicit formula is ζ's applied to g·2cosh(ax):
D_{W_a}(x) = 2cosh(ax)·D_ζ(x) (derivation). Consequences:

- Its jump measure is K(|u|)cosh(au) plus atoms Λ(n)(n^a + n^{−a})n^{−1/2},
  all nonnegative, so it is Markov: (H1) and (H2) hold.
- Its pole part is 2cosh((½+a)x) + 2cosh((½−a)x), i.e. **two** positive
  pole directions in the even sector.
- All its zeros are off its critical line. It is positive on small windows
  (Bombieri Thm 12's argument goes through, since the archimedean density
  only doubles near 0). By Weil's criterion applied to W_a (a standard
  argument, not checked for W_a here), it must turn negative on some
  window.

So Markov structure plus an Euler product plus a functional equation do not
propagate positivity. C2 survives only through its **one-pole** hypothesis,
which W_a violates.

*The control that matches C2's hypotheses:* Epstein Q = (1,1,6),
discriminant −23. It has one pole, off-line zeros, a Γ(s) factor (positive
Levy density), and Λ_Q(n) ≥ 0 for n ≤ 47 (first negative at n = 48). That
is recorded earlier in `hunts/epp_herglotz/RESULTS.md` and re-measured here.
Handed to the numerics worker by the supervisor, 2026-09-23. It is decisive
only if its window form turns negative below c = 48. This tree does not
locate its first off-line zero (`hunts/gate5_p6_a/RESULTS.md`), so the
test may come back uninformative (crossing above 48). **C2 stays a
candidate until that control runs.**

If Epstein turns negative below c = 48, then "Markov + one pole + Γ-class"
does not propagate positivity, and any C2-based argument must use more of
the Euler product. Candidates: prime-power support, and the local-factor
identity (Σ_k p^{−|k|/2} δ_{k log p}) ∗ Φ_p = (1 − 1/p) δ₀ with
Φ_p = (1 + 1/p)δ₀ − p^{−1/2}(δ_{log p} + δ_{−log p}), which holds exactly
for degree-1 local factors.

*Smallest checks.*

1. Numerics (handed off): an Epstein (1,1,6) Galerkin assembly, with Γ(s) = Γ(s/2)Γ((s+1)/2)2^{s−1}/√π so the archimedean block is the sum of the a = 1/4 and a = 3/4 kernels; its floor for c ≤ 48.
2. Numerics (handed off): for ζ over c ∈ [2, 60] at converged N, μ₂(Q°_e), λ₁(Q_e), λ₂(Q_e) and Φ_ℓ. The question is whether μ₂(Q°) tracks λ₂(Q) at a fixed ratio (0.64 in both measured cells).
3. Sign-definiteness of the pole-free ground state at more cells.
4. Optional, cheap once (1) exists: W_a's window form, built from the same blocks (archimedean a' = 1/8 and 3/8, pole blocks for cosh((½ ± a)x), atoms Λ(n)(n^a + n^{−a})n^{−1/2}). It locates where two poles stop sufficing.

*Restatement of RH?* The propagation form (a)+(b) is an **exact
reformulation**, with no new estimate. What is new is the structure: a
Perron-Frobenius operator, and access to the spectral theory of killed
Levy processes (ground-state transform, Poincaré inequalities). The one
missing estimate is named: a spectral gap of the Doob-transformed killed
process of at least C_ℓ − μ₁^{Dir}(ℓ). The measured margin of that
inequality is doubly-exponentially small (3.5e−37 on a gap of 5.85 at
c = 13). So any proof of it must be structural (an identity), not
perturbative.

### C3. Local ground-state transport: **refuted at norm scale; restatement at eigenvalue scale**

*Statement (as a class).* Positivity at ℓ plus a bound on local
ground-state data at ℓ implies positivity at ℓ + δ. Examples of such
data: ‖φ_{ℓ+δ} − T_δφ_ℓ‖ ≤ ε with T_δ the dilation; the boundary-mass
ratio φ_ℓ(0)²/λ*(ℓ) ≤ R; CCM step 2's proximity ‖ξ_λ − k_λ‖ = O(λ^{−2}).

*Would imply* RH by chaining, if the data bound held uniformly.

*Euler product enters* nowhere explicitly. The CCM near-radical k_λ = E(h_λ)
uses the Dirichlet series and Poisson summation, not the Euler product.
The Mellin transform of E_a(h) is f(s)·Mh(s) for any Dirichlet series f,
so a DH analogue exists (ordinary argument, sketched; the odd Hermite data
for Γ((s+1)/2) are not worked out).

*DH test (checks F, H).*

- Across 30 → 31 (N = 60), DH's ground state moves 7.7e−3 in norm, against
  4.4e−3 for ζ.
- Yet its λ flips sign.

The norm hypothesis holds with ε ≈ 1e−2, and the conclusion fails.
**Refuted at the lattice level** for norm transport. For the boundary-mass
version, see §5: at matched N = 128 it is a reformulation of the
log-derivative of λ, not an independent datum. Quantitatively, the transported old
ground state has Rayleigh quotient 5.2e−5 (DH) and 6.8e−8 (ζ) at the new
window, 10²³ and 10⁶¹ times λ. A transport statement that carries
positivity must be accurate to about √λ in norm (1e−14 for DH, 1e−34 for
ζ), and at that accuracy it is a restatement of positivity.

The lab record agrees: at (31, 60) the sign is carried by a beam component
of coefficient mass 7.8e−29 (weil_trunc RESULTS s8.3 item 3). So CCM's
O(λ^{−2}) prolate proximity cannot fix a sign by proximity. It is
aimed at zero convergence via Hurwitz, a different route.

By CvS applied to DH (no arithmetic needed), DH's simple-even ground
states have transforms with only real zeros at every c. Since DH has
off-line zeros, the DH analogue of CCM step 2 must fail as c grows (Hurwitz).

*Smallest check.* Count the real zeros of DH's ground-state transform F_v
in the on-line gap (83.109, 87.647) around the off-line ordinate 85.699,
at c = 29, 30, 31, 47 (band edge above 88 needs N ≥ 48 at c = 31). DH has
no on-line zero there. A real zero of F_v inside the gap is a ghost forced
by CvS reality, and its first appearance against c* tells whether the zero
route "sees" the off-line zero before, at, or after the sign flip.

*Restatement of RH?* At norm scale: refuted. At eigenvalue scale: yes, a
reformulation with no new estimate.

## 5. Does the Euler product bound the boundary trace? (the numerics worker's question)

The numerics worker measures an edge law dλ/dL = −κμ₀², with μ₀ = Σu_k the
band-N edge amplitude (so φ_N(0)² = μ₀²/L) and κ ≈ 1.0 … 1.3. It holds
through DH's crossing, with κμ₀² N-stable and κ alone not
(numerics RESULTS s4 row 7, s5). They ask whether the Euler product, via
the Markov structure of §2.6, bounds μ₀² ≲ λ/(κδ).

*Matched-N data* (their `grid_*_N128.json` on branch
`teal-sea/weil-propagation`, commit 75865a7; λ₁ and μ₀ as stored; the
ratio is my arithmetic on their numbers):

| c | 29 | 30 | 30.5 | 30.625 | 30.6875 | 31.5 |
|---|---|---|---|---|---|---|
| DH μ₀²/λ | 39 | 72 | 226 | 1210 | λ < 0 | λ < 0 |
| ζ μ₀²/λ | 166 | 193 | 186 | 190 | 193 | 180 |

Readings:

1. With the edge law, μ₀²/λ = −(1/κ) d ln λ/dL. The ratio *is* the
   relative decay rate of λ. A bound μ₀² ≤ Rλ is the log-derivative bound
   that the numerics worker's candidate 6 already tested, and it is
   equivalent to a lower bound on λ. **Reformulation, not an estimate**
   (ordinary argument given the measured edge law).
2. DH's ratio sits **below** ζ's until c ≈ 30.4: 101 at c = 30.25 (their
   s3.3 table) against ζ's ≈ 190, and 226 at c = 30.5. It then diverges
   within the last ΔL ≈ 0.013 before the crossing. So it gives no usable early warning, and
   no threshold R separates ζ from DH ahead of time (measured). My
   N = 60 reading in check H ("no precursor at c ≤ 30") was correct but
   stopped short of c*(60).
3. **Does Λ ≥ 0 bound it? No, not by itself.** W_a has Λ ≥ 0, an Euler
   product and the functional equation, and it must cross somewhere (§4
   C2). At a transversal crossing (μ₀ ≠ 0 where λ = 0, as the numerics
   worker observes for DH) the ratio diverges. So the Markov structure
   cannot bound μ₀²/λ unless the one-pole structure is used. Grade:
   ordinary argument, conditional on Weil's criterion for W_a and on
   transversality. DH lies outside the hypothesis (signed jumps).
   Epstein (1,1,6) is the pending control.
4. What the Markov structure *does* control: the pole-free ground state
   φ°, which is positive and flat (min/max 0.71 … 0.80, max φ°² ≈ 1.2 …
   1.4 × 1/ℓ). The Weil ground state is instead the resolvent
   (A° − λ)^{−1} c at a spectral parameter inside the doubly-exponentially
   thin gap (μ₁, μ₂). Its boundary trace relative to λ is set by the
   secular balance (b), not by Markovianity (derivation).

## 6. The Poincaré attempt for condition (a) (about one hour, supervisor-allocated)

*Ground-state representation (exact, ordinary argument).* Write
𝓔(f) = ½∬ j(y−z)(f(y)−f(z))² dy dz + ∫ κ f², and let φ° > 0 be the
Perron-Frobenius ground state, 𝓔(φ°, ·) = m₁⟨φ°, ·⟩ with
m₁ = μ₁ + C_ℓ. For f = φ°u the cross terms telescope:

    𝓔(φ°u) − m₁‖φ°u‖² = ½ ∬ j(y−z) φ°(y) φ°(z) (u(y) − u(z))² dy dz.

Expand (φ°(y)u(y) − φ°(z)u(z))² = φ°(y)φ°(z)(u(y)−u(z))² +
(φ°(y) − φ°(z))(φ°(y)u(y)² − φ°(z)u(z)²); the second group is
𝓔(φ°, φ°u²) = m₁‖φ°u‖². So μ₂ − μ₁ is the spectral gap of the Doob-
transformed process (kernel j φ°φ°, reference measure π = φ°² dy), and

    (a)  ⟺  gap_e(ℓ) ≥ D_ℓ := −μ₁(Q°)     (Poincaré inequality for the conditioned process).

*The simplest comparison bound (computed, check I).* Var_π(u) =
½∬φ°²(y)φ°²(z)(u(y)−u(z))² (π normalised). Discarding the atoms, which is
legitimate since they are nonnegative jumps, gives

    gap ≥ inf_{y,z} j(y−z)/(φ°(y)φ°(z)) ≥ (K(ℓ)/2) / max φ°².

| c, N | required D_ℓ | comparison bound | true gap μ₂ − μ₁ | relative margin of (a) |
|---|---|---|---|---|
| 13, 24 | 5.8497 | 0.579 | 5.8497 (+3.5e−37) | 6.0e−38 |
| 31, 32 | 8.7819 | 0.443 | 8.7819 (+6.5e−63) | 7.4e−64 |

The comparison bound is short by factors of 10 and 20. More to the point,
the true gap exceeds the requirement by a relative 6e−38 and 7e−64.
**Scoped obstruction (measured, restricted class):** any Poincaré or
comparison inequality whose ratio to the true gap is bounded away from 1
by more than about 1e−37 (c = 13) cannot establish (a). Condition (a) is
saturated to the eigenvalue scale, so it can only come from an identity
that exhibits the saturating direction, not from an inequality with slack.

*The saturating direction (measured, check I).* The Poincaré extremal is
e₂, the second pole-free eigenvector. It is orthogonal to the pole vector
to 2⟨c, e₂⟩² = 4.4e−63 (c = 13) and 4.2e−113 (c = 31). That is exactly
what a CCM near-radical vector must satisfy. k_λ = E(h_λ) with ∫h = 0
(Riemann's vanishing-integral condition, CCM s7 Lemma 7.1) has transform
nearly vanishing at ±i/2, i.e. ⟨k_λ, c⟩ ≈ 0, and Q(k_λ) ≈ 0 (CCM s8
item 2; Connes 2602.04022 s6.4). The first pole-free eigenvector carries
the pole almost entirely: 2⟨c, e₁⟩² = 5.883 against μ₁ = −5.850, so
Q(e₁) = +0.033 (c = 13). The Weil ground state mixes the two (overlaps
0.52 with e₁, 0.60 with e₂).

*Status (ALIGNMENT s5).*

- **Attempt unresolved:** (a) was not established.
- **Restricted class obstructed (measured, not proved):** non-sharp
  comparison or Poincaré bounds.
- **Paused by allocation** after the allotted hour.
- **Reduction obtained:** (a) holds iff the near-null directions of Q°
  orthogonal to φ° have nonnegative energy. If e₂ is a CCM near-radical
  vector (measured orthogonality supports it; not proved), then (a) is
  CCM's missing step 2 at the eigenvalue scale, the same place the
  Connes program is stuck.

This identification is itself a finding. C2's condition (a) and CCM's
step 2 are the same obstacle seen from two sides (derivation plus
measurement, not a theorem).

## 7. Threads (observations, not pursued)

- **Boundary mass.** At fixed N the ratio φ_N(0)²/λ_N stays within 11-24
  for ζ over λ from 1e−8 to 1e−60 (check G). §5 shows it is the log-rate
  of λ. A Hadamard-type domain derivative for the Weil operator, whose
  principal part is half the logarithmic Laplacian (Suzuki (4.6)), would
  explain why κμ₀² is N-stable while κ and μ₀ are not. The continuum
  trace should be a log-weighted boundary quantity. Not derived here, and
  no log-Laplacian source was read.
- **Krein-Langer continuation.** Suzuki identifies g_ζ as a screw function
  exactly under RH. Window positivity is then the Krein-Langer continuation
  problem from an interval, whose continuous Schur-parameter description is
  the natural home for any propagation law. Not worked out here.
- **Bombieri's window-independent inertia (Thm 8)** in finite zero models,
  and the fake-zero critical window (§13), are the closest existing results
  to "the ground state at ℓ vs ℓ + δ". The DH lattice curve first_neg_N(c)
  in weil_trunc s8.2 is a measured instance of §13's t_c.
- **Yoshida 1992 unread.** The primary text should be read before any
  claim that leans on the exact form of his result.

## 8. Grading summary

- Proposition M, its Corollary, and the collar criterion: ordinary
  arguments, unreviewed. They rely on standard theorems: Beurling-Deny,
  positivity-improving semigroups of irreducible Dirichlet forms,
  rank-one interlacing.
- Kink formula at finite N: ordinary argument plus a measured agreement to
  1e−7 or better. The continuum version is a derivation under stated
  assumptions (simple ground state, continuity at the edges).
- DH arithmetic (Λ_f(5m) = 0, Λ_f(31) = log 31, zero edge weight): exact,
  numerically confirmed.
- All eigenvalue data in §2.6 and §3: measured at float grade, except the
  DH signs at c = 30, 31, which are hardened (lab record).
- C1 refuted at every N = 64 … 256 (hardened inputs, the numerics
  worker's brackets); continuum refutation conditional on ℓ* > log 29.
- C2 open: an exact reformulation plus an unconditional structural result
  (ordinary argument, unreviewed). It has faced no rival satisfying its
  hypotheses; the Epstein control is pending.
- C3 refuted at norm scale (measured inputs). The boundary-mass variant is
  a reformulation (§5).
- §6: the ground-state representation is an ordinary argument. The
  comparison-bound shortfall and the orthogonality 2⟨c, e₂⟩² ≈ 1e−63 are
  measured (float, dps 60 and 110, N = 24 and 32). The identification of
  e₂ with a CCM near-radical vector is a hypothesis supported by that
  measurement, not a theorem.
- Originality: the Levy-Markov decomposition of the full Weil form and the
  kink formula were produced here. Novelty was searched only in the 10
  sources above plus one web search, which found no match.

## 9. Reproduction

    .venv/bin/python hunts/weil_propagation/theory/checks.py    # about 2 min, writes checks.json

Epstein coefficient signs: a 10-line loop over
`zeta.epstein.epstein_representation_count(n, (1,1,6))` with the
log-derivative recursion of `galerkin.dh_lambda_coeffs`; not saved as a
script.
