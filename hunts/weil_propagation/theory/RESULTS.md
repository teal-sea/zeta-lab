# RESULTS: theory worker, Weil positivity propagation across window size

1. **Strongest candidate (C2, Levy-Markov + pole):** with its pole term removed, the zeta Weil form on any window is exactly the Dirichlet form of a symmetric jump process (digamma Levy density plus jumps of size ±log n at rate Λ(n)/√n) killed outside the window, minus the constant C_ℓ = log π − ψ(1/4) + Σ_{log n<ℓ} 2Λ(n)/√n (the last sum being the whole ℓ-dependence of C_ℓ as ℓ → ∞). Λ ≥ 0 makes it Markov, so its ground state is simple and positive on every window.
2. **What it would give:** unconditionally, a simple even-sector Weil ground state on every window (outside one nongeneric coincidence), which is half of the first missing step in the Connes-Consani-Moscovici program. Propagation becomes two conditions: (a) the killed process has at most one even Dirichlet eigenvalue below C_ℓ; (b) a scalar pole-capacity inequality. Measured, (b) is about 1e6 tighter than (a). Both are exact reformulations, and (a)'s margin is also doubly-exponentially small, so the reduction is not yet a proof route.
3. **What refutes it:** DH cannot: Λ_f(3) = −0.312 < 0 makes its jump measure signed, and DH has no pole. The live rival is Epstein (1,1,6). It has a pole, off-line zeros and Λ_Q ≥ 0 for every n ≤ 47. If its window form goes negative below c = 48, every mechanism that uses only "Markov + one pole" is refuted. Separately, C1 (propagation driven by the atoms that enter) is refuted by DH: the 30→31 step adds no arithmetic at all (Λ_f(30) = 0, and atom 31 has zero weight at c = 31), yet the sign flips. C3 (local ground-state transport) is also refuted by DH.
4. **New or known:** the Markov reading of the full Weil form, primes included, and the prime-entry kink formula are original to this session. They were not in the 10 sources read, and one web search found nothing. Suzuki (arXiv:2606.09096 s5) uses a Dirichlet form for the archimedean part only, and only for small windows. The fixed-window dilation formula is Suzuki's s4.2. Novelty is not established: the search was shallow.
5. **Next step:** the numerics worker computes the Epstein (1,1,6) window floor for c ≤ 48, and tracks μ₂ of the pole-free zeta form against λ₁, λ₂ of the full form over c ∈ [2, 60]. On the theory side, try a spectral-gap (Poincaré) bound for the Doob-transformed killed process, which is the single estimate C2 is missing.

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
50-80% to the slope in these cells. An entering prime never helps
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

**Proposition M (ordinary argument, unreviewed).** Take ζ and any window I,
and let Q° = Q − P (pole removed). Then 𝓔 is an irreducible Dirichlet form
on L²(I): a pure jump form, with killing from jumps that leave I. It is
Markov because the jump measure (½K(|u|)du plus atoms Λ(n)n^{−1/2} at
u = ±log n) is nonnegative, which is exactly **Λ(n) ≥ 0**. It is
irreducible because K > 0. Q° = 𝓔 − C_ℓ has discrete spectrum, since P is
bounded rank-2 on L²(I) (CCM Thm 3.6). Consequences:

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
- **Simplicity:** λ₁(Q_e) is simple whenever ⟨c, e₂⟩ ≠ 0, and otherwise
  unless one exact coincidence occurs. This holds on every window,
  unconditionally.
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
| H | same ratio for DH toward the crossing | 11.4, 14.1, 18.4, 13.5, 17.8 at c = 13, 20, 25, 29, 30; ζ 20.3, 20.7, 18.3 at c = 25, 29, 31 |

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
negative at (31, 60) (hardened). **Refuted at the lattice level.**

For the continuum form, DH's floor is:

- continuous (Suzuki's Thm 1.3 argument uses only compact embedding and a
  finite prime sum, so it ports);
- positive on small windows (Bombieri Thm 12's argument ports, with the
  pole term simply absent);
- negative at log 31.

So a first crossing ℓ* ≤ log 31 exists. Unless ℓ* is exactly log n for a
DH atom n, a neighbourhood of ℓ* is atom-free and refutes C1 without any
lattice caveat. The lattice data (positive through N = 256 at c = 29 and
30) put ℓ* in (log 30, log 31]. That is consistent, not established.

*Kink formula (§2.3):* for ζ, each entering atom only steepens the
decrease. **Scoped obstruction:** the Euler product cannot drive
propagation through the atoms that enter. It has to act through the
interior block and the interior-collar coupling (§2.4).

*Smallest check.* Already done here (checks A, B). For the numerics
worker: λ_60(c) on a fine grid c ∈ [30, 31] locates the lattice crossing
inside the atom-free step.

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
which fails at c = 31 with exactly one negative eigenvalue. **Not refuted
by DH.**

*Second rival, required before anything is built on C2.* Epstein
Q = (1,1,6), discriminant −23. It has a pole, off-line zeros, and
Λ_Q(n) ≥ 0 for every n ≤ 47 (first negative at n = 48; measured here from
`zeta.epstein.epstein_representation_count`). Its Γ(s) factor also gives
a positive Levy density. If its window form goes negative at some c < 48,
then "Markov + one pole + Γ-class" does not propagate positivity, and any
C2-based argument must use more of the Euler product (prime-power support,
the local-factor identity (Σ_k p^{−|k|/2} δ_{k log p}) ∗ Φ_p = (1 − 1/p) δ₀).

*Smallest checks.*

1. Numerics: an Epstein (1,1,6) Galerkin assembly, with Γ(s) = Γ(s/2)Γ((s+1)/2)2^{s−1}/√π so the archimedean block is the sum of the a = 1/4 and a = 3/4 kernels; its floor for c ≤ 48.
2. For ζ over c ∈ [2, 60] at converged N: μ₂(Q°_e), λ₁(Q_e), λ₂(Q_e) and Φ_ℓ. The question is whether μ₂(Q°) tracks λ₂(Q) at a fixed ratio (0.64 in both measured cells).
3. Sign-definiteness of the pole-free ground state at more cells.

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
- Its boundary ratio is 17.8 at c = 30, against about 20 for ζ, and it
  shows no precursor at c = 13 … 30.
- Yet its λ flips sign.

The hypothesis holds with ε ≈ 1e−2 and R ≈ 20, and the conclusion fails.
**Refuted at the lattice level.** Quantitatively, the transported old
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

## 5. Threads (observations, not pursued)

- **Boundary mass.** φ_N(0)²/λ_N stays within 11-24 for both ζ and DH
  while λ spans 52 orders of magnitude (checks G, H). The one-mode test of
  §2.4 would explain an O(√λ) boundary value heuristically. The ratio is
  Euler-product-blind and gives no warning of the DH crossing. There may
  be a Hadamard-type identity dλ/dℓ ≈ −κ φ(0)φ(ℓ) (measured
  κ ≈ 1.6 … 2.4 at N = 16). No exact identity was found: the archimedean
  kernel is not local.
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

## 6. Grading summary

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
- C1 refuted at the lattice level (hardened inputs); continuum refutation
  conditional as stated. C2 open, exact reformulation plus an
  unconditional structural result. C3 refuted at norm scale (measured
  inputs).
- Originality: the Levy-Markov decomposition of the full Weil form and the
  kink formula were produced here. Novelty was searched only in the 10
  sources above plus one web search, which found no match.

## 7. Reproduction

    .venv/bin/python hunts/weil_propagation/theory/checks.py    # about 2 min, writes checks.json

Epstein coefficient signs: a 10-line loop over
`zeta.epstein.epstein_representation_count(n, (1,1,6))` with the
log-derivative recursion of `galerkin.dh_lambda_coeffs`; not saved as a
script.
