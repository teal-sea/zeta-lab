1. **Built: the exact place-2 analysis, the refusal gate, P_2 through E_S as closed-form matrix entries on the shared basis, and the T_S assembly on the module form (Π_S = orthogonal projection onto Θ·range S_∞, CCM arXiv:2310.18423 Thm 4.6). T_S itself was not evaluated on any cell: kernel/'s S_∞ was not routed within the box.** `T_S_matrix` refuses W_a and the Epstein (1,1,6) tower (exact), stops on Γ_C with a stated reason, and raises `KernelUnavailable` for ζ instead of returning a number.
2. **Key identity: on 2 < c < 4 the Weil prime block is −Wp = log 2 · (Gram(θ_S) − 3/2·I) (exact algebra; hardened: the closed form agrees with the independent `weil_trunc/galerkin.py` block to 4.5e−40 at dps 40 on every mission cell).** The Gram spectrum of θ_S fills [3/2 − 1/√2, 3/2 + 1/√2] (Cauchy-Schwarz bound; the ends are reached to 1e−18 at N = 32 for c = 2.5 and 2.9, measured). First derived and pinned here (f1e912d); cutoff/ rechecked it by direct quadrature as a third route (its commit e678d94).
3. **New structural fact: the semilocal time-frequency operator P F_S P is not Hilbert-Schmidt.** Its HS² over Euler levels j ≤ K is K/2 + 1.07079 (closed form in Si; the partial sums are measured to 4e−9 at K = 40, dps 30), against 2.23748 for the archimedean P P̂ P. So ΔT = T_S − T_∞ needs Sonin data across the whole Mellin band of the window basis, not the first few prolates. Grade: ordinary argument (unreviewed) plus measured partial sums.
4. **Rechecked and refuted: theory §7.3 item 2 (exact). Time and frequency limiting to Z_2 are different projections; they commute and their product has rank one. The literal Π_S = S_∞ ⊗ P_2 + 1 ⊗ (1 − P_2) has infinite trace on X_S (ordinary argument).** Positive control: Γ_C data (Dedekind ζ_{Q(√−23)}) cannot be realized over Q with S = {∞, 2}: no idele class character of C_S is odd at ∞ and unramified at 2. Not exercised (ordinary argument).
5. **ALIGNMENT s5: §7.3 item 2 refuted (exact); the product-ball Π_S obstructed (infinite trace). T_S on the module form is unresolved: the construction is fixed and implemented up to kernel/'s data, and its evaluation is paused at the box.** Open: ΔT and R_S on the cells, which needs ξ_n up to the Mellin band (INTERFACE.md, "consumed").

# RESULTS: two_adic/, gap (b), P_2 through E_S and the assembly of T_S

Worker `two_adic/`, 2026-09-23, branch `teal-sea/weil-c4-s2`, time box
21:10 to 00:10. Nothing here is a claim about RH. Positivity on c ∈ [2, 3)
is already known (Zhu arXiv:2608.24827); this folder builds the 2-adic half
of the C4 trace term. Grades follow the `AGENTS.md` ladder. No
kernel-checked statement is made (AXLE not attempted: nothing here reduced
to a lemma small enough to be worth it within the box). Every number below is
pinned by a test in this folder; raw values are in `ta_es_cells.json` and
`ta_ts_cells.json`. The rejected cabinet attempt (`req-c4-s2-remainder/a1`)
was read and not reused: its split of Q is superseded by §3's closed form.

## 0. Sources and conventions

- Connes arXiv:math/9811068 §VII: X_S = A_S/O_S^*, eq. (5) (the Hilbert space
  as the completion of S(A_S) under the Γ-periodized norm), (7) (scaling),
  (12)-(13) (cutoffs by the module), Theorem 4 (semilocal trace formula),
  (17) (trace on X_S as a sum over S-units).
- Connes-Consani arXiv:2006.13771: Sonin space S(1,1), Prop 4.5 and eq. (81)
  (S_∞ = 1 − Σ_n(|ξ_n⟩⟨ξ_n| + |ζ_n⟩⟨ζ_n|)), Theorems 4.7 and 6.11.
- Connes arXiv:2602.04022 §7.2-7.4, eq. (22) and its footnote 11 (the
  projections P^S_T, P̂^S_W are defined with the module).
- **Connes-Consani-Moscovici arXiv:2310.18423 §4** (not in the brief; found
  while fixing the objects, cited as [29] in 2602.04022): the unitary
  w_S : L²(X_S)^{K_S} → L²(ℝ_+^*, d^*u) (eq. (42)); E_S = η_S, the class of
  1_{Z_2} ⊗ f (eqs. (44)-(47)); the local Sonin space at p (Def 4.4, Prop
  4.5); θ_S, the class of σ_2 ⊗ f (Prop 4.6, eqs. (57)-(58)); F_S ∘ θ_S =
  θ_S ∘ F (Prop 4.7); and **Thm 4.6: θ_S maps S_λ(ℝ) onto the semilocal
  Sonin space S_λ(X_S), boundedly with bounded inverse.**

S = {∞, 2}, Γ_S = {±2^n}, C_S = (ℝ^* × Q_2^*)/Γ_S, module |x|_S =
|x_∞||x_2|_2, K_S = its kernel ≅ Z_2^*. In the log variable x = log u of
L²(ℝ_+^*, d^*u), scaling is translation, D := translation by log 2 (CCM's
g(λ) ↦ g(λ/2)), and P := time limiting to u ≤ 1 (the module ball; on this
sector it is the archimedean interval cutoff).

## 1. Task 1: the objects, and the recheck of theory §7.3 item 2

At the place 2 alone (`ta_local.py`, exact rational arithmetic on the
Z_2^*-invariant sector, ball basis B_r = 1_{|x|_2 ≤ 2^r}, F(B_r) = 2^r B_{−r}):

| statement | value |
|---|---|
| F unitary, F² = 1, F(1_{Z_2}) = 1_{Z_2}, F(σ_2) = σ_2, F(ε_0) ≠ ε_0 | all true |
| P_2 := multiply by 1_{Z_2}, P̂_2 := F P_2 F: both orthogonal projections | true |
| P_2 = P̂_2 | **false** |
| P_2 P̂_2 = P̂_2 P_2 = rank one projection onto 1_{Z_2} | true |
| P_2 ∨ P̂_2 = 1 (closed ball \|x\|_2 ≤ 1) | true: local Sonin space dim **0** |
| open ball \|x\|_2 < 1 (CCM Def 4.4) | local Sonin space dim **1**, spanned by σ_2 = ε_0 − ε_1/2 |
| ‖σ_2‖², ‖1_{Z_2}‖² | 3/4, 1 |

Pinned by `test_ta_local_and_data.py` for truncations K = 3, 5, 6, 8 (the
span V_K of the balls is invariant under P_2, P̂_2 and F, so the kernels are
not truncation artefacts). **Grade: exact.** Theory §7.3 item 2 ("1_{Z_p} is
its own Fourier transform, so time and frequency limiting to Z_p are the
same projection") is **refuted**: self-duality is a statement about one
vector. What is true is that the two projections commute and meet in that
vector, so the p-adic uncertainty is exact with a one-dimensional joint range.

## 2. The product-ball obstruction (graded result on its own)

Ordinary argument, unreviewed. cutoff/ reached the same conclusions in its
milestone 1 (its RESULTS lines 1 and 4):

1. The product ball B = [−λ, λ] × Z_2 is not Γ_S-invariant (2B ≠ B), so
   multiplication by 1_B is not an operator on L²(X_S), where eq. (22) and
   the prime term live (Connes (17): the trace on X_S is a sum over S-units).
2. Pushed through the periodization J = E_S (Connes (5)), the ranges of the
   product-ball time and frequency limits become the module ranges: every
   f supported in B has J f supported in |x|_S ≤ λ, and every function on
   {|x|_S ≤ λ} is J of its restriction to the shell |x_2|_2 = 1 times
   1_{|x_∞| ≤ λ}. F commutes with J (Connes Lemma 1(b)), so the same holds
   for the frequency side.
3. The summand 1 ⊗ (1 − P_2) is pushed onto all of L²(X_S) (every Γ_S-orbit
   meets the shell |x_2|_2 = 2), so the literal Π_S of theory §7.3 has
   trace +∞ against ϑ(g)ϑ(g)^*. The brief's "start with the 1 ⊗ (1 − P_2)
   piece" therefore has no finite matrix entries to deliver.
4. The finite, positive, E_S-compatible object is the one CCM Thm 4.6
   supplies: the semilocal Sonin space is θ_S(S_λ(ℝ)), i.e. S_∞ tensored
   with the open-ball 2-adic Sonin vector σ_2 and periodized. This is the
   T_S built below (coordinator decision on milestone 1).

## 3. Task 2: P_2 through E_S on the shared basis (closed form)

In the w_S picture θ_S = Θ_α := 1 − α 2^{−1/2} D (Mellin multiplier
1 − α 2^{−1/2−is}, CCM (57)-(58)) and E_S = Σ_{k≥0} (ᾱ 2^{−1/2})^k D^{−k}
(multiplier L_2(1/2 − is), CCM (47)). On a window of length L,
⟨f, D^k f⟩ = 0 once k log 2 ≥ L, so for 2 < c < 4 every Gram form of θ_S or
E_S on window functions is built from one matrix,

    C_{mn} = ⟨U_m, D U_n⟩ = e^{−2πinh/L} (1 − e^{2πi(n−m)h/L}) / (2πi(n−m)),   m ≠ n,
    C_{nn} = e^{−2πinh/L} (L − h)/L,                                           h = log 2,

and:

- Gram(Θ_α) = (1 + |α|²/2) I − 2^{−1/2}(α C + ᾱ C*);
- Gram(E_S) = 2 I + √2 (ᾱ C + α C*) for |α| = 1;
- the CCM prime block of the atom n = 2 is Wp = (log 2/√2)(C + C*);
- hence **−Wp_α = log 2 · (Σ_j Gram(Θ_{α_j}) − Σ_j (1 + |α_j|²/2) I)**, and for
  ζ, **−Wp = log 2 · (Gram(θ_S) − 3/2 I)**.

The 2-adic atom of the Weil form on these windows is the failure of the
Sonin map θ_S to be a multiple of an isometry on window functions. The
orientation for complex α is fixed by matching Θ_α's multiplier; no mission
cell uses complex α.

Checks (`test_ta_es.py`, dps 40; tolerance = measured deviation rounded up):

| check | measured max deviation | test tolerance |
|---|---|---|
| closed form C against direct quadrature (dps 50), 25 entries per cell | 2.1e−42 | 1e−39 |
| Wp from C against `galerkin.py`'s prime block (independent code) | 4.5e−40 | 5e−39 |
| identity −Wp_α = log 2 (Gram − shift), α ∈ {(1), (1,1), (−1), (i)} | 1.2e−41 | 1e−39 |
| Gram(E_S) closed form against its operator series (140 terms), α ∈ {1, −1, i} | 4.6e−41 | 5e−39 |

**Grade: the identity is exact algebra from the closed form; the closed
form is hardened (quadrature and an independent implementation agree to
working precision).**

Mission cells (`ta_es_cells.json`, dps 40, runtime 13 s for all nine):

| c | N | Gram(θ_S) min | Gram(θ_S) max | Wp min | Wp max |
|---|---|---|---|---|---|
| 2.2 | 8 | 0.80547231866512626 | 2.19834594065960534 | −0.48405651982368832 | 0.48140990413810388 |
| 2.2 | 16 | 0.79293162516069561 | 2.20708619002499827 | −0.49011479902870128 | 0.49010245048296641 |
| 2.2 | 32 | 0.79289321910867856 | 2.20710678105946315 | −0.49012907164618542 | 0.49012907152963847 |
| 2.5 | 8 | 0.79290766300001662 | 2.20708688175546311 | −0.49011527849972269 | 0.49011905978708118 |
| 2.5 | 16 | 0.79289321890453224 | 2.20710678106376477 | −0.49012907164916708 | 0.49012907167114192 |
| 2.5 | 32 | 0.79289321881345248 | 2.20710678118654752 | −0.49012907173427360 | 0.49012907173427360 |
| 2.9 | 8 | 0.79289323304064058 | 2.20710673297045489 | −0.49012903831342493 | 0.49012906187273828 |
| 2.9 | 16 | 0.79289321881345310 | 2.20710678118654718 | −0.49012907173427336 | 0.49012907173427316 |
| 2.9 | 32 | 0.79289321881345248 | 2.20710678118654752 | −0.49012907173427360 | 0.49012907173427360 |

The band is [3/2 − 1/√2, 3/2 + 1/√2] = [0.79289321881345248, 2.20710678118654752]:
window and shifted window overlap in less than half when c < 4, so
|Re⟨f, Df⟩| ≤ ‖f‖²/2 (Cauchy-Schwarz; ordinary argument). Every cell lies in
it; at N = 32 the ends are on it to 1e−18 (c = 2.5, 2.9) and 3e−10 (c = 2.2).
Correspondingly Wp's spectrum fills [−log 2/√2, log 2/√2] = ±0.49012907173.
**Grade: measured spectra (mpmath eigsy at dps 40) of hardened matrices.**

## 4. Kill-control 2: the refusal gate (`ta_data.py`)

Local data at 2 enter as Satake parameters or as a tower s_k(2) =
Λ(2^k)/log 2 with degree d. The gate checks |s_k| ≤ d, recovers the α_j
by Newton's identities, checks |α_j| = 1, and requires the α_j to reproduce
every given s_k. Exact arithmetic (sympy); float inputs need an explicit
tolerance, which is recorded.

| data at 2 | outcome |
|---|---|
| ζ, α = (1) | accepted |
| Dedekind ζ_{Q(√−23)}, α = (1, 1); also its tower s_k = 2 (k ≤ 7, numerics `us_check.json`) | accepted, α = (1, 1) |
| W_a, a = 1/4: α = 2^{±1/4} | **refused** (\|α\| ≠ 1); its tower refused at k = 1 (s_1 = 2^{1/4} + 2^{−1/4} = 2.030103 > 2; theory §7.1 prints 2.0303, a slip in the fourth digit that changes nothing) |
| Epstein (1,1,6) tower (0, 2, 6, 2, 0, 2, 0) | **refused** at k = 3 (\|s_3\| = 6 > 2, n = 8) |
| Epstein's s_1, s_2 alone | accepted as α = (1, −1): the window c < 4 sees only s_1, so detecting Epstein needs the tower beyond the window, as the mission says |
| synthetic tower (0, 2, 1), d = 2 | refused: not a power-sum tower |

`T_S_matrix` runs the gate before anything else, so no code path returns a
trace term for W_a or Epstein data (`test_ta_ts.py`). **Grade: exact.**
Why the gate is a correctness condition and not a guard: T_S uses the local
data only through Θ_α, and the trace term is a diagonal (nonnegative)
quantity only when α enters as a unitary twist of the scaling action; for
W_a the form is a pairing of two different vectors (theory §4, C2).

## 5. Task 3: the assembly of T_S

Definition (module/quotient form, coordinator decision): on
L²(X_S)^{K_S} = L²(ℝ_+^*, d^*u),

    T_S(g) = Tr(ϑ(g) Π_S ϑ(g)^*),   Π_S = orthogonal projection onto Θ(range S_∞),
    Θ = Π_j (1 − α_j 2^{−1/2} D) per Satake parameter (degree d: sum over j).

Derivations (ordinary arguments, unreviewed):

1. **Finite and nonnegative.** ϑ(g)Π_S = Θ·ϑ(g)S_∞·G^{−1}S_∞Θ^* with
   G = S_∞Θ^*ΘS_∞ invertible on range S_∞ (Θ is bounded with bounded
   inverse since ‖2^{−1/2}D‖ < 1). So T_S(g) is finite whenever
   T_∞(g) = ‖ϑ(g)S_∞‖²_HS is, and T_S ≥ 0 by construction.
2. **Composition with kernel/'s data.** Θ^* maps range P onto itself
   (D^{−1} moves support towards u = 0), and 1 − S_∞ = P + Q_∞ with Q_∞ the
   projection onto span{ζ_n} (CC (81)). Hence

       1 − Π_S = P + Q_S,   Q_S = projection onto span{(1 − P) Θ^{*−1} ζ_n},
       Θ^{*−1} = Σ_{k≥0} (ᾱ 2^{−1/2})^k D^{−k},
       T_S = T_∞ + ΔT,   ΔT(g) = Tr(ϑ(g)(Q_∞ − Q_S)ϑ(g)^*).

   ΔT is the whole 2-adic part of T_S; it needs P, F and Θ only, plus the
   ζ_n from kernel/.
3. **Only |Θ| matters.** Θ = W|Θ| with W unitary and both commuting with
   ϑ(g); trace is invariant under unitary conjugation, so T_{ΘV} = T_{|Θ|V}.
   T_S depends on α only through |1 − α 2^{−1/2−is}| on the critical line.
   (For complex unitary α the twisted semilocal Fourier transform was not
   rechecked here; every mission data set has real α.)
4. **Place 2 off.** α = 0 (or `local_data=None`) gives Θ = 1, Q_S = Q_∞,
   ΔT = 0, T_S = T_∞.
5. **The oblique projection carries no 2-adic content.** ΘS_∞Θ^{−1} has
   range Θ(range S_∞) and Tr(ϑ(f)ΘS_∞Θ^{−1}) = Tr(ϑ(f)S_∞): the 2-adic part
   of T_S is entirely the difference between the orthogonal and the oblique
   projection onto the same space (cutoff/ line 4 says the same).
6. **Γ_C is a framework limit.** A component of L²(X_S) with archimedean
   parity ε is an idele class character χ_∞ ⊗ χ_2 trivial on Γ_S; at −1 this
   forces (−1)^ε χ_2(−1) = 1, so an odd component is ramified at 2 and has no
   Satake parameter. L(s, χ_{−23}) (odd, unramified at 2) needs 23 ∈ S, or
   the construction over K = Q(√−23). The Dedekind positive control is
   therefore **not exercised** here (`FrameworkLimit`, message in
   `ta_ts_cells.json`).

Implementation (`ta_ts.py`): `delta_T_matrix` builds Q_∞ and Q_S from a
finite mode family on a uniform log grid with spacing log 2/m (D is an
exact grid shift) and returns ΔT with its two PSD pieces. It was exercised
on **synthetic** smooth modes only; no synthetic number is a value of T_S.
Checks (`test_ta_ts.py`, float64): α = 0 gives ΔT = 0 exactly (measured
0.0); both pieces Hermitian PSD for α ∈ {1, i, −1}; the direct trace route
agrees with an independent FFT route to 5.9e−16 relative. **The grid form
does not suit real ζ_n**: ζ_n(v) oscillates like sin(2πv)/v, which a log
grid cannot resolve beyond u of a few tens; the evaluation has to be done in
the Mellin variable (§7).

`T_S_matrix` on the mission cells (`ta_ts_cells.json`): ζ →
`awaiting_kernel`; Dedekind with Γ_C → `framework_limit`; W_a and the
Epstein tower → `refused_nonunitary`; place 2 off → `awaiting_kernel`.

## 6. The semilocal time-frequency operator is not Hilbert-Schmidt (`ta_hs.py`)

For real α (all mission data; F Θ = Θ^* F uses FD = D^{−1}F and a real),
F_S = Θ F Θ^{−1} = U_2 F, U_2 = −aD + (1 − a²) Σ_{j≥0} a^j D^{−j},
a = α/√2 (CCM Prop 4.7 (i)), P F_S P = Σ_{j≥−1} c_j A_j with A_j := P D^{−j} F P,
whose kernel is K(2^j u v), K(t) = 2 t^{1/2} cos 2πt. Exactly,

    ⟨A_j, A_l⟩_HS = 2 · 2^{(j+l)/2} [S(2π|2^j − 2^l|) + S(2π(2^j + 2^l))],   S(w) = Si(w)/w, S(0) = 1,

so the diagonal terms c_j²⟨A_j, A_j⟩ tend to 1/2 each. Measured at dps 30
(`test_ta_hs.py`):

| K (Euler levels j ≤ K) | 0 | 8 | 16 | 24 | 32 | 40 |
|---|---|---|---|---|---|---|
| ‖P F_S^{(K)} P‖²_HS | 0.405037 | 5.052145 | 9.070653 | 13.070786 | 17.070787 | 21.070787 |

The partial sums lie on K/2 + 1.0707867954 (within 2e−5, 1e−7, 4e−9 at
K = 24, 32, 40); the archimedean value (α = 0, place 2 off) is
Tr(P P̂ P) = 2 + 2 Si(4π)/(4π) = 2.23748483494183. The kernel of P F_S P is
the lacunary series Σ_j c_j K(2^j uv), whose coefficients c_j 2^{j/2} = 1/2
are not square summable, so P F_S P is bounded but not Hilbert-Schmidt and
P P̂^S P is not trace class. **Grade: closed form, ordinary argument
(unreviewed), partial sums measured.** Consequence for the mission: the
semilocal Sonin problem has no super-exponential eigenvalue decay; the 2-adic
dilation copies of the prolate problem at scales 2^j each contribute. Any
truncation of the data feeding ΔT must be by Mellin band. T_S itself stays
finite (§5, item 1).

## 7. What is open, and the next step

- **ΔT and R_S on the cells.** Recipe (derivation, not implemented): in the
  Mellin variable, ζ̂_n(s) = ∫_1^∞ ζ_n(v) v^{−1/2−is} dv follows from ξ_n on
  [0, 1] by Tate's local functional equation (M[Fξ](z) = 2Γ(z)cos(πz/2)
  (2π)^{−z} M[ξ](1 − z)) minus a finite integral over [0, 1]; the Mellin
  transform of (1 − P)Θ^{*−1}ζ_n is ζ̂_n(s)/(1 − ᾱ2^{−1/2+is}) minus
  Σ_{k≥1} (ᾱ 2^{−1/2} 2^{is})^k times the partial transforms over [1, 2^k],
  the latter from the large-v expansion of Fξ_n once 2^k is large. Then
  ΔT = ∫ (ρ_∞ − ρ_S)(s) conj(V̂_m) V̂_n ds/2π with ρ the Mellin diagonals of
  Q_∞ and Q_S. Needs kernel/'s ξ_n and λ_n up to the band (INTERFACE.md,
  "consumed"). Cost not estimated (nothing measured).
- **Whether R_S = Q − T_S has bounded rank.** With §3, Q = Q_∞ +
  log 2 (Gram(θ_S) − 3/2): C4 at S = {∞, 2} asks whether ΔT matches
  log 2 (Gram(θ_S) − 3/2) up to bounded rank. cutoff/ refuted the variant
  with T_∞ in place of T_S (its line 2), so everything rests on ΔT.
- **Positive control** needs S ∋ 23 or the construction over Q(√−23).

## 8. Grading and ALIGNMENT s5 status

| statement | grade |
|---|---|
| §1 local facts at 2; refutation of theory §7.3 item 2 | exact |
| §2 product-ball obstruction, infinite trace of the literal Π_S | ordinary argument, unreviewed (cutoff/ reached the same) |
| §3 closed form of C, Gram forms, −Wp = log 2 (Gram(θ_S) − 3/2) | exact algebra; closed form hardened (two routes) |
| §3 cell spectra, band ends reached | measured, on hardened matrices |
| §4 refusal outcomes | exact |
| §5 items 1 to 6 | ordinary arguments, unreviewed; item 6 uses only the definition of C_S |
| §5 implementation | tested on synthetic modes only; no T_S value produced |
| §6 closed form for ⟨A_j, A_l⟩_HS and the divergence | ordinary argument, unreviewed; partial sums measured |

Original to this session (novelty not searched): the identity of §3 in
matrix form (first derived here, f1e912d; cutoff/ rechecked it by a third
route, e678d94), the Hilbert-Schmidt divergence of §6, and the Γ_C
framework limit. The
objects are Connes', Connes-Consani's and Connes-Consani-Moscovici's.

ALIGNMENT s5: theory §7.3 item 2 **refuted** (exact). The product-ball Π_S
**obstructed** (infinite trace; no finite reading carries the place 2 except
the module one). T_S on the module form **unresolved**: built to the point
of kernel/'s data, evaluation **paused by allocation** at the box.

## 9. Reproduction

    PYTHONPATH=$PWD /Users/thomas/zeta-lab/.venv/bin/python hunts/weil_propagation/c4_s2/two_adic/ta_local.py
    PYTHONPATH=$PWD /Users/thomas/zeta-lab/.venv/bin/python hunts/weil_propagation/c4_s2/two_adic/ta_run_es.py   # 13 s
    PYTHONPATH=$PWD /Users/thomas/zeta-lab/.venv/bin/python hunts/weil_propagation/c4_s2/two_adic/ta_run_ts.py   # 2 s
    PYTHONPATH=$PWD /Users/thomas/zeta-lab/.venv/bin/python -m pytest -q -n 2 hunts/weil_propagation/c4_s2/two_adic tests/test_hunt_probe_discipline.py tests/test_docs_numbering.py   # about 65 s
