# Dyadic audit of the kernel-checked xi-prime development

Recorded 2026-09-12. This is the gating audit for `MISSION.md` §6, run
read-only against `anthropics/formal-math` at commit
`fbdc36bbf17d20af3fd0447c6d1a8a02773c9844` and against Wang
arXiv:2609.07918v1. It was produced by a delegated session and is kept
verbatim as evidence; the one edit is that em dashes were replaced by commas
per house style, and one line numbering artifact was left as found. No file
in this repository was changed by the audit itself. Its verdict and the
correction it makes to the brief are folded into `MISSION.md` §6 and
`RESULTS.md`.

# Gating audit: localizing the kernel-checked xi' development to short intervals (T, T + T^theta]

Date: 2026-09-12. Read-only audit.

## 0. Sources, scope, and the one framing correction

**Sources read.**

- `anthropics/formal-math`, sparse clone of `zeta23/`, commit `fbdc36bbf17d20af3fd0447c6d1a8a02773c9844` (2026-09-05). Path `zeta23/Zeta23/XiPrime/` exists (111 files, 29,749 lines); no web fallback was needed. All `file:line` references below are relative to `zeta23/`.
- Wang, arXiv:2609.07918v1, HTML version, Sections 1 to 4 read in full (the text extraction dropped inline `<` characters; the hypotheses `0 < lambda < theta < 1` and `1 <= H <= T` were checked against the mission brief and the surrounding prose).
- `hunts/short_interval/MISSION.md` sections 2, 4, 6 (and the rest for context).

**What was and was not verified.** I read every statement the headline theorem `xiDeriv_simple_on_line` depends on down to the interface propositions: the full text of `XiPrime/Final.lean`, `Statement.lean`, `Defs.lean`, `Inputs.lean`, `Assembly.lean`, `Transfer.lean`, `Transfer/Inputs.lean`, `PrimeSide/Moments.lean`, `PrimeSide/PPUpper.lean`, `ZeroCount.lean`, `ZeroCount/GenericRvM.lean`, the zeta-side `Defs.lean`, `Hypotheses.lean`, `Assembly/Inputs.lean`, `Assembly/Certificate.lean`, and the statements plus module docstrings of the other files named below. I did not re-derive the proofs of the leaf lemmas (`Tail/Count`, `Ends E1/E2`, `PrimeSideA` prop:trace, `ThmE` kernels, `Coeff/*`); their classification rests on their kernel-checked statements and the routes described in their docstrings. No `lake build` was run.

**The framing correction, stated first because the verdict depends on it.** The mission brief (§6.2) frames the route as "Wang's Theorem 2.2 delivers the arithmetic `|x|` on the narrowed band; the `-4x^2` and the series are a deterministic transfer". That is not how the kernel-checked development is built. There is no zeta pair-correlation input and no transfer from zeta zeros to xi' zeros anywhere in `Zeta23/XiPrime/`. The development treats the zeros of xi' directly: its own explicit formula (`XiEF`), its own zero count (`xiDeriv_riemannVonMangoldt`), its own strip fact (`xiDerivZerosInStrip_holds`). The form factor never appears. What appears instead is the density `D1(s) = s - 4s^2 + sum d_k s^(2k+1)` (`XiPrime/Defs.lean:161`), the diagonal mean square of the coefficient system `C(N; L_T)`, entering through one arithmetic identity, hypothesis `(H3)`. The arithmetic term `s` and the "deterministic" terms are one object there, not two.

Consequently Wang's Theorem 2.2 is the **template** for the localization, not an **input** to it. The short-interval xi' theorem needs a short-interval version of the development's own second moment (`CoeffMoments`), not Wang's zeta second moment plus a correction. Established below: every step Wang localized on the zeta side has an exact counterpart in the xi' development, localizes for the same reason, and the xi'-specific steps are either range-free or become easier in a short window.

## 0.1 The architecture in five lines

Grid: `h = 2 pi / L`, `d = floor(L T / 2 pi)`, `tau_k = T + k h`, `0 <= k < d`, filling `[T, 2T]` (`Defs.lean:212-219`). `L = lambda * l`, `l = log(T/2 pi)`, `X = e^L`.

Zero side: Gram matrix `G_kl = sum_rho m_rho phihat(gamma_rho - tau_k) phihat(gamma_rho - tau_l)` over **all** zeros (`Defs.lean:298-305`), split `G = A + E` with `A` the zeros in `I' = (T - D0, 2T + D0]`, `D0 = sqrt T` (`Defs.lean:60-67, 307-316`). Lemma R gives `4 tr Ghat - ||Ghat||_F^2 - 2 N(T,2T) - 3 NII - B(...) <= N0s(T,2T)` (`Assembly/SeamMult.lean:46-53`), `NII = N(T - D0, T) + N(2T, 2T + D0)` (`Assembly/Inputs.lean:33`).

Prime side: `XiEF` (`Statement.lean:204-208`) identifies `G` entrywise with a prime-side matrix with coefficients frozen at `L*(tau*_kl)`; `XiTraceTransfer` (`Statement.lean:217-223`) moves to fixed coefficients `C(N; L_T)`; `CoeffMoments` (`Statement.lean:236-241`) gives `tr Mhat = N(1 + o(1))`, `||Mhat||_F^2 <= (kappa + o(1)) N`, `kappa = kappaXi lambda v = 1/c_lambda(v; D1)`.

Certificate: `count_certificate` (`Assembly/Certificate.lean:39-54`), generic in the count `N`, yields `(2 - kappa - eps) N <= N0s` and `(3/2 - kappa/2 - eps) N <= N_d`. All at fixed `lambda in (0,1)` (`xiDeriv_fixedLamBounds`, `Final.lean:216`); decimals from `CertFlat`/`CertQuartic` at `lambda` near 1.

## 1. Inventory: every place the dyadic range enters

Grep: `2 \* T` occurs in 26 files under `XiPrime/` (the `Coeff/MainTerm/Asymp.lean:338` hit is a variable named `Tk`; the `Coeff` tree is otherwise range-free) and in 51 files elsewhere under `Zeta23/`. `Zeta23/WeilEF/` (14 files) has zero occurrences. Repeated bookkeeping occurrences of one use (e.g. the 50 in `Final.lean`, all the statement `Ncount T (2 * T)`) are grouped.

### 1.1 Definitions that fix the range

| # | Where | Verbatim | Role |
|---|---|---|---|
| D1 | `Zeta23/Defs.lean:63-64` | `def Iwin (T : ℝ) : Set ℝ := Icc T (2 * T)` | the window `I` |
| D2 | `Zeta23/Defs.lean:60-61, 66-67` | `def D0 (T : ℝ) : ℝ := Real.sqrt T` / `def Iprime (T : ℝ) : Set ℝ := Ioc (T - D0 T) (2 * T + D0 T)` | padded window `I'` |
| D3 | `Zeta23/Defs.lean:215-216` | `def d : ℕ := ⌊P.L T * T / (2 * Real.pi)⌋₊` | grid size, `d h ~ T` |
| D4 | `Zeta23/Defs.lean:51-52, 209-210` | `def ell1 (T : ℝ) : ℝ := l T + 2 * Real.log 2 - 1` / `def lam1 : ℝ := P.L T / ell1 T` | `ell1` is the dyadic integral of the log |
| D5 | `Zeta23/Defs.lean:307-308, 332-335` | `def ZIprime ... := Z.window (T - D0 T) (2 * T + D0 T)`, `NIprime`, `NonIprime` | zeros in `I'` |
| D6 | `Zeta23/Assembly/Inputs.lean:33` | `def NII : ℕ := Z.N (T - D0 T) T + Z.N (2 * T) (2 * T + D0 T)` | end strips |
| D7 | `Zeta23/Defs.lean:263-265` | `def calE : ℝ := P.w / P.L T + (l T ^ 2 + P.X T) * Real.log (l T) / (T * l T) + T ^ (P.lam / 2 - 1)` | zeta thm:traces error; range length `T` in the middle denominator |

### 1.2 Hypothesis and interface statements with `N(T,2T)`

| # | Where | Verbatim |
|---|---|---|
| S1 | `Zeta23/Hypotheses.lean:67-70` | `structure RiemannVonMangoldt (Z : ZeroConfig) : Prop where` / `main : ∃ C T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T → \|(Z.N T (2 * T) : ℝ) - T / (2 * Real.pi) * ell1 T\| ≤ C * Real.log T` / `local_count : ∃ A₀ : ℝ, 1 ≤ A₀ ∧ ∀ t : ℝ, (Z.N t (t + 1) : ℝ) ≤ A₀ * Real.log (\|t\| + 3)` |
| S2 | `Zeta23/Hypotheses.lean:134-138` | `int_mu : ∃ C T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T → \|(∫ τ in T..(2 * T), mu τ) - T * ell1 T / (2 * Real.pi)\| ≤ C / T`, and `int_mu_sq` with `T * ell1 T ^ 2 / (4 * Real.pi ^ 2)` |
| S3 | `XiPrime/Statement.lean:217-223` | `def XiTraceTransfer ... := (∀ δ : ℝ, 0 < δ → ∀ᶠ T in atTop, \|rtrace (...) - rtrace (...)\| ≤ δ * (Z.N T (2 * T) : ℝ)) ∧ (... ≤ (1 + δ) * frobSq (...) + δ * (Z.N T (2 * T) : ℝ))` |
| S4 | `XiPrime/Statement.lean:236-241` | `def CoeffMoments ... := (∀ δ, 0 < δ → ∀ᶠ T in atTop, (1 - δ) * (Z.N T (2 * T) : ℝ) ≤ rtrace (...) ∧ rtrace (...) ≤ (1 + δ) * (Z.N T (2 * T) : ℝ)) ∧ (... frobSq (...) ≤ (κ + δ) * (Z.N T (2 * T) : ℝ))` |
| S5 | `XiPrime/Statement.lean:246-248` | `def GzMoments` (same shape) |
| S6 | `XiPrime/Statement.lean:287-290` | `def FixedLamBounds (v : ℝ → ℝ) (lam : ℝ) : Prop := ∀ ε : ℝ, 0 < ε → ∃ T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T → (2 - kappaXi lam v - ε) * (Ncount T (2 * T) : ℝ) ≤ (N0simple T (2 * T) : ℝ) ∧ (3 / 2 - kappaXi lam v / 2 - ε) * (Ncount T (2 * T) : ℝ) ≤ (Ndist T (2 * T) : ℝ)` |
| S7 | `XiPrime/Final.lean:199-202` | `theorem xiDeriv_simple_on_line : ∃ T₀ : ℝ, ∀ T ≥ T₀, (0.85838 : ℝ) * (Ncount T (2 * T) : ℝ) ≤ (N0simple T (2 * T) : ℝ) ∧ (0.92919 : ℝ) * (Ncount T (2 * T) : ℝ) ≤ (Ndist T (2 * T) : ℝ)` |
| S8 | `XiPrime/Transfer.lean:63-67` | `def HatNegligible ... := ∀ η : ℝ, 0 < η → ∀ᶠ T in atTop, \|rtrace ((Pf T).hat T (A T))\| ≤ η * (Z.N T (2 * T) : ℝ) ∧ frobSq ((Pf T).hat T (A T)) ≤ η ^ 2 * (Z.N T (2 * T) : ℝ)` |
| S9 | `XiPrime/ZeroCount.lean:149-151` | `theorem xiDeriv_rvM_main (hF2 : XiDerivZerosInStrip) (hs : XiDerivSeam) : ∃ C T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T → \|((xiDerivZeros hF2 hs).N T (2 * T) : ℝ) - T / (2 * Real.pi) * ell1 T\| ≤ C * Real.log T` |
| S10 | `XiPrime/Hardy/Count.lean:260` | the same for `W` (Hardy `Z'` arm) |

### 1.3 Proof steps that use the range

| # | Where | What the range does there |
|---|---|---|
| P1 | `Zeta23/Assembly.lean:713-714` | `lemma eventually_N_ge ... : ∀ᶠ T in atTop, T * l T / (4 * π) ≤ (Z.N T (2 * T) : ℝ)`: the lower bound every `o(N)` comparison uses |
| P2 | `Zeta23/Assembly.lean:760-761, 780, 786` | `isLittleO_N_of_isLittleO_Tl : f =o (T * l T) → f =o (Z.N T (2*T))`; `isLittleO_log_Tl`; `isLittleO_sqrt_mul_l_Tl : (sqrt T * l T) =o (T * l T)` |
| P3 | `XiPrime/Assembly.lean:110-124` | tail package with `θ₀ T ≤ C * l T * T ^ (P.lam / 2 - 1)` |
| P4 | `XiPrime/Assembly.lean:128-136, 186-194` | `NII ≤ C * Real.sqrt T * l T`, then `hNII_o : NII =o N(T,2T)` via P2 |
| P5 | `Zeta23/Tail.lean:57` | `def theta0 (A₀ K T : ℝ) : ℝ := 4 * A₀ * K ^ 2 * Real.log (4 * T) / T` (`D₀² = T`) |
| P6 | `Zeta23/Tail/Count.lean:10-24` (docstring), `:294, :410` | `sum_{γ∉I'} m_ρ dist(γ,I)^-3 ≤ 4 A₀ log(4T)/D₀²`, zeros grouped by integer distance from the nearer endpoint of `I = [T,2T]`; `boundary_count_le` gives `NII ≤ 6 A₀ √T l` |
| P7 | `Zeta23/Tail/Grid.lean:10-15` | `sum_{k<d} \|γ − τ_k\|^-4 ≤ L D^-3` for `τ_0..τ_{d−1} ∈ [T, 2T)` |
| P8 | `Zeta23/ZeroSide.lean:804-805` | `abbrev PoissonSq : Prop := ∀ γ : ℝ, HasSum (fun k : ℤ => P.phiHatR T (γ - P.tau T k) ^ 2) (P.a T * P.L T ^ 2)`: full lattice, no truncation |
| P9 | `Zeta23/Assembly/SeamMult.lean:61-64` | `s1 ≤ N0s T (2*T) + NII`, `NIprime = N T (2*T) + NII` |
| P10 | `Zeta23/Assembly/Certificate.lean:39-54` | `count_certificate` with `hNII_o`, `hNtop`, `hBto : B → 0` |
| P11 | `XiPrime/Transfer.lean:225-227, 458-470` | `d_le : (P.d T : ℝ) ≤ P.L T * T / (2 * π)`; `d_mul_hgrid_le : (P.d T : ℝ) * P.hgrid T ≤ T`; `tau_lt_two_T : P.tau T k < 2 * T` |
| P12 | `XiPrime/Transfer.lean:472-490` | `deltaKL_mem : P.deltaKL T k l ∈ Set.Icc (0:ℝ) (1 / 2)` from `T ≤ τ* < 2T`; `deltaKL k l := Real.log (P.tauStar T k l / T) / 2` (`Transfer/Inputs.lean:33`) |
| P13 | `XiPrime/Transfer.lean:362-378` | entry-error trace: `≤ (a₀ * P.L T ^ 2)⁻¹ * ((P.L T * T / (2 * π)) * (C * T ^ (-δ) * 2)) = (C * T ^ (-δ)) * T / (π * a₀ * P.L T) ≤ ... ≤ η * (T * l T / (4 * π)) ≤ η * (Z.N T (2 * T) : ℝ)` |
| P14 | `XiPrime/Transfer.lean:380-425` | entry-error Frobenius: `(P.d T) * (8 * (1 + 1 / hgrid)) + (P.d T) ^ 2 / T ^ 2 ≤ P.L T ^ 2 * T`, then `≤ η ^ 2 * (T * l T / (4 * π)) ≤ η ^ 2 * N` |
| P15 | `XiPrime/Transfer.lean:511-531, 611-612` | `tendsto_lpow_mul_X_div : Tendsto (fun T => l T ^ n * P.X T / T) atTop (𝓝 0)` for `P.lam < 1`; used as `hsmallX : l T ^ 4 * P.X T / T ≤ ε` |
| P16 | `XiPrime/Transfer.lean:565-569` | `sumSq_le : ... ≤ A * (ρ₀ / l T) ^ (2 * r) * ((Pf T).L T ^ 4 * T * l T ^ 2) + A * ((Pf T).L T ^ 3 * l T ^ 4 * (1 + (Pf T).X T))` (main term proportional to the range length; end-effect independent of it) |
| P17 | `XiPrime/Transfer.lean:721-736` | entry-dependence trace: `≤ κtr * Real.sqrt (P.X T) ≤ κtr * Real.sqrt T ≤ ... ≤ η * (T * l T / (4 * π)) ≤ η * N` |
| P18 | `XiPrime/Transfer.lean:751-784` | entry-dependence Frobenius: `i1 : 2 * A * ρ₀ ^ 2 / a₀ ^ 2 * T ≤ η ^ 2 / (8 * π) * (T * l T)` (main, needs only `l` large); `i2 : 2 * A / a₀ ^ 2 * (l T ^ 4 * (1 + P.X T) / P.L T) ≤ η ^ 2 / (8 * π) * (T * l T)` (end effect, needs `l⁴ X / T → 0`) |
| P19 | `XiPrime/Transfer/Inputs.lean:80-88`, `PrimeSide/PPUpper.lean:56-62` | `PPUpper`: `∑ k l, GentryNu (Pc p.X e) p F k l ^ 2 ≤ C * p.L ^ 2 * (p.T * p.L * ∑ ‖e N‖ ^ 2 / N + p.L * ∑ ‖e N‖ ^ 2 + p.L * S1 e p.X ^ 2 + p.L * p.l * Real.log p.l * (p.l + S1 e p.X) ^ 2)`: `p.T` is the range length in the MV diagonal |
| P20 | `XiPrime/PrimeSide/PP.lean:149` | `(volume.restrict (Icc T (2 * T) ×ˢ Icc T (2 * T)))`: `𝓜[P_c, P_c]` over `I × I` |
| P21 | `XiPrime/PrimeSide/PP.lean:395-402` | `MV_four hMV hC X (2 * T) w φ ...` and `MV_four hMV hC X T w φ ...`: `τ`-integrals over `[T,2T]` evaluated at the endpoints, then Montgomery-Vaughan off the diagonal |
| P22 | `Zeta23/PrimeSideA/Ends.lean:114-118` (docstring 15-36) | `lem_ends_nu : ... \|(p.L)⁻¹ ^ 2 * ∑ k l, GentryNu ν p F k l ^ 2 - MtotalNu ν p F\| ≤ C * (p.L * p.l * Real.log p.l * B ^ 2)`: grid sum versus `I × I` integral; error from the grid ends |
| P23 | `XiPrime/PrimeSide/Traces.lean:44-48, 53-64` | `mainTr2Xi ... := T * P.L T / (2 * π) * (bT T * ell1 T ^ 2 + P.L T ^ 2 * JT T)`; `TracesBoundsXi` with `Ncnt = T ℓ₁/2π + O(l)` |
| P24 | `XiPrime/PrimeSide/Traces.lean:14-17, 134-139, 405-411` | remainders `prop_trace O(L√X·l)`, `lem_ends O(L·l³·log l·(1+X))`, `prop_PP O(L·l²·X)`, `cross_muP O(L·l²·√X)`, `cross_PPi O(L·X·l)`, each `o(main)` via `l T ^ 2 * P.X T / T ≤ T ^ ((P.lam - 1) / 2)` |
| P25 | `XiPrime/PrimeSide/Concrete.lean:96, 321-329` | `intMu2 := fun T => ∫ τ in T..(2 * T), Zeta23.mu τ ^ 2`, prop:mumu against it |
| P26 | `Zeta23/GammaFacts/IntMu.lean:28-30` | `integral_main_eq : ∫ τ in T..(2 * T), (1 / (2 * Real.pi)) * Real.log (τ / (2 * Real.pi)) = T * ell1 T / (2 * Real.pi)` |
| P27 | `XiPrime/ExplicitFormula/XiEFAssembly.lean:83` | `tau_mem : ∀ (P : Params) (T : ℝ), 0 < P.L T → 0 < T → ∀ k : Fin (P.d T), T ≤ P.tau T k ∧ P.tau T k ≤ 2 * T` (field of `GramBridgeFacts`) |
| P28 | `XiPrime/ExplicitFormula/TestWeight.lean:879-898, 900-917, 921-925` | `tau_mem_Icc`; `far_subset ... : {t \| 3 * ((τk + τl) / 2) / 4 ≤ \|t - (τk + τl) / 2\|} ⊆ {t \| T / 4 ≤ \|t - τk\|}`; far-region integral `≤ 16 * Real.pi * (1 + C) ^ 2 * P.X T ^ (3 / 4 : ℝ) * P.L T ^ 2 / T ^ 2` |
| P29 | `XiPrime/ExplicitFormula/GramBridge.lean:206, 233` | `T ≤ P.tau T k ∧ P.tau T k ≤ 2 * T`, same for `tauStar` |
| P30 | `XiPrime/ExplicitFormula/FamilyFacts.lean:91-98` | `pow_log_absorb`: `T ^ (3 * lam / 4) * Real.log T ^ 2 * A / (T * Real.log T) ≤ C * T ^ (-((1 - 3 * lam / 4) / 2))` and `/ T ^ 2 ≤ C * T^(-δ) / T` |
| P31 | `XiPrime/ZeroCount/GenericRvM.lean:118-126, 144-179` | `rvM_main_of`: good heights in `[T−1, T]` and `[2T, 2T+1]`, `N T₁ T₂ = N T₁ T + N T (2T) + N (2T) T₂`, unit strips by the local count |
| P32 | `XiPrime/Transfer/Dependence.lean:224-229` | `Aphi_mul_norm_tauKernel_le' ... (hy : Real.log 2 ≤ y) : ... ≤ p.L ^ 2 / (2 * Real.log 2)`: `2 log 2` comes from `y ≥ log 2` (frequency `log N`, `N ≥ 2`), **not** the range |
| P33 | `XiPrime/ExplicitFormula/ZeroFree.lean:1343-1359`, `Hardy/ZeroFree.lean:459-470` | `exists_isNontrivialZero` / `exists_NT_ge`: nonemptiness of `zetaZeroConfig.window T (2*T)` via P1 |
| P34 | `XiPrime/Assembly.lean:517-550`, `Zeta23/Assembly.lean:592-598` | `cumulative_of_dyadic`, `dyadic`: summation of dyadic blocks to `(0, T]` |
| P35 | `XiPrime/Final.lean:279-298` | `eventually_zetaCount_le_Ncount : ∀ᶠ T in atTop, (1 - δ) * (Zeta23.zetaZeroConfig.N T (2 * T) : ℝ) ≤ (Ncount T (2 * T) : ℝ)` from both `main` fields and `isLittleO_log_Tl` |

### 1.4 Shared zeta-side files (the four Wang localized)

| Component | Lean location | Range dependence |
|---|---|---|
| Explicit formula | `Zeta23/WeilEF/*` (zero `2*T` occurrences); `XiPrime/ExplicitFormula/*` (P27 to P30 only) | none beyond `τ_k ∈ [T, 2T]` used as an upper bound |
| Montgomery-Vaughan | `Zeta23/Hypotheses.lean:107-111` (`MVHilbert`, abstract, no interval), `Zeta23/MV/Final.lean:30-31` (`mv_hilbert`, `C = 26`); applied in P20, P21, `Zeta23/PrimeSideB/PPKernel.lean` | mean value over `[T, 2T]`; the constant is interval-free |
| Riemann-von Mangoldt | `Zeta23/RvM/MainTerm.lean:215-221, 482-484` (`rvM_main_param`, `rvM_main`), same good-height argument as P31 | dyadic statement; arbitrary-height intermediates |
| Local count | `Zeta23/RvM/LocalCount.lean:294` (`zetaZeroConfig_local_count`); `XiPrime/ZeroCount/Landau.lean:79-80`: `theorem xiDeriv_local_count : ∃ A₀ : ℝ, 1 ≤ A₀ ∧ ∀ t : ℝ, ((xiDerivZeros hF2 hs).N t (t + 1) : ℝ) ≤ A₀ * Real.log (\|t\| + 3)` | none (unit windows at every real `t`) |

## 2. Classification

Short-window notation: `I_H = (T, T+H]`, `H = T^theta`, `d_H = floor(L H / 2 pi)`, `tau_k = T + k h ∈ [T, T+H]`, `N_H = N_xi'(T, T+H) ~ H l / 2 pi`. A class (b) entry lists `c` such that the step survives iff `c < theta`.

**Class (a), cosmetic.**

- D1, D2, D3, D5, D6: replace `2T` by `T + H` and `LT/2π` by `LH/2π`. D2 keeps `D0 = √T` or takes `T^β`.
- D4: `ell1` is the dyadic value of `(1/T)∫_T^{2T} log(τ/2π)`; in the short window the main term is `H l/2π + O(H²/T)`, so `ell1 → l` and `lam1 = L/ell1 → λ` exactly, simplifying `cRatio` (`ThmD/AssemblyD.lean:28`: `def cRatio (lam1 a b J : ℝ) : ℝ := lam1 * a ^ 2 / (b + lam1 ^ 2 * J)`).
- S1, S2, S9, S10, P25, P26: count and `μ`-integrals over `[T, T+H]`; short-window statements needed (§5), arguments height-local.
- S3 to S8: interface Props; replace `Z.N T (2 * T)` by `Z.N T (T + H)`.
- P8: full-lattice identity; truncation to `0 ≤ k < d_H` only shrinks sums.
- P9, P10, P34: bookkeeping; P34 is not part of a short-interval statement at all.
- P11, P12, P27, P28, P29: `d_H h ≤ H ≤ T`, `τ_k ≤ T + H ≤ 2T`, so `δ_kl ∈ [0, ½ log(1+H/T)] ⊂ [0, ½]`; every use is an **upper** bound and holds a fortiori. `far_subset` (P28) concludes `|t − τ_k| ≥ T/4` from `T ≤ τ_k, τ_l ≤ 2T`; same two-line proof. The `1/T`, `1/T²` floors come from `cauchyK_far` (`EntryError.lean:88-90`: `T ≤ a → t ≤ T / 4 → cauchyK a t ≤ 16 / (9 * T ^ 2)`), a height fact.
- P30: `δ = (1 − 3λ/4)/2` is the power saving `X^{3/4}L²l/T` from the contour on `Re s = 5/4` at height `~T`; unchanged.
- P31: height-local; localizes with `2T ↦ T + H` (§5).
- P32: frequency constant; the bound holds "for EVERY K" (`Dependence.lean:16`), so the number of grid points is irrelevant.
- P33: any window with `N → ∞` serves.
- P20, P21: identity part cosmetic (`I_H × I_H`, endpoints `T`, `T+H`); off-diagonal in (b).
- P16 main term, P18 `i1`, P19 first term, P23: main terms proportional to the range length become proportional to `H`, as `N_H` does; ratios unchanged.
- The whole coefficient side (`Coeff/*`, `xiCoeffFamily_hyps` `Coeff.lean:41-47`, `coeff_H3` `Coeff/H3.lean:44-45`, `xiReexpansion` `Coeff/Reexpansion.lean:42-44`): no interval; constants `T`-uniform (`Statement.lean:151-153`: "with T-UNIFORM constants (every ∃C is outside ∀T)").
- `xiDerivZerosInStrip_holds`, `xiDerivSeam_of_strip`, `wZerosInStrip_holds`: height-free.

**Class (b), absorptions `E ≤ ε N`.**

| Item | Error `E` | Against | `c` | Survives iff |
|---|---|---|---|---|
| P4, P6 (`NII`, `D0 = √T`) | `6 A₀ √T l` | `H L` | `1/2` | `θ > 1/2`. Removable: with `D0 = T^β`, `NII ~ T^β l` and (P5) `θ₀ ~ T^{λ/2 − 2β} l`, so any `β ∈ (λ/4, θ)` works, nonempty whenever `λ < θ`. In the stated range `θ ∈ (0.5133, 1)` nothing changes. |
| P3, P5 (`B = θ₀/(aL)`) | `C l T^{λ/2 − 1}/L` | `1` | height-only | always (`λ < 2`) |
| P13, P14 (entry errors) | `C H T^{−δ}/L`, `C² T^{−2δ} H/L²` after `d ≤ LT/2π ↦ d_H ≤ LH/2π` | `H l` | `−δ` | always |
| P15, P18 `i2`, P16 second term, P19 last three terms | `A L³ l⁴ (1+X)` in `(aL²)² N` units, i.e. `l⁴ X/H` | `H l` | `λ` | `λ < θ` |
| P17 (trace of entry dependence) | `κ_tr √X = O(T^{λ/2})` | `H l` | `λ/2` | implied by `λ < θ` |
| P22 (`lem:ends`) | `C L l log l B²`, `B ~ l + √X l`, i.e. `O(L l³ log l X)` | `H L l²` | `λ` | `λ < θ` |
| P24 `prop_PP`, `cross_PPi`, D7 middle term | `l² X` | `H` | `λ` | `λ < θ` |
| P24 `prop_trace`, `cross_muP` | `l² √X` | `H L` | `λ/2` | implied |
| P21 (MV off-diagonal `16 C (∫Φ²) Σ w_n² n`) | `L X l²` | `H L l²` | `λ` | `λ < θ` |
| P35, S9 error, P2 `isLittleO_log_Tl` | `log T` | `H L` | `0` | always |
| P1 | replaced by `N_H ≥ H l/4π` from §5 | | | |

**Class (c).** None found. Candidates examined and rejected: the span bound `d h ≤ T` (P11) is consumed only as an upper bound on `δ_kl`; the `2 log 2` (P32) is a frequency constant; the Poisson lemma (P8) is a full-lattice identity; the argument principle (P31) is stated for arbitrary good heights; the fold `ξ'(1 − conj s) = −conj ξ'(s)` is the functional equation; the `1/T` floors (P28, P30) are height effects; no dyadic decomposition or average produces a main term. The dyadic decomposition that exists (P34) only produces the cumulative form.

**Class (d).** None. Two places where I relied on docstrings rather than proof text: (i) `Tail/Count.lean` groups zeros by integer distance from the nearer endpoint of `I` (docstring `:20-24`); `tail_count_sum_le` (`:294`) is stated for `I = [T, 2T]` and would be restated with endpoints `T`, `T+H`; (ii) `Ends.lean` uses weights `g := (1 + dist(·, ∂I))^{−2}` (docstring `:26-33`); the `E2` bound `∫_{I^c}|ν|σ ≪ B L l` uses only the grid spacing, not its length.

**The hidden `T^{1−θ}`.** A per-block error absorbed against `N(T,2T)` reappears against `HL` with a factor `T^{1−θ}` only if the error scales with the height while the main term scales with the range length. Exactly two such places exist, and both are the named exponent conditions: MV / grid-end effects (`X` vs `H`, `λ < θ`, Wang's condition) and the end-strip count (`√T` vs `H`, `θ > 1/2` or re-choose `D0`). Every other error scales with the range length itself (P13, P14, P16, P18 `i1`, P19, P22 main, P23) or is a pure height power saving. There is no third place.

## 3. Comparison with Wang

**BGSTB Lemma 1 (Wang (2.7)-(2.9)).** `E_x ≪ 1/x + x^{1/2}/T² + x^{−5/2}/T`, pointwise, height-local. Lean: `XiEF`, entrywise at `τ_k, τ_l`, error `C T^{−δ}(1/max 1 Δ² + 1/T)`; same far-contour effects. Class (a) on both sides; the xi' version's extra feature (coefficients frozen at `L*(τ*_kl)`) is range-free.

**BGSTB Lemma 3 (Wang Lemmas 2.3, 2.4), restriction to `I`, error `O(xL³)`.** Wang uses the `1/(1+(t−γ)²)` Cauchy decay plus the unit-window count. Lean, in two pieces: (i) the zero side never restricts; zeros at distance `> D0 = √T` are the tail `E` with `θ₀` (P5-P7), via the faster decay `φ̂(r)² ≪ X^{1/2}C₁²/r⁴`; zeros in the end strips are `NII` and are surrendered in Lemma R (P9: `s1 ≤ N0s + NII`). Wang's `xL³` corresponds to the pair (`θ₀`, `NII`): `θ₀` free, `NII ~ √T l` costs `θ > 1/2` or a re-chosen `D0`. (ii) The prime side does restrict: `lem_ends` (P22) is the grid-sum-versus-`I×I`-integral difference, `O(L l log l B²)`, Wang's `xL³` on the nose; both `o(HL)` iff `λ < θ`. Same constraint, same origin.

**BGSTB Lemma 4 (Wang Lemma 2.5, Prop 2.6).** Wang: `∫_I|D_x|² = H Σ a_n² + O(Σ n a_n²)` (MV), `∫_I|B_x|² = HL²/x² + O(HL/x²)`, cross terms by Cauchy-Schwarz. Lean: prop:PP for `P_c` (P19-P21; `O1_bound_w` is Wang's `O(Σ n a_n²)`), the diagonal `(T/π)Σ|c_N|² g(log N)/N` via `(H3)` (Wang's Lemma 2.5 with `D1` in place of `s`), the `μ`-integrals S2/P25/P26 (Wang's `B_x` terms), cross terms (`Traces.lean:14-17`). Every localization Wang performs here is class (a) on the identity and class (b), `c = λ`, on the MV end effect. Identical.

**BGSTB Lemma 5 (Wang Theorem 2.2).** Wang integrates `F_I(T^α)` against `g`; main term `M_1 = (HL/2π)∫|α|g`; error `O(H + T^λ L²)`. Lean forms no pair-correlation function: it computes `tr` and `‖·‖_F²`; the `|α|`-integral is `jWin D lam v = 2 ∫_0^1 D(lam r)(v⋆v)(r) dr` (`Defs.lean:176`), `D = D1`. Wang's error is Lean's `o(N)` at fixed `λ < 1`, becoming `λ < θ`. Same.

**Wang §3 (removing `w`).** Not needed: the Gram kernel is entire, off-line zeros are handled by prop:block (`Ahat = P + Q`, `posIndex Q ≤ p`, `Assembly/Inputs.lean:42-52`), and the certificate is Lemma R directly. Nothing to localize.

**Lamzouri Prop 2.1.** Lean: `seamA_mult2/3` (`Assembly/SeamMult.lean:46-53, 69-75`) plus `count_certificate` (`Assembly/Certificate.lean:39-54`); no arithmetic; apply verbatim to xi' zeros in `I_H`.

**Wang §4 (Prop 4.1).** Lean has `cWin D lam v` for any admissible `v` and every `λ ∈ (0,1]` (`Window.lean` W1-W5), decimals fixed at `λ` near 1 (`Statement.lean:266-274`). No kernel-checked optimal window for `D1` at any bandwidth; Wang's Euler-Lagrange argument (`f'' + 2f = 0`) is specific to `|u−v|`.

**Steps with no zeta analogue.** (1) Entry dependence `[XF' Lemma 6.1]` (`Transfer.lean` §3, `Dependence.lean`): `δ_kl ≤ ½ log(1+H/T) ≤ H/2T → 0` inside the expansion domain `[0, ½]` (`Transfer/Inputs.lean:58`) with room to spare; **easier** in a short window; absorptions P17, P18 class (b) with `c = λ/2`, `λ`. (2) `(H3)` with `D1`: range-free (§4). (3) Strip fact and seam: height-free. (4) Contour on `Re s = 5/4` with the geometric expansion of `1/(L − A)`: height-local.

## 4. The deterministic corrections

**Where.** `XiPrime/Defs.lean:154-161`:

```
def D1coeff (k : ℕ) : ℝ := 2 * (4 : ℝ) ^ (k + 1) * (Nat.factorial k : ℝ) / (Nat.factorial (2 * k + 2) : ℝ)
def D1 (s : ℝ) : ℝ := s - 4 * s ^ 2 + ∑' k : ℕ, D1coeff k * s ^ (2 * k + 3)
```

`D1` is `F_1` minus its `T^{−2α} log T` term (docstring `:158-159`). Its only consumer is `(H3)` (`Statement.lean:166-168`):

```
H3 : ∀ ε : ℝ, 0 < ε → ∃ T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T → ∀ y : ℝ, 0 ≤ y → y ≤ l T →
  |(∑ N ∈ Finset.Ioc 0 ⌊Real.exp y⌋₊, ‖F.c T N‖ ^ 2 / N) - l T ^ 2 * ∫ s in (0:ℝ)..(y / l T), F.D s|
    ≤ ε * l T ^ 2
```

proved by `coeff_H3` (`Coeff/H3.lean:44-45`):

```
theorem coeff_H3 (Λf : ℝ → ℂ) (hre : ∀ T, (Λf T).re = l T / 2) (him : ∀ T, |(Λf T).im| ≤ 1) :
    ∀ ε : ℝ, 0 < ε → ∃ T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T → ∀ y : ℝ, 0 ≤ y → y ≤ l T → ...
```

instantiated at `Λf = LT`, `def LT (T : ℝ) : ℂ := ((l T / 2 : ℝ) : ℂ) + Complex.I * (Real.pi / 4 : ℝ)` (`Defs.lean:85`). Downstream, `D1` reaches the certificate only through `jWin`, `cWin`, `kappaXi` (`Defs.lean:176-188`), the limit `J_T → jWin/λ` (`Window.lean` W2; `Traces.lean:18-19`, "sumJ is in ε-form"), and the prime-side diagonal `(T/π)Σ|c_N|²g(log N)/N` (P19 first term, `Concrete.lean:97`).

**Whether the range is used.** It is not. `(H3)` is an arithmetic identity for `Σ_{N≤e^y}|C(N;L_T)|²/N`, `0 ≤ y ≤ l` (squarefree layers by `ω(N)`, Mertens induction, non-squarefree remainder, `Coeff/DiagLaw.lean:7-14`), whose only `T`-dependence is the scalar `l(T)` inside `L_T`. No height average, no interval, no `2T` under `Coeff/`. Where `D1` enters the second moment it multiplies the MV diagonal, which is proportional to the range length (`p.T` in P19, `T` in P23) and becomes proportional to `H`, exactly as `N_H` does.

So the corrections carry no hidden `T^{1−θ}`. **The brief's hazard is refuted.** The short-window proof needs from this side exactly what Wang's Lemma 2.5 supplies on the zeta side: an arithmetic diagonal law with `T`-uniform constants, already kernel-checked (`xiCoeffFamily_hyps`, `Coeff.lean:41-47`).

Two secondary, benign meetings of coefficients and height: `L*(τ*_kl) − L_T = δ_kl ≤ H/2T` (§3, new step 1); and the `(H1)`-`(H3)` ranges `x ≤ e^{l(T)}` (`Statement.lean:151-155`) cover `X = e^{λl}` unchanged.

Caution for the brief: "Wang's Theorem 2.2 delivers exactly that on the narrowed band" is not usable; the kernel-checked route consumes no zeta second moment, so the xi' `CoeffMoments` must itself be localized, by Wang's MV / ends arguments (§3).

## 5. The local count

**Proved.** `xiDeriv_local_count` (`Landau.lean:79-80`) for every real `t`; `xiDeriv_rvM_main` (S9), dyadic only. "N_xi'(T) = N(T) + O(log T)" appears only in docstrings (`Statement.lean:132`, `Final.lean:268`, `ZeroCount.lean:11`); the only zeta comparison is `eventually_zetaCount_le_Ncount` (P35), dyadic, from the two dyadic main terms.

**Do these suffice for `N_xi'(T,H) = HL/2π + O(H + log T)`?** As stated, no: the dyadic main term cannot be localized, and the unit-window count alone gives `N_xi'(T,T+H) ≤ A₀(H+1) log(T+H+3)`, the right order with no main term. The cumulative comparison would finish it in one line via Wang's (1.2), but it is not a theorem in this tree.

**What is missing is a statement, not an argument.** The proved intermediates are interval-free:

- `Ncount_eq_im_halfContour` (`ZeroCount/Contour.lean:142-145`): `(hF2 : XiDerivZerosInStrip) (hs : XiDerivSeam) {T₁ T₂ : ℝ} (h12 : T₁ ≤ T₂) (hg₁ : GoodHeight T₁) (hg₂ : GoodHeight T₂) : (Ncount T₁ T₂ : ℝ) = (1 / Real.pi) * (Zeta23.RvM.halfContour (logDeriv xiDeriv) T₁ T₂).im`.
- `halfContour_Yfn_bound` (`ZeroCount.lean:111-114`): `∃ C T₀ : ℝ, 0 < C ∧ 4 ≤ T₀ ∧ ∀ T₁ T₂ : ℝ, T₀ ≤ T₁ → T₁ ≤ T₂ → GoodHeight T₁ → GoodHeight T₂ → |(halfContour (logDeriv Yfn) T₁ T₂).im| ≤ C * Real.log (|T₁| + 3) + 3 * Real.pi + C * Real.log (|T₂| + 3)`.
- `halfContour_xiDeriv_split` (`ZeroCount.lean:43-46`) and `Zeta23.RvM.gamma_side` (`RvM/GammaSide.lean:121`): `(1/π) Im halfContour(Γℝ'/Γℝ) T₁ T₂ = ∫_{T₁}^{T₂} μ` exactly.
- `exists_goodHeight` (`ZeroCount/Contour.lean:31`): `(hs : XiDerivSeam) (a : ℝ) : ∃ T ∈ Icc a (a + 1), GoodHeight T`.
- `rvM_main_of` (`GenericRvM.lean:118-126`): the bookkeeping, with unit strips by the local count (`:162-179`).

Hence `N_xi'(T₁,T₂) = ∫_{T₁}^{T₂} μ + O(log T₂)` for good `T₁ ≤ T₂ ≥ T₀`, and with good heights in `[T−1,T]` and `[T+H, T+H+1]`, `N_xi'(T,T+H) = ∫_T^{T+H} μ + O(log(T+H))`. The one new lemma is the short-window `μ`-integral: from `GammaFacts.stirling` (`Hypotheses.lean:131-132`, `|mu τ − (1/2π) log(|τ|/2π)| ≤ C/τ²`) and the FTC anchor pattern of `IntMu.lean:28-30` at upper limit `T+H`, `∫_T^{T+H} μ = (H/2π) l(T) + O(H²/T + 1/T)`. Since `H²/T ≤ H` for `H ≤ T` and `l = L − log 2π`: `N_xi'(T,H) = HL/2π + O(H + log T)`, Wang's (1.2). The same FTC argument gives `∫_T^{T+H} μ² = (H/4π²) l²(1 + O(1/l²))` for P25.

Consequences: P1 becomes `N_H ≥ H l/4π`; P2 becomes "`o(H l)` implies `o(N_H)`"; `tendsto_N_atTop` and `count_certificate`'s `hNtop` follow. For a statement against the zeta count one also needs Wang's (1.2) or a localized `rvM_main_param` (`RvM/MainTerm.lean:215`).

Verdict on item 5: **something is missing, and it is a two-lemma statement (`xiDeriv_rvM_window` plus the short-window `μ`-integrals), not an argument.** Main term and `O(H + log T)` come out right.

## 6. Verdict

**PASS WITH CONDITIONS.**

Every dyadic use is class (a) or (b). Class (b) exponents: `c = λ` (MV and grid-end effects, seven occurrences, one mechanism), `c = λ/2` (entry-dependence trace and two crude remainders, implied), `c = 1/2` (end strips with `D0 = √T`), `c = 0` (`O(log T)`), and pure height power savings. The corrections of item 4 are a range-free arithmetic identity and survive unchanged. No step uses the dyadic structure to produce a main term.

**Conditions.**

1. **Bandwidth `λ < θ`** (Wang's condition; P15, P16, P18 `i2`, P19, P21, P22, P24, D7). Band `(−θ, θ)` open; theorem at every fixed `λ < θ`, constant by `λ → θ⁻` via continuity of `λ ↦ kappaXi λ v` (`Window.lean` W4), as `xiDeriv_simple_on_line_limitForm` (`Final.lean:227-249`) does at 1.
2. **End strips: `θ > 1/2` with `D0 = √T`**, or `D0 = T^β`, `λ/4 < β < θ` (P4-P6). In the range `θ > 0.51332` the first option costs nothing; the second changes one frozen constant (`Defs.lean:60-61`, `Tail.lean:57`).
3. **Short-window zero count** (§5): state and prove `xiDeriv_rvM_window` and the two short-window `μ`-integrals; corollaries of kernel-checked lemmas.
4. **Grid**: `d_H = floor(LH/2π)` (`Defs.lean:215-216`), `NII_H = N(T−D0,T) + N(T+H, T+H+D0)` (`Assembly/Inputs.lean:33`), `tau_mem` as `T ≤ τ_k ≤ T+H` (P27, P29). Every downstream use is an upper bound.
5. **Constant**: `CertFlat`/`CertQuartic` (`Statement.lean:266-274`) are strict at `λ` near 1 and do not transfer; bandwidth-`θ` decimals must be recomputed (`landscape.py`: `0.130262` at `θ = 0.55`, `0.281718` at `0.60`, `0.682554` at `0.80`, threshold `0.51332`) and enclosed by ball arithmetic before any number is stated.
6. **Denominator**: natural statement against `N_xi'(T, T+T^θ)`; against `N(T, T+T^θ)` needs the zeta short-window count. The cumulative `N_xi'(T) = N(T) + O(log T)` is not a theorem here and should not be quoted as one.
7. **Framing**: write it as "localization of the kernel-checked xi' second moment along Wang's route", not "Wang's Theorem 2.2 plus a correction" (§0, §4).

**The Hardy `Z'` arm** (`hardyW_simple_on_line`, `Final.lean:516-520`): same architecture, real base `l/2`, `wReexpansion`, `riemannVonMangoldt_W` from the same `rvM_main_of`; `wZerosInStrip_holds` for `|Im| ≥ t_W`, height-free. Verdict and conditions 1-6 apply verbatim.

### Outline of the short-interval xi' proof (Wang's section structure)

Fix `θ ∈ (0,1)`, `H = T^θ`, `I_H = (T, T+H]`, `λ ∈ (0, θ)`, `L = λl`, `X = e^L`, admissible `v` (`WindowProfile`, `Statement.lean:252-256`), `D0 = √T` if `θ > 1/2` (else `T^β`, `λ/4 < β < θ`).

1. **Setup** (Wang §1). Grid `h = 2π/L`, `d_H = floor(LH/2π)`, `τ_k = T + kh` (localizes `Defs.lean:212-219`); `I'_H`, `NII_H` (localizes `Defs.lean:66-67`, `Assembly/Inputs.lean:33`); `xiDerivZeros₀` unchanged (`Final.lean:83-84`).
2. **Short-window count** (Wang (1.2)). `N_xi'(T,T+H) = (H/2π) l(T) + O(H + log T)` from `Ncount_eq_im_halfContour`, `halfContour_xiDeriv_split`, `halfContour_Yfn_bound`, `gamma_side`, `exists_goodHeight`, `xiDeriv_local_count`, new short-window `∫μ`; consequences `N_H → ∞`, `N_H ≥ Hl/4π`, `log T = o(N_H)`, `√T l = o(N_H)` (localizes `rvM_main_of`, `eventually_N_ge`, `isLittleO_N_of_isLittleO_Tl`).
3. **Zero side** (Wang §2 Prop 2.1, §3). (3a) prop:block for zeros in `I'_H` (`ZeroSide.lean` §3; `PoissonSq` unchanged). (3b) prop:tail at `I_H`: `theta0` unchanged, `Tail/Grid` a fortiori, `Tail/Count` with endpoints `T`, `T+H`; `B → 0`. (3c) `NII_H ≤ 6A₀ D0 l = o(N_H)` (localizes `Tail.lean:676-679`). (3d) Lemma R: `4 tr Ghat − ‖Ghat‖_F² − 2N_H − 3NII_H − B(4 + 2√‖Ghat‖² + B) ≤ N0s_xi'(I_H)` and the `c = 3` form (localizes `seamA_mult2/3`).
4. **Explicit formula** (Wang Lemma 1). `XiEF xiDerivZeros₀ Pf_H`: identical constants, `δ = (1−3λ/4)/2`; only `tau_mem : T ≤ τ_k ≤ T+H` changes (localizes `XiEFAssembly.lean:83`, `TestWeight.lean:879-898`).
5. **Trace transfer** (`[XF' 5.1, 6.1]`, no zeta analogue). (5a) `|tr Ehat| ≤ d_H C T^{−δ} 2/(a₀L²) = o(N_H)`, `‖Ehat‖_F² = o(N_H)` (localizes `Transfer.lean:362-425` with `d_H ≤ LH/2π`). (5b) `δ_kl ∈ [0, H/2T]`; trace `≤ κ_tr √X = o(N_H)` (`λ/2 < θ`); Frobenius main `2Aρ₀²H/a₀²` vs `η²Hl` (`Transfer.lean:751-762`, `T ↦ H`), end effect `AL³l⁴(1+X)/(a₀L²)² = o(Hl)` (`λ < θ`; `Transfer.lean:611-612, 763-775`; `PPUpper` with `p.T ↦ H`).
6. **Prime-side moments** (Wang Lemmas 2.3-2.5, Prop 2.6, Thm 2.2). `CoeffMoments xiDerivZeros₀ Pf_H xiCoeffFamily (kappaXi λ v)` with `N = N_H`: (6a) prop:trace with `∫_T^{T+H}μ`; (6b) `lem:ends` over `I_H × I_H`, `O(L l³ log l X) = o(HLl²)` (`λ < θ`); (6c) prop:mumu with `∫_T^{T+H}μ²`; (6d) prop:PP `𝓜 = (H/π)Σ|c_N|²g(log N)/N + O(LΣ|c_N|² + LS1²)`, MV at endpoints `T`, `T+H` (localizes `PP.lean:149, 395-402`); diagonal by `(H3)` **unchanged**; (6e) cross terms `Traces.lean:14-17` with `T ↦ H`; (6f) ratio `~ cRatio(λ; a,b,J) N_H`, `lam1 = λ` exactly, limit `cWin D1 λ v` (localizes `TracesBoundsXi`, `momentsW_of_family`, `Window.lean` W2, W3).
7. **Assembly** (Wang §3 (3.7)-(3.9)). `gzMoments_of_transfer` (`XiPrime/Assembly.lean:37-66`) then `count_certificate`/`_c3` give `(2 − kappaXi λ v − ε)N_xi'(I_H) ≤ N0s_xi'(I_H)` and `(3/2 − kappaXi λ v/2 − ε)N_xi'(I_H) ≤ N_d,xi'(I_H)` (localizes `fixedLam_family`, `XiPrime/Assembly.lean:443-462`). Let `λ → θ⁻` (`eps_form_of_continuousOn`): `liminf N0s_xi'(T,T^θ)/N_xi'(T,T^θ) ≥ 2 − kappaXi θ v`.
8. **Window at bandwidth θ** (Wang §4). Optimize `v` in `c_θ(v; D1)`; no closed form (Wang's Euler-Lagrange is specific to `|u−v|`); `landscape.py` supplies the candidate, ball arithmetic the stated decimal (condition 5). Positive for `θ > 0.51332`; claim "first power-length statement, `T^θ`, `θ < 1`, as a function of θ", with Rezvyakova's `0.413` and Conrey's `0.79874` as comparanda.

**Formalization footprint.** To touch: `Zeta23/Defs.lean` (`Iwin`, `Iprime`, `d`, `ZIprime`, `NIprime`), `Zeta23/Assembly/Inputs.lean` (`NII`), `Zeta23/Hypotheses.lean` (short-window `RiemannVonMangoldt`, `int_mu(_sq)`), `Zeta23/Tail/Count.lean`, `Zeta23/PrimeSideA/Ends*.lean`, `Zeta23/PrimeSideB/PPKernel.lean`, `XiPrime/PrimeSide/PP.lean`, `XiPrime/Transfer.lean` (`d_le`, `tau_lt_two_T`, four `N` comparisons), `XiPrime/ExplicitFormula/{XiEFAssembly,TestWeight,GramBridge}.lean` (`tau_mem`), `XiPrime/ZeroCount.lean`, `XiPrime/Statement.lean`, `XiPrime/Assembly.lean`, `XiPrime/Final.lean`. Untouched: `Coeff/`, `Certificate/`, `Window.lean`, `ZeroSide.lean`, `LinAlg`, `MV/`, `WeilEF/`, strip and seam files. A clean route is to make the range a second parameter `(T, U)` with `U = 2T` recovering the current tree, so the rule "never hard-code `2T`" is enforced by the type.

**Not claimed.** That the Lean localization is small (some 40 touch points); novelty beyond `RESULTS.md` §4's search; any constant, since none is enclosed at bandwidth θ; anything about RH.
