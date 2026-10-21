# Short-interval simple zeros of xi-prime: proof draft

Written 2026-09-12 against `anthropics/formal-math` at commit
`fbdc36bbf17d20af3fd0447c6d1a8a02773c9844` (every `file:line` below is relative
to `zeta23/`), Wang arXiv:2609.07918v1 (Sections 1 to 4, read in full),
Lamzouri arXiv:2609.02882 (Sections 2 and 3), and `AUDIT-dyadic.md` in this
directory, whose section 6 supplies the eight-step outline this document
follows. It is a draft of a proof at the level of detail of a research paper.
It is not a result: it has not been refereed, nothing in it is kernel-checked
beyond the statements quoted from the tree, and the constant it produces is
carried as a symbol. Nothing here bears on RH (`docs/08-why-it-is-hard.md`).

Grades. Every step carries one of three tags.

- `[KERNEL-CHECKED, DYADIC]`: a statement the Lean tree proves for the dyadic
  window `(T, 2T]` (or with no window at all) and which is used here unchanged,
  as a special case, or as an upper bound. What is quoted is the statement,
  never a docstring.
- `[NEW STATEMENT, PROOF WRITTEN HERE]`: a short-window statement not in the
  tree, with its proof written out below at the level of Wang's paper.
- `[ASSERTED]`: a step that could not be written out. Each one names what is
  missing.

Conventions. No em dashes. The word reserved to `zeta/rigor.py` and the Lean
arm is not used in this file. "Kernel-checked" means: a theorem of the tree at
the commit above, zero sorrys. Numbered equations in Wang are cited as
"Wang (2.19)", his results as "Wang Lemma 2.4"; Lamzouri's as "Lamzouri
Proposition 2.1".

---

## Status

| Tag | Steps and lemmas carrying it |
|---|---|
| `[KERNEL-CHECKED, DYADIC]` | 1 (definitions); 3a (block inequality); 3b Lemma 3.3 (grid sum); 4 (explicit formula, special case); 5b-i (re-expansion, Dirichlet-kernel bound); 6.0 (Poisson identity, taper decay, MV Hilbert inequality, Chebyshev-Mertens, (H1)-(H3), the diagonal law and its partial summation); 6f-ii (window limits W1-W3); 7.1 (moment transfer algebra); 7.3 and 8 (continuity W4, the window functional). 14 items. |
| `[NEW STATEMENT, PROOF WRITTEN HERE]` | 1.2 (two-sided floor); 2.1, 2.2, 2.3 (contour form), 2.3′ (the two count forms), 2.4; 3.2, 3.4, 3.5, 3.6; 5.1, 5.2, 5.3, 5.4; 6.1, 6.2, 6.3, 6.4, 6.5, 6.6 (including the `lam1` restatement); 7.2, 7.3, 7.3′ (the `λ → θ⁻` device), 7.4; Theorem A and Theorem B. 26 items. |
| `[ASSERTED]` | **None.** |

Two remarks on the count, so that "none" is read correctly.

1. Several `[NEW STATEMENT]` items are localizations whose proof is the tree's
   proof with the range renamed (2.3, 5.2, 6.3, 6.4, 6.5, 7.2). They are written
   out here anyway, because the point of the exercise is to show *where* the
   range enters and that it enters only as an upper bound. The tag records that
   the short-window statement is not in the tree, not that the mathematics is
   new.
2. Two `[NEW STATEMENT]` items, 6.1 and 6.2, are the prime-side boundary
   effects (Wang Lemma 2.4's counterpart). Their proofs are written here from
   the tree's stated ingredients (the Poisson identity, the real-line decay of
   the taper transform, the density bound `NuBound`), following the route the
   tree's `Ends.lean` describes. A reader checking them line by line needs
   those three kernel-checked inputs and nothing else; the audit
   (`AUDIT-dyadic.md` §0) says it did not re-derive `Ends E1/E2`, and this
   document does.

The seven conditions of the audit are all discharged by the proof: condition 1
(bandwidth `λ < θ`) is where every prime-side and grid-end error is absorbed
(§9); condition 2 (end strips) is discharged by the choice of padding in §1;
condition 3 (short-window count) is §2; condition 4 (grid bookkeeping) is §1
and §4; condition 5 (constants) is §8, which states no decimal; condition 6
(denominator) is the statement itself, against the xi-prime count, with the
zeta count handled in 7.4; condition 7 (framing) is the title of §6.

**Two conditions are carried here in the form the adversarial re-audit of
`AUDIT-dyadic.md` (2026-09-12) corrected them to, not as the audit first
stated them.** Condition 4 is false as first stated: the grid size `d` is
consumed two-sidedly, not only as an upper bound. The lower floor inequality
`T < (d+1)h` (`Nat.lt_floor_add_one`) is what makes the grid fill the window
to within one spacing, and it is load-bearing in the main term of the first
trace (`riemann_sum_monotone`, `Zeta23/PrimeSideA/Basic.lean:876-882`) and in
the majorant of the missing lattice mass in `lem:ends` (`tau_d_gt`,
`Zeta23/PrimeSideA/EndsE1.lean:262-266`). Both localize with `d_H = ⌊H/h⌋`,
Lemma 1.2. Condition 3 named the wrong statement shape: the interface never
consumes Wang's (1.2). What `prop_trace` consumes is a count within `O(l)` of
the `μ`-main term `T ℓ₁/2π`, supplied by `rvm_evBound`; the localized
count is therefore stated first in contour form, `|N_H − ∫_T^{T+H} μ| ≤ C log T`
(Lemma 2.3), and Wang's form is a corollary (2.3′), with the `H²/T` living in
the `μ`-integral (Lemma 2.1) and not in the count error. The re-audit's six
further points (the `ThmE/PPChi.lean` layer under 6d; the two roles of
`Setting.T`; the `λ → θ` device; `lam1`; the ordering of §2 before §5; the
additional files) are folded in where they belong and are marked "(re-audit)".

---

## 0. The theorem, the notation, and where the conditions enter

### 0.1 Statement

Throughout, `ξ(s) = ½ s(s−1) π^{−s/2} Γ(s/2) ζ(s)` is Riemann's xi-function
(`Zeta23/XiPrime/Statement.lean:63-66`, `xi_eq`) and `ξ′` its derivative. For
real `T₁ ≤ T₂` let

- `N_{ξ′}(T₁, T₂)` be the number of zeros `ρ` of `ξ′` with `T₁ < Im ρ ≤ T₂`,
  counted with multiplicity and with no condition on `Re ρ`
  (`Ncount`, `Zeta23/XiPrime/Defs.lean`);
- `N^s_{0,ξ′}(T₁, T₂)` the number of those that are simple and have
  `Re ρ = 1/2` (`N0simple`);
- `N_{d,ξ′}(T₁, T₂)` the number of distinct ones (`Ndist`).

Let `v` be an admissible window profile, meaning `WindowProfile v`
(`Zeta23/XiPrime/Statement.lean:252-256`):

```lean
structure WindowProfile (v : ℝ → ℝ) : Prop where
  even : ∀ s : ℝ, v (-s) = v s
  contDiff : ContDiff ℝ 3 v
  pos : ∀ s ∈ Icc (-(1/2 : ℝ)) (1/2), 0 < v s
  le_one : ∀ s : ℝ, v s ≤ 1
```

and let `kappaXi lam v = 1 / cWin D1 lam v` be the window constant of the
tree (`Zeta23/XiPrime/Defs.lean:176-188`; quoted in full in §8).

**Theorem A (fixed bandwidth).** Fix `0 < θ < 1`, `0 < λ < θ`, an admissible
profile `v`, and a taper profile `ϱ` (`TaperProfile`). Put `H = T^θ` and
`I = (T, T + H]`. For every `ε > 0` there is `T₀` such that for all `T ≥ T₀`,

```
(2 − kappaXi(λ, v) − ε) · N_{ξ′}(T, T+H)  ≤  N^s_{0,ξ′}(T, T+H),
(3/2 − kappaXi(λ, v)/2 − ε) · N_{ξ′}(T, T+H)  ≤  N_{d,ξ′}(T, T+H).
```

**Theorem B (bandwidth θ).** Under the same hypotheses, for every `θ ∈ (0,1)`
and every admissible `v`,

```
liminf_{T→∞} N^s_{0,ξ′}(T, T+T^θ) / N_{ξ′}(T, T+T^θ)  ≥  2 − kappaXi(θ, v),
liminf_{T→∞} N_{d,ξ′}(T, T+T^θ) / N_{ξ′}(T, T+T^θ)   ≥  3/2 − kappaXi(θ, v)/2.
```

The constant is `2 − kappaXi(θ, v)`, enclosed separately, see `RESULTS.md`.
No decimal for it appears in this document.

Both theorems are unconditional. Theorem B is Theorem A plus continuity of
`λ ↦ kappaXi λ v` on `(0, 1]` (§7.3). The denominator is the xi-prime count; the
same bounds against the zeta count `N_ζ(T, T+H)` follow from Wang (1.2) and
are recorded in 7.4.

### 0.2 Notation

The tree's notation is kept wherever it exists, with one new symbol
(`ℓ_H`) replacing one dyadic scalar (`ℓ₁`).

| Symbol | Meaning | Tree |
|---|---|---|
| `l = l(T)` | `log(T/2π)` | `Zeta23/Defs.lean:48` |
| `L = λ l`, `X = e^L = (T/2π)^λ` | bandwidth and its exponential | `Params.L`, `Params.X` |
| `h = 2π/L` | grid spacing | `Params.hgrid` |
| `τ_k = T + k h` | grid points, `k ∈ ℤ` | `Params.tau`, `Zeta23/Defs.lean:218-219` |
| `d = ⌊LT/2π⌋` | dyadic grid size | `Params.d`, `Zeta23/Defs.lean:215-216` |
| `d_H = ⌊LH/2π⌋` | short-window grid size | **new**, localizes `d` |
| `I_H = (T, T+H]` | the window | localizes `Iwin`, `Zeta23/Defs.lean:63-64` |
| `D₀ = T^β` | padding, `β` chosen in §1 | localizes `D0 = √T`, `Zeta23/Defs.lean:60-61` |
| `I′_H = (T − D₀, T + H + D₀]` | padded window | localizes `Iprime`, `Zeta23/Defs.lean:66-67` |
| `NII_H = N(T−D₀, T) + N(T+H, T+H+D₀)` | end strips | localizes `NII`, `Zeta23/Assembly/Inputs.lean:33` |
| `N_H = N_{ξ′}(T, T+H)` | the count | localizes `Ncount T (2*T)` |
| `ℓ_H = (1/H) ∫_T^{T+H} log(τ/2π) dτ` | window mean of the log | **new**, localizes `ell1 = l + 2 log 2 − 1 = (1/T)∫_T^{2T} log(τ/2π)dτ` |
| `λ_{1,H} = L/ℓ_H` | | localizes `lam1 = L/ell1`, `Zeta23/Defs.lean:209-210` |
| `φ = φ_T` | the taper `ϱ((L/2 − |u|)/w)`, support `[−L/2, L/2]`; with profile `v`, `φ_v(u) = √(v(u/L)) φ(u)` | `Params.phi`, `Params.atV` |
| `φ̂(z) = ∫ φ(u) e^{izu} du` | paper Fourier transform, entire | `paperFT`, `Params.phiHat` |
| `a = L^{−1}∫φ²`, `b = L^{−1}∫φ⁴` | taper moments | `Params.a`, `Params.b` |
| `Φ(x) = ∫ φ(u)² e^{ixu} du` | transform of `φ²`; `Φ(0) = aL`, `∫Φ² = 2π b L` | `Params.PhiR` |
| `g(y) = ∫ φ(u)² φ(u+y)² du` | window autocorrelation, `g(0) = bL`, `∫Φ(x)² e^{ixy}dx = 2π g(y)` | `AdmWindow.gv` |
| `ψ(r) = min(L, 2/|r|, c_ϱ/(w r²))` | decay majorant of `|φ̂|` on `ℝ` | `Params.psi` |
| `μ(τ)` | `(1/2π) Re digamma(1/4 + iτ/2) − log π/(2π)` | `Zeta23/Defs.lean:83-85` |
| `Π_X(τ)` | `1/(2π(1/4+τ²)) + (1/π) Re((X^s − 1)/s)`, `s = 1/2 + iτ` | `Zeta23/Defs.lean:89-91` |
| `P_c(τ)` | `(1/π) Σ_{N ≤ X} (Re c_N cos(τ log N) + Im c_N sin(τ log N)) / √N` | `XiPrime.Pc`, `Zeta23/XiPrime/Defs.lean:101-103` |
| `ν_c = μ + Π_X + P_c` | the xi-prime density with coefficients `c` | `XiPrime.nuc`, `:113` |
| `c^T_N = C(N; L_T)`, `L_T = l/2 + iπ/4` | the fixed coefficients | `xiCoeffFamily`, `XiPrime.LT` |
| `D₁(s) = s − 4s² + Σ_{k≥0} d_{k+1} s^{2k+3}` | the diagonal density | `Zeta23/XiPrime/Defs.lean:154-161` |
| `γ_ρ = (ρ − 1/2)/i` | complex ordinate, real iff `Re ρ = 1/2` | `gammaOf`, `Zeta23/Defs.lean:105` |
| `G_kl = Σ_ρ m_ρ φ̂(γ_ρ − τ_k) φ̂(γ_ρ − τ_l)` | zero-side Gram matrix | `ZeroConfig.Gz`, `Zeta23/Defs.lean:298-305` |
| `M_kl = ∫_ℝ φ̂(τ−τ_k) φ̂(τ−τ_l) ν_{c^{kl}}(τ) dτ` | entry-dependent prime-side matrix, `c^{kl} = C(·; L_T + δ_kl)` | `Params.Gentry1` |
| `M^T_kl` | the same with `c^{kl}` replaced by `c^T` | `Params.GpC` |
| `M̃ = M/L`, `M̂ = M/(aL²)` | tilde and hat units | `Params.tilde`, `Params.hat` |
| `rtrace`, `frobSq` | real trace, squared Frobenius norm | `RHLinalg` |

Subscript `H` on a matrix means "indexed by `0 ≤ k, l < d_H`". Since
`H ≤ T` gives `d_H ≤ d`, and `τ_k` does not depend on `d`:

> **Observation 1.1 (the short grid is an initial segment of the dyadic
> grid).** `{τ_0, …, τ_{d_H − 1}} ⊂ {τ_0, …, τ_{d − 1}}`, both at the same
> height `T`, same `L`, same taper. Hence every quantity defined entrywise
> from the grid (`G_kl`, `M_kl`, `M^T_kl`, `δ_kl`, the entry error) is, for
> `k, l < d_H`, literally the same real number as in the dyadic development,
> and every entrywise theorem of the tree restricts to the short grid with no
> change. What does not restrict: anything summed over the grid and compared
> with `N(T, 2T)`, and anything defined from the padded window `I′`.

### 0.3 Where the seven conditions enter

| Condition (audit §6) | Discharged in |
|---|---|
| 1. bandwidth `λ < θ` | 5.4, 6.2, 6.4, 6.5, 6.6 (every `X`-sized error) |
| 2. end strips | 1 (choice of `β`), 3.5 |
| 3. short-window count (re-audit: in contour form, `N_H` within `O(log T)` of `∫_{I_H} μ`) | 2.3, 2.3′, 2.2 |
| 4. grid bookkeeping (re-audit: the floor is two-sided) | 1, Observation 1.1, Lemma 1.2, 4, 6.1, 6.2 |
| 5. constants | 8 (no decimal stated) |
| 6. denominator | 0.1 (xi-prime count), 7.4 (zeta count) |
| 7. framing | title of §6 |

---

## 1. Setup (Wang §1; audit step 1)

Fix `θ ∈ (0,1)`, `λ ∈ (0, θ)`, an admissible profile `v`, a taper profile `ϱ`
with width `w ≥ 1`, and `P = paramsOf ϱ λ` with the height-indexed family
`Pf = P.atV v` (flat window: `Pf = fun _ => P`). Let `H = T^θ`. The grid,
window and padding are localized as in the notation table; the zero
configuration is the tree's, unchanged:

`Zeta23/XiPrime/Final.lean:83-84`:

```lean
def xiDerivZeros₀ : ZeroConfig :=
  xiDerivZeros xiDerivZerosInStrip_holds (xiDerivSeam_of_strip xiDerivZerosInStrip_holds)
```

with carrier all zeros of `ξ′` and multiplicity the analytic order. The strip
fact `xiDerivZerosInStrip_holds` (every zero has `0 < Re ρ < 1`) and the seam
facts (reflection `ρ ↦ 1 − ρ̄` preserves zeros and multiplicities; each height
window contains finitely many zeros) are height-free and used unchanged.

**The padding.** The tree takes `D₀ = √T` (`Zeta23/Defs.lean:60-61`,
`def D0 (T : ℝ) : ℝ := Real.sqrt T`). Here `D₀ = T^β` with

```
β ∈ (λ/4, θ),   β ≤ 1/2,
```

a nonempty interval since `λ < θ` (take `β = 1/2` whenever `θ > 1/2`, which
recovers the tree's choice verbatim; otherwise `β = (λ/4 + θ)/2`). The two
constraints are exactly condition 2 of the audit: `β > λ/4` makes the tail
quantity `θ₀` tend to zero (3.4) and `β < θ` makes the end strips negligible
(3.5).

**The grid fills the window (re-audit, condition 4).** The tree uses the
floor two-sidedly. `riemann_sum_monotone` (`Zeta23/PrimeSideA/Basic.lean:876-882`):

```lean
lemma riemann_sum_monotone {μ : ℝ → ℝ} {T h : ℝ} (hh : 0 < h) (hhT : h ≤ T)
    (hmono : MonotoneOn μ (Set.Ici (T - h))) (hnonneg : ∀ x, T - h ≤ x → 0 ≤ μ x) :
    |h * ∑ k ∈ Finset.range ⌊T / h⌋₊, μ (T + k * h) - ∫ x in T..(2 * T), μ x|
      ≤ 2 * h * μ (2 * T)
```

whose proof (`:883-890`) extracts both `d h ≤ T` (`Nat.floor_le`) and
`T < (d+1) h` (`Nat.lt_floor_add_one`); and `tau_d_gt`
(`Zeta23/PrimeSideA/EndsE1.lean:262-266`):

```lean
theorem tau_d_gt (hL : 0 < p.L) (_hT : 0 < p.T) : 2 * p.T - p.h < p.tau p.d
```

#### Lemma 1.2 (two-sided floor, short window). `[NEW STATEMENT, PROOF WRITTEN HERE]`

With `d_H = ⌊H/h⌋ = ⌊LH/2π⌋`: `d_H h ≤ H < (d_H + 1) h`, equivalently
`T + H − h < τ_{d_H} ≤ T + H`, and `τ_{d_H − 1} < T + H`. *Proof.* `Nat.floor_le`
and `Nat.lt_floor_add_one` applied to `H/h ≥ 0`, then multiply by `h > 0` and
add `T`. ∎ (Verbatim the two lines of `riemann_sum_monotone`'s proof and of
`tau_d_gt`, with `T` replaced by `H` in the floor and `2T` by `T+H` in the
conclusion.) Consumers: the Riemann-sum main term in 6.1 and the missing-mass
majorant `(R)` in 6.0 and 6.2. Nothing else in the proof uses the lower floor
inequality.

**Grade.** `[KERNEL-CHECKED, DYADIC]` for every definition carried over
(`Gz`, `Az`, `Ez`, `hat`, `tilde`, `NII`, `s1`, `NIprime`, `theta0`) with
`2T ↦ T+H`, `d ↦ d_H`, `√T ↦ T^β`; `[NEW STATEMENT]` for Lemma 1.2. No other
claim is made in this section.

---

## 2. The short-window count (Wang (1.2); audit step 2 and §5)

The tree's count is dyadic. `Zeta23/Hypotheses.lean:67-70`:

```lean
structure RiemannVonMangoldt (Z : ZeroConfig) : Prop where
  main : ∃ C T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T →
    |(Z.N T (2 * T) : ℝ) - T / (2 * Real.pi) * ell1 T| ≤ C * Real.log T
  local_count : ∃ A₀ : ℝ, 1 ≤ A₀ ∧ ∀ t : ℝ, (Z.N t (t + 1) : ℝ) ≤ A₀ * Real.log (|t| + 3)
```

instantiated for `ξ′` by `xiDeriv_rvM_main` (`Zeta23/XiPrime/ZeroCount.lean:149-151`):

```lean
theorem xiDeriv_rvM_main (hF2 : XiDerivZerosInStrip) (hs : XiDerivSeam) :
    ∃ C T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T →
      |((xiDerivZeros hF2 hs).N T (2 * T) : ℝ) - T / (2 * Real.pi) * ell1 T| ≤ C * Real.log T
```

and `xiDeriv_local_count` (`Zeta23/XiPrime/ZeroCount/Landau.lean:79-80`):

```lean
theorem xiDeriv_local_count : ∃ A₀ : ℝ, 1 ≤ A₀ ∧ ∀ t : ℝ,
    ((xiDerivZeros hF2 hs).N t (t + 1) : ℝ) ≤ A₀ * Real.log (|t| + 3)
```

The local count is height-local and is used unchanged. The main term is
rebuilt below from the tree's own intermediates, all of which are stated for
arbitrary heights `T₁ ≤ T₂`:

`Zeta23/XiPrime/ZeroCount/Contour.lean:28`: `def GoodHeight (T : ℝ) : Prop := ∀ ρ : ℂ, IsXiDerivZero ρ → ρ.im ≠ T`

`Zeta23/XiPrime/ZeroCount/Contour.lean:31`:

```lean
theorem exists_goodHeight (hs : XiDerivSeam) (a : ℝ) : ∃ T ∈ Icc a (a + 1), GoodHeight T
```

`Zeta23/XiPrime/ZeroCount/Contour.lean:142-145`:

```lean
theorem Ncount_eq_im_halfContour (hF2 : XiDerivZerosInStrip) (hs : XiDerivSeam) {T₁ T₂ : ℝ}
    (h12 : T₁ ≤ T₂) (hg₁ : GoodHeight T₁) (hg₂ : GoodHeight T₂) :
    (Ncount T₁ T₂ : ℝ)
      = (1 / Real.pi) * (Zeta23.RvM.halfContour (logDeriv xiDeriv) T₁ T₂).im
```

`Zeta23/XiPrime/ZeroCount.lean:43-46`:

```lean
theorem halfContour_xiDeriv_split (hF2 : XiDerivZerosInStrip) {T₁ T₂ : ℝ}
    (hg₁ : GoodHeight T₁) (hg₂ : GoodHeight T₂) :
    halfContour (logDeriv xiDeriv) T₁ T₂ =
      halfContour (logDeriv Complex.Gammaℝ) T₁ T₂ + halfContour (logDeriv Yfn) T₁ T₂
```

`Zeta23/XiPrime/ZeroCount.lean:111-114`:

```lean
theorem halfContour_Yfn_bound : ∃ C T₀ : ℝ, 0 < C ∧ 4 ≤ T₀ ∧ ∀ T₁ T₂ : ℝ, T₀ ≤ T₁ → T₁ ≤ T₂ →
    GoodHeight T₁ → GoodHeight T₂ →
    |(halfContour (logDeriv Yfn) T₁ T₂).im|
      ≤ C * Real.log (|T₁| + 3) + 3 * Real.pi + C * Real.log (|T₂| + 3)
```

`Zeta23/RvM/GammaSide.lean:121`:

```lean
theorem gamma_side {T₁ T₂ : ℝ} (_h0 : 0 < T₁) (_h0' : 0 < T₂) :
    (1 / Real.pi) * (halfContour (logDeriv Complex.Gammaℝ) T₁ T₂).im = ∫ t in T₁..T₂, mu t
```

`Zeta23/RvM/GammaSide.lean:165-166`:

```lean
theorem mu_le_log (hΓ : Zeta23.GammaFacts) : ∃ C : ℝ, 0 < C ∧ ∀ τ : ℝ, 1 ≤ τ →
    |mu τ| ≤ C * Real.log (τ + 3)
```

and Stirling for `μ` (`Zeta23/Hypotheses.lean:131-132`, a field of
`GammaFacts`, proved by `Zeta23.gammaFacts`):

```lean
  stirling : ∃ C : ℝ, ∀ τ : ℝ, 1 ≤ |τ| →
    |mu τ - (1 / (2 * Real.pi)) * Real.log (|τ| / (2 * Real.pi))| ≤ C / τ ^ 2
```

The dyadic μ-integrals the tree states (`Zeta23/Hypotheses.lean:134-138`):

```lean
  int_mu : ∃ C T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T →
    |(∫ τ in T..(2 * T), mu τ) - T * ell1 T / (2 * Real.pi)| ≤ C / T
  int_mu_sq : ∃ C T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T →
    |(∫ τ in T..(2 * T), mu τ ^ 2) - T * ell1 T ^ 2 / (4 * Real.pi ^ 2)|
      ≤ C * (T * ell1 T ^ 2 / (4 * Real.pi ^ 2)) / l T ^ 2
```

are replaced by Lemma 2.2. All of the above: `[KERNEL-CHECKED, DYADIC]`
(height-local statements used unchanged, or dyadic statements replaced by the
lemmas below).

### Lemma 2.1 (the window mean of the log). `[NEW STATEMENT, PROOF WRITTEN HERE]`

For `T > 0` and `0 < H ≤ T`, with `ℓ_H := (1/H) ∫_T^{T+H} log(τ/2π) dτ`:

```
(i)   l ≤ ℓ_H ≤ l + log(1 + H/T) ≤ l + H/T;
(ii)  ∫_T^{T+H} log(τ/2π)² dτ = H ℓ_H² + E₂,   0 ≤ E₂ ≤ H (H/T)²;
(iii) L/ℓ_H → λ as T → ∞ when H = T^θ, θ < 1.
```

*Proof.* (i): `log(τ/2π)` is increasing, so its mean over `[T, T+H]` lies
between its values at the endpoints, `l` and `l + log(1 + H/T)`; and
`log(1+x) ≤ x`. (ii): write `log(τ/2π) = ℓ_H + r(τ)` with `∫_T^{T+H} r = 0` by
definition of `ℓ_H`; then `∫ log² = H ℓ_H² + ∫ r²`, and `|r(τ)| ≤ log(1+H/T)
≤ H/T` by (i). (iii): `L/ℓ_H = λ l/(l + O(H/T))` and `H/T = T^{θ−1} → 0`. ∎

This is the exact analogue of `ell1`: the tree's `ℓ₁ = l + 2 log 2 − 1` is
`(1/T)∫_T^{2T} log(τ/2π) dτ` (`Zeta23/GammaFacts/IntMu.lean:28-30`,
`integral_main_eq`). Wang's (1.2) uses `log T` in place of `ℓ_H`; the two
differ by `O(1 + H/T)`, i.e. by `O(H)` after multiplication by `H/2π`, which
is Wang's `O(H)`.

### Lemma 2.2 (μ-integrals over a short window). `[NEW STATEMENT, PROOF WRITTEN HERE]`

There are absolute `C, T₀` such that for `T ≥ T₀` and `1 ≤ H ≤ T`:

```
(i)  |∫_T^{T+H} μ − H ℓ_H/(2π)| ≤ C/T;
(ii) |∫_T^{T+H} μ² − H ℓ_H²/(4π²)| ≤ C · (H ℓ_H²/(4π²)) / l².
```

*Proof.* Let `m(τ) = (1/2π) log(τ/2π)` and `r = μ − m`, so `|r(τ)| ≤ C_s/τ² ≤
C_s/T²` on `[T, T+H]` by Stirling. (i): `∫ μ = ∫ m + ∫ r = H ℓ_H/2π + O(C_s H/T²)`
and `H/T² ≤ 1/T`. (ii): `∫ μ² = ∫ m² + 2∫ m r + ∫ r²`. By Lemma 2.1(ii),
`∫ m² = (H ℓ_H² + E₂)/(4π²)` with `0 ≤ E₂ ≤ H³/T²`. Next
`|2∫ m r| ≤ 2 · (l + 1)/(2π) · H · C_s/T² ≤ C H l/T²` and
`∫ r² ≤ C_s² H/T⁴`. Divide by the main term `H ℓ_H²/4π² ≥ H l²/4π²`:

```
E₂/(H l²) ≤ H²/(T² l²) ≤ 1/l²,   (H l/T²)/(H l²) = 1/(T l) ≤ 1/l²,   (H/T⁴)/(H l²) ≤ 1/l²
```

for `T ≥ T₀` (using `H ≤ T` and `l ≥ 1`). ∎

Both statements have the shape of `int_mu` and `int_mu_sq` with
`T ↦ H`, `ℓ₁ ↦ ℓ_H`; the relative error in (ii) is `O(1/l²)` for every
`1 ≤ H ≤ T`, not only for `H = T^θ`.

### Lemma 2.3 (the short-window count, contour form). `[NEW STATEMENT, PROOF WRITTEN HERE]`

(Re-audit, condition 3.) The statement the prime side consumes is not Wang's
(1.2). `prop_trace` (`Zeta23/PrimeSideA.lean:300-304`, quoted in 6.1) and its
coefficient-generic form `prop_trace_W` (`Zeta23/XiPrime/PrimeSide/Trace.lean:184-188`):

```lean
theorem prop_trace_W (cϱ lam : ℝ) (hΓ : Zeta23.GammaFacts) (hlam : 0 < lam ∧ lam ≤ 1)
    (cPi A : ℝ) :
    ∃ C T₀ : ℝ, ∀ (p : Setting) (F : LocalFun) (c : ℕ → ℂ), p.lam = lam → T₀ ≤ p.T →
      LocalHypsCore cϱ p F → c 1 = 0 → ∀ N : ℝ, |N - p.T * p.ell1 / (2 * π)| ≤ A * p.l →
      |trGtW cPi c p F - F.a * p.L * N| ≤ C * (p.L * Real.sqrt p.X + p.L * S1 c p.X)
```

take any real `N` within `A l` of the `μ`-main term `T ℓ₁/2π`, and the
assembly feeds them `N = N(T, 2T)` through `rvm_evBound`
(`Zeta23/XiPrime/PrimeSide/Moments.lean:110`, from `RiemannVonMangoldt.main`).
So the count must be placed within `O(log T)` of the `μ`-integral first.

**Statement.** There are `C, T₀` such that for `T ≥ T₀` and `1 ≤ H ≤ T`,

```
|N_{ξ′}(T, T+H) − ∫_T^{T+H} μ| ≤ C log T.
```

*Proof.* Take `T₀ ≥ max(T_Y + 1, 16)` where `T_Y` is the threshold of
`halfContour_Yfn_bound`. Let `A₀` be the local-count constant, `C_Y` the
`Yfn` constant, `C_M` the `mu_le_log` constant.

*Good heights.* By `exists_goodHeight` there are `T₁ ∈ [T − 1, T]` and
`T₂ ∈ [T + H, T + H + 1]` with `GoodHeight T₁`, `GoodHeight T₂`. Then
`T₀ − 1 ≤ T₁ ≤ T₂`.

*Additivity and the unit strips.* `N(T₁, T₂) = N(T₁, T) + N(T, T+H) + N(T+H, T₂)`
(`ZeroConfig.N_add`, interval-additivity of a finite sum). Since
`(T₁, T] ⊂ (T₁, T₁ + 1]` and `(T+H, T₂] ⊂ (T+H, T+H+1]`, the local count gives
`N(T₁, T) ≤ A₀ log(T₁ + 3) ≤ 2 A₀ log T` and
`N(T+H, T₂) ≤ A₀ log(T+H+3) ≤ 2 A₀ log T`, using `x + 3 ≤ T²` for
`x ∈ {T₁, T+H}` and `T ≥ 4`.

*The argument principle.* By `Ncount_eq_im_halfContour`,
`halfContour_xiDeriv_split` and `gamma_side` (with `0 < T₁`),

```
N(T₁, T₂) = ∫_{T₁}^{T₂} μ + R,   |R| ≤ (1/π)(C_Y log(T₁+3) + 3π + C_Y log(T₂+3)) ≤ (4 C_Y/π) log T + 3.
```

*The μ-integral.* `∫_{T₁}^{T₂} μ = ∫_T^{T+H} μ + ∫_{T₁}^{T} μ + ∫_{T+H}^{T₂} μ`; the
last two are over intervals of length at most 1 on which `|μ| ≤ C_M log(2T+4)
≤ 4 C_M log T` (`mu_le_log`, `T ≥ 4`).

*Collect.* `|N(T, T+H) − ∫_T^{T+H} μ| ≤ (4A₀ + 4C_Y/π + 8C_M) log T + 3 ≤ C log T`
for `T ≥ T₀`. ∎

This is `rvM_main_of` (`Zeta23/XiPrime/ZeroCount/GenericRvM.lean:118-126`)
with the upper good height taken in `[T+H, T+H+1]` instead of `[2T, 2T+1]` and
with `int_mu` *not* applied; every other line of that proof is height-local
and unchanged. The contour chain gives exactly this statement, with no
`H`-dependent error at all.

### Corollary 2.3′ (the two count forms). `[NEW STATEMENT, PROOF WRITTEN HERE]`

For `T ≥ T₀`, `1 ≤ H ≤ T`:

```
(i)  |N_{ξ′}(T, T+H) − H ℓ_H/(2π)| ≤ C log T           (the form prop_trace consumes, with A = C);
(ii) N_{ξ′}(T, T+H) = (H log T)/(2π) + O(H + log T)      (Wang (1.2)).
```

*Proof.* (i): Lemma 2.3 and Lemma 2.2(i), `C/T ≤ log T`. (ii): (i) and
Lemma 2.1(i), `H ℓ_H/2π = H l/2π + O(H²/T) = H log T/2π − H log(2π)/2π + O(H)`
since `H²/T ≤ H`. ∎

The `H²/T` (Wang's `O(H)`) lives entirely in the passage from `ℓ_H` to
`log T`, i.e. in the `μ`-main term; the count error is `O(log T)` in both
forms. It is (i), not (ii), that replaces `rvm_evBound` in 6.6.

### Corollary 2.4 (comparison facts). `[NEW STATEMENT, PROOF WRITTEN HERE]`

For `H = T^θ`, `0 < θ < 1`, eventually in `T`:

```
(a) H l/(4π) ≤ N_H ≤ H l;           (b) N_H → ∞;
(c) log T = o(N_H);                  (d) T^β l = o(N_H)  iff  β < θ;
(e) X l^k = o(N_H) for every fixed k  iff  λ < θ;    √X l^k = o(N_H)  iff  λ/2 < θ;
(f) H T^{−δ} l^k = o(N_H) for every δ > 0 and fixed k;
(g) N_H / (H ℓ_H/2π) → 1.
```

*Proof.* (a): from Corollary 2.3′(i) and `ℓ_H ≥ l`, `N_H ≥ H l/2π − C log T ≥ H l/4π`
once `H ≥ 4πC log T/l`, which holds since `H = T^θ → ∞` and `log T/l → 1`; the
upper bound from `ℓ_H ≤ l + 1`. (b) and (c) follow from (a). (d), (e), (f):
compare exponents, `X = (T/2π)^λ`, `H = T^θ`, powers of `l` and `log T` being
`T^{o(1)}`. (g): Corollary 2.3′(i) divided by `H ℓ_H/2π ≥ H l/2π`. ∎

(Re-audit, ordering.) Item (a) is consumed in §5 four times, at the lines
where the tree closes with `gcongr` against `T l/(4π) ≤ N(T, 2T)`
(`Zeta23/XiPrime/Transfer.lean:378, 425, 736, 784`); the localized closes are
against `H l/(4π) ≤ N_H`. This is why §2 precedes §5.

These replace, in order, `eventually_N_ge` and `eventually_N_le`
(`Zeta23/Assembly.lean:713-714` and following), `tendsto_N_atTop`,
`isLittleO_log_Tl` (`:780`), `isLittleO_sqrt_mul_l_Tl` (`:786`),
`isLittleO_N_of_isLittleO_Tl` (`:760-761`), and `tendsto_lpow_mul_X_div`
(`Zeta23/XiPrime/Transfer.lean:511-531`, which is `l^n X/T → 0` for `λ < 1`;
here `l^n X/H → 0` for `λ < θ`). The dyadic versions are `[KERNEL-CHECKED,
DYADIC]` and are not used; the short-window versions above are used
throughout.

---

## 3. The zero side (Wang §2 Proposition 2.1 and §3; audit step 3)

The zero side produces Lemma R: a lower bound for the simple on-line count in
`I_H` in terms of the two traces of the Gram matrix. Wang reaches the same
point differently (Lamzouri's Proposition 2.1 applied to the multiset of
rescaled zeros, then removal of the weight `w` in §3); the tree's route is
Lamzouri's inequality in Gram-matrix form, and it never needs the weight `w`,
because the Gram kernel `φ̂` is entire. Nothing in this section is arithmetic.

### 3a. The block inequality. `[KERNEL-CHECKED, DYADIC]`

`Zeta23/ZeroSide/Mult.lean:185-187`:

```lean
theorem hatAz_mult2 (hconj : PhiHatConj T P) (hreal : PhiHatReal T P) (hPois : PoissonSq T P)
    (hc : 0 < P.a T * P.L T ^ 2) :
    4 * rtrace (P.hat T (Z.Az P T)) - frobSq (P.hat T (Z.Az P T)) - 2 * (Z.NIprime T : ℝ) ≤ (Z.s1 T : ℝ)
```

and `hatAz_mult3` (`:193-195`): `6 tr Â − ‖Â‖_F² − 3 N(I′) ≤ 2 N_d(I′)`. Here
`Â = A/(aL²)` with `A_kl = Σ_{ρ ∈ 𝒵(I′)} m_ρ φ̂(γ_ρ − τ_k) φ̂(γ_ρ − τ_l)` the Gram
matrix of the zeros with ordinate in the padded window (`ZeroConfig.Az`,
`ZIprime`, `Zeta23/Defs.lean:307-316`), `s₁` the number of simple on-line
zeros in `I′`, `N(I′)` the count in `I′` with multiplicity, and `N_d(I′)` the
distinct count.

The hypotheses are: `φ̂(z̄) = conj φ̂(z)` (`PhiHatConj`), `φ̂` real on `ℝ`
(`PhiHatReal`), and the Poisson identity (`Zeta23/ZeroSide.lean:804-805`):

```lean
abbrev PoissonSq : Prop :=
  ∀ γ : ℝ, HasSum (fun k : ℤ => P.phiHatR T (γ - P.tau T k) ^ 2) (P.a T * P.L T ^ 2)
```

**Localized statement.** With `𝒵(I′_H)` the zeros with ordinate in
`I′_H = (T − D₀, T + H + D₀]`, `A_H` their Gram matrix on the short grid, and
`s_{1,H}`, `N(I′_H)`, `N_d(I′_H)` the corresponding counts:

```
4 tr Â_H − ‖Â_H‖_F² − 2 N(I′_H) ≤ s_{1,H},     6 tr Â_H − ‖Â_H‖_F² − 3 N(I′_H) ≤ 2 N_d(I′_H).
```

**Why it holds unchanged.** The proof of `hatAz_mult2` is one line: it
rewrites `Â = P + Q` and applies `ZeroBlockData.mult_two` to `mkData Z T v hv`
(`Zeta23/ZeroSide.lean:633-642`), a statement about an abstract
`ZeroBlockData` (`:161-173`): a finite index set of distinct zeros with
multiplicities `m ≥ 1`, evaluation vectors `v_ρ = (φ̂(γ_ρ − τ_k))_k`, and an
involution `σ` (reflection `ρ ↦ 1 − ρ̄`) with `m ∘ σ = m` and `v ∘ σ = conj v`.
The only input from the window is that it is closed under reflection (it is:
reflection preserves the imaginary part, so any height window is closed) and
that it is finite (`finite_window`). The only input from the grid is the
Poisson identity through `sum_normSq_v_le`: `Σ_{k<d} φ̂(γ − τ_k)² ≤ aL²` for
real `γ`, which is a partial sum of a series of nonnegative terms with sum
`aL²`, hence holds for every finite index range, in particular `k < d_H`. So
the statement holds for `𝒵(I′_H)` and the short grid with the same proof.
This is the audit's item P8 and the reason `ZeroSide.lean` is in its
"untouched" list.

*Sanity check against Lamzouri (2.4).* With `tr Â ≈ N(I′)` and
`‖Â‖² ≈ κ N(I′)` (§6), the first inequality reads
`s₁ ≥ (4 − κ − 2) N(I′) = (2 − κ) N(I′)`, which is Lamzouri's
`Σ_{simple real} 1 ≥ 2|𝒵| − Σ K(z−s)²` with `Σ K² ↔ ‖Â‖²` and
`2|𝒵| ↔ 4 tr Â − 2N`. The second reads
`N_d(I′) ≥ (3 − κ/2 − 3/2) N = (3/2 − κ/2) N`, Lamzouri's (2.5).

### 3b. The tail: zeros outside the padded window.

The tree's tail package (`Zeta23/Tail.lean:57`):

```lean
def theta0 (A₀ K T : ℝ) : ℝ := 4 * A₀ * K ^ 2 * Real.log (4 * T) / T
```

with `K = e^{L/4} C₁ = X^{1/4} C₁` and `D₀² = T` in the denominator, and
(`Zeta23/Tail.lean:651-659`, hypotheses abbreviated, conclusion verbatim):

```lean
theorem eventually_tailInputs (Z : ZeroConfig) (P : Params) (hP : P.Valid) {A₀ : ℝ}
    (hA₀ : 1 ≤ A₀) (hloc : ∀ t : ℝ, (Z.N t (t + 1) : ℝ) ≤ A₀ * Real.log (|t| + 3))
    (C₁ : ℝ → ℝ) (hC₁ : ∀ T, 0 ≤ C₁ T)
    (hdecay : ∀ᶠ T in atTop, ∀ (r y : ℝ), |y| ≤ 1 / 2 → (r : ℂ) - I * y ≠ 0 →
      ‖P.phiHat T (r - I * y)‖ ≤ Real.exp (P.L T / 4) * C₁ T / ‖(r : ℂ) - I * y‖ ^ 2)
    (ha : ∀ᶠ T in atTop, 0 < P.a T)
    (hconj : ∀ᶠ T in atTop, ∀ z : ℂ,
      P.phiHat T ((starRingEnd ℂ) z) = (starRingEnd ℂ) (P.phiHat T z)) :
    ∀ᶠ T in atTop, Assembly.TailInputs Z P T (theta0 A₀ (Real.exp (P.L T / 4) * C₁ T) T)
```

where `TailInputs θ₀` (`Zeta23/Assembly/Inputs.lean`) packages: every
eigenvalue of `Ẽ = E/L` is at most `θ₀` in absolute value, and there is
`B ≥ 0` with `|tr Ê| ≤ B`, `‖Ê‖_F² ≤ B²`, `B ≤ θ₀/(aL)`. The decay hypothesis
is a theorem of the tree (`Zeta23/Taper/Params.lean:106-108`,
`norm_phiHat_sub_I_mul_le`, for `2w ≤ L`); the two leaf lemmas are:

`Zeta23/Tail/Count.lean:294-297` (with `distI T γ = max 0 (max (T − γ) (γ − 2T))`,
`InTail T γ ↔ γ ≤ T − √T ∨ 2T + √T < γ`, `T₀ = 300`, `Zeta23/Tail/Basic.lean:18,36,53`):

```lean
theorem tail_count_sum_le {ι : Type*} {γ : ι → ℝ} {m : ι → ℕ} {A₀ T : ℝ}
    (hN : LocalCount γ m A₀) (hT : T₀ ≤ T) (s : Finset ι) (hs : ∀ ρ ∈ s, InTail T (γ ρ)) :
    ∑ ρ ∈ s, (m ρ : ℝ) * ((distI T (γ ρ)) ^ 3)⁻¹ ≤ 4 * A₀ * Real.log (4 * T) / T
```

and `Zeta23/Tail/Grid.lean` (the pure inequality
`Σ_{k<d} |γ − τ_k|^{−4} ≤ L D^{−3}` for `D = dist(γ, I) ≥ 1`, `L ≥ 2`, grid
points in `I` with spacing `h`).

#### Lemma 3.2 (tail count sum, short window). `[NEW STATEMENT, PROOF WRITTEN HERE]`

Let `2 ≤ D₀ ≤ √T`, `T ≥ 16`, `H ≤ T`. For every finite set `s` of zeros with
`γ_ρ ∉ I′_H` (i.e. `γ ≤ T − D₀` or `γ > T + H + D₀`), writing
`D(γ) = dist(γ, I_H) ≥ D₀`,

```
Σ_{ρ ∈ s} m_ρ D(γ_ρ)^{−3} ≤ 6 A₀ log(4T) / D₀².
```

*Proof* (Wang Lemma 2.4's partition, with cubes in place of squares).

*Above the window.* Group the zeros with `γ > T + H + D₀` by
`γ ∈ (T+H+D₀+j, T+H+D₀+j+1]`, `j ≥ 0`. In group `j`, `D ≥ D₀ + j` and, by the
two-sided local count, `Σ m_ρ ≤ A₀ log(T+H+D₀+j+4)`. For `j ≤ T`:
`T+H+D₀+j+4 ≤ 3T + √T + 4 ≤ 4T` (as `T ≥ 16`), so the group sum is at most
`A₀ log(4T) (D₀+j)^{−3}`, and `Σ_{j≥0}(D₀+j)^{−3} ≤ D₀^{−3} + ∫_{D₀}^∞ x^{−3}dx
= D₀^{−3} + 1/(2D₀²) ≤ D₀^{−2}` since `D₀ ≥ 2`. For `j > T`: `(D₀+j)^{−3} ≤ j^{−3}`
and `T+H+D₀+j+4 ≤ 4j`, so the sum is at most
`A₀ Σ_{j>T} log(4j) j^{−3} ≤ A₀ ∫_T^∞ log(4x) x^{−3} dx = A₀ (log(4T)/(2T²) + 1/(4T²))
≤ A₀ log(4T)/T² ≤ A₀ log(4T)/D₀²`. Total above: `≤ 2A₀ log(4T)/D₀²`.

*Below the window, positive ordinate.* Group `0 < γ ≤ T − D₀` by
`γ ∈ (T−D₀−j−1, T−D₀−j]`, `j ≥ 0`; `D ≥ D₀ + j`, count `≤ A₀ log(T+3) ≤ A₀ log(4T)`;
the same sum gives `≤ A₀ log(4T)/D₀²`.

*Nonpositive ordinate.* Group `γ ∈ (−j−1, −j]`, `j ≥ 0`; `D ≥ T + j`; the
two-sided local count at `t = −j−1` gives `≤ A₀ log(j+4)`. For `j ≤ T`,
`log(j+4) ≤ log(4T)` and `Σ_j (T+j)^{−3} ≤ T^{−2} ≤ D₀^{−2}`; for `j > T` the
bound above applies. Total: `≤ 2A₀ log(4T)/D₀²`.

Adding: `≤ 5A₀ log(4T)/D₀² ≤ 6A₀ log(4T)/D₀²`. ∎

The upper endpoint `T + H` enters only through `T+H+D₀+j+4 ≤ 4T`, an upper
bound; the length `H` never enters. The tree's constant `4` (for `D₀ = √T`) is
not load-bearing, since only `θ₀ → 0` is consumed.

#### Lemma 3.3 (grid sum). `[KERNEL-CHECKED, DYADIC]` (used unchanged)

For `γ ∈ ℂ` with `D = dist(Re γ, I_H) ≥ 1`, `L ≥ 2`:
`Σ_{0≤k<d_H} |γ − τ_k|^{−4} ≤ L D^{−3}`.

The tree's `Tail/Grid.lean` proves the real-variable inequality for any points
`τ_0 < … < τ_{d−1}` lying in the interval, spaced by `h = 2π/L`, at distance
at least `D` from `γ`: the sum is at most `D^{−4} + h^{−1}∫_D^∞ x^{−4}dx =
D^{−4} + (L/2π) D^{−3}/3 ≤ L D^{−3}`. The short grid `τ_0 < … < τ_{d_H − 1}` lies
in `[T, T+H)` (because `d_H h ≤ H`), so `|Re γ − τ_k| ≥ D` for every `k`, and
`|γ − τ_k| ≥ |Re γ − τ_k|`. Fewer points, same bound.

#### Proposition 3.4 (prop:tail, short window). `[NEW STATEMENT, PROOF WRITTEN HERE]`

Let `E_H = G_H − A_H` (the Gram matrix of the zeros with `γ_ρ ∉ I′_H`, on the
short grid) and

```
θ₀ := 6 A₀ C₁² X^{1/2} log(4T) / D₀².
```

Eventually in `T`: `E_H` is Hermitian, every eigenvalue of `Ẽ_H = E_H/L` is at
most `θ₀` in absolute value, and `B := ‖Ê_H‖₁ ≤ θ₀/(aL)` satisfies
`|tr Ê_H| ≤ B`, `‖Ê_H‖_F ≤ B`. Moreover `θ₀ ≤ C l T^{λ/2 − 2β}`, so `B → 0`
under `β > λ/4`.

*Proof.* Every zero `ρ` has `|Im γ_ρ| = |Re ρ − 1/2| < 1/2` (strip fact), so by
the decay hypothesis, for real `r`,
`|φ̂(γ_ρ − τ_k)| ≤ X^{1/4} C₁ / |γ_ρ − τ_k|²`. Let `u_ρ = (φ̂(γ_ρ − τ_k))_{k<d_H}`.
Then by Lemma 3.3, for `ρ` in the tail (`D ≥ D₀ ≥ 1`),

```
‖u_ρ‖₂² ≤ C₁² X^{1/2} Σ_k |γ_ρ − τ_k|^{−4} ≤ C₁² X^{1/2} L D(γ_ρ)^{−3}.
```

`E_H = Σ_{tail} m_ρ u_ρ u_ρ^⊤` (a sum of rank-one complex-symmetric matrices;
pairing `ρ` with `1 − ρ̄`, whose vector is `conj u_ρ`, makes the sum Hermitian,
which is `hconj` plus the seam's reflection facts). The series converges
absolutely by Lemma 3.2. Operator and trace norms of `u u^⊤` both equal
`‖u‖₂²`, so by the triangle inequality and Lemma 3.2,

```
‖Ẽ_H‖_op ≤ ‖Ẽ_H‖₁ ≤ L^{−1} Σ_{tail} m_ρ ‖u_ρ‖² ≤ C₁² X^{1/2} · 6A₀ log(4T)/D₀² = θ₀.
```

Passing to hat units divides by `a`: `B := ‖Ê_H‖₁ ≤ θ₀/(aL)`, and
`|tr M| ≤ ‖M‖₁`, `‖M‖_F ≤ ‖M‖₁` for any matrix. Finally `C₁ ≤ 2R` with
`R = ‖ϱ″‖₁` (`Params.C1_le`), `X^{1/2} ≤ T^{λ/2}`, `log(4T) ≤ 2l` for `T ≥ 300`
(`log_four_mul_le_two_mul_l`, `Zeta23/Tail.lean:65`), so
`θ₀ ≤ 48 A₀ R² l T^{λ/2 − 2β}`, which is the tree's `theta0_le`
(`Zeta23/Tail.lean:82-84`, `32 A₀ R² l T^{λ/2 − 1}` for `β = 1/2`) with the
constant `6` in place of `4`. Since `a ≥ 1/2` eventually (`Params.half_le_a`)
and `L → ∞`, `B ≤ 2θ₀/L → 0`. ∎

> Error line. Size `B = O(l T^{λ/2 − 2β}/L)`; absorbed against the constant 1
> (only `B → 0` is consumed, in 7.2); requires `β > λ/4`, which condition 2
> arranges. Height-only: `H` does not appear.

### 3c. The end strips. `[NEW STATEMENT, PROOF WRITTEN HERE]`

The tree (`Zeta23/Tail.lean:593-595`, `677-679`):

```lean
theorem NII_le (Z : ZeroConfig) {A₀ T : ℝ} (hA₀ : 1 ≤ A₀)
    (hloc : ∀ t : ℝ, (Z.N t (t + 1) : ℝ) ≤ A₀ * Real.log (|t| + 3)) (hT : T₀ ≤ T) :
    (Assembly.NII Z T : ℝ) ≤ 3 * A₀ * Real.sqrt T * Real.log (4 * T)
theorem eventually_NII_le (Z : ZeroConfig) {A₀ : ℝ} (hA₀ : 1 ≤ A₀)
    (hloc : ∀ t : ℝ, (Z.N t (t + 1) : ℝ) ≤ A₀ * Real.log (|t| + 3)) :
    ∃ C : ℝ, ∀ᶠ T in atTop, (Assembly.NII Z T : ℝ) ≤ C * Real.sqrt T * l T
```

#### Lemma 3.5. For `T ≥ 300`, `H ≤ T`, `2 ≤ D₀ ≤ √T`:

```
NII_H = N(T − D₀, T) + N(T + H, T + H + D₀) ≤ 6 A₀ D₀ l,   hence  NII_H = o(N_H)  iff  β < θ.
```

*Proof.* `(T − D₀, T]` is covered by `⌈D₀⌉ ≤ D₀ + 1 ≤ 3D₀/2` unit windows
`(t, t+1]` with `t ≥ T − D₀ − 1 ≥ 0`, each counting at most
`A₀ log(t+4) ≤ A₀ log(4T) ≤ 2A₀ l`; likewise `(T+H, T+H+D₀]` with
`t + 4 ≤ T + H + D₀ + 4 ≤ 4T`. So `NII_H ≤ 2 · (3D₀/2) · 2A₀ l = 6A₀ D₀ l`.
The second clause is Corollary 2.4(d). ∎

> Error line. Size `NII_H = O(T^β l)`; absorbed against `H l` (in 7.2, as
> `3 NII_H ≤ δ N_H`); requires `β < θ`. This is the audit's `c = 1/2` entry
> when `β = 1/2`, i.e. condition 2.

### 3d. Lemma R on the short window. `[NEW STATEMENT, PROOF WRITTEN HERE]`

The tree (`Zeta23/Assembly/SeamMult.lean`, `seamA_mult2`, statement lines 46-53):

```lean
theorem seamA_mult2 (hT : 0 ≤ T) (hconj : ZeroSide.PhiHatConj T P)
    (hreal : ZeroSide.PhiHatReal T P) (hPois : ZeroSide.PoissonSq T P)
    {θ₀ : ℝ} (hTl : TailInputs Z P T θ₀) (ha : 0 < P.a T) (hL : 0 < P.L T) :
    4 * rtrace (P.hat T (Z.Gz P T)) - frobSq (P.hat T (Z.Gz P T)) - 2 * (Z.N T (2 * T) : ℝ)
      - 3 * (NII Z T : ℝ)
      - θ₀ / (P.a T * P.L T)
          * (4 + 2 * Real.sqrt (frobSq (P.hat T (Z.Gz P T))) + θ₀ / (P.a T * P.L T))
      ≤ Z.N0s T (2 * T)
```

and `seamA_mult3` (`:69-75`) with `6, 3, 5, 6` in place of `4, 2, 3, 4` and
conclusion `≤ 2 N_d(T, 2T)`. Its proof uses three facts besides 3a and 3b:
`s1_le` (`Zeta23/Assembly.lean:986`: `s₁ ≤ N0s(T, 2T) + NII`), `NIprime_eq`
(`:943`: `N(I′) = N(T, 2T) + NII`), and the perturbation lemma
`ctr_sub_frobSq_perturb` (`SeamMult.lean`, quoted in 7.2).

#### Proposition 3.6 (Lemma R, short window). With `B` from 3.4, eventually in `T`:

```
4 tr Ĝ_H − ‖Ĝ_H‖_F² − 2 N_H − 3 NII_H − B (4 + 2 √‖Ĝ_H‖_F² + B)  ≤  N^s_{0,ξ′}(I_H),
6 tr Ĝ_H − ‖Ĝ_H‖_F² − 3 N_H − 5 NII_H − B (6 + 2 √‖Ĝ_H‖_F² + B)  ≤  2 N_{d,ξ′}(I_H).
```

*Proof.* `Ĝ_H = Â_H + Ê_H`. The perturbation lemma (pure matrix algebra, for
any `c ≥ 0` and any `B ≥ 0` with `|tr Ê| ≤ B`, `‖Ê‖_F ≤ B`):

```
c tr Ĝ − ‖Ĝ‖_F² − B(c + 2√‖Ĝ‖_F² + B) ≤ c tr Â − ‖Â‖_F²,
```

whose proof is `tr Â = tr Ĝ − tr Ê` and
`‖Â‖_F ≤ ‖Ĝ‖_F + ‖Ê‖_F ≤ ‖Ĝ‖_F + B`, then squaring. With `c = 4` and 3a:
`≤ s_{1,H} + 2N(I′_H)`. Now `N(I′_H) = N_H + NII_H` (interval additivity at the
two padding endpoints) and `s_{1,H} ≤ N^s_{0,ξ′}(I_H) + NII_H` (a simple
on-line zero of `I′_H` is in `I_H` or in one of the two strips). Substitute:
`≤ N^s_{0,ξ′}(I_H) + 2N_H + 3NII_H`. Rearranging gives the first line; the
second is identical with `c = 6`, `hatAz_mult3`, and
`N_d(I′_H) ≤ N_{d,ξ′}(I_H) + NII_H`. ∎

No arithmetic input; the only `H`-dependence is through the sets, and every
use of the range is an identity or an upper bound. This is Wang's (3.7) in
Gram form.

---

## 4. The explicit formula (Wang (2.7)-(2.9), BGSTB Lemma 1; audit step 4)

`Zeta23/XiPrime/Statement.lean:204-208`:

```lean
def XiEF (Z : ZeroConfig) (Pf : ℝ → Params) : Prop :=
  ∃ C δ T₀ : ℝ, 0 < δ ∧ ∀ T : ℝ, T₀ ≤ T → ∀ k l : Fin ((Pf T).d T),
    Summable (fun ρ : Z.carrier => Z.Gsummand (Pf T) T k l ρ) ∧
    ‖Z.Gz (Pf T) T k l - ((Pf T).Gentry1 T k l : ℂ)‖
      ≤ C * T ^ (-δ) * (1 / max 1 (((Pf T).tau T k - (Pf T).tau T l) ^ 2) + 1 / T)
```

proved for the xi-prime configuration by `xiEF_xiDerivZeros`
(`Zeta23/XiPrime/ExplicitFormula/Main.lean:120-122`):

```lean
theorem xiEF_xiDerivZeros (hs : XiDerivSeam) (Pf : ℝ → Params) (hPf : FamilyHyps Pf) :
    XiEF (xiDerivZeros xiDerivZerosInStrip_holds hs) Pf
```

with `δ = (1 − 3λ/4)/2 > 0` (`Zeta23/XiPrime/ExplicitFormula/FamilyFacts.lean:91-98`,
`pow_log_absorb`). The range enters this development in exactly four places
(audit P27-P30): `tau_mem` (`XiEFAssembly.lean:83`; `GramBridge.lean:206`,
`tau_mem`; `:233`, `tauStar_mem`),

```lean
theorem tau_mem (hL : 0 < P.L T) (hT : 0 < T) (k : Fin (P.d T)) :
    T ≤ P.tau T k ∧ P.tau T k ≤ 2 * T
```

`tau_mem_Icc` (`TestWeight.lean:879-880`, same statement), `far_subset`
(`TestWeight.lean:900-901`):

```lean
theorem far_subset {τk τl T : ℝ} (hk1 : T ≤ τk) (hk2 : τk ≤ 2 * T) (hl1 : T ≤ τl) (hl2 : τl ≤ 2 * T) :
    {t : ℝ | 3 * ((τk + τl) / 2) / 4 ≤ |t - (τk + τl) / 2|} ⊆ {t : ℝ | T / 4 ≤ |t - τk|}
```

and the far-region integral (`TestWeight.lean:921-925`), which consumes
`T ≤ τ_k, τ_l ≤ 2T` and concludes a bound `≤ 16π(1+C)² X^{3/4} L²/T²`.

**Localized statement.** For all large `T` and all `k, l < d_H`, the
same inequality with the same `C, δ, T₀`.

**Grade and proof.** `[KERNEL-CHECKED, DYADIC]`, used as a special case. By
Observation 1.1, for `k, l < d_H ≤ d` the entries `G_kl`, `M_kl`, and
`τ_k − τ_l` are the same numbers as in the dyadic statement at the same
height `T` and the same `Pf`; the dyadic statement quantifies over all
`k, l < d`; restrict the quantifier. No proof is re-run. (For a reader who
wants the proof anyway: the four range uses above are all of the form
`T ≤ τ_k ≤ 2T`, which is implied by `T ≤ τ_k ≤ T + H` since `H ≤ T`; the
far-region floor `1/T`, `1/T²` comes from `cauchyK_far`
(`EntryError.lean:88-90`, a height fact); the entry-dependent coefficient
`c^{kl} = C(·; L_T + δ_kl)` is range-free; the contour on `Re s = 5/4` at
height `≈ T` is height-local. This is the audit's classification (a) for
P27-P30, and it is not needed given the restriction argument.)

> Error line. The entry error is `C T^{−δ}(min(1, Δ^{−2}) + 1/T)`, absorbed in
> 5.2 against `H l`; requires only `δ > 0`, i.e. `λ < 4/3`, true.

The window hypotheses `FamilyHyps Pf` (regularity, support and decay of the
tapers `φ_v` at scale `L`) are about the profile and the taper only and are
used unchanged (`familyHyps_flat_gevrey`, `familyHyps_atV`).

---

## 5. The trace transfer (`[XF′ Lemma 5.1, 6.1]`; audit step 5; no zeta analogue)

Target (`Zeta23/XiPrime/Statement.lean:217-223`, dyadic):

```lean
def XiTraceTransfer (Z : ZeroConfig) (Pf : ℝ → Params) (F : CoeffFamily) : Prop :=
  (∀ δ : ℝ, 0 < δ → ∀ᶠ T in atTop,
    |rtrace ((Pf T).hat T (Z.Gz (Pf T) T)) - rtrace ((Pf T).hat T ((Pf T).GpC T (F.c T)))|
      ≤ δ * (Z.N T (2 * T) : ℝ)) ∧
  (∀ δ : ℝ, 0 < δ → ∀ᶠ T in atTop,
    frobSq ((Pf T).hat T (Z.Gz (Pf T) T))
      ≤ (1 + δ) * frobSq ((Pf T).hat T ((Pf T).GpC T (F.c T))) + δ * (Z.N T (2 * T) : ℝ))
```

**Localized statement (`XiTraceTransfer_H`).** The same two clauses with
`Gz`, `GpC` on the short grid and `N(T, 2T) ↦ N_H`.

The proof decomposes `Ĝ_H − M̂^T_H = Ê_H^{entry} + D̂_H` with
`E^{entry} = G − M` (entry error, 5a) and `D = M − M^T` (entry dependence,
5b), and shows each is `HatNegligible` against `N_H`
(`Zeta23/XiPrime/Transfer.lean:63-67`, with `N(T,2T) ↦ N_H`):

```lean
def HatNegligible (Z : ZeroConfig) (Pf : ℝ → Params)
    (A : (T : ℝ) → Matrix (Fin ((Pf T).d T)) (Fin ((Pf T).d T)) ℂ) : Prop :=
  ∀ η : ℝ, 0 < η → ∀ᶠ T in atTop,
    |rtrace ((Pf T).hat T (A T))| ≤ η * (Z.N T (2 * T) : ℝ) ∧
    frobSq ((Pf T).hat T (A T)) ≤ η ^ 2 * (Z.N T (2 * T) : ℝ)
```

The reduction from two negligible pieces to the two clauses is pure algebra
(`tr(Ĝ) − tr(M̂^T) = tr Ê + tr D̂`; `‖Ĝ‖_F ≤ ‖M̂^T‖_F + ‖Ê‖_F + ‖D̂‖_F`, then
`(x + η√N)² ≤ (1+η)x² + (1 + 1/η)η²N`), `[KERNEL-CHECKED, DYADIC]`, generic in
`N`; it is `xiTraceTransfer_of` in `Transfer.lean` §1.

Every "negligible" conclusion in this section ends by comparing an explicit
quantity with `H l/(4π)` and then with `N_H` through Corollary 2.4(a). In the
tree the four closing lines are `Transfer.lean:378` (`η (T l/4π) ≤ η N`),
`:425` (Frobenius, entry error), `:736` (trace, entry dependence) and `:784`
(Frobenius, entry dependence), each `_ ≤ η * (Z.N T (2 * T) : ℝ) := by gcongr`
against `eventually_N_ge`. Corollary 2.4(a) is the input that replaces
`eventually_N_ge` there, and it depends on §2, which is why the count comes
first (re-audit, ordering).

### 5a. The entry error.

#### Lemma 5.1 (fixed `T`, any grid size). `[NEW STATEMENT, PROOF WRITTEN HERE]`

If `|E_kl| ≤ C T^{−δ}(1/max(1, Δ_kl²) + 1/T)` for all `k, l < n` with
`Δ_kl = τ_k − τ_l = (k − l)h`, then

```
|tr E| ≤ n C T^{−δ}(1 + 1/T),    ‖E‖_F² ≤ 2 (C T^{−δ})² (8 n (1 + 1/h) + n²/T²).
```

*Proof.* The trace is a sum of `n` diagonal entries with `Δ = 0`. For the
Frobenius norm, `(x + y)² ≤ 2x² + 2y²` gives
`‖E‖_F² ≤ 2C²T^{−2δ}(Σ_{k,l} 1/max(1, Δ_kl⁴) + n²/T²)`, and
`Σ_{k,l<n} 1/max(1, ((k−l)h)⁴) ≤ n (1 + 2 Σ_{j≥1} 1/max(1, (jh)⁴))
≤ n(1 + 2(⌈1/h⌉ + h^{−1}∫_1^∞ x^{−4}dx)) ≤ 8n(1 + 1/h)`. ∎

This is the tree's fixed-`T` lemma (`Zeta23/XiPrime/Transfer.lean`, §2, stated
in its docstring at `:227-229` as
`|tr E| ≤ d·C T^{−δ}(1 + 1/T)` and `‖E‖_F² ≤ 2(C T^{−δ})²(8d(1 + 1/h) + d²/T²)`)
with `d` renamed `n`; its proof is the double sum above and is generic in `n`.

#### Proposition 5.2 (entry error is negligible against `N_H`). `[NEW STATEMENT, PROOF WRITTEN HERE]`

For every `η > 0`, eventually: `|tr Ê_H^{entry}| ≤ η N_H` and
`‖Ê_H^{entry}‖_F² ≤ η² N_H`.

*Proof.* Apply Lemma 5.1 with `n = d_H ≤ LH/2π` (the floor bound `d_le`,
`Transfer.lean:225-227`, with `T ↦ H`) and `1/h = L/2π`, then divide by
`aL²` resp. `(aL²)²`, using `a ≥ a₀ > 0` eventually (`ha`). Trace:

```
|tr Ê| ≤ (a₀L²)^{−1} (LH/2π)(2 C T^{−δ}) = C H T^{−δ}/(π a₀ L) ≤ η H l/(4π) ≤ η N_H
```

once `T^{−δ} ≤ η a₀ L l/(4C)`, which holds eventually; the last step is
Corollary 2.4(a). Frobenius: with `1 + L/2π ≤ L/π` for `L ≥ 2π` and
`H²/T² ≤ H`,

```
8 d_H (1 + 1/h) + d_H²/T² ≤ (LH/2π)(8L/π) + L²H²/(4π²T²) ≤ L² H,
```

so `‖Ê‖_F² ≤ (a₀L²)^{−2} · 2C² T^{−2δ} L² H = 2C² T^{−2δ} H/(a₀² L²) ≤ η² H l/(4π)
≤ η² N_H` once `T^{−2δ} ≤ η² a₀² L² l/(8πC²)`. ∎

This is `Transfer.lean:362-378` and `:380-425` with `LT/2π ↦ LH/2π` and
`T l/4π ≤ N(T,2T) ↦ H l/4π ≤ N_H`.

> Error line. Size `O(H T^{−δ}/L)` (trace) and `O(H T^{−2δ}/L²)` (Frobenius);
> absorbed against `H l`; requires nothing beyond `δ > 0`. Audit P13, P14.

### 5b. The entry dependence.

`D_kl = M_kl − M^T_kl`, the difference between the entry with coefficients
frozen at `L⋆ = L_T + δ_kl` and the entry with coefficients `c^T = C(·; L_T)`;
by linearity in the coefficients the `μ` and `Π_X` parts cancel and
`D_kl = Q_kl(c^{kl} − c^T)` with `Q_kl(e) := ∫ φ̂(τ−τ_k) φ̂(τ−τ_l) P_e(τ) dτ`
(`Transfer/Inputs.lean:25-27`, `QpEntry`; `Gp1_sub_GpC_apply`,
`Transfer.lean:576`).

#### 5b-i. Inputs used unchanged. `[KERNEL-CHECKED, DYADIC]`

`Zeta23/XiPrime/Transfer/Inputs.lean:33`:
`def deltaKL (k l : ℤ) : ℝ := Real.log (P.tauStar T k l / T) / 2`, and the
re-expansion (`Zeta23/XiPrime/Coeff/Reexpansion.lean:42-44`):

```lean
theorem xiReexpansion :
    ∃ (e : ℝ → ℕ → ℕ → ℂ) (ρ₀ A T₀ : ℝ), 0 ≤ ρ₀ ∧ Reexpansion xiCoeffFamily e ρ₀ A T₀
```

where `Reexpansion F e ρ₀ A T₀` (`Transfer/Inputs.lean:58-79`) states, with
`T`-uniform constants: for `T ≥ T₀`, `δ ∈ [0, 1/2]`, every `N`,
`C(N; L_T + δ) − c^T_N = Σ_{r≥1} e_r(N) δ^r` (absolutely convergent); `e_r(1) = 0`;
and the majorants `(H1)_r`, `(H2)_r`, `(H3)_r`:

```
Σ_{N≤x} |e_r(N)| N^{−1/2} ≤ A (ρ₀/l)^r √x l,     Σ_{N≤x} |e_r(N)|² ≤ A (ρ₀/l)^{2r} x l²,
Σ_{N≤x} |e_r(N)|²/N ≤ A (ρ₀/l)^{2r} l² (1 + log x),   for 2 ≤ x ≤ e^l.
```

The Dirichlet-kernel bound (`Zeta23/XiPrime/Transfer/Dependence.lean:224-229`):

```lean
lemma Aphi_mul_norm_tauKernel_le' (hF : LocalHypsCoreW cϱ p Fn) {y : ℝ} (hy : Real.log 2 ≤ y)
    (K : ℕ) :
    Fn.Aphi y * ‖∑ k ∈ Finset.range K, Complex.exp ((-(p.tau k * y) : ℝ) * Complex.I)‖
      ≤ p.L ^ 2 / (2 * Real.log 2)
```

for **every** `K`, where `A_φ(y) = ∫ φ̂(τ)² e^{−iτy} dτ`. This is the audit's
P32: the constant `2 log 2` is the lowest frequency `log 2`, not the range.

#### Lemma 5.3 (the shift is small). `[NEW STATEMENT, PROOF WRITTEN HERE]`

For `k, l < d_H`: `0 ≤ δ_kl ≤ ½ log(1 + H/T) ≤ H/(2T) ≤ 1/2`.

*Proof.* `τ⋆_kl = (τ_k + τ_l)/2 ∈ [T, T + H)` by Observation 1.1 and
`d_H h ≤ H`; `log` is increasing; `log(1+x) ≤ x`; `H ≤ T`. ∎

This sharpens `deltaKL_mem` (`Transfer.lean:472-490`, `δ_kl ∈ [0, 1/2]`) and
lands inside the expansion domain `[0, 1/2]` of `Reexpansion` with room to
spare, which is why the audit calls this step "easier" in a short window.

#### Proposition 5.4 (entry dependence is negligible against `N_H`). `[NEW STATEMENT, PROOF WRITTEN HERE]`

For every `η > 0`, eventually: `|tr D̂_H| ≤ η N_H` and `‖D̂_H‖_F² ≤ η² N_H`.

*Proof of the trace bound.* For `k < d_H`, `D_kk = Σ_{r≥1} δ_kk^r Q_kk(e_r)`
(the expansion is a finite ℝ-linear functional of the coefficients, so it
commutes with `Q_kk`; `Dependence.lean` §A). Writing
`P_e(τ) = (1/π) Re Σ_N e(N) N^{−1/2} e^{−iτ log N}` (the definition of `Pc`),

```
Q_kk(e_r) = (1/π) Re Σ_N e_r(N) N^{−1/2} e^{−iτ_k log N} A_φ(log N).
```

Hence `Σ_{k<d_H} δ_kk^r Q_kk(e_r) = (1/π) Re Σ_N e_r(N) N^{−1/2} A_φ(log N) S_N`,
`S_N := Σ_{k<d_H} δ_kk^r e^{−iτ_k log N}`. Since `k ↦ δ_kk = ½ log(τ_k/T)` is
nondecreasing and nonnegative, Abel summation gives
`|S_N| ≤ 2 δ_max^r max_{K ≤ d_H} |Σ_{k<K} e^{−iτ_k log N}|`, and the
Dirichlet-kernel bound (valid for every `K`, frequency `log N ≥ log 2`) gives
`A_φ(log N)|S_N| ≤ δ_max^r L²/log 2`. With `(H1)_r` at `x = X`:

```
|Σ_k δ_kk^r Q_kk(e_r)| ≤ (1/π) δ_max^r (L²/log 2) A (ρ₀/l)^r √X l.
```

Sum over `r ≥ 1` with `δ_max ≤ 1/2` and `l ≥ ρ₀`: the geometric series gives
`|tr D_H| ≤ (2/(π log 2)) A ρ₀ L² √X`, and in hat units
`|tr D̂_H| ≤ κ_tr √X` with `κ_tr = 2Aρ₀/(π a₀ log 2)`. This is exactly the
tree's bound (`Transfer.lean:721-736`: `κtr * Real.sqrt (P.X T)`), obtained
with the same constants because `δ_max ≤ 1/2` and the kernel bound holds for
every `K`. Now `κ_tr √X ≤ η H l/(4π) ≤ η N_H` eventually iff `√X = o(H l)`,
which is Corollary 2.4(e) with `λ/2 < θ`. (The tree at this point compares
`√X ≤ √T` against `T l/4π`, `Transfer.lean:729-734`.)

*Proof of the Frobenius bound.* By Minkowski in `r`,
`‖D_H‖_F ≤ Σ_{r≥1} δ_max^r ‖(Q_kl(e_r))_{k,l<d_H}‖_F`. For each `r`, `e_r(1) = 0`
and the localized `PPUpper` (Proposition 6.4 plus Lemma 6.2 below, with range
length `H`) gives

```
Σ_{k,l<d_H} Q_kl(e_r)² ≤ C L² ( H L Σ_{N≤X} |e_r(N)|²/N + L Σ |e_r(N)|² + L S₁(e_r)² + L l log l (l + S₁(e_r))² ),
```

`S₁(e) := Σ_{N≤X} |e(N)| N^{−1/2}`. Insert `(H1)_r`-`(H3)_r` (with `1 + log X ≤ 2L`):

```
Σ_{k,l<d_H} Q_kl(e_r)² ≤ A′ (ρ₀/l)^{2r} L⁴ H l² + A′ L³ l⁴ (1 + X),
```

which is the tree's `sumSq_le` (`Transfer.lean:565-569`) with `T ↦ H`.
Take square roots, sum the geometric series in `r` (`δ_max ≤ 1/2`), square,
and divide by `(a₀L²)²`:

```
‖D̂_H‖_F² ≤ 2A′ρ₀² H/a₀² · (1/l²) · l² ... = 2A′ρ₀² H/a₀²  +  (2A′/a₀²) · l⁴(1 + X)/L.
```

The first term is `≤ (η²/8π) H l` once `l ≥ 16π A′ρ₀²/(a₀²η²)` (the tree's
`i1`, `Transfer.lean:751-762`, with `T ↦ H`). The second is `≤ (η²/8π) H l`
once `l⁴(1+X)/H ≤ ε(η)`, i.e. once `l⁴ X/H → 0`, which is Corollary 2.4(e)
with `λ < θ` (the tree's `i2`, `:763-775`, and `hsmallX`, `:611-612`, which
there reads `l⁴ X/T ≤ ε`). Adding, `‖D̂_H‖_F² ≤ η² H l/(4π) ≤ η² N_H`. ∎

> Error lines. Trace: size `O(√X)`, absorbed against `H l`, requires
> `λ/2 < θ` (implied by condition 1). Frobenius main: size `O(H)`, absorbed
> against `H l`, requires nothing (`l → ∞`). Frobenius end effect: size
> `O(l⁴ X/L)`, absorbed against `H l`, requires `λ < θ` (condition 1).
> Audit P15, P17, P18.

With 5.2 and 5.4, `XiTraceTransfer_H` holds.

---

## 6. Localization of the kernel-checked xi-prime second moment along Wang's route (Wang Lemmas 2.4, 2.5, Proposition 2.6, Theorem 2.2; audit step 6)

This is the step the audit's framing correction is about. The tree consumes no
zeta pair correlation; it computes the two traces of the fixed-coefficient
prime-side matrix `M^T` directly. Target (`Zeta23/XiPrime/Statement.lean:236-241`):

```lean
def CoeffMoments (Z : ZeroConfig) (Pf : ℝ → Params) (F : CoeffFamily) (κ : ℝ) : Prop :=
  (∀ δ : ℝ, 0 < δ → ∀ᶠ T in atTop,
    (1 - δ) * (Z.N T (2 * T) : ℝ) ≤ rtrace ((Pf T).hat T ((Pf T).GpC T (F.c T))) ∧
    rtrace ((Pf T).hat T ((Pf T).GpC T (F.c T))) ≤ (1 + δ) * (Z.N T (2 * T) : ℝ)) ∧
  (∀ δ : ℝ, 0 < δ → ∀ᶠ T in atTop,
    frobSq ((Pf T).hat T ((Pf T).GpC T (F.c T))) ≤ (κ + δ) * (Z.N T (2 * T) : ℝ))
```

**Localized statement (`CoeffMoments_H`).** With `M^T_H` on the short grid,
`N_H` in place of `N(T, 2T)`, and `κ = kappaXi λ v`:

```
(1 − δ) N_H ≤ tr M̂^T_H ≤ (1 + δ) N_H    and    ‖M̂^T_H‖_F² ≤ (κ + δ) N_H,   eventually, for every δ > 0.
```

Wang's corresponding statement is Theorem 2.2: the pair sum equals
`(HL/2π)(g(0) + ∫|α| g) + O(H + T^λ L²)`. Here the "`g(0)`" is the trace and
the "`∫|α|g`" is `jWin D₁ λ v`, entering through the diagonal law (H3); the
error `O(T^λ L²)` corresponds to the `X`-sized remainders below.

### 6.0 The inputs used unchanged. `[KERNEL-CHECKED, DYADIC]`

- The Poisson identity `PoissonSq` (quoted in 3a), for every real `γ`.
- Real-line decay of the taper transform: `|φ̂(r)| ≤ C₁′/r²` for real `r ≠ 0`,
  with `C₁′ = 2‖ϱ″‖₁/w` (two integrations by parts on the `C²` compactly
  supported `φ`; this is the `y = 0` case of `norm_phiHat_sub_I_mul_le` without
  the factor `e^{L/4}`, which arises only from the imaginary shift). Also
  `|φ̂(r)| ≤ ψ(r) = min(L, 2/|r|, c_ϱ/(w r²))` (`Params.psi`), and the bounds
  `|Φ(x)| ≤ ψ(x)`, `∫_ℝ ψ ≪ log L`, `∫_{|x|≥Δ} ψ² ≪ min(L, 1/Δ, 1/(w²Δ³))`,
  `∫ ψ(x)² |x| dx ≪ log L`.
- The weighted Hilbert inequality (`Zeta23/Hypotheses.lean:107-111`,
  `MVHilbert C`, proved as `mv_hilbert`, `Zeta23/MV/Final.lean:30-31`, with an
  absolute constant): for distinct `λ_r` and `0 < δ_r ≤ min_{s≠r}|λ_r − λ_s|`,
  `|Σ_{r≠s} x_r conj(z_s)/(λ_r − λ_s)| ≤ C (Σ|x_r|²/δ_r)^{1/2}(Σ|z_r|²/δ_r)^{1/2}`.
  No interval appears.
- Chebyshev-Mertens (`ChebyshevMertens`, `Zeta23/Hypotheses.lean:80-99`),
  no interval.
- The coefficient hypotheses `xiCoeffFamily_hyps` (`Zeta23/XiPrime/Coeff.lean:41-47`),
  i.e. `(H1)`-`(H3)` of `CoeffFamily.Hyps` (`Statement.lean:151-168`), with
  `T`-uniform constants, for `2 ≤ x ≤ e^l` and `0 ≤ y ≤ l`:

```lean
  H1 : ∃ C T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T → ∀ x : ℝ, 2 ≤ x → x ≤ Real.exp (l T) →
    (∑ N ∈ Finset.Ioc 0 ⌊x⌋₊, ‖F.c T N‖ / Real.sqrt N) ≤ C * Real.sqrt x * l T
  H2 : ∃ C T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T → ∀ x : ℝ, 2 ≤ x → x ≤ Real.exp (l T) →
    (∑ N ∈ Finset.Ioc 0 ⌊x⌋₊, ‖F.c T N‖ ^ 2) ≤ C * x * l T ^ 2
  H3 : ∀ ε : ℝ, 0 < ε → ∃ T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T → ∀ y : ℝ, 0 ≤ y → y ≤ l T →
    |(∑ N ∈ Finset.Ioc 0 ⌊Real.exp y⌋₊, ‖F.c T N‖ ^ 2 / N) - l T ^ 2 * ∫ s in (0:ℝ)..(y / l T), F.D s|
      ≤ ε * l T ^ 2
```

  proved by `coeff_H3` (`Zeta23/XiPrime/Coeff/H3.lean:44-45`) with `F.D = D₁`.
  This is the audit's §4: the only `T`-dependence is the scalar `l(T)` inside
  `L_T`. The `s`-term and the corrections of `D₁` are one object here; there
  is no separate "arithmetic `|α|`" input and no transfer from zeta zeros.
- The partial-summation consequence `sumJ` (`FactsXi.sumJ`,
  `Zeta23/XiPrime/PrimeSide/Traces.lean:228-229`): for every `ε > 0`,
  eventually `|Σ_{N≤X} |c^T_N|²/N · g(log N) − (L³/2) J_T| ≤ ε l² L`, with
  `J_T = (2/L³) l ∫_0^L D₁(y/l) g(y) dy` (`JD`, `:44`). Range-free: it is Abel
  summation of (H3) against `g` on `[0, L]`.
- The density bound `NuBound` (`Zeta23/PrimeSideA/EndsCore.lean:63-64`):
  `|ν(τ)| ≤ B + max(log(|τ|/4T), 0)` for all `τ`, which for `ν = ν_{c^T}` holds
  with `B = C(l + √X l)`: `|μ(τ)| ≤ (1/2π)log(|τ|/2π) + C ≤ l + log⁺(|τ|/4T) + C`
  for `|τ| ≥ 1` (Stirling) and `|μ| ≤ C` near `0`; `|Π_X| ≤ 2 + 2(√X + 1)/π`
  (from the definition, `|X^s| = √X`, `|s| ≥ 1/2`); `|P_{c^T}(τ)| ≤
  (1/π) Σ_{N≤X}|c^T_N| N^{−1/2} ≤ C √X l` by (H1). The tree's `Traces.lean:217`
  records `B ≍ l(1 + √X)` for exactly this reason.

**The two roles of `Setting.T` (re-audit).** The prime side is stated over
`PrimeSide.Setting` (`Zeta23/PrimeSideA/Defs.lean:65-87`): a structure with
fields `T, lam, w`, from which `l = log(T/2π)`, `L = lam·l`, `X = e^L`,
`h = 2π/L`, `d = ⌊L T/2π⌋`, `tau k = T + k h` and the window `I = [T, 2T]` are
*derived*; `Params.toSetting T = ⟨T, P.lam, P.w⟩`
(`Zeta23/PrimeSideB/Concrete.lean:36`), and the trace transfer pins
`eT : ((Pf T).toSetting T).T = T` (`reexpansionGeom_of`,
`Zeta23/XiPrime/Transfer.lean:822` and following). So one field is at once
the **height** and the **range length**. The localization splits it. In every
prime-side statement of §6 and in `PPUpper` (5.4), the occurrences of `p.T`
that become `H` are: `d = ⌊L T/2π⌋` (→ `d_H`); the window `I = [T, 2T]` and
the product domain of `Mform` (→ `I_H`, `I_H × I_H`); the Riemann-sum integral
`∫_T^{2T}` and its end point `μ(2T)` (→ `∫_T^{T+H}`, `μ(T+H)`; 6.1);
`tau_d_gt`'s `2T` (→ `T + H`; 6.2); the Montgomery-Vaughan endpoint `2T` in
the sine and cosine arguments (→ `T + H`; 6.4); the diagonal main term
`T/π · Σ …` (→ `H/π`; 6.4); `hvol : volume.real (Icc T (2T)) = T` (→ `H`;
6.5); the `∫_T^{2T}` upper limits of the leaf integrals
(`Zeta23/Defs/LeafIntegrals.lean:25, 51, 77`; → `T + H`; 6.2); the `μ²`
integral (6.3). The occurrences that **stay** `T`: every threshold `T₀ ≤ p.T`;
`l`, `L`, `X`, `h` and the base point `tau 0 = T`; `NuBound`'s
`log⁺(|τ|/4T)`; the bounds `|Π_X| ≤ C√X/T` and `|μ′| ≤ C/T` on the window;
the `1/T`, `1/T²` floors; `log(4T)`. A `(T, U)` parameterization has to be
threaded through `Setting` (a fourth field, or `U` in place of the derived
`I`), not only through `Params`; §12 records this.

Throughout §6 write `ν = ν_{c^T}` and `S_H(τ) := Σ_{k<d_H} φ̂(τ − τ_k)²`,
`R_H(τ) := Σ_{k ∉ [0, d_H)} φ̂(τ − τ_k)² ≥ 0`, so that `S_H + R_H = aL²` for every
real `τ` (Poisson). Two bounds on `R_H` and `S_H`, both from the real-line
decay and Lemma 3.3's counting:

```
(R)  for τ ∈ I_H at distance Δ ≥ 2π from both endpoints of I_H:  R_H(τ) ≤ 4 C₁′² L Δ^{−3};   always R_H ≤ aL².
(S)  for τ ∉ I_H at distance Δ ≥ 1 from I_H:  S_H(τ) ≤ C₁′² L Δ^{−3};   always S_H ≤ aL².
```

(For (R): the missing points `τ_k`, `k < 0`, are at distances `≥ Δ + |k|h`
from `τ`; those with `k ≥ d_H` at distances `≥ (τ_{d_H} − τ) + (k − d_H)h ≥
Δ − h + (k − d_H)h ≥ Δ/2 + (k − d_H)h` since `τ_{d_H} > T + H − h` by
**Lemma 1.2** and `h ≤ π ≤ Δ/2`; sum as in Lemma 3.3. This is the one place
in (R) where the lower floor inequality is load-bearing: without it the
grid could stop short of `T + H` and `R_H` would not be small deep inside
`I_H`. It is the localization of `tau_d_gt`.)

### Proposition 6.1 (prop:trace, short window). `[NEW STATEMENT, PROOF WRITTEN HERE]`

The tree (`Zeta23/PrimeSideA.lean:300-304`, for the zeta density, and the
xi-prime field `FactsXi.prop_trace`, `Traces.lean:214-216`):

```lean
theorem prop_trace (hΓ : Zeta23.GammaFacts) (hcheb : Zeta23.ChebyshevMertens)
    (hlam : 0 < lam ∧ lam ≤ 1) (A : ℝ) :
    ∃ C : ℝ, EventuallyAtCore cϱ lam (fun p F => ∀ N : ℝ,
      |N - p.T * p.ell1 / (2 * π)| ≤ A * p.l →
      |trGtA p F - F.a * p.L * N| ≤ C * (p.L * Real.sqrt p.X))
```

```lean
  prop_trace : EvBound (fun T => D.trG T - D.aT T * P.L T * D.Ncnt T)
      (fun T => P.L T * Real.sqrt (P.X T) * l T)
```

**Statement.** `tr M̃^T_H = a L N_H + O(L √X l)`, hence
`tr M̂^T_H = N_H (1 + o(1))` (as `√X l = o(H l)` by 2.4(e)).

*Proof.* `L · tr M̃^T_H = Σ_{k<d_H} M^T_kk = ∫_ℝ S_H(τ) ν(τ) dτ` (finite sum of
absolutely convergent integrals; `|φ̂(τ−τ_k)²ν(τ)| ≤ ψ² · (B + log⁺)` is
integrable). Split `ℝ = I_H ∪ I_H^c` and use `S_H = aL² − R_H` on `I_H`:

```
∫_ℝ S_H ν = aL² ∫_{I_H} ν − ∫_{I_H} R_H ν + ∫_{I_H^c} S_H ν.
```

*Second term.* On `I_H`, `|ν| ≤ B` (as `|τ|/4T < 1`). By (R), splitting at
distance `2π` from the endpoints,
`|∫_{I_H} R_H ν| ≤ B(4π · aL² + 2 ∫_{2π}^∞ 4C₁′² L Δ^{−3} dΔ) ≤ C L² B`.

*Third term.* By (S), splitting at distance `1`:
`|∫_{I_H^c} S_H ν| ≤ 2 aL² (B + 1) + 2 ∫_1^∞ C₁′² L Δ^{−3} (B + log⁺((T+H+Δ)/4T)) dΔ ≤ C L² B + C L log T/T² ≤ C L² B`
(the `log⁺` is nonzero only for `Δ ≥ 2T`, where `∫_{2T}^∞ Δ^{−3} log(Δ/T) dΔ ≪ 1/T²`).

So `tr M̃^T_H = aL ∫_{I_H} ν + O(L B)`. Now
`∫_{I_H} ν = ∫_{I_H} μ + ∫_{I_H} Π_X + ∫_{I_H} P_{c^T}`:

- `∫_{I_H} μ = H ℓ_H/2π + O(1/T) = N_H + O(log T)` (Lemma 2.2(i), Lemma 2.3);
- `|∫_{I_H} Π_X| ≤ H · (1/(2πT²) + (√X + 1)/(πT)) ≤ C √X` (on `I_H`, `|s| ≥ T`);
- `|∫_{I_H} P_{c^T}| ≤ (1/π) Σ_{N≤X} |c^T_N| N^{−1/2} · |∫_T^{T+H} e^{−iτ log N} dτ|
  ≤ (2/(π log 2)) S₁(c^T) ≤ C √X l` (H1; `N ≥ 2` since `c^T_1 = 0`).

Hence `tr M̃^T_H = aL N_H + O(L log T + L √X + L √X l + L B) = aL N_H + O(L √X l)`,
using `B ≍ l(1 + √X)`. ∎

The range enters through `∫_{I_H} μ` (main term), through
`∫_{I_H} Π_X ≤ H · √X/T ≤ √X` (an upper bound using `H ≤ T`), and through
Lemma 1.2 inside `(R)` (the grid must reach `T + H` to within `h`). The
boundary effects are two, one per endpoint, and do not see `H`. This is
Wang's Lemma 2.4 in trace form; Wang's `O(xL³)` corresponds to the `O(L²B)`
above before division by `L`.

*The tree's own route (re-audit).* The tree does not use the Poisson
decomposition for the first trace. `prop_trace_mu` (`Zeta23/PrimeSideA.lean:58-61`)
writes the `μ`-part of `Σ_{k<d} G_kk` as `2π a L Σ_{k<d} μ(τ_k) + (end terms)` and
then, at `:137-150`, compares the grid sum with the integral by
`riemann_sum_monotone` (quoted in §1):

```
|2π a L Σ_{k<d} μ(τ_k) − a L² ∫_T^{2T} μ| ≤ 4π L l,
```

which is `aL² · |h Σ_{k<d} μ(T + kh) − ∫_T^{2T} μ| ≤ aL² · 2h μ(2T) ≤ 4π a L l`,
using `d = ⌊T/h⌋` (`Setting.d_eq_floor`) so that `T < T + dh ≤ 2T < T + (d+1)h`,
`μ` monotone and nonnegative on `[T − h, ∞)` (`GammaFacts.monotoneOn`,
`mu_nonneg_eventually`), and `μ(2T) ≤ l`. Localized: with `d_H = ⌊H/h⌋` and
Lemma 1.2, `T < T + d_H h ≤ T + H < T + (d_H + 1)h`, and the same Riemann-sum
comparison (Mathlib's monotone unit-step sums rescaled to step `h`, on the
interval `[T, T+H]`) gives

```
|2π a L Σ_{k<d_H} μ(τ_k) − a L² ∫_T^{T+H} μ| ≤ 2π a L · 2 μ(T+H) ≤ 4π L l.
```

Both floor inequalities are used: the upper one to keep every `τ_k` in
`[T, T+H)`, the lower one so that the last grid cell `[τ_{d_H − 1}, T+H]` has
length at most `2h` and its contribution is bounded by `2h μ(T+H)`. This is
the localization the re-audit asked for (condition 4, first instance). Either
route gives Proposition 6.1; they are recorded together so that a Lean port
can follow the tree's.

> Error line. Size `O(L √X l)`; absorbed against `a L N_H ≍ L H l`; requires
> `√X/H → 0`, i.e. `λ/2 < θ` (implied by condition 1). Audit P24.

### Lemma 6.2 (lem:ends, short window). `[NEW STATEMENT, PROOF WRITTEN HERE]`

The tree (`Zeta23/PrimeSideA/Ends.lean:114-118`, ν-generic; `:143-146` for
the zeta density; the xi-prime field `FactsXi.lem_ends`, `Traces.lean:218`):

```lean
theorem lem_ends_nu :
    ∃ C T₀ : ℝ, ∀ (p : Setting) (F : LocalFun) (B : ℝ) (ν : ℝ → ℝ), p.lam = lam → T₀ ≤ p.T →
      LocalHypsCore cϱ p F → Continuous ν → NuBound p B ν → p.l ≤ B →
      |(p.L)⁻¹ ^ 2 * ∑ k : Fin p.d, ∑ l : Fin p.d, GentryNu ν p F k l ^ 2 - MtotalNu ν p F|
        ≤ C * (p.L * p.l * Real.log p.l * B ^ 2)
```

with `MtotalNu ν p F = Mform F.Phi p.T ν ν` and (`Zeta23/PrimeSideA/Defs.lean:150-151`)

```lean
def Mform (Φ : ℝ → ℝ) (T : ℝ) (u₁ u₂ : ℝ → ℝ) : ℝ :=
  ∫ q in (Set.Icc T (2 * T)) ×ˢ (Set.Icc T (2 * T)), (Φ (q.1 - q.2)) ^ 2 * u₁ q.1 * u₂ q.2
```

**Statement.** Let `𝓜_H[u₁, u₂] := ∬_{I_H × I_H} Φ(τ − τ′)² u₁(τ) u₂(τ′) dτ dτ′`
(the `Mform` with `Icc T (2T) ↦ I_H`). For any continuous `ν` with
`NuBound p B ν` and `l ≤ B`,

```
| L^{−2} Σ_{k,l<d_H} (∫ φ̂(τ−τ_k) φ̂(τ−τ_l) ν)² − 𝓜_H[ν, ν] | ≤ C L l log l B²,
```

with `C` independent of `H`. For `ν = ν_{c^T}`, `B ≍ l(1 + √X)`, this is
`O(L l³ log l (1 + X))`, the tree's `Rxi`.

*Proof.* Expanding the square and exchanging finite sums with the integrals,
`Σ_{k,l<d_H} (∫ φ̂_k φ̂_l ν)² = ∬_{ℝ²} K_H(τ,τ′)² ν(τ)ν(τ′) dτ dτ′` with
`K_H(τ,τ′) := Σ_{k<d_H} φ̂(τ−τ_k) φ̂(τ′−τ_k)`. Let
`K_∞(τ,τ′) := Σ_{k∈ℤ} φ̂(τ−τ_k) φ̂(τ′−τ_k) = L Φ(τ − τ′)` (Poisson summation over
the grid of spacing `2π/L`, applied to the product of two functions whose
spectra lie in `[−L/2, L/2]`; the tree's `LocalHyps.poisson`). Then
`L² 𝓜_H[ν,ν] = ∬_{I_H²} K_∞² νν′`, and

```
Σ_{k,l} (…)² − L² 𝓜_H = 𝓔₁ + 𝓔₂,   𝓔₁ := ∬_{I_H²} (K_H² − K_∞²) νν′,   𝓔₂ := ∬_{ℝ² ∖ I_H²} K_H² νν′.
```

*Bounding `𝓔₁`.* `K_∞ − K_H = K_out := Σ_{k∉[0,d_H)} φ̂(τ−τ_k) φ̂(τ′−τ_k)`, and by
Cauchy-Schwarz and the weighted AM-GM inequality, for any `s > 0`,
`|K_out(τ,τ′)| ≤ (R_H(τ) R_H(τ′))^{1/2} ≤ ½(s R_H(τ) + R_H(τ′)/s)`. Also
`|K_H|, |K_∞| ≤ aL²` (Cauchy-Schwarz and Poisson), so
`|K_H² − K_∞²| ≤ 2aL² |K_out|`. Take `s = g(τ′)/g(τ)` with
`g(τ) := (1 + dist(τ, ∂I_H))^{−2}`. On `I_H`, `|ν| ≤ B`. Hence

```
|𝓔₁| ≤ aL² B² ∬_{I_H²} (R_H(τ) g(τ′)/g(τ) + R_H(τ′) g(τ)/g(τ′)) = 2aL² B² (∫_{I_H} R_H/g)(∫_{I_H} g).
```

`∫_{I_H} g ≤ 2∫_0^∞ (1+Δ)^{−2} dΔ = 2`; in the tree this is the three leaf
integrals `Zeta23/Defs/LeafIntegrals.lean:25` (`∫_T^{2T} (1+(τ−T))^{−2} ≤ 1`),
`:51` (`∫_T^{2T} (1+(2T−τ))^{−2} ≤ 1`) and `:77` (`Ig_core`,
`∫_{[T,2T]} (1 + min(τ−T, 2T−τ))^{−2} ≤ 2`), each of which is the same
antiderivative with `2T ↦ T+H` (re-audit). By (R), which rests on Lemma 1.2
exactly as `EndsE1.lean`'s majorant for `ρ` on `I` rests on `tau_d_gt`
(`:262-266`, "the majorant for ρ on I"),
`∫_{I_H} R_H/g ≤ ∫_{Δ<2π} aL²(1+2π)² + 2∫_{2π}^{H/2} 4C₁′² L Δ^{−3}(1+Δ)² dΔ
≤ C L² + C′ L log H ≤ C″ L l` (as `L ≤ l` and `log H ≤ l`). So
`|𝓔₁| ≤ C L³ B² l`.

*Bounding `𝓔₂`.* `ℝ² ∖ I_H² ⊂ (I_H^c × ℝ) ∪ (ℝ × I_H^c)`, and by symmetry
`|𝓔₂| ≤ 2 ∫_{I_H^c} ∫_ℝ K_H(τ,τ′)² |ν(τ)| |ν(τ′)| dτ′ dτ`. Write
`ψ_k(τ) := |φ̂(τ − τ_k)|`. Then `K_H² ≤ (Σ_k ψ_k(τ)ψ_k(τ′))²`, and
`Σ_{k∈ℤ} ψ_k(τ)ψ_k(τ′) ≤ (Σ_k ψ_k(τ)²)^{1/2}(Σ_k ψ_k(τ′)²)^{1/2} = aL²` (Poisson),
so `K_H(τ,τ′)² ≤ L² Σ_{k<d_H} ψ_k(τ) ψ_k(τ′)`. Therefore

```
|𝓔₂| ≤ 2L² Σ_{k<d_H} (∫_{I_H^c} ψ_k |ν|) (∫_ℝ ψ_k |ν|).
```

Second factor: `∫_ℝ ψ(τ′ − τ_k)(B + log⁺(|τ′|/4T)) dτ′ ≤ B Ψ₀ + ∫_{|τ′|≥4T} (c_ϱ/(w(τ′−τ_k)²)) log(|τ′|/4T) dτ′ ≤ B Ψ₀ + C/T ≤ 2BΨ₀`,
where `Ψ₀ := ∫_ℝ ψ ≪ log L`. First factor, summed over `k`:
`Σ_k ∫_{I_H^c} ψ_k |ν| = ∫_{I_H^c} σ_H(τ) |ν(τ)| dτ` with
`σ_H(τ) := Σ_{k<d_H} ψ(τ − τ_k)`. For `τ ∉ I_H` at distance `Δ` from `I_H`, the
grid points are at distances `≥ Δ` from `τ` with spacing `h` (for `τ` to the
right of `I_H` this is the reflected-index domination
`sum_psiA_shift_right`, `Zeta23/PrimeSideA/EndsWeighted.lean:218-229`, whose
hypotheses `2T ≤ τ` and `T + kh ≤ 2T` for `k < d` become `T + H ≤ τ` and
`T + kh ≤ T + H` for `k < d_H`, the latter from Lemma 1.2), so
`σ_H(τ) ≤ ψ(Δ) + h^{−1} ∫_Δ^∞ ψ ≤ L + (L/2π)Ψ₀` always, `≤ 2/Δ + (L/2π) c_ϱ/(wΔ) ≤ C L/Δ`
for `Δ ≥ 1`, and `σ_H(τ) ≤ d_H ψ(Δ) ≤ (LH/2π) c_ϱ/(wΔ²)` for the far range.
Hence, splitting at `Δ = 1` and `Δ = T`,

```
∫_{I_H^c} σ_H |ν| ≤ 2·(L + LΨ₀)(B + 1) + 2∫_1^T (CL/Δ) B dΔ + 2∫_T^∞ (LH/(2πΔ²)) (c_ϱ/w)(B + 1 + log(Δ/T)) dΔ
                 ≤ C L log L · B + C L B log T + C L (H/T) B ≤ C B L l.
```

So `|𝓔₂| ≤ 2L² · C B L l · 2BΨ₀ ≤ C L³ B² l log L`.

Divide `𝓔₁ + 𝓔₂` by `L²`: `|L^{−2} Σ(…)² − 𝓜_H| ≤ C L B² l log l`. ∎

The range entered in exactly two places, both as upper bounds:
`log H ≤ l` in `𝓔₁`, and `d_H ≤ LH/2π ≤ LT/2π` in the far range of `𝓔₂`
(where the tree has `d ≍ LT`). This is Wang's Lemma 2.4 ("restriction to `I`
costs `O(xL³)`") for the squared kernel, and the tree's E1/E2 route.

> Error line. Size `O(L l³ log l (1 + X))`; absorbed against the main term
> `M⋆_H ≍ H L l²` of 6.6; requires `l log l X/H → 0`, i.e. `λ < θ`
> (condition 1). Audit P22.

### Proposition 6.3 (prop:mumu, short window). `[NEW STATEMENT, PROOF WRITTEN HERE]`

The tree (`Zeta23/PrimeSideA/MuMu.lean:224-229`):

```lean
theorem prop_mumu (hΓ : Zeta23.GammaFacts) (hcheb : Zeta23.ChebyshevMertens)
    (hlam : 0 < lam ∧ lam ≤ 1) :
    ∃ C : ℝ, EventuallyAtCore cϱ lam (fun p F =>
      |Mform F.Phi p.T Zeta23.mu Zeta23.mu
          - 2 * π * F.b * p.L * ∫ τ in p.T..(2 * p.T), Zeta23.mu τ ^ 2|
        ≤ C * (p.l ^ 2 * Real.log p.L))
```

**Statement.** `|𝓜_H[μ, μ] − 2π b L ∫_T^{T+H} μ²| ≤ C l² log L`, `C` independent
of `H`; hence by Lemma 2.2(ii)

```
𝓜_H[μ, μ] = (HL/2π) · b ℓ_H² · (1 + O(1/l²)) + O(l² log L).
```

*Proof.* Write `μ(τ′) = μ(τ) + (μ(τ′) − μ(τ))`:

```
𝓜_H[μ,μ] = ∫_{I_H} μ(τ)² (∫_{I_H} Φ(τ−τ′)² dτ′) dτ + ∬_{I_H²} Φ(τ−τ′)² μ(τ)(μ(τ′) − μ(τ)).
```

*First term.* `∫_{I_H} Φ(τ − τ′)² dτ′ = ∫_ℝ Φ² − ∫_{τ′ ∉ I_H} Φ(τ − τ′)²` and
`∫_ℝ Φ² = 2π ∫ φ⁴ = 2π b L` (Plancherel for `paperFT`). For `τ ∈ I_H` at
distance `Δ` from `∂I_H`, the deficit is at most
`∫_{|x| ≥ Δ} Φ(x)² dx ≤ ∫_{|x|≥Δ} ψ² ≤ 2 min(2πbL, 8/Δ, c_ϱ²/(3w²Δ³))`. With
`sup_{I_H} μ² ≤ (l + 1)²`, the first term equals
`2πbL ∫_{I_H} μ² + O((l+1)² ∫_0^∞ min(L, 8/Δ, c²/(w²Δ³)) dΔ) = 2πbL ∫_{I_H} μ² + O(l² (1 + log(wL)))`,
since `∫_0^{1/L} L + ∫_{1/L}^{w} 8/Δ + ∫_w^∞ c²/(w²Δ³) ≪ 1 + log(wL) ≪ log L`.

*Second term.* `|μ(τ′) − μ(τ)| ≤ |τ − τ′| sup_{[T, T+H]} |μ′| ≤ C|τ − τ′|/T`
(`GammaFacts.deriv_bound`, `|μ′(τ)| ≤ C/|τ|`). So the second term is at most
`(C/T) ∫_{I_H} |μ| · ∫_ℝ Φ(x)² |x| dx ≤ (C/T) H (l+1) log L ≤ C l log L` (as `H ≤ T`). ∎

The range enters only as `H/T ≤ 1`. Wang's counterpart is (2.20),
`∫_I |B_x|² = HL²/x² + O(HL/x²)`.

> Error line. Size `O(l² log L)`; absorbed against `H L l²`; requires
> nothing. Audit P25 (with Lemma 2.2 supplying the μ²-integral).

### Proposition 6.4 (prop:PP, short window). `[NEW STATEMENT, PROOF WRITTEN HERE]`

The tree (`Zeta23/XiPrime/PrimeSide/Concrete.lean:62-66`, the shape the
coefficient-generic prime side consumes; `Zeta23/PrimeSideB/PP.lean:332-336`
for the zeta coefficients):

```lean
def PPInput : Prop :=
  ∀ (C cϱ : ℝ), Zeta23.MVHilbert C → 0 < C → ∃ K : ℝ, ∀ (p : Setting) (F : LocalFun) (c : ℕ → ℂ),
    LocalHypsCore cϱ p F → 1 ≤ p.T → c 1 = 0 →
    |Mform F.Phi p.T (Pc p.X c) (Pc p.X c) - p.T / π * sumW2g c p.X F.g|
      ≤ K * p.L * (sumSqDivW c p.X + sumSqW c p.X + S1 c p.X ^ 2)
```

with `sumW2g c X g = Σ_{N≤X} |c_N|²/N · g(log N)`, `sumSqDivW = Σ|c_N|²/N`,
`sumSqW = Σ|c_N|²`, `S1 = Σ|c_N| N^{−1/2}`. The Montgomery-Vaughan step is
`MV_four` (`Zeta23/XiPrime/PrimeSide/PP.lean:301-311`), applied at
`cc ∈ {T, 2T}` (`:395-402`), and the range is the product domain
`Icc T (2T) ×ˢ Icc T (2T)` (`:149`).

(Re-audit.) This step localizes more of the tree than `PP.lean` alone.
`PP.lean:10` imports `Zeta23.ThmE.PPChi`, the twisted prime side of Theorem E,
and the xi-prime `prop_PP` runs on that layer: `Aminus`, the four endpoint
integrals `Cm, Sm, Cp, Sp`, `MV_four`, `Mform_cos_cos_ph`, and in particular
`diag_estimate_chi` (`Zeta23/ThmE/PPChi.lean:520-525`):

```lean
lemma diag_estimate_chi (hT : 0 ≤ T) (hΦ : Continuous Φ) (hΦ2 : Integrable fun x => Φ x ^ 2)
    (hΦabs : Integrable fun x => Φ x ^ 2 * |x|) {g : ℝ → ℝ}
    (hFT : ∀ y, ∫ x, Φ x ^ 2 * Real.cos (x * y) = 2 * π * g y) (hc1 : ∀ n, ‖c n‖ ≤ 1) (X : ℝ) :
    |(1 / (2 * π ^ 2)) * (∑ n ∈ primeRange X, (acoef n * ‖c n‖) ^ 2 * Aminus Φ T (Real.log n) (Real.log n))
        - T / π * ∑ n ∈ primeRange X, acoef n ^ 2 * ‖c n‖ ^ 2 * g (Real.log n)|
      ≤ (1 / (2 * π ^ 2)) * (∑ n ∈ primeRange X, acoef n ^ 2) * ∫ x, Φ x ^ 2 * |x|
```

where the `T` in `T/π · Σ …` is the **range length** (it is `|I_x| = T − |x|`
integrated against `Φ²`; class (a), `T ↦ H`), and `O1_bound_chi`
(`:615-640`), where the `T` and `2T` inside `Real.sin ((2 * T) * (Real.log n − Real.log m) − …)`
are the **endpoints** of `I_x` (class (a), `2T ↦ T + H`; MV is uniform in
them). Beneath these sit `Zeta23/PrimeSideB/PPKernel.lean` (`Ix`, `Ix_le`,
`Ix_length`, `measurePreserving_shear`, `intervalIntegral_cos_linear`, all
with `Icc T (2T)`, all elementary in the endpoints), `PPOffDiag.lean:40`
(`O1_bound`, the untwisted MV step) and, for the `μμ` term,
`PrimeSideA/MuMu.lean:71` (`Ix_le`, `Ix_length` with `p.T`). The whole layer
is `ThmE/PrimeSideChi.lean`'s prime side reused with the xi-prime
coefficients; every occurrence of the range in it is one of the two kinds
just named, class (a) or (b) with `c = λ`, the same mechanism as P20, P21.

**Statement.** For any coefficients `c` with `c_1 = 0`,

```
| 𝓜_H[P_c, P_c] − (H/π) Σ_{N≤X} |c_N|²/N · g(log N) | ≤ K L ( Σ|c_N|²/N + Σ|c_N|² + S₁(c)² ),
```

`K` independent of `H`. For `c = c^T`, by (H1)-(H3) the error is `O(L l² X)`.

*Proof* (Wang (2.19) with the smooth weight `Φ²`). Write
`P_c(τ) = (1/π) Σ_{2≤N≤X} w_N cos(τ log N − φ_N)` with `w_N = |c_N| N^{−1/2}`
and a phase `φ_N`. Then

```
𝓜_H[P_c,P_c] = (1/π²) Σ_{N,M} w_N w_M ∬_{I_H²} Φ(τ−τ′)² cos(τ log N − φ_N) cos(τ′ log M − φ_M) dτ dτ′.
```

Substitute `τ = τ′ + x`; for fixed `x` the inner domain is
`I_x := {τ′ ∈ I_H : τ′ + x ∈ I_H}`, an interval of length `max(H − |x|, 0)`
with endpoints in `{T, T − x, T + H, T + H − x}` (the tree's `Ix`, `Ix_length`,
`measurePreserving_shear`, `Zeta23/PrimeSideB/PPKernel.lean`). Use
`cos A cos B = ½[cos(A − B) + cos(A + B)]`.

*Diagonal `N = M`, difference frequency.* `A − B = x log N`, so the
contribution is `½ w_N² ∫_ℝ Φ(x)² cos(x log N) |I_x| dx
= ½ w_N² (H ∫ Φ² cos(x log N) − ∫_{|x|≤H} Φ² |x| cos(x log N) − H ∫_{|x|>H} Φ² cos(x log N))
= ½ w_N² (2π H g(log N) + O(log L) + O(H · c²/(w² H³)))`,
using `∫ Φ(x)² e^{ixy} dx = 2π g(y)` and `∫ ψ² |x| ≪ log L`. Summed: the main
term `(H/π) Σ |c_N|²/N g(log N)` plus `O(Σ w_N² log L) = O(L Σ|c_N|²/N)`.

*Diagonal, sum frequency.* `∫_{I_x} cos(2τ′ log N + x log N − 2φ_N) dτ′` has
absolute value `≤ 1/log N ≤ 1/log 2`; integrate against `Φ²`: `O(w_N² L)`;
summed `O(L Σ|c_N|²/N)`.

*Off-diagonal `N ≠ M`, difference frequency.* The `τ′`-integral is
`[sin(τ′(log N − log M) + x log N − (φ_N − φ_M))/(log N − log M)]` evaluated at
the two endpoints of `I_x`, which are of the form `cc` or `cc − x` with
`cc ∈ {T, T + H}`. Integrating against `Φ(x)²` over `x` produces, for each
endpoint, an expression of the form
`Σ_{N≠M} w_N w_M · M_N · sin(cc(log N − log M) − (φ_N − φ_M)) / (log N − log M)`
(and a cosine twin) with `|M_N| ≤ W := ∫ Φ² = 2πbL` (`M_N` is `∫_0^∞ Φ² cos(x log N)`
or its sine companion, the tree's `Cm, Sm, Cp, Sp`). This is exactly the
shape of `MV_four`, and the weighted Hilbert inequality with frequencies
`log N`, spacing `δ_N = 1/(2N)` (for `N ≠ M ≤ X`, `|log N − log M| ≥ 1/(2 max(N,M))`),
bounds each such sum by `2 C_MV W Σ_N w_N² · 2N = O(L Σ |c_N|²)`. There are
eight such sums (two endpoints, sine and cosine, two orderings), all with
`cc ∈ {T, T + H}`; MV is uniform in `cc`.

*Off-diagonal, sum frequency.* `|1/(log N + log M)| ≤ 1/(2 log 2)`, so the
contribution is `O(W Σ_{N,M} w_N w_M) = O(L S₁(c)²)`.

Collecting: `𝓜_H[P_c,P_c] = (H/π) Σ |c_N|²/N g(log N) + O(L(Σ|c|²/N + Σ|c|² + S₁²))`.
For `c = c^T`: `Σ|c^T_N|²/N ≤ 2 l² ∫_0^λ D₁ ≪ l²` (H3 at `y = L`),
`Σ|c^T_N|² ≪ X l²` (H2), `S₁² ≪ X l²` (H1), so the error is `O(L l² X)`. ∎

The range enters only through `|I_x| = H − |x|` in the main term and through
the endpoint values `cc ∈ {T, T + H}`, which MV bounds uniformly. This is
Wang's `∫_I |D_x|² = H Σ a_n² + O(Σ n a_n²)` (his (2.19), MV Corollary 3),
with the smooth weight producing `g(log N)` in place of `1` and the
`Σ n a_n²` producing the `Σ|c_N|²` and `S₁²` terms.

> Error line. Size `O(L l² X)`; absorbed against `H L l²`; requires `X/H → 0`,
> i.e. `λ < θ` (condition 1). Audit P19-P21.

### Proposition 6.5 (cross terms, short window). `[NEW STATEMENT, PROOF WRITTEN HERE]`

The tree (`Zeta23/PrimeSideA/CrossMuP.lean:69-72`, `Zeta23/PrimeSideA.lean:408-411,
428-431, 449-452`, all with `Mform` over `[T, 2T]²`; the xi-prime fields
`cross_muP`, `cross_muPi`, `cross_PPi`, `cross_PiPi`, `Traces.lean:231-237`):

```
𝓜_H[μ, P_{c^T}] ≪ L l² √X,   𝓜_H[μ, Π_X] ≪ l L √X,   𝓜_H[P_{c^T}, Π_X] ≪ L X l,   𝓜_H[Π_X, Π_X] ≪ L X/T.
```

*Proof.* *`[μ, P_c]`.* For fixed `N ≥ 2` let
`Ψ(τ′) := ∫_{I_H} Φ(τ − τ′)² μ(τ) dτ`. Then `|Ψ| ≤ (l+1) · 2πbL`, and, integrating
by parts in `τ`, `Ψ′(τ′) = ±[μ(T)Φ(T−τ′)² − μ(T+H)Φ(T+H−τ′)²] + ∫_{I_H} Φ(τ−τ′)² μ′(τ) dτ`,
so `|Ψ′(τ′)| ≤ (l+1)(ψ(T−τ′)² + ψ(T+H−τ′)²) + C L/T`. Integrating by parts in `τ′`
against `e^{−iτ′ log N}`,

```
|∫_{I_H} Ψ(τ′) e^{−iτ′ log N} dτ′| ≤ (1/log N)(2 sup|Ψ| + ∫_{I_H}|Ψ′|) ≤ (1/log 2)(C l L + 2(l+1)∫ψ² + C L H/T) ≤ C l L,
```

using `∫ψ² ≪ L` and `H ≤ T`. Hence
`|𝓜_H[μ, P_c]| ≤ (1/π) Σ_N |c_N| N^{−1/2} · C l L ≤ C L l · √X l` by (H1).

*`[μ, Π_X]`.* On `I_H`, `|Π_X| ≤ C√X/T` and `|μ| ≤ l + 1`; trivially
`|𝓜_H| ≤ ∫_{I_H}∫_{I_H} Φ² |μ||Π_X| ≤ H · 2πbL · (l+1) · C√X/T ≤ C l L √X`.

*`[P_c, Π_X]`.* `|P_{c^T}| ≤ C√X l` uniformly (H1), so
`|𝓜_H| ≤ H · 2πbL · C√X l · C√X/T ≤ C L X l`.

*`[Π_X, Π_X]`.* `|𝓜_H| ≤ H · 2πbL · (C√X/T)² ≤ C L X/T`. ∎

The range enters only as `H/T ≤ 1`. (The tree's zeta versions use `|P_X| ≤ √X`
on `I` in place of (H1); the xi-prime remainders are the crude ones listed in
`Traces.lean:14-17`.) In the tree's `[μ, P_c]` proof the range appears
explicitly once: `abs_Mform_cos_phase_le`
(`Zeta23/PrimeSideA/CrossMuPCore.lean:151`, `hvol : volume.real (Icc T (2T)) = T`)
carries the length of `I` multiplied by `D := sup |μ′|`, and `D · T = O(1)`
since `|μ′| ≤ C/T`; localized, `volume.real I_H = H` and `D · H ≤ D · T = O(1)`
(re-audit). That is the `(C/T) · H · (l+1) log L` term above.

> Error lines. Sizes `O(L l² √X)`, `O(l L √X)`, `O(L X l)`, `O(L X/T)`;
> absorbed against `H L l²`; require `√X/H → 0` (first two; `λ/2 < θ`) and
> `X/(H l) → 0` (third; `λ < θ`). Audit P24.

### Proposition 6.6 (the two moments). `[NEW STATEMENT, PROOF WRITTEN HERE]`

The tree's assembly is `TracesBoundsXi` (`Zeta23/XiPrime/PrimeSide/Traces.lean:53-64`,
from the fields of `FactsXi`, `:203-237`) followed by `momentsW_of_family`
(`Zeta23/XiPrime/PrimeSide/Moments.lean:96-107`), with

```lean
def mainTr2Xi (P : Params) (bT JT : ℝ → ℝ) (T : ℝ) : ℝ :=
  T * P.L T / (2 * π) * (bT T * ell1 T ^ 2 + P.L T ^ 2 * JT T)
```

```lean
structure TracesBoundsXi (P : Params) (aT bT JT trG trG2 Ncnt : ℝ → ℝ) : Prop where
  tr1' : trG ~[atTop] (fun T => aT T * P.L T * Ncnt T)
  tr2 : trG2 ~[atTop] mainTr2Xi P bT JT
  ratio : (fun T => trG T ^ 2 / trG2 T)
    ~[atTop] (fun T => ThmD.cRatio (P.lam1 T) (aT T) (bT T) (JT T) * Ncnt T)
  frhat : (fun T => trG2 T / (aT T * P.L T) ^ 2)
    ~[atTop] (fun T => (ThmD.cRatio (P.lam1 T) (aT T) (bT T) (JT T))⁻¹ * Ncnt T)
```

and `cRatio lam1 a b J = lam1 a²/(b + lam1² J)` (`Zeta23/ThmD/AssemblyD.lean:28`).

**Statement.** With `M⋆_H := (HL/2π)(b ℓ_H² + L² J_T)`:

```
(i)   tr M̃^T_H ~ a L N_H;
(ii)  tr (M̃^T_H)² := L^{−2} Σ_{k,l<d_H} (M^T_kl)² ~ M⋆_H;
(iii) (tr M̃^T_H)² / tr(M̃^T_H)² ~ cRatio(L/ℓ_H; a, b, J_T) · N_H;
(iv)  ‖M̂^T_H‖_F² = tr(M̃^T_H)²/(aL)² ~ cRatio(L/ℓ_H; a, b, J_T)^{−1} · N_H;
(v)   cRatio(L/ℓ_H; a, b, J_T) → cWin D₁ λ v = c_λ(v; D₁) > 0,
```

hence `CoeffMoments_H` holds with `κ = kappaXi λ v = 1/c_λ(v; D₁)`.

*Proof.* (i) is Proposition 6.1 with Corollary 2.4(e).

(ii). By Lemma 6.2, `tr(M̃^T_H)² = 𝓜_H[ν,ν] + O(L l³ log l (1+X))`, and by
bilinearity (the tree's `Msplit`)
`𝓜_H[ν,ν] = 𝓜_H[μ,μ] + 𝓜_H[P,P] + 2𝓜_H[μ,P] + 2𝓜_H[μ,Π] + 2𝓜_H[P,Π] + 𝓜_H[Π,Π]`.
Insert 6.3, 6.4, 6.5 and `sumJ`:

```
𝓜_H[ν,ν] = (HL/2π) b ℓ_H² (1 + O(l^{−2})) + (H/π)((L³/2) J_T + o(l² L)) + O(l² log L + L l² X + L l² √X + l L √X + L X l + L X/T)
         = (HL/2π)(b ℓ_H² + L² J_T) + o(H L l²) + O(L l² X).
```

Since `b ≥ 1/2` eventually and `J_T ≥ 0` (`FactsXi.ab_range`), `M⋆_H ≥ H L l²/(4π)`,
and every remainder, including Lemma 6.2's, is `o(H L l²)` by Corollary 2.4(e)
under `λ < θ`. So `tr(M̃^T_H)² = M⋆_H (1 + o(1))`. (In the tree this is `tr2`,
whose remainder collection uses `l² X/T ≤ T^{(λ−1)/2}`,
`Traces.lean:125-139`; here `l² X/H → 0`.)

(iii) and (iv). The two exact identities (`Traces.lean:243-246, 258-260`,
with `T ↦ H`, `ℓ ↦ ℓ_H`):

```
(aLN)² / ((HL/2π)(bℓ² + L²J)) = cRatio(L/ℓ; a, b, J) · N · (N/(Hℓ/2π)),
(HL/2π)(bℓ² + L²J) / (aL)² = cRatio(L/ℓ; a, b, J)^{−1} · (Hℓ/2π),
```

together with (i), (ii), and `N_H/(Hℓ_H/2π) → 1` (Corollary 2.4(g)).

(Re-audit, `lam1`.) The tree hard-wires `Params.lam1 = L/ell1`
(`Zeta23/Defs.lean:209-210`, `def lam1 : ℝ := P.L T / ell1 T`), and both
`TracesBoundsXi.ratio`/`frhat` (`Traces.lean:60-64`, quoted above) and the
hypothesis `hc` of `momentsW_of_family` (`Moments.lean:105-108`) are stated in
`P.lam1 T`. The localized package (ii)-(iv) is therefore a *restatement* with
`λ_{1,H} = L/ℓ_H` in place of `P.lam1 T` (equivalently with `L/l`, since both
tend to `λ`), not the tree's statement with a substitution; its proof is the
two identities above, which are stated for an arbitrary `ℓ ≠ 0`. The consumer
`tendsto_cRatio_cWin` takes an arbitrary `lam1f → λ` (its `hl1`), so nothing
downstream of the restatement changes. `MomentsW` itself
(`Moments.lean:81-86`) carries `Z.N T (2 * T)` and is restated with `N_H`.

(v). `L/ℓ_H → λ` (Lemma 2.1(iii)); `a_T → ∫_{−1/2}^{1/2} v`, `b_T → ∫ v²`,
`J_T → jWin D₁ λ v / λ` (the window limits W2, W3 of `Zeta23/XiPrime/Window.lean`:
`tendsto_JT_of_autocorr_close`, `:122`, and for the flat window
`tendsto_a_flat`, `tendsto_b_flat`, `tendsto_JT_flat`, `:230-281`; all about
the taper at scale `L`, range-free, `[KERNEL-CHECKED, DYADIC]`); then
`tendsto_cRatio_cWin` (`Window.lean:92-98`):

```lean
theorem tendsto_cRatio_cWin {lam : ℝ} (h0 : 0 < lam) {lam1f aT bT JT : ℝ → ℝ}
    (hl1 : Tendsto lam1f atTop (𝓝 lam))
    (ha : Tendsto aT atTop (𝓝 (∫ s in (-(1:ℝ)/2)..(1/2), v s)))
    (hb : Tendsto bT atTop (𝓝 (∫ s in (-(1:ℝ)/2)..(1/2), v s ^ 2)))
    (hJ : Tendsto JT atTop (𝓝 (jWin D lam v / lam)))
    (hden : 0 < (∫ s in (-(1:ℝ)/2)..(1/2), v s ^ 2) + lam * jWin D lam v) :
    Tendsto (fun T => ThmD.cRatio (lam1f T) (aT T) (bT T) (JT T)) atTop (𝓝 (cWin D lam v))
```

with `hden` from `cWin_denom_pos` (`:79`, using `D₁ ≥ 0` on `[0,1]` and `v > 0`).
Positivity `cWin D₁ λ v > 0` is `cWin_pos` (`:71`). Then (iv) and (v) give
`‖M̂^T_H‖_F² ≤ (κ + δ) N_H` eventually for every `δ > 0`, and (i) gives
`(1 − δ) N_H ≤ tr M̂^T_H ≤ (1 + δ) N_H`. ∎

The only change from the tree's `momentsW_of_family` is the substitution
`T ↦ H` in the main terms, `ℓ₁ ↦ ℓ_H`, `Ncnt ↦ N_H`, and the regime facts
`l^k X/T → 0` replaced by `l^k X/H → 0`. This is where Wang's condition
`λ < θ` does all of its work, seven times (audit condition 1).

---

## 7. Assembly and the limit `λ → θ` (Wang §3 (3.7)-(3.9); audit step 7)

### 7.1 Moments of the zero-side Gram matrix. `[KERNEL-CHECKED, DYADIC]` (generic algebra)

`Zeta23/XiPrime/Assembly.lean:37-39`:

```lean
theorem gzMoments_of_transfer (Z : ZeroConfig) (Pf : ℝ → Params) (F : CoeffFamily) {κ : ℝ}
    (hκ : 0 ≤ κ) (hCM : CoeffMoments Z Pf F κ) (hTT : XiTraceTransfer Z Pf F) :
    GzMoments Z Pf κ
```

with `GzMoments` (`Statement.lean:246-248`): `(1 − δ)N ≤ tr Ĝ` and
`‖Ĝ‖_F² ≤ (κ + δ)N` eventually. The proof is two filter arguments and the
inequality `(1+η)(κ+η) + η ≤ κ + δ` for `η = min(1, δ/(κ+3))`; `N` is an
arbitrary nonnegative function of `T`. Applied to `CoeffMoments_H` (6.6) and
`XiTraceTransfer_H` (§5) with `N = N_H` it gives `GzMoments_H`:

```
(1 − δ) N_H ≤ tr Ĝ_H    and    ‖Ĝ_H‖_F² ≤ (κ + δ) N_H,   eventually, every δ > 0.
```

### 7.2 The count certificate. `[NEW STATEMENT, PROOF WRITTEN HERE]`

The tree (`Zeta23/Assembly/Certificate.lean:39-54`):

```lean
theorem count_certificate (Z : ZeroConfig) (P : Params) (κ : ℝ) (lower : ℝ → ℝ)
    (θ₀ : ℝ → ℝ)
    (h0 : ∀ᶠ T in atTop, 4 * rtrace (P.hat T (Z.Gz P T)) - frobSq (P.hat T (Z.Gz P T))
      - 2 * (Z.N T (2 * T) : ℝ) - 3 * (NII Z T : ℝ)
      - θ₀ T / (P.a T * P.L T)
          * (4 + 2 * Real.sqrt (frobSq (P.hat T (Z.Gz P T))) + θ₀ T / (P.a T * P.L T))
      ≤ lower T)
    (hB0 : ∀ᶠ T in atTop, 0 ≤ θ₀ T / (P.a T * P.L T))
    (hBto : Tendsto (fun T => θ₀ T / (P.a T * P.L T)) atTop (𝓝 0))
    (hNII_o : (fun T => (NII Z T : ℝ)) =o[atTop] (fun T => (Z.N T (2 * T) : ℝ)))
    (hNtop : Tendsto (fun T => (Z.N T (2 * T) : ℝ)) atTop atTop)
    (htrace : ∀ δ > (0:ℝ), ∀ᶠ T in atTop,
      (1 - δ) * (Z.N T (2 * T) : ℝ) ≤ rtrace (P.hat T (Z.Gz P T)))
    (hfrob : ∀ δ > (0:ℝ), ∀ᶠ T in atTop,
      frobSq (P.hat T (Z.Gz P T)) ≤ (κ + δ) * (Z.N T (2 * T) : ℝ)) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀, (2 - κ - ε) * (Z.N T (2 * T) : ℝ) ≤ lower T
```

**Proof of Theorem A.** Let `κ = kappaXi λ v ≥ 0`. Fix `ε > 0` and put
`δ = ε/8`. Eventually in `T`, all of the following hold: Lemma R (3.6),
`B ≥ 0` and `B ≤ δ` (3.4), `3 NII_H ≤ δ N_H` (3.5, `β < θ`), `N_H ≥ 1` and
`B ≤ δ √N_H / (2√(κ + 1))` (2.4(b) and `B → 0`), and `GzMoments_H` at `δ` (7.1).
Then, from Lemma R's first line,

```
N^s_{0,ξ′}(I_H) ≥ 4(1−δ)N_H − (κ+δ)N_H − 2N_H − δN_H − B(4 + 2√((κ+δ)N_H) + B)
                ≥ (2 − κ − 6δ) N_H − 4δ − δ N_H − δ²
                ≥ (2 − κ − 8δ) N_H = (2 − κ − ε) N_H,
```

using `2B√((κ+δ)N_H) ≤ 2B√((κ+1)N_H) ≤ δ N_H` and `4B + B² ≤ 5δ ≤ δ N_H`.
From Lemma R's second line, with `δ = ε/10`,

```
2 N_{d,ξ′}(I_H) ≥ 6(1−δ)N_H − (κ+δ)N_H − 3N_H − (5/3)δN_H − B(6 + 2√((κ+δ)N_H) + B) ≥ (3 − κ − 10δ) N_H,
```

so `N_{d,ξ′}(I_H) ≥ (3/2 − κ/2 − ε/2) N_H ≥ (3/2 − κ/2 − ε) N_H`. ∎

This is `count_certificate` and `count_certificate_c3` with `N ↦ N_H`,
`NII ↦ NII_H`; nothing in the algebra sees the range. It is also Wang's
(3.7)-(3.8): `N^s_0(I) ≥ 2N(I) − S_K(I)` with `S_K(I) = (C(f) + o(1)) HL/2π`,
where here `S_K ↔ ‖Ĝ_H‖_F² + (4 tr Ĝ_H − 4N_H) ≈ κ N_H`.

### 7.3 Proof of Theorem B: `λ → θ⁻`. `[NEW STATEMENT, PROOF WRITTEN HERE]`

Continuity (`Zeta23/XiPrime/Window.lean:338-341`):

```lean
theorem continuousOn_kappaXi (hv : Continuous v) (hv0 : ∀ s ∈ Icc (-(1:ℝ)/2) (1/2), 0 ≤ v s)
    (ha : (∫ s in (-(1:ℝ)/2)..(1/2), v s) ≠ 0) (hb : 0 < ∫ s in (-(1:ℝ)/2)..(1/2), v s ^ 2) :
    ContinuousOn (fun lam => kappaXi lam v) (Ioc 0 1)
```

whose hypotheses follow from `WindowProfile v` (`[KERNEL-CHECKED, DYADIC]`,
W4; for the flat and quartic profiles, `continuousOn_kappaXi_vFlat`,
`Window.lean:391`, and `continuousOn_kappaXi_vQuartic`, `:395`, on `Ioc 0 1`).

(Re-audit.) The tree's limit device is hard-wired to the endpoint `1` and the
interval `Icc (1/2) 1`: `ThmD.eps_form_of_approx` (`Zeta23/ThmD/Limit.lean:73-78`),

```lean
theorem eps_form_of_approx {g : ℝ → ℝ} {N lower : ℝ → ℝ}
    (hg : ∀ δ : ℝ, 0 < δ → ∃ lam : ℝ, 1/2 ≤ lam ∧ lam < 1 ∧ g 1 - δ ≤ g lam)
    (hN : ∀ T, 0 ≤ N T)
    (h : ∀ lam : ℝ, 1/2 ≤ lam → lam < 1 →
      ∀ ε > 0, ∃ T₀, ∀ T ≥ T₀, (g lam - ε) * N T ≤ lower T) :
    ∀ ε > 0, ∃ T₀, ∀ T ≥ T₀, (g 1 - ε) * N T ≤ lower T
```

`exists_lt_one_pos` (`Window.lean:345`, `ContinuousOn f (Icc (1/2) 1)`,
`0 < f 1 → ∃ lam ∈ [1/2, 1), 0 < f lam`) and `eps_form_of_continuousOn`
(`:364-367`). A version with endpoint `θ` is a new lemma, trivial but not
verbatim:

#### Lemma 7.3′ (the `λ → θ⁻` device). `[NEW STATEMENT, PROOF WRITTEN HERE]`

Let `0 < θ ≤ 1`, `g` continuous on `[θ/2, θ]`, `N(T) ≥ 0`, and suppose that
for every `λ ∈ [θ/2, θ)` and every `ε > 0` there is `T₀` with
`(g(λ) − ε) N(T) ≤ lower(T)` for all `T ≥ T₀`. Then for every `ε > 0` there is
`T₀` with `(g(θ) − ε) N(T) ≤ lower(T)` for all `T ≥ T₀`.

*Proof.* Given `ε > 0`, continuity of `g` at `θ` within `[θ/2, θ]` gives
`δ ∈ (0, θ/2)` with `g(λ) ≥ g(θ) − ε/2` for `λ ∈ [θ − δ, θ]`; take
`λ = θ − δ/2 ∈ [θ/2, θ)`. The hypothesis at this `λ` with `ε/2` gives `T₀`
with `(g(λ) − ε/2) N ≤ lower`, and `g(λ) − ε/2 ≥ g(θ) − ε`; multiply by
`N ≥ 0`. ∎

Apply Lemma 7.3′ with `g = 2 − kappaXi(·, v)`, `N = N_H`, `lower = N^s_{0,ξ′}(I_H)`
(continuity on `[θ/2, θ] ⊂ (0, 1]` from `continuousOn_kappaXi`; the
hypothesis at every `λ ∈ [θ/2, θ)` is Theorem A), and again with
`g = 3/2 − kappaXi(·, v)/2`, `lower = N_{d,ξ′}(I_H)`. Divide by `N_H > 0`
(Corollary 2.4(b)) and take `liminf`. ∎

This is the device of `xiDeriv_simple_on_line_limitForm`
(`Zeta23/XiPrime/Final.lean:227-249`) with the limit point `1` replaced by
`θ`, and it is Wang's final paragraph ("finally let `λ → θ` and use (4.2)").

### 7.4 Against the zeta count. `[NEW STATEMENT, PROOF WRITTEN HERE]` (one line, from Wang (1.2))

The tree compares the two configurations only dyadically
(`eventually_zetaCount_le_Ncount`, `Zeta23/XiPrime/Final.lean:279-298`) and
states `N_{ξ′}(T) = N(T) + O(log T)` only in docstrings; neither is used.
Wang's (1.2), `N_ζ(T, T+H) = H log T/2π + O(H + log T)` for `1 ≤ H ≤ T`,
is a consequence of the classical Riemann-von Mangoldt formula (1.1) (his
reference: Davenport, Chapter 15), and Lemma 2.3 gives the same asymptotic for
`N_{ξ′}`. Hence `N_{ξ′}(T, T+T^θ)/N_ζ(T, T+T^θ) → 1` for `θ > 0`, and both
liminf bounds of Theorem B hold verbatim with `N_ζ(T, T+T^θ)` in the
denominator. (Within the tree, the zeta version of Lemma 2.3 is
`rvM_main_param`, `Zeta23/RvM/MainTerm.lean:215-221`, localized by the same
good-height argument as Lemma 2.3, with Backlund's horizontal bound in place
of `halfContour_Yfn_bound`.)

---

## 8. The window at bandwidth θ (Wang §4; audit step 8)

The constant of the tree (`Zeta23/XiPrime/Defs.lean:176-188`):

```lean
def jWin (D : ℝ → ℝ) (lam : ℝ) (v : ℝ → ℝ) : ℝ := 2 * ∫ r in (0:ℝ)..1, (D (lam * r) * vConv v r)
def cWin (D : ℝ → ℝ) (lam : ℝ) (v : ℝ → ℝ) : ℝ :=
  lam * (∫ s in (-(1:ℝ)/2)..(1/2), v s) ^ 2 /
    ((∫ s in (-(1:ℝ)/2)..(1/2), v s ^ 2) + lam * jWin D lam v)
def kappaXi (lam : ℝ) (v : ℝ → ℝ) : ℝ := 1 / cWin D1 lam v
```

with `vConv v r = ∫_{−1/2}^{1/2 − r} v(s) v(s+r) ds` and, for the flat window
(`Window.lean:222`, `kappaXi_vFlat`), `kappaXi λ 1 = 1/λ + 2∫_0^1 (1 − r) D₁(λr) dr`.
`[KERNEL-CHECKED, DYADIC]`, and range-free: no `T` appears.

Theorem B holds for every admissible `v`. The best bound the method yields at
bandwidth `θ` is `2 − inf_v kappaXi θ v`. Three remarks, none of them a claim:

1. Wang's Proposition 4.1 (unique minimizer `cos(√2 u)/(√2 sin(λ/√2))`,
   minimum `λ/2 + (1/√2) cot(λ/√2)`) is specific to the kernel `|u − v|`: its
   Euler-Lagrange equation `f″ + 2f = 0` comes from differentiating
   `∫|u − v| f(v) dv` twice. With `D₁` in place of `|·|` no closed form is
   claimed here and none is in the tree.
2. `MISSION.md` §5 measures that the window-shape gain decays like `λ³/180`
   with bandwidth, so at bandwidth `θ` the flat window is close to optimal;
   that is a measurement, not an input to the proof.
3. The constant is `2 − kappaXi(θ, v)`, enclosed separately, see `RESULTS.md`.
   No decimal is stated here, per condition 5 of the audit. The theorem is
   nonvacuous exactly when `kappaXi θ v < 2` (simple on-line) resp.
   `kappaXi θ v < 3` (distinct), which the enclosure decides.

The tree's ε-free decimals `CertFlat`/`CertQuartic`
(`Statement.lean:266-274`) are strict at some `λ ∈ [1/2, 1)` and do not
transfer to bandwidth `θ`; they are not used.

---

## 9. Exponent ledger

Every error term of the proof, with its size, what it is absorbed against, and
the condition on the exponents it needs. `E ≍ T^{c + o(1)}` is absorbed
against `H l ≍ T^{θ + o(1)}` iff `c < θ`.

| Where | Error `E` | Absorbed against | Requires | Audit item |
|---|---|---|---|---|
| 2.1 | `ℓ_H − l ≤ H/T` | `1` | none | D4 |
| 2.2(i) | `1/T` | `H l` | none | S2 |
| 2.2(ii) | relative `1/l²` | `1` | none | S2 |
| 2.3 | `log T` | `H l` | `θ > 0` | S9, P35 |
| 3.4 | `B ≍ l T^{λ/2 − 2β}/L` | `1` (`B → 0`) | `β > λ/4` | P3, P5 |
| 3.5 | `NII_H ≍ T^β l` | `H l` | `β < θ` (condition 2) | P4, P6 |
| 4 | entry error `T^{−δ}(min(1,Δ^{−2}) + 1/T)` | via 5.2 | `δ > 0` | P28, P30 |
| 5.2 trace | `H T^{−δ}/L` | `H l` | none | P13 |
| 5.2 Frobenius | `H T^{−2δ}/L²` | `H l` | none | P14 |
| 5.4 trace | `√X` | `H l` | `λ/2 < θ` | P17 |
| 5.4 Frob. main | `H` | `H l` | none (`l → ∞`) | P18 i1 |
| 5.4 Frob. ends | `l⁴(1 + X)/L` | `H l` | `λ < θ` (condition 1) | P15, P16, P18 i2, P19 |
| 6.1 | `L √X l` | `L H l` | `λ/2 < θ` | P24 prop_trace |
| 6.2 | `L l³ log l (1 + X)` | `H L l²` | `λ < θ` (condition 1) | P22 |
| 6.3 | `l² log L` | `H L l²` | none | P25 |
| 6.4 | `L l² X` | `H L l²` | `λ < θ` (condition 1) | P19-P21, D7 |
| 6.5 | `L l² √X`, `l L √X`, `L X l`, `L X/T` | `H L l²` | `λ/2 < θ`, `λ < θ` | P24 cross terms |
| 6.6 | `o(l² L)` from (H3) | `H L l²` | none (range-free) | (H3) |
| 7.2 | `B √N_H`, `B`, `B²` | `N_H` | `B → 0` | P10 |

The two places the audit named as the only carriers of a hidden `T^{1−θ}`
are visible: the `X`-sized errors (rows 5.4 ends, 6.2, 6.4, 6.5), one
mechanism, Wang's own condition; and the end strips (row 3.5), condition 2.
Everything else scales with the range length or is a height power saving.

---

## 10. Comparanda

The claim, in the form the literature search of `RESULTS.md` §4.1 licenses:

> **First power-length statement for the zeros of `ξ′`: proportions of
> simple on-line and of distinct zeros in `(T, T + T^θ]`, for every fixed
> `θ < 1`, as a function of `θ`, unconditionally.**

It is not the first short-interval statement for `ξ′`, and must not be
called one. The comparanda:

- **Rezvyakova** (Izv. Math. 69 (2005), 70 (2006)), following Conrey (JNT 17
  (1983)): in the sub-dyadic windows `(T, T + U]`, `U = T (log(T/2π))^{−10}`,
  a proportion of simple on-line zeros of `ξ^{(k)}` exceeding
  `1 − ((e² + 2)/16) k^{−2}`, uniformly in `k` up to
  `(1/2) log log T / log log log T`; at `k = 1` about `0.413`. The window there
  is `T/(log T)^{10}`, longer than `T^θ` for every fixed `θ < 1`; the present
  statement is for power-length windows and carries an explicit `θ`-curve.
- **Conrey** (JNT 16 (1983), §2 and the table restated by Rezvyakova): at full
  range, on-line proportion of `ξ′` zeros at least `0.79874` (the `k = 1`
  entry; simple on-line is the object of the present statement).
- **Chirre, Gonçalves and de Laat** (arXiv:1810.08843, Corollary 7): under RH,
  full range, `0.8825` simple and `0.9412` distinct for `ξ′`. Any conditional
  curve at `θ → 1` is compared against these; the present statement is
  unconditional and, as `θ → 1⁻`, tends to the tree's `2 − kappaXi(1, v)`,
  the unconditional dyadic figure of `xiDeriv_simple_on_line_limitForm`.
- **Wang** (arXiv:2609.07918, Theorem 1.1): the same shape of statement for
  `ζ` itself, with the closed-form curve `c(θ) = 2 − θ/2 − (1/√2)cot(θ/√2)`,
  positive for `θ > θ₀ = 0.550193…`. The present statement is Wang's
  Theorem 1.1 with `ζ` replaced by `ξ′`, the kernel `|α|` replaced by `D₁`,
  and the second moment supplied by the kernel-checked xi-prime development
  rather than by BGSTB's Lemma 5.

What is not claimed: novelty beyond the documented search; any decimal for the
xi-prime curve; optimality of the window; anything about RH.

---

## 11. The Hardy `Z′` arm

The tree formalizes the same headline for `W := ζ′ + L₂ ζ` (so that
`Z′(t) = i e^{iϑ(t)} W(1/2 + it)`), `Zeta23/XiPrime/Final.lean:516-520`:

```lean
theorem hardyW_simple_on_line :
    ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (0.85838 : ℝ) * (NcountW T (2 * T) : ℝ) ≤ (N0simpleW T (2 * T) : ℝ) ∧
      (0.92919 : ℝ) * (NcountW T (2 * T) : ℝ) ≤ (NdistW T (2 * T) : ℝ)
```

with configuration `wZeros` (`Statement.lean:349-355`, carrier the zeros of
`W` with `|Im ρ| ≥ t₀`), strip fact `wZerosInStrip_holds`
(`Hardy/ZeroFree.lean:547`), seam `WSeam t₀` (`Statement.lean:338-343`), count
`hardyW_rvM_main` (`Hardy/Count.lean:257-260`, an instance of the same
`rvM_main_of`), coefficient family `wCoeffFamily = C(·; l/2)` with real base
and the same density `D₁` (`Statement.lean`, `wCoeffFamily`,
`wCoeffFamily_hyps`, `Coeff.lean:49`), explicit formula `wEF_flat`
(`Final.lean:475-477`), and the same window constant `kappaXi`.

**Does the proof above go through verbatim?** Yes, with the following
substitutions and no new mathematics, as the audit states (its §6, last
paragraph):

- §2: replace `xiDeriv` by `W`, `GoodHeight` by `GoodHeightW`,
  `halfContour_Yfn_bound` by `halfContour_hardyW_bound`
  (`Hardy/Count.lean`, conclusion `≤ C log(|T₁|+3) + 2π + C log(|T₂|+3)`),
  `xiDeriv_local_count` by the `W` local count; the argument of Lemma 2.3 is
  literally `hardyW_rvM_main`'s `rvM_main_of` instance with the upper good
  height at `T + H`. Heights below `t₀` never enter for `T ≥ t₀`.
- §3: the configuration `wZeros` is reflection-closed with finite windows
  (`WSeam`), so 3a-3d apply unchanged.
- §4, §5: the `W` explicit formula is again entrywise on the same grid
  (Observation 1.1 applies); the density is `ν^𝒵_c = μ + 2Π_X + P_c`
  (`nucZ`, `Defs.lean:116`, pole weight 2 instead of 1), which changes a
  constant in the `Π_X` bounds of 6.1 and 6.5 and nothing else; the
  re-expansion is about the real base `l/2` (`Transfer/W.lean`), with the same
  `δ_kl ∈ [0, H/2T]` (Lemma 5.3). The `W` transfer closes against
  `N(T, 2T)` at `Zeta23/XiPrime/Transfer/W.lean:306, 333, 337`
  (`η * (T * l T/(4π)) ≤ η * N`, and the Frobenius `κ₂² X ≤ κ₂² T ≤ (η²/4π) l T`),
  exactly as `Transfer.lean:378, 425, 736, 784` do for `ξ′`; localized by
  Corollary 2.4(a) and, for the `X ≤ T` step, by `X = o(H l)` under
  `λ < θ` (re-audit).
- The dictionary between `N^s_{0,W}` and the simple stationary points of
  Hardy's `Z` is stated dyadically: `simpleStationaryZ T := {t ∈ Ioc T (2T) |
  Z′(t) = 0 ∧ Z″(t) ≠ 0}` and `ncard_simpleStationaryZ : (simpleStationaryZ T).ncard
  = N0simpleW T (2 * T)` (`Zeta23/XiPrime/Hardy/ZFunction.lean:339-366`). The
  bijection `t ↦ 1/2 + it` is height-by-height, so the same statement holds
  with `Ioc T (T + H)` and `N0simpleW T (T + H)`; class (a) (re-audit).
- §6: `wCoeffFamily_hyps` gives (H1)-(H3) with the same `D₁`, so 6.1-6.6
  hold with the same statements and `κ = kappaXi λ v`.
- §7, §8: unchanged.

So Theorems A and B hold with `(N_{ξ′}, N^s_{0,ξ′}, N_{d,ξ′})` replaced by
`(N_W, N^s_{0,W}, N_{d,W})`, i.e. for the simple real stationary points of
Hardy's `Z` in `(T, T + T^θ]`, with the same constant `2 − kappaXi(θ, v)`.
Equally absent from the short-interval literature (`RESULTS.md` §4.1). It
should be stated in the same paper.

---

## 12. What a Lean port would touch (brief)

Not part of the proof; recorded so the draft and the audit's footprint agree.
Observation 1.1 says the entrywise layer (`XiEF`, `Reexpansion`, `deltaKL`,
`Gentry*`) needs no change if the grid size becomes a parameter. What needs a
second range parameter: `Iwin`, `Iprime`, `d`, `ZIprime`, `NIprime`, `NII`
(`Zeta23/Defs.lean`, `Assembly/Inputs.lean`); the short-window
`RiemannVonMangoldt`, `int_mu`, `int_mu_sq` (§2; the contour-form count 2.3,
two `μ`-lemmas and one new scalar `ℓ_H`); `Tail/Count.lean`'s endpoints and
constant, and `Tail/Basic.lean:18, 36` (`distI`, `InTail`, both written with
`2T`); `Mform`'s domain and `Setting.T` split into a height and a length
(`PrimeSideA/Defs.lean:65-87` derives `d`, `tau`, `I` from `T`; the split is
listed occurrence by occurrence in §6.0); `PrimeSideA/Basic.lean:876-890`
(`riemann_sum_monotone`) and `PrimeSideA.lean:137-150` (its use in
`prop_trace_mu`); `PrimeSideA/EndsE1.lean:262-266` (`tau_d_gt`),
`EndsWeighted.lean:218-229`, `Defs/LeafIntegrals.lean:25, 51, 77`;
`CrossMuPCore.lean:151` (`hvol`); the `ThmE/PPChi.lean` layer
(`diag_estimate_chi:520-525`, `O1_bound_chi:615-640`) and `ThmE/PrimeSideChi.lean`
(the twisted prime side it sits in), `PrimeSideB/PPKernel.lean`,
`PPOffDiag.lean`, `MuMu.lean:71`, `XiPrime/PrimeSide/Concrete.lean:62-66, 96`
(`PPInput`, `intMu2 := ∫_T^{2T} μ²`), and `PP.lean`'s two `MV_four` endpoints;
`Transfer.lean`'s `d_le`, `tau_lt_two_T` and its four `N` comparisons
(`:378, 425, 736, 784`), `Transfer/W.lean:306, 333, 337`; `Defs.lean:209-210`
(`lam1`) or, instead, `Traces.lean:60-64` and `Moments.lean:81-109`
(`MomentsW`, `momentsW_of_family`'s `hc`); `Traces.lean`'s `mainTr2Xi` and
regime; `ThmD/Limit.lean:73-78` and `Window.lean:345, 364-373` (the endpoint
`1` device, replaced by Lemma 7.3′); `Hardy/ZFunction.lean:339-366`; the
`N(T, 2T)` in the six interface `Prop`s of `Statement.lean`. Untouched:
`Coeff/`, `Window.lean` apart from the two limit lemmas, `ZeroSide/`,
`LinAlg`, `MV/`, `WeilEF/`, the strip and seam files, and every
`Certificate/` decimal (which is replaced, not edited). The audit's suggestion
stands: make the range `(T, U)` a parameter with `U = 2T` recovering the tree,
so that "never hard-code `2T`" is enforced by the type; the re-audit adds that
the parameter must reach `Setting`, not stop at `Params`.

---

## 13. Revision after the adversarial re-audit

`AUDIT-dyadic-adversarial.md` (2026-09-12, section D) re-checked every
citation of the gating audit, confirmed PASS WITH CONDITIONS, and corrected
two conditions and eight points of the outline. Every Lean fact it names was
opened at commit `fbdc36bb` before the corresponding edit. What changed in
this document, in the order of section D:

1. **Step 2, statement shape (condition 3).** Lemma 2.3 now states
   `|N_{ξ′}(T,T+H) − ∫_T^{T+H} μ| ≤ C log T` and proves it from the contour
   chain alone; Corollary 2.3′ derives the `prop_trace` form
   `|N_H − H ℓ_H/2π| ≤ C log T` and Wang's (1.2). The `H²/T` moved to
   Lemma 2.1 where it belongs. `prop_trace_W` (`Trace.lean:184-188`) and
   `rvm_evBound` (`Moments.lean:110`) are quoted as the consumers.
2. **Step 6a.** Proposition 6.1 now also records the tree's own route,
   `riemann_sum_monotone` (`Basic.lean:876-890`) inside `prop_trace_mu`
   (`PrimeSideA.lean:137-150`), localized with `d_H = ⌊H/h⌋`; and the Poisson
   route's bound `(R)` names Lemma 1.2 as the place the lower floor
   inequality is load-bearing.
3. **Step 6b.** Lemma 6.2 cites `tau_d_gt` (`EndsE1.lean:262-266`),
   `sum_psiA_shift_right` (`EndsWeighted.lean:218-229`) and the three leaf
   integrals (`Defs/LeafIntegrals.lean:25, 51, 77`) at the lines that use them.
4. **Step 6d.** Proposition 6.4 cites the `ThmE/PPChi.lean` layer
   (`diag_estimate_chi:520-525` quoted; `O1_bound_chi:615-640`; `Aminus`,
   `Cm/Sm/Cp/Sp`, `MV_four`, `Mform_cos_cos_ph`), `ThmE/PrimeSideChi.lean`,
   `PrimeSideB/PPKernel.lean`, `PPOffDiag.lean:40`, `MuMu.lean:71`, and says
   which `T` is the range length and which the endpoint. §12's "to touch"
   list carries the omitted files.
5. **`Setting.T`.** A paragraph in §6.0 lists, occurrence by occurrence, which
   `p.T` become `H` and which stay `T`, with `eT` in `reexpansionGeom_of` as
   the pin; §12 says the `(T, U)` parameter must reach `Setting`.
6. **Step 7.** The `λ → θ⁻` device is Lemma 7.3′, `[NEW STATEMENT, PROOF
   WRITTEN HERE]`, with `eps_form_of_approx` (`ThmD/Limit.lean:73-78`) and
   `exists_lt_one_pos` (`Window.lean:345`) quoted as the endpoint-`1`
   originals it replaces; continuity from `continuousOn_kappaXi` (`:338-341`,
   `:391`, `:395`).
7. **Step 6f, `lam1`.** Proposition 6.6 says that (ii)-(iv) are a
   restatement of `TracesBoundsXi.ratio`/`frhat` and of `momentsW_of_family`'s
   `hc` with `λ_{1,H} = L/ℓ_H` for `Params.lam1`, and why nothing downstream
   changes (`tendsto_cRatio_cWin` takes any `lam1f → λ`).
8. **Ordering.** Corollary 2.4 and the introduction of §5 cite
   `Transfer.lean:378, 425, 736, 784` as the four closes against
   `T l/4π ≤ N`, replaced by `H l/4π ≤ N_H`.

Also: Lemma 1.2 (both floor inequalities) added to §1; condition 4 restated
in the Status section and in table 0.3; the Hardy arm (§11) cites
`Transfer/W.lean:306, 333, 337` and `Hardy/ZFunction.lean:339-366`. The
Status table went from 23 to 26 `[NEW STATEMENT]` items (Lemma 1.2,
Corollary 2.3′, Lemma 7.3′); the 14 `[KERNEL-CHECKED, DYADIC]` items and the
zero `[ASSERTED]` items are unchanged. No tag was softened. Nothing in the
re-audit changed an exponent, a condition on `θ`, or the constant.

---

## Files

- This document: `hunts/short_interval/PROOF-DRAFT.md`.
- Sources read: `hunts/short_interval/AUDIT-dyadic.md` (in full);
  `hunts/short_interval/MISSION.md` §2, §3, §5, §6; Wang arXiv:2609.07918v1,
  Sections 1-4 (LaTeX alt-text of the arXiv HTML); Lamzouri arXiv:2609.02882,
  Sections 2-3; `anthropics/formal-math` at `fbdc36bb`, sparse clone of
  `zeta23/`, the files cited above by `file:line`.
- Constants: none stated. The bandwidth-`θ` constant is `2 − kappaXi(θ, v)`,
  enclosed separately, see `RESULTS.md`.
