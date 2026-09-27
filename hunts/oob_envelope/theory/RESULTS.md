# RESULTS: theory lane, hunt `oob_envelope`

Branch `teal-sea/oob-cert-theory`. Author: theory worker (Claude Code, Opus).
Every statement below carries its grade on the ladder of `AGENTS.md`. A proof
here is an *ordinary derivation, self-reviewed*: it has not been refereed and
it is not kernel-checked. Numbers from float64 scripts are *measured*.

## Graded summary

(Filled in as tasks close; see `PROGRESS.md` for status.)

1. **Task 1, lemma and modified reduction.** For every complex `f ∈ L²`
   with `supp f ⊆ [-L, L]` and every `H = μ̂` with `μ` a finite measure
   carried by `|λ| ≥ 2L` (boundary included), `∫|F|²H = 0`; Zhu's
   Theorem 1.1 holds with `A_L` replaced by any bound `S ≥ sup_{t≥T#}(P_L − H)`.
   The proof of the inequality goes through unchanged; the computational
   constants of his §4–§5 do not (four places, §1.5), and the reduction now
   runs with `T#` near the window's resolution height, a regime Zhu never
   tested (§1.6). *Ordinary derivation, self-reviewed.*
2. **Task 2, duality.** For every `L > 0`, `inf_H sup_t(P_L − H) = λ_max(P)`,
   the top of the windowed comb operator: weak duality for every
   finite-measure `H`, strong duality by an explicit trigonometric `H_N`
   within `(π²/(4(N+1)²)) Σ m² log p/p^{m/2}` of the floor (a completion
   argument on the order `k ↦ k·log p`); continuous parts of `μ` do not lower
   the constant even on tails `t ≥ T` (§2.1–2.6). *Ordinary derivation,
   self-reviewed.* Measured (float64): `λ_max(P) = 0.9009276` at `L = 0.6`
   and `1.2191380` at `L = 0.8` (finite 4- and 12-vertex components), and
   the construction reaches `0.90719` and `1.23295` at `N = 20` against
   per-prime `1.12441` and `1.52205` (§2.4–2.5).
3. Task 3: pending.
4. Task 4: pending.
5. Task 5: pending.

## 0. Conventions

Zhu = arXiv:2608.24827v2 (X. Zhu, 2026). Section, equation and lemma numbers
below are those of v2's LaTeX source (sections: 1 intro, 2 the Weil form,
3 envelope lemmas, 4 proof of Theorem 1.1, 5 the computation at support 1.6,
6 parity, 7 the support-2.38 computation, 14 barrier, 15 failed routes).

* `F(z) = f̂(z) = ∫ f(u) e^{izu} du`.
* Window class `W_L = { f ∈ L²(ℝ; ℂ) : f = 0 a.e. outside [-L, L] }`.
* `f̃(x) = conj f(-x)`, `g = f ⋆ f̃`, so `g(x) = ∫ f(y) conj f(y − x) dy` and
  `ĝ(t) = |F(t)|²` for real `t`.
* Zhu's form, for real even `f ∈ W_L` (his eq. (2), (3)):
  `Q(f) = 2F(i/2)² + (1/2π) ∫_ℝ |F(t)|² Ψ_L(t) dt`,
  `Ψ_L(t) = a(t) − P_L(t)`, `a(t) = Re ψ(1/4 + it/2) − log π`,
  `P_L(t) = Σ_{log n < 2L} (2Λ(n)/√n) cos(t log n)`, `A_L = P_L(0)`.
  For general complex `f` the pole term is `ĝ(i/2) + ĝ(−i/2) =
  2 Re[F(i/2) conj F(−i/2)] = 2|∫f cosh(u/2)du|² − 2|∫f sinh(u/2)du|²`
  (derived and checked in §1.3); the multiplier term is the same integral.
* `a` is even, continuous, bounded below (`a(0) = ψ(1/4) − log π ≈ −5.37`) and
  `a(t) = log(|t|/2π) + O(1/|t|)`. `P_L` is bounded. So `Ψ_L` is bounded below
  and the multiplier integral is well defined in `(−∞, +∞]` for every
  `f ∈ W_L`; it is finite when `∫|F|² log(2 + |t|) dt < ∞`. Nothing below
  needs more than this.

## 1. Task 1: the out-of-band lemma and the modified reduction

### 1.1 Statement

**Lemma 1 (out-of-band orthogonality).** Let `L > 0`, `f ∈ W_L`, and let `μ`
be a finite complex Borel measure on `ℝ` with `|μ|((−2L, 2L)) = 0`. Put
`H(t) = ∫ e^{iλt} dμ(λ)`. Then `|F|² H ∈ L¹(ℝ)` and

    ∫_ℝ |F(t)|² H(t) dt = 0.

In particular this holds for `H(t) = Σ_w b_w cos(λ_w t)` with
`Σ_w |b_w| < ∞` and every `|λ_w| ≥ 2L` (take `μ = Σ_w (b_w/2)(δ_{λ_w} + δ_{−λ_w})`),
including frequencies exactly equal to `±2L`.

No reality, parity or smoothness of `f` is assumed. `H` may be complex; for
`Q` to stay real one takes `μ` real and symmetric, so that `H` is a real
cosine transform.

**Corollary 1 (invariance of Q).** For every `f ∈ W_L` and every real
admissible `H`,

    Q(f) = [pole term] + (1/2π) ∫_ℝ |F(t)|² (Ψ_L(t) + H(t)) dt,

as an identity in `(−∞, +∞]`. The pole term is not touched.

### 1.2 Proof of Lemma 1

(i) *`g` is continuous, bounded, and vanishes on `|x| ≥ 2L`.* Write
`g(x) = ⟨f, τ_x f⟩` with `(τ_x f)(y) = f(y − x)`. Translation is continuous
from `ℝ` into `L²`, so `g` is continuous, and `|g| ≤ ‖f‖₂²`. The integrand
`f(y) conj f(y − x)` vanishes unless `y ∈ [−L, L] ∩ [x − L, x + L]`. For
`x > 2L` that set is empty. For `x = 2L` it is the single point `{L}`. A
point has Lebesgue measure zero and `f(y) dy` is absolutely continuous, so
`g(2L) = 0`. The case `x ≤ −2L` is symmetric.

(ii) *Inversion holds pointwise.* `f ∈ L²` with compact support is in `L¹`,
so `g ∈ L¹ ∩ C(ℝ)`, and Fubini gives `ĝ(t) = F(t) conj F(t) = |F(t)|² ≥ 0`.
By Plancherel `∫ ĝ = 2π‖f‖₂² < ∞`, so `ĝ ∈ L¹`. For `g ∈ L¹ ∩ C` with
`ĝ ∈ L¹`, Fourier inversion holds at every point:
`g(x) = (1/2π) ∫ ĝ(t) e^{−itx} dt` for all `x ∈ ℝ`.

(iii) *Fubini against μ.* `∫∫ |ĝ(t)| d|μ|(λ) dt = ‖ĝ‖₁ · |μ|(ℝ) < ∞`, so

    ∫ ĝ(t) H(t) dt = ∫ ( ∫ ĝ(t) e^{iλt} dt ) dμ(λ) = 2π ∫ g(−λ) dμ(λ).

`μ` is carried by `{|λ| ≥ 2L}` and `g(−λ) = 0` there by (i), boundary
included. Hence the integral is `0`, and `|F|²H ∈ L¹` because `|H| ≤ |μ|(ℝ)`. ∎

*Proof of Corollary 1.* `Ψ_L` is bounded below and `H` is bounded, so
`∫|F|²(Ψ_L + H)` is defined in `(−∞, +∞]`, and it equals
`∫|F|²Ψ_L + ∫|F|²H` (a bounded-below integral plus an absolutely convergent
one). The second term is `0` by Lemma 1. ∎

### 1.3 Remarks that the referee brief asks about

* **Boundary frequency `|λ| = 2L`.** Handled in step (i): the overlap of
  `[−L, L]` and `[L, 3L]` is `{L}`, a null set. This is the only place the
  proof uses that `f` is a function rather than a measure. It is sharp: for
  `f = δ_{−L} + δ_L` (not in `L²`) one gets `|F(t)|² = 2 + 2cos(2Lt)`, whose
  mean against `cos(2Lt)` is `1`, not `0`. So the lemma needs "no atoms at
  `±L`", which every `f ∈ L²` satisfies. Equivalently: `g` is continuous and
  supported in `[−2L, 2L]`, hence `g(±2L) = 0`.
* **Complex and odd `f`.** No symmetry is used. For real `H` the multiplier
  term stays real for complex `f` (`|F|²` is real).
* **The pole term.** Lemma 1 is a statement about the multiplier integral
  only. Adding `H` to the symbol is licensed because the pole term is a
  separate finite-rank term evaluated at `±i/2`; `H` is never evaluated there
  and never enters it.
* **The pole term for complex `f`, checked.** `g` is continuous with compact
  support, so `ĝ` is entire, and for every `z ∈ ℂ`
  `ĝ(z) = F(z) · (f̃)^(z)` with
  `(f̃)^(z) = ∫ conj f(−x) e^{izx} dx = conj( ∫ f(u) e^{i z̄ u} du ) = conj F(z̄)`.
  Hence `ĝ(i/2) = F(i/2) conj F(−i/2)` and `ĝ(−i/2) = conj ĝ(i/2)`, and the
  pole term is the real number `2 Re[F(i/2) conj F(−i/2)]`. With
  `c = ∫ f(u) cosh(u/2) du` and `s = ∫ f(u) sinh(u/2) du` one has
  `F(i/2) = c − s`, `F(−i/2) = c + s`, and
  `(c − s)(conj c + conj s) = |c|² − |s|² + 2i Im(c conj s)`, so

      pole term = 2|c|² − 2|s|²,

  a Hermitian form of rank at most 2 and signature `(1, 1)`, with `c` seeing
  only the even part of `f` and `s` only the odd part. It reduces to
  `2F(i/2)²` for real even `f` (Zhu (2)), to `−2(∫ f sinh(u/2))²` for real odd
  `f` (Zhu Lemma 6.1), and it splits as `pole(Re f) + pole(Im f)` because
  `cosh` and `sinh` are real, which is the pole half of Zhu's
  `Q(f) = Q(Re f) + Q(Im f)`. Two formulas that are *wrong* for complex `f`
  and easy to type by accident: `2F(i/2)²` (complex-valued) and `2|F(i/2)|²`
  (loses the negative odd-sector sign). Both terms `ĝ(±i/2)` enter with a
  plus sign in Zhu's normalisation, as his (2) shows for real even `f`.
  A measured check of the identity against a direct time-domain computation
  of `ĝ(±i/2)` from `g = f ⋆ f̃` is in `theory/pole_check.py`.
* **Polarised form.** For `f_1, f_2 ∈ W_L`, `∫ F_1 conj F_2 · H = 0` (same
  proof with `g = f_1 ⋆ f̃_2`). So in any basis `{T_n}` of `W_L`, every
  full-line matrix entry `∫_ℝ H T̂_n conj T̂_m dt` vanishes. This is a free
  numerical control for K3.
* **Odd parts of `H` never help.** For `u = e + o` (even plus odd),
  `sup u ≥ sup e`, because `max(u(t), u(−t)) ≥ e(t)`. So one may take `H`
  even without loss.
* **`S_L(H) ≥ 0`.** `P_L − H` has Bohr mean `0`: every frequency of `P_L` is
  `log n > 0`, and the mean of `μ̂` is `μ({0}) = 0`. A bounded continuous
  function with mean `0` has `sup ≥ 0`. So `S_L(H) := sup_t (P_L − H)(t) ≥ 0`
  for every admissible `H`.
* **Almost periodic `H`.** If `H` is Bohr almost periodic (for instance the
  absolutely summable cosine series of the brief), `P_L − H` is almost
  periodic, and then `sup_{t ≥ T}(P_L − H) = sup_ℝ (P_L − H)` for every `T`:
  near-maxima recur at arbitrarily large `t`. So for this class, restricting
  the envelope to `t ≥ T#` gains nothing. (A non-almost-periodic `H`, i.e. a
  measure `μ` with a continuous part, is outside this remark; see §1.6.)

### 1.4 The modified one-stroke reduction

**Theorem 1′ (Zhu's Theorem 1.1 with an out-of-band correction).** Let
`L > 0` and let `H` be admissible, real and even. Let `S` be any number with

    S ≥ sup_{t ≥ T#} (P_L(t) − H(t)),

and fix `T# ≥ 15/4` with

    β* := log(T#/2π) − 1/T# − S > 0.

(If `S ≥ sup_ℝ(P_L − H)`, then `S ≥ 0` by §1.3, so `β* > 0` already forces
`T# > 2π > 15/4`.) Then for every real even `f ∈ W_L`,

    Q(f) ≥ R_H(f) := 2F(i/2)² + (1/π) ∫_0^{T#} (Ψ_L(t) + H(t) − β*) |F(t)|² dt + β*‖f‖₂².

The Legendre-basis statement of Theorem 1.1 holds verbatim with
`C_nm = (1/π) ∫_0^{T#} (Ψ_L + H − β*) T̂_n T̂_m dt` and with the constant
changes listed in §1.5. The odd-sector version (Zhu §6) holds with pole term
`−2(∫ f sinh(x/2) dx)²`.

*Proof.* By Corollary 1, `Q(f) = 2F(i/2)² + (1/2π)∫_ℝ |F|²(Ψ_L + H)`. For
`|t| ≥ T#`, Zhu's Lemma 3.1 (valid for `|t| ≥ 15/4`) and the choice of `S`
give

    Ψ_L(t) + H(t) = a(t) − (P_L − H)(t) ≥ log(|t|/2π) − 1/|t| − S ≥ β*,

the last step because `t ↦ log(t/2π) − 1/t` increases. For real even `f`,
`|F|²` and `Ψ_L + H` are even, and `∫_0^∞ |F|² = π‖f‖²`, so

    (1/2π) ∫_{|t|≥T#} |F|²(Ψ_L + H) ≥ (β*/π) ∫_{T#}^∞ |F|² = β*(‖f‖² − (1/π)∫_0^{T#}|F|²),

which rearranges to `Q(f) ≥ R_H(f)`. If `Q(f) = +∞` there is nothing to
prove, and `R_H(f)` is always finite (a bounded symbol on `[0, T#]`). ∎

For the per-prime construction of `probes/separable.py` the bound `S` is
supplied prime by prime: `P_L(t) = Σ_p φ_p(t log p)` exactly, with
`φ_p(θ) = Σ_{k log p < 2L} (2 log p / p^{k/2}) cos kθ`, and a pointwise
identity `Φ_p = M_p − φ_p + h_p ≥ 0` in `θ`, with `h_p` supported on
`m_p < |k| ≤ D`, gives `(P_L − H)(t) ≤ Σ_p M_p` for all `t`. The frequencies
of `h_p(t log p)` are `k log p ≥ (m_p + 1) log p ≥ 2L` by the definition of
`m_p`, so `H = Σ_p h_p(t log p)` is admissible (a finite cosine sum).

### 1.5 Line-by-line check against Zhu §3–§7

"Unchanged" means the argument and its constants carry over word for word.
"Changed" means the logic holds but a constant or an assembly step must be
redone. Nothing below breaks the inequality `Q ≥ R_H`.

| Zhu | content | status with `H` |
|---|---|---|
| Thm 1.1, threshold sentence | `β* > 0` above a unique threshold near `T_1` | unchanged with `A_L → S`, `T_1 → 2π e^S` |
| Lemma 3.1 | archimedean envelope, `t ≥ 15/4` | unchanged; the comb bound `|P_L| ≤ A_L` is replaced by `P_L − H ≤ S`; `t ≥ 15/4` automatic |
| Lemma 3.2 | `sup_t P_L = A_L` | still true, no longer binding: it bounds `P_L`, the reduction now needs a bound on `P_L − H` |
| Remark 3.3 | the retracted `A_eff` substitution | not the same move: `A_eff` bounds `P_L` from below (wrong direction); `S` bounds `P_L − H` from above, and Corollary 1 is what licenses replacing `P_L` by `P_L − H` |
| §4, split and Parseval | `∫_0^∞ = ∫_0^{T#} + ∫_{T#}^∞` | unchanged |
| §4, row bound on `C_nm` | `≤ max_{[0,T#]}|Ψ_L − β*| · …` | **changed (a):** `max|Ψ_L + H − β*| ≤ max|Ψ_L − β*| + Σ_w|b_w|` |
| §4, pole vector | super-exponential decay | unchanged (no `H`) |
| §4, eq. (13), Gershgorin, Schur | two-block bound | unchanged as linear algebra; entry bounds inherit (a), so `ε_D`, `ε_B` grow by the factor `1 + Σ|b_w| / max|Ψ_L − β*|` |
| §5.1 assembly | integrand `(Ψ_L − β*) T̂_n T̂_m` on `[0, T#]` | **changed (c):** the integrand is `(Ψ_L + H − β*) T̂_n T̂_m`. `H` is not zero on `[0, T#]`: Lemma 1 kills only the full-line integral |
| §5.2 Lemma 5.1 | Bernstein ellipse in `|Im t| ≤ 0.4`, `|Ψ_L − β*| ≤ 20` there | **changed (b):** see below |
| §5.3 tail and coupling | `max_{t≤T#}|T̂_400|`, row sums | changed only through (a) |
| §5.4 Lemma 5.2 | Cholesky residual | unchanged |
| §5.5(b) monotonicity in `T#` | `R_{T#}` increases with `T#` | unchanged: it only uses `Ψ_L + H ≥ β*` above `T#` |
| §6 Lemma 6.1, odd sector | parity splitting | unchanged: `Ψ_L + H` is even and Lemma 1 holds for odd and complex `f` |
| §7 dips of `Ψ_L` below `β*` | why `H = 0` fails at `T# = 1100`, `L = 1.19` | not applicable: with `H` the pointwise statement used above `T#` is `Ψ_L + H ≥ β*`, true by the choice of `S` |
| Thm 1.4 / §14 barrier | `T# > 2π e^{A_L}` | becomes `T# > 2π e^{S}`, and by Task 2 `S ≥ λ_max` of the windowed comb operator |

**(b) The quadrature bound, in numbers.** Lemma 5.1 continues the integrand
into the strip `|Im t| ≤ 0.4`. There `|cos(λt)| ≤ cosh(0.4 λ)`, so the bound
`|Ψ_L − β*| ≤ 20` becomes `|Ψ_L + H − β*| ≤ 20 + Σ_w |b_w| cosh(0.4 λ_w)`.
With Fejér degree `D = 64` as in `probes/separable.py`, at `L = 0.8` the
largest frequency is `64 log 3 ≈ 70.3` (prime 3; prime 2 reaches
`64 log 2 ≈ 44.4`), and `cosh(0.4 · 70.3) = cosh(28.1) ≈ 8 × 10^11`. The
ellipse constant `M` in the Gauss error bound therefore grows by up to about
eleven orders of magnitude, weighted by the size of the top coefficients.
This is a budget break, not a logic break: the numerics lane must either
shrink the strip to `δ ≈ c/λ_max` with correspondingly narrower panels, or
split `C = C^Ψ + C^H` and integrate `C^H` with a rule matched to its
bandwidth, or keep `D` small. `H` also oscillates at frequency up to
`λ_max`, which raises the node count per panel.

**(d) An incidental constant in Zhu §4 (not caused by `H`).** As printed,
the row bound
`|C_nm| ≤ max|Ψ_L − β*| · 2√(Lν_n) (T# L)^n/(2n+1)!! · 2√(Lν_m)`
has no factor from the length of `[0, T#]`. Bounding `(1/π)∫_0^{T#}` by
`(T#/π) · sup` and `|j_m| ≤ 1` gives the same expression times `T#/π`
(about `64` at `T# = 200`). Against Zhu's margins of `10^{-100}` this is
immaterial; it is recorded so the referee does not have to find it.

**(e) `T# ≥ 15/4`.** Automatic whenever `S` bounds the global supremum,
because then `S ≥ 0` (§1.3). If one uses a bound valid only on `t ≥ T#`, the
hypothesis must be checked; for almost periodic `H` the two suprema coincide.

### 1.6 The load-bearing caveat for the numerics lane

The inequality `Q ≥ R_H` is valid for every admissible `H`. Whether the
reduced form is *useful* is a different question, and here the out-of-band
route moves into a regime Zhu never ran.

* Zhu's run at `L = 0.8` used `T# = 200`, about six times the window's
  resolution height `T* = 2π e^{2L} ≈ 31.1`.
* With the seed constants of `MISSION.md`, `2π e^S` is `29.6` (separable,
  `S = 1.549`) and `21.3` (comb floor, `S = 1.219`), both *below* `T*`; with
  `β* = 0.5` the split point is `T# ≈ 49` or `≈ 35`, just above `T*`.
* Zhu §15, failed route (2): replacing `Ψ_L` beyond a height the window
  resolves by a constant minorant made the form indefinite
  (measured `λ_min ≈ −2.7`). `R_H` is exactly such a replacement above `T#`,
  by the constant `β*`. It remains a valid lower bound, but `λ_min(R_H)` is
  not bounded below by anything in this lane, and may be negative or far
  below Zhu's `λ_min(R) ≈ 0.54 λ*` at `L = 0.8`. The loss
  `Q(f) − R_H(f) = (1/π)∫_{T#}^∞ (Ψ_L + H − β*)|F|²` is paid on the
  minimiser, whose mass reaches up to about `T*`.
* **A better objective.** For fixed `T#` and `S`, `R_H` is affine in `H` (and
  in `(H, S)` jointly, since `β*` is affine in `S`), and the envelope
  constraint `sup(P_L − H) ≤ S` is convex. So "maximise `λ_min` of the leading
  `N × N` block of `R_H` over `H`, subject to the envelope" is a concave
  maximisation over a convex set: after truncating `H` to finitely many
  frequencies it is an SDP (an LMI for `λ_min`, a sum-of-squares constraint
  on the torus for the envelope). Minimising `S` alone controls the matrix
  size, not the loss. This is a proposal for the numerics lane, not a
  measured result.

## 2. Task 2: the optimal constant (weak and strong duality)

### 2.1 The two problems

Write `w_n = Λ(n)/√n` and let `n` range over prime powers with `log n < 2L`.
The *windowed comb operator* on `L²[−L, L]` is

    (Pφ)(x) = Σ_n w_n [φ(x − log n) + φ(x + log n)],    x ∈ [−L, L],

with `φ = 0` outside `[−L, L]`. It is bounded, self-adjoint and positivity
preserving, with `‖P‖ ≤ A_L`. Put `λ_max(P) = sup spec(P)`. For
`φ ∈ W_L` with transform `Φ`, `(1/2π)∫|Φ|² e^{iat} dt = g_φ(−a)` (step (ii)
of §1.2), which gives the identity

    ⟨Pφ, φ⟩ = (1/2π) ∫_ℝ |Φ(t)|² P_L(t) dt.                          (2.1)

The *out-of-band problem* is `S*_L := inf_H S_L(H)`, the infimum over real
even admissible `H` of `S_L(H) = sup_t (P_L − H)(t)`. Three classes of `H`
give the same infimum (by 2.2 and 2.3 below): finite real even trigonometric
polynomials with frequencies `|λ| ≥ 2L`, absolutely summable cosine series,
and transforms of finite real symmetric measures carried by `|λ| ≥ 2L`.

### 2.2 Weak duality

**Proposition 2.1.** For every admissible `H`, `S_L(H) ≥ λ_max(P)`.

*Proof.* By (2.1) and Lemma 1, for `φ ∈ W_L`,
`⟨Pφ, φ⟩ = (1/2π)∫|Φ|²(P_L − H) ≤ S_L(H) · (1/2π)∫|Φ|² = S_L(H)‖φ‖²`. ∎

So `S*_L ≥ λ_max(P)`, and the seed column `S_opt` of `MISSION.md` (a
piecewise-constant Galerkin value, which approximates `λ_max(P)` from below)
is a floor for every out-of-band construction.

### 2.3 Strong duality

Let `p_1 < … < p_r` be the primes below `e^{2L}`,
`ℓ = (log p_1, …, log p_r)` and `s(k) = k · ℓ` for `k ∈ ℤ^r`. Unique
factorisation makes the `log p_i` linearly independent over `ℚ`, so `s` is
injective. Every comb frequency is `log p_i^m = s(m e_i)`, and
`K := { k : |s(k)| < 2L }` (the *slab*) contains all of them.

**Theorem 2 (strong duality).** For every `L > 0`,

    S*_L = inf_H sup_t (P_L − H)(t) = λ_max(P),

the infimum taken over real even trigonometric polynomials whose frequencies
lie in `{ s(k) : k ∈ ℤ^r, |s(k)| ≥ 2L }`. Quantitatively: for every
`t ≥ λ_max(P)` and every integer `N ≥ 1` there is such an `H_N`, with
frequencies `s(k)` for `k ∈ [−2N, 2N]^r`, satisfying

    S_L(H_N) ≤ t + Σ_{p^m < e^{2L}} (2 log p / p^{m/2}) (1 − cos(π m/(2N+2)))
             ≤ t + (π² / (4(N+1)²)) Σ_{p^m < e^{2L}} m² log p / p^{m/2}.

The infimum is in general not attained (for a single prime it needs a
Fejér limit, `D → ∞` in `probes/separable.py`).

*Proof.* Weak duality is Proposition 2.1. For the other direction fix
`t ≥ λ_max(P)` and define `ψ : K → ℝ` by `ψ(0) = t`,
`ψ(±m e_i) = −w_{p_i^m}`, and `ψ(k) = 0` for every other `k ∈ K`.

*Step 1 (the window gives positivity on strips).* Let `F ⊂ ℤ^r` be finite
with `diam s(F) < 2L`. Then the matrix `[ψ(j′ − j)]_{j, j′ ∈ F}` is positive
semidefinite. Indeed, choose `x_0` with `x_0 + s(F) ⊂ (−L, L)` and for
`ε > 0` put `φ_ε = Σ_{j∈F} a_j ε^{−1/2} 1_{[x_0 + s(j), x_0 + s(j) + ε)}`.
The points `x_0 + s(j)` are distinct (injectivity), and a shifted bump
overlaps another only if `s(j′) − s(j) = ±log n` up to `ε`. For `ε` below the
least nonzero value of `|s(j′) − s(j) ∓ log n|` over the finitely many
triples, only exact coincidences remain, and `s(j′ − j) = s(m e_i)` forces
`j′ − j = m e_i`. Hence
`0 ≤ ⟨(t − P)φ_ε, φ_ε⟩ = Σ_{j,j′} a_j conj a_{j′} ψ(j′ − j)`.

*Step 2 (completion along the order).* Let `F ⊂ ℤ^r` be finite, listed as
`j_1, …, j_M` in increasing order of `s`. Consider the partial symmetric
matrix with entries `ψ(j_a − j_b)` specified exactly when
`|s(j_a) − s(j_b)| < 2L`. It has a positive semidefinite completion `M̃`.
Proof by induction on `M`: suppose the first `k` points are completed to
`M_k ⪰ 0`. The earlier points specified against `j_{k+1}` form a contiguous
block `B = {j_a : s(j_{k+1}) − s(j_a) < 2L}`, and `B ∪ {j_{k+1}}` has
`s`-diameter `< 2L`, so by Step 1 the fully specified matrix
`[[M_BB, v], [v*, t]]` is positive semidefinite; in particular
`v ∈ range(M_BB)` and `t − v* M_BB⁺ v ≥ 0`. Fill the unspecified entries
against the remaining earlier points `U` by `u = M_UB M_BB⁺ v`. The new
column is `w = M_k E_B M_BB⁺ v ∈ range(M_k)` (with `E_B` the coordinate
inclusion of `B`), and `w* M_k⁺ w = v* M_BB⁺ v ≤ t`, so the extended matrix is
positive semidefinite. (This is the standard completion argument for chordal
patterns, Grone, Johnson, Sá and Wolkowicz 1984; the pattern here is a unit
interval graph on the real line through `s`, hence chordal, and the proof
above is self-contained.)

*Step 3 (averaging over a box).* Take `F = F_N = {−N, …, N}^r` with weights
`α_j = Π_i cos(π j_i/(2N+2)) > 0`, `Z = Σ α_j²`, and set

    c(k) = (1/Z) Σ_{j − j′ = k} α_j α_{j′} M̃_{j j′}.

For finitely supported `a`, `Σ_{k,k′} a_k conj a_{k′} c(k − k′)` equals
`(1/Z)` times the Frobenius product of `M̃` with the positive semidefinite
matrix `[α_j β(j − j′) α_{j′}]`, `β = a ⋆ ã`; so `c` is positive definite on
`ℤ^r`, supported in `[−2N, 2N]^r`. For `k ∈ K` every pair with `j − j′ = k`
was specified with value `ψ(k)`, so `c(k) = ψ(k) ρ(k)` with
`ρ(k) = Σ_{j−j′=k} α_j α_{j′} / Z`. For `k = m e_i` this is the
one-dimensional ratio `ρ_N(m) = [(n−1−m) cos(πm/n) + sin(π(m+1)/n)/sin(π/n)]/n`,
`n = 2N + 2`. Since `sin((m+1)x)/sin x = Σ_{q=0}^m cos((m − 2q)x) ≥ (m+1)cos(mx)`
for `mx ≤ π`, `ρ_N(m) ≥ cos(πm/n)`.

*Step 4 (the nonnegative polynomial).* `μ(θ) := Σ_k c(k) e^{ik·θ}` is a real
even trigonometric polynomial on `T^r`, and
`μ(θ) = (1/Z) Σ_{j,j′} (α_j e^{ij·θ}) M̃_{jj′} (α_{j′} e^{−ij′·θ}) ≥ 0`
because `M̃ ⪰ 0`. Split `μ = μ_K + H̃_N`, where `μ_K` collects the
coefficients with `k ∈ K` and `H̃_N` the rest. By Step 3,

    μ_K(θ) = t − Σ_{p^m} 2 w_{p^m} ρ_N(m) cos(m θ_i)       (i the index of p),

so, with `Φ(θ) = Σ_{p^m} 2 w_{p^m} cos(m θ_i)` (the comb on the torus,
`P_L(t) = Φ(tℓ)`), the inequality `μ ≥ 0` reads

    Φ(θ) − H̃_N(θ) ≤ t + Σ_{p^m} 2 w_{p^m} (1 − ρ_N(m)).

*Step 5 (back to the line).* Put `H_N(t) = H̃_N(tℓ)`, a real even
trigonometric polynomial whose frequencies are `s(k)` with `k ∉ K`, i.e.
`|s(k)| ≥ 2L`: admissible. Evaluating Step 4 at `θ = tℓ` gives the bound on
`sup_t (P_L − H_N)`, and `1 − ρ_N(m) ≤ 1 − cos(πm/(2N+2)) ≤ π²m²/(8(N+1)²)`.
Letting `N → ∞` and `t ↓ λ_max(P)` gives `S*_L ≤ λ_max(P)`. ∎

*Remarks.*

* Kronecker's theorem is not needed for Theorem 2: Step 5 only uses that
  `t ↦ tℓ` maps into the torus. (It does show the torus problem and the line
  problem have the same value, which is how the probes are organised.)
* For one prime (`r = 1`) the theorem is the Carathéodory–Toeplitz statement
  of `MISSION.md`: `λ_max(P)` is then the top eigenvalue of the
  `(m+1) × (m+1)` Toeplitz matrix with first row `(0, t_1, …, t_m)`, because
  the window graph is a union of arithmetic progressions of step `log p`
  with at most `m + 1` terms. `S_sep = Σ_p λ_max(T_p)` is Theorem 2 applied
  one prime at a time, and weak duality gives `S_sep ≥ λ_max(P)`.
* Why a Perron–Frobenius argument alone does not close the gap: the dual
  objects are vectors on `ℤ^r` whose autocorrelation vanishes off the slab,
  and taking absolute values destroys that cancellation. What closes it is
  that `s` totally orders `ℤ^r` and the slab is an interval for that order,
  so the specification pattern is an interval graph (Step 2). This is a
  Krein-type extension property for the ordered group `(ℤ^r, s)`: a function
  positive definite on every strip of width `2L` extends to a positive
  definite function on `ℤ^r`. In two or more dimensions with box-shaped
  patterns the analogous extension fails (Rudin 1963); the irrational order
  makes the problem one-dimensional.
* The construction converts *any* upper bound `t` on `λ_max(P)` into an
  explicit `H`. Where `λ_max(P)` is not known in closed form, a
  Collatz–Wielandt bound `t = sup_x (Ph)(x)/h(x)` for a positive trial `h`
  (valid because `P` preserves positivity) supplies it.

### 2.4 Exact values while the window graph has finite components

Join `x, y ∈ [−L, L]` when `y − x = ±log n` for a comb term `n`. `P` is the
weighted adjacency operator of this graph against Lebesgue measure.

**Proposition 2.2.** If every component is finite, then up to null sets
`[−L, L]` splits into finitely many families of translated base intervals,
one family per combinatorial type `τ` with `k_τ` vertices and weighted
adjacency matrix `A_τ`, and `P ≅ ⊕_τ A_τ ⊗ I_{L²(B_τ)}`. Hence
`spec P = ∪_τ spec A_τ` and `λ_max(P) = max_τ λ_max(A_τ)`, attained with
infinite multiplicity. (The type changes only where some `x + s(k)` crosses
`±L`, finitely many breakpoints, so each base set is a finite union of
intervals.) *Ordinary derivation, self-reviewed.*

Measured census (float64 breadth-first search, points merged at `1e-9`;
4000 random base points plus a grid of 160 001; one route):

| L | comb | component types (vertices) | λ_max(P) | Galerkin, M = 800 |
|---|---|---|---|---|
| 0.6 | 2, 3 | 1, 2, 4 (paths) | 0.9009276 | 0.9007657 |
| 0.8 | 2, 3, 4 | 4, 7, 12 | 1.2191380 | 1.2186272 |

At `L = 0.6` the top type is the path `x, x − log 2, x − log 2 + log 3,
x − 2 log 2 + log 3` with weights `(a, b, a)`, `a = w_2`, `b = w_3`, and
`λ_max² = [(2a² + b²) + √((2a² + b²)² − 4a⁴)]/2`, `λ_max = 0.9009276`
(closed form; the float value agrees with the census). At `L = 0.8` the top
type has 12 vertices and 13 edges (two triangles from `log 2 + log 2 = log 4`)
and occupies 71.9% of the window; a 13-vertex "type" seen once in a random
sample was two float copies of one point `3e−17` apart. These two values are
exact eigenvalue problems of size 4 and 12, so they can be enclosed with
ball arithmetic; that is for the numerics lane.

The regime ends soon after `5` enters the comb at `L = log 5 / 2 ≈ 0.8047`.
Measured (200 base points, cap 2000 vertices): largest finite component 24
vertices at `L = 0.81`, 92 at `L = 0.83`; at `L = 0.85` 89.5% of samples
exceed the cap, at `L = 0.88` all do. Without the prime 5 the components
stay finite to at least `L = 0.88`. So at `L = 1.0` and `L = 1.19` the window
operator has (numerically) infinite quasi-periodic components, Proposition
2.2 does not apply, and `λ_max(P)` is available only as a bracket:
Galerkin or Rayleigh quotients from below, Collatz–Wielandt from above.

### 2.5 Measured check of the construction

`theory/duality_check.py` runs Steps 2 to 5 literally (float64, one route,
`t = λ_max(P) + 10^{−9}`, the torus sampled on a 256 × 256 grid). Output
(`hunts/oob_envelope/theory/duality_check.py`, about 5 s):

| L | N | S_sep (D = ∞) | λ_max(P) | sup(Φ − H_N) on grid | proof bound | min μ on grid | ‖H_N‖₁ | top frequency of H_N |
|---|---|---|---|---|---|---|---|---|
| 0.6 | 6 | 1.124413 | 0.9009276 | 0.9566213 | 0.9573104 | 6.3e−4 | 22.3 | 21.5 |
| 0.6 | 12 | 1.124413 | 0.9009276 | 0.9172182 | 0.9173241 | 9.6e−5 | 57.9 | 43.0 |
| 0.6 | 20 | 1.124413 | 0.9009276 | 0.9071908 | 0.9072158 | 2.3e−5 | 117.7 | 71.7 |
| 0.8 | 6 | 1.522051 | 1.219138 | 1.338374 | 1.339261 | 8.9e−4 | 22.6 | 21.5 |
| 0.8 | 12 | 1.522051 | 1.219138 | 1.254767 | 1.254901 | 1.3e−4 | 66.2 | 43.0 |
| 0.8 | 20 | 1.522051 | 1.219138 | 1.232949 | 1.232984 | 3.5e−5 | 141.7 | 71.7 |

The in-slab coefficients of `μ` other than those of `t − Φ` vanish to
machine precision, and the completed matrices have least eigenvalue about
`1e−10` (the margin `10^{−9}` in `t`). The joint out-of-band constant beats
the per-prime one by `0.22` at `L = 0.6` and `0.29` at `L = 0.8`, and the gap
to the floor closes like `N^{−2}`, as the proof bound says.

The price is visible in the last two columns: the `H` that approaches the
floor has large coefficients and high frequencies, which is exactly what
inflates the quadrature constant of §1.5 (b). The matrix size gained by a
smaller `S` has to be weighed against that, and against §1.6.

### 2.6 Finite-measure `H` outside the almost periodic class

The supervisor asked whether transforms of finite measures with a continuous
part change the duality. Answer: not for the constant envelope that
Theorem 1′ uses, even restricted to a tail `t ≥ T`; they could matter only
for a pointwise envelope, and there they pay exponentially in total
variation.

**Proposition 2.3 (continuous parts do not lower the constant).** Let `μ` be
a finite real symmetric Borel measure carried by `{|λ| ≥ 2L}`, `H = μ̂`, and
`T ∈ ℝ`. Then

    sup_{t ≥ T} (P_L − H)(t) ≥ λ_max(P).

*Proof.* Split `μ = μ_d + μ_c` into its atomic and continuous parts. `μ_d`
is again finite, real, symmetric and carried by `{|λ| ≥ 2L}`, so
`u := P_L − μ̂_d` is Bohr almost periodic and, by Proposition 2.1,
`sup_ℝ u ≥ λ_max(P)`. Fix `ε > 0`. `u` is uniformly continuous and its
`ε`-almost periods are relatively dense, so `E = {t : u(t) > sup u − ε}`
contains an interval of fixed length `2δ > 0` inside every interval of some
fixed length `ℓ_ε`; hence `|E ∩ [T, T + X]| ≥ c X` for large `X`, with
`c > 0`. By Wiener's theorem, `(1/2X) ∫_{−X}^{X} |μ̂_c|² → Σ_x |μ_c({x})|² = 0`,
so `|{t ∈ [T, T + X] : |μ̂_c(t)| ≥ ε}| ≤ ε^{−2} ∫_T^{T+X} |μ̂_c|² = o(X)`. For
large `X` the two sets meet, and at a common point
`(P_L − H)(t) = u(t) − μ̂_c(t) > sup u − 2ε`. ∎

So over every class between trigonometric polynomials and finite measures
the constant-envelope optimum is the same number, `λ_max(P)`: Proposition 2.1
bounds all of them below, Theorem 2 attains it with trigonometric
polynomials, and Proposition 2.3 closes the tail loophole.

**Where a non-almost-periodic `H` could still act.** The proof of
Theorem 1′ uses only the pointwise condition
`Ψ_L(t) + H(t) ≥ β*` for `|t| ≥ T#`, which is weaker than a constant bound
because `a(t)` increases. Zhu §7 already exploits this for `H = 0` (interval
evaluation of `Ψ_L` on a finite range lowers `T#` at `L = 1.19` from about
`1.2 × 10^4` to about `8.5 × 10^3`). The same applies with any `H`, and a
localised out-of-band wave packet (a measure with a smooth density on
`|λ| ≥ 2L`, modulated to sit at a chosen height) can in principle lift
`Ψ_L + H` where an almost periodic envelope dips. The cost is exponential in
the length lifted:

**Proposition 2.4 (cost of a localised lift).** Let `μ` be a finite complex
measure carried by `{|λ| ≥ a}`, `a > 0`, `H = μ̂`, and suppose
`Re H ≥ h_0 > 0` on an interval `I` of length `ℓ ≥ 2e/a`. Then

    ‖μ‖ ≥ h_0 · exp(⌊aℓ/(2e)⌋),    i.e. ‖μ‖ ≥ h_0 · exp(⌊Lℓ/e⌋) for a = 2L.

*Proof.* Put `q = ⌊aℓ/(2e)⌋ ≥ 1` and let `k` be the `q`-fold convolution of
the uniform probability density on an interval of length `ℓ/q`, translated
into `I`. Then `k ≥ 0`, `∫ k = 1`, `supp k ⊆ I`, and
`|k̂(λ)| = |sin(λℓ/2q)/(λℓ/2q)|^q ≤ (2q/(aℓ))^q ≤ e^{−q}` for `|λ| ≥ a`. By
Fubini, `h_0 ≤ Re ∫ H k = Re ∫ k̂ dμ ≤ ‖μ‖ e^{−q}`. ∎

At `L = 0.8` a lift over a stretch of length 10 costs a factor at least
`e^2 ≈ 7.4` in total variation, over length 100 at least `e^{29}`. Since
`‖H‖_∞ ≤ ‖μ‖` enters the retained matrix on `[0, T#]` and the quadrature
bound of §1.5 (b), long lifts are not a practical route. Short lifts at the
isolated near-alignment spikes of an almost periodic envelope are not
excluded by this bound. The best pointwise threshold over finite-measure `H`
is **unresolved** here; it is a different optimisation problem from the one
Theorem 2 solves, and no duality statement is claimed for it.

### 2.7 Cross-check against the numerics lane

The numerics lane reports enclosure-carrying per-prime constants at Fejér
degree `D = 128` (sine-kernel decomposition plus an adaptive Arb scan in
`θ`): `S(0.8) = 1.52268`, `S(1.0) = 2.97835`, `S(1.19) = 3.76891`
(`numerics/PROGRESS.md` on `teal-sea/oob-cert`, relayed by the supervisor;
not read here). The per-prime infimum over all degrees is
`Σ_p λ_max(T_p)` (Theorem 2 with `r = 1`, one prime at a time), which float64
evaluation gives as `1.522051`, `2.977298`, `3.767084` (measured, one
route). Every reported value lies above its limit, by `6 × 10^{−4}`,
`1.1 × 10^{−3}` and `1.8 × 10^{−3}`, as it must: a per-prime enclosure below
these numbers would contradict weak duality and would signal a bug.
