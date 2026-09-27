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
2. Task 2: pending.
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
  2 Re[F(i/2) conj F(−i/2)]` (Zhu Lemma 6.1 and its proof); the multiplier
  term is the same integral.
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
  separate rank-one term evaluated at `±i/2`; `H` is never evaluated there
  and never enters it.
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
