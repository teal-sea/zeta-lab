<!-- Landed from a novelty-check agent, 2026-08-12. Wording adjusted for
the hunts/ lexical rules; no factual content altered. -->

# Novelty check: the involution-normalised PSD Frobenius bound

**Date:** 2026-08-12. **Purpose:** avoid a false novelty claim.

**Verdict up front: (b) FOLLOWS EASILY from known results.** Not merely "adjacent" —
the statement is a two-line composition of two lemmas that are (i) textbook classical, and
(ii) *already stated, proved, and Lean-formalised* in the Aug-2026 zeta paper and its
repository, where the exact numerical specialisation "‖·‖²_F ≥ 2N in the all-off-line
configuration" is written out in §7.5(a). A novelty claim would not survive review.

---

## 1. The statement, restated

Index set `A = Fin n × Bool`, `N = 2n`. `S` = permutation matrix of the fixed-point-free
involution σ. Hypotheses: `Q ⪰ 0` Hermitian; (i) `Q(a, σa) = 1`; (ii) `Q(σa, σb) = Q(b,a)`,
i.e. `Q̄ = S Q S`. Claim: `Re Σ_{a,b} Q(a,b)² ≥ 4n`.

Two immediate reductions (checked numerically, see §6):

- `Σ_{a,b} Q(a,b)² = tr(Q Qᵀ) = tr(Q Q̄) = tr(Q S Q S) = tr((QS)²)`.
- `tr(QS) = Σ_a Q(a, σa) = 2n`.

**The `Re` is cosmetic.** Under (ii), `conj tr((QS)²) = tr((SQ)²) = tr((QS)²)`, so the
quantity is real automatically. Presenting it as a real part makes the statement look more
delicate than it is; a referee will notice.

So the claim is exactly

> `tr(M²) ≥ (tr M)² / n` for `M = QS`, given `tr M = 2n`.

## 2. The two ingredients — both classical

Write `Q = B*B` and `C = B S B*` (Hermitian). Then `tr C = tr(QS) = 2n` and
`tr(C²) = tr((QS)²)`.

**(a) Inertia bound `n₊(C) ≤ n`.** σ fixed-point-free on 2n points ⇒ `S` is Hermitian,
`S² = I`, `tr S = 0` ⇒ signature exactly `(n, n)` ⇒ `S = VV* − WW*` with `n` columns each.
Hence `C = (BV)(BV)* − (BW)(BW)*` and `n₊(C) ≤ rank(BV) ≤ n`. This is **Sylvester's law of
inertia in pull-back form**: `n₊(A*QA) ≤ n₊(Q)` for arbitrary (not necessarily square or
injective) `A`. Classical; see Sylvester's law and its Ostrowski/Haynsworth refinements
(https://en.wikipedia.org/wiki/Sylvester%27s_law_of_inertia,
https://en.wikipedia.org/wiki/Haynsworth_inertia_additivity_formula,
https://nhigham.com/2021/03/09/eigenvalue-inequalities-for-hermitian-matrices/).

**(b) Cauchy–Schwarz on eigenvalues.** For Hermitian `C` with `tr C > 0`,
`(tr C)² ≤ (Σ_{λ>0} λ)² ≤ n₊(C) · Σ_{λ>0} λ² ≤ n₊(C) · tr(C²)`
(discarding negative eigenvalues only helps). Also textbook: it is the Hermitian case of
`‖X‖_*² ≤ rank(X)·‖X‖_F²`, the standard nuclear-vs-Frobenius bound used throughout
low-rank recovery (Recht–Fazel–Parrilo, *Guaranteed Minimum-Rank Solutions…*,
https://arxiv.org/pdf/0706.4138 ; https://epubs.siam.org/doi/10.1137/070697835).

Combining: `(2n)² ≤ n · tr(C²)` ⇒ `tr((QS)²) ≥ 4n` ⇒ `Σ Q² ≥ 4n`. Three lines.

The described proof route (regularised projection `T = Z(Z*Z+ε)⁻¹Z*`, `tr T² ≤ n`,
`tr(CT) ≥ tr C − εn`, trace Cauchy–Schwarz, `ε → 0`) is a spectral-theory-free *re-derivation*
of exactly (a)+(b). Avoiding the spectral theorem is a formalisation convenience, not new
mathematics.

## 3. Direct prior art: the Aug-2026 paper and its Lean repository

Paper: "More than two thirds of the zeros of the Riemann zeta function lie on the critical
line" (Claude, Anthropic, 2026),
https://www-cdn.anthropic.com/564f962e60643842f5fcb4a17c9dbc8f608f1c37.pdf
Repo: https://github.com/anthropics/zeta-23-lean

### 3.1 Lemma 3.1 = our ingredient (a), verbatim

> **Lemma 3.1 (Inertia under pull-back).** Let Q be a Hermitian form on ℂᵐ and A : U → ℂᵐ a
> linear map… Then n₊(Q∘A) ≤ n₊(Q).

Formalised as `RHLinalg.posIndex_conj_le` in `Zeta23/LinAlg/Inertia.lean`:
```lean
theorem posIndex_conj_le {Q : Matrix m m 𝕜} (hQ : Q.IsHermitian) (B : Matrix m d 𝕜) :
    posIndex (isHermitian_conjTranspose_mul_mul B hQ) ≤ posIndex hQ
```

### 3.2 Lemma 3.3 = our ingredient (b), at θ = 0

> **Lemma 3.3 (Thresholded Cauchy–Schwarz count).** Let R be Hermitian d×d and θ ≥ 0 with
> tr R > θd. Then n₊^θ(R) ≥ (tr R − θd)² / tr(R²).

Formalised as `RHLinalg.cauchySchwarz_count` in `Zeta23/LinAlg/Weyl.lean`:
```lean
theorem cauchySchwarz_count {R : Matrix n n 𝕜} (hR : R.IsHermitian)
    {θ : ℝ} (hθ : 0 ≤ θ) (htr : θ * Fintype.card n < rtrace R) :
    (rtrace R - θ * Fintype.card n) ^ 2 / frobSq R ≤ (posIndexAbove hR θ : ℝ)
```
At θ = 0 this **is** our conclusion once `n₊ ≤ n` is supplied.

### 3.3 Lemma 3.2 also gives it, by a different optimisation

`rank_trace_ineq` (`Zeta23/LinAlg/RankTrace.lean`):
```lean
theorem rank_trace_ineq {P Q : Matrix n n 𝕜} (hP : P.PosSemidef) (hQ : Q.IsHermitian)
    {r b : ℕ} (hr : P.rank ≤ r) (hb : posIndex hQ ≤ b) {c : ℝ} (hc : 0 < c) :
    c * rtrace P - c ^ 2 / 4 * r + 2 * c * rtrace Q - c ^ 2 * b ≤ frobSq (P + Q)
```
Take `P = 0`, `r = 0`, `Q = C`, `b = n`, `c = tr C / n = 2`: LHS `= 2·2·2n − 4n = 4n`.
So `frobSq C ≥ 4n` directly. The paper even remarks in the Lemma 3.2 proof discussion:
*"Taking Q = 0 and optimising c recovers rank P ≥ (tr P)²/‖P‖²_F."*

### 3.4 The **exact numerical specialisation** is in the paper's §7.5(a)

> "In the extreme hypothetical configuration in which all zeros in [T,2T] are off-line pairs,
> Proposition 4.1 gives rank P = 0, n₊(Q) ≤ N/2, while Lemma 3.2 would then force
> ‖Â‖²_F ≥ 2N > (4/3)N…"

With `N = 2n` zeros forming `n` off-line pairs, `‖Â‖²_F ≥ 2N = 4n`. That is our inequality,
same constant, same hypothesis content, in print.

### 3.5 The hypotheses are the paper's off-line block structure

Proposition 4.1(ii) of the paper: each off-line pair `{ρ, 1−ρ̄}` contributes a 2×2 hyperbolic
block `[[0, m_ρ],[m_ρ, 0]]` of signature (1,1); `Q` is the pull-back of the direct sum of the
`p` hyperbolic blocks under the evaluation map, so `n₊(Q) ≤ p` by Lemma 3.1.

Our `(Fin n) × Bool` indexing with a fixed-point-free involution **is** that ρ ↔ 1−ρ̄ pairing;
condition (i) `Q(a,σa) = 1` is the normalisation `m_ρ = 1`; condition (ii) is the reality/
functional-equation symmetry. And the stated application — energy of
`Σ_i 2 cosh(y_i w) e^{i t_i w}` against the window autocorrelation `c₂` — is literally the
paper's off-line Gram-matrix computation, since `2 cosh(y w) e^{itw}` is the sum of the two
exponentials attached to `ρ = ½ + y + it` and `1 − ρ̄ = ½ − y + it`. This is not an analogy;
it is the same object with the number theory stripped off.

**Logical relationship:** our statement is a **corollary** of {Lemma 3.1 + Lemma 3.3(θ=0)},
and equally of {Lemma 3.1 + Lemma 3.2 at c=2, P=0}. It does not imply either of them (both
are strictly more general: arbitrary Hermitian `Q`, arbitrary bound `b`, rank term, threshold θ).
It is strictly weaker than Lemma 3.2, and it is the special case of §7.5(a).

## 4. Wider literature checked

- **Bombieri, "Remarks on Weil's quadratic functional in the theory of prime numbers I"**,
  Rend. Lincei Mat. Appl. 11 (2000) 183–233 (https://eudml.org/doc/252338): the *negative*
  index of finite truncations of Weil's form counts off-line zero pairs. This is the
  dual bookkeeping of our hypothesis structure, and the Aug-2026 paper attributes it to him
  explicitly. Nearest genuine classical antecedent for the *setup*.
- **Montgomery (1973) pair correlation / simple-zero deduction**; **Cheer–Goldston**;
  **Conrey–Ghosh–Gonek [CGG98]**; **Baluyot–Goldston–Suriajaya–Turnage-Butterbaugh**
  (https://arxiv.org/pdf/2501.14545, https://arxiv.org/pdf/2511.20059). The scalar shadow of
  the linear algebra here is Montgomery's integrality step `m² ≥ 2m − 1`. Nothing in this
  literature states our matrix inequality, but nothing in it would find it surprising.
- **The paper's own novelty claim** (§7.4): *"We are not aware of a previous use of the
  positive index or of the rank in combination with a second-moment evaluation."* Our
  statement sits **inside** that claim, not beside it — it is a consequence of the machinery
  whose novelty they are asserting, published Aug 2026.
- **de Branges / Hermite–Biehler / Beurling–Selberg**: searched for "Gram matrix of
  exponentials against a nonnegative weight with conjugation involution" as a named object
  with known norm bounds. Found no such named object or matching bound. Gram matrices of
  exponentials are of course ubiquitous there, but the inertia-plus-second-moment bound is
  not how that literature uses them. This search was the least conclusive (see §7).
- **Kantorovich / Haagerup / correlation-matrix Frobenius bounds**: not the mechanism. The
  bound here is pure Cauchy–Schwarz on eigenvalues; no operator-norm or free-probability
  input is involved.

## 5. What, if anything, is not already written down

Essentially nothing mathematical. The most that can honestly be said:

- The **packaging** as a standalone matrix statement with no number theory in it (hypotheses
  phrased as an abstract involution + unit involution-diagonal, rather than as off-line zero
  pairs) does not appear verbatim anywhere I found.
- The **spectral-theorem-free proof** (regularised projection instead of eigenvalue
  Cauchy–Schwarz) is a proof-engineering variant, of interest only for formalisation.

Neither is a new theorem. Claiming novelty here would be claiming novelty for a corollary of
a published lemma whose numerical specialisation is printed in the same paper's §7.5(a).

## 6. Numerical checking performed

2000 random feasible instances (n ∈ {1,2,3,5,8}, complex PSD Q built as B*B, symmetrised to
enforce `Q̄ = SQS`, then congruence-normalised by a diagonal `E` with `e_a = |d_a|^{-1/2}
e^{-i·arg(d_a)/2}` to enforce `Q(a,σa) = 1`). All satisfied the hypotheses to 1e-8. Results:

- `Σ Q(a,b)²` had zero imaginary part in every instance (confirming §1).
- `Σ Q² = tr((QS)²)` and `tr(BSB*) = 2n` held identically.
- `n₊(BSB*) ≤ n` held in every instance.
- `min (Σ Q²)/(4n) = 1.0251` over the random sample; equality attained at n=1 with the
  all-ones 2×2 matrix (`Σ Q² = 4`), as claimed. Sharpness substantiated.

Script: `/tmp/claude-0/-home-user-zeta-lab/b36e7360-bacb-5ff5-9319-18b0b8b964ba/scratchpad/chk.py`

## 7. Residual uncertainty (what I did *not* settle)

- I read the paper via a text extraction of the public PDF; a local clone of
  `anthropics/zeta-23-lean` (commit `3635e74`) was available and I read the Lean sources
  directly. Those two are solid.
- I did **not** search MathSciNet/zbMATH (no access). A 19th/20th-century source stating
  "(tr A)² ≤ n₊(A)·tr(A²)" as a named lemma very likely exists; I could only cite the
  rank-version via the modern low-rank-recovery literature. This does not change the verdict,
  which is already (b).
- The de Branges / Beurling–Selberg sweep (§4, item 5) was keyword-based only. A specialist in
  Hermite–Biehler theory should be asked whether the "energy ≥ 4k" corollary has an
  independent name there. But since the corollary follows from textbook linear algebra, a
  prior appearance would be *additional* prior art, never a rescue of novelty.

## 8. Naming advice

Given the verdict, the honest framing is *not* a new named theorem but "the involution
specialisation of the inertia + Cauchy–Schwarz bound (Lemma 3.1 + Lemma 3.3 of [Zeta23])".
If a local descriptive label is still wanted for a Lean file:

1. **"Involution-normalised inertia bound"** — accurate; no collision found.
2. **"Hyperbolic-pair Frobenius lower bound"** — matches the paper's own "hyperbolic blocks"
   vocabulary; mild collision risk with Krein-space "hyperbolic pair" (a standard term for a
   two-dimensional neutral-vector pair), which is arguably a feature since it is the same idea.
3. **"Pair-normalised positive-index bound"** — accurate, unlovely.

Names to **avoid** because they are taken by the very source that pre-empts this:
"rank–trace inequality" (Lemma 3.2 / `rank_trace_ineq`), "thresholded Cauchy–Schwarz count"
(Lemma 3.3 / `cauchySchwarz_count`), and anything eponymous. Also avoid "Sylvester-type
inequality" (overloaded: Sylvester rank inequality, law of inertia, Sylvester's determinant
identity).

## 9. Sources

- https://www-cdn.anthropic.com/564f962e60643842f5fcb4a17c9dbc8f608f1c37.pdf
- https://github.com/anthropics/zeta-23-lean
- https://eudml.org/doc/252338 (Bombieri, Weil's quadratic functional I)
- https://arxiv.org/pdf/0706.4138 and https://epubs.siam.org/doi/10.1137/070697835 (Recht–Fazel–Parrilo)
- https://en.wikipedia.org/wiki/Sylvester%27s_law_of_inertia
- https://en.wikipedia.org/wiki/Haynsworth_inertia_additivity_formula
- https://nhigham.com/2021/03/09/eigenvalue-inequalities-for-hermitian-matrices/
- https://arxiv.org/pdf/2501.14545 (Baluyot–Goldston–Suriajaya–Turnage-Butterbaugh)
- https://arxiv.org/pdf/2511.20059 (Goldston–Suriajaya)
- https://en.wikipedia.org/wiki/Montgomery%27s_pair_correlation_conjecture
