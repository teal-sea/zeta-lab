# BRIDGE-SPEC — the composition restated on upstream's own objects

**Sprint 1 draft, 2026-08-12.** Lane 1 step 2 of `PIPELINE.md`. This is the
specification a later session turns into an Aristotle submission for
`Zeta23Ext/Bridge.lean`. It is written against the upstream package as it
actually reads on disk (`/private/tmp/zeta-23-lean`, pinned in
`zeta23ext/lakefile.toml` at `3635e748`), with every name checked at its
definition site rather than recalled. Nothing here is proved; it is a target.

## 1. The upstream objects, verbatim

From `Zeta23/LinAlg/PosIndex.lean`:

```lean
def rtrace  (A : Matrix n n 𝕜) : ℝ := RCLike.re A.trace
def frobSq  (A : Matrix n n 𝕜) : ℝ := RCLike.re (Aᴴ * A).trace
def posIndex {A : Matrix n n 𝕜} (hA : A.IsHermitian) : ℕ
```

From `Zeta23/ZeroSide/RankTraceMult.lean`:

```lean
def gc   (c x : ℝ) : ℝ := x ^ 2 - c * x - (max (x - c) 0) ^ 2
def Pmat (m : ι → ℝ) (v : ι → n → 𝕜) : Matrix n n 𝕜 := Wmat m v * (Wmat m v)ᴴ
def xsq  (v : ι → n → 𝕜) (j : ι) : ℝ := ∑ a, ‖v j a‖ ^ 2
```

From `Zeta23/ZeroSide.lean`, `structure ZeroBlockData (ι d : Type*)` with
fields `m : ι → ℕ` (`one_le_m`), `v : ι → d → ℂ`, the involution
`σ : ι → ι` (`σ_invol`) with `m_σ : m (σ z) = m z` and
`v_σ : v (σ z) = star (v z)`; plus `onLine`, `S₁`, `S₂` as `Finset ι`.

## 2. The fork point, stated exactly

Upstream **Lemma R** (`RankTraceMult.lean:281`) reads

```lean
theorem rank_trace_mult {m : ι → ℝ} (hm : ∀ j, 0 ≤ m j) (v : ι → n → 𝕜)
    {Q : Matrix n n 𝕜} (hQ : Q.IsHermitian) {b : ℕ} (hb : posIndex hQ ≤ b)
    {c : ℝ} (hc : 0 < c) :
    c * rtrace (Pmat m v) + (∑ j, gc c (m j * xsq v j)) + 2 * c * rtrace Q - c ^ 2 * b
      ≤ frobSq (Pmat m v + Q)
```

The cross term never appears: upstream carries `rtrace Q` and forms no
`tr(P·Q)`. That is the whole seam. Our composition skeleton
(`Zeta23Ext/Composition.lean`, kernel-checked and confirmed to build under
`v4.33.0-rc2`) keeps it:

    D = R + 2·tr(P Q) + ‖Q‖²_F,     s ≥ 2N − ‖P+Q‖²_F + D.

**The algebraic identity that makes the two compatible**, and the thing
`Bridge.lean` must actually establish:

    ‖P+Q‖²_F = ‖P‖²_F + 2·tr(P Q) + ‖Q‖²_F   and   ‖P‖²_F = Σ_j m_j² + R,

so `D = ‖P+Q‖²_F − Σ_j m_j²` identically. Our skeleton's conclusion is
therefore the multiplicity inequality `s ≥ 2N − Σ_j m_j²` with the cross
term cancelled, and the census enters as an *extra* lower bound on `D`
rather than as a new term in the composition.

## 3. Target statement

The transplant's own headline, in upstream's objects (the form
`PREPRINT.md` derives, conversion factor exactly 1):

    ‖Â‖²_F  ≥  Σ_{S₁ ∪ S₂} m_ρ²  +  2·θ·c_u·N(I′)

so the target for `Bridge.lean` is, schematically:

```lean
theorem bridge_frobSq_lower
    (D : ZeroBlockData ι d) (Q : Matrix d d ℂ) (hQ : Q.IsHermitian)
    (θ c_u : ℝ) (hθ : 0 ≤ θ) (hcu : 0 ≤ c_u)
    (hcensus : <census hypothesis: D ≥ θ · R₀ carried as a named hypothesis>) :
    (∑ z ∈ D.onLine, ((D.m z : ℝ)) ^ 2) + 2 * θ * c_u * (N I')
      ≤ frobSq (Pmat (fun z => (D.m z : ℝ)) D.v + Q)
```

Three things are deliberate:

1. **The census hypothesis is named, not proved here.** It is the same seam
   as `H3` in `BandCert/`. `Bridge.lean` is a restatement lemma; it must not
   silently absorb an open obligation. Give the hypothesis a name in the
   theorem's binder list so `#print axioms` and a reader both see it.
2. **`𝕜 = ℂ` and `n = d`.** `ZeroBlockData.v : ι → d → ℂ` fixes both; do not
   generalise, the upstream pipeline instantiates at ℂ.
3. **Multiplicities are ℕ upstream and ℝ in Lemma R.** `ZeroBlockData.m` is
   `ι → ℕ` with `one_le_m`; `Pmat`/`rank_trace_mult` take `m : ι → ℝ` with
   `0 ≤ m j`. The coercion `fun z => (D.m z : ℝ)` and the discharge of
   `hm` from `one_le_m` are part of the obligation, not an afterthought —
   a cast mismatch here is the most likely way a generated proof ends up
   proving something adjacent to what is needed.

## 4. What the submission must forbid

Same constraints as batches 1 and 2: zero `sorry`/`admit`/`axiom`
declarations, no `native_decide`, no weakening or restating of any theorem,
proof bodies only. Additionally, specific to this one: **the census
hypothesis may not be discharged**, only carried. An artifact that "proves"
the target without it has proved something else.

## 5. Before submitting

- Resolve `N I'` to the upstream counting function's real name (it is
  referenced as the Theorem B/D density in `PROOF-LEDGER.md`; the mapping to
  `ZeroBlockData` was not chased in this sprint and is the one open item in
  this spec).
- Confirm `Bridge.lean` imports `Zeta23` and not just `Mathlib`, unlike
  `Composition.lean`; that makes it the first module whose local build needs
  the upstream dependency fetched, so the scratch-target trick used for the
  port survey will not work on it.
- Batch 2's port must have landed first: `Bridge` is downstream of nothing,
  but assembling the package to check it is downstream of all of it.
