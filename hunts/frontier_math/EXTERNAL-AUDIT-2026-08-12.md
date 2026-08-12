# Adversarial audit of the 0.6725106958 candidate (2026-08-12)

An audit run from a **fresh clone** by a session that did not build any of
the instruments below, against the source paper's own text. The brief was:
attack the mathematics, and describe plainly whatever survives.

**Result in one line.** No error was found in the algebra, and one hole the
ledger had left implicit was closed. What is *not* closed is a single named
analytic lemma: the retention inequality is established as a genuine
one-sided supremum over on-line configurations, but only at **four sampled
pair depths** and over a **swept family of pair sets**, not uniformly in
either. Until it is uniform, `D >= theta*R0` is not available and the
composition does not deliver the improved constant.

## 0. What was run

Fresh `.venv`, `rigor.BACKEND = python-flint`, both backends present.

| Instrument | Outcome |
|---|---|
| `test_paper_chain.py`, `test_hardened_paper.py`, `test_paper_joint.py`, `test_transplant_lemma.py` | 67 passed in 319 s |
| the source paper (SHA-256 `6792988e…d72f`), §3–§4 and §7.1 | text extracted and read against the chain |
| four new probes written for this audit | §2–§4 below |

## 1. The chain, restated from the source

Re-deriving the composition from the paper's Proposition 4.4 rather than
from this hunt's own documents, to check for double counting.

The paper writes `Â = P₁ + Q′` (simple on-line block; everything else),
and applies its Lemma 3.2 (rank–trace, via von Neumann) to get

    ‖Â‖²_F  ≥  2 tr P₁ − s₁ + 4 tr Q′ − 4(s₂ + p)                    (paper)

whence `s₁ ≥ 4 tr Â − 2N(I′) − ‖Â‖²_F`, and with `tr Ĝ = N(1+o(1))`,
`‖Ĝ‖²_F = N(1/c*₁ + o(1))`, the constant `2 − 1/c*₁ = 0.6725007…`.

The hunt's route replaces Lemma 3.2 by the Frobenius expansion and treats
the two blocks separately:

    ‖Â‖²_F = ‖P₁‖²_F + 2 tr(P₁Q′) + ‖Q′‖²_F
           ≥ (2 tr P₁ − s₁ + R) + 2 tr(P₁Q′) + (4 tr Q′ − 4 n₊(Q′))

using `(n_i − 1)² ≥ 0` on the on-line side (which is where the `+R` comes
from, `R` being the off-diagonal Gram mass the paper's spectral step never
sees) and, on the off-line side, `λ² ≥ 4λ − 4` for `λ > 0` together with
`λ² ≥ 0 ≥ 4λ` for `λ ≤ 0`, i.e. exactly the paper's own `n₊(Q′) ≤ s₂ + p`
(its Prop 4.1). Subtracting:

> **The improvement over the paper is exactly `R + 2 tr(P₁Q′)`.**

**This is not a double count.** The `4 tr Q′ − 4 n₊(Q′)` term appears
identically in both routes; the hunt neither spends it twice nor needs the
paper to have left it unused. The ledger's phrase "the 4-per-pair cushion
the paper's (L) would have consumed" reads as though the cushion were the
source of the gain; it is not. The gain is `R + 2 tr(P₁Q′)`, and nothing
else.

**Why the per-pair decomposition is nevertheless forced.** Taking
`‖Q′‖²_F ≥ 4 tr Q′ − 4 n₊(Q′)` whole leaves the requirement
`−2 tr(P₁Q′) ≤ (1−θ)R`. Measured on this hunt's own worst adversarial
placement that is `0.0796 ≤ 1.3e-5` — false by four orders of magnitude.
So the chain must go per-pair,

    ‖Q′‖²_F = Σ_p ‖Q_p‖²_F + Σ_{p≠p′} tr(Q_p Q_{p′}),
    ‖Q_p‖²_F = (4 tr Q_p − 4 b_p) + slack(y_p),

and the load-bearing inequality is

    −2 tr(P₁Q′)  ≤  (1−θ) R  +  Σ_p slack(y_p)  +  Σ_{p≠p′} tr(Q_p Q_{p′}).   (★)

The pair-pair term sits on the **right**, it is measured **negative**, and
it is therefore load-bearing rather than decorative.

## 2. Closed by this audit: the pair-pair term is the dual's `T_signed`

`paper_joint.budget` charges `Σ_r slack(y_r) + T_signed`, with
`T_signed = 2 Σ_{i<j} T(t_i − t_j, y_i, y_j)` and
`T(dt,y₁,y₂) = W(dt,|y₁−y₂|) + W(dt,y₁+y₂)`. Nothing in the tree pinned
`T_signed` against the composition's `Σ_{p≠p′} tr(Q_p Q_{p′})`, so the
identification dictionary had a fifth entry missing.

It is an identity. Writing `Q_p = 2(x_p x_pᵀ − y_p y_pᵀ)` with
`x_p + i y_p = v_{z_p}/√(2πA)`,

    tr(Q_p Q_q) = 2 [ Re⟨v_p, v_q⟩² + Re⟨v_p, v̄_q⟩² ],

and LAW D turns the two inner products into `Φ₂(Δt + i(y_p−y_q))/A` and
`Φ₂(Δt + i(y_p+y_q))/A`, which is `W(Δt, y_p−y_q) + W(Δt, y_p+y_q)`.

Measured on explicit truncated-grid matrices (K = 1200):

| pairs | `cross_total` | `2 Σ T` | rel. defect |
|---|---|---|---|
| (0,0.49), (6.406,0.49) | −0.08473897 | −0.08489156 | 1.8e-3 |
| (0,0.49), (3.1,0.3) | 3.53379498 | 3.53367033 | 3.5e-5 |
| (0,0.02), (2.0,0.45) | 5.85442997 | 5.85768327 | 5.6e-4 |
| (0,0.49), (4,0.49), (9,0.49) | 2.52609743 | 2.52267401 | 1.4e-3 |

Defects are the assembly's own ~1/K LAW D truncation. So the joint dual
does budget the pair-pair term, and (★) is the statement its verdict makes.

## 3. Audit finding A: the end-to-end battery omits the term it is testing

`identification_seam.end_to_end`'s SHARP row compares

    damage := −2 tr(PQ)   against   (1−θ)R + Σ_p slack_p

with the pair-pair term absent from the left. By §1 it belongs there.

Re-run with `damage − cross` against the same budget, all eleven
configurations still hold, with room:

| configuration | damage | cross | damage−cross | budget | margin |
|---|---|---|---|---|---|
| ADV zeros at first damage minimum | 0.03978 | 0 | 0.03978 | 0.15344 | +0.11366 |
| ADV zeros at first two minima | 0.04861 | 0 | 0.04861 | 0.15354 | +0.10493 |
| ADV double zeros at first minimum | 0.07956 | 0 | 0.07956 | 0.15345 | +0.07389 |
| worst dipole y=0.49 | −7.77127 | −0.08458 | −7.68669 | 0.30712 | +7.99381 |
| ν=0.5 lattice y=0.49 | −15.31364 | −0.06607 | −15.24757 | 0.61399 | +15.86156 |
| soft lattice ν=0.9576 y=0.49 | −19.28195 | −0.34223 | −18.93972 | 0.76743 | +19.70715 |

So the omission changes no verdict **in this battery** — but the reason is
that the battery's three binding rows are single-pair, where `cross = 0`
identically, and every multi-pair row uses the benign 9-point lattice whose
damage is hugely negative. The battery therefore never tests the
combination the adversary would actually choose: on-line points at the
*joint* damage minima of a *multi-pair* field. The joint dual sweeps that
supremum; the end-to-end matrix check does not corroborate it there.

**Recommended:** add multi-pair rows whose on-line points are placed at the
joint field's minima (the `_damage_minima` device, applied to the summed
field), and put `cross` on the left of the SHARP row.

## 4. Audit finding B: the shipped band instrument is unusable at shallow depth

`PaperBandDual` ships with `step = 5e-4`. Sweeping the depth continuum at
θ = 0.995 with that step:

| y | 0.0001 | 0.0005 | 0.001 | 0.002 | 0.02 | 0.1 | 0.3 | 0.49 |
|---|---|---|---|---|---|---|---|---|
| cap/slack | (0 bands) | **1.399** | 0.941 | 0.688 | 0.447 | 0.425 | 0.424 | 0.594 |

At y = 5e-4 the verdict is **negative**, and at y ≲ 1e-4 the instrument
finds no bands at all and returns `cap = 0` while its own `no_missed_band`
control reports `clear = False` — a silent pass, not a pass.

This is the instrument, not the mathematics. A band has half-width ~y, and
`bands()` adds a local slope margin `slope·step` whose ratio to the true
band maximum scales as `2·step/y`. Refining the step at fixed y confirms it
(G = 100):

| y | step 5e-4 | 1e-4 | 2e-5 | 5e-6 |
|---|---|---|---|---|
| 5e-4 | 1.4359 | 0.6929 | 0.5249 | **0.4926** |
| 1e-3 | 0.9903 | 0.5889 | 0.5034 | **0.4872** |
| 2e-3 | 0.7444 | 0.5357 | 0.4926 | **0.4845** |
| 0.02 | 0.5091 | 0.4872 | — | — |

The refined ratio converges to ≈0.49 at every depth tested, the same value
the shipped step reports at y = 0.02. So (★) looks comfortable and roughly
depth-uniform down to at least y = 5e-4 — but the shipped instrument would
report a false negative for any session that probed there, and the four
depths the rational certificate covers are all in the region where the
coarse step happens to be adequate.

**Recommended:** tie `step` to `min(y)/40` (or accept a supplied step) and
re-run the depth ladder; then extend `band_certificate.py` to a depth
*cover* rather than four depth *points*.

## 5. What is universally quantified and what is sampled

| object | quantification |
|---|---|
| `s ≥ 2N − ‖P+Q‖²_F + D` and its θ-corollary | all configurations — Lean 4 + Mathlib, sorry-free, **for exactly unit vectors** |
| grid-incidence law | all even bounded measurable φ supported in [−½,½] — Lean, sorry-free |
| `cap(θ,y) ≤ slack(y)` — the on-line side | genuine sup over **all** on-line placements and multiplicities (band lattice, cross-band charges dropped, per-band square completion, closed-form tail) |
| the same, over pair depths | **four sampled y** in {1/50, 1/10, 3/10, 49/100} — exact in ℚ; float grade on a depth grid ≥ 2e-3 (§4) |
| the same, over pair sets | **swept families** (lattices ν_p = 0.5–3, dipoles, phases) — not all finite pair sets |
| `R ≥ R₀` census | exact rational dual certificate for the LP; four kernel-minimum bounds at numeric-plus-slope-margin grade |
| prime-side `tr Ĝ`, `‖Ĝ‖²_F`, Theorem B density | cited from the source paper |

Two mismatches worth naming, both routine to repair, neither yet repaired:

1. **The Lean skeleton's hypothesis is `⟨u_i,u_i⟩ = 1`.** The paper's
   vectors are truncated to `0 ≤ k < d`, so `‖u‖² ≤ 1` with equality only
   in the limit (its Lemma 2.2 sums over `k ∈ ℤ`). For sub-unit norms the
   conclusion is `s ≥ 2 tr P − ‖P+Q‖²_F + D`, not `s ≥ 2N − …`; the
   difference `2(N − tr P)` is exactly what seam (i) has to show is o(N).
   The kernel-checked artifact therefore does not literally apply to the
   objects it is applied to.
2. **`Σ_p b_p = p` vs `n₊(Q′) ≤ s₂ + p`.** The per-pair route measures
   `b_p = 1`; the paper bounds the whole index. They agree when `s₂ = 0`.
   The multiple-on-line case (`s₂ > 0`) is not exercised by the battery.

## 6. Verdict

The mechanism is written down and correct as far as it goes; the
improvement term is identified exactly; the composition is arithmetic and
kernel-checked; the census floor has an exact rational dual; the retention
has a rational cell-cover at the depths it covers. One analytic statement
remains genuinely open, and it is the one the whole reading rests on:

> **Retention lemma (open).** There is a θ ≥ 0.995 such that for *every*
> finite on-line configuration and *every* finite set of off-line pairs
> with depths in (0, ½], inequality (★) holds.

Established: the supremum over on-line configurations, for fixed pair sets,
at four depths exactly and on a depth grid numerically. Not established:
uniformity in the depth, and uniformity over pair sets. Without it the
corollary's hypothesis `D ≥ θ·R₀` is unavailable, and `H + 2θc_u` does not
follow from the source paper's theorems.

The rest of the outstanding work — the units seam, the unit-vector
hypothesis, the Lean leaves for the four kernel minima, the multi-pair rows
in the battery — is bookkeeping and mechanisation, not discovery.
