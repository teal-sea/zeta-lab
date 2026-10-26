# PREREG: exact_gram/, the rebuilt rows, their reading, and the decision table

Written 2026-10-26 on branch `hunt/c4-exact-gram`. **Committed before any
rebuilt row exists**: at this commit no rebuild module (`rebuild.py`) exists,
no block has been computed, and the only computation run in this folder is
`price_block.py` (timings on synthetic values, no number about ΔT). The
stored rows it refers to were analysed long ago (checker/ s7.8, s7.9;
delta_t_bound/); the two stored-row readings quoted in s2.4 were computed
today from those rows and are labelled as such. Everything below is fixed
from here on. Anything added after a rebuilt row exists goes in a dated
section of `RESULTS.md` headed as post-registration, never here. Nothing here
is a claim about RH.

## 1. The rebuilt object

- **ΔT_rb(c, N)** for c ∈ {2.2, 2.5, 2.9} and N ∈ {8, 16, 32}, from one hat
  computation at **nvec = 280**, Kmax = `two_adic.ta_prolate.kmax_for(280)`
  = 14. The hats and ρ do not depend on c or N; only the window sums do, so
  the nine cells cost one rebuild.
- **Modes**: kernel/'s `sonin.prolate_vectors(40, 0, 280)` Legendre
  coefficients, read as exact decimals and carried in balls. The object is
  the projection onto the span of these computed modes (and their b_n). Its
  distance to the span of exact prolates (bound_quad/'s E5) belongs to the
  truncation side, with ε_t (s2.2).
- **Exact Gram matrices, never from s-samples** (bound_quad/ DERIVATION
  s2.8 step 2): G_z in closed form (Parseval on ℝ for the polynomial
  modes, minus the [0, 1] part by the power series of Fξ_n); G_b by Gauss
  panels in v on [1, 2^14] with an a priori panel bound, plus the finite
  integration-by-parts sum beyond 2^14, where it converges (the kmax_for
  rule). Both as ball matrices; each must pass a ball Cholesky (positive
  definiteness decided in balls) or the rebuild stops.
- **Hats** ζ̂_n(s), b̂_n(s): the algebra of `ta_prolate.hats_modes` (per
  dyadic level partials, then r^k sums), in balls at 133 bits (dps 40), with
  the w-quadrature error (E3) and the tail-series remainder (E4) added to
  each hat's radius by a priori bounds.
- **s-grid**: Gauss-Legendre panels of width 1/2, 8 nodes, on [0, S'] with
  **S' = 10^4**; the half s < 0 by the exact symmetry ρ(−s) = ρ(s) of real
  modes at α = 1, with V̂ evaluated at −s directly. At S' = 10^4,
  bound_quad/'s crude E1 (Prop 2, m ≤ nvec) is **6.97e−4** at c = 2.9,
  N = 32 (pinned in `test_exact_gram.py`); at the stored S = 2266.1 it is
  1.455e−2, above the decision scale, so the stored S is not used unless a
  tail-mass lemma is committed before production (then S' = 2266.1 with
  that lemma's E1, an option recorded, not chosen).
- **The window integral's Gauss error** on the s-panels: bounded a priori on
  the Bernstein ellipse inside the strip |Im s| < 1/2, where the hats and ρ
  continue analytically.
- **ρ and M in balls**: ρ_Q(s) = ŵ(s)* G^{−1} ŵ(s) by triangular solves with
  the ball Cholesky factor; M = (1/2π) Σ_s w_s (ρ_∞ − ρ_S) V̂V̂*.

**Prerequisites, each a derivation committed before production:** P1 the E3
panel bound, P2 the E4 remainder, P3 the s-panel Gauss bound, P4 the G_b
panel bound and its tail. If any of them does not close, the rebuild is not
run and that step is recorded as the obstruction (s3, row D0).

**ε_q**, the rebuild's error: the spectral norm of the ball radius of ΔT_rb
(upper-rounded Frobenius norm of the radius matrix) plus E1 plus the P1 to
P4 terms that are not already inside the balls. It bounds
‖ΔT_280,exact − centre(ΔT_rb)‖₂, where ΔT_280,exact is bound_quad/'s
ΔT_nvec,exact at nvec = 280.

## 2. The reading checker/ will apply to the rebuilt rows

### 2.1 The matrices

- R_centre(c, N) = Q_mp − T∞_mp − centre(ΔT_rb), every entry an exact
  rational: Q_mp and T∞_mp as `assembler/assemble.py` forms them (`q_mp`,
  `t_inf_mp`, dps 40), and the ball midpoints read exactly.
- ε_aux = (2N + 1)(E_Q_ENTRY + E_TINF_ENTRY), assembler/ PREREG (a)'s
  stated entry bounds for Q and T∞ (4e−39 and 1e−29).

### 2.2 The bound

ε = ε_q + ε_t + ε_aux, with ε_t a bound on ‖ΔT_exact − ΔT_280,exact‖₂ from
a truncation lemma (bound_trunc/'s statement O, or LEMMA.md), **null today**.
If the lemma closes only on the continuous windows H = {Σ v_n = 0}
(bound_trunc/ Prop 4(c)), ε_t is a bound on H only and every count below
that uses it is taken on H.

### 2.3 What counts as a surviving negative

**C_N(ε) := n_−(R_centre + εI)**, by exact rational inertia (the LDLᵀ route
of checker/ s7.9 and assembler/'s `count_build`, ε upper-rounded to a
rational), on three spaces: the full (2N + 1)-dimensional space, C4's class
V_4 (as assembler/ builds it), and H. An eigenvalue of R_centre strictly
below −ε is a surviving negative; by Weyl, n_−(R) ≥ C_N(ε) for every R
within ε of R_centre. No band enters any count of a rebuilt row: the band
rule is retired for rebuilt rows.

- With ε_t null, the statement is about the 280-mode object
  R^(280) = Q − T∞ − ΔT_280,exact, not about R_S: the mode limit stays the
  unproven assumption of bound_trunc/ claim (i).
- With ε_t closed, it is about the construction's R_S on the window space
  (assembler/ PREREG's R_ex).
- On H, n_−(full) ≥ C_N^H(ε), and C_N^H ≥ C_N − 1 (interlacing).

### 2.4 Context from the stored rows (computed today, float64, measured)

Neither number below is a gate; they say where the rebuilt reading is
expected to sit. On the stored (280, 2266) row at c = 2.9, N = 32 the 20th
eigenvalue is −1.0285e−2 on the full space and −9.7248e−3 on H (the 19th
on H is −1.0527e−2); the record's 1.18e−2 (V_4) and 1.21e−2 (full) are the
uniform-ε crossovers over all five N = 32 builds (delta_t_bound/ s5), set by
the 200-mode build.

## 3. The decision table (c = 2.9; the same rows are read at 2.5 and 2.2)

The scale is the record's: **1.18e−2**, the uniform bound below which the
stored 20 at N = 32 survives (delta_t_bound/ s5, V_4).

| row | ε_q | ε_t | reading |
|---|---|---|---|
| D0 | not finite, or a prerequisite P1 to P4 fails | any | nothing counted; E2 unresolved, with the failing step named |
| D1 | finite, **below 1.18e−2** | null | **E2 closes below the scale.** Record C_8, C_16, C_32 at ε_q + ε_aux on the three spaces, as statements about R^(280) only |
| D2 | finite, **at or above 1.18e−2** | any | **E2 closes above the scale.** Record the same counts; the stored scale does not carry the 20 at this ε, whatever C_32 is, and the next door is S' or the tail-mass lemma |
| D3 | finite | finite | a statement about R_S. G := C_32(ε) − C_16(ε) on the space ε_t covers: **G ≥ 2**: the growth survives a bound, evidence against the bounded-rank prediction that rules out any remainder of rank below C_32(ε); **G ≤ 1**: the growth does not survive, the prediction stays alive (unresolved) |

G ≥ 2, not G ≥ 1: assembler/ s5 found that a rise of one can be the
deepest direction deepening (interlacing), not a new negative direction.
The brief calls D3 with G ≥ 2 a refutation. The operator's ruling
(`c4_s2/MISSION.md`, ΔT-bound follow-up: C4 fixes no rank bound, so no
finite N refutes it) is the grade this folder will record; the wording is
the owner's to change.

## 4. Checks every rebuilt row must pass before it is read

1. **Precision replay**: every 16th block is recomputed at 200 bits
   (dps 60); its balls must intersect the 133-bit balls entrywise. A miss is
   a defect: stop, count nothing.
2. **Stored-row comparison**: ‖centre(ΔT_rb(2.9, 32)) −
   ΔT_stored(280, 2266)‖₂ is recorded. If it exceeds band(2.9, 32) + ε_q
   (8.2e−3 + ε_q) and the replay passed, the finding is that the band
   understated the stored error at that build (bound_quad/ s2.8 already
   measures E2 there at band size), not a defect of the rebuild.
3. **Gate**: the rebuild module calls `two_adic`'s data validation on its
   inputs before any block, and `test_exact_gram.py` checks that the gate
   refuses Epstein (1,1,6), W_a (a = 1/4) and DH (s5).

## 5. The (U-S) gate, extended to DH

checker/'s gate (`checker_gate.OBJECTS`) holds ζ, Dedekind, Epstein (1,1,6)
and W_a, not DH. This folder adds the DH case without editing checker/:
DH's coefficients (period 5, a_2 = κ, a_3 = −κ, a_4 = −1, a_5 = 0,
κ = (√(10 − 2√5) − 2)/(√5 − 1)) in exact arithmetic over ℚ(√5, √(10 − 2√5))
through `checker_gate.lambda_vectors` and `gate_events`, which must report a
composite atom at n = 6; and DH's 2-adic data through two_adic/'s
`ta_data.validate`, degree 1, which must refuse it (|s_1(2)| = |κ| ≠ 1).

## 6. The guard and the checkpoint

`guard.py`. The key is the sha256 of the HEAD blobs of `rebuild.py`'s import
closure over exact_gram/, two_adic/ and kernel/ (checker_glue's
`imported_names`), together with checker/'s T_S input digest (**b2e7787b**,
`checker_glue.ts_key()` today). It is re-read before every block; a dirty
closure file, an untracked file shadowing an imported name, or a dirty T_S
input refuses the block (raises; never skips). The s-blocks are split into
contiguous shards (RUNS.md). After every block a shard writes, atomically,
one JSON checkpoint: the running ball sum of its window sums for every
(c, N) and both families ([midpoint, radius] decimal strings, about 3 MB),
the index of the last block it holds, the key and a payload hash. A
checkpoint whose key differs is refused, not resumed and not recomputed
silently. Assembly sums the shards in index order and refuses if a shard is
missing or does not end at its last block. Every 16th block (the replay
set, s4) also keeps its own block sum. Outputs stay outside git and are
recorded by SHA-256.
