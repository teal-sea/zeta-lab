1. **The bound: none. No finite bound on the prolate-mode truncation error of ΔT was derived; `eps_trunc.json` has `"eps_upper": null` on all 33 entries (11 builds × 3 c) and `eps_trunc()` returns arb("inf"). Outcome 4 for bound_trunc/; ALIGNMENT s5 status unresolved (paused by the box), not obstructed.** The truncation error is exactly E_n = τ_f(R_n − Π'_n) (Identity A), and both traces are +∞ for every n (Lemma 1), so any bound must come from a cancellation. Two claims are kept apart: (i) that ΔT^(n) → ΔT_exact at all is proven nowhere in the record (DERIVATION s2.5 lists where I looked); (ii) the route the brief names is blocked by the Sonin overlap S_∞F(1 − P)D on the prolate tail, whose norm does not decay in n. (ii) kills that route; it does not show that no bound exists.
2. **Assumptions:** A1 (the objects: S_∞ from CC eq. 81, Π_S the projection onto Θ ran S_∞, the module form of two_adic/ s5), A2 (T_∞, T_S finite), A3 (the stored ΔT is τ_f(Q_∞^(n) − Q_S^(n)) before bound_quad/'s errors), A4 (Q, T_∞ as delivered at dps 40). No number in `eps_trunc.json` depends on any of them, because there is no number. The same assumptions give a mode-free statement that serves the count without ΔT: **Lemma 3, κT_∞ ≤ T_S ≤ KT_∞ with κ = (√2 − 1)⁴ = 17 − 12√2 ∈ [0.02943725152286 ± 3.6e−15] and K = 1/κ = (√2 + 1)⁴ ∈ [33.9705627484771 ± 4.6e−14]**, so n_−(R_S) ≥ n_−(Q − κT_∞) and n_−(R_S) ≤ n_−(Q − KT_∞) on the window space. The counts are assembler/'s.
3. **Values on the c = 2.9 builds: null on all eleven.** What any future bound must meet there, by the triangle inequality through ΔT_exact: ε_t(a) + ε_q(a) + ε_t(b) + ε_q(b) ≥ ‖ΔT(a) − ΔT(b)‖₂, up to **4.950e−3** at N = 32 (200 against 280 modes). What a bound along the blocked route would cost even if it closed (Proposition 4, the window weight above the heuristic frequency 2n/√3): **0.2125 / 0.1603 / 0.1313 / 0.1131 / 0.0975** at N = 32 for 200 / 240 / 280 / 319 / 364 modes, 12 to 26 times the band 8.2e−3; the mass is the edge jump of the window, and on the continuous windows (Σv_n = 0, one eigenvalue of any count) it is **0.0275 / 0.0115 / 0.0063 / 0.0040 / 0.0025**, 8 to 39 times smaller.
4. **Grade:** Identity A, Lemmas 1, 2, 2', 3 and Proposition 4 are ordinary arguments, **unreviewed** (referee/ has DERIVATION s2 since 91ce087). Lemma 1's measured companion: the partial sums of τ_f(Q_∞^(n)) for f = U_0 at c = 2.9 grow by **0.9900 / 0.9910 / 0.9909 per unit of log n** (predicted w_f = 0.9899), while the stored ΔT's U_0 entry moves by **1.67e−3** over 200 to 364 modes, 0.28 percent of its pieces' growth: measured, one window, one c. Lemma 3 holds on every stored build (smallest margins 1.09e−3 and 2.78e−3): necessary, not sufficient.
5. **Open:** statement O (DERIVATION s2.5): a bound on the τ_f-effect of the Sonin overlap, which needs a frequency-by-frequency localization of ran S_∞ against F(1 − P)D on the prolate tail; or a lower bound on that effect, which would turn "blocked" into "obstructed". Also open: the prolate-to-Legendre leak sin θ_n of Lemma 2' (derivable from kernel/'s coefficients, not computed); Lemma 3' (a sharper mode-free lower form, stated, not built: it needs W_∞ at the autocorrelation shifted by ±log 2). Nothing here is a claim about RH.

# RESULTS: bound_trunc/, the prolate-mode truncation tail of ΔT

Worker `bound_trunc/`, 2026-09-24, 17:35 to about 18:40 (box to 20:35),
branch `teal-sea/weil-c4-s2`. Brief: `BRIEF.md` (870d1bd). The derivation is
`DERIVATION.md` (s1 feasibility, s2 derivation); the interface is
`INTERFACE.md`. Every number below is pinned by `test_bound_trunc.py`.

## 1. What was asked, and what came of it

The brief asked for a proven ε_trunc ≥ ‖ΔT_exact − ΔT_stored‖₂ from the
modes beyond nvec, evaluated in arb on every stored build. The milestone-1
verdict (4a0818f) was that no such bound closes; the coordinator accepted it
with five adjustments (grade "does not close" exactly; a measured companion
for Lemma 1; the window-size claim as a proposition; Lemma 3 delivered with
κ enclosed and its direction, the count left to assembler/; the upper
constant). This file reflects all five.

## 2. Results

**Identity A** (DERIVATION s1.1). With R_n the projection onto the omitted
ζ_j, and Π'_n the projection onto (1 − Π_S)ΘW_n:
ΔT_exact − ΔT^(n) = τ_f(R_n − Π'_n). The stored construction is the same
2-adic functional applied to ran S_∞ ⊕ W_n instead of the Sonin space.

**Lemma 1** (s1.2). τ_f(R_n) = τ_f(Π'_n) = +∞ for every n and every window
f ≠ 0. Companion (s2.9, f = U_0, c = 2.9, |s| ≤ 60): w_f = 0.9899; partial
sums 3.162 at 80 modes and 4.251 at 240; slopes 0.9900, 0.9910, 0.9909 per
unit of log n on [40, 80], [80, 160], [120, 240]; the Poisson form
4j/(s² + 4j²) matches each mode to a relative 0.47/j at j = 20 and 0.27/j at
j = 239. Extrapolated along that slope, each piece grows by 0.593 over 200 to
364 modes; the stored ΔT's U_0 entry stays in [5.06e−3, 6.73e−3].

**Lemma 2 and 2'** (s1.3, s2.4). A degree (Legendre) truncation is carried
into itself by Θ up to λ-sized terms (PD preserves polynomial degree; checked
exactly for P_2 to P_16 in the test). The prolate truncation leaks by at most
2a sin θ_n. sin θ_n was not computed.

**The blocked step** (s1.3 mechanism 2, s2.5). Up to λ-sized terms the
overlap of ΘW_n with Θ ran S_∞ is −a⟨Fσ, (1 − P)Du⟩, an operator whose
norm does not decay in n.

**Proposition 4** (s2.7). For σ above the window band 2πN/L:
λ_max(M_σ) ≤ 4(2N + 1)/(πL(σ − 2πN/L)), attained up to a few percent by the
edge-jump vector (overlap of the top eigenvector with it 0.944 to 0.999 on
the builds where the proposition applies), and on Σ v_k = 0 the supremum is
at most 4K₂/(3πL(σ − 2πN/L)³). At σ_n = 2n/√3 on the stored builds:
0.0975 to 0.2973 where it applies (0.1174 at c = 2.9, N = 8; the N = 32 row is
line 3), 0.0025 to 0.0799 on the continuous windows; where σ_n lies inside the
band (80 modes at N = 16; 200 modes at c = 2.2, N = 32) it is 0.8764
(c = 2.9, N = 16) to 1.0 (c = 2.2).

**Lemma 3** (s2.6). κT_∞ ≤ T_S ≤ KT_∞, κ = 17 − 12√2, K = 17 + 12√2
(rationals κ_lo < κ < κ_hi of width 12·2^{−80} in `kappa_bounds()`).
Checked on the stored builds as a necessary condition: the smallest margin
of T_S − κT_∞ is 1.086e−3 (c = 2.9, N = 32, 240 modes) and of KT_∞ − T_S is
2.783e−3 (c = 2.9, N = 32, 364 modes). A float probe of Q − κT_∞ is in
DERIVATION s1.4, labelled as a probe; the counts are assembler/'s
(`assembler/floor_count.py`).

**Measured responses** (`responses.json`, every pair of stored builds at
equal (c, N)). The largest ‖ΔT(a) − ΔT(b)‖₂ is 4.950e−3 at c = 2.9, N = 32
(200 against 280 modes) and 2.974e−2 at c = 2.2, N = 32 (200 against 240).
Single pairs quoted elsewhere: 4.177e−3 at c = 2.9, N = 32 for 319 against
364 modes; 3.688e−3 at c = 2.9, N = 16 for 120 against 160 modes at
S = 1600; 7.853e−2 at c = 2.2, N = 16 for 80 against 120 modes at S = 1200.
With every entry here null, the necessary inequality of line 3 holds
vacuously; the test checks it for any finite entry, here or in bound_quad/.

## 3. Pins

| statement | test |
|---|---|
| 33 null entries, keys, reasons, Kmax | `test_json_has_every_build_with_null_and_reason`, `test_kmax_matches_two_adic_and_the_stored_units` |
| eps_trunc() has no finite upper end; unknown builds refused | `test_eps_trunc_returns_no_finite_upper_end` |
| responses (4.950e−3, 4.177e−3, 3.688e−3, 7.853e−2, 2.974e−2) | `test_responses_recomputed_from_the_snapshot`, `test_response_values_quoted_in_results` |
| the necessary inequality, triangle inequality explicit | `test_every_bound_dominates_every_response` |
| κ, K, κ_lo, κ_hi | `test_kappa_and_K_enclosures` |
| Lemma 3 on the stored builds (1.086e−3, 2.783e−3) | `test_lemma3_holds_on_every_stored_build` |
| Lemma 2 (exact rationals) | `test_lemma2_D_inverse_keeps_the_degree_tail` |
| Proposition 4 closed form, inequalities, values | `test_window_tail_closed_form_against_quadrature`, `test_proposition4_inequalities_and_pinned_values`, `test_proposition4_recomputed_for_one_build` |
| Lemma 1 companion (0.9899, 3.162, 4.251, slopes, 0.47/j, 0.27/j, [5.06e−3, 6.73e−3], 1.67e−3, 0.593, 0.28 percent) | `test_lemma1_partial_sums_grow_like_log_n`, `test_lemma1_stored_delta_T_entry_stays_put`, `test_lemma1_mode_contributions_reproduce` |

## 4. Reproduction

    PYTHONPATH=$PWD /Users/thomas/zeta-lab/.venv/bin/python hunts/weil_propagation/c4_s2/bound_trunc/eps_trunc.py          # about 20 s: eps_trunc.json, responses.json
    PYTHONPATH=$PWD /Users/thomas/zeta-lab/.venv/bin/python hunts/weil_propagation/c4_s2/bound_trunc/lemma1_companion.py   # about 4 min: lemma1_companion.json
    PYTHONPATH=$PWD /Users/thomas/zeta-lab/.venv/bin/python -m pytest -q -n 2 hunts/weil_propagation/c4_s2/bound_trunc tests/test_hunt_probe_discipline.py tests/test_docs_numbering.py   # about 40 s

## 5. Grades and ALIGNMENT s5

| statement | grade |
|---|---|
| Identity A, Identity B, Lemmas 1, 2, 2', 3, Corollaries 3.1 and 3.2, Proposition 4 | ordinary argument, unreviewed |
| no bound on the truncation error | outcome 4; ALIGNMENT s5 **unresolved (paused by the box)**: a route is blocked, no obstruction is proven |
| Lemma 1's companion, Proposition 4's values, the responses, Lemma 3 on the stored builds | measured |

Original to this session (novelty not searched): Identity A, Lemma 1 and its
consequence that the response band cannot bound the truncation error without
an argument identifying the limit, Lemma 2 (the degree truncation is
Θ-compatible), Lemma 3 with its constants, and Proposition 4. The objects are
Connes-Consani's and Connes-Consani-Moscovici's as two_adic/ and kernel/ built
them.

## 6. The doors

This folder did not measure a ceiling, but its blocked route has the same
shape of inventory, so it is listed.

1. **Active constraint.** The Sonin overlap (mechanism 2) is the only step
   that did not close; the edge jump of the window basis (Proposition 4) is
   what would set the size of any bound along it.
2. **Frozen choices, and what relaxing each would trade.**
   - Truncation by prolate index, not by Legendre degree: a degree
     truncation removes mechanism 1 exactly (Lemma 2) at the price of
     rebuilding ΔT (two_adic/'s code, other folders' units).
   - The discontinuous window basis U_n: restricting to Σ v_n = 0 costs one
     eigenvalue in any count and cuts the high-frequency weight 8 to 39
     times at c = 2.9, N = 32 (Proposition 4). Genuine trade shape: give up
     one slack eigenvalue to buy the binding weight.
   - The heuristic threshold 2n/√3 in Proposition 4: a phase-space estimate,
     not derived; a proof of mechanism 2 would replace it.
   - The crude step of Lemma 3 (Tr M ≥ (1 − a)²T_∞): Lemma 3' keeps Tr M
     exactly, needs W_∞ at shifted autocorrelations.
3. **Information class.** Every door above stays inside the data the current
   construction reads (the prolate modes, kernel/'s T_∞, the window basis)
   except Lemma 3', which needs a new archimedean form, and a degree
   truncation, which needs ΔT rebuilt.
