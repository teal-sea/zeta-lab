# VERIFICATION: every exact number by a second implementation, and planted faults

**Hunt #148. Status: the cross-check run of 2026-10-26 (15 items) reproduced every exact
number it recomputes; no row disagrees with the primary run (section 2 lists the rows that
record source errata or findings, and the nine probe triples that rest on the shared
empty-box argument rather than an independent sum). Files produced on branch
`hunt/ff-probe`, not landed.** Every count on
this page is read from `results_second.json` (written by `crosscheck.py`) or measured by
`test_ffprobe.py`, and pinned there. Grades as in `MISSION.md`.

## 1. The second implementation

`ffprobe_pari.py` writes the arithmetic again in PARI/GP, through cypari2, and imports
nothing from `ffprobe.py`: residue symbols by resultant and by Frobenius at each prime
factor, Gauss sums by enumeration of the residues, by the Davenport-Hasse closed form and by
the prime-power reduction, cyclotomic numbers as polmods modulo polcyclo(N), Patterson's C
and rho_0, the probe's weights and its direct sum, the local factor of eq. (local-P) by its
definition, and the rival's L-polynomials, whose roots come from PARI's `polroots`. Python
and numpy only add up integer exponent histograms (counts of roots of unity). The
conventions are read again from the sources, not from `ffprobe.py`.

`crosscheck.py` runs it over the ranges of the primary run. Where the documents quote a
value, PARI recomputes the value and the two are compared as exact elements of Q(zeta_N);
where they quote a count of checks, PARI recomputes the count on its own. The identities
the second implementation uses beyond the definitions (the Chinese remainder theorem for
Gauss sums, Davenport-Hasse, the prime-power reduction, Gamma(c) = gamma_3(c) for squarefree
c, which it uses at degree 5) are each checked inside PARI against enumeration at smaller
degree (item `pari_internal`, and the Davenport-Hasse and C_p items).

## 2. What was reproduced

One row per comparison in `results_second.json`, rendered by `render_verification.py`
(`--check` fails if this table is stale; `test_ffprobe.py` runs it). "short" marks a row
whose held count is below its checked count, a false flag or a nonzero mismatch count; the
prose after the table says, for each, whether it is a documented erratum or a failure.

<!-- results-table: begin (render_verification.py) -->
| item | check | held / checked | |
|---|---|---|---|
| `C_p` | `agree` | 720 / 720 |  |
| `C_p` | `reduction_eq_enumeration` | 448 / 448 |  |
| `C_routes` | `agree` | 56 / 56 |  |
| `F_routes` | `pari_crt_eq_pari_definition` | 30,576 / 30,576 |  |
| `F_routes` | `pari_definition_eq_ffprobe_factorization` | 30,576 / 30,576 |  |
| `K` | `specs.0.agree` | 120,344 / 120,344 |  |
| `K` | `specs.1.agree` | 44,247 / 44,247 |  |
| `davenport_hasse` | `q13_n4.mismatches.2007_own_character` | 0 mismatches |  |
| `davenport_hasse` | `q13_n4.mismatches.2007_with_2014_character` | 4,394 mismatches | short |
| `davenport_hasse` | `q13_n4.mismatches.2014` | 0 mismatches |  |
| `davenport_hasse` | `q7_n3.mismatches.2007_own_character` | 0 mismatches |  |
| `davenport_hasse` | `q7_n3.mismatches.2007_with_2014_character` | 0 mismatches |  |
| `davenport_hasse` | `q7_n3.mismatches.2014` | 0 mismatches |  |
| `davenport_hasse` | `q7_n6.mismatches.2007_own_character` | 0 mismatches |  |
| `davenport_hasse` | `q7_n6.mismatches.2007_with_2014_character` | 45,129 mismatches | short |
| `davenport_hasse` | `q7_n6.mismatches.2014` | 0 mismatches |  |
| `ledger` | `target_L.degree_one` | true |  |
| `pari_internal` | `Gamma_eq_gamma3_squarefree` | 2,401 / 2,401 |  |
| `pari_internal` | `structural_eq_enumeration` | 9,975 / 9,975 |  |
| `phase_identities` | `G_refinement_all_pairs.mismatches` | 0 mismatches in 3,249 |  |
| `phase_identities` | `Gamma_closed_form.mismatches` | 0 mismatches in 400 |  |
| `phase_identities` | `lambda_alpha_equal` | true |  |
| `phase_identities` | `prime_phases.mismatches` | 0 mismatches in 27 |  |
| `phase_identities` | `reciprocity.mismatches` | 0 mismatches in 2,688 |  |
| `phase_identities` | `signal.mismatches.G_squarefree` | 0 mismatches |  |
| `phase_identities` | `signal.mismatches.gamma1_gamma2` | 0 mismatches |  |
| `phase_identities` | `signal.mismatches.gamma2_cubed` | 0 mismatches |  |
| `probe` | `0_0_1.equal_to_stored` | true |  |
| `probe` | `0_0_1.zero` | true |  |
| `probe` | `0_0_2.equal_to_stored` | true |  |
| `probe` | `0_0_2.zero` | true |  |
| `probe` | `0_0_3.equal_to_stored` | true |  |
| `probe` | `0_0_3.zero` | true |  |
| `probe` | `0_0_5.equal_to_stored` | true |  |
| `probe` | `0_0_5.zero` | true |  |
| `probe` | `0_1_0.frequency_box_empty` | true |  |
| `probe` | `0_1_0.zero` | true |  |
| `probe` | `0_1_1.equal_to_stored` | true |  |
| `probe` | `0_1_1.zero` | true |  |
| `probe` | `0_1_2.equal_to_stored` | true |  |
| `probe` | `0_1_2.zero` | true |  |
| `probe` | `0_2_1.equal_to_stored` | true |  |
| `probe` | `0_2_1.zero` | false |  |
| `probe` | `0_2_2.equal_to_stored` | true |  |
| `probe` | `0_2_2.zero` | true |  |
| `probe` | `0_3_2.equal_to_stored` | true |  |
| `probe` | `0_3_2.zero` | false |  |
| `probe` | `1_0_2.equal_to_stored` | true |  |
| `probe` | `1_0_2.zero` | true |  |
| `probe` | `1_0_3.equal_to_stored` | true |  |
| `probe` | `1_0_3.zero` | true |  |
| `probe` | `1_0_5.equal_to_stored` | true |  |
| `probe` | `1_0_5.zero` | true |  |
| `probe` | `1_1_0.frequency_box_empty` | true |  |
| `probe` | `1_1_0.zero` | true |  |
| `probe` | `1_1_2.equal_to_stored` | true |  |
| `probe` | `1_1_2.zero` | true |  |
| `probe` | `1_1_3.equal_to_stored` | true |  |
| `probe` | `1_1_3.zero` | true |  |
| `probe` | `1_2_1.frequency_box_empty` | true |  |
| `probe` | `1_2_1.zero` | true |  |
| `probe` | `1_3_2.equal_to_stored` | true |  |
| `probe` | `1_3_2.zero` | false |  |
| `probe` | `2_0_3.equal_to_stored` | true |  |
| `probe` | `2_0_3.zero` | true |  |
| `probe` | `2_1_0.frequency_box_empty` | true |  |
| `probe` | `2_1_0.zero` | true |  |
| `probe` | `2_2_1.frequency_box_empty` | true |  |
| `probe` | `2_2_1.zero` | true |  |
| `probe` | `3_0_5.equal_to_stored` | true |  |
| `probe` | `3_0_5.zero` | false |  |
| `probe` | `3_1_0.frequency_box_empty` | true |  |
| `probe` | `3_1_0.zero` | true |  |
| `probe` | `3_2_1.frequency_box_empty` | true |  |
| `probe` | `3_2_1.zero` | true |  |
| `probe` | `4_0_5.equal_to_stored` | true |  |
| `probe` | `4_0_5.zero` | false |  |
| `probe` | `4_1_0.frequency_box_empty` | true |  |
| `probe` | `4_1_0.zero` | true |  |
| `probe` | `5_1_0.frequency_box_empty` | true |  |
| `probe` | `5_1_0.zero` | true |  |
| `rho0_relations` | `affine_invariance.hold` | 144 / 144 |  |
| `rho0_relations` | `finite_hecke.hold` | 72 / 72 |  |
| `rho0_relations` | `finite_hecke.vanish_at_r_o_P^(n-1)` | 36 / 36 |  |
| `rho0_relations` | `hecke_infinity.corrected.hold` | 60 / 60 |  |
| `rho0_relations` | `hecke_infinity.printed_2007.hold` | 40 / 60 | short |
| `rho0_relations` | `hecke_infinity.printed_2014.hold` | 20 / 40 | short |
| `rho0_relations` | `hecke_infinity_both.q7_n3.2007_character.hold` | 30 / 30 |  |
| `rho0_relations` | `hecke_infinity_both.q7_n3.2014_character.hold` | 30 / 30 |  |
| `rho0_relations` | `hecke_infinity_both.q7_n6.2007_character.hold` | 30 / 30 |  |
| `rho0_relations` | `hecke_infinity_both.q7_n6.2014_character.hold` | 30 / 30 |  |
| `rho0_relations` | `periodicity.hold` | 24 / 24 |  |
| `rho0_relations` | `psi_polynomial.vanish_above_R` | 36 / 36 |  |
| `rho0_relations` | `rho0_agree_q7_n3.agree` | 1,218 / 1,218 |  |
| `rho0_relations` | `rho0_agree_q7_n6.agree` | 60 / 60 |  |
| `rho0_relations` | `theta_base.j1.rho0_1_0_is_1` | true |  |
| `rho0_relations` | `theta_base.j1.rho0_1_1_is_q_tau` | true |  |
| `rho0_relations` | `theta_base.j1.rho0_1_2_is_0` | true |  |
| `rho0_relations` | `theta_base.j2.rho0_1_0_is_1` | true |  |
| `rho0_relations` | `theta_base.j2.rho0_1_1_is_q_tau` | true |  |
| `rho0_relations` | `theta_base.j2.rho0_1_2_is_0` | true |  |
| `rival` | `any_disc_zero` | false |  |
| `rival` | `off_iff_disc_positive` | true |  |
| `s4` | `F_abs2_q_to_1_plus_degA.hold` | 10 / 10 |  |
| `s4` | `base_values.deg1_rho0_0_is_1` | true |  |
| `s4` | `base_values.deg1_rho0_1_3_zero` | true |  |
| `s4` | `base_values.deg1_rho0_2_is_tau2_q2` | true |  |
| `s4` | `base_values.rho0_1_0_is_1` | true |  |
| `s4` | `base_values.rho0_1_1_is_q_tau` | true |  |
| `s4` | `base_values.rho0_1_2_is_0` | true |  |
| `s4` | `base_values.rho0_1_3_is_0` | true |  |
| `s4` | `component_table.0,0.all_zero` | false |  |
| `s4` | `component_table.0,1.all_zero` | false |  |
| `s4` | `component_table.0,2.all_zero` | true |  |
| `s4` | `component_table.0,3.all_zero` | true |  |
| `s4` | `component_table.1,0.all_zero` | false |  |
| `s4` | `component_table.1,1.all_zero` | true |  |
| `s4` | `component_table.1,2.all_zero` | false |  |
| `s4` | `component_table.1,3.all_zero` | true |  |
| `s4` | `component_table.2,0.all_zero` | false |  |
| `s4` | `component_table.2,1.all_zero` | false |  |
| `s4` | `component_table.2,2.all_zero` | false |  |
| `s4` | `component_table.2,3.all_zero` | false |  |
| `s4` | `component_table.3,0.all_zero` | true |  |
| `s4` | `component_table.3,1.all_zero` | false |  |
| `s4` | `component_table.3,2.all_zero` | true |  |
| `s4` | `component_table.3,3.all_zero` | false |  |
| `s4` | `component_table.4,0.all_zero` | false |  |
| `s4` | `component_table.4,1.all_zero` | false |  |
| `s4` | `component_table.4,2.all_zero` | false |  |
| `s4` | `component_table.4,3.all_zero` | false |  |
| `s4` | `hecke_infinity_both.2007_character.hold` | 20 / 20 |  |
| `s4` | `hecke_infinity_both.2014_character.hold` | 20 / 20 |  |
| `s4` | `hypergeometric.0.C1_equals_tau_times_H` | true |  |
| `s4` | `hypergeometric.0.rho0_i1_equals_C1` | true |  |
| `s4` | `hypergeometric.1.C1_equals_tau_times_H` | true |  |
| `s4` | `hypergeometric.1.rho0_i1_equals_C1` | true |  |
| `s4` | `hypergeometric.2.C1_equals_tau_times_H` | true |  |
| `s4` | `hypergeometric.2.rho0_i1_equals_C1` | true |  |
| `s4` | `hypergeometric.3.C1_equals_tau_times_H` | true |  |
| `s4` | `hypergeometric.3.rho0_i1_equals_C1` | true |  |
| `s4` | `hypergeometric.4.C1_equals_tau_times_H` | true |  |
| `s4` | `hypergeometric.4.rho0_i1_equals_C1` | true |  |
| `s4` | `hypergeometric.5.C1_equals_tau_times_H` | true |  |
| `s4` | `hypergeometric.5.rho0_i1_equals_C1` | true |  |
| `s4` | `hypergeometric.6.C1_equals_tau_times_H` | true |  |
| `s4` | `hypergeometric.6.rho0_i1_equals_C1` | true |  |
| `s4` | `hypergeometric.7.C1_equals_tau_times_H` | true |  |
| `s4` | `hypergeometric.7.rho0_i1_equals_C1` | true |  |
| `s4` | `hypergeometric.8.C1_equals_tau_times_H` | true |  |
| `s4` | `hypergeometric.8.rho0_i1_equals_C1` | true |  |
| `s4` | `hypergeometric.9.C1_equals_tau_times_H` | true |  |
| `s4` | `hypergeometric.9.rho0_i1_equals_C1` | true |  |
| `s4` | `relations.finite_hecke.hold` | 36 / 36 |  |
| `s4` | `relations.hecke_infinity_corrected.hold` | 10 / 20 | short |
| `s4` | `relations.periodicity_r_b4` | true |  |
| `s4` | `rho0_agree_q13_n4.agree` | 232 / 232 |  |
| `s4` | `three_body.0001.all_equal_one` | false | short |
| `s4` | `three_body.0003.all_equal_one` | false | short |
| `s4` | `three_body.0011.all_equal_one` | false | short |
| `s4` | `three_body.0013.all_equal_one` | false | short |
| `s4` | `three_body.0021.all_equal_one` | false | short |
| `s4` | `three_body.0023.all_equal_one` | false | short |
| `s4` | `three_body.0031.all_equal_one` | false | short |
| `s4` | `three_body.0033.all_equal_one` | false | short |
| `s4` | `three_body.0201.all_equal_one` | false | short |
| `s4` | `three_body.0203.all_equal_one` | false | short |
| `s4` | `three_body.0211.all_equal_one` | false | short |
| `s4` | `three_body.0213.all_equal_one` | false | short |
| `s4` | `three_body.0221.all_equal_one` | false | short |
| `s4` | `three_body.0223.all_equal_one` | false | short |
| `s4` | `three_body.0231.all_equal_one` | false | short |
| `s4` | `three_body.0233.all_equal_one` | false | short |
| `s4` | `three_body.1001.all_equal_one` | false | short |
| `s4` | `three_body.1003.all_equal_one` | false | short |
| `s4` | `three_body.1011.all_equal_one` | false | short |
| `s4` | `three_body.1013.all_equal_one` | false | short |
| `s4` | `three_body.1021.all_equal_one` | false | short |
| `s4` | `three_body.1023.all_equal_one` | false | short |
| `s4` | `three_body.1031.all_equal_one` | false | short |
| `s4` | `three_body.1033.all_equal_one` | false | short |
| `s4` | `three_body.1201.all_equal_one` | false | short |
| `s4` | `three_body.1203.all_equal_one` | false | short |
| `s4` | `three_body.1211.all_equal_one` | false | short |
| `s4` | `three_body.1213.all_equal_one` | false | short |
| `s4` | `three_body.1221.all_equal_one` | false | short |
| `s4` | `three_body.1223.all_equal_one` | false | short |
| `s4` | `three_body.1231.all_equal_one` | false | short |
| `s4` | `three_body.1233.all_equal_one` | false | short |
| `structural` | `agree` | 319,200 / 319,200 |  |
| `symbols` | `q13_n4.all_routes_agree` | 182 / 182 |  |
| `symbols` | `q7_n3.all_routes_agree` | 399 / 399 |  |
| `symbols` | `q7_n6.all_routes_agree` | 399 / 399 |  |

15 items, 193 rows, 37 marked short; 7,727.7 s of item time in total.
<!-- results-table: end -->

**No row is a failure to reproduce.** The rows marked short are of three kinds, and each
equals the primary run's own record (`test_ffprobe.py`,
`test_second_implementation_reproduces_the_primary_numbers`):

- **Source errata, reproduced exactly.** Davenport-Hasse in the 2007 note's form, with the
  2014 additive character: 45,129 mismatches at (7, 6) and 4,394 at (13, 4) (`SOURCES.md`
  row 2). The Hecke relations at infinity as printed: 40 of 60 hold in the 2007 reading and
  20 of 40 in the 2014 one (rows 8 and 9). The corrected reading holds 60 of 60.
- **A fit tried outside its range.** `s4.relations.hecke_infinity_corrected`, 10 of 20, is
  the n = 3 sign rule applied at n = 4, recorded the same way in `results_step3.json`
  (`relations_note`). The n = 4 relation holds 20 of 20 in each additive character
  (`s4.hecke_infinity_both`).
- **The finding itself.** `s4.three_body.*.all_equal_one` is false for every admissible
  component choice. That is `S4.md` section 3's defect: the three-prime ratio is defined
  only at lambda = 5 and 11, and the defect values equal the primary run's.

Beyond the rows, PARI reproduces these values: the 66 off-circle rivals, 50 of them beyond
sigma = 1; the rival's mismatched monomials, X^2 to X^3 W; the balanced probe values 1.529
and 0.609; and every probe triple's exact value. The nine triples with an empty frequency box
are zero by the same box argument in both implementations, not by an independent sum. The
crosscheck run of 2026-10-26 crashed once in item `s4`. The cause was a bug in
`crosscheck.norm2`, which asked PARI for the degree of an exact zero; nothing disagreed. It
was fixed and `s4` was rerun alone (`RUNS.md`).

## 3. Planted faults

`ffprobe.FAULTS` switches on eight planted faults, four wrong Gauss-sum signs and four wrong
residue symbols, each at a different place, and `test_ffprobe.py` checks which of six quick
equality checks each one turns red: the two symbol routes, Davenport-Hasse against
enumeration, the structural route against enumeration, Lemma 7.1 locally (definition
against closed form at T + 1 for j = 0..5 and at T^2 + 1 for j = 0, 3), the probe's direct
and Euler representations at (0,2,1), and the PARI implementation against `ffprobe`. Without
a plant all six are green.

| plant | what is wrong | checks turned red |
|---|---|---|
| `gauss_sign` | G_1(P) negated at every prime of degree 2 (structural route) | structural, Lemma 7.1, probe, PARI |
| `gauss_brute_sign` | every enumerated Gauss sum negated | Davenport-Hasse, structural, probe, PARI |
| `dh_sign` | the Davenport-Hasse closed form negated | Davenport-Hasse |
| `prime_gauss_all` | every prime Gauss sum G_m(P) negated (structural route) | structural, Lemma 7.1, probe, PARI |
| `tau_sign` | every tau(eps chi^j) negated | all but the symbol routes |
| `symbol` | the Frobenius-route symbol modulo T + 1 one step off | all but Davenport-Hasse |
| `symbol_res` | the resultant-route symbol modulo T + 1 one step off | all six |
| `dlog` | the discrete logarithm of 2, which both symbol routes share, one step off | all six |

Every plant turns at least one check red. The Davenport-Hasse closed form of `gauss_dh`
feeds nothing else (the structural route has its own prime formula), so its sign is caught
by its own check alone. A fault in a component that both of `ffprobe`'s own routes share is
what the PARI comparison is for: it goes red for six of the eight plants.

## 4. Reproduce

```
.venv/bin/python hunts/ff_probe/crosscheck.py                 # results_second.json, checkpointed per item
.venv/bin/python -m pytest -q -n0 hunts/ff_probe/test_ffprobe.py -k "plant or lesion or second"
```
