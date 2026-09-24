# INTERFACE: bound_trunc/ (the prolate-mode truncation error of ΔT)

For assembler/ and referee/. Import with
`sys.path.insert(0, "hunts/weil_propagation/c4_s2/bound_trunc")`, then
`import eps_trunc`. Python:
`PYTHONPATH=<worktree root> /Users/thomas/zeta-lab/.venv/bin/python`.
Importing `eps_trunc` pulls in numpy, mpmath and python-flint only (not
kernel/'s prolate machinery).

## 1. The brief's interface

| name | returns | notes |
|---|---|---|
| `eps_trunc(c, N, nvec, S, Kmax)` | `flint.arb` | **arb("inf"), a ball with no finite upper end, for every stored build**: no bound was derived (DERIVATION.md s1, s2.5; outcome 4, unresolved). The same for any other configuration (no bound is derived anywhere); `known_build(c, N, nvec, S, Kmax)` says whether a configuration is one of the stored ones (c in {2.2, 2.5, 2.9} as string or float, the eleven (nvec, S, N) of BRIEF.md with S rounded down to an integer, Kmax = `kmax_for(nvec)`). |
| `eps_trunc.json` | a **list** of 33 entries | keys `c` (string), `N`, `nvec`, `S` (the S the build used, a float: 2266.10…, 2633.16…, 3060.08… for 280, 319, 364 modes, as bound_quad/ and referee/ key it), `S_key` (the integer of the brief), `Kmax`, `eps_upper` (**null** in every entry), `grade`, `assumptions` (empty: no number depends on any), plus `reason`, `blocking_step` and `size_if_closed` (Proposition 4 at σ_n = 2n/√3: a size, not a bound) |

`kmax_for(nvec)` restates `two_adic.ta_prolate.kmax_for`; a test pins the
equality and the stored units' `kmax`.

## 2. What else is here

| name | what | grade |
|---|---|---|
| `responses(c, N)` → `responses.json["responses"]["c|N"]` | ‖T_S(a) − T_S(b)‖₂ for every pair of stored builds at equal (c, N) (checker/'s snapshot, digest in `responses.json["meta"]`). Any bounds must satisfy ε_t(a) + ε_q(a) + ε_t(b) + ε_q(b) ≥ that value (triangle inequality through ΔT_exact); `test_every_bound_dominates_every_response` checks it for every finite entry here and in bound_quad/. | measured |
| `kappa_ball()`, `K_ball()`, `kappa_bounds(bits=80)` | Lemma 3's κ = (√2 − 1)⁴ = 17 − 12√2 and K = 1/κ = (√2 + 1)⁴ = 17 + 12√2 as arb balls (at the caller's `flint.ctx.prec`), and rationals κ_lo < κ < κ_hi of width 12·2^{−80} | closed forms |
| `window_tail(c, N, σ)`, `window_tail_matrix`, `window_tail_report` | Proposition 4: M_σ = the compression of (1/2π)∫_{|s|>σ}\|f̂\|² to the window space in closed form (Si, Ci; mpmath dps 30); λ_max, the edge-jump vector's value, the top eigenvector's overlap with it, the supremum on Σ v_k = 0, and the explicit upper bounds of Prop. 4 (a) and (c) when σ > 2πN/L | measured (closed form, float eigenvalues) |
| `lemma1_companion.py` → `lemma1_companion.json` | partial sums of τ_f(Q_∞^(n)) for f = U_0 at c = 2.9, \|s\| ≤ 60, to 240 modes, from kernel/'s closed-form transforms; the stored ΔT's U_0 entry on the five c = 2.9, N = 32 builds | measured |

## 3. For assembler/

- There is no ε_trunc. Any ε built as ε_trunc + ε_quad is +∞ on every
  build, so the Weyl route of the brief gives no count from this folder.
- Lemma 3 (DERIVATION.md s2.6) is a mode-free alternative:
  κT_∞ ≤ T_S ≤ KT_∞ on window functions, so n_−(R_S) ≥ n_−(Q − κT_∞) and
  n_−(R_S) ≤ n_−(Q − KT_∞), with the errors of Q and T_∞ entering as in
  Corollary 3.1. The counts are yours (floor_count.py); use `kappa_bounds()`
  for an exact rational κ_lo ≤ κ (lower side), and 1/κ_lo ≥ K for the upper
  side, K_hi := 1/κ_lo (Q − K_hi T_∞ ≤ Q − K T_∞ ≤ R_S, since T_∞ ≥ 0).
- Lemma 3' (s2.6) is a sharper lower form, stated and not built: it needs
  the archimedean form W_∞ at the autocorrelation shifted by ±log 2.
