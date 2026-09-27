# RESULTS: numerics lane (oob_envelope), interim

Interim, 2026-09-27: phases 1 and 2 at L = 0.8; L = 1.19 stage A running.
Branch `teal-sea/oob-cert`, not pushed. Every grade uses the AGENTS.md ladder.

## Five-line graded summary

1. **Envelope constants** S = Σ_p M_p with P_L − H ≤ S for all real t, at
   L = 0.8, 1.0, 1.19 (e.g. 1.5552528 and 3.8634773 with the sine kernel,
   D = 16, against A_L = 2.9420 and 7.0750). *Enclosure-carrying* (Arb,
   two independent proofs per prime). `envelope.json`, commit ca41ce2.
2. **K3**: every H frequency is out of band and ∫|F|²H = 0 on random window
   functions to 5e-13; planted in-band terms and a moved-in-band lesion break
   it by exactly the predicted amounts. *Measured* (float64). `k3.json`.
   **Sign gate**: Ψ + H stays above the envelope through the matrix code path;
   flipped-H and S → S_opt lesions fire. *Measured*. `envelope_check.json`.
3. **Leading block at L = 0.8, T# = 100, H = sine:16, N = 96**: λ_min(R_H)
   ≥ 1.158e-17 on all of L²_even[−0.8, 0.8], with Zhu's two-block tail and
   coupling terms and a Bernstein-ellipse quadrature radius in every entry;
   LDL provably fails at 1.1585e-17. *Enclosure-carrying*.
   `harden_L08_T100_sine16*.json`, commit 58795ee.
4. **Composite at L = 0.8**: Q(f) ≥ 1.158e-17 ‖f‖² for real even f with
   supp f ⊆ [−0.8, 0.8]. *Candidate*: its weakest step is the ordinary
   derivation Q ≥ R_H (theory lane RESULTS §1, self-reviewed, no referee
   yet). K1 holds (below Zhu's 2.27e-17 upper bound and the measured
   window floor 1.656e-17). Same support as Zhu (1.6); a sharper constant
   (his 8.9e-18) with half the matrix, not a new window.
5. **Calibration**: the same hardened pipeline in Zhu's configuration
   (H = 0, T# = 200, N = 200) gives λ_min ≥ 1.02e-17 (< 1.028e-17 provably),
   and the measured R_150 floor 1.3564e-18 matches his 1.356e-18.
   *Enclosure-carrying* / *measured* respectively. `harden_L08_T200_none.json`,
   `run_L08_N200.json`.

## The L = 0.8 replication, in full

Reduction (Zhu arXiv:2608.24827v2 Theorem 1.1, eq. (4), with Ψ_L → Ψ_L + H):
for even real f with supp f ⊆ [−L, L],

    Q(f) = 2F(i/2)² + (1/π)∫_0^∞ |F|² (Ψ_L + H) dt           (∫|F|²H = 0)
         ≥ 2F(i/2)² + (1/π)∫_0^{T#} (Ψ_L + H − β*)|F|² dt + β*‖f‖² = R_H(f),

using, for t ≥ T# ≥ 15/4, Ψ_L + H ≥ log(t/2π) − 1/t − S ≥ β* (Zhu Lemma 3.1
as published, plus P_L − H ≤ S from line 1), β* = log(T#/2π) − 1/T# − S.

Steps of the claim in line 4, each with its own grade:

| step | content | grade |
|---|---|---|
| a | P_L − H ≤ S, S = 1.555252846719556 (sine:16) | enclosure-carrying (`envelope.py`) |
| b | ∫|F|²H = 0: H frequencies ≥ 2L | frequencies decided in Arb; identity is Fourier support (theory §1); K3 measured |
| c | Zhu Lemma 3.1 (digamma lower bound, t ≥ 15/4) | published, used as stated |
| d | Q ≥ R_H | ordinary derivation, theory lane, self-reviewed, no referee |
| e | λ_min(A) ≥ 1.158e-17, leading 96 × 96 block with quadrature radius | enclosure-carrying (`harden.py`) |
| f | ε_D ≤ 2.8e-95, ε_B ≤ 3.0e-44 (Zhu (12), (13)) | enclosure-carrying |

Error budget of step e: GL-64 on 200 panels of width 1/2; per panel,
Trefethen's Gauss bound (h/2)·64M/(15(ρ²−1)ρ^{128}), ρ = 1 + √2, with M
bounding the integrand on the rectangle |Re z − c| ≤ h/√2, |Im z| ≤ h/2:
|T̂_n| ≤ 2√(Lν_n)e^{L h/2} (Poisson integral), |cos λz| ≤ cosh(λh/2),
digamma by a center-plus-derivative bound. Total ≤ 5.8e-44 for the largest
entry, added as radius to every entry (asserted in code). Nodes
are snapped to exact dyadic Bessel arguments; the shift ≤ 5.5e-75 enters the
budget through a Cauchy bound on f'.

Measured λ_min(R_H) vs T# (N = 200, no error bounds), sine:32: indefinite
(1 to 3 negative eigenvalues) for T# ≤ 60, positive from T# = 65 (2.0e-18),
1.16e-17 at T# = 100, 1.42e-17 at T# = 200. The envelope threshold 2π e^S ≈ 30
is not the operating point; see `PROGRESS.md` for the table.

## Reproduction (from the repo root; about 10 minutes in total)

```bash
PY=/Users/thomas/zeta-lab/.venv/bin/python   # python-flint 0.9.0, numpy, scipy
cd hunts/oob_envelope/numerics
$PY envelope.py --D 8 16 32 64 128                 # 134 s, writes envelope.json
$PY k3.py                                          # 1 s, k3.json
$PY envelope_check.py                              # 3 s, envelope_check.json
$PY assemble.py --N 200 --Tmax 200 --prec 256 \
    --checks 40 50 60 65 70 75 80 100 120 150 200 \
    --env sine:16 sine:32 sine:64 --out run_L08_N200.json   # 6 min
$PY harden.py --lam0 1.158e-17 1.1585e-17 --out harden_L08_T100_sine16_control.json   # 30 s
$PY harden.py --env none --T 200 --N 200 --lam0 9e-18 1.02e-17 1.028e-17 \
    --out harden_L08_T200_none.json               # 3 min
$PY summarize.py run_L08_N200.json
```

## Not yet done

L = 1.19 (stage A measured scout approved and running; stage B needs a fresh
approval), K2, the joint LP/SDP envelope, theory §1.7's B_T scan.
