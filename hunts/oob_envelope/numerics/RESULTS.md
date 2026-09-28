# RESULTS: numerics lane (oob_envelope)

2026-09-28: the L = 0.8 bound and the L = 1.19 stage B bound both passed
independent referee review (`referee/REVIEW.md`, sections "L = 1.19" and 5).
Every grade uses the AGENTS.md ladder.

## Item 6. L = 1.19 (support 2.38), stage B: candidate, hardened by two independent routes

For real even f with supp f ⊆ [−1.19, 1.19] and H = sine:16:

    λ_min(R_H(500)) ≥ 5.71789230595e-48,   so   Q(f) ≥ 5.71789230595e-48 ‖f‖²

given Q ≥ R_H. Route: Arb GL-96 assembly of the N = 500 leading block
(orders 0..998, 384 bits) with the Bernstein-ellipse radius ε_Q ≤ 6.9e-66
in every entry; midpoint Cholesky of A − λ₀I snapped to exact dyadics and
its residual enclosed in Arb (r ≤ 1.5e-113); entry uncertainty
e ≤ 2.3e-63 by row sums; Zhu (13) with ε_D ≤ 1.8e-184, ε_B ≤ 1.5e-87.
λ_min(R_H) ≥ min(λ₀ − r − e, β* − ε_D) − ε_B, only the Arb lower endpoint
reported. `stage_b_modal.py`, `stage_b_result.json`, ledger in `RUNS.md`.

Grades, weakest first:
- Q ≥ R_H: ordinary derivation, referee PASS with stated scope (the
  reduction is L-independent; the referee reviewed it at L = 4/5).
- The numerical step: *enclosure-carrying*, one implementation (this
  lane's GL radii, which the referee did not audit at L = 4/5 either). The
  same code on Modal reproduces the reviewed L = 4/5 bracket
  (≥ 1.15822443198e-17 at λ₀ = 0.9999 λ_meas, referee 1.1579e-17).
- Independent reproduction: the referee's own Clenshaw-Curtis-192/Arb
  route, with its own quadrature and entry bound and a shift fixed in
  advance, proves lambda_min(R_H) > 5.7179e-48 on the same 500-mode
  subspace, and recomputes eps_D < 1.490e-184, eps_B < 1.553e-90
  (`referee/REVIEW.md`, "L = 1.19", verdict lines 1 to 5, PASS).
- So the composite is a **candidate** positivity bound at support 2.38,
  hardened by two independent implementations (sharing python-flint),
  resting on a refereed ordinary derivation; even sector only, not
  kernel-checked, pending external verification.
- Controls (RUNS.md "Negative controls"): at L = 4/5, T# = 60, where the
  form is indefinite, the step returns no bound; a planted in-band constant
  fires. Dropping or flipping H does not discriminate at L = 4/5.
- Consistency (one-sided, K1 analogue): 5.7e-48 ≤ λ*(1.1) ≤ 2.78e-38 (Zhu
  Table 3). N-convergence, measured: λ_meas at N = 500, GL-96 equals
  stage A's N = 360, GL-64 value to 12 digits.

## Five-line graded summary

1. **Envelope constants** S = Σ_p M_p with P_L − H ≤ S for all real t, at
   L = 0.8, 1.0, 1.19 (e.g. 1.5552528 and 3.8634773 with the sine kernel,
   D = 16, against A_L = 2.9420 and 7.0750). *Enclosure-carrying* (Arb,
   two independent proofs per prime). `envelope.json`, commit ca41ce2.
2. **Controls, all measured.** K3: every H frequency is out of band and
   ∫|F|²H = 0 on random window functions to 5e-13; in-band plants and a
   moved-in-band lesion break it by the predicted amounts (`k3.json`). Sign
   gate: Ψ + H stays above the envelope through the matrix code path;
   flipped-H and S → S_opt lesions fire (`envelope_check.json`). K2 on
   Davenport-Heilbronn at L = (log 47)/2, where the form is negative
   (independent enclosure-grade witness): the valid pipeline returns no
   bound (inconclusive, as required); a forced-β lesion finds λ = −0.288
   beamed at the off-line ordinate (`k2_dh.json`).
3. **Reduced form at L = 0.8, T# = 100, H = sine:16, N = 96**: the
   leading block has λ_min(A) > 1.158e-17 (Arb LDL of A − λ₀I, quadrature
   radius in every entry) and provably < 1.1585e-17; with Zhu's two-block
   bound (13), λ_min(R_H) ≥ min(λ₀, β* − ε_D) − ε_B = 1.158e-17 − ε_B,
   ε_B < 3.031e-44, on all of L²_even[−0.8, 0.8]. **Outward-safe endpoint:
   λ_min(R_H) ≥ 1.1579e-17** (the referee's figure; any value up to
   1.157999999999e-17 is also safe). *Enclosure-carrying*
   (`harden_L08_T100_sine16*.json`, 58795ee). Calibration: the same
   pipeline in Zhu's configuration (H = 0, T# = 200, N = 200) gives
   λ_min(R) ≥ 1.02e-17 − ε_B with ε_B < 1.5e-102, **outward-safe ≥ 1.0199e-17**,
   and λ_min(A) < 1.028e-17; the measured R_150 floor 1.3564e-18 matches
   his 1.356e-18 (`harden_L08_T200_none.json`). Correction (referee REVIEW
   §5): an earlier version quoted λ_min(R_H) ≥ 1.158e-17 and ≥ 1.02e-17,
   which dropped ε_B; the code subtracted it but the quoted figure was the
   10-digit display midpoint, and the JSON `lower_bound` field was a
   round-to-nearest float. `harden.py` now stores the exact dyadic lower
   endpoint and a decimal rounded down (edited, not yet rerun).
4. **Composite at L = 0.8**: Q(f) ≥ 1.1579e-17 ‖f‖² for real even f with
   supp f ⊆ [−0.8, 0.8]. An **independently reviewed ordinary derivation**
   (Q ≥ R_H, theory lane, referee PASS) combined with a **hardened
   numerical step** (this lane's Arb/GL bound, reproduced by the referee's
   independent Clenshaw–Curtis/Arb implementation at two resolutions, both
   ≥ 1.1579e-17). Not kernel-checked; pending external verification.
   Referee verdict: `hunts/oob_envelope/referee/REVIEW.md` at b65ef69 on
   branch `teal-sea/oob-cert-referee`. Scope: even sector only; complex f
   would also need the odd-sector bound. Not independently audited: this
   lane's GL entry radii (the referee used its own quadrature instead).
   K1 holds (below Zhu's 2.27e-17 upper bound and the measured window
   floor 1.656e-17). Same support as Zhu (1.6); a sharper constant (his
   8.9e-18) with half the matrix, not a new window.
5. **L = 1.19 (support 2.38), stage A**: on the N = 360 leading block of
   R_H (sine:16), a 384-bit midpoint LDL has one negative pivot at
   T# = 320 and none from T# = 350 to 525 (λ ≈ 5.78e-48 at T# = 500).
   *Measured only*: no quadrature, tail or coupling bound, Arb interval LDL
   undecided, nothing claimed about the whole form. Modal, ≈ 0.85
   core-hours (`stageA_L119_reduced.json`, ledger in `RUNS.md`). Stage B
   (enclosure-carrying) not approved.

## L = 1.19 (support 2.38), stage A: measured only

Modal, 9 units, ≈ 0.85 core-hours (`stageA_L119_reduced.json`). Envelope
sine:16 (S = 3.8634773, enclosure-carrying), N = 360, GL-64, 384 bits, no
quadrature, tail or coupling bound. On the N = 360 leading block, a plain
384-bit midpoint LDL has one negative pivot at T# = 320 and none at
T# = 350, 400, 450, 500, 525; inverse iteration gives λ = 1.65e-48,
4.15e-48, 5.17e-48, 5.776e-48, 6.00e-48 there, monotone as R_{T#} must be.
Arb interval LDL is undecided (304 to 306 of 360 pivots) at every
checkpoint, so even the block's sign is measured, not enclosed, and
**nothing is claimed about the whole form**. External consistency, one
sided only: λ* is nonincreasing in L (nested windows), so Zhu's Table 3
upper bound at L = 1.1 gives λ*(1.19) ≤ λ*(1.1) ≤ 2.78e-38, and the
measured 5.8e-48 is consistent with λ_min(R_H) ≤ λ*(1.19). His bound at
L = 1.2 (9.98e-49) bounds λ*(1.2) ≤ λ*(1.19) from above and so says
nothing about λ*(1.19); no table value brackets it. (Correction, supervisor
review: an earlier version claimed the two upper bounds bracket the
L = 1.19 floor. They do not.)
Zhu's valid-certificate estimate at this support needed N ≈ 1.4 to 2 × 10^4
(his §7); stage B would need N = 500. **This is not a positivity bound at
support 2.38.**

## K2: Davenport-Heilbronn at L = (log 47)/2

The DH form is negative on this window (independent, enclosure-grade witness
in `hunts/rogue_frontier/weil_trunc/dhneg_log.md`, λ = −0.3163, off-line
pair at 85.699). DH normalization pinned to that code (κ to 4e-56, Λ_f(n)
to 5e-55). The valid pipeline (H = 0, S_DH = 25.59) needs T# ≳ 1.6e11 for
β* > 0, so it returns no bound: **inconclusive, as K2 requires**. With β*
forced (an invalid envelope, lesion only), the matrix code finds λ = −0.288
at T# = 150 with the eigenvector beamed at t = 84.5, matching weil_trunc.
`k2_dh.json`, measured.

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
| f | ε_D ≤ 2.8e-95, ε_B < 3.031e-44 (Zhu (12), (13)); full space: λ_min(R_H) ≥ 1.158e-17 − ε_B > 1.1579e-17 | enclosure-carrying |

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

Modal jobs (profile teal-sea): `modal run stage_modal.py` (stage A units then
reducer; `--reduce-only` to rerun the reducer on the stored units) and
`modal run k2_modal.py`.

## Not yet done

Stage B (enclosure-carrying L = 1.19, needs approval), N-convergence at
L = 1.19, the joint LP/SDP envelope, theory §1.7's B_T scan.
