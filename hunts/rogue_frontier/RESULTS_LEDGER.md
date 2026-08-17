# RESULTS_LEDGER — every serious claim, its status, its grade

Grades use the repository ladder (measured / hardened / kernel-checked); a
composite claim takes the grade of its weakest step. Statuses: ACTIVE,
UNDER ATTACK, PROMOTED, DEAD, REFUTED. Dead ends move to FAILURE_LEDGER.md
with their mechanism.

---

## RF-C001 — m_4(1) = 13/4 for the sine-Gram matrix, checked exactly

- **Statement.** For the band Gram matrix of the sine process at
  lambda = 1, the normalised fourth spectral moment is 13/4, as the
  10 Aug 2026 paper states in §7.5(f).
- **Status:** settled (a verification, not a new claim).
- **Origin:** this campaign's own engine first said 49/15; the exact
  finite-N lattice-count engine plus a CUE Monte Carlo killed the 49/15
  and located the defect (Gaussian trace-moment approximation out of its
  regime). Record in `sine_gram/RESULTS.md`.
- **Grade:** hardened (exact integer arithmetic at finite N, two-sided
  Lagrange extrapolation agreeing to 3.24996..3.24998, independent MC).
- **Value:** methodological; confirms the instrument for RF-C002.

## RF-C002 — exact higher sine-Gram moments (P-SG)

- **Statement (target).** Exact values of m_5(1), m_6(1), and the
  lambda-polynomials, beyond the literature's m_4.
- **Status:** ACTIVE, computation running.

## RF-C003 — improved window in the RH-conditional cubic certificate (P-WIN)

- **Statement.** In the Aug 2026 paper's §7.5(g) chain (RH assumed,
  unrefereed preprint), replacing the hand-picked window cos(8s/5) by
  v*(s) = 1 - (1467/1000)s^2 + (1159/1000)s^4 raises
  2m_2(1,v) - m_3(1,v) from 0.6852438755373... to the exact rational
  2245228120295149280/3276332462159207451 = 0.6852870232880...,
  lifting the distinct-zeros constant from 0.850826305842608 to
  0.850828702939872 (+2.397e-6).
- **Evidence (first arm):** closed forms reproducing the paper's printed
  value to all digits; windowed-CUE exact-lattice cross-check to 4e-10 at
  two windows; EL residual showing the paper's window is not a critical
  point (max residual 5.6e-2); exact rational arithmetic for v*;
  two-backend ball enclosures of the final constants; positivity and
  monotonicity of v* in rational arithmetic; admissibility analysis
  (v* is admissible exactly as the paper's own windows are, including the
  same two glosses the paper itself carries: the endpoint taper and the
  lambda -> 1 limit of the triple-correlation input).
- **Status:** UNDER ATTACK. A blinded second arm is re-deriving the
  functional from the paper and attacking (independent reconstruction +
  adversarial stage). Not promoted until it survives.
- **Grade if it survives:** hardened, RH-conditional, inheriting the
  source paper's §7.5(g) machinery and its unrefereed status. The
  improvement is in the sixth decimal; the paper's printed 0.85082
  headline is unchanged. Honest framing: a measured optimization gain
  inside someone else's theorem chain, exactly like the laboratory's
  flagship transplant, but smaller.
- **Caveat recorded by the first arm:** the reported sup (0.6852870321770)
  is a local search outcome over three parametrizations; global
  optimality over the full admissible class is NOT claimed.

## RF-C004 — truncated Weil form: replication, enclosures, and the rival control (P-WEIL)

- **Delivered 2026-08-17.** Three findings, graded separately; the full
  record is `weil_trunc/RESULTS.md` and `weil_trunc/SOURCE.md`.
- **(a) Replication of arXiv:2605.20224 / 2607.02828 (Groskin; construction
  from Connes-van Suijlekom arXiv:2511.23257 Prop 4.1 and CCM
  arXiv:2511.22755; open question from Connes arXiv:2602.04022 SS6).**
  Independent implementation from definitions only; eight validation gates
  against printed values all pass; no defect located in either posting.
  Two display-level constant slips in CCM (4.4)/(4.14) that cancel in
  their own tables are documented. The survey's provenance for these IDs
  was scrambled and is corrected in SOURCE.md. Grade: hardened.
- **(b) Enclosure-checked spectra.** Ball-arithmetic assembly with
  explicit tail radii; LDL^T inertia, Rayleigh brackets and Rump
  eigenvalue enclosures mutually consistent at all 27 grid cells; every
  eigenvalue of both parity sectors strictly positive over the zeta grid
  c in {6..29} x N in {4..32} and the DH grid c in {6..47} x N = 32.
  Grade: hardened.
- **(c) The rival control, run for the first time.** The RH-violating
  Davenport-Heilbronn function, fed through the identical pipeline,
  shows the SAME qualitative signature as zeta: strictly positive
  spectrum and a ground state locating its on-line zeros (to 1.7e-36 at
  c = 47). The qualitative spectral picture therefore distinguishes
  nothing; what separates the two is the N-saturated error floor
  (zeta ~3.7e-59 vs DH ~1.0e-10 at c = 13, a ~49-order gap), whose
  attribution (RH-truth vs Euler product vs pole, all differing at once)
  is measured but NOT settled. Grade: measured, with the confound stated.
- **Follow-up thread (not pursued, per foraging rule):** Weil positivity
  is false for DH, so its band minimum must eventually go negative;
  the data bound the first negative at c > 47 (N <= 32). Candidate for a
  GitHub issue as an observation.

## RF-C005 — rigorous Baez-Duarte distances (P-NB)

- **Status:** ACTIVE.

## RF-C006 — Bian F_kappa engine and tail (P-FK)

- **Status:** ACTIVE.
