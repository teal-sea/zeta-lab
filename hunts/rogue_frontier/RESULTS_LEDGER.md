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

## RF-C004 — truncated Weil form enclosures (P-WEIL)

- **Status:** ACTIVE (source verification stage).

## RF-C005 — rigorous Baez-Duarte distances (P-NB)

- **Status:** ACTIVE.

## RF-C006 — Bian F_kappa engine and tail (P-FK)

- **Status:** ACTIVE.
