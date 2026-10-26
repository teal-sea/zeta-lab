# li_arithmetic: a uniform bound on the arithmetic part of lambda_n

**Hunt #150 (`rh_moonshot`), mechanism 3. Built 2026-10-21, written up and its prime-side
run made on 2026-10-26 when the owner resumed the hunt in place. Status: constructed and
measured; not challenged yet; unreviewed by any person.** Nothing here is a result until
the case log in `hunts/README.md` says how this hunt ended. Files: `li_arith_split.py`
(the split and its routes), `li_arith_prime.py` (the prime-side form and the bounds),
`li_arith_wa.py` (the W_a rival), the three `run_li_arith_*.py` drivers,
`test_li_arithmetic.py` (the pins), `artifacts/` (every number below), `RUNS.md`, this page.

Grades are the hunt's (`MISSION.md`, top): *measured*, *hardened*, *derived* with its
review status, *kernel-checked*; *inferred* marks a reading no computation here checks.
Nothing here is kernel-checked and no Arb enclosure carries any step (the Cauchy routes use
Arb as fast multiprecision and drop the radii). A composite claim takes the grade of its
weakest step.

## 1. Target

Li's criterion: RH holds if and only if lambda_n = n [z^n] log xi(1/(1-z)) >= 0 for every
n >= 1 (Li 1997; Bombieri and Lagarias 1999). Bombieri and Lagarias split lambda_n into an
archimedean part and an arithmetic part. Target: an inequality on the arithmetic part,
proved from the Euler product, whose uniformity in n gives lambda_n >= 0 for every n; or
else the exact n-range and term at which every candidate inequality fails.

The target is RH-equivalent by construction (it is Li's criterion rewritten), so the only
possible progress is an estimate that proves it. Kill condition 3 of `MISSION.md` applies
to any version that offers the rewrite without the estimate.

## 2. Construction (derivations self-reviewed, each identity pinned by a test)

**The split.** With s = 1/(1-z) and the factor (s-1) kept with zeta,

    lambda_n = A(n) + T(n),
    A(n) = n [z^n] log( s pi^{-s/2} Gamma(s/2) )
         = 1 - (n/2)(gamma + log 4 pi) + sum_{k=2}^{n} C(n,k) (-1)^k (1 - 2^{-k}) zeta(k),
    T(n) = n [z^n] log( (s-1) zeta(s) ) = sum_{j=1}^{n} C(n,j) eta_{j-1},

with zeta'/zeta(s) + 1/(s-1) = sum_k eta_k (s-1)^k. T(1) = Euler's gamma, and A(n) grows
like (n/2) log n. The DH analogue keeps f(s) whole (no pole, f(1) > 0) with its own
archimedean factor (`li_arith_split.py` docstring).

**Routes.** A(n): a binomial transform of zeta(k) at the precision its 2^n cancellation
needs, and a cancellation-free series with a Hurwitz tail. T(n): Stieltjes constants
(small n) and a Cauchy integral of log((s-1) zeta(s)) on |z| = r with Arb's zeta. lambda_n
itself: an independent Cauchy route on xi, and the tables of hunt #128 (`li_dh_onset`).

**The prime-side form.** The Laguerre generating function gives
n [z^n] p^{-ks} = n p^{-k} L_n^{(-1)}(k log p), and with E(x) = psi(x) - x and an
integration by parts,

    lambda_n = A(n) + 1 - L_n^{(1)}(log 2) - P_n,
    P_n = int_2^oo (psi(x) - x) L_{n-1}^{(2)}(log x) dx / x^2,

so lambda_n >= 0 is exactly **P_n <= M(n) := A(n) + 1 - L_n^{(1)}(log 2)**. The Euler
product enters only through psi. A proof of RH along this mechanism is a proof of that
inequality for every n.

## 3. Results (measured unless stated)

**The split, zeta and DH, n <= 5000** (`artifacts/split_zeta.json`, `split_dh.json`):

| | zeta | DH |
|---|---|---|
| identity defect lambda - A - T | 8.1e-28 (three evaluators) | 3.1e-27 against the `li_dh_onset` table |
| max over n <= 5000 of abs T(n) | 13.52, at n = 3298 | 19.12, at n = 2799 |
| A(5000) | 15642.1 | 19665.2 |
| T(n) / ((n/2) log n), 100 <= n <= 5000 | in [-0.0032, 0.0075] | in [-0.0112, 0.0093] |
| min lambda_n | 0.0231 at n = 1 | 0.0976 at n = 1 |

A(n) carries lambda_n for both functions; their arithmetic parts are of the same small
size. Two routes for A(n) agree at 30 digits on the twelve spot indices up to 5000
(exactly as printed, except 7.7e-22 at n = 10 for zeta; the test holds them to 1e-20 for
n <= 60), and two routes for T(n) agree to 1e-18 for n <= 16 (tests).

**W_{1/4} = zeta(s+1/4) zeta(s-1/4), n <= 9000** (`artifacts/wa_quarter.json`): lambda_n > 0
for n < 8260 and **lambda_8260 = -122.32**; 215 negative values up to 9000, the least
-87409.5 at n = 8977. The Cauchy route at r = 0.95 and at r = 0.93 agree to 2.6e-48
(relative), and the zero-side route (zeta's first 1000 zeros and the smooth density; it
never evaluates zeta) gives -122.3158 at n = 8260, a difference of 2.5e-3. Grade of the
sign: hardened (two independent float routes). The split of W_{1/4}: T_W(2000) = 41.6,
T_W(5000) = 22.8, then T_W(8258) = -52042 and T_W(8260) = -55949 against A_W(8260) = 55827.
The failure is in the arithmetic part, abruptly.

**The prime side, zeta, x0 = 10^8, n <= 5000** (`artifacts/prime_side.json`, made
2026-10-26):

- The regularized prime sum converges to T(n) for n <= 6: the integrated form is within
  8.1e-4 at X = 10^8 (1.1e-3 at 10^6), and the boundary term improves every n.
- M(n) < 0 for n <= 4, and the measured P_n meets it there (P_1 = -0.884 < M_1 = -0.861).
  For n >= 5, P_n / M(n) lies in [-0.184, 0.454] (largest at n = 8). P_n stays of size 1 to
  10 while M(5000) = 15650.
- **The pointwise route fails at every n.** B(n) = int beta |e^{-u/2} L_{n-1}^{(2)}(u)| du,
  with beta = abs E exactly below 10^8 and Schoenfeld's envelope sqrt(x) log^2 x / (8 pi)
  above, which assumes RH. B(n) > M(n) at every n <= 5000 where M(n) > 0; the least
  ratio is 11.5, the ratio at n = 5000 is 1.57e4, and B(n) / abs(P_n) has median 1.07e7.
  Even an RH-strength pointwise input does not give the inequality: the true P_n is small
  by cancellation of the kernel's oscillation against E, not by the size of E.
- **The mean-square route fails outside [32, 1258].** sqrt(D2 K2) + tail, with the exact
  mean square below 10^8, Cramer's RH mean square beyond (a model) and the Schoenfeld
  envelope past the kernel's turning point, is at most M(n) for n in [32, 1258] (1227
  indices) and above it for n <= 31 and every n >= 1259; at n = 5000 it is 3.05 M(n),
  driven by the tail (3.99e4 against sqrt(D2 K2) = 7.7e3).
- An envelope of de la Vallee Poussin shape x exp(-sqrt(log x / R)), R = 5.573412,
  prefactor 1 (not a theorem's constants), exceeds M(n) at every n <= 200 and grows like
  exp(2n) (2.3e18 at n = 10).

All three bounds are trapezoid integrals on a sampled grid: measured, adequate for the
factor-of-many comparisons they are used for, not for a sign at a margin.

## 4. The distinguishing step and the rivals

The step that uses the Euler product is P_n <= M(n) through psi: the inequality must use
that the log-derivative coefficients are Lambda(m), supported on prime powers, and it must
fail for any function lacking what zeta has.

| rival | hypotheses it meets | result | grade |
|---|---|---|---|
| DH | functional equation, no Euler product, signed coefficients | lambda_n > 0 for n <= 5000 and abs T_DH(n) <= 19.1 there, as small as zeta's; first negative index extrapolated near **n = 328997** (`li_dh_onset`, hunt #128, measured inputs, extrapolated conclusion), **not computed here** | measured (n <= 5000; hardened for n <= 12 in hunt #128) |
| W_{1/4} | scalar Euler product, log-derivative coefficients Lambda(m)(m^a + m^-a) >= 0, exact s -> 1-s functional equation of its completion | lambda_8260 < 0: any step that uses only those hypotheses fails by n = 8260, and the failure sits in T_W | hardened (two routes) |
| Epstein (1,1,6) | not run | not run | none |
| zeta(s - delta) | not run | not run | none |

So: no bound on T(n) or P_n read off n <= 5000 separates zeta from DH (both pass any bound
abs T(n) <= 0.012 (n/2) log n on that range: a shared finite-range lemma, no verdict); and
W_{1/4} shows that the Euler product with nonnegative coefficients and a functional
equation is not enough. What W_{1/4} lacks is that its local roots p^{+-1/4} are not
unitary, the same input `ccm_arithmetic` isolated (its section 4).

## 5. Known obstructions engaged

- **A finite range is a finite height.** One off-line quadruple 1/2 +- delta +- i gamma
  contributes about -2 R^n cos(n psi) to lambda_n with log R ~ delta / ((1/2 + delta)^2 + gamma^2), so
  it first beats the baseline (n/2) log n near the root of
  n log R = log((n/4) log n). That root is 7821 for W_{1/4}'s first quadruple (measured
  onset 8260) and 330025 for DH's off-line pair (extrapolated onset 328997); the test
  pins both. Inferred (a heuristic that ignores the cosine and the other zeros), but it
  says what the record already implies: positivity of lambda_n for n <= N says nothing
  about off-line zeros above a height of order sqrt(N delta / log N), so any check to n = 5000 is a check to
  bounded height, and a uniform-in-n step is the whole content (`docs/08` section 3).
- **The pointwise and mean-square routes are absolute-value routes**, and on the measured
  range both fail even with RH-conditional inputs (section 3), which also makes them
  circular as written. A proof has to exploit the sign structure of E against the
  Laguerre kernel.
- **The zeros route to lambda_n** is structurally nonnegative over any list of on-line
  zeros (`MISSION.md` dead routes); nothing here uses it as evidence for zeta. W_{1/4}'s
  zero-side route is a cross-check of a negative value, not positivity evidence.

## 6. Tests run

`test_li_arithmetic.py`, 15 tests, 21 to 27 s with `-n0`, writing nothing into the tree:
closed forms at n = 1; the two A routes and the two T routes for zeta and DH; a planted
fault (the Euler factor of 2 removed) that the T cross-check must see; the identity against
the hunt #128 tables; the Laguerre generating identity and the elementary piece on [1, 2);
the regularized prime sum against T(n) at X = 10^6; the pointwise route recomputed at
x0 = 10^6, n <= 40; the W_{1/4} split at small n by three routes; the radius rule; the
onset heuristic; and every artifact number this page quotes.

## 7. Disposition (proposed by the builder; the challengers decide)

**Unresolved**, with two sub-routes refuted at their stated parameters: the pointwise
absolute-value bound (at every n <= 5000 where M(n) > 0, with x0 = 10^8 and the
Schoenfeld envelope above it) and the mean-square bound (at n <= 31 and every
1259 <= n <= 5000, with Cramer's mean square as a model above x0). Both refutations are of
the bounds, not of the inequality P_n <= M(n), which holds on the whole measured range.

## 8. Furthest true statement, with its grade

For 1 <= n <= 5000, lambda_n = A(n) + T(n) holds to 8.1e-28 for zeta and 3.1e-27 for DH,
abs T(n) <= 13.6 for zeta and <= 19.2 for DH while A(n) reaches 1.6e4 and 2.0e4, the
prime integral satisfies P_n <= M(n) with P_n / M(n) <= 0.46 for n >= 5, and no bound on
P_n by abs E (pointwise, even granting Schoenfeld's RH envelope) reaches M(n) at any of
those n; W_{1/4}, which has an Euler product, nonnegative log-derivative coefficients and
a functional equation, has lambda_8260 < 0 with the failure in its arithmetic part.
**Grade: measured**, except W_{1/4}'s sign (hardened, two routes) and the split's
derivation (derived, self-reviewed). No novelty search was made: the split is
Bombieri-Lagarias's and Coffey's, and the prime-side Laguerre form is the integrated
version of Bombieri and Lagarias's arithmetic formula; whether the measured failure of the
absolute-value routes is in the literature was not searched.

## 9. Next step

1. A signed bound: write P_n against the explicit formula for E and bound the sum over
   zeros of the Laguerre transform zero by zero; that reads the zeros and so is a
   different information class from the prime-side input (`MISSION.md`, zero-importing).
   The arithmetic alternative is a large-sieve or mean-value bound on
   sum_m Lambda(m) m^{-1/2} e^{i t log m} weighted by the kernel's phase 2 sqrt(n u).
2. Run Epstein (1,1,6) and zeta(s - delta) through the split, to see which hypothesis of
   the inequality each lacks.
3. Compute DH's lambda_n to the predicted onset only if a candidate inequality survives
   to n = 5000 for zeta and its DH analogue does not yet fail there; at today's cost
   (150 s for n = 5000 at r = 0.95, with work digits growing like n log10(1/r)) the run to
   n = 3.3e5 needs its own estimate in `RUNS.md` first.
