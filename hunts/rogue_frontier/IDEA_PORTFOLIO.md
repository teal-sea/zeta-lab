# IDEA_PORTFOLIO - candidate attack surfaces, scored

Scores are the surveying arm's (importance, novelty probability,
tractability, verifiability, computational leverage, each /10;
sat = literature saturation, high is bad). Selection notes and the
chosen portfolio are the coordinator's, at the bottom.

## Davenport-Heilbronn control run against the two-thirds framework's separation step
*from Territory K: systematic sweep of mid-2025 through August 202*
- I=8 N=8 T=8 V=9 C=10 F=3 sat=1 signal: 2-4 days
- The Anthropic 67.25% paper separates on-line from off-line zero contributions via Sylvester inertia of a Hermitian form built from the Weil explicit formula. Davenport-Heilbronn satisfies a functional equation, has real Z, and violates RH, so any honest separation mechanism must behave differently on it. Concretely: build the analogous truncated Hermitian form for the DH function using zeta/epstein.py and zeta/weil.py, compute its inertia signature with Arb-enclosure-checked eigenvalue enclosures at matched truncations, and check whether the rank-trace inequality step produces a (false) on-line proportion bound for DH. First signal (2-4 days): enclosure-checked inertia signatures for zeta vs DH at 3-4 truncation levels. Falsification is cheap in both directions: if DH passes the separation step identically, that is a publishable structural caveat about the new framework; if it fails as it must, the experiment documents exactly which hypothesis (Euler product input) does the work.
- key ref: Anthropic manuscript + arXiv:2006.13771 (Weil positivity archimedean) + lab's docs/09 battery discipline

## Solve the exact variational window for the ξ' inertia functional and try to cross Wu's 0.86957
*from Territory A: proportions of zeros of zeta on/near the critic*
- I=7 N=8 T=8 V=9 C=9 F=8 sat=1 signal: 4-8 hours to the discretized optimum; 2-4 days to enclosure-checked constant
- Remark 7.3 of the Aug 2026 paper computes unconditional simple-on-line proportions for ξ' with only a flat window (0.85838) and a hand-picked quartic window v(s)=1−(7/100)(2s)²−(51/200)(2s)⁴ (0.86864). The ζ case shows the true optimum solves an explicit Euler–Lagrange ODE (v''+2λ²v=0 → Montgomery–Taylor). Project: write down the ξ' analogue of the scale-free functional c_λ(v) (quadratic form with the ξ' prime-side J-term), solve its Euler–Lagrange equation (a second-order ODE with modified constant, likely v''+2μ²v=0 with μ determined by the ξ' density ratio), and compute the resulting constant in closed form with Arb enclosures. Falsifiable first signal in hours: discretize c_λ(v) as a Rayleigh quotient (50–200 Chebyshev modes, mpmath), maximize; if the numerical sup ≤ 0.86864 the quartic was already near-optimal and the project dies cheaply; if it exceeds 0.86957 (Wu's on-line-only record) the unconditional simple-on-line constant for ξ' would exceed the best known on-line constant, a new qualitative statement. Then port the closed form into the lab's Lean arm following the existing Zeta23.XiPrime quartic_stdform pattern.
- key ref: Anthropic 2026 preprint Remark 7.3; github.com/anthropics/zeta-23-lean XiPrime/

## enclosure-checked replication and rate-fitting of the CvS truncated Weil form (attack on the open convergence question)
*from Territory F: spectral and operator approaches to RH (Hilbert*
- I=8 N=7 T=8 V=9 C=9 F=3 sat=2 signal: 1-2 days
- Implement the Connes-van Suijlekom Galerkin matrix (as specified in arXiv:2605.20224, which gives the construction publicly) in the lab's mpmath machinery, cross-check against Groskin's reported values (first-zero error 2e-55 at c=13, N=100; 1.5e-168 at c=67), then do two things Groskin did not: (a) certify smallest-eigenvalue enclosures with the Arb backend (rigor.py) so the eigenvalue signs and magnitudes are enclosure-carrying rather than floating-point; (b) fit the error law err(c, N) over a denser grid of c and both parity sectors, producing a falsifiable conjectured convergence rate for the open question Connes posed in Feb 2026. First signal: reproducing the c=13 error to the stated order within 1-2 days. Cheap falsification: if our independently coded matrix disagrees with Groskin's spectrum beyond precision, one implementation is wrong and the discrepancy is itself publishable; if eigenvector zeros drift from gamma_1 as N grows at fixed c, the observed 'convergence' is a basis artifact.
- key ref: arXiv:2605.20224; Connes-van Suijlekom 2025

## enclosure-checked smallest-eigenvalue window on the truncated Weil quadratic form
*from Territory E: equivalent and near-equivalent criteria for RH *
- I=7 N=7 T=8 V=9 C=9 F=4 sat=2 signal: 2-4 days
- Implement the (2N+1)x(2N+1) Galerkin matrix of the prime-cutoff-c truncated Weil form (arXiv:2605.20224, 2607.02828) inside weil.py, independently re-deriving every entry from the lab's own Guinand-Weil convention (both sides computed independently, per house rule). Compute Arb-enclosed smallest eigenvalues over a (c, N) grid, certify the sign, and fit the archimedean tail order against the July 2026 claim. Simultaneously track the even-sector ground state's Fourier-Mellin zeros against gamma_1..gamma_50 as c grows to put numbers on the open c -> infinity convergence question. First signal (2-4 days): an enclosure-carrying lambda_min(c, N) curve; the project falsifies cheaply if the published tail order or the critical-line ground-state claim contradicts the enclosures, and either outcome (confirmation with enclosure-checked arithmetic, or a located defect in a weeks-old posting) is publishable.
- key ref: arXiv:2607.02828; arXiv:2605.20224; arXiv:2006.13771

## Optimize the window inside the RH-conditional cubic certificate: beat N_d ≥ 0.85082
*from Territory A: proportions of zeros of zeta on/near the critic*
- I=6 N=8 T=8 V=9 C=9 F=7 sat=1 signal: 1-2 days
- §7.5(g) of the Aug 2026 paper proves, under RH, N_d/N ≥ 1/2 + (2m₂−m₃)/18 + (4/9)(19/27) = 0.85082… using the window v(s)=cos(8s/5), for which 2m₂(1,v)−m₃(1,v) = 0.68524…; the weight ψ(m) is LP-optimal but the window is a one-parameter guess. Project: maximize 2m₂(1,v)−m₃(1,v) (sine-kernel Gram second and third moments, explicit double/triple integrals against |v̂|²) over windows v ≥ 0 on [−1/2,1/2] via mpmath quadrature + Chebyshev parametrization, then re-run the LP jointly (window and weight interact through m₂, m₃). Every improvement δ in 2m₂−m₃ lifts the constant by δ/18, and 0.85082 already beats CGdL's SDP 0.8477, so any gain extends the RH-conditional distinct-zeros record. First signal: gradient ascent over 5-10 coefficients; falsified cheaply if cos(8s/5) is a critical point of the functional (check the Euler-Lagrange residual numerically in an afternoon). Interval-certify the final constants with rigor.py (both backends) since the paper interval-certifies m₂, m₃ from closed forms.
- key ref: Anthropic 2026 preprint §7.5(g); Chirre-Gonçalves-de Laat arXiv:1810.08843

## Davenport-Heilbronn control for Zeta Spectral Triples
*from Territory F: spectral and operator approaches to RH (Hilbert*
- I=8 N=8 T=6 V=8 C=9 F=2 sat=1 signal: 3-5 days
- Run the counterexample battery against arXiv:2511.22755: rebuild the Connes-Consani-Moscovici rank-one-perturbed scaling operator with the Davenport-Heilbronn Dirichlet-series coefficients (the lab's epstein.py already provides Z_dh, the functional equation, and the known off-line zero) in place of the zeta Euler factors, and measure whether the finite spectra lock onto DH zeros, including the off-critical ones. Either outcome is a result: if the spectra track DH zeros equally well, the numerical resemblance in 2511.22755 distinguishes nothing about RH (a gate-#3-style negative result nobody has published); if the construction visibly fails for DH (e.g. no real eigenvalue near the off-line zero's height, or spectral defect concentrated there), that is quantitative evidence that the Euler product structure is load-bearing, sharpening the conjecture. First signal: DH-analogue spectrum at one lambda within days. Falsified cheaply if the DH function admits no analogous operator (the construction may require an Euler product, which DH lacks; documenting exactly which step breaks is itself the finding).
- key ref: arXiv:2511.22755; Davenport-Heilbronn via zeta/epstein.py

## Rigorous RH_1(T): enclosure-checked verification that all zeros of xi' up to height T lie on the critical line
*from Territory G: geometry of the Riemann xi function ,  de Bruij*
- I=6 N=8 T=8 V=9 C=9 F=6 sat=2 signal: 1-2 days to a enclosure-checked count at T=10^3; ~2 weeks to T=10^6
- Build on zeta/rigor.py to certify, via Arb ball arithmetic, that all zeros of xi'(s) with |Im s| <= T lie on Re s = 1/2 and are simple, for T ~ 10^6-10^9. Concretely: (a) count zeros of xi' in the rectangle by a enclosure-checked argument-principle integral of xi''/xi' on a box contour (xi' is entire, no pole issues); (b) count sign changes of the real function d/dt Xi(t) = derivative of Hardy-type Xi on the line with proven_sign; (c) equality of the two counts is exactly RH_1(T). No rigorous RH_1(T) computation exists in the literature at any height, and via GORTTW Theorem 1.2 (arXiv:1910.01227) any T immediately yields 'J^{d,n} hyperbolic for all n >= 1 and d <= floor(T)^2', a new unconditional theorem-grade finite statement. First signal (hours): enclosure-checked count agreement on T = 1000. Falsified cheaply if the argument-principle enclosures blow up near Gram-point-like degeneracies (visible in the first box).
- key ref: Griffin-Ono-Rolen-Thorner-Tripp-Wagner, Adv. Math. 397 (2022) 108186, arXiv:1910.01227, Theorem 1.2

## Blindness horizon of the sequential Riesz criterion, measured on Davenport-Heilbronn
*from Territory J: forgotten, abandoned, or obscure RH approaches *
- I=6 N=8 T=8 V=9 C=10 F=2 sat=2 signal: 1-2 days
- Build the DH analogue of the Baez-Duarte coefficients (DH is an explicit linear combination of two Dirichlet L-functions, so 1/f(2j+2) is computable) and measure at what k the off-line zero at s0 ~ 0.808517 + 85.699348i breaks the k^{-3/4} envelope: theory predicts a component ~ k^{-(1-sigma0)/2} = k^{-0.0957} oscillating with frequency (t0/2)/(2pi) in log k. This is the never-published positive control for the entire c_k literature (Wolf 0910.1534 discusses DH but never ran it), and it converts the criterion into a calibrated instrument: 'an off-line zero at (sigma, T) is visible in c_k by k = K(sigma, T)'. Falsifiable cheaply: if the DH c_k sequence does NOT show the predicted k^{-0.0957} growth by the predicted k, the detection model is wrong. Uses zeta/epstein.py directly. First signal: DH c_k for k <= 10^4 showing envelope departure, one day.
- key ref: arXiv:0910.1534 (Wolf); L. Baez-Duarte, sequential Riesz criterion (2005)

## FFT census of large values of structured Dirichlet polynomials at V = N^{3/4}
*from Territory B: zero-density estimates and zero-free regions , *
- I=6 N=7 T=9 V=8 C=10 F=1 sat=3 signal: 4-12 hours for the first exponent measurements at N = 2^16
- Numerically map the true large-values landscape that Guth-Maynard bound: for coefficient choices b_n in {Moebius mu(n), Dirichlet characters, random +/-1, smoothed von Mangoldt} and N up to 2^20+, count 1-separated points t in [0,T] (T = N^{6/5}..N^2) with |sum b_n n^{it}| >= N^{3/4}, and measure the empirical growth exponent against (a) the GM bound, (b) the conjectured optimal LV(sigma) curve from Tao's discussion, and (c) additive energy of the large-value point sets (the lab's statistics/moments machinery applies directly). First signal (hours): measured exponents for random coefficients vs the mean-value prediction. Falsifiable target: the natural conjecture that no coefficient sequence gets within delta of the GM bound at sigma = 3/4 for these N; any structured example approaching it would be a genuinely interesting phenomenon and a guide to where the method is tight.
- key ref: arXiv:2405.20552; terrytao.wordpress.com 2024-07-07 zero-density discussion

## enclosure-checked singular-value decay law for the Alcantara-Bode operator
*from Territory F: spectral and operator approaches to RH (Hilbert*
- I=6 N=7 T=9 V=9 C=9 F=7 sat=2 signal: 1-2 days
- Compute enclosure-carrying (Arb) smallest singular values sigma_min(n) of the n x n finite sections of the operator (Af)(x) = int_0^1 {y/x} f(y) dy on L^2(0,1), for n up to a few hundred in a well-conditioned basis, and fit the decay law. This is the calibration object for every claimed numerical-injectivity argument in the 2021-2025 literature (which uses not enclosure-checked numerics), and no enclosure-checked table exists. Side deliverable for the Lean arm: the Hilbert-Schmidt norm ||A||_HS^2 = int int {y/x}^2 dx dy is an exact constant expressible via zeta values and log(2pi); deriving, pinning numerically, and kernel-checking that closed form is a self-contained formalization at the scale of the lab's prior Lean theorems. First signal: enclosure-checked sigma_min(50) in 1-2 days. Falsification: if sigma_min(n) decays faster than any claimed o(n^{-s}) criterion can tolerate, the numerical-injectivity program in the recent literature is dead on arrival and we can document it.
- key ref: Alcantara-Bode, Integral Equations Operator Theory 17 (1993); researchgate.net/publication/385983954

## Propagate the March-2026 zero-free region (4.896) through Lee's kth-powers tables
*from Territory H: explicit and computer-assisted results ,  RH ve*
- I=6 N=7 T=9 V=9 C=8 F=2 sat=3 signal: 1-3 days
- Lee's Feb 2026 paper (arXiv:2602.14340, k=86 for primes between consecutive kth powers) was finalized three weeks before Bellotti-Trudgian-Yang published the classical zero-free region 1/(4.896 log t) (arXiv:2603.21490), improving on 5.558691. Reimplement Lee's five tables (the Littlewood-form minimal zero-free-region computation plus the explicit-formula inequality) in mpmath, validate against his published k=86/k=70/k>=65 values, then substitute 4.896 and the Bellotti-Wong N(T) bound (0.10076 log T). Falsifiable claim: k drops below 86 for all n. First signal: reproduction of one row of Lee's Table within 24h; the improved k within days. Cheap falsification: if the binding constraint in Lee's optimization is the verification height 3e12 rather than the zero-free constant, the improvement is nil and that is visible from the reproduced table's sensitivity column immediately.
- key ref: arXiv:2602.14340 + arXiv:2603.21490

## Effective interpolation of Goldston-Lee-Schettler-Suriajaya: proportion simple as a function of partial PCC support
*from Territory D: pair correlation and zero statistics ,  Montgom*
- I=7 N=7 T=7 V=8 C=8 F=5 sat=2 signal: 1-2 days for the first point on the curve
- arXiv:2503.15449 shows full PCC implies 100% simple with no rate. Between Montgomery's 2/3 (support [-1,1]) and GLSS's 100% (all supports) there is an uncomputed curve: assume F(α,T) ≤ 1 + ε for 1 ≤ |α| ≤ A and optimize the simple-zero proportion p(A, ε) over admissible test functions on [-A, A]. Project: set up the extremal problem (a one-parameter family of Beurling-Selberg-type problems, SDP-solvable), tabulate p(A, ε), and identify the marginal value of each unit of support. First signal (1-2 days): p(1.1, 0) computed and strictly above 2/3 wait-consistency check against known A→∞ limit 1. Falsifiable: the curve's shape is checkable against the known endpoints; a bug shows immediately as p(1,0) ≠ 2/3. Value: converts a qualitative 2026 theorem into a quantitative target list, and tells the community exactly what partial pair-correlation knowledge buys ,  no such table exists in the literature.
- key ref: arXiv:2503.15449 (Goldston-Lee-Schettler-Suriajaya)

## Re-run the explicit PNT-error pipeline with 2024-25 inputs through Johnston's lossless transfer
*from Territory B: zero-density estimates and zero-free regions , *
- I=7 N=6 T=8 V=9 C=9 F=3 sat=6 signal: 1-2 days to reproduce FKS constants, then immediate signal on swapping inputs
- Fiori-Kadiri-Swidinsky's records (9.22022 x (log x)^{3/2} exp(-0.8476836 sqrt(log x)); 4.9678e-15 x at exp(3000)) predate Bellotti's KV region (48.0718/53.989), her log-free and near-unity explicit densities, Chourasiya-Simonic's explicit Ingham with log^{(7-5sigma)/(2-sigma)}, and Johnston's eps-free transfer omega(x) = min_t {eta(t) log x + log t}. Project: implement eta(t) as the pointwise max over ALL current explicit regions (MTY classical + Bellotti KV + Platt-Trudgian height), numerically minimize omega(x), and recompute |psi(x)-x|/x on a grid x = exp(1000)..exp(10^5), comparing against FKS. First signal (1-2 days): reproduction of the FKS numbers; success = strictly smaller enclosure-checked constants on some x-range, a publishable increment with the lab's mpmath/Arb machinery doing the enclosure-checked minimization. Falsified if the new inputs move nothing anywhere below exp(481958), which would itself sharpen the community's map of which input binds where.
- key ref: arXiv:2411.13791; arXiv:2204.02588; arXiv:2306.10680

## Phase-diagram experiment for negative moments: Gonek vs Forrester-Keating in the contested regime k in (1/2, 1]
*from Territory C: moments of the Riemann zeta function on the cri*
- I=6 N=7 T=8 V=8 C=10 F=1 sat=2 signal: 2-3 days for the k=0.3 calibration run
- Bui-Florea (arXiv:2302.07226) prove Gonek's conjectured asymptotics for Int_T^(2T) |zeta(1/2+alpha+it)|^(-2k) dt when k < 1/2 and alpha >> 1/log T, and the k > 1/2 regime is governed by a conjectural freezing transition (Forrester-Keating) where Gonek's exponent is expected wrong; no systematic numerics exist. Project: using the lab's mpmath Hardy-Z and enclosure-checked enclosures (to lower-bound |zeta| rigorously away from zeros and control the near-zero contributions), compute the negative moment on grids k in {0.3, 0.5, 0.6, 0.75, 1.0} x alpha in [c/log T, 10/log T] at heights T ~ 10^6..10^8, and fit the alpha-exponent. Gonek and Forrester-Keating predict different alpha-scaling exponents for k > 1/2; the measured slope discriminates them. First signal: at k=0.3 the fitted exponent must reproduce the proven Bui-Florea asymptotic (calibration); the k=0.75 slope is then the result. Cheap falsification: if variance across sample windows swamps the exponent difference at reachable heights, that is measurable within days and bounds what any numerics can say.
- key ref: arXiv:2302.07226 (Bui-Florea, Negative moments of the Riemann zeta-function)

## Numerical spectral audit of Suzuki's screw-function operator conjecture
*from Territory E: equivalent and near-equivalent criteria for RH *
- I=7 N=8 T=6 V=7 C=8 F=2 sat=1 signal: 4-7 days
- Implement Suzuki's screw function g_zeta(t) (explicit prime sum plus archimedean part; arXiv:2606.09096, June 2026) and the nonlocal differential operator's self-adjoint realizations on [-a, a]; compute low-lying eigenvalues for a in [2, 30] and measure convergence (or non-convergence) to gamma_1..gamma_30 with rate fits. The conjecture is two months old with zero published numerics; any measured convergence-rate law, or a demonstration that spurious spectrum persists, is new information about a live conjecture by a serious author. First signal (4-7 days): eigenvalues of the discretized operator at a = 5 landing within O(1) of the first few gamma_n (or demonstrably not); cheap falsification of the discretization itself via the lab's weil.py cross-checks (the same g feeds the Weil form both ways).
- key ref: arXiv:2606.09096

## Sharpen the archimedean tail constant in the finite Guinand-Weil budget
*from Territory F: spectral and operator approaches to RH (Hilbert*
- I=6 N=7 T=8 V=9 C=8 F=5 sat=1 signal: hours (dictionary check), 1 week (constant)
- arXiv:2607.02828 proves the tail beyond the Galerkin band is a totally positive Cauchy-Stieltjes increment with budget B_T ~ (2N+1)(2pi/log c) log(T)/(pi^2 T), an order statement. Because the increment is totally positive, a sharp constant (and plausibly a second-order term) should follow from a Chebyshev-system extremal argument over the band-limited window, a finite optimization the lab can do: parametrize the window, compute the exact tail integral in mpmath, optimize coefficients, and compare to B_T. A smaller enclosure-checked budget directly enlarges the certification region [-B_T, 0) where eigenvalues are currently 'undetermined'. Verify the exact dictionary identity <v,Qv> = sum over zeros of g_v first, using weil.py's independently coded two-sided explicit formula on random vectors (an afternoon, and an independent check of a 6-week-old paper). First signal: dictionary identity confirmed/refuted to 30 digits in hours. Falsification: if the optimized window only improves the constant by <10%, the surface is mined and we say so.
- key ref: arXiv:2607.02828

## Tabulate and test the zeta screw function (Krein) from Suzuki 2026
*from Territory F: spectral and operator approaches to RH (Hilbert*
- I=6 N=8 T=7 V=9 C=9 F=3 sat=1 signal: 2-4 days
- arXiv:2606.09096 (June 2026) re-expresses Weil's quadratic form via a continuous screw function g(t) in Krein's sense; the paper is weeks old and no numerical study exists. Implement g(t) with the lab's explicit-formula code (both prime-sum and zero-sum routes, cross-checked as house style requires), tabulate it, and test the operational consequences: positivity of the associated kernel matrices [g(t_i - t_j)] on finite grids (which encodes truncated Weil positivity in a new coordinate), smoothness/monotonicity structure, and where the first violation appears as grids grow if RH-adjacent positivity is pushed past its proven range. Doubles as a fresh face of the same object as projects 1 and 3, so implementations cross-validate. First signal: g(t) on [0,20] to 30 digits agreeing between the two routes, within days; disagreement between routes falsifies our reading of the paper's normalization (and is caught immediately, per lab convention-derivation practice).
- key ref: arXiv:2606.09096

## Re-run the Fiori-Kadiri-Swidinsky psi(x) pipeline with 2025-2026 inputs
*from Territory H: explicit and computer-assisted results ,  RH ve*
- I=8 N=7 T=6 V=9 C=8 F=2 sat=4 signal: 1-2 weeks
- FKS's |psi(x)-x| < 9.22106 x (log x)^{3/2} exp(-0.8476836 sqrt(log x)) is an optimization pipeline whose inputs are all superseded: MTY 5.558691 -> BTY 4.896 (classical), MTY 55.241/48.1588 -> Bellotti 48.0718 (KV), KLN density -> Bellotti log-free (2025) + explicit Ingham (2507.15184), HSW N(T) -> Bellotti-Wong 0.10076. Reimplement the Pintz zero-region-splitting optimization (the paper documents the regions and per-region estimates; ancillary code exists) and re-derive both headline constants. Expected outcome: 0.8476836 rises (better exponent constant) and/or 9.22106 and the 4.47e-15 plateau drop. First signal: reproduction of the published constants from published inputs, ~1 week; the update run is then mechanical. Falsified cheaply if reproduction shows the dominant loss is the density estimate in a range where Bellotti's log-free version is weaker than KLN (checkable per-region). Larger effort than the Lee-table project but higher payoff: these are THE reference psi bounds.
- key ref: arXiv:2204.02588 + arXiv:2603.21490 + arXiv:2405.12545

## Measure the small-q boundary of the function-field CFKRS theorem
*from Territory I: neighboring L-function problems ,  Dirichlet cr*
- I=6 N=7 T=8 V=10 C=9 F=4 sat=2 signal: 2-3 days for q=3,5 moments through genus ~6
- Bergstrom-Diaconu-Petersen-Westerland + Miller-Patzt-Petersen-Randal-Williams prove all CFKRS moments for quadratic L-functions over F_q(t) for 'sufficiently large' odd q, with an ineffective threshold. Compute exact moments (2nd, 4th, 6th, 8th) at q = 3, 5, 7, 9 over all squarefree conductors of degree up to ~14-18 (exact L-polynomials via hyperelliptic point counts; the lab's finite-field machinery is built for this) and compare against the CFKRS polynomial in genus, term by term. First signal within days: either the q=3 fourth moment tracks the CFKRS polynomial (evidence the ineffective threshold is small, worth reporting) or it deviates in a structured way (a measured lower bound on q_0(k), which no one has published). Every number is exact integer arithmetic, so 'hardened' grade is automatic; falsification is impossible to fake because the theorem guarantees agreement for large q.
- key ref: arXiv:2302.07664, arXiv:2402.00354

## Optimal test function for the fixed-b narrow-box pair correlation theorem
*from Territory K: systematic sweep of mid-2025 through August 202*
- I=6 N=7 T=8 V=9 C=8 F=4 sat=3 signal: 3-7 days
- Baluyot-Goldston-Suriajaya-Turnage-Butterbaugh (arXiv:2501.14545) get 2/3 simple + 2/3 on-line only as box width b -> 0; for fixed b the proportion degrades through a Fejér-kernel-based extremal quantity. Project: extract the explicit proportion-as-function-of-b functional from their proof, implement it in mpmath, and optimize over admissible bandlimited test functions (finite cosine-basis LP/SDP, the same machinery as Montgomery-Taylor/Cohn-Elkies problems) to find the kernel maximizing the proportion at each fixed b. First signal (3-7 days): the proportion-vs-b curve for Fejér reproduced, plus any basis direction with positive gradient at fixed b = 0.5. Falsified if the Fejér choice is provably extremal for all b (itself a clean lemma worth recording); improvement of the curve at any fixed b is a concrete publishable delta on a Jan-2025 paper whose authors explicitly did not optimize this.
- key ref: arXiv:2501.14545

## SDP (Cohn-Elkies class) transplant into the unconditional 67.25% framework
*from Territory D: pair correlation and zero statistics ,  Montgom*
- I=9 N=6 T=6 V=9 C=9 F=8 sat=2 signal: 3-6 days to a working LP reproducing the published constant
- The Chirre-Gonçalves-de Laat SDP function class improved the RH-conditional simple-zero constant from 0.6727 to 0.6792 purely by enlarging the test-function class beyond bandlimited functions. The August 2026 unconditional framework (0.6725007037) uses the classical Fejér-type window; this lab's existing prior art there is a Cheer-Goldston gap-census floor (+9.9×10^-6), NOT a function-class enlargement, so the two levers are independent and possibly composable. Project: extract the framework's admissible-function constraint set (which differs from Montgomery's because the pair-correlation input is unconditional/narrow-box-free), formulate the LP/SDP over Hermite expansions, verify the bandlimited restriction reproduces 0.6725007, then release the class. First signal: does the SDP relaxation beat 0.6725007 by more than the gap-census floor's 1e-5? The RH-conditional analogue gained 6.5×10^-3, so a 1e-3-scale gain is plausible if the constraint structure transfers. Falsification: if the unconditional constraints force effective bandlimiting (the enlargement collapses), that is a structural theorem about the framework worth recording. Dual certificates verifiable in Arb; Lean-checkable finite positivity on top of the existing zeta-23-lean infrastructure.
- key ref: arXiv:1810.08843 + Anthropic Aug 2026 preprint (www-cdn.anthropic.com/564f962e60643842f5fcb4a17c9dbc8f608f1c37.pdf)

## Measure the slack in the explicit truncated Riemann-von Mangoldt error (Cully-Hugill-Johnston)
*from Territory H: explicit and computer-assisted results ,  RH ve*
- I=5 N=7 T=9 V=8 C=9 F=1 sat=2 signal: 2-3 days
- The explicit O(x/T) error in arXiv:2402.04272 underlies the kth-powers and short-interval records, but the ratio (actual error)/(bound) has never been mapped. The lab's explicit.py computes psi(x) and the truncated zero-sum directly. Compute the true truncation error on a log-spaced grid x in [1e4, 1e12], T in [1e2, 3e6] using the enclosure-checked zero list, and compare to the CHJ bound with their exact constants. Deliverable: a slack map; slack persistently > 5 in the regime that binds Lee's k=86 computation identifies the specific lemma (the Goldston window estimate vs the log^2 term) worth sharpening, and gives a concrete conjectural improved constant to then prove. First signal: slack values on a 10x10 grid in ~2 days. Falsified if slack is < 2 uniformly (bound is near-tight, no room).
- key ref: arXiv:2402.04272

## enclosure-checked Baez-Duarte c_k to k = 10^11 and the envelope constant
*from Territory J: forgotten, abandoned, or obscure RH approaches *
- I=5 N=7 T=9 V=9 C=9 F=3 sat=3 signal: 4-8 hours to reproduce Wolf's range enclosure-checked; 2-4 days for the k = 10^10 envelope fit
- Implement the Norlund-Rice/saddle-point evaluation of c_k = sum_j (-1)^j binom(k,j)/zeta(2j+2) in ball arithmetic (rigor.py + flint), certify c_k on a log-spaced grid to k = 10^10-10^11 (Wolf/Maslanka stopped at 4*10^8-10^9, float-only, in 2006), and fit the enclosure-checked values against the two-term model c_k ~ Re[A * k^{-3/4} * exp(i (gamma_1/2) log k)] + trivial-zero trend, where A is the explicitly computable constant from rho_1 = 1/2 + 14.134725141734694i and zeta'(rho_1). Falsifiable: the fitted amplitude/phase either matches the predicted A to within enclosure width or it does not; a mismatch means the accepted asymptotic model for the sequential Riesz criterion is wrong. First signal: enclosure-checked c_k at k = 10^6 agreeing with Wolf's float values, one afternoon.
- key ref: arXiv:math/0605485 and arXiv:math/0603713

## Numerically measure tr G̃⁴ against the sine-kernel prediction 13/4: a falsification probe of HL*(4,λ)
*from Territory A: proportions of zeros of zeta on/near the critic*
- I=6 N=7 T=7 V=8 C=10 F=2 sat=1 signal: 2-5 days (matrix sizes d ≈ 500-5000 are cheap; the Λ⋆Λ correlation sums are the long pole)
- The only stated route from 2/3 to 13/18 = 0.7222 inside band-width one is HL*(4,λ): tr G̃⁴ = dℓ₁⁴(13/4 + o(1)), encoding an additive-correlation asymptotic for Λ⋆Λ. The 2026 paper's §8 validates prime-side = zero-side for G̃ itself to 1e-8 at heights 100–2000 but never computes the fourth trace. Project: build G̃ (the lab's Weil-form and explicit-formula machinery does exactly this compression) on windows up to height ~10⁵–10⁶ using committed zero tables plus mpmath zetazero, compute tr G̃⁴/(dℓ₁⁴) as a function of λ ∈ {0.6, 0.8, 0.9, 1.0} and of height, and compare against m₄(λ) computed independently from the sine-kernel Gram moments. Also compute the prime-side prediction directly from Σ(Λ⋆Λ)(m)(Λ⋆Λ)(m+h). First signal: the drift (or convergence) of the ratio to 13/4 at λ=1 over one decade of height, with error bars; a systematic drift falsifies the naive smoothing and would locate exactly which |h| range of the Hardy–Littlewood correlations carries the obstruction. All illustrative; publishes as a measured scorecard, hedged per lab rules.
- key ref: Anthropic 2026 preprint §7.5(f) and §8

## Rigorize the hybrid q-aspect Theorem E: q ≤ T^ϑ with proportion H(1/(1+ϑ))
*from Territory A: proportions of zeros of zeta on/near the critic*
- I=7 N=7 T=6 V=8 C=5 F=6 sat=1 signal: 1-2 weeks to the complete q-dependence audit
- Remark 7.2(i) of the Aug 2026 paper states the Dirichlet Theorem E 'appears to go through uniformly for q ≤ T^ϑ provided X = (qT)^Λ ≤ T^{1−ε}', giving positive proportion H(1/(1+ϑ)) of critical zeros of L(s,χ) for ϑ < √6/3 = 0.8164965…, but explicitly disclaims having checked uniformity of every error term. Project: audit and prove the q-uniform versions of the three load-bearing steps ,  the taper tail bound (Prop 4.2), the Montgomery–Vaughan step (Lemma 5.2 with χ-twisted coefficients), and the Γ'/Γ + log(q·) density terms (ℓ₁,χ) ,  tracking explicit q-dependence in every O(·). Deliverable: either a theorem (first unconditional positive proportion of critical zeros for individual L(s,χ) uniformly in a polynomial hybrid range via a non-Levinson method, directly comparable to Wu 2019's log q = o(log T) restriction) or a named breaking term, which is itself a publishable observation about the method's degree structure. First signal: the q-dependence table of all error terms in §5 ,  about a week of careful bookkeeping against the PDF; numerical spot-checks of the χ-twisted prime side with the lab's mpmath machinery at q ~ 10²-10³, T ~ 10⁴ validate each bound as it is proved.
- key ref: Anthropic 2026 preprint Remark 7.2; Wu 2019 [Wu19]

## Arb-enclosure-checked dual certificates + Lean positivity check for the 1.3208 multiplicity bound
*from Territory D: pair correlation and zero statistics ,  Montgom*
- I=6 N=7 T=7 V=10 C=8 F=10 sat=3 signal: 2-3 days (dependent on recovering/re-solving the SDP coefficients)
- The SDP bounds of Chirre-Gonçalves-de Laat (N*(T) ≤ 1.3208 N(T) on RH, hence 67.92% simple) rest on numerically-found test functions whose feasibility is a finite list of positivity/interpolation conditions. Project: reconstruct the extremal function from the paper (or re-solve the SDP), then (a) verify every feasibility condition with rigor.py ball arithmetic, and (b) formalize the finite-dimensional certificate check in Lean 4, giving the first kernel-checked pair-correlation-window constant. First signal: Arb confirms the certificate with explicit margin (hours once coefficients are in hand). Falsification: if the published rounding does not survive ball arithmetic, that is a defect report with a witness ,  also a result. This is the same certificate-verification pattern as the lab's existing Lean arm and directly extends the zeta-23-lean asset; a natural rung after the 0.6725 formalization.
- key ref: arXiv:1810.08843, Adv. Math. 361 (2020)

## Enclosure-carrying Baez-Duarte distances d_N^2 via exact Vasyunin Gram matrices
*from Territory E: equivalent and near-equivalent criteria for RH *
- I=6 N=7 T=7 V=9 C=9 F=3 sat=4 signal: 3-5 days
- Compute the NBBD Gram matrix exactly via the Vasyunin cotangent-sum formula, solve the least-squares problem with ball arithmetic, and produce the first enclosure-checked values of d_N^2 for N up to ~10^3-10^4 (prior computations are float-grade and stop near N ~ 4000). Deliverables: (a) enclosure-checked d_N^2 log N versus the Burnol/BCF constant 0.0461914179...; (b) the measured finite-N gap between the Bettin-Conrey-Farmer mollifier choice and the true optimum, a number that exists nowhere in the literature; (c) a stress test of Pyvovarov's July 2026 finite-scale formulas at concrete scales. First signal (3-5 days): enclosure-checked d_N^2 at N = 100 agreeing with published floats; falsified/redirected if the linear solve is too ill-conditioned for balls, which is itself a reportable obstruction with a condition-number curve.
- key ref: arXiv:math/0103058; arXiv:1211.5191; arXiv:2607.12084

## Second-order term of the prolate negative spectrum vs N(T)
*from Territory F: spectral and operator approaches to RH (Hilbert*
- I=7 N=6 T=7 V=8 C=8 F=2 sat=3 signal: 3-5 days
- Connes-Moscovici prove the UV counting asymptotics of the negative prolate eigenvalues matches that of squares of zeta zeros (arXiv:2112.05500), i.e. the leading Weyl term. Compute the negative spectrum of the self-adjoint extension on the Sonin space to high precision at several lambda (a 1D singular ODE eigenproblem, ideal for mpmath shooting plus Arb verification of sign conditions) and measure the DEFECT between the eigenvalue counting function and N(sqrt(E)) = (sqrt(E)/2pi)log(...) + 7/8 + S: does the second-order (constant, oscillating S(T)-like) structure appear, and with what lambda-dependence? A measured second-order agreement law would be new public data sharpening what the theorem leaves open; a measured disagreement bounds how much of the zero data the prolate operator actually carries. First signal: first 30 negative eigenvalues at one lambda vs gamma_n^2, within days; the paper's own figures give an immediate sanity anchor.
- key ref: arXiv:2112.05500 / PNAS 119 (2022) e2123174119

## Modern mollifier transplant into Conrey's 1983 xi^(m) framework
*from Territory G: geometry of the Riemann xi function ,  de Bruij*
- I=7 N=7 T=6 V=8 C=7 F=2 sat=3 signal: 3-5 days for the general-phi functional and first optimization
- Conrey's beta_1 > 0.7869 (simple zeros of xi' on the line) and alpha_1 >= 0.8137 use Levinson's original mollifier phi(x) = 1-x and one free parameter R, untouched since 1983. Step 1 (numerical, this lab): re-derive Conrey's functional F_m(R) for general polynomial phi (his paper reduces to the same Q_m analysis with phi arbitrary), then optimize phi's coefficients and R as a finite-dimensional quadratic-form problem in mpmath; this mirrors the lab's prior gap-census transplant methodology. Step 2 (analytic): verify the mean-value theorem tolerates the optimized phi (it does for Levinson-Conrey classes) and longer theta via Conrey 1989 / PRZZ technology. First signal (days): the numerical optimum for beta_1 exceeds 0.80 with phi of degree <= 4; if optimization of phi gains < 0.005, the project dies cheaply. Distinct from the lab's prior critical-line-proportion project (different theorem, different functional).
- key ref: B. Conrey, J. Number Theory 17 (1983) 71-75 (verified via https://aimath.org/~kaur/publications/4.pdf)

## Numerically optimized test function for the Buthe-Johnston partial-RH transfer
*from Territory H: explicit and computer-assisted results ,  RH ve*
- I=7 N=6 T=7 V=8 C=9 F=2 sat=3 signal: 3-7 days
- Johnston's condition (9.06/log log x) sqrt(x/log x) <= T0 for Schoenfeld-type bounds uses Logan's extremal band-limited functions, which are extremal for a tail criterion, not the actual composite objective in the Weil-Barner explicit formula. Discretize the space of band-limited even test functions (say 50-200 coefficients against a Fourier basis with support constraint), and solve the resulting linear/semidefinite program minimizing the constant in Johnston's Theorem 1.4 shape, evaluating both sides with the lab's weil.py explicit-formula machinery against the real zero database. Falsifiable claim: a kernel achieving constant < 9.06 (equivalently, extending the unconditional Schoenfeld range past 1.101e26 with T0=3e12 fixed). First signal: reproduce Johnston's 9.06 from his stated kernel, then show the LP finds any admissible kernel beating it on a coarse grid. Falsified cheaply if the LP optimum equals the Logan value to 3 digits (meaning Logan is near-extremal for the composite objective too).
- key ref: arXiv:2109.02249 (Johnston); arXiv:1410.7015 (Buthe)

## Enclosure-enclosure-checked Skewes crossover via Lehman's method with Revers's error terms
*from Territory H: explicit and computer-assisted results ,  RH ve*
- I=7 N=7 T=6 V=9 C=10 F=3 sat=4 signal: 1-2 weeks
- Every published localization of the first pi(x) > li(x) crossover (Saouter-Demichel interval [1.39792136e316, 1.39847567e316]; Revers 2025 improved Lehman error terms) rests on high-precision floating-point sums over zeta zeros. No ball-arithmetic-enclosure-checked version exists. Implement Lehman's integral with the lab's rigor.py (Arb backend) over the first ~2e7 zeros (obtainable from LMFDB/Odlyzko tables via moments.py's ingestion path), carrying Revers's explicit error terms as interval quantities. Deliverable: a hardened (enclosure-carrying) proof that pi(x) > li(x) somewhere in an explicit interval near 1.398e316, possibly narrower than Saouter-Demichel. First signal: enclosure of the Lehman integral at one test point agreeing with published float values, ~1 week. Falsified/blocked cheaply if the required zero precision exceeds the available table precision (checkable on day one by interval-width propagation analysis).
- key ref: Saouter-Demichel IJNT 2010, doi 10.1142/S1793042110003125; Revers J. Number Theory 2025

## q-aspect transplant of the August 2026 two-thirds framework into Sono's 61.07%
*from Territory I: neighboring L-function problems ,  Dirichlet cr*
- I=7 N=6 T=7 V=8 C=9 F=2 sat=4 signal: 1-2 days to reproduce Sono's 0.6107 functional numerically; ~1 week to a re-optimized candidate constant
- Take the kernel/mollifier combination that produced the 0.67250 zeta critical-line constant (the two combined papers behind the Aug 2026 'more than two thirds' result) and re-run Sono's conductor-averaged Levinson optimization (arXiv:2105.07422: Feng mollifier + Conrey-Iwaniec-Soundararajan asymptotic large sieve) with that combination. Concretely: write the q-aspect kappa functional, verify it reproduces 0.6107 with Sono's published coefficient choices (first falsifiable signal, ~1-2 days in mpmath), then substitute the new framework's mollifier pieces and numerically re-optimize coefficients subject to the CIS length constraint. Success = any enclosure-checked value > 0.6107; failure mode is cheap and visible (optimum lands at or below Sono's). Distinct from the lab's prior zeta-side gap-census transplant: this is the q-aspect family, a different mean-value input, and an unwritten analogue.
- key ref: arXiv:2105.07422 (Sono) + the Aug 2026 zeta framework papers

## Two-moment non-vanishing scheme from the new mollified fourth moment
*from Territory I: neighboring L-function problems ,  Dirichlet cr*
- I=7 N=6 T=7 V=9 C=8 F=1 sat=3 signal: 3-5 days: write the proportion functional with both moment inputs and optimize numerically
- Gao-Wu-Zhao (arXiv:2509.24690) provide a mollified fourth moment of length q^(1/22) with power saving; no non-vanishing consequence has been published from it. Set up the constrained optimization: given mollified second moment (length q^theta, theta per Qin-Wu / Khan-Milicevic-Ngo) and mollified fourth moment (length q^(1/22)), maximize the guaranteed proportion of chi with L(1/2,chi) != 0 over moment-mixing inequalities (Cauchy-Schwarz on the second alone vs Holder mixtures using the fourth to control the exceptional set). This is a finite-dimensional numerical optimization the lab can run exactly. First signal: does ANY mixture beat 7/19 (general q) or 5/13 (prime q)? A negative answer with the optimum located is itself a clean result about the 1/22 length being too short, and quantifies the length needed to matter.
- key ref: arXiv:2509.24690 + arXiv:2504.11916

## Stress-test the July 2026 truncated-Weil-form tail bounds, with a DH failure curve
*from Territory J: forgotten, abandoned, or obscure RH approaches *
- I=7 N=7 T=6 V=8 C=9 F=4 sat=1 signal: 2-3 days
- Independently reimplement the finite Guinand-Weil dictionary of arXiv:2607.02828 (prime cutoff c, band N, worked example c = 100, N = 200, T = 800) on the lab's weil.py, verify the claimed budget formula B_T ~ (2N+1) rho log T / (pi^2 T) with rho = 2pi/log c against enclosure-checked explicit-formula evaluations, and then run the same truncation on Davenport-Heilbronn, where the truncated form must go indefinite at finite (c, N): measure the (c, N) frontier at which the off-line zero becomes spectrally visible. The paper is six weeks old with zero independent verification; either confirming or breaking its tail-order claim is immediate value, and the DH indefiniteness frontier is a new calibration curve for the entire finite-Weil-positivity program (Yoshida 1990 through Connes-Consani-Moscovici). First signal: reproduction or contradiction of the paper's 512-zero check, 2-3 days.
- key ref: arXiv:2607.02828 (Groskin, 2026); arXiv:2607.24830

## enclosure-checked tail-order test for the truncated Weil quadratic form
*from Territory K: systematic sweep of mid-2025 through August 202*
- I=6 N=7 T=7 V=9 C=10 F=2 sat=2 signal: 3-5 days
- arXiv:2607.02828 (July 2026) claims a specific archimedean tail order for the truncated Weil quadratic form, and arXiv:2605.20224 uses float spectra of the truncated form to approximate zeros. The lab's weil.py already computes W(h) with truncation-tail accounting and has Arb enclosures. Project: compute enclosure-checked enclosures of the minimal eigenvalue lambda_min(Lambda_cutoff) of the truncated Weil Gram matrix for a geometric ladder of cutoffs, fit the decay exponent with rigorous error bars, and compare against the claimed tail order and the Connes-van Suijlekom UV/IR prediction. First signal (3-5 days): enclosure-checked lambda_min at 5 cutoffs with an exponent fit. Falsification: the fitted exponent's enclosure-checked interval excludes the claimed order, which would be a concrete numerical correction to a July 2026 preprint; agreement produces the first enclosure-carrying confirmation of the tail law.
- key ref: arXiv:2607.02828, arXiv:2605.20224

## Beat 34.4: numerical re-optimization of the Durkan-Page two-piece amplifier for the unconditional sixth-moment lower bound
*from Territory C: moments of the Riemann zeta function on the cri*
- I=6 N=6 T=8 V=9 C=9 F=2 sat=2 signal: 2-4 days to reproduce the functional; 1-2 weeks to a verdict on improvement
- arXiv:2606.27323 (June 2026) proves M_3(T) >= (34.4+o(1)) c_3 T (log T)^9 unconditionally, where 42 is the conjectured constant. The 34.4 is the value of an explicit variational functional over two-piece amplifier profiles, optimized by the authors within a restricted family, with piece lengths capped by the BCR twisted second moment (T^(17/33)) and the BBLR twisted fourth moment (T^(1/4)). Project: implement their functional in mpmath/numpy, reproduce 34.4, then optimize over (a) a wider profile class (discretized free functions on [0,1] rather than their parametric family), (b) the length split between the two pieces, and (c) the exponent split r between amplifier pieces. First signal: reproduction of 34.4 to three digits, then any admissible profile scoring > 34.4. Falsification is immediate: if the optimizer converges to their reported optimum from many starts, the family is already extremal and the project ends in days with a negative result worth recording.
- key ref: arXiv:2606.27323 (Durkan-Page, Amplified moments of the Riemann zeta function)

## Degree escalation of Inoue's test function in the resonance-correlation method
*from Territory D: pair correlation and zero statistics ,  Montgom*
- I=6 N=6 T=8 V=9 C=9 F=4 sat=3 signal: 2-4 days (1-2 days to reproduce the published optimum)
- Inoue (arXiv:2604.05733, April 2026) proves μ < 0.50895 on RH using the explicitly-flagged linear ansatz f(x) = 1 - 0.7x and notes higher-degree polynomials could improve the constant, with a rigorous method floor at 0.508. Project: reimplement the final optimization (resonator coefficients, approximator length X, shift h, and f) in mpmath/numpy, reproduce 0.50895, then optimize f over degree 2-6 polynomials and jointly re-tune the other parameters. First signal (day 1-2): reproduction of 0.50895 from the paper's parameter values; then whether degree-2 f moves the fourth decimal. Falsification: if the joint optimizer returns the linear f as a local-and-global optimum within the admissible class, the surface is closed and that itself is a publishable remark. Deliverable if positive: μ < 0.5088-0.5085 with a certificate; every step is a finite-dimensional inequality checkable in Arb.
- key ref: arXiv:2604.05733 (Inoue 2026)

## Global PF_4 status of the de Bruijn-Newman kernel: enclosure-checked minor atlas
*from Territory G: geometry of the Riemann xi function ,  de Bruij*
- I=4 N=8 T=9 V=10 C=10 F=8 sat=1 signal: hours (reproduce the enclosure-checked 5x5 minor), 2-3 days for the D_4 atlas
- Michalowski (arXiv:2602.20313, Feb 2026) proved K(u) = Phi(|u|) is not PF_5 via one enclosure-checked negative 5x5 Toeplitz minor at (u_0,h) = (0.01,0.05), withdrew his v1 asymptotic-threshold claims as unsound, and left global PF_4 open. Project: reproduce his 5x5 enclosure with zeta-lab's Phi + Arb (independent check of a 6-month-old result), then run a enclosure-checked scan of 4x4 Toeplitz minors D_4(u_0,h) over a log-spaced grid u_0 in [10^-4, 10], h in [10^-4, 1]. Outcome A: a enclosure-checked negative D_4 kills PF_4 (a publishable finite theorem, one determinant). Outcome B: an all-positive atlas plus a correct proof of the tail asymptotics (fixing what v1 botched) establishes the threshold phenomenon. First signal (hours): reproduction of the [-1.8472496e-9, -1.8472225e-9] enclosure. Falsification: if D_4 is uniformly and robustly positive with margins growing at the grid edges, Outcome A is dead within a day and the project pivots to B or stops.
- key ref: W. Michalowski, arXiv:2602.20313v2 (2026)

## Optimize the month-old 1/9 for PGL(3) x Dirichlet twists
*from Territory I: neighboring L-function problems ,  Dirichlet cr*
- I=6 N=8 T=6 V=8 C=9 F=1 sat=1 signal: 2-4 days to reconstruct and validate the kappa functional from the paper
- arXiv:2607.00282 (Conrey-Kwan-Lin-Turnage-Butterbaugh, July 2026) proves >= 1/9 of zeros of L(s, Pi_0 x chi) on the critical line with a first-generation Levinson setup. The constant is certainly not optimized: apply Feng-type multi-piece mollifiers and numerical shift/coefficient optimization within their proven mean-square range (T in [Q^eps, Q^(1/3-eps)], error O(Q^(7/4+eps))). First signal: implement their kappa functional in mpmath, confirm it yields 1/9 with their choices, then re-optimize; any improvement is immediately checkable by quadrature. Falsified cheaply if the functional is already at its optimum under their length constraint (also a publishable observation). Because the paper is one month old, the surface is unmined by construction.
- key ref: arXiv:2607.00282

## Explicit-Guth-Maynard crossover audit: when would 30/13 ever beat explicit Ingham?
*from Territory B: zero-density estimates and zero-free regions , *
- I=7 N=8 T=5 V=7 C=6 F=2 sat=2 signal: 3-5 days for a loss ledger of the main large-values proposition plus first crossover estimate
- Nobody has produced an explicit version of Guth-Maynard (verified by search, Aug 2026). Before anyone attempts one, quantify whether it can matter: inventory every T^{o(1)} loss in the published Annals proof (divisor-bound losses, dyadic decompositions, epsilon-losses in the additive-energy dichotomy), assign each a concrete explicit cost function, and compute the height T* beyond which an explicitized 30/13 (or 15/(3+5sigma)) bound would beat Kadiri-Lumley-Ng / Chourasiya-Simonic explicit Ingham bounds. First signal (days): a loss ledger for one core proposition with a first crude T* estimate. Either outcome publishes: T* < exp(10^4) means explicitization is worth a campaign; T* astronomically large is a citable negative delimiting the explicit frontier. Falsified cheaply if a single unavoidable log-power loss already forces T* beyond all application ranges.
- key ref: arXiv:2405.20552 (Annals of Math. 203 (2026) 623-675)

## Kernel-check the Hardy-Littlewood second moment: Int_0^T |zeta(1/2+it)|^2 dt ~ T log T in Lean 4 / Mathlib
*from Territory C: moments of the Riemann zeta function on the cri*
- I=7 N=8 T=5 V=10 C=3 F=10 sat=1 signal: 1-2 weeks to the mean-value-theorem lemma compiling
- No critical-line mean-value theorem for zeta exists in any proof assistant. The 1918 Hardy-Littlewood asymptotic is the entry point, and its modern proof needs exactly one reusable analytic lemma absent from Mathlib: the Montgomery-Vaughan mean value theorem for Dirichlet polynomials, Int_0^T |sum a_n n^(-it)|^2 dt = sum |a_n|^2 (T + O(n)), or even the weaker classical version with T + O(N log N), which suffices for the leading asymptotic. Mathlib already has zeta's analytic continuation and functional equation. Project: formalize (1) the mean value theorem for Dirichlet polynomials (self-contained, Hilbert-inequality flavor), (2) an approximate-functional-equation-free proof of the second moment via the approximation zeta(1/2+it) = sum_{n<=t} n^(-1/2-it) + O(t^(-1/2)). Both steps are elementary analysis, no automorphic input. First signal: a sorry-free Lean statement and proof of the Dirichlet-polynomial mean value theorem within 1-2 weeks; that lemma alone is independently valuable Mathlib material. Falsification: none needed, this is formalization; the risk is scope, bounded by the two-lemma decomposition.
- key ref: Hardy-Littlewood 1918; Montgomery-Vaughan, 'Hilbert's inequality', J. London Math. Soc. 8 (1974); Mathlib's Mathlib.NumberTheory.LSeries / ZetaFunction

## Negative control for Matiyasevich's Hankel eigenvalue conjectures
*from Territory J: forgotten, abandoned, or obscure RH approaches *
- I=5 N=8 T=7 V=8 C=9 F=1 sat=1 signal: 1-2 days for replication; 1 week for the DH control
- Reproduce Matiyasevich's almost-triangular Hankel matrix construction (entries from zeta Taylor coefficients) with multiprecision Lanczos in flint at matrix sizes ~10x his 2014-2017 runs, then run the IDENTICAL pipeline on the Davenport-Heilbronn function via the lab's battery. Two outcomes, both informative: if DH reproduces the same eigenvalue patterns, Matiyasevich's stronger-than-RH conjectures distinguish nothing (a refutation-with-witness of a published conjecture family, closing a route); if DH breaks the patterns, the conjectures gain their first real evidence and an explicit discriminating statistic. Nobody has independently replicated these computations at all. First signal: replication of his published eigenvalue pictures at his sizes, 1-2 days.
- key ref: Proc. Steklov Inst. Math. 296 (2017), Matiyasevich, Riemann's hypothesis in terms of the eigenvalues of special Hankel matrices

## Formalize Montgomery's 2/3-simple-zeros theorem in Lean via the Goldston-Suriajaya streamlined route
*from Territory K: systematic sweep of mid-2025 through August 202*
- I=7 N=8 T=5 V=10 C=4 F=10 sat=1 signal: 3-5 days to the dependency map and first sorry-free lemma
- arXiv:2603.28104 is a deliberately minimal 7-page path to 'under RH (or the narrow-box hypothesis), at least 2/3 of zeta zeros are simple', built from the explicit formula plus Fejér-kernel positivity. No pair-correlation result is formalized anywhere, and PNT+/Mathlib now carries the zeta infrastructure (Wiener-Ikehara PNT, L-series API) that makes the prerequisites finite. Project: formal statement + the Fejér positivity lemma + the counting corollary, with the explicit-formula input either proved or isolated as the one named assumption. First signal (3-5 days): a sorry-free Lean proof of the extremal Fejér inequality and a dependency map showing exactly which explicit-formula lemma Mathlib lacks; that map is valuable even if the full theorem stalls. Falsified/blocked-cheaply if the Guinand-Weil explicit formula gap is deeper than one lemma, which the dependency map reveals immediately.
- key ref: arXiv:2603.28104 + PNT+ repository

## enclosure-checked finite-T pair correlation histogram with Bogomolny-Keating correction test
*from Territory D: pair correlation and zero statistics ,  Montgom*
- I=5 N=6 T=9 V=9 C=10 F=2 sat=4 signal: 1-2 days
- GUE agreement for zeta zeros is universally cited but no published pair-correlation histogram at large height carries enclosure-checked error bars (zero locations AND binning both enclosure-tracked). Project: using the lab's Odlyzko-table ingestion (zeta.moments) plus rigor.py enclosures for zeros in a fresh window (e.g. 10^4 zeros near T = 10^8, computed independently rather than ingested), produce a ball-arithmetic-enclosure-checked R_2 histogram and test the finite-T lower-order term predicted by Montgomery's F (the T^{-2α} log T diagonal term) and the Bogomolny-Keating prime corrections, with rigorous rejection thresholds. First signal (1-2 days): enclosure-checked histogram over 10^3 zeros with enclosure widths small enough to distinguish GUE from GUE+correction at 2σ. Falsification target: a specific plausible conjecture ,  that the leading finite-T correction to R_2 at height T has the BK prime-sum form with coefficient 1 ,  either passes with enclosure-checked error bars (a citable numerical result) or fails, which would be genuinely important. Entirely inside existing lab machinery.
- key ref: arXiv:2004.09765 (Platt-Trudgian); Odlyzko datasets; Bogomolny-Keating 1996

## Numerical divergence map for the one-shift ratios conjecture outside Cech's proved range
*from Territory I: neighboring L-function problems ,  Dirichlet cr*
- I=5 N=6 T=9 V=8 C=9 F=1 sat=3 signal: 2-3 days for the d <= 10^6 grid
- Cech (arXiv:2110.04409) proves the one-shift ratios conjecture for real Dirichlet characters under GRH only for shifts in an explicit range. Compute the family ratio average sum_d L(1/2+alpha, chi_8d)/L(1/2+gamma, chi_8d) over d <= 10^7 with mpmath/numpy for a grid of (alpha, gamma) spanning proved and unproved regions, against the CFZ prediction including its lower-order terms. First signal in days: a heat map of |computed - predicted| * normalization across the shift plane. Interesting outcomes are symmetric: either the prediction visibly holds far outside the proved range (sharpens the conjecture's plausible domain and locates where MDS continuation should aim) or an anomaly appears near the natural boundary of the MDS continuation (a genuinely new observation about where the recipe's error terms concentrate). Cheap falsification: the computation itself is the test; ball-arithmetic spot checks harden any anomaly before it is claimed.
- key ref: arXiv:2110.04409

## First enclosure-checked Speiser verification: zeta' nonvanishing in 0 < sigma < 1/2 up to t = 10^4
*from Territory J: forgotten, abandoned, or obscure RH approaches *
- I=5 N=6 T=9 V=10 C=10 F=6 sat=2 signal: 3-6 hours for t <= 100; 1-2 weeks for t <= 10^4
- Run a ball-arithmetic argument-principle sweep (rigor.py, flint acb_dirichlet derivatives) proving zeta'(s) != 0 on 0 < Re s < 1/2, 0 < Im s <= 10^4, with the safe-failure discipline the lab already enforces (undecided rectangles named, never rounded up). Every existing Speiser check is float-grade; this would be the first enclosure-carrying verification of the Speiser side of RH for a nontrivial height, a clean 'hardened' rung result. Companion run on DH exhibits the enclosure-checked failure signature (zeta_DH' zeros left of the line paired with off-line zeros). Falsification is intrinsic: any rectangle where the winding number refuses to certify is either a real zeta' zero (enormous) or a precision bug (the ladder's first inference). First signal: enclosure-checked empty rectangles for t <= 100, hours.
- key ref: Speiser, Math. Ann. 110 (1935); arXiv:1904.03123 for the float-grade state of the art

## enclosure-checked interval-arithmetic audit of the Harman-sieve integrals behind theta = 0.52
*from Territory B: zero-density estimates and zero-free regions , *
- I=6 N=7 T=6 V=9 C=9 F=3 sat=2 signal: 2-4 days for a enclosure-checked enclosure of the dominant Buchstab integral at theta = 0.525
- Runbo Li's preprint (arXiv:2308.04458 v8) claims primes in [x - x^{0.52}, x], refining Baker-Harman-Pintz 0.525, resting on C++ numerical evaluation of high-dimensional sieve integrals at theta = 0.520..0.525. Independently re-evaluate the published decomposition integrals with rigorous enclosures (Arb), producing either a enclosure-checked confirmation that the sieve lower bound is positive at theta = 0.52 or a located failure. First signal (days): enclosure of the single dominant two-dimensional Buchstab integral at theta = 0.525 (the BHP-anchored sanity case), then theta = 0.52. This is exactly the lab's enclosure-checked-numerics niche; either outcome (confirmation or refutation of an uncredentialed but widely-watched preprint) is valuable, and a refutation-with-witness is a result by the lab's own rules.
- key ref: arXiv:2308.04458

## TTY-style systematic LP pass on the q-aspect (Dirichlet L) zero-density inventory
*from Territory B: zero-density estimates and zero-free regions , *
- I=6 N=7 T=6 V=9 C=8 F=2 sat=2 signal: 3-5 days to catalogue q-aspect LV inputs and reproduce 12/5 and 7/3 as LP outputs
- Chen-Gupta-Li (arXiv:2507.08296, revised July 2026) transplanted Guth-Maynard to get exponent 7/3 for Dirichlet L-functions, but no one has run the Tao-Trudgian-Yang systematic optimization over the q-aspect large-values inventory (character large sieve, Montgomery, Huxley, Jutila q-analogues, plus the new GCD-twist estimates). Project: build the q-aspect analogue of the zero-density LP, catalogue the known LV inputs with exact exponents, and search for piecewise improvements between 7/3 and the t-aspect frontier 30/13, plus sigma-dependent refinements like the 15/(3+5sigma) form. First signal (days): reproduction of 12/5 (Huxley) and 7/3 (CGL) as LP outputs from catalogued inputs; success = any exact rational improvement on a sigma-subinterval. Surface is 13 months old and essentially unmined; every output is an exactly checkable rational.
- key ref: arXiv:2507.08296; arXiv:2501.16779

## Lean formalization of the Bombieri-Lagarias positivity lemma (abstract half of Li's criterion)
*from Territory E: equivalent and near-equivalent criteria for RH *
- I=6 N=7 T=6 V=10 C=2 F=9 sat=3 signal: 2-3 days for skeleton; 2-4 weeks for full proof
- Formalize in Lean 4 + Mathlib the Bombieri-Lagarias multiset lemma: for a multiset R of complex rho != 0,1 with sum (1+|rho|)^{-1-epsilon} convergent and closed under rho -> 1-rho-bar symmetry, all rho satisfy Re(rho) <= 1/2 iff sum_rho Re(1 - (1-1/rho)^{-n}) >= 0 for all n >= 1 (statement to be transcribed exactly from J. Number Theory 77 (1999) before starting). This is elementary complex analysis (Mobius map |1-1/rho| vs 1 dichotomy plus a convergence argument), needs no zeta-specific input, and delivers the kernel-checked abstract engine behind Li's criterion, slotting beside the lab's kernel-checked Hardy-Ramanujan and Mertens. First signal (2-3 days): the statement plus the easy direction compile sorry-free; falsified as a project if the convergence bookkeeping needs Hadamard-product machinery absent from Mathlib, which is discoverable within the first week.
- key ref: Bombieri-Lagarias, J. Number Theory 77 (1999) 274-287

## Finite truncations of Yakaboylu's intertwiner W, with a Davenport-Heilbronn discriminating test
*from Territory F: spectral and operator approaches to RH (Hilbert*
- I=6 N=7 T=6 V=8 C=8 F=2 sat=1 signal: about 1 week
- The load-bearing open claim in arXiv:2408.15135 is strict positivity of the intertwiner W (proven only >= 0). Compute finite matrix truncations of W in a Mellin basis, track lambda_min(W_n) vs n; then build the analogous intertwiner for the Davenport-Heilbronn function, where strict positivity MUST fail (DH has off-line zeros). If our numerics detect a clear negative/null direction in the DH case and none for zeta at comparable truncation, the construction has measurable discriminating power (not previously demonstrated); if the two cases look identical, that is a quantitative refutation of the approach's usefulness and worth recording. First signal: lambda_min(W_n) curve for zeta at n <= 100 within a week. Cheap falsification: the DH analogue may be ill-defined without an Euler product; identifying the exact failing step is the fallback result.
- key ref: arXiv:2408.15135

## Feed Revers's Feb-2026 critical-line bound into the Bellotti-Wong N(T) optimization
*from Territory H: explicit and computer-assisted results ,  RH ve*
- I=6 N=6 T=7 V=9 C=8 F=4 sat=4 signal: 3-7 days
- Bellotti-Wong (arXiv:2412.15470) obtain |N(T) - (T/2pi)log(T/2pi e)| <= 0.10076 log T + ... explicitly from subconvexity bounds on sigma_k-lines; their improvement over Hasanalizade-Shen-Wong came precisely from better subconvexity inputs. Revers (arXiv:2602.05614, Feb 2026) improved the explicit van der Corput critical-line estimate after their v2. Extract Bellotti-Wong's optimization (choice of sigma_k lines + convexity interpolation, documented in their appendix), reimplement in mpmath, verify 0.10076, then substitute Revers's constants and re-optimize the sigma_k placement. Any improvement tightens Turing's method globally. First signal: reproduction of 0.10076 within days. Falsified cheaply if the binding term in their optimization is the 1-line or 0-line bound rather than the critical-line one (readable off the reproduced optimization's active constraints).
- key ref: arXiv:2412.15470 + arXiv:2602.05614

## Kernel-checked witness that the Chowla analogue fails over function fields
*from Territory I: neighboring L-function problems ,  Dirichlet cr*
- I=6 N=7 T=6 V=10 C=8 F=9 sat=2 signal: hours to find the numerical witness; ~1 day to assess Mathlib expressibility
- Wanlin Li (arXiv:1801.02873) proves infinitely many quadratic Dirichlet L-functions over F_q(t) vanish at s=1/2. Because L(s,chi) is a polynomial in q^(-s) with integer coefficients, central vanishing of one explicit character is decidable integer arithmetic. Project: (1) use finitefield.py-style point counting to locate the smallest explicit witness (a squarefree D in F_q[t] with L(1/2, chi_D)=0), hours of compute; (2) formalize in Lean 4 + Mathlib the statement 'there exists a quadratic Dirichlet character over F_q(t) whose L-function vanishes at the central point', by exhaustive point-count verification of the witness's L-polynomial. This would be, to our knowledge after search, the first kernel-checked central-vanishing witness in any L-function family, and it is a theorem about the RH-is-a-theorem world contrasting sharply with the Chowla conjecture over Q. Falsified/blocked cheaply if Mathlib's finite-field curve infrastructure cannot express the L-polynomial (probe this in day 1).
- key ref: arXiv:1801.02873

## Rerun the Polymath15 barrier at height 3*10^12: push Lambda <= 0.2 down
*from Territory K: systematic sweep of mid-2025 through August 202*
- I=7 N=6 T=6 V=10 C=10 F=2 sat=4 signal: 2 days for the paper-scaling feasibility check; 1-2 weeks for a enclosure-checked barrier segment
- Polymath15's Lambda <= 0.2 (arXiv:1904.12438) was gated by the 2019 RH-verification height (~3*10^10 used in their conditional step) and the cost of the barrier computation; the paper itself says more compute yields more. Platt-Trudgian's 3*10^12 (arXiv:2004.09765) has been available since 2020 and nobody has republished the barrier. Project: using heatflow.py + rigor.py, recompute the effective H_t approximation error bounds at t ~ 0.15 and run an Arb-enclosure-checked barrier at the x-range that the 3*10^12 height now licenses. First signal (1-2 weeks): a feasibility table (barrier location, mesh count, enclosure-checked margin) showing whether t = 0.15 closes; the Polymath15 write-up's own scaling estimates make this checkable on paper in days before any big run. Falsified cheaply if the error-bound recomputation shows the needed x exceeds what 3*10^12 supports. Risk: someone may have done this quietly; a 30-minute literature pass on citations of 1904.12438 is the first gate.
- key ref: arXiv:1904.12438 + arXiv:2004.09765

## enclosure-checked explicit constants C(k) in Harper's RH-conditional bound at k=2,3,4
*from Territory C: moments of the Riemann zeta function on the cri*
- I=5 N=7 T=7 V=10 C=9 F=5 sat=2 signal: 1 week to an not enclosure-checked C(2); 2-3 weeks to enclosure-checked values
- Tingyu Tao (arXiv:2407.20023) optimized the implicit constant in Harper's bound Int |zeta|^(2k) <= C(k) T (log T)^(k^2) under RH, but only under restricted conditions and without enclosure-checked arithmetic. Harper's proof reduces C(k) to a finite optimization over prime-range cut points beta_i and truncation levels of exponential approximations, all evaluable in interval arithmetic. Project: re-derive the constant-tracking chain, implement it against the lab's Arb ball arithmetic (rigor.py), and produce enclosure-checked explicit C(2), C(3), C(4), optimizing the cut-point sequence numerically. Explicit conditional moment constants feed explicit RH-conditional zero-gap and S(T) estimates that currently cite ineffective bounds. First signal: an enclosure for C(2) matching or beating Tao's value. Falsified cheaply if the chain forces C(k) so large (e.g. > 10^100 at k=3) that no downstream application can use it; that too is a publishable calibration.
- key ref: arXiv:2407.20023 (Tao) building on arXiv:1305.4618 (Harper)

## Cosine universality rates for Xi^(n) and the Davenport-Heilbronn discriminant test
*from Territory G: geometry of the Riemann xi function ,  de Bruij*
- I=5 N=7 T=7 V=7 C=9 F=1 sat=2 signal: 1-2 days for the first Delta(n) decay curve
- Campbell-O'Rourke-Renfrew (arXiv:2410.06403) prove Farmer-Rhoades cosine universality qualitatively for real-rooted even entire functions; no rates are known and Xi is covered only under RH. Numerical program: compute zeros of Xi^{(n)} for n = 1..64 in the window t in [0, 500] at high precision (derivatives via the Hermite/Turan expansion of Xi, whose coefficients Romik's asymptotics control), measure the deviation-from-equal-spacing statistic Delta(n) = normalized variance of consecutive gaps, and fit the decay rate (conjecture: Delta(n) ~ c/n, testable). Then run the identical pipeline on the Davenport-Heilbronn function (epstein.py): since DH violates RH but has real coefficients and a Hardy-type Z, whether differentiation equalizes its on-line spacing at the same rate is exactly Farmer's discriminance question, and either answer is a robust publishable conjecture with a battery-passing methodology. First signal (1-2 days): Delta(n) curve for n <= 16 for Xi; falsified as a project if derivative zero computation loses precision before any trend is visible.
- key ref: Campbell-O'Rourke-Renfrew, arXiv:2410.06403; Farmer-Rhoades, Trans. AMS 357 (2005)

## Refutation-with-witness of Liu's arXiv 'Disproof of the Riemann Hypothesis'
*from Territory K: systematic sweep of mid-2025 through August 202*
- I=3 N=9 T=9 V=10 C=9 F=3 sat=1 signal: 1-2 days
- Liu (arXiv:2404.06306, latest v Jan 2025) claims a contradiction from reciprocal sums over xi-zeros. The claimed contradiction routes through computable series identities. Project: identify the first quantitative equation in the paper, compute both sides with Arb-enclosure-checked enclosures over the lab's zero tables (sums over reciprocals of zeros converge fast enough to certify), and publish the located error as a two-page refutation with a numerical witness. First signal (1-2 days): the first equation whose enclosure-checked enclosures are disjoint. Cheap to falsify our own attempt: if every checkable identity holds, the error is in a limiting/interchange step, which the audit then pinpoints symbolically. Low mathematical glory, but it is exactly the 'route closed with a witness' output class the lab counts, and nobody in the literature has bothered.
- key ref: arXiv:2404.06306

## A multi-window inertia census toward the 0.68185 bandwidth-one ceiling
*from Territory A: proportions of zeros of zeta on/near the critic*
- I=8 N=5 T=6 V=8 C=9 F=5 sat=2 signal: 3-7 days to the discriminating-LP verdict
- The unconditional proof uses two traces of one window family; the configuration-by-configuration ceiling for bandwidth-one data is 0.68185 (Remark 1.1) and the lab's gap-census transplant (prior art) reaches only 0.6725106958. Project: design a certificate using the JOINT inertia data of several overlapping window families (e.g. two interleaved Gabor families at offsets 0 and π/L, or dyadic sub-windows), whose block structure sees off-line pairs and on-line doubles with different charges than a single family does, and find the extremal configuration law by LP over synthetic configurations (simples, doubles, triples, off-line pairs at varying depths ,  reproducing the paper's §8(3) synthetic-configuration harness inside the lab). First falsifiable signal: an LP over ≤ 10^4 discretized configurations showing whether ANY two-window invariant separates the 2/3-extremal configuration (2N/3 simples + N/6 doubles) strictly better than the single-window rank-trace bound; if the LP value stays ≤ 0.67252, the invariant class is dominated and the route dies in under a week. This deliberately differs from the Cheer–Goldston-style nearest-neighbor gap census already in the lab's prior art.
- key ref: Anthropic 2026 preprint Remark 1.1, §7.5, §8(3); Zeta23/PairCeiling in zeta-23-lean

## Does the CFKLT-B variational derivative combination compose with the two-thirds framework? Evaluate kappa at theta = 4/7
*from Territory C: moments of the Riemann zeta function on the cri*
- I=8 N=5 T=6 V=9 C=10 F=4 sat=4 signal: 3-5 days to a validated implementation of the variational optimum
- Conrey-Farmer-Kwan-Lin-Turnage-Butterbaugh (arXiv:2508.11108) solve a calculus-of-variations problem producing an optimal linear combination of zeta-derivatives for Levinson's method at ANY mollifier length theta, and report large gains in the short-theta regime (modular L-functions). The August 2026 two-thirds framework operates at long theta with a different lever set (this lab's prior art is the Cheer-Goldston gap-census floor inside that framework; the derivative-combination lever is disjoint from it). Project: implement the CFKLT-B Euler-Lagrange solution numerically (their kernel is explicit), tabulate the proportion functional kappa(theta) for zeta on theta in (0, 4/7], and evaluate whether their optimal derivative combination, inserted into the two-thirds framework's main-term functional in place of its chosen combination, changes the output constant 0.6725007037 in the fourth decimal. First signal: reproducing their reported proportions for Levinson's original mollifier (validates the implementation, ~3 days). Cheap falsification: if the framework's combination already agrees with the Euler-Lagrange optimum at theta=4/7 to high precision, composition gains nothing and the question closes with a numerical certificate.
- key ref: arXiv:2508.11108 (Short mollifiers of the Riemann zeta-function)

## enclosure-checked extension of the colossally abundant Robin verification, plus pinning Zimov's band constants
*from Territory E: equivalent and near-equivalent criteria for RH *
- I=5 N=6 T=8 V=9 C=8 F=6 sat=5 signal: 2-3 days
- Two coupled deliverables on Robin's criterion. (a) Regenerate colossally abundant numbers as prime-exponent vectors and verify Robin's inequality with exact rational/interval arithmetic out to 10^(10^12) (Briggs stopped at 10^(10^10) in 2006 with unpublished precision details), producing an enclosure-carrying record. (b) Numerically instantiate Zimov's October 2025 band e^gamma < G(n) < e^gamma(1 + c/(log n)^b), 0 < b < 1/2, for the least CA exception: extract the explicit (c, b) his ratio argument yields and test whether known CA data already contradicts sharper (c, b) pairs, which would delimit how much his exclusion can be strengthened. First signal (2-3 days): G(n) computed with balls for the first 10^4 CA numbers, matching Briggs where they overlap; falsification surface: any CA number where the enclosure cannot decide the inequality exposes precision limits immediately.
- key ref: arXiv:2510.23889; Briggs, Exp. Math. 15 (2006)

## Turan-type inequalities in Romik's Meixner-Pollaczek and continuous Hahn bases
*from Territory G: geometry of the Riemann xi function ,  de Bruij*
- I=5 N=6 T=8 V=8 C=9 F=3 sat=1 signal: 3-4 days for both coefficient tables and the first inequality census
- Romik (arXiv:1902.06330) proved his Meixner-Pollaczek and continuous Hahn expansion coefficients of Xi alternate in sign and suggested these bases are more natural than Hermite for RH, but no Jensen/Turan-type theory exists in them. Project: (a) compute the coefficient sequences c_n to 50+ digits (explicit integrals against Phi, Arb-certifiable); (b) test Turan and cubic Turan inequalities for |c_n| for n <= 5000; (c) run the identical computation for the Davenport-Heilbronn analogue (its kernel is a finite combination of Epstein theta data) to see whether any inequality that holds for Xi fails for DH: a discriminating inequality would be the first Farmer-criteria-passing positivity statement in this corner and a genuinely new conjecture; a non-discriminating one is a documented negative result. First signal (days): the n <= 500 table for both functions. Cheap falsification: DH satisfies everything Xi does (likely per docs/09 experience), settled within a week.
- key ref: D. Romik, arXiv:1902.06330

## Recompute the explicit Mertens constant 0.209 with the new zero-free cascade
*from Territory H: explicit and computer-assisted results ,  RH ve*
- I=5 N=6 T=8 V=8 C=7 F=5 sat=3 signal: 2-4 days
- Lee(-Leong)'s M(x) <= x exp(-0.209 (log x)^{3/5} (log log x)^{-1/5}) (arXiv:2208.06141) derives its exponent constant from pre-2025 KV zero-free constants and explicit 1/zeta bounds. The dependence chain (KV constant c -> eta_2 ~ f(c)) is stated explicitly in the paper. Recompute eta_2 with Bellotti 48.0718 and check whether the March-2026 classical region shifts the binding range. Secondary computational arm: extend Hurst's exact M(x) computation beyond 10^16 using Helfgott-Thompson mu-sieving to update the empirical |M(x)|/sqrt(x) < 0.571 record. The lab's criteria.py (Mertens/Mobius face) provides the checking harness, and the lab already holds a kernel-checked Mertens theorem to anchor the Lean-adjacent write-up. First signal: the recomputed eta_2 from the paper's own dependence formula, 2-4 days. Falsified if eta_2 is insensitive to c in the relevant range (visible from the formula immediately).
- key ref: arXiv:2208.06141 + arXiv:2603.21490; Hurst arXiv:1610.08551

## Kernel-checked Turing/Backlund zero-counting criterion in Lean 4
*from Territory H: explicit and computer-assisted results ,  RH ve*
- I=7 N=8 T=4 V=10 C=6 F=10 sat=1 signal: 1-2 weeks (scoping verdict); 4-8 weeks (instance)
- No proof assistant has a verified statement of the Turing-method completeness criterion (if Z(t) has M sign changes in [0,T] and the Backlund/argument bound holds, then N(T) = M), even though every RH verification since 1953 rests on it. Target: formalize in the lab's ZetaLean the elementary implication [explicit S(T) bound] + [sign-change count] => [exact N(T)], with the Bellotti-Wong constants as hypotheses (not proved), and instantiate it kernel-checked for a small window using the existing IntervalExp/Rigor layers to certify sign changes of Z on [0,100], yielding a kernel-checked N(100) = 29. First signal: the criterion statement compiling with sorry-free elementary parts within 1-2 weeks; the numeric instantiation rides existing lab interval machinery. Falsified/blocked if Mathlib's argument-principle support is too weak for even the hypothesis-carrying version (discoverable in days by scoping against Mathlib's ZetaFunction and argument-principle files).
- key ref: arXiv:2412.15470; Turing (1953); lab lean/ZetaLean Rigor layers

## Effective Montgomery: the sigma_N census for partial sums of zeta
*from Territory J: forgotten, abandoned, or obscure RH approaches *
- I=4 N=7 T=8 V=8 C=7 F=5 sat=3 signal: 6-12 hours for N <= 500; a week for the full census
- Compute sigma_N = sup{Re s : zeta_N(s) = 0} with enclosure-checked rightmost-zero location for N up to ~10^5 and measure the convergence of (sigma_N - 1) * log N / log log N to Montgomery's constant 4/pi - 1 = 0.2732395447351628, which has only a non-effective o(1). Deliverables: an empirical second-order term, a conjectured effective form, and (stretch) an explicit-constant version of Montgomery's lower-bound construction for a concrete N. Platt-Trudgian 2016 only decided existence of zeros with sigma > 1; nobody has published the sigma_N curve. Falsifiable: the scaled quantity either stabilizes toward 0.27324 or visibly does not in the computable range (either outcome is publishable as a measured fact about a 40-year-old asymptotic). First signal: sigma_N for N <= 500 (rightmost zeros of low-degree Dirichlet polynomials), hours.
- key ref: arXiv:1507.01340 (Platt-Trudgian); Montgomery 1983, Zeros of approximations to the zeta function

## Formalize det(R_n) = M(n) and the eigenvalue-1 multiplicity of the Redheffer matrix in Lean 4
*from Territory J: forgotten, abandoned, or obscure RH approaches *
- I=4 N=8 T=7 V=10 C=3 F=10 sat=2 signal: 2-3 days
- Kernel-check Redheffer's 1977 identity det R_n = M(n) (finite combinatorics on the divisibility poset, Mobius function already in Mathlib) plus Barrett-Forcade-Pollington's fact that R_n has exactly n - floor(log_2 n) - 1 eigenvalues equal to 1. This is a self-contained, genuinely attractive formalization no one has done (checked: not in Mathlib), it connects directly to the lab's kernel-checked Mertens work, and it is the natural Lean-side anchor for any future Redheffer-spectrum computation. Falsifiable trivially at small n by exact integer computation inside the proof development. First signal: det R_n = M(n) for symbolic n proved for the n <= 10 instances plus the general unimodular-triangularization skeleton, 2-3 days of Lean work.
- key ref: Redheffer 1977; Barrett-Forcade-Pollington 1988; arXiv:2511.13627 for the current literature state

## First kernel-checked zero-density statement: Carlson/Bohr-Landau in Lean 4
*from Territory B: zero-density estimates and zero-free regions , *
- I=6 N=9 T=4 V=10 C=3 F=10 sat=1 signal: 3-7 days for formal statement + Jensen-based counting lemma compiling with zero sorrys
- Formalize in Lean 4 + Mathlib a genuine zero-density estimate, targeting the weakest nontrivial rung: Bohr-Landau (N(sigma,T) = O(T) for fixed sigma > 1/2) or Carlson's N(sigma,T) = O(T^{4sigma(1-sigma)+eps}), via a mollified second moment plus Jensen/Littlewood zero counting. No formalized zero-density theorem exists in any proof assistant (none found in searches; Mathlib has zeta, the argument principle, and PNT-adjacent infrastructure from the PrimeNumberTheoremAnd project). First signal (days): the formal statement plus a sorry-free proof of the finite-region zero-counting lemma from Jensen's formula; full proof is weeks. Verifiability is absolute (kernel); falsification is a demonstrated missing-prerequisite wall in Mathlib, which is itself a useful map. Fits the lab's zero-sorry Lean arm and its Hardy-Ramanujan/Mertens formalization experience.
- key ref: arXiv:2412.02068 (explicit Carlson, as the blueprint); Mathlib/PrimeNumberTheoremAnd

## SDP for the averaged-F extremal problem: tighten 0.9303 from below
*from Territory D: pair correlation and zero statistics ,  Montgom*
- I=6 N=6 T=6 V=9 C=8 F=5 sat=3 signal: 3-5 days to reproduction of 0.9303
- Carneiro-Milinovich-Ramos (arXiv:2310.01913) bound the conjectured-to-be-1 average of Montgomery's F by [0.9303, 1.3208] on RH, using hand-selected function families with a novel averaging mechanism. Unlike the pure pair-correlation window (where SDP is converged), the AVERAGED extremal problems have never been given a rigorous SDP treatment: the averaging measure itself is an optimization variable alongside the test function. Project: cast the lower-bound problem as an SDP over (Hermite-coefficient, discretized-averaging-measure) pairs, reproduce 0.9303, then optimize both jointly with Arb-verified feasibility. First signal: reproduction of 0.9303, then whether joint optimization moves the third decimal. Falsification: if the paper's choice is within 1e-4 of the SDP optimum, the extremal problem is effectively solved and the bottleneck is arithmetic, not analysis ,  a useful negative delta to record. Improvement here transfers automatically to Selberg's variance integral and the second moment of ζ'/ζ via the 'three integrals' identities (arXiv:2108.09258).
- key ref: arXiv:2310.01913 + arXiv:2108.09258

## Propagate post-2020 Kloosterman-sum exponents through the 50/1093 support constant
*from Territory I: neighboring L-function problems ,  Dirichlet cr*
- I=6 N=6 T=6 V=9 C=7 F=2 sat=3 signal: ~1 week to transcribe the exponent bookkeeping and reproduce 50/1093
- Drappeau-Pratt-Radziwill's one-level-density support 2 + 50/1093 is the output of a linear optimization whose inputs are Deshouillers-Iwaniec-type bilinear Kloosterman estimates. Refinements of exactly those estimates have appeared since (Pascadi's improvements to Deshouillers-Iwaniec exponent pairs, 2023-2025; verify the exact statements online first, this survey did not fetch them). Project: extract DPR's final linear program (their Section with the exponent bookkeeping), re-derive 50/1093 from it (first falsifiable signal), then substitute the improved exponents and solve. Output is a new explicit support radius or a proof that the improvements do not enter the binding constraint (also citable). Entirely mechanical once the LP is transcribed; the risk is that DPR's binding constraint is elsewhere, discoverable in the first week.
- key ref: arXiv:2002.11968

## d_N^2 log N versus 0.0461914179: enclosure-checked Nyman-Beurling minimization at N ~ 10^4
*from Territory J: forgotten, abandoned, or obscure RH approaches *
- I=6 N=6 T=6 V=9 C=8 F=2 sat=4 signal: 1-2 days for N <= 100; 2-3 weeks for N ~ 10^4 with structure-exploiting solver
- Compute the Baez-Duarte distance d_N^2 with enclosure-checked error: Arb-enclosed Vasyunin-sum Gram entries (the 2024 Gram-structure paper arXiv:2405.06349 gives the algebra), multiprecision Cholesky/CG solve, and rigorous enclosure of the minimum of the quadratic form for N on a log grid to ~10^4. Target: the first credible empirical approach curve of d_N^2 log N toward 2 + gamma - log(4pi) = 0.0461914179, whose second-order term tests the Bettin-Conrey-Farmer side hypothesis sum_rho 1/|zeta'(rho)|^2 << T^{3/2-delta} numerically. Mid-2000s float attempts never exhibited convergence. Falsifiable: a measured second-order coefficient inconsistent with the BCF model at small N is a real constraint on the discrete moment conjecture. First signal: enclosure-checked d_N^2 for N <= 100 matching literature floats, 1-2 days.
- key ref: arXiv:1211.5191 (Bettin-Conrey-Farmer); arXiv:2405.06349 (Gram matrices, 2024)

## Interval-certify and formalize the RH-conditional cubic certificate (0.85082) ,  the one theorem-family zeta-23-lean left out
*from Territory A: proportions of zeros of zeta on/near the critic*
- I=5 N=6 T=7 V=10 C=8 F=10 sat=1 signal: hours for Arb enclosures; 1-2 weeks for the Lean lemmas
- The public Lean formalization (zeta-23-lean) covers Theorems A–E, XiPrime, and the PairCeiling, but NOT the §7.5(g) RH-conditional cubic-weight result N_d ≥ 1/2 + (2m₂−m₃)/18 + (4/9)·(19/27) = 0.85082…. Its ingredients are finite and formalization-shaped: (i) ψ(m) = m/2 + (2m²−m³)/18 + (4/9)1_{m=1} ≤ 1 for all integers m ≥ 1 with equality at m = 1,2,3 (a decidable integer inequality plus an easy tail); (ii) the Schur–Horn majorisation step Σ(2m_i²−m_i³) ≥ 2trH²−trH³ for PSD H with the admissible cubic f(x) = −x²/9 + x³/18; (iii) Arb/rigor.py two-backend enclosures of m₂(1,v), m₃(1,v) for v = cos(8s/5) pinning 2m₂−m₃ = 0.68524… and the final 0.85082…. First signal: the rigor.py enclosure of both constants (hours ,  the moments are explicit low-dimensional integrals of sine-kernel products); then Lean lemmas (i)-(ii) in the lab's own Lean arm, reusing Mathlib's inner_mul_le_norm_mul_norm/majorisation infrastructure and the ladder discipline (zero sorrys or it does not count). If project 2's window optimization succeeds first, certify the improved constant instead ,  the pipeline is identical.
- key ref: Anthropic 2026 preprint §7.5(g); github.com/anthropics/zeta-23-lean (scope list)

## Joint simple-AND-critical functional in the narrow-box framework: beat the 1/3
*from Territory D: pair correlation and zero statistics ,  Montgom*
- I=7 N=5 T=6 V=8 C=7 F=6 sat=4 signal: 3-5 days
- BGST (arXiv:2501.14545) get 2/3 simple and 2/3 critical under the narrow box, but only 1/3 for the joint count ,  the shape of an inclusion-exclusion bound (2/3 + 2/3 - 1). The Claude Aug 2026 paper reaches 0.6725 joint unconditionally, so the 1/3 in the published BGST route is provably not optimal; the question is whether a DIRECT joint pair-correlation functional (single optimization weighting both horizontal multiplicity and off-line penalty simultaneously, rather than intersecting two separate bounds) recovers 2/3 - δ joint inside the simpler narrow-box setting, with an explicit extremal function. Project: formulate the joint functional following the horizontal-multiplicity bookkeeping of arXiv:2503.15449, optimize the test function numerically, and check against the two known endpoints. First signal: the functional written down and evaluated at the Fejér kernel ,  if it already gives > 1/3, the direction is live within days. Cheap to falsify: if the joint functional provably decouples into the two marginals, the intersection bound is optimal in this framework and that is a clean lemma.
- key ref: arXiv:2501.14545 + arXiv:2503.15449

## First enclosure-checked finite Speiser verification: zeta' non-vanishing left of the critical line up to height T
*from Territory E: equivalent and near-equivalent criteria for RH *
- I=5 N=6 T=7 V=10 C=9 F=3 sat=3 signal: 2-3 days
- Adapt rigor.py's argument-principle enclosures to zeta'(s) and certify: zeta' has no zeros with 0 < Re(s) < 1/2, 0 < Im(s) <= T, for T = 10^4 initially, then as far as compute allows. Literature search found float-grade zeta' zero computations but no enclosure-carrying Speiser certificate at any height; the deliverable is a enclosure-checked statement with the safe-failure contract (not enclosure-checked rectangles named, not hidden). Bottleneck to probe first: enclosure blowup near the zeros of zeta' that hug the critical line (Zhang/Soundararajan clustering). First signal (2-3 days): a enclosure-checked zero count of zeta' in the rectangle [0, 1/2] x [0, 100] cross-checked against known float lists; falsified as a project if ball widths near sigma = 1/2 make rectangles undecidable at feasible precision, measurable immediately.
- key ref: Speiser, Math. Ann. 110 (1935); Levinson-Montgomery, Acta Math. 133 (1974)

## Effective Ki-Kim-Lee: enclosure-checked non-real-zero-free heights for H_t at fixed t > 0
*from Territory G: geometry of the Riemann xi function ,  de Bruij*
- I=5 N=7 T=6 V=9 C=9 F=5 sat=2 signal: 3-5 days for the first enclosure-checked box count at t=0.2
- Ki-Kim-Lee (Adv. Math. 222 (2009)) prove H_t has only finitely many non-real zeros for each t > 0 but give no effective bound. Polymath15's effective A+B approximation already controls H_t above explicit heights for t near 0.2. Project: for a ladder of fixed times t in {0.05, 0.1, 0.15, 0.2}, produce enclosure-checked statements 'all zeros of H_t with |Im z| > 0 lie in |Re z| <= X(t), and H_t has exactly k(t) non-real zeros' by combining the Polymath15 effective bounds (above the barrier) with Arb contour counts (below it). This turns a qualitative 2009 theorem into the first quantitative non-real-zero census of the de Bruijn-Newman flow, directly reusable by anyone attacking Lambda from above, and the k(t) curve as t decreases toward Lambda is itself new measured structure (how the flow sheds complex zeros). First signal (days): a enclosure-checked count k(0.2) = 0 up to height 1000 reproducing barrier-region behavior; falsified if the A+B error terms are too weak below Polymath15's x-range to close any box.
- key ref: Ki-Kim-Lee, Adv. Math. 222 (2009) 281-306; arXiv:1904.12438 effective estimates

## Rigorous re-optimization of the van der Corput parameter space in the Revers explicit sub-Weyl bound
*from Territory K: systematic sweep of mid-2025 through August 202*
- I=5 N=6 T=7 V=9 C=9 F=5 sat=5 signal: 4-7 days
- Revers (arXiv:2602.05614, Feb 2026) improves the explicit |zeta(1/2+it)| constant over Hiary-Patel-Yang via a refined explicit van der Corput method 'together with computational calculations', i.e. finite parameter searches whose optimality is not established. Project: reconstruct the paper's constant chain, express each range-of-t constant as an explicit function of the subdivision/exponent-pair parameters, and run an Arb-enclosure-checked branch-and-bound over the parameter boxes. Explicit critical-line bounds feed directly into zero-counting (Bellotti-Wong) and verification pipelines, so even a 1-3% constant shave propagates. First signal (4-7 days): reproduction of Revers' constant from the reconstructed chain (a nontrivial audit in itself, given the Cheng-Graham precedent of a wrong constant surviving for years), then the first parameter cell with a enclosure-checked improvement. Falsified if branch-and-bound certifies the published parameters are within 0.5% of optimal, which is itself a useful optimality certificate no explicit-bounds paper currently has.
- key ref: arXiv:2602.05614

## enclosure-checked re-run of the cosine-polynomial layer of MTY/Bellotti zero-free regions
*from Territory B: zero-density estimates and zero-free regions , *
- I=5 N=5 T=8 V=9 C=8 F=7 sat=7 signal: 4-8 hours to enclosure-checked degree-6 reproduction; 1-2 days for degree 7-8 certification
- Reproduce Arestov's degree-6 optimum and Tan's numerical degree 7-8 optima for the Landau extremal problem inside the lab's Arb stack, produce exact rational SOS/Fejer-type nonnegativity certificates, then extend the search to (a) degrees 9-16 and (b) Nielsen's enlarged class with factor (1+cos theta), and push any strictly better polynomial through the Mossinghoff-Trudgian-Yang pipeline to recompute R = 5.558691 and the KV constant 55.241/54.004. First signal (hours-days): enclosure-checked reproduction of the degree-6 optimum and a measured improvement curve vs degree, which immediately falsifies or confirms whether > 10^{-3} of R is available. Cheap falsification: if the degree-7/8 marginal gain Tan reports is < 10^{-4} of R, kill the degree direction and keep only the class-enlargement direction.
- key ref: arXiv:2411.01385, arXiv:2210.14130, arXiv:2212.06867

## Coefficient-by-coefficient confrontation of the CFKRS sixth-moment polynomial with high-height |zeta|^6 data
*from Territory C: moments of the Riemann zeta function on the cri*
- I=5 N=5 T=8 V=9 C=10 F=2 sat=4 signal: 2-4 days to enclosure-checked P_3 coefficients
- The full degree-9 CFKRS polynomial P_3 for the sixth moment is explicitly computable (2k-fold residue formula; coefficients are polynomials in gamma, log(2pi), and a_3-type Euler products). The lab's moments module ingests LMFDB/Odlyzko-height data and separately sourced |zeta| samples by design. Project: (1) compute all ten coefficients of P_3 to 30 digits in mpmath via the CFKRS contour formula; (2) estimate Int_T^(T+H) |zeta|^6 over many windows at the largest heights with available samples; (3) fit the observed H-dependence against P_3 and measure the residual as a function of T, testing the conjectured square-root-cancellation error shape O(T^(1/2+eps)) that Ng's reduction implicitly assumes for the ternary divisor correlations. A residual decaying visibly slower than T^(1/2) at reachable heights would be genuine evidence about the divisor-conjecture error term; agreement pins the constants publicly. First signal: the ten enclosure-checked coefficients of P_3 (a self-contained deliverable, ~2-4 days, checkable against CFKRS's published numerics for the fourth moment as calibration). Falsification: sampling variance may dominate beyond the first two coefficients; the variance model says so in advance and bounds the claim.
- key ref: CFKRS, Proc. LMS 91 (2005) 33-104; arXiv:1610.04977 (Ng)

## Re-optimization of the Polymath15 barrier at fixed verification height: is 0.2 tight?
*from Territory E: equivalent and near-equivalent criteria for RH *
- I=8 N=5 T=5 V=9 C=10 F=3 sat=6 signal: 1-2 weeks to full reproduction; parameter landscape within days after
- Reproduce the Polymath15 pipeline (effective H_t ~ B_t bounds, barrier certification) with heatflow.py + rigor.py, then treat (t, y_0, barrier location X, mollifier b_n) as an explicit optimization problem at the fixed rigorously-verified height 3*10^12 (Platt-Trudgian). The 0.2 bound was a round-number stopping point, not a computed optimum; the question 'what is the best Lambda achievable from height 3*10^12?' has a definite answer nobody has published. Expected outcome is a small shave (0.19x) or a documented proof that 0.2 is within epsilon of optimal for this height, and either is a citable delta against arXiv:1904.12438. First signal (1-2 weeks): reproduction of Lambda <= 0.22 end-to-end on the lab's own stack; falsified early if the effective bounds' constants already consume all slack, visible in the first parameter sweep.
- key ref: arXiv:1904.12438; arXiv:2004.09765

## Computational audit of the numerical inequality in Zhang's Landau-Siegel argument
*from Territory I: neighboring L-function problems ,  Dirichlet cr*
- I=8 N=5 T=5 V=9 C=8 F=3 sat=2 signal: 3-7 days to extract and encode the first block of explicit inequalities
- The publicly reported obstruction to Zhang's arXiv:2211.02515 includes a 'meaningful mistake in numerics' of unclear criticality (Manifold/community discussion; Tao forwarded technical problems). The paper's discrete mean estimates culminate in explicit inequalities between computed constants. Project: locate the specific numerical inequalities in the preprint (Sections with explicit constants), recompute each with ball-arithmetic enclosures (rigor.py), and publish a verdict per inequality: holds / fails / holds-with-degraded-constant, with enclosure-checked enclosures. This does not attempt to verify the whole 111-page argument, only its finite numerical spine. First signal: within a week, either all checked inequalities enclose correctly (raising confidence and worth stating) or one fails with a enclosure-checked counter-enclosure (a concrete, checkable contribution to the status of the most important claimed result in the field). Requires care in presentation: an inequality failure is a statement about the preprint's constants, not a refutation of the strategy.
- key ref: arXiv:2211.02515

## LP slack hunt over the ANTEDB large-values inventory near the A(sigma) crossover points
*from Territory B: zero-density estimates and zero-free regions , *
- I=7 N=4 T=7 V=9 C=9 F=4 sat=8 signal: 1-2 days to reproduce the table; signal is immediate LP slack or dual optimality certificates
- Implement (or drive) the ANTEDB zero-density LP and search for strict improvements to the piecewise A(sigma) record specifically on sigma in (19/25, 7/9), where five different methods tie at awkward rationals (127/167, 13/17, 17/22, 41/53), by adding the Guth-Maynard LV estimate variants, the four new Tao-Trudgian-Yang exponent pairs, and Chen-Debruyne-Vindas inputs simultaneously rather than pairwise. First signal (1-2 days): exact reproduction of Table 11.1; success = any subinterval where the LP optimum beats the recorded piece by a positive rational; clean negative = dual certificates proving the current table is optimal for the current inventory (itself a contributable fact to ANTEDB). Falsifiable by construction since every output is an exact rational checked against the table.
- key ref: arXiv:2501.16779; teorth.github.io/expdb blueprint ch. 11

## Squeeze the log powers: parameter re-optimization of the Palojarvi-Trudgian E_2(T) chain and its 8th-12th moment consequences
*from Territory C: moments of the Riemann zeta function on the cri*
- I=4 N=6 T=8 V=9 C=8 F=2 sat=3 signal: 2-3 days to reproduce their exponents
- Palojarvi-Trudgian (arXiv:2506.16766, June 2025, 12 pages) improve the powers of log T in E_2(T) << T^(2/3)(log T)^C and thereby the 2k-th moments for 8 <= 2k <= 12, including the constant in Heath-Brown's twelfth moment T^2 (log T)^17. Their improvements come from explicit choices (truncation points, interpolation exponents between the 4th and 12th moments, large-value parameters) that are fixed by hand. Project: transcribe the finite parameter set of their lemma chain into a small optimization problem and search it numerically (the lab has done exactly this pattern for the two-thirds framework); additionally test whether substituting the Guth-Maynard 2024 large-value theorem into the Heath-Brown balance moves any exponent. First signal: reproducing their stated C values from the lemma chain (2-3 days); any slack found is an immediate, checkable improvement to a named constant in a 2025 paper. Falsification: the chain may be provably tight at each step, determinable by inspecting where each optimization is interior vs boundary.
- key ref: arXiv:2506.16766 (Palojarvi-Trudgian)

## Dependency audit: do Curran's sharpened shifted-moment bounds shrink the hypotheses of the Ng-Shen-Wong eighth moment?
*from Territory C: moments of the Riemann zeta function on the cri*
- I=6 N=5 T=6 V=8 C=5 F=2 sat=3 signal: 3-5 days to the dependency map
- The NSW eighth moment (arXiv:2204.13891) assumes RH plus a quaternary additive divisor conjecture with a specific power saving delta and shift-uniformity, and its proof consumes a sharp RH-conditional shifted-moment bound of Chandee type (proved in arXiv:2206.03350). Curran (Mathematika 2024) sharpened these shifted-value correlation bounds by log factors. Project: map exactly where the shifted-moment bound enters NSW (which error range it controls, with which log budget), substitute Curran's bound, and compute the minimal (delta, uniformity) pair in the divisor hypothesis that still closes the argument. Deliverable: either a strictly weaker sufficient hypothesis for the eighth moment (a real, checkable improvement to a 2022 JEMS result's hypothesis set) or a documented proof that the divisor-sum bottleneck absorbs all log savings. First signal: the one-page dependency map identifying the binding inequality, achievable from a close read plus symbolic bookkeeping in sympy. Cheap falsification: if the shifted-moment input is already lossless at the binding step, the audit terminates negatively in under a week.
- key ref: arXiv:2204.13891 (Ng-Shen-Wong) + Curran, Mathematika 70 (2024) e12268

## Map the Toeplitz sign diagram of the de Bruijn-Newman kernel beyond order five
*from Territory E: equivalent and near-equivalent criteria for RH *
- I=4 N=5 T=9 V=10 C=9 F=5 sat=2 signal: 1-2 days
- Independently recompute the February 2026 claim (arXiv:2602.20313) that Phi fails Polya-frequency order 5, then chart the full (order k, node configuration) sign diagram of Phi's Toeplitz/Hankel minors with enclosure-checked determinant signs: at which orders and scales positivity fails, and whether the 'threshold' is monotone. Value: (i) audits a fresh unrefereed posting (and checks whether it overlaps this lab's own heatflow output before any duplication); (ii) the diagram constrains which total-positivity arguments could ever apply to H_t reality-preservation, a structured negative result in the style the lab already publishes. First signal (1-2 days): reproduction or refutation of the order-5 failing minor with Arb determinant enclosures; falsifies instantly if the minor's sign certificate disagrees, which is itself the headline.
- key ref: arXiv:2602.20313; arXiv:1801.05914

## Rerun and re-optimize the Polymath15 barrier: publish Lambda <= 0.20 (or lower)
*from Territory G: geometry of the Riemann xi function ,  de Bruij*
- I=6 N=6 T=5 V=10 C=8 F=4 sat=3 signal: ~1 week to reproduce the 0.22 certificate, 2-4 weeks for a new constant
- The unconditional record is Lambda <= 0.22 (arXiv:1904.12438); the improvement to 0.20 enabled by Platt-Trudgian's 3x10^12 verification exists only as a Polymath-wiki remark and was never published or optimized. Project: port the public dbn_upper_bound pipeline (github.com/km-git-acc/dbn_upper_bound) onto the lab's Arb stack, reproduce the 0.22 certificate, then re-place the barrier at the 3x10^12 frontier and re-optimize (t_0, barrier x_0, mesh) to find the true minimum t the current verified height supports (plausibly below 0.20, since the wiki number was not optimized). Every step is a finite enclosure-checked computation; the deliverable is an unconditional record constant with a reproducible certificate, exactly this lab's genre. First signal (week 1): independent reproduction of the 0.22 barrier certificate. Cheap falsification: if reproduction cost is prohibitive at lab scale, stop; scaling estimates are visible after the first barrier run.
- key ref: D.H.J. Polymath, arXiv:1904.12438; https://michaelnielsen.org/polymath/index.php?title=De_Bruijn-Newman_constant

## Hybrid resonance-correlation × SDP attack on the positive-proportion small-gap constant 0.6039
*from Territory D: pair correlation and zero statistics ,  Montgom*
- I=7 N=5 T=5 V=8 C=8 F=3 sat=2 signal: 4-7 days to the feasibility verdict
- Two disjoint toolkits currently bound different small-gap functionals: SDP over Cohn-Elkies functions gives gaps < 0.6039·average for ≫N(T) pairs (RH), while Inoue's resonance-correlation gives μ < 0.50895 for infinitely many. The resonator weight w(t) = |R(t)|² can be inserted into the SDP counting functional: the cross terms reduce, via the explicit formula, to the same Montgomery-window information plus approximator terms Inoue already controls. Project: write the weighted pair-correlation functional, verify all arithmetic inputs stay inside |α| ≤ 1 support (the go/no-go check, computable on paper + mpmath in days), then run the joint optimization. First signal: the feasibility audit ,  if the resonator pushes required support beyond 1, the project dies cheaply in under a week. If feasible, target: positive-proportion gaps below 0.60, or a documented obstruction. Nobody has published this combination (Inoue's paper is 4 months old).
- key ref: arXiv:2604.05733 + arXiv:1810.08843

## Variational derivative-combinations plugged into the full-length zeta Levinson functional
*from Territory K: systematic sweep of mid-2025 through August 202*
- I=5 N=5 T=7 V=8 C=8 F=2 sat=6 signal: 4-8 days
- Conrey-Farmer-Kwan-Lin-Turnage-Butterbaugh (arXiv:2508.11108) show optimizing the linear combination of zeta derivatives beats refining the mollifier, but they exploit it mainly for short mollifiers and degree-2 L-functions. Project: implement their Euler-Lagrange system for the combination measure in mpmath and evaluate the Levinson functional with the standard theta = 4/7 full-length zeta mollifier, scanning whether the optimal combination shifts the smooth-surrogate proportion above the Pratt-Robles-Zaharescu-Zeindler kappa >= 0.4172 baseline configuration (this is the classical-pipeline analogue, independent of the lab's existing gap-census transplant work on the 0.6725 framework). First signal (4-8 days): the surrogate functional value for their optimal combination vs the classical c*Q(d/dlog) combination at matched arithmetic inputs. Falsified if the gain provably vanishes as mollifier length grows (the paper hints gains concentrate at short lengths; quantifying that decay is itself a result).
- key ref: arXiv:2508.11108

## CFKLT variational derivative-combinations at full mollifier length: does 0.417293962 move?
*from Territory A: proportions of zeros of zeta on/near the critic*
- I=7 N=4 T=6 V=8 C=8 F=2 sat=8 signal: 2-4 days to reproduce PRZZ's constant; 1-2 weeks for the enlarged optimization
- Conrey–Farmer–Kwan–Lin–Turnage-Butterbaugh (arXiv:2508.11108, Aug 2025) construct by calculus of variations a sequence of linear combinations of ζ-derivatives adapted to Levinson's method, and report the combination matters more than the mollifier when the mollifier is short. PRZZ's record 0.417293962 was obtained with a FINITE truncation (d = 1, K = 3) of the analogous combination at full length θ_C = 4/7, θ_F = 6/11. Project: reimplement the PRZZ main-term functional (their §6-8 closed forms, with printed optimal polynomials P₁,P₂,P₃,Q and R = 1.1167 as regression targets ,  reproducing κ = 0.417293962 validates the implementation) and then enlarge the search space to the CFKLT variational family (higher d, continuum combination) plus joint polynomial re-optimization under mpmath/scipy. First signal: reproduction of 0.417293962 to 9 digits (2-4 days); then whether coordinate ascent over the enlarged family gains ≥ 1e-6. Cheap falsification: if the variational optimum at θ = 4/7 coincides with the finite Feng combination (plausible ,  the length is long), the surface is enclosure-checked exhausted, itself a useful negative result quantifying why CFKLT only helps short mollifiers. Also directly tests transplanting θ_F = 17/33 (Bettin–Chandee–Radziwiłł generic length) into the Feng piece.
- key ref: arXiv:2508.11108; arXiv:1802.10521 §8

## Extend the inertia method to ξ'': first unconditional simple-on-line constant for the second derivative
*from Territory A: proportions of zeros of zeta on/near the critic*
- I=6 N=6 T=4 V=7 C=7 F=4 sat=2 signal: 1-2 days for the coefficient-growth criterion; 2-3 weeks for the full constant
- Remark 7.3 stops at ξ'. For ξ^(m), m ≥ 2, the zero density agrees with ξ to main order but the prime-side second moment (the analogue of Montgomery's F for ξ''-zeros) changes; under RH it is computed in the Farmer–Gonek–Lee line of work. Conrey 1983 gives unconditionally ≥ some proportion (79.874% is the ξ' value; the ξ'' value is higher and → 1 as m → ∞). Project: (a) derive the unconditional band-width-1 second-moment evaluation for ξ'' zeros by running the BGSTB-style Montgomery–Vaughan argument on −(ξ'')'/ξ''-coefficients (the Dirichlet-series coefficients are Λ-like with an extra polynomial-in-log factor, so Prop 5.6's diagonal method should apply ,  this is the falsifiable step); (b) feed the resulting 4/3-analogue constant through the inertia certificate to get the m = 2 constants. First signal: the coefficient-growth check Σ_{n≤x}|c(n)|² ≪ x^{1+o(1)} for the ξ'' log-derivative coefficients (the paper's own criterion for when the certificate is non-empty, which the Davenport–Heilbronn battery in the lab can also sanity-check as negative control ,  DH-type functions must fail it); computable in mpmath in a day. Risk: the mean-square constant may come out too small to beat Conrey 1983's Levinson-type ξ'' record, which would still be a clean measured negative.
- key ref: Anthropic 2026 preprint Remark 7.3 and §5; Conrey, J. Number Theory 16 (1983); Farmer-Gonek-Lee [FGL14]

## Harvest and extend: Jensen hyperbolicity degree bound 9.36x10^20 -> 9x10^24 and the Lean-checked corollary
*from Territory G: geometry of the Riemann xi function ,  de Bruij*
- I=4 N=5 T=7 V=10 C=3 F=9 sat=4 signal: 30 minutes for the harvest check; 1-2 weeks for a meaningful Lean skeleton
- GORTTW Corollary 1.3 (arXiv v3) derives 'J^{d,n} hyperbolic for all n >= 0, d <= 9.36x10^20' from Platt's RH_0(3.06x10^10). Inserting Platt-Trudgian's rigorous RH_0(3x10^12) (arXiv:2004.09765) through Theorem 1.2 gives d <= 9.0000...x10^24 immediately. Two deliverables: (1) check the published Advances version has not already made this substitution (30 minutes; if it has, this arm dies and only arm 2 survives); (2) formalize the deduction 'RH_0(T) and d <= floor(T)^2 implies hyperbolicity for all n' style finite corollary in Lean 4, taking RH_0(T) as a named hypothesis, making it the first kernel-checked statement in the Jensen-Polya program. The Lean arm needs only polynomial real-rootedness plus the GORTTW combinatorial deduction, not zeta analytics. First signal: the published-version check plus a Lean skeleton with the deduction stated and one lemma closed.
- key ref: arXiv:1910.01227 Corollary 1.3 + arXiv:2004.09765

---

# Coordinator selection (2026-08-17)

Eighty-seven candidates from eleven surveying arms, plus ten from an
independent shortlist drafted before any survey output was read
(scratchpad, preserved in the campaign record). Selection criteria:
diversity across territories, honest novelty probability after checking
this repository's own hunts (the surveys did not know `hunts/wide_search/`
existed and their top pick was already done there; see FAILURE_LEDGER
RF-D001), verifiability inside this lab's machinery, and a mix of grade
ceilings.

## Active portfolio

- **P-SG. Exact sine-Gram spectral moments and the conditional ladder.**
  From the m_4 = 13/4 verification episode (sine_gram/RESULTS.md): the
  exact finite-N CUE engine computes moments the literature stops short
  of. Deliverables: exact m_5(1), m_6(1) and beyond, lambda-polynomials,
  Christoffel-function pricing of the paper's HL*-type hypotheses.
- **P-FK. Bian's F_kappa coefficients: engine, closed form, tail.**
  The 2008 Rochester thesis (recovered in full, with its Mathematica
  source and exact coefficient grid) computes pair correlation for zeros
  of the kappa-th xi derivative under RH but cannot bound its tail for
  kappa >= 2; its 0.9544 / 0.9774 simple-zero constants rest on an
  eleven-term truncation. Reimplement exactly, extend the table, hunt
  the closed form for the stable diagonal, then a tail bound.
- **P-WIN. The cubic-certificate window.** The Aug 2026 paper's
  RH-conditional N_d >= 0.85082 uses a hand-picked window cos(8s/5);
  only the weight was optimized. Maximize 2 m_2(1,v) - m_3(1,v) over
  admissible windows; every delta lifts the record by delta/18.
- **P-WEIL. The truncated Weil form, enclosure-checked.** Replicate the
  2026 Connes-van Suijlekom-line Galerkin truncation independently,
  enclose smallest eigenvalues with Arb, fit the convergence law the
  February 2026 letter leaves open, and run the Davenport-Heilbronn
  control that the spectral literature never runs.
- **P-NB. Baez-Duarte distances with enclosures.** Exact Vasyunin Gram
  matrices, ball-arithmetic solves, the first rigorous d_N^2 values at
  scales the mid-2000s float work never reached, against the
  Bettin-Conrey-Farmer constant 0.0461914179.

## Reserves (next wave, in order)

1. Explicit psi(x) pipeline re-run with 2024-26 inputs through
   Johnston's transfer (high value, heavy; competition risk).
2. Suzuki screw-function operator numerics (fresh conjecture, zero
   published numerics).
3. First kernel-checked zero-density statement (Carlson/Bohr-Landau in
   Lean 4; high novelty, heavy formalization lift).
4. Interpolation of the Goldston-Lee-Schettler-Suriajaya PCC result:
   proportion simple as a function of partial pair-correlation support.
5. Inoue's small-gap test-function degree escalation.

## Killed at selection

- xi'-window variational optimum: laboratory prior art
  (FAILURE_LEDGER RF-D001).
- Scalar-moment LP over window certificates: prior art, two hunts
  (RF-D002).
- Everything graded literature_saturation >= 7 without a specific
  fresh input (mollifier-length ladder variants, generic moment
  recomputations).
