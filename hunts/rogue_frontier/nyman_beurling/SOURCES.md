# Pinned primary sources

Every formula this study implements was read in at least one primary source
during the session of 2026-08-17; the two load-bearing statements (Vasyunin's
formula, the BCF asymptotic) were each pinned in two independent sources whose
normalizations were checked against each other symbol by symbol before any
code was written.

## 1. The criterion

- **Nyman 1950, Beurling 1955** (via the surveys below): RH iff
  chi_(0,1) lies in the closed span of {t -> {theta/t}, 0 < theta <= 1}
  in L^2(0, infty) (equivalent forms on L^2(0,1) exist).
- **Baez-Duarte, "A strengthening of the Nyman-Beurling criterion for the
  Riemann Hypothesis"**, Rend. Mat. Acc. Lincei 14 (2003) 5-11.
  arXiv: https://arxiv.org/abs/math/0202141
  Integer dilations suffice: RH iff d_N -> 0 with
  d_N^2 = inf_a || chi_(0,1) - sum_{k=1}^N a_k rho(1/(kt)) ||^2_{L^2(0,infty)},
  rho = fractional part. This is the d_N computed here.

## 2. Vasyunin's formula (the exact Gram entries)

- **V. I. Vasyunin, "On a biorthogonal system associated with the Riemann
  hypothesis"**, Algebra i Analiz 7 (1995); St. Petersburg Math. J. 7 (1996)
  405-419. Original statement (not directly consulted; quoted by the two
  sources below, whose statements agree).
- **S. Bettin, J. B. Conrey, "Period functions and cotangent sums"**,
  Algebra and Number Theory 7 (2013) 215-242, arXiv:1111.0931.
  https://arxiv.org/abs/1111.0931  (eq. (13) and surrounding text, read in
  the ar5iv rendering https://ar5iv.labs.arxiv.org/html/1111.0931 and the
  arXiv PDF). With the Vasyunin sum
      V(h/k) = sum_{m=1}^{k-1} {m h / k} cot(pi m / k),   gcd(h,k)=1,
  eq. (13) states, for coprime h, k >= 1:
      (1/(2 pi sqrt(hk))) Int_{-infty}^{infty} |zeta(1/2+it)|^2 (h/k)^{it}
          dt/(1/4+t^2)
        = (log 2pi - gamma)/2 * (1/h + 1/k)
          + ((k-h)/(2hk)) log(h/k)
          - (pi/(2hk)) ( V(h/k) + V(k/h) ).
  Also from the same paper: c_0(h/k) = -sum_{m=1}^{k-1} (m/k) cot(pi m h/k)
  and V(h/k) = -c_0(hbar/k), h hbar == 1 (mod k); the reciprocity formula
  for c_0 is theirs and is not used here.
- **B. Landreau, F. Richard, "Le critere de Beurling et Nyman pour
  l'hypothese de Riemann: aspects numeriques"**, Experiment. Math. 11 (2002)
  349-360. PDF: https://projecteuclid.org/journals/experimental-mathematics/volume-11/issue-3/Le-crit%C3%A8re-de-Beurling-et-Nyman-pour-lhypoth%C3%A8se-de-Riemann/em/1057777427.pdf
  Their Theoreme 2.1 (attributed to Vasyunin) gives, for e_n(t) = {1/(nt)},
  omega = gcd(n,m), n = omega n0, m = omega m0:
      <e_n, e_m> = (log 2pi - gamma)/2 * (1/n + 1/m)
                   + ((m-n)/(2mn)) log(n/m)
                   - (pi omega/(2nm)) sum_{j=1}^{n0-1} {j m0/n0} cot(pi j/n0)
                   - (pi omega/(2mn)) sum_{j=1}^{m0-1} {j n0/m0} cot(pi j/m0).
  Cross-check performed: dividing the Bettin-Conrey coprime statement by
  omega and simplifying reproduces the Landreau-Richard statement exactly
  (the mixed-argument form used in the code). Mellin route from |zeta|^2
  integral to the inner product: <e_j, e_k> equals the eq. (13) integral by
  Mellin-Plancherel with Mellin(e_k)(s) = -zeta(s) k^{-s}/s on Re s = 1/2.

## 3. The target inner products (derived, then validated)

  b_k = <chi_(0,1), e_k> = (1 - gamma + log k)/k.
  Derivation: substitute u = 1/(kt), use int_1^infty {u}/u^2 du = 1 - gamma
  and int_{1/k}^1 du/u = log k. Landreau-Richard state the equivalent
  <chi, g_theta> = theta(1 - gamma - log theta) for theta = 1/k (their
  section 2). Validated here by direct quadrature (see RESULTS.md).
  Special case: <e_1, e_1> = log 2pi - gamma, so
  d_1^2 = 1 - (1-gamma)^2/(log 2pi - gamma) = 0.85821205139551088467...
  (closed form, digits computed at 40 dps in this session).

## 4. The conjectured asymptotic and its status

- **Baez-Duarte, Balazard, Landreau, Saias, "Notes sur la fonction zeta de
  Riemann, 3"**, Adv. Math. 149 (2000) 130-144: unconditional lower bound
  liminf d_N^2 log N >= sum_{Re rho = 1/2} 1/|rho|^2 (distinct zeros), and
  the conjecture d_N^2 ~ C/log N.
- **J.-F. Burnol** (cited in BCF as [Bur]): improved lower bound
  liminf d_N^2 log N >= sum_{Re rho = 1/2} m(rho)^2/|rho|^2.
- **S. Bettin, J. B. Conrey, D. W. Farmer, "An optimal choice of Dirichlet
  polynomials for the Nyman-Beurling criterion"**, arXiv:1211.5191,
  Proc. Steklov Inst. Math. 2013. https://arxiv.org/abs/1211.5191
  Theorem 1: if RH holds and sum_{|Im rho| <= T} 1/|zeta'(rho)|^2 << T^{3/2-delta}
  for some delta > 0, then the smoothed Mobius choice
      V_N(s) = sum_{n<=N} (1 - log n/log N) mu(n) n^{-s}
  achieves (1/2pi) Int |1 - zeta V_N(1/2+it)|^2 dt/(1/4+t^2)
      = (1/log N) sum_rho 1/|rho|^2 + O(1/log^2 N),
  hence d_N^2 ~ (2 + gamma - log 4pi)/log N if all zeros are simple
  (sum over distinct zeros; under RH, sum_rho 1/|rho|^2 with rho and 1-rho
  paired equals 2 + gamma - log 4pi = 0.04619141793...). The displayed error
  term O(1/log^2 N) is read directly from the end of their proof of
  Theorem 1 ("moving the line of integration in (7) ... the integral is
  equal to (1/log N) sum_rho 1/|rho|^2 + O(1/log^2 N)"). So the predicted
  next-order shape tested in this study is
      d_N^2 log N = C + O(1/log N),  C = 2 + gamma - log 4pi.
  Note their theorem is an upper-bound statement about the specific vector
  V_N; the true minimizer satisfies d_N^2 <= that value, and the Burnol
  bound pins the constant from below.

## 5. Prior numerical values (validation targets)

- **Landreau-Richard 2002** (same PDF as above), the only substantial
  published float computation found: d_n by Gram-Schmidt with exact
  Vasyunin entries up to n = 20000 (confirmed by conjugate gradient and QR
  up to n = 10000). No table of d_n digits is printed; the paper gives
  (a) Figure 1: d_n decreasing from ~0.10 to ~0.066 over n = 1..20000, with
      the window [0.07, 0.08] crossed during n ~ 2000..10000 (Figure 2);
  (b) the least-squares fit d_n ~ a_N/sqrt(log n) with a_N ~= 0.21377 at
      N = 20000, against sqrt(2+gamma-log 4pi) = 0.21492 (their section 3);
  (c) Conjecture 3.1 restated: d_n^2 ~ (2+gamma-log 4pi)/log n.
  These are the external anchors reproduced in RESULTS.md.
- **Maslanka's mid-2000s numerics** (searched 2026-08-17): what was located
  concerns the Riesz/Baez-Duarte c_k moment criterion, not d_N; no d_N table
  found there, so no Maslanka validation target is used.
- **Repo-internal**: `data/baez_duarte_gram_N50_dps50.json` and
  `zeta.criteria.baez_duarte_d2` compute the BBLS basis
  A_k = {1/(kx)} - (1/k){1/x} on L^2(0,1), k = 2..N, target 1. That is a
  different quadratic form with the same conjectured d_N^2 log N limit; it
  is compared, not equated, in RESULTS.md.

## 6. Constants

  gamma = 0.5772156649015328606...,  log 2pi = 1.8378770664093454836...,
  C = 2 + gamma - log 4pi = 0.0461914179322420676286204958134...
  (matches `zeta.criteria.BD_CONSTANT`, itself pinned by the repo's tests
  as 2*lambda_1 of Li's criterion).
