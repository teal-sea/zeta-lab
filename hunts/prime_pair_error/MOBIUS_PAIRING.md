# Mobius Prime Pairing (p = 2) Inside Sigma_2: Exact Identity, Complete Boundary, No Asymptotic Gain

Base: `a626c916a0082e59b2c4c0eca83035e948160d3e`. Date: 2026-09-20.
Scope: one concrete pairing only. No survey, no further construction after this mechanism.
Prior pairing work in this hunt: none (narrow grep over `hunts/prime_pair_error/*.md` for
pairing / opposite-sign / mu(pm) returns only unrelated sign mentions in arc-split and
residue notes). Earlier attempt produced no improved D_N bound; no finer analytic claim
is made here. The sign identity mu(2m) = -mu(m) for odd m is standard, not a discovery.

## 1. Setup and exact statement

Inherit N >= 4, K = floor(sqrt(N)), Y = N/K, M = floor(N/2), U = floor(sqrt(M)) and

D_N = S_smooth(N,K) + Sig1(N) + Sig2(N),  Sig2 = sum_{b=2..U} log b * M_b(N),

M_b(N) = sum_{a=U+1..V(b)} mu(a) w_N(ab),  V(b) = floor(M/b),

from FACTORIZATION_NEXT_STEP (sections 2-3) and FINAL_ACCEPTANCE (sections 2.5-2.6).
S_smooth and Sig1 are carried unchanged. The pairing acts inside each M_b only.

Theorem (exact p = 2 pairing with complete boundary). Fix N >= 4, b in [2, U],
V = V(b), F = floor(V/2), and general kernel w (either branch). With

P_b = sum_{m odd, U < m <= F} mu(m) [w(mb) - w(2mb)]        (paired differences),
T_b = sum_{m odd, max(U,F) < m <= V} mu(m) w(mb)          (upper-tail singles),
H_b = sum_{t <= U, U < 2t <= V} mu(2t) w(2tb)                (lower-head singles),
Z_b = sum_{m = 2t, U < t <= F, t even} mu(m) w(mb)           (identically zero),

M_b = P_b + T_b + H_b + Z_b holds exactly, and Z_b = 0 termwise.

Ranges: for N <= 11, Sig2 is empty (V(b) <= U for all b) and the identity is vacuous
0 = 0. For N >= 12 all sums are finite integer-indexed sums; the m <= Y versus m > Y
split inside w is over integers against rational Y, hence exact.

Proof. Partition (U, V] into disjoint sets: odd m <= V/2 (A_odd_low), odd m > V/2
(A_odd_high), m = 2t with t <= U (head), m = 2t with U < t <= V/2 and t odd
(mid-odd-half), m = 2t with U < t <= V/2 and t even (mid-even-half). Every even
m <= V has half t = m/2 <= V/2, so the three even classes exhaust the evens; the two
odd classes exhaust the odds. The map m |-> 2m is a bijection A_odd_low -> mid-odd-half
with inverse n |-> n/2 (when F < U the low class is empty and the tail is all odds of
(U, V]). For odd m: if m is squarefree, mu(2m) = -mu(m); if m is not
squarefree (odd squared prime divides m, hence divides 2m), mu(m) = mu(2m) = 0, so
mu(m) w(mb) + mu(2m) w(2mb) = mu(m)[w(mb) - w(2mb)] termwise in all cases. Summing the
paired classes gives P_b; the remaining classes give T_b, H_b, Z_b. On mid-even-half,
4 | m gives mu(m) = 0 termwise, so Z_b = 0. Q.E.D.

Preserved structure. b-side prime powers (log 4, log 8, log 9, ...) are untouched (b
is fixed by the pairing). a-side prime powers and squares contribute exact zeros via
mu = 0 on both sides of the identity (e.g. m = 9, 25, 49 in tails; m divisible by 4
in Z_b). p-divisibility (p = 2): m even in range is either head (partner below range),
a paired partner (m = 2t with t odd in range), or a proved zero (4 | m). Floor jumps
are inside w and never smoothed: the difference below keeps them exactly.

## 2. Paired weight difference (exact, under the proved ab > Y gate)

Section 4.2 of the prior note proves ab > Y for every Sig2 pair at every N >= 4
(small N checked by hand, gate asserted per-pair in the check script). Hence on Sig2,
w(mb) = 1 - floor(N/(mb)) and the paired difference is exactly

Delta(m, b) = w(mb) - w(2mb) = floor(N/(2mb)) - floor(N/(mb)) <= 0,

i.e. minus the integer floor drop. No Taylor expansion, no smoothing cost.

## 3. Complete quantitative bound versus the same baseline

Decisive arithmetic hypotheses: the sign flip mu(2m) = -mu(m) for odd m (exact,
elementary) and |mu| <= 1 for every estimate. No Mertens, PNT, or RH input.
Majorants used on both sides: |w(m)| <= N/m (both branches: N/m - 1, floor(N/m) - 1)
and, in the integer branch, |Delta(m,b)| <= N/(2mb) + 1 (the +1 is the exact
floor-jump cost per pair: floor(X) - floor(X/2) < X/2 + 1).

Per-b paired majorant:

|M_b| <= P^maj_b + T^maj_b + H^maj_b,
P^maj_b = sum_{odd U<m<=F} (N/(2mb) + 1),
T^maj_b = sum_{odd max(U,F)<m<=V} N/(mb),
H^maj_b = sum_{t<=U: U<2t<=V} N/(2tb).

Pre-pairing baseline with the same majorants: |M_b| <= B_b = sum_{U<a<=V} N/(ab).
Weighted totals: B(N) = sum_b log b * B_b, Ptot(N) = sum_b log b * (P^maj+T^maj+H^maj);
|Sig2| <= Ptot(N) versus |Sig2| <= B(N).

Order accounting (harmonic sums; measured confirmation in results_mobius_pairing.json).
P^maj main term is ~(1/4)(N/b) log(V/U): constant-factor drop against B_b's
(N/b) log(V/U) on the paired odds, because each pair now carries half weight N/(2mb)
over roughly half the odds. The +1 floor costs total O(N log^2 N); the tail T^maj is
Theta((N/b)) per b, Theta(N log^2 N) overall; the head H^maj is O(N log^2 N). Hence

Ptot(N) = c_p N log^3 N + O(N log^2 N),  B(N) = c_0 N log^3 N + O(N log^2 N),

with 0 < c_p < c_0 (measured Ptot/B = 0.60 at N = 10000, 0.69 at N = 1000,
0.87 at N = 100; exactly 1.0 at N <= 36 where every paired range is vacuous and the
identity reduces to an odd/even split with zero gain). The pairing buys a constant
factor on a non-sharp trivial majorant only. No exponent and no log power is improved.

The boundary pays back a fixed positive fraction of the term count but not the whole
leading constant: the measured unpaired-term fraction falls from 1.0 (N <= 36) to 0.43
at N = 10000, and tail+head majorants are
provably Theta(N log^2 N) in the same framework, i.e. one log power below the leading
N log^3 N term. So the obstruction is precise: within absolute-value majorants this
pairing cannot go below order N log^3 N, because the paired main term itself is
Theta(N log^3 N) from below (restrict b <= sqrt(U): odd-low harmonic range stays
~(1/4) log N wide, sum_b (log b)/b over that range is Theta(log^2 N)).

Combination with the principal term: D_N = S_smooth + Sig1 + sum_b log b (P_b+T_b+H_b)
exactly. S_smooth = N(log Y + H_K - 2 - gamma) is preserved untouched in closed form.
Sig1 is untouched and has no accepted bound (formal heuristic scale match only, per
FINAL_ACCEPTANCE section 4). Therefore the joint target
|S_smooth + Sig1 + Sig2| << N^{1/2+eps} is unmoved: the complete bound stays
|S_smooth + Sig1| (unpriced) + O(N log^3 N). For the D_N target, no gain survives.

## 4. Verdict on this mechanism

This is a proved obstruction to this particular p = 2 Sig2 pairing under
absolute-value majorants, not a failed estimate: the identity is exact, the majorant
comparison is apples-to-apples, and the paired majorant is pinned at Theta(N log^3 N)
from above and below. It is not a claim about any other pairing or method, and it
does not assert that any bound is false. Stop this construction here.

Smooth-diagnostic relation: the measured ratios |S_smooth + Sig1|/N^{3/4} (0.17 at
N = 400, 0.75 at N = 1000) concern Type I versus the smooth term only. The pairing
lives in Sig2 under disjoint hypotheses (exact sign flip plus |mu| <= 1), so that
diagnostic neither supports nor tests it; conversely the pairing leaves Sig1
untouched and cannot explain that diagnostic.

## 5. Evidence

`mobius_pairing_check.py` (repo .venv, N <= 10000, predicted < 60 s: ~20k exact
Fraction terms at the largest N): per-b exact rational identity M_b = P_b+T_b+H_b
(zero Fraction defect), ab > Y gate asserted per pair, mu(2m) = -mu(m) asserted on
odd squarefree m with mu(2m) = 0 on even m, square/nonsquare/prime-power mu spot
checks, missing-head/missing-tail/wrong-sign lesions (exact nonzero defects),
before/after per-b prime-log coefficient match, bound totals B(N) vs Ptot(N) and
unpaired-term fractions. Outputs `results_mobius_pairing.json`. Observed: all exact
checks pass with zero defect; all three lesions detected; Ptot/B from 1.0 (N <= 36,
vacuous) down to 0.60 at N = 10000; unpaired fraction from 1.0 down to 0.43;
small-N ratios reported as diagnostics only, never as asymptotics. Exact commands
and outputs recorded in section 6.

## 6. Run record

```
$ git status --short   # clean; git rev-parse HEAD -> a626c916a0082e59b2c4c0eca83035e948160d3e
$ .venv/bin/python hunts/prime_pair_error/mobius_pairing_check.py
  exit 0, elapsed_s 0.73 (estimate was < 60 s; numerical compute well under 2 min)
  N=100:   defect 0, gate_min 60,   Ptot/B 0.872, unpaired 0.778
  N=1000:  defect 0, gate_min 426,  Ptot/B 0.691, unpaired 0.514
  N=10000: defect 0, gate_min 4200, Ptot/B 0.600, unpaired 0.425
  lesions N=100: missing_head 11, missing_tail 5, wrong_sign 2 (all exact, nonzero)
  lesions N=400: missing_head 39, missing_tail 17, wrong_sign 20 (all exact, nonzero)
  mu sieve == sympy.mobius on 1..10000; divisor-sum identity to 200; mu spots
  (4,8,9,25,27,36,49,121 -> 0; 6 -> 1; 30 -> -1) all pass.
$ .venv/bin/python # Sig2 cross-check vs results_factorization_diagnostic.json
  all 11 table N (16..1000) agree to <= 1.5e-14 (float64 rounding).
$ .venv/bin/python -m pytest tests/test_prime_pair_residue.py -q -n0
  27 passed in 0.96s.
$ git add hunts/prime_pair_error/MOBIUS_PAIRING.md \
    hunts/prime_pair_error/mobius_pairing_check.py \
    hunts/prime_pair_error/results_mobius_pairing.json
$ git commit -m "prime_pair_error: exact p=2 Mobius pairing in Sigma_2 ..."
```
