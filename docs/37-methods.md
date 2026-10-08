# 37. Methods: the reusable identities, lemmas, controls and techniques, by theme

This is the cross-hunt index of method. `hunts/README.md` logs each hunt by outcome;
nothing there says which trick a later hunt could pick up. This file does. It was built
by a retroactive sweep of every hunt directory (99 hunts, about 775k words of record),
and it is meant to be kept current: a hunt that produces something on the list below
adds an entry here in the same change.

## What earns an entry

An entry is a technique with a stated scope and a recorded provenance: an exact
identity, a proved lemma, a construction, a control that discriminated a real fault, a
computational technique that a second hunt reached for, or an obstruction that closes a
route so nobody walks it again. The bar is one of:

- proved: ordinary derivation with an independent review, an exact finite check, an enclosure, or a kernel check; or
- reused: consumed by a second hunt, a `docs/` document, `zeta/`, `tests/` or the Lean arm.

A larger computation is not a method. A number is not a method. A heuristic that was
measured once and never carried is recorded under "Seen and not admitted" so the next
sweep does not re-judge it; it is not an entry.

## How to read an entry

Every entry carries kind, originating hunt, and the grade as the hunt's own record
states it. This index upgrades nothing: an ordinary derivation stays an ordinary
derivation, a measured number stays measured, and a hunt entry is still a hunt entry
(nothing under `hunts/` is a result). The certainty ladder in `AGENTS.md` governs the
words: measured, hardened or enclosure-carrying, kernel-checked. Prior art is reported
as the hunt reported it: cited, searched-and-found, searched-and-absent, or unsearched.
"Unsearched" is a statement about the record, not a novelty claim.

Statements are condensed from the hunt's RESULTS and theorem files by a reader, not
copied; the evidence line points at the section that carries the actual proof or table.
Read that before using the method.

## Adding an entry

Same fields, same order: name; kind, hunt, grade; statement; Evidence; Prior art; Reused
in; Why it travels. Put it under the theme it belongs to, or open a theme if none fits.
Grade it with the hunt's words. The reserved word for `zeta/rigor.py` and the Lean arm
stays out of this file. No em dashes.

## Themes

- **Prime pairs and the circle method** (22). Shifted prime correlations at a modulus,
  the centered circle-method budget, character-twisted pair sums, exceptional-zero
  corrections and the controls that kept the fits honest.
- **Factorial and LP certificates for psi(N)** (16). Chebyshev-type factorial
  certificates for psi(N) as linear programs: the quotient relaxation, its floor, exact
  duals, repair budgets and the rank and transport obstructions.
- **Weil positivity, Gram forms and kernels** (55). Weil-form truncations, window
  optima, incidence laws, cell-table and interval certificates for kernel inequalities,
  and the ceilings on what out-of-band positivity can buy.
- **Higher xi derivatives and moments** (13). Exact resolvent identities for xi
  derivatives, resummed Lambda-convolutions, mean-value inputs and the moment
  obstructions to counting simple zeros.
- **Heat flow and de Bruijn-Newman constants** (14). Backward heat flow of xi-type
  functions: landing times as lower bounds, contour and winding instruments that refuse
  rather than round, and the calibrations that fix the frame.
- **Epstein zeta, precision and zero counting** (7). Precision floors for the completed
  Epstein zeta, what argument-principle box counts can and cannot discriminate, and the
  rightmost-zero wall for the prime zeta.
- **Erdos #126 and S-unit equations** (17). Equivalent forms of the problem,
  residue-class and deletion lemmas, reductions to S-unit equations, and the barriers
  that show which relaxations are exact.
- **Lean arm: formalised elementary number theory** (5). Kernel-checked Mertens bands,
  Abel summation by direct induction, and the transfer patterns that make an aggregate
  inequality formalisable.
- **Certificates, verifiers and exact arithmetic** (18). Exact rational acceptance of
  published witnesses, fault-injection ladders for verifiers, and the controls that
  separate an instrument reading from a mathematical claim.
- **Zero-free half-planes, L(1, chi) and class numbers** (2). An explicit Littlewood
  bound from a fixed zero-free half-plane, and the exact sieve that spends it on
  complete class-number lists.
- **Primes in short intervals and explicit formulas** (1). Smoothed explicit formulas
  with closed-form sums over zeros split at a verified height; threshold exponents for
  primes between powers under a zero-free half-plane.
- **Seen and not admitted** (38). Surfaced by the sweep, below the bar for now.

Totals: 170 entries from 62 hunts. Kinds: identity 21, lemma 43, bound 12, construction
15, calibration 7, computational 16, control 35, obstruction 21.

## Prime pairs and the circle method

Shifted prime correlations at a modulus, the centered circle-method budget,
character-twisted pair sums, exceptional-zero corrections and the controls that kept the
fits honest.

- identity: Modulus-q four-piece decomposition of the prime-pair count
  (`prime_pair_error`)
- identity: Mod-3 character antisymmetry and the Wronskian reduction of the
  character-weighted pair sum (`prime_pair_error`)
- identity: q=1 mixed moment is a completed square of prime-counting remainders
  (`prime_pair_error`)
- identity: Exact p=2 Mobius pairing partition inside a hyperbola block
  (`prime_pair_error`)
- lemma: Theorem A: double-zero kernel bound for the Wronskian via Perron with a moving
  weight (`prime_pair_error`)
- lemma: Theorem B: character-weighted Cauchy-Schwarz plus Landau pole gives an
  unconditional Omega bound (`prime_pair_error`)
- lemma: Signed exceptional-correction bridge from a corrected pair energy to the
  prime-counting remainder (`prime_pair_error`)
- lemma: Bounded-order Bonferroni divisor approximant to the sieve indicator with
  explicit error (`prime_pair_error`)
- bound: Centered circle-method budget for E(N): geometric leakage and large-denominator
  mixed-moment bounds (`prime_pair_error`)
- bound: Farey-block residual fourth-moment baseline by bounded overlap
  (`prime_pair_error`)
- construction: Explicit exceptional-zero correction to the pair count with exact
  residue-average identities (`prime_pair_error`)
- construction: Lifted balanced-seed factorial certificate for psi(N)
  (`prime_pair_error`)
- calibration: Asymptotic of the character-twisted singular-series sum H_chi(N) and its
  constant c_H (`prime_pair_error`)
- calibration: Replication convention for CHHL Table 1: truncate, do not round
  (`prime_pair_error`)
- control: Freeze-then-test protocol with derived coefficients and post-hoc slope
  diagnostic (`prime_pair_error`)
- control: Davenport-Heilbronn battery for pair energies via the periodic-sequence
  singular series (`prime_pair_error`)
- control: Counterfeit greedy-deficit sequence: falsifier for coarse-property arguments
  (`prime_pair_error`)
- control: Exact-rational planted-lesion discrimination with three evidence classes
  (`prime_pair_error`)
- obstruction: Exact scale relation from the factorial identity, and the zeta-multiplier
  obstruction to contraction (`prime_pair_error`)
- obstruction: Rudin-Shapiro-type polynomial obstruction to minor-arc fourth-moment
  saving from global norms (`prime_pair_error`)
- obstruction: LP floor for floor-sum prime certificates, its dual, and the rough-spike
  lemma (`prime_pair_error`)
- obstruction: Nonnegative squared-term obstruction to an integrated
  Barban-Davenport-Halberstam theorem at N^{1+eps} (`prime_pair_error`)

### Modulus-q four-piece decomposition of the prime-pair count

identity | `hunts/prime_pair_error/` | grade: exact identity, numerically pinned (I3 at
every k<=5000 for q=1,2,3,5,30,210; closed form vs general code to 2e-6); the
corrections built on it are measured

Fix q, phi=phi(q), w=q/phi, M_q(n)=w on (n,q)=1 else 0, and split Lambda on reduced
classes as M_q+delta'. For 1<=k<=N, psi_2(N,k)=A_q+L_q+X_q+D_q exactly, where A_q=sum
M(n)M(n+k)=S_q(k)(N-k)+rho_q(N,k) with S_q(k)=q nu_q(k)/phi^2=prod_{p|q} sigma_p(k)
(sigma_p=p/(p-1) if p|k, else p(p-2)/(p-1)^2) and |rho_q|<=w^2 nu_q(k); L_q is linear in
psi(x;q,b) at x=N, k, N-k only (I4); X_q is the O(log^2 N) sum over pairs containing a
power of a prime dividing q; D_q is the centered-correlation remainder. The singular
series factors S(k)=S_q(k)S^(q)(k) at every k including odd k (I3). At q=1 the endpoint
term is R(N)+R(N-k)-R(k), R=psi-x. Under the one heuristic (H_q) the predicted signed
part is c_q=S^(q)(k)[rho_q+L_q]+X_q with every coefficient 1.

Evidence: RESULTS.md Section 8 'The decomposition at a modulus q' (lines 232-288, items
I1-I6); Section 9 lines 290-332; residue.py FROZEN table;
tests/test_prime_pair_residue.py
Prior art: searched-and-found: Bogomolny-Keating (arXiv:1307.6010) finite products over
primes dividing the modulus are (I3); BHMS (Mathematika 2019) is the sum-side analogue;
Korevaar-te Riele (Math. Comp. 2010) is the q=1 small-k average. Hunt states 'not
claimed new'.
Reused in: residue.py (q=1,3,30 corrections, q=210 diagnostic); RESULTS.md Section 12
statement (T); hunts/README.md summary
Why it travels: Any shifted correlation of an arithmetic function can be split into
periodic baseline, endpoint prime-count terms, exceptional pairs and a centered
remainder at any modulus, with the singular series factoring cleanly.

### Mod-3 character antisymmetry and the Wronskian reduction of the character-weighted pair sum

identity | `hunts/prime_pair_error/` | grade: exact identities checked on Gaussian
random weights at N=7,50,301,1000 to 5e-12 and on Lambda; reviewed written proof
(REFEREE.md), not kernel-checked

For chi the non-principal character mod 3 and 3 dividing neither n nor m,
chi(m-n)=(chi(n)-chi(m))/2 (E0); this is special to modulus 3. Hence for any weight f
supported off multiples of 3, with A,B the prefix sums on the classes 1,2 mod 3, P=A-B,
r=A+B-n: sum_{n<m<=N} f(n)f(m)chi(m-n) = sum_{j=0}^{N-1}P(j) - ((N-1)/2)P(N) + W(N),
W(N)=(1/2)sum_n[P(n-1)dr(n)-r(n-1)dP(n)] (E1). Pairs with a power of 3 give
X_chi(N)=(log 3)sum_{3^j<=N}[P(N)-2P(3^j)] (E2). With T(N)=sum_k
chi(k)[psi_2(N,k)-S(k)(N-k)], I(N)=sum_{j<N}P(j)-(N/2)P(N), H_chi=sum chi(k)S(k)(N-k):
T-I = W + P(N)/2 + X_chi - H_chi (E3). Partial summation gives W = R(N)P(N)/2 - J(N) +
Q(N), J(N)=sum_{m<=N}Lambda(m)chi(m)(psi(m)-m), |Q|=O(N log N) (E4).

Evidence: RESULTS.md Section 14 lines 532-583 (E0-E3), Section 16 lines 629-658 (E4-E5);
REFEREE.md Section 1 lines 34-60 (verified, corrects the symmetric identity's missing
P(N)); wronskian.py; tests section 5
Prior art: searched-and-absent: web search 2026-09-06 for a character-weighted
difference-side pair sum returned nothing; BHMS is the sum side; hunt claims no novelty
Reused in: RESULTS.md Sections 17-18 (Theorems A and B); THEOREM_B_SEQUENCE.md;
FAREY_BASELINE_REPAIR.md Appendix B
Why it travels: Turns any antisymmetric character-weighted pair correlation into a
Wronskian of two prime-counting remainders plus explicit one-point terms; the
random-weight check is a generic test for such identities.

### q=1 mixed moment is a completed square of prime-counting remainders

identity | `hunts/prime_pair_error/` | grade: ordinary derivation, independent model
review 'no substantive defect'; identity pinned on arbitrary weights

With K_N the Dirichlet kernel, F_N the von Mangoldt exponential sum and
Delta(t)=psi(t)-t at integers: T_N := int_T |K_N|^2|F_N-K_N|^2 = sum_{t=1}^N Delta(t)^2
+ sum_{t=1}^{N-1}[Delta(N)-Delta(t)]^2 = ((N+1)/2)Delta(N)^2 + 2
sum_{t<N}[Delta(t)-Delta(N)/2]^2 (29), because the coefficient of e(m beta) in
K_N(F_N-K_N) is Delta(m-1) for 2<=m<=N+1 and Delta(N)-Delta(m-N-1) for N+2<=m<=2N. The
q=1 arc integral U_1 differs from T_N by at most (N^2/4Q^2) sum(Lambda(n)-1)^2 << N^2 L
(30). Consequence: the sufficient bound (31) sum Delta(t)^2 << N^{2+eps} implies
Delta(N)=O(N^{1/2+eps}), i.e. the q=1 component of any centered circle-method budget for
E(N) contains the RH-strength remainder; Siegel-Walfisz at q=1 yields only T_N << N^3
L^{-2H}.

Evidence: UPPER_BOUND.md Section 7 lines 476-540 (eqs 29-31); Section 8 review note
(convolution and completed square checked on 640 exact signed-integer-weight examples,
N<=64); tests/test_prime_pair_upper_bound.py
Prior art: unsearched
Reused in: RESULTS.md 'The doors' rank 1; RANK3_SCOPE.md, RANK3_Z_COMPONENT.md (Z_(1) >=
3U_1^2/(2N^3+N)); LOCALIZED_MIXED_ENERGY.md; FRONTIER_2026_09_12.md
Why it travels: Exhibits, for any centered exponential-sum energy, exactly where the
one-point remainder hides; the Parseval-plus-complete-the-square step works for any
coefficient sequence a_n-1.

### Exact p=2 Mobius pairing partition inside a hyperbola block

identity | `hunts/prime_pair_error/` | grade: ordinary reviewed derivation plus Class A
exact rational checks at 20 cutoffs to N=10000; no asymptotic gain; ATTEMPT_UNRESOLVED

For N>=4, K=floor(sqrt N), M=floor(N/2), U=floor(sqrt M), b in [2,U], V=floor(M/b),
F=floor(V/2) and any kernel w: M_b=sum_{U<a<=V}mu(a)w(ab) equals P_b+T_b+H_b+Z_b
exactly, with P_b=sum_{m odd, U<m<=F}mu(m)[w(mb)-w(2mb)] (paired differences via the
bijection m -> 2m and mu(2m)=-mu(m) for odd squarefree m), T_b=sum_{m odd,
max(U,F)<m<=V}mu(m)w(mb), H_b=sum_{t<=U, U<2t<=V}mu(2t)w(2tb), and Z_b (m=2t, t even)
identically zero since 4|m. Under the gate ab>Y=N/K (proved for every Sigma_2 pair,
N>=12), w(mb)=1-floor(N/(mb)) and the paired difference
Delta(m,b)=floor(N/(2mb))-floor(N/(mb)) <= 0. Under absolute-value majorants
B(N)=(1/48)N log^3 N+O(N log^2 N) and Ptot=(1/192)N log^3 N+O(N log^2 N): the majorant
is pinned Theta(N log^3 N) from both sides, so this explicit majorant cannot improve,
while signed pairing, more primes, or a Sig1 bound remain open.

Evidence: MOBIUS_PAIRING.md Sections 1-2 lines 10-70 (theorem and proof), Section 5;
MOBIUS_PAIRING_REVIEW.md Sections 3-4; RESULTS.md Fourth pass lines 926-972
Prior art: cited as standard: mu(2m)=-mu(m); no prior pairing work found in the hunt
(narrow grep only)
Reused in: FINAL_ACCEPTANCE.md; RESULTS.md Fourth pass 'Doors of this mechanism'
Why it travels: A general bookkeeping identity for pairing a Mobius-weighted sum with
its 2-multiples, with the head/tail boundary written out exactly; applies to any kernel
w.

### Theorem A: double-zero kernel bound for the Wronskian via Perron with a moving weight

lemma | `hunts/prime_pair_error/` | grade: ordinary derivation, independently reviewed
written proof (REFEREE.md); not kernel-checked

Let Theta, Theta_chi be the suprema of real parts of zeros of zeta and of L(s,chi_3).
Then W(N) << N^{Theta+Theta_chi}(log N)^4 unconditionally, so
T(N)=I(N)+O(N^{Theta+Theta_chi}log^4 N), and O(N log^4 N) under RH for both. Mechanism:
insert the truncated explicit formula (T=N) for R(m) into J(N); for each zeta zero rho
apply Perron to -L'/L(w-rho,chi) with c=1+beta+1/log N and a height V_rho in [2N,2N+1]
chosen at distance >= a/log(2N) from every L-zero ordinate (measure argument via O(log)
zeros per unit interval); shift to Re w=-delta with delta in {1/8,3/16} avoiding the
trivial zero; the residues give A_rho(N) = -sum_{rho' in D_rho} N^{rho+rho'}/(rho+rho')
+ O(N^beta log^2 N) on slanted cutoff sets D_rho. The exact J-RP/2 kernel is
K(rho,rho')=(rho'-rho)/(2 rho rho'(rho+rho')) and sum |K| over the same sets is O(log^4
N), the central bin |gamma+gamma'|<1 handled by |rho+rho'|>=beta>>1/log N from the
classical zero-free region. No simplicity, distinct-ordinate or attained-supremum
assumption.

Evidence: RESULTS.md Section 17 lines 674-801 (Theorem A, Steps 0-3, F1-F5); REFEREE.md
Sections 2-3 lines 101-256 (R1-R6, verdict 'proof valid after specified repair')
Prior art: searched-and-found for comparison only: BHMS Theorem 2 (Mathematika 65, 2019)
sum-side with Gamma-factor kernels; Fujii 1991; Languasco-Zaccagnini 2012/2015;
Goldston-Yang arXiv:1601.06902. No difference-side statement found.
Reused in: RESULTS.md Section 18 (Theorem B uses A for the transfer); REFEREE.md Section
7
Why it travels: The good-height selection, slanted cutoff sets and the near-diagonal
handling via the zero-free region apply to any bilinear sum over zeros of two
L-functions with 1/(rho(rho+rho')) type weights.

### Theorem B: character-weighted Cauchy-Schwarz plus Landau pole gives an unconditional Omega bound

lemma | `hunts/prime_pair_error/` | grade: ordinary derivation, independently reviewed
written proof; not kernel-checked

E(N) >= 2T(N)^2/N by Cauchy-Schwarz since sum chi(k)^2 <= N. For Re s>1, int_1^inf
I(x)x^{-s-2}dx = -(L'/L)(s,chi)(1-s)/(2s(s+1)) with
I(x)=sum_{m<=x}Lambda(m)chi(m)(x/2-m); a zero rho' of multiplicity h gives residue
h(rho'-1)/(2rho'(rho'+1)) != 0, so absolute convergence implies I(x) is not
O(x^{1+Theta_chi-eps'}) (only 'absolute convergence implies analyticity', no sign
condition). With eta=min(eps,1-Theta)/2 and Theorem A, along an unbounded sequence
|T(N)|>=N^{1+Theta_chi-eta}/2 and E(N)>=N^{1+2Theta_chi-eps}/2. Case Theta_chi<=Theta is
CHHL Theorem 2. Conclusion is along a sequence, not eventual; sequence may depend on
eps.

Evidence: RESULTS.md Section 18 lines 803-852; REFEREE.md Section 4 lines 258-321
('Proof verified'); THEOREM_B_SEQUENCE.md Section 2 (why it is nonconstructive:
obstructions A and B)
Prior art: cited: CHHL Theorem 2 (same mechanism with weight 1); Ingham ch. V /
Montgomery-Vaughan 15.1 for the Landau direction used
Reused in: REFEREE.md Section 7 strongest surviving statement; FRONTIER_2026_09_12.md
table ('settled nonconstructive Theorem B is unaffected')
Why it travels: Replaces the k-mean weight 1 by any character; RESULTS Section 18 notes
the general-modulus version needs only a fresh main term since the bilinear
antisymmetric form is handled pairwise by Theorem A.

### Signed exceptional-correction bridge from a corrected pair energy to the prime-counting remainder

lemma | `hunts/prime_pair_error/` | grade: handwritten deduction; the mean criterion and
parameter substitution independently re-derived in FRONTIER_INDEPENDENT_REVIEW.md; not
kernel-checked

With r_N(h)=psi_2(N,h)-(N-h)S(h), an exact correction C_N(h) (zero when no exceptional
zero is assigned), and E_corr(N)=2 sum_{h<=N}|r_N(h)-C_N(h)|^2: from CHHL's identity
psi(N)^2 = d_N + 2 sum_h psi_2(N,h) and the singular-series first moment 2 sum (N-h)S(h)
= N^2+O(N log N), Cauchy-Schwarz on the corrected vector only gives |psi(N)-N| <=
sqrt(2E_corr(N)/N) + (2/N)|sum_h C_N(h)| + O(log N) (18), using psi(N)+N>=N. The signed
first moment satisfies |sum_h C_N(h)| << N(log N)^{2/5} (2) by a divisor expansion of
S_*(h) with the parity factor retained and cancellation of the nonprincipal character
over complete periods. Hence E_corr << N^{2+eps} for every eps implies RH (one direction
only; the two-way scalar criterion is RH iff M_N=2|sum_h(r_N-C_N)|^2/N << N^{2+eps}).

Evidence: CORRECTED_RH_BRIDGE.md Sections 1-5 lines 40-330 (eqs 2, 3, 8-9, 17-20);
FRONTIER_2026_09_12.md lines 28-52 (two-way scalar criterion);
FRONTIER_INDEPENDENT_REVIEW.md ('Mean criterion epsilon quantifiers: Passed';
signed-mean equivalence reviewed)
Prior art: cited: CHHL Section 3 identity and first moment; Tao-Teraevaeinen Definition
2.1 for the exceptional data
Reused in: SIGNED_MEAN_RENEWAL.md Section 2; FRONTIER_2026_09_12.md;
ENDPOINT_BOUND_REVIEW.md dependency 4; S8_CONTROL.md
Why it travels: Shows how to keep an explicit exceptional-zero correction inside a
Cauchy-Schwarz bridge without bounding its second moment; the same shape applies to any
corrected correlation energy.

### Bounded-order Bonferroni divisor approximant to the sieve indicator with explicit error

lemma | `hunts/prime_pair_error/` | grade: ordinary derivation, independently reviewed
(Codex review 2026-09-09, PASS; finite illustration corrected 2026-09-11)

For P=prod_{p<Z}p, even m, B_m(n)=sum_{d|P, d|n, omega(d)<=m} mu(d): B_m(n)=1 if no
prime below Z divides n, and B_m(n)=binom(s-1,m) otherwise (s the number of such
primes), so 0 <= B_m(n)-1_{s=0} <= binom(s,m+1) (4). Hence
sum_{n<=N}|B_m(n)-1_{(n,P)=1}| <= sum_{omega(d)=m+1} floor(N/d) <= N H_Z^{m+1}/(m+1)!,
H_Z=sum_{p<Z}1/p (5), with no accumulated O(D_0) remainder, every coefficient in
{0,+-1}, every divisor below D_0=Z^m. With m=2ceil(sqrt(log N)) and Z=exp((log
N)^{1/10}) this is N exp(-c sqrt(log N) log log N). Retuning at the endpoint kappa=1/2
requires m+1=ceil((2c/kappa)l^kappa/log l) and Mertens for H_Z rather than H_Z<=1+log Z;
ENDPOINT_SHARP_REVIEW found the document's finite retuned-m table too small by exactly 2
at every row while confirming the asymptotic (A).

Evidence: ENDPOINT_BOUND.md Section 2 lines 138-190 (eqs 4-6); ENDPOINT_BOUND_REVIEW.md
(PASS); ENDPOINT_SHARP.md Section 2.1; ENDPOINT_SHARP_REVIEW.md Item 1 (asymptotic
confirmed, finite table defective)
Prior art: unsearched (Bonferroni/Brun truncation is textbook; the explicit
prefix-uniform error form is the lab's)
Reused in: ENDPOINT_SHARP.md, ENDPOINT_HALF.md, ARC_SPLIT_BUDGET.md (later dropped from
the chain as unnecessary)
Why it travels: A drop-in replacement for the sieve indicator whenever a sum over
divisors of bounded length is needed with an error uniform over all prefixes and no
boundary remainder.

### Centered circle-method budget for E(N): geometric leakage and large-denominator mixed-moment bounds

bound | `hunts/prime_pair_error/` | grade: ordinary derivation, independent model review
2026-09-06 found no substantive defect; finite identity tests only

Arcs I_{q,a}={|alpha-a/q|<=Q/(qN)}, q<=Q, 2Q^2<N (disjoint, measure <=2Q^2/N). With
A_Q=sum|P_{q,a}|^2 1_{I_{q,a}}, P_{q,a}=(mu(q)/phi(q))K_N(alpha-a/q), H_Q=V_Q-A_Q>=0 and
w(Q)=max_{q<=Q}q/phi(q): ||H_Q||_2^2 << N^3 Q^{-2} log(2Q) w(Q)^2 (13), proved by int
H_Q << N (14) times ||H_Q||_inf << w(Q)^2((N^2/Q^2)log(2Q)+N) from dyadic
center-counting sum ||alpha-x||^{-2} << delta^{-2}+R^2/delta. Total: E(N) <=
4M_Q+4I_Q+4||H_Q||_2^2+2D_tail(N,Q) (12), and at Q=floor(sqrt N/3) E(N) <=
4M_Q+4I_Q+O(N^2L^3) (16). Splitting M_Q into U_Q=sum int|P|^2|R|^2 and Z_Q=sum int|R|^4
gives E(N)<=32U_Q+8Z_Q+4I_Q+O(N^2L^3) (23); the large sieve at unshifted centers in
dyadic blocks R<q<=2R gives U_{q>R_0} << w(Q)^2 N^3 L/R_0^2 (26), hence O(N^2L^5) at
R_0=Q/L. The tail identity |sqrt E - sqrt J_ms(N,z)| <= sqrt D_tail(N,z) with D_tail <<
N^3/z^2 from GHN Theorem 2 (doubled, exact tail sum T(z)) is (4)-(6).

Evidence: UPPER_BOUND.md Sections 2-6 lines 101-474 (eqs 4-6, 12-13, 16, 23-27); Section
8 table; ARC_SPLIT_BUDGET_REVIEW.md Item 1 (identities confirmed)
Prior art: cited: CHHL Sections 3-4 (centered setup), Goldston-Hunts-Ngotiaoco Theorem 2
(tail), Montgomery-Vaughan MNT II Theorems 17.1 and 19.4 (Vaughan, large sieve)
Reused in: MINOR_LEVEL_SETS.md, CENTERED_DISPERSION.md, ARITHMETIC_FOURTH.md, RANK3_*
series, ARC_SPLIT_BUDGET.md, LOCALIZED_MIXED_ENERGY.md, RESULTS.md 'The doors'
Why it travels: A fully itemised difference-side budget with every component's exponent,
reusable as the starting ledger for any sharp-cutoff pair-correlation mean square.

### Farey-block residual fourth-moment baseline by bounded overlap

bound | `hunts/prime_pair_error/` | grade: ordinary derivation, independently reviewed;
not kernel-checked

For integer N>=16, 1<=Q<=N^{2/5}, reduced a/q with Q<=q<2Q and q<=sqrt N, and
R_{q,a}(theta)=F_N(a/q+theta)-(mu(q)/phi(q))K_N(theta): sum_q sum_a^* int_{|theta|<=1/(q
sqrt N)} |R_{q,a}|^2 << N log N (E) and sum sum int |R_{q,a}|^4 << N^3 (log N)^9/Q (A).
Proof of (E): arcs in one block have radius <=1/(Q sqrt N) and centers
1/(4Q^2)-separated, so any point is covered at most 9 times; Parseval gives the F part
<< NL, and sum_{q in block} mu(q)^2/phi(q) << 1 (dyadic reciprocal-totient bound (C))
gives the model part << N. (A) follows from (E) times the supremum bound |R|^2 << N^2
L^8/Q from Vaughan with all three terms O(N/sqrt Q) for Q<=N^{2/5}. Supersedes a faulty
AP-variance/character-orthogonality argument; explicitly not an optimality or closure
statement.

Evidence: FAREY_BASELINE_REPAIR.md Sections 1-3 lines 19-133 (eqs A-E); Section 4 (exact
corrections to the AP-variance argument); FRONTIER_INDEPENDENT_REVIEW.md Section 1 and
obligation matrix (Farey overlap, residual second moment, fourth-moment range: Passed)
Prior art: cited: Vaughan (MNT II 17.1), Gallagher's lemma, primitive large sieve for
the optional Gauss-first route (Appendix A)
Reused in: FRONTIER_2026_09_12.md route table; SHARP_EXPONENT.md Section 1.2 correction
Why it travels: A clean template for block-wise residual moments on Farey arcs with an
explicit overlap constant and an explicit Q-range where Vaughan's N^{4/5} term stays
harmless.

### Explicit exceptional-zero correction to the pair count with exact residue-average identities

construction | `hunts/prime_pair_error/` | grade: handwritten deduction with bounded
algebra checks (artifacts/siegel_uniformity/check.py); consumed as a checked dependency
by ENDPOINT_BOUND_REVIEW (PASS) and ENDPOINT_SHARP_REVIEW

Model a(n)=nu(n)(1-n^{beta-1}chi(n)) with nu(n)=b_Z 1_{(n,P(Z))=1}, Z=exp((log
N)^{1/10}) (TT Definition 2.1). Uniformly for 1<=h<=N: sum_{n<=N-h}a(n)a(n+h)-(N-h)S(h)
= C_{q,beta,Z}(h)+O(N e^{-c L^{1/10}}) (18), where C =
L_h[-u_q(h)J_1(h)-v_q(h)J_2(h)+(c_q(h)/q)J_{12}(h)], L_h=(q/phi(q))^2 prod_{p<Z,p
not|q}alpha_p(h), J_1=int_0^{N-h}max(1,t)^{-delta}, J_2=int_0^{N-h}(t+h)^{-delta}, J_12
their product integral, delta=1-beta. Exact identities (17): u_q(h)=mu(q)chi(-h)/q,
v_q(h)=mu(q)chi(h)/q for odd primitive real conductor q, u=v=0 for 4|q, and sum_r
chi(r)chi(r+h)=c_q(h) (Ramanujan sum). Supporting tools: fundamental-lemma sieve count
per residue class with sharp endpoint N-h (10); |sigma_Z(h)-S(h)| << L^2/Z (12);
transfer ||C(|F|^2-|H|^2)||_2 <= ||W||_4(||F||_4+||H||_4) (6) with exact U^2
normalization A_N=(2N^3+N)/3 (4); moment bound sum_h|C|^2 << 1_{q
odd}N^{2beta+1}q^2/phi(q)^4 + N^{4beta-1}q^2/phi(q)^3 (23) and matching lower bound
A_exc >= (1/192)N^{4beta-1}q^2/phi(q)^3 (EXCEPTIONAL_ENERGY eq 2).

Evidence: SIEGEL_UNIFORMITY.md Sections 1-5 lines 26-350 (eqs 3-6, 10-12, 17-19, 23);
EXCEPTIONAL_ENERGY.md lines 6-30 (eqs 1-3); ENDPOINT_BOUND_REVIEW.md 'Checked
dependencies' item 3
Prior art: cited: Tao-Teraevaeinen arXiv:2107.02158v4 (Definition 2.1, Theorem 2.7,
Lemma 5.1); CHHL Section 7 for the Ramanujan approximant
Reused in: CORRECTED_RH_BRIDGE.md, EXCEPTIONAL_ENERGY.md, LOCALIZED_MIXED_ENERGY.md,
ENDPOINT_BOUND.md, ENDPOINT_SHARP.md, ARC_SPLIT_BUDGET.md, MAJOR_ARC_EXPLICIT.md,
PAGE_ZERO_ASYMPTOTIC.md, S8_CONTROL.md
Why it travels: Gives the exact shape a Siegel zero imprints on any shifted correlation
with sharp endpoint, with the residue averages in closed form for every primitive real
conductor.
Index note: Consumed by seven downstream documents in the same hunt as a checked input.

### Lifted balanced-seed factorial certificate for psi(N)

construction | `hunts/prime_pair_error/` | grade: exact-rational feasibility checks plus
elementary general argument; pilot independently reviewed (all 87 seeds reproduced);
later refinement rules 'no separate proof review'

Choose L>=M>=2 and rationals a_j indexed by j|L with sum_j a_j/j=0 (balance), g(t)=sum
a_j floor(t/j) >= 0 on r=0..L-1 and >=1 on r=1..M-1; balance makes g periodic with
period L and integer breakpoints, so one period certifies g>=0 for all real t>=0 and
g>=1 on [1,M). For N put K=floor(log_M N) and W_N(t)=sum_{k<=K} g(t/M^k); then W_N(t)>=1
for 1<=t<=N (the term k=floor(log_M t) is >=1, the rest >=0), and B_N=sum_k sum_j a_j
log floor(N/(jM^k))! = sum_{d<=N}Lambda(d)W_N(N/d) >= psi(N) with no RH input. Cost: B_N
= C N + O(A (log N)^2) with kappa=-sum a_j log(j)/j, C=kappa/(1-1/M), using |log
floor(y)! - (y log y - y)| <= 1+log^+ y. Period 30 recovers Chebyshev; best period-2310
seed C~1.0699; structural enlargement to 30030 gives 1.0558; the refinement rule with
carry b_n(t)=floor(t/n)-floor(t/(n+1))-floor(t/(n(n+1))) (nonnegative, 0 before n, 1 at
n) and h_p=sum_{d|210}mu(d)b_p(t/d) reaches C~1.0500, and the combined-weight variant
(W_g>=1 below R, g>=0 above R suffices) reaches C~1.04866. Every fixed seed has C>1; the
omitted-prime lemma forces W(p)>=2 for primes absent from the denominator set.

Evidence: frontier/2026-09-06/factorial_certificate_pilot/PILOT.md Sections 1-3 (lines
7-75), REVIEW.md; checkpoint/CHECKPOINT.md Sections 4.8, 4.10-4.12 (lines 95-143);
certificate_refinement_rule/REFINEMENT.md; certificate_route_test/ROUTE_ASSESSMENT.md
Prior art: cited: Chebyshev's factorial construction (the period-30 seed);
Nyman-Beurling noted as a different known criterion, not executed
Reused in: hunts/paid_shortfall/RESULTS.md (inherits the pilot main term and remainder);
certificate_lp_frontier (the family whose LP floor is computed);
hunts/quotient_certificate/
Why it travels: A self-certifying majorant template: one finite integer-period check
plus a radix lift gives an unconditional psi(N) ceiling with an explicit leading
constant for any seed.

### Asymptotic of the character-twisted singular-series sum H_chi(N) and its constant c_H

calibration | `hunts/prime_pair_error/` | grade: reviewed written proof; constant is a
truncated-product value, not an enclosure

For chi mod 3, H_chi(N)=sum_{k<=N}chi(k)S(k)(N-k) = c_H N + O(N^{3/4}) with c_H = D(0) =
-(2C_2/3) prod_{p>3}(1+chi(p)/(p-2)) < 0, from the Dirichlet series D(s) = -2^{1-s}C_2
L(s,chi)F(s), F(s)=L(1+s,chi)K(s), K an Euler product absolutely convergent for Re
s>-1/2, contour shifted to Re s=-1/4 using L(s,chi)<<(1+|t|)^{3/4} and
L(1+s,chi)<<(1+|t|)^{1/8+nu}. Numerically c_H is near -0.31305 (JSON value -0.31306242
is a product truncated at 2e6, not the limit); measured H_chi(N)/N = -0.3130 to -0.3131
at five cutoffs. Also M(x)=sum_{k<=x}chi(k)S(k) << log x by Mertens. Hence
P(N)/2+X_chi-H_chi = -c_H N + o(N), so the auxiliary term in (E3) is Theta(N), not O(N
log^2 N) as first proposed.

Evidence: RESULTS.md Section 15 lines 585-627; REFEREE.md Section 5 lines 323-416
('proof valid after specified repair'; finite products must be labelled approximations);
wronskian.py H_chi_by_divisor_expansion (independent evaluation agreeing to 1e-10)
Prior art: cited: Friedlander-Goldston / Korevaar-te Riele for the untwisted sum sum
S(k) = h - (1/2)log h + ...; twisted version derived here
Reused in: RESULTS.md Section 16 (E5); REFEREE.md Section 7
Why it travels: Template for any character-twisted or otherwise weighted sum of the
singular series: write the Dirichlet series as a product of L-factors and an absolutely
convergent Euler product, shift the Riesz-mean contour, read the constant at s=0.

### Replication convention for CHHL Table 1: truncate, do not round

calibration | `hunts/prime_pair_error/` | grade: measured

Chou-Haag-Huryn-Ledoan report E(N)/(N^2 log^2 N) truncated to five decimals, not
rounded: at N=1e4 the computed value 0.1232782 rounds to 0.12328 and truncates to the
paper's 0.12327; all eleven rows match after truncation. Supporting pins: C_2 from the
Euler product to 4e6 is 0.6601618261 against the pinned 0.6601618158 inside the tail
bound; the identity sum_{|k|<=N}psi_2(N,k)=psi(N)^2-sum Lambda(n)^2 holds at every N to
float precision and forces the k-mean of e to psi(N)-N+c(N), c in [1.21,1.32]; odd
separations carry E-share 2e-6 at 1e7 and only involve powers of 2.

Evidence: RESULTS.md Section 1 lines 10-41; MISSION.md required_oracles and
kill_conditions
Prior art: cited: CHHL arXiv:2308.14888 Table 1 and Section 3
Reused in: CHALLENGE.md Attack 1 (uses the 1e5 row 0.16857 as an external sanity
target); S8_CONTROL.md
Why it travels: Anyone re-deriving or extending Table 1 must truncate to match; the 1e4
row is the discriminating check.

### Freeze-then-test protocol with derived coefficients and post-hoc slope diagnostic

control | `hunts/prime_pair_error/` | grade: measured

Every coefficient of a candidate correction is fixed by derivation (here all equal to
1), recorded in a FROZEN table that the test suite refuses to let move, and the
correction is evaluated only at cutoffs the discovery pass never used (2e5, 5e5, 2e6,
5e6, 7e6 after discovery on 1e3..1e7), with nothing inspected in between. Two read-outs:
reduction 1-sum(e-c)^2/sum e^2, and the post-hoc least-squares slope of e on c whose
derived value is 1 (measured within 0.2 percent of 1 for q=30 at all five cutoffs). The
first pass used the same pattern with held-out N=3e6 and 1e7 and a kill condition
'coefficient moves by more than its scale between discovery and held-out N'.

Evidence: RESULTS.md Section 9 lines 305-311 ('Every coefficient is fixed at 1 by the
derivation... the test refuses any other value'); Section 10 lines 336-364; Section 4
lines 131-133 (held-out rows); MISSION.md kill_conditions
Prior art: unsearched (standard held-out practice; the specific convention of
derived-not-fitted coefficients plus slope-should-be-1 diagnostic is the lab's)
Reused in: residue.py and tests/test_prime_pair_residue.py; S8_CONTROL.md and
CHALLENGE.md reuse the independent-reimplementation cross-check pattern
Why it travels: Separates 'the model explains X percent' from 'the fit absorbed X
percent' for any predicted profile on any family of cutoffs.

### Davenport-Heilbronn battery for pair energies via the periodic-sequence singular series

control | `hunts/prime_pair_error/` | grade: measured (float) plus written argument

To test whether an exact identity or domination for E_corr carries arithmetic content,
feed the identical construction a real, period-5 sequence a(n) built from the DH
coefficients (1,kappa,-kappa,-1,0), kappa=0.284079..., whose L-function satisfies
F(s)=F(1-s) and has a located zero at Re s ~ 0.8085. The exact analogue of the singular
series for a periodic sequence is its period autocorrelation rho(h)=(1/5)sum_j
a(j)a(j+h), which is the exact main term of sum a(n)a(n+h) with no error term. If the
identity holds for the DH sequence to the same precision (here 8.2e-16), it
distinguishes nothing about zeta. Attack 3 pairs this with a line-by-line audit: does
any proof step use Lambda, S, or C_N beyond being fixed real numbers? For the dyadic
Haar/martingale energy the answer was no (P_aP_b=P_max(a,b), orthogonal projections,
Pythagoras).

Evidence: CHALLENGE.md Attacks 2 and 3 (lines 73-172) and Overall verdict;
CANDIDATE_ENERGY.md Section 3 lines 98-165 (the identity being tested); s8_challenge.py
Prior art: cited: the repository's standing counterexample-battery rule (zeta/epstein.py
docstring, NULLCONTROLS.md, REDTEAM.md attack A3); the periodic-sequence main term is
the hunt's adaptation
Reused in: POSITIVITY_ENERGY.md (runs the battery against the per-scale arithmetic facts
of a second energy); CHECKPOINT.md
Why it travels: Any 'exact energy decomposition' or 'domination' claimed for the primes
can be falsified as arithmetic evidence in one run by substituting a periodic DH-type
sequence with its exact period autocorrelation as prediction.

### Counterfeit greedy-deficit sequence: falsifier for coarse-property arguments

control | `hunts/prime_pair_error/` | grade: elementary written argument with computed
table to N=2e6; unreviewed draft per CHECKPOINT.md 4.7

Fix beta=3/4, t=3, c=1/10, A(x)=x+c x^beta cos(t log x)+b. Keep true Lambda through
n0=10000; above n0 allow weight only at (n,30)=1, adding log n exactly when
A(n)-Psi_a(n-1)>=log n, else 0. Since |(c x^beta cos(t log x))'|<1/2 and gaps between
permitted n are at most 6, the deficit stays in [0, log n+9), so
Psi_a(N)=N+cN^{3/4}cos(3 log N)+b+O(log N) (C1), sum a_n^2 = N log N - N + O(N^{3/4}log
N) (C2), and the support count is ~N/log N. The sequence is nonnegative, has the right
density and second moment, avoids multiples of 2,3,5, yet violates any N^{1/2+eps}
remainder and fails the divisor identity sum_{d|n}Lambda(d)=log n first at n=10007
(defect about -9.211). Any argument that uses only positivity, leading density,
prime-sized second moment and small-prime avoidance therefore cannot prove (U).

Evidence: frontier/2026-09-06/DIRECT_ATTACK.md Section 5 lines 139-194, Section 6;
check_attack.py, checks.json (run to 2e6)
Prior art: unsearched
Reused in: frontier/2026-09-06/checkpoint/CHECKPOINT.md 4.7 ('counterfeit control');
FRONTIER_2026_09_12.md route table ('existing DH control')
Why it travels: A constructive negative control for any proposed prime-counting upper
bound: list the coarse properties the proof consumes, build a sequence with those
properties and a planted oscillation, check the proof does not exclude it.

### Exact-rational planted-lesion discrimination with three evidence classes

control | `hunts/prime_pair_error/` | grade: Class A exact finite checks for the stated
cutoffs only; general identities rest on written derivations

Finite identities in a proof package are checked in exact Fraction arithmetic with zero
tolerance (Class A), transcendental constants at high precision without enclosure (Class
B, mpmath dps=80, 'not exact'), and floats only for envelopes and ratios (Class C,
'diagnostic only'); every claim is labelled with its class. Each identity check is
paired with planted lesions that must produce strictly nonzero exact defects: for the
p=2 Mobius pairing M_b=P_b+T_b+H_b+Z_b, lesions missing_head/missing_tail/wrong_sign
give defects 11/5/2 at N=100 and 39/17/20 at N=400; for the hyperbola factorization,
four lesions (E-sign flip, smooth/fractional minus sign, empty-cell guard omission,
partition boundary omission) all fail with positive defect. The independent-review
script must not import the author's checker (mobius_pairing_independent_check.py vs
mobius_pairing_check.py; 15794 pairs over 20 cutoffs). A first review draft citing an
ephemeral scratch script was retracted and replaced by a durable artifact.

Evidence: FINAL_ACCEPTANCE.md Section 3 lines 86-98 (evidence classes), Section 1 item
2; MOBIUS_PAIRING.md Section 5 lines 140-170 and Section 6 run record;
MOBIUS_PAIRING_REVIEW.md lines 244-260; ARITHMETIC_CANCELLATION_REVIEW.md lines 347-363;
RESULTS.md Fourth pass lines 947-959
Prior art: unsearched
Reused in: MOBIUS_PAIRING.md and its review; FACTORIZATION_NEXT_STEP.md; RESULTS.md
Fourth pass
Why it travels: A checking convention that separates 'identity holds exactly at these
cutoffs' from 'float agreement' and proves each guard is load-bearing by removing it.

### Exact scale relation from the factorial identity, and the zeta-multiplier obstruction to contraction

obstruction | `hunts/prime_pair_error/` | grade: ordinary derivation, independently
reviewed (FRONTIER_INDEPENDENT_REVIEW.md, conditional on named classical inputs); not
kernel-checked

From sum_{d|m}Lambda(d)=log m: sum_{k<=N}psi(N/k)=log N!, so sum_{k<=N}R(N/k)=G(N)=log
N! - N H_N = -(1+gamma)N + (1/2)log N + O(1). With I=int_1^inf R(u)u^{-2}du = -(1+gamma)
(proved via -zeta'/(s zeta)-1/(s-1) as s->1+ and absolute integrability from the
unconditional PNT rate), for every integer 1<=K<=N: sum_{k<=K}R(N/k) - N int_{N/K}^inf
R(u)u^{-2}du = G(N)+(1+gamma)N - Q_{N,K}, |Q_{N,K}| <= Var_{[1,N/K]}R << N/K, hence =
O(N/K+log N) (16); at K=sqrt N the forcing is O(sqrt N). Obstruction: for
f_rho(u)=u^rho, 0<Re rho<1, the same operator gives (L_K f_rho)(N) =
N^rho(sum_{k<=K}k^{-rho} - K^{1-rho}/(1-rho)) = zeta(rho)N^rho + O_rho((N/K)^beta) (22),
by Euler-Maclaurin; at a zeta zero the N^beta mode passes every scale within the O(N/K)
allowance. Equivalently the Mellin transform of R has residue -m/rho at a zero of
multiplicity m, which no exact forcing cancels. Hence no absolute-value or
positivity-preserving contraction on (16) can exclude off-line zeros; the missing
estimate is |D_N| << N^{1/2+eps} with D_N = N int_{N/K}^inf R u^{-2} - sum_{k=2}^K
R(N/k).

Evidence: SIGNED_MEAN_RENEWAL.md Sections 3-6 lines 132-340 (eqs 9-16, 20-23), Section 8
(positive monotone model); frontier/2026-09-06/DIRECT_ATTACK.md Sections 2-4 (F1-F5, M);
FRONTIER_INDEPENDENT_REVIEW.md Section 2 obligation matrix (integral constant, all-K
estimate, multiple-zero claim: Passed); FRONTIER_2026_09_12.md lines 54-102
Prior art: cited: NIST DLMF 25.11.E5 (Euler-Maclaurin for zeta); text says the zeta(s)
multiplier is 'the familiar Mellin/Dirichlet-convolution multiplier, not a newly
discovered phenomenon'
Reused in: FRONTIER_2026_09_12.md; FINAL_ACCEPTANCE.md and FACTORIZATION_NEXT_STEP.md
(D_N target); MOBIUS_PAIRING.md
Why it travels: Any renewal or feedback argument for a summatory function through
Dirichlet convolution must check the multiplier at the zeros of the convolving series;
if it vanishes there the recursion is blind to those modes.

### Rudin-Shapiro-type polynomial obstruction to minor-arc fourth-moment saving from global norms

obstruction | `hunts/prime_pair_error/` | grade: written derivation with exact finite
algebra check; 'bounded independent agent check', not external verification

For r>=2 put d=2^{2r}, m=2^{3r}, N=dm=2^{5r}. Define A_0=B_0=1, A_{s+1}=A_s+z^{2^s}B_s,
B_{s+1}=A_s-z^{2^s}B_s; then |A_s|^2+|B_s|^2=2^{s+1} on |z|=1 with coefficients in
{-1,1}. Let H=e(alpha)A_{2r}(e(alpha))D_m(d alpha) (or B). Then H has frequencies 1..N
with unimodular coefficients, ||H||_2^2=N, ||H||_inf<=sqrt2 N^{4/5}, and one of the two
has int|H|^4 >= (2/3)N^{13/5} since int|D_m(d alpha)|^4=(2m^3+m)/3. Fubini over
translates places the mass in the actual minor set: some g=H(.-theta) has int_{m_Q}|g|^4
>= (14/27)N^{13/5}, while int|g|^p <= 2^{(p-2)/2}N^{p-1} for every p>2. A
nonnegative-coefficient variant f_omega=sum[1+Re(omega c_n)]e(n alpha) keeps the
conclusion. So the minor-arc supremum (Vaughan), Parseval, and every Green-Tao
restriction-type bound int|F|^p<<N^{p-1} together cannot imply I_Q << N^{13/5-delta};
additional prime arithmetic must enter.

Evidence: MINOR_LEVEL_SETS.md Section 4 lines 157-266 (eqs 11-20), Section 5 lines
293-300; artifacts/minor_level_sets/check.py (exact integer convolutions at N=32,1024)
Prior art: unsearched in the text (the recursion is the classical Rudin-Shapiro
construction; the hunt does not name it and claims no novelty)
Reused in: RESULTS.md 'The doors' rank 2; RANK3 documents; ARITHMETIC_FOURTH.md
Why it travels: A ready-made extremal example showing which scalar norm inputs are
insufficient for any minor-arc L^4 target; reusable whenever a circle-method budget is
stuck at sup times L^2.

### LP floor for floor-sum prime certificates, its dual, and the rough-spike lemma

obstruction | `hunts/prime_pair_error/` | grade: LP values measured (HiGHS float,
certificates re-verified cell by cell); Lemmas 1-3 and Proposition 4 proved elementarily
and pinned in tests; barrier law is conjecture

Every certificate of the form W(t)=sum_{j<=y}c_j floor(t/j)>=1 on cells 1..N gives
psi(N) <= B(N)=sum_j c_j log floor(N/j)!, and the excess is exactly B(N)-psi(N)=sum_n
(W(n)-1) m_n with m_n=psi(N/n)-psi(N/(n+1)) (E). The best certificate at (y,N) is the LP
V*(y,N)=min c.L s.t. W>=1; its dual maximises sum nu_n over nonnegative nu with sum_n
nu_n floor(n/j)=log floor(N/j)! for j<=y, i.e. a nonincreasing measure passing the first
y Chebyshev tests, the primes being feasible with value psi(N). Lemma 1 (dual): any
delta with sum delta_n floor(n/j)=0 (j<=y) and delta_n>=-m_n gives E(c)>=sum delta_n.
Lemma 2: all admissible U(k)=sum_{n>=k}delta_n arise as U(k)=sum_m mu(m)T(km) for T on
(y,N], gain sum_{m>y}mu(m)T(m), constraint U(k)-U(k+1)>=-m_k. Lemma 3 (rough spikes):
E(c) >= sum_{y<q<=N, q y-rough} m_q, since the jump of W at a y-rough q equals
c_1=W(1)>=1. For one cutoff N only, W>=1 is needed only on the attainable quotients
Q_N={floor(N/d)}, about 2 sqrt N cells (T*, prime-blind). Measured floor at y=sqrt N is
about 0.32 N^{3/4} over three decades; the barrier V*-psi >= cN/sqrt y is a conjecture,
and the Section 4.2 dimension-count argument is refuted by N=27,y=9.

Evidence: frontier/2026-09-06/certificate_lp_frontier/RESULTS.md Sections 1-3, 5-6
(lines 22-94, 344-398) and correction header; BARRIER.md Sections 1-2 lines 16-123
(Lemmas 1-3, 5, Proposition 4); barrier_lemmas.py; tests/test_certificate_lp_barrier.py
Prior art: cited: Chebyshev's construction (recovered at period 30); Selberg's identity
as a test dictionary; Huxley's divisor bound for the Voronoi alternative
Reused in: hunts/quotient_certificate/ (T* relaxation, N=27 counterexample, PR #203);
hunts/paid_shortfall_scaling/RESULTS.md (cites BARRIER.md); hunts/outband_certificate/,
hunts/paid_shortfall/
Why it travels: Converts any 'hand-built majorant' family into a computable floor plus a
dual witness showing where the freedom sits; the excess identity (E) and rough-spike
lemma hold for any floor-sum certificate.

### Nonnegative squared-term obstruction to an integrated Barban-Davenport-Halberstam theorem at N^{1+eps}

obstruction | `hunts/prime_pair_error/` | grade: measured (exact enumeration, small Q
only) plus heuristic argument; the text calls it 'strong evidence, not a proof' and does
not extrapolate to Q polynomial in N

Sigma(N,Q)=sum_{q<=Q}sum_b^* sum_{t<=N}Delta(t;q,b)^2 with
Delta(t;q,b)=psi(t;q,b)-t/phi(q) is a sum of nonnegative terms, so no cancellation
across t is possible; if Delta(t;q,b)^2 is of order t/phi(q) (up to logs) for a positive
proportion of t in [N/2,N], which is what square-root cancellation and the proved sharp
BDH asymptotic assert, then Sigma(N,Q) >> QN^2, not QN^{1+eps}. Measured exactly (true
Lambda, exact cumulative class sums, no sampling) for Q in {5,10,20,30} and N from 1e4
to 3.2e5: Sigma/(QN^2 log N) stable within a factor 2 and log-log exponent 1.97-2.00 in
N. Hence the t-integrated mean-value theorem RANK3_ROUTE_D.md's (D11) would need does
not exist because the quantity does not have that size; the obstruction is the object,
not the technique.

Evidence: RANK3_INTEGRATED_BDH.md Section 3 lines 126-216 and Section 4;
rank3_integrated_bdh_probe.py, results_rank3_integrated_bdh_probe.json
Prior art: cited: Montgomery 1970, Hooley (sharp BDH); Barban-Vehov and Motohashi
examined by name and found inapplicable
Reused in: RANK3_ROUTE_D.md, RANK3_MEAN_VALUE_TOOLS.md Section 5, RANK3_BDH_VERIFY.md
Section 6
Why it travels: The general principle: before searching the literature for a mean-value
theorem of a given strength, check whether the target is a sum of squares whose typical
term already has the forbidden size.

## Factorial and LP certificates for psi(N)

Chebyshev-type factorial certificates for psi(N) as linear programs: the quotient
relaxation, its floor, exact duals, repair budgets and the rank and transport
obstructions.

- identity: Exact paid-cost excess identity for factorial certificates
  (`paid_shortfall`)
- identity: Perfect-power cap mass: exact Möbius-type identity and asymptotic bound
  (`paid_shortfall_scaling`)
- identity: Attainable-cell (quotient) relaxation of the factorial LP certificate
  (`quotient_certificate`)
- identity: Exact full-period sawtooth covariance and Jordan-totient variance identity,
  with primorial refutation of the diagonal comparison (`quotient_certificate`)
- identity: True-rate prefix transport identities and the zero-mass drain obstruction
  (`quotient_certificate`)
- lemma: Contractive repair lemma: explicit budget for compensating empty-cell deficits
  (`quotient_certificate`)
- lemma: Halving folds are an integer basis of ker(A^T); nonnegative-fold gain has a
  finite rational upper certificate (`quotient_certificate`)
- lemma: Strictly positive dual as an exact uniqueness certificate for the floor-LP
  optimizer (`quotient_certificate`)
- bound: Early-truncation lemma: repair bill of a square-root-support balanced seed lift
  (`paid_shortfall`)
- bound: Finite prime-weighted variance decomposition (R), atom-loss conversion (M), and
  kernel-distance bound (F) (`quotient_certificate`)
- construction: Perfect-power cap and an exact finite LP-dual optimum removing an
  artificial-mass obstruction (`paid_shortfall`)
- construction: Balanced Möbius-prefix coefficient family with bounded mass
  (`paid_shortfall_scaling`)
- construction: Zero-surplus rational balanced vector at N = 144 and the exact cost
  identity C = psi(N) + S (`paid_surplus_obstruction`)
- construction: Sampling-null feasible witness from a residue-matrix kernel
  (`quotient_certificate`)
- computational technique: Finite duality lower bound with exact integer product
  capacity checks (`quotient_certificate`)
- obstruction: Rank obstruction: more columns than prime cells does not force zero
  excess (N=27 exact counterexample) (`quotient_certificate`)

### Exact paid-cost excess identity for factorial certificates

identity | `hunts/paid_shortfall` | grade: ordinary derivation, independently checked
algebra; small deterministic checks in construction.py and tests/test_paid_shortfall.py

For N >= 2, Q_N = {floor(N/d) : 2 <= d <= N}, W_c(q) = sum_j c_j floor(q/j), B_N(c) =
sum_j c_j log(floor(N/j)!), m_q = sum_{floor(N/d)=q} Lambda(d), and any cap U_q >= m_q,
define C_N^U(c) = B_N(c) + sum_q U_q (1 - W_c(q))_+. Then by the divisor identity log n
= sum_{d|n} Lambda(d) one has B_N(c) = sum_q m_q W_c(q), and exactly: C_N^U(c) - psi(N)
= sum_q m_q (W_c(q)-1)_+ + sum_q (U_q - m_q)(1 - W_c(q))_+ >= 0. The first term charges
surplus coverage; the second charges slack in the cap precisely where coverage is
missing; improving a cap helps only where the candidate has a deficit.

Evidence: RESULTS.md section 1 'Definitions and the complete paid cost', equation (1),
lines 24-60
Prior art: paid functional and capped dual preserved from a September 7 conversation;
main term inherited from
../prime_pair_error/frontier/2026-09-06/factorial_certificate_pilot; novelty not
assessed
Reused in: hunts/paid_shortfall_saturation (full total = factorial + P_Lambda = psi(N) +
S, the surplus S = sum Lambda(d)(W_d - 1)_+)
Why it travels: Splits the excess of any Chebyshev-type factorial upper bound into two
nonnegative, separately attributable terms, so every coefficient or cap change can be
priced exactly.

### Perfect-power cap mass: exact Möbius-type identity and asymptotic bound

identity | `hunts/paid_shortfall_scaling/` | grade: elementary written derivations, not
Lean, independently reviewed once; numerics carry two-backend rational enclosures

For d ≥ 2 let r(d) be its largest perfect-power exponent, h(d) = log d·(1 − 1/r(d)),
T(X) = Σ_{2 ≤ d ≤ X} h(d), L(X) = log(⌊X⌋!). With b_k = −Π_{p | k}(1 − p) over distinct
primes (b_2..b_12 = 1,2,1,4,−2,6,1,2,−4,10,−2), for X ≥ 4 and K = ⌊log₂X⌋: T(X) =
Σ_{k=2}^{K} b_k L(X^{1/k}), using exact integer roots (root^k ≤ n < (root+1)^k, no
floating-point root rounding). Proof: with b_1 = −1, Σ_{k | r} (−b_k)/k = Π_{p^a ∥ r}(1
+ (1−p)Σ_{i=1}^{a} p^{−i}) = 1/r, so Σ_{k | r, k ≥ 2} b_k/k = 1 − 1/r and the factorial
expansion counts d = a^r exactly at k | r. Asymptotic: L(√N) ≤ T(N) ≤ L(√N) +
8N^{1/3}log N, hence T(N) = ½√N log N − √N + O(N^{1/3}log N) with the coefficient of
N^{1/3}log N at most 2/3 + 12/(e log 2) < 8 (using max_{x ≥ 1} (log x)x^{−1/12} = 12/e).
For any finitely supported coefficient vector the cap saving is exactly S_N =
Σ_{d=2}^{N} h(d)δ_{⌊N/d⌋} with 0 ≤ S_N ≤ D_N T(N), so if D_N = o(√N/log N) the
perfect-power cap cannot change a leading term CN + o(N).

Evidence: RESULTS.md §1 (eqs. 1–3, lines 25–83), §2 (eq. 6, lines 105–131);
computations/check-001 (257 cap identities, two interval log implementations at 35 and
70 digits)
Prior art: 'Novelty has not been assessed'
Reused in: §3 eq. 10 (saving bound D_N T(N/y) for the balanced-prefix family); §1 bound
(5) for the old truncated lifts, S_N = O(N^{1/4}log N)
Why it travels: An O(log X) evaluation of a perfect-power-weighted log sum, and a clean
criterion for when a capacity refinement cannot move a leading constant.

### Attainable-cell (quotient) relaxation of the factorial LP certificate

identity | `hunts/quotient_certificate/` | grade: identity exact (integer arithmetic on
all 889 retained cells); optimum values and logarithms measured (float LP, 50/80-digit
replays)

Let W_c(t) = sum_{j<=y} c_j floor(t/j), B_c(N) = sum_{j<=y} c_j log(floor(N/j)!), and
Q_N = {floor(N/d) : 2<=d<=N}. Expanding log(m!) = sum_{d<=m} Lambda(d) floor(m/d) and
interchanging finite sums gives exactly B_c(N) - psi(N) = sum_{d=2}^N Lambda(d)
[W_c(floor(N/d)) - 1] (floors commute under successive integer division). Hence W_c(n)
>= 1 for n in Q_N alone suffices for B_c(N) >= psi(N); no constraint at other integers,
no sieve, no prime locations. For r = floor(sqrt N), Q_N = ({1..r} union {floor(N/d):
d<=r}) minus {N}, so |Q_N| <= 2r-1. The relaxed optimum T* satisfies psi(N) <= P* <= T*
<= V* (P* = prime-cell, V* = all-cell relaxations). Measured savings of 30-42% of the
excess at N = 10^3, 10^4, 10^5 with rational coefficients (denominator 10^12) checked
feasible in Python integers.

Evidence: hunts/quotient_certificate/RESULTS.md, Section 1 'A relaxation that uses no
prime locations' (lines 14-50) and Section 2 table (lines 52-79)
Prior art: Chebyshev identity is classical and used as such; Section 5 corrects cited
literature (Brent-Platt-Trudgian, CHHL, Burnol, Bettin-Conrey-Farmer, Baez-Duarte,
Diamond) but the relaxation itself is unsearched; no novelty claimed
Reused in: Reused as the base object in FINITE_TRANSFER.md, HEIGHT_KERNEL.md,
COMPENSATED_REPAIR.md, TRANSPORT_CAPACITY.md, FOLD_UPPER.md, CREDITED_BUNDLE.md (same
hunt) and consumed by the prime_pair_error/frontier certificate_lp_frontier lane (PR
#208 DUAL_WITNESS.md)
Why it travels: Any floor-dictionary LP bounding a Lambda-weighted sum only needs
constraints at the distinct values floor(N/d); cuts constraint count from N to about 2
sqrt N with no loss of validity.

### Exact full-period sawtooth covariance and Jordan-totient variance identity, with primorial refutation of the diagonal comparison

identity | `hunts/quotient_certificate/` | grade: exact (finite enumeration and exact
algebra); ordinary derivation, self-reviewed

For f_j(n) = {n/j} - (j-1)/(2j) and n uniform on a common integer period, Cov(f_i, f_j)
= (gcd(i,j)^2 - 1)/(12 i j) exactly, and Var(sum_j c_j f_j) = (1/12) sum_{d=2}^y J_2(d)
[sum_{j<=y, d|j} c_j/j]^2 with J_2(d) = d^2 prod_{p|d}(1 - 1/p^2), via gcd(i,j)^2 - 1 =
sum_{d | gcd, d>=2} J_2(d). Corollary (obstruction): no uniform kappa>0 gives 12 Var >=
kappa sum c_j^2 for balanced coefficients: for a squarefree primorial P with delta =
phi(P)/P, tau = 2^omega(P), take c_d = mu(d) on d|P but c_1 = 1 - delta; then sum c_d/d
= 0, 12 Var = tau delta - delta^2 and sum c_d^2 = tau - 2 delta + delta^2, ratio -> 0.
Also W_c(n) = n A_c - sum_j c_j {n/j} with A_c = sum c_j/j, and the LP does not impose
A_c = 0 (measured A_c = 0.0081388771875 at (1000,31)).

Evidence: hunts/quotient_certificate/RESULTS.md, Section 4 'The random-sawtooth argument
discards structure' (lines 119-158); covariance checked by exact full-period enumeration
for all 400 pairs i,j<=20; primorial formulas checked at P=6,30,210,2310
Prior art: unsearched (full-period sawtooth correlations are classical Franel-Landau
territory; hunt does not cite)
Reused in: FINITE_TRANSFER.md Section 3 uses the period matrix K^per_{ij} and its lower
bound ||c - A_c e_1||^2/(24 H_y^2) (issue #204) as the comparison target
Why it travels: Closed-form second-moment structure for any linear combination of
sawtooths; the primorial family is a ready-made witness against unrestricted diagonal
(l2) comparisons.

### True-rate prefix transport identities and the zero-mass drain obstruction

identity | `hunts/quotient_certificate/` | grade: hardened (integer moment identities,
independent triangular solve and factorization, interval enclosures); not formalized or
externally reviewed

With {1..y} in Q_N, define for q > y: R_q(s) = sum_{k<=y/s} mu(k) floor(q/(sk)), r_s(q)
= R_q(s) - R_q(s+1) (R_q(y+1) = 0), z_q = e_q - sum_{s<=y} r_s(q) e_s. Summation by
parts and sum_{k|n} mu(k) = 1_{n=1} give sum_{s<=y} r_s(q) floor(s/j) = floor(q/j), so
A^T z_q = 0 and sum z_q = 1 - W_mu(q). Endpoint correction: r_s need not be 0 or 1 (r_51
= 2, r_100 = 50 at q=5000,y=100). Exact suffix identity: for y/2 < u <= y, sum_{s=u}^y
r_s(q) = floor(q/u); hence aggregate drains satisfy sum_{s=u}^y C_s = sum_{q>y} eta_q
floor(q/u) against sum_{s=u}^y m_s = psi(floor(N/u)) - psi(floor(N/(y+1))). Obstruction:
the proposed shortcut 'source capacity plus top-half prefix conditions imply a
positive-fraction feasible exchange' is false at a=103, b=101 (N=10000): the exchange
withdraws -theta at cell 33 whose integer cell {295..303} contains no prime power, so
m_33 = 0 and every theta > 0 fails; the exact feasible amount for that direction is
theta_max = min(nu_3, nu_5, nu_17, nu_33, nu_50, nu_103).

Evidence: hunts/quotient_certificate/TRANSPORT_CAPACITY.md, Section 2 'True integer
rates and an exact suffix identity' (eqs. 3-4), Section 3 'A precise capacity shortcut
and its exact counterexample' (eqs. 5-6), Section 4 (eqs. 7-9)
Prior art: identities consumed from PR #208 and corrected here; unsearched
Reused in: Feeds the capacity bookkeeping (7)-(9) that COMPENSATED_REPAIR.md Section 4
restates as the uniform-family obligation
Why it travels: Exact signed-rate calculus for moving dual mass through the prefix of a
floor dictionary, and a concrete demonstration that zero-mass cells (not source mass)
are the binding constraint.

### Contractive repair lemma: explicit budget for compensating empty-cell deficits

lemma | `hunts/quotient_certificate/` | grade: ordinary derivation with independent
mathematical review and rational algebra control (four-row example with C_12 = 1/4, C_21
= 1/2, S = 4); hardened evidence, not formalized

Fix N, y, the exact measure m, empty cells Z = {q : m_q = 0}. Let U (seed) and R_1..R_r
(repairs) be zero-moment vectors on Q_N, and Z_1..Z_r disjoint nonempty blocks of empty
cells; outside the blocks require U_q >= 0 and (R_i)_q >= 0. Hypotheses: (1) R_i
supplies >= 1 at every cell of Z_i and >= -C_{ki} on Z_k (C >= 0, C_ii = 0), d_k =
max_{Z_k}(-U_q)_+; (2) prices p_i > 0 and 0 <= rho < 1 with sum_k p_k C_{ki} <= rho p_i;
(3) envelopes (-U_q)_+ <= b_0(q), (-(R_i)_q)_+ <= p_i b(q) on positive-mass cells; (4)
seed gain >= G_0, repair gains >= -ell p_i. Put S = sum p_i d_i/(1-rho), t = (I -
C)^{-1} d = sum C^n d >= 0, D = U + sum t_i R_i. Then D >= 0 on all empty cells, p^T t
<= S, and if b_0(q) + S b(q) <= K m_q on P then m + D/K >= 0 and E_c >= (G_0 - ell S)/K.
Proof: p^T C^n d <= rho^n p^T d gives convergence; on Z_k, D_q >= -d_k + t_k - sum_i
C_{ki} t_i = 0. Positive repair gain may be retained for a sharper bound
(CREDITED_BUNDLE: (sum V + t_1 sum R)/K = 615 log229/146). Limitation identified: the
lemma forces aggregate repair >= 0 on every empty cell, so it cannot spend seed credits;
regroup the seed to fit.

Evidence: hunts/quotient_certificate/COMPENSATED_REPAIR.md, Section 2 'Conditional
lemma: repair budgets from a contraction' (eqs. 5-9) and Section 3; CREDITED_BUNDLE.md
Sections 3-4 (why the 2U seed fails, regrouped decomposition V = F_103, R = D - V)
Prior art: unsearched; 'No novelty claim is made'
Reused in: CREDITED_BUNDLE.md applies it to the coordinator's N=10000 bundle with Z_1 =
{33}, K = 146/log 229
Why it travels: A general sufficient rule for bounding the total amount of a cascade of
compensating perturbations under a weighted-l1 contraction; applicable to any
dual-measure repair where secondary deficits are created.

### Halving folds are an integer basis of ker(A^T); nonnegative-fold gain has a finite rational upper certificate

lemma | `hunts/quotient_certificate/` | grade: hardened (exact integer column
inequalities, fresh interval arithmetic at 90/105 digits, independent algebra review,
computation manifest); not formalized or externally reviewed

Assume {1..y} is contained in Q_N and let H = Q_N minus the prefix. The fold at
attainable a > y is F_a = -e_a + 2 e_{floor(a/2)} + sum_{i<=y} (T_i(a) - T_{i+1}(a)) e_i
with T_i(a) = sum_{k<=y/i} mu(k) (floor(a/(ik)) mod 2), T_{y+1} = 0; the parity identity
floor(a/j) - 2 floor(floor(a/2)/j) = floor(a/j) mod 2 plus prefix Mobius inversion gives
A^T F_a = 0 and gain g(a) = 1 + sum_{j<=y} mu(j)(floor(a/j) mod 2). At rows q > y,
(Fx)_q = -x_q + 2x_{2q} + 2x_{2q+1}, so any zero-moment delta supported on Q_N has the
unique signed fold coordinates x_q = 2x_{2q} + 2x_{2q+1} - delta_q evaluated in
descending q, and the prefix residual h = delta - Fx vanishes because the prefix matrix
(floor(i/j))_{i,j<=y} is unit lower triangular. The high-row matrix is unimodular, so
folds form an integer basis of ker(A^T) on the lattice. Separately, at N=10000, y=100, a
52-entry nonnegative integer vector B with beta = B/1387 satisfies -1387 g_a - sum_q B_q
F_{qa} >= 0 for all 98 columns, hence x >= 0, m + Fx >= 0 implies g^T x <= beta^T m in
[66.3384089619581189, ...190] (exact cost 16456 log2 + 3052 log7 + ... over 1387).

Evidence: hunts/quotient_certificate/FOLD_UPPER.md, Section 1 (fold convention, eq. 3),
Section 2 'The rational certificate and the inequality signs' (eqs. 4-6), Section 4
'Signed recurrence, including prefix reconstruction' (eqs. 7-8); COMPENSATED_REPAIR.md
Section 1 eq. 3
Prior art: fold construction consumed from PR #208 (other lane); basis lemma and upper
certificate 'No novelty claim is made'; unsearched
Reused in: Used to prove the 132.729535 prefix-exchange witness must have a negative
fold coordinate (FOLD_UPPER Section 4 'Scope consequence')
Why it travels: Gives an explicit unimodular coordinate system for all zero-moment dual
perturbations of a floor-dictionary LP, and shows how a finite rational dual certificate
caps an entire cone of constructions at once.

### Strictly positive dual as an exact uniqueness certificate for the floor-LP optimizer

lemma | `hunts/quotient_certificate/` | grade: exact integer/rational identities plus
fresh interval enclosures; independent agent review; not formalized or externally
reviewed

Let S be a basis of 100 attainable cells with A_S = (floor(s/j)) invertible (det -1328),
primal c* with A_S c* = 1 and W_{c*} >= 1 on all 198 cells. Reconstruct the integer
matrix E_{jp} = sum_k floor(floor(N/j)/p^k) over the 1229 primes p <= N, L_j = sum_p
E_{jp} log p, V = (A_S^T)^{-1} E, so nu_s = sum_p V_{sp} log p satisfies A_S^T nu = L
with no rationalization of logarithms; 80-digit intervals prove every nu_s > 0 (min in
[0.000612063301151538696782037139, ...140]). Then for every feasible c, B_c - T* =
sum_{s in S} nu_s (W_c(s) - 1) with T* = sum_s nu_s, so B_c = T* forces c = c*: all
nonzero cost-preserving feasible displacements are excluded. Every feasible vector is c*
+ A_S^{-1} z, z >= 0, nu^T z <= Delta, together with the 98 non-basis inequalities
(control: z = e_1 gives W(20) = -13/83, so they cannot be dropped).

Evidence: hunts/quotient_certificate/HEIGHT_KERNEL.md, Section 1 'Exactly which
ingredients of #208 were consumed' and Section 2 'Keep the full slack parameterization
and budget'
Prior art: complementary slackness, standard; the exact prime-log reconstruction is
unsearched
Reused in: Consumed within the same hunt (HEIGHT_KERNEL Section 4 uses T* in bound (3))
Why it travels: Pattern for certifying LP optimality and uniqueness exactly when the
objective involves logarithms: keep coefficients as integer matrices over log p, enclose
only at the end.

### Early-truncation lemma: repair bill of a square-root-support balanced seed lift

bound | `hunts/paid_shortfall` | grade: ordinary derivation, self-reviewed with
independently checked algebra; finite checks only falsify the implementation

Fix M >= 2 and finitely supported a_j (support in j <= J) with sum a_j/j = 0, g(t) = sum
a_j floor(t/j), full lift W_inf(t) = sum_{k>=0} g(t/M^k) >= 1 for t >= 1, and g <= H.
With A = sum |a_j|, kappa = -sum a_j log j / j, C = kappa/(1 - 1/M), L(x) =
log(floor(x)!), truncation K, R = M^{K+1}, c_n = sum_{j M^k = n, k <= K} a_j: psi(N) <=
C_N(c) <= C(1 - 1/R) N + E_N + H sum_{l>=0} L(N/(R M^l)), E_N = A sum_{k<=K} (1 +
log^+(N/M^k)), and the repair term is at most (H/(1-1/M)) x log^+ x with x = N/R. For J
M^K <= sqrt N the bill is at most (H J/(1-1/M)) sqrt N log(J sqrt N), so C_N(c) - N =
(C-1)N + O_{a,M}(sqrt N log N) for a fixed seed. Explicit base-6 seed g(t) = floor t -
floor(t/2) - floor(t/3) - floor(t/6) (values 0,1,1,1,1,2 on residues) has (1 - W_K(q))_+
= 1_{R | q} exactly, coefficient mass 2r+2, C_6 = (4 log 2 + 3 log 3)/5 > 1.

Evidence: RESULTS.md section 2 'Early-truncation lemma' with proof, equations (2)-(7),
lines 62-179; section 3 base-6 construction, equation (8), lines 181-234
Prior art: balanced-seed main term inherited from the factorial_certificate_pilot; not
searched
Reused in: hunts/paid_shortfall_saturation imports the cutoff selection from
paid_shortfall_scaling
Why it travels: A fully charged truncation for any balanced floor-sum seed at any base
M; the exact base-6 indicator identity (8) is a clean test object.

### Finite prime-weighted variance decomposition (R), atom-loss conversion (M), and kernel-distance bound (F)

bound | `hunts/quotient_certificate/` | grade: algebraic proofs and finite exact checks;
'not formalized or externally reviewed' (hunt's words); moment values measured at 50/80
digits

Let p_q = m_q/Psi on the positive-mass attainable cells P (m_q = sum of Lambda over the
exact integer cell, Psi = psi(N)), S_c = sum_j c_j {q/j}, V_q = Var_p(q), beta =
Cov_p(q,S_c)/V_q. Then (R): Var_p(W_c) = Var_p(S_c - beta q) + (A_c - beta)^2 V_q
exactly, so Var_p(W_c) >= c^T R_f c with R_f = C_f - h h^T/V_q, ker R_f = {c : Uc in
span(1, t)}. (M): for X = W_c - 1 >= 0, mu = E_p X, v = Var_p X, alpha = min p_q: E X^2
<= mu^2/alpha, hence E := B_c - psi(N) = Psi mu >= Psi sqrt(alpha v/(1-alpha)); for
N>=4, alpha = log2/Psi exactly (cell floor(N/2) holds only d=2), and (M) is sharp at
N=4, y=2, c=(1,t-1). (F): with D_W the anchored integer difference matrix of rank r and
L = ||D_W||_F^2, v >= p_{q0} alpha L^{-(r-1)} dist(c, K_W)^2, because the product of
positive eigenvalues of D_W^T D_W is a sum of squared integer minors >= 1. Zero-mass
rows must be excluded from D_W.

Evidence: hunts/quotient_certificate/FINITE_TRANSFER.md, Section 1 'Exact finite
measure', Section 4 'Drift is a separate obstruction, with an exact repair' (eq. R),
Section 5 'Second moments to nonnegative linear excess' (eqs. M, F); N=9 drift control
with masses (log210, log2, log3, log2)
Prior art: unsearched; no novelty claimed
Reused in: HEIGHT_KERNEL.md Section 5 applies (M) with the Cauchy-Schwarz bound v >=
M^2/D; TRANSPORT_CAPACITY.md Section 1 uses (M) to cap the
constant-variance/smallest-atom procedure at 17.507
Why it travels: Generic bookkeeping for converting a variance lower bound on a
nonnegative slack vector under a finite positive measure into a linear-excess bound,
with the smallest-atom loss made explicit and shown sharp.

### Perfect-power cap and an exact finite LP-dual optimum removing an artificial-mass obstruction

construction | `hunts/paid_shortfall` | grade: exact finite example (ordinary
derivation); no growth estimate claimed

For d >= 2 let r(d) be the largest r with d = b^r, u(d) = log d / r(d), U_q =
sum_{floor(N/d)=q} u(d); then u = Lambda on prime powers and m_q <= U_q <= w_q,
computable with integer power tests only. At N = 14 with support j <= 3 and cells
(1,2,3,4,7), c = (1,-1,-3/2) gives C^w = psi(14) + (1/2) log 2 and C^U = psi(14). The
raw-cap excess is unavoidable for every c' with that support: with epsilon = (1/2) log
2, v = (-1,1,2,0,-1), x = m + epsilon v is feasible (0 <= x <= w) with zero moments
sum_q v_q floor(q/j) for j = 1,2,3 and sum v_q = 1; since x(W-1) + w(1-W)_+ >= 0 for 0
<= x <= w, summing gives C^w(c') >= sum x_q = psi(14) + (1/2) log 2. The saving from the
cap is exactly sum_d log d (1 - 1/r(d)) (1 - W_c(floor(N/d)))_+.

Evidence: RESULTS.md section 4 'A finite obstruction removed by arithmetic capacity',
equation (9) and the dual vector argument, lines 236-301
Prior art: unsearched
Reused in: hunts/paid_shortfall_saturation (perfect-power capacity retained on prime
powers, saturated by trial division through sqrt(X))
Why it travels: The dual-vector certificate of a finite optimum (feasible x with
matching zero moments) is a reusable way to prove a paid-cost floor exactly, and the
perfect-power cap is a reusable arithmetic refinement.

### Balanced Möbius-prefix coefficient family with bounded mass

construction | `hunts/paid_shortfall_scaling/` | grade: elementary written derivations,
not Lean; finite identities checked exactly at N = 144…36864

For integer y ≥ 2 and S(m) = Σ_{j ≤ m} μ(j)/j, set c_j^{(y)} = μ(j) for j < y and
c_y^{(y)} = −yS(y−1). Then Σ_j c_j^{(y)}/j = 0 (zero harmonic drift), W_y(q) = 1 for 1 ≤
q < y (coverage, from Σ_{j ≤ q} μ(j)⌊q/j⌋ = 1), and mass A_y = Σ|c_j| ≤ 2y − 1 because
mS(m) = 1 + Σ_{j ≤ m} μ(j){m/j} with the j = 1 fractional part zero gives |S(m)| ≤ 1.
Consequences without positivity: |W_y(q)| ≤ A_y, D_N ≤ 1 + A_y ≤ 2y; with κ_y = Σ_{j <
y} (μ(j)/j)log(y/j), |B_N(c^{(y)}) − κ_y N| ≤ A_y(1 + log N) for every N ≥ 2; deficits
occur only for d ≤ N/y, so 0 ≤ P_N^U ≤ D_N L(N/y) and 0 ≤ C_N^w − C_N^U ≤ D_N T(N/y). At
y = ⌊√N⌋ the factorial error has square-root scale but the crude penalty bound does not;
the missing control is on the combined (κ_y − 1)N + P_N^U with its actual signs.

Evidence: RESULTS.md §3 (eqs. 7–10, lines 133–182); scaling.py; MISSION.md 'First
construction'
Prior art: prior lab work: finite Möbius-prefix and harmonic-drift identities in
prime_pair_error/frontier/…/BARRIER.md; novelty not assessed
Reused in: §4–§5 finite discriminators; cutoff selection rule
Why it travels: A scale-dependent coefficient family with explicit coverage, drift and
mass bounds, usable as a baseline in any paid-bound or factorial-route experiment.

### Zero-surplus rational balanced vector at N = 144 and the exact cost identity C = psi(N) + S

construction | `hunts/paid_surplus_obstruction/` | grade: 'ordinary finite argument with
exact rational executable checks and two independent logarithm enclosure
implementations' by the same producer; review status 'pending independent challenge'; no
Lean, no novelty claim, no uniform estimate

Class: rational c_1..c_12 with harmonic balance sum c_j/j = 0, coverage W(q) = sum c_j
floor(q/j) = 1 for 1 <= q <= 5 (forcing c_1 = 1), and mass sum |c_j| <= 23.
Construction: 20(c_1..c_12) = (20,-20,-20,0,-20,-13,7,6,0,0,0,13) has balance (840 sum
b_j/j = 16800-8400-5600-3360-1820+840+630+910 = 0), coverage (q - floor(q/2) -
floor(q/3) - floor(q/5) = 1 for q <= 5), mass 119/20, and W_d := W(floor(144/d)) <= 1 at
every prime power 2 <= d <= 144: for d >= 25 the quotient lies in [1,5] so coverage
gives W_d = 1 automatically (34 of 47 prime powers), and the 13 prime powers <= 24 are
checked by integer substitution (values 3/10, 3/10, 0, 1, 0, 0, 13/20, 1, 1, 1, 1, 7/10,
-13/20). Identity: with B = sum_j c_j log(floor(144/j)!) = sum_{d<=144} Lambda(d) W_d
(finite rearrangement of the Legendre count, no limit interchange) and P_Lambda = sum
Lambda(d)(1 - W_d)_+, applying w + (1-w)_+ = 1 + (w-1)_+ row by row gives C := B +
P_Lambda = psi(144) + S, S = sum Lambda(d)(W_d - 1)_+; the table proves S = 0 exactly so
C = psi(144), the elementary lower bound, attained. The previous endpoint
(1,-1,-1,0,-1,1,-1,0,0,1,-1,2/385) has S_old = (2/55) log 2 + (8/385) log 3 + (387/385)
log 7 + (387/385) log 11 > 0 exactly. The vector lies outside the convex hull of all
balanced Möbius prefixes (c_7 = 7/20 > 0 where every prefix has c_7 <= 0). Controls: LP
used only as discovery aid with exact rational reconstruction; old endpoint rejected on
five surplus rows; a class-preserving perturbation (+3/5 on c_6, -6/5 on c_12) rejected
on four rows; zero vector fails coverage; domain/support/balance/coverage/mass lesions
rejected.

Evidence: RESULTS.md 'Exact class and source boundary' (lines 22-50), 'Finite proof'
(lines 52-90), 'Full cost and what was improved' (lines 92-145), 'Controls,
reproducibility and remaining uncertainty' (lines 147-185); construction.py;
computations/check-001/
Prior art: unsearched ('An unrun literature search establishes nothing about priority')
Reused in: relaxes the balanced-prefix construction of
hunts/paid_shortfall_scaling/RESULTS.md §3; none else stated
Why it travels: The row-wise identity turning a signed Chebyshev-type sum plus repair
cost into psi(N) plus a surplus term, and the coverage trick that discharges all large-d
constraints for free, apply to any finite Möbius-style coefficient design at other
cutoffs or supports.

### Sampling-null feasible witness from a residue-matrix kernel

construction | `hunts/quotient_certificate/` | grade: exact rational witness with
independent integer checks (all 198 constraints, every sawtooth at every positive cell);
general construction proved algebraically, not externally reviewed

Let R be the integer matrix with rows (q mod j) - (q_0 mod j) over positive-mass cells q
in P minus {q_0} and columns j = 2..y. Whenever rank R < y-1, pick nonzero rational z in
ker R, set v_j = j z_j (denominators cleared), v_1 = 0, D = sum_{j>=2}|v_j|, c = e_1 +
v/D. Then S_c is constant on P (finite sawtooth variance zero), the full-period variance
is strictly positive (the largest index k contributes J_2(k) c_k^2/(12 k^2) > 0),
sum_{j}|c_j| = 2, and W_c(q) >= q - sum_{j>=2}|c_j| floor(q/j) >= q - floor(q/2) >= 1
for every integer q >= 1, so c is feasible on all of Q_N without repair. This refutes
any comparison Var_p(S_c) >= kappa Var_period(S_c) over the full feasible class (witness
at N=10000, y=100: 98x99 residue matrix of rank 95, 42 nonzero tail coefficients).
Boundary: its cost is B_c = log(N!), so it says nothing about low-cost certificates, and
its direction is blocked at the saved optimizer by two zero-mass cells (q=60, 333).

Evidence: hunts/quotient_certificate/FINITE_TRANSFER.md, Section 3 'One candidate
comparison, and its feasible counterexample' and subsection 'What the same direction
does to the saved low-excess certificate'; witness in
finite_transfer_counterexample.json
Prior art: unsearched
Reused in: HEIGHT_KERNEL.md Section 1 extends the two-cell blocking to all
cost-preserving displacements via the strictly positive dual
Why it travels: Cheap, prime-blind-in-coverage feasibility construction (sum|c| = 2
guarantees W_c >= 1 everywhere) for producing counterexamples to sampling/transfer
inequalities in floor-dictionary LPs; also shows why zero-mass constraints must be
retained.

### Finite duality lower bound with exact integer product capacity checks

computational technique | `hunts/quotient_certificate/` | grade: hardened (integer
identities, independent factorization and triangular reconstruction, interval
enclosures); not formalized or externally reviewed

For the exact measure m_q on Q_N and floor matrix A_{qj} = floor(q/j): if H is supported
on Q_N with A^T H = 0 (zero moments) and m + H >= 0, then every feasible c (W_c = Ac >=
1) has E_c = B_c - psi(N) >= sum_q H_q. To find the maximal scale lambda with m + lambda
D >= 0 without rounding logarithms, let M_q be the product of prime bases p once per
prime power in cell q, so m_q = log M_q exactly; then m_q + lambda D_q >= 0 with lambda
= log(P)/K is the integer inequality M_q^K >= P^{-D_q}. Instances: N=1000,y=31, D = F_76
+ 2F_200 + F_333 gives M_q^3 >= 7^{-D_q} with equality only at q=20 (cell {48,49,50},
only 49 = 7^2), so E_c >= (10/3) log 7 in [6.48636716351771101701, ...02]; N=10000: E_c
>= (615/146) log 229 and the two-cell control delta = log(97)(e_1 + e_102 - e_103) gives
E_c >= log 97.

Evidence: hunts/quotient_certificate/COMPENSATED_REPAIR.md, Section 1 'Fixed definitions
and the independently checked bundle' (eqs. 2, 4); TRANSPORT_CAPACITY.md Section 1 'The
two coordinator deductions' (eq. 1); CREDITED_BUNDLE.md Section 2 (eq. 3)
Prior art: ordinary finite LP duality, used as such; the exact-product capacity check is
unsearched; no novelty claimed
Reused in: Used in COMPENSATED_REPAIR.md, CREDITED_BUNDLE.md, TRANSPORT_CAPACITY.md,
FOLD_UPPER.md Section 2 (eq. 6, grouped log p evaluation)
Why it travels: Turns 'is this dual perturbation feasible against the prime measure'
into exact integer comparisons; no N/q^2 approximation or interval-length proxy for m_q,
and the binding cell is identified exactly.

### Rank obstruction: more columns than prime cells does not force zero excess (N=27 exact counterexample)

obstruction | `hunts/quotient_certificate/` | grade: elementary finite proof with
exact-arithmetic checks of row relation, rank, prime weights and attaining vector (hunt:
'not a kernel proof or an asymptotic result')

The claim 'P*(y,N) = psi(N) whenever y exceeds the number of prime-looking cells' is
false. At N=27, y=9 the prime-cell set S = {1,2,3,4,5,6,9,13} has |S| = 8 < 9, yet the
rows R_n = (floor(n/j))_{j<=9} satisfy the integer relation -R_1 + R_3 - R_6 - R_9 +
R_13 = 0 whose coefficients sum to -1, so the matrix (rank 7) cannot interpolate the
constant vector on S. For feasible W with e_n = W(n)-1 >= 0 the relation forces e_3 +
e_13 >= 1, and the excess identity weights at cells 3 and 13 (log 42, log 2) give B -
psi(27) >= log 2, attained by c = (1,-1,-1,0,-1,1,0,0,-1). Hence P*(9,27) - psi(27) =
log 2 exactly. General lesson: the zero-excess question is a feasibility/rank question
about integer row relations, not a variable count.

Evidence: hunts/quotient_certificate/RESULTS.md, Section 3 'More columns than prime
cells does not force zero excess' (lines 81-117)
Prior art: unsearched
Reused in: Generalised in HEIGHT_KERNEL.md Section 3 (21-cell integer relation at
N=10000 excludes the height kernel) and TRANSPORT_CAPACITY.md Section 1 (normalized
signed measures with A^T w = 0, sum w = 1)
Why it travels: Template for refuting dimension-count optimality claims in floor-matrix
LPs: exhibit an integer row relation with nonzero coefficient sum, read off a forced
excess from the positive weights.

## Weil positivity, Gram forms and kernels

Weil-form truncations, window optima, incidence laws, cell-table and interval
certificates for kernel inequalities, and the ceilings on what out-of-band positivity
can buy.

- identity: Window Rayleigh ceiling and the sqrt(2) harmonic orthogonality
  (`amtopa_ceiling`)
- identity: Finite Poisson lattice formula for the infinite-chain energy (`family_wall`)
- identity: LAW D: alias-free grid incidence identity and the rigid bilinear diagonal
  (`frontier_math`)
- identity: k-pair identity and the three-term Gram form of the multi-pair slack
  (two-species reduction) (`frontier_math`)
- identity: Closed forms for the windowed sine-Gram moments m2, m3 as functionals of the
  window, with exact rationals for polynomial windows (`rogue_frontier`)
- identity: Bridge identity between the BBLS basis Gram and the Vasyunin Gram, and the
  enclosure pipeline for Baez-Duarte d_N^2 (`rogue_frontier`)
- lemma: n-point certificate-to-proportion bridge with block cap (`ainta_seven_point`)
- lemma: Sharp stability rank–trace inequality with no hypothesis on V
  (`ainta_seven_point`)
- lemma: Pinching inequality via row-stochastic spectral mixture (no Peierls, no unitary
  invariance) (`ainta_seven_point`)
- lemma: Interior optimum in the pressure denominator and the affine-infimum concavity
  argument (`ainta_seven_point`)
- lemma: Witness-leg barrier for the n-point pressure family, with the case split that
  makes it a proof (`family_wall`)
- lemma: Integer trade with window decomposition: the k=1 retention inequality with no
  separation hypothesis (`frontier_math`)
- lemma: Homogeneity closure of the shallow end (an interval with no smallest point)
  (`frontier_math`)
- lemma: Lattice extremality via the structure-factor identity and Newton's identities
  (`frontier_math`)
- lemma: Edge lemma for autocorrelations of real even factors (`outband_certificate`)
- lemma: Second-order small-depth bound from evenness of ĝ, closing the u → 0 corner
  (`r_a97060`)
- lemma: Kernel-checked count of pairings (2m-1)!! with lesion tests and a proper-subset
  oracle (`rogue_frontier`)
- lemma: Global window optimum for xi' via the coercive operator A = I + T_{F_1}
  (`wide_search`)
- lemma: Out-of-band envelope: frequencies at or above 2L are free in the window reduction
  (`oob_envelope`)
- bound: LAW E/F/K: depth envelope for signed on/off incidence and the exact pair
  spectrum (`frontier_math`)
- bound: LAW G/H: a correlation is a gap, and n-independent anti-duplication caps
  (`frontier_math`)
- bound: Outer bound sup F <= 1 - (inf D2)^2 via the central-moment identity and a
  Neumann-series rational bound on inf D2 (`rogue_frontier`)
- construction: Lean cell-table architecture for certifying a kernel functional
  inequality (`ainta_seven_point`)
- construction: Period-37 Sturmian witness word with closed-form length margin and
  uniform tail estimate (`family_wall`)
- construction: Chain counting dual: configuration-free cap by cell partition, exact
  integer DP, and one-sided Lipschitz cell sups (`frontier_math`)
- construction: Odd-factor kernel: pointwise nonnegative, compactly supported transform
  nonpositive outside the band (`outband_certificate`)
- construction: Davenport-Heilbronn port of the truncated Weil form (structure-matched
  rival control) with attribution by dictionary decomposition (`rogue_frontier`)
- construction: Source-admissible closure certificate: exact rational strict-concavity
  plus C^3 endpoint tapers (`wide_search`)
- calibration: Cover level c(n−1)/2 for the near-zero cover at n ≥ 4
  (`ainta_seven_point`)
- computational technique: Exhaustive kernel-zero seeding for the F_n minimiser
  (`ainta_seven_point`)
- computational technique: Interval-table certification discipline: inflate caps off the
  attained supremum and round-trip the generator against the kernel's arithmetic
  (`frontier_math`)
- computational technique: Control-ladder calibrated extrapolation for LP ladders
  (`outband_intake`)
- computational technique: Ball LDL^T inertia ladder with an exact-dyadic Rayleigh
  witness (`r_ac9ca3`)
- computational technique: One ball LDL^T factorisation yields the inertia of every
  leading principal submatrix (whole N-ladder per c) (`rogue_frontier`)
- computational technique: Residual-enclosed shifted Cholesky: a rigorous lambda_min lower
  bound where interval LDL^T is undecided (`oob_envelope`)
- computational technique: Exact finite-N CUE engine for band-Gram trace moments, with
  the fit-and-check polynomial identification protocol and the Wick regime boundary
  (`rogue_frontier`)
- control: Target-derived pressure-cutoff soundness rule for the box verifier
  (`ainta_seven_point`)
- control: Fault-injection harness for an interval certificate verifier
  (`ainta_seven_point`)
- control: Two-sided bracket on an infimum: interval certificate below, Arb point
  evaluation above (`ainta_seven_point`)
- control: Preflight arithmetic filter that reads the generated Lean, plus a
  fault-injected, must-fail axiom audit (`ainta_seven_point`)
- control: Shared-invariance test before promoting a repeated null to a constraint
  (`director_run`)
- control: Lesion the reference, not the instrument: mis-set a constant in the closed
  form to prove the agreeing comparison can disagree (`frontier_map`)
- control: Clean-kill exact witness against the first algebraic lemma (transpose vs
  conjugate-transpose) (`frontier_math`)
- control: Refinement-direction ladder with a structurally adjacent control
  configuration (`frontier_math`)
- control: Hardening control set for converting a sampled table to an enclosure table
  (`r_a97060`)
- control: Zeta control at the identical cell (rival discrimination in both directions)
  (`r_ac9ca3`)
- control: Dictionary attribution: isolating the off-line quadruple as the sole negative
  term of the explicit-formula decomposition (`r_ac9ca3`)
- obstruction: Scalar and moment-matched obstruction families: no universal recovery
  coefficient from rank, trace and positive-index inputs (`frontier_math`)
- obstruction: Sieve wall: constant-factor prime-pair upper bounds cannot open the λ > 1
  band (`frontier_math`)
- obstruction: Measure-level LP collapse: multiplicity types reduce out to the
  Montgomery–Taylor dual (`frontier_math`)
- obstruction: Place-local Selberg-bound gate and the non-assembly of local norms
  (`local_positivity`)
- obstruction: Ceiling: positive-definite (Gram) kernels cannot spend out-of-band
  form-factor positivity (`outband_certificate`)
- obstruction: Autocorrelation-kernel obstruction: inertia arguments cannot spend
  out-of-band positivity (`outband_intake`)
- obstruction: Universal certificate pinning and band-limited exclusion for the
  centre-gas gap (`r_b9552d`)
- obstruction: Scalar-moment joint-window LP collapses to the best single window
  (`wide_search`)

### Window Rayleigh ceiling and the sqrt(2) harmonic orthogonality

identity | `hunts/amtopa_ceiling/` | grade: VERIFIED in the hunt's own label (recomputed
from the primary source; float confirmation max |M[0,1:]| = 1.7e-16); not an enclosure

For a window family v = sum_j c_j w_j in the AF2026/AMTOPA construction, the window
constant is H(v) = 2 - 1/c1 with c1 = (u.c)^2 / (c^T M c), a Rayleigh quotient in the
coefficients, so its supremum over the whole coefficient space is the closed form H_max
= 2 - 1/(u^T M^{-1} u), attained at c proportional to M^{-1} u. For the frequency set
{w_0} union {2 j pi}: u_j = sinc(w_j/2) = 0 for every harmonic, and the off-diagonal
entry M[0,j] times 4 j^2 pi^2 D / S (S = (-1)^j sin(w_0/2), D = w_0^2/4 - j^2 pi^2)
reduces to 2 j^2 pi^2 (w_0^2 - 2)/w_0, which vanishes iff w_0 = sqrt(2). Hence at the
fundamental sqrt(2), and only there, the harmonics are M-orthogonal and each strictly
lowers H (about -0.59 c_j^2), and H_max = 0.67250070367941172655 (Theorem D, HD(1)) for
1, 2, 3, 7, 13, 17 and 25 terms alike.

Evidence: RESULTS.md section '4.1 The window: 16 free coefficients, and an exact ceiling
of zero gain' (lines 356-404); probe_window.py; section 8 'Knownness'
Prior art: unsearched; the hunt explicitly claims no novelty (Conrey-Ghosh-Gonek shape;
Rayleigh-quotient maximiser is standard); whether the w_0^2 = 2 decoupling is in the
literature was not checked
Reused in: hunts/outband_certificate/RESULTS.md
Why it travels: Gives an exact ceiling for any linear window family in a
Rayleigh-quotient functional without search, and the orthogonality criterion tells you
when adding basis functions cannot raise the constant.

### Finite Poisson lattice formula for the infinite-chain energy

identity | `hunts/family_wall/` | grade: DERIVED, VERIFIED against brute force;
minimisation over P ≤ 6 is MEASURED (an upper bound on the true minimum)

With f(t) = cos(√2 t)·1_{[−1/2,1/2]}(t), K = f̂ and w = FT(G)/K(0)², G = f∗f supported
on [−1,1] with G(u) = (1−|u|)cos(√2u)/2 + sin(√2(1−|u|))/(2√2) for |u| ≤ 1. For a
period-T configuration with P points x_j per period, Poisson summation terminates: W_inf
= (1/(PTK(0)²)) Σ_{|ν| ≤ T} G(ν/T)|Σ_j e^{−2πiνx_j/T}|² − 1, since G(ν/T) = 0 for |ν| >
T. Verified against a brute-force sum over 800,001 images to 7.9e-9 (the brute force's
own truncation error). The resulting W_inf(mean gap) curve is violently non-monotone
(commensurability with kernel zeros), which is why the finite-n ladder's convex
envelope, not the curve, governs the peak.

Evidence: FAMILY-LIMIT.md §2.6 (lines 499–529); periodic_energy.py;
artifacts/periodic-energy-curve.json
Prior art: none (standard Poisson summation; the finite termination is specific to the
compact-support kernel)
Reused in: FAMILY-LIMIT.md §1.4 chord reading
Why it travels: Exact, cheap periodic energies for any kernel whose autocorrelation has
compact support; replaces truncated lattice sums.

### LAW D: alias-free grid incidence identity and the rigid bilinear diagonal

identity | `hunts/frontier_math/` | grade: kernel-checked (Lean 4 + Mathlib, sorry-free,
standard axioms) for real arguments; the complex-argument form is hardened (truncation
ladder 1.7e-13 → 5.4e-19 at K = 150/300/600, lesion 65/64 grid stretch flat at 0.3038,
decoy refuted, DH rival defect 2.7e-14)

For a window φ that is even, bounded, measurable and supported in [−1/2, 1/2] (no
continuity, no decay), with φ̂(x) = ∫φ(u)e^{ixu}du, the family n ↦ φ̂(x−n)φ̂(y−n) is
summable over ℤ and Σ_n φ̂(x−n)φ̂(y−n) = 2π·FT(φ^2)(x−y) for real x, y (kernel-checked;
evenness is necessary, counterexample the indicator of (0,1/2] with grid sum 0 against
π). Proof route: polarised Parseval on ℝ/2πℤ rather than Poisson summation, which is why
bounded-measurable suffices. In the paper's units (window supported in [−L/2, L/2],
critical grid τ_k at spacing h = 2π/L, normalisation aL^2) and extended to complex
arguments the identity reads Σ_k φ̂(z−τ_k)φ̂(z'−τ_k) = L·Φ2(z−z') with Φ2 = FT(φ^2), and
taking z' = z gives Σ_k φ̂(z−τ_k)^2 = aL^2 for every z ∈ ℂ: the bilinear self-incidence
of a zero is exactly +m_ρ per unit multiplicity at every depth and position, so a
conjugate pair contributes bilinear trace +2m_ρ, while the Hermitian mass Σ|φ̂|^2 =
L·Φ2(2iy) is what grows like X^{|2β−1|}.

Evidence: hunts/frontier_math/law_d_incidence.lean (tsum_phihat_mul_phihat_even,
tsum_phihat_windowA/B, tsum_phihat_of_continuous, grid_incidence_needs_even);
TRANSPLANT-LEMMA.md §Seam (i), core: LAW D exactness is kernel-checked;
SIGNED-INCIDENCE-LAW.md §The three laws (LAW D) and §Controls ledger
Prior art: cited: the source paper's Lemma 2.2 (real arguments) and its Appendix B
numerical check at complex arguments; new here: the complex statement used structurally,
the bilinear/Hermitian split, the no-continuity hypothesis, and the Parseval proof found
by the Aristotle prover
Reused in: LEVEL2-GAP-CONSISTENCY.md (LAW G); LEVEL3-THETA-RECOVERY.md (LAW K);
LEVEL5-ENCLOSURE-AND-PAIRS.md (LAW L); LEVEL7-VCELL.md (LAW M); PREPRINT.md §What is
kernel-checked item 2; docs/27-state-of-the-transplant.md §2
Why it travels: Any Gabor/critical-grid Gram computation with a compactly supported
window gets exact incidence values with no aliasing term and no smoothness assumption,
including windows that jump at the box edge.

### k-pair identity and the three-term Gram form of the multi-pair slack (two-species reduction)

identity | `hunts/frontier_math/` | grade: measured (identities checked numerically to
1e-17 and 1e-25; the hunt's own label 'identity, checked, sufficient'); B ≥ 0 rests on
the kernel-checked energy_F_ge

With F(w) = Σ_a e^{i x_a w}, P(w) = Σ_p 2cosh(y_p w)e^{i t_p w} and D(y,s) = Qim(y,s)^2
− Qre(y,s)^2: margin_k = Eng(F+P) − (199/200)Eng(F) − n/200 − 4k = (4/A^2)·slack_k with
slack_k = Σ_p Shq(y_p)/2 − Σ_{p,a} D(y_p, x_a − t_p) + (1/400)Σ_{a<b} φ_r(x_a − x_b)^2 −
(1/2)Σ_{p≠q}[D(y_p+y_q, τ_pq) + D(y_p−y_q, τ_pq)] (checked against quadrature on Eng for
k = 1..4, mixed depths, worst residual 4.21e-17). Rewritten against the measure c_2 dw:
slack_k = B(T,y) + Cross + R(X)/400 with B(T,y) = ∫c_2(w)[cosh^2(yw)|T̂(w)|^2 − k]dw ≥ 0
(free: energy_F_ge on the pair centres, cosh^2 ≥ 1, c_2 ≥ 0), R = Σ_{a<b}φ_r(x_a−x_b)^2
≥ 0 (sum of squares), Cross = −Σ_{a,p}D(y, x_a − t_p) the only sign-indefinite term;
−D(y,·) = ∫c_2(w)cosh(yw)cos(sw)dw is positive definite by Bochner since c_2 cosh(y·) is
a positive measure on [−1,1]. The additive budget k·Shq/2 was never the budget
(coincident centres give B 175× larger than spread ones). D(0,τ) = −Kpair(τ) exactly
(Qim vanishes at depth 0), so the pair centres are atoms of a second species with the
same repulsion kernel at 400× the rate and the same window damage at doubled depth;
general depths split per pair as K_{y_p+y_q} + K_{|y_p−y_q|}. Two-species counting: m
atoms and j centres in one window (width ≤ 0.9860008) close by a square completion iff
D_1^2 ≤ 4(γ^2/800)κ(w_max), which holds with margin 327.9×, and maximising m j D_1 −
m(m−1)γ^2/800 − j(j−1)κ(w_max) over integers gives j = 1 optimal (recovering the k = 1
optimum m = 3): a second pair in the same window is never profitable.

Evidence: hunts/frontier_math/PROOF-LEDGER.md §The k-pair identity, and coordinator
defect #20; §ROAD B, step 2: the slack is three terms and two of them are free; §ROAD B,
step 3: the counting lemma; K2-TWO-SPECIES.md §0–§1; kpair_identity.py, gram_form.py,
two_species.py, counting_lemma.py
Prior art: unsearched
Reused in: K2-TWO-SPECIES.md (k = 2 equal-depth closure over the tau-table);
LATTICE-EXTREMALITY-ROUTE.md (centre-gas cost); hunts/r_a97060 (interval pass);
CROSS-ARM-REPLY.md
Why it travels: Shows how to rewrite a multi-source quadratic energy against its
positive spectral measure so that every term but one is nonnegative for free, before
charging anything per source; the failure of additive per-source budgets is diagnosed by
the same rewrite.

### Closed forms for the windowed sine-Gram moments m2, m3 as functionals of the window, with exact rationals for polynomial windows

identity | `hunts/rogue_frontier/window_opt` | grade: hardened (continuum derivation
cross-checked by the exact finite-N CUE lattice count at two windows; exact rationals;
two-backend enclosures for the strict improvement)

For the windowed Gram kernel K_v(x) = int_{-1/2}^{1/2} v(xi) e^{2 pi i x xi} dxi over
the unit-density sine process, with l1 = int v, W = 1_B * v, tri = 1_B * 1_B, B =
[-1/2,1/2]: E tr H^2/N = l1^2 + [int v^2 - int W^2]; E tr H^3/N = l1^3 + 3 l1 [int v^2 -
int W^2] + [int v^3 - 3 int (tri*v) v^2 + 2 int W^3]. With D2 = (int v^2 - int W^2)/l1^2
and D3 = (int v^3 - 3 int (tri*v) v^2 + 2 int W^3)/l1^3: m2 = 1 + D2, m3 = 1 + 3 D2 +
D3, F = 2 m2 - m3 = 1 - D2 - D3. Everything reduces to V0(x) = int_0^x v and P0(x) =
int_0^x t v via W(eta) = V0(1/2) + V0(1/2 - eta) and (tri*v)(s) = l1 - [2 s V0(s) - 2
P0(s) + 2 P0(1/2)], so polynomial v gives exact rationals. Witness: v*(s) = 1 -
(1467/1000)s^2 + (1159/1000)s^4 gives F = 2245228120295149280/3276332462159207451,
beating cos(8s/5) by 4.3148e-5 (both ball backends).

Evidence: RESULTS.md section 1 'Setup and derivation', lines 46-83; section 2 validation
(four routes, exact finite-N CUE cross-check), lines 85-120; section 5, lines 174-193
Prior art: cited: the 10 Aug 2026 'more than two thirds' preprint section 7.5(g) (m2
closed form sketched by the coordinator; m3 formula new here)
Reused in: RF-C003 promoted claim, re-run by hunt R-F00E48 (hunts/r_f00e48/probe.py pins
the rational)
Why it travels: Any certificate whose input is a spectral moment of a windowed Gram
matrix can now be optimised over windows exactly; the reduction to V0, P0 is the
reusable trick.

### Bridge identity between the BBLS basis Gram and the Vasyunin Gram, and the enclosure pipeline for Baez-Duarte d_N^2

identity | `hunts/rogue_frontier/nyman_beurling` | grade: measured with
enclosure-checked arithmetic (arb balls conditional on Vasyunin's published formula,
validated five independent ways)

With e_k(t) = {1/(kt)} on L^2(0, inf) and the repo's BBLS basis A_k on L^2(0,1): <A_j,
A_k>_{L^2(0,1)} = G_jk - G_j1/k - G_1k/j + G_11/(jk), where G is Vasyunin's Gram matrix;
derived from e_k(t) = 1/(kt) for t > 1 and validated across all 1225 entries of the
repo's digamma-based cache to 4.9e-61. Pipeline: the Vasyunin sum V(p/q) is an exact
integer matrix (reduced weights 2(mp mod q) - q) times a ball vector of cot(pi m/q),
using the pairing m <-> q-m and reflection V((q-p)/q) = -V(p/q); d_N^2 = 1 - b^T G^{-1}
b via arb_mat.solve at 192 bits (radii ~1e-56 to N = 1536). Calibration: cond(G) grows
almost exactly quadratically in N (not the folklore severe ill-conditioning); each extra
solve bit buys one enclosure bit; the obstruction to pushing the criterion is the 1/log
N decay, not conditioning. Exact anchor d_1^2 = 1 - (1-gamma)^2/(log 2pi - gamma).

Evidence: RESULTS.md section 1 'What was computed', lines 18-37; section 2 validation
battery and bridge identity, lines 39-64; section 6 'Conditioning, measured', lines
123-138
Prior art: cited: Baez-Duarte 2003, Vasyunin's formula, BCF arXiv:1211.5191,
Landreau-Richard 2002 (float values to n = 20000 as anchors)
Reused in: ties to zeta.criteria._bd_gram_block and zeta.criteria.baez_duarte_table (N =
50 cache)
Why it travels: The bridge identity lets any BBLS-basis result be checked against a
Vasyunin-basis computation and vice versa; the exact-integer-times-ball-cot
decomposition is the way to make cotangent sums enclosure-carrying at large q.

### n-point certificate-to-proportion bridge with block cap

lemma | `hunts/ainta_seven_point/` | grade: kernel-checked (Lean 4, sorry-free, axioms
[propext, Classical.choice, Quot.sound]); conditional on hCert, which at n=7,8 is an
interval-verifier acceptance, at n=3,4 discharged in Lean

For n ≥ 2, c > 0, integers m ≥ n, p > 0: if the finite inequality hCert: ∀ g ∈
ℝ^{n−1}_{≥0}, c ≤ F_n,p(g) holds (F_n,p(g) = (1/p)Σg_i + Σ_{i<j} (2/(n−(j−i)))
w(y_j−y_i), w = (K/K(0))², K(x)=∫_{−1/2}^{1/2} cos(√2 t)cos(2πxt)dt) and the side
condition A₀ = c(m−(n−1)) ≤ 1 holds, then liminf N₀^s(T,2T)/N(T,2T) ≥ Φ_n(c,m,p) = (H −
(n−1)(m−1)/(pm)) / (1 − c(m−(n−1))/m), H = 3/2 − (1/√2)cot(1/√2). The paper's numerals 6
and m−6 are the per-gap charge n−1 and window count m−(n−1); m is capped at (n−1)+⌊1/c⌋
(the min{1,·} in the block-defect lemma), so the bound is sawtoothed, not monotone, in
c. One genuine change was needed for general n: the pre_solve tolerance η =
min(εm/(m+3+(n−1)(m−1)), A₀) instead of the paper's min(ε/10, A₀).

Evidence: BRIDGE.md §1 'The n-point theorem, and the eight-point instance' (lines
85–147); TRUST-MAP.md §1.1–1.3 (lines 61–168); Lean:
lean/bridge/Zeta23Ext/Bridge/Main.lean n_point_bound
Prior art: cited: Ainta paper/riemann.tex (n=7 only, 1/500 hardcoded); generalisation to
n and the derivation of the cap are the lab's
Reused in: hunts/family_wall (uses Φ_n and the cap as its starting point);
THREE-POINT.md and FOUR-POINT.md (n=3,4 instances, unconditional bounds Φ₃, Φ₄)
Why it travels: Any finite-window pressure certificate for simple zeros plugs into one
parametric theorem; only (n, c, m, p) change.

### Sharp stability rank–trace inequality with no hypothesis on V

lemma | `hunts/ainta_seven_point/` | grade: kernel-checked (eleven declarations,
[propext, Classical.choice, Quot.sound], zero sorry)

For V : Matrix n r 𝕜 and Hermitian Q with positive index ≤ b: 2·tr(VVᴴ) + 4·tr Q − r −
4b + tr Ψ(VᴴV) ≤ ‖VVᴴ + Q‖_F², with Ψ(t) = (t−1)² for t ≤ 2 and 2t−3 otherwise
(stable_rank_trace_sharp). Ainta's form 4·tr(VVᴴ+Q) − 3r − 4b + tr Ψ(VᴴV) ≤ ‖VVᴴ+Q‖_F²
(which assumes column norms ≤ 1) follows. Identification: Ψ = gc 2 + 1 of
anthropics/zeta-23-lean, so the paper's 'new' lemma S2 is an instance of the upstream
kernel-checked rank_trace_mult at c = 2 evaluated in the eigenbasis of P = VVᴴ; the
column-norm hypothesis hV is decoration.

Evidence: ARISTOTLE-PROBE.md 'Verdict' and §1 'What was proved' (lines 7–75), §6 'What
hV is actually for'; Lean: Zeta23Ext/StableRankTrace.lean
Prior art: searched-and-found: Zeta23.ZeroSide.RankTraceMult.rank_trace_mult
(zeta-23-lean) is the same theorem at c=2; TRUST-MAP had filed it as 'a different one'
Reused in: BRIDGE.md skeleton (D(M) = rtrace (specMap hM Psi) with Psi = gc 2 + 1)
Why it travels: A defect-carrying rank–trace inequality valid for every Hermitian Q and
every V, usable wherever a Gram/projector energy is compared to a trace.

### Pinching inequality via row-stochastic spectral mixture (no Peierls, no unitary invariance)

lemma | `hunts/ainta_seven_point/` | grade: kernel-checked (part of the sorry-free
bridge)

For Hermitian M = U diag(λ) Uᴴ and an injective index map g selecting a principal
submatrix with spectrum μ: the matrix Y = Vᴴ(U restricted to rows g) has orthonormal
rows and diag(μ) = Y diag(λ) Yᴴ, so each μ_j is a convex combination of the λ_i with
weights summing to exactly 1 per eigen-direction (eigenvalues_submatrix_eq_mix). Scalar
Jensen then gives Σ_B tr Ψ(G_B) ≤ tr Ψ(M) for concave Ψ with NO positivity of Ψ needed;
positivity of Ψ enters only in the separate step D(M) ≥ D(M°). This replaces the paper's
one-sentence appeal to 'pinching is an average of unitary conjugations and X ↦ tr Ψ(X)
is convex and unitarily invariant', both halves of which are absent from Mathlib and
heavier than needed.

Evidence: BRIDGE.md §6 'Pinching (S14)' (lines 294–311); bridge/ARISTOTLE-pinching.md
Prior art: searched-and-found partial: upstream sum_gc_diag_le_sum_gc_eigenvalues
(RankTraceMult.lean:119) is the 1×1-blocks fibre at f = gc c; the general block form is
the lab's
Reused in: Bridge step S14 for every n
Why it travels: Block-diagonal pinching of trace-concave functionals appears in every
operator-counting argument in this programme; this is the cheapest formal route.

### Interior optimum in the pressure denominator and the affine-infimum concavity argument

lemma | `hunts/ainta_seven_point/` | grade: VERIFIED by inspection (the four structural
facts); the location of the optimum is INFERRED/float

Split F_n^{(p)}(g) = (1/p)S(g) + W(g), S = Σg_i, W the w-sum, and c(p) = inf_{g≥0}
F^{(p)}. As a function of u = 1/p, c is an infimum of affine functions of u, hence
concave and nondecreasing in 1/p; c(p) → W(0) = Σ_s (2/(n−s))(n−s) as p → 0⁺ (=12 at
n=7) and c(p) → 0 as p → ∞. Feeding into Φ: at large p the gain c(m−(n−1))/m → 0 and Φ →
H; at small p m_max = n−1 kills the gain while the penalty diverges, so Φ has an
interior maximum in p and the paper's p = 3000 is a tuning constant, nearly optimal
(peak at 3400 for n=7). Approximation Φ*(p) ≈ (H − (n−1)/p)/(1 − c(p)), accurate to
~1e-5.

Evidence: TRUST-MAP.md §1.5 'The third leg' (lines 228–314); RESULTS.md §3 'The peak is
at p = 3400' (lines 154–165)
Prior art: none; nothing in Ainta derives 3000
Reused in: hunts/family_wall §1.2–1.3 (closed-form monotonicity within a minimiser
family and the crossover formula)
Why it travels: Any bound with a linear-pressure certificate has the same trade-off; the
concavity argument fixes the shape without a search.

### Witness-leg barrier for the n-point pressure family, with the case split that makes it a proof

lemma | `hunts/family_wall/` | grade: DERIVED (audit's argument re-derived line by
line), VERIFIED numerically; nothing machine-checked

Let k = n−1 ≥ 2, c any uniform floor for F_k on nonnegative gap vectors, m at the cap q0
+ ⌊1/c⌋, Φ_n = N/D with N = Hm − q0(m−1)/p, D = m − cd, d = m − q0. Case split: if Φ_n ≤
H, then Φ_n ≤ H(1+W(g)) for any g since W ≥ 0. If Φ_n > H, then Φ_n − H = [Hcd −
q0(m−1)/p]/D > 0 forces pcH > 1 + c(q0−1), which is exactly the sign condition for Φ to
increase in m, so moving to m_max is legitimate, N > 0 there so replacing D by m−1
raises the quotient (step A), and m_max − 1 ≥ 1/c (step B). Then Φ_n ≤ Hm/(m−1) − k/p ≤
H + Hc/(1+(k−2)c) − k/p ≤ H + Hc − k/p ≤ H + HW(g) + (HS(g) − k)/p for every g ≥ 0
(since c ≤ F(g,p)). Witness leg: any g with S(g) = Σg ≤ (n−1)/H makes the pressure term
nonpositive, so Φ_n ≤ H(1+W(g)) for every p; reaching the ceiling would need W ≥
0.0138706 for every admissible witness. Trivial leg: Φ_n ≤ H(n−1)/(n−2). Sharp form with
finitely many witnesses: Φ_n ≤ H + max_p min_j [Hc_j(p)/(1+(k−2)c_j(p)) − k/p], c_j(p) =
W_j + S_j/p. The one-line chain as first written was invalid at two steps (denominator
replacement with negative numerator; evaluating at the cap without monotonicity),
exhibited by admissible counterexamples at n=3, c=0.01.

Evidence: FAMILY-LIMIT.md §2.1–2.2 (lines 189–314), §2.1a (AUDIT, lines 216–273);
chain_repair_check.py (6,475 increment-sign checks, 5,729 admissible triples, zero
violations)
Prior art: unsearched; novelty not declared
Reused in: RESULTS.md verdict sup_n Φ_n ≤ 0.675142509660254; the lab's reading of the
ainta ceiling (RESULTS.md 'Where the family runs out')
Why it travels: Converts a pressure-certificate bound into a pure energy statement at
fixed density; the case-split pattern applies whenever a Möbius-in-m bound is evaluated
at a cap.

### Integer trade with window decomposition: the k=1 retention inequality with no separation hypothesis

lemma | `hunts/frontier_math/` | grade: hardened (four independent instruments agree
plus an exact-rational certificate and a from-definitions reproduction); obligations O1,
O2, O5–O8 kernel-checked, O3, O4, O9, O10, O11 not; O9's 699-cell table decides at
kernel grade but its soundness seam lemmas are unwritten, so the composite is not
kernel-checked

Setting (bespoke, in Zeta23Ext/EForm3/Defs.lean): g(u) = cos(√2 u) on |u| ≤ 1/2, A = ∫g,
c_2 = g⋆g, Eng G = (1/A^2)∫_{−1}^{1} c_2 |G|^2, Qre/Qim the cosh/sinh transforms, Shq y
= Qre(2y,0)^2 − A^2, Kpair(u) = Qre(0,u)^2, Dam(y,s) = max(0, Qim(y,s)^2 − Qre(y,s)^2).
Claim (★★), for every n, every x, every t, every y ∈ [0,1/2]: 4Σ_j Dam(y, x_j−t) ≤
(1/200)Σ_{j≠k} Kpair(x_j−x_k) + 2 Shq(y); it implies (199/200)Eng(F) + n/200 + 4 ≤
Eng(F+P). The damage-only route (retention_of_damage) is false from n = 8 (8 ×
0.00439642 > Shq(1/2)/2 = 0.03375420), so the repulsion term must be kept. Three facts
make (★★) true: Kpair ≥ 0 pointwise (cross-group pairs may be dropped with no sign
bookkeeping); Kpair ≥ 39/50 on |u| ≤ 1 and ≥ 1/125 on |u| ≤ 6; Dam(y,s) = 0 for |s| ≤
28/5 and otherwise supported in nine windows I_k of length < 1 with rational endpoints,
left endpoints spaced > 6.16, caps c_k = 21/20 × sup(Dam/y^2) (table in §4), far field
by the proved majorant Wt with Wt(w) ≤ (637/1000)/w for w ≥ 1368. Lemma 5.1 (integer
trade): for q > 0, c ≥ 0, m ∈ ℕ, 4cm − q m(m−1) ≤ P(c,q) := max over m_0 ∈ {⌊1/2 +
2c/q⌋, ⌈1/2 + 2c/q⌉} of (4c m_0 − q m_0(m_0−1)). Summing window by window (q = 39/10000,
q_far = 1/25000) the deficit at y = 1/2 is 8.5555138e-2 against budget (51944/100000)/4
= 0.12986, surplus 4.4304862e-2, margin 1.5179×; n never appears. Closing argument
against the obvious alternative: relaxing the n unit atoms to a measure gives inf gap =
0.114022 − n/200 exactly linear from n = 6 on and unbounded below (mass escapes as
dust), so no convex relaxation of the atom constraint can close this; integrality is
spent only in Lemma 5.1.

Evidence: hunts/frontier_math/RETENTION-PROBLEM.md §1–§5, §7, §8, §9; PROOF-LEDGER.md
§The SINGLE-PAIR retention closed at hardened grade (four independent routes,
salvage_audit 7/7); NOVELTY-CHECK-RETENTION.md; exact_gap_attack.py, repulsion_trade.py,
near_coincident.py
Prior art: searched-and-absent, in the weakest sense: NOVELTY-CHECK-RETENTION.md finds
no occurrence of retention/Eng/Kpair/Dam in the upstream 316-file formalisation and
grades the inequality novel only because nobody had asked it
Reused in: K2-TWO-SPECIES.md (the three pillars transplanted to the centre species; k =
2 equal-depth closed over 6601 tau-cells); PROOF-LEDGER.md ROAD B step 3 (two-species
square completion, 'at most one pair per window'); hunts/r_a97060 (interval pass);
O9-SCOPING.md, O9-LEAF-REPAIR.md, LATTICE-EXTREMALITY-ROUTE.md
Why it travels: The pattern 'positive pair kernel with a short-range floor + damage
confined to sparse narrow windows + integer maximisation per window' bounds any
atom-configuration energy uniformly in the number of atoms, where convex relaxations
provably cannot.

### Homogeneity closure of the shallow end (an interval with no smallest point)

lemma | `hunts/frontier_math/` | grade: hardened (double precision; 18 cells tiling
(0,1/2] exactly, closes at 0.995 and 0.996, fails at 0.997 on the deepest cell)

When the adversary's damage scales as the square of the depth parameter (f^+(g,y) ≤ y^2
F̂(g); in the retention setting every deficit piece is P(c_k v, q) with v = y^2), each
cap piece is a maximum of finitely many affine functions of v vanishing at v = 0, hence
convex through the origin with P(λv) ≤ λP(v) for λ ∈ [0,1], and the budget is linear in
v (2Shq(y) ≥ (51944/100000)v; at the paper window slack(y)/y^2 ≥ 8L_2/A = 0.6199944, its
y→0^+ limit via sinh t ≥ t). Then a single finite check at the deepest point of a cell
covers every shallower depth, and the check at y = 1/2 gives the inequality for all y ∈
[0,1/2]. A geometric ladder of depth cells can never reach 0 and would leave (0,ε) open,
the same missing quantifier one decade lower. Measured margin runs from 1.72× at y = 1/2
to 2.51× as y → 0, so the shallow end is the easy case. Extension route for two depths:
every piece convex in (v_1,v_2) so the vertex argument would finish it, but the honest
convex majorant at the (1/4,0) vertex is too fat by ~0.015 (named obligation).

Evidence: hunts/frontier_math/RETENTION-PROBLEM.md §6 Uniformity in y, for free;
PROOF-LEDGER.md §Blocker 1 closed (single-pair layer): depth-uniform retention, row 'The
shallow end (no smallest point)'; PREPRINT.md §Statement item 1; K2-TWO-SPECIES.md §3
and §4; depth_uniform.py
Prior art: unsearched; elementary convexity
Reused in: K2-TWO-SPECIES.md §3 (k = 2 depth uniformity for free) and §4 (unequal-depth
route); k2_closure.py; PREPRINT.md
Why it travels: Any depth- or amplitude-parametrised inequality whose bad term is
homogeneous of degree 2 and whose budget is linear needs one check at the extreme, not a
ladder toward zero.

### Lattice extremality via the structure-factor identity and Newton's identities

lemma | `hunts/frontier_math/` | grade: measured (double precision, no enclosure); §1–§4
a proof sketch, not formalised; hypothesis H1 (periodic, ρ ≥ 1/(2π)) explicit; lattice
extremality as a whole not established

For a P-periodic centre configuration with offsets a_1..a_m and density ρ = m/P, the
per-centre cost J_h(T) = (2/m)Σ'_{p,q,n} h(a_p − a_q + nP) satisfies J_h(T) = 2ρĥ(0) −
2h(0) + (2/(mP))Σ_{j≠0} ĥ(2πj/P)|A_j|^2 with A_j = Σ_p exp(2πi j a_p/P) (Poisson
summation; residual < 4e-9 against direct summation on five configurations). If ĥ ≤ 0 is
supported in [−1,1] and vanishes at ±1 (here h = −κ, κ̂(ξ) = 2π c_2(|ξ|)(1 + cosh|ξ|),
and c_2 = g⋆g > 0 on (−1,1) because g > 0 on its support, c_2(±1) = 0 because the
supports meet in a point), every j ≠ 0 term is ≤ 0, so J ≤ LP(ρ) = 2ρĥ(0) − 2h(0),
strictly decreasing in ρ. For ρ ≥ 1/(2π): J(T) ≤ −4c_2(0) + 2κ(0) =
0.11433003938654052…, with equality iff ρ = 1/(2π) and A_j = 0 for j = 1..m−1, which by
Newton's identities (power sums vanish ⇒ elementary symmetric functions vanish) forces
the polynomial z^m − c, i.e. T is a translate of the 2π lattice; the threshold is sharp
because the constrained modes are exactly j = 1..m−1. Rectification gap closed by the
explicit majorant v(x) = c·(sin(x/2)/(x/2))^2 with c = K_1(0) = 0.9115647 (needs c ≤
cos^2(√2/2)(1 + cosh 1) = 1.4698290, margin 0.558; ∫v = 2πv(0) keeps tightness). Sparse
side ρ < 1/(2π): the bound is vacuous; the only route (a density-independent bound,
forced by linearity) is infeasible at bandwidth 1 by Boas–Kac/Shannon rigidity, short by
29% (3.5076780 vs 4.9441838). A sampled-point LP for u ≥ 0 is unsound (returns 4.908534,
dips negative between samples); the right tool is an SDP through the Fejér–Riesz
representation u = |h|^2.

Evidence: hunts/frontier_math/LATTICE-EXTREMALITY-ROUTE.md §1 The identity, §2 Three
facts about kappa_hat, §3 The bound, §4 Uniqueness, §5, §5a Gap B closed, §6a Gap A;
K2-TWO-SPECIES.md §5 T1 (amended 2026-08-20); lattice_extremality.py
Prior art: unsearched (Poisson summation, Newton's identities, Boas–Kac, Shannon used as
standard tools; the assembly for this kernel is the lab's)
Reused in: K2-TWO-SPECIES.md T1 row (closes the dense side of the centre-gas obligation)
Why it travels: Template for 'is the lattice extremal' for any periodic pair energy
whose kernel has a nonnegative compactly supported Fourier transform vanishing at the
band edge, including the uniqueness step and the diagnosis of why sampled LPs cannot
certify positivity.

### Edge lemma for autocorrelations of real even factors

lemma | `hunts/outband_certificate` | grade: proved (prose grade, not kernel-checked);
named as the natural next Lean target

Let u be real, even, in L^2, supported in [-s,s] with s the true support edge, and Khat
= u*u (autocorrelation). Then Khat is not nonpositive on any interval (2s-eta, 2s).
Hence a kernel K=|k|^2 with real even spectral factor either has supp Khat inside [-1,1]
or fails any 'nonpositive on the out-of-band strip' condition. Proof: near the edge only
the two ends of u meet, Khat(2s-c) = (W*W)(c) with W the edge profile; Titchmarsh's
convolution theorem puts 0 in supp(W*W); Laplace transforms at large real lambda give
(LW)^2 = L(W*W), a square equal to a negative quantity, contradiction.

Evidence: RESULTS.md section 5 'Its death, with proof', lines 154-173
Prior art: cited: Titchmarsh convolution theorem (used as published); the lemma itself
unsearched
Reused in: none recorded
Why it travels: Kills any signed-spectral-profile / difference-of-squares certificate
with real even factor before any price is paid; applies to every inertia-type argument
on band-limited kernels.

### Second-order small-depth bound from evenness of ĝ, closing the u → 0 corner

lemma | `hunts/r_a97060/` | grade: enclosure-carrying (python-flint balls at 96 bits,
cross-checked with mpmath.iv)

For D(u,τ) = −Re ĝ(u/2 + iτ)² with ĝ even with real Taylor coefficients, ĝ'(iτ) is
purely imaginary, so ∂_u D(u,τ)|_{u=0} = −2G(τ)Re ĝ'(iτ) = 0 identically (G(τ) = ĝ(iτ)):
D has no depth-linear term. Hence for every u ≤ b, D(u,τ) ≤ −G(τ)² +
(u²/2)sup_{[0,b]}|D''|, and the ratio bound 4max(0,D)/u² ≤ 4max(0, sup|D''|/2 − G²/b²).
Taking the smaller of this and the direct box bound closes the sup over the open depth
interval (0, 1/2] at the resonance cell τ ∈ [6.62,6.64] (a root of G) where a plain
branch-and-bound in u stalls at 0.1142 against a true 0.0673, bringing C1 ≤ 0.0703 and
the table to 0 nonpositive cells. No sampling grid starting at y = 0.05 can check y <
0.05, which is where the 0/0 lives; the enclosure pass had to prove it.

Evidence: RESULTS.md §2 'The one thing that genuinely resisted, and what fixed it'
(lines 63–102); probe.py lines 255–287 (second_order); Loose thread 4
Prior art: unsearched; hunt notes evenness of ĝ was used here for the first time in the
tree
Reused in: suggested for the unequal-depth majorant of K2-TWO-SPECIES.md §4 (not done)
Why it travels: Any ratio sup D(u)/u² with an even generating function has a vanishing
linear term; the second-order bound converts an unboundable open-interval corner into
one enclosed inequality.

### Kernel-checked count of pairings (2m-1)!! with lesion tests and a proper-subset oracle

lemma | `hunts/rogue_frontier/matchings` | grade: kernel-checked per the coordinator's
recorded recompilation (EXIT=0, standard axioms); the landing did not recompile, so a
fresh lake build is owed before the grade is cited outside the hunt

In Lean 4 / Mathlib (v4.33.0-rc2, rev 51e6992e), for pairings of a Finset s represented
as fixed-point-free involutions extended by the identity outside s (PairsUp),
card(pairings s) = (|s|-1)!! for even |s| and 0 for odd |s|; also card_pairings_two_mul
and 2^m m! card = (2m)!. Proof by Nat.twoStepInduction with a card_nbij' bijection
dropPair/addPair; 430 lines, 0 sorry, axioms [propext, Classical.choice, Quot.sound], no
native_decide. Controls: the oracle (three routes: brute force, partner recursion,
(2m)!/(2^m m!)) run before writing Lean; a kernel decide check on a proper subset
{0,1,2,3} of Fin 5 to exercise the extension-by-identity clause that the univ case
leaves vacuous; two lesions (wrong double factorial; deleted extension clause) each
compiled to EXIT=1. Not bridged to SimpleGraph.Subgraph.IsPerfectMatching (estimated
80-150 lines).

Evidence: NOTE.md; LOG.md entries 7-10 (lines 169-273); Matchings.lean; LANDING.md
verification paragraph
Prior art: searched-and-absent in Mathlib at the pin (compiled run_cmd over getEnv
sweeps: no Isserlis/Wick, no perfect-matching counting API)
Reused in: closes the blocker named at step A2c of hunts/r_8c3b94 (Erdos-Kac in Lean);
same count enumerated by sine_gram's moment engine
Why it travels: Library content usable by any Wick/Isserlis or Erdos-Kac formalisation;
the lesion-plus-proper-subset control pattern is the template for testing that a Lean
statement is load-bearing.

### Global window optimum for xi' via the coercive operator A = I + T_{F_1}

lemma | `hunts/wide_search/` | grade: ordinary derivation, self-reviewed (the theorem);
the constant is measured (five routes, three agreeing to 14 digits; 'converged
high-precision numerical evaluation, not an interval enclosure')

Let I = [-1/2, 1/2], H = L^2_even(I), F_1(x) = |x| - 4x^2 + sum_{k>=1} ((k-1)!/(2k)!)
(2|x|)^{2k+1} for |x| <= 1 (Farmer-Gonek-Lee form factor minus its spike), (T v)(s) =
int_I F_1(s-t) v(t) dt, A = I + T. Then: (1) ||T||_{2->2} <= 4/9; (2) <Av, v> >=
(5/9)||v||^2, so A^{-1} exists with norm <= 9/5; (3) w = A^{-1} 1 has a continuous even
representative with w >= 1/5 on I; (4) sup over 0 != v >= 0 of (int v)^2 / (int v^2 +
iint F_1(s-t) v v) = <1, A^{-1} 1> = c*, with equality exactly on the rays v = c w; (5)
the source functional's optimum c_lambda* is nondecreasing in lambda on (0, 1], so the
bandwidth-one optimum sits at lambda = 1. Numerically c* = 0.8838931253605797508..., H*
= 2 - 1/c* = 0.8686415005297670641..., Hd* = 0.9343207502648835320...; the source
paper's quartic is 1.5005e-6 below sharp and no admissible window reaches Wu's
unconditional 0.86957 (short by 9.285e-4).

Evidence: RESULTS-xiprime-global-optimality.md sections 'Theorem' (lines 12-84),
'Proof', 'Numerical status'; RESULTS-xiprime.md sections 'The answer', 'The functional',
'How it was checked'; xiprime.py
Prior art: searched-and-absent for the unconditional xi' window optimisation (confidence
0.85 stated); Farmer-Gonek-Lee Thm 1.1 and Chirre-Goncalves-de Laat (RH-conditional SDP)
cited; Wu 2015 read at primary source
Reused in: hunts/frontier_map/RESULTS-frontier-map.md;
hunts/frontier_math/RESULTS-frontier-math.md; hunts/outband_certificate/RESULTS.md;
hunts/wide_search/HANDOFF.md
Why it travels: The operator-coercivity route (norm bound on the kernel operator,
coercive A, optimum = <1, A^{-1} 1>, positivity of A^{-1} 1, monotonicity in the scale)
solves the window problem for any pair-correlation kernel with a bounded convolution
operator, e.g. higher derivatives once F_k is available.

### Out-of-band envelope: frequencies at or above 2L are free in the window reduction

lemma | `hunts/oob_envelope` | grade: ordinary derivation, independent referee PASS
(different model family); not kernel-checked

For supp f in [-L, L], |F|^2 is the Fourier transform of an autocorrelation supported in
[-2L, 2L], so any bounded almost-periodic H whose frequencies all satisfy |lambda| >= 2L
(boundary included) has integral of |F|^2 H equal to 0, for every complex f. The Weil
symbol may therefore be replaced by Psi_L + H without changing Q on the window, and
Zhu's one-stroke reduction (arXiv:2608.24827, Theorem 1.1) runs with S = sup(P_L - H)
in place of A_L = sup P_L. The best such S is exactly lambda_max of the windowed comb
operator (strong duality), reached at rate N^{-2} by explicit trigonometric H, and it
grows like e^L against Zhu's 4 e^L: the threshold stays doubly exponential, but the
matrix size needed at a fixed window drops by one to two orders.

Evidence: hunts/oob_envelope/theory/RESULTS.md sections 1 to 3 (Lemma 1, Theorem 1',
Theorem 2, Theorem 3); referee/REVIEW.md sections 2 to 4
Prior art: searched-and-found: Burnol 2000 (math/0101068, Theoreme 3.7) uses one
boundary cosine for the same purpose; Liu 2026 Theorem B is the operator form. The
systematic prime-comb use, the duality and the e^L constant were not found in the
searched scope (theory/RESULTS.md section 4.2).
Reused in: hunts/oob_envelope/numerics (support 1.6 and 2.38 window bounds)
Why it travels: Any positivity argument on a band-limited class may spend the symbol
outside the band for free; it turns a pointwise envelope question into an operator one.

### LAW E/F/K: depth envelope for signed on/off incidence and the exact pair spectrum

bound | `hunts/frontier_math/` | grade: hardened (random-subgrid envelope floors never
violated and nearly attained, worst margin +3.3e-4; LAW K eigenvalues to 8 digits at
three depths, x·y ~ 1e-16); derivations ordinary, self-reviewed

Define σ^2(y) by Σ_k (Im φ̂(t−iy−τ_k))^2 = L∫φ^2(u)sinh^2(yu)du = aL^2 σ^2(y),
independent of t (the imaginary mass is band-limited to [−L/2, L/2] with density
φ(u)sinh(yu), so it is alias-free). Since every omitted term of LAW D's real part is (Re
φ̂)^2 ≥ 0, for every subgrid S (any truncation, any placement) and real x: Re Σ_{k∈S}
φ̂(z−τ_k)^2 ∈ [−aL^2σ^2(y), aL^2(1+σ^2(y))] and |Im Σ_{k∈S} φ̂(x−τ_k)φ̂(z−τ_k)| ≤
aL^2σ(y) (Cauchy–Schwarz against the two alias-free masses), hence every normalised
on/off cross cell obeys 2Re(B̂(x,z)^2) ≥ −2σ^2(y), with σ(0) = 0: negative incidence
mass requires depth. LAW F: by convexity of sinh, σ^2(y) ≤ sinh^2(yL/2), and since 0 < β
< 1 unconditionally, σ(y) < sinh(L/4) for every zero at bandwidth L; a pair whose cross
column reaches |Im B̂| = m needs depth y ≥ y_min(m) := inf{y : σ^2(y) ≥ m^2} and is
impossible once m ≥ σ(1/2^−) (at L = 8, σ(1/2^−) = 1.315, so every m ≥ 2 dies). LAW I
sharpening: W(g,y) ≥ −σ^2(y)(1−ω(2g)) ≥ −(1+m_0)σ^2(y) with m_0 = −min ω = 0.2137172540
for this window. LAW K: for a pair u = x+iy at depth y, LAW D's u·u = 1 (real) forces x
⊥ y with |x|^2 = 1+σ^2, |y|^2 = σ^2, so spec(2(xx^T − yy^T)) = {2(1+σ^2), −2σ^2}
exactly, and against the flat charge 4 the pair retains slack exactly 8σ^2 + 8σ^4;
consequence (three-zero lemma): a pair with at most three on-line zeros in its negative
cells has net ≥ (8 − 6(1+m_0))σ^2 = 0.7177σ^2 > 0, placement- and depth-free.

Evidence: hunts/frontier_math/SIGNED-INCIDENCE-LAW.md §The three laws (LAW E, LAW F),
§The exclusion, wall by wall, §Controls ledger; LEVEL2-TWO-GAP-MARKED.md §LAW I: the
one-cell tightening; LEVEL3-THETA-RECOVERY.md §LAW K: the exact pair spectrum, §The
three-zero lemma
Prior art: cited: the paper knew the (1,1) signature of the pair block and Remark 5.10's
Hermitian mass; the envelope, the depth floor and cap, the eigenvalues pinned by depth
and the three-zero lemma are the lab's; no literature search recorded
Reused in: LEVEL2-GAP-CONSISTENCY.md; LEVEL3-THETA-RECOVERY.md; LEVEL4-COUNTING-DUAL.md
(cell sups use σ, E); LEVEL5-ENCLOSURE-AND-PAIRS.md (depth split σ^2(y±y'));
K2-TWO-SPECIES.md
Why it travels: Gives explicit, depth-graded lower bounds for the sign-indefinite part
of any windowed Gram matrix with complex (off-line) evaluation points, using only
alias-free masses and Cauchy–Schwarz.

### LAW G/H: a correlation is a gap, and n-independent anti-duplication caps

bound | `hunts/frontier_math/` | grade: hardened (float mirror vs mpmath closed form
4.5e-7; majorant, cap, decoy planted 4x too small fires 11/12, collapse lesion,
n-independence and duplication-cheat controls); derivation ordinary, self-reviewed

On the full grid the normalised on-line correlation of two zeros at gap g is exactly
ω(g) = Φ2(g)/Φ2(0), with ω(0) = 1 and |ω(g)| < 1 for g ≠ 0 (φ^2 ≥ 0 continuous with
interval support), so a declared correlation ≥ c caps the gap (at L = 8: c = 0.99 buys g
≤ 0.0719, c = 0.5 buys g ≤ 0.5557) and a marked two-gap word's outer correlation must be
ω(g_1+g_2), not a free value (the independence guess ω(g_1)ω(g_2) is refuted with
residual 0.13228305 at (0.7, 1.3)). With the paper's majorant |Φ2(r)| ≤ ψ(r) = min(L,
2/|r|, c_ρ/(w r^2)) (c_ρ = 4‖ρ'‖_∞ + 4‖ρ''‖_1 = 105/4 exactly for the septic ramp) and
local density ν (ν ≤ A_0 log T by Titchmarsh Thm 9.2), the incidence mass of one point
against any configuration is bounded independently of the configuration's size: Σ_{j≠i}
ω(x_i−x_j)^2 ≤ κ(ν) = 2ν[1 + Σ_{k≥1}(ψ(k)/aL)^2] and Σ_j |B̂(x_j,z)|^2 ≤ κ_cross(ν,y) =
2ν[E(y)^2 + Σ_{k≥1}(ψ_y(k)/aL)^2] with E(y) = Φ2(iy)/Φ2(0) and ψ_y(r) = min(aL E(y),
(c_ρ/w)cosh(yL/2)/r^2). Hence Σ_j 2Re(B̂(x_j,z)^2) ≥ −2κ_cross(ν,y), an n-independent
floor where level 1 had −2nσ^2(y) (crossover n > κ_cross/σ^2 = 72 at L = 8, y = 0.3),
and R(P) ≤ nκ(ν) for any real configuration, so n − 1 ≤ κ(ν) = O(log T): the obstruction
family's realisable size at height T is explicitly finite.

Evidence: hunts/frontier_math/LEVEL2-GAP-CONSISTENCY.md §Pinned inputs, §The two laws,
§The kill control, run, §The robust exclusion, §Controls ledger; gap_consistency.py;
test_gap_consistency.py
Prior art: cited: the paper's (2.17) majorant and Titchmarsh Theorem 9.2 as inputs; the
laws and the assembly are the lab's
Reused in: LEVEL3-THETA-RECOVERY.md (dense packing self-defeat);
LEVEL4-COUNTING-DUAL.md; LEVEL7-VCELL.md; SIGNED-INCIDENCE-LAW.md addendum (removes
n-extensivity)
Why it travels: Converts per-cell floors that scale with the number of points into a
per-point cap using only kernel decay plus a local density bound; applies to any
decaying-kernel Gram sum over a configuration of bounded local density.

### Outer bound sup F <= 1 - (inf D2)^2 via the central-moment identity and a Neumann-series rational bound on inf D2

bound | `hunts/rogue_frontier/window_opt` | grade: derived (exact rational chain end to
end on the hardened closed forms); slice sup derived in exact arithmetic; landscape
statements measured

F = 2 m2 - m3 = 1 - int lam (lam-1)^2 dmu_v(lam) where mu_v is the limiting spectral
measure of A = H/l1, a positive measure on [0, inf) since H is Gram. Hence F <= 1 for
every admissible window, F <= 1 - D2^2 pointwise (Cauchy-Schwarz m2^2 <= m1 m3), and sup
F <= 1 - (inf D2)^2. D2 = <v,(I-T)v>/l1^2 with T the tri-kernel operator (Fourier
multiplier sinc^2, tr T^2 = 1/2, ||T|| <= 1/sqrt2), and for int v = 1, <v,(I-T)v> >= 2c
- c^2 <1,(I-T)^{-1} 1>. The moments t_k = <1, T^k 1> are exact rationals; K = 44 terms
with tail t_44/(1 - 707107/1000000) give U >= <1,(I-T)^{-1}1>, inf D2 >= 1/U =
0.327499295198, sup F <= 0.892744211644411 (exact rational). Sharp for its inputs: the
two-point measure (d/(1+d)) delta_0 + (1/(1+d)) delta_{1+d} attains 1 - d^2. Companion:
the quartic slice sup is settled exactly by compactification (interior critical points
via Groebner eliminant, endpoint-zero and double-root boundary families, arc at
infinity), giving 0.685287032176998 <= sup F <= 0.892744211644412.

Evidence: RESULTS.md section 9.1 'The outer bound', lines 335-399; section 9.3 'Exact
slice suprema', lines 452-512; global_bound.py, global_slice.py
Prior art: unsearched; hunt notes closing the gap needs a time-band-limiting-style
exclusion of near-two-point spectral measures
Reused in: upgrades RF-C003's caveat from 'local search outcome' to 'unique critical
point, globally capped by a derived bound'
Why it travels: The moment-relaxation ceiling (positive spectral measure,
Cauchy-Schwarz, exact Neumann tail) applies to any 'optimise a polynomial in spectral
moments over windows' problem.

### Lean cell-table architecture for certifying a kernel functional inequality

construction | `hunts/ainta_seven_point/` | grade: kernel-checked (three_point_cert,
three_point_bound sorry-free, standard axioms; GitHub Actions run 32689888754 green);
four-point likewise per FOUR-POINT.md §5 axiom audit

Prove ∀ g ≥ 0, c ≤ F_n,p(g) in Lean without an interval tactic: (1) Kfun_eq_sinc: K(x) =
(sinc((√2−2πx)/2) + sinc((√2+2πx)/2))/2, total, no singularity case split; (2)
cos_sin_taylor12: for |θ| ≤ 1, twelve-term Taylor enclosures of cos and sin with error
|θ|^{12}·13/5748019200 (from Complex.exp_bound at n=12), wrapped as four monotone
one-sided bounds; (3) kfun_closed: k(x) = (cos b − 2γ b sin b)/(1 − 2b²), b = πx, γ =
(1/√2)cot(1/√2) = 3/2 − H, so one transcendental constant is enclosed once (gam_bounds
width 1.11e-8); (4) one general lemma wfun_ge (x nlo dhi …): (nlo/dhi)² ≤ w(x),
instantiated by generated cell lemmas wc_k with rational literals, angles reduced
exactly to half-integer anchors so θ ≤ π/4; (5) window [0,1/2] done from the sinc form
(sinc_taylor valid at 0), w ≥ 19/100 across the removable singularity; (6) pressure
cutoff Σg ≥ c·p closes everything outside a simplex by w ≥ 0 and linarith; (7) 1-D cover
lemma exporting only the near-zero intervals of the kernel, then bisection trees over
products of those intervals with leaf = sum of cell constants + linarith; (8) all
rationals rounded outward to fixed denominators, generator in fractions.Fraction, never
float. At n=3: 368 cell lemmas, 487 leaves, ~65 min cold CI.

Evidence: THREE-POINT.md §3 (lines 176–296); CERTIFICATE-ROUTE.md §4.1–4.4 (lines
223–306); FOUR-POINT.md §3 (lines 229–350); three_point_gen.py, four_point_gen.py
Prior art: searched-and-absent in pinned Mathlib: no numerical sin/cos evaluator, no
interval tactic (Real.cos_bound error 5/96·|x|⁴ is far too weak); cos_sin_taylor12 and
sinc_taylor are the lab's
Reused in: FOUR-POINT (imports the cell machinery from three_point_gen.py); lean/bridge
ThreePoint and FourPoint libraries; Palomar surface
Why it travels: Any inequality over a bounded region of a trigonometric/sinc kernel
functional can be kernel-checked in Lean by the same generator; the primitives
(Taylor-12 enclosure, anchor reduction, sinc window) are problem-independent.

### Period-37 Sturmian witness word with closed-form length margin and uniform tail estimate

construction | `hunts/family_wall/` | grade: AUDIT (mpmath.iv 100 digits, unsafe
direction) and VERIFIED here (famlib float and 60-digit integer-window sum agree to
1.3e-17); not machine-checked

g_i = 1 + ⌊18i/37⌋ − ⌊18(i−1)/37⌋ (nineteen 1s and eighteen 2s per period). Its prefix
of length k has S_k = k + ⌊18k/37⌋ ≤ (55/37)k, and 55/37 = 1.48648… < 1/H = 1.48698…, so
S ≤ k/H holds for every k in closed form with no per-n check. Tail estimate for n ≥ 12:
at least 5/12 of prefix gaps are 2s (min over 11 ≤ k ≤ 20000 of ⌊18k/37⌋/k is exactly
5/12 at k=12); every scale-s window has integer length ≥ s and w decreases at integers,
w(s) ≤ w(1)/s⁴ since 2π²s² − 1 ≥ s²(2π²−1); hence W ≤ 2[(7/12)w(1) + (5/12)w(2)] +
2w(1)(π⁴/90 − 1) < 0.003928331920529310 and H(1+W) < 0.675142509660253902. At integer j
the kernel collapses exactly to k(j) = (−1)^{j+1}/(2π²j² − 1), so W is a finite sum of
exactly representable terms. Small n (3–7, 11) closed with separately polished
interval-checked witnesses. Replaced a 367-value scan plus bolted-on trivial tail with
one word.

Evidence: FAMILY-LIMIT.md §2.3a (lines 357–437), §2.4 table; RESULTS.md §2;
period37_check.py; audit/periodic_certificate.py (directed intervals)
Prior art: unsearched
Reused in: RESULTS.md headline bound
Why it travels: A balanced word whose density beats 1/H by a rational margin gives an
all-n witness for any density-constrained energy bound; the integer-argument kernel
collapse makes W exactly computable.

### Chain counting dual: configuration-free cap by cell partition, exact integer DP, and one-sided Lipschitz cell sups

construction | `hunts/frontier_math/` | grade: hardened (level-5 ball-arithmetic pass at
128 bits, radii 1e-16 to 1e-20, secures θ* = 0.1 at the hunt window; the MT band dual
hardened in balls with no Lipschitz margin at θ* = 0.9988); the counting theorem itself
is elementary, ordinary derivation

Partition the offset line into cells of width δ. Same-cell pairs are within δ so each
pays internal mass at least K_δ = min_{[0,δ]} ω^2; adjacent-cell pairs pay at least
K_{2δ}; non-adjacent payments are dropped (one-sided in the adversary's favour). With
F_j ≥ sup over cell j of the damage's positive part and c = 1−θ, the adversary's value
is at most max over n_j ∈ ℕ of Σ_j [n_j F_j − c K_δ n_j(n_j−1) − c K_{2δ} n_j n_{j+1}],
a tridiagonal chain program solved exactly by dynamic programming (pentadiagonal
refinement adds K_3 = min_{[δ,3δ]} ω^2 with 3δ ≤ 0.9; with K_3 = 0 it reduces to the
chain within 1e-6). The chain term is load-bearing: without it the free density is 1/δ
and the scan fails by an order of magnitude (19.2 vs the plain bound at y = 0.45); at θ
= 1 every charge vanishes and the cap is infinite, matching the measured dense-regime
failure. Cell sups come from closed-form centre values of C = Re Φ2(g+iy), S = −Im
Φ2(g+iy) inflated by explicit constants |dS/dg| ≤ (L/2)aLσ(y), |dC/dg| ≤ (L/2)aL E(y),
|dS/dy| ≤ (L/2)aL E(y), |dC/dy| ≤ (L/2)aLσ(y), so f^+ ≤ 4(S̄^2 − C_und^2)^+/(aL)^2 on
the whole cell; the far tail uses the depth-scaled majorant |S| ≤ ψ_S(y)/g^2 with ψ_S =
(c_ρ/w)sinh(yL/2) + 4y cosh(yL/2) + y^2 aL sinh(yL/2), which vanishes linearly in y so
shallow cells (where slack also vanishes) are not silently failed. The sup grid must be
decoupled from the capacity partition δ; the Lipschitz inflation scales with the
sup-grid step, so coarsening the grid changes the theorem's constants (a 2x coarser
hardened run failed by −3.0 while the original resolution holds with +0.27 to +2.03
margins). Projection control: the bound must dominate every lower-level measured
adversary, which caught a factor-2 error in the damage. Band-partition variant (MT
window): partition by the damage field's own negative bands rather than a ruler, with
the off-band allowance exactly zero (an unresolved band would need an interior dip
excluded whenever q > (1/8)|q''|step^2), cap(θ) = 2Σ_k max_m[mF_k − (1−θ)m(m−1)K_k] +
closed-form 1/g^2 tail.

Evidence: hunts/frontier_math/LEVEL4-COUNTING-DUAL.md §The theorem, §One-sided cells,
§The soundness incident, §Measured record; LEVEL5-ENCLOSURE-AND-PAIRS.md §Gate 1: the
hardened scan, and what almost went wrong; LEVEL6A-THETA-FULL.md §Lever 1: the
pentadiagonal counting dual; TRANSPLANT-LEMMA.md §The dual; counting_bound.py,
enclosure_pass.py
Prior art: unsearched; elementary counting on top of the lab's LAW E/G/H
Reused in: LEVEL5, LEVEL6A, LEVEL6B, LEVEL7-VCELL.md (direct route: the same DP on the
joint damage field); TRANSPLANT-LEMMA.md band dual (θ* = 0.995 at the paper window);
PREPRINT.md; K2-TWO-SPECIES.md and k2_closure.py (tau-table); hunts/r_a97060 (interval
pass over the k=2 table)
Why it travels: Any problem of the form 'an adversary places atoms to maximise damage
minus a quadratic internal charge' reduces to a small integer DP once the kernel has a
positive short-range floor, and the one-sided cell-sup recipe makes the result
configuration-free.

### Odd-factor kernel: pointwise nonnegative, compactly supported transform nonpositive outside the band

construction | `hunts/outband_certificate` | grade: proved and verified on a grid of
step 1e-3 (min K = 0, max Khat on 1<|alpha|<3.05 = 1.5e-6 FFT noise, min -0.5)

k(x) = sqrt2 sinc(x) sin(2 pi x), real and odd, gives K = |k|^2 = sinc^2(x)(1 - cos 4 pi
x) >= 0 with Khat = tri(alpha) - tri(alpha-2)/2 - tri(alpha+2)/2, supported in [-3,3]
and nonpositive on |alpha| > 1. With 1 - c cos in place of 1 - cos the same holds with
K(0) = 1-c > 0. Together with the edge lemma this is a dichotomy: even factor is
Gram-able but strip-blind; odd/complex factor is strip-capable but never the kernel of a
Gram matrix (antisymmetric under difference of ordinates).

Evidence: RESULTS.md section 5 'And the lemma is false for the class one needs' and 'The
dichotomy', lines 175-193
Prior art: cited: Krein factorisation (as published); the explicit odd witness
unsearched
Reused in: none recorded
Why it travels: An explicit witness for the class of kernels that can spend out-of-band
positivity; usable as a test object for any future certificate class claim.

### Davenport-Heilbronn port of the truncated Weil form (structure-matched rival control) with attribution by dictionary decomposition

construction | `hunts/rogue_frontier/weil_trunc` | grade: hardened for every sign
statement and the transition curve (ball LDL^T, Rayleigh, acb_mat.eig agreeing);
measured for localisation, dictionary decomposition, and the mechanism reading

The CvS/CCM truncated Weil form Q = W02 - WR - Wp on the Fourier basis of L^2([0, L]), L
= log c, ports to the DH function with three changes dictated by its explicit formula:
(i) coefficient measure Lambda_f(n) = a_n log n - sum_{d | n, 1<d<n} Lambda_f(d) a_{n/d}
on all n >= 2 (no Euler product), band-limited to n <= c; (ii) no pole block (f entire);
(iii) archimedean kernel from Re psi_Gamma(3/4 + ir/2) - log(pi/5), x-space rho_1(x) =
e^{-3x/2}/(1 - e^{-2x}). The ported form is positive at every cell with N <= 32, c <= 47
(enclosure-checked), so 'positive with ground state locating zeros' distinguishes
nothing; the first negative cell on the integer lattice is (c*, N*) = (31, 60), even
sector, lam_min = -1.874e-31 (three rigorous routes), while zeta at the same cell is
+4.8e-100. Attribution: the ported G2 Thm 2.5 dictionary sum has exactly one negative
entry, the off-line quadruple 4 Re g_v(gamma_off - i delta) = -6.7e-29 (359x the
eigenvalue); crossing happens once the band edge 2 pi N / L reaches the off-line
ordinate 85.7 with amplification e^{delta L} = c^{0.3085}.

Evidence: RESULTS.md section 4 'The DH control', lines 137-192; section 8.1-8.3, lines
255-366; SOURCE.md section 4 'Davenport-Heilbronn portability'
Prior art: cited: Connes-van Suijlekom arXiv:2511.23257 Prop 4.1, CCM arXiv:2511.22755,
Groskin arXiv:2605.20224 / 2607.02828 (chi_3 port corroborates the shift), Connes
arXiv:2602.04022; the DH port and failure height searched-and-absent in those sources
Reused in: zeta.epstein.battery discipline (docs/09 gate #3); thread raised for an issue
on the N -> infinity limit at fixed c <= 30
Why it travels: A recipe for running any explicit-formula compression on the
RH-violating rival, and a way to attribute a negative eigenvalue to a specific off-line
zero rather than to 'the form went negative'.

### Source-admissible closure certificate: exact rational strict-concavity plus C^3 endpoint tapers

construction | `hunts/wide_search/` | grade: exact rational bounds (fractions.Fraction
and SymPy), self-reviewed, pinned by tests and two lesions; not kernel-checked

To show an L^2 optimiser w = A^{-1} 1 is the supremum over the source paper's physically
admissible (nonnegative, radially monotone) window class: (i) take an exact rational
even polynomial trial u (degree 10, coefficients c_0..c_5 = 427163/446844,
-205089/684401, -2976898/824779, -13369/15690, -104561/672519, -32375/630751), a
truncated kernel A_0 (M = 20 terms) with tail bound rho = ||A - A_0|| <=
45088768/2828846926917599723269509375 < 1.6e-20, residual r_0 = 1 - A_0 u with ||r_0||_2
< 7.875e-10 and ||r_0||_inf < 2.171e-5, and derive a uniform second-derivative bound
showing w is strictly concave hence strictly decreasing in |s| (concavity margin
+0.59326318); (ii) build source-admissible approximants v_L = w times a taper using
eta(x) = 35x^4 - 84x^5 + 70x^6 - 20x^7 on (0,1) (C^3, eta' = 140 x^3 (1-x)^3 >= 0,
||eta''||_1 = 35/8, int eta'^2 = 700/429, ||(eta^2)''||_1 <= 20615/1716), converging to
w in L^2 at rate 2/L; (iii) boundedness of A closes the quotient. Lesions: setting the
delta_0 coefficient 2 to zero is rejected; multiplying residual bounds by 101 flips the
concavity margin to -0.0128 and the verdict to false.

Evidence: RESULTS-xiprime-admissible-closure.md sections 'Theorem', 'Exact
strict-concavity bound' (lines 90-224), 'Explicit source-admissible sequence' (225-312),
'Closing the quotient', 'Executable evidence and lesions'; admissible_closure.py;
tests/test_pub1_admissible_closure.py
Prior art: unsearched
Reused in: none recorded
Why it travels: A reusable recipe for certifying that an abstract Hilbert-space optimum
lies in the closure of a constrained physical class: rational trial + tail bound +
derivative bound for shape, then an explicit C^3 taper with exact norms for
approximation.

### Cover level c(n−1)/2 for the near-zero cover at n ≥ 4

calibration | `hunts/ainta_seven_point/` | grade: kernel-checked as part of the
FourPoint build; the level rule itself is an ordinary derivation

At n=3 the adjacent-pair coefficient in F is 2/(n−1) = 1, so a gap x with c ≤ w(x)
closes the certificate alone and the 1-D cover can run at level c. For n ≥ 4 the
coefficient is 2/(n−1) < 1, so the cover must run at level c(n−1)/2 (3c/2 at n=4) so
that (2/(n−1))·level = c exactly; the near-zero intervals widen by ≈1.22× in half-width
(w quadratic at a simple zero). A sizing pass at level c gave leaf counts ~30% too
optimistic and would have produced a tree that looks right and proves nothing. Also:
beyond x ≈ √(0.06938/level) the local maxima of w fall below the level (envelope
γ²/(π²x²)), so the last basin merges into a tail interval running to the cutoff.

Evidence: FOUR-POINT.md §3.1 'The cover level: the correction that matters' (lines
237–277); four_point_preflight.py §2 checks the level explicitly
Prior art: none; lab-internal correction
Reused in: four_point_preflight.py (explicit level check so the mistake cannot recur)
Why it travels: Any n-point extension of the cell-table route must set the cover level
from the smallest pair coefficient, not from c.

### Exhaustive kernel-zero seeding for the F_n minimiser

computational technique | `hunts/ainta_seven_point/` | grade: INFERRED (float; every c_p
is an upper bound on the true floor)

Uniform multistart Nelder–Mead, differential evolution and sample-then-polish all miss
the global minimiser of F_6 at p=3000 (they return 0.003868–0.004140 against
0.0038262312), because the true argmin (1.046,1.989,1.986,1.042,1.977,1.045) is
non-palindromic and every symmetric basin is higher. What works: polish all 4^{n−1}
combinations of the first four positive zeros of k (1.057278, 2.030068, 3.020243,
4.015236) as seeds, then refine the best ~30 basins. Recovers the argmin to 1.2e-13 at
p=3000, used as the gate before applying the same method at every p and n.

Evidence: TRUST-MAP.md §1.5 lines 272–283; RESULTS.md §2–3 (float floors at n=7,8,9 with
1-2-2-1 structure)
Prior art: unsearched
Reused in: modal_npoint_sweep.py / artifacts/npoint-sweep.json; hunts/family_wall
(minimiser families as balanced 1-2 words)
Why it travels: Any energy over gap vectors whose kernel has zeros has minimisers on the
lattice of those zeros; the seeding rule generalises immediately.

### Interval-table certification discipline: inflate caps off the attained supremum and round-trip the generator against the kernel's arithmetic

computational technique | `hunts/frontier_math/` | grade: measured (cell counts,
inflation wall); the 699-cell table is kernel-checked for consistency only (all 18
chunks decide, no sorry/native_decide/axiom), soundness open

(i) An inequality that is an equality at an interior point of a box cannot be proved by
interval arithmetic at any table size: any enclosure of a box containing the argmax has
an upper bound strictly above the supremum, so the caps must carry documented slack.
Here c_k = 21/20 × sup(Dam/y^2) over I_k × [0,1/2] (sup attained at y = 1/2, interior);
the budget absorbs inflation up to 1.3945× before the surplus reaches zero, and a 1.02×
table closes with 0 undecided in 196 cells, so 1.05× sits inside both; buying the margin
costs 6.104e-3 of surplus. (ii) A generator that builds its transcendental leaves by one
route (Arb at 300 bits, outward rounding onto the 2^-64 grid, 4-ulp pad) while the
kernel builds them by another (truncated Taylor via hornerI, widen by one ulp, reduction
modulo a 2^-64 enclosure of 2π with Lean's truncating integer division) can only confirm
itself: decide +kernel refuted the 339-cell table on 7 of 9 chunks. The control is a
kernel-faithful model (same coefficient lists, SQ2 and PI2iv integers copied not
recomputed) plus #eval round-trips requiring the fixed-point integers to be equal, not
close (14/14 leaves, then 10/10 compositions one level up before the table was
believed). The faithful model doubled the cell count (339 → 699 at 1.20×; 325 → 618; 309
→ 568), with the width loss entirely in the trig leaves through argument reduction
(cosX2 39.9× wider, hyperbolics 1.0×, shc 0.7×). (iii) A green decide +kernel build then
certifies self-consistency of the table, not the enclosed statement, until the _mem seam
lemmas (rIv_mem, qreIv_mem, sqrScaled_mem, the shcSmall truncation lemma, the y = 0 case
split) connect enclosure to quantity.

Evidence: hunts/frontier_math/RETENTION-PROBLEM.md §4 'The caps carry deliberate slack,
and this is load-bearing'; O9-LEAF-REPAIR.md §1–§6; O9-SCOPING.md §2 The two knobs;
tests/test_o9_leaves_kernel.py; Zeta23Ext/EForm3/O9RoundTrip.lean, O9CompEval.lean
Prior art: unsearched
Reused in: hunts/README.md entry on the o9_leaf.py repair (476-cell kernel-model
reproduction); K2-TWO-SPECIES.md §4 ('exactly the O9-table technology, in the tau
dimension'); hunts/r_a97060
Why it travels: Applies to every numerically generated Lean or interval certificate:
budget the inflation explicitly against the attained supremum, and prove the generator
mirrors the checker's arithmetic bit for bit before trusting any cell count.

### Control-ladder calibrated extrapolation for LP ladders

computational technique | `hunts/outband_intake/` | grade: measured

When extrapolating a discretised LP ladder v(X) to its limit, run a matched control
ladder whose true limit is known (here the in-band LP, whose limit is the
Montgomery-Taylor dual 0.6725007) on the same grids (X, J) = (40,200), (80,320),
(120,480), (160,640), (240,960), fit the same three-parameter law a + b X^{-p} to both,
and report the control's miss as the method error. Here the difference ladder d(X) =
v_out - v_in extrapolates to +0.0065 while the control's known-zero excess extrapolates
to +0.0018, so the gain exceeds the method error by about 3.5x and the honest statement
is a range ([0.679, 0.682] for the class value, [0.005, 0.009] for the gain) rather than
a third digit. A ratio test (2.808, 2.714, 2.780, 2.869 looked flat) was tried and
withdrawn: over this range both ladders decay at nearly the same rate so the ratio is
uninformative under either hypothesis.

Evidence: RESULTS.md section '1. The measurement' (table, 'The difference is the signal,
and the method is calibrated before it is believed', 'A ratio test was tried first and
is withdrawn'); refit.py; RUNS.md
Prior art: unsearched
Reused in: docs/35-the-unspent-fact.md; hunts/outband_certificate/RESULTS.md
Why it travels: Any relaxation ladder converging from above can borrow the same
calibration: a sibling ladder with known limit on identical grids turns a fit into a
measurement with an error bar, and exposes ratio-type tests that carry no information.

### Ball LDL^T inertia ladder with an exact-dyadic Rayleigh witness

computational technique | `hunts/r_ac9ca3/` | grade: hardened / enclosure-carrying (ball
LDL^T inertia, exact-dyadic Rayleigh upper endpoint and Rump eigenvalue enclosure agree,
plus an independent mpmath float scout)

For a Galerkin/Gram matrix family indexed by band limit N in which the (N+1)-band matrix
is the leading principal submatrix of the N_max-band one, a single ball (Arb,
python-flint) LDL^T factorisation at N_max (precision 600–700 bits) returns the pivot
signs, and by Sylvester's law the number of negative pivots among the first N+1 equals
the number of negative eigenvalues at band N, so one factorisation per cutoff c yields
the entire N-ladder (first negative N, even and odd sectors separately). The
factorisation is declared conclusive only if every pivot ball excludes zero; a pivot
straddling zero returns inconclusive rather than a sign. To certify a specific negative
eigenvalue rigorously: take a high-precision float eigenvector (mpmath eigsy at 60 dps),
convert its entries to exact dyadics (mantissa × 2^exp), and evaluate v^T M v / v^T v in
balls; the upper endpoint is a rigorous upper bound on λ_min (−1.873935689e-31 < 0 at
(c,N) = (31,60)), cross-checked by acb_mat.eig Rump enclosure (radius ~3e-192) and by
the pivot ladder. Result of the sweep: c ≤ 30 positive to N = 128 (256 at c = 29, 30); c
= 31 first negative at N = 60 (even sector), N = 59 positive (+8.365e-31); c = 32..60
first negative N in 48..54 with crossing band edge 2πN/log c averaging 83.64 ± 2.44
against γ_off = 85.6993.

Evidence: hunts/r_ac9ca3/RESULTS.md §1 Positivity Horizon and the Crossing Curve; §2
Marginal Cell (31, 60) Multi-Route Verification; probe.py pivot_signs,
first_neg_from_signs, eig_enclosure_min, and the exact-dyadic Rayleigh block (~lines
432–460); origin hunts/rogue_frontier/weil_trunc/RESULTS.md §2 and §8.2 ('one
factorization per c gives the whole N-ladder')
Prior art: unsearched for the ball-arithmetic variant; LDL^T/Sylvester inertia and
Rayleigh quotients are textbook; the CvS/CCM truncated Weil form is used as published
Reused in: hunts/r_f00e48 (salvage of weil_trunc; agrees digit for digit on the DH
eigenvalue −1.87393568857018838648… and the zeta control);
hunts/rogue_frontier/weil_trunc (origin; r_ac9ca3 is the stable reference per
hunts/README.md)
Why it travels: Any nested-truncation positivity question (Weil forms, Li-type Gram
matrices, moment matrices) gets a rigorous first-failure ladder at one factorisation per
parameter, and any single negative eigenvalue gets a certificate from a float
eigenvector made exact.

### One ball LDL^T factorisation yields the inertia of every leading principal submatrix (whole N-ladder per c)

computational technique | `hunts/rogue_frontier/weil_trunc` | grade: hardened
(conclusive-pivot ball factorisations)

The (N+1)-band even-sector matrix is the leading principal submatrix of the Nmax-band
one, so the signs of the LDL^T pivots of one conclusive ball factorisation at Nmax give
the number of negative eigenvalues at every band N <= Nmax at once (negative pivots
among the first N+1). One factorisation per integer c (Nmax = 128, prec 600, about 1 s
each) replaces a per-(c,N) eigenproblem sweep; used with the Weyl-shift logic (a uniform
diagonal error eps shifts every eigenvalue by eps) to validate the DH diagonal constant
to 1e-30 via Gate H (DH diagonal = zeta diagonal + log 5 + a difference-kernel integral
decaying like r^-4).

Evidence: RESULTS.md section 8.2 'The transition curve (one factorization per c gives
the whole N-ladder)', lines 280-308; Gate H rationale, lines 44-50
Prior art: standard linear algebra (Sylvester inertia via LDL^T), unsearched as applied;
the cost-class change is the lab's
Reused in: dhneg_scan.py ladders for c in 6..60
Why it travels: Changes the cost class of any nested-band positivity sweep from O(#cells
eigenproblems) to O(#c factorisations).

### Residual-enclosed shifted Cholesky: a rigorous lambda_min lower bound where interval LDL^T is undecided

computational technique | `hunts/oob_envelope` | grade: hardened / enclosure-carrying
(two independent implementations, GL-96 and Clenshaw-Curtis-192, both Arb)

At condition numbers near 1e48 a ball LDL^T of A - lambda0 I leaves hundreds of pivots
straddling zero. Instead: take the exact dyadic midpoint matrix M of the assembled
balls, compute a plain Cholesky factor C of M - lambda0 I, freeze every entry of C as an
exact dyadic, and enclose Rres = M - lambda0 I - C C^T in Arb with every operand exact.
With r the max absolute row sum of Rres and e the max row sum of (entry radius +
quadrature radius), symmetry and Weyl give lambda_min(A) >= lambda0 - r - e. The factor
need not be accurate: its only job is to make r small, and r is enclosed. lambda0 is a
proposal (0.99 of a measured Ritz value, or an exact rational fixed in advance); a
Cholesky at 1.01 of the Ritz value must break, which is the built-in lesion.

Evidence: hunts/oob_envelope/numerics/stage_b_modal.py (positivity) and RUNS.md stage B;
referee/REVIEW.md "L = 1.19" positivity audit. At L = 1.19, N = 500: r ~ 1e-113, e ~
2e-63 against lambda0 ~ 5.7e-48.
Prior art: unsearched for this exact pipeline; residual-based eigenvalue inclusion is
standard verified numerics (Rump-style)
Reused in: none recorded beyond the two oob_envelope lanes
Why it travels: Any ill-conditioned positive Gram or Galerkin block where interval LDL^T
gives up but the gap to zero is many orders above the arithmetic noise.

### Exact finite-N CUE engine for band-Gram trace moments, with the fit-and-check polynomial identification protocol and the Wick regime boundary

computational technique | `hunts/rogue_frontier/sine_gram` | grade: integers exact;
polynomial and limit identifications measured (heavily overdetermined exact agreement on
the computed grid, Monte Carlo consistent); lambda forms conjectured on the sampled
grids

For T_{m,m'} = Tr U^{m-m'} over a band of d consecutive integers, U ~ CUE(N), E tr T^k
is an integer computed exactly: E prod_j Tr U^{h_j} reduces through determinantal
correlations and the Dirichlet kernel to lattice-point counts max(0, N - spread) per
signed permutation cycle over set partitions; validated by E|Tr U^h|^2 = min(|h|, N)
including h > N, Fubini term counts, and E tr T^3 = 2N^4 - N^2. Identification: fit a
degree-(k+1) polynomial in N through the k+2 smallest grid points, demand exact integer
agreement at every remaining computed value and at even N off the grid; m_k(lambda) is
the leading coefficient over q^k p on families N = qt, d = pt. Results: m_5(1) = 101/18,
m_6(1) = 640/63; m_k(lambda) piecewise with Wick polynomial below lambda = 1/floor(k/2)
and defects -(j lambda - 1)^{2j+1} g_{k,j}(lambda)/lambda above each 1/j. Calibration:
the Gaussian (Diaconis-Shahshahani) regime for joint trace moments needs total positive
frequency <= N, which is why a Wick-pairing engine gave the wrong m_4(1) = 49/15 against
the true 13/4; exact arithmetic was load-bearing because the defects vanish to order
2j+1 at breakpoints.

Evidence: RESULTS.md 'What happened so far' items 1-4, lines 19-43; moments_report.md
sections 1-3 (engine validation, lambda = 1 table, lambda structure and its
fit-and-check bookkeeping)
Prior art: cited: the source paper's m_k(1) = 1, 4/3, 2, 13/4 (7.5(f)); literature
surveyed stops at m_4 (searched-and-absent for m_5, m_6)
Reused in: window_opt/crosscheck_finiteN.py (read-only import of exact_finite_N.py) as
the independent validation of the m3 functional
Why it travels: An exact integer instrument for any CUE band-Gram moment, plus a
reusable identification protocol with explicit spare-point counts; the Wick-boundary
calibration warns every Gaussian-approximation moment computation at lambda near 1.

### Target-derived pressure-cutoff soundness rule for the box verifier

control | `hunts/ainta_seven_point/` | grade: measured (verifier re-run on Modal,
artifacts/modal-rerun-sound-cutoff.json)

In the Arb branch-and-bound verifier for F_n ≥ c, the compactification prune 'discard
any box whose gap-sum lower corner ≥ CUTOFF' is sound iff CUTOFF/p ≥ c, i.e.
CUTOFF_cells ≥ ceil(GRID·p·c). The published constant 45600 at GRID 4000, p 3000 encodes
exactly c = 19/5000; every run that raised only the target (Gohms 191/50000, and the
lab's own probes) pruned 3,087 boxes on unproved grounds. Repair: derive the cutoff from
the target (46,400 cells sound for c ≤ 0.003867) and re-run; node counts moved by tens,
all acceptances stood. Node-for-node reproduction of a published run is agreement, not
soundness.

Evidence: TRUST-MAP.md §5.1 'The Gohms variant's compactification prune is unsound at
its own target' (lines 590–634); RESULTS.md §3 'A defect in every raised-target run'
(lines 100–122) and §7 (lines 289–298)
Prior art: searched-and-absent: defect present in the published verifier and in the
Gohms issue; reported upstream
Reused in: verify_n.py / modal_verify_n.py (cutoff derived from target rather than
hardcoded); the eight-point certificate
Why it travels: Any verifier that prunes by a linear term must have its prune constant
tied to the target; hardcoded prune constants silently encode one target.

### Fault-injection harness for an interval certificate verifier

control | `hunts/ainta_seven_point/` | grade: MEASURED, both runs

To test that a branch-and-bound interval verifier can fail (not merely that it
reproduces): (i) a known-false target just above the float floor must be REFUSED at a
terminal cell; (ii) four planted unsoundnesses (prune ignoring the target, kernel lower
table inflated by 2e-4, coefficients scaled by 1.01, the minimiser's boxes dropped) must
each flip that refusal to ACCEPTED. Pitfall recorded: when the functional has a symmetry
(F is reversal-symmetric), all symmetric images of the minimiser's box must be dropped,
else the verifier refuses at the mirror and the fault looks undetected. Passed 4/4 at
n=3 and n=7.

Evidence: RESULTS.md §7 (lines 289–298); RUNS.md runmanifest
'ainta_seven_point-2026-08-31-verify-n-rescue-and-fault-injection' (lines 395–408);
verify_n_faults.py
Prior art: unsearched
Reused in: none recorded
Why it travels: Applies to any accept/refuse interval verifier: it is the only way to
distinguish a verifier that is right from one that cannot say no.
Index note: Fault-injection of a verifier is the lab standard; this is the
interval-certificate instance.

### Two-sided bracket on an infimum: interval certificate below, Arb point evaluation above

control | `hunts/ainta_seven_point/` | grade: hardened (interval-enclosed lower end, Arb
enclosure upper end)

To make an 'apparent floor' rigorous on both sides: the lower end is the largest
rational target the interval verifier ACCEPTS (a proof that inf F ≥ c), the upper end is
an Arb ball evaluation of F at the float argmin (any point value is an upper bound on
the infimum). Gives 0.003826 ≤ inf F_6 ≤ 0.0038262312115073 (width 2.3e-7) and 0.0041763
≤ inf F_7 ≤ 0.0041773221. The upper end is a value at a rounded point, not the infimum;
family_wall later found two independent minimisers 2.0e-13 below it, which is the
correct behaviour against an upper bound.

Evidence: RESULTS.md §3 'And the bracket is rigorous on both sides' (lines 89–98) and
eight-point bracket (lines 181–182); family_wall/FAMILY-LIMIT.md §3 (lines 533–556) on
how to read the upper end
Prior art: unsearched
Reused in: hunts/family_wall (control on n=7,p=3000; corrected its own reading of the
number)
Why it travels: Standard shape for any 'how low does this functional go' question where
a refusal-capable verifier exists.

### Preflight arithmetic filter that reads the generated Lean, plus a fault-injected, must-fail axiom audit

control | `hunts/ainta_seven_point/` | grade: MEASURED / VERIFIED (preflight exit 0,
audit fixtures)

Before spending a CI build: (a) a Python preflight re-reads the emitted Lean text (not
the generator's in-memory tree, so emission bugs are caught) and checks against the true
w from the sinc form that every cell constant is a lower bound (401-point sweep per
cell), the cover is contiguous and hits the cutoff exactly, and at every leaf the
invoked cells cover the ranges the branch conditions force and the linarith combination
is true; fault-injected four ways, 4/4 caught. (b) The #print axioms audit is scoped to
the advertised declaration names, accepts choice/Classical.choice as one axiom, REQUIRES
all advertised names to be present (an empty log cannot pass), and is tested against
three fixtures: the real log passes, a planted sorryAx fails, an empty log fails. (c)
Set autoImplicit := false in a package whose point is an advertised theorem; with it on,
unresolved names (HD, Ncount, N0simple) silently became implicit variables and the
statements were briefly about nothing.

Evidence: THREE-POINT.md §4 (lines 299–347), §5 'The axiom audit, VERIFIED' (lines
515–538), §7 autoImplicit bullet (lines 600–608); FOUR-POINT.md §4 (lines 353–358);
RUNS.md line 380
Prior art: unsearched
Reused in: four_point_preflight.py (extends three_point_preflight.py);
.github/workflows/three-point.yml audit step
Why it travels: Generated-proof pipelines fail at emission and at audits that cannot
fail; both checks are generic to any Lean table generator.

### Shared-invariance test before promoting a repeated null to a constraint

control | `hunts/director_run/` | grade: argument with an in-tree counterexample;
disposition of the universal: REJECTED (director's ledger)

Before a repeated failure across N instruments is promoted to a class-level constraint
('coefficient-side statistics cannot see the critical line'), check whether the
instruments share an invariance. The three instruments (factorization defect D(f),
Fourier quasicrystal separation, local-positivity c_p) are each invariant or nearly so
under the twist a_n -> n^delta a_n, which is what produced the common blind spot; the
universal is refuted in-tree by Titchmarsh 14.25(B)/(C) (zeta/criteria.py face 1), an
RH-equivalence in the coefficients of 1/zeta alone. Rule: a repetition across
instruments is evidence about the instruments before it is evidence about the subject; a
'counterexample' offered against a universal must be nontrivial in the sense the claim
intends (sigma_a, d_p died to this; theta survived only for zeta).

Evidence: GRAVEYARD.md entries G1 and G2 (lines 10-60); CLAIMS.md entries C-SHIFT-01,
C-SHIFT-02, C-SHIFT-03
Prior art: searched-and-found for the shift computation itself (C-SHIFT-02 is the
Selberg-class theta < 1/2 axiom, Conrey-Ghosh 1992; Jacquet-Shalika); the control rule
is the run's own
Reused in: docs/25-the-director-run.md
Why it travels: Applies to any 'N independent probes all failed, therefore the class is
closed' argument: first exhibit the symmetry the probes share, or the closure is about
the probes.

### Lesion the reference, not the instrument: mis-set a constant in the closed form to prove the agreeing comparison can disagree

control | `hunts/frontier_map/` | grade: measured (float; 'a map, not a result')

When a numerical optimiser is cross-checked against a published closed form (here the
lambda-landscape optimum c*_lambda = sqrt2 tan(theta)/(1 + theta tan theta), theta =
lambda/sqrt2, paper eq. 7.4, not used in building the optimiser; max deviation 9.5e-15
over lambda in [0.1, 1]), also run the same comparison against the closed form with one
constant deliberately mis-set (sqrt2 -> 1.5): the minimum deviation must jump by orders
of magnitude (here 1.5e-2, twelve orders), which shows the comparison is capable of
disagreeing and the 9.5e-15 is a real agreement. Paired with a basis/quadrature
convergence ladder (stability < 6e-15 per rung against pinned constants) and a
monotonicity check on the refinement grid (0 decreases), reported in a controls ledger
with the rival control explicitly marked 'not run here, quoted'.

Evidence: RESULTS-frontier-map.md §1 'Cross-check (control 1)' and lesion (lines 40-48),
'Controls ledger' (lines 109-117); probe.py (crosscheck_zeta_curve, lesion,
convergence_response, monotonicity)
Prior art: cited: the 10 August 2026 paper eq. 7.4 for the closed form; the optimiser is
shared with hunts/wide_search
Reused in: inherits caveats from hunts/wide_search RESULTS files; none else stated
Why it travels: A cheap way to make any 'numeric matches closed form' cross-check
falsifiable: lesion the oracle side, not the instrument, and report the minimum
deviation the lesion produces alongside the agreement.

### Clean-kill exact witness against the first algebraic lemma (transpose vs conjugate-transpose)

control | `hunts/frontier_math/` | grade: kernel-checked (Lean 4, axioms
propext/Classical.choice/Quot.sound only) for the integer obstruction; exact
Gaussian-integer checker for the witness

Before any numerical search on a proposed inequality built over a pinned upstream
object, rebuild the upstream summand literally and attack the first lemma the chain
needs with the smallest exact-arithmetic witness. Here the upstream zero-side summand is
m·u_z·u_z^T (transpose, not conjugate transpose), so an off-line conjugate pair with u_z
= a+ib contributes 2m(aa^T − bb^T), a hyperbolic block, and the class interactions are
on/on m_x m_y B(x,y)^2, on/off 2 m_x m_z Re(B(x,z)^2), off/off 2 m_z m_w Re(B(z,w)^2 +
B(z,conj w)^2), of which only on/on is automatically nonnegative. The old instrument had
built u u* (always a squared modulus) and could not see the sign. Witness in one
dimension: u_x = 1, u_z = i, u_{conj z} = −i, all multiplicity one gives P1 = [1], Q' =
[−2], tr(P1 Q') = −2, refuting the asserted tr(P1 Q') ≥ 0; with five unit on-line labels
the proposed additive inequality demands 9 ≥ 13. The kill happens before taper,
truncation, census, bootstrap or LP questions can matter, and all downstream values
(0.6725124, 0.672529, 0.6725318) lose their zeta implication at once.

Evidence: hunts/frontier_math/CLEAN-KILL-REPORT.md §First false statement, §Smallest
exact obstruction, §Permanent controls; hunts/frontier_math/clean_kill.py;
lean/ZetaLean/FrontierMathObstruction.lean; RESULTS-frontier-math.md §0
Prior art: cited: the transpose summand is the upstream paper's own definition
(Zeta23/Defs.lean:298-305, ZeroSide.lean:314-379 at the pinned commit); the obstruction
and the witness are the lab's
Reused in: RESULTS-frontier-math.md §0 and §3; SIGNED-INCIDENCE-LAW.md (pins the
transpose reading as input); INTERACTION-CONTROL-REPORT.md;
tests/test_frontier_math_clean_kill.py; hunts/README.md frontier_math entry
Why it travels: Any transplant onto a formalised upstream must reproduce the upstream
bilinear form literally and be attacked by a minimal exact witness before a single float
scan is run.

### Refinement-direction ladder with a structurally adjacent control configuration

control | `hunts/frontier_math/` | grade: measured

A discretised lower bound that is real rises toward its tight relaxation under
refinement; a bound that falls under refinement is manufacturing floor. The
gap-distribution LP's first implementation assigned bins to cells by midpoint, crediting
straddling bins wholesale, and produced a false conditional 0.6728294 that would have
beaten Cheer–Goldston; the bin-width ladder caught it (the floor fell), and snapping
cell edges onto the bin grid restored the monotone ladder 0.69 → 1.02 → 1.44 → 1.47
×1e-5 for h = 0.02 … 0.0025. Conversely a numerically found counterexample must survive
a full ladder, not one refinement: sparse-24 read −0.004396 at step 0.005 / G = 60 and
closed at every finer setting; every-5 was +0.000075 coarse, −0.002288 at the first
refinement (step 0.0025 / G = 120), and +0.000069 to +0.000073 on the rest of the
ladder, identified as an artifact of one setting because the structurally adjacent
every-4 control closed at every step. Also: a per-cell allowance granted uniformly (a
Lipschitz margin of ~1.7e-3 on ~800 cells) manufactured ~1.3 units of damage and a false
obstruction; any per-cell allowance must be local and scale with the quantity it
protects (three occurrences: level-5 coarse-grid scare, level-7 mid-zone blanket,
transplant first session). And the evaluator must be read inside its calibrated domain:
the reported y = 0.979 'counterexample' sat outside the strip (y < 1/2 always) and
vanished when the search guard was clamped.

Evidence: hunts/frontier_math/RESULTS-frontier-math.md §5 ('A control earned its keep
here, twice'); BLOCKER2-INDOMAIN-FLOOR.md §1, §2, §3; LEVEL5-ENCLOSURE-AND-PAIRS.md
§Gate 1: the hardened scan, and what almost went wrong; TRANSPLANT-LEMMA.md §The first
session's obstruction was not one
Prior art: unsearched
Reused in: LEVEL4-COUNTING-DUAL.md (sup grid decoupled from the capacity partition);
TRANSPLANT-LEMMA.md band dual (off-band allowance exactly zero); enclosure_pass.py
defaults pinned at original resolution with the coarse failure kept as a negative
control
Why it travels: A generic acceptance test for any discretised floor (must rise under
refinement) and for any numerically found counterexample (must survive a ladder and
differ from an adjacent control).

### Hardening control set for converting a sampled table to an enclosure table

control | `hunts/r_a97060/` | grade: enclosure-carrying for the τ-table step; the
composite k=2 claim takes the grade of its weakest step (the convexity transfer, argued
not enclosed)

Replacing scans by bounds in the k=2 τ-table used six paired controls: (H1) enclosure vs
unpadded scan on the binding cells must be within a small ratio (1.0000–1.0004; the
deleted flat 1.05 pad was 100–400× the actual enclosure error); (H2) any heuristic prune
in the adversary's search is on the unsound side, so re-run exhaustively on binding
cells and report the delta (0.0); (H3) the enclosure's lower witness never exceeds the
scan value, so the old grid's blindness is qualitative (y < 0.05), not numerical; (H4)
planted cap fault: inflate the table's own caps by 1.01/1.02/1.05/1.10 and record where
the resonance cell dies (1.10×; the measured pass fired at 1.02×), showing the detector
still has power; (H5) cross-backend: mpmath.iv rectangles must contain the Arb balls
(they did, 1.8–3.5× wider); (H6) clamp check: verify the geometric assumption behind any
clamp (Kpair(min(dmax,6)) is a valid lower bound only if Kpair is monotone on [0,dmax];
widest component 1.9894 so it never bound). Replacement for the clamp: a running minimum
of the Kpair envelope over [0,dmax], which needs no monotonicity argument.

Evidence: RESULTS.md §1 table (lines 41–58), §3 'Controls' (lines 104–113), §4 (lines
115–134); ball_field.py
Prior art: unsearched
Reused in: named as the template for k ≥ 3 and the depth-1 far constant (loose threads
1, 5); K2-TWO-SPECIES.md §6 updated
Why it travels: A checklist for any 'measured → hardened' upgrade: it catches pads that
were standing in for enclosures, prunes on the unsound side, and clamps whose soundness
rests on unstated geometry.

### Zeta control at the identical cell (rival discrimination in both directions)

control | `hunts/r_ac9ca3/` | grade: hardened (ball LDL^T at precision 2400 plus Rump
eigenvalue enclosure; inertia conclusive)

A positivity failure on a structure-matched RH-violating rival (Davenport–Heilbronn,
off-line zero ρ ≈ 0.8085 + 85.6993i, δ = 0.3085) is evidence only if the same truncation
at the same (c, N) is strictly positive for ζ: at (31, 60) the zeta form has even
inertia (61, 0), odd (60, 0), λ_min(ζ) = +4.82160175e-100 (ball LDL^T at precision 2400
plus eigenvalue enclosure) against λ_min(DH) = −1.8739e-31, a discrimination of 100
orders of magnitude at one cell. The zeta control failing to remain positive is a stated
kill condition. The complementary direction is used by frontier_math for structural
lemmas: LAW D, LAW E and LAW H must also hold on the DH off-line zero (LAW D defect
2.7e-14 at depth 0.30851718; level-2 cap 31.856 obeyed), because a lemma failing on the
rival would be a bug and passing distinguishes nothing.

Evidence: hunts/r_ac9ca3/RESULTS.md §2 table row 'Riemann Zeta Control (31, 60)' and the
paragraph following; MISSION.md kill_conditions;
hunts/frontier_math/SIGNED-INCIDENCE-LAW.md §What is not achieved (third bullet) and
§Controls ledger row 'rival (Davenport–Heilbronn off-line zero)';
LEVEL2-GAP-CONSISTENCY.md controls ledger row 'rival'
Prior art: unsearched; the Davenport–Heilbronn function is used as published
Reused in: hunts/r_f00e48; hunts/rogue_frontier/weil_trunc; hunts/frontier_math levels
1–2 (rival checks on DH)
Why it travels: Every 'the instrument detects the off-line zero' claim needs the same
instrument at the same parameters on the object without one, and every structural lemma
about zeros must pass on the rival too.

### Dictionary attribution: isolating the off-line quadruple as the sole negative term of the explicit-formula decomposition

control | `hunts/r_ac9ca3/` | grade: measured (float dictionary sums with a 7%
bookkeeping residual; the eigenvalue itself is enclosed)

For the minimising eigenvector v of a truncated Weil form, expand the form value through
the zero-side identity λ = ⟨v, Qv⟩ = Σ_{γ>0} 2 g_v(r_γ). Every on-line zero contributes
a nonnegative term; the off-line pair contributes the quadruple 4Re g_v(γ_off − iδ). At
(31, 60): λ_min = −1.8739e-31, quadruple = −6.734989e-29, on-line partial sum (T ≤ 120,
64 zeros, all ≥ 0) = +5.9537e-29, tail model (T > 120 via mean density) +2.956e-30,
second off-line pair +7.57e-32, bookkeeping residual 4.67e-30 (~7% of the quadruple); λ
− quadruple = +6.716250e-29 > 0. Since all on-line terms are nonnegative the quadruple
is the sole negative contributor and removing it flips the sign, which attributes the
failure to that zero; corroborated by beam profiling of the eigenvector (95.63% of
coefficient mass within ±6.0 of γ_off at the deep cell (47, 64), peak mode k = 52 vs
target 52.51) and by the crossing band edge tracking γ_off across c ∈ [32, 60]. A second
negative eigenvalue appearing at c ≥ 44 matches the second off-line zero (δ_2 = 0.15083,
γ_2 = 114.1633), later because c^{δ_2} amplification is weaker. Kill condition: removal
of the quadruple not flipping the sign.

Evidence: hunts/r_ac9ca3/RESULTS.md §3 Mechanism and Localization (3.1 beam profile, 3.2
dictionary decomposition); §4 Second Off-Line Pair Detection; §1 band-edge tracking;
MISSION.md kill_conditions; probe.py dictionary_attribution_31_60
Prior art: unsearched; the explicit formula is standard
Reused in: hunts/rogue_frontier/weil_trunc/RESULTS.md (same decomposition at (31, 60)
and (47, 64))
Why it travels: Converts 'the form went negative' into 'this zero made it negative' for
any quadratic form with an explicit-formula expansion over zeros, and gives a
falsifiable kill condition for the attribution.

### Scalar and moment-matched obstruction families: no universal recovery coefficient from rank, trace and positive-index inputs

obstruction | `hunts/frontier_math/` | grade: exact integer/rational arithmetic
throughout (no optimizer, sampled grid, or floating tolerance); ordinary derivation,
self-reviewed

Given only the data the pinned rank-trace lemma consumes (P psd, rank P ≤ r, tr P ≤ s, Q
Hermitian, n_+(Q) ≤ b, A = P+Q), the sharp available inequality is ‖A‖_F^2 ≥ ((2 tr A −
tr P)_+)^2/(r+4b), which at c = 2 reduces to the paper's census form ‖A‖_F^2 ≥ 4 tr A −
3s − 4b and contains no on-line cross mass R(P) = Σ_{i≠j}|⟨u_i,u_j⟩|^2. Exact scalar
family: for integer m ≥ 1 take n = 2m^2+2 on-line labels with scalar evaluation vector 1
and one off-line pair with vectors im, −im; then P = n, Q = −(n−2), A = 2, R(P) =
n(n−1), census slack 3n, so any universal strengthening ‖A‖_F^2 ≥ 4 tr A − 3s − 4b + θ
R(P) forces θ ≤ 3/(2m^2+1) → 0. A direct-sum dilution (M = kn orthogonal positive
off-line blocks of eigenvalue 2+1/k plus L unit on-line blocks with L the nearest
integer to (‖A_0‖_F^2 − C N_0)/(C−1)) simultaneously matches tr A = N and drives
‖A‖_F^2/N to the paper's printed Frobenius ratio C = 1327499296/10^9 while R(P)/N
exceeds twice the proposed gap floor (checked exactly at m = 10, k = 100000).
Conclusion: separate on-line gap statistics plus aggregate off-line counts cannot yield
the strengthening; the missing datum is a signed joint on/off incidence law, and the
report specifies the level hierarchy (state retained / exact object / kill control)
needed to obtain one.

Evidence: hunts/frontier_math/INTERACTION-CONTROL-REPORT.md §Sharp inequality available
at this interface, §Exact scalar family, §Matching the paper's prime-side moments,
§Missing invariant, §Next configuration hierarchy; interaction_obstruction.py;
test_interaction_obstruction.py
Prior art: cited: the upstream rank-trace lemma (Zeta23/LinAlg/RankTrace.lean:157-195)
and the paper's §7.5(a); the obstruction families are the lab's
Reused in: SIGNED-INCIDENCE-LAW.md (walls W1–W4 exclude the family);
LEVEL2-GAP-CONSISTENCY.md (epsilon-robust exclusion via LAW H); LEVEL3-THETA-RECOVERY.md
Phase 5 battery; PROOF-LEDGER.md post-kill audit
Why it travels: Template for pricing any proposed strengthening of an inequality: build
in exact arithmetic the extremal family satisfying every retained hypothesis, show it
drives the coefficient to zero, then dilute it to match the printed moments so the
unrealistic-moments objection is closed too.

### Sieve wall: constant-factor prime-pair upper bounds cannot open the λ > 1 band

obstruction | `hunts/frontier_math/` | grade: ordinary derivation, self-reviewed

The paper's §4 machinery is support-agnostic; only the prime-side second moment caps the
support parameter λ at 1 (its §7.5(a)). The tempting unconditional route, bounding the
off-diagonal prime sums by a Selberg-sieve upper bound Σ_{n≤N}Λ(n)Λ(n+h) ≤ C·𝔖(h)·N with
classical C, fails structurally: for X = T^λ with λ > 1 the off-diagonal and
expected-value terms are each of scale (x/T)·N = T^{λ−1}·N and cancel to O(N) only under
Hardy–Littlewood with error; a sieve constant C multiplies the x-scale term, so the loss
is (C−1)·T^{λ−1}·N/log T, unbounded relative to N for any fixed C > 1. Only C = 1 +
o(1), Hardy–Littlewood itself, closes it. This makes the paper's Remark 1.1 wall ('0.70
needs support ≈ 1.04') mechanism-explicit: no constant-factor upper bound on prime pair
correlations, however sharp, opens the band.

Evidence: hunts/frontier_math/RESULTS-frontier-math.md §2 The λ > 1 sieve wall,
quantified; cited by docs/35-the-unspent-fact.md §4
Prior art: cited: the paper's Remark 1.1 and §7.5(a); the mechanism-explicit accounting
is the lab's
Reused in: docs/35-the-unspent-fact.md §4 (uses it to distinguish a wall from Hunt
#110's gap); hunts/README.md frontier_math entry; hunts/README.md line ~436 (contrast
with a construction)
Why it travels: Tells any future attempt at widening support that sieve-grade constants
are structurally insufficient and the required input is Hardy–Littlewood grade; the
T^{λ−1} scale argument transfers to any prime-side second moment beyond the diagonal.

### Measure-level LP collapse: multiplicity types reduce out to the Montgomery–Taylor dual

obstruction | `hunts/frontier_math/` | grade: measured (LP ladder, last rung ~78 min)
plus an exact reduction (ordinary derivation, self-reviewed)

Minimising the density of simple on-line points over multiplicity types p_m, off-line
pair density q and off-diagonal pair measure ρ ≥ 0, subject to the bandwidth-one data
R̂_2(α) = δ(α) + |α| on [−1,1], the type structure reduces out exactly: eliminating
(p_m, q) against the density constraint gives p_1 = 2 − D + Σ_{m≥3}(m^2 − 2m)p_m, where
the m ≥ 3 and off-line types enter with nonnegative coefficients m^2 − 2m and 0, so the
LP value is the dual of the Montgomery–Taylor extremal problem and integrality devices
beyond (m−1)(m−2) buy nothing at the measure level. Measured: the (X, J, ε) ladder
descends monotonically 0.6794 → 0.6776 → 0.6765 → 0.6756 → 0.6750823 (X = 40…640, J =
5X, ε = 0.4/X) with D climbing 1.3206 → 1.324918 toward the MT constant 1.3274993,
consistent with convergence to 0.6725007 from above and nothing in between; τ = −sinc^2
satisfies the data rows (GUE anchor), and the value moves in the predicted directions as
ε and X change. Consequence: the ceiling gap (0.6725007, 0.68185) is not about the pair
measure; it measures what configuration realizability (ordered real sequences) adds
beyond measure positivity. With BGSTB's unconditional out-of-band positivity added as
data the class value at (X = 80, J = 320) is 0.6863 and still descending.

Evidence: hunts/frontier_math/RESULTS-frontier-math.md §1 THREAD 1 answered: the
measure-level LP collapses, §4, §Controls ledger; configuration_lp.py
Prior art: cited: the paper's §1.2 scoping of Theorem D's optimality to F on [−1,1];
Cheer–Goldston 1993 closing remark; BGSTB 2023 (arXiv:2306.04799) Theorem 1 for the
out-of-band positivity, which the lab re-derived before finding
Reused in: hunts/README.md frontier_math entry; the ordered-gap LP of RESULTS §5 and the
whole level hierarchy build on 'the gap is configuration realizability';
docs/35-the-unspent-fact.md
Why it travels: Closes the class 'add multiplicity or type variables to the
pair-correlation LP' for any kernel with the same bandwidth-one data, and identifies the
realizability constraint as the only remaining lever.

### Place-local Selberg-bound gate and the non-assembly of local norms

obstruction | `hunts/local_positivity/` | grade: measured (float; the file states it
carries no enclosure at any step)

For a degree-d object with Satake parameters alpha_j at p, the place-local kernel
K_p^{(d)}(theta) = d + 2 sum_m lambda_m p^{-m/2} cos(m theta) has closed form sum_j (1 -
|alpha_j|^2/p)/|1 - alpha_j p^{-1/2} e^{i theta}|^2, so the coefficient-computable test
c_p <= d is exactly the local bound |alpha_j| <= sqrt p (zeta's threshold 2/(sqrt p + 1)
to 12 digits). Calibration: decoy swap moves the verdict by 15 orders; 300 random
period-5 nulls fail 100% with DH at the 6th percentile; lesion blindness threshold eps*
= 0.184 on the zeta -> DH interpolation; degree-2 family keeps margin >= 0.343 over 60
Satake angles; a legitimate degree-2 product with alpha = 2.3, 1/alpha is rejected at p
= 5 (c_p = 65.24), so the gate tests the local Selberg/Ramanujan bound, not 'has an
Euler product'. Obstruction: the prime side of the explicit formula decomposes place by
place as -sum_p log p (Q_p(f) - ||f||^2) with Q_p = (1 - 1/p) ||Phi_p f||^2 a genuine
norm at every place (reconstruction to 22 digits), but Q_p - ||f||^2 is not of definite
sign (52 of 60 places positive, 8 negative), so local positivity does not assemble into
a global one and is compatible with either sign of W. Director's adjudication:
c_p(zeta(. - delta)) = 2x/(1 + x), x = p^{delta - 1/2}, c_p <= d iff delta <= 1/2, is
KNOWN (Selberg-class theta < 1/2).

Evidence: CORRECTIONS.md section '2. New hunt: hunts/local_positivity/' (paragraphs
'What it establishes', 'Reference table', 'Controls', 'Where it dies', 'The honest
boundary'); localpos.py; director_run/CLAIMS.md C-SHIFT-01, C-SHIFT-02
Prior art: searched-and-found by the director run for the shift computation
(Conrey-Ghosh 1992 theta < 1/2; Jacquet-Shalika, stated sharp by Sarnak); the closed
form is standard Satake arithmetic; the assembly obstruction is the hunt's own
Reused in: docs/24-the-local-positivity-attempt.md; hunts/director_run/CLAIMS.md
Why it travels: The place-local decomposition with the measured sign-indefiniteness
closes the 'prove Weil positivity place by place' route with a mechanism, and the gate
with its calibrated blindness threshold is a ready coefficient-side instrument for any
rival battery.

### Ceiling: positive-definite (Gram) kernels cannot spend out-of-band form-factor positivity

obstruction | `hunts/outband_certificate` | grade: proved for the edge lemma and
dichotomy; 'read' for the compression structure (checked against the paper's full text);
prose grade

Any certificate whose positivity input is Weil's Hermitian form compresses to G = V V^H
+ Q with the on-line block a definite Gram matrix; its pair-weight kernel is
positive-definite, so Khat >= 0 everywhere; the out-of-band term int_{|alpha|>1} Khat F
is then nonnegative and unbounded above because F has no unconditional upper bound
outside the band, forcing Khat = 0 outside [-1,1]. A kernel with signed transform has
odd/complex factor (dichotomy above), equivalently an indefinite inner product, which
hunt #110 refuted by a 2x2 witness. So the strip is worth exactly zero to unconditional
Gram-form certificates; the LP value [0.679,0.682] is the RH-conditional
pointwise-positivity class.

Evidence: RESULTS.md section 8 'The ceiling, and why the LP priced the wrong class',
lines 240-322; kill condition 2 in MISSION.md
Prior art: cited: Chirre-Goncalves-de Laat 0.6792 (conditional), BGSTB arXiv:2306.04799,
Guth-Maynard arXiv:2405.20552, hunt #110 outband_intake witness
Reused in: placed hunts amtopa_ceiling, four_point_pressure, cycle_moments, wide_search,
prime_pair_error (RESULTS.md section 9)
Why it travels: Closes the whole class 'inertia/isolation argument on a kernel signed
only on a strip' and names the two inputs that would reopen it; any future out-of-band
proposal must first escape this argument.

### Autocorrelation-kernel obstruction: inertia arguments cannot spend out-of-band positivity

obstruction | `hunts/outband_intake/` | grade: measured; the 2x2 counterexample is exact
arithmetic

Any diagonal-isolation / inertia argument of the CGdL type requires the evaluation form
to be positive semidefinite, which forces the window spectral density v = phi^2 >= 0 and
hence the pair weight Khat = v * v >= 0 everywhere; the framework never has a free
signed ghat. The requirement cannot be relaxed to a weighted inner product tr(X^H S Y S)
with indefinite S: the rank half of the lemma survives but the inertia half needs
S^{1/2}; minimal counterexample Q = t [[0,1],[1,0]], S = diag(1,-1), c = 2 gives slack
+2.0 at t = 1 and -0.5 at t = 1.5, while 4000 random PSD pairs never violate (worst
slack +0.001321). First-order law: adding out-of-band mass -eps where F >= Lbar moves
the bound by dJ/deps = (J - Lbar)/g(0), adverse for Lbar below about 1.3275, so with
BGSTB's Lbar = 0 the direct channel pays nothing and the entire measured gain is
indirect (it licenses an in-band profile that is not an autocorrelation). Calibration of
where the information lives: at (X, J) = (80, 320) enforcing nonnegativity on (1, A_out]
gives 60.2% of the full gain by A_out = 1.25 and 91.4% by 1.5, so a certificate only
needs to be signed on a narrow strip just past the band.

Evidence: RESULTS.md sections '1b. The information is local: 91% of it sits in (1,
1.5]', '2. Why no certificate can spend it', '3. So the result is a gap, not a wall';
price_the_band.py
Prior art: cited: BGSTB arXiv:2306.04799 Thm 1 for the positivity; Chirre-Goncalves-de
Laat section 4 for the argument that does not transfer; frontier_math/paper_pin.py for
the int |Khat| discharge
Reused in: docs/35-the-unspent-fact.md; hunts/outband_certificate/RESULTS.md
Why it travels: Names the exact structural property (kernel must be a square) that any
attempt to use signed or out-of-band constraints in a Gram/inertia certificate must
escape, with a two-by-two witness that kills the obvious weakening.

### Universal certificate pinning and band-limited exclusion for the centre-gas gap

obstruction | `hunts/r_b9552d/` | grade: measured (double precision, no enclosures);
section 3's factorisation and sampling steps are quoted standard results, not proved or
probed

Let f(s) = Dam(1,s) - Kpair(s) = -kappa(s) + K_1(s)^+, J(T) the per-centre row, L = 2
kappa(0) - 4 c2(0) = 0.11433003938654052 its value on the uniform 2 pi lattice, and let
a certificate be g >= f pointwise with ghat <= 0, giving J <= B_g(rho) = 2 rho ghat(0) -
2 g(0). (P) If one rho-independent g proves J <= L at every density then necessarily
ghat(0) = 0, g(0) = -L/2, sup|g| <= L/2, ghat(j) = 0 for every integer j and g(2 pi n) =
f(2 pi n) for n != 0; the cheap necessary test sup_{s != 0} f <= L/2 passes with margin
3.05 (sup f = 0.0187431348 at s = 6.3974 vs L/2 = 0.05716501969). For the gap-B family g
= -kappa + c s, s = (sin(x/2)/(x/2))^2, ghat(0) = 0 iff c = 2 c2(0) =
1.6984559986366083, but admissibility caps c at cos^2(sqrt2/2)(1 + cosh 1) =
1.4698290136, a shortfall factor 1.15554665 (witness: ghat > 0, max +0.0839 at xi =
0.87493). By Fejer-Riesz factorisation plus critical sampling on 2 pi Z, any
band-limited (support in [-1,1]) nonnegative v = g + kappa vanishing on 2 pi Z minus 0
is c times the Fejer kernel, so the whole band-limited family is excluded: any
certificate closing gap A must carry Fourier mass outside [-1,1]. Consolation bound at
the cap: J(T) <= 2 kappa(0) - 2 cos^2(sqrt2/2)(1 + cosh 1) = 0.5715840115651507 for
every periodic configuration at every density.

Evidence: RESULTS.md sections '1. What a certificate that closes gap A must be,
exactly', '2. The family that closed gap B cannot close gap A, and by an exact amount',
'3. Why this is a statement about a family and not about one ansatz', '4. What the
family does give' (lines 40-170); section 5 controls (inflation-ladder planted fault
caught)
Prior art: unsearched for the pinning argument; Fejer-Riesz / Krein and Paley-Wiener
sampling cited as standard
Reused in: hunts/r_c7f779/MISSION.md; hunts/frontier_math/K2-TWO-SPECIES.md;
hunts/dps_cap/README.md; hunts/support_5418c63e/MISSION.md
Why it travels: Template for any Cohn-Elkies-style LP with a known extremal lattice:
equality at the lattice plus affine dependence on density pins the certificate's zeroth
moment, value at zero, sup norm and lattice interpolation, and gives a one-line
necessary test before any LP is run.

### Scalar-moment joint-window LP collapses to the best single window

obstruction | `hunts/wide_search/` | grade: argument, self-reviewed (the hunt labels the
file 'measured'); frontier_math later confirmed the collapse at the pair-measure level

If, for each admissible window v, the only data retained from the Weil-form matrix is
its trace and Frobenius norm, the resulting constraint is exactly s1/N >= H(v) and the
joint feasible set over all windows is the intersection of half-lines, i.e. s1/N >=
sup_v H(v). Therefore no LP or SDP built from per-window scalar moments can move the
single-window constant 0.6725007037...; any non-collapsing formulation must retain
cross-window information or act on the whole bandwidth-one form-factor measure before
reduction to one Rayleigh quotient. The full bandwidth-one certificate (c0 + sum_j s_j
r(j/N) <= p configuration by configuration) is an infinite LP dual and does not reduce
to single-window bounds.

Evidence: RESULTS-pair-ceiling.md sections '1. Joint scalar trace constraints collapse'
and '2. Full bandwidth-one certificates do not reduce to one window' (lines 31-66);
HANDOFF.md 'What is now closed, and what is left'
Prior art: unsearched
Reused in: hunts/frontier_math/RESULTS-frontier-math.md; hunts/wide_search/HANDOFF.md
Why it travels: Closes a whole class of 'combine many windows' proposals in one line and
tells any successor exactly what information a non-collapsing relaxation must keep.

## Higher xi derivatives and moments

Exact resolvent identities for xi derivatives, resummed Lambda-convolutions, mean-value
inputs and the moment obstructions to counting simple zeros.

- identity: Exact distinct-cycle Möbius corrections with overlap statistics
  (`cycle_moments`)
- identity: Exact resolvent identity for xi'''/xi'' and its frozen rational generating
  function Q(z), with strict sign alternation (`higher_xi`)
- identity: Squarefree depth identity alpha_k(n) = log(n) Lambda_k(n)/k and the
  support-density origin of the lost logarithm (`higher_xi`)
- lemma: Concave spectral score and quartic perturbation for simple-real counting
  (`cycle_moments`)
- lemma: Powerful-squarefree factorisation of resummed Lambda-convolution coefficients
  (RAMS1 mechanism) (`higher_xi`)
- lemma: Spacing-sensitive mean value with log-frequency spacing: off-diagonal O(sum n
  |c_n|^2) independent of polynomial length (`higher_xi`)
- lemma: Finite-prime peeling of the powerful Euler product to reach every compact
  coefficient band (`higher_xi`)
- lemma: Majorant-with-equality-recurrence bypass for tight aggregate inequalities
  (hprime gate) (`higher_xi`)
- bound: Factorial-permanent tail majorant with rational atom weights and a two-step
  geometric ratio (`higher_xi`)
- construction: Isospectral multisets with different simple counts under one fixed
  kernel (`cycle_moments`)
- construction: Exact rational Legendre window with an exact pointwise floor
  (`higher_xi`)
- control: Invariance claims need a control that moves the invariant's parameter
  (fault-injection power measurement) (`r_2ac05f`)
- obstruction: Third-moment obstruction block diag(b+2, b+2, −2b) (`cycle_moments`)

### Exact distinct-cycle Möbius corrections with overlap statistics

identity | `hunts/cycle_moments/` | grade: D_3 identity and the frame example
Lean-checked (AXLE, standard axioms); D_4 identity ordinary proof with exact-fraction
enumeration checks

For complex symmetric N×N K with K_ii = 1, M_j = tr K^j, S = Σ_i(Σ_j K_ij²)², Q = Σ_ij
K_ij⁴, and D_j the ordered j-cycle sum over pairwise distinct indices: D_3 = M_3 − 3M_2
+ 2N and D_4 = M_4 − 4M_3 − 2S + 10M_2 + Q − 6N (partition-lattice coefficients μ(F) =
Π(−1)^{|B|−1}(|B|−1)!, with the opposite-pair identification giving S and the
double-opposite giving Q, not power traces). With V_3 = Σ_{i,j,k distinct} K_ij²K_ik², S
= 2M_2 + Q − 2N + V_3 and Δ_4 = −D_4 − 2V_3 + M_2 − Q. Replacing S and Q by power traces
is an incorrect simplification: the frame v_1=(1,0), v_2=(0,1), v_3=(c,s), v_4=(−s,c)
has K² = 2K (all M_j = 2^{j+1}) but D_4 = −8c²s².

Evidence: MOBIUS-CORRECTIONS.md §1–§3 (eqs. 1–5); DistinctCycles.lean (D_3 over any
commutative ring), IsospectralCycles.lean (the frame example); distinct_cycles.py
Prior art: cited: Rudnick–Sarnak §4 (partition-lattice inversion, eq. 4.4–4.9) for the
general mechanism; the explicit overlap-statistic form is the lab's
Reused in: COUNTING-OVERLAP.md, OVERLAP-BOUND.md (S and Q as counting statistics)
Why it travels: Anyone converting all-index cycle sums to distinct-index correlation
sums (or back) needs exactly these coefficients; the overlap terms are where naive
simplifications go wrong.

### Exact resolvent identity for xi'''/xi'' and its frozen rational generating function Q(z), with strict sign alternation

identity | `hunts/higher_xi/` | grade: hardened (three independent exact q_j generators
and two scalable mean-square routes agree exactly through index 40; symbolic identity
checked by resummed_bridge.py); third exact route in hunts/r_2ac05f

With U = xi'/xi = L + D, D = zeta'/zeta, direct differentiation gives xi'''/xi'' = U +
(2UU' + U'')/(U^2 + U'), an identity with no coefficient-order cutoff; on Re s >= 1 +
epsilon the denominator inverts in the weighted Dirichlet algebra via b(1,s) = A_0^{-1},
b(n,s) = -A_0^{-1} sum_{d|n, d>1} a_+(d,s) b(n/d,s). Freezing L' = L'' = 0, z = 1/L, and
using the convolution atoms A = Lambda, B = Lambda log, C = Lambda log^2, the arithmetic
part becomes exactly Q(z) = -A + (2Bz - (2A*B + C)z^2)/((1 - Az)^2 + Bz^2), whose
coefficients q_n have the closed binomial form q_n = 2 sum_j (-1)^j C(n-1,2j)
A^{*(n-1-2j)} * B^{*(j+1)} - sum_j (-1)^j C(n-1,2j+1) A^{*(n-2-2j)} * B^{*j} * C. Every
word beta in q_n has entries in {0,1,2}, len(beta) + |beta| = n + 1, sign (-1)^{n -
len}; nonzero pairings need equal length with powers summing to i - 1, so sgn C_{2,i} =
(-1)^{i-1} exactly with no internal cancellation, and 2r + |beta| + |delta| - 1 = i
reduces the mean-square denominator to i!. Corrected sequence 1, -8, 24, -32, 64/3,
-64/3, 1216/45, ... (Bian's printed -4 dropped the multiplicity weights M(v_l)M(w_k) on
thesis p. 71).

Evidence: hunts/higher_xi/RESUMMED-BRIDGE.md Sections 2-3 'Exact representation without
geometric order', 'The corrected Q object is the frozen exact resolvent';
CORRECTED-F2.md 'Exact generating mechanism' and 'Exact coefficient fixture';
C2_PROVENANCE.md 'The one-line obstruction' and 'Independent exact routes'
Prior art: cited: Bian 2008 thesis (SHA-256 pinned), Farmer-Gonek arXiv:0803.0425
(level-1 control reproduced exactly); the rational generating function is the lab's
Reused in: hunts/r_2ac05f (fourth exact route, general-kappa form), URMS1-CLOSURE.md
Section 6, RAMS2-CLUSTER.md (the cluster expression is algebraically identical to Q(z)),
window_certificate.py, LEAN-FRONTIER.md
Why it travels: Replaces a finite geometric-order expansion by an exact resolvent whose
arithmetic part is a rational function of three convolution atoms; the same freezing
procedure applies to any higher logarithmic derivative of xi or of another completed
L-function.

### Squarefree depth identity alpha_k(n) = log(n) Lambda_k(n)/k and the support-density origin of the lost logarithm

identity | `hunts/higher_xi/` | grade: exact identities checked as formal polynomials in
independent symbols log p for every squarefree integer through 70 and every depth
(hardened by exactness); diagnosis ordinary derivation, self-reviewed

For the level-one resummed coefficient family a_T(n) = -Lambda(n) + sum_{k>=1} z_T^k
alpha_k(n), alpha_k = Lambda_{k-1} * (Lambda log), marking one of the k identical
convolution positions gives alpha_k(n) = log(n) Lambda_k(n)/k. On squarefree n =
p_1...p_r, alpha_k(n) = (r-1)! log n prod_{p|n} log p if k = r and 0 otherwise, so
distinct convolution depths never cross on squarefree support; cross-depth terms are
collision terms requiring a repeated prime. Pure prime powers: alpha_k(p^a) = C(a,k)(log
p)^{k+1}, hence a_z(p^a) = log p ((1 + z log p)^a - 2), with total square contribution
O_r(x^{1/2}(log x)^2). Diagnosis: the elementary majorant |alpha_k(n)| <= (log n)^{k+1}
summed over all integers gives sum (log n)^2 ~ x (log x)^2 already at depth zero,
whereas the prime-power support gives sum Lambda(n)^2 = x log x + O(x); the extra
logarithm is support density, created by replacing exact coefficients by a pointwise
envelope (planted dense-support control retains x(log x)^2).

Evidence: hunts/higher_xi/RAMS1-ATTACK.md, Section 2 'Exact squarefree identity' (lines
76-140) and Section 3 'The missing logarithm is support density' (lines 142-183,
classification table); URMS1-CLOSURE.md Section 2.1
Prior art: Farmer-Gonek-Lee cited for fixed-depth prime asymptotics; identity unsearched
Reused in: URMS1-CLOSURE.md Section 2 (RAMS1 theorem), RAMS2-CLUSTER.md, URMS2-ATTACK.md
Section 5
Why it travels: Any mean square of iterated Lambda-convolutions should be split by
squarefree support before majorising; the identity gives the exact squarefree main term
and localises all cross-depth interaction to repeated-prime strata.

### Concave spectral score and quartic perturbation for simple-real counting

lemma | `hunts/cycle_moments/` | grade: Lean-checked (AXLE, Lean 4.33.0, standard
axioms) for the spectral Jensen step, the quartic's concavity/bounds and the composition
under explicit diagonal-block hypotheses; adapted-basis construction and kernel-cycle
identification are ordinary proofs, self-reviewed, external review pending

Let A = Σ v_i⊗v_i + Σ m_j w_j⊗w_j + 2Σ n_l(g_l⊗g_l − h_l⊗h_l) on a finite real
inner-product space with unit v_i (s of them, 'simple'), unit w_j with m_j ≥ 2, and
pairs with ‖g_l‖² − ‖h_l‖² = 1 (no positivity of A). For every globally concave f with
f(0)=f(2)=0 and f ≤ 1: tr f(A) ≤ s. Proof via adapted subspaces U ⊂ V ⊂ W, the
diagonal-sum estimate Σ_{j≤d_U} α_j ≥ 2d_U, and the direction-sensitive comparison
f(α_j) ≥ Σ_i Q_ji² f(λ_i). Instance: q_t(x) = x(2−x)[1+t(x−1)+t²(x−1)²] is concave for
|t| ≤ √(5/8) and ≤ D_t = 1 + t²/(4(1−t²)), giving s ≥ [2N − M_2 − tΔ_3 + t²Δ_4]/D_t with
M_j = tr A^j, Δ_3 = M_3 − 3M_2 + 2N, Δ_4 = 2N − 5M_2 + 4M_3 − M_4; t=0 recovers s ≥ 2N −
M_2. Asymptotically, if M_2/N → c_2, M_3/N → c_3 with δ_3 = c_3 − 3c_2 + 2 ≠ 0 and
limsup M_4/N ≤ B < ∞, an explicit t = −sign(δ_3)·min(1/2, |δ_3|/(2(C+1))) gives a strict
gain. For the Fourier realisation with even p and conjugation-invariant multiset Z, M_j
= C_j(Z,p) the ordered cycle sums, nonreal pairs retained. At the Montgomery–Taylor
profile δ_3 = (6k−5)(6k²+6k−1)/24 < 0 with k = cot(1/√2)/√2, sign proved by elementary
inequalities 3/4 < k < 5/6.

Evidence: FINITE-THEOREM.md §2–§4, §7, §8, §10; Lean: SpectralJensen.lean,
QuarticScore.lean, CycleMomentAssembly.lean (FORMAL-CHECKS.json)
Prior art: cited: Lamzouri, arXiv 2609.02882 Prop. 2.1 (adapted subspaces, quadratic
score); the general concave score, quartic family and asymptotic condition are the
lab's; novelty not established
Reused in: MIXED-MOMENTS.md, THIRD-MOMENT-OBSTRUCTION.md, COUNTING-OVERLAP.md (all build
on §1 hypotheses)
Why it travels: Turns any bounded family of matched power-trace moments into a
simple-count lower bound with an explicit, tunable concave score.
Index note: Kernel-checked core; the adapted-basis construction around it is ordinary
proof.

### Powerful-squarefree factorisation of resummed Lambda-convolution coefficients (RAMS1 mechanism)

lemma | `hunts/higher_xi/` | grade: ordinary derivation, self-reviewed (exact algebra
and finite checks in test_higher_xi.py; prime-measure asymptotic and dominated
convergence are classical analytic inputs); 'remaining promotion gate is external
mathematical review'

Every integer factors uniquely as n = qm with q powerful, m squarefree, (q,m) = 1; put j
= omega(m) and B_{q,j}(z) = sum_{h>=0} C(j+h-1,h) z^h Lambda_h(q), the coefficient at q
of (1 - zA)^{-j}. For j >= 1 the positive part of the level-one family factors exactly:
sum_{k>=1} z^k alpha_k(qm) = (j-1)! z^j log(qm) prod_{p|m} log p B_{q,j}(z) (checked on
every eligible integer through 55). For q <= y and r_y = log y/lambda_T <= r_0 < 1, 0 <=
B_{q,j} <= (1 - r_0)^{-j}, and B_{q,j}(z_T) -> 0 for each fixed powerful q > 1; since
every powerful q = a^2 b^3 with b squarefree, sum_{q powerful} 1/q <= zeta(2) zeta(3),
so dominated convergence with the squarefree prime-measure majorant D^j y (log
y)^{2j+1}/(j!(2j-1)!) gives sum_{qm<=y, q>1, j>=1} |a_T(qm)|^2 = o(y log y) uniformly on
the compact band, and the j = 0 powerful integers contribute O(sqrt y (log y)^2). Result
(RAMS1, assuming RH): sum_{n<=y}|a_T(n)|^2 = y log y Phi_1(r_y) + o(y log y), Phi_1(r) =
1 - 2r + 2 sum_{j>=1} (j-1)!/(2j)! r^{2j}, uniformly for r_min <= r_y <= r_0 < 1.

Evidence: hunts/higher_xi/URMS1-CLOSURE.md, Section 2 'RAMS1 theorem' with 2.2 'Unique
support split', 2.3, 2.4 'Mixed repeated-prime strata vanish' (lines 58-201); hostile
controls Section 7
Prior art: cited Farmer-Gonek-Lee for fixed-depth prime asymptotics, Chebyshev estimate;
the split is unsearched
Reused in: RAMS2-CLUSTER.md Section 7 'Repeated primes' reuses the split after the
Gaussian mixture; BANDWIDTH-FORENSICS.md finite-prime peeling
Why it travels: Turns a uniform-in-depth second-moment problem for multiplicative-like
coefficient families into a squarefree main term plus a finite-harmonic-mass powerful
correction; applicable to any Borel/Laplace-resummed Euler-product coefficient.

### Spacing-sensitive mean value with log-frequency spacing: off-diagonal O(sum n |c_n|^2) independent of polynomial length

lemma | `hunts/higher_xi/` | grade: Montgomery-Vaughan application: ordinary derivation,
independently agent-audited (URMS2-051-AUDIT PASS on six gates); elementary substitute
and rational witness margins: kernel-checked (Lean 4, no sorry per LEAN-FRONTIER.md);
not externally reviewed

For distinct real frequencies lambda_n, the weighted Montgomery-Vaughan estimate is
int_U^{2U} |sum_n c_n e^{-it lambda_n}|^2 dt = U sum |c_n|^2 + O(sum |c_n|^2/delta_n),
delta_n the nearest-neighbour spacing. With lambda_n = log n, log(n+1) - log n >=
1/(n+1) gives delta_n^{-1} <= 2n for n >= 2, hence int_U^{2U} |sum_{n<=W} c_n n^{-it}|^2
dt = U sum_{n<=W}|c_n|^2 + O(sum_{n<=W} n |c_n|^2) with no condition W < U. Replacing
delta_n^{-1} by the worst spacing W had forced gamma < delta < 1 against the tail's
2alpha < gamma, i.e. a deficit of exactly 51/50 - 1 = 1/50 at alpha = 0.51; retaining
the spacings removes it. With alpha = 51/100, delta = 3/4, gamma = 21/20, epsilon =
1/100 the margins are 6/25 (mean value), 9/1000 (infinite tail), 1/4, 7399/10000,
far-cutoff ratio 14/5. An elementary application-specific substitute is kernel-checked
in Lean: for real magnitudes, sum_{m<n<=W} 2|c_m||c_n|/(log n - log m) <= 3 H_W
sum_{n<=W} n c_n^2 (both orientations cost <= 6 H_W sum n c_n^2), with H_W <= 1 + log W
connected to Mathlib; the extra log is absorbed by the strict power margin.

Evidence: hunts/higher_xi/URMS2-051.md, Section 2 'Exact failure of the old proof at
0.51' and Section 3 'The minimal replacement lemma' (lines 108-171), Section 6 'Rational
witness at 0.51'; URMS2-051-AUDIT.md Section 1; LEAN-FRONTIER.md items 1, 2, 8, 9
Prior art: cited: Montgomery and Vaughan, Hilbert's Inequality, J. London Math. Soc. (2)
8 (1974) 73-82 (weighted form); the log-spacing specialisation and Lean substitute are
the lab's
Reused in: URMS2-051.md Section 7 (URMS2 through |alpha| <= 51/100), Section 8
(simplicity proportion >= 0.0147728663285376 under RH and the rebuilt bridge);
LEAN-FRONTIER.md modules LogMeanValue, ComplexLogMeanValue, TwoRangeWeights
Why it travels: Whenever a Dirichlet-polynomial mean square is truncated at length W >>
U, using the actual 1/n spacing of log n instead of the worst spacing removes an
artificial length restriction; the kernel-checked substitute is available for any
real-coefficient instance.

### Finite-prime peeling of the powerful Euler product to reach every compact coefficient band

lemma | `hunts/higher_xi/` | grade: ordinary derivation, self-reviewed, with exact
rational parameter witnesses

Fix any finite rho_0 and choose 0 < R < 1 so small that the Laplace rate E_R(rho_0) <
1/2. Put P = R^{-2} and split the powerful support into primes <= P and primes > P. The
tail product prod_{p>P}(1 + sum_{e>=2} R^{-2e}/p^e) converges (each local series
converges and its first term is O_R(p^{-2})), with Laplace rate at most E_R(rho_0) <
1/2. The finitely many primes <= P each get their own radius R_p > p^{-1/2}; their
exponent sums converge and the total logarithm of the finite set is constant, so its
contribution to the Laplace rate is o(1) as z -> 0 and is absorbed by the remaining half
of the gap. Dominated convergence on the powerful strata then runs as before,
establishing RAMS2 on every compact fixed rho band (previously only rho <= 1/10). With
RAMS2 at target, intermediate and far cutoffs, choosing delta = (2alpha+1)/2, gamma =
(2alpha+delta)/2, beta = (alpha+gamma)/2 gives alpha < beta < gamma < delta < 1 and
2alpha < gamma, so RC2 and URMS2 hold on every compact band 0 < |alpha| < 1/2 (exact
witness at alpha = 0.499 and split_powerful_witness(21/10) in exact arithmetic).

Evidence: hunts/higher_xi/BANDWIDTH-FORENSICS.md, Section 7 subsection 'Finite-prime
peeling removes the fixed-rho endpoint' (lines 441-491); Lesion 4 in URMS2-051.md
Section 9
Prior art: unsearched
Reused in: URMS2-051.md Section 6 (RAMS2 at far-cutoff ratio 14/5), RESULTS-higher-xi.md
'URMS2 attack'
Why it travels: Standard-shaped but explicitly quantified: when a uniform Euler-product
estimate fails only because of finitely many small primes, give those primes individual
radii and absorb their bounded logarithmic mass; converts a fixed-band result into every
compact band.

### Majorant-with-equality-recurrence bypass for tight aggregate inequalities (hprime gate)

lemma | `hunts/higher_xi/` | grade: R (equality recurrence) and
mass_le_of_dominated_majorant kernel-checked (ZetaLean/MajorantBypass.lean); L1, L2, L10
kernel-checked; the remaining chain is ordinary derivation with every link checked
numerically at X = 250 and X = 5000 (margins 3.9x to 3582x); obstruction arguments
ordinary, self-reviewed with measured crossing

The literal gate (2j)(2j+1) D_j(X) <= B(X) A_j(X) puts the true distinct-prime-support
mass A_j on the right and needs an order-uniform lower bound on it; upper Chebyshev
cannot supply that, and two-sided elementary Chebyshev (theta_ge with log 2 against log
4) loses 2^j across j up to about log X/log log X, so the gate cannot close by a
Chebyshev route (obstruction, two independent arguments, measured crossing at X about
2e4 where 12 A_2^small/A_1(sqrt X) exceeds B(X)). Retarget: exhibit an explicit majorant
M_j(X) = C_0^j X L^{2j+1}/(j!(2j-1)!) with C_0 = log 16, L = log X, prove A_j <= M_j
(Route A chain L1-L10: theta(y) <= (log 4) y, N(y) = sum_{p<=y}(log p)^2 <= C_0
(e^u(u-1)+1), Abel comparison against int t e^t g(t) dt, ordered-tuple recursion
W_{j+1}(V) = sum (log p)^2 W_j(V - log p), convolution identity int_0^V t e^t E_j(V-t)
dt = E_{j+1}(V), E_j(V) <= e^V V^{2j-1}/(2j-1)!, V_j <= W_j/j!, A_j <= L^2 V_j), and
note that M satisfies the recurrence with equality: (j+1)(2j)(2j+1) M_{j+1} = C_0 L^2
M_j because the factorial denominator was built so that (j+1)(2j)(2j+1) is the step
ratio. Domination then transfers the downstream display A_r(X) <= (log 16)^r X (log
X)^{2r+1}/(r!(2r-1)!). Route B (one-dimensional Abel, constant 60 log 4) is kept for its
formalisation advantage.

Evidence: hunts/higher_xi/HPRIME-ROUTES.md, Section 0 'What both chains agree on',
Section 1 'Route A' (table L1-L10, M, R), Section 3 'Why the literal gate does not
close'; CROSS-ARM-TRANSFER.md Section 3 (the three-step pattern)
Prior art: Mathlib Chebyshev.theta_le_log4_mul_x cited; pattern unsearched
Reused in: RAMS2-CLUSTER.md (consumes the display near line 427); proposed to
hunts/frontier_math in CROSS-ARM-TRANSFER.md, where the frontier arm's reply records
that the transfer does not survive there
Why it travels: When a target inequality is tight and every local charging argument
dies, dominate the true object by a majorant that satisfies the required recurrence with
equality by construction; the tightness becomes the majorant's identity. The obstruction
half tells you when to stop trying Chebyshev-only routes.

### Factorial-permanent tail majorant with rational atom weights and a two-step geometric ratio

bound | `hunts/higher_xi/` | grade: exact rational majorant computed deterministically
(hardened by exactness); the ratio-monotonicity argument is ordinary derivation,
self-reviewed

For the pairing K(beta,delta) = sum_{pi in S_r} prod_j (b_j + d_{pi(j)} + 1)!/(2r +
|beta| + |delta| - 1)! with entries in {0,1,2}, set w_0 = 1, w_1 = 5/2, w_2 = 11; all
nine inequalities (a+b+1)! <= w_a w_b hold, so the permanent for two length-r words is
at most r! w(beta) w(delta). Retaining exact word length through index 101 and, for n =
i - 1 >= 25, R = floor(n/2), L = ceil(n/4), M = R - L + 1, a = 5/2, K = 47/4, using
C(n,j) <= 2^n and monotonicity of r! a^{-2r}: |C_{2,i}| <= B_i = (n-1) M 4^n K^2
a^{n-2-2R} R!/(n+1)!. The two-step ratio B_{i+2}/B_i splits by n mod 4 into four
rational expressions with decreasing differences (numerators -32, -2(16m^4+...),
-8(16m^3+...), -32(8m^3+...)), largest start rho = 5202/64375 < 0.081 for n >= 101, so
both parity tails are geometric and the series is entire. Exact tail bound E_40(alpha) =
sum_{i=41}^{101} U_i alpha^i + (B_102 alpha^102 + B_103 alpha^103)/(1 - rho alpha^2); at
bandwidth one sum_{i>40}|C_{2,i}| |alpha|^i < 3.279e-9, and 4.76344632220668 <
sum_{i>=1} C_{2,i} < 4.76344632876331. For any integrable window v the omitted
autocorrelation tail is at most E_40(1) ||v||_1^2.

Evidence: hunts/higher_xi/CORRECTED-F2.md, 'Tail majorant' (lines 116-185) and 'Direct
weighted consequence' (lines 187-194); TAIL-BARRIER.md 'Split result'; checker
corrected_form_factor.py
Prior art: unsearched
Reused in: window_certificate.py (2 - D > 0.9234015), URMS2-051.md Section 8 (0.51
window), BANDWIDTH-FORENSICS.md Section 9 (positivity of F_2 on [0,1/2])
Why it travels: A general recipe for bounding an infinite series of factorial-permanent
pairings: dominate each factorial by a product of per-letter weights, keep exact lengths
for a finite prefix, then bound the remainder by a proven-decreasing two-step ratio.

### Isospectral multisets with different simple counts under one fixed kernel

construction | `hunts/cycle_moments/` | grade: kernel-checked for the two explicit
matrices (AXLE, standard axioms); Fourier realisation ordinary proof

Density p(u) = 1 + cos(2πu) + cos(4πu)/4 on |u| ≤ 1/2 (= 1/4 + (1+cos2πu)²/2 ≥ 1/4,
even, integral one) has K(0)=1, K(±1)=1/2, K(±2)=1/8, K(n)=0 for |n| > 2. Multisets Z_A
= (0,0,0,3,6) (multiplicities 3,1,1, s=2) and Z_B = (0,0,1,1,4) (multiplicities 2,2,1,
s=1) both have weighted location Gram spectrum (3,1,1), hence M_j = 3^j + 2 for every j
≥ 1, yet s differs; S = 29 vs 26, Q = 11 vs 19/2, D_4 = 0 vs 9/2. Translating h
independent blocks by 10j (cross-block kernel entries vanish) keeps all normalized power
traces fixed while s/N ranges over [1/5, 2/5]. Proves the full power-trace sequence does
not determine the simple count even with the kernel fixed; the rescaling q(u) = Lp(Lu)
makes the frequency support arbitrarily narrow.

Evidence: COUNTING-OVERLAP.md §2–§4 (eqs. 3–7), §6; CountingOverlap.lean (equal power
traces for every natural exponent, simple counts 2 and 1); counting_overlap.py (G³ = 4G²
− 3G, 60-digit Fourier quadrature)
Prior art: none cited; 'original finite constructions'
Reused in: OVERLAP-BOUND.md §4 equality cases; README.md
Why it travels: A ready-made counterexample kit for any claim that a spectral
(power-trace) summary controls a simple-point count; also a test fixture for
overlap-aware bounds.

### Exact rational Legendre window with an exact pointwise floor

construction | `hunts/higher_xi/` | grade: exact rational calculation (hardened by
exactness); conditional on the unproved analytic bridge for any statement about zeros of
xi''

v(s) = P_0(2s) - (185616/10^6) P_2(2s) - (111471/10^6) P_4(2s) - (20783/10^6) P_6(2s) on
|s| <= 1/2. Since |P_j(x)| <= 1, v has the exact positive floor 68213/100000, integral
one and L1 norm one, so it is an admissible spectral factor and the tail allowance
E_40(1) ||v||_1^2 applies with ||v||_1 = 1. Exact polynomial integration of the first 40
corrected coefficients gives D_40 = 1.0765984703331668..., and with the full tail
allowance 2 - D > 0.923401526388517... > 0.9234015; the floating optimizer reaches
0.923401531890862, only 5.51e-9 higher. Caveat the hunt states: v(+-1/2) = 68213/100000
> 0, so the autocorrelation has only a simple zero at the band edge, which is why the
window cannot repair the source's endpoint estimate.

Evidence: hunts/higher_xi/CORRECTED-F2.md, 'Direct weighted consequence' (lines
197-227); BRIDGE-CLOSURE.md Section 6 'Why the target weighting does not repair the
source bound'; window_certificate.py
Prior art: unsearched
Reused in: URMS2-051.md Section 8 uses a different (indicator) window;
RESULTS-higher-xi.md 'Weighted window result'
Why it travels: Low-degree rational Legendre combinations give windows with exact floors
and norms, so simplicity-proportion functionals can be evaluated in exact arithmetic
with a uniform tail allowance instead of a float optimizer.

### Invariance claims need a control that moves the invariant's parameter (fault-injection power measurement)

control | `hunts/r_2ac05f/` | grade: hardened for the identity (two independent exact
derivations plus external kappa = 1 anchor); the control-power measurement is exact
rational arithmetic

When an inherited lemma asserts a quantity is invariant in a parameter (Bian Lemma 12:
C_{kappa,2} = -4 for all kappa), a control that only checks the anchored instance (the
Farmer-Gonek kappa = 1 row) has zero power against a defect in the invariance. Measured
by planting: forcing the x^1 coefficient of Qhat_kappa to g instead of kappa g (the
defect under audit) leaves the kappa = 1 control passing and reproduces the published
wrong C_{2,2} = -4; corrupting the pairing denominator by one factorial step fails the
control, so the control is not vacuous. Stated rule: compute the quantity independently
for kappa = 1, 2, 3 and assert the values are not equal. The underlying identity: the
x^1 coefficient of Qhat_kappa is kappa g, so C_{kappa,2} = 2(<q_0,q_1> + <q_1,q_0>) = -4
kappa (derived -4, -8, -12, -16, -20 for kappa = 1..5).

Evidence: hunts/r_2ac05f/RESULTS.md, Section 3 'Why the other table is wrong, in one
line' (lines 85-104) and Section 4 'The control that would have caught it' (table lines
136-139, rule lines 147-164); fault_check.py
Prior art: Bian 2008 thesis Lemma 12 (the corrected claim); Farmer-Gonek arXiv:0803.0425
(anchor); the general-kappa correction 'recorded nowhere but here'
Reused in: Matches the failure shape recorded from run 726a6b3f on
finite_height_spacing_experiment; confirms hunts/higher_xi C2_PROVENANCE.md
Why it travels: A one-line design rule for validating any audit that inherits a
universality/invariance lemma as an axiom, with a demonstrated fault-injection procedure
for measuring a control's power.

### Third-moment obstruction block diag(b+2, b+2, −2b)

obstruction | `hunts/cycle_moments/` | grade: scalar power sums, discrepancy, slack and
their signs Lean-checked; vector construction and limit ordinary proof

Under the signed-vector hypotheses, matched second and third moment limits alone cannot
improve the quadratic counting proportion, even with strictly negative third
discrepancy. Block: g_1 = √(1+b/2)e_1, h_1 = √(b/2)e_3, g_2 = √(1+b/2)e_2, h_2 =
√(b/2)e_3 gives A_b = diag(b+2,b+2,−2b), N_b = 4, s_b = 0, M_2 = 6b²+8b+8, M_3 =
−6b³+12b²+24b+16, M_4 = 18b⁴+16b³+48b²+64b+32, so Δ_3 = −6b²(b+1) < 0 while the slack
E_b = M_2 − 2N_b + s_b = 6b²+8b, with −Δ_3 − (b/2)E_b = b²(3b+2) ≥ 0. Adding it with b_L
= (dL/6)^{1/3} to a baseline of s_L simple and r_L doubled orthonormal vectors gives,
for any 1 < c_2 < 2, d > 0: M_2/N → c_2, Δ_3/N → −d, s/N → 2 − c_2, while M_4/N → ∞.
Hence a finite normalized fourth-moment bound is a substantive hypothesis, and any
conclusion liminf s/N ≥ 2 − c_2 + ε from two moment limits is impossible in this class.

Evidence: THIRD-MOMENT-OBSTRUCTION.md §1–§3; ThirdMomentObstruction.lean (AXLE request
660ac38d…, standard axioms)
Prior art: none cited; 'original finite construction; novelty has not been established'
Reused in: README.md summary; closes the second+third-moment shortcut for the quartic
route
Why it travels: A concrete isospectral-type gadget showing which moment hypotheses are
load-bearing; the shared negative direction trick generalises.
Index note: Kernel-checked scalar part.

## Heat flow and de Bruijn-Newman constants

Backward heat flow of xi-type functions: landing times as lower bounds, contour and
winding instruments that refuse rather than round, and the calibrations that fix the
frame.

- identity: Shave integral for the landing time of a crowded pair, with isolated,
  leading-order and dense-sea limits (`lambda_dh_exact`)
- lemma: Threshold bracket via upward-closed, closed set S for Hermitian (not
  necessarily even) heat kernels (`dh_minus_heat`)
- lemma: Lemma M2: uniform bound on |H_t''| over a half-strip by a shifted u-contour
  (`lambda_dh_bounds`)
- lemma: Phase obstruction for a two-L-function combination: Theta(sigma) < tau gives a
  zero-free half-plane (`lambda_dh_bounds`)
- lemma: Landing times are unconditional lower bounds for the DH de Bruijn-Newman
  constant; equality needs no-creation (`lambda_dh_exact`)
- bound: Euler-phase zero-free half-plane for a two-character combination, with integer
  tail (`dh_minus_heat`)
- construction: Contour-moment pair tracker in the collision-safe discriminant variable
  (`flow_repair`)
- calibration: Frame scaling law for de Bruijn-Newman constants: Lambda/Delta^2 is the
  frame-free quantity (`lambda_dh_bounds`)
- calibration: Delta^2/2 calibration of de Bruijn Theorem 13 by polynomial heat flows
  (derived, never recalled) (`lambda_dh_bounds`)
- computational technique: Taylor/Rouche disk certificate for a simple non-real zero of
  a heat-flowed entire function, with all tails charged (`dh_minus_heat`)
- computational technique: Chord-tube segment winding count that refuses rather than
  rounds (`lambda_dh_bounds`)
- control: Arithmetic-free N-body null control: the repair clock reads geometry
  (`flow_repair`)
- control: Deflation lesion of an analytic constant, with onset factor, blindness radius
  and health-metric direction (`lambda_dh_bounds`)
- control: t=0 admissibility gate for exact polynomial heat flow (float root-finding
  lesion) (`lambda_dh_exact`)

### Shave integral for the landing time of a crowded pair, with isolated, leading-order and dense-sea limits

identity | `hunts/lambda_dh_exact/` | grade: measured (one float route; derivations
ordinary, self-reviewed)

Isolated pair p_0 = (z-x)^2 + y_0^2: p_t = p_0 - t p_0'' = (z-x)^2 + y_0^2 - 2t, so
t*(isolated) = y_0^2/2 exactly (verified to about 1e-13 by exact polynomial flow;
backward cross-route via zeta.heatflow.polynomial_heat_flow gives -a^2/2). Frozen
neighbours: with Q = -y^2 and S(y) = sum_a 1/((x-a)^2 + y^2), dy/dt = -(1 + 2 y^2
S(y))/y, hence t* = int_0^{y_0} y dy/(1 + 2 y^2 S(y)) (*); S > 0 for real neighbours
proves t* < y_0^2/2 (sign theorem). Leading term: relative shave = 1 - t*/(y_0^2/2) =
S_0 y_0^2 + O(y_0^4), S_0 = sum_a 1/(x-a)^2; two neighbours at distance d give
2(y_0/d)^2. Dense sea of density rho = 1/h: S -> pi rho/y, dy/dt = -1/y - 2 pi rho, t* =
[V - log(1+V)]/(2 pi rho)^2 with V = 2 pi rho y_0; for V >> 1, t* -> y_0/L, L = 2 pi/h.
Frozen-neighbour bias measured: (*) under-predicts t* by 1% (light crowding) to about
17% (heavy), because neighbours repel. Four-root control: landing time t_+ = [(Y^2 -
a^2) + sqrt((Y^2-a^2)^2 + 12 a^2 Y^2)]/12 for (z^2-a^2)(z^2+Y^2).

Evidence: hunts/lambda_dh_exact/MISSION.md, Section 3 'The isolated-pair law, derived
and verified' (lines 188-222), Section 4.2 'The shave, in one integral', 4.3, 4.4 'The
deep regime', 4.7 'The bias of the frozen-neighbour approximation, measured' (table
lines 370-378); Section 2 quartic control (lines 173-178)
Prior art: unsearched; N-body law attributed to zeta/heatflow.py four-way sign check
Reused in: Explains hunts/flow_repair's empirical 'shave tracks y_0^2 times local
density' (P1/P2); calibrated against its nine landings (rms 0.54%) and a census holdout
(0.79%)
Why it travels: Closed-form landing-time model for any conjugate pair under heat flow
given the surrounding real zero configuration; the sign theorem alone converts every
measured landing into a strict inequality against y_0^2/2.

### Threshold bracket via upward-closed, closed set S for Hermitian (not necessarily even) heat kernels

lemma | `hunts/dh_minus_heat` | grade: ordinary derivation, self- and model-reviewed;
numerical inputs enclosure-carrying

Let S be the set of real t at which H_t has all zeros real. If the whole-line Fourier
kernel is Hermitian (K(u) = conj K(-u), e.g. K = -2i g with g real odd), then de
Bruijn's strip-contraction theorem (Dobner's extended-Selberg-class form) makes S upward
closed; locally uniform dependence on t plus Rouche on a small disk with zero-free
boundary makes S closed; so S = [Lambda, inf). One enclosed non-real zero at t_0 gives
Lambda > t_0; one zero-free strip |Im z| < b gives Lambda <= b^2/2. No trajectory
tracking and no even-kernel restriction needed. Applied: 217/200 < Lambda_minus <=
567009/320000 (narrow frame); Lambda_plus <= 1/2.

Evidence: RESULTS.md section 5 'Threshold and strict lower bound', lines 232-251;
section 1 for the odd-kernel construction, lines 77-101
Prior art: cited: de Bruijn strip contraction, Dobner arXiv:2005.05142v2; bounded search
for second-DH heat bounds found no bracket (searched-and-absent, not claimed as novelty)
Reused in: none recorded
Why it travels: Gives a two-sided de Bruijn-Newman-type bracket for any L-function-like
object with odd or complex theta kernel from one local disk and one zero-free strip.

### Lemma M2: uniform bound on |H_t''| over a half-strip by a shifted u-contour

lemma | `hunts/lambda_dh_bounds/` | grade: hardened (prose proof plus decided Arb
arithmetic at 300 bits; every constant a reported ball, every hypothesis a decided
predicate); not kernel-checked; read by no human; weakest input is the cited evenness
Phi_DH(-u) = Phi_DH(u)

Let Phi_DH(u) = 4 e^{3u/2} sum_n n a_n exp(-pi n^2 e^{2u}/5) with |a_n| <= 1 and Phi_DH
even on the strip |Im u| < pi/4, G(u) = e^{t u^2} Phi_DH(u), H_t(z) = int_0^inf G(u)
cos(zu) du, t >= 0, and R(x_lo, y_hi) = {Re z >= x_lo > 0, |Im z| <= y_hi}. If (H1) 0 <
v < pi/4, (H2) S >= 1 and q_S = exp(-(pi/5) e^{2S} cos 2v) <= 29/100, (H3) c = (pi/5)
cos 2v - (t S^2 + beta S) e^{-2S} > 0 with beta = 7/2 + y_hi, then H_t is entire and for
all z in R, |H_t''(z)| <= M2 := e^{-x_lo v - t v^2} (J + T), where J = int_0^S (s^2+v^2)
e^{t s^2} 4 e^{3s/2} Omega(e^{2s} cos 2v) cosh(y_hi s) ds is bounded by an 800-panel
interval sum using two Omega majorants (unimodal comparison 1/(2a) + 2e^{-1/2}/sqrt(2a)
and geometric q/(1-q)^2 <= 2q for q <= 29/100), and T = 4 e^{2v} e^{-cV}/(cV), V =
e^{2S}. Proof: differentiation under the integral with explicit dominant, Cauchy on the
rectangle 0, R, R+iv, iv with the far side bounded by 8e^{2v}e^{-c e^{2R}}, vertical
legs cancel by evenness of G (Fact E, the one load-bearing citation), then majorise the
two rays. Corollary: affine interpolation error on any axis-parallel segment of
half-length h is <= M2 h^2/2 (Green's-function form, valid for complex g). Decided at v
= pi/4 - 1/256, S = 5: M2 <= 1.1887e-78 (t = 23/400) and 1.1371e-78 (t = 36/625);
decided cushion over the true sup at most 55.65 and 53.79. Key point: pointwise ball
enclosure of H_t'' cannot give a uniform bound (a z-ball of radius 1e-24 already
contains 0), because at Re z ~ 240 the integrand is O(1) and the integral ~1e-80; the
contour shift puts the factor e^{-x_lo v} outside the integral.

Evidence: M2-LEMMA.md §2 (lines 74-125, statement and decided instantiation), §3 Steps
0-4 (lines 131-416, proof), §4 (corollary, lines 452-475), §7 (cushion table, lines
527-600), §8 (why ball evaluation cannot give a uniform bound, lines 604-631);
m2_lemma.py
Prior art: cited for inputs (Cauchy, Morera, dominated convergence, Hecke theta
transformation for the functional equation); the lemma itself unsearched
Reused in: hunts/lambda_dh_exact/RESULTS.md §5 item 6 (inherits the M2 blind-spot
lesson); docs/29-de-bruijn-newman-davenport-heilbronn.md; hunts/dh_minus_heat/RESULTS.md
uses the same Taylor-remainder M2 r^2/2 pattern at a small disk
Why it travels: Any argument-principle count of a heat-deformed Fourier integral H_t at
large Re z needs a uniform second-derivative bound that ball arithmetic cannot supply;
the recipe (shift by v just inside the kernel's analyticity strip, cancel legs by
evenness, panel-plus-closed-form tail) transfers to any even kernel holomorphic on a
strip.

### Phase obstruction for a two-L-function combination: Theta(sigma) < tau gives a zero-free half-plane

lemma | `hunts/lambda_dh_bounds/` | grade: decided constants plus exact elementary
analysis (hunt's own wording); the composite Lambda_DH <= Delta^2/2 is 'cited plus
decided, weakest step cited' (de Bruijn 1950 Theorem 13)

Let chi be the odd primitive character mod 5 with chi(2) = i, A = (1 - i kappa)/2, so
the Davenport-Heilbronn coefficients satisfy a_n = A chi(n) + conj(A) conj(chi)(n) and
f(s) = A L(s,chi) + conj(A) L(s,conj chi) for Re s > 1. Since both Euler products
converge absolutely and do not vanish there, f(s) = 0 iff R(s) := L(s,chi)/L(s,conj chi)
= -conj(A)/A = exp(i(pi + 2 arctan kappa)), whose smallest absolute argument is tau = pi
- 2 arctan kappa. Only primes p = 2,3 mod 5 contribute to R, each factor being
(1+u)/(1-u) with |u| = p^{-sigma}. Moebius-disc lemma: for |u| <= r < 1, |arg
(1+u)/(1-u)| <= 2 arctan r, with equality at u = +-ir, and the argument-maximising point
has modulus exactly 1 (centre C = (1+r^2)/(1-r^2), radius rho = 2r/(1-r^2), C^2 - rho^2
= 1), so the |R| = 1 constraint cannot sharpen the bound. Hence if Theta(sigma) :=
sum_{p = 2,3 mod 5} 2 arctan(p^{-sigma}) < tau then f has no zero on Re s = sigma, and
since Theta is decreasing one decided sigma* closes the half-plane Re s >= sigma*; the
gamma factor and F(s) = F(1-s) carry it to the completed F and give the strip |Im z| <
Delta = sigma* - 1/2. Theta is decided with no prime counting: head summed exactly from
a sieve to P, tail closed by the Euler-product identity T1 - Tchi = 2Q + (E_chi - E_1)
where all even-k terms cancel because chi5(p)^2 = 1, leaving eps3 = (2/3) P^{1-3
sigma}/((3 sigma - 1)(1 - P^{-2 sigma})) (a factor 5.7e5 better than bounding the two
tails separately). Decided on both backends (flint 192 bits, mpmath.iv dps 40, P =
10^5): sigma* = 1.12036249819 exactly, Delta^2/2 = 0.19242481458026887663805 narrow,
improving the coefficient-domination abscissa 1.39513615823511 by factor 2.082.

Evidence: STRIP2.md §3.1-3.6 (lines 146-268), §4.1-4.3 (tail identities and backends,
lines 272-348), §5 (decided numbers, lines 352-412), §6 (eight abort-on-fail controls
plus the tau_- control reproducing Bombieri-Ghosh's 2.3822861089 to ten digits, lines
416-464); RESULTS.md §3.6 (lines 598-755)
Prior art: searched-and-found: Bombieri and Ghosh 2011 Theorem 7 is the same equation
Theta(sigma) = tau term for term; the hunt rederives only the necessary half (upper
bound) without Bohr/Kronecker theory and states 'what is new here is the grade and not
the number'
Reused in: hunts/dh_minus_heat/RESULTS.md (lines 210-218: same Euler-factor argument for
the second DH function with a simpler tail 2 P^{1-sigma}/(sigma-1));
docs/29-de-bruijn-newman-davenport-heilbronn.md
Why it travels: Any Dirichlet series that is a fixed linear combination of two
L-functions with Euler products gets a zero-free half-plane from a phase budget rather
than from L1 coefficient domination; the k=2-cancelling tail identity is a general trick
for sums over a residue class of primes.

### Landing times are unconditional lower bounds for the DH de Bruijn-Newman constant; equality needs no-creation

lemma | `hunts/lambda_dh_exact/` | grade: Section 1: ordinary derivation, self-reviewed,
resting on cited theorems; Section 2 (NC): mechanism only, sampled not proved (hunt's
own words)

Phi_DH is real and even (evenness measured to 4.2e-51), so nonreal zeros of H_t come in
conjugate pairs. By Dobner (arXiv:2005.05142, Thm 1) the set {t : H_t has only real
zeros} is a closed half-line [Lambda_DH, inf). For a pair P present at t = 0 define
t*(P) = inf{t >= 0 : P is no longer nonreal}; it is finite by de Bruijn/Newman-Wu,
y_max(t) <= sqrt(max(Delta^2 - 2t, 0)). For t < t*(P), H_t has a nonreal zero so t <
Lambda_DH; hence Lambda_DH >= t*(P) for every pair and Lambda_DH >= sup_P t*(P),
unconditionally. Equality Lambda_DH = sup_P t*(P) holds under (NC): forward flow never
drives two real zeros off the axis. (NC) is the time-reversed Sturm/Angenent lap-number
statement (since u(x,t) = H_t(x) solves du/dt = -d^2u/dx^2 on the real line), which the
hunt states is a mechanism, not a proof for entire functions; sampled 400/400 gated
random polynomial configurations with no decrease in real-zero count.

Evidence: hunts/lambda_dh_exact/MISSION.md, Section 1 'Why every landing time is a lower
bound for Lambda_DH' (lines 89-113) and Section 2 'Does Lambda_DH equal that sup? The
no-creation step' (lines 117-184)
Prior art: cited: Dobner arXiv:2005.05142; de Bruijn 1950 Thm 13 / Newman-Wu Thm 7;
Sturm 1836, Matano 1982, Angenent 1988; Polya-Wiman theory named as the standard route
Reused in: Stated as the reason hunts/flow_repair's nine landings are floors and
hunts/lambda_dh_bounds could decide one
Why it travels: Fixes exactly which half of a landing-time program is unconditional for
any real even entire function of the de Bruijn class, so floors can be published without
the no-creation step.

### Euler-phase zero-free half-plane for a two-character combination, with integer tail

bound | `hunts/dh_minus_heat` | grade: enclosure-carrying (Arb and mpmath.iv, arctangent
Taylor series with explicit remainder); the Euler-factor argument itself is inherited
from ../lambda_dh_bounds/STRIP2.md, the simpler tail is new here

For D(s) = A L(s,chi) + conj(A) L(s,conj chi) with chi the primitive quartic character
mod 5, a zero with Re s = sigma > 1 needs the Euler-product ratio to reach phase 2
atan(kappa), kappa = tau_plus. Primes p = 1,4 mod 5 and p = 5 contribute phase 0; each p
= 2,3 mod 5 contributes at most 2 atan(p^{-sigma}). Zero excluded if Theta(sigma) = 2
sum_{p=2,3 mod 5} atan(p^{-sigma}) < 2 atan(kappa); tail above P bounded by 2
P^{1-sigma}/(sigma-1). Decided at sigma = 953/400 with sieve through P = 10000 on two
interval backends; monotone in sigma; reflected by the functional equation to give all
zeros in |Im z| < 753/400.

Evidence: RESULTS.md section 4 'Upper strip from prime phases', lines 195-230
Prior art: cited as inherited from hunts/lambda_dh_bounds/STRIP2.md; literature
unsearched
Reused in: inherited from lambda_dh_bounds, sharpened here with the integer tail
Why it travels: Any linear combination of two L-functions with conjugate coefficients
gets an explicit zero-free half-plane from a finite prime sieve plus a one-line tail.

### Contour-moment pair tracker in the collision-safe discriminant variable

construction | `hunts/flow_repair/` | grade: measured (mpmath floats with cross-route
defects; 'no enclosure claims are made anywhere in this hunt')

For a conjugate pair of zeros of an entire function H_t inside a circular contour,
compute the power sums q_1 = z_1 + z_2, q_2 = z_1^2 + z_2^2 by contour integration of
z^k H_t'/H_t, and track the discriminant Delta = 2 q_2 - q_1^2 = (z_1 - z_2)^2, Q =
Delta/4 (Q = -y^2 off the axis, Q > 0 on it). Q is analytic through the landing Q = 0,
so the landing time t* under the backward heat flow H_t = exp(-t d^2/dz^2) H_0 is read
as the root of Delta(t) by bracketing, with the contour's winding number required to be
exactly 2. Companion N-body law: with S(y) = sum_a 1/((x-a)^2 + y^2) over neighbours,
dQ/dt = 2 - 4 Q sum_a 1/((x-a)^2 - Q), from dz_k/dt = 2 sum_{j != k} 1/(z_k - z_j).
Refusals are loud: a clipped contour reports N = 1 and refuses; a grazing contour
returns non-integer winding (about 1.8e9) and refuses. Precision response: t* for pair 1
identical to the last digit across dps 44/54/70 and 96/192 nodes.

Evidence: hunts/flow_repair/NOTES.md, Section 1 'The headline: the repair times,
measured', Section 3 'The null control', Section 4 'Lesions', Section 5 'Precision
response'; MISSION.md lines 57-79
Prior art: searched-and-found for the N-body law (Calogero-Moser: Cuenca-McSwiggen
arXiv:2606.06859, Hall-Ho arXiv:2308.11685); no tabulated DH de Bruijn-Newman constant
found; contour-moment discriminant tracking unsearched
Reused in: hunts/lambda_dh_exact (MISSION.md Section 4.1 re-derives dQ/dt from the
N-body law; uses the nine landings as calibration data); hunts/lambda_dh_bounds (decided
landing referenced in lambda_dh_exact RESULTS.md Section 4)
Why it travels: Works for any entire function under the heat flow (DH, Epstein, zeta):
the pair discriminant is the only quantity analytic through a real-axis collision, and
the winding gate makes half-pair and grazing failures impossible to feed silently.

### Frame scaling law for de Bruijn-Newman constants: Lambda/Delta^2 is the frame-free quantity

calibration | `hunts/lambda_dh_bounds/` | grade: derived (the hunt's word), with every
row measured numerically; the earlier claim that the two deformations 'share Lambda
exactly' was wrong by a factor 4 and is preserved in a correction box

For any admissible kernel Phi, a > 0, c != 0, define Phitilde(u) = (c/a) Phi(u/a) and
Htilde_t(z) = int_0^inf e^{t u^2} Phitilde(u) cos(zu) du. Then Htilde_t(z) = c H_{a^2
t}(a z), so the zero set scales by 1/a, Delta -> Delta/a and Lambda -> Lambda/a^2; hence
Lambda/Delta^2 is invariant and de Bruijn's threshold t >= Delta^2/2 can be quoted
frame-free while Lambda and Delta separately cannot. Applied with a = 1/2, c = 1/2:
Phi_F(u) = Phi_DH(2u), xi_t^F((1+iz)/2) = H_{t/4}(z/2), so Lambda(wide: s = (1+iz)/2,
Newman/Rodgers-Tao/Polymath 15/Dobner/zeta.heatflow) = 4 Lambda(narrow: s = 1/2 + iz,
Stopple/Newman-Wu kernel), Delta(wide) = 2 Delta(narrow). Verified numerically row by
row at a = 1/2, 2, 13/10 (relative defects <= 2.2e-29) and with Dobner's Phi_F computed
only from his own definition by Fourier inversion. House rule: always print the frame
with the number, print both values or the factor 4 with its direction, never compare a
zeta record across frames unconverted.

Evidence: FRAME.md §2 (lines 179-210, derivation), §3 (lines 214-236, explicit
conversion), §4 (conversion table, lines 240-254), §5 (numerical verification), §8
(lines 455-464, what to write every time); RESULTS.md §0 (lines 33-61); THEOREM13.md §6
'Dobner's frame is not this frame: the factor is 4'
Prior art: cited: Stopple arXiv:1301.3158, Dobner arXiv:2005.05142, Rodgers-Tao
arXiv:1801.05914, Polymath 15 arXiv:1904.12438, Newman-Wu 2020; the scaling law and
factor-4 dictionary derived in-tree
Reused in: docs/29-de-bruijn-newman-davenport-heilbronn.md §1 'the frame trap';
hunts/dh_minus_heat/RESULTS.md (reports narrow and wide by the same factor 4);
SEPARATION.md (frame-invariant cross-multiplication); zeta.heatflow.lambda_facts()
Why it travels: Every future Lambda-type constant for any function in the extended
Selberg class must be tagged with its frame; the invariant Lambda/Delta^2 is the safe
way to compare bounds across papers.

### Delta^2/2 calibration of de Bruijn Theorem 13 by polynomial heat flows (derived, never recalled)

calibration | `hunts/lambda_dh_bounds/` | grade: measured (one float route each; the
hunt's own words)

To pin the constant in de Bruijn's Theorem 13 (all zeros of H_0 in |Im z| <= Delta
implies all zeros of H_t real for t >= Delta^2/2 under the multiplier e^{t u^2}) without
trusting memory: first check that the e^{tu^2} multiplier under the integral and the
finite polynomial series sum_k (-t)^k/k! p^{(2k)} both satisfy the backward heat
equation dG/dt = -d^2G/dz^2 (residual 0 at dps 30 by quadrature; 4.2e-6 by float64
central differences consistent with h^2), which licenses calibrating the integral
multiplier with polynomials. Route A: p(z) = z^2 + Delta^2 lands exactly at t* =
Delta^2/2 (ratio 2t*/Delta^2 = 1.0 at Delta = 0.6, 0.895136, 1.2), refuting Delta^2/8 by
a factor 4 and showing 2 Delta^2 slack by 4. Route B: cos z + c flowed to e^t cos z + c
gives ratios 0.8366, 0.9839, 0.99967 at c = 2.0, 1.05, 1.001 climbing to 1, so the
constant 1/2 is sharp. Route C: (z^2+1)(z^2-A^2) gives 0.9329, 0.99506, 0.99980 at A =
5, 20, 100: spectator real zeros only accelerate landing. Independently reproduced by an
adversary at D = 0.3, 0.6, 0.895136, 1.0, 2.0. Reading: the threshold is t = lambda^2/2
for de Bruijn's e^{(1/2) lambda^2 u^2}, t = lambda/2 for Newman-Wu's e^{lambda u^2/2},
frame-free in either.

Evidence: THEOREM13.md §6 'Calibration of the factor Delta^2/2 (derived, never
recalled)' (lines 502-549); RESULTS.md §3.3-3.4 (lines 526-586); calibrate_theorem13.py,
calibration.json
Prior art: cited: de Bruijn 1950 Duke Math. J. 17 Theorem 13 (transcribed from the image
scan), Dobner Theorem 3, Newman-Wu 2020 Theorem 7 as typeset corroborations
Reused in: RESULTS.md §3.5 (the upper bound), STRIP2.md §3.5, docs/29; the same
dictionary is what dh_minus_heat's wide-frame values ride on
Why it travels: A three-family numerical calibration that fixes the constant and the
multiplier convention of any Polya-de Bruijn style strip-to-time theorem before it is
applied to a new function; the heat-equation check is the licence for using polynomials
as the oracle.

### Taylor/Rouche disk certificate for a simple non-real zero of a heat-flowed entire function, with all tails charged

computational technique | `hunts/dh_minus_heat` | grade: enclosure-carrying (Arb at
96/128/160 bits, exact rational recheck; mpmath 55-digit quadrature as float
cross-check); ordinary argument, model-reviewed only

For H_t(z) = 4 int_0^inf e^{t u^2} g(u) sin(zu) du (or cos), a disk |z-c| <= r avoiding
the real axis, enclose |H_t(c)|, |H_t'(c)|, and a disk-wide majorant M2 >= |H_t''|
(replace every coefficient by its bound M and the wave factor by u^k e^{yu}, y = |Im c|
+ r). If |H_t(c)| + M2 r^2/2 < r |H_t'(c)| as an exact rational inequality on the dyadic
endpoints, Rouche gives exactly one simple non-real zero in the disk. Tails: theta tail
after n=N bounded by M(N+1)rho^{N+1}/(1-rho)^2 times 4U^{k+1}exp(tU^2+(3/2+y)U);
integral tail after U by 4 M U^k exp(-CV)/(CV) with V=e^{2U}, C = pi/5 -
(tU^2+(3/2+y)U)/V > 0. An insufficient cutoff returns inconclusive, never silently drops
a tail.

Evidence: RESULTS.md sections 2-3 'Two local disks' and 'Error bounds actually
consumed', lines 108-193; verify.py, rouche.json
Prior art: cited: Rouche, Taylor remainder (standard); packaging unsearched
Reused in: none recorded
Why it travels: Drop-in local zero-existence certificate for any heat deformation of a
theta-type kernel; converts 'a root-finder residual' into a statement with all errors
retained.
Index note: Enclosure-carrying zero certificate; the chord-tube winding count in
lambda_dh_bounds is the sibling instrument.

### Chord-tube segment winding count that refuses rather than rounds

computational technique | `hunts/lambda_dh_bounds/` | grade: decided (enclosure-carrying
integer count, python-flint Arb 420 bits; second float witness by an independent DHFlow
argument-principle route at dps 130 sharing 0 declared layers)

To decide the number N of zeros of H_t inside an exact-rational rectangle: split the
boundary into axis-parallel subsegments with exact dyadic endpoints; for each subsegment
[z_a, z_b] of half-length h evaluate Arb balls A = H(z_a), B = H(z_b); the image lies in
chord(A,B) + disc(M2 h^2/2) with M2 the uniform |H_t''| bound (Lemma M2). Decide (i)
dist(0, chord) > M2 h^2/2 via a lower-ball _chord_clearance (cases on the foot of the
perpendicular), which puts the image in an open half-plane so |Delta arg| < pi, and (ii)
Re(B/A) > 0, so |Arg q| < pi/2 and Delta = Arg q exactly. Undecided subsegments are
halved (evaluations cached) down to a budget; on exhaustion the routine returns status
'undecided' naming the failing segment and never an integer. The sum of per-segment Arg
q balls divided by 2pi must be a ball deciding a single integer. Box validators reject
boxes touching the real axis (Im lo = 0 raises before any evaluation). The
countermeasure winding.measured_h2_guard requires M2 to dominate a directly sampled
sup|H_t''| on a rule sharing no code with the derivation, and main() refuses the floor
if it fails. Decided N = 1 at t = 23/400 and t = 36/625 on boxes with Im z >= 3/1024,
prec 420 bits, winding-ball width < 1e-39.

Evidence: winding.py header lines 20-60 (the two per-segment decisions and the refusal
rule), lines 593-730 (_chord_clearance, winding_rectangle, tube = M2*hh*hh/2);
RESULTS.md §2.1 (lines 298-316), §5 controls table (lines 801-811: displaced box N=0,
on-axis box raises, edge-through-zero returns undecided)
Prior art: cited in-tree: adapts the zeta.rigor._segment_delta pattern with the no-zero
step rescaled for |H_t| ~ 1e-83; argument principle standard
Reused in: hunts/lambda_dh_exact/RESULTS.md §7 step 1 recommends this instrument to
decide the height-10^6 zero; hunts/dh_minus_heat uses a Rouché variant of the same
chord/tube inequality
Why it travels: A general rigorous zero-count for any entire function with a uniform
second-derivative bound on the box, with an explicit refusal path instead of rounding;
the on-axis and edge-through-zero controls specify what the detector must do when the
box is bad.

### Arithmetic-free N-body null control: the repair clock reads geometry

control | `hunts/flow_repair/` | grade: measured

To test whether a flow-time quantity carries arithmetic information, census the t=0 zero
configuration in a window (line zeros by phase-refined sign scan, total strip count by
the argument principle, accounting required to close exactly: line + 2 x quadruples =
strip, e.g. 49 + 4 = 53), then integrate the bare N-body ODE dz_k/dt = 2 sum 1/(z_k -
z_j) from those positions only (no Dirichlet series, character or conductor) in the
variable Q, and compare its landing time with the PDE flow. For five DH quadruples the
ODE and PDE landing times agree to within 0.04% (differences -0.036%, -0.010%, -0.002%,
-0.006%, +0.024%), sign scattering with truncation knobs, so the repair time contains no
information beyond the initial zero layout. Companion 'rival-as-validation' leg: the
generic-Phi evaluator must reproduce the sibling module (zeta's H_t to 5.4e-42) before
it is trusted on the rival.

Evidence: hunts/flow_repair/NOTES.md, Section 3 'The null control: the repair clock
reads geometry, not arithmetic' (table lines 104-110), Section 0 'The instrument is
telling the truth', 'Standing-checklist accounting'
Prior art: unsearched for the control design; N-body universality literature cited
(Hall-Ho, Cuenca-McSwiggen)
Reused in: hunts/lambda_dh_exact MISSION.md Section 4.6 uses the N-body null control
landing of the census pair at gamma = 531.28 as a holdout
Why it travels: A matched decoy that explains the effect rather than merely failing to
reproduce it; applicable whenever a claimed structural quantity might be a function of
configuration geometry alone.

### Deflation lesion of an analytic constant, with onset factor, blindness radius and health-metric direction

control | `hunts/lambda_dh_bounds/` | grade: measured (float guard; hunt's stated
verdict 'SENSITIVITY MEASURED (not a pass)'); the cushion is decided as of 2026-08-18

For a detector that consumes a derived analytic constant (here M2, the uniform |H_t''|
bound feeding the chord-tube radius): hold geometry, precision and subdivision fixed and
deflate only the constant by factors 1, 10, 72, 75, 100, 1000; record for each whether
status is 'decided', the integer returned, whether it is correct, and the detector's own
health metrics. Findings that define the control: (a) wrong_answer_onset_factor = 75
with n_wrong_and_silent = 3 (wrong integer with status 'decided', the one output the
routine promises never to produce); (b) the health metric min_chord_margin_digits reads
0.02 on the correct run and 0.11, 1.11 on the wrong runs, i.e. the detector's own metric
improves as the answer becomes wrong, so it may not be used as a guard on the constant;
(c) countermeasure: a measured guard (sup|H''| sampled on a rule sharing no code with
the derivation) that trips at deflation 55.7, before the first wrong integer at 75, with
the ordering later shown structural (cushion 33-204 across a 40-unit span) but not
proved on arbitrary boxes; (d) the same discipline applied to the two tail bounds gives
a blindness factor 8.02 (smallest domination ratio bound/true over 18 stress rows), so a
bound deflated by less than 8 is invisible. Verdict vocabulary: 'SENSITIVITY MEASURED
(not a pass)', with all_pass = false reported as the headline rather than
controls_1_to_4_pass.

Evidence: RESULTS.md §5 table (lines 801-811), §5.1 'Control 5, in full' (lines 825-888,
deflation table at 838-847, 'the perverse metric' 855-863, countermeasure 865-871, what
is still blind 873-881), §5.1a (lines 890-940); INDEPENDENCE.md §5(ii) (tail-bound
domination ratios, lines 234-305, blindness factor 8.02); controls.py,
controls_results.json
Prior art: cited in-tree: docs/25's rule that a lesion threshold without a blindness
radius is half a measurement
Reused in: hunts/lambda_dh_exact/RESULTS.md §5 item 6 (lesion_degree52 records the same
health-metric blind spot); GATE.md known assumption 6
Why it travels: Any enclosure-based detector with a hand-derived constant should be
lesioned this way; the two numbers to report are the wrong-answer onset and the
blindness radius, and the direction the health metric moves under the lesion is itself a
finding.

### t=0 admissibility gate for exact polynomial heat flow (float root-finding lesion)

control | `hunts/lambda_dh_exact/` | grade: measured

When zeros of a heat-evolved polynomial are found by float64 numpy.roots on coefficients
evolved in closed form (p_t = sum_k (-t)^k/k! p^{(2k)}), reject any configuration whose
starting roots at t=0 are not recovered. Lesion that fired silently: at degree 52 with
spacing 0.5, numpy.roots reported 14 nonreal roots at t=0 where there are 2 and max|Im|
= 0.967 where it is 0.600; the resulting landing time was wrong by a factor 3.3 and
looked ordinary. All tables in the hunt are gated; the detector's own health metric does
not flag this fault (inherited blind spot recorded in
hunts/lambda_dh_bounds/M2-LEMMA.md).

Evidence: hunts/lambda_dh_exact/MISSION.md, Section 4.7 'Lesion, recorded because it
fired silently' (lines 387-392); RESULTS.md Section 5 item 6 'Lesion evidence is
published, not resolved'
Prior art: unsearched
Reused in: Rule stated for every later phase using exact polynomial flow; lesion
cross-referenced to hunts/lambda_dh_bounds/M2-LEMMA.md
Why it travels: Cheap, mandatory sanity check for any root-tracking experiment on
high-degree polynomials: the answer at t=0 is known and must be reproduced before any
evolved root is believed.

## Epstein zeta, precision and zero counting

Precision floors for the completed Epstein zeta, what argument-principle box counts can
and cannot discriminate, and the rightmost-zero wall for the prime zeta.

- bound: Tail-subset wall lower bound via short-interval prime count
  (`prime_zeta_rightmost`)
- calibration: Precision-adequacy guard (evaluate at dps D and D+15) and the Epstein
  digit-loss rule dps = 20 + ceil(0.6822 t_max) (`gate5_p6_b`)
- calibration: Height-dependent precision rule for the completed Epstein zeta and its
  digit-loss law (`gate5_p6_c`)
- control: Parse-sensitivity and archimedean-envelope checks for detecting precision
  noise (`dps_cap`)
- control: Decided-root control battery: known-answer calibration plus template-swap
  lesion (`prime_zeta_rightmost`)
- control: Convergence-floor ladder before spending winding-number budget (`r_f7cd45`)
- obstruction: Local zero-free box properties cannot discriminate RH from its rivals
  (`gate5_p6_c`)

### Tail-subset wall lower bound via short-interval prime count

bound | `hunts/prime_zeta_rightmost/` | grade: proved in THEOREM.md (ordinary
derivation, self-reviewed); the numeric instance D3 is decided on two independent
backends (python-flint arb 350 bits, mpmath.iv dps 40)

For the k-th prime p_k >= 23 let S = {p >= p_k} and let sigma_c(p_k) be the unique root
in (1, inf) of the balance h(T) = sum_{p > p_k} p^{-T} - p_k^{-T} = 0 (the supremum of
real parts of zeros of the tail prime zeta function). Then sigma_c(p_k) >= B_k := log2(3
p_k / (5 log p_k)), which tends to infinity with k. Proof template: Rosser-Schoenfeld
(3.8) gives more than 3x/(5 log x) primes in (x, 2x] for x >= 20.5; each contributes at
least (2 p_k)^{-T}, so h(T) > 0 whenever 2^{-T} 3 p_k/(5 log p_k) > 1, i.e. T < B_k, and
monotonicity of h forces the root above B_k. Decided instance: B_9 = log2(69/(5 log 23))
in [2.1379035036560028560606113813, +1e-30], > 17/8 on both backends (D3). Corollary C3:
no constant bounds the real parts of zeros over all subsets of the primes.

Evidence: THEOREM.md, section 'Theorem C2 (tail subsets have unbounded walls)' and
'Corollary C3' (lines 576-644); RESULTS.md section 7.1 item (b) and section 1 (D3)
Prior art: searched-and-absent (four independent searches; the hunt itself notes this is
a statement about the searches). Framework (wall = balance root, triangle-inequality
proof) is prior art: Belovas-Cepaityte-Sabaliauskas 2025 Thm 1; Sepulcre-Vidal 2022 Thm
4.3. Rosser-Schoenfeld cited.
Reused in: docs/30-prime-zeta-rightmost-zeros.md
Why it travels: Turns any explicit short-interval prime-count inequality into an
explicit lower bound on the balance root of a tail Dirichlet series over primes; the
same three lines apply to any subseries where a leading term competes with a tail.

### Precision-adequacy guard (evaluate at dps D and D+15) and the Epstein digit-loss rule dps = 20 + ceil(0.6822 t_max)

calibration | `hunts/gate5_p6_b/` | grade: measured (two-precision replication guard,
mpmath)

Before trusting an argument-principle zero count of a completed L-function at height,
evaluate the integrand at the box corners at working precision D and again at D + 15 and
require relative disagreement below 1e-6 (worst observed 3.5e-22 across ten decided
cells). Calibration for zeta.epstein.epstein_completed: Lambda_Q is exponentially small
in t while its Mellin-split terms are O(10^-2), so about pi t/(2 ln 10) = 0.6822 t
digits are lost; at s = 0.8 + 85.7i, (2,1,3): 1.2e-34 at dps 20 versus 1.617e-58 at dps
60 and 90 against the analytic magnitude 2.64e-58. Preregistered rule dps = 20 +
ceil(0.6822 t_max) (28 for t <= 11.5, 79 for t <= 86.2). Defect found:
zeta.epstein.battery's rival interfaces cap dps at min(dps, 20), so above t about 25
they return winding numbers of round-off that still pass the integrality check.

Evidence: hunts/gate5_p6_b/RESULTS.md, 'The table' (adequacy paragraph lines 33-36),
'What was chosen, and why: The precision' (lines 85-99), 'A defect in the battery, found
on the way' (lines 165-185), loose thread 'A precision-adequacy guard as a reusable
instrument'
Prior art: unsearched
Reused in: none recorded
Why it travels: Every hunt evaluating a completed L-function at height needs the
digit-loss rule and the two-precision guard; the hunt states nothing in zeta/ offers it.
Index note: Fourth hunt to hit the Epstein digit-loss defect; belongs with the
gate5_p6_c, dps_cap and r_f7cd45 entries.

### Height-dependent precision rule for the completed Epstein zeta and its digit-loss law

calibration | `hunts/gate5_p6_c/` | grade: measured (three independent hunts, one route
each)

epstein_completed returns d^{s/2}(first + second/√d + 1/(√d(s−1)) − 1/s), a sum of
O(1/t)-to-O(1) terms, while |Λ_Q(s)| ~ |Γ(s)| ~ exp(−πt/2); so about πt/(2 ln 10) =
0.6822·t decimal digits cancel. Rule: evaluate Λ_Q at dps = 20 + ceil(0.6822·t_max) for
the box, a function of the box alone written before any winding number was computed.
Confirmed independently: dps_cap measured the noise floor at ≈1e-(D+13), crossover at t
≈ 50 for dps 20 (relative error passes 1 between t=45 and t=50), and r_f7cd45 measured a
convergence floor of dps ≈ 60 at t ≈ 85.5 (0.6822×85.5 ≈ 58). ξ and Davenport–Heilbronn
are unaffected at dps 20. The battery's hardcoded min(dps, 20) at zeta/epstein.py:1091,
:1141 therefore sits below the floor for every t ≳ 30.

Evidence: gate5_p6_c/RESULTS.md 'The defect that cost this hunt its high-t Epstein arm'
(lines 90–125); probe.py GUARD_PER_UNIT_HEIGHT = 0.6822 (lines 61–77); dps_cap/README.md
'Where up the strip the cap actually fails' (lines 143–168); r_f7cd45/RESULTS.md 'The
precision floor, measured' (lines 101–140)
Prior art: none; a defect in the lab's own module
Reused in: hunts/dps_cap (crossover table), hunts/r_f7cd45 (convergence-floor ladder),
gate5_p6_c B2/B4 counts
Why it travels: Any completed L-function evaluated via a sum of O(1) terms loses ~πt/(2
ln 10) digits at height t; the rule sets working precision from the box before spending
budget.

### Parse-sensitivity and archimedean-envelope checks for detecting precision noise

control | `hunts/dps_cap/` | grade: measured, one point (0.8 + 85.7i), form (2,1,3)

(a) Parse sensitivity: write the same evaluation point at several parse precisions
(mp.mpc('0.8','85.7') at dps 15, 20, 60, and as Python floats); a converged evaluation
must return the same magnitude for all, since the bit patterns denote the same number
far past any digit that matters. At dps 20 the returned |Λ_Q(0.8+85.7i)| spread by a
factor 64 across parses; at dps 60 no spread to twelve digits. This also reconciled two
earlier 'conflicting' numbers (1.2e-34 vs 3.1e-33) as two samples of the same floor. (b)
Archimedean envelope: divide the returned magnitude by |(√d/π)^s Γ(s)| (computable from
mp.gamma alone, touching nothing under test) to get the implied |ζ_Q(s)|; a Dirichlet
series continued into the strip grows polynomially, so an implied 1e25 at t=85.7 is
impossible while 0.61 is ordinary. (c) Refinement stability: the value at D=60 and D=80
agreeing to 1.5e-16 is the convergence control; D=30 returning exactly 0.0+0.0i is the
failure mode that looks like a root.

Evidence: README.md readings 1–5 (lines 57–141); FINDINGS.md 'Reading' (lines 18–46);
probe-f12f9441.py parse_sensitivity (lines 90–105), implied_abs_zeta_Q;
sanity_stirling.py
Prior art: unsearched
Reused in: gate5_p6_c and r_f7cd45 precision findings (same defect, independently);
HANDBACK.json thread on count_zeros_box
Why it travels: Both checks are routine-agnostic ways to tell a rounded answer from
noise; the envelope check works for any completed L-function with a known gamma factor.

### Decided-root control battery: known-answer calibration plus template-swap lesion

control | `hunts/prime_zeta_rightmost/` | grade: decided (two backends), as the hunt
states

A bisection root solver on a strictly decreasing function (decide.bisect_decreasing,
endpoint signs decided by ball/interval enclosures with exact-Fraction bracket
bookkeeping) is validated by five controls run through the identical code path: (1)
calibration: feed the zeta partial-sum balance 1 = sum_{n>=2} n^{-sigma} and recover the
OEIS value x* = 1.72864723899818361813... (31 digits on flint, 13 on iv); (2) input
lesion: drop one term (p = 3) and require a decided shift (0.35022851787919218338...);
(3) template lesion, the 'mis-port made mechanical': keep the zeta series but balance
the prime-zeta template's leading term 2^{-sigma} against the tail after it, which must
land at a value (2.4241112509134051...) decidedly equal to neither x* nor sigma_c,
proving both the series and the balance template are read; (4) precision response:
widths must shrink strictly (60/120/200 bits: 1.4e-15 / 6.2e-34 / 1.0e-57) with nested
intervals; (5) subprocess rerun reproduces decided.json line for line.

Evidence: RESULTS.md section '4. Calibration control and lesions (WP5)' (lines 282-317);
controls.py, controls_results.json
Prior art: unsearched (standard lesion discipline of the lab; the template-swap lesion
is the hunt's own)
Reused in: docs/30-prime-zeta-rightmost-zeros.md
Why it travels: Any 'decided constant' claim from a root solver can be pinned by the
same five-control sequence; the template-swap lesion specifically catches the failure
mode where a solver is ported from one balance problem to another with the wrong leading
term.

### Convergence-floor ladder before spending winding-number budget

control | `hunts/r_f7cd45/` | grade: measured

Before running an argument-principle count on a box, evaluate each completed function at
one interior point (0.75 + 85.5i) up a dps ladder and record the lowest dps at which the
value stops moving; cells whose preregistered precision is below that floor are marked
INADMISSIBLE and skipped rather than computed. Rationale: count_zeros_box's integrality
check cannot detect noise, since noise winds to an integer as readily as signal does, so
a below-floor count returns a plausible small integer that is not a zero count. Floors
found: ξ ≤ 15, Davenport–Heilbronn ≤ 15, Epstein (2,1,3) and (1,1,6) 60. A preregistered
dps 15 would have published a wrong integer.

Evidence: RESULTS.md 'The number this run adds: the precision floor, measured' (lines
101–134), Loose threads bullet 1
Prior art: unsearched
Reused in: confirms dps_cap and gate5_p6_c; recommendation to replace min(dps,20) with a
box-height floor pinned by a dps 60 vs 100 stability test
Why it travels: A pre-check that turns a silent wrong integer into an explicit
'inadmissible' for any contour-count oracle whose only self-check is integrality.

### Local zero-free box properties cannot discriminate RH from its rivals

obstruction | `hunts/gate5_p6_c/` | grade: measured (argument-principle counts,
count_zeros_box, preregistered boxes committed at c29c876 and 53c8cd1)

'In a box strictly off the critical line the completed function has no zeros' has no
truth value as a property: with σ ∈ [0.7,0.9] fixed, t ∈ [85.5,85.9] gives DISTINGUISHES
(Davenport–Heilbronn has its off-line zero at 0.80852+85.6993i, ζ has none) while t ∈
[10,14] and [40,44] give VACUOUS (all four functions have zero count 0). Mechanism: an
RH-violating function has a positive proportion of zeros on the line and sparse off-line
zeros, so any box missing them looks RH-satisfying; a local statement cannot carry a
global distinction. Every repair that both has a truth value and distinguishes collapses
to RH-with-a-margin (uncheckable in a box) or to 'no zeros with σ > 1' (the Euler
product, which is gate property 5 already). B4 in σ ∈ [1.05,1.55], t ∈ [10,14] returned
VACUOUS even though DH has zeros in σ > 1 by the 1936 theorem, because a width-4 window
is silent about the band. Reproduced independently by r_f7cd45 on preregistered boxes B1
[80,81] VACUOUS, B2 [85,86] with DH count exactly 1.

Evidence: RESULTS.md 'Answer', 'The table', 'Reading the flip', 'What a well posed
version would be' (lines 18–195); r_f7cd45/RESULTS.md 'The sixth property' (lines 67–99)
Prior art: cited: Davenport–Heilbronn 1936 (zeros in σ > 1); the well-posedness argument
is the lab's
Reused in: hunts/r_f7cd45 (independent reproduction); recommendation to retire property
6 from the battery
Why it travels: Closes the class of box-local zero-freeness properties as gate
discriminators, with an argument (sparse off-line zeros) rather than a failed run; the
blind/declared-non-blind box design is reusable for any local property.

## Erdos #126 and S-unit equations

Equivalent forms of the problem, residue-class and deletion lemmas, reductions to S-unit
equations, and the barriers that show which relaxations are exact.

- identity: Lattice rational identity for the depth-1 damage kernel: sign on 2 pi Z for
  all d without a horizon (`support_5418c63e`)
- identity: Four-subset to nondegenerate three-term S-unit equation reduction
  (`support_8ea74995`)
- lemma: Normalization lemma for S-admissible sets (dilates of primitive sets)
  (`support_60982bf6`)
- lemma: Deletion lemma and primitive descent g*(k) <= 2^k (`support_7ddfee4b`)
- lemma: Galois connection and six equivalent forms of Erdos #126 (`support_8ea74995`)
- lemma: Residue-class lemma for an omitted prime (correct form of the pigeonhole), with
  parity as the unique capping case (`support_8ea74995`)
- lemma: Lemma A: residue-class cap for S-summable sets at a prime outside S
  (`support_baf4cde6`)
- lemma: Four-subset to non-degenerate three-variable S-unit equation reduction
  (`support_baf4cde6`)
- lemma: Two-base-element injectivity lemma reducing Erdős #126 to a two-variable S-unit
  equation count (`support_d5d5ccae`)
- lemma: Unit-equation reduction for sets with S-smooth pairwise sums
  (`support_f3ab3e34`)
- bound: Counting-horn threshold: log Psi(2N,S)/k -> 0 iff log 2N = o(log rad S),
  two-sided (`support_95bb5cb7`)
- control: Control: cancellation-free cross-route for a high-cancellation Epstein value,
  and the ambient-precision argument trap (`support_e6241336`)
- obstruction: Order-blindness barrier: the selection lemma is equivalent to the target
  bound; corrected selection inequality (star) and the primitivity requirement
  (`support_517b887f`)
- obstruction: Refutation of the mod-p pigeonhole size bound, with the repaired
  residue-support lemma (`support_60982bf6`)
- obstruction: Residue relaxation (R1)+(R2) has optimum exactly 2^k: no
  residue/parity/deletion recurrence beats loss 2 per prime (`support_7ddfee4b`)
- obstruction: Amplification-refutes theorem and enumeration-is-refutation-only
  quantifier obstruction (`support_8ea74995`)
- obstruction: Obstruction: admissible cliques yield only four-term S-unit relations,
  for which no height theorem exists (`support_95bb5cb7`)

### Lattice rational identity for the depth-1 damage kernel: sign on 2 pi Z for all d without a horizon

identity | `hunts/support_5418c63e` | grade: derived (exact identity, checked to 8.4e-16
relative against direct evaluation; the cubic coefficients are double precision, not
enclosure-carrying, with wide sign margin)

With ghat(z) = int_{-1/2}^{1/2} cos(sqrt2 t) e^{zt} dt, the exact one-term form is
ghat(z) = [alpha z sinh(z/2) + beta cosh(z/2)]/(z^2+2), alpha = 2 cos(1/sqrt2), beta = 2
sqrt2 sin(1/sqrt2). For D(1,s) = -Re ghat(1+is)^2 at s = 2 pi d, cos s = 1 and sin s = 0
make cosh z, sinh z real, giving D(1, 2 pi d) = P(u)/(u^2-2u+9)^2 with u = (2 pi d)^2
and P(u) = p u^3 - (3p-3q+r)u^2 - (5p+2q-10r)u - 9(p+q+r), p = (1+cos sqrt2)(cosh1 - 1),
q = 2 sqrt2 sin(sqrt2) sinh1, r = 2(1-cos sqrt2)(cosh1+1). All coefficients of P but the
constant are positive, so P has one nonnegative root u* = 1.7707 < 4 pi^2, hence D(1, 2
pi d) > 0 for every integer d >= 1 (and D(1,0) < 0, harmless since P sums over p != q).
This replaces the measured 'P = 0 on the critical lattice out to d = 4000' ingredient of
the ceiling rho* <= 0.153216295 with a derivation for all d.

Evidence: RESULTS.md section 1 (one-term form, lines 42-59) and section 5 'The lattice
is exactly solvable', lines 164-194; section 6 for the consequence
Prior art: unsearched
Reused in: hunts/r_c7f779 (run 872d7dce) ceiling rho* <= 0.153216295, the P = 0
ingredient; RESULTS-37fb06a9.md section 2
Why it travels: The move 'evaluate the kernel only where it becomes rational (the
lattice) and decide the sign by a polynomial root count' turns a horizon-limited scan
into an all-d statement; also the edge law centre - 2 pi d = K/s with odd next-order
term translating rather than widening the window.

### Four-subset to nondegenerate three-term S-unit equation reduction

identity | `hunts/support_8ea74995` | grade: proved (elementary); the counting
consequence is conditional on the unbounded multiplicity M

If a,b,c,d are distinct positive integers whose six pairwise sums are S-smooth, then
(a+b)+(c+d) = (a+c)+(b+d) yields x+y+z = 1 (equivalently X+Y-Z = 1) in positive S-units
of Q with no vanishing subsum (a subsum vanishing forces a=d or b=c or a zero sum). So
an n-element witness supplies C(n,4) instances; if the map to solutions has multiplicity
<= M then g(k) <= (4! M N_3(S))^{1/4}, and N_3(S) = exp(o(k)) would prove #126. Known
lower bounds on S-unit solution counts (exp(c sqrt s / log s)) do not obstruct this. Gap
named: the multiplicity/distinctness step.

Evidence: RESULTS.md section 6 'S-unit form', lines 258-294; independently in
hunts/support_eccd5f5e/RESULTS.md section 7 Proposition, lines 238-271
Prior art: cited: Evertse 1984, Evertse-Schlickewei-Schmidt, Erdos-Stewart-Tijdeman
1988; the hunt says 'not a new idea in the field' but the explicit bridge was absent
from the prior hunt
Reused in: support_eccd5f5e and support_517b887f name it as the only door that reads
more than residues
Why it travels: Converts any sum-smoothness extremal problem into a unit-equation
counting problem with an explicit, checkable degeneracy analysis.

### Normalization lemma for S-admissible sets (dilates of primitive sets)

lemma | `hunts/support_60982bf6/` | grade: proved (ordinary, three-line), exhaustively
checked on the sweep's witnesses

S a finite set of primes; A ⊂ ℤ_{>0} finite is S-admissible if a + b is S-smooth for all
a ≠ b in A. If |A| ≥ 2 and d = gcd(A), then (1) d is S-smooth (d | a + b, divisors of
smooth numbers are smooth); (2) A/d is S-admissible and primitive; (3) for S-smooth m ≥
1, A is admissible iff mA is. Hence the S-admissible sets are exactly mA_0 with m
S-smooth and A_0 primitive admissible, and g(S) = max|A| is attained on a primitive set.
Consequence: widening the search box only produces dilates of small optima (e.g.
{120,2280,3720,10680,19320} = 40·{3,57,93,267,483}), which explains why box width
'changed not one row' in the predecessor hunt; the right box parameter is the height of
the smallest primitive optimum, not N. Checked on all 381 sweep witnesses.

Evidence: RESULTS.md §2 'Lemma 1 (normalization). Proved.' (lines 92–124); raw2.json
normalization_checks
Prior art: cited context: Erdős #126, Erdős–Turán finiteness; the lemma itself
unsearched
Reused in: §5 Conjecture 1 (height h(S) defined over primitive sets); audit table of
r_186989
Why it travels: Any smoothness-closed additive problem has the same dilation structure;
it converts a box-size question into a height question.

### Deletion lemma and primitive descent g*(k) <= 2^k

lemma | `hunts/support_7ddfee4b` | grade: proved (ordinary derivation, self-reviewed)

Let (S,A) be admissible (all distinct pairwise sums S-smooth) and p in S odd. Write A_p
= {a : p | a}, B_1 = union of classes c in [1,(p-1)/2], B_2 = union of classes -c. Then
A = A_p sqcup B_1 sqcup B_2 and each B_i is admissible for S minus {p}. For primitive A
(no element divisible by a prime of S) A_p is empty, so g*(k) <= 2 g*(k-1), and with
g*(1) = 2 (power-of-2 base case: a+b=2^x, a+c=2^y, b+c=2^z with a<b<c forces 2a<0) one
gets g*(k) <= 2^k, tight at k=1,2 ({1,5,7,11}, S={2,3}). The gap to g(k): A_p/p is
admissible for the same S, so the split is circular for non-primitive sets.

Evidence: RESULTS.md section 2 Theorems 2-4, lines 90-129; section 6 on the primitivity
hole, lines 221-236
Prior art: cited: Erdos-Turan 1934 (3*2^{k-1}); Erdos-Suranyi form 2^k noted in
support_517b887f section 1
Reused in: support_517b887f reconstructs the same architecture and finds the sketch
defects
Why it travels: A clean self-contained induction for smooth-sum problems; the
primitivity caveat is the exact place where 'divide by gcd' is not enough.

### Galois connection and six equivalent forms of Erdos #126

lemma | `hunts/support_8ea74995` | grade: proved (ordinary derivation, self-reviewed;
audited by a second arm)

With f(n) = min_{|A|=n} |P(A)| and g(k) = max_{|S|=k} max{|A| : P(A) subset S}
(distinct-pair convention): f is non-decreasing; g(k) is a genuine maximum (Erdos-Turan
bound uniform in S); f(n) <= k iff n <= g(k). Consequently the following are equivalent:
f(n)/log n -> inf; log g(k) = o(k); g(k)^{1/k} -> 1; f(2^m)/m -> inf; g(k) <= e^{ck}
eventually for every c; the Cesaro mean of log(g(j+1)/g(j)) -> 0. Correction recorded:
finiteness of g is equivalent to f -> inf, strictly weaker than f >> log n.

Evidence: RESULTS.md sections 1-2, Theorem 1.4 and Theorem 2.1, lines 42-112;
independently re-proved in hunts/support_eccd5f5e/RESULTS.md section 1
Prior art: cited: Erdos-Turan 1934 used as published
Reused in: support_eccd5f5e (audit), support_7ddfee4b, support_517b887f all use the g/f
inverse forms
Why it travels: Template for any min/max inverse-staircase pair; the Cesaro form (6) is
the one that makes direction results obvious.

### Residue-class lemma for an omitted prime (correct form of the pigeonhole), with parity as the unique capping case

lemma | `hunts/support_8ea74995` | grade: proved, with counterexamples verified by trial
division in results.json (three independent arms)

If P(A) subset S and the odd prime p is not in S, then at most one element of A lies in
class 0 mod p, the set R of occupied nonzero classes satisfies R cap (-R) = empty, so A
occupies at most (p+1)/2 residue classes mod p, and no bound on |A| follows (A = {1,
1+p, ..., 1+(m-1)p} has all pairwise sums = 2 mod p). p = 2 is the unique prime where
every class is self-paired, giving |A| <= 2 when 2 is not in S. The proposed claim |A|
<= p-1 is false for every prime (also at p=2 by {1,2}, S={3}), and would have settled
#126 in three lines.

Evidence: RESULTS.md section 4, lines 152-194; hunts/support_eccd5f5e/RESULTS.md section
5, lines 166-198; hunts/support_7ddfee4b/RESULTS.md Theorem 1 and Corollaries 1a, 1b,
lines 55-88
Prior art: unsearched
Reused in: support_eccd5f5e, support_7ddfee4b (three arms converge on the same
statement)
Why it travels: Also a control: a claim strong enough to settle a 92-year-old problem
that agrees with seven data points is a warning, not evidence; the sieve reformulation
(density 1/2 at every prime above max S) is the salvage.

### Lemma A: residue-class cap for S-summable sets at a prime outside S

lemma | `hunts/support_baf4cde6/` | grade: ordinary derivation, self-reviewed (two-line
proof), with computational checks (probe.py, stdlib)

Let A be a finite set of distinct positive integers with a + b free of primes outside S
for all distinct a, b in A, and let p be a prime not in S. Then (1) A contains at most
one element divisible by p; (2) A never meets both classes r and -r mod p for r not 0;
(3) hence A meets at most (p+1)/2 residue classes mod p; (4) for p = 2, |A| <= 2. Proof:
a = -b mod p with a != b gives p | a + b, so p in S. The cap is on classes, not
elements: any number of elements may share a class r with 2r not 0. Refutes the parent
thread 'prove |A| <= p - 1 when p not in S': A = {1,3,7,13}, S = {2,5,7}, 3 not in S,
|A| = 4 > 2; sweeps reach |A| = 5 (S = {2,5,11,17}, A = {1,9,31,79,241}). Verified on
all seven parent witnesses at every prime <= 37 outside S; {1,3,7,13} is sharp mod 3.

Evidence: hunts/support_baf4cde6/RESULTS.md, Section 1 table (loose thread refutation,
lines 58-67) and Section 2 'Lemma A: the exact local obstruction' (lines 69-95)
Prior art: Erdos-Turan 1934 bound cited; Lemma A itself unsearched
Reused in: Used in Proposition C (same hunt); proposed as a Lean target in the loose
threads
Why it travels: Exact local constraint for any 'pairwise sums avoid prime p' set system;
the class-versus-element distinction is the correction that other arms had missed.
Index note: Same statement as the support_8ea74995 residue-class lemma, reached
independently.

### Four-subset to non-degenerate three-variable S-unit equation reduction

lemma | `hunts/support_baf4cde6/` | grade: ordinary derivation, self-reviewed; the
reduction is proved, the counting bound is conditional on m

For distinct a, b, c, d in an S-summable set A, (a+b) + (c+d) = (a+c) + (b+d); dividing
by a + b gives x + y + z = 1 with x = (a+c)/(a+b), y = (b+d)/(a+b), z = -(c+d)/(a+b) in
the group of rationals supported on S (rank k plus sign). The solution is
non-degenerate: x + y = 0 is impossible for positive elements, x + z = 0 iff a = d, y +
z = 0 iff b = c. Hence C(|A|,4) <= m E_3(k), so |A| <= (24 m E_3(k))^{1/4}, where E_3(k)
bounds non-degenerate solutions and m bounds the fibers of the map 4-subsets ->
solutions. This is an upper-bound route; with Evertse-Schlickewei-Schmidt's
exp((6n)^{3n}(r+1)) the exponent constant is about 5e10 against Erdos-Turan's log 2, and
the fiber bound m is the missing lemma.

Evidence: hunts/support_baf4cde6/RESULTS.md, Section 6 'Where the constraint actually
lives' (lines 185-223)
Prior art: cited: Evertse-Schlickewei-Schmidt unit-equation bound;
Erdos-Stewart-Tijdeman lower bound exp(c (k/log k)^{1/2})
Reused in: none recorded
Why it travels: Precise transport of a pairwise-sum smoothness condition into
unit-equation counting, with the direction and the fiber gap stated so a later run can
attack m directly.
Index note: Same reduction as support_8ea74995 and support_d5d5ccae, reached
independently.

### Two-base-element injectivity lemma reducing Erdős #126 to a two-variable S-unit equation count

lemma | `hunts/support_d5d5ccae/` | grade: ordinary derivation, self-reviewed (two-line
proof); counts measured (exact enumeration in a box, lower bounds on N_S for d > 1,
oracle-checked against Lehmer's Størmer table for d = 1)

Let S be a set of k primes and A a finite set of distinct positive integers with every
off-diagonal sum a + b S-smooth (admissible); g(k) = max |A|. Lemma: for any a > b in A
with d = a - b, the map x -> (a + x, b + x) injects A \ {a,b} into Sol_S(d) = {(U,W): U
- W = d, U, W positive S-smooth}. Corollary: |A| <= 2 + min_{a>b in A} N_S(a-b) <= 2 +
max_{d>=1} N_S(d), finite by Mahler. Implication runs the useful way (bound on S-unit
solutions => bound on g(k) => Erdős #126); the converse fails. Free facts: gcd(a+x, b+x)
| d so Sol_S(d) decomposes over S-smooth divisors g | d as g times primitive solutions
of u - w = d/g; d = 1 is the Størmer case counted exactly by Lehmer. Quantitative
accounting: Evertse 1984 (ax + by = 1, at most 3·7^{d+2s}) gives g(k) <= 2 + 3·7^{2k+3}
~ 1029·49^k versus the elementary 2^k, so the theorem, not the route, is loose by
~24.5^k (measured: at k = 7 the lemma's value at the extremal witness is 96, 2^k = 128,
Evertse 7e14). Obstruction for higher arity: fixing three base elements gives (b-c)(a+x)
+ (c-a)(b+x) + (a-b)(c+x) = 0, a linear consequence of the two-element statement whose
coefficients are not S-smooth, forcing rank-based theorems (Beukers-Schlickewei
2^{16k+16}) instead of Evertse's arbitrary-coefficient accounting; cross-ratios of four
elements reintroduce the same defect. Named missing lemma: a constant c and phi(k) =
exp(o(k)) such that every admissible A with |A| > c has a pair with N_S(a-b) <= phi(k).

Evidence: RESULTS.md §1 (lines 24-53, lemma, corollary, direction), §2 (lines 55-79,
three-element downgrade), §3 (lines 81-111, Evertse vs Beukers-Schlickewei table), §4
(lines 113-160, exact N_S counts to 10^14 with Lehmer oracle check), §7 (lines 193-203)
Prior art: searched-and-absent, with the hunt explicitly not claiming originality: 'very
likely in Győry-Stewart-Tijdeman 1986 in some form'; Evertse 1984, Beukers-Schlickewei
1996, Erdős-Stewart-Tijdeman 1988 cited
Reused in: support run for hunts/r_186989 (0897a5a7 arm 'sunit-equations'); none else
stated
Why it travels: A clean bridge from any 'all pairwise sums are S-smooth' clique problem
to counting solutions of U - W = d in S-units, plus the exact statement of why gadgets
with three or more base elements lose (coefficients leave S).

### Unit-equation reduction for sets with S-smooth pairwise sums

lemma | `hunts/support_f3ab3e34/` | grade: proved (elementary), self-reviewed; checked
as exact rationals on the witness A = {1,2,3,5,7,13}, S = {2,3,5,7}

Let S be a set of k primes and A a set of n >= 3 distinct positive integers with every
off-diagonal a + b S-smooth. Lemma 1: d = gcd A is S-smooth and A/d is again valid.
Lemma 2: fix distinct a_1, a_2 in A, D = a_1 - a_2, and Gamma = <-1, p_1, ..., p_k, D>
<= Q^*, rank <= k + 1; then c -> (X_c, Y_c) = ((a_1 + c)/D, -(a_2 + c)/D) injects A
minus {a_1, a_2} into {(X, Y) in Gamma^2 : X + Y = 1}. Corollary: g(k) <= 2 + N(k+1)
where N(r) is the maximal number of solutions of x + y = 1 in a rank-r subgroup, so N(r)
= exp(o(r)) implies Erdos #126, and unconditionally g(k) <= 2 + 2^{8k+16} via
Beukers-Schlickewei. The implication is one-directional: lower bounds on N
(Erdos-Stewart-Tijdeman) cannot refute. Elementary lower bound: A = {1..m} is valid for
S = {p <= 2m - 1}, so g(k) >= (1 + o(1)) k log k / 2. Audit of r_186989's loose thread
3: the pigeonhole '|A| <= p - 1 when p not in S' is false for odd p (A = {1,3,7,13}, S =
{2,5,7} avoids 3 with |A| = 4).

Evidence: RESULTS.md sections '2. The lemma I attacked, in full: the unit-equation
reduction' (Lemmas 1, 2, Corollary, 'Direction check'), '4. Audit of r_186989' (4b, 4c);
probe.py checks.unit_equation_reduction
Prior art: searched, not found written down; the hunt says it is almost certainly
folklore inside the Gyory-Stewart-Tijdeman method; literature rows marked 'cited, not
verified at the source' (erdosproblems.com returned 403)
Reused in: none recorded
Why it travels: Localises the difficulty of a family of additive-smoothness problems in
a single named counting theorem, and the more-base-points variant (chain B: m base
points give m - 1 simultaneous twisted unit equations) is a concrete, unexamined door.

### Counting-horn threshold: log Psi(2N,S)/k -> 0 iff log 2N = o(log rad S), two-sided

bound | `hunts/support_95bb5cb7/` | grade: 'both directions are rigorous and measured'
(hunt's words): Rankin and simplex bounds are ordinary derivations, self-reviewed; the
table is measured; witnesses re-verified by trial division

Notation: S = k primes, rad(S) = prod p, theta = log rad(S), Psi(x,S) = number of
S-smooth integers <= x. Normalisation (N1): if A is admissible and lambda is S-smooth
then lambda A is admissible, and A/gcd(A) is admissible with gcd(A) S-smooth, so WLOG
gcd(A) = 1; (N2) translation is unavailable (A + t shifts sums by 2t), so max A is a
genuine invariant. Lemma 1: with a_n = max A the n-1 sums a_j + a_n are distinct
S-smooth integers in (N, 2N], so |A| <= 1 + Psi(2N, S). Lemma 2 (threshold): writing log
2N = c theta, log Psi(2N,S)/k = Theta_c(1) and -> 0 iff c -> 0, uniformly in k, with S =
first k primes the worst case. Upper: Rankin Psi(x,S) <= x^sigma prod_{p in S}(1 -
p^{-sigma})^{-1} minimised over sigma. Lower: lattice points of {e >= 0: sum e_i log p_i
<= log x} are S-smooth integers <= x and number at least the simplex volume (log
x)^k/(k! prod log p_i). Measured table: at c = 0.5 the lower bound is 0.32 k and at c =
1 it is 1.01 k, so for max A >= rad(S)^{1/2} the counting horn is false, not merely
unproven; at c -> 0 the Rankin bound -> 0. Consequence: the controlled-interval horn
yields log g(k) = o(k) iff max A = rad(S)^{o(1)}, and no refinement of the counting step
(dyadic, short interval) moves this. Companion measurement: primitive admissible triples
for S = {2,3} enumerated through their sums (the constrained objects, giving an
exhaustive universe) have height tracking the sum cutoff linearly over 10^4..10^15, so
sub-extremal admissible sets have unbounded height and any descent argument fails.

Evidence: RESULTS.md §1 (N1/N2, lines 23-38), §2 Lemma 1, Lemma 2 and table (lines
40-88), §3.1 (lines 92-117, sum-bounded enumeration and unbounded height), §5 'Added'
(lines 192-199, bounding sums is exhaustive for the property)
Prior art: cited: Rankin's trick, Lehmer/Størmer; the threshold lemma and the
sum-bounded enumeration are the lab's, unsearched
Reused in: audit of hunts/r_186989/RESULTS.md (corrects its claim that every optimal
witness has all elements < 50: the extremal 5-set {5,11,25,245,475} for S = {2,3,5} has
height rad^{1.81})
Why it travels: Gives the exact regime in which 'count smooth numbers in an interval'
arguments can and cannot deliver subexponential bounds, and the enumeration-through-sums
trick makes exhaustive searches honest for any 'all pairwise sums lie in a sparse set'
problem.

### Control: cancellation-free cross-route for a high-cancellation Epstein value, and the ambient-precision argument trap

control | `hunts/support_e6241336` | grade: measured (first rung for the value, second
rung for the agreement of independent routes)

epstein_completed at s = 0.8 + 85.7i splits the theta Mellin transform at t = 1 and
loses about 55 digits to cancellation (pole terms ~1e-3 against an answer ~1e-58), so a
dps ladder only shows convergence, not correctness. Three checks against routes that do
not share the cancellation: (A) normalisation at s = 4 where the lattice sum converges,
(B) the Dedekind class-number identity sum_Q Lambda_Q(s) = 2 (sqrt23 / 2pi)^s Gamma(s)
zeta(s) L(s, chi_{-23}), which reaches 1e-58 with no cancellation because the smallness
comes from Gamma directly (agree to 4.0e-17 at dps 60, 6.3e-76 at dps 120), (C) the
functional equation across the inverse class. Trap found: an mpc built at the ambient
default dps arrives short of digits and workdps inside the routine cannot repair it
(2.1e-15 shift at this point since d/ds log Lambda ~ log|s|); the same trap (reference
strings parsed at ambient dps) produced two uniform floors in rogue_frontier/weil_trunc,
detected by the 'identical floor across unrelated cells = artifact' reflex and by
checking floors for c-dependence.

Evidence: RESULTS.md 'How much of that number is real', lines 22-47; 'The three checks',
lines 49-83; 'One defect found', lines 85-103;
hunts/rogue_frontier/weil_trunc/RESULTS.md section 6, lines 204-215
Prior art: cited: Dedekind zeta factorisation for class number 3 discriminant -23
(standard); reproduces hunts/dps_cap (Hunt #12)
Reused in: reproduces hunts/dps_cap value digit for digit; trap recorded in
HANDBACK.json
Why it travels: Any Epstein/Dedekind evaluation at height where the Mellin split cancels
can be validated through the class-group identity; the ambient-precision trap is a
recurring lab defect with a named detector.

### Order-blindness barrier: the selection lemma is equivalent to the target bound; corrected selection inequality (star) and the primitivity requirement

obstruction | `hunts/support_517b887f` | grade: proved (ordinary derivation,
self-reviewed); exhaustive check of the repaired form over 104,183 admissible sets with
zero primitive violations (measured)

Define c(A) = max size of a subset of A all of whose distinct pairwise sums are powers
of 2. Then c(A) in {1,2} for every admissible A (archimedean base case), so for any phi,
[forall admissible A: c(A) >= |A|/phi(k)] iff [g(k) <= 2 phi(k)] up to a factor 2. c(A)
is defined by a maximum over subsets and mentions no prime order or grouping, so no
reordering or joint processing of primes changes what the Erdos-Turan architecture
proves. Two defects in the standard sketch: the per-prime halving |B'| >= |B|/2 is false
(A = {1,3,15,21,33}, q=3 gives 2 < 5/2); the correct form is |B'| >= (|B| - n_0(q))/2 +
min(n_0(q),1) and the assembled bound c(A) >= n/2^s needs primitivity (3*{1,3,7,17,47}
has c = 1 < 5/4). The CRT configuration x_eps = eps_i mod q_i realises the 2^s loss
exactly, jointly or one prime at a time.

Evidence: RESULTS.md section 3 (defects 3.1, 3.2), lines 77-116; section 4 Theorem
(order-blindness) and Corollary, lines 118-160
Prior art: cited: Erdos-Turan 1934, Erdos-Suranyi, Gyory-Stewart-Tijdeman 1986 as the
two-set tool the architecture does not use
Reused in: none recorded
Why it travels: Shows how to prove that 'reorder/combine the steps' cannot help: find
the order-blind quantity the architecture reduces to and show the refined lemma is the
target restated.

### Refutation of the mod-p pigeonhole size bound, with the repaired residue-support lemma

obstruction | `hunts/support_60982bf6/` | grade: unconditional (explicit witnesses
re-verified); the structural argument is an ordinary proof

Proposed (r_186989): |A| ≤ p − 1 whenever p ∉ S, by pigeonhole on residues mod p against
r ↔ −r. False for every odd p, structurally: p ∉ S forces a + b ≢ 0 (mod p) for distinct
a, b ∈ A, so the occupied residue set R satisfies R ∩ (−R) ⊆ {0} and at most one element
of A lies in class 0; but for odd p and r ≢ 0, 2r ≢ 0, so arbitrarily many elements may
share one nonzero class. The pigeonhole bounds the number of occupied classes by (p−1)/2
+ 1, not |A|. p = 2 is the unique prime with 2r ≡ 0 for all r, which is exactly why the
parity argument works there and nowhere else. Counterexamples (re-verified by trial
division): p=3, S={2,5,7,11,23}, A={5,45,65,95,155,395}, |A|=6; p=5, |A|=8; p=7, |A|=8;
smallest: S={2,5,7}, A={1,3,7,13}, 3 ∉ S. Repaired Lemma 3: for p ∉ S, A meets at most
one of {r,−r} for each r ≢ 0 and |A ∩ pℤ| ≤ 1; hence |A| ≤ 2 when 2 ∉ S, and no size
bound when p is odd.

Evidence: RESULTS.md §3 'Refutation: the mod-p pigeonhole lemma is false.
Unconditional.' (lines 126–180)
Prior art: none
Reused in: audit table §6; door ranking (2 ∈ S is the one proved binding constraint)
Why it travels: Closes the class of residue-pigeonhole size bounds for this problem with
an argument, and records the one prime where it works; the residue-support form is the
correct starting point for any counting argument.

### Residue relaxation (R1)+(R2) has optimum exactly 2^k: no residue/parity/deletion recurrence beats loss 2 per prime

obstruction | `hunts/support_7ddfee4b` | grade: proved (ordinary derivation,
self-reviewed)

A relaxed instance of order k is a finite set V, odd primes p_1..p_{k-1}, maps r_i : V
-> (Z/p_i)^*, and a graph G on V with (R1) every distinct pair either has r_i(u)+r_i(v)
= 0 mod p_i for some i or is an edge, and (R2) G triangle-free. Every primitive
admissible pair with 2 in S yields such an instance (G = pairs summing to a power of 2).
Theorem: max |V| = 2^k exactly (upper: the sign vector epsilon_i(u) = [r_i(u) in H_i]
has fibres that are cliques, so size <= 2; lower: V = {0,1}^{k-1} x {0,1} with residues
1 or p_i-1 and a perfect matching). Hence any exp(o(k)) bound must read something the
relaxation discards: actual S-smoothness (not just divisibility by some p_i), CRT
rigidity of residues of the same integer, or the ordering of Z.

Evidence: RESULTS.md section 3 Theorem 5 and the 'Discarded' table, lines 131-184
Prior art: unsearched
Reused in: support_517b887f's order-blindness barrier is the same wall from the
selection side
Why it travels: A template for proving that a whole family of cheap arguments is capped:
define the relaxation they all factor through, compute its exact optimum, list what it
discards.

### Amplification-refutes theorem and enumeration-is-refutation-only quantifier obstruction

obstruction | `hunts/support_8ea74995` | grade: proved (ordinary derivation,
self-reviewed)

(5.1) If g(k+C) >= lambda g(k) for constants C >= 1, lambda > 1 and all k >= k_0, then
log g(k) >> k and #126 is false; supermultiplicativity is the special case C=1,
lambda=g(1)=2, no Fekete needed. (5.4) #126 is a forall S forall A statement; every
bounded computation (clique search in a box, sweep over a finite family of S, witness
table) establishes an exists S exists A statement, so no enumeration can contribute to a
proof, only refute. Companion table of which WLOG normalisations are valid for upper
bounds (gcd A = 1, 2 in S) versus invalid (1 in A, max A <= N, S = first k primes), the
S-unit scaling orbit making every box unjustified for upper bounds.

Evidence: RESULTS.md section 5 Theorems 5.1, 5.2, 5.4, lines 196-248; section 3
normalisation table, lines 127-150; sharpened in support_eccd5f5e section 3 (composition
law would pin g(k) in [2^k, 1.5*2^k]; g(3) <= 7 refutes it) and 'Correction B' (report
max(g_N, ceil((p_k+1)/2)))
Prior art: cited: Erdos-Turan 1934; Fekete noted as unnecessary
Reused in: support_eccd5f5e, support_7ddfee4b, support_517b887f (direction-safe target
list)
Why it travels: A one-line test that sorts any proposed lemma or instrument into
prove/refute/settles-nothing before budget is spent; the quantifier argument applies to
every extremal problem attacked by search.

### Obstruction: admissible cliques yield only four-term S-unit relations, for which no height theorem exists

obstruction | `hunts/support_95bb5cb7/` | grade: ordinary derivation, self-reviewed
(argument from cited theorems plus the measured threshold table)

Height bounds for S-smooth numbers (Baker-Győry effectively, abc conjecturally) are
theorems about x + y = z with all three terms S-smooth or two smooth and one fixed. An
admissible clique (all pairwise sums a + b S-smooth) produces no such relation; its only
relations are (a+b) + (c+d) = (a+c) + (b+d), four-term S-unit equations, for which only
the Evertse-Schlickewei-Schmidt bound on the number of non-degenerate solutions is
available, which is exp(O(k)) and provably not improvable to exp(o(k)) in general
(Erdős-Stewart-Tijdeman exhibit S with more than exp(c (k/log k)^{1/2}) solutions of x +
y = 1). A count is not a height. Even the best imaginable outcome, a three-term relation
plus abc, gives max A <<_eps rad(S)^{1+eps}, i.e. c -> 1 in the threshold lemma where
the lower bound already reads 1.01 k, one full power of the radical above what the
counting horn needs. Hence the size dichotomy for Erdős #126 cannot close from inside
the data (integers and smoothness of pairwise sums); the missing object is a height
theorem for x_1 + x_2 = x_3 + x_4 in S-units with a clique-suppliable non-degeneracy
hypothesis.

Evidence: RESULTS.md §3.2 (lines 119-139), 'The doors' §3 information class (lines
236-243), loose thread 'Four-term S-unit heights' (lines 247-252)
Prior art: cited: Baker-Győry, abc, Evertse-Schlickewei-Schmidt, Erdős-Stewart-Tijdeman
1988
Reused in: agrees with hunts/r_186989's conclusion 'from the other side', now quantified
as one power of rad(S)
Why it travels: Closes every descent/height route to Erdős #126 that stays inside
smoothness-of-sums data, and states the exact literature request (a four-term S-unit
height theorem) that would reopen it.

## Lean arm: formalised elementary number theory

Kernel-checked Mertens bands, Abel summation by direct induction, and the transfer
patterns that make an aggregate inequality formalisable.

- lemma: Zero-admission sandwich for formalised extremal counts (`r_186989`)
- lemma: Pointwise-from-density transfer for normal-order theorems via the sqrt(N) split
  (`r_233abe`)
- bound: One-sided Mertens band accounting and the log t <= t/e majorant (`r_4218d4`)
- computational technique: Direct-induction discrete Abel summation and explicit Mertens
  bands in Lean (`r_3c1cbb`)
- obstruction: Supermultiplicative composition refutes rather than proves (Fekete
  direction check) (`r_186989`)

### Zero-admission sandwich for formalised extremal counts

lemma | `hunts/r_186989/` | grade: proved (elementary), self-reviewed; the finite table
is exhaustive over [0,40]

Let f(n) be the minimum over n-sets of positive integers and f_0(n) the minimum over
n-sets of nonnegative integers (the Finset N formalisation) of the number of primes
dividing some off-diagonal sum a + b. Then for n >= 2, f(n-1) <= f_0(n) <= f(n). Proof:
every positive set is a nonnegative set (upper); if an f_0-optimal set contains 0,
removing it leaves a positive (n-1)-set whose off-diagonal sums are a subset (lower).
Hence f(n)/log n -> inf iff f_0(n)/log n -> inf, so the formalised limit statement is
faithful, while pinned finite values differ (f(2) = 1 via {1,2}, f_0(2) = 0 via {0,1}).
Also proved: 2 not in S implies |A| <= 2 (parity), and g(1) = 2 (three elements with
pairwise sums powers of two are impossible).

Evidence: RESULTS.md section '2. Arm 0: the Formal Conjectures positivity mismatch.
Settled.' (lines 27-61); section 4 opening paragraph for g(1) = 2 and the parity remark
Prior art: unsearched
Reused in: hunts/support_f3ab3e34/RESULTS.md
Why it travels: The same one-step sandwich settles the 0-versus-positive mismatch for
any extremal problem over integer sets whose constraint is monotone under deletion,
before anyone repairs a formal statement unnecessarily.

### Pointwise-from-density transfer for normal-order theorems via the sqrt(N) split

lemma | `hunts/r_233abe/` | grade: kernel-checked (lake build
ZetaLean.HardyRamanujantheorem, zero sorry, axioms [propext, Classical.choice,
Quot.sound])

Given the density form of Hardy-Ramanujan at scale N (for every eps > 0, #{n <= N :
|omega(n) - log log N| > eps log log N}/N -> 0), the pointwise-normalised form
(deviation measured against each n's own log log n) follows with no new arithmetic:
split (0, N] at n^2 <= N; the low range has at most sqrt(N) elements and sqrt(N)/N -> 0;
on the high range N < n^2 gives log log N - log 2 < log log n <= log log N, so |omega n
- log log N| > eps log log n - log 2 >= eps log log N - (eps + 1) log 2 >= (eps/2) log
log N eventually; hence the pointwise exceptional set sits inside the low range union
exceptional(N, eps/2) and the density theorem at eps/2 finishes. The pointwise form
inherits every sharpening of the density form for free. Also: omega n =
ArithmeticFunction.cardDistinctFactors n is rfl (primeFactors.card vs
primeFactorsList.dedup.length unfold to the same term), giving a Mathlib-facing
statement hardy_ramanujan_cardDistinctFactors.

Evidence: RESULTS.md sections '(a) The bridge' and '(b) The pointwise form' (steps 1-4:
card_low_range_le, tendsto_natSqrt_div, loglog_band, exceptionalPointwise_subset); 'What
the kernel said'
Prior art: unsearched (the split is a standard device; the formal transfer is the hunt's
own)
Reused in: none recorded
Why it travels: The same split-and-slack transfer converts any scale-N normal-order or
density statement into its pointwise-normalised form in a formal library, at the cost of
one constant (log 2) and a sqrt(N) exceptional set.

### One-sided Mertens band accounting and the log t <= t/e majorant

bound | `hunts/r_4218d4/` | grade: kernel-checked (Lean 4 + Mathlib v4.33.0-rc2, zero
sorry, standard axioms), as the hunt states

Three local tightenings move the kernel-checked Turan variance constant from 5855 to 275
with no statement reshaped: (1) log t <= t/e for t > 0
(ZetaLean.Mertens.log_le_div_exp_one, from log x <= x - 1 at x = t/e), giving 2 sqrt(x)
log x <= (4/e) x < (3/2) x and psi(x) <= x log 4 + (3/2) x for x >= 1
(psi_le_const_mul_self'), against Mathlib's log 4 + 4; (2) sum_{n <= N} (log n)/n^2 <=
3/2 by starting the telescope at n = 2 (sum_{2 <= n <= N} n^{-3/2} <= 2 - 2/sqrt N) with
the same majorant, so the prime-power tail in Mertens I is 3 not 12; (3) keep the two
halves of the von Mangoldt form apart: the lower half loses only 1 and the upper half
loses the Chebyshev constant, and the prime form loses the tail on the lower side only,
so the honest band is max(c_psi, 1 + tail) = 4 instead of the symmetric c_psi + tail =
5.886 (new one-sided lemma log_sub_one_le_sum_vonMangoldt_div). Resulting constants:
mertens_first_theorem band log 4 + 3 = 4.3863 (was log 4 + 16), mertens_second_theorem
band 16 (was 76; assembly needs 15.698 with 1/log 2 <= 1.443), sum_sq_dev_le constant
m^2 + m + 3 = 275.

Evidence: RESULTS.md sections 'Before and after' (table), 'What was chosen, and why'
items 1-4; PrintMertensAxioms.lean; lean/ZetaLean/Mertensstheorems.lean
Prior art: cited: Mathlib Chebyshev.psi_le; sharp values 4/e and classical bands 2 and 4
quoted
Reused in: hunts/r_233abe/RESULTS.md; lean/ZetaLean/Mertensstheorems.lean;
lean/ZetaLean/HardyRamanujantheorem.lean
Why it travels: The majorant and the one-sided accounting are drop-in tightenings for
any formalised Chebyshev/Mertens-type chain; the quadratic propagation m^2 + m + 3 tells
you where upstream slack pays most.

### Direct-induction discrete Abel summation and explicit Mertens bands in Lean

computational technique | `hunts/r_3c1cbb/` | grade: kernel-checked (lake build exit 0,
zero sorrys by grep, no warnings)

Mertens's theorems kernel-checked against pinned Mathlib v4.33.0-rc2 with explicit
constants: |Σ_{n ≤ N} Λ(n)/n − log N| ≤ log 4 + 4; |Σ_{p ≤ N} (log p)/p − log N| ≤ log 4
+ 16 (mertens_first_theorem); |Σ_{p ≤ N} 1/p − log log N| ≤ 76 for every N
(mertens_second_theorem), all deliberately slack, with the slack decomposed into named
local steps (tightening the first band to the classical 2 would bring 76 to ≈ 9.8).
Technique that closed the second theorem: the discrete Abel identity Σ_{p ≤ N} 1/p =
A(N)/log N + Σ_{n=2}^{N−1} A(n)(1/log n − 1/log(n+1)), A(n) = Σ_{p ≤ n} log p/p, proved
by induction from N = 2 via Finset.sum_Ioc_succ_top (increment 1/(N+1) if N+1 prime,
else 0, one field_simp; ring per case) instead of reindexing Mathlib's range-indexed
sum_range_by_parts, killing the estimated 150–250-line reindexing labour; termwise
comparison via (v−u)/v ≤ log v − log u ≤ (v−u)/u at u = log n, v = log(n+1), with
overshoot ≤ 4/n² and Σ_{n ≥ 2} 1/n² ≤ 1 from sum_Ioc_inv_sq_le_sub. Also built: Σ_{n ≤
N} 1/(n√n) ≤ 3 − 2/√N (absent from Mathlib PSeries, which has only s = 2).

Evidence: RESULTS.md 'The statements that landed' (lines 23–47); RESULTS-second.md 'How
the block was closed' (lines 53–88), Loose threads; lean/ZetaLean/MertensSecond.lean
sum_inv_primes_eq (line 149), sum_Ico_telescope (line 128)
Prior art: searched-and-absent in pinned Mathlib (grep -ril mertens hits only
Dedekind–Mertens; SumPrimeReciprocals has divergence with no rate)
Reused in: hunts/r_8c3b94 (Erdős–Kac pricing uses mertens_second_theorem as the O(1)
band and finds the constant is not needed); the direct-induction Abel pattern flagged
for extraction
Why it travels: The induction-on-N Abel pattern closes any partial-summation argument
with a monotone weight f on [2,∞) without Finset reindexing; the explicit bands are the
constants downstream Lean work must consume.

### Supermultiplicative composition refutes rather than proves (Fekete direction check)

obstruction | `hunts/r_186989/` | grade: proved (elementary), self-reviewed; the search
data are lower bounds only

For Erdos #126 in the inverse form g(k) = max{n : f(n) <= k}, the conjecture is g(k) =
exp(o(k)). Any rigorous composition law g(k_1 + k_2) >= g(k_1) g(k_2) makes log g
superadditive, so by Fekete lim g(k)^{1/k} = sup g(k)^{1/k} >= g(1) = 2, hence g(k) >=
2^k and the conjecture is false. Therefore a 'find the gadget' lane is a refutation
search; the problem asks for an anti-composition theorem. Bounded evidence against any
small gadget: supermultiplicativity at (1,2) needs g(3) >= 8, exhaustive search to N =
60000 gives 5; all 11 tested (k_1, k_2) pairs fail by wide margins. Confirmed and
extended by the independent-architect arm: transferring Erdos-Stewart-Tijdeman's
exp((4+o(1))(s/log s)^{1/2}) construction would confirm, not refute.

Evidence: RESULTS.md section '4. Arm 3: the composition gadget points the wrong way'
(lines 108-143); support_f3ab3e34/RESULTS.md section '5. Routes that point at
refutation'
Prior art: unsearched
Reused in: hunts/support_f3ab3e34/RESULTS.md
Why it travels: A direction check to run on any proposed 'structure theorem' for an
extremal function before funding it: if the structure is a semigroup or product law with
a positive seed value, Fekete turns it into a refutation.

## Certificates, verifiers and exact arithmetic

Exact rational acceptance of published witnesses, fault-injection ladders for verifiers,
and the controls that separate an instrument reading from a mathematical claim.

- lemma: Signed-lattice binomial/trinomial sieve on a support torus (`r_044dd2`)
- lemma: Branch-and-bound prune soundness under nonnegative pair charges, with
  planted-bite control (`r_401bbf`)
- computational technique: Exact rational dual certificate by directed rounding of
  irrational LP coefficients (`overlap_lower`)
- computational technique: Semi-infinite LP repair: subtract the sup to get a valid
  bound and a bracket (`r_6f0f63`)
- computational technique: Exact rational acceptance of a primal step-function witness
  with mass repair, and the rounding-denominator calibration (`r_828c8b`)
- computational technique: Exact rational evaluation of autoconvolution functionals on
  step-function witnesses (knot lemma) (`r_8539dc`)
- control: Soundness read of a certificate verifier: target-encoding prunes, duplicated
  constants, binary64 goal comparisons, cap semantics (`bloch_ceiling`)
- control: Theorem-universe instrument validation: point the diffraction instrument at a
  proved quasicrystal before pointing it at zeta (`golden_control`)
- control: Planted-fault guard audit against provable monotonicity, with the recorded
  miss (`overlap_lower`)
- control: Independence-by-mutation: shared-layer lesion for 'independent' verification
  routes (`r_065f29`)
- control: Axis-separated sweep and hypothesis check of a falsification control's family
  (`r_065f29`)
- control: Control: planted-fault lesion with two separated verdict classes (`r_0dfb8d`)
- control: Mutation battery for a detector with exit-code, diff and token-in-diff as
  three separate readings (`r_414eed`)
- control: Instantiate every enclosure lemma at a recorded box, and parametrise seam
  denominators as free reals (`r_6c7d6a`)
- control: Planted-fault ladder for a polynomial certificate verifier (`r_6f0f63`)
- control: Stopping rule for cutting-plane loops: test the true constraint residual, not
  objective stall; monotonicity separates solver stall from family ceiling (`r_828c8b`)
- control: Control: a margin against a prediction drawn at the bound is not evidence;
  verify the obligation that spends the constant (`r_908de5`)
- control: Control: compare a sup only on the range the lemma asserts, and price
  depth-interval inflation before declaring a constant broken (`r_a7c12f`)

### Signed-lattice binomial/trinomial sieve on a support torus

lemma | `hunts/r_044dd2/` | grade: exact (integer certificates, independently audited);
the hunt labels the algebraic sieve 'open' overall

For a polynomial system restricted to a candidate support (all supported variables
nonzero, a torus), every equation whose support has exactly two monomials x^a + x^b = 0
yields the signed lattice relation x^{a-b} = -1. If an odd integer combination of these
relations equals the exponent difference of two terms of an equation whose support has
exactly three monomials, those two terms cancel identically on the torus, forcing the
remaining supported monomial to vanish, which is impossible; hence the support is
infeasible. Each exclusion is an exact integer certificate (l1 norms 1, 3, 1 for three
successive orbit-18 supports of the Krenn-Gu 8x3 system, with 81/240/42 zero-binomial
relations and 771/792/294 zero trinomials), independently verified by audit_laurent.py
(binomial and trinomial supports, exponent identity, odd parity, nonzero forced
monomial).

Evidence: RESULTS.md 'Result 2: three successive orbit-18 supports have exact
contradictions' (statement, table, audit paragraph); laurent_sieve.py; audit_laurent.py;
CHECKSUMS.sha256
Prior art: unsearched
Reused in: none recorded
Why it travels: A cheap exact pre-filter for any support-enumeration attack on a sparse
polynomial system (matching polynomials, design equations): it kills branches with a
small integer certificate before any Groebner or numerical solve.

### Branch-and-bound prune soundness under nonnegative pair charges, with planted-bite control

lemma | `hunts/r_401bbf/` | grade: measured to double precision (both solvers float;
residual 1e-16), plus an ordinary derivation, self-reviewed, for the soundness claim

Consider maximising a quadratic trade over multiplicity vectors m (sum m <= budget) with
objective val = sum_i cap_i m_i - sum_{j<i} 2 q_ji m_j m_i - (diagonal terms), zones
sorted by descending cap. Claim: if every pair charge q_ji >= 0 and every cap >= 0, then
the inner prune 'descend into branch m only if v > val - 1e-18 or m == 0' removes
nothing and the outer bound 'return if val + rem*caps[idx] <= best' is admissible, so
the search returns the exact maximum. Proof: F(ms, idx, rem) (best completion) is
nondecreasing in rem and nonincreasing in each prefix multiplicity (a prefix atom enters
only through -2 q m_j m_i <= 0); a non-improving branch's best completion v + F(ms+[m],
idx+1, rem-m) <= val + F(ms+[0], idx+1, rem), which the always-taken m = 0 branch
reaches. The hypothesis holds by construction when q = Kpair(.)/200 with Kpair =
Re(ghat)^2, a square, for any cap vector. The 1e-18 tolerance is in the permissive
direction. Planted-bite control: break the hypothesis with one negative off-diagonal
charge and the four cut configurations give 0.184 / 0.146 / 0.226 / 0.226 against
exhaustive 0.226, showing the probe detects a bite and that disabling only the inner
prune (0.146) is worse than leaving both cuts (half-audit worse than none). Audit
method: since components have at most 8 charged zones, enumerate all C(Z+10,Z) <= 43758
vectors as one vectorised quadratic form (exact maximum with no cuts) and difference
against the published search cell by cell on the same zone data: 13,200 cells, max
|delta| 1.1e-16, 1467/965 negative deltas proving the residual is summation order.

Evidence: RESULTS.md §0 table (lines 11-36), §1 (lines 38-66, exhaustive enumeration as
a fortiori bound), §2 'Claim' and proof (lines 74-115), §3 controls table and planted
bite (lines 119-145); test_prune_discharge.py
Prior art: unsearched (standard branch-and-bound monotonicity; the hunt does not claim
novelty)
Reused in: discharges the load-bearing assumption recorded in hunts/r_a97060/RESULTS.md
§4 for hunts/frontier_math/k2_closure.py zone_trade; recommends the exhaustive trade
replace the heuristic
Why it travels: Whenever a heuristic pruning rule in an LP/branch-and-bound feeds a
published table, the pattern is: prove the prune sound from a sign hypothesis that holds
by construction, enumerate exhaustively where components are small, and plant a
hypothesis-breaking instance to show the audit can see a bite.

### Exact rational dual certificate by directed rounding of irrational LP coefficients

computational technique | `hunts/overlap_lower/` | grade: VERIFIED (exact arithmetic, no
floating point in the value)

For White's simplified program (4.1)-(4.4), the dual is: maximize (N/4) lam - z/3
subject to sum_j y_j <= 1, lam <= y_j + sum_m a_{m,j} u_m + s_j z for all j, y,u,z >= 0.
The float solver only proposes (u, z). Then in fractions.Fraction: replace each
trigonometric envelope alpha^-_{j,2m} by a rational lower bound (float cosine, floored
at denominator 10^7, minus one unit, minus the Lipschitz term as an exact rational),
which enlarges the primal feasible set and can only weaken the bound; form theta_j
exactly; find the largest feasible lam exactly by sorting theta. At N, R = 5000, 20:
float optimum 0.3739966049729149, exact dual value 0.37399241331212807... (29-digit
numerator over 29-digit denominator), sum y_j = 1 exactly, dual feasible exactly, cost
of directed rounding -4.19e-6. The exact step is also the only guard that catches a
dropped envelope (front F): monotonicity in N and R does not.

Evidence: hunts/overlap_lower/RESULTS.md, Section D3 'Exact rational dual certificate
(VERIFIED)' (lines 257-287) and Section F 'The guard, and what it misses' (lines
406-434)
Prior art: White arXiv:2201.05704 program cited; exact directed-rounding acceptance
unsearched
Reused in: none recorded
Why it travels: Template for turning any float LP dual into a rigorous certificate when
constraint coefficients are irrational: round each coefficient in the direction that
relaxes the primal, then verify feasibility and value in exact rationals.
Index note: See the r_8539dc entry: same family.

### Semi-infinite LP repair: subtract the sup to get a valid bound and a bracket

computational technique | `hunts/r_6f0f63/` | grade: measured (float, rung 1); the
repaired value would be enclosure-carrying only after recomputing sup in ball arithmetic
and rationalising coefficients, not done

A Delsarte-type LP (Gegenbauer basis, f_0 = 1, coefficients f_k ≥ 0, f(t) ≤ 0 on
[−1,1/2]) solved on a finite node set is a relaxation, so its optimum can sit strictly
below the true LP value and is not a bound: at m = 600 nodes in dimension 24 it reports
196505.76 for the exactly-tight 196560 (dimension 8: 239.9930 for 240), at every m
tested up to 20000. Repair: compute M = sup_{[−1,1/2]} f (here via Chebyshev
interpolation and companion-matrix roots); if M > 0 and f_0 > M, then f − M satisfies
the sign condition exactly, leaves f_k (k ≥ 1) untouched, and gives the valid value
(f(1) − M)/(f_0 − M). The true LP value is bracketed: node optimum ≤ truth ≤ repaired
value, the repaired value converging from above. Measured: the one-sided error decays
like m⁻² with Chebyshev-clustered nodes; degree saturates by d ≤ 14 in every dimension
3–24, so node count, not degree, is the binding parameter.

Evidence: RESULTS.md §2 'The soundness read' (lines 55–103), §3; probe.py
sup_on_interval (line 91), repaired_bound (line 114); HANDBACK.json core_candidates
Prior art: unsearched; hunt says 'built by hand'; Delsarte LP and the tight E8/Leech
certificates are the literature's
Reused in: HANDBACK.json names zeta/weil.py positivity probe as first consumer (not
done)
Why it travels: Every semi-infinite programme in the lab (Delsarte, Cohn–Elkies,
Bachoc–Vallentin, Weil-positivity probes) is discretised in the same unsound direction;
the repair prices the coarseness instead of hiding it.

### Exact rational acceptance of a primal step-function witness with mass repair, and the rounding-denominator calibration

computational technique | `hunts/r_828c8b/` | grade: VERIFIED for the acceptance step
and D1-D2; MEASURED for D3 witnesses

The value of an m-piece step function f for Erdos's overlap functional is a finite sum
of products of its pieces. Round the pieces to multiples of 1/D, repair the mass
constraint in Q so the object is exactly feasible, then evaluate max_j h_j with
fractions.Fraction; no floating point survives into the value. Calibration: at the
natural D = 2m the rounding penalty is 2.4e-4 to 6.8e-4 (larger than the remaining gap
to the published constant); D = 20m costs nothing in runtime and drops the penalty to
1.1e-5. Best exact object: C <= 9990167/26214400 = 0.381094627... (128 pieces, D =
2560). Also the vacuity obstruction for single-weight averaging: for any probability
density w on the shift axis, sup_t h_f >= <f, w*1> - <f, w*f>, but the naive Fourier
bound <f, w*f> <= sup what * ||f||_2^2 <= 1 since what(0) = 1, so the bound collapses to
<= 0 for every admissible weight (200 random weights: 0 positive), and explicit
f-witnesses cap the averaging skeleton at 0.2526 (uniform), 0.2500 (tent), 0.1909,
0.1701.

Evidence: hunts/r_828c8b/RESULTS.md, Section C 'The acceptance step (VERIFIED)' (table
lines 96-103, remarks 1-2) and Section D 'The lower-bound side' D1-D3 (lines 134-181)
Prior art: White arXiv:2201.05704 and Haugland cited as reference values; acceptance
step unsearched
Reused in: none recorded
Why it travels: Generic exact acceptance for any upper-bound witness given by a finite
parameter vector, with a measured warning that coarse rounding throws away more than
float optimisation gained; the D2 argument kills any 'average against a probability
weight, bound the quadratic term by Parseval' route in one line.
Index note: See the r_8539dc entry: same family.

### Exact rational evaluation of autoconvolution functionals on step-function witnesses (knot lemma)

computational technique | `hunts/r_8539dc/` | grade: measured (the hunt's own words:
every arithmetic step is exact rational arithmetic on the published decimals; what is
not exact is the published truncated witnesses themselves)

For a step function f on [−1/4, 1/4] with n equal steps of width h = 1/(2n) and heights
a_0…a_{n−1}, f*f is supported on [−1/2, 1/2], is piecewise linear with knots at
multiples of h, and takes the value h·b_k at the k-th knot where b = a⋆a is the discrete
autoconvolution. A piecewise-linear function attains its extrema at knots, so with ∫f =
hΣa: A := max_t (f*f)(t)/(∫f)^2 = 2n·max_k b_k/(Σa)^2 and B := max_t |f*f(t)|/(∫f)^2 =
2n·max_k |b_k|/(Σa)^2. Since ∫f*f = (∫f)^2 > 0 forces max_t f*f > 0 for every admissible
f, an abs() outside the max is a no-op, and A ≤ B always, so a bound under B is a bound
under A but not conversely. Ingest published ten-place decimals as Fractions with
denominator 10^10 so the entire chain is integer arithmetic, and self-check the
discretisation by reproducing a published figure on which both readings must agree
(1.4688 at n = 150, where max|b| = max b). Results: height_sequence_3 (n = 400) gives A
= 1.455642795374540… but B = 4.334046524387984… (extreme knot negative at index 215);
height_sequence_4 (n = 150) gives A = B = 1.468762069741021…; so 1.4557 was stated
against the wrong functional in November 2025, and the corrected statements (arXiv v2,
colab commit 39d0c63) survive with no number moving.

Evidence: hunts/r_8539dc/RESULTS.md §1 The two functionals, and why the published abs()
is a no-op; §2 Both functionals on both published sequences, exact; probe.py
(exact_heights, autoconvolve, functionals); MISSION.md kill_conditions
Prior art: unsearched for the knot lemma (elementary); the functionals and prior bounds
are Matolcsi–Vinuesa 2010 and Vinuesa 2009 as published
Reused in: none stated; HANDBACK.json names it a Core candidate shared with r_2ac05f,
r_a7c12f and overlap_lower, each of which hand-rolled its own exact evaluator
Why it travels: Any published constant defined as a max of a convolution of a
step-function witness can be recomputed exactly under each candidate reading of the
inequality, on the same witness, with the discretisation validated by a figure both
readings share.
Index note: Same technique as the exact rational acceptance in overlap_lower and
r_828c8b; three hunts each hand-rolled it, which is exactly the reuse this index exists
to stop.

### Soundness read of a certificate verifier: target-encoding prunes, duplicated constants, binary64 goal comparisons, cap semantics

control | `hunts/bloch_ceiling/` | grade: measured/verified code reading; no finding
overturns a published run

Checklist applied to third-party rigorous verifiers, each item with a finding: (1) does
any prune's justification encode the target (the Hunt #79 zeta pattern)? Bloch: no, the
away subdivision discards a box only against goal = sqrt(3)/4 + target with target a run
parameter. (2) Are load-bearing constants duplicated across source and stored data and
read by different routines with nothing asserting agreement? Bloch: ETA and LARGE_RAD
live in three places; verify_positivity uses the source LARGE_RAD while
verify_near_moment integrates to the data's large_rad (latent, bit-identical as
shipped). (3) Does a constant silently encode another certificate's result? Bloch: C =
3.2888 is valid only because the fine fixed-radius certificate proves |a_3| <=
3.28877762819, asserted nowhere in the variable-radius programs. (4) Are Arb bounds
compared against a goal computed in binary64? Bloch: float(sqrt(3)/4 + 0.0153) is
4.5e-17 below exact, so accepted sectors prove target - 4.5e-17. (5) Does the cap refuse
or accept when hit? Bloch: refuses (RIGOROUS INCOMPLETE), soundness untouched but the
documented command cannot reproduce the run. Field audit of trmdy: acceptance one-sided
against the target rounded up, tables clamped nonnegative before unsigned products,
sign-aware product used where the table can be negative, float pre-filter can only
decline to prune.

Evidence: hunts/bloch_ceiling/RESULTS.md, Section 3 'Soundness read of the verifier'
(findings 1-6, lines 117-180); hunts/field_audit/RESULTS.md Section 6 'Soundness read of
trmdy's verifier' (lines 187-259)
Prior art: lab-internal pattern (Hunt #79 / Gohms target-wiring); unsearched externally
Reused in: hunts/field_audit/RESULTS.md Section 6 applies the same read to
trmdy/zeta-simple-zeros-673137
Why it travels: A concrete, repeatable audit list for any interval/Arb branch-and-bound
certificate; distinguishes latent from load-bearing defects and names the sound failure
direction for each.

### Theorem-universe instrument validation: point the diffraction instrument at a proved quasicrystal before pointing it at zeta

control | `hunts/golden_control/` | grade: measured (numpy float64; exact integers for
the Pisano stage); 'instrument validation against a proved answer, in the same spirit as
zeta/finitefield.py'

Before trusting a tapered-transform 'atoms at log prime powers' measurement on zeta's
zeros, run the identical transform architecture on objects whose spectrum is a theorem,
with predictions pre-registered: P1 calibration on Z (Poisson summation peaks at 2pi,
4pi, 6pi to 6.4e-14, fixing the instrument's one constant, taper mass T sqrt(2pi), by an
elementary identity); P2 the golden cut-and-project set with window [0,1), density
1/sqrt5, whose Fourier module and intensity law |W|/covol * |sinc(k*|W|/2)| are derived
in code from the embedding lattice and reproduced to 8.7e-9 in position and 2.5e-8
relative in amplitude; P3 silence off the module (200 random frequencies, median 1.0e-5
of scale vs weakest peak 9.7e-2, 9717x separation against a 30x bar; zeta's prime-power
gate measured 26.8x); P4 lesions: Gaussian jitter suppresses peaks by the Debye-Waller
factor (log-slope vs -sigma^2/2 within 1%), a Poisson set of matched density shows max
response 14x below the weakest true peak; P6 precision response monotone under doubling
extent/taper (8.6e-9 -> 1.8e-9 -> 1.0e-10). P5 recorded a pre-registered Pisano claim
that the exact-integer stage falsified at p = 3 (correct statement: pi(p) | p-1 when
chi5(p) = 1, pi(p) | 2(p+1) when chi5(p) = -1), kept on the books as the
derive-never-remember rule doing its job.

Evidence: RESULTS.md 'What was measured' P1-P6 (lines 15-52), 'What this buys the tree'
(lines 54-62); probe.py, results.json; MISSION.md pre-registered predictions
Prior art: cited: Poisson summation, cut-and-project diffraction theory, Debye-Waller;
the control design is the lab's
Reused in: KAPPA-CLOSED-FORM.md §5 in hunts/lambda_dh_bounds (conductor-5 golden
arithmetic connection); the quasicrystal gate on zeta inherits the control
Why it travels: Any spectral instrument aimed at an arithmetic object should first
reproduce a proved spectrum, a proved silence and a quantitative lesion law; the
pre-registered bars and the recorded failed prediction are the reusable discipline.

### Planted-fault guard audit against provable monotonicity, with the recorded miss

control | `hunts/overlap_lower/` | grade: measured

When a program is provably monotone in a parameter (adding constraints cannot lower a
minimum; refining a grid cannot lower a relaxation), plant faults in the builder and
check which are caught by monotonicity in N and in R. At N, R = 2000, 10: negative
control 0.372105479; drop the pi m L/4 envelope: +2.84e-3, unsafe direction, NOT caught
(the defective program is still monotone, it is simply a different program); constrain
every other mode: -1.33e-2, safe, not caught; constrain cos(pi m x) at odd m:
infeasible, unsafe, caught. Conclusion stated for reuse: on this program the guard is
the exact acceptance step, and monotonicity is not a substitute for it. Companion from
r_828c8b: grid_sufficiency_defect (8x-refined reference supremum minus reported maximum)
over 40 random step functions catches mis-strided enumeration (defects 0.104, 0.067) but
not truncation of the shift range (0.000), a miss written into the guard ledger.

Evidence: hunts/overlap_lower/RESULTS.md, Section F 'The guard, and what it misses
(MEASURED)' (table lines 416-421); hunts/r_828c8b/RESULTS.md Section E 'The guard, and
its power (MEASURED)' (table lines 207-212)
Prior art: unsearched
Reused in: r_828c8b records its miss in harness/departments/guard_ledger.py
Why it travels: A cheap power measurement for any monotonicity-based sanity check: it
tells you which fault classes the check is blind to, so the blind class can be covered
by an exact step.

### Independence-by-mutation: shared-layer lesion for 'independent' verification routes

control | `hunts/r_065f29/` | grade: measured

Two verification routes are independent only on the layers they do not share. Test:
mutate a layer both routes import and check whether their outputs diverge; if both move
by the identical amount they are one route. Applied to the urms2-0.51 window functional,
mutating the shared layer moved both the primary route and the audit's 'JSON fixture and
rebuilt tail sum' route by exactly 4.426081703885579e-27, the tail terms are
bit-identical exact rationals, and the fixture C2_EXTENDED.json reproduces
corrected_coefficients(40) index for index: the audit route is a second arithmetic
assembly of the same numbers. Companion formulation in the compiler department:
enumerate each route's layers and report the independence radius (shared prefix length),
e.g. 1 of 6 with only 'LLVM IR text' shared; agreement is evidence only about the
distinct layers. The director's ledger states the same for zeta/rigor.py's two backends
(shared _exact, contour, grid policy) and predicts the next correlated failure will be a
shared input.

Evidence: RESULTS.md table row A2 and section 'A2: gate 6's independent route is
arithmetic, not independence'; director_run/CLAIMS.md C-RIG-01 and C-RIG-03 and
GRAVEYARD.md 'Standing predictions' item 2; r_e2ee73/RESULTS.md section '6. Verification
Path Independence'
Prior art: unsearched
Reused in: hunts/director_run/CLAIMS.md; hunts/r_e2ee73/RESULTS.md;
harness/departments/review_ledger.py
Why it travels: A mechanical check to run before any 'two independent routes agree'
sentence is written, in Python or Lean or C++: plant one fault in the suspected common
layer and watch both routes.

### Axis-separated sweep and hypothesis check of a falsification control's family

control | `hunts/r_065f29/` | grade: measured (numpy and sympy, no enclosures)

A control offered as evidence for a step must (a) run on a family satisfying that step's
hypothesis and (b) vary the quantity the step claims is invariant while holding the
others fixed. The urms2-0.51 record's section 9 ladder moves x = e^{0.51 l} and W = e^l
together along one ray, so its decreasing sequence (0.409, 0.282, 0.185) is consistent
both with the claimed W-independence and with W^{0.825} growth; sweeping W alone at
fixed x on the record's own frozen coefficient family shows the upper-range sum growing
32.1x, and that family violates the hypothesis A(y) << y log y (A(y)/(y log y) climbs by
a factor 88 from 0.0231 at y = 400 to 2.036 at y = e^{10}), whereas a surrogate built to
satisfy the law (|b(n)|^2 = log n) saturates (441.6 -> 984.7 over a 67x sweep). The
load-bearing step itself survives when attacked correctly: the exact block second moment
int_U^{2U} |sum c_n n^{-it}|^2 dt saturates to four figures (17.2964 -> 17.3642) as W/U
grows 7.5x. Also found: the recorded rational witness does not select alpha = 51/100
(admits 257/500 at the published (delta, gamma, eps), and 0.9 with them free).

Evidence: RESULTS.md table rows A1, A3, A5 and sections 'A3: the load-bearing step holds
where it was attacked', 'A5: the record's own control does not satisfy its own
hypothesis'; probe.py; results.json
Prior art: unsearched
Reused in: harness/departments/review_ledger.py
Why it travels: Two questions to ask of any numerical falsification table before citing
it: does the family obey the hypothesis, and does the sweep move the claimed-invariant
axis alone; both are cheap and both were failed by a record that looked supported.

### Control: planted-fault lesion with two separated verdict classes

control | `hunts/r_0dfb8d` | grade: VERIFIED (re-derived from pinned artifacts), per the
hunt's own label scheme

For a two-verdict reproduction (A: aggregate recount equals the published integer; B:
each per-instance verdict is consistent with the stated rule, required lists taken from
the split not the entry), lesion a copy of one unit's archive with four faults chosen so
that the expected response pattern differs per class: flip one verdict (A mismatch, B
inconsistent), add a failure under a positive verdict (B only), drop required successes
(B only), delete one report file (A only). All four must be detected and the two classes
must move independently. Supplement: a finer published artifact (12 per-repository
sub-counts) is cross-checked so one aggregate agreement cannot come from cancelling
errors. Recorded self-catch: a '+' in an object key read as a space produced a false
absence; a procedure that reports the target's absence when the fault is its own fetcher
is the failure mode this class of check exists to catch.

Evidence: RESULTS.md 'The check can fail: four planted faults, four reds', lines 71-86;
per-repo cross-check, lines 55-60; section 6 on the self-inflicted retrieval bug, lines
187-194
Prior art: unsearched; label scheme inherited from Hunt #80
Reused in: labels and shape carried from hunts/r_* Hunt #80; probe.py control stage
Why it travels: The 'lesion must move exactly the class it should' design is the same
discipline the Lean lesion tests use, applied to any recount/reproduction instrument.

### Mutation battery for a detector with exit-code, diff and token-in-diff as three separate readings

control | `hunts/r_414eed/` (extended by hunts/r_7ad39f/` and `hunts/r_cb5ffe/) | grade:
measured (17/17 in-scope, 1 genuine miss; 0/299 exhaustive; 5/10 for test_doors.py); 'a
mutation battery is a sample, not a census' where stated

To measure a guard's power and scope rather than assert it: (1) copy the tree to a
throwaway sandbox (never mutate the live checkout); (2) null control: run the unmutated
sandbox through the guard first (rules out catches caused by the copy); (3) after every
mutant, undo and re-run the guard (rules out row n+1 inheriting row n); (4) for each
mutant record not only the exit code but the number of diff lines in the regenerated
artifact and whether the mutant's own new symbol appears in that diff, distinguishing
'caught by comprehension' from 'caught by accounting' (a line-count tell); (5) include
boundary probes expected to be silent and a control mutant with no symbol at all (one
blank line); (6) apply all escapes simultaneously to one tree to confirm the miss is
measured, not inferred; (7) run the expensive tier only where the cheap tier gave
'escaped'. Findings that make it a method: the declared smallest mutant fired for the
wrong reason (line count), which predicted and then exhibited the one genuine miss
(length-neutral in-place private-to-public rename in an __all__ module, 0/299 detected
in the exhaustive census), and the guard's real invariant was restated as 'the artifact
is a byte-exact function of the tree'. Result is reported as a proposed ledger amendment
(fired, demonstrated_by, scope, known_misses), not applied by the hunt.

Evidence: r_414eed/RESULTS.md 'Controls' (lines 15-26), tables (lines 34-68), 'What the
numbers say' items 2-4 (lines 79-101), 'What I chose, and why' (lines 112-127);
r_7ad39f/RESULTS.md 'Repository census and exhaustive mutation analysis' (lines 83-96);
r_cb5ffe/RESULTS.md 'The table' and combined five-escape tree (lines 21-44), 'Method
notes' (lines 105-124)
Prior art: unsearched (mutation testing is a standard field; the token-in-diff
discriminator and the ledger fields are the lab's)
Reused in: r_7ad39f (exhaustive census over 49 __all__ modules, historical git-log scan
showing zero incidence); r_cb5ffe (same protocol on tests/test_doors.py with worktrees);
proposed amendments to harness/departments/guard_ledger.py
Why it travels: The target here was repository tooling, but the protocol (null control,
undo re-check, three-level reading, combined-escape tree, blind-region table) is exactly
what a planted-fault audit of a mathematical detector needs, and r_cb5ffe's caching
caveat (worktrees share the editable install, so assert the module path before trusting
a number) is a real pitfall.

### Instantiate every enclosure lemma at a recorded box, and parametrise seam denominators as free reals

control | `hunts/r_6c7d6a/` and `hunts/r_938ab4/` | grade: kernel-checked (Lean 4, zero
sorrys, axioms [propext, Classical.choice, Quot.sound]; box0_in_table depends on no
axioms)

A Lean interval-enclosure lemma that compiles with zero sorrys can be vacuous:
O9Seam.r_comp_mem asked the denominator enclosure E to contain c*c + dOverY*dOverY while
the field denAbs2 actually encloses c*c + d*d with d = dOverY*y; the two agree only when
y^2 = 1 or s = 0, never on the table's boxes [28/5, 60] x [0, 1/2], so r_comp_mem and
rIv_mem were true, zero-sorry and unusable at every box. Control: for every enclosure
identification, also prove a *_box instance at a recorded row of the table (e.g.
Retention.box0_in_table by membership, point (23/4, 1/8) interior, hypotheses discharged
by norm_num), choosing a box that touches the hypothesis' edge (a mode-2 box whose
y-range starts at 0), and keep the audit aggregator's #print axioms list complete. Fix
pattern: state the seam lemma with the denominator's real as a free variable e
(r_comp_mem' : E.mem e -> ... (bOverY*c - a*dOverY)/e), same proof term, one fewer
coincidence; leave numerator components abstract so the layer does not couple to the
leaves. Companion finding (r_938ab4): imNumOverY encloses Im num / y only for y != 0 (at
y = 0 it encloses the removable limit, disequality proved at s = pi), so the y != 0
hypothesis is stated as a disequality rather than hedged.

Evidence: r_6c7d6a/RESULTS.md §3 (lines 69-126, the defect and the fix), §4 (lines
128-141), §5 (lines 169-183, zero sorrys, audit list); r_938ab4/RESULTS.md §2 (lines
49-83), §5 'Instantiability, checked' (lines 119-137)
Prior art: unsearched
Reused in: hunts/frontier_math/zeta23ext/Zeta23Ext/EForm3/O9NumShape.lean (27
declarations, imported by EForm3/Main.lean); O9Audit.lean; r_938ab4 explicitly reuses
r_6c7d6a's r_comp_mem' rather than r_comp_mem
Why it travels: 'A statement that compiles is not thereby a statement with content':
every enclosure seam in a Lean interval-arithmetic package should carry a discharged
instance at a recorded box, and quantities entering only squared need an external check.

### Planted-fault ladder for a polynomial certificate verifier

control | `hunts/r_6f0f63/` | grade: VERIFIED (float)

Five items run before any result is read: two controls (E8 and Leech certificates
rebuilt from contact structure, f vanishing to order 2 at each realised inner product
and order 1 at the interval endpoints, must give sup ≤ 0, min f_k > 0, values 240 and
196560); f_0 scaled by 1.01 must give sup = 0.01·f_0 exactly; f_4 negated must trip the
coefficient-sign test while the interval scan stays clean (a certificate can be
inadmissible with f ≤ 0 everywhere, so the scan alone is not the verifier); node set
starved to 14 points at degree 12 must report below 240 and fail the sign scan. All five
behaved as expected.

Evidence: RESULTS.md §0 'The planted-fault ladder, which fires first' (lines 17–32), §1;
probe.py planted_faults (line 213)
Prior art: unsearched
Reused in: none recorded
Why it travels: Template for any positivity/sign-condition certificate checker: separate
faults for each condition (P2 coefficient signs vs P3 interval sign) so the verifier's
blind spots are enumerated.
Index note: Planted-fault ladder, polynomial-certificate instance.

### Stopping rule for cutting-plane loops: test the true constraint residual, not objective stall; monotonicity separates solver stall from family ceiling

control | `hunts/r_828c8b/` | grade: measured (the monotonicity facts are provable; the
lesson is stated by the hunts)

Two related rules from the ceiling procedure. (a) A cut loop that stops when the
objective stalls can return values that fall when a constraint is added (R = 5 ->
0.37433, R = 10 -> 0.37246, R = 20 -> 0.37504 at N = 2000), which is impossible for the
real program; the stopping test must be the residual of the true quadratic constraint,
and any remaining non-monotone row is reported as unconverged, not as a measurement. (b)
Upsampling lemma: an m-piece step function upsamples to a feasible 2m-piece one with the
same value, so the m-piece optimum is non-increasing in m; if a published construction
(Haugland 0.380926) sits strictly below the solver's stalled value (0.381083768
identical at m = 32, 64, 128), the stall is the solver's, not the parameterisation's.
Stated lesson: a ceiling procedure that cannot tell 'the parameterisation ran out' from
'the search ran out' measures the search.

Evidence: hunts/r_828c8b/RESULTS.md, Section B 'The ceiling on the upper-bound side'
(lines 60-87) and loose thread 'The m-piece optimum is not where SLSQP stops';
hunts/overlap_lower/RESULTS.md Section E2 (lines 337-353) and E3
Prior art: unsearched
Reused in: hunts/overlap_lower/RESULTS.md Section E2 ('the second time in two days that
this family has produced that exact confusion')
Why it travels: Applies to every ceiling sweep over a nested family: use a provable
monotonicity as the falsifier of the search, and never stop an outer-approximation loop
on the objective.

### Control: a margin against a prediction drawn at the bound is not evidence; verify the obligation that spends the constant

control | `hunts/r_908de5` | grade: measured (exact rational arithmetic over 200 cell
obligations; ball and chained-rect enclosures)

If beta_pred was produced by point evaluation minus a sampling slack, the certificate
obligation normLower(enclosure) >= beta_pred sits at the line by construction in any
arithmetic, and its margin measures where the prediction was drawn, not the enclosure.
Remedy: set beta := normLower(B.inflate r) (rounded down to a multiple of 2^-40 so the
Lean literal stays small and true), which makes the grid inequality true by
construction, and move verification to the obligation that actually consumes beta, eps'
+ L h/2 <= beta, asserted at generation time so a site whose beta cannot support its
cell fails loudly. Measured: the worst cell obligation moves from 1.3647x to 1.3697x
(ball) or 1.3566x (chained rect), not the predicted >= 10x, because 98% of the
requirement is L h/2 (gap-limited, not beta-limited). Companion calibration: three
enclosure arithmetics coexist (rect non-chain, rect composite chains, ball); non-chain
is 2-6x too wide and fails all 24 obligations it carries; the remedy is contingent on
emitting composite chains.

Evidence: RESULTS.md 'What the defect was', lines 27-39; 'Before / after' tables, lines
41-69; 'The arithmetic the remedy needs', lines 71-106; 'What changed in the tree',
lines 108-128
Prior art: unsearched
Reused in: scripts/60_rung3_generate.py and scripts/65_rung3_full_validation.py
(generator assertion and validation verdict changed); docs/25 section 4.3 prediction
refuted
Why it travels: Any certificate pipeline that copies a numerically fitted constant into
a proof obligation has this failure mode; the fix (read the constant off the enclosure,
assert the consuming inequality at generation) is generic.

### Control: compare a sup only on the range the lemma asserts, and price depth-interval inflation before declaring a constant broken

control | `hunts/r_a7c12f` | grade: enclosure-carrying for the depth ladder on s in
[37.0135, 400]; measured for break depths and the asymptotic constant

A reported refutation '0.6636 > 637/1000 at depth 1' was a supremum over s in [8,400]
against a lemma (Wt_tail_le, hypothesis w = s^2 - 2 >= 1368, i.e. s >= 37.0135) that
carries no depth at all; the depth hypothesis lives in a different lemma (Qim_far_sq, y
<= 1/2). Procedure: (1) read the Lean statement to find which lemma carries the
hypothesis at issue; (2) restrict the scan to that lemma's range; (3) enclose there (Arb
96 bits, outward cells, enclosure cost 1.00005); (4) when treating depth as an interval,
note the normalisation divides by y_lo^2 so a cell of relative width w inflates by
(1+w)^2, and with a 0.82% margin cells must be under ~0.4% wide (~174 geometric cells
over [1/2,1]). Result: 637/1000 holds at depth 1 with +0.0052; what breaks first is
Qim_far_sq, asymptotically iff 4 sinh(y/2)^2 cos(1/sqrt2)^2/y^2 > 5/8, i.e. y >
0.972659.

Evidence: RESULTS.md sections 1-4, lines 21-135; 'Honest scope', lines 155-179
Prior art: unsearched
Reused in: harness review ledger claim k2-far-constant-depth1 (white-box attack outcome
recorded); input to R-B9552D's k >= 3 pass
Why it travels: Generic for auditing any 'constant X is violated' claim produced by a
scan against a Lean lemma; the depth-interval inflation arithmetic applies to every
ratio-normalised enclosure.

## Zero-free half-planes, L(1, chi) and class numbers

### Two-cutoff Littlewood bound for log L(1, chi) under a zero-free half-plane, with Hadamard positivity for the zero sum

lemma | `hunts/qrh_class_number` | grade: ordinary written derivation, unreviewed; every
constant evaluated in Arb (enclosure-carrying); conditional on the input half-plane

For a primitive odd real chi of conductor q whose zeros satisfy beta <= sigma0: subtract
the explicit formula for sum_{n<=t} Lambda(n) chi(n) n^-sigma log(t/n) at t = y and t = x;
the (L'/L)'(sigma) term cancels, and integrating sigma over [1, inf) gives log L(1, chi)
= sum Lambda chi w / (n log n) + E with the trapezoid weight w (1 up to y, linear in
log n down to 0 at x), so no L'/L(1, chi) term survives. Each zero term is charged
against Re xi'/xi(sigma) = sum_rho (sigma - beta)/|sigma - rho|^2 <= (1/2) log(q/pi) +
(1/2) psi((sigma+1)/2) - zeta'/zeta(sigma) + 2 zeta'/zeta(2 sigma), using that
t^(beta-sigma)/(sigma-beta) is increasing in beta, so only beta <= sigma0 is used and
no zero counting. With sigma0 = 7/8 it gives L(1, chi_D) >= 1/(10 log log |D|) for all
fundamental D < 0 except -3; the method's limit is (1 - sigma0) zeta(2) e^-gamma /
log log q, and at sigma0 = 1/2 it reproduces Lamzouri-Li-Soundararajan within 2% at
q = 10^100.

Evidence: RESULTS.md sections 2 and 4; `lbound.py`; `abscissae.json`
Prior art: searched; the mechanism is Littlewood's (GRH) and Friedlander-Iwaniec,
arXiv:1701.03771, Theorem 3 (half-plane Re s > 3/4, constants unspecified); no explicit
half-plane constant found
Reused in: none yet
Why it travels: any zero-free half-plane (a new sigma0, or a Hecke family over a fixed
field) turns into an explicit L(1, chi) lower bound by changing one parameter; the
positivity step needs no zero-counting input.

### Streamed reduced-form sieve for all class numbers h(D) <= H up to a bound X

computational | `hunts/qrh_class_number` | grade: exact integer computation, checked
against brute force, PARI, Watkins (h <= 100) and Holmin-Kurlberg (odd h <= 1500)

For fundamental D = -n the number of reduced forms with first coefficient a < sqrt(n)/2
is r(a) = #{b mod 2a : b^2 = D mod 4a}, multiplicative with r(p^k) = 1 + chi(p) off D.
Since r(a) is periodic in n, sum_a r(a) over any set of such a is a lower bound for h(D)
that can be added to a whole segment of n with SIMD-friendly periodic patterns; all a
below sqrt(n)/2 where the primes alone cannot exceed H, otherwise about 1.3 H primes.
Survivors get an exact count: r(a) by a multiplicative sieve, and the boundary range
n <= 4a^2 <= 4n/3 by Tonelli-Shanks, Hensel lifting and CRT. All 1.65 * 10^9 fundamental
discriminants below 5.4 * 10^9 for H = 1000 took ten minutes on one core, and all 3.77 *
10^9 below 1.24 * 10^10 for H = 1500 took 39 minutes, with no GRH. The filter can only
lose a field by over-counting, so the control that guards completeness recomputes every
streamed count without the periodic patterns (`CN_CHECK_STREAM=1`).

Evidence: RESULTS.md section 5; `cn.c`; `search_H1500.json`; `test_qrh_class_number.py`
Prior art: reduced-form counting is classical; unsearched as a batch filter
Reused in: none yet
Why it travels: any explicit bound |D| <= D(h) (from a zero-free region, GRH, or a
future theorem) becomes a complete class-number list by this sieve at cost about
X * H additions, without a conditional class-group algorithm.

## Primes in short intervals and explicit formulas

Explicit short-interval prime counts from a smoothed explicit formula, with the sums over
zeros bounded in closed form and the zeros split at a verified Riemann-hypothesis height.

- lemma: Height-split B-spline explicit formula with closed-form zero sums
  (`qrh_prime_powers`)

### Height-split B-spline explicit formula with closed-form zero sums

lemma | `hunts/qrh_prime_powers/` | grade: ordinary written proof, not reviewed outside
the hunt; every numerical inequality decided in Arb; conditional uses take a zero-free
half-plane as hypothesis

For the quadratic B-spline phi on [0, 1] (C^1, integral 1, max 9/4, ||phi'||_1 = 9/2,
TV(phi'') = 216) and w(t) = phi((t-x)/h), eta = h/x, a = 1 + 1/eta: the Mellin transform
has the closed form W(s) = -(h^2 s(s+1)(s+2))^-1 sum_i J_i (x + ih/3)^(s+2) with
J = (27, -81, 81, -27); |W(rho)| <= h x^(beta-1) g(|gamma|/a), g(u) = min(1, 9/(2u),
216/u^3); and sum Lambda(n) w(n) = h - sum_rho W(rho) - tau exactly, tau in [0,
h/(x(x^2-1))]. If every zero has beta <= theta and those below height H have beta = 1/2,
then sum_{x<p<x+h} log p >= (4h/9)(1 - E) - P with E = 2x^(-1/2) sum_{gamma<=H} g(gamma/a)
+ 2x^(theta-1) sum_{gamma>H} g(gamma/a) + 1/(x(x^2-1)) and an explicit prime-power term P.
The zero sums are bounded through explicit N(T) bounds by Stieltjes integration, and every
piece integrates in closed form once log log t is replaced by its tangent line at the
left end of each piece. Monotonicity in the interval parameter turns a finite Arb cover
plus a monomial tail lemma into an all-x statement.

Evidence: hunts/qrh_prime_powers/RESULTS.md sections 2 to 6 (Lemmas 2.1, 3.1, 5.1, 6.2,
6.4, Proposition 4.1); bound.py; test_qrh.py (normalisation against 1000 tabulated zeros
and a direct prime sum, closed forms against mpmath quadrature)
Prior art: cited: smoothed explicit formula with a verified-height split as in Buthe,
arXiv:1511.02032; qualitative half-plane-to-short-interval implication classical. The
B-spline envelope and the tangent-line closed forms are this hunt's choices; no explicit
consequence of a zero-free half-plane for primes between powers was found in the searches
listed in RESULTS.md section 11.
Reused in: RESULTS.md sections 7 to 9 (the same lemma drives the k-th power chain for
three abscissae, the short-interval theorem and, with a one-sided weight, the psi bound)
Why it travels: Any hypothesis of the form "zeros above height H have beta <= theta"
(a half-plane, a zero-density substitute, or a hypothetical zero) plugs into E directly,
so the threshold k = floor(1/(1-theta)) + 1 and its margins can be read off for any
theta in seconds.

## Seen and not admitted

Candidates the sweep surfaced that do not meet the bar yet: measured once, self-reviewed
only, not carried anywhere, or hunt-specific. Listed so the next sweep does not re-judge
them, and so a hunt that later reuses one knows it has just earned an entry above.

- Per-cell sharding of a branch-and-bound certificate with exact terminal-count
  reproduction (`hunts/bloch_ceiling/`, computational): not carried.
- Decision-trace reproduction: compare branch counters, not artifact digests
  (`hunts/field_audit/`, control): self-reviewed or measured only; not carried.
- Kernel-leaf mirror as the predictor of decide+kernel verdicts; margins are not
  commensurable with leaf-model error (`hunts/r_2926e4/`, control): self-reviewed or
  measured only; not carried.
- Obstruction: a box-instantiated 'no off-line zeros' property is not a function
  property and cannot be a gate input (`hunts/gate5_p6_a/`, obstruction): self-reviewed
  or measured only; not carried.
- Box-indexed properties are vacuous almost everywhere: the well-posed quantification
  collapses to the conclusion (`hunts/gate5_p6_b/`, obstruction): self-reviewed or
  measured only; not carried.
- Smooth-sum edge generation with box-conditional labelling for clique-search lower
  bounds (`hunts/support_60982bf6/`, computational): used only inside its hunt.
- Kink-contact lemma: a differentiable majorant cannot touch a positive-part target at
  an upward kink (`hunts/support_78c499b4/`, lemma): the hunt itself marks it unverified
  numerically.
- Theorem B: the p-adic signature model of S-summable sets has no ceiling
  (`hunts/support_baf4cde6/`, obstruction): self-reviewed or measured only; not carried.
- Cost-adaptive cutoff selection with ψ(N) cancelling, and convex-average cost identity
  (`hunts/paid_shortfall_scaling/`, computational): not carried.
- Post-landing blindness window of sign-scan zero counting, measured by grid-phase sweep
  (`hunts/flow_repair/`, control): self-reviewed or measured only; not carried.
- Jensen degree as de Bruijn-Newman heat: t_eff = |x0|/(8d) and the additive budget
  (`hunts/jensen_clock/`, calibration): self-reviewed or measured only; not carried.
- Trichotomy of coefficient-side blindness: Jensen degree, Jensen shift, Li index
  (`hunts/jensen_clock/`, obstruction): self-reviewed or measured only; not carried.
- Nested-contour monotonicity control and instrument-floor censoring for zero screens
  (`hunts/lambda_dh_exact/`, control): self-reviewed or measured only; not carried.
- Grid-phase lesion at close zero pairs, and the |Z| magnitude anti-heuristic
  (`hunts/lehmer_pair/`, control): not carried.
- Mixed-moment counting inequality with a narrow fourth moment (`hunts/cycle_moments/`,
  bound): self-reviewed or measured only; used only inside its hunt.
- Inertia lemma for the signed Fourier feature operator and the resulting count bound
  (`hunts/cycle_moments/`, lemma): self-reviewed or measured only; used only inside its
  hunt.
- Overlap-band counting bound and exact count in the {1,3} spectral class
  (`hunts/cycle_moments/`, bound): self-reviewed or measured only; used only inside its
  hunt.
- Fourier-support obstruction for four-cycle corrections (`hunts/cycle_moments/`,
  obstruction): self-reviewed or measured only; used only inside its hunt.
- Contour-tail obstruction: the unit-interval lower bound and incompatible order
  requirements in fixed-order explicit-formula bridges (`hunts/higher_xi/`,
  obstruction): self-reviewed or measured only; used only inside its hunt.
- Early-smoothed right-line Cauchy partial fraction selecting two Dirichlet ranges by
  Fourier support, with the height-freezing commutator (`hunts/higher_xi/`,
  construction): self-reviewed or measured only; used only inside its hunt.
- Rank-one monomer-dimer classification of the level-two Hadamard square (paths and even
  cycles only) (`hunts/higher_xi/`, lemma): self-reviewed or measured only; used only
  inside its hunt.
- Bernstein-coefficient positivity certificate for the corrected form factor on [0, 1/2]
  (`hunts/higher_xi/`, computational): used only inside its hunt.
- Normalisation pinning by recomputing unused printed values before comparing records
  (`hunts/r_2969b0/`, control): not carried.
- Polynomial-vs-exponential error obstruction for a sieve-free characteristic-function
  route to Erdős–Kac (`hunts/r_8c3b94/`, obstruction): self-reviewed or measured only;
  used only inside its hunt.
- Affine characterisation of structure-carrying bijections and the circulant/DFT
  obstruction (`hunts/chroma_hue/`, obstruction): Music-theory hunt; exhaustive but not
  carried anywhere in the mathematics.
- Cyclotomic norm as an integer invariant of subsets of Z_12 (`hunts/chroma_hue/`,
  identity): self-reviewed or measured only; not carried.
- Planted off-line zero sensitivity control for a pair-correlation energy
  (`hunts/prime_pair_error/`, control): self-reviewed or measured only; not carried.
- Local de-smoothing lemma with explicit distant-frequency budget
  (`hunts/prime_pair_error/`, lemma): self-reviewed or measured only; used only inside
  its hunt.
- Refused-cell descent: use the fail-closed verifier's rejected cells as oracle seeds;
  the LP value is the only hard side (`hunts/amtopa_ceiling/`, control): not carried.
- Symmetric-shift product rival W_a = zeta(s+a) zeta(s-a) for positivity-shaped
  mechanisms (`hunts/epp_herglotz/`, construction): self-reviewed or measured only; not
  carried.
- Boundary-identity obstruction: positivity mechanisms for Re(xi'/xi) >= 0 have zero
  margin on the line and the zeros as their first-order term (`hunts/epp_herglotz/`,
  obstruction): self-reviewed or measured only; not carried.
- Coefficient claims carry their truncation: gate #3 verdict flips between n <= 40 and n
  <= 200 (`hunts/epp_herglotz/`, calibration): self-reviewed or measured only; not
  carried.
- Crossover formula for the optimal pressure and the chord reading of the peak
  (`hunts/family_wall/`, identity): self-reviewed or measured only; used only inside its
  hunt.
- Independent adversarial audit of a barrier claim (brief-first, isolated, different
  model) (`hunts/family_wall/`, control): used only inside its hunt.
- Control: never optimise against a quadrature that is not exact for the search space
  (`hunts/rogue_frontier/window_opt`, control): self-reviewed or measured only; not
  carried.
- Derived-kernel validation by locating an unexplained ansatz, with fitted rivals as
  decoys (`hunts/wide_search/`, control): self-reviewed or measured only; not carried.
- Half-plane transfer for primes in progressions: a zero-free half-plane Re s > theta
  < 1 for all Dirichlet L-functions plus a single-modulus density exponent A(sigma)
  gives the Linnik exponent max(2, sup over 1/2 < sigma <= theta of A) and half of it
  for almost all classes, with the sup computed exactly at the breakpoints of the
  monotone density envelope and checked against a float grid (`hunts/qrh_linnik/`,
  lemma): self-reviewed only; the conditional implication is already CGL
  arXiv:2507.08296 Corollary 1.4 at h = x; not carried.
- Lorentzian domination of a smoothed explicit formula under a zero-free half-plane
  Re s > theta: with weight (n/x)^c log(x/n), W(s) = (s+c)^-2 and sigma0 = 2 theta + c,
  each zero obeys |x^rho W(rho)| <= x^theta K(x) Re 1/(sigma0 - rho), so the Hadamard
  identity prices the whole zero sum at x^theta (log q/2 + O(1)) with Arb-enclosed
  constants; gives explicit (log q)^(1/(1-theta)) witness bounds
  (`hunts/qrh_nonresidue/`, lemma): self-reviewed only; not carried.

