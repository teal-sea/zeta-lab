# Independent review: arithmetic bilinear cancellation candidate

Date: 2026-09-20. Reviewer: Muse worker (Grok unavailable; this package covers
both the mathematical challenge and the independent diagnostic).
Target: `hunts/prime_pair_error/ARITHMETIC_CANCELLATION_CANDIDATE.md`
at commit `b0f8daed26bfd310b173a18514dcd5b6a50d70bb` (HEAD).
Priots read: `SIGNED_MEAN_RENEWAL.md`, `FRONTIER_INDEPENDENT_REVIEW.md`,
`FRONTIER_2026_09_12.md` as needed; author checker
`arithmetic_cancellation_candidate_check.py` and
`results_arithmetic_cancellation_candidate.json` read but never imported.
Independent script: `hunts/prime_pair_error/independent_arithmetic_cancellation_check.py`.
Evidence: `hunts/prime_pair_error/independent_arithmetic_cancellation_evidence.json`.
No author file was modified. Numerical work: one process, ~40 s total, N <= 100000.

## Verdict: ATTEMPT_UNRESOLVED, with three refuted sub-claims

The candidate identity (2) is exact and confirmed independently. But no new
arithmetic cancellation was established: the load-bearing analytic claims
built on top of the identity are false as stated (three exact refutations
below), one growth claim is unproved (upper bound only), and the memo's own
diagnostic table disagrees with its own JSON at four cutoffs. The honest
remainder of the construction is a re-proof of the inherited scale relation
`R(N) = D_N + O(sqrt N)`, not an isolation of the hard part. This agrees with
the memo's self-disposition ("attempt unresolved", section 10) while
narrowing it: the remaining obstacle is larger than section 5 states, and two
terms, not one, are unbounded.

Claim-level verdicts (section references are to the candidate memo):

| Claim | Location | Verdict |
|---|---|---|
| Identity (2), derivation (8)-(16), integral formula (9)-(11) | sec 2 | CONFIRMED (defect <= 5e-12, dps=80, independent code) |
| Sawtooth trivial bound `|T_saw| <= psi(Y)/2` | sec 4 | CONFIRMED (elementary; rechecked) |
| Smooth term `S = N(log N - 2) + O(sqrt N)` | sec 4, line 172 | CONFIRMED |
| Eq (3), second equality `T_bil = -sum(R(N/k) - R(Y))` | sec 1, eq (3) | REFUTED (exact rational counterexamples, R1) |
| Boundary discrepancy `A(N) - log(N!) = O(sqrt N)`, hence `R_b = O(sqrt N)` "established" | sec 4, lines 170-175 | REFUTED (exact identity + Theta(N) main term, R2) |
| Spectral remainder `O(N^beta K^{-beta}) = O(N^{beta/2})`, "with margin" | sec 5, lines 211-217 | REFUTED (exact finite bracket stays O(1); k=1 mode dropped, R3) |
| `sum|R(N/k)| ~= N^{3/4}`, "exceeds by factor N^{1/4}" | sec 4 table, sec 5.1, sec 8 | UNPROVED (upper bound only; R4) |
| `R(N)` "eliminated", obstacle exactly (17) | sec 9.1, sec 5, eq (17) | MISSTATED (R5; corrected remainder below) |
| Small-case table (N = 81, 144, 200, 400) | sec 8 | STALE (disagrees with author's own JSON; R6) |
| `R_eta` diagnostic of section 7 | sec 7 | CONFIRMED, and it contradicts section 5 (see R3) |

## R1. Equation (3), second equality, is false at every tested N

`R(N/k) - R(Y) = [psi(N/k) - psi(Y)] - (N/k - Y)`, while the summand of
`T_bilinear` is `[psi(N/k) - psi(Y)] - (floor(N/k) - floor(Y))`. The two agree
only when `N/k - Y` is an integer for every k, which fails in general because
neither `N/k` nor `Y = N/K` need be integers. Exact rational residual
`E(N) = T_bil + sum_{k=2}^K (R(N/k) - R(Y)) = -sum_{k=2}^K ({N/k} - {Y})`:

| N | K | Y (exact) | E(N) (exact) |
|---|---|---|---|
| 27 (prime power, nonsquare) | 5 | 27/5 | +1/20 |
| 49 (prime power, square, integer Y) | 7 | 7 | +41/20 |
| 121 (prime power, square, integer Y) | 11 | 11 | nonzero (2.405159) |
| 200 (nonsquare, non-integer Y) | 14 | 100/7 | nonzero (-0.401820) |

`E(N) != 0` in exact `Fraction` arithmetic at all 16 tested cutoffs
(squares, nonsquares, prime powers). The first equality in (3) (the double
sum definition) is unaffected and is what the derivation actually uses. The
practical damage is bounded (`|E(N)| <= K`), so obstacle (17) and the
`T_bilinear` bound differ by at most `O(sqrt N)`; but every spectral sentence
in section 5 reasons about `sum R(N/k)` while claiming conclusions about
`T_bilinear`, and those now need the `E(N)` correction carried explicitly.

## R2. The boundary `O(sqrt N)` proof is invalid; the discrepancy is Theta(N)

Let `A(N) = sum_{d<=Y} Lambda(d) floor(N/d) + B_main(N,K)`. Splitting
`log(N!) = sum_{dk<=N} Lambda(d)` at `d <= Y` versus `d > Y`, the region
`{dk <= N, d > Y}` has `k < N/Y = K`, so with pair counting:

```
A(N) - log(N!) = T_bilinear(N,K) - (psi(N) - psi(Y))      (exact)
```

verified to 2.4e-10 in the evidence JSON. Since
`psi(N) - psi(Y) = (N - Y) + (R(N) - R(Y))` carries the main term `N - Y`,
the discrepancy is order N, not `O(sqrt N)`. Measured
`(A - log(N!))/N = -0.905, -0.908, -1.037, -0.991` at
`N = 400, 1000, 10000, 100000`: stable near -1, i.e. the memo's
"O(sqrt N) discrepancy" (lines 173-175) is off by a factor of order sqrt N,
and the complementary region `{k = 1, d > Y}` that lines 170-175 omit is
exactly where the missing `psi(N) - psi(Y)` lives.

Corollary. Substituting into (5) gives the exact corrected remainder:

```
R_boundary = R(N) - T_bilinear + E_det(N),
E_det(N) = S_smooth - log(N!) + N - psi(Y)/2               (exact, <= 2.5e-10)
```

with `E_det(N) = -R(Y)/2 + O(log N)` (Stirling plus `N·eps_K - Y/2`
cancellation; measured `|E_det|/sqrt N <= 0.41`, falling to 0.02 at 1e5).
Hence " `R_boundary = O(sqrt N)` established unconditionally" is false as a
standalone elementary bound: bounding `R_boundary` is equivalent to bounding
`R(N) - T_bilinear`, the hard quantity itself. Two terms of (2), not one,
are unbounded, and section 9.1's "`R(N)` eliminated" holds only
syntactically: semantically `R(N)` was moved into `R_boundary`.

## R3. The spectral remainder drops the k=1 mode; the true remainder is N^beta

For a pure mode `g(u) = u^rho`, linearity plus closed forms give the exact
finite bracket (no zeta-value assumed, stdlib `cmath` only):

```
D[g](N) = N^rho · B,   B = K^{1-rho}/(1-rho) - S2,   S2 = sum_{k=2}^K k^{-rho}.
```

Since `S2 = S1 - 1`, `B = (1 - zeta(rho)) - tail_K`. Section 5 keeps only
`tail_K = O(K^{-beta})` and reports `O(N^beta K^{-beta}) = O(N^{beta/2})`
(lines 211-214). The `-1`, i.e. the excluded k=1 term `R(N)` itself, i.e.
the full `N^rho/rho` mode, is missing. Measured `|B|` versus the claimed
decaying scale `K^{-beta}`:

| mode | N=400 | N=10000 | N=100000 | limit |
|---|---|---|---|---|
| `rho = 0.75+2i` | 0.54 vs 0.106 | 0.60 vs 0.032 | 0.58 vs 0.013 | `|1 - zeta(rho)|` = 0.59 |
| `rho = 1/2+14.1347i` (first zero) | 1.00 vs 0.224 | 1.03 vs 0.100 | 0.97 vs 0.056 | 1 |

`|B|` stays O(1) while the claimed scale decays; the ratio grows 4x to 44x.
What section 5 computed is the `L_K` remainder, not the `D_N` remainder:
`D_N = R(N) - L_K R(N)`, and at a zero `L_K` is small while `R(N)` keeps the
full `N^rho/rho`. The memo's own section 7 agrees with this correction
(`D_N[R_eta] ~= eta·N^beta`, large), so section 5 and section 7 contradict
each other and section 7 is the correct one. Consequences: on the critical
line the modal remainder is borderline `N^{1/2}/|rho|`, not `N^{1/4}` "with
margin"; off-critical it violates the target outright. The explicit-formula
lines 202-210 are additionally heuristic as written (pointwise convergence
and the prime-power jump conventions of `R` are never addressed).

## R4. The N^{3/4} "growth" and N^{1/4} "loss factor" are unproved

Section 5.1 derives an upper bound `sum|R(N/k)| << N^{3/4} log^2 N` under RH,
then the table, section 8, and the prose upgrade it to `~= N^{3/4}`,
"grows as", and "exceeds the true value by a factor of N^{1/4}". No lower
bound is given or cited; `R` changes sign and takes small values, so no such
bound follows from the argument. Measured `sum|R|/N^{3/4}`:
0.534, 0.414, 0.327, 0.304 at N = 400, 1000, 10000, 100000 (declining,
oscillating with the sign flips). This is compatible with the upper bound
and proves nothing about sharpness. Finite ratios are not asymptotics.

## R5. Strongest surviving decomposition (corrected remainder)

Adding the R2 identity to (2), `T_bilinear` cancels identically:

```
D_N = R(N) + T_sawtooth(N,K) + E_det(N)      (exact; verified, see evidence)
```

with `|T_saw| <= psi(Y)/2 << sqrt N` and `E_det = -R(Y)/2 + O(log N)`.
So the construction re-expresses the inherited `R(N) = D_N + O(sqrt N)`
through a different door; it isolates no new hard quantity and exhibits no
cancellation beyond the exact algebra. That is a true, checkable, neutral
statement, and it is all of what section 9 can claim.

## R6. The section 8 table is stale at N = 81, 144, 200, 400

My independent values reproduce the author's own
`results_arithmetic_cancellation_candidate.json` to 4 decimals everywhere
(e.g. N=400: `R = -2.1692, D = -1.7997, T_bil = 16.3908, R_b = -22.1910`),
while the memo's section 8 table prints different numbers
(e.g. `R = -4.4716, D = -6.6575, T_bil = -8.1368, R_b = -1.5026`).
The table matches the JSON only through N = 64; from N = 81 it looks copied
from an older run. Any "falsifiable diagnostic" built on those rows must use
the JSON values.

## Quantitative implication (corrected)

If the true bilinear bound `|T_bilinear| << N^{1/2+eps}` were established,
the section 6 chain would still need a bound on `R(N) - T_bilinear`
(equivalently `R_boundary`), per R2, so the current "one term left" becomes
at least "the hard quantity in two clothes". Nothing in this review closes
the bilinear route: bounding the signed sum is a legitimate unresolved
target. But as written the memo overstates by exactly the step that would
have to be proved.

## Exact repair obligations (no memo edit made here)

1. Eq (3): delete the second equality or append the exact `- E(N)` term with
   `E(N) = sum_{k=2}^K ({N/k} - {Y})`; propagate to obstacle (17), which must
   target `T_bilinear` (or carry `E(N)`).
2. Section 4 boundary: replace lines 170-175 with the R2 exact identity;
   downgrade `R_boundary` in the table from "established unconditionally" to
   unresolved (equivalent to the hard estimate via the corollary); qualify
   section 9.1 as syntactic elimination only.
3. Section 5 spectral: redo with the k=1 mode retained (`B = 1 - zeta(rho) -
   tail`); retract "N^{1/4} with margin" (critical-line remainder is
   borderline `N^{1/2}`); reconcile with section 7; mark the explicit-formula
   manipulation heuristic with its convergence/jump caveats.
4. Table/`~= N^{3/4}`/`N^{1/4}` factor language: upper bound only, everywhere
   it appears (table, 5.1, 8).
5. Section 8 table: regenerate from the JSON for N >= 81 (or delete the rows
   and point at the JSON).
6. Section 6 implication: re-derive from the corrected remainder (R5),
   stating both missing estimates.

## Method, commands, and reproducibility

```bash
.venv/bin/python hunts/prime_pair_error/independent_arithmetic_cancellation_check.py
```

One process, ~40 s (estimate given upfront: <60 s sieve + O(K) prefix-sum
loops, N <= 100000; no builds, no network, no spend). Lambda from a fresh
pure-stdlib sieve; floors/endpoints exact (`Fraction`); transcendentals
(`log`, `gamma`, `zeta`) evaluated in mpmath at dps=80, a different
precision and code path from the author's dps=40 checker; spectral bracket
in stdlib `cmath`. Nothing from the author checker, `zeta/`, or any hunt
module is imported. Max defects: identity (2) 5.3e-12 (float-`psi`
accumulation dominates at 1e5; 4.8e-16 at N=400), integral formula 6e-17,
both exact remainder identities <= 2.5e-10.

External inputs used: the inherited integral value `-(1+gamma)` and the
unconditional PNT envelope from `SIGNED_MEAN_RENEWAL.md` (accepted as
inherited, not re-proved); `gamma_1 = 14.134725141734693` as the classical
first-zero ordinate for the critical-line spectral row (repository ground
truth; no zero was searched or assumed beyond this published value).
Inaccessible sources: none needed; no primary-source theorem beyond the
inherited renewal identities is invoked. The NIST Euler-Maclaurin check
cited from `FRONTIER_INDEPENDENT_REVIEW.md` was not re-opened.

## Proof versus numerics versus novelty

Proof: the refutations R1-R3 are exact identities plus measured scales, not
finite counterexamples to big-O claims alone (R1 is purely exact; R2 pairs
the exact identity with a Theta(N) main term measured at ratio ~= -1 across
three decades; R3 pairs the exact bracket with convergence to `|1-zeta|`,
including 1 at a true zero). Numerics: all scale statements (`(A-log!)/N`,
`|B|`, envelope ratios) are non-enclosing diagnostics supporting, not
replacing, the identities. Novelty: none claimed; the confirmed identity is
the author's, and the corrected remainder (R5) is a direct algebraic
consequence of it. The `E(N)` fraction formula and the two exact remainder
identities are original to this review to the best of my knowledge, recorded
here as derivations, not as results about the primes.

## Author-adjudication note (2026-09-20)

Target: review findings R1-R6 above. Provenance preserved: the review text and
evidence above remain unchanged; this section records the author's mathematical
audit of the review.

1. **R1 (Rational residual in eq 3): CONFIRMED, WITH SIGN CORRECTION.**
   The second equality of equation (3) is false as written: `R(N/k) - R(Y)` uses
   continuous linear slopes `N/k - Y`, while `T_bilinear` uses integer floor
   differences `floor(N/k) - floor(Y)`. The exact difference is
   `E_frac(N) = sum_{k=2}^K ({N/k} - {Y})`.
   Reviewer sign audit: line 49 wrote `E(N) = -sum({N/k} - {Y})`, but the review
   table at N=49 recorded `+41/20`, matching `sum_{k=2}^7 {49/k} = 41/20`.
   The correct identity is `T_bilinear = -sum_{k=2}^K (R(N/k) - R(Y)) + E_frac(N)`.
   The residual is bounded by `|E_frac(N)| <= K <= sqrt(N)`.

2. **R2 (Boundary discrepancy): CONFIRMED IN DISCREPANCY, QUALIFIED IN BOUNDARY.**
   The author memo's lines 173-175 claimed `A(N) - log(N!) = O(sqrt N)`.
   This claim was invalid: `A(N) - log(N!) = T_bilinear - (psi(N) - psi(Y)) = -N + o(N)`
   is indeed Theta(N), as the complementary region `{k=1, d > Y}` carries the
   entire main term `N - Y`.
   However, the reviewer's inference that `R_boundary` itself is Theta(N) is
   unjustified: `R_boundary = R(N) - T_bilinear + E_det(N)`, with
   `E_det(N) = -R(Y)/2 + O(log N) = O(sqrt N)`.
   A missing proof of `R_boundary = O(sqrt N)` is not a proof that `R_boundary`
   is Theta(N). The status of `R_boundary` is unresolved, coupled directly to
   `R(N) - T_bilinear`.

3. **R3 (Spectral remainder): CONFIRMED, WITH OSCILLATION QUALIFIER.**
   Section 5 dropped the k=1 mode. Retaining it gives `B = 1 - zeta(rho) - tail_K`.
   At any zeta zero, `B -> 1`, so `D_N[u^rho] ~ N^rho`. On the critical line,
   this is borderline `N^{1/2}`, not `N^{1/4}`. Off-critical, it is `N^beta`.
   This reconciles section 5 with section 7.
   Qualification: for non-real zeros `rho = beta + i gamma`, `N^rho = N^beta e^{i gamma log N}`
   oscillates. The growth is an envelope bound `|N^rho| = N^beta`, not monotonic
   asymptotics at all integers.

4. **R4 (Growth vs upper bound): CONFIRMED.**
   The bound `sum_{k=2}^K |R(N/k)| << N^{3/4} log^2 N` under RH is an upper
   bound only. The memo's text claiming proved growth `~= N^{3/4}` or an established
   loss factor of `N^{1/4}` is retracted.

5. **R5 and R6 (Surviving representation and stale table): CONFIRMED.**
   The exact identity `D_N = R(N) + T_sawtooth + E_det` is verified.
   The section 8 table rows for N in [81, 144, 200, 400] were stale formatting
   copies and are corrected to match the author's verified JSON records.

## Correction and acceptance record (2026-09-20, repair dispatch)

Owner of this section: the repair worker (second dispatch). Earlier sections
above are preserved as written, including the adjudication note; where they
are wrong they are corrected here, not silently edited.

1. **E-sign: my R1 had a text/table inconsistency, now fixed on both sides.**
   R1 line 49 stated `E(N) = T_bil + sum(R diffs) = -sum({N/k} - {Y})` while
   the R1 table printed the script's `e_frac = +sum({N/k} - {Y})`
   (e.g. `+41/20` at N = 49). The exact relation, asserted both sides
   independently (mpmath dps-80 transcendentals versus exact `Fraction`
   arithmetic, flipped sign discriminated) in
   `results_factorization_diagnostic.json` at 13 cutoffs including N = 49, is
   `T_bil + sum_{k=2}^K (R(N/k) - R(Y)) = -sum_{k=2}^K ({N/k} - {Y})`
   (`-41/20` at N = 49). The candidate memo (3$'$) carried the same sign the
   other way (`+ E_frac`) and is corrected to minus in this repair.
2. **Misattribution corrected: this review never asserted `R_boundary = Theta(N)`.**
   The record: R2 asserted the *discrepancy* `A(N) - log(N!)` is Theta(N)
   (exact identity plus main term `N - Y`, measured ratio near `-1` across
   three decades), and that bounding `R_boundary` is *equivalent* to bounding
   `R(N) - T_bilinear`. The sentence "Two terms of (2), not one, are
   unbounded" meant "not elementarily bounded", i.e. unresolved, and is
   hereby reworded to exactly that. No proof that `R_boundary` is large was
   given or is claimed; its status is unresolved, coupled to
   `R(N) - T_bilinear`. The adjudication's "reviewer's inference" sentence is
   corrected accordingly.
3. **Acceptance of the repaired package (base `b823a64`, repair commit below).**
   Proved exact identities (each re-derived and machine-checked): candidate
   (2) with (8)-(16); sign-corrected (3$'$); `A - log(N!) = T_bil - (psi(N) -
   psi(Y))`; `R_b = R(N) - T_bil + E_det` with `E_det = -R(Y)/2 + O(log N)`;
   collapsed `D_N = R(N) + T_saw + E_det`; spectral `B = 1 - zeta(rho) -
   tail_K`; hyperbola absence-of-remainder lemma and the
   `D_N = S + Sigma_1 + Sigma_2` partition; guarded Mertens-cell identity.
   Genuine baselines now on record: `|T_saw| <= psi(Y)/2 << sqrt(N)`;
   `E_det = O(sqrt N)`; `T_bil`, `R_b << N log N exp(-c sqrt(log N))`
   unconditional; `Sigma_2 << N log^2 N` unconditional (logs retained);
   RH upper envelope `sum|R| << N^{3/4} log^2 N`.
   Remaining estimate: the joint `|D_N| << N^{1/2+eps}`, equivalently the
   signed bilinear/frac-piece cancellation; the fractional-weight piece
   `sum mu(a){N/(ab)}` is its analytic core.
   Any new cancellation obtained: none. The surviving content is a correct
   reformulation (candidate identity plus exact factorization) preserved as
   attempt unresolved; the factorization method as a whole is not closed.
   Commands run (one process, ~2.5 min total numerical compute, N <= 100000):
   `.venv/bin/python hunts/prime_pair_error/independent_arithmetic_cancellation_check.py`
   (prior dispatch, ~40 s) and
   `.venv/bin/python hunts/prime_pair_error/factorization_diagnostic.py`
   (~110 s: E-sign discrimination at 13 N; Y sweep 4..100000 with 314
   documented `Y < sqrt(N)+1` violations; `2(U+1) - Y` minimum 0.5;
   pair-level `Kab - N` minimum 3 over 30.8M pairs; kernel/partition defects;
   section-6 table validated to < 5e-5; 3 empty-guard counterexamples).
   No full slow suite or Lean run was needed (no core files touched).

