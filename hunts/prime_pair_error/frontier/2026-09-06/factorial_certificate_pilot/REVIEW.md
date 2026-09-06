# Review: the factorial-certificate pilot

Reviewed 2026-09-06, in a fresh worktree, by a session that did not write the pilot.

**Label.** This is a pilot. It is not a new prime-counting record, not an improvement to
the total CHHL error E(N), and not an RH result; nothing here bears on RH (`docs/08`).
Its smallest example is Chebyshev's 1852 construction, and the pilot says so itself.
This review does not reopen the completed A/B referee work in the parent hunt.

**Verdict in one line.** The 87 reported certificates reproduce exactly, and the general
argument in `PILOT.md` sections 1 to 3 is correct as written: every step was re-derived
by hand below and every finite consequence that can be computed was recomputed with
independent code. No mathematical error was found. The two non-mathematical findings are
listed in section 6.

## 1. What is preserved, and how

| item | where | check |
|---|---|---|
| original ZIP, 10,876 bytes | `archive/factorial_certificate_pilot.zip` | SHA-256 `215f0ab2de4957e5d98d42106f2a525286b9fa9e89fa5f4db167ceb82ed7ad0c`, the value the attachment was delivered with |
| hash sidecar | `archive/SHA256SUMS` | same digest |
| the four members the ZIP's own `SHA256SUMS.json` lists | inside the ZIP | each present with the recorded hash and byte count |
| extracted copies | this directory | `PILOT.md`, `requirements.txt`, `SHA256SUMS.json` byte-identical to the members; `pilot.py` and `results.json` differ from their members by one token, see below |
| the test | `tests/test_factorial_pilot_archive.py` | fails if the ZIP is missing, zero bytes, or hashed differently; if any member is missing or altered; if an extracted copy differs from its member by anything other than the documented token; if any of the 87 records stops re-verifying |

**The one edit, stated plainly.** `pilot.py` (two places) and `results.json` (one place)
contain the word this repository reserves for `zeta/rigor.py`, both times inside a
sentence disclaiming it. `AGENTS.md` bans that word everywhere under `hunts/`, disclaimers
included, and `tests/test_hunt_probe_discipline.py` reads the bytes. The extracted copies
therefore carry the same one-token substitution (reserved word to `established`) that
commit `befceb5` applied to the four frontier checker files in this directory on the same
day. The originals are the ZIP members and are not edited; the test reconstructs each
extracted copy from its member by exactly that substitution and demands equality, so the
edit is the only difference there can be. This is a deviation from "extracted contents
unchanged", chosen over relaxing the lexical rule, which is not this session's to relax.
Reverting it is one `git mv` from the ZIP plus an exemption in the lexical test.

Nothing else in the original files was touched. All new material is under `review/` or in
this file.

## 2. Reproduction of the 87 certificates

Command, from a copy of `pilot.py` in a scratch directory, output to a temporary file that
is not committed:

    OPENBLAS_NUM_THREADS=1 .venv/bin/python pilot.py --output rerun_results.json

Environment: Python 3.14.0, numpy 2.5.2, scipy 1.18.0 (HiGHS). The original record was
produced under Python 3.13.5. Elapsed 3.10 s against the recorded 3.13 s.

Result, comparing the rerun to the preserved `results.json` field by field:

- 87 of 87 cases, in the same (L, M) order, L in {30, 210, 2310} and M from 2 to 30.
- 87 of 87 coefficient vectors identical as exact rationals.
- 87 of 87 leading constants identical to within 1e-12 (the recorded floats).
- 87 of 87 exact-feasibility records identical (balance, 30/210/2310 residues checked,
  integer scale, minimum scaled margin).
- The three selected seeds identical, including all 12 finite staircase checks (exact
  fields) and 25 prime-exponent identities each.
- The only differences anywhere: the float `log_factorial_upper_bound_float` in 7 of the
  12 staircase rows differs in the last one or two decimal digits (for example
  29.169645742125766 against 29.169645742125756). That field is `math.lgamma` summed in
  double precision and the two interpreters sit on different libm builds. No exact field
  moved.

So the reported certificates reproduce.

## 3. Independent check: `review/check_pilot.py`, output `review/check_pilot.json`

Written for this review, shares no code with `pilot.py`, reads `results.json` as data.
Runs in about 9 s. Every assertion passed. What it establishes is finite and exact; the
general argument is section 4.

1. **All 87 seeds re-verify** with `Fraction` arithmetic: balance `sum a_j/j = 0`,
   `g(r) >= 0` on `r = 0..L-1`, `g(r) >= 1` on `r = 1..M-1`, and periodicity `g(r+L) = g(r)`
   and `g(r + 1/3) = g(r)` at sample points as computed facts. Minimum slack is 0 in both
   constraint classes for some seeds, which is what an LP vertex looks like.
2. **The leading constant** `C = kappa/(1 - 1/M)` at 40 digits agrees with every recorded
   float to at most 2.4e-16. Range over the 87: 1.0698544525734643 (L=2310, M=15) to
   1.3862943611198906 = 2 log 2 (L=30, M=2, the seed `a_1 = 1, a_2 = -2`). The recorded
   `coefficient_l1` (A) matches the exact sum for every seed.
3. **The pilot's lower bound** `C - 1 >= [1/(L+1) - 1/(L+2)]/(1 - 1/M)` holds for all 87,
   and `kappa >= 1 - 1/M` holds for all 87.
4. **The integral representation** `kappa = int_1^inf g(t)/t^2 dt`: the truncated integral
   has the closed form `sum_j a_j [H_{floor(R/j)}/j - floor(R/j)/R]`; at R = 10^7 it is
   within 5.0e-8, 1.0e-7 and 1.5e-7 of kappa for the three selected seeds, which is the
   O(A/R) the derivation predicts.
5. **The factorial inequality** `|log(floor(y)!) - (y log y - y)| <= 1 + log^+ y` holds at
   127,074 points (half-integers to 10^4, multiples of sqrt 2 to 10^4, every integer to
   10^5); the ratio of left side to right side reaches 1.0, so the inequality is tight
   (at y = 1 both sides are 1) and cannot be sharpened in this form.
6. **The certificate against an independent psi.** psi(N) from a smallest-prime-factor
   sieve, summed as log p over prime powers at 30 digits:
   psi(10^3) = 996.680912247175, psi(10^4) = 10013.3966932631,
   psi(10^5) = 100051.564025658, psi(10^6) = 999586.597495633. B_N from log-factorials at
   30 digits. For all 87 seeds at N = 10^3, 10^4, 10^5 and the three selected seeds at
   N = 10^6 (264 rows): `psi(N) <= B_N <= C N + A (K+1)(1 + log N)` holds, and so does the
   two-sided budget with the `(1 - M^{-K-1})` factor and the `-log(M) K(K+1)/2` term.
   At N = 10^6:

   | L | M | K | B_N / N | C | B_N - C N | budget A(K+1)(1+log N) |
   |---|---|---|---|---|---|---|
   | 30 | 6 | 7 | 1.10552811633 | 1.10555042752 | -22.3 | 592.6 |
   | 210 | 6 | 7 | 1.07392641283 | 1.07396536007 | -38.9 | 1185.2 |
   | 2310 | 15 | 5 | 1.06982569230 | 1.06985445257 | -28.8 | 1333.4 |

   Over all 264 rows the residual `|B_N - C N|` never exceeds 10.2% of the budget (worst:
   L=30, M=22, N=10^4). The budget is valid and loose by a factor of ten or more at these N.
7. **The factorial identity in integers only**, three selected seeds, N = 10^4: for each of
   the 1229 primes p <= N, the exponent of p in `prod_{k,j} floor(N/(j M^k))!^{a_j}` by
   Legendre's formula equals `sum_{p^i <= N} W_N(N/p^i)` exactly, and every `W_N(N/p^i)`
   is >= 1 (minimum exactly 1 for all three seeds). This is `B_N = sum_d Lambda(d) W_N(N/d)`
   with `W_N >= 1` on the support of Lambda, checked without a single logarithm.

## 4. The general argument, step by step

These are the pilot's claims for every N, not for the tested ones. Each was re-derived.

**4.1 Do the finite period constraints establish global positivity? Yes.**
`g(t) = sum_{j|L} a_j floor(t/j)`. For j | L, `floor((t+L)/j) = floor(t/j) + L/j` for every
real t, so `g(t+L) = g(t) + L sum_j a_j/j = g(t)`: the balance condition is exactly
periodicity. Each `floor(t/j)` changes value only when t crosses a multiple of j, an
integer, so g is constant on every `[n, n+1)` and `g(t) = g(floor(t) mod L)` for all real
t >= 0. Hence `g(r) >= 0` on the L residues gives `g >= 0` on `[0, inf)`, and
`g(r) >= 1` on `r = 1..M-1` gives `g >= 1` on `[1, M)` because those residues are below L
(the pilot requires `M <= L`, and `exact_verify` enforces `2 <= M <= L`). `g = 0` on
`[0, 1)`. Correct.

**4.2 Does rescaling establish W_N(t) >= 1 throughout [1, N]? Yes.**
`W_N(t) = sum_{k=0}^K g(t/M^k)` with `K = floor(log_M N)`, computed by integer powers
(`M^K <= N < M^{K+1}`, and `lifted_coefficients` does exactly this). For real
`1 <= t <= N` put `k = floor(log_M t)`; then `0 <= k <= K` because `1 <= t <= N`, and
`t/M^k` lies in `[1, M)`, so that term is >= 1 by 4.1. Every other term is `g` of a
nonnegative real, so >= 0. Correct, for every real t in `[1, N]`, both endpoints
included (t = 1 uses k = 0 and g(1) >= 1; t = N uses k = K).

**4.3 Does the factorial identity give B_N >= psi(N)? Yes.**
`log(n!) = sum_{m<=n} log m = sum_{m<=n} sum_{d|m} Lambda(d) = sum_{d<=n} Lambda(d) floor(n/d)`.
With `n = floor(N/(j M^k))` and the nested-floor identity `floor(floor(x)/d) = floor(x/d)`
for integer d >= 1, `log(floor(N/(jM^k))!) = sum_d Lambda(d) floor(N/(d j M^k))`.
Summing with weights a_j over j and k and exchanging the finite sums,
`B_N = sum_{d<=N} Lambda(d) sum_k sum_j a_j floor((N/d)/(j M^k)) = sum_{d<=N} Lambda(d) W_N(N/d)`
(terms with d > N vanish since every floor is 0). For `1 <= d <= N`, `N/d` is in `[1, N]`,
so `W_N(N/d) >= 1` by 4.2, and `Lambda(d) >= 0`; therefore `B_N >= sum_{d<=N} Lambda(d) = psi(N)`.
No prime data enters the choice of a_j, and no RH assumption enters anywhere. Correct.
Section 3 item 7 is this identity checked in integers.

**4.4 Is the error budget correct? Yes, every piece.**

- *The factorial inequality.* For y >= 1 with m = floor(y) >= 1, integral comparison of
  the increasing function log t against the sums gives `m log m - m + 1 <= log(m!)` (compare
  `sum_{i=2}^m log i` with `int_1^m`) and `log(m!) <= m log m - m + 1 + log m` (compare
  `sum_{i=1}^{m-1} log i` with `int_1^m`). With `f(t) = t log t - t`, `f' = log t >= 0` on
  `[1, inf)`, so `0 <= f(y) - f(m) = int_m^y log t dt <= (y - m) log y <= log y`. Subtracting,
  `log(m!) - f(y)` lies in `[1 - log y, 1 + log m]`, and both ends are bounded in absolute
  value by `1 + log y`. For `0 <= y < 1`, `log(0!) = 0` and `f(y)` decreases from 0 to -1, so
  the difference is at most 1 = `1 + log^+ y`. Correct, and tight at y = 1.
- *Cancellation of the leading terms.* With `y_j = x/j`,
  `sum_j a_j (y_j log y_j - y_j) = x log x sum a_j/j - x sum a_j log j/j - x sum a_j/j = kappa x`
  by the balance condition, with `kappa = -sum_j a_j log(j)/j`. Correct.
- *Coefficient size.* `|sum_j a_j [log(floor(x/j)!) - (y_j log y_j - y_j)]| <= sum_j |a_j| (1 + log^+(x/j)) <= A (1 + log^+ x)`,
  since `log^+(x/j) <= log^+ x` for j >= 1. Correct: the per-level constant is the seed's
  l1 norm A, and combining coincident lifted indices `j M^k = j' M^{k'}` can only lower it.
- *Number of rescaling levels.* K + 1 levels, `K = floor(log_M N)`. For `0 <= k <= K`,
  `N/M^k >= N/M^K >= 1`, so `log^+(N/M^k) = log N - k log M` exactly, and
  `sum_{k=0}^K A (1 + log N - k log M) = A[(K+1)(1 + log N) - log(M) K(K+1)/2]`. Correct.
- *Main term.* `kappa N sum_{k=0}^K M^{-k} = kappa N (1 - M^{-K-1})/(1 - 1/M)`. Correct.
  Since `kappa >= 1 - 1/M > 0` (next item) the factor `(1 - M^{-K-1}) < 1` may be dropped for
  an upper bound, and the `-log(M) K(K+1)/2` term may be dropped from the error, which gives
  the stated `psi(N) <= B_N <= C N + A (K+1)(1 + log N)` with `C = kappa/(1 - 1/M)`. For the
  lower side, `kappa N M^{-K-1} < kappa` because `M^{K+1} > N`, so `B_N = C N + O_{a,M}(log^2 N)`
  two-sided. Correct. Section 3 item 6 checks both sides numerically at 264 rows.
- *Floors and endpoints.* The only floor that matters is `floor(N/(j M^k))`, which is what
  `pilot.py` evaluates (`N // j` with the lifted index `j M^k`). Endpoints are covered in 4.2.
  N = 1 gives K = 0 and `B_1 = 0 = psi(1)`, so the inequality holds from N = 1.
- *The integral representation of kappa.* `int_1^R floor(t/j)/t^2 dt = H_{floor(R/j)}/j - floor(R/j)/R`;
  summing with a_j, the `(log R + gamma) sum a_j/j` part vanishes by balance,
  `-sum a_j log j/j = kappa` remains, and `sum_j a_j floor(R/j)/R = g(R)/R -> 0` because g is
  bounded (periodic). So `int_1^inf g(t)/t^2 dt = kappa`. Correct; item 4 of section 3 sees
  the O(1/R) tail. Since `g >= 1` on `[1, M)` and `g >= 0` elsewhere, `kappa >= int_1^M dt/t^2 = 1 - 1/M`.
- *The obstruction `C > 1` for a fixed seed.* `g(t) = g(1) >= 1` on `[L+1, L+2)`, disjoint from
  `[1, M)` because `M <= L`, so `kappa >= (1 - 1/M) + 1/(L+1) - 1/(L+2)` and the stated bound
  follows. Correct and, by the same argument iterated over every period, weak: `g >= 1` on
  every `[mL+1, mL+M)`, so `kappa - (1 - 1/M) >= sum_{m>=1} [1/(mL+1) - 1/(mL+M)]`. Neither
  bound is close to the truth (for L=30, M=6 the stated bound gives `C - 1 >= 0.0012` where
  `C - 1 = 0.1056`); both are valid, and the pilot claims only positivity.

**4.5 What the construction is.** The seed `a_1 = 1, a_2 = a_3 = a_5 = -1, a_30 = 1` is
Chebyshev's step function, kappa = 0.92129 is Chebyshev's constant A, and summing the
rescalings over powers of M = 6 to get the upper bound `6A/5 = 1.10555` is Chebyshev's
own argument for the upper bound, not just his seed. The L = 210 and L = 2310 seeds are
LP-selected members of the same family, with the same proof. The pilot states this
correctly ("positive control, not a discovery").

**4.6 The pilot's section 5, two reviewer remarks.** Both are outside what the pilot
claims and are recorded as pointers, not findings.

- The pilot says that to reach the RH scale one would need seeds varying with N and the
  whole right-hand side `(C-1)N + A(K+1)(1 + log N)` to be `O(N^{1/2+eps})`. That condition
  is sufficient, and it is not missing a second half: a one-sided bound
  `psi(x) - x <= O(x^{theta})` already forces every zero to have real part <= theta, by
  Landau's theorem on Mellin integrals with nonnegative integrand (Montgomery and Vaughan,
  Chapter 15, to the reviewer's recollection; not re-derived here).
- Prior art on the varying-seed question exists: Diamond and Erdős, "On sharp elementary
  prime number estimates", L'Enseignement Math. 26 (1980), 313 to 321. Existence of the
  paper was confirmed in this session by a web search; what it proves is stated from the
  reviewer's recollection only, namely that Chebyshev-type constants can be made
  arbitrarily close to 1, by an argument that itself uses the prime number theorem. That
  recollection was not verified against the paper and should be before anyone cites it.

## 5. Grade

- The 87 certificates and the finite checks in section 3: **exact finite checks**, rational
  arithmetic, no floating tolerance anywhere the pilot or this review claims exactness. The
  constants C and the psi comparisons are 30- to 40-digit floating values, so those rows are
  *measured*; nothing depends on their last digits.
- The general argument (section 4): an elementary classical proof, reviewed by hand, prose
  grade. Not kernel-checked; nobody has asked for that and the result is Chebyshev's.
- Novelty: none claimed by the pilot, none found by this review. Optimality of the LP
  solutions: not claimed by the pilot, not checked here.

## 6. Precise findings

No mathematical error. Two findings, neither about the mathematics:

1. `pilot.py` and `results.json` use the repository's reserved word in disclaimers, so their
   extracted copies could not be committed byte-identical under `hunts/`. Handled as in
   section 1; the ZIP members are untouched and the test pins the substitution.
2. `PILOT.md` section 4 reports C for the rational reconstruction
   (`Fraction(float).limit_denominator(10^6)`) rather than for the float LP optimum, and the
   two are only guaranteed to agree when the reconstruction succeeds, which `exact_verify`
   enforces by raising. All 87 reconstructions succeeded in the original and in the rerun;
   the recorded C values are the constants of the exact rational seeds, which is the right
   thing to report. Recorded here so a future scipy or HiGHS change that returns a different
   vertex in a degenerate case is read as a solver difference and not as a defect.

## 7. What ran and what did not

Ran: the rerun of `pilot.py` (section 2); `review/check_pilot.py` (section 3);
`tests/test_factorial_pilot_archive.py`, `tests/test_frontier_archive.py`,
`tests/test_hunt_probe_discipline.py`, `tests/test_docs_numbering.py`, `tests/test_doors.py`,
`tests/test_repo_hygiene.py`; `scripts/make_context.py --check`.

Did not run: any check of LP optimality (the pilot disclaims it); any Lean build; the full
slow tier; any literature search beyond confirming that the Diamond and Erdős paper
exists; any reading of Bober or Fiori, Kadiri and Swidinsky, which the pilot cites and
this review takes as cited.
