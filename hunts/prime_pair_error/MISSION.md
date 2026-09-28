# prime_pair_error: the Chou, Haag, Huryn, Ledoan error, reproduced and taken apart by separation

Chou, Haag, Huryn and Ledoan (arXiv:2308.14888, J. Number Theory 2025) define, for the
von Mangoldt pair count psi_2(N, k) = sum_{n, n' <= N, n' - n = k} Lambda(n) Lambda(n')
and the Hardy-Littlewood prediction S(k)(N - |k|),

    E(N) = sum_{1 <= |k| <= N} (psi_2(N, k) - S(k)(N - |k|))^2,

conjecture E(N) ~ c_3 N^2 (log N)^2, and publish E(N)/(N^2 log^2 N) at eleven values of
N up to 10^5 (their Table 1). This hunt reproduces that table, extends it to 10^7, and
asks which separations k carry the error: by the size of k, by the prime factors of k,
and against three candidate profiles that a first-order heuristic predicts. The
prediction S(k)(N - k) is held fixed throughout; nothing is refit.

Everything in the first pass runs from one script, `probe.py`, in about half a minute
on a laptop; the numbers it writes are `results.json`, and `RESULTS.md` reads them.
The second pass (2026-09-06) is `residue.py`: it derives the first pass's profile as the
modulus-1 member of a residue-class decomposition, writes down the modulus-3 and
modulus-30 members with every coefficient fixed by the derivation, and evaluates all
three at cutoffs the first pass never used; it writes `results_residue.json`, and
`tests/test_prime_pair_residue.py` pins its identities and its numbers. The third pass
(2026-09-06) is `wronskian.py`: it takes the character-weighted sum of RESULTS.md
Section 12 apart into a Wronskian of the two prime-counting remainders plus an explicit
term of order N, checks the identities on arbitrary weights, and RESULTS.md Part 3 proves
what can be proved about it (a bound in terms of the zeros of zeta and L(s, chi_3),
and an unconditional lower bound on E(N)); it writes `results_wronskian.json` and the
same test file pins it. Nothing here bears on RH (`docs/08`).

The upper-bound assignment (2026-09-06) is recorded separately in
UPPER_BOUND.md. Its scope is the entire sharp-cutoff CHHL error E(N), through
the centered Fourier mean square and a major/minor-arc proof attempt.
It may add that proof record and small identity tests. It does not reopen the
completed numerical passes or the A/B review, or change their records.
The objective is an unconditional upper bound, with every unproved estimate
identified and every component's contribution to total E retained.

```huntspec
id: prime_pair_error
question: Which separations k carry the Chou-Haag-Huryn-Ledoan error E(N), and is there one compact relationship, with the Hardy-Littlewood prediction held fixed, that accounts for a measurable part of psi_2(N, k) - S(k)(N - k)?
frontier: Table 1 of arXiv:2308.14888 gives E(N)/(N^2 log^2 N) from 0.09464 at N = 10^3 to 0.16857 at N = 10^5; Korevaar and te Riele (Math. Comp. 2010) state a k-averaged heuristic for the remainder at small k with numerics to 10^12 on the prime-count side
proposed_attack: FFT autocorrelation of Lambda up to N = 10^7, cross-checked against direct pair counts; decompose E(N) by decile of k/N and by the small prime divisors of k; fit the error jointly on three profiles, S(k), S(k) times the prime-power deficit, and S(k) times the antisymmetric zero profile R(N-k) - R(k); discover on N <= 10^6 and test at 3 x 10^6 and 10^7
dead_routes:
  - refitting C_2 or the singular series to the data; the prediction is fixed by the brief
  - per-k tables such as the twin prime tables; the signed part is below the per-k noise and only shows when pooled over k
required_oracles:
  - the paper's Table 1, matched after truncation to five decimals at all eleven N
  - a pure-Python pair count with no numpy at N = 2000 and a direct numpy pair count at N = 10^5 against the FFT
  - trial-division factorization against the singular-series sieve at every k <= 3 x 10^4
  - the exact identity sum_{|k| <= N} psi_2(N, k) = psi(N)^2 - sum Lambda(n)^2, evaluated at every N
kill_conditions:
  - Table 1 fails to reproduce after truncation at any of its eleven rows
  - a candidate profile's coefficient moves by more than its scale between the discovery range and the held-out N
  - the relationship is found stated in the literature in the same k-resolved form, in which case the hunt records the citation and claims a reproduction only
agents_may:
  - search
  - derive
  - code
  - measure
agents_may_not:
  - declare novelty
  - refit the prediction
  - promote their own claim
```
