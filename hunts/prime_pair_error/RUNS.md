# Runs

## 2026-09-06, probe.py, discovery pass to N = 10^6 and held-out pass to 10^7

**Estimate written before the large run.** `decompose` at N = 10^6 took 1.2 s and the
whole script 3.1 s; the FFT is N log N, so 10^7 was priced at about 15 to 20 s for the
decomposition plus the sieves, under a minute in all, with the padded FFT of length
2^25 costing about 1 GB and the per-k arrays another gigabyte. Measured: 33.5 s wall,
2.2 GB maximum resident set, 3.9 GB peak footprint, on the operator's 16 GB laptop.
Nothing checkpoints because nothing runs long enough to need it. The final run, after
the singular-series cross-check was added, took 31.7 s wall and 2.7 GB resident.

```runmanifest
id: prime_pair_error-2026-09-06-probe
hunt: prime_pair_error
started: 2026-09-06
finished: 2026-09-06
ran:
  - .venv/bin/python hunts/prime_pair_error/probe.py --max-n 100000
  - .venv/bin/python hunts/prime_pair_error/probe.py --max-n 1000000
  - .venv/bin/python hunts/prime_pair_error/probe.py
outcome: Table 1 reproduced at all eleven N after truncation; the ratio keeps rising to 0.24449 at N = 10^7; the signed part of the error is S(k) times the one-point remainder profile R(N) + R(N - k) - R(k) with unit coefficients at the two held-out N, a k-resolved form of the Korevaar-te Riele average, carrying 1 to 3 percent of E(N) and 12 to 22 percent of the prime-only analogue.
artifacts:
  - hunts/prime_pair_error/results.json
```

## 2026-09-06, residue.py, the residue-class correction at fresh cutoffs

**Estimate written before the run.** `residue.py` at N = 10^6 took 7.0 s wall and
484 MB resident (four moduli, the identity checks, the product form and the
modulo-3 closed form all included). The work is N log N in the FFTs and linear in N
times the number of reduced residues elsewhere, so the fresh list
2 x 10^5, 5 x 10^5, 2 x 10^6, 5 x 10^6, 7 x 10^6 was priced at about 1.5 + 3.5 + 15 + 40
+ 56 s, two minutes in all with the sieve to 7 x 10^6, and the peak resident set at
about 1.6 GB (the closed-form check at q = 3 holds about fourteen arrays of length N
at once). Nothing checkpoints because nothing runs long enough to need it.

**Measured.** 177 s wall, 3.27 GB maximum resident set, 4.4 GB peak footprint, on
the operator's 16 GB laptop: the time estimate was low by half and the memory
estimate by a factor of two. The memory is the q = 3 closed-form check and the q = 30
product form each holding a dozen arrays of length N beside the four corrections; both
are checks, not predictions, and the next pass should compute them at one cutoff
rather than five. Per cutoff: 2.3, 12.5, 28.9, 60.6 and 68.7 s.

```runmanifest
id: prime_pair_error-2026-09-06-residue
hunt: prime_pair_error
started: 2026-09-06
finished: 2026-09-06
ran:
  - .venv/bin/python hunts/prime_pair_error/probe.py --max-n 1000000 --out <scratch> (re-check of the first pass)
  - .venv/bin/python hunts/prime_pair_error/residue.py --fresh 1000000 --out <scratch> (timing)
  - .venv/bin/python hunts/prime_pair_error/residue.py
outcome: The first pass's profile is the modulus-1 member of an exact four-piece decomposition whose only heuristic is that the primes not dividing q act on the reduced classes as all primes act on the integers; with every coefficient fixed at 1, the modulus-3 and modulus-30 members remove more of E(N) than the original at all five fresh cutoffs (0.5 to 1.9 percent for q = 1, 1.0 to 7.6 for q = 3, 2.2 to 10.0 for q = 30) with post-hoc slopes within 1 percent of 1 at q = 30; the residual after q = 30 carries no structure mod 30 and all of its structure at the next primes, which the q = 210 member predicts to within one standard error; the character-weighted sum T(N) matches the integral form to 0.5 percent at every cutoff.
artifacts:
  - hunts/prime_pair_error/results_residue.json
```
