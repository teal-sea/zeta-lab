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
