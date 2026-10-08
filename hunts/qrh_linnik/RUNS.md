# Run record

## Baseline

Worktree `/home/user/zeta-lab-qrh-linnik`, branch `hunt/qrh-linnik`, from
`origin/main` at `ef4e0564349c19c9e6ca91e78ebe3e4f5e224997`. Interpreter
`.venv/bin/python` (Python 3.13), sympy 1.14.0, numpy 2.5.3, matplotlib 3.11.2;
`zeta.rigor.BACKEND` reports `python-flint` with both backends available. No
enclosure is computed in this hunt, so the backend is recorded, not used. Shared
machine: 4 cores, 15 GB, three other agents; every run below is one serial process.

## Literature pass (2026-10-08, before any computation)

Read the extracted OpenAI texts (the 7/8 paper dated 30 September 2026, the 11/12
paper dated October 5); neither mentions Linnik's constant. Downloaded and read
Chen, Gupta, Li, arXiv:2507.08296v2: abstract, sections 1 and 2, section 12 in full
(zero detection, class-II zeros, Lemma 12.1 and its four cases, Remark 12.2, the
conclusion and (12.6)), reference list. Their Theorem 1.1 proof (sections 3 to 11)
was not audited. Searches: web search on Guth-Maynard extensions to characters, on
Linnik's constant under zero-free strips, density hypothesis and quasi-GRH, on
almost-all least primes; zbMATH Open API (four queries); the Wikipedia table
(raw wikitext); Bruna arXiv:2603.25612 (structure only); Naslund hexagon
2610.00018v1 (abstract only). Findings are in RESULTS section 7.

## Budget, before execution

Exponent algebra: sympy on a handful of rational functions, seconds. Least primes:
one pilot at `q <= 500` (sieve `2*10^6`) to time a unit, then the full table
`q <= 5000`. Per-modulus cost scales like the scanned prefix, about
`q log^2 q`, so the full run extrapolates to about `100 * 1.9 = 190` times the
pilot's compute; allow a 900 s wall limit, memory under 0.3 GB (sieve to `2*10^7`).

Pilot: 0.446 s of compute at `q <= 500`, max exponent 1.83 at `q = 5`, nothing at
or above 2. Full run: 50.9 s, about a quarter of the extrapolation (the prefix cut
rarely needed the whole table). That first full run wrote uncompressed rows
(598 kB); the output format was compacted and the run repeated (49.1 s), and only
the repeat's artifacts are kept. Figure checked by eye after each render: the
legend was moved off the reference lines and the horizontal grid removed where it
doubled the dashed lines.

```runmanifest
id: qrh_linnik-2026-10-08-pilot
hunt: qrh_linnik
started: 2026-10-08T11:23:30+00:00
finished: 2026-10-08T11:25:17+00:00
ran:
  - .venv/bin/python -m hunts.qrh_linnik.exponents
  - .venv/bin/python -m hunts.qrh_linnik.least_primes --Q 500 --limit 2000000 (outputs to scratch, not kept)
outcome: exact exponents 12/5 at 3/4, 7/3 at 5/7 and 30/13 at 7/10 agree with the float grid; least-prime pilot timed at 0.45 s for q up to 500
artifacts:
```

```runmanifest
id: qrh_linnik-2026-10-08-table
hunt: qrh_linnik
started: 2026-10-08T11:25:29+00:00
finished: 2026-10-08T11:32:23+00:00
ran:
  - .venv/bin/python -m hunts.qrh_linnik.least_primes --Q 5000 --limit 20000000 (first pass, uncompressed rows, superseded)
  - .venv/bin/python -m hunts.qrh_linnik.least_primes --Q 5000 --limit 20000000
outcome: least primes for every reduced class with q up to 5000; the largest log p over log q is 1.83 at q equal to 5 and 1.72 for q at least 100, with no modulus reaching 2
artifacts:
  - hunts/qrh_linnik/least_primes.json
  - hunts/qrh_linnik/least_primes.png
```

```runmanifest
id: qrh_linnik-2026-10-08-checks
hunt: qrh_linnik
started: 2026-10-08T11:32:30+00:00
finished: 2026-10-08T11:38:14+00:00
ran:
  - .venv/bin/python -m pytest -q -n0 hunts/qrh_linnik/
outcome: 33 hunt tests pass, covering exact exponents, grid agreement, the theta profile, the shadow price of the q1 exponent, three lesions, the divisor profile, the Lemma 5 bookkeeping, the parse of the CGL closed forms, and the least-prime table against brute force
artifacts:
  - hunts/qrh_linnik/exponents.py
  - hunts/qrh_linnik/least_primes.py
  - hunts/qrh_linnik/test_qrh_linnik.py
  - hunts/qrh_linnik/RESULTS.md
```

## Lemma 2 calibration run

Pilot first: the tail `|W(rho_n)|` is 3.5e-3, 4.7e-4, 8.2e-5 at `n` = 10, 30, 60
(0.2 to 0.7 s each), and one residual at `x = 500`, `n = 10` took 1.5 s. Budget:
a sweep `n` = 20, 40, 80, 160 at `x = 1000` under a 900 s wall limit, the
per-zero cost growing with `gamma`; no finer estimate was made. It took 193 s (the quadratures at large
`gamma` dominate). The hunt test reruns only `n` = 20, 40 and the flipped sign
(24 s).

```runmanifest
id: qrh_linnik-2026-10-08-explicit
hunt: qrh_linnik
started: 2026-10-08T11:42:28+00:00
finished: 2026-10-08T11:47:17+00:00
ran:
  - explicit_check.tail_size at n = 10, 30, 60 and explicit_check.residual at x = 500, n = 10 (pilot)
  - explicit_check.residual at x = 1000 for n = 20, 40, 80, 160, and with the zero-sum sign flipped at n = 80
  - .venv/bin/python -m pytest -q -n0 hunts/qrh_linnik/
outcome: the Lemma 2 residual for zeta falls from 0.041 to 0.00042 as the zero count goes from 20 to 160 and is 0.279 with the sign flipped; 34 hunt tests pass
artifacts:
  - hunts/qrh_linnik/explicit_check.py
  - hunts/qrh_linnik/test_qrh_linnik.py
```

## Gates before hand-back

The first gate run failed one test: `MISSION.md` cited the kernel-check note as a
bare `docs/38`, which exists only on unmerged PR #271. The citation was reworded;
the rerun passed.

```runmanifest
id: qrh_linnik-2026-10-08-gates
hunt: qrh_linnik
started: 2026-10-08T11:38:49+00:00
finished: 2026-10-08T11:51:30+00:00
ran:
  - .venv/bin/python -m pytest -q -n0 tests/test_docs_numbering.py tests/test_hunt_probe_discipline.py tests/test_doors.py tests/test_huntspec.py tests/test_hunt_numbering.py tests/test_contribution_check.py tests/test_hunt_doors.py hunts/qrh_linnik/ (first run, one docs-numbering failure)
  - .venv/bin/python -m pytest -q -n0 tests/test_docs_numbering.py tests/test_hunt_probe_discipline.py tests/test_doors.py tests/test_huntspec.py tests/test_hunt_numbering.py tests/test_contribution_check.py hunts/qrh_linnik/
  - .venv/bin/python scripts/make_context.py --check
  - .venv/bin/python scripts/71_contribution_check.py hunts/qrh_linnik
  - .venv/bin/python scripts/check_secrets.py --tree hunts/qrh_linnik
outcome: required subset 75 passed after the citation fix; context up to date; contribution contract passes; secret scan clean
artifacts:
  - hunts/qrh_linnik/MISSION.md
```
