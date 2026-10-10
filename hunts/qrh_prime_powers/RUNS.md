# Run record

## Baseline

Worktree `/home/user/zeta-lab-qrh-prime-powers`, branch `hunt/qrh-prime-powers`
from origin/main `ef4e0564`. The virtual environment is the primary checkout's
(symlinked); `zeta.rigor.BACKEND` reported `python-flint` with backends
`['mpmath.iv', 'python-flint']`; python-flint 0.9.0. Machine shared with three
other agents (4 cores, 15 GB); every run here was a single serial process.

## Estimate before spending

One Arb interval bound (`bound.interval_bound`, 256 bits) was timed inside the
first cover: 1564 intervals in under one second, so about 0.5 ms per interval.
The planned work (four covers of 1500 to 6300 intervals, two pointwise control
scans of about 2000 points, one 3000-interval psi cover, nine small Pratt
certificates per exponent) extrapolated to under one CPU-minute in total, far
inside the 60 CPU-minute allowance. No checkpointing was needed: the longest
single run took 8 seconds wall-clock.

## Pilots (scratch, not committed)

A float prototype (numpy trapezoid integration of the Stieltjes integrals)
was run first, outside the tree, to choose the weight and see whether k = 9
could close. It reported a k = 9 peak of E = 0.163 at log n = 31.25, failure
for k = 8 from log n near 28.5, closure for theta = 15/16 at k = 17 and failure
at k = 16. The Arb closed forms later reproduced the k = 9 peak to five digits
(0.16285 both ways). Prototype numbers are measured only and appear nowhere as
evidence.

The first Arb cover used an adaptive step that grew to width 2 in log n where
margins were large; it closed but reported a worst-interval margin of 0.043,
an artefact of the coarse width near the peak (the factor e^(2*9/8) between the
interval ends). The step was capped at 1/16, after which the worst margin is
0.8253. Both covers are valid; the capped one is recorded.

A first attempt at the psi tail lemma contained a placeholder line and was
rewritten from the derivation before any number from it was used.

```runmanifest
id: qrh_prime_powers-2026-10-08-pilot
hunt: qrh_prime_powers
started: 2026-10-08T11:13+00:00
finished: 2026-10-08T11:25+00:00
ran:
  - float prototype of E(n) for (k, theta) in {(9, 7/8), (8, 7/8), (16, 15/16), (17, 15/16), (18, 15/16)}, scratch directory
  - .venv/bin/python -m hunts.qrh_prime_powers.verify chain   (first adaptive cover, step cap 2)
outcome: the prototype showed k = 9 closing and k = 8 failing; the first Arb cover closed with a coarse-grid worst margin of 0.043 and was superseded by the step-capped cover
artifacts:
```

## The recorded run

```runmanifest
id: qrh_prime_powers-2026-10-08-record
hunt: qrh_prime_powers
started: 2026-10-08T11:41:17+00:00
finished: 2026-10-08T11:41:35+00:00
ran:
  - PYTHONPATH=. .venv/bin/python -m hunts.qrh_prime_powers.verify
  - PYTHONPATH=. .venv/bin/python -m pytest -q -n0 hunts/qrh_prime_powers/
outcome: Theorem 1 (k = 9) closes with worst margin 0.8253, and 0.3027 with no verified height; Theorem 1' (k = 13 from 11/12) closes; the 15/16 control closes at k = 17; k = 8, 12, 16 fail from log n = 28.43, 29.03, 29.47; Theorems 2 and 3 close; hunt tests pass
artifacts:
  - hunts/qrh_prime_powers/verification.json
  - hunts/qrh_prime_powers/witnesses_k9.json
  - hunts/qrh_prime_powers/witnesses_k13.json
  - hunts/qrh_prime_powers/witnesses_k17.json
```

Wall-clock for the full replay and the hunt tests: 18 seconds. Peak memory was not separately
measured; the process holds only Arb scalars and three small JSON trees.
