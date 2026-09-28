# L = 1.19 bounded referee plan

Authorized by Thomas's 2026-09-27 task, received 2026-09-28. This supersedes
only the earlier prohibition on new L=1.19 work. No push or PR. All writes
stay under referee/. Modal profile teal-sea, at most four core-hours total.

Read BRIEF, PROGRESS, REVIEW and RUNS first. Author input: prose/results only,
9419552, 500a803 and b876f0a. Exact witness copied from b876f0a envelope JSON.
No author implementation read or imported. Shared arithmetic library remains
python-flint, while quadrature, series and analytic budgets are independent.

First unit: last ten half-unit panels, [495,500], CC degree 192, 1024 bits,
500 even Legendre modes. Anticipated 60 to 600 seconds, unmeasured. Hard
limit 900 seconds, 1 CPU, 1792 MiB. Write each panel's progress and final
exact-dyadic matrix to oob-envelope-referee/l119/REVISION/UNIT. No retries.
Measure this unit and record a total estimate in RUNS before the other 99
units. Refuse the full dispatch if measured extrapolation plus reducer and
startup allowance exceeds four core-hours. Monitor every app to stopped.

The independent positivity witness uses a fixed exact shift 5.718e-48,
chosen before assembly. Its midpoint Cholesky factor is converted to exact
dyadics and checked by Arb matrix multiplication. Row sums bound both the
symmetric residual and all entry errors. Full bound subtracts independently
computed tail and coupling norms. Desired outward-safe endpoint 5.7179e-48.
Failure of the fixed shift or arithmetic widths is inconclusive, not a
negative theorem. No optimization toward the last successful digit planned.

The constant in-band mutation H -> H-100 together with beta -> beta-100
changes the reduced form by exactly -100 I. A negative constant-window
Rayleigh enclosure must be obtained and the same factor step must reject it.
This targets positivity rejection and the violated Fourier support premise;
it does not purport to be a legitimate alternative zeta envelope.

The published L=1.1 upper bound is 2.78e-38 (Zhu Table 3, read from v2).
Nested even windows give the necessary one-sided K1 ceiling at L=1.19.
No odd-sector conclusion, novelty claim or uniform RH conclusion is sought.
