# Runs

Every run, including the ones that produced nothing. All on a cloud container; nothing
ran on the operator's machines. The arithmetic is exact rational algebra plus small
numpy grids, so no estimate was owed beyond "seconds to minutes".

## 2026-10-16, reading and derivation

The paper's source was cloned (blob-filtered) from `github.com/openai/math` at
`adc7f124` into a scratch directory outside the tree, read as data only. Four
separate readings of fixed line ranges ran in parallel, each writing a report of
verbatim formulas with line numbers and checking its own arithmetic (about ten
minutes each). Their reports stayed in scratch; what this hunt uses from them is
re-derived in `probe.py` or marked inferred in `RESULTS.md`.

One scratch scan that lowered the slope α together with the target (treating α as
the 11/12 input) was wrong, since α = 5/6 is the sextic amplification slope (line
15300). Its output (an apparent fixed point near 0.8745) is not used anywhere.

## 2026-10-16, the probe

`probe.py --quick` (exact part only) takes a few seconds. The full run adds float
scans (19 offsets times two capacity settings, then five excess scalings, each a
46-step bisection over a 1201 × 201 grid) and took a few minutes on one core. The
first refresh attempt failed before running because `/usr/bin/time` is absent in the
container; it was rerun without it.

```runmanifest
id: seven_eighths_pin-2026-10-16-probe
hunt: seven_eighths_pin
started: 2026-10-16T14:25Z
finished: 2026-10-16T14:47Z
ran:
  - .venv/bin/python hunts/seven_eighths_pin/probe.py --paper <clone>/preprints/The-Quasi-Riemann-Hypothesis-September-30-2026/build/paper.tex
outcome: 38 of 38 printed constants reproduced, 39 of 39 citations on their line; exact bound 5655673/6464057 over every geometry, scan optimum 0.874958, floor corner 13/15
artifacts:
  - hunts/seven_eighths_pin/results.json
  - hunts/seven_eighths_pin/probe_output.txt
```

## 2026-10-21, landing check against the public follow-ups

At landing the hunt was renumbered #139 and the prior-art search of `RESULTS.md`
section 10 was run. It found the re-optimized geometry already published, so three
checks ran against this hunt's own formulas, on a 32-vCPU Linux box and not on the
operator's machines, each taking seconds to a minute. `probe.py`, `results.json` and
`probe_output.txt` were not rerun or changed.

- Two scratch refinements of the float scan, kept out of the tree, took the minimum
  over δ at x = 1/2 continuously from the grid's minimum with a bounded scalar
  minimizer, bisected ℓ for 60 steps and searched b in [0.115, 0.13]. With c = 4/9 they
  gave best b = 0.123405 and target 0.8749570698, and 0.8749572006 at b = 1/8; with the
  capacity tied to the target, 0.8749570194 at b = 0.123406.
- An exact symbolic computation (sympy) found that at x = 1/2 and c = 4/9 the
  b-coefficient of −E_* vanishes where 288δ² − 588δ + 185 = 0, at
  δ* = (49 − √921)/48, and that the one-witness program there gives
  (1507 − 2√921)/1653 exactly, tight at ℓ* = 11/551 + 8√921/1653 and
  b* = −4/29 + 230√921/26709.
- The last three tests of `test_seven_eighths_pin.py` pin these agreements with Gao,
  Guo and Liu at 45 digits. Planted faults in the slope α, in the default capacity
  coefficient and in the sign of the offset term each turned at least one of them red.

```runmanifest
id: seven_eighths_pin-2026-10-21-landing
hunt: seven_eighths_pin
started: 2026-10-21T15:30Z
finished: 2026-10-21T15:56Z
ran:
  - .venv/bin/python -m pytest -q -n0 -p no:cacheprovider hunts/seven_eighths_pin
outcome: 114 tests pass, three landing checks among them; the hunt's formulas reproduce the public optimum sigma star, Liu's tight point at sigma dagger and Gao's boundary line
artifacts:
```

## 2026-10-21, prior-art extension

The landing's search had stopped at Guo's README. It was extended the same day to the
three works that README names and to the follow-ups' own manuscripts, as listed in
`RESULTS.md` section 10. Each source was fetched read-only through the GitHub API at the
stated commit into a scratch directory outside the tree, on the same Linux box, and read
as data; nothing in it was executed. The pinned `paper.tex` was fetched again (sha256
matches) to read lines 15085 to 15119 and 15290 to 15311. One scratch comparison in
mpmath at 40 digits put LW56e2's 4374785349/5000000000 at 8.3 × 10⁻¹³ above σ*.
`probe.py`, `results.json` and `probe_output.txt` were not rerun or changed.

Section 10 states several translations between this hunt's variables and the sources'
(tomoto0's E is C₀ on M + ℓ = 1, its corner condition is M − 2ℓ ≥ 3/8 + b, the
follow-ups' low-side loss is `row_loss` on that line). A block of exact tests added
before the landing checks pins each of them. Planted faults (13/12 changed to 13/11 in
tomoto0's exponent, the loss denominator 4 changed to 3, `row_loss` with M − d in place
of M − 2d, LW56e2's numerator lowered by one, and the corner constant 3/8 changed to 1/4)
each turned at least one of those tests red.

```runmanifest
id: seven_eighths_pin-2026-10-21-prior-art-extension
hunt: seven_eighths_pin
started: 2026-10-21T21:27Z
finished: 2026-10-21T21:50Z
ran:
  - .venv/bin/python -m pytest -q -n0 -p no:cacheprovider hunts/seven_eighths_pin
outcome: 133 tests pass, 19 of them new exact checks of the translations section 10 states; the extension changed text and tests only
artifacts:
```
