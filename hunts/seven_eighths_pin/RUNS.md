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
