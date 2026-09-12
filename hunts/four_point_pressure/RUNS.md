# Runs

## 2026-09-05: candidate emitted, complete Lean check canceled

**Terminal status: canceled, not kernel-checked.** The existing registered
four-point bound remains unchanged. This experiment produced no new proved
constant, and no 68% or 69% result.

The selected parameters were `n=4`, `c=2330/1000000`, `p=2500`, `m=432`.
Substitution into the existing bridge gives the candidate expression

    (14400000 * H - 17240) / 14366681

where `H = 3/2 - cot(1/sqrt(2))/sqrt(2)`. Numerical evaluation at 80-digit
working precision, rounded here:

    registered: 0.672847019766688827607589366851
    candidate:  0.672860358838866659500205300554
    difference: 0.0000133390721778318926159337024

The subtraction compares expressions, not two established lower bounds.
The candidate's uniform finite-certificate obligation was not discharged by
a complete Lean build. The earlier
[FOUR-POINT.md](../ainta_seven_point/FOUR-POINT.md) already tabulated this
floor, so this is not a claim to have discovered the numerical parameter.

### Exactly what ran

The original local run reported exact search-tree closure. The separate
emitted-source preflight was rerun before this publication on the preserved
candidate checkout. It reports 1516 cell lemmas, 11863 leaves, 220 chunks,
13 boxes, and 64 dispatch cases, with zero problems. This is an arithmetic
and coverage check of the emitted source, not a Lean kernel check.

The complete check was attempted only in
[GitHub Actions run 33987435968](https://github.com/teal-sea/zeta-lab/actions/runs/33987435968),
against commit `d28df5f992479cd32751cb90c8c88551550582a3`.
The run was created at `2026-09-05T19:32:53Z` and reached terminal
`completed/cancelled` status at `2026-09-05T19:42:20Z`.

Toolchain installation and the Mathlib cache step succeeded. The dependency
build was canceled. Every candidate proof step, including `FourPoint.Base`,
the cells, the chunks, `FourPoint.Main`, and the final axiom audit, was
**skipped**. A later cache-saving step failed during cancellation cleanup;
that is not a mathematical failure of the candidate. No Modal job was
started. The state was read back from the run API before publication.

The original time estimate was about 3h50m with ideal two-process scaling,
using the earlier measured per-cell and per-leaf rates in `FOUR-POINT.md`.
The run did not measure that speedup. Accordingly, its parallel-build
workflow change is not included in this publication.

### Reproduce the arithmetic without starting a search or build

From a repository environment with the declared Python dependencies:

```sh
.venv/bin/python - <<'PY'
from fractions import Fraction as Q
import mpmath as mp

with mp.workdps(80):
    H = mp.mpf(3)/2 - mp.cot(1/mp.sqrt(2))/mp.sqrt(2)

    def expression(c, p, m):
        denominator = Q(m) - c * (m - 3)
        coeff = Q(m) / denominator
        offset = Q(3 * (m - 1), p) / denominator
        value = (mp.mpf(coeff.numerator) / coeff.denominator * H
                 - mp.mpf(offset.numerator) / offset.denominator)
        return coeff, offset, value

    old = expression(Q(2310, 10**6), 2500, 435)
    candidate = expression(Q(2330, 10**6), 2500, 432)
    assert old[:2] == (Q(906250, 904171), Q(1085, 904171))
    assert candidate[:2] == (Q(14400000, 14366681), Q(17240, 14366681))
    assert old[2] < candidate[2] < mp.mpf('0.68') < mp.mpf('0.69')
    for label, value in [('registered', old[2]), ('candidate', candidate[2]),
                         ('difference', candidate[2] - old[2])]:
        print(label, mp.nstr(value, 30))
PY
```

To inspect the already-emitted source, use a checkout at the pinned
candidate commit and run:

```sh
.venv/bin/python hunts/ainta_seven_point/four_point_preflight.py
```

That command reads the generated files. Regenerating them or launching the
complete Lean workflow is not necessary to reproduce this record.

### Scope and exclusions

The existing [family-wall analysis](../family_wall/FAMILY-LIMIT.md) concerns
the current n-point pressure construction for `n>=3`. Its written argument
and interval-arithmetic witnesses give a ceiling near `0.675142509660254`,
below 68%. This experiment did not produce a new Lean proof of that ceiling,
nor does it turn a method-specific wall into a bound for every possible
zeta argument. The previously published analysis, including its repaired
case split, is the source for that statement.

The candidate branch is preserved for reproducibility. None of its generated
Lean replacements, candidate-specific preflight constant, or workflow edits
is merged with this record. The registered theorem and public headline are
unchanged.

The original broad local fast-tier attempt stopped with 28 failures, 610
passes, and one expected failure; its failures reported absent `clang`.
It was not a green full-suite run. The archival publication instead checks
the touched documentation and hunt contracts, the arithmetic snippet above,
the emitted-source preflight, the context index, and the secret guard.

```runmanifest
id: four_point_pressure-2026-09-05-c2330-disposition
hunt: four_point_pressure
started: 2026-09-05T19:32:53Z
finished: 2026-09-05T19:42:20Z
ran:
  - .venv/bin/python hunts/ainta_seven_point/four_point_gen.py 2330 2500
  - .venv/bin/python hunts/ainta_seven_point/four_point_preflight.py
  - GitHub Actions four-point workflow at d28df5f992479cd32751cb90c8c88551550582a3, run 33987435968
outcome: exact search and source preflight completed; dependency build canceled and every candidate proof step skipped; no new proved bound
artifacts:
  - hunts/four_point_pressure/MISSION.md
  - hunts/four_point_pressure/RUNS.md
```
