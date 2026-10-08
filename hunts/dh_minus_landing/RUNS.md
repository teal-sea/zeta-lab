# Runs

All runs on 2026-10-08 in the `hunt/forage-2026-10-08` worktree, Python
3.13 from the repository's `.venv` (python-flint 0.9.0, `rigor.BACKEND =
python-flint`), one core, no CI, no Lean build.

## Estimate written before the probe

The parent hunt records one 128-bit disk enclosure at `0.0093 s` and one
320-node continuation step under a millisecond. Timed here before the ladder:
`odd_ball.rouche` at `217/200`, 128 bits: `0.041 s`; one mpmath quadrature of
`H_t` at 30 digits: `0.17 s`, at 50 digits: `0.31 s`; one float grid
evaluation: `0.3 ms`. Budget: route A is six quadratures per Newton step times
about eight steps at each of two precisions, about `10 s`; route B is a few
thousand grid evaluations, under `5 s`; the ladder is five rungs of one mpmath
centre polish (about `2 s`) plus four disks, about `12 s`; the second pair and
lesions, about `6 s`. Expected total under one minute, no checkpointing needed.

## 2026-10-08, prototypes in the scratchpad (not committed)

Two throwaway scripts validated the routes before the probe was written. Both
landing-time routes agreed at once (`t_c = 1.0876360002296` float,
`1.08763600022958693221796...` at 30 and 50 digits). Two instrument refusals
happened and are worth recording: the quartic tracker control first enclosed
all four roots (winding 4, with `Y > a` no circle separates the pair from the
real roots), fixed by choosing `a = 1.2, Y = 0.5`; and a fixed contour for the
second pair at `t = 0.7` returned winding 1 because one real zero had already
left it after the landing, fixed by bracketing from the last off-axis time
with a `0.4` radius. Neither refusal produced a number that was used.

```runmanifest
id: dh_minus_landing-2026-10-08-prototype
hunt: dh_minus_landing
started: 2026-10-08T00:00Z
finished: 2026-10-08T00:30Z
ran:
  - .venv/bin/python <scratchpad>/proto.py (route B float discriminant, route A mpmath double zero)
  - .venv/bin/python <scratchpad>/proto2.py (second pair continuation, polynomial controls, disk ladder, lesions)
artifacts:
outcome: both landing-time routes agree on t_c near 1.0876360002296 and five rational disks below it decide; two contour refusals (winding 4, winding 1) were corrected before any number was recorded
```

## 2026-10-08, probe.py, first full run (one stage null)

`37.1 s` wall. Every stage returned except the shared-layer kernel lesion,
which looked for the perturbed pair at `t = 1.08` from the true pair's
position and found a real zero there: the 1% fault moves the landing time
below `1.08`, so the lesion stage returned `pair_found: false`, a null for that
stage. No other number changed between this run and the next.

```runmanifest
id: dh_minus_landing-2026-10-08-probe1
hunt: dh_minus_landing
started: 2026-10-08T01:00Z
finished: 2026-10-08T01:01Z
ran:
  - .venv/bin/python hunts/dh_minus_landing/probe.py
artifacts:
  - hunts/dh_minus_landing/results.json (overwritten by probe2)
outcome: t_c measured by both routes to 4.7e-14 agreement, ladder decided to 10876359/10^7, second pair lands at 0.63095; the shared-layer lesion stage returned null because it started below the perturbed landing time
```

## 2026-10-08, probe.py, second full run (the recorded one)

The lesion stage now tracks the perturbed pair from `t = 0`, and the second
pair gains the 960-node resolution check. `33.1 s` wall: controls `3.3 s`,
route B `7.7 s`, route A `10.4 s`, ladder `10.9 s`, second pair and lesions
`4.8 s`. Measured against the estimate: within budget throughout.

```runmanifest
id: dh_minus_landing-2026-10-08-probe2
hunt: dh_minus_landing
started: 2026-10-08T01:10Z
finished: 2026-10-08T01:11Z
ran:
  - .venv/bin/python hunts/dh_minus_landing/probe.py
artifacts:
  - hunts/dh_minus_landing/results.json
outcome: t_c = 1.087636000229586932217964154453984835461141904 (route A, 50 digits; route B within 4.7e-14), strict lower endpoint 10876359/10^7 decided on four Arb configurations, door worth 2.636e-3 for this pair and shut to 1.0e-7; the 1% kernel fault moves t_c by 0.067 while both routes agree to 1.4e-13 and only the Hurwitz identity (defect 1.2e-3) catches it; no kill condition fired
```

## 2026-10-08, tests

```runmanifest
id: dh_minus_landing-2026-10-08-tests
hunt: dh_minus_landing
started: 2026-10-08T01:20Z
finished: 2026-10-08T01:25Z
ran:
  - .venv/bin/python -m pytest -q -n0 hunts/dh_minus_landing
  - .venv/bin/python -m pytest -q -n0 hunts/dh_minus_landing tests/test_docs_numbering.py tests/test_hunt_probe_discipline.py tests/test_doors.py tests/test_hunt_doors.py tests/test_huntspec.py tests/test_hunt_numbering.py
  - .venv/bin/python scripts/make_context.py --check
artifacts:
  - hunts/dh_minus_landing/test_dh_minus_landing.py
outcome: hunt subset 15 passed in 0.65 s; governance subset 71 passed and 3 xfailed (the three pre-existing KNOWN_INCOMPLETE doors sections) in 142.24 s; CONTEXT.md up to date; no em dash, reserved word, whitespace or secret finding
```
