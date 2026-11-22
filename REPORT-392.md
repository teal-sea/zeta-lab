# Issue #392: independent zero count for `hunts/skewes_enclosure/zero_layer.py`

Branch `muse/feat-392-nzeros`. Not pushed, no PR opened, `main` untouched.

Reporter credit: the method is KIDA-Nya's, reported in issue #392 and
implemented there as `check_completeness` in `zeta_audit/audit_table.py` of
github.com/KIDA-Nya/zeta-audit. That file was read as a design reference only.
The code in this tree is written to fit `zero_layer.py` and credits the
reporter in the module docstring and in `mpmath_window_count`.

## What was added

`zero_layer.py` gains a route 3 beside route 1 (Arb isolation and Turing
count) and route 2 (mpmath `siegelz` bracket signs). Route 3 differences
mpmath `nzeros` at midpoints between consecutive ordinates. It is never
evaluated at an ordinate itself. It is route-independent float-grade evidence:
a second opinion, not a certificate, and not a replacement for the Arb route.

API, matching the layer's existing conventions (arb balls or decimal strings
in, JSON-ready dicts out, `dps` through `mpmath.workdps`, lazy mpmath import,
default `dps=30` as in route 2):

- `mpmath_window_count(gammas, start, window_rows, dps=30) -> dict`: one
  window. Reads only the four boundary ordinates, forms the two midpoints,
  raises `ValueError` unless each midpoint is strictly between its ordinates,
  then returns table count, independent count, agreement, and the seconds
  taken by the two `nzeros` calls. Differenced, so it needs no absolute
  index and works on a shard that does not start at gamma_1.
- `check_completeness_mpmath(gammas, windows=3, window_rows=200, dps=30,
  starts=None) -> dict`: sampled windows spread over the table (the
  reporter's placement) or at explicit 0-based `starts`. Returns the method,
  the grade label, the sampled-coverage label, per-window rows,
  `all_agree`, failing starts, and wall seconds.
- `count_vs_smooth(gammas, n0=1, dps=30) -> dict`: the weak sanity check,
  kept separate on purpose. Implied S(T) is the total count minus the smooth
  count theta(T)/pi + 1 at the last ordinate, with the |S(T)| < 3 test.

Design choices worth noting:

- Balls are read by midpoint through the same `mid().str(40)` conversion
  route 2 uses; decimal strings and floats are also accepted, so an external
  table can be checked in its native shape.
- The check is not wired into `run_shard`. Shard JSON keeps its current
  shape, and wiring route 3 into production shards (window size, sampling
  rate, where failures land) is a separate decision for the hunt owner.
- Refusals fail closed: a window without one ordinate outside each end, a
  table too small for the window, an empty window list, and a duplicated
  boundary ordinate all raise instead of evaluating `nzeros` somewhere
  ill-defined.

## Negative control (real run output)

Fixture: the first 60 ordinates, generated locally by `arb_zeros` and handed
to route 3 as decimal strings. Windows: three 10-row windows at 0-based
starts 5, 25, 45. The deleted row, 0-based index 30, lies inside the middle
window only. Output of the demo run, unedited:

```text
deleted ordinate (0-based index 30): 103.725538040478339416398408109

intact, sampled windows:
{
 "method": "mpmath.nzeros differenced at midpoints between consecutive ordinates",
 "grade": "float (mpmath, no error bound): a second opinion, not a certificate",
 "coverage": "sampled windows only: a hole outside them is missed",
 "windows": [
  {
   "start": 5,
   "window_rows": 10,
   "lo": "35.260619873282430474",
   "hi": "66.096177288787890188",
   "table_count": 10,
   "independent_count": 10,
   "agree": true,
   "seconds": 0.01957526500336826
  },
  {
   "start": 25,
   "window_rows": 10,
   "lo": "90.65050523909647486",
   "hi": "113.09744004622267493",
   "table_count": 10,
   "independent_count": 10,
   "agree": true,
   "seconds": 0.018634838983416557
  },
  {
   "start": 45,
   "window_rows": 10,
   "lo": "134.12712347818572889",
   "hi": "154.56880155271838188",
   "table_count": 10,
   "independent_count": 10,
   "agree": true,
   "seconds": 0.02887037000618875
  }
 ],
 "all_agree": true,
 "failures": [],
 "seconds": 0.8984852750145365
}

holed (one row deleted), same windows:
{
 "method": "mpmath.nzeros differenced at midpoints between consecutive ordinates",
 "grade": "float (mpmath, no error bound): a second opinion, not a certificate",
 "coverage": "sampled windows only: a hole outside them is missed",
 "windows": [
  {
   "start": 5,
   "window_rows": 10,
   "lo": "35.260619873282430474",
   "hi": "66.096177288787890188",
   "table_count": 10,
   "independent_count": 10,
   "agree": true,
   "seconds": 0.01370301897986792
  },
  {
   "start": 25,
   "window_rows": 10,
   "lo": "90.65050523909647486",
   "hi": "115.27345061815513357",
   "table_count": 10,
   "independent_count": 11,
   "agree": false,
   "seconds": 0.02066176600055769
  },
  {
   "start": 45,
   "window_rows": 10,
   "lo": "136.43627590395365727",
   "hi": "156.85525055591596373",
   "table_count": 10,
   "independent_count": 10,
   "agree": true,
   "seconds": 0.024404902011156082
  }
 ],
 "all_agree": false,
 "failures": [
  25
 ],
 "seconds": 0.06016999599523842
}

weak check, intact: {"T": "163.03070968718198724", "count": 60, "smooth_N": "59.413392270685928377", "S_implied": "0.58660772931407162306", "abs_S_lt_3": true, "grade": "float (mpmath): weak sanity only, not a completeness check"}
weak check, holed:  {"T": "163.03070968718198724", "count": 59, "smooth_N": "59.413392270685928377", "S_implied": "-0.41339227068592837694", "abs_S_lt_3": true, "grade": "float (mpmath): weak sanity only, not a completeness check"}
```

Reading of that output: with one row deleted, the middle window reports an
independent count of 11 against a table count of 10 and is the only failure,
while the weak check passes on both tables (the deletion moves implied S(T)
by exactly 1 and it stays inside the tolerance). This is the reporter's
Odlyzko-table control reproduced at 60 rows, with the same shape: the
windowed count fails at the right window and the weak check catches nothing.

The pitfall that forces midpoints, from the probe run on this machine
(also pinned by `test_nzeros_at_an_ordinate_is_unreliable`):

```text
nzeros(gamma_1) = 0 (expect ambiguous)  0.0001s
nzeros(gamma_2) = 1 (expect ambiguous)  0.0109s
nzeros(gamma_3) = 2 (expect ambiguous)  0.0062s
nzeros(gamma_10) = 10 (expect ambiguous)  0.0056s
```

## Timings (real run output)

Single `nzeros` calls at midpoints, from the probe run. The high call sits
at the reporter's Odlyzko height:

```text
T=17.5783823903 nzeros=1 0.0049s
T=102.521694523 nzeros=30 0.0068s
T=162.109836912 nzeros=59 0.0083s
midpoint near gamma_100000: T=74921.3786464763 nzeros=100000 (expect 100000) 0.1352s single call
```

Route 3 itself at that height, one 10-row window over arb balls starting at
gamma_99990, from the demo run. `seconds` covers the pair of `nzeros` calls:

```text
arb_zeros(99990, 12) batch seconds: [0.6035464340238832]
{
 "start": 1,
 "window_rows": 10,
 "lo": "74914.633221143017619",
 "hi": "74921.378646476300551",
 "table_count": 10,
 "independent_count": 10,
 "agree": true,
 "seconds": 0.1707049270044081
}
```

One timing caveat visible in the negative-control output above: the first
aggregate call in a fresh process reports wall seconds of 0.8984852750145365
while its three windows sum to far less, because the aggregate wall clock
includes the first mpmath import. Per-window `seconds` times only the two
`nzeros` calls and is the number to compare across windows.

## Tests (real run output)

New file `hunts/skewes_enclosure/test_zero_layer_completeness.py`, 11 tests:
fixture anchoring against the known first ordinates, intact agreement,
the negative control, a hole outside the sampled windows passing (the
sampled limitation, pinned), default sampled starts, arb-ball input, the
shard offset in the weak check, midpoint placement, the at-ordinate
pitfall, and the refusal cases.

```text
...........                                                              [100%]
============================= slowest 5 durations ==============================
0.15s setup    hunts/skewes_enclosure/test_zero_layer_completeness.py::test_fixture_is_the_first_60_ordinates
0.08s call     hunts/skewes_enclosure/test_zero_layer_completeness.py::test_intact_table_agrees_in_every_window
0.05s call     hunts/skewes_enclosure/test_zero_layer_completeness.py::test_windows_accept_arb_balls
0.04s call     hunts/skewes_enclosure/test_zero_layer_completeness.py::test_hole_outside_the_sampled_windows_is_missed
0.04s call     hunts/skewes_enclosure/test_zero_layer_completeness.py::test_negative_control_one_deleted_ordinate
11 passed in 0.55s
```

The hunt's existing tests plus the new ones, one process for the directory
(the per-directory shape `scripts/run_hunt_tests.py` uses; the full all-hunts
sweep was not run):

```text
..................................................                       [100%]
50 passed in 20.11s
```

Baseline before the change, same command shape on the pre-existing file:

```text
39 passed in 17.28s
```

Related gates: the reserved-word test in `tests/test_hunt_probe_discipline.py`
passes on the new hunt files (`1 passed, 6 deselected` under `-k reserved`),
and `scripts/make_context.py --check` reports `CONTEXT.md is up to date.`
The ball-arithmetic backend for these runs:

```text
python-flint ['mpmath.iv', 'python-flint']
```

Environment note: this worktree had no `.venv`. One was created with the
subset the hunt tests need (mpmath, python-flint, pytest, pytest-xdist,
numpy, plus scipy, sympy, matplotlib, pyyaml for the backend check), not the
full `requirements.txt`. Versions as installed:

```text
flint 0.9.0
mpmath 1.4.1
pytest 9.2.0
```

## Docstring update

The `zero_layer.py` module docstring no longer lists the independent count as
missing. It now describes route 3, credits issue #392, and states what
remains open: sampling, float grade with no error bound, and the
argument-principle route unchanged and still not implemented here. Route 1
remains the completeness statement the shards rest on.

## Limitations

- Sampled. Only the windows actually run are checked. A hole outside them is
  missed, and one of the new tests pins exactly that behavior so the limit
  cannot be forgotten. A full sweep costs one pair of `nzeros` calls per
  window at the per-call prices timed above.
- Float grade. mpmath `nzeros` carries no error bound. Agreement is measured
  evidence from a code-disjoint route, graded as a second opinion in the
  result dict itself. It is not a certificate and not a replacement for the
  Arb route, whose Turing count remains the layer's completeness statement.
- Boundary placement. A missing ordinate strictly inside a window is caught.
  If instead a window's boundary midpoint is formed from two table rows with
  a third ordinate missing between them, that midpoint lands near the
  missing ordinate and the differenced count can absorb the hole. Window
  placement should be read with that in mind.
- Unchanged by this issue: the argument-principle independent count (the
  reporter's `certify.py` route) is still the tool that could carry
  enclosures, it is still not implemented in this layer, and nothing here
  changes its cost picture.

## Files changed

- `hunts/skewes_enclosure/zero_layer.py`: route 3 implementation and module
  docstring.
- `hunts/skewes_enclosure/test_zero_layer_completeness.py`: new tests,
  including the negative control.
- `REPORT-392.md`: this report.
