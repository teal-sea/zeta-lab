# Run evidence

Owner prime_gap_density, 2026-10-08. Read-only lab base and source pins are
in MISSION.md. Scope limited to this directory; no Git mutation or paid calls.

From task-3/zeta-research:

```
.venv/bin/python ../routes/prime-gap-multistrip/layers.py > ../routes/prime-gap-multistrip/verification.txt
```

Python3.13/python-flint0.9.0, Arb256bits, serial, .356seconds wall time on
final run. No heavy arrays or worker processes. Limits organizational, not
OS enforced. Finite contract: assert764 interval inequalities, analytic-tail
monotonicity conditions and a tail value, plus9 exact small prime witnesses.
The finite computation relies on the written reduction and cited source.

Final script SHA256 457c1144f45640888656599e744a8e73877d59999ca14ab655c4231f7af0dbe5.
Output SHA256 31b28b250e36ba26bbc218f1baf6a7543e4731aa0063c984104acd0f951a3dab.
Read-only imported density.py SHA256 ea2f62d92df2d8011131f973ef2570556f9c8d178e1fd14df4fccc5820335b55.
Read-only imported base_bound.py SHA256 a5e2e54079979bbd71197ddddb4e45443bc027fe23a4692f7d44ea8e46410969.

Independent review requested from independent_audit with exact files and
mathematical claim. Its report is maintained outside this write scope.
