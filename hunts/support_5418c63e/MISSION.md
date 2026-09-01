# MISSION: ARM B, window asymptotics for the depth-1 damage kernel (support run 5418c63e)

**This is a hunt. Nothing in `hunts/` is a result, and nothing here is
evidence for or against RH (`docs/08`).**

A support run launched by a parent session working `hunts/r_c7f779` (run
`872d7dce`), to answer one bounded question independently and hand the answer
back.

## The bounded question

`hunts/frontier_math/gram_form.py` defines
`ghat(z) = int_{-1/2}^{1/2} cos(sqrt2 t) e^{zt} dt` and the damage
`D(a, s) = -Re ghat(a + i s)^2`. A *depth-1 damage window* is a maximal
interval of `s` on which `D(1, s) > 0`.

Locate the depth-1 window edges out to `s ~ 1e5`. Decide whether the window
centres minus `2 pi d` are (i) linear in `d`, (ii) bounded and converging to a
constant offset, or (iii) something else. Concretely: does every multiple of
`2 pi` lie inside a depth-1 window for all `d`? If not, give the first `d` that
does not. If so, give `min_d dist(2 pi d, nearest edge)` and say whether it is
bounded away from 0.

It matters because `hunts/r_b9552d/RESULTS-37fb06a9.md` §2 derives the
atom-reserve ceiling `rho* <= 0.153216295` from the *measured* fact that
`P = 0` on the critical lattice out to `d = 4000`. If the windows track `2 pi`
asymptotically the ceiling is exact; if they drift, the true `rho*` is slightly
below it.

## Scope

May write: this directory and one case-log entry in `hunts/README.md`.
May not write: any other hunt directory, `zeta/`, `harness/`, `lean/`, `meta/`,
`ontology/`, `hunts/frontier_math/`, or any root markdown file.

The launching brief's deliverables paragraph named `hunts/r_c7f779/arm_b/`
while its scope paragraph named `hunts/support_5418c63e/` and forbade writing
into any other hunt directory. The scope paragraph wins, so the work is here
and the parent is told where to find it.

## What it measures

`probe_arm_b.py` (numpy + mpmath, ~7 s; `--quick` in under a second):

* the closed one-term form of `ghat`, cross-checked against
  `gram_form.damage` (read-only import) and against an independent mpmath
  evaluation of the two-term form at `dps = 50`;
* the derived `1/s^2, 1/s^3, 1/s^4` expansion of `D(1,s)`, checked against the
  exact kernel at five ordinates;
* the exact rational identity for `D` restricted to `s in 2 pi Z`, and the
  sign of the cubic that controls it;
* every sign change of `D(1, .)` on `[1e-6, 1e5]`, by a `0.002` scan plus
  bisection, with the window/lattice incidence, the centre offsets and the
  margins;
* the edge-law constants `w0`, `K`, `W2`, against high-precision edge
  locations at `dps = 50` and `dps = 60`.

Results in `RESULTS.md` and `results.json`. The reserved word is not used.
