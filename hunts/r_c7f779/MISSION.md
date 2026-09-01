# r_c7f779 — the Cohn–Elkies-style certificate route for T1

**Run `872d7dce-5f49-4e7c-8fcf-f470fd066e6f`, opened 2026-08-24.**
Parent: `hunts/r_b9552d` run `37fb06a9` (`RESULTS-37fb06a9.md` §5, loose
thread 2), which recorded the route as assessed and not settled.

## The question

A Cohn–Elkies-style certificate for T1 is a function `G` with

    G(s) >= f(s) := Dam(2y, s) - Kpair(s)      for every s != 0,
    Ghat(w) <= 0                               for every w,

since then `sum_{p,q} G(tau_pq) = int Ghat |That|^2 <= 0`, so
`GAS <= -k G(0)` for **every** configuration at once, and T1 follows for all
`k` simultaneously whenever `-G(0) < Shq(1/2) = 0.06750840786062762`.

Parametrising `G(s) = -int mu(w) cos(sw) dw` with `mu >= 0` makes
`Ghat <= 0` structural, and the route's value is the linear program

    V := min int mu   subject to   G >= f on (0, infinity).

Two thresholds bracket the verdict, both inherited from run `37fb06a9`:

* `V >= L/2 = 0.05716501969327026` always, because the uniform `2*pi`
  lattice is a dual-feasible configuration. A computed value **below**
  `0.05716` is a truncation artefact and carries no upper-bound content.
* `V < Shq(1/2) = 0.06750840786062762` is what the route needs. A value
  **above** `0.06751` kills the route with a witness.

Run `37fb06a9` reached `0.05410` at horizon `s_max = 200` and its solver
failed at 400 and 600. The window between the two thresholds is 15% wide and
is exactly `2*(c2(0) - A^2) = 0.010343...`.

**This hunt's question: where in that window does `V` actually sit, or is it
above the top of it?**

## Preregistered kill conditions (written before any search)

1. If a re-solved, well-conditioned LP whose feasibility is verified a
   posteriori on a dense grid returns a value **above 0.06750841**, the route
   is dead with a witness and this hunt says so.
2. If the LP value **stalls below 0.05716502** as the horizon grows and the
   verified certificate class cannot be repaired, the discretisation is still
   biting and this hunt reports *not settled*, not a bound.
3. If a certificate is produced whose value clears `0.05716502` and stays
   under `0.06750841`, it is only a result if a dense independent
   re-evaluation of `G - f` (different code path from the LP's constraint
   matrix) finds no violation, and the tail `s > s_max` is covered by an
   argument rather than by absence of grid points.
4. Any claimed certificate that a red-team arm breaks is withdrawn, not
   repaired-and-kept.

## Scope

Writes only inside `hunts/r_c7f779/` plus one case-log entry (Hunt #110) in
`hunts/README.md`. No changes to `zeta/`, `ontology/`, `harness/`, `lean/`,
`meta/`, `hunts/frontier_math/`, or any root markdown file. Nothing here
bears on RH (`docs/08`). The reserved word is not used.

```huntspec
id: r_c7f779
question: Does the Cohn-Elkies-style certificate LP for T1 have value below Shq(1/2) = 0.06750841, above it, or is it unresolvable at this cost?
frontier: V >= 0.05716501969327026 (the 2*pi lattice is dual-feasible); route works iff V < 0.06750840786062762; run 37fb06a9 reached 0.0541015 at s_max = 200 with solver failure above
proposed_attack: replace the uniform s-grid and the piecewise-constant measure by a class whose G has an exact closed form and a 1/s^2 tail, solve by constraint generation with a posteriori dense verification, and cover the tail by the leading asymptotic comparison
dead_routes:
  - per-pair domination of the gas charge
  - separation-assuming arguments
  - Cauchy-Schwarz on the pair sum
  - band-limited Fejer certificates, short by 1.15554665 with the frequency-domain witness ghat(0.87493) = +0.0839055 (r_b9552d run 1)
  - piecewise-constant mu on a uniform s-grid, which cannot be feasible at large s because its G decays only like 1/s
required_oracles:
  - exact closed-form evaluation of G for the chosen measure class, checked against numerical quadrature
  - independent dense re-evaluation of G - f on a grid disjoint from the LP constraint grid
  - HiGHS simplex and interior-point cross-check on the same program
  - the achievability floor 0.05716501969327026 computed from the 2*pi lattice by an independent route
kill_conditions:
  - the verified LP value exceeds 0.06750841, killing the route with a witness
  - the LP value stalls below the achievability floor 0.05716502 and the class cannot be repaired
  - a produced certificate fails dense a posteriori verification of G >= f
  - the tail s > s_max is not covered by an argument
agents_may:
  - search
  - derive
  - code
  - attack
  - formalize
agents_may_not:
  - declare novelty
  - declare theorem status
  - promote their own claim
  - open or merge a pull request
```
