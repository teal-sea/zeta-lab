# Results: the rule the core never learned

**2026-09-10. Grade: measured**, against an oracle the routine shares no code
with. Nothing here bears on RH (`docs/08`): it is a measurement of an
implementation, and the mathematics it uses is classical.

## 1. The verdict

    zeta.epstein.epstein_zeta at dps 15, form (1,1,4), Re s = 5
      t = 40    15.6 correct digits
      t = 60     3.1 correct digits
      t = 80     0   correct digits, relative error 1.0
      t = 120    0   correct digits, relative error 2.3e+36

    the routine raises nothing, warns nothing, and its docstring says nothing

The tree already knew why. `hunts/gate5_p6_c/probe.py` derives the mechanism in
a comment and writes the constant down as `GUARD_PER_UNIT_HEIGHT = 0.6822`;
`hunts/dps_cap` (#113) measured the cost at one point and got the interfaces to
stop clamping a caller's `dps`. Neither reached `zeta/epstein.py`, which still
accepts any precision at any height and returns a number.

What this hunt adds is the surface rather than the point, an exactly derived
loss in place of the leading constant, a guard with the faults that fire it,
and an answer to the question `hunts/dps_cap/reach_check.py` left open.

## 2. The oracle

At `Re s = 5` the defining sum converges absolutely, so it can be summed
directly. Grouping lattice points by the value they represent turns the double
sum into one sum over `q <= qmax`, and the truncation is bounded by the
measured point count: with `qmax = 20000` the bound is about `1e-17`, and the
achieved floor over the whole surface is 17.6 correct digits.

`epstein_completed` reaches the same value through a split Mellin transform and
the incomplete gamma, so the two share the definition and nothing else.

## 3. The surface

Correct digits, form `(1,1,4)`, `Re s = 5`, against that oracle:

| t \ dps | 15 | 20 | 30 | 50 | 80 |
|---:|---:|---:|---:|---:|---:|
| 10 | 16.0 | 16.0 | 16.0 | 16.0 | 16.0 |
| 20 | 16.5 | 16.5 | 16.5 | 16.5 | 16.5 |
| 40 | 15.6 | 16.1 | 16.1 | 16.1 | 16.1 |
| 60 | **3.1** | 8.2 | 16.1 | 16.1 | 16.1 |
| 80 | **0** | **0** | 5.1 | 16.3 | 16.3 |
| 100 | **0** | **0** | **0** | 12.4 | 16.1 |
| 120 | **0** | **0** | **0** | **0** | 16.5 |
| 160 | **0** | **0** | **0** | **0** | 2.4 |

The form `(2,1,3)` gives the same picture shifted by about a digit and a half,
and `(1,0,1)` agrees where it was reached. 158 cells in
`artifacts/surface.json`; the ones inside the transition band were chosen by
the law and run separately (`boundary.py`), because the rectangular grid put
only twelve cells where a prediction could be tested and the rest at the
oracle's ceiling or flat at zero.

## 4. The loss, derived rather than fitted

The first model here took the recorded leading constant and added the `sigma`
term:

    L(sigma, t) = 0.68219 t - (sigma - 1/2) log10 t - 0.399

Residual over the 49 transition cells: mean `+0.13`, rms `0.86`. **But the
residuals were not noise.** They averaged `+0.85` for `(1,1,4)` and `-0.75` for
`(2,1,3)`, a systematic 1.6-digit gap between two forms at the same `sigma` and
`t`. A per-subject offset means a missing term, so the model was re-derived.

`epstein_completed` forms `first + second/sqrt(d) + 1/(sqrt(d)(s-1)) - 1/s`,
whose last two terms are about `1/t`, and returns `d^{s/2}` times it. Since
`Lambda_Q(s) = (sqrt(d)/pi)^s Gamma(s) zeta_Q(s)`,

    |mellin| = |Lambda_Q(s)| d^{-sigma/2} = pi^{-sigma} |Gamma(s)| |zeta_Q(s)|,

the discriminant cancels, and the digits lost are

    L(sigma, t, Q) = -log10 t + sigma log10 pi - log10|Gamma(s)| - log10|zeta_Q(s)|.

No asymptotic and no fitted constant: `|Gamma|` from mpmath, `|zeta_Q|` from
the oracle. Substituting Stirling recovers the recorded `0.68219 t` and shows
what the first model dropped, including the size of `zeta_Q` itself, which is
exactly where the per-form offset lived: `(1,1,4)` represents 1 and `(2,1,3)`
represents 2, so at `sigma = 5` their `log10|zeta_Q|` differ by about 1.5.

| model | residual mean by form | rms |
|---|---|---:|
| leading constant plus the `sigma` term | `+0.93 / +0.85 / -0.75` | 0.86 |
| derived exactly | `+0.93 / +1.09 / +1.07` | 0.36 about one constant |

**The per-form bias is gone.** What is left is a single offset of `+1.068`
digits, uniform over three forms and heights 40 to 160, with rms `0.357` about
it and worst deviation `+1.22`. That is what a correct derivation should leave:
the model assumed the largest quantity formed is exactly `1/t` and it is a
little smaller, so the routine carries about one digit more than the bound
says. The guard below keeps the unfitted version, which errs safe.

## 5. The guard, and the faults that fire it

`zeta/epstein.py` is outside what a hunt may write, so `guard.py` is a
reference implementation with its own planted-fault ladder rather than a landed
change. The rule refuses instead of returning:

    required dps for ten correct digits
       t     sigma = 0.5   sigma = 3   sigma = 5
      20            15          15          15
      40            17          15          15
      60            31          27          23
    85.7            49          44          40
     100            58          53          49
     160            99          94          89
     240           154         148         143

`sigma = 0.5` is the worst case and it is the line `Z_epstein` and
`count_zeros_box` work on.

The ladder, all six rungs passing:

- refuses `0.8 + 85.7i` at `dps 20`, the exact case `hunts/dps_cap` measured;
- the unguarded routine really is wrong there and at `t = 120, dps = 15`
  (relative error `2.3e+36`, measured against the oracle in the same run);
- refuses that call;
- **does not** refuse `t = 20` at `dps 30`, and the value it returns is right to
  `2.5e-19`;
- needs more precision on the critical line than at `sigma = 5` at the same
  height (58 against 49);
- and, with the cancellation constant set to zero, **stops firing**, which is
  what makes the other rungs mean anything.

## 6. What `hunts/dps_cap/reach_check.py` left open

That file asks whether the precision cap costs a wrong answer or a refusal, and
records that neither run returned: the uncapped comparison stopped after 30
minutes, the capped path after 25. It offers a hypothesis and says plainly it
did not test it, that `_edge_variation` subdivides without converging when the
samples carry no correct digits.

It is testable without running the thing that does not return.
`_arg_variation` accepts a segment when the endpoint arguments differ by less
than `pi/3` and otherwise bisects, to a depth limit of 45 at which **it returns
the principal value rather than raising**. So the branching factor is
`2(1 - p)` with `p` the acceptance probability, and `p` costs two evaluations
per segment to measure. When the phase is noise, `p = 1/3` by symmetry, the
branching factor is `4/3`, and one segment costs about `(4/3)^45 = 4e5`
evaluations at roughly two seconds each.

`why_it_hangs.py` measures `p` at both precisions. Its numbers are in
`artifacts/why_it_hangs.json`.

The consequence for the open question is structural and does not depend on the
measured `p`: because the depth limit returns a value instead of raising, the
cap cannot cost a refusal. It costs either a wrong count or a run that does not
finish, and which one you get is decided by the depth limit rather than by any
check. `count_zeros_box`'s integrality test cannot separate them, for the reason
`tests/test_interface_dps_is_honoured.py` already gives: noise winds to an
integer as readily as signal does.

## 7. The doors

1. **Active constraint.** Working precision against height, binding
   everywhere above `t` about 40 at default precisions. Its shadow price is
   steep and known exactly: one decimal digit of `dps` buys one decimal digit of
   answer, and the requirement grows linearly at `0.682` digits per unit height.
2. **Frozen-constant inventory.**
   - **`_GUARD = 10`, applied twice.** `epstein_zeta` opens `workdps(dps + 10)`
     and hands `mp.dps` to `epstein_completed`, which opens another. A caller
     asking for `dps` gets `dps + 20`, which is not documented anywhere and is
     load-bearing in every number above. Relaxing it trades time for digits
     linearly, with no other structure.
   - **The Mellin split at `t = 1`.** Every term above comes from that choice.
     Splitting at a `t` chosen per `s` is the one change that could reduce the
     cancellation rather than pay for it, and nothing in the tree has tried it.
     That is the door with real trade shape: it costs a derivation and buys back
     digits that are currently bought with precision.
   - **The depth limit 45 in `_arg_variation`**, which decides whether a bad
     contour miscounts or hangs, and is the only thing standing between the two.
3. **Information class.** Everything here reads the same data the routine
   already forms; nothing needs a new mathematical input. The guard is a
   arithmetic on quantities the routine has in hand, and the Mellin-split door
   is a re-derivation of an existing representation. That is the cheapest kind
   of door there is, and it is open because nobody wrote the rule down where the
   code could read it.
