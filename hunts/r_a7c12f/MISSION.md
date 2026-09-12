# R-A7C12F: does the far-field constant `637/1000` survive at depth 1?

`hunts/frontier_math/K2-TWO-SPECIES.md` section 2 records a depth-extended
landscape table whose last row is starred as a correction:

| object | depth 1/2 (known) | depth 1 (new) |
|---|---|---|
| far constant `sup Dam*(s^2-2)/y'^2` | 0.6220 (proved <= 0.637) | **0.6636 (> 0.637)** |

and the text below it says `Wt_tail_le`'s `637/1000` does **not** survive at
depth 1. That is a proved constant reported as going invalid, rather than a
loose bound getting looser, so it is an input to every `k >= 3` pass that
raises the depth: the `k = 2` far rows live at depth `1/2` and are untouched,
but centre-centre damage lives at depth `2y <= 1`.

**Scope.** This hunt re-derives that one table row and the lemma it names. It
does not touch the other starred entry (`no_damage`'s `28/5` shrinking to
`5.3984`), it does not re-open the `k = 2` closure, and nothing here is
evidence for or against RH (`docs/08`).

**Writes only** `hunts/r_a7c12f/`, one case-log row in `hunts/README.md`, and
one appended outcome in `harness/departments/review_ledger.py`.

```huntspec
id: r_a7c12f
question: Does the far-field constant 637/1000 survive at depth 1, given that K2-TWO-SPECIES.md section 2 measures 0.6636 there?
frontier: Wt_tail_le proves Wt w <= (637/1000)/w for w = s^2-2 >= 1368; two_species.far_constant measures 0.6220 at depth 1/2 and 0.6636 at depth 1 by scanning s in [8, 400]
proposed_attack: re-derive the depth-1 far constant with ball_field.D_enclosure, which takes the depth as an interval, over the range the constant is actually asserted on rather than the range the scan uses
dead_routes:
  - bounding the depth-1 tail by |ghat| <= cosh(y/2)(1/(s+sqrt2)+1/(s-sqrt2)), which drops the cos(s/2)cos(1/sqrt2) interference and is 8x too weak at s = 400
required_oracles:
  - Arb ball arithmetic at 96 bits via python-flint, through hunts/r_a97060/ball_field.py
  - the Lean 4 source of Wt, Wt_tail_le and Qim_far_sq read as written, not as quoted
  - independent double-precision scan of the same quantity, as a cross-check on the enclosure width
kill_conditions:
  - the ball pass returns an upper bound above 637/1000 on the asserted range at depth 1
  - the enclosure is wider than the float scan by enough that the verdict is an interval artifact rather than a fact
  - the argmax of the 0.6636 scan turns out to lie inside w >= 1368 after all
agents_may:
  - search
  - derive
  - code
  - attack
agents_may_not:
  - declare novelty
  - declare theorem status
  - promote their own claim
  - edit hunts/frontier_math/
```
