# CLEAN KILL REPORT: 0.672529

## Disposition

The `0.672529` candidate is withdrawn. Its first required algebraic lemma is
false. The failure occurs before taper, truncation, census, bootstrap, or LP
questions can affect the result.

The surviving unconditional statement is the pinned upstream Theorem D bound
`0.6725007037...`. No strict improvement survives from the mechanism audited
here.

## Pinned inputs

- Local repository state audited:
  `add40513fb1919ea4d00f87bdb61b5b433f7801d`.
- Paper: *More than two thirds of the zeros of the Riemann zeta function lie
  on the critical line*, PDF SHA-256
  `6792988e6cd0e17690621ce898abd5d534f98407741bc7cb14bbe7d07c77d72f`.
- Lean companion: `anthropics/zeta-23-lean` at
  `3635e74826a4c1fcece7d1cd2b6fa75e43a00510`, tag `v1.0`.
- Pinned upstream Mathlib:
  `51e6992efd06126df61a496bebf8f49482a4e129`.

The decisive upstream definitions are `Zeta23/Defs.lean:298-305` and
`Zeta23/ZeroSide.lean:314-379` at that commit.

## First false statement

The candidate asserted

```text
tr(P1 Q') >= 0
```

in `cg_transplant.py`, and justified it by claiming that every conjugate-class
cross block was a sum of squared moduli. The old `blockpos.py` appeared to
support this claim.

The upstream zero-side summand is instead

```text
m u_z u_z^T
```

with transpose, not conjugate transpose. For an off-line pair with
`u_z = a + ib`, its contribution is

```text
m (u_z u_z^T + conjugate(u_z) conjugate(u_z)^T)
  = 2m (a a^T - b b^T).
```

It is a hyperbolic block. `blockpos.py` formerly constructed
`u_z u_z*`, a positive-semidefinite matrix that is not the upstream matrix.
Its scan could not find the sign error because the implemented block formula
was a squared modulus for every input.

Writing `B(z,w) = u_z^T u_w`, the correct class interactions are

```text
on/on:    m_x m_y B(x,y)^2
on/off:   2 m_x m_z Re(B(x,z)^2)
off/off:  2 m_z m_w Re(B(z,w)^2 + B(z,conjugate(w))^2).
```

Only the on/on line is automatically nonnegative.

## Smallest exact obstruction

In one matrix dimension, take one simple on-line vector `u_x = 1` and one
off-line conjugate pair `u_z = i`, `u_conjugate(z) = -i`, all with multiplicity
one. Then

```text
P1 = [1]
Q' = [i^2 + (-i)^2] = [-2]
tr(P1 Q') = -2.
```

This is Gaussian-integer arithmetic and directly negates the first false
statement.

The proposed final additive inequality also fails under the same abstract
block data. With five unit on-line labels and the pair above,

```text
P1 = 5
Q' = -2
cross11 = 5^2 - 5 = 20
||P1 + Q'||_F^2 = 9
claimed right side = 4*3 - 3*5 - 4*1 + 20 = 13.
```

Thus the proposed strengthening demands `9 >= 13`.

## Why no weaker strict improvement survives

Both the Cheer-Goldston bucket value `0.6725124` and the gap-LP value near
`0.672529` enter the upstream count only through the discarded positive
on-line cross mass. Once the off-line interaction can be negative, that mass
cannot be added to the rank-trace inequality from the pinned upstream
hypotheses. The upstream paper explicitly retains only rank and positive index
for these hyperbolic blocks.

Controlling the negative interaction would require an additional unconditional
input about off-line blocks. That is a different mechanism, so it is outside
this closure run. The exact gap floors remain facts about an ordered real
configuration problem, but they no longer imply a zeta-zero improvement.

## Permanent controls

- `clean_kill.py`: deterministic Gaussian-integer checker.
- `blockpos.py`: corrected to use transpose zero-side summands.
- `tests/test_frontier_math_clean_kill.py`: exact obstruction plus a finite
  Gabor-kernel negative-block regression.
- `lean/ZetaLean/FrontierMathObstruction.lean`: kernel-checked obstruction.

Artifact SHA-256 values:

```text
323e8ee0c393d041403cb4a71a0f864f4c98ea48c2196ac5eb5a1561f93fe7dc  clean_kill.py
dfe22d7a90e4103a0568704d4fdc7e2702f36ee7d89d57203409cdf889939541  FrontierMathObstruction.lean
ae2f4331c5684fd7590e991c40274ca7ec77cf5649df147016df29ad89dece3e  test_frontier_math_clean_kill.py
```

Reproduce from the repository root:

```bash
.venv/bin/python hunts/frontier_math/clean_kill.py
.venv/bin/python -m pytest -q -o addopts='' tests/test_frontier_math_clean_kill.py
cd lean && PATH="$HOME/.elan/bin:$PATH" lake build ZetaLean.FrontierMathObstruction
PATH="$HOME/.elan/bin:$PATH" lake env lean PrintFrontierMathObstruction.lean
```

Expected exact checker output:

```text
correct_off_pair: -2
old_instrument_off_pair: 2
cross_trace: -2
frobenius_sq: 9
proposed_rhs: 13
defect: -4
```

The axiom audit reports only Lean's standard `propext`, `Classical.choice`,
and `Quot.sound`; the final integer inequality does not use
`Classical.choice`.
