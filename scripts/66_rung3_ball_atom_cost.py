"""Which ball obligations the kernel can actually discharge, and at what cost.

Rung 3's history has two measured dead ends about *evaluation*, both found the
same way, by trying it rather than estimating it:

* HANDOFF negative result #2 (rectangles): one `dirichletTermBox` literal
  equality took ~8 min and then exceeded simp's step limit.
* This script's finding (balls): asking `norm_num` to unfold a whole
  `dirichletTermBallB` is worse still, **stack overflow after 376 s**.

The first diagnosis was wrong, and the correction is recorded here rather than
swept.  This docstring originally blamed `Nat.sqrt` for not reducing under
`norm_num`; in fact Mathlib has an extension for exactly that
(`Mathlib.Tactic.NormNum.NatSqrt`, verified directly on the 127-bit literal from
the failing goal).  The real blocker was the `Int.toNat` inside `sqrtUpperQ`
hiding the literal from the extension, with `Int.toNat` in the simp set the
same `mulA` atom discharges in ~6.5 s.

The design decision survives its own corrected diagnosis, but as a cost choice
rather than an impossibility: ~6.5 s per computed-sqrt atom against ~0.55 s per
literal-bounds atom is ~12x, across ~78k obligations.  So the generator emits
`ComplexBall.mul` with the modulus bounds supplied as literals, discharging
`norm_centre_le`'s one rational inequality per product, the design
`ZetaLean.Ball` was built for ("moduli are arguments, not computations").  The
recursive tower (`expCrB`, `sqIter`, `powIB`, `expSumCB`, `mulA`) remains the
soundness story, not the evaluated one.

Measured here, 10 realistic composite-chain atoms over 64-bit-coarsened literals:
**8 s wall including a ~2.5 s import baseline, so ~0.55 s per atom**, which is
the same rate the rectangle layer measured for its composite step.

Run: .venv/bin/python scripts/66_rung3_ball_atom_cost.py [--atoms N] [--out FILE]
Then compile the emitted file with `lean` from the `lean/` directory.
"""
from __future__ import annotations

import argparse
import importlib
import sys
from fractions import Fraction as F
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / "scripts"))

ball = importlib.import_module("63_rung3_ball_mirror")

NLOG, NEXP, P, KE = 32, 20, 64, 10
ORACLE = (F(808517, 10 ** 6), F(85699348, 10 ** 6))


def q(x) -> str:
    x = F(x)
    return (f"({x.numerator} : ℚ)" if x.denominator == 1
            else f"({x.numerator}/{x.denominator} : ℚ)")


def lit(b) -> str:
    return f"(⟨{q(b.cre)}, {q(b.cim)}, {q(b.rad)}⟩ : ComplexBall)"


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--atoms", type=int, default=10)
    ap.add_argument("--out", default=None)
    args = ap.parse_args()

    S = ball.C(*ORACLE, 0)
    primes = [2, 3, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53]
    pairs = [(a, b) for i, a in enumerate(primes) for b in primes[i + 1:]]

    out = ["import ZetaLean.BallTerm",
           "open ZetaLean ZetaLean.ComplexBall",
           "set_option maxRecDepth 100000",
           "",
           "-- Each atom: one coarsened ball product over 64-bit-coarsened inputs,",
           "-- with the two modulus bounds supplied as literals.  This is the shape",
           "-- a generated certificate emits; `mulA` is not used because computing",
           "-- its sqrt bounds in-tactic costs ~12x more (see module docstring).",
           ""]
    for i, (a, b) in enumerate(pairs[:args.atoms]):
        A = ball.dirichletTermBox2(NLOG, NEXP, P, a.bit_length(), KE, a, S)
        B = ball.dirichletTermBox2(NLOG, NEXP, P, b.bit_length(), KE, b, S)
        prod = ball.ccoarsen(P, ball.cmul(A, B))
        uA, uB = ball._absc_upper(A), ball._absc_upper(B)
        out += [f"def A{i} : ComplexBall := {lit(A)}",
                f"def B{i} : ComplexBall := {lit(B)}",
                f"example : coarsenB {P} (ComplexBall.mul A{i} B{i} {q(uA)} {q(uB)})",
                f"    = {lit(prod)} := by",
                f"  norm_num [A{i}, B{i}, coarsenB, recentre, widenRad, ceilP,",
                "    ComplexBall.mul]",
                ""]

    text = "\n".join(out)
    if args.out:
        Path(args.out).write_text(text)
        print(f"wrote {args.out} ({args.atoms} atoms)")
    else:
        print(text)


if __name__ == "__main__":
    main()
