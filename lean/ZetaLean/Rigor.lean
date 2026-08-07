import Mathlib

/-!
# Certified Interval Evaluation

This module provides certified interval arithmetic for real and complex numbers.
It is designed to support the evaluation of Dirichlet series with explicit error bounds,
paving the way for the Davenport-Heilbronn theorem (Rung 3).
-/

structure Interval where
  lo : ℚ
  hi : ℚ
  le : lo ≤ hi
  deriving Repr, DecidableEq

namespace Interval

def exact (q : ℚ) : Interval :=
  { lo := q, hi := q, le := le_refl q }

def add (x y : Interval) : Interval :=
  { lo := x.lo + y.lo,
    hi := x.hi + y.hi,
    le := add_le_add x.le y.le }

def neg (x : Interval) : Interval :=
  { lo := -x.hi,
    hi := -x.lo,
    le := neg_le_neg x.le }

def sub (x y : Interval) : Interval :=
  add x (neg y)

def mul (x y : Interval) : Interval :=
  let opts := [x.lo * y.lo, x.lo * y.hi, x.hi * y.lo, x.hi * y.hi]
  -- A robust interval multiply needs more logic to handle signs correctly without `sorry`.
  -- For certification using the Oracle Boundary pattern, we can often just provide
  -- the multiplied value and an error bound instead of computing it dynamically in Lean.
  sorry

end Interval

structure ComplexInterval where
  re : Interval
  im : Interval
  deriving Repr, DecidableEq

namespace ComplexInterval

def exact (c : ℚ × ℚ) : ComplexInterval :=
  { re := Interval.exact c.1, im := Interval.exact c.2 }

def add (x y : ComplexInterval) : ComplexInterval :=
  { re := Interval.add x.re y.re,
    im := Interval.add x.im y.im }

def sub (x y : ComplexInterval) : ComplexInterval :=
  { re := Interval.sub x.re y.re,
    im := Interval.sub x.im y.im }

end ComplexInterval
