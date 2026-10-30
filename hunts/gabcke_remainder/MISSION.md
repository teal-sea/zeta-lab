# Gabcke's remainder

The height cap on the kernel-checked strip proof is the order-4 Euler-Maclaurin
error bar, which grows like a power of the height. This hunt formalizes the
recorded alternative: Gabcke's explicit remainder for the Riemann-Siegel formula.

The source is Wolfgang Gabcke, *Neue Herleitung und explizite Restabschätzung
der Riemann-Siegel-Formel*, Göttingen, 1979, reissued 2015. The PDF used here
is the Göttingen file `DissGab1979.pdf` (133 pages), kept outside the
repository. The university server returned 403 to a plain fetch; the copy was
taken from the Internet Archive of that same file.

## Target

Satz 3.2.2 (b), page 55. For real `t ≥ 200` and `K ≤ 9`,

```
|R0(t)| < 0.127 t^{-3/4}     |R1(t)| < 0.053 t^{-5/4}
|R2(t)| < 0.011 t^{-7/4}     |R3(t)| < 0.031 t^{-9/4}
|R4(t)| < 0.017 t^{-11/4}    |R5(t)| < 0.061 t^{-13/4}
|R6(t)| < 0.661 t^{-15/4}    |R7(t)| < 9.2   t^{-17/4}
|R8(t)| < 130   t^{-19/4}    |R9(t)| < 1837  t^{-21/4}
```

and `|R10(t)| < 25966 t^{-23/4}`. For `K ≤ 4` Gabcke calls the bounds optimal.
`R_K` is the remainder after `K` correction terms in formula (6) of the
introduction. The first payoff is `K = 0`: one main sum of length about
`sqrt(t)`, plus a remainder that does not grow like a power of `t`.

## First check

Satz 2.1.1's recursion for `λ_n` matches the seven values printed on pages
19–20. Lean's kernel accepts that match (`lean/Coefficients.lean`,
`lambda_printed` and `lambda_divides`) with no axioms. That is not the
remainder bound.

```huntspec
id: gabcke_remainder
question: Can Lean prove Gabcke's explicit bounds on the first 11 Riemann-Siegel remainders for every real t at least 200, with zero sorry and only the standard axioms?
frontier: the order-4 Euler-Maclaurin box dies as a power of t; at height 1000 the corner needs about 990 terms and the code stops at 200; Gabcke's remainder is unformalized
proposed_attack: formalize Satz 3.2.2 (b), starting from the coefficient recursion in Satz 2.1.1, then the remainder integral
dead_routes:
  - raising the Euler-Maclaurin order, which only softens the power from 8/7 to 12/11
  - copying the height-100 generator to a higher height
  - quoting Gabcke's inequalities as axioms
required_oracles:
  - Lean 4 kernel at the pinned toolchain, zero sorry, printed axioms
  - the Göttingen 2015 PDF of Gabcke's thesis, checked against the printed lambda values
kill_conditions:
  - the coefficient recursion disagrees with the values printed in Satz 2.1.1
  - a stated bound fails a numerical check at a height where the main sum is known
  - the kernel accepts the bound only by taking an external computation as an axiom
agents_may:
  - derive
  - code
  - formalize
agents_may_not:
  - declare the remainder proved before the kernel accepts it
  - declare a higher finite height proved by this hunt
  - treat a matched recursion as the remainder bound
```
