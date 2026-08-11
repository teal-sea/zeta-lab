# Resolution of the 2008 higher-derivative discrepancy

## Disposition

The `0.9544` and `0.9774` proportions on page 93 of Ji Bian's 2008 thesis are
chapter-11 calculation errors. They are not outputs of equation (11.5) applied
to either coefficient row printed in the thesis.

This resolves the internal discrepancy. It does not determine whether the
Figure 10.1 coefficients themselves are mathematically correct, and it does
not supply replacement positive proportions.

## Pinned source

Ji Bian, *The Pair Correlation of Zeros of Derivatives of Riemann's
Xi-Function*, University of Rochester PhD thesis, 2008:

```text
https://urresearch.rochester.edu/institutionalPublicationPublicView.action?institutionalItemId=5500
PDF SHA-256:
ec1143f4f6c83288b717cfd4cd0aa6cc620f8c68b892f510a2a8d1708f36bfb7
```

The source repository lists one public PDF version. Its original TeX file is
restricted to repository administrators.

## Source reconstruction

Equation (11.2) integrates the triangular Fourier kernel against

```text
F_kappa(alpha) = spike + sum_i C[kappa,i] |alpha|^i.
```

For a finite coefficient row, the endpoint expression in equation (11.5) is
therefore exactly

```text
P = 1 - 2 sum_i C[kappa,i]/((i+1)(i+2)).
```

There is no missing factor in this passage. The same expression applied to the
Figure 10.1 `kappa=1` row gives

```text
348002/405405 = 0.858405791739125...,
```

which matches the Farmer-Gonek first-derivative control.

## First source defect: page 93 changes three signs

Figure 10.1 prints the `kappa=2` entries at indices 8, 9 and 10 as

```text
-512/45, -104/63, -416/945.
```

Page 93 says it is recalling Figure 10.1, but prints all three as positive.
These are distinct coefficient rows, so both must be checked.

## Fatal source defect: neither row gives the reported proportion

Using the Figure 10.1 signs gives

```text
sum_i C[2,i]/((i+1)(i+2)) = 37057/73710,
P_2 = -202/36855
    = -0.005480938814272...
```

Using the page 93 signs gives

```text
P_2 = -107714/184275
    = -0.584528557861891...
```

For `kappa=3`, where the two displayed rows have the same signs, exact
substitution gives

```text
P_3 = -10284002/1216215
    = -8.455743433521212...
```

All three values are trivial negative lower bounds. None rounds to `0.9544` or
`0.9774`.

## An unprinted tail cannot rescue the stated calculation

Suppose an omitted weighted tail `R_kappa` were silently included. Equation
(11.5) would require

```text
claimed = 1 - 2 (shown weighted sum + R_kappa).
```

The exact tails needed to obtain the reported values are

```text
R_2 = -8844103/18427500
    = -0.479940469407136...

R_3 = -11472730541/2432430000
    = -4.716571716760606...
```

Their absolute sizes are respectively

```text
95.46485684216207% and 99.76099182302386%
```

of the displayed weighted sums. Page 93 explicitly obtains its percentages by
assuming the coefficients after index 11 are negligible. A tail canceling
almost the entire displayed sum is the opposite of that assumption.

## Exact conclusion

The first local error is the three-sign mistranscription on page 93. Correcting
those signs does not repair the headline. The first fatal statement is:

> Applying equation (11.5) to the first eleven displayed coefficients gives
> `0.9544` for `kappa=2` and `0.9774` for `kappa=3`.

It does not. The exact outputs are the negative values above. No normalization,
rounding choice, or negligible omitted tail reconciles the sentence with the
displayed source.

The source does not publish the arithmetic worksheet that produced the two
decimals, so the particular keystroke or intermediate expression cannot be
reconstructed. The source-level diagnosis is nevertheless closed: this is a
chapter-11 arithmetic error, not an alternative interpretation of equations
(11.2) through (11.5).

## What survives

- The `kappa=1` control remains consistent with Farmer-Gonek.
- This audit does not adjudicate the full proof of the coefficient formula or
  the Appendix Mathematica implementation.
- The `kappa=2` and `kappa=3` percentage claims must be withdrawn.
- The first eleven coefficients alone yield no positive simplicity bound.
- Any future positive bound needs a separately justified tail, not the page 93
  negligible-tail substitution.

## Reproduction

```bash
.venv/bin/python hunts/higher_xi/bian_audit.py
.venv/bin/python -m pytest -q -o addopts='' hunts/higher_xi/test_higher_xi.py
```
