# Exact provenance for the xi-double-prime coefficients

## Result

The displayed `kappa=2` row in Bian Figure 10.1 does not survive independent
reconstruction. The first divergence is already

\[
C_{2,2}=-8,
\]

not `-4`. Of the first eleven entries, only `C_{2,1}=1` matches the printed
row.

This is Outcome B1. The first causal defect is visible on thesis page 71.
The exact expansion of `A(x)` contains the weights

\[
M(v_l)M(w_k).
\]

They are present in the line immediately before the application of Theorem 3,
then absent from the next displayed line and from equation (8.1). The constant
`C(v_l,w_k)` defined in equation (7.8) does not contain these weights. Equations
(9.6), (10.1), Lemma 12, Figure 10.1, and the Chapter 11 percentages inherit
that omission.

## Pinned inputs

- Audited repository state: `922884d1649999e1960cdc46c31a4ffaa25f4c6a`.
- Ji Bian thesis PDF SHA-256:
  `ec1143f4f6c83288b717cfd4cd0aa6cc620f8c68b892f510a2a8d1708f36bfb7`.
- Farmer-Gonek arXiv source archive SHA-256:
  `f6cdc7b71db06187dac655647e24312843441aa2598e41a3b53834dd1b36822f`.
- Farmer-Gonek main TeX SHA-256:
  `a3a9ac955a9c95d10d36d6b05aae05a79c6408f6e1cdcb8c14fd79f000144fb1`.

The thesis archive exposes the PDF publicly. Its original TeX attachment is
access-restricted, so the source-level audit is bounded by the PDF.

## The one-line obstruction

Put `g=zeta'/zeta`, `Dg=g'`, and `x=1/L`. Ignoring only terms lower by a
power of the height, the exact logarithmic-derivative identity gives

\[
R_2=\frac{\xi'''}{\xi''}
   =L+g+D\log\left(1+2gx+(g'+g^2)x^2\right).
\]

Therefore

\[
R_2=L-\Lambda+2(\Lambda\log)L^{-1}+O(L^{-2})
\]

as a formal Dirichlet series. Write these first two arithmetic coefficients as
`q_0=-Lambda` and `q_1=2 Lambda log`. The leading prime-number-theorem
pairing is

\[
\langle\Lambda,\Lambda\log\rangle=1.
\]

With the thesis normalization `log(x)/L=2|alpha|`,

\[
C_{2,2}
=2\bigl(\langle q_0,q_1\rangle+\langle q_1,q_0\rangle\bigr)
=2(-2-2)=-8.
\]

Bian's equation (2.21) independently exposes the same factor: for `kappa=2`,
its first term from `f'/(1+f)` is `2g'/L`. The printed `-4` cannot follow from
that equation.

## Independent exact routes

`exact_c2.py` implements three coefficient generators.

Route A starts from

\[
R_0=L-\Lambda,
\qquad
R_{j+1}=R_j+D(R_j)/R_j,
\]

and performs formal power-series inversion under Dirichlet convolution.

Route B starts from

\[
1+2gx+(g'+g^2)x^2
\]

and expands its logarithmic derivative by separate operator-word code. It does
not call Route A's expression or series helpers.

Route C uses the independently derived rational generating object

\[
Q(z)=-\Lambda+
\frac{2(\Lambda\log)z-
[2\Lambda*(\Lambda\log)+\Lambda\log^2]z^2}
{(1-\Lambda z)^2+(\Lambda\log)z^2}
\]

and expands its quadratic denominator by a closed binomial formula. It shares
neither series-inversion implementation.

The mean-square constant retains the original two literal checks through index
11: relative permutations and subset-permanent dynamic programming. Two
additional implementations scale to index 40: a column-type count recurrence
and an independent enumeration of 3-by-3 contingency tables. For basis words
`beta=(b_1,...,b_r)` and `delta=(d_1,...,d_r)`, both calculate

\[
K(\beta,\delta)=
\frac{\displaystyle\sum_{\pi\in S_r}
\prod_{j=1}^r(b_j+d_{\pi(j)}+1)!}
{(2r+|\beta|+|\delta|-1)!}.
\]

Words of unequal length pair to zero. Finally,

\[
C_{2,i}=2^{i-1}\sum_{p+q=i-1}\langle q_p,q_q\rangle.
\]

All coefficient routes agree exactly through index 40. Both scalable
mean-square routes agree there, and both literal routes agree through index 11.
`C2_EXTENDED.json` is the authoritative 40-entry fixture. The infinite
structure and tail are in `CORRECTED-F2.md`.

## Level-1 normalization control

Running Route A for one derivative reproduces the Farmer-Gonek series exactly:

\[
1,-4,4,0,\frac43,0,\frac{16}{45},0,
\frac8{105},0,\frac{64}{4725}.
\]

This is the same eleven-entry `kappa=1` row printed by Bian. Thus the level-2
disagreement is not caused by the definition of `L`, the factor `2|alpha|`, or
the form-factor normalization.

## Exact table

| i | Route A | Route B | Bian Figure 10.1 | Status |
|---:|---:|---:|---:|:---|
| 1 | 1 | 1 | 1 | MATCH |
| 2 | -8 | -8 | -4 | MISMATCH |
| 3 | 24 | 24 | 4 | MISMATCH |
| 4 | -32 | -32 | -16 | MISMATCH |
| 5 | 64/3 | 64/3 | 28 | MISMATCH |
| 6 | -64/3 | -64/3 | 16 | MISMATCH |
| 7 | 1216/45 | 1216/45 | 544/45 | MISMATCH |
| 8 | -256/15 | -256/15 | -512/45 | MISMATCH |
| 9 | 1088/63 | 1088/63 | -104/63 | MISMATCH |
| 10 | -11776/945 | -11776/945 | -416/945 | MISMATCH |
| 11 | 42496/4725 | 42496/4725 | 6688/1575 | MISMATCH |

`C2_EXACT.json` is the historical comparison fixture through index 11.
`C2_EXTENDED.json` is the corrected machine-readable fixture through index 40.
Rational strings, not decimal renderings, are the stored values.

## Consequence for the historical calculation

The Chapter 11 problem is upstream of its endpoint arithmetic. The printed
higher-derivative coefficient rows were generated from equation (10.1) after
the multiplicity weights had disappeared. They are not coefficients of the
independently reconstructed `xi'''/xi''` arithmetic object.

The historical `0.9544` and `0.9774` remain quarantined. They are not inputs,
targets, normalization controls, or expected oracle outputs.

## Reproduction

```bash
.venv/bin/python hunts/higher_xi/exact_c2.py --max-index 40
.venv/bin/python -m pytest -q hunts/higher_xi/test_higher_xi.py
```
