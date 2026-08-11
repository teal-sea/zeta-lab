# MISSION: higher derivatives of xi

## Objective

Attack the open higher-derivative form-factor problem left by Ji Bian's 2008
thesis and exposed by the August 2026 rank-trace paper.

The first obligation is forensic: determine whether Bian's displayed exact
coefficients, equations (10.2) and (11.5), and the reported `0.9544` and
`0.9774` simplicity proportions are mutually consistent. No higher-derivative
constant may be computed until the normalization survives this audit.

That obligation is closed in `RESOLUTION-2008-DISCREPANCY.md`. Page 93 changes
three coefficient signs and its two percentages follow from neither printed
row. The fault is a chapter-11 calculation error, not a normalization variant.

If it survives, or after the precise defect is isolated, build an independent
completed-CUE experiment for the zeros of angular derivatives of

```text
Z_U(theta) = constant * product_j sin((theta-theta_j)/2).
```

The controls are forced:

1. derivative level 0 reproduces the CUE form factor `min(alpha,1)`;
2. derivative level 1 reproduces the Farmer-Gonek-Lee closed form;
3. derivative level 2 agrees with Bian's exact low-order coefficients where
   the omitted tail is numerically negligible;
4. matrix size and sample count ladders separate finite-size error from signal.

The desired outputs, in order, are:

1. an exact normalization audit and smallest obstruction or repair;
2. an independent numerical oracle for the full-band `F_2` curve;
3. only if both survive, a window-weighted tail experiment below bandwidth 1.

## Scope

This hunt may write only under `hunts/higher_xi/` and `figures/`. It may read
the rest of the repository and pinned primary sources. Changes to `zeta/`,
`lean/`, `ontology/`, `harness/`, or repo-level records require a separate
promotion decision.

The exact pinned primary source is Ji Bian, *The Pair Correlation of Zeros of
Derivatives of Riemann's Xi-Function*, University of Rochester PhD thesis,
2008, repository item 5500, downloaded PDF SHA-256
`ec1143f4f6c83288b717cfd4cd0aa6cc620f8c68b892f510a2a8d1708f36bfb7`.

## Non-goals

- No claim about RH.
- No unconditional xi-double-prime constant from Bian or CUE alone. The
  off-line zero-side algebra and prime-side asymptotic would be separate gates.
- No coefficient fitting presented as a derivation.
- No trust in the eleven-term truncation near `alpha=1`.
- No raw characteristic-polynomial derivative substituted for the completed
  real trigonometric polynomial.

## Vocabulary and controls

This directory is exploratory. Use *exact*, *measured*, *reproduced*, and
*consistent with*. Do not use the reserved claim vocabulary banned under
`hunts/`.

Every headline number must have an exact-rational route or an independent
precision and finite-size ladder. A generated claim cannot adjudicate its own
normalization.
