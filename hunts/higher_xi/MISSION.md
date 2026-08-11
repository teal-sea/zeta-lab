# MISSION: higher derivatives of xi

## Objective

Attack the open higher-derivative form-factor problem left by Ji Bian's 2008
thesis and exposed by the August 2026 rank-trace paper.

The Chapter 11 percentages are quarantined historical data. They may appear
only in source-forensics checks. They are never inputs, targets, priors,
normalization controls, or expected outputs.

The present obligation is to reconstruct the arithmetic coefficients of
`xi'''/xi''` from first principles, derive the corresponding form-factor
information with a controlled tail, and use completed-CUE and direct
Dirichlet recurrences only as independent falsification oracles.

`C2_PROVENANCE.md` closes the coefficient audit. It finds that thesis page 71
drops the factors `M(v_l)M(w_k)` when passing to equation (8.1). The corrected
system first diverges at `C[2,2]=-8`, not the printed `-4`.

The completed-CUE experiment uses angular derivatives of

```text
Z_U(theta) = constant * product_j sin((theta-theta_j)/2).
```

The controls are forced:

1. derivative level 0 reproduces the CUE form factor `min(alpha,1)`;
2. derivative level 1 reproduces the Farmer-Gonek-Lee closed form;
3. derivative level 2 is compared with the independently regenerated exact
   finite coefficients under identical weighted observables;
4. matrix size and sample count ladders separate finite-size error from signal.

The desired outputs, in order, are:

1. an exact coefficient provenance table and smallest obstruction;
2. a rigorous full-band tail or a quantified tail barrier;
3. independent numerical oracles for the corrected object;
4. only after the tail closes, a window-functional calculation.

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
- No historical coefficient row used outside source forensics.
- No raw characteristic-polynomial derivative substituted for the completed
  real trigonometric polynomial.

## Vocabulary and controls

This directory is exploratory. Use *exact*, *measured*, *reproduced*, and
*consistent with*. Do not use the reserved claim vocabulary banned under
`hunts/`.

Every headline number must have an exact-rational route or an independent
precision and finite-size ladder. A generated claim cannot adjudicate its own
normalization.
