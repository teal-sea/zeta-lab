# Department: `zeta`

The Riemann zeta function and RH — department #1, and the worked example every
later department should copy.

**Declared in** `harness/departments/zeta_department.py`.
**Audited by** `tests/test_department_conformance.py`.

## What it studies

The classical machinery, implemented at arbitrary precision, with every
identity exposed as a measured *defect* rather than assumed: θ and modularity,
the functional equation, Hardy's Z and sign changes, the explicit formula, GUE
statistics, heat flow on Ξ and the de Bruijn–Newman constant, Weil positivity,
Li's criterion and Jensen hyperbolicity, the four equivalence faces, curves
over 𝔽_p (the RH that is a theorem), and the Davenport–Heilbronn
counterexample.

Modules: `zeta.core`, `zeta.zeros`, `zeta.explicit`, `zeta.statistics`,
`zeta.heatflow`, `zeta.weil`, `zeta.epstein`, `zeta.rigor`, `zeta.li`,
`zeta.criteria`, `zeta.moments`, `zeta.finitefield`.

## What is entitled to kill a claim here

| Role | Members | Source |
|---|---|---|
| **Rivals** (3) | Davenport–Heilbronn; Epstein ζ of the forms (2,1,3) and (1,1,6), discriminant −23 | `zeta.epstein` |
| **Decoys** (2) | non-prime replacement of matched density; permutation of the same primes | `zeta.spectral_gate` |
| **Surrogates** (3) | log-correlated field; full random Euler product; CUE | `zeta.surrogate` |
| **Lesions** (3) | zero quadruples at ½ ± δ ± 40i, for δ = 0.1, 0.01, 0.001 | `zeta.detectors` |

Each rival satisfies a Riemann-type functional equation, has real Dirichlet
coefficients and a real Hardy-style Z, and violates RH. Each is assembled from
legitimate Euler products but has no scalar Euler product of its own, because
linear combination destroys primitive multiplicative structure while preserving
the functional equation. That is where they part from ζ, and it is the only
place a claim can hold on to.

The two decoys are sharp only as a pair: a construction must react to *which*
places are present and ignore *what order* they arrive in.

## The calibration

The department declares two claims whose verdicts are already derived in
`zeta/epstein.py`, and the conformance test re-runs both rather than trusting
the labels:

| Claim | Expected | Why |
|---|---|---|
| `claim_functional_equation` | **killed** | true of ζ *and* of every rival; a symmetry shared with functions that violate RH cannot be why RH holds |
| `claim_multiplicativity` | **distinguishes** | the fingerprint of an Euler product; false for every rival |

Together they pin the battery in both directions. A referee that has only ever
said "no" has not been shown to work.

## Where to start

- Learn the mathematics: [learn.md](learn.md)
- Attack a claim of your own: [refute.md](refute.md)
- The certified arm: [certify.md](certify.md)
