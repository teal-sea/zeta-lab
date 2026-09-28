# Department: `zeta`

The Riemann zeta function and RH, department #1, and the worked example every
later department should copy.

**Declared in** `harness/departments/zeta_department.py`.
**Audited by** `tests/test_department_conformance.py`.

## What it studies

The classical machinery, implemented at arbitrary precision, with every
identity exposed as a measured *defect* rather than assumed: θ and modularity,
the functional equation, Hardy's Z and sign changes, the explicit formula, GUE
statistics, heat flow on Ξ and the de Bruijn–Newman constant, Weil positivity,
Li's criterion and Jensen hyperbolicity, the four equivalence faces, and the
Davenport–Heilbronn counterexample. Curves over 𝔽_p, the RH that is a
theorem, are [department #2](finitefield.md).

Modules: `zeta.core`, `zeta.zeros`, `zeta.explicit`, `zeta.statistics`,
`zeta.heatflow`, `zeta.weil`, `zeta.epstein`, `zeta.rigor`, `zeta.li`,
`zeta.criteria`, `zeta.moments`.

## What can refute a claim here

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
| `claim_functional_equation` | **rejected** | true of ζ *and* of every rival; a symmetry shared with functions that violate RH cannot be why RH holds |
| `claim_multiplicativity` | **distinguishes** | the fingerprint of an Euler product; false for every rival *in this department's list* |

Together they pin the battery in both directions. A referee that has only ever
said "no" has not been shown to work.

**One row above is narrower than it reads, and the qualifier is load-bearing.**
`zeta.epstein.battery` gained a third rival on 2026-08-21, the symmetric
shifted product `W_a(s) = ζ(s+a)ζ(s−a)`, which *does* have a scalar Euler
product and still has zeros off its own critical line. Against the live rival
set `claim_multiplicativity` therefore no longer distinguishes; against this
department's list, which predates the addition and is not being extended
(`harness/VERDICT.md`), it still does. Both readings are pinned in
`tests/test_epstein.py`. `docs/09` §5.1 has the construction and the scope
caveat, which matters: the shifted product is outside the Selberg class, so a
claim it shares is shown to be blind to a shift rather than shown to be
irrelevant.

### One instrument that does *not* qualify, and why

`zeta.factorization.factorization_defect` is Gate 4 made into a number: D(f) = 0
exactly when f has an Euler product, which looks like an ideal third reference
claim. It is not one, and the battery is what showed that.

Measured across the four subjects at n_max = 60:

| Subject | a₁ | D |
|---|---|---|
| ζ | 1 | 1.03e−32 |
| Davenport–Heilbronn | 1 | 0.993 |
| Epstein (2,1,3) | **0** | *undefined, raises* |
| Epstein (1,1,6) | 2 | 1.76 |

The form 2x² + xy + 3y² does not represent 1, so that Epstein series has
a₁ = 0 and the logarithmic-derivative recursion the statistic is built on has
no normalisation to divide by. The rival did not answer, so the claim has not
been shown to exclude it: `run_battery` records the exception in `errors` and
`distinguishes` stays `False`.

That is the safe failure mode working as specified. A verdict that had quietly
counted a crashed rival as refuted would be the most flattering possible bug,
and it would have promoted D from "works on three of four subjects" to "the
decision procedure for Gate 4".

## Where to start

- Learn the mathematics: [learn.md](learn.md)
- Attack a claim of your own: [refute.md](refute.md)
- The certified arm: [certify.md](certify.md)
