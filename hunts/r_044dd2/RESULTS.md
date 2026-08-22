# Results

**Status: exact support census settled; algebraic sieve open.** No 8x3 branch
has been closed and no complex witness has been found.

## Result 1: the inherited support layer closes zero of 31 branches

Every target-matching orbit has a support on the 252 aggregate edge entries
that satisfies all five inherited necessities:

1. every monochromatic equation has at least one supported matching;
2. no non-target equation has exactly one supported matching;
3. every root-colour pair has a star anchor;
4. every two-colour pencil satisfies the proved support dichotomy;
5. every full colour column has an anchor.

The optimizer returned 31 of 31 survivors.  A separate implementation replayed
all 6,561 colourings and every structural condition for every support, or
203,391 branch-colouring checks.  It found zero failures.

Support sizes range from 76 to 132 of the 252 entries, with median 118 and
mean 112.71.  The full run consumed 2,420.05 solver-seconds.  Orbit 18 is the
sparsest returned branch and is therefore the first algebraic target.

This is a clean negative result for the support-only route.  It does not say
that any survivor admits complex weights.

## Result 2: three successive orbit-18 supports have exact contradictions

For a support torus, a zero binomial

`x^a + x^b = 0`

gives the signed lattice relation `x^(a-b) = -1`.  If an odd integer
combination of these relations equals the exponent difference of two terms in
a zero trinomial, those terms cancel.  The remaining supported monomial would
then equal zero, impossible because every variable in that monomial is
nonzero on the support torus.

The sieve excluded three successive orbit-18 survivors:

| support | active entries | unique zero-binomial relations | zero trinomials | certificate l1 |
|---:|---:|---:|---:|---:|
| 1 | 76 | 81 | 771 | 1 |
| 2 | 113 | 240 | 792 | 3 |
| 3 | 133 | 42 | 294 | 1 |

`audit_laurent.py` independently verifies the exact binomial and trinomial
supports, the integer exponent identity, odd sign parity, and the nonzero
forced monomial.  All three certificates pass.

## Scope correction to Hunt #71

The 31 orbits classify the choice of one supported monochromatic perfect
matching in each colour.  They do **not** quotient the complete system of
6,561 equations in 252 variables.  Hunt #71's statement that they directly
reduce the full polynomial system to 31 representatives is withdrawn.  Their
valid role is as an exhaustive outer branch cover.

## Knownness and provenance

The five support necessities and signed-Laurent architecture are inherited
from `algal/krenn-gu-6x3-certificate` at commit
`c04696e515e0c02be140353fb52ea60c62e827b1`.  Zeta Lab's 8x3 implementation,
lazy branch census, and independent replay are separate code paths.  The
active public repository `YesterdaysLemon/krenn-gu-research` was checked before
this run; no novelty claim is made here.

## Reproduce

```bash
uv pip install --python .venv/bin/python -r hunts/r_044dd2/requirements-solver.txt
.venv/bin/python hunts/r_044dd2/audit.py \
  hunts/r_044dd2/artifacts/orbit18-support-01.json
.venv/bin/python hunts/r_044dd2/audit_laurent.py \
  hunts/r_044dd2/artifacts/orbit18-support-01.json \
  hunts/r_044dd2/artifacts/orbit18-laurent-01.json
```

To request the next support while excluding all three verified local
patterns:

```bash
.venv/bin/python hunts/r_044dd2/support_frontier.py --orbit 18 \
  --seconds 60 --max-rounds 10 --cuts-per-round 0 --optimize-rounds 1 \
  --pattern-cut hunts/r_044dd2/artifacts/orbit18-laurent-01.json \
  --pattern-cut hunts/r_044dd2/artifacts/orbit18-laurent-02.json \
  --pattern-cut hunts/r_044dd2/artifacts/orbit18-laurent-03.json
```

The next frontier is to continue this exact no-good loop, symmetry-close each
certificate under the orbit-18 stabilizer, and measure whether the branch
closes or reaches supports requiring stronger ideal-membership certificates.
