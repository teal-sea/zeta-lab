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

To search again while excluding all four local patterns and their four
stabilizer images:

```bash
.venv/bin/python hunts/r_044dd2/support_frontier.py --orbit 18 \
  --seconds 60 --max-rounds 10 --cuts-per-round 0 --optimize-rounds 1 \
  --pattern-cut hunts/r_044dd2/artifacts/orbit18-laurent-01.json \
  --pattern-cut hunts/r_044dd2/artifacts/orbit18-laurent-02.json \
  --pattern-cut hunts/r_044dd2/artifacts/orbit18-laurent-03.json \
  --pattern-cut hunts/r_044dd2/artifacts/orbit18-laurent-05.json \
  --pattern-cut hunts/r_044dd2/artifacts/orbit18-laurent-01-sym.json \
  --pattern-cut hunts/r_044dd2/artifacts/orbit18-laurent-02-sym.json \
  --pattern-cut hunts/r_044dd2/artifacts/orbit18-laurent-03-sym.json \
  --pattern-cut hunts/r_044dd2/artifacts/orbit18-laurent-05-sym.json \
  --output /tmp/orbit18-next.json
```

Each committed support artifact names and hashes the cuts used to generate it.
The next frontier is an exact algebraic method that can combine trinomial
relations directly, such as ideal-membership or Gröbner-style certificates.

## Result 3: a concrete blind support for the current signed-Laurent sieve

The orbit-18 stabilizer in `S8 x S3` has size 2. Applying its nonidentity
element to the four exact Laurent certificates produces four additional
replayable cuts.

The follow-up loop returned these supports:

| support | active entries | cuts loaded | unique zero-binomials | zero trinomials | certificate |
|---:|---:|---:|---:|---:|---:|
| 1 | 76 | 0 | 81 | 771 | L1=1 |
| 2 | 113 | 1 | 240 | 792 | L1=3 |
| 3 | 133 | 2 | 42 | 294 | L1=1 |
| 4 | 123 | 3 | 4 | 417 | none |
| 5 | 126 | 3 (different seed) | 60 | 621 | L1=1 |
| 6 | 132 | 4 | 26 | 873 | none |
| 7 | 138 | 8 (symmetric) | 0 | 180 | none (empty lattice) |

Support 7 passes the independent support audit, avoids all eight named and
hashed cuts, and has zero zero-binomial equations. The current sieve starts
from signed relations extracted from zero binomials, then uses those relations
to cancel two terms of a zero trinomial. Its relation lattice is therefore
empty on this support, so this implementation cannot exclude it.

This does not rule out Laurent-ideal arguments that combine trinomials
directly, exact ideal membership, Gröbner-style certificates, or another exact
contradiction. Orbit 18 remains open. No branch is closed and no complex
witness has been found.

## Audit correction

The original follow-up commit `1b1b99d` landed directly on `main` without a
pull request, CI run, or new regression tests. Its documentation also claimed
more than the evidence established. This corrective follow-up adds independent
tests for the new supports, stabilizer, symmetry images, certificate replay,
and cut provenance; removes the machine-specific path; and narrows the result
to the exact limitation measured above.

## Result 4: fixed-degree algebra reaches a measured cap-5 elimination wall

`polynomial_sieve.py` retains multi-term zero equations, removes their common
support-torus factors, and tests the product of the three monochromatic target
brackets against the fixed-degree span of monomial multiples of those
relations. A positive result is only a candidate until an explicit identity
is emitted and independently replayed.

For Support 7, the exact cap-3 and cap-4 screens both found no membership:

| relation cap | retained relations | reachable monomials | relation multiples | exact rank | residual terms |
|---:|---:|---:|---:|---:|---:|
| 3 | 180 | 5,406 | 1,569 | 523 | 4,500 |
| 4 | 755 | 96,319 | 184,997 | 59,284 | 4,216 |

These are limitations of the retained fixed-degree spans, not evidence that
Support 7 admits complex weights.

At cap 5, the exact closure completed on a one-core, 32 GiB Modal container
and produced 13,379,522 relation multiples. The lexicographic sparse modular
elimination then developed severe fill-in. Its first 1.7 million columns took
27.0 seconds, while the intervals ending at 2.7, 2.8, and 2.9 million columns
took 72.1, 135.6, and 149.0 seconds per 100,000. The run was stopped at
2.9 million columns with modular rank 2,787,358. The modular membership test
did not finish and rational elimination did not start.

This is a resource-limit result with no algebraic conclusion. The exact next
frontier is a fill-reducing ordering or block decomposition together with a
compiled characteristic-zero backend. Any replacement must first reproduce
the cap-3 and cap-4 results. Orbit 18 remains open, no branch is closed, and no
complex witness has been found.
