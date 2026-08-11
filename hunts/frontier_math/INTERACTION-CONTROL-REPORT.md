# Negative on/off interaction: no recovery from the paper's inputs

## Disposition

No positive portion of the ordered-gap floor follows from the paper's existing
unconditional zero-side inputs. The obstruction is quantitative, not merely a
missing sign argument.

The sharp universal coefficient multiplying extra on-line cross mass is zero.
The interaction `2 tr(PQ)` itself has no finite lower bound from rank, trace of
`P`, and positive index of `Q`: replacing `Q` by `-tP` sends it to negative
infinity while keeping `n_+(Q)=0`.

This is an information statement. It does not assert that a zeta-zero block
realizes the families below. It says that the data passed to the paper's
rank-trace step do not exclude them, so those data alone cannot yield the
required strengthening.

## Pinned inputs

- Local repository state at the start of this audit:
  `21ad0d49720a288b1d428d46664d623a0f6c4282`.
- Paper PDF SHA-256:
  `6792988e6cd0e17690621ce898abd5d534f98407741bc7cb14bbe7d07c77d72f`.
- Lean companion: `anthropics/zeta-23-lean`, commit
  `3635e74826a4c1fcece7d1cd2b6fa75e43a00510`, tag `v1.0`.
- Upstream Mathlib commit:
  `51e6992efd06126df61a496bebf8f49482a4e129`.

The decisive interfaces are `Zeta23/ZeroSide.lean:470-555` and
`Zeta23/LinAlg/RankTrace.lean:157-195` at the pinned commit. They supply:

```text
P is positive semidefinite
rank(P) <= r
tr(P) <= s
Q is Hermitian
n_+(Q) <= b
A = P + Q.
```

No hypothesis there couples an off-line hyperbolic block to the ordered
on-line configuration.

## Sharp inequality available at this interface

For every `c > 0`, the pinned rank-trace lemma gives

```text
||A||_F^2
  >= c tr(P) - c^2 r/4 + 2c tr(Q) - c^2 b
   = 2c tr(A) - c tr(P) - c^2(r/4+b).
```

When `r+4b > 0`, optimizing this one-parameter family gives

```text
||A||_F^2 >= ((2 tr(A)-tr(P))_+)^2 / (r+4b).
```

At the paper's `c=2` this is

```text
||A||_F^2 >= 4tr(A) - 2tr(P) - r - 4b.
```

Using only `tr(P) <= s` and `r <= s` reduces it to the paper's census form

```text
||A||_F^2 >= 4tr(A) - 3s - 4b.
```

None of these expressions contains the positive on-line cross quantity

```text
R(P) = tr(P^2) - sum_j ||u_j||^4
     = sum_(i != j) |<u_i,u_j>|^2.
```

The omission cannot be repaired with a positive universal coefficient.

## Exact scalar family

For an integer `m >= 1`, put

```text
n = 2m^2 + 2.
```

Take `n` simple on-line labels, each with scalar evaluation vector `1`, and
one off-line conjugate pair with evaluation vectors `im` and `-im`. Then

```text
P = n
Q = (im)^2 + (-im)^2 = -2m^2 = -(n-2)
A = P+Q = 2
R(P) = n(n-1)
2tr(PQ) = -2n(n-2).
```

All entries are Gaussian integers. The paper's `c=2` census bound has slack

```text
||A||_F^2 - (4tr(A)-3n-4) = 3n.
```

Consequently any proposed universal strengthening

```text
||A||_F^2 >= 4tr(A)-3n-4 + theta R(P)
```

must satisfy

```text
theta <= 3/(n-1) = 3/(2m^2+1).
```

The right side tends to zero. Therefore every fixed `theta > 0` fails for an
explicit integer `m`. Even if the actual rank `rank(P)=1` and actual positive
index `n_+(Q)=0` are inserted, the `c=2` slack is only `2n-3`, and the same
zero-coefficient conclusion follows.

## Matching the paper's prime-side moments

The scalar family has deliberately extreme moments. A direct sum removes that
possible objection.

Let `M = kn`. Add:

- `M` orthogonal positive off-line blocks, each with eigenvalue `2+1/k`;
- `L` orthogonal unit on-line blocks.

Each positive block is an exact off-line hyperbolic block, represented for
example by the conjugate pair of real algebraic vectors
`sqrt((2+1/k)/2)`. The resulting quantities are

```text
N = n + L + 2(1+kn)
tr(A) = 2 + kn(2+1/k) + L = N
||A||_F^2 = 4 + kn(2+1/k)^2 + L
paper-bound slack = 3n + n/k
R(P) = n(n-1).
```

For any fixed target `C` in `(1,2)`, choose `L` as the nearest nonnegative
integer to

```text
(||A_0||_F^2 - C N_0)/(C-1).
```

Then `||A||_F^2/N` approaches `C`. Taking `k` large drives the paper-bound
slack per zero to zero. After that, taking `m` large makes `R(P)/N` exceed any
prescribed positive floor.

The exact checker uses the paper's printed second-moment target
`C = 1327499296/10^9`, with `m=10`, `k=100000`. Nearest-integer dilution gives

```text
N                         = 123360900
L                         = 82960696
||A||_F^2/N               = 8188075400101/6168045000000
distance from C           = 122617/154201125000000
paper-bound slack/N       = 49591/10095000000
R(P)/N                    = 6767/20560150
twice the old LP floor    = 14371/500000000.
```

Numerically, these last three densities are

```text
slack/N                   = 0.000004912431897...
R(P)/N                    = 0.000329131839991...
twice the old LP floor    = 0.000028742.
```

Thus the paper's trace identity, its printed Frobenius ratio, and more than
the entire proposed additive gap floor can coexist with failure of the
strengthened rank-trace inequality. The actual-rank version has still less
slack, `2n+n/k-3` before normalization.

## Missing invariant

The missing datum is a **signed on/off incidence law**. It must retain the
joint distribution of:

- an ordered on-line zero or gap word;
- an off-line conjugate pair;
- the pair's horizontal displacement from the line;
- its ordinate relative to the on-line word;
- the signed kernel value `2 Re(B(x,z)^2)`;
- reuse of the same off-line pair across overlapping on-line words.

Separate on-line gap statistics and aggregate off-line counts cannot recover
this information. Trace and Frobenius moments see only totals after positive
and negative blocks have already cancelled.

## Next configuration hierarchy

No decimal search should run before level 1 below has an unconditional zeta
constraint that excludes the obstruction family.

| Level | State retained | Required exact object | Kill control |
|---|---|---|---|
| 0 | Existing census, trace, Frobenius moment, positive index, separate on-line gaps | Current rank-trace lemma | Scalar and moment-matched families remain feasible |
| 1 | Signed on/off incidence cells `(gap position, ordinate offset, horizontal depth)` | Rational lower envelope for `2 Re(B(x,z)^2)` on every cell, plus an unconditional mass constraint | Concentrate all off-line mass in the most negative cells |
| 2 | One off-line pair marked against two consecutive on-line gaps | Projective consistency between one-gap marginals and marked two-gap words | Duplicate one off-line pair independently in overlapping cells |
| 3 | Marked `k`-gap words with overlap constraints | Local potential inequality whose boundary terms telescope | Periodic obstruction words and the direct-sum family |
| 4 | Full finite marked configuration | Rational dual object and one-sided continuum cell bounds | Projection to every lower level must reproduce its controls |

The first useful theorem schema is not another unmarked gap floor. It is a
conditional signed-incidence statement of the form

```text
joint on/off incidence constraints
  => 2tr(PQ) + theta R_selected >= -E N
```

with exact `theta > 0` and `E < theta Delta`. The zeta application may begin
only when every incidence constraint on the left is already available
unconditionally from the pinned paper or a separately established input.

## Reproduction

From the repository root:

```bash
.venv/bin/python hunts/frontier_math/interaction_obstruction.py
.venv/bin/python -m pytest -q -o addopts='' \
  hunts/frontier_math/test_interaction_obstruction.py
```

Both commands use integer or rational arithmetic. No optimizer, sampled grid,
or floating feasibility tolerance enters the obstruction.
