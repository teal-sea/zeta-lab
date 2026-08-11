# The all-window question and the bandwidth-one ceiling

**Status: one exact collapse result, and a full reproduction of every number the
public artifact makes reproducible. No improved proportion is claimed. Nothing
here is evidence for or against RH, and nothing here is a defect report against
the paper or its formalisation.**

## The question from the handoff

For each admissible window `v`, the paper obtains

    s1/N >= H(v) = 2 - 1/c(v),

where `s1` counts simple on-line zeros. Optimising one window gives

    sup_v H(v) = 0.6725007037...

The open suggestion was that all windows compress the same Weil form, so their
constraints might be stronger jointly than their best member.

There are two different meanings of "joint" here, and separating them settles
the first one.

### 1. Joint scalar trace constraints collapse

If the retained datum for each window is only its trace and Frobenius norm,
then the resulting feasible condition is literally

    s1/N >= H(v)  for every admissible v.

The intersection of these half-lines is

    s1/N >= sup_v H(v).

So this formulation collapses exactly to the best single window. The common
origin of the matrices is no longer represented after each matrix has been
reduced to its two scalar moments. An SDP or LP built only from those scalar
inequalities cannot move `0.6725007037...`.

Any non-collapsing formulation must retain cross-window information or,
equivalently, act on the whole bandwidth-one form-factor measure before it is
reduced to one Rayleigh quotient.

### 2. Full bandwidth-one certificates do not reduce to one window

The public companion repository makes the larger problem explicit. A
certificate is a pair `(c0, r)` that is valid configuration by configuration:

    c0 + sum_j s_j r(j/N) <= p,

where `s_j` are the form-factor masses of a marked configuration and `p` is its
simple-point fraction. Its asymptotic value against the bandwidth-one datum is

    c0 + integral_0^1 r(x) x dx.

This is an infinite linear-programming dual, not the conjunction of the
single-window rank-trace bounds. The published ceiling comes from a primal law
over marked periodic configurations.

## Reconstructing the public `N = 256` law data

The public Lean source is
`Zeta23/PairCeiling/LawN256.lean` at commit `3635e74826a4c1fcece7d1cd2b6fa75e43a00510`
of `github.com/anthropics/zeta-23-lean`. Running

    .venv/bin/python hunts/wide_search/pair_ceiling.py \
      /path/to/zeta-23-lean/Zeta23/PairCeiling/LawN256.lean

recomputes the following with exact rational arithmetic, from the published
enclosures alone:

| quantity | reconstructed value |
|---|---:|
| enclosure scale | `2^140` |
| number of rows | `256` |
| largest interior error `abs(256 S(j) - j)` | `1.83670992316e-40`, at `j = 1` |
| advertised interior tolerance | `3e-40` |
| edge discrepancy `D(1)` | `0.8239531607128352...` |
| stability coefficient | `2.5431315104166665e-6` |
| simple fraction stated in the source comment | `0.6818286874638315...` |

Every one of these agrees with the repository. This reconstructs the numerical
content behind the paper's rounded `0.68185` and gives a gap of about
`0.00932798` above the Montgomery-Taylor bound.

## Where the trust boundary sits

The formalisation is explicit about having exactly one step outside the Lean
kernel, and says so in three separate places. This section records that
boundary because a reader of this note needs to know where it is, not because
it is undocumented.

The exact-rational law is `cert_N256_blk_b128m.json`, SHA-256
`cc3de9917db4d14d844630a4e97dda8387fd6e257e52b6967f430b8914584eb8`. It is not
in the public repository. Per the README, the enclosures are "obtained outside
Lean by interval arithmetic from an exact-rational certificate ... available
from the authors", and

> The ONE displayed hypothesis of these theorems is `EnclOK`: that the law's
> form factor S(j), j = 1...256, lies in the 256 integer enclosures recorded in
> `LawN256.lean`.

The header of `LawN256.lean` repeats it ("the certificate file is available
from the authors"; "DISPLAYED HYPOTHESIS downstream: EnclOK ... verified
outside Lean by interval arithmetic"), and `AUDIT.md` records that the ceiling
theorems "carry the displayed hypothesis `EnclOK` described in the README".

Concretely, on the public side of that boundary:

- `ceiling_law256` (`CeilingLaw256.lean:38`) takes `S` as a generic function
  with `EnclOK` and `hvalid` as hypotheses, and leaves `p` a generic real.
- The fraction `10909258999421303588095230195816054408197 /
  16000000000000000000000000000000000000000` appears in a comment in
  `LawN256.lean` and in no executable declaration.
- Everything downstream of the enclosures is kernel-checked: the 255 near-CUE
  row inequalities, the edge bound, the sign of the edge term, and the analytic
  stability inequality.

So the artifact is exactly as advertised. What a third party can verify without
the certificate file is the entire chain from the enclosures onward, plus the
arithmetic reproduction in the table above, which is what `pair_ceiling.py`
does. What requires the authors' file is the construction of an `S` satisfying
`EnclOK`, together with its law weights, its simple fraction, and
configuration-by-configuration validity.

### On how the ceiling is quantified

The README states the result with its error terms carried explicitly:

> every bandwidth-one certificate certifies a proportion of simple zeros at
> most 0.6818287 + 2.55e-6 * (abs(r'(1)) + integral abs(r'')).

That is the correct form, and it is what the `N = 256` theorem gives. Worth
noting only for readers working from a rounded `0.68185` quoted without those
terms: a single finite law does not by itself yield a certificate-independent
ceiling without a uniform bound on the derivative term or a sequence of laws
with `N -> infinity`. The formal statement does not make that elision.

## Disposition

- The proposed LP over only the per-window trace and Frobenius constraints is
  closed: it equals the single-window optimum exactly.
- The larger full-data LP remains a legitimate route to an improvement between
  `0.6725007` and the published ceiling.
- Every quantity derivable from the public enclosures is reproduced by
  `pair_ceiling.py` and matches. Independently reconstructing the extremal law
  itself requires the certificate file, which the authors state is available on
  request.
- Nothing here is a claim that the extremal law is false, and nothing here is a
  defect in Theorems A-E. The `0.6725` result does not depend on the ceiling
  remark.
